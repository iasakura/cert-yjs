# Design: ghost-tracked global operation history (issue #42)

Implementation plan for
[#42 — core: ghost-tracked global operation history](https://github.com/iasakura/cert-yjs/issues/42):
a shared Perennial ghost resource for the global operation history, so that the
heap/WP state of every replica *refines* the rocq-yjs network model
(`YjsOperationNetwork`), each replica's document is a causally-closed subset of
that history, and `applyUpdate`'s validity becomes a **sender-side certificate**
instead of the receiver-side `ValidReplay` precondition.

This document is written to be executable step by step: every new definition is
given in (near-)final Rocq, every lemma has a statement sketch, a proof sketch,
a difficulty tag, and a home file. Model citations are into
`iasakura/iris-yjs` (the `rocq-yjs` opam package); cert-yjs citations are into
this repo. Read together with `docs/aneris-oplib-artifact.md` (the OpLib
comparison that motivated several choices here).

---

## 0. TL;DR

- **Ghost state** (three pieces, one global `inv`, no `1 + 5N` gname grid):
  1. `ghost_map ClientId (list Event)` — the per-client event histories,
     mirroring the model's `NodeHistories` *directly*. The auth sits in a global
     invariant; each replica's store-lock invariant holds its own client's
     exclusive element `c ↪[γ] h` (= the append capability).
  2. `ghost_map YjsId (YjsOperation A * gset YjsId)` — the broadcast-op registry.
     Persistent elements `id ↪[γ]□ (op, D)` are the **op certificates**: "op was
     broadcast, and `D` covers its causal past". Minted by `Insert`, consumed by
     `applyUpdate`.
  3. per-store `own γgov (to_agree parent)` — agreement on *which* text the
     network governs (single-root-text scope).
- **The global invariant** holds both auths plus `⌜history_wf N⌝`, where
  `history_wf` is *literally* the conjunction of the model's network axioms
  (`NetworkBase` + `CausalNetwork` + `OperationNetwork` + `YjsOperationNetwork`
  fields) over the raw `gmap`, plus two disciplines of our instantiation
  (immediate self-delivery, insert-only). Re-establishing `history_wf` at each
  ghost append **is** the proof that the WP state refines the network model.
- **`applyUpdate` consumes certificates via a pure lemma**: certificates +
  `history_wf` ⇒ `ValidReplay inputs arr arr'`. The existing
  `wp_store__applyUpdate` proof is then invoked **unchanged**; the new spec is a
  thin fupd-wrapper around it.
- **Prerequisite upstream fix**: iris-yjs's `deliver_locally` axiom had its
  hypothesis flipped relative to Gomes et al.; as stated it (together with
  `histories_client_id`) made remote delivery **unsatisfiable**, so no
  multi-replica instantiation existed. **Fixed and merged**
  (iasakura/iris-yjs#24, merge `b95e6da`; ported back to lean-yjs as
  iasakura/lean-yjs#31). Remaining M0 step: bump the `pin-depends` SHAs. §2
  has the details.
- **Scope cuts** (each flagged with rationale + extension path, §8): `Delete`
  does *not* mint ops (insert-only history); client set fixed at allocation;
  one governed root text per store; the history tracks `st_items` only (not
  tombstone flags).

---

## 1. Where we start / what must not break

Current verified surface (all axiom-clean; keep them that way):

- `wp_Store__Integrate` — `src/proof/yjs_store.v:1985`.
- `wp_store__applyUpdate` — `src/proof/yjs_store.v:2093`, with the
  receiver-side `ValidReplay` (`yjs_store.v:2076`).
- `wp_Text__Insert` — `src/proof/yjs_text.v:185`; `wp_Text__Delete` —
  `yjs_text.v:653`; both go through the lock layer `store_inv` / `is_Store`
  (`yjs_store.v:192/210`) and `is_Text` (`yjs_text.v:150`).

Contract changes proposed by this design (maintainer sign-off required per
CLAUDE.md; this document is the sign-off artifact):

| contract | change |
|---|---|
| `store_inv`, `is_Store` | new parameter `γh : history_names`; new conjuncts (own-history element, governed-text tie) |
| `is_Text` | new parameter `γh`; new conjuncts (`is_history γh`, governed-text agreement) |
| `wp_Text__Insert` | post additionally mints one op certificate per inserted item |
| `wp_Text__Delete` | statement unchanged up to the new `is_Text` arity (no minting; see §8.1) |
| `wp_store__applyUpdate` | **new sibling spec** `wp_store__applyUpdate_certs` (sender-side); the old `ValidReplay` spec is kept as the internal lemma it already is |
| `yjs/*.go` | **no Go changes at all** — this is a ghost-only feature |

---

## 2. Prerequisite: fix `deliver_locally` in iris-yjs (upstream)

Status: **fixed and merged** — iasakura/iris-yjs#24 (merge commit `b95e6da`)
and, for the port source, iasakura/lean-yjs#31 (merge commit `ac08745`). What
remains of M0 is the `pin-depends` bump (§2.3 item 3). §§2.1–2.2 record the
bug and the fix for reference.

### 2.1 The bug

`theories/crdt/network/causal_network.v:66` (ported verbatim from
`LeanYjs/Network/CausalNetwork.lean:33`):

```rocq
deliver_locally : forall i e,
  EvDeliver e ∈ histories nb_nodes i ->
  locallyOrdered nb_nodes i (EvBroadcast e) (EvDeliver e);
```

i.e. *every delivery at node `i` is preceded by a broadcast of the same message
at node `i` itself*. Combined with
`histories_client_id : EvBroadcast e ∈ histories i → clientId (opid e) = i`
(`yjs_operation_network.v:46`), any node that delivers `e` must be `e`'s
author. So a well-formed `YjsOperationNetwork` cannot contain a single remote
delivery, `toDeliverMessages i` only ever contains `i`'s own operations, and
the convergence theorems are vacuous for `i ≠ j` with non-empty delivered sets.
No ghost instantiation of a real replicated run can satisfy the axioms — this
blocks #42 outright.

Gomes et al. (OOPSLA 2017, the model lean-yjs ports) state the axiom in the
other direction — a node that **broadcasts** must subsequently self-deliver:

```rocq
deliver_locally : forall i e,
  EvBroadcast e ∈ histories nb_nodes i ->
  locallyOrdered nb_nodes i (EvBroadcast e) (EvDeliver e);
```

### 2.2 The fix is 3 lines

`deliver_locally` is used **exactly once** in all of iris-yjs:
`causal_network.v:202`, inside `HappensBefore_asymm`. At that use site the
proof context already contains
`Hlo : locallyOrdered cn i (EvDeliver a') (EvBroadcast b')`, from which
`EvBroadcast b' ∈ histories cn i` follows by the same `set_solver` idiom used
two lines above. So the adaptation is:

```rocq
    have Hmem_bb' : EvBroadcast b' ∈ histories cn i
      by case: Hlo => l1 [l2 [l3 ->]]; set_solver.
    have Hlo_bb'_db' : locallyOrdered cn i (EvBroadcast b') (EvDeliver b')
      := deliver_locally cn i b' Hmem_bb'.
```

(replacing the derivation of `Hmem_db'`, which becomes unused). Everything
downstream (`network_causal_order`, the replay-validity file, the convergence
theorems) only depends on `HappensBefore_asymm`, not on the axiom directly.

### 2.3 Deliverable M0

1. PR to `iasakura/iris-yjs`: flip the hypothesis, adapt `HappensBefore_asymm`,
   `dune build` green. **Done and merged: iasakura/iris-yjs#24** (merge
   `b95e6da`). The same fix is ported back to lean-yjs
   (`LeanYjs/Network/CausalNetwork.lean:33`): **iasakura/lean-yjs#31, merged**
   (`ac08745`) — independent of cert-yjs.
2. Add the upstream lemmas of §4.4 that belong in iris-yjs (they mention only
   model types) in a follow-up iris-yjs PR (can proceed in parallel with M1).
3. **Remaining**: bump both `pin-depends` SHAs in `cert-yjs.opam` (`rocq-yjs`,
   `rocq-yjs-core`) to `b95e6da` (or the then-current iris-yjs main),
   `opam install ./cert-yjs.opam --deps-only` (reinstalls the pins),
   `./build.sh` green.

Note: the currently pinned SHA `2947b30f` predates iris-yjs HEAD `245ada52`
("Prove setfii_loop_eq_fii_loop"); the bump lands that too — re-run the full
build and expect no fallout (the insert_set API did not change shape).

---

## 3. Architecture

```
             ┌────────────────────────────────────────────────────────────┐
             │  global invariant  inv histN (history_inv γh)              │
             │   ghost_map_auth hn_hist N   (N : gmap ClientId (list Ev)) │
             │   ghost_map_auth hn_ops  ops (ops : gmap YjsId (op, D))    │
             │   ⌜history_wf N⌝  ⌜ops_coh N ops⌝                          │
             └──────────▲──────────────────────────▲──────────────────────┘
              open at ghost append           persistent certificates
              (broadcast / deliver)           id ↪[hn_ops]□ (op, D)
             ┌──────────┴───────────┐    ┌──────────┴───────────┐
             │ replica 1 store lock │    │ replica 2 store lock │   ...
             │  store_inv:          │    │                      │
             │   c₁ ↪[hn_hist] h₁   │    │   c₂ ↪[hn_hist] h₂   │
             │   own γgov (to_agree │    │        ...           │
             │        gparent)      │    │                      │
             │   ⌜history_state_coh │    │                      │
             │        h₁ ts_gov⌝    │    │                      │
             │   (+ everything      │    │                      │
             │      already there)  │    │                      │
             └──────────▲───────────┘    └──────────────────────┘
                        │ is_Text / wp_Text__Insert / wp_Text__Delete
                        │ wp_store__applyUpdate_certs (caller holds lock)
             ┌──────────┴───────────┐
             │ heap: DLL, is_ytype, │
             │ store fields, slices │
             └──────────────────────┘
```

- The **model** (`rocq-yjs`) supplies: `Event`, `YjsOperation`, `yjs_op_effect`,
  `interpHistory`, `toDeliverMessages`, the network records, happens-before,
  and the endgame theorems (`isValidState_insert_from_source`,
  `yjs_strong_convergence`, `YjsOperationNetwork_converge_final`).
- The **pure bridge** (`yjs_network_model.v`, new) re-states the network records
  over a raw `gmap ClientId (list Event)` and proves the append-preservation and
  certificate-to-`ValidReplay` lemmas. Zero Iris — iterate on it with rocq-mcp
  without touching goose.
- The **ghost layer** (`yjs_history.v`, new) wraps the bridge in `ghost_map` +
  `inv` and exports three fupd lemmas (`alloc` / `broadcast` / `deliver`).
- The **WP layer** threads the new conjuncts through `store_inv` / `is_Text`
  and re-proves `Insert` (minting), `Delete` (frame), and states the
  certificate-based `applyUpdate`.

Why this shape and not OpLib's (`docs/aneris-oplib-artifact.md` §5–6): OpLib's
`1 + 5N` gname grid exists to reconcile three views (user / lock / invariant)
of the same sets. We have no separate "user view" — the lock invariant *is* the
local view, so a single exclusive `ghost_map` element per client replaces
`γ_own/γ_for/γ_sub/γ_cc/γ_inv`. Likewise we do not need Aneris's monotone RA
over `cc_subseteq`: causal closure lives inside `history_wf` (the
`causal_delivery` axiom), and the *stability* that the monotone RA provided is
recovered by a pure lemma (§4.4 L6: happens-before between existing ops is
unchanged by appends), which makes the persistent certificate sound.

---

## 4. The pure bridge: `src/proof/yjs_network_model.v` (new)

No Iris. Section context: `Context {A : Type} `{Countable A} `{EqDecision A}.`
(instantiated at `A := go_string` downstream). Abbreviations used below:

```rocq
Notation Op    := (@YjsOperation A).            (* yjs_network.v:23  *)
Notation opid  := (@YjsOperation_id A).         (* yjs_network.v:31  *)
Notation O     := (@YjsOp A _).                 (* yjs_network.v:44  *)
Notation Ev    := (@Event Op).                  (* causal_network.v  *)
Notation RawHistories := (gmap ClientId (list Ev)).
```

First task: `Countable YjsId` (needed for `gset YjsId` keys of the ops map) —
derive via the pair encoding `(clientId, clock)`; one `Instance` next to
`YjsItem_countable` in `yjs_common.v:82` or at the top of this file.
`EqDecision Op` / `EqDecision Ev` already exist upstream
(`yjs_network.v:27`, `causal_network.v` `Event_eq_dec`).

### 4.1 Raw-history views

```rocq
Definition to_histories (N : RawHistories) : ClientId -> list Ev :=
  fun i => default [] (N !! i).

(* All broadcast operations / their ids, across the whole network. *)
Definition broadcasts (N : RawHistories) : list Op := ...   (* concat, filter EvBroadcast *)
Definition op_ids (N : RawHistories) : gset YjsId := ...

(* Ops delivered in one raw history, in order (= toDeliverMessages).  *)
Definition delivered_ops (h : list Ev) : list Op := omap deliverP h.
Definition delivered_ids (h : list Ev) : gset YjsId := list_to_set (opid <$> delivered_ops h).
```

### 4.2 `history_wf`

One record, whose fields are *verbatim* the model's axioms specialized to
`to_histories N`, plus the two extra disciplines of our instantiation:

```rocq
Record history_wf (N : RawHistories) : Prop := {
  (* NodeHistories (causal_network.v:29) *)
  hwf_nodup : forall i, NoDup (to_histories N i);
  (* NetworkBase (causal_network.v:62), deliver_locally in Gomes form (§2) *)
  hwf_deliver_has_a_cause : ...;
  hwf_deliver_locally     : ...;   (* subsumed by hwf_self_deliver, keep for record-building *)
  hwf_msg_id_unique       : ...;
  (* CausalNetwork (causal_network.v:92) *)
  hwf_causal_delivery     : ...;
  (* OperationNetwork (operation_network.v:26), isValidMessage := YjsIsValidMessage *)
  hwf_broadcast_valid     : ...;
  (* YjsOperationNetwork (yjs_operation_network.v:43) *)
  hwf_client_id           : ...;
  hwf_unique_id           : ...;
  (* ours: a broadcast is immediately followed by its own delivery.       *)
  (* Needed for L4/L5 (clock discipline at receivers): it forces the      *)
  (* author's replayed state at broadcast time to contain all of its own  *)
  (* earlier items.                                                       *)
  hwf_self_deliver : forall i e pre post,
    to_histories N i = pre ++ [EvBroadcast e] ++ post ->
    exists post', post = EvDeliver e :: post';
  (* ours: insert-only history (§8.1). *)
  hwf_insert_only : forall i e, (EvBroadcast e ∈ to_histories N i \/
                                 EvDeliver e ∈ to_histories N i) ->
                    exists input, e = OpInsert input;
}.
```

Then the packaging, which is what #40 will consume:

```rocq
(* history_wf is literally the data of the model records. *)
Definition to_network (N : RawHistories) (wf : history_wf N) : YjsOperationNetwork (A := A).
(* to_histories (to_network N wf) = to_histories N, definitionally. *)
```

Building `to_network` is `Program Definition` / record-constructor plumbing:
each model field is a `history_wf` field (or a two-line consequence). Also
define the induced order once:

```rocq
Definition raw_hb (N : RawHistories) (wf : history_wf N) : relation Op :=
  HappensBefore (to_network N wf).   (* the strict part; causal_network.v:74 *)
```

Convention: state the *lemmas* below against `HappensBefore`-style splits of
`to_histories N` directly (not through `to_network`) wherever possible, so they
do not carry a `wf` proof-term argument; package into `to_network` only at the
boundaries that call model theorems.

### 4.3 Local coherence (lock-side tie)

```rocq
(* The events h replay (delivers only) to a state whose item list is arr.
   Tombstone flags are NOT tracked by the history (§8.4).                  *)
Definition history_state_coh (h : list Ev) (arr : list (YjsItem A)) : Prop :=
  exists s, interpHistory O h (op_init O) s /\ st_items s = arr.
```

`interpHistory` is `operation_network.v:22`; it is deterministic here because
`yjs_op_effect` is (`YjsState_insert` is a function into `option`), so
`history_state_coh` pins `arr` uniquely — prove that as lemma L0 below.

### 4.4 Lemma inventory (pure)

Difficulty scale: (E)asy < (M)edium < (H)ard. "Home": `up` = belongs upstream
in iris-yjs (mentions only model types), `here` = `yjs_network_model.v`.

| # | statement (sketch) | proof sketch | diff | home |
|---|---|---|---|---|
| L0 | `history_state_coh h arr → history_state_coh h arr' → arr = arr'` and `effect_list`-append composition: `effect_list O l1 init s → effect_list O l2 s s' → effect_list O (l1++l2) init s'` (and the converse split) | unfold `apply_ops`; induction on `l1`; determinism of `yjs_op_effect` by case on the op | E | up |
| L1 | `st_items`-monotonicity: `yjs_op_effect op s s' → ∀ x, x ∈ st_items s → x ∈ st_items s'`; corollary for `effect_list` | case on op: `YjsState_insert_insertIdx_form` (yjs_replay_validity.v:46) gives an `insertIdx`; `deleteById` keeps items | E | up |
| L2 | **hb append-stability**: if `N' = <[c := to_histories N c ++ tail]> N` then (a) `HappensBefore N x y → HappensBefore N' x y`; (b) for `x, y` both *broadcast in `N`*: `HappensBefore N' x y → HappensBefore N x y` | (a) splits survive appends. (b) induction on the derivation; the last local step lands strictly before `y`'s (old, fixed-position) broadcast event, so it lies in the old prefix; transitivity chains through events that are themselves before an old broadcast, hence old | M–H | up |
| L3 | **hb-past of a fresh broadcast**: `N' = <[c := h ++ [EvBroadcast op; EvDeliver op]]> N`, `N !! c = Some h`, `opid op ∉ op_ids N` ⇒ `∀ x, HappensBefore N' x op → x ∈ events_ops h` (ops mentioned by `h`, broadcast or delivered) | last hop of the derivation must be a local step at `c` below `EvBroadcast op` (msg-id-uniqueness kills other nodes); induct with L2(b) for the prefix chain | M–H | up |
| L4 | **freshness**: `history_wf N → N !! c = Some h → history_state_coh h arr → (∀ x ∈ arr, clientId (item_id x) = c → clock (item_id x) < k) → MkYjsId c k ∉ op_ids N` | an op with client `c` is broadcast only at `c` (`hwf_client_id` + `hwf_msg_id_unique`), so it is in `h`; `hwf_self_deliver` ⇒ its delivery is in `h`; its item enters `st_items` (`YjsState_insert_mem`, yjs_replay_validity.v:150) and persists (L1) ⇒ its clock `< k` | M | here |
| L5 | **receiver clock safety** (`isClockSafe_from_source`): `history_wf N`; `OpInsert input` broadcast at its author; `l` a list of ops all broadcast in `N`, `OpInsert input ∉ l`, `l ⊇` its strict hb-past; `effect_list O l init s` ⇒ `isClockSafe (in_id input) (st_items s) = true`, hence `maximalId item (st_items s)` for the resolved item | a same-client item `x ∈ st_items s` comes from some `OpInsert x_op ∈ l` (induction/L1); both authored at `c'` (client of `input`); locally ordered one way: `x_op` before ⇒ `hwf_self_deliver` puts `EvDeliver x_op` before `EvBroadcast op`, so `hwf_unique_id`'s replayed prefix state contains `x` (needs L0 split) ⇒ `clock x < clock op`; `op` before `x_op` ⇒ `op` hb `x_op` ⇒ `op ∈ l` by hb-past coverage — contradiction | H (the one real theorem) | up (needs `hwf_self_deliver` as an explicit hypothesis if stated model-side) |
| L6 | **broadcast step**: `history_wf N`, `N !! c = Some h`, `history_state_coh h arr`, `op = OpInsert input`, `toItem input arr = Some item`, `IsItemValid item`, `maximalId item arr`, `opid op = MkYjsId c k`, `k` fresh per L4's hypothesis ⇒ `history_wf (<[c := h ++ [EvBroadcast op; EvDeliver op]]> N)` ∧ `history_state_coh (h ++ …) (insertIdx-result)` ∧ `∀ x, HappensBefore N' x op → opid x ∈ delivered_ids h` | field by field: NoDup from freshness; `hwf_broadcast_valid` for the new split is exactly `toItem`+`IsItemValid` at `arr` (via L0); `hwf_unique_id` new split = `maximalId` (via L0 + `hwf_self_deliver`); `hwf_causal_delivery` for the new `EvDeliver op` = L3 + `hwf_self_deliver` (everything in `h` is delivered in `h`); old splits unchanged (append). The `coh` part: `YjsState_insert` succeeds because `maximalId ↔ isClockSafe` (L9) and `integrate_some` (commutativity.v) | H | here |
| L7 | **deliver step**: `history_wf N`, `N !! c = Some h`, cert facts (`op` broadcast in `N` with registered `(op, D)`, `D ⊇` hb-past ids), `D ⊆ delivered_ids h`, `opid op ∉ delivered_ids h`, `clientId (opid op) ≠ c` or op simply not yet delivered ⇒ `history_wf (<[c := h ++ [EvDeliver op]]> N)` | NoDup: no prior `EvDeliver op` (id-injectivity via `hwf_msg_id_unique`); `deliver_has_a_cause`: cert; `causal_delivery` for the new event: hb-past ids `⊆ D ⊆ delivered_ids h`, and id-uniqueness turns id-membership into op-membership; delivers add no broadcast splits, so the operation-network fields are untouched | M | here |
| L8 | **certificate soundness is stable**: if `∀ x, HappensBefore N x op → opid x ∈ D` and `N'` extends `N` by appends, then the same holds for `N'` (for `op` broadcast in `N`) | direct from L2(b) | E | here |
| L9 | `maximalId item arr ↔ isClockSafe (item_id item) arr = true` (with `toItem input arr = Some item`, so ids agree via `toItem_id`) | unfold both (`insert_loop.v:534`, `insert_basic.v:122`); `forallb`/`bool_decide` reflection | E | here |
| L10 | **certs ⇒ ValidReplay** (the applyUpdate bridge): see full statement below | per-step: L5 (+ `isValidState_insert_from_source`, yjs_replay_validity.v:614) for `toItem`/`IsItemValid`; L5 for `maximalId`; `integrate_some` for progress; L7 iterated for wf of the extended history; induction over the batch | M given L5–L7 | here |

Full statement of L10 (shapes the WP spec, so it is worth writing out):

```rocq
(* Batch delivery precondition, receiver-side but *pure and id-level*:
   every input's certified causal past is covered by what this replica
   already delivered plus the earlier part of the batch, and no input is a
   re-delivery. This is what y-octo's UpdateIterator establishes with the
   state vector; the verified subset takes it as a hypothesis.            *)
Definition batch_ok (h : list Ev) (inputs : list (IntegrateInput (A := A)))
    (Ds : list (gset YjsId)) : Prop :=
  forall i input D, inputs !! i = Some input -> Ds !! i = Some D ->
    D ⊆ delivered_ids h ∪ list_to_set (in_id <$> take i inputs) /\
    in_id input ∉ delivered_ids h ∪ list_to_set (in_id <$> take i inputs).

Lemma certs_ValidReplay (N : RawHistories) (c : ClientId) (h : list Ev)
    (arr : list (YjsItem A)) (inputs : list (IntegrateInput (A := A)))
    (Ds : list (gset YjsId)) :
  history_wf N -> N !! c = Some h ->
  history_state_coh h arr ->
  (forall i input D, inputs !! i = Some input -> Ds !! i = Some D ->
     op_registered N (OpInsert input) D) ->      (* the ops_coh facts, §5.2 *)
  batch_ok h inputs Ds ->
  exists arr',
    ValidReplay inputs arr arr' /\
    history_state_coh (h ++ (EvDeliver ∘ OpInsert <$> inputs)) arr' /\
    history_wf (<[c := h ++ (EvDeliver ∘ OpInsert <$> inputs)]> N).
```

(`ValidReplay` is `yjs_store.v:2076`; note `certs_ValidReplay` *produces* the
existential `arr'`, so the WP spec no longer needs the caller to supply it.)

### 4.5 How to build this file

Standalone: it only `Require`s `yjs_core` (extend `yjs_core.v` to also
re-export `yjs.crdt.network.causal_network`, `yjs.crdt.network.operation_network`,
`yjs.network.yjs_network`, `yjs.network.yjs_operation_network`,
`yjs.network.yjs_replay_validity`). Iterate with `rocq_start`/`rocq_check` on
it alone; it compiles without goose output. This is where most of the proof
effort lives, and none of it touches WP.

Order of implementation inside M1: L0, L1, L9 (warm-up) → L2 → L3 → L4 →
L5 → L6, L7, L8 → L10. L2/L3/L5 are the hard kernel; if L5 stalls, everything
else can still land (L10 is the only consumer).

---

## 5. The ghost layer: `src/proof/yjs_history.v` (new)

Iris but no goose. `Require`s `yjs_network_model`, `yjs_common`.

### 5.1 Typeclass context and gnames

```rocq
Notation A := go_string.
Notation Op := (@YjsOperation A).
Notation Ev := (@Event Op).

(* One record instead of loose gnames (Perennial house style). *)
Record history_names := HistoryNames {
  hn_hist : gname;   (* ghost_map ClientId (list Ev)           *)
  hn_ops  : gname;   (* ghost_map YjsId (Op * gset YjsId)      *)
}.

Class historyG Σ := {
  hist_map_G :: ghost_mapG Σ ClientId (list Ev);
  ops_map_G  :: ghost_mapG Σ YjsId (Op * gset YjsId);
  gov_agree_G :: inG Σ (agreeR (leibnizO loc));   (* per-store governed text *)
}.
Definition historyΣ : gFunctors := #[ghost_mapΣ _ _; ghost_mapΣ _ _; GFunctor (agreeR (leibnizO loc))].
```

`ghost_map` needs `Countable` only on keys (`ClientId = nat` ✓, `YjsId` via the
new instance); values go through `leibnizO`, no `Countable` needed. `heapGS Σ`
already provides `invGS`, so `inv`/`iInv` work in Perennial-New proofs (see
`new/proof/own_crash.v` for the allocation/opening idiom).

### 5.2 Predicates

```rocq
Definition histN : namespace := nroot .@ "cert_yjs" .@ "history".

(* ops registry coherence: every registered op is broadcast (at its author),
   its D covers its causal past, and every broadcast op is registered.
   ops_coh / op_registered are pure Props — define them in
   yjs_network_model.v (they are hypotheses of L10) and only USE them here. *)
Definition ops_coh (N : RawHistories) (ops : gmap YjsId (Op * gset YjsId)) : Prop :=
  (forall id op D, ops !! id = Some (op, D) ->
     opid op = id /\
     EvBroadcast op ∈ to_histories N (clientId id) /\
     (forall wf : history_wf N, forall x, HappensBefore (to_network N wf) x op -> opid x ∈ D) /\
     D ⊆ op_ids N) /\
  (forall op, op ∈ broadcasts N -> is_Some (ops !! opid op)).

Definition op_registered (N : RawHistories) (op : Op) (D : gset YjsId) : Prop := ... (* the per-op half *)

Definition history_inv (γh : history_names) : iProp Σ :=
  ∃ (N : RawHistories) (ops : gmap YjsId (Op * gset YjsId)),
    "HhistAuth" ∷ ghost_map_auth γh.(hn_hist) 1 N ∗
    "HopsAuth"  ∷ ghost_map_auth γh.(hn_ops) 1 ops ∗
    (* Certificate recovery (needed by the network layer's relay server,
       docs/plan-network-sync-protocol.md §3): keep a copy of every persisted
       fragment inside the invariant, so any party that can open [is_history]
       and name a registered id can duplicate its certificate.  G2 mints the
       [↪□] fragment anyway, so re-establishing this big-op is free. *)
    "#Hcerts"   ∷ ([∗ map] id ↦ p ∈ ops, id ↪[γh.(hn_ops)]□ p) ∗
    "%Hwf"      ∷ ⌜history_wf N⌝ ∗
    "%Hopscoh"  ∷ ⌜ops_coh N ops⌝.

Definition is_history (γh : history_names) : iProp Σ :=
  inv histN (history_inv γh).                                  (* persistent *)

(* Exclusive: this replica IS client c, with event history h. Lives in the
   store lock invariant.                                                    *)
Definition own_client_history (γh : history_names) (c : ClientId) (h : list Ev) : iProp Σ :=
  c ↪[γh.(hn_hist)] h.

(* Persistent: op was broadcast; D covers its causal past. THE certificate. *)
Definition is_op_cert (γh : history_names) (op : Op) (D : gset YjsId) : iProp Σ :=
  (opid op) ↪[γh.(hn_ops)]□ (op, D).
```

Technical note on `ops_coh`'s hb clause: quantifying over `wf : history_wf N`
avoids storing a proof term; `HappensBefore` only reads `to_histories`, so any
`wf` gives the same relation. If this proves awkward, restate `HappensBefore`
over `NodeHistories`-as-function without the record (it only uses
`locallyOrdered`), which needs no `wf` at all — preferred if L2/L3 are stated
that way anyway.

### 5.3 Ghost update lemmas (the whole API)

All are `fupd`-only (no WP): they open `inv histN`, apply an L-lemma from §4.4
to re-establish `history_wf`/`ops_coh`, and close. Usable inside any WP proof
via `iApply fupd_wp` / around a step (no atomic step is *required* since the
invariant is not held open across one).

```rocq
(* G1: allocation, client set fixed up front (§8.2). *)
Lemma history_alloc (C : gset ClientId) E :
  ⊢ |={E}=> ∃ γh, is_history γh ∗ [∗ set] c ∈ C, own_client_history γh c [].

(* G2: broadcast (mint). Preconditions = L6's hypotheses, all available
   inside wp_Text__Insert's loop at the call site.                         *)
Lemma history_broadcast γh (c : ClientId) (k : nat) h arr input item E :
  ↑histN ⊆ E ->
  toItem input arr = Some item -> IsItemValid item -> maximalId item arr ->
  in_id input = MkYjsId c k ->
  (forall x, x ∈ arr -> clientId (item_id x) = c -> (clock (item_id x) < k)%nat) ->
  history_state_coh h arr ->
  is_history γh -∗ own_client_history γh c h ={E}=∗
  ∃ D, own_client_history γh c (h ++ [EvBroadcast (OpInsert input); EvDeliver (OpInsert input)]) ∗
       is_op_cert γh (OpInsert input) D ∗
       ⌜D ⊆ delivered_ids h⌝ ∗
       ⌜history_state_coh (h ++ [_; _]) (the L6 arr')⌝.

(* G3: deliver a certified batch (used by applyUpdate's spec).             *)
Lemma history_deliver_batch γh c h arr inputs Ds E :
  ↑histN ⊆ E ->
  batch_ok h inputs Ds ->
  history_state_coh h arr ->
  is_history γh -∗ own_client_history γh c h -∗
  ([∗ list] input;D ∈ inputs;Ds, is_op_cert γh (OpInsert input) D) ={E}=∗
  ∃ arr', own_client_history γh c (h ++ (EvDeliver ∘ OpInsert <$> inputs)) ∗
          ⌜ValidReplay inputs arr arr'⌝ ∗
          ⌜history_state_coh (h ++ …) arr'⌝.

(* G4: agreement/read — combine cert with the auth to extract op_registered
   facts under the invariant (used inside G3's proof, exported for #40).   *)
```

Proof shape for G2/G3: `iInv histN as (N ops) "(>Hauth & >Hops & >%Hwf & >%Hcoh)"`,
`ghost_map_lookup` (elem vs auth) to learn `N !! c = Some h`, apply L6/L7+L10,
`ghost_map_update` / `ghost_map_insert` + `ghost_map_elem_persist` for the new
cert, close with the new pure facts. Freshness for `ghost_map_insert` on
`hn_ops` comes from L4 + `ops_coh` (registered ⇒ broadcast ⇒ id in `op_ids N`).

---

## 6. WP-layer changes

### 6.1 `store_inv` / `is_Store` (`yjs_store.v:192/210`)

New section context: `Context `{!historyG Σ}.` New parameters `γh` and a
per-store `γgov : gname`. Bundle `γgov` next to the existing `γ` (either as a
second explicit parameter or a two-field record `store_names`; recommended:
`store_names` with `sn_seq`, `sn_gov`, to avoid a third gname argument later).

New conjuncts inside the existing existential (after `"%Hctr"`):

```rocq
    (* --- network layer (issue #42) --- *)
    ∃ (gparent : loc) (ts_gov : text_state) (h : list Ev),
    "Hgov"     ∷ own γs.(sn_gov) (to_agree (gparent : leibnizO loc)) ∗
    "%Hgovts"  ∷ ⌜texts !! gparent = Some ts_gov⌝ ∗
    "Hhist"    ∷ own_client_history γh (uint.nat client) h ∗
    "%Hhcoh"   ∷ ⌜history_state_coh h (ts_arr ts_gov)⌝
```

and `is_Store s_loc γs γh := is_Mutex … (store_inv s_loc γs γh)` (the
`is_history γh` handle rides in `is_Text`, not here, to keep `store_inv`
first-order).

Sanity deliverable (non-vacuity): a resource-assembly lemma

```rocq
Lemma store_inv_init s_loc γs γh c … :
  (fresh-store heap points-tos) -∗ own_client_history γh c [] ==∗
  ∃ …, store_inv s_loc γs γh
```

with one registered empty text (`ts_arr = []`, `history_state_coh [] []` holds
by `interpHistory [] init init`). This guards against an accidentally-false
invariant and is the seam where a future `wp_NewDoc`/`wp_Doc__GetText` plugs in.

### 6.2 `is_Text` (`yjs_text.v:150`)

```rocq
Definition is_Text (t : loc) (γh : history_names) (L : list (YjsItem A)) : iProp Σ :=
  ∃ (tv : yjs.Text.t) (s_loc parent : loc) (γs : store_names),
    … (as today) …
    "His_store" ∷ is_Store s_loc γs γh ∗
    "His_hist"  ∷ is_history γh ∗
    "Hgov"      ∷ own γs.(sn_gov) (to_agree (parent : leibnizO loc)) ∗
    … (lb + sortedness as today) …
```

Every `Text` handle claims its text is the governed one; two handles on
*different* texts of one store are now unsatisfiable together (agreement) —
deliberate single-root-text scope (§8.3). Under the lock, `Hgov` (handle) +
`Hgov` (invariant) + `to_agree` validity give `parent = gparent`, which
replaces nothing but *adds* the governed-text extraction to the existing
`auth_gmap_gset_lookup` prologue.

### 6.3 `wp_Text__Insert` (`yjs_text.v:185`)

Statement: same shape, plus certificates. Sketch of the post delta:

```rocq
  {{{ … as today … ∗
      ∃ (inputs : list (IntegrateInput (A := A))) (Ds : list (gset YjsId)),
        ⌜length inputs = length ins⌝ ∗
        ⌜∀ i it input, ins !! i = Some it -> inputs !! i = Some input ->
           toItem-consistency: in_id input = item_id it ∧ in_content input = content it ∧ …⌝ ∗
        [∗ list] input;D ∈ inputs;Ds, is_op_cert γh (OpInsert input) D }}}
```

Proof changes (mechanical but the largest rethreading; the #29/#35 sed-style
passes are precedent):

1. Prologue additionally destructs the new `store_inv` conjuncts and matches
   `parent = gparent` via agreement; out-of-range branch reframes them
   unchanged.
2. The insert loop already establishes, per character, exactly
   `toItem`/`IsItemValid`/`maximalId` (they feed `wp_Store__Integrate`) and has
   `Hctr` for the clock bound. **Mint inside the loop**: after
   `wp_Store__Integrate` returns, `iMod (history_broadcast …)` (G2) with those
   facts; accumulate `is_op_cert` (persistent) and the updated
   `own_client_history`/`history_state_coh` in the loop invariant. The loop
   invariant gains: current `h_j`, `history_state_coh h_j arr_j`, and the cert
   list for the first `j` characters.
3. Epilogue: `store_inv` closes with the grown `h`; `Hctr` reasoning is
   unchanged (heap clock bump already proved).

Watch out (from memory/proof-engineering.md): keep `set_solver` out of the WP
context — all `gset` reasoning is already packaged in §4.4 lemmas; `iInv`
inside the loop needs the mask on the WP (`↑histN ⊆ ⊤` — the triples are at
`⊤`, fine); persistent big-ops across `wp_for` want `iClear`/re-intro care
(see the `#Horigins` note in `iris-big-sep-origin-refactor-gotchas`).

### 6.4 `wp_Text__Delete` (`yjs_text.v:653`)

`ts_arr` is untouched by Delete (tombstone-only), so `history_state_coh` is
*frame-stable*: the proof only destructs and re-frames the new conjuncts.
No minting (§8.1). Estimated: mechanical pass, no new lemmas.

### 6.5 `wp_store__applyUpdate_certs` (new, next to `yjs_store.v:2093`)

```rocq
Lemma wp_store__applyUpdate_certs (s parent : loc) (sl : slice.t)
    (γh : history_names) (c : ClientId) (h : list Ev)
    (arr : list (YjsItem A)) (inputs : list (IntegrateInput (A := A)))
    (Ds : list (gset YjsId)) :
  batch_ok h inputs Ds ->
  {{{ is_pkg_init yjs ∗ is_history γh ∗
      own_client_history γh c h ∗ ⌜history_state_coh h arr⌝ ∗
      ([∗ list] input;D ∈ inputs;Ds, is_op_cert γh (OpInsert input) D) ∗
      is_valid_ytype parent arr ∗ is_update sl inputs }}}
    s @! (go.PointerType yjs.store) @! "applyUpdate" #parent #sl
  {{{ (cells' : list item_cell) (arr' : list (YjsItem A)), RET #();
      is_ytype parent cells' arr' ∗ ⌜YjsArrInvariant arr'⌝ ∗
      own_client_history γh c (h ++ (EvDeliver ∘ OpInsert <$> inputs)) ∗
      ⌜history_state_coh (h ++ (EvDeliver ∘ OpInsert <$> inputs)) arr'⌝ }}}.
```

Proof: `iApply fupd_wp`, `iMod (history_deliver_batch …)` (G3) — this yields
`ValidReplay inputs arr arr'` *before any code runs* — then apply the existing
`wp_store__applyUpdate` **verbatim** and match `arr'` (unique by
determinism/L0). The 80-line existing loop proof is untouched. Note the ghost
history is advanced up front while the heap catches up during the loop; that
is fine because the tie is only re-asserted in the postcondition (the caller —
the locked wrapper in #40 — restores `store_inv` afterwards).

The old `ValidReplay`-based `wp_store__applyUpdate` remains as the internal
composition lemma (it is what the new spec calls); its doc comment should be
updated to say so.

### 6.6 `yjs_doc.v`

`is_Doc` gains `γh` and mirrors the `is_Store` arity change. Nothing else (no
verified Doc methods yet).

---

## 7. Milestones

Each lands independently, `./build.sh` + `GOTOOLCHAIN=go1.26.0 go test ./yjs/`
green, `Print Assumptions` on the new top-level lemmas showing only
goose/Perennial axioms. Suggested PR granularity below follows
`pr-granularity` guidance (each PR has real review value).

| M | contents | deliverables / acceptance | risk |
|---|---|---|---|
| **M0** | iris-yjs: `deliver_locally` fix (§2) — **merged, iris-yjs#24 / lean-yjs#31**; remaining: upstream lemmas L0–L3, L5 if stated model-side; bump `pin-depends` in `cert-yjs.opam` to `b95e6da`+; full rebuild | iris-yjs CI green ✓; cert-yjs `./build.sh` green on the new pin | low (fix landed; L2/L3/L5 are the real work and can trail in a second upstream PR — M1 can start against local pins) |
| **M1** | `yjs_network_model.v`: §4 defs + L4, L6–L10 (+ any of L0–L5 not yet upstream, proved here first and upstreamed later) | file compiles standalone; `certs_ValidReplay` Qed | **highest** — L5 is the one genuinely hard theorem; do it early to de-risk |
| **M2** | `yjs_history.v`: §5 classes, predicates, G1–G4 | compiles; G2/G3 Qed; a smoke lemma: alloc + one broadcast + one remote deliver composed end-to-end (two ghost clients, no WP) proving the ghost story is consistent | low — mechanical given M1 |
| **M3** | `store_inv`/`is_Store`/`is_Text` extension + `store_inv_init` + **Insert minting** + Delete/other call-site rethreading | `wp_Text__Insert` (new post) and `wp_Text__Delete` Qed, axiom-clean | medium — big mechanical rethreading (cf. #29: ~7 call sites then; grep `store_inv`/`is_Store`/`is_Text` uses first and list them in the PR) |
| **M4** | `wp_store__applyUpdate_certs` (§6.5) + doc comments + CLAUDE.md "verified so far" update | Qed, axiom-clean; issue #42 acceptance boxes checkable | low given M2 (thin wrapper) |
| **M5** (stretch, coordinate with #40/#43) | OpDelete minting + delete_range receiver; dynamic client registration; multi-text; delivered-set lower-bound ghost for #40 | — | out of #42 scope; see §8 |

PR slicing: M0 (upstream + pin bump) / M1 / M2+M4-statement / M3 / M4-proof —
or M1+M2 together if M1 lands fast. Avoid a single mega-PR.

---

## 8. Scope decisions (deviations from the issue sketch, with rationale)

### 8.1 `Delete` does not mint (insert-only history)

Issue #42 says "Insert / Delete mint op fragments". Deviation: only `Insert`
mints; `hwf_insert_only` bakes this in.

- The verified `Text.Delete` is a *local visible-index tombstone*; the
  propagated form is `store.delete_range`/the delete set, which is unverified
  (#43, #37) — a Delete certificate would have **no verified consumer**.
- The model's `OpDelete` (`yjs_network.v:24`) carries its own `YjsId` subject
  to the same per-client clock discipline (`histories_UniqueId` quantifies over
  *all* broadcasts), but the Go code does not consume clock on delete — so
  minting Delete ops today would need a ghost-only id scheme that diverges
  from the heap clock. Resolve this together with #43's delete_range design.
- Extension path: drop `hwf_insert_only`, give `OpDelete` ids above the item
  clock (or mirror y-octo's actual delete-set semantics), extend
  `history_state_coh` to also track `st_deleted`, add an `OpDelete` branch to
  L6/L7 (validity is trivial: `IsValidMessage _ (OpDelete _ _) = True`).

### 8.2 Client set fixed at `history_alloc`

Dynamic registration would need `ghost_map_insert` on `hn_hist` with
`c ∉ dom N`, which is unknowable from outside the invariant. OpLib has the
same restriction (per-replica gname lists fixed at init). Extension path: a
"registration token" ghost (auth over the unclaimed-client set) — only worth
it when a verified `NewDoc` exists.

### 8.3 One governed root text per store

The `to_agree` binding (§6.2) makes the single governed text explicit; other
texts of a store are outside the network story (and, with the current
`is_Text`, cannot even be constructed alongside — acceptable because the
verified subset and all tests are single-root-text; #43 tracks multi-type).
Extension path: key histories by `(ClientId, text-name)` and move the binding
into a per-name agreement map.

### 8.4 The history tracks `st_items` only

`history_state_coh` pins the item *sequence*, not tombstone flags — Delete
stays local (8.1), so replicas may disagree on flags while agreeing on the
sequence. #40's convergence statement is therefore about the item sequence.
This matches what the model's `effect_list` on insert-only histories
determines anyway (`st_deleted` stays `∅`).

### 8.5 `batch_ok` is a pure precondition, not code

The Go `applyUpdate` does not check causal order / re-delivery (y-octo's
`UpdateIterator` + state vector do; out of subset, #43). The certificate
design moves *validity* to the sender; *ordering within a batch* remains a
caller obligation, now expressed purely over ids (`batch_ok`) instead of over
receiver state (`ValidReplay`) — strictly weaker to discharge for a caller
that trusts the sender's state vector.

---

## 9. Gotchas / risk register

- **L5 is the crux.** It is the only lemma whose *statement* needed a new
  network discipline (`hwf_self_deliver`). If its proof stalls, check first
  whether `yjs_replay_validity.v` already has a same-client-clock lemma to
  adapt (grep `UniqueId`/`isClockSafe` there; as of `245ada52` all such lemmas
  point the wrong way — from `YjsState_insert = Some` — so a new proof is
  expected).
- **State `HappensBefore` facts over `to_histories` functions, not
  `to_network` records**, or every lemma drags a `history_wf` proof term.
  `HappensBefore`/`locallyOrdered` only need the histories function.
- **`set_solver` inside WP contexts hangs** (see
  `docs/proof-engineering.md`): all `gset`/`gmap` reasoning must stay inside
  §4.4 lemmas; the WP layer only applies them.
- **`iInv` in Perennial-New WPs**: follow `new/proof/own_crash.v`; when
  minting inside `wp_for`, do the fupd adjacent to a concrete step, and mind
  the persistent-big-op re-open clash (`iClear` before `wp_for`, cf.
  `iris-big-sep-origin-refactor-gotchas`).
- **`ghost_map_insert` freshness for `hn_ops`** needs `opid ∉ dom ops`; it
  comes from L4 via `ops_coh` (dom = broadcast ids). Don't try to get it from
  the elem side.
- **Determinism plumbing**: `interpHistory` is relational; L0's determinism
  and append/split lemmas get used constantly — write them first and make them
  `Hint`-friendly (plain rewriting equalities where possible).
- **Pin bump fallout** (M0): the pinned iris-yjs SHA moves across
  `setfii_loop_eq_fii_loop`; if any cert-yjs proof named an admitted constant
  from before, `./build.sh make` will flag it — expected clean, verify.
- **Arity churn** (M3): `store_inv`/`is_Store`/`is_Text` signature changes
  touch every proof in `yjs_text.v`/`yjs_doc.v`; do a grep inventory first and
  land as one mechanical commit separate from the minting logic.

---

## 10. Relation to #40 (what this hands over)

After M4, #40 gets:

- `is_history γh` + `is_op_cert` as the persistent vocabulary to state
  "document = function of the delivered op-set";
- `to_network N wf : YjsOperationNetwork`, so
  `YjsOperationNetwork_converge_final` (`yjs_replay_validity.v:669`) applies to
  the invariant's `N` directly — the convergence theorem is *consumed at the
  ghost boundary, not re-proved*;
- the deliver lemma G3 and `history_state_coh`, from which the locked public
  `ApplyUpdate` wrapper re-establishes `store_inv`;
- one known gap to fill there: a persistent *delivered-set lower bound* per
  replica (e.g. a mono-set ghost beside `hn_hist`) so two replicas can be
  compared without holding both locks — deliberately left out of #42.

The physical network layer (Grove send/recv, the Yjs sync protocol
SyncStep1/SyncStep2/Update, the star-topology server) is specified separately
in `docs/plan-network-sync-protocol.md`; it consumes this design unchanged
(plus the `Hcerts` amendment in §5.2 and a `hwf_dense_clocks` field on
`history_wf` established by G2).
