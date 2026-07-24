# Aneris op-based CRDT artifact — investigation notes

Study notes on the **OpLib / RcbLib** Aneris development accompanying:

> Abel Nieto, Léon Gondelman, Alban Reynaud, Amin Timany, Lars Birkedal.
> *Modular Verification of Op-Based CRDTs in Separation Logic.*
> OOPSLA 2022, Proc. ACM Program. Lang. 6, Article 188.

Read as a reference point for where cert-yjs could go. **All `path:line`
citations below are into the external Aneris artifact** (the `logsem/aneris`
OpLib development; line numbers verified against the local checkout), not this
repository. Paper citations use the article's page numbers, e.g. `(§5.2,
p.188:17)`.

---

## TL;DR for cert-yjs

- OpLib defines what "done" looks like for an executable op-based CRDT:
  **SEC (convergence + eventual delivery) + functional correctness, modular,
  over runnable code.** That is the natural north-star shape for cert-yjs.
- A new CRDT in OpLib = **one `examples/<crdt>/` directory** (a `*_code.v` and a
  `*_proof.v`) that supplies a *denotation*, an *effect function* (an LTS), and a
  coherence proof. Everything else — network, concurrency, mutation, causal
  broadcast, convergence plumbing — is inherited. The closest existing example to
  a sequence CRDT is `mvreg` (concurrent writes, causality-sensitive).
- Two routes for cert-yjs:
  - **Aneris route**: instantiate OpLib. Cheap, but it would verify a *purely
    functional* Yjs (`setintegrate` over an immutable list), losing the
    imperative-DLL realism that distinguishes cert-yjs.
  - **Perennial/goose route** (current): verify the real imperative Go. Must
    rebuild the RCB / network layer (RcbLib is ~5.6k LOC of Coq here) or assume
    causal delivery for a first result. The RA toolkit it needs all exists in
    Perennial; the cost is proofs, not cameras.
- Key reused fact: **`cc_subseteq` — the preorder of OpLib's monotone snapshot
  RA — is exactly "subset + causally closed", i.e. the `hbClosed`/`IdNoDup`
  well-formedness that is cert-yjs's bridge obligation.** Aneris ships the RA for
  it; a Perennial build would construct an equivalent monotone RA.

---

## 1. Artifact layout — a two-library tower

The development is the `aneris/examples/{rcb,crdt}` subtree of a stripped-down
Aneris monorepo (Trillium ⊃ Aneris). Programs are written in an **OCaml subset →
translated to AnerisLang by `o2a`** (`*_code.v`), then proved.

### RcbLib — `aneris/examples/rcb/` (~5.6k LOC Coq)

Reliable causal broadcast over UDP. The directory structure mirrors the paper's
recipe (§4.3, p.188:13): *model as a state-transition system → embed via ghost
theory → global invariant → implementation meets spec*.

| dir | role |
|---|---|
| `rcb_code.v` | AnerisLang code (from `rcb_code.ml`) |
| `model/` | abstract STS: `model_gst` (global state), `model_lhst` (local history), `model_lst`, `model_lsec`, + `model_update_*` (transition relations) |
| `resources/` | ghost resources: `resources_global` (**OwnGlobal**), `resources_global_inv` (the **RcbInv / global invariant**), `resources_lhst` (**OwnLocal**), `resources_local_inv` |
| `spec/` | client-facing abstract spec (broadcast / deliver, the paper's Fig 4) |
| `proof/` | implementation meets spec: `proof_of_{broadcast,deliver,init,network}` |
| `instantiation/` | instantiate the abstract spec with the concrete model |
| `examples/broadcast_1_2/` | 2-replica example + `adequacy.v` (a closed theorem) |

### CRDT generic framework — `aneris/examples/crdt/spec/` (~380 LOC)

CRDT-agnostic vocabulary:

- `crdt_denot.v` — the **denotation** `⟦ s ⟧ ⇝ st`:
  `Class CrdtDenot { crdt_denot : Rel2 (gset (Event Op)) St; crdt_denot_fun }`
  (`crdt_denot.v:25`). A denotation is a *functional relation from a set of
  events to a state* — the paper's `⟦·⟧ : 𝒫(Event) → St` partial function
  (§5.2, p.188:17). Order-independence is structural: the input is a *set*.
- `crdt_resources.v` — the abstract **`CRDT_Res_Mixin`**: `GlobInv`,
  `GlobState`/`GlobSnap`, `LocState`/`LocSnap`, and their laws (Exclusive,
  Persistent, TakeSnap, Union, Included, …).
- `crdt_events.v`, `crdt_time.v` — events (op + vector clock + origin) and
  causal order; `causally_closed` / `causally_closed_subseteq` live here.

### OpLib — `aneris/examples/crdt/oplib/`

- `spec/model.v` — the LTS and its coherence:
  - `Class OpCrdtEffectCoh (effect : St → Event Op → St → Prop)` (`model.v:15`)
    is the **denotation/LTS coherence** (paper Fig 11). Its own comment:
    *"This is where causality shows up in one [of] the assumptions of
    coherence."*
  - `Class OpCrdtModel { op_crdtM_effect; op_crdtM_effect_coh;
    op_crdtM_init_st_coh : ⟦∅⟧ ⇝ op_crdtM_init_st }` (`model.v:36`). **This is
    exactly what a CRDT author fills in.**
- `spec/spec.v` — client API: `get_state_spec` (`:73`), `update_spec` (`:83`)
  (logically-atomic, namespace `↑CRDT_InvName` = the paper's "N contains the
  global invariant's name"), `effect_spec` (`:104`), `init_st_fn_spec`,
  `crdt_pair_spec` (the `(init_st, effect)` pair).
- `proof/` (~3.3k LOC) — `oplib_proof.v` (the main proof: the lock invariant
  *"state = denotation of the processed set"*), `resources.v` (RAs, below),
  `params.v`, `time.v`.
- `examples/` (~4.5k LOC, 13 dirs) — the 12 CRDTs + one closed use-case.
  Per-CRDT cost is tiny (counter ~260 LOC; the compound *table-of-X* CRDTs are
  ~100 LOC because they reuse the map combinator). **No sequence/text/RGA/YATA
  CRDT exists** — the hard class the paper lacks, and cert-yjs's opening.

---

## 2. The recipe: what a CRDT author actually provides

Per the paper (§5, p.188:8) and `model.v`, a CRDT instance supplies:

1. a **denotation** `⟦·⟧` (a Coq function on sets of events);
2. an **effect / LTS** (`op_crdtM_effect`, one-operation transition);
3. **coherence** `OpCrdtEffectCoh` + `⟦∅⟧ ⇝ init` (Coq, meta-level);
4. an **`EffectSpec`** Hoare triple: the executable effect refines the LTS step.

Steps 1–3 are meta-level Coq; only step 4 is in separation logic. A Yjs instance
would be one new `examples/yjs/` dir reusing all of `crdt/spec`, `crdt/oplib`,
and `rcb`, with the single nontrivial obligation being `OpCrdtEffectCoh` for
`integrate` — which reduces to rocq-yjs's `hb_consistent_effect_convergent` plus
the causal-closure bridge.

---

## 3. Where convergence and commutativity live

This dissolves the recurring confusion "how is convergence shown, and where does
the user prove commutativity?".

- **Convergence is near-definitional.** The denotation is a function of a *set*
  (§3.2, p.188:7), so it is order-independent by construction. `get_state`
  returns `⟦delivered set⟧` (its spec), so two replicas with the same delivered
  set return the same value. Done.
- **The user never proves pairwise commutativity** (`∀ a b. f a (f b s) = f b
  (f a s)`). The obligation is the coherence equation
  `Valid(s,e) ∧ ⟦s⟧=p ∧ p →ᵉ p' ⟹ ⟦s∪{e}⟧=p'` (Fig 11, p.188:19) — "incremental
  effect = recomputing the set denotation". Commutativity is *dissolved* into
  this single equation.
- **`Valid(s,e)`** (e ∉ s, e ∈ Maximals(s∪{e}), …) is supplied by causal
  broadcast (§5, p.188:19). For Yjs it means *the origins of an inserted item are
  already delivered* — the precondition that makes `integrate` well-defined.
- **The actual mechanical proof** is a lock invariant *"physical state =
  ⟦processed set⟧"* (§5.3, p.188:20), re-established at every effect step.
- **For Yjs specifically, the hard part is already done in rocq-yjs**
  (`hb_consistent_effect_convergent`, `integrate_commutative`). cert-yjs reuses
  it; the residual obligation is bridging the generic broadcast `Valid` to Yjs's
  structural well-formedness (origins resolvable / causal closure).

---

## 4. Network & language semantics: AnerisLang vs GooseLang/Grove

The two stacks make opposite design choices. (Grove citations are into
`mit-pdos/perennial`, `src/goose_lang/ffi/grove_ffi/`.)

### Source language and how programs enter the logic

| | AnerisLang | GooseLang |
|---|---|---|
| source | **OCaml subset** → `o2a` | **real Go** → `goose` |
| IR | bespoke HeapLang-style untyped λ-calculus | models Go faithfully (structs/slices/maps/typed memory) |
| memory | flat values, `ℓ ↦[ip] v` | Go's structured/typed memory |

Both have a trusted source→IR translator. Aneris targets a clean re-implementation
in idealized OCaml; goose targets the **actual deployed Go**. AnerisLang *has*
per-node heap mutation and `Fork`, so it is not "purely functional"; the realism
gap is fidelity to a real language's memory model and real source code.

### Where "distributed" lives

- **Aneris: distribution is primitive in the core.** State is
  `gmap ip_address (heap × sockets)` plus one global message soup
  (`lang.v:708`). Every WP / points-to is node-annotated.
- **Grove: single-node concurrency is the core; network is an FFI add-on.**
  The global network is `grove_net : gmap endpoint (gset message)` in an
  `ffi_global_state` (`impl.v:84`). Nodes are separate GooseLang programs sharing
  that FFI state.

### Network model (the most informative difference)

| axis | Aneris | Grove |
|---|---|---|
| global net state | `state_ms : gmultiset message` (one soup) | `grove_net : gmap endpoint (gset message)` (per-endpoint) |
| multiplicity | **multiset** (counts duplicates) | **set** (duplicates collapse) |
| send | atomic node step; `{[+ m +]} ⊎ M` (`lang.v:780`) | atomic FFI step; `ms ∪ {[Message …]}` (`impl.v:154`) |
| receive | from node-local **socket buffer** (`lang.v:795`) | samples the **global set directly** (`impl.v:163`) |
| delivery | **separate `config_step`**: soup → buffer, soup unchanged ⇒ dup (`lang.v:982`); `MessageDropStep` ⇒ loss (`lang.v:995`) | none — receive *is* the sampling |
| addressing | UDP datagram, socket_address | endpoint u64 + connection 4-tuple (TCP-ish) |

**The structural difference is step count.** Aneris models **send / deliver /
receive as three steps** (a scheduler `config_step` delivers asynchronously),
making network asynchrony explicit — which is *why causal broadcast is a real
theorem* (RcbLib must reorder the soup into causal order). Grove collapses to
**two steps** (send → set, receive samples set) using set semantics, no buffer or
scheduler. Both make the network op a single **atomic** step
(`wp_GroveOp` wraps it in `|NC={E}=>`, `grove_ffi.v:153`), so the "global
message structure updated atomically" pattern holds in both.

### Spec-level abstraction

- **Aneris** hides the network behind **socket protocols** `sa ⤇ φ` + a
  message-history ghost theory; RcbLib's `OwnLocal`/`OwnGlobal` sit on top.
- **Grove** exposes a raw `gen_heap` points-to `c c↦ ms` (`grove_ffi.v:75`,
  `DfracOwn 1`) with **ordinary Hoare-triple** specs `wp_SendOp`/`wp_RecvOp`
  (`grove_ffi.v:231`/`:246`). To get the "global set in an invariant" pattern you
  put `c↦` in a shared invariant and open it around the atomic op yourself.

---

## 5. Resource algebras behind GlobSt / LocSt

Three RA idioms (plus a one-shot), used across two layers.

### The three idioms

| idiom | RA | symbols | guarantee |
|---|---|---|---|
| **frac⊗agree** | `prodR fracR (agreeR (gsetO E))` | `(q, to_agree S)` | exact value (agree forces all holders equal) + exclusive update (need full fraction = 1) |
| **auth-gset** | `authUR (gsetUR E)` | `● S` / `◯ T` | persistent lower-bound snapshot (`◯` ⊆ `●`, mergeable, copyable) |
| **monotone** | `authUR (monotoneUR cc_subseteq)` | `● princ_ev S` / `◯ princ_ev T` | **causally-closed** lower bound; only grows along `cc_subseteq` |

`agree` and `auth` are **distinct RAs**. `●`/`◯` belong to `auth`; `to_agree`
belongs to `agree`. They are combined, not the same thing.

The monotone preorder (`oplib/spec/events.v:14,28`):

```coq
cc_impl s s'    := ∀ e e', e∈s' → e'∈s' → e ≤_t e' → e'∈s → e∈s.  (* causally down-closed in s' *)
cc_subseteq s s' := s ⊆ s' ∧ cc_impl s s'.                          (* subset + causal closure *)
```

**`cc_subseteq` is exactly the `hbClosed` (causal closure) structure.** The
monotone RA tracks "the delivered set grows while staying causally closed".

### Resource → RA map

| resource | layer | RA | role |
|---|---|---|---|
| `OwnGlobal(h)` | RcbLib | frac⊗agree (over `global_event`) | exact/exclusive broadcast set |
| `OwnGlobalSnapshot(h)` | RcbLib | auth-gset | persistent lower bound |
| `OwnLocal(i,s)` | RcbLib | frac⊗agree (over `local_event`) | exact/exclusive delivered set |
| `GlobSt(h)` | OpLib | frac⊗agree (over `Event`) | exact global CRDT-event set |
| `GlobSnap(h)` | OpLib | auth-gset (rides on `OwnGlobalSnapshot`) | persistent lower bound |
| `LocSt(i,own,for)` | OpLib | frac⊗agree ×2 (own, foreign) + carried monotone snap | exact local state |
| `LocSnap(i,own,for)` | OpLib | monotone over `cc_subseteq` (`◯`) | persistent causally-closed lower bound |

Sources: `rcb/resources/base.v:31` (`internal_RCBG`),
`rcb/resources/resources_global.v:26` (`own_global_user`/`_sys`),
`oplib/proof/resources.v:18` (`Internal_OpLibG`), `:261`/`:265`/`:299`/`:314`
(the OpLib resource bodies), `:1367` (`oplib_res : CRDT_Res_Mixin` — wires each
abstract field/law to a concrete body/lemma).

> `OwnGlobal` and `OwnLocal` use the **same RA shape** (frac⊗agree) but over
> **different element types** (`global_event` vs `local_event`) — distinct `inG`
> instances, distinct ghost names. The two event types differ because local and
> global events are represented differently; the global form is the *erasure*
> `⌊a⌋` of the local one (§4.2 footnote, p.188:12).

### Two layers, one bridge

`GlobSt` (OpLib, CRDT events) and `OwnGlobal` (RcbLib, raw events) are tied
inside the OpLib **global invariant** by a coherence predicate
(`glob_st_set_coh`): `OwnGlobal s ∗ (a fraction of GlobSt h) ∗ ⌜s ↔ h coherent⌝`.
RcbLib = the raw network message set; OpLib = the CRDT-meaning event set; the
invariant translates between them.

### Why frac⊗agree *and* a separate snapshot RA

For a tracked set there are two parallel cells: frac⊗agree gives the **exact,
update-locked** value (no one changes it without combining all fractions); the
auth/monotone gives a **persistent, copyable lower-bound certificate** that
survives growth. The snapshot `◯` is bundled into the user resource so a snapshot
can be taken **without opening the invariant** (`resources_global.v:29` comment).
A `◯` lower bound *can* be outrun by the `●` holder (the set grows past it);
the frac⊗agree value *cannot* be changed by any single party.

---

## 6. Ghost-name structure & the global invariant

The gname count is large but regular: **kind × replica × view**.

- **kinds** (OpLib): `γ_glob` (global, 1), and per-replica `γ_own`, `γ_for`,
  `γ_sub`, `γ_cc`, `γ_inv` (`OpLib_InvGhostNames`, `resources.v:49`) → `1 + 5N`
  for N replicas; RcbLib adds its own. Per-replica families are *lists* of
  gnames, one per replica.
- **views** (the non-obvious third axis): the *same* set is held in up to three
  places that must agree — the **user** logical view (in get_state/update specs),
  the **lock**-protected physical state (what the apply-thread mutates), and the
  **global invariant**. Fractions/separate-gnames force agreement at sync points.
  - `γ_own` is split 1/3 user + 1/3 lock + 1/3 invariant (three-way).
  - foreign uses **two gnames**: `γ_sub` = foreign as seen in the *user* view
    (`oplib_loc_st_user`, `resources.v:314`, fraction 2/3); `γ_for` = the *same*
    foreign set in the *lock* view (`oplib_loc_st_lock`, `:333`, fraction 1/2).
    Separate gnames let the logical and physical views diverge temporarily and be
    reconciled by the invariant.

**Fractions are update-authority tokens, not data shares.** `agree` already
shares the exact value to every holder for free; the fraction only controls who
may update (need 1) and forbids two full copies. Hence **no `1/N`**: the N
replicas do not durably co-own the global cell — they *borrow* it transiently by
opening the shared invariant at their atomic broadcast/deliver step (the
logically-atomic design). The global cell is split only among the few durable
holders (a user/system handle + the invariant). N-independence is deliberate:
`1/N` would break on replica join and require gathering all N pieces to update.

**The global invariant** (RcbInv, §4.2, p.188:11) states, over the
agree-mirrored values:

- `h = ⨄ᵢ (replica i's own/generated events)` — every event has exactly one
  originator, so it is effectively a *disjoint* union; foreign sets are
  re-deliveries (`foreignᵢ ⊆ ⋃_{j≠i} ownⱼ`). Both "union of own" and "union of
  full local states" equal `h`.
- each local set is **causally closed** (the `● princ_ev` over `cc_subseteq`);
- **cross-layer coherence** (OpLib events ↔ RcbLib events).

It is not active polling: `agree`/`●` keep the invariant's recorded value equal
to each node's real value, the invariant asserts the pure relation above, and
**every update must re-establish it to close the invariant** — that proof
obligation *is* the event-consistency check. This `h = ⋃ locals` + causally
closed + unique-ids invariant is precisely the `IdNoDup`/`hbClosed`
well-formedness that earlier cert-yjs notes identified as the bridge needed for
convergence.

---

## 7. Implications for cert-yjs

- **`cc_subseteq` = `hbClosed`/`IdNoDup`.** The structural obligation we flagged
  for cert-yjs is, in OpLib, the preorder of an off-the-shelf monotone RA. The
  Aneris route inherits it; a Perennial route builds an equivalent monotone RA
  (Perennial/Iris ship `mono_list`, `mono_nat`, and a generic monotone
  construction).
- **The RA toolkit is not Aneris-specific.** frac⊗agree, auth-gset, monotone,
  one-shot all exist in Perennial. Porting the resource *layer* is mechanical;
  the cost is the proofs (coherence + the lock/global invariants), not the
  cameras.
- **A Perennial rebuild can be leaner.** OpLib's `1 + 5N` gname grid reflects a
  full user/lock/invariant split; a design that does not separate the user and
  lock views could collapse `γ_sub`/`γ_for` and shrink the grid.
- **The real cost remains the RCB / network layer.** Grove gives an atomic,
  set-based, unreliable per-endpoint mailbox (`c↦ ms`) — comparable raw power to
  AnerisLang's soup, but *without* RcbLib's causal-broadcast library or the
  socket-protocol abstraction. cert-yjs would build causal delivery on `c↦`, or
  assume it for a first convergence result (as most prior op-based CRDT
  verification did).
- **Realism is the differentiator.** goose verifies the real imperative Go (the
  mutable DLL); AnerisLang verifies idealized OCaml. Combined with a sequence
  CRDT (absent from the paper), that is cert-yjs's contribution over OpLib —
  exactly the part OpLib abstracts away.
