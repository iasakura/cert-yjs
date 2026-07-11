# Plan: cohesive predicates for the applyUpdate certificate spec

Target: `wp_store__applyUpdate_certs` (src/proof/yjs_store.v). It is the
top-level verified entry point of the update path (Doc.ApplyUpdate in
codec.go is a thin unverified decode+lock+call wrapper over it), so it should
follow the public-spec rule of CLAUDE.md: no internal data, stated over
`is_X` / `own_X` predicates and their model parameters.

## 1. Problems with the current spec

The current statement (yjs_store.v, `wp_store__applyUpdate_certs`):

```coq
Lemma wp_store__applyUpdate_certs (s : loc) (sl : slice.t) (dq : dfrac)
    (γh : history_names) (c : ClientId) (h : list Ev)
    (inputs : list (TId * IntegrateInput)) (Ds : list (gset YjsId))
    (m : DocM) (types : gmap loc type_state) (bind : gmap P loc)
    (mref tref : loc) :
  batch_ok h inputs Ds ->
  history_state_coh h m ->
  doc_registry_coh m bind types ->
  (∀ i ti, inputs !! i = Some ti -> ∃ nm p, ti.1 = RootId nm /\ bind !! nm = Some p) ->
  (∀ c0, c0 ∈ all_cells types -> (uint.Z (cell_clock c0) + 1 < 2^64)%Z) ->
  (∀ i ti, inputs !! i = Some ti -> (Z.of_nat (clock (in_id ti.2)) + 1 < 2^64)%Z) ->
  {{{ is_pkg_init yjs ∗ is_history γh ∗ own_client_history γh c h ∗
      ([∗ list] ti;D ∈ inputs;Ds, is_op_cert γh (ti.1, OpInsert ti.2) D) ∗
      own_update sl dq inputs ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types ∗
      (s .[(yjs.store.t), "types"]) ↦ tref ∗ own_map tref (DfracOwn 1) bind ∗
      ([∗ map] p ↦ ts ∈ types, own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
                               ⌜YjsArrInvariant (ty_arr ts)⌝) }}}
    s @! (go.PointerType yjs.store) @! "applyUpdate" #sl
  {{{ types' m', RET #();  … the same wall, plus three pure clauses … }}}.
```

Concrete defects, in decreasing order of severity:

1. **Internal data in a top-level spec.** The pre/post name the struct
   fields (`s .[…, "items"] ↦ mref`, `"types" ↦ tref`), the raw registry map
   `bind`, the raw `types : gmap loc type_state`, and `all_cells` /
   `cell_clock` (heap-representation-level W64 projections). All of these
   are `store_inv` internals; the CLAUDE.md rule says a top-level spec must
   not see them.

2. **The store's value state is not one resource.** The store's document
   state is spread over five separate spatial conjuncts (two field
   points-tos, `own_item_map`, `own_map bind`, the `big_sepM` of DLLs) plus
   two loose pure coherence hypotheses (`history_state_coh`,
   `doc_registry_coh`) plus the separately-passed `own_client_history`.
   Callers must thread eight things and four universally-quantified ghosts
   (`types`, `bind`, `mref`, `tref`) that they should never see.

3. **Low cohesion across related facts.** The certificates come as a
   `big_sepL2` against a caller-chosen `Ds` with `batch_ok` as a separate
   pure hypothesis; the "every target root is registered" fact is a raw
   `bind !!` lookup even though the proof layer already has a persistent
   witness for exactly this (`is_type_binding`). Related things are
   scattered instead of named.

4. **The postcondition is too primitive to compose.** It hands back raw
   pure provenance (`∀ c0 ∈ all_cells types', c0 ∈ all_cells types ∨ …`)
   and a new raw `types'`. Worse, the spec does not even thread the
   grow-only item-set authority (`γs.(sn_seq)`, the `Hseq` of `store_inv`),
   so a lock-holding caller cannot re-establish `store_inv` after the call
   without performing the ghost auth update itself from those pure crumbs.
   What a caller actually wants is the monotone, persistent witness of how
   the store grew: fragments (`◯`) of the item-set auth, in the same style
   as `is_type_lb` / `is_op_cert`.

## 2. Target spec

```coq
Lemma wp_store__applyUpdate_certs (s : loc) (sl : slice.t) (dq : dfrac)
    (γs : store_names) (γh : history_names)
    (c : ClientId) (h : list Ev) (m : DocM)
    (inputs : list (TId * IntegrateInput (A := A))) :
  (∀ t x, x ∈ docm_get m t -> (Z.of_nat (clock (item_id x)) + 1 < 2^64)%Z) ->
  (∀ i ti, inputs !! i = Some ti -> (Z.of_nat (clock (in_id ti.2)) + 1 < 2^64)%Z) ->
  {{{ is_pkg_init yjs ∗ is_history (A := A) (P := P) γh ∗
      own_store s γs γh c h m ∗
      own_update sl dq inputs ∗
      is_certified_batch γh h inputs ∗
      ([∗ list] ti ∈ inputs, ∃ nm, ⌜ti.1 = RootId nm⌝ ∗ is_root γs nm) }}}
    s @! (go.PointerType yjs.store) @! "applyUpdate" #sl
  {{{ (m' : DocM), RET #();
      own_store s γs γh c (h ++ (deliver_ev <$> inputs)) m' ∗
      own_update sl dq inputs ∗
      ⌜ValidReplay inputs m m'⌝ ∗
      ([∗ list] ti ∈ inputs, ∃ nm, ⌜ti.1 = RootId nm⌝ ∗
         is_root_lb γs nm (list_to_set (docm_get m' (RootId nm)))) }}}.
```

This is exactly the house shape `{{{ own_X … m ∗ ⌜Pre m⌝ }}} f {{{ own_X … m'
∗ ⌜Post m m' ret⌝ }}}` plus persistent monotone certificates:

- The whole store value state is ONE `own_store s γs γh c h m` before and
  after; `types` / `bind` / field locs are existential inside it.
- The pure precondition is stated over the model `m` only (the no-wrap seam
  moves from `all_cells` / `cell_clock` to `docm_get m` / `clock ∘ item_id`;
  the two are interconvertible via the DLL id-bound pins).
- `ValidReplay inputs m m'` is the entire pure post: it determines the new
  model, replacing the three raw clauses (`history_state_coh` and
  `doc_registry_coh` move inside `own_store`; the `all_cells` provenance
  clause is its heap shadow and becomes derivable).
- The monotone growth witness the caller keeps is `is_root_lb`: a persistent
  auth FRAGMENT of the item-set authority, per touched root, carrying the
  full post-delivery content as a lower bound. Per-item membership certs
  are pure corollaries of it plus `ValidReplay`.

## 3. New predicates

All in yjs_store.v unless noted.

**(a) `own_store`, the cohesive store-state predicate.** Everything the
write lock protects, at model `(c, h, m)`; `store_inv` becomes (or is proved
equivalent to) its model-existential closure.

```coq
Definition own_store (s : loc) (γs : store_names) (γh : history_names)
    (c : ClientId) (h : list Ev) (m : DocM) : iProp Σ :=
  ∃ (client k : w64) (items_mref types_mref : loc) (dset : yjs.deletedSet.t)
    (types : gmap loc type_state) (bind : gmap P loc),
    "%Hclientc" ∷ ⌜uint.nat client = c⌝ ∗
    "Hclient" ∷ (s .[(yjs.store.t), "client"]) ↦ client ∗
    "Hclock"  ∷ (s .[(yjs.store.t), "clock"]) ↦ k ∗
    "Hitemsf" ∷ (s .[(yjs.store.t), "items"]) ↦ items_mref ∗
    "Hitemmap" ∷ own_item_map items_mref (DfracOwn 1) types ∗
    "Htypesf" ∷ (s .[(yjs.store.t), "types"]) ↦ types_mref ∗
    "Htypesmap" ∷ own_map types_mref (DfracOwn 1) bind ∗
    "Hdset"   ∷ (s .[(yjs.store.t), "deletedSet"]) ↦ dset ∗
    "Hseq"    ∷ own γs.(sn_seq) (● ((λ ts, (list_to_set (ty_arr ts) : gset (YjsItem A))) <$> types) : seqUR) ∗
    "Htypes"  ∷ ([∗ map] parent ↦ ts ∈ types,
                   own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
                   ⌜YjsArrInvariant (ty_arr ts)⌝) ∗
    "HtypesAuth" ∷ ghost_map_auth γs.(sn_types) 1 bind ∗
    "#Hbinds" ∷ ([∗ map] name ↦ p ∈ bind, is_type_binding γs.(sn_types) name p) ∗
    "Hhist"   ∷ own_client_history γh c h ∗
    "%Hregcoh" ∷ ⌜doc_registry_coh m bind types⌝ ∗
    "%Hhcoh"  ∷ ⌜history_state_coh h m⌝ ∗
    "%Hctr"   ∷ ⌜∀ t x, x ∈ docm_get m t -> clientId (item_id x) = c ->
                   (clock (item_id x) < uint.nat k)%nat⌝.
```

Notes:

- `doc_registry_coh` (already defined for the current spec) is exactly the
  five registry clauses of `store_inv` (`Hbindtypes`/`Hbindinj`/
  `Htypesbound`/`Hmtypes`/`Hmdom`); `own_store` absorbs it, so `store_inv`'s
  body and `store_inv_excl`'s near-duplicate collapse into one definition.
- The counter clause `Hctr` moves from `types`-level to model level (over
  `docm_get m`); the two are equivalent under `doc_registry_coh`. The
  W64 shadow `Hcellctr` is DERIVABLE from model-level `Hctr` plus the DLL
  id-bound pins (`types_cells_id_bounds` gives `clientId`/`clock < 2^64`,
  so the `W64` projections are exact), and becomes a lemma instead of an
  invariant clause. Insert's loop can still carry it locally.
- No dfrac parameter: `own_store` contains ghost authorities and the
  exclusive history element, so it is exclusive by nature (like
  `own_fresh_item`), consistent with the naming rule.

**(b) `store_inv` in terms of `own_store`.**

```coq
Definition store_inv (s_loc : loc) (γs : store_names) (γh : history_names) : iProp Σ :=
  ∃ c h m, own_store s_loc γs γh c h m.
```

Migration-friendly alternative for the first PR: keep `store_inv`'s current
definition and prove the bridge `store_inv ⊣⊢ ∃ c h m, own_store s γs γh c h m`
(both directions are pure re-grouping plus the `Hctr`/`Hcellctr`
equivalences). Then the RWMutex tie layer (`tie_body`, `store_inv_ro` /
`store_inv_excl`, wlock/rlock proofs) is untouched, and Insert/Delete keep
compiling unchanged. Folding the definition (and deduplicating
`store_inv_excl`) is a follow-up cleanup.

**(c) `is_root`, the persistent root-registration witness.** Replaces the
raw `bind !! nm = Some p` hypothesis (`Hbatchbnd`); mintable wherever the
registry is open (getOrCreateYType hit, Doc.GetText, is_Text).

```coq
Definition is_root (γs : store_names) (name : P) : iProp Σ :=
  ∃ p, is_type_binding γs.(sn_types) name p.
```

**(d) `is_root_lb`, the name-keyed monotone content lower bound.** The
"delivery certificate" of the postcondition: a persistent fragment of the
`sn_seq` authority, lifted from loc-keyed (`is_type_lb`) to name-keyed via
the persistent binding. `S` is a subset of the root's content now and at
all future times (the auth is grow-only).

```coq
Definition is_root_lb (γs : store_names) (name : P) (S : gset (YjsItem A)) : iProp Σ :=
  ∃ p, is_type_binding γs.(sn_types) name p ∗ is_type_lb γs.(sn_seq) p S.
```

`is_Text`'s `#Hbind ∗ His_lb` pair is literally `is_root_lb name
(list_to_set L)`; adopting it there is an optional cohesion follow-up.

**(e) `is_certified_batch` (yjs_history.v, next to `is_op_cert`).** Bundles
the certificates with their coverage fact and hides `Ds` (pure noise for
callers; `big_sepL2` carries the length agreement for free).

```coq
Definition is_certified_batch (γh : history_names) (h : list Ev)
    (inputs : list (TId * IntegrateInput (A := A))) : iProp Σ :=
  ∃ Ds : list (gset YjsId),
    ⌜batch_ok h inputs Ds⌝ ∗
    [∗ list] ti;D ∈ inputs;Ds, is_op_cert γh (ti.1, OpInsert ti.2) D.
```

Persistent (certs are persistent, the rest pure).

## 4. Proof plan

`wp_store__applyUpdate` (the ValidReplay/fields lemma) stays VERBATIM as the
internal composition lemma; only the certificate spec is restated. The new
proof is glue:

1. Unfold `own_store`, destruct `is_certified_batch` (recovering `Ds`,
   `batch_ok`), and for each input combine `is_root` with `HtypesAuth`
   (`ghost_map_lookup`) to recover `Hbatchbnd`'s `bind !! nm = Some p`.
2. Convert the model-level no-wrap hypothesis to the cell-level one via
   `types_repr_all` + `types_cells_id_bounds` + `doc_registry_coh` (every
   pooled cell's item is an item of `m`, and its id components round-trip
   through W64 exactly).
3. Run the existing ghost-first argument (`history_deliver_batch`, then
   `wp_store__applyUpdate`) unchanged.
4. NEW: grow the `sn_seq` authority from `types` to `types'`
   (per touched type, `auth_gmap_gset_grow`; growth of each `ty_arr` as a
   set follows from `ValidReplay`, insert-only), and mint one `is_root_lb`
   fragment per touched root at its new content (same mechanics as
   Insert's lower-bound minting). This also fixes a real composability
   gap: today the spec leaves the auth stale, so `store_inv` could not be
   re-established by a caller without caller-side ghost surgery.
5. Repackage `own_store` at `(c, h ++ deliver_ev <$> inputs, m')`:
   `doc_registry_coh` and `history_state_coh` exactly as in the current
   proof; the counter clause `Hctr` for `m'` needs the one genuinely new
   model lemma:

```coq
(* yjs_network_model.v: a certified, batch_ok batch contains no op authored
   by the receiving client: own broadcasts are self-delivered, so freshness
   against delivered_ids h excludes them. *)
Lemma batch_not_own_client N c h inputs Ds :
  history_wf N -> N !! c = Some h ->
  (∀ i ti D, inputs !! i = Some ti -> Ds !! i = Some D ->
     op_registered N (ti.1, OpInsert ti.2) D) ->
  batch_ok h inputs Ds ->
  ∀ i ti, inputs !! i = Some ti -> clientId (in_id ti.2) ≠ c.
```

   With it, no new item has `clientId = c`, so the clock bound transfers
   from `m` to `m'` (new items come only from the batch, by
   `ValidReplay`).

   Fallback if this lemma fights back (e.g. `history_wf` does not directly
   expose self-delivery): split `own_store` into the doc part and the
   client/clock part, give applyUpdate only the doc part, and leave the
   counter clause to the (future) locking caller. The primary plan is
   preferred: it keeps one predicate and makes the spec lock-shaped
   (`store_inv` in, `store_inv` out, with the model exposed).

## 5. PR plan

- **PR 1 (this refactor):** `is_root`, `is_root_lb`, `is_certified_batch`,
  `own_store`, the `store_inv ⊣⊢ ∃ c h m, own_store` bridge,
  `batch_not_own_client`, restated `wp_store__applyUpdate_certs` with the
  new proof (including the auth growth). No Go changes, no changes to
  Insert/Delete/lock proofs.
- **PR 2 (cleanup, optional):** define `store_inv` via `own_store` and
  deduplicate `store_inv_excl`; adopt `is_root_lb` inside `is_Text`;
  re-thread Insert/Delete over the new named structure.

## 6. Follow-up: vector-clock (state vector) certificates

A second, coarser certificate layer, complementary to `is_root_lb` (not a
replacement): certify the doc's delivered state as a vector clock
`sv : gmap ClientId nat`, and state applyUpdate's effect as the JOIN
(pointwise max, the least upper bound) of the doc's sv and the update's sv.
This is the protocol-native form: y-octo's EncodeStateVector / the sync
protocol (issue #51, branch issue-51: `state_vector_model` / `diff_model`
in yjs_sync.v) already speak sv, and the eventual convergence statement
(issue #40) is naturally "equal sv implies equal doc".

Why it does not REPLACE `is_root_lb`: an sv is id-level and doc-global. It
cannot say which items (contents, origins) are present, nor in which root;
`is_Text`'s content lower bound `L` and the Len/String read API need
item-level knowledge. Keep both granularities.

Ghost structure: nothing new is needed for the PURE statement, because
`own_store` exposes `h` and the sv is a function of it:

```coq
Definition sv_of (h : list Ev) : gmap ClientId nat := …  (* per-client max delivered clock + 1 *)
Definition batch_sv (inputs : list (TId * IntegrateInput)) : gmap ClientId nat := ….
Lemma sv_of_deliver_batch h inputs :  (* max semantics; cheap *)
  sv_of (h ++ (deliver_ev <$> inputs)) = sv_of h ⊔ batch_sv inputs.
```

so the applyUpdate postcondition can gain
`⌜sv_of h' = sv_of h ⊔ batch_sv inputs⌝` for free. The persistent
out-of-lock certificate is one small new CMRA, per replica:
`auth (gmapUR ClientId max_natUR)` (pointwise-max composition; fragments
are persistent lower bounds):

```coq
Definition is_sv_lb (γ : gname) (sv : gmap ClientId nat) : iProp Σ := own γ (◯ …).
```

minted by both `Text.Insert` (own component grows) and `applyUpdate` (the
join), with the auth kept next to `own_client_history` in `own_store`.

**The real prerequisite: gaplessness.** An sv faithfully summarizes the
delivered set only if `delivered_ids h` is per-client downward closed
(`ids_below (sv_of h) = delivered_ids h`). Today the model does NOT
guarantee this: `history_broadcast` only requires the new op's clock to
EXCEED all of the author's prior clocks (the `maximalId` / doc-global
bound), not to be the successor, so an author may skip clocks. The Go code
(and y-octo) allocate consecutive clocks, so this is a faithful model
strengthening, and it is exactly the theorem that makes Yjs state vectors
work at all (an update's per-client contiguous ranges, the pending
mechanism's sv check). Without it, `is_sv_lb` only bounds the per-client
MAX and cannot support diff correctness ("send everything the peer's sv
misses, then the peer has the union").

Staged plan (separate from PR 1/2; the own_store refactor makes each step
a local postcondition extension):

1. Pure sv toolkit: `sv_of`, `batch_sv`, `sv_of_deliver_batch` (max
   semantics), extra pure conjunct in the applyUpdate post. No new ghost.
2. Model strengthening: broadcast requires the successor clock
   (`k = own max + 1`, matching store.clock++), new invariant
   `delivered_downward_closed : history_wf N -> per-client prefix-closed
   (delivered_ids h)` (uses `hwf_self_deliver` on the author side, causal
   coverage of the cert `D` on the receiver side). After this,
   `ids_below (sv_of h) = delivered_ids h`, and an op cert's `D` is
   representable as the author's sv (the wire format of y-octo updates);
   keep the `gset` as the ghost-layer source of truth, sv as the
   compressed interface.
3. The `is_sv_lb` ghost + minting in Insert / applyUpdate. This is the
   interface the issue #51 protocol composition consumes (Step1 sends
   `sv_of h`; Step2's `diff_model` correctness is stated against
   `ids_below`; after apply, the receiver holds `is_sv_lb` at the join).

Caveat for later: the exact join equality is a feature of the verified
no-pending subset. Once the pending buffer (issue #43 territory) exists,
the delivered part still equals the join of what was APPLIED, but an
update may be partially deferred; the spec split (applied vs pending sv)
should be designed then, not now.

## 7. Non-goals / other follow-ups

- A persistent PREFIX lower bound on the history (`mono_list` per client)
  is the analogous refactor for `own_client_history`, and is what a future
  public `Doc.ApplyUpdate` spec needs (the dropped wrapper's "caller does
  not know h" problem). Out of scope here; the store-side certs do not
  depend on it.
- Tombstone/delete-set state is still existential (the history does not
  track flags); `is_root_lb` and `is_sv_lb` are membership bounds, not
  visibility bounds. Unchanged by this refactor.
- The `2^64 - 1` no-wrap seam remains a pure hypothesis, now stated over
  the model.
