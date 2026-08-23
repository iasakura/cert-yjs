# Plan: bring every WP spec onto the spec rules (review of 2026-08-22)

The four spec rules now in CLAUDE.md (Spec shape / Specs stay intuitive /
No over-specification / One spec per function) apply to every function,
exported or not. This document is the review of the 80 WP lemmas in
`src/proof` against them, with a verdict per lemma and the target shapes and
migration order. Numbers are from `grep` over the lemma statements on main
at b2c0426.

## 0. Summary

| finding | where | size |
|---|---|---|
| F1 the unlocked store state is written as 3 to 5 raw field points-tos plus an inline `big_sepM` of `own_ytype_cells … ∗ ⌜YjsArrInvariant …⌝` | every `store/*.v` spec except `applyUpdate_certs` and `applyDeleteSpans_store` | 42 specs carry `"items" ↦ mref`, the `big_sepM` appears 45 times |
| F2 goose struct values and their fields in specs | Integrate family, item methods, `is_origin_id`, `item_or_null`, `containsId`, `getNodeIndex`, every spec taking `idv : yjs.id.t` | 20 specs |
| F3 `w64` arithmetic restating a model predicate | `cell_covers` written out 16 times, `cell_fits` 17 times, the same-client max clause 6 times | 25 specs |
| F4 `pool_invs` exists and is inlined instead | 17 specs, and `own_store` / `store_inv_excl` themselves | |
| F5 `doc_registry_coh` exists and is inlined instead | `applyUpdate` (pre and post), `integrateDecoded` x3 (pre and post), `store_inv_excl` | 7 clause sets |
| F6 repeated unnamed clause blocks | integrate readiness (6 premises, 8 specs), cell cursors (4 premises, 8 specs), coordinate provenance (4 specs and 3 transport records), the repair `match` premises | |
| F7 postconditions stating one fact three ways | Integrate family: `arr'` three ways, `cells'` three ways, the new cell in 4 conjuncts | 8 specs, 15 to 17 conjuncts each |
| F8 unused or subsumed spec variants | 21 lemmas | see section 3 |
| F9 specs in the wrong file | `wp_getNodeIndex_total`, `wp_store__GetNode_total` live in `repair.v` | 2 |

The heaviest specs (top-level premises / postcondition conjuncts):
`integrateDecoded_fresh` 22/20, `integrateDecoded_grow` 18/20,
`applyUpdate` 18/23, `integrateDecoded` 17/15, `Integrate_nil_run` 17/17,
`Integrate` 16/17, `Integrate_nil` 16/17, `findIntegrationLeft` 16/5,
`integrateCore_aux` 15/15, `scanConflicts` 14/5, `integrateCore_cells_run`
14/15, `integrateCore_cells` 13/14. Everything above 8 premises is in
`store/`, and all of it is the same five clause blocks (F1, F3 to F6)
pasted into each statement.

After the plan: 80 lemmas become 54 (section 3), no spec has more than 4
top-level premises, and the store internals are stated over one predicate.

## 1. The one interpretation call

"No runtime values" cannot mean "no locations at all": `findPos`,
`scanConflicts`, `splitNode`, `GetNode` return node pointers, and their
callers need to know WHICH node. The rule as codified resolves this with two
model levels, and the review below applies it that way:

- public predicates (`is_Text`, `own_store`, `own_ytype`, `is_Doc`,
  `own_delete_ids`) have the public model: `YjsItem` lists, `DocModel`,
  `gset YjsId`;
- store-internal helpers have the CELL model: `item_cell` (a node's location,
  its run of model items, its tombstone bit, its parent) and `type_state`.
  A pointer is named only as `ic_loc c` / `node_loc cells k` of a model cell.

What is banned at both levels: field points-tos, `yjs.item.t` /
`yjs.updateItem.t` / `yjs.id.t` values and their projections, flag bytes,
and `uint.Z` arithmetic where `cell_covers` / `cell_fits` / `maximalId` say
the same. Perennial's own predicates over a pure model (`s ↦*{dq} (data :
list w8)`, `own_map m dq (bind : gmap P loc)`) are `own_X o dq m` shaped and
are fine on their own; what is not fine is listing several of them next to
the struct fields that hold them instead of one predicate for the structure.

## 2. Findings

### F1. The unlocked store state is not one resource

Every store method spec starts with some subset of

```coq
(s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types ∗
(s .[(yjs.store.t), "types"]) ↦ tref ∗ own_map tref (DfracOwn 1) bind ∗
(s .[(yjs.store.t), "pending"]) ↦ pend_sl ∗ own_update_structs pend_sl (DfracOwn 1) pend ∗
(s .[(yjs.store.t), "pendingDeletes"]) ↦ pdel_sl ∗ own_delete_spans pdel_sl (DfracOwn 1) pdel ∗
([∗ map] parent ↦ ts ∈ types,
    own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
    ⌜YjsArrInvariant (ty_arr ts)⌝)
```

and threads `mref`, `tref`, `pend_sl`, `pdel_sl` as universally quantified
ghosts the caller never cares about. `docs/plan-predicate-refactor.md`
section 1 item 2 already named this defect for `applyUpdate_certs` and fixed
it there with `own_store`; the 41 specs below it were left as they were.

Target: two predicates in `store/heap.v`.

```coq
(** [own_type_pool dq types]: every registered type's DLL at its cell model,
    each satisfying the document invariant. The reader path holds it at a
    fraction; the writer path owns it through [own_store_heap]. *)
Definition own_type_pool (dq : dfrac) (types : gmap loc type_state) : iProp Σ :=
  [∗ map] parent ↦ ts ∈ types,
    own_ytype_cells parent dq (ty_cells ts) (ty_arr ts) ∗ ⌜YjsArrInvariant (ty_arr ts)⌝.

Record store_state := MkStoreState {
  ss_types : gmap loc type_state;                    (* the type pool *)
  ss_bind  : gmap P loc;                             (* the root registry *)
  ss_pending : list (TId * IntegrateInput (A := A)); (* buffered wire items *)
  ss_pending_deletes : list delete_span;             (* buffered delete spans *)
}.

(** [own_store_heap s st]: the store's heap state under the write lock, the
    four struct fields and what they point to, with the pool invariants and
    the registry coherence that every store method preserves. [store_inv_excl]
    is this plus the ghost state. *)
Definition own_store_heap (s : loc) (st : store_state) : iProp Σ :=
  ∃ (items_mref types_mref : loc) (pend_sl pdel_sl : slice.t),
    (s .[(yjs.store.t), "items"]) ↦ items_mref ∗ own_item_map items_mref (DfracOwn 1) st.(ss_types) ∗
    (s .[(yjs.store.t), "types"]) ↦ types_mref ∗ own_map types_mref (DfracOwn 1) st.(ss_bind) ∗
    (s .[(yjs.store.t), "pending"]) ↦ pend_sl ∗ own_update_structs pend_sl (DfracOwn 1) st.(ss_pending) ∗
    (s .[(yjs.store.t), "pendingDeletes"]) ↦ pdel_sl ∗ own_delete_spans pdel_sl (DfracOwn 1) st.(ss_pending_deletes) ∗
    own_type_pool (DfracOwn 1) st.(ss_types) ∗
    ⌜pool_invs st.(ss_types)⌝ ∗ ⌜registry_coh st.(ss_bind) st.(ss_types)⌝.
```

Then every internal store spec is
`{{{ own_store_heap s st ∗ ⌜Pre st⌝ }}} m {{{ st', RET r; own_store_heap s st' ∗ ⌜Post st st' r⌝ }}}`,
`pool_invs` and registry coherence disappear from all pre/postconditions
(they are carried), and `store_inv_excl` / `own_store` become
`own_store_heap` plus the ghost layer.

`own_type_pool` alone is a mechanical change (45 sites, `rewrite
/own_type_pool` where a proof opens it). `own_store_heap` changes the
statement of 41 lemmas and the shape of their proofs' first and last lines.
`Integrate` and `Text.Insert` / `Text.Delete`, which today borrow one
`own_ytype_cells` out of the `big_sepM` and keep the rest framed, keep
doing exactly that behind `own_store_heap` (open, `big_sepM_insert_acc`,
close).

### F2. Goose struct values in specs

| spec | offending parameter or clause | fix |
|---|---|---|
| `wp_scanConflicts`, `wp_findIntegrationLeft`, `wp_Store__integrateCore_aux` | `(itemVal : yjs.item.t) (oleft oright : option yjs.id.t)` in `own_fresh_item_raw item_l input itemVal oleft oright`; `integrateCore_aux` also `itemVal.(left') = …`, `itemVal.(parent') = parent`, `itemVal.(flags') = W8 2`, `1 <= length itemVal.(content').(content')` | `own_fresh_item item_l input` with the struct existential inside (it already is, in `own_linked_item`); the core spec takes `own_linked_item` |
| `wp_item__Len`, `wp_item__Deleted`, `wp_item__Indexable` | `l ↦{dq} v` with `v : yjs.item.t`, results `is_deleted_flag v`, `length v.(content').(content')`, premise `is_countable_flag v = true` | an item-node predicate, F2a below |
| `wp_itemPtrEqual` | `item_or_null pa ova dqa` with `ova : option yjs.item.t`, result `originId_of ova = originId_of ovb` | same predicate; result `bool_decide (oa = ob)` over `option YjsId` |
| `wp_idOptEqual`, `is_origin_id`, `own_fresh_item_raw`, `is_update_item` | `is_origin_id p (oid : option yjs.id.t)` forces `toYjsId <$> oleft = in_originId input` side equations everywhere | `is_origin_id p (oid : option YjsId)` with the `yjs.id.t` cell existential inside; the four `%Hin_l` / `%Hin_r` equations vanish |
| `wp_containsId` | `s ↦*{dq} (vs : list yjs.idSpan.t)` with `Forall span_no_overflow vs`, result over `⋃ (span_ids <$> vs)` | `own_id_set s dq gs` (exists, `store/heap.v`), result `bool_decide (toYjsId id ∈ gs)` |
| `wp_getNodeIndex` (x3) | `sl ↦*{dq} (ic_loc <$> run)` plus `StronglySorted cell_le run`, `∀ c ∈ run, c ∈ all_cells types` | `own_client_run sl dq types client` (the per-client slice `own_item_map` already describes), or state it over `own_item_map` and the client |
| `wp_store__GetNode_*`, `hasNode`, `originArrived`, `splitAtAndGet*`, `containsUpdateItemId`, `splitNode` | `idv.(yjs.id.clientId')`, `uint.Z idv.(yjs.id.clock')`, `W64 (clientId …)` | `toYjsId idv` once, then `cell_covers c (toYjsId idv)` |
| `wp_Id__Add`, `wp_Id__Sub`, `wp_NewId` | `RET #(yjs.id.mk …)` | Add / Sub are unused: delete. `NewId`: `RET r; ⌜toYjsId r = MkYjsId (uint.nat client) (uint.nat clock)⌝` |
| `wp_yType__Text` | `own_ytype_cells`, `visible_string (cells_model cells)` | `own_ytype parent dq m`, `RET #(visible_string m)` |

F2a, the item node predicate. `own_dll_acc` / `own_dll_lookup_acc` /
`own_dll_update_gen` hand out `itemVal : yjs.item.t` with ten pure facts
(`item/heap.v:272-286`), and every caller restates the subset it needs. The
item layer's own model is the wire item plus the tombstone bit and parent:

```coq
(** [own_item_node l dq input deleted parent]: a heap [item] at [l] whose
    id, content and origin ids are [input]'s, tombstoned iff [deleted],
    under [parent]. Its [left'] / [right'] links are positional and belong
    to [own_dll]. *)
Definition own_item_node (l : loc) (dq : dfrac) (input : IntegrateInput (A := A))
    (deleted : bool) (parent : loc) : iProp Σ := ∃ (v : yjs.item.t), l ↦{dq} v ∗ … .
```

`own_dll` holds one per cell at `input_of_run (ic_run c)`,
`own_fresh_item item_l input := own_item_node item_l (DfracOwn 1) input false null`
(links unconstrained), and the three method specs become

```coq
{{{ own_item_node l dq input d p }}} l @! item @! "Len" #()
{{{ RET #(W64 (length (in_content input))); own_item_node l dq input d p }}}
{{{ own_item_node l dq input d p }}} l @! item @! "Deleted" #()   {{{ RET #d; … }}}
{{{ own_item_node l dq input d p }}} l @! item @! "Indexable" #() {{{ RET #(negb d); … }}}
```

(`Indexable`'s `is_countable_flag` premise disappears: every cert-yjs item is
countable, which `own_item_node` pins.) `wp_item__Len` has 17 callers, so
this is a whole-tree change, but each call site gets shorter.

### F3. `w64` arithmetic where the model has the predicate

`cell_covers c d` (`store/value_span.v:62`) is exactly

```coq
cell_client c = idv.(yjs.id.clientId') ∧
(uint.Z (cell_clock c) <= uint.Z idv.(yjs.id.clock'))%Z ∧
(uint.Z idv.(yjs.id.clock') < uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)))%Z
```

at `d = toYjsId idv`, and that triple is written out 16 times
(`GetNode` x2, `getNodeIndex` x3, `splitAtAndGet*` x4, `splitNode`,
`repair_split` x2 in `nat`, `splitAtAndGet*_inv` x2 post). `cell_fits c` is
written out 17 times as `(uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) < 2^64)%Z`,
including inside `pool_invs` itself (`value_cells.v:190`). The per-client
maximality premise of `Integrate` / `integrateDecoded`

```coq
∀ c0, c0 ∈ all_cells types -> cell_client c0 = W64 (clientId (item_id newItem)) ->
  (uint.Z (cell_clock c0) < uint.Z (W64 (clock (item_id newItem))))%Z /\
  (uint.Z (cell_clock c0) + Z.of_nat (length (ic_run c0)) <= uint.Z (W64 (clock (item_id newItem))))%Z
```

appears 6 times and is the cell-level `maximalId`; name it
(`pool_clock_below types id`) and derive it once from `own_store`'s `Hctr`.

### F4. `pool_invs` is inlined

`pool_invs types` (`value_cells.v:189`) bundles loc `NoDup`, range
disjointness, `cell_fits`, `cell_origin_clk`. Its four clauses are pasted as
separate hypotheses in `getNodeIndex` x3, `GetNode_range`, `GetNode_total`,
`hasNode`, `originArrived`, `depsArrived`, `integrateDecoded` x3,
`repair_split`, `splitNode`, `splitAtAndGet*_range` x2, `applyUpdate` (pre
AND post), and as four named conjuncts inside `own_store` and
`store_inv_excl`. With `own_store_heap` (F1) the bundle is carried and no
spec mentions it.

### F5. `doc_registry_coh` is inlined

`doc_registry_coh m bind types` (`value_cells.v:180`) is five clauses. The
five are pasted in `applyUpdate` (pre and post), `integrateDecoded` (three of
five), `integrateDecoded_fresh` / `_grow` (pre and post), and inside
`store_inv_excl` (`Hbindtypes`, `Hbindinj`, `Htypesbound`, `Hmtypes`,
`Hmdom`), while `own_store` uses the name. Worse, the relation is really a
FUNCTION: the last two clauses say `doc_model_get m (RootId nm) = ty_arr
(types !! (bind !! nm))` and `m` is empty elsewhere. Target:

```coq
Definition registry_coh (bind : gmap P loc) (types : gmap loc type_state) : Prop :=
  (∀ nm p, bind !! nm = Some p -> is_Some (types !! p)) ∧
  (∀ n1 n2 p, bind !! n1 = Some p -> bind !! n2 = Some p -> n1 = n2) ∧
  (∀ p, is_Some (types !! p) -> ∃ nm, bind !! nm = Some p).
Definition registry_model (bind : gmap P loc) (types : gmap loc type_state) : DocModel := … .
(* doc_registry_coh m bind types  <->  registry_coh bind types ∧ ∀ t, doc_model_get m t = doc_model_get (registry_model bind types) t *)
```

`registry_coh` lives in `own_store_heap`; the model equation is the one
clause `own_store` adds.

### F6. Repeated unnamed clause blocks

- Integrate readiness, 8 specs, 6 premises each:
  `YjsArrInvariant arr -> toItem input arr = Some newItem -> IsItemValid newItem -> maximalId newItem arr -> findLeftIdx … = Some leftIdx -> findRightIdx … = Some rightIdx`.
  `setintegrate input arr = Some arr'` already implies the last two and is
  the model step the spec should be stated with; the first four are
  `integrate_ready arr input newItem` (one `Definition` in `ytype/model.v`).
- Cell cursors, 8 specs, 4 premises each plus the two `node_loc` arguments:
  `(Z.of_nat (length (run_flatten (take curL cells))) = leftIdx + 1)%Z -> (curL <= length cells)%nat -> … curR … = rightIdx …`.
  This says "`lft` / `rgt` are the cells whose first chars sit at model
  indices `leftIdx + 1` and `rightIdx`", i.e. that the item is linked to its
  resolved origins: one pure predicate `origins_linked cells arr input lft rgt`
  and the `curL` / `curR` binders disappear from the statements.
- Coordinate provenance, 4 specs (`integrateDecoded` x3, `applyUpdate`) as
  a 10-line disjunction, and the same "every new cell's clock range lies in
  an old cell's range" clause as the last conjunct of
  `split_types_update_rel`, `repair_types_update_rel`,
  `delete_types_update_rel`: name it `cells_within before after` (and
  `cells_within_or_from input before after` for the integrate step) in
  `value_cells.v`, then the three transport records share it.
- `wp_store__repair`: four `match` premises on `in_originId input,
  ocL` etc. and two `match` postconditions with 6-conjunct existentials.
  Meaning: "the origin ids of `input` that exist are covered by `ocL` /
  `ocR`; afterwards the item's `left` is the cell ENDING at the left origin
  and its `right` the cell STARTING at the right origin, in the same type".
  Pre: `origins_covered types input ocL ocR`. Post: `own_linked_item item_l
  input p_t lft rgt ∗ ⌜origins_split types2 input lft rgt⌝` with
  `cell_ends_at` / `cell_starts_at` (which also replace the 6-conjunct
  existentials of `splitAtAndGetLeft_inv` / `Right_inv`).
- `wp_Doc__ApplySyncUpdate` / `wp_store__applyUpdate_certs` premises:
  `(∀ typedInput ∈ inputs, clock + length content < 2^64) -> is_pending_rooted inputs ->`
  is `batch_wf inputs`; also fold the no-wrap bound into
  `is_update_item` (it is a property of one wire item, like `Hunonempty`).
- `wp_Text__Insert` post: eight pure conjuncts describing `ins`. The model
  already has the chain constructor (`ops_from client clock originId
  rightOriginId chars`, `item/run_theory.v:1011`), so the post is
  `⌜L' ⊇ L⌝ ∗ ⌜inserted_run L L' ins client k0 originLeft originRight cs⌝`
  (or directly `ins = items_of (ops_from …)`), one predicate in
  `ytype/model.v`.
- `wp_Text__Len` / `wp_Text__String`: `⌜list_to_set L ⊆ list_to_set marr.*1⌝ ∗ ⌜YjsArrInvariant marr.*1⌝`
  plus, in the `_hist` variants, the delivered-ops clause. One
  `text_snapshot L marr` and one `history_reflected h0 name marr`.
- `wp_store__applyDeleteSpans` post: `∃ D, ids_tombstoned D … ∧ ∀ sp ∈ pdel ++ spans, no_overflow sp -> ids sp ⊆ D ∪ batch_ids rest`
  is "every span is tombstoned or still pending": `deletes_accounted (pdel ++ spans) pool' rest`.
- `hasNode` / `originArrived` / `depsArrived` premise
  `∀ d, doc_model_has m d = true <-> ∃ c ∈ all_cells types, cell_covers c d`:
  follows from registry coherence plus `cells_repr`; a lemma
  (`registry_model_has`), not a premise.

### F7. One fact stated three ways

`wp_Store__Integrate` (and the 7 siblings) postcondition:

```coq
⌜arr' = insertIdxIfInBounds midx newItem arr⌝ ∗      (* 1 *)
⌜setintegrate input arr = Some arr'⌝ ∗               (* 1 again *)
⌜arr' = take midx arr ++ newItem :: drop midx arr⌝ ∗ (* 1 again *)
⌜cells' = take idx cells ++ c :: drop idx cells⌝ ∗   (* 2 *)
⌜cells' ≡ₚ cells ++ [c]⌝ ∗ ⌜cells' !! idx = Some c⌝ ∗ (* 2 again, twice *)
⌜ic_loc c = item_l⌝ ∗ ⌜run_head c = newItem⌝ ∗ ⌜ic_deleted c = false⌝ ∗ ⌜cell_unit c⌝  (* 3, in four pieces *)
```

Facts 1 to 3 are: the model took the `setintegrate` step; the cell list got
the unit cell of `newItem` at `item_l` spliced at the cell index matching
`midx`; that is all. Target (the run form; the unit form is the
`length = 1` instance):

```coq
Lemma wp_Store__Integrate (s parent item_l : loc) (st : store_state) (ts : type_state)
    (input : IntegrateInput (A := A)) (lft rgt : loc) :
  st.(ss_types) !! parent = Some ts ->
  {{{ own_store_heap s st ∗ own_linked_item item_l input parent lft rgt ∗
      ⌜origins_linked ts input lft rgt⌝ ∗ ⌜integrate_ready st ts input⌝ }}}
    s @! (go.PointerType yjs.store) @! "Integrate" #parent #item_l
  {{{ (c : item_cell) (arr' : list (YjsItem A)), RET #();
      own_store_heap s (store_integrate st parent c arr') ∗
      ⌜integrate_step ts input item_l c arr'⌝ }}}.
```

where `integrate_step ts input item_l c arr'` packs "`arr'` is the
run-granular `setintegrate` of `input` into `ty_arr ts`, `c = MkItemCell
item_l run false parent` with `run` the resolved chain, spliced at the cell
index of its model index". The `_nil` variants are the same lemma: Go's
`Integrate` reads `item.parent` when `parent == nil` (`store.go:505`), so
`parent` becomes `(if parent = null then ic_parent … else parent)` inside
`own_linked_item`'s parent, or simply the spec is stated for the resolved
parent and the `#null` call site rewrites once.

Other duplicates:

- `integrateDecoded*` / `applyUpdate` post: `dom types ⊆ dom types'` follows
  from `bind ⊆ bind'` and registry coherence; the four pool-invariant
  conjuncts are `pool_invs types'`; both go away under F1.
- `wp_store__applyUpdate_certs` post carries `wire_drain … = (applied, rest, m')`
  AND `ValidReplay (expand_inputs applied) m m'` (derivable from the
  `wire_drain` equation under the spec's own certificate hypotheses:
  `wire_drain_replay` + `WireReplay_to_PendingReplay`, both in
  `applyUpdate.v`) AND `inputs_not_from (expand_inputs applied) c` (a fact
  about certified inputs, not about the function: a lemma on
  `is_pending_certified`) AND `∀ x ∈ inputs, input_accounted …` (the
  no-loss statement; keep, it is the point of the spec) AND
  `is_applied_root_lb`. Keep `wire_drain`, `input_accounted`, the two
  certificates; move the rest to model lemmas in `store/model.v`.
- `wp_Doc__ApplySyncUpdate` / `wp_Doc__ApplyEncodedUpdate`: the binder
  `rest` is existentially introduced and never mentioned (dead); the clause
  `∀ x ∈ expand_inputs applied, ∃ it, item_id it = in_id x.2 ∧ it ∈ doc_model_get m' x.1`
  is the content side of `is_applied_root_lb γs applied m'`: bundle the two
  into `is_applied_certs γs applied m'`, which with `is_history_lb` and the
  `is_accepted` receipts makes the post three conjuncts.
- `wp_store__splitAtAndGet{Left,Right}_inv` post: `∃ cL, cL ∈ all_cells types' ∧ ic_loc cL = ic_loc cw ∧ cell_client cL = … ∧ (uint.Z … = uint.Z idv.(clock') + 1)%Z ∧ ic_parent cL = ic_parent cw ∧ cell_clock cL = cell_clock cw`
  is `cell_ends_at types' (ic_loc cw) (toYjsId idv)` (F6).
- `wp_store__splitNode` post: `⌜rloc ≠ null⌝ ∗ ⌜rloc ∉ ic_loc <$> all_cells types⌝`
  is one `fresh_loc rloc types`; with `own_store_heap` and `split_cells`
  the statement is `own_store_heap s (store_split st parent k o rloc) ∗ ⌜fresh_loc rloc st⌝`.

### F8. Variants (see the table in section 3 for the per-lemma verdict)

| function | specs today | used externally | keep |
|---|---|---|---|
| `store.Integrate` | `Integrate`, `_nil`, `_nil_run` | `Integrate` (Text.Insert), `_nil_run` (integrateDecoded); `_nil` unused | 1 (run form, parent resolved) |
| `store.integrateCore` | `_aux`, `_cells`, `_cells_run` | none (all feed the Integrate proofs) | 1, `#[local]` |
| `getNodeIndex` | plain (`GetNode.v`), `_range` (`GetNode.v`), `_total` (`repair.v`) | plain by `splitNode`, `_range` by `GetNode_range`, `_total` by `GetNode_total` | `_total` (it has the `ok = false` branch; the others are its `ok = true` instance), in `GetNode.v` |
| `store.GetNode` | `_range` (`GetNode.v`), `_total` (`repair.v`) | both | `_total`, in `GetNode.v` |
| `store.splitAtAndGetLeft` / `Right` | `_range`, `_inv` | `_inv` only; `_range` is the stepping stone of `_inv` | `_inv` (renamed to the bare name); `_range` `#[local]` or inlined |
| `store.integrateDecoded` | plain, `_fresh`, `_grow` | plain and `_grow` by `applyUpdate`; `_fresh` by `_grow` | `_grow` (its `bind'` existential covers the hit case), renamed |
| `store.repair` | `_split`, `_create` | `_split` by integrateDecoded, `_create` by `_fresh` | one, with `origins_covered` allowing the no-origin case |
| `store.getOrCreateYType` | hit, `_miss` | both | one: `RET #p; own_store_heap s (registry_get_or_create st nm p) ∗ ⌜bind !! nm = Some p ∨ (bind !! nm = None ∧ fresh_loc p st)⌝` |
| `Text.Len`, `Text.String` | plain, `_hist` | `_hist` only | `_hist`, renamed to the bare name (the plain one is `h0 = []`) |
| `RWMutex.RLock` | `rlock`, `rlock_hist` | `rlock` by Len/String plain (which go), `_hist` by the `_hist` reads | `_hist`, renamed |
| `itemPtrEqual` | `wp_itemPtrEqual` (item), `_self`, `_node` | `_self`, `_node` inside Integrate.v | item-level one over `own_item_node`; `_node` (cell indices) stays as the store-level law; `_self` is a one-line corollary, inline |
| `id.Add`, `id.Sub` | one each | none | delete (the value-layer law `id_add_sub_roundtrip` keeps the arithmetic fact) |

### F9. Placement

`wp_getNodeIndex_total` and `wp_store__GetNode_total` are in `repair.v`
("one exported method's `wp_` per `<Method>.v`"); they belong in
`GetNode.v`, where the two weaker variants they replace already live.

### Specs that already have the right shape

`wp_store__applyUpdate_certs` (modulo F7), `wp_store__applyDeleteSpans_store`,
`wp_Doc__GetOrCreateText`, `wp_NewDoc`, `wp_Text__Delete` (it is
UNDER-specified: no certificate yet, that is the delete-set D2 work, not a
spec defect), `wp_Id__Equal`, `wp_newYType`, `wp_store__deleteRange`
(already `pool_invs` + `delete_types_update_rel` + `ids_tombstoned`; only F1
applies), the six `ws_relay.v` lemmas and the demos (stated over the FFI's
own predicates and the `member` / `room` models; `wp_Room__Join`'s three
field equations pin the connection-facing fields of `member` and leave its
ghost fields existential, which is the right shape).

## 3. Verdict per lemma

R = restate (shape only, same meaning), M = merge into the named survivor,
D = delete, K = keep. "F" columns are the findings that apply.

| file | lemma | verdict | findings |
|---|---|---|---|
| `demo/pingpong.v` | `wp_ServeOnce`, `wp_Ping` | K | |
| `demo/ws_echo.v` | `wp_ServeEcho` | K | |
| `demo/ws_server.v` | `wp_*_initialize'` x3, `wp_server_boot` | K | |
| `doc/ApplyEncodedUpdate.v` | `wp_Doc__ApplyEncodedUpdate` | R | dead `rest`; `is_applied_certs`; `batch_wf` |
| `doc/ApplySyncUpdate.v` | `wp_Doc__ApplySyncUpdate` | R | same |
| `doc/GetOrCreateText.v` | `wp_Doc__GetOrCreateText` | K | |
| `doc/NewDoc.v` | `wp_NewDoc` | K | |
| `id/Add.v` | `wp_Id__Add` | D | unused, F2 |
| `id/Sub.v` | `wp_Id__Sub` | D | unused, F2 |
| `id/Equal.v` | `wp_Id__Equal` | K | |
| `id/wp_private.v` | `wp_NewId` | R | F2 |
| `id/wp_private.v` | `wp_idOptEqual` | R | `is_origin_id` over `option YjsId` |
| `item/Deleted.v`, `Indexable.v`, `Len.v` | `wp_item__*` | R | F2a |
| `item/wp_private.v` | `wp_itemPtrEqual` | R | F2a |
| `store/GetNode.v` | `wp_getNodeIndex` | M → `wp_getNodeIndex` (today `_total`) | F1 F2 F3 F4 |
| `store/GetNode.v` | `wp_getNodeIndex_range` | M | same |
| `store/repair.v` | `wp_getNodeIndex_total` | R, move to `GetNode.v`, rename | same |
| `store/GetNode.v` | `wp_store__GetNode_range` | M → `wp_store__GetNode` | F1 F3 F4 |
| `store/repair.v` | `wp_store__GetNode_total` | R, move, rename | same |
| `store/Integrate.v` | `wp_containsId` | R | F2 (`own_id_set`) |
| `store/Integrate.v` | `wp_itemPtrEqual_self` | D (inline) | |
| `store/Integrate.v` | `wp_itemPtrEqual_node` | K | |
| `store/Integrate.v` | `wp_scanConflicts`, `wp_findIntegrationLeft` | R | F2 F3 F6 (readiness, cursors) |
| `store/Integrate.v` | `wp_Store__integrateCore_aux`, `_cells`, `_cells_run` | M → one `#[local]` `wp_Store__integrateCore` | F2 F6 F7 |
| `store/Integrate.v` | `wp_Store__Integrate`, `_nil`, `_nil_run` | M → `wp_Store__Integrate` | F1 F3 F6 F7 |
| `store/applyUpdate.v` | `wp_store__applyUpdate` | R, `#[local]` (only `_certs` uses it) | F1 F4 F5 F6 F7 |
| `store/applyUpdate.v` | `wp_store__applyUpdate_certs` | R (rename to the bare name once the raw one is local) | F7 |
| `store/deleteRange.v` | `wp_store__deleteNode` | R | F1 |
| `store/deleteRange.v` | `wp_store__deleteRange` | R | F1 |
| `store/deleteRange.v` | `wp_store__applyDeleteSpans` | R | F1 F6 (`deletes_accounted`) |
| `store/deleteRange.v` | `wp_store__applyDeleteSpans_store` | K | |
| `store/repair.v` | `wp_store__getOrCreateYType`, `_miss` | M → one | F1 |
| `store/repair.v` | `wp_store__repair`, `_create` | M → `wp_store__repair` | F1 F3 F4 F6 |
| `store/repair.v` | `wp_store__hasNode`, `originArrived`, `depsArrived` | R | F1 F4 F6 (model premise is a lemma) |
| `store/repair.v` | `wp_containsUpdateItemId` | R (`pending_id_set`) | F2 |
| `store/repair.v` | `wp_store__integrateDecoded`, `_fresh`, `_grow` | M → `wp_store__integrateDecoded` | F1 F3 F4 F5 F6 F7 |
| `store/splitNode.v` | `wp_store__splitNode` | R | F1 F3 F4 F7 |
| `store/splitNode.v` | `wp_store__splitAtAndGet{Left,Right}_range` | M (stepping stone) | |
| `store/splitNode.v` | `wp_store__splitAtAndGet{Left,Right}_inv` | R, rename | F1 F3 F7 |
| `store/wp_private.v` | `wp_Store__wlock`, `wunlock` | R: hand out `∃ c h m pend, own_store …` via `store_inv_own_store` | |
| `store/wp_private.v` | `wp_Store__rlock` | M → `rlock` (today `_hist`) | |
| `store/wp_private.v` | `wp_Store__rlock_hist`, `runlock` | R: `store_inv_ro γs types q` is `own_type_pool q types` plus the auth; name the reader snapshot | F6 (`history_reflected`) |
| `text/Delete.v` | `wp_Text__Delete` | K | |
| `text/Insert.v` | `wp_Text__Insert` | R | F6 (`inserted_run`) |
| `text/Len.v`, `String.v` | plain | D | |
| `text/Len.v`, `String.v` | `_hist` | R, rename | F6 |
| `ws_relay.v` | all six | K | |
| `ytype/Text.v` | `wp_yType__Text` | R | F2 (`own_ytype`) |
| `ytype/findPos.v` | `wp_yType__findPos` | R | F6: `find_pos cells idx = (p, off)` plus the two `node_loc` equations |
| `ytype/newYType.v` | `wp_newYType` | K | |

Count: 80 today; deletions and merges remove 26 (`Id__Add`, `Id__Sub`,
`itemPtrEqual_self`, `Len`/`String` plain, `rlock` plain = 6; merges
`getNodeIndex` 3→1, `GetNode` 2→1, `integrateCore` 3→1, `Integrate` 3→1,
`getOrCreateYType` 2→1, `repair` 2→1, `integrateDecoded` 3→1,
`splitAtAndGet*` 4→2 = 13 removed; the `applyUpdate` raw spec and
`integrateCore` become `#[local]`). 54 remain, two of them local.

## 4. Migration order

Each step is one PR, builds green, and leaves every downstream file
compiling; estimated blast radius is in files.

1. **Name the pool and use the bundles that exist.** `own_type_pool`
   (45 sites), `pool_invs` for its four clauses everywhere including
   `own_store` / `store_inv_excl` (and `cell_fits` inside `pool_invs`),
   `doc_registry_coh` / `registry_coh` + `registry_model` in
   `store_inv_excl` and the `integrateDecoded` / `applyUpdate` statements,
   `cell_covers` / `cell_fits` for the 33 inline copies, `cells_within`
   shared by the three transport records. No meaning changes; every proof
   edit is `rewrite /pred` or `split_and!`. Radius: all of `store/`, ~12
   files.
2. **Drop the variants** (F8): delete the 6 unused, merge the 13, move the
   two `_total` specs to `GetNode.v`, make `applyUpdate` raw and
   `integrateCore` `#[local]`. Radius: `store/`, `text/Len.v`, `String.v`,
   the Insert call site.
3. **`is_origin_id` over `option YjsId`** and the item node predicate
   (F2a): `id/heap.v`, `item/heap.v` (`own_dll` payload and the three
   borrow lemmas), the three `item/*.v` methods, `own_fresh_item` /
   `own_linked_item` / `is_update_item` lose their `%Hin_*` equations.
   Radius: every file that calls `wp_item__Len` (17 sites) or opens a
   borrow.
4. **`own_store_heap` + `store_state`** (F1): restate the 41 internal
   store specs, `store_inv_excl` and `own_store` on top of it. Radius:
   `store/*.v`, `text/Insert.v`, `text/Delete.v`, `doc/GetOrCreateText.v`.
5. **The Integrate family** (F6 + F7): `integrate_ready`,
   `origins_linked`, `integrate_step`; one `wp_Store__Integrate` in the run
   form; `Text.Insert` becomes the length-1 instance. Radius:
   `store/Integrate.v`, `store/repair.v`, `text/Insert.v`.
6. **Repair / split / getNodeIndex** (F6 + F7): `origins_covered`,
   `cell_ends_at` / `cell_starts_at`, `fresh_loc`, `find_pos`. Radius:
   `store/repair.v`, `splitNode.v`, `GetNode.v`, `ytype/findPos.v`.
7. **Public layer** (F6 + F7): `batch_wf`, `is_applied_certs`, dead `rest`,
   `inserted_run`, `text_snapshot` / `history_reflected`, `own_ytype` for
   `yType.Text`, the `applyUpdate_certs` post trimmed to `wire_drain` +
   `input_accounted` + certificates with the rest as model lemmas. Radius:
   `doc/`, `text/`, `ytype/Text.v`, `ws_relay.v` (consumer of the doc specs).

Steps 1 and 2 are mechanical and can go first; 3 and 4 are independent of
each other; 5 to 7 depend on 4.

## 5. Open points for the owner

- The two-level model reading (section 1) is the reviewer's resolution of
  "no runtime values"; if the intent is stricter (no `loc` in any spec),
  the node-returning helpers need an indirection predicate
  (`is_node_at parent p k`) instead, which is more machinery for the same
  information.
- `own_store` exposes `pend` (pending wire items) as model but hides the
  pending delete spans; under `store_state` both are model fields. Whether
  `own_store`'s public signature should grow `pdel` is a public-spec change
  and is left as proposed, not done.
- The old CLAUDE.md bullet also said "one `.v` proof file per Go file";
  that sentence contradicted the Architecture section (one directory per
  type, one `<Method>.v` per exported method) and was dropped with the
  rewrite.

## 6. What was done (2026-08-22)

Steps 1, 2, 4, 5, 6 and 7 are implemented as the stacked PRs #143 to #151
(main <- #143 <- #144 <- #145 <- #146 <- #147 <- #148 <- #149 <- #150 <- #151),
each green under `./build.sh`. Where the realized design differs from the
sections above:

- **F1 footprint.** Realized as planned, under the name `own_store_cells s st`
  (`store/heap.v`): `store_state` (`store/value_cells.v`) is a `RecordSet`
  record of every field at the cell level (`ss_client`, `ss_clock`,
  `ss_types`, `ss_bind`, `ss_pending`, `ss_pending_deletes`), `store_invs st`
  bundles `pool_invs` and `registry_coh`, and `own_store_cells s st` is every
  field (`own_store_fields`) with `store_invs`. Every store-internal method
  (`Integrate`, `GetNode`, `splitNode`, `deleteRange`, `repair`,
  `integrateDecoded`, `getOrCreateYType`, `applyUpdate`, ...) takes it whole
  and returns it at `st <| ss_types := ... |>`; `own_store` is restated on
  top of it. A first version (#147 to #151) had a two-level footprint
  (`own_store_items s types ∗ own_type_pool dq types` for cell surgeries,
  `own_store_core s types bind` for the registry-touching helpers), rejected
  because a method on `s` must take `s`'s predicate whole (CLAUDE.md "Spec
  shape"). No field of the store has a predicate of its own (the former
  `own_store_items` / `own_store_registry` / `own_store_pending` /
  `own_store_pending_deletes` / `own_store_deleted_set` are gone:
  `own_store_fields` spells each field as an anonymous existential), so the
  only store predicate a spec can name is `own_store_cells`. The partial
  footprints survive only in three `#[local]` stepping stones that run while
  the store is open: `wp_Store__Integrate_parts` / `wp_store__AddNode` (the
  parent's cells borrowed out of the pool, the item index raw) and
  `wp_store__deleteNode` (the pool alone).
- **F6 / F7 names.** `integrate_ready`, `origins_linked`, `integrate_splice`,
  `run_denotes`, `pool_clock_below` (Integrate); `pool_cell_covers`,
  `cell_covers_clock`, `sorted_client_run`, `cell_starts_at`, `cell_ends_at`,
  `fresh_loc`, `origins_covered`, `repair_parent`, `origins_split`,
  `find_pos` (lookups, splits, repair); `registry_models`,
  `registry_lookup_or_create`, `cells_within`, `cells_within_or_from`
  (update path); `update_wf` (moved from `yjs_prot`, the `batch_wf` of F6),
  `is_applied_certs`, `inserted_run`, `text_snapshot`, `history_reflected`
  (public layer). `cell_ends_at` carries the parent (the split helpers'
  callers need the node's type); the transport records keep their shape and
  only their last clause is `cells_within`.
- **Kept as they were.** `wp_yType__Text` stays at the cell model: its one
  caller (`Text.String`) must get the same cells back to close the pool, which
  `own_ytype`'s existential would hide. `wp_store__applyUpdate` keeps
  `ValidReplay` next to `wire_drain` (it is the fact the doc layer uses and
  is not derivable by the caller from `wire_drain` alone); `inputs_not_from`
  is dropped (no caller used it). `wp_store__repair` (the former `_split`) is
  the spec of `repair`; the fresh-root form stays local, since a merged
  lemma would have no user.
- **Variants.** `getNodeIndex` 3 -> 1, `GetNode` 2 -> 1, `integrateCore`
  3 -> 1 local, `Integrate` 3 -> 1, `getOrCreateYType` 2 -> 1,
  `integrateDecoded` 3 -> 1 (two local), `splitAtAndGet*` `_inv` renamed
  with `_range` local; `own_linked_item` unit form deleted.
- **Step 3 (F2a, `is_origin_id` over `option YjsId`, `own_item_node`)** is
  not done. It rewrites the per-node payload of `own_dll`, which is exactly
  what the `item_cell` split (`docs/plan-item-run-split.md`) rewrites too, so
  it is folded into that plan's stage 3.
