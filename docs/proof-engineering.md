# Proof-engineering notes (Rocq / ssreflect / Iris / Perennial-New / goose)

Working reference for proving things in this stack — tactics, features, and the
non-obvious gotchas we hit while verifying the Go port of the Yjs/y-octo CRDT.
A living document; verify names against the current libraries before relying on
them, since the APIs drift.

## A. Rocq + ssreflect

- **Rewrite**: `rewrite H1 H2 /def`. Suffixes: `//` = then `done`, `/=` =
  `simpl`, `//=` = both. `-H` rewrites right→left. Occurrence selectors:
  `{1}H` rewrites only occurrence 1, `{2}H`, etc. ssreflect `rewrite H`
  rewrites the first matching subterm **and every syntactically-equal copy** in
  a single pass — so a generalizing rewrite (e.g. `-(take_drop k l)`) can hit
  *all* copies of `l`; constrain it with `{1}`.
- **`have`**: `have H : P. { proof }`, `have H : P by tac`, `have -> : a = b by
  tac` (proves and immediately rewrites with the equation), `have <- : ...`.
- **Intro / elim patterns**: `move=> [a [b c]]`, `[->|Hne]`, `case: x => [|n]`,
  `elim: H => [|c cs IH]`, `last by tac`, `first done`.
- **Deciding**: `case_decide` / `case_bool_decide` split a `decide P` /
  `bool_decide P`. They also reduce that same `decide P` occurrence **inside
  hypotheses**, not only the goal — so a redundant `rewrite (decide_True …) in
  Hx` afterwards fails ("LHS does not match"). Prefer `case_decide` over
  `rewrite decide_True` (the latter needs a proof of `P`; if you use it, supply
  it via `; last lia`).
- **Closed decidable goals**: `done` / `reflexivity` / `vm_compute`. E.g.
  `bool_decide (word.and (W8 2) (W8 2) = W8 0) = false` is closed `by vm_compute`.
- **Arithmetic**: `lia` (nat/Z; handles `Nat.min`/`max` by case analysis);
  `word` for `w64`/`w8` goals including mod-2^n wraparound
  (`word.add (W64 a) (W64 1) = W64 (a + 1)` holds by `word`).
- **Axiom audit**: `Print Assumptions <thm>`. Only standard framework axioms
  (Perennial/goose `type_eq_dec`, `signature_eq_dec`, `into_val_typed_array`,
  Iris/stdpp classical/funext, …) = clean; any project-named axiom or
  `_admitted` constant = an unfinished hole.
- **Handy list lemmas** (stdpp): `take_drop`, `take_drop_middle`, `drop_S`,
  `take_S_r`, `length_app`, `length_take`, `length_drop`, `drop_ge`,
  `lookup_ge_None`(`_2`), `Nat2Z.id`, `last_snoc`, `take_0`/`drop_0`.

## B. Iris proof mode

- Core: `iIntros`, `iDestruct … as "[..]"/"(..)"/%H/#H`, `iFrame "H1 H2"`,
  `iExists`, `iApply`, `iPureIntro`, `iAssert P as %H` (pure — keeps the spatial
  context) / `as "#H"` (persistent).
- A **persistent** hyp named in an `iAssert … with "[… H]"` clause is *moved*
  into the asserted proof, not copied — the outer context loses it (the clause
  treats it spatially). If you still need it (a loop-constant `is_origin_id` for
  the next iteration, say), first `iDestruct "H" as "#H"` to land it in the `□`
  context, then frame the `□` copy.
- **Splitting**: `iSplitL "H1 H2"` gives those hyps to the **left** goal;
  `iSplitR "H1 H2"` gives them to the **right**; a bare `iSplitL` / `iSplitR`
  sends *all* spatial hyps to one side (the other proves a resource-free / pure
  goal).
- **Named conjuncts** `"H" ∷ P` and `iNamed "H"` to introduce by name (Perennial
  uses these heavily in invariant definitions and `wp_if_join` postconditions).
- **Rewriting in proof mode**: a plain Coq `rewrite H` acts on the whole
  `environments.envs_entails Δ Q` sequent — it rewrites the **hypotheses in `Δ`
  too**, not just the goal `Q`. So after a `rewrite H` that sets up a heap
  read/store, the relevant `↦` hypotheses are usually already rewritten; don't
  redundantly `iEval (rewrite H) in "Hx"` (it then fails to match). To rewrite
  *only* a hypothesis, use `iEval (rewrite H) in "Hx"` directly.
- **Affinity**: the logic is affine — unused spatial hypotheses can be dropped
  (`_` in destruct patterns; a leftover `↦` at `Qed`-time is fine).
- `typed_pointsto_not_null : l ↦{dq} v ⊢ ⌜l ≠ null⌝`.
- `set_solver` discharges `gset` goals, but **never run it inside a large WP
  proof** — it does `set_unfold in *` over the whole context and hangs. Extract
  the `gset` fact as a small standalone lemma and `set_solver` there.

## C. Perennial New / goose WP

- Driving: `wp_start as "..."`, `wp_auto` (a cold first call is slow — give the
  interactive checker a generous timeout), `wp_apply (lem with "[$H1 $H2]")`,
  `wp_bind`, `wp_pures`.
- **`wp_if_join asn with "[hyps]"`** joins both branches of an `if` into a
  shared assertion `asn`. It yields three goals: the true branch ⊢ `asn`, the
  false branch ⊢ `asn`, and the continuation with `asn` in hand. The internal
  `wp_if_destruct` auto-runs each branch body using the resources you passed in
  (so a branch whose body needs a not-yet-extracted `↦` is left as a pending WP
  for you to finish). Defined in `perennial/new/golang/theory/auto.v`.
- **Stepping method / builtin calls** (`wp_auto` will not): `wp_method_call`
  (rewrites a `MethodUnfold`; a pointer method loads its receiver to the value
  method), `wp_call` (beta-reduces the resolved `T__mⁱᵐᵖˡ` impl), `wp_func_call`
  (the functions table, e.g. `go.len`). Nested methods need one
  `wp_method_call. wp_call. wp_auto.` cycle per level (e.g. `Item.Len` →
  `Content.Len`). A symbolic word test left by `wp_auto`
  (`#(negb (bool_decide (… = W8 0)))`) is resolved by `rewrite`-ing the known
  field facts to make the operands literal, then
  `rewrite (bool_decide_eq_false_2 …); last by vm_compute` (or `vm_compute`).
- **Joining an `if`'s branches** so a large continuation (a whole loop) is proved
  *once*, not per branch: `wp_if_join (λ v, asn) with "[hyps]"` (the join's arg is
  a `val → iProp` postcondition, not a bare `iProp`). It yields three goals —
  branch₁ ⊢ `asn`, branch₂ ⊢ `asn` (each a *pending WP* if the body still needs an
  `↦` you pass in), and the continuation `∀ v, asn -∗ WP (v ;;; rest)`.
  **Non-obvious gotcha when the `if` is followed by `;;;`** (verified — affects
  this tactic too, not just a manual approach): that `v ;;; rest` is **stuck for
  an abstract `v`** — a goose `if`/`do:` returns `execute_val` (the
  exception-monad "continue" wrapper), *not* `#()`, and `wp_auto` cannot reduce
  `exception_seq (#cont) v`. Pin `v` by making the join postcondition
  `λ v, ⌜v = execute_val⌝ ∗ asn`, then `iIntros (v) "[%Hv HQ]"; subst v` in the
  continuation. (A manual `wp_bind (if …)%E` + `iApply (wp_wand _ _ _
  (λ v, ⌜v = execute_val⌝ ∗ asn))` produces the same three obligations if you want
  finer control.)
- **Persisting a freshly-stored pointer (`↦ → ↦□`) must happen inside the WP.**
  `iPersist` / `pointsto_persist` needs a WP / bupd context; on a bare wand or
  postcondition it fails ("could not eliminate update modality"). So don't let
  `wp_auto` run all the way to the post — step the store explicitly
  (`wp_load. wp_pures. wp_store.`), then
  `iDestruct (typed_pointsto_not_null …) as %Hnn; iPersist "p"`, then `wp_auto`.
  (`wp_store` alone errors "could not find store_ty" until the let-bound value is
  reduced, hence the `wp_pures` first.)
- **A struct-literal constructor** (e.g. goose `newItem`) collapses badly under a
  bare `wp_auto` ("Failed to progress" / pathologically slow). Do one explicit
  `wp_alloc x as "Hx"` for the leading `GoAlloc`, then let `wp_auto` finish.
- **A value-receiver method nested inside an expression** (e.g. `i.Len()` inside
  `id.clock + i.Len() - 1`): `wp_bind` the call to focus it as the whole goal,
  then step / `wp_apply` the helper (after `wp_alloc`-ing the receiver-value copy
  goose introduces).
- **Heap**: `l ↦ v`, `↦□` (persistent / read-only), `StructFieldRef T "f" e`
  for field access; field stores step under `wp_auto` once the `↦` is in scope.
- **Maps** (full support, `perennial/new/golang/theory/map.v`):
  `own_map mref dq (m : gmap K V)`, and `wp_map_insert` / `wp_map_delete` /
  `wp_map_lookup1`,`2` / `wp_map_make1`,`2` / `wp_map_clear` /
  `wp_map_for_range`. Struct keys require a `SafeMapKey` instance.
- **Slices**: `own_slice` / `own_slice_cap`, `slice.len`, and `pure_wp_slice_len`
  (`go.len [SliceType t]` reduces to `slice.len s`).
- **Strings**: `go.len [go.string]` unfolds (`string_len_unfold`, in
  `golang/defn/string.v`) to `InternalStringLen`, which steps to
  `if decide (length s < 2^63) then #(W64 (length s)) else AngelicExit`.
- **Records**: goose structs are RecordSet `Settable`s; `r <| f := v |>` is the
  field update. Projecting a field of such an update does **not** reduce for the
  `eq_refl` *term* — pass a proof obtained by the `reflexivity` / `done` /
  `simpl` *tactic* instead (e.g.
  `have Hf : (r <| f := v |>).f = v by reflexivity` then hand `Hf` to the lemma).

## D. Interactive workflow (rocq-mcp / coq-lsp)

- Iterate proofs against a warm session (`rocq_start` once, then `rocq_check` /
  `rocq_step_multi` from the returned state ids); `rocq_query`
  (`Search`/`Print`/`Check`/`About`/`Locate`) to explore. Compile in full only
  at the end.
- **coq-lsp / Fleche tolerates errors**: a broken `Qed`, or a lemma that
  forward-references something defined later in the file, is flagged but the
  symbol is still made available (treated as admitted) and processing
  continues. So an interactively-green downstream goal does **not** prove the
  upstream lemmas compile. The final gate must be a strict `coqc` / `make` /
  `rocq_compile_file`, which stops at the first real error. (Two such errors in
  this project only surfaced at `coqc`: a `rewrite … decide_True` that needed
  `case_decide`, and a helper placed before the `is_dll_acc` it used.)
- `rocq_check`'s default timeout is low; raise it (e.g. 300s) for heavy tactics
  such as a cold `wp_if_join` or a big `wp_auto`.
- A few tactics flaky-**timeout** in the interactive checker on inputs that are
  trivial for `coqc` — `word` on `word.add (W64 j) (W64 1) = W64 (S j)`, the
  loop-body-entry `wp_auto`. Just retry with a larger `timeout`; they are not
  stuck.
- `Print Assumptions` over a big dependency closure floods thousands of
  "Fetching opaque proofs from disk" lines before the axiom list, overrunning the
  query output buffer. Capture the result via `coqc` on a one-line `.v`
  (`From New.proof Require Import yjs_invariant. Print Assumptions <thm>.`) piped
  through `grep -v "Fetching opaque" | tail`, not the interactive query.

## E. cert-yjs specifics

- **Pipeline**: `yjs/yjs.go` (Go port) → goose → `src/code` + `src/generatedproof`
  (gitignored, never hand-edit) → proofs in `src/proof/`. After editing Go,
  re-run goose or the model is stale.
- **Reuse the rocq-yjs model and order theory** (the installed `yjs.*`
  library): do not invent independent proofs — state cert-yjs WP specs as
  refinements of the pure `integrate` / `setintegrate` model and compose with
  rocq-yjs's invariant/order/commutativity lemmas (`YjsArrInvariant_integrate`,
  `setintegrate_eq_integrate`, `integrate_commutative`,
  `yjs_strong_convergence`, …).
- **Extract algorithmic cores to their own Go functions** (e.g.
  `scanConflicts`, `findIntegrationLeft`) so the hard WP loop is provable in
  isolation, separate from the surrounding pointer surgery.
- **Heap ↔ model isomorphism**: `is_dll` (the doubly-linked spine), `is_ytext` /
  `is_valid_ytext` relate a heap `YText` to a `YjsArrInvariant` model list
  cellwise (by id / content / origin-ids). Heap id-slices (`[]Id`) are
  abstracted to `gset YjsId` via `is_id_set` / `list_to_set`.
- **The `Text.Insert` loop proof** (`wp_Text__Insert`) is a per-character loop
  over the modular `wp_Store__Integrate`. Its invariant tracks `j, arr, cells,
  leftloc, dvj` plus, as pure facts, the **left/right neighbour positions**:
  `Hleftj` (the node at `idx+j-1`, carrying `1 ≤ idx+j` so an origin is never
  wrongly `First`) and `Hrightj` (the right neighbour at `idx+j`, which *shifts*
  to `idx+j+1` after each insert). The loop-constant right origin is threaded as
  a persistent `is_origin_id`, kept *out* of the existential. Each iteration
  places the new item at `p = idx+j` via `insert_straddle`, locates the
  just-inserted cell by id-uniqueness (a trichotomy on its index via
  `getElem_lt_YjsLt'` + `yjs_lt_asymm`), and re-establishes the invariant for
  `j+1`. `item_valid_at` / `toItem_at` dispatch the corner cases (head / middle /
  tail / empty) from which neighbours actually exist; `find_by_id_self` resolves
  an origin id back to its model item.
- **`cell_repr` pins two model simplifications** — `flags' = W8 2` (every cell is
  Countable and non-Deleted, since `Delete` is `//go:build !goose`) and
  `Len() = 1` (every visible char is its own 1-char item, no splitting). Both
  must relax when the verified model gains deletions / multi-clock items (see the
  `TODO` on `cell_repr`); `findPos`/`Indexable`/`LastId` reasoning leans on them.
- **Faithfulness to the source**: match the porting source's data structures —
  a Rust `HashSet`/`HashMap` should become a Go `map` (`map[K]struct{}` for a
  set), a `Vec` a slice. Do not downgrade a set to a `[]slice` for proof
  convenience (map support exists, see §C). Known deviation to revisit:
  `scanConflicts` uses `[]Id` where y-octo's `store.rs` uses `HashSet`.
