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
- **Locks (`sync.Mutex`, `New.proof.sync_proof.mutex`)**: `is_Mutex m R`
  (persistent, `R` a fixed invariant), `wp_Mutex__Lock` → `own_Mutex m ∗ R`,
  `wp_Mutex__Unlock` consumes `own_Mutex m ∗ ▷ R` (build the `▷ R` with `iNext`
  then `iExists …; iFrame; iPureIntro`), `init_Mutex` to allocate. `R` must NOT
  mention per-operation state — existentially quantify the mutable bits (model
  list, counter, …) inside `R`. `sync.RWMutex` is far heavier (the guard wrapper
  needs `Fractional P`, which would force fractionalising your whole heap-predicate
  stack; the base RWMutex is logically-atomic) — use `Mutex` unless you genuinely
  need concurrent readers.
- **Calling a method of an *imported* package** (e.g. `sync.Mutex.Lock`) needs
  `is_pkg_init sync`, separate from `is_pkg_init yourpkg`. Supply it by FRAMING the
  spatial premise with `$`: `wp_apply (wp_Mutex__Lock with "[$Hmu]")` — the
  `is_pkg_init sync` then auto-resolves. `with "Hmu"` (no brackets) fails: it tries
  to match the whole `is_pkg_init ∗ is_Mutex` premise against the one hyp. Also,
  embedding `sync.Mutex` in a struct makes *your* package import `sync`, so the
  `IsPkgInit yourpkg := define_is_pkg_init …` instance now needs `IsPkgInit sync` /
  `GetIsPkgInitWf sync` in scope — add `From New.proof.sync_proof Require Import
  base.` in the file that declares it (the required `sync.Assumptions` comes free
  from `yourpkg.Assumptions`'s `import_sync_Assumption ::` field).
- **A Persistent-typed hyp sitting in the SPATIAL context is consumed by `$H`
  framing.** If you Lock then later Unlock with the same `is_Mutex`, move it to the
  `□` context first: `iDestruct "Hmu" as "#Hmu"`. (The type being `Persistent` does
  not save a spatial occurrence from `$`.) Same for any reused `is_Store` / witness.
- **Align goose field reads with your invariant before `wp_apply`**: the body reads
  `(tv.store').[store.t, "mu"]` while your `is_Mutex` is stated at `s_loc.[…]`;
  `subst` the field equality (`s_loc = tv.store'`) so they are syntactically equal.
  Field-ref notation is `l.[(T.t), "field"]` = `struct_field_ref T.t field l`.

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
  (`From New.proof.text Require Import text. Print Assumptions <thm>.`) piped
  through `grep -v "Fetching opaque" | tail`, not the interactive query.
- **`Require` vs `Import` and notation scopes**: `Import`ing `iris.algebra.{auth,
  gmap,gset}` (or `iris.algebra.lib.mra`) at a file's top retunes the `<` scope so
  *already-verified* `word`-arithmetic proofs break (`sint.Z i` re-parsed at
  `nat`). Fix: `Require` (no `Import`) those at the top — loading a module does not
  change scopes — and `Import` them INSIDE the section, AFTER the verified proofs
  and just before the code that needs them (`Import` only affects what follows).
  Pairs with the `Context`-at-end-of-section trick (§A/E): both keep new
  assumptions/notations from disturbing the proofs above.
- **Stale generated `.vo` after goose**: `./build.sh goose` rewrites
  `src/code/*.v` but not its `.vo`; a bare `rocq compile X.v` then links the OLD
  `yjs.vo`. Tell-tale: a proof goal shows a Go call you already deleted, or a field
  that no longer exists. Rebuild the model in dep order with `make
  src/proof/<type>/X.vo` (or `./build.sh make`), not `rocq compile` alone.
- **Developing one big proof inside a big file** with rocq-mcp: position-start does
  NOT land *inside* an `Admitted` proof (returns empty goals / `proof_finished`).
  Instead open a scratch context: `rocq_start(preamble=<all the file's imports>,
  force_restart=true)`, then `rocq_check` a `Section dev. Context … (re-list the
  section's Context vars) … Lemma … Proof. <tactics>` threading the returned
  `state_id`s. `force_restart=true` is essential — a cached preamble silently keeps
  the OLD import set (a new `From … Require Import …` is ignored); verify with
  `Locate` that your names resolve. Batch cheap tactics in one `rocq_check`
  (it returns only the final goal), but run `wp_auto` ALONE with `timeout=90`
  (a batch ending in `wp_auto` overruns the 30s default → "Timeout!"). When the
  branch closes, transplant the tactics into the file replacing the `admit`; final
  gate is still strict `coqc`/`make`.
- `destruct (m !! k) eqn:H` **fails** ("LHS of H does not match any subterm of the
  goal") when `m !! k` occurs only in a *hypothesis*, not the goal. For
  `f <$> (m !! k) = Some y`, use `apply fmap_Some in H as (x & Hk & ->)` instead.

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
- **Heap ↔ model isomorphism**: `own_dll` (the doubly-linked spine) and
  `own_ytype_cells` relate a heap `yType` to a `YjsArrInvariant` model list
  cellwise (by id / content / origin-ids); the public `own_ytype` hides the
  cells behind the model `list (YjsItem A * bool)` (item + tombstone bit). Heap
  id-slices (`[]Id`) are abstracted to `gset YjsId` via `own_id_set` /
  `list_to_set`. Naming: `is_X` = Persistent handle, `own_X` = (dfrac'd)
  ownership (issue #47).
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

## F. Monotone ghost state for a lock invariant (`auth (gmap K (gset V))`)

To put a *growable* per-key resource under a lock invariant so a holder keeps a
**persistent lower bound that also witnesses the key exists** (e.g. "text `parent`
is registered, and at least item-set `S` is present"), use the RA
**`auth (gmap K (gset V))`** — the `auth` wraps the WHOLE map:

- The lock invariant holds `own γ (● m)` (`m : gmap K (gset V)`); a holder keeps a
  persistent fragment `own γ (◯ {[k := S]})`. Combined,
  `own γ (● m) ∗ own γ (◯ {[k := S]}) ⊢ ⌜∃ S', m !! k = Some S' ∧ S ⊆ S'⌝` — i.e.
  **key membership** (registration witness) AND the **subset** lower bound, in one
  ghost. Proof: `own_valid_2` → `auth_both_valid_discrete` (gives `≼` + `✓`) →
  `singleton_included_l` (gives `m !! k ≡ Some S' ∧ Some S ≼ Some S'`) →
  `rewrite Some_included_total in H. rewrite gset_included in H.` (forward), then
  `apply leibniz_equiv in H` for the `≡`→`=`.
- **Nesting matters.** `gmap K (auth (gset V))` (a per-key `auth`) does NOT work: a
  per-key fragment `◯ S` is valid even when the key is *absent*, so it does NOT
  witness membership. Put the `auth` on the outside.
- **`apply lemma in H` picks the wrong direction** of an iff like
  `Some_included_total`/`gset_included` (it re-wraps in `Some`); use
  `rewrite lemma in H` instead.
- **Grow**: `m !! k = Some Sold → Sold ⊆ Snew → own γ (● m) ==∗ own γ (●
  <[k:=Snew]> m) ∗ own γ (◯ {[k:=Snew]})`. Via `own_update` +
  `auth_update_alloc` + `local_update_unital_discrete`; **keep** the validity hyp it
  hands you (`intros z Hvm Hz`, not `_`) — `apply insert_valid` needs it. The frame
  equality is `intros i; rewrite lookup_op; destruct (decide (i=k))` then
  `lookup_insert`/`lookup_singleton` + `-Some_op` + `gset_op` + `set_solver` on the
  `k` case, `lookup_insert_ne`/`lookup_singleton_ne` + `left_id` off-`k`.
- `✓ (m : gmap K A)` does not `intros i`; use `apply insert_valid` (gset values are
  always valid, so the leaf goals are trivial).
- **`iris.algebra.lib.mra`** (the generic monotone RA over an arbitrary preorder —
  what a *subsequence*-ordered monotone list would need) is **absent** from this
  iris pin (only `max_prefix_list` / `mono_list`, i.e. prefix order; subsequences
  aren't a meet-semilattice, so the `max_prefix_list` construction can't be
  reused). You usually don't need it: a grow-only **`gset` of ids** is enough as a
  membership lower bound, and CRDT order is recoverable from the items' origin
  pointers.
- **`gset X` needs `Countable X`.** rocq-yjs gives `Countable YjsId` (basic.v) but
  NOT `Countable (YjsItem A)` (mutually recursive with `YjsPtr`) — track a
  `gset YjsId`, not a `gset (YjsItem A)`.
- **Three-layer handle, lock owns the mutable state**: model y-octo's
  `Arc<RwLock<DocStore>>` as `is_Text → is_Doc → is_Store` where
  `is_Store s γ := is_Mutex (&s.mu) (store_inv s γ)` and `store_inv` (the lock
  invariant) owns the mutable store fields + DLLs + the `● …` ghost (existentially
  hiding the per-op state). Each layer dereferences only its own struct's fields
  and delegates downward (so `is_Text` never mentions store fields); a method like
  `Insert` `Lock`s, pulls its slice out of `store_inv` (a `big_sepM_lookup_acc`
  keyed by the registration witness), works, rebuilds, `Unlock`s.
