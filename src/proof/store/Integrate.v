(** WP proofs for the [store] integration stack: the id-lookup helpers
    ([containsId] / [findById] / [itemPtrEqual]), the conflict scan
    ([scanConflicts] / [findIntegrationLeft]) refining [set_find_integration_loop] (the
    splice lands at the pure [setfindIntegratedIndex] and the result inherits
    [YjsArrInvariant] from [YjsArrInvariant_integrate]), the item-validity /
    insertion helper lemmas ([item_valid_*], [insert_*], [toItem_at]), and the
    top-level [Store.Integrate] (cells-level and model-level, including the
    per-client item-map maintenance), and its run-granular derived form
    [wp_store__Integrate_runs] (over [own_store_runs], splicing the run and
    the fresh address at one shared cursor).

    Split out of [store/heap] (the predicates and the lock layer) so
    these heavy loop proofs compile in their own [.vo]; the update path
    continues in [store/applyUpdate], and downstream files see everything
    through the [store/store] facade. Same [Section] boilerplate; [Type*]
    footprints. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core.
From New.proof.item Require Import run_theory model value heap.
From New.proof Require Import prelude.
From New.proof.id Require Import id.
From New.proof.item Require Import item.
From New.proof.ytype Require Import ytype.
From New.proof Require Import history.
From New.proof.store Require Import model value heap.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
From iris.algebra Require Import auth gmap gset.
From stdpp Require Import sorting.

(* iris.algebra / stdpp.sorting push [nat_scope], retuning the default [<] / [≤].
   The verified WP proofs write [Z] comparisons (e.g. [sint.Z i < …]) unannotated
   and annotate [nat] ones with [%nat], so restore [Z_scope] as the default. *)
Local Open Scope Z_scope.

(** Small-context set rewrites for the conflict-scan accumulators. After a Go
    [append] of the conflict id, an id slice abstracts to [X ∪ ({[a]} ∪ ∅)] (the
    trailing [∅] is [list_to_set []] from the singleton tail); these relate that
    to the [set_find_integration_loop] accumulator form [{[a]} ∪ X]. Proving them as standalone
    lemmas keeps [set_solver] on a tiny context — calling [set_solver] inside
    [wp_scanConflicts] instead does [set_unfold in *] over the whole proof state
    (including the [list_to_set] slice hypotheses) and is prohibitively slow.

    They live at top level (outside [Section store]): [set_solver] runs
    [set_unfold in *], which would otherwise pull the heap section variables into
    the proof term and force them into the lemma's [Proof using] footprint. Only
    this module uses them, so they sit here rather than in [prelude]. *)
Lemma gset_union_singleton_swap (X : gset YjsId) (a : YjsId) :
  (X ∪ ({[a]} ∪ ∅) : gset YjsId) = {[a]} ∪ X.
Proof. set_solver. Qed.

Lemma gset_elem_union_singleton_swap (X : gset YjsId) (a b : YjsId) :
  b ∈ ({[a]} ∪ X) -> b ∈ (X ∪ ({[a]} ∪ ∅) : gset YjsId).
Proof. set_solver. Qed.

Lemma gset_not_elem_union_singleton_swap (X : gset YjsId) (a b : YjsId) :
  b ∉ ({[a]} ∪ X) -> b ∉ (X ∪ ({[a]} ∪ ∅) : gset YjsId).
Proof. set_solver. Qed.

Section store_integrate.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.
Notation P := go_string.
Local Notation TId := (TypeId P).
Local Notation Op := (TId * @YjsOperation A)%type.
Local Notation Ev := (@Event Op).
Local Notation DocModel := (gmap TId (list (YjsItem A))).

(* The heap-layer extraction lemmas ([own_type_pool_id_bounds] and kin) and
   [own_store_struct_intro] abstract over [store/heap]'s ghost instances;
   declare them so the run-granular derivation can invoke those lemmas
   (the same three [store/splitNode] declares). *)
Context {seq_inG : inG Σ (authR (gmapUR loc (gsetUR (YjsItem A))))}.
Context {acc_inG : inG Σ (authR (gsetUR YjsId))}.
Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO (gmap loc type_state)))}.

(** [containsId] decides membership of the span slice's char-id set (issue #28:
    an id addresses any char of a scanned run, so the Go test is a clock-range
    test; [span_no_overflow] makes its [w64] [clock + len] exact). *)
Lemma wp_containsId (s : slice.t) (vs : list yjs.idSpan.t) (id : yjs.id.t) (dq : dfrac) :
  Forall span_no_overflow vs ->
  {{{ is_pkg_init yjs ∗ s ↦*{dq} vs }}}
    @! yjs.containsId #s #id
  {{{ RET #(bool_decide (toYjsId id ∈ ⋃ (span_ids <$> vs)));
      s ↦*{dq} vs }}}.
Proof.
  move=> Hwfs.
  wp_start as "Hs". wp_auto.
  iAssert (∃ (i : w64) (xv : yjs.idSpan.t),
    "Hi" ∷ i_ptr ↦ i ∗ "Hx" ∷ x_ptr ↦ xv ∗ "Hs" ∷ s ↦*{dq} vs ∗
    "%Hib" ∷ ⌜(0 ≤ uint.Z i ≤ Z.of_nat (length vs))%Z⌝ ∗
    "%Hnf" ∷ ⌜toYjsId id ∉ ⋃ (span_ids <$> take (uint.nat i) vs)⌝)%I
    with "[i x Hs]" as "IH".
  { iExists (W64 0), _. iFrame. iPureIntro.
    replace (uint.nat (W64 0)) with 0%nat by word.
    rewrite take_0 /=. split_and!; [word | word | set_solver]. }
  wp_for "IH".
  iDestruct (own_slice_len with "Hs") as %[Hslen Hslen0].
  destruct (bool_decide (sint.Z i < sint.Z s.(slice.len))) eqn:Hlt.
  - apply bool_decide_eq_true_1 in Hlt.
    have Hilt : (uint.nat i < length vs)%nat by word.
    wp_auto. rewrite decide_True; last by word.
    destruct (vs !! uint.nat i) as [v|] eqn:Hv;
      last by (apply lookup_lt_is_Some_2 in Hilt; rewrite Hv in Hilt; by destruct Hilt).
    iDestruct (own_slice_elem_acc (sint.Z i) v s dq vs with "Hs") as "[Hel Hrest]".
    { word. }
    { replace (Z.to_nat (sint.Z i)) with (uint.nat i) by word. exact Hv. }
    wp_auto.
    have Hwfv : span_no_overflow v := Forall_lookup_1 _ _ _ _ Hwfs Hv.
    (* under [span_no_overflow] the Go [w64] range test is the mathematical one *)
    have Hadd : uint.Z (word.add v.(yjs.idSpan.id').(yjs.id.clock') v.(yjs.idSpan.len'))
              = (uint.Z v.(yjs.idSpan.id').(yjs.id.clock') + uint.Z v.(yjs.idSpan.len'))%Z.
    { rewrite /span_no_overflow /range_no_overflow in Hwfv. word. }
    have Hv' : vs !! sint.nat i = Some v.
    { replace (sint.nat i) with (uint.nat i) by word. exact Hv. }
    have Hstep : toYjsId id ∉ span_ids v ->
        toYjsId id ∉ ⋃ (span_ids <$> take (uint.nat (word.add i (W64 1))) vs).
    { move=> Hnotin.
      replace (uint.nat (word.add i (W64 1))) with (S (uint.nat i)) by word.
      rewrite (take_S_r _ _ v); [| exact Hv].
      rewrite fmap_app union_list_app_L /= (right_id_L ∅ (∪)).
      apply not_elem_of_union. split; [exact Hnf | exact Hnotin]. }
    (* the short-circuit && is nested ifs: case each test *)
    destruct (bool_decide (v.(yjs.idSpan.id').(yjs.id.clientId') = id.(yjs.id.clientId'))) eqn:Hcid.
    + apply bool_decide_eq_true_1 in Hcid.
      wp_auto.
      destruct (bool_decide (uint.Z v.(yjs.idSpan.id').(yjs.id.clock') ≤ uint.Z id.(yjs.id.clock'))%Z) eqn:Hle.
      * apply bool_decide_eq_true_1 in Hle.
        wp_auto.
        destruct (bool_decide (uint.Z id.(yjs.id.clock') <
            uint.Z (word.add v.(yjs.idSpan.id').(yjs.id.clock') v.(yjs.idSpan.len')))%Z) eqn:Hltc.
        -- apply bool_decide_eq_true_1 in Hltc.
           wp_auto. wp_for_post.
           have Hin : toYjsId id ∈ ⋃ (span_ids <$> vs).
           { apply elem_of_union_list. exists (span_ids v). split.
             { apply list_elem_of_fmap_2. by eapply list_elem_of_lookup_2. }
             apply span_ids_elem. split_and!; [exact Hcid | exact Hle | lia]. }
           iEval (rewrite (bool_decide_eq_true_2 _ Hin)) in "HΦ".
           iDestruct ("Hrest" $! v with "Hel") as "Hs".
           iEval (rewrite (list_insert_id _ _ _ Hv')) in "Hs".
           iApply "HΦ". iFrame.
        -- apply bool_decide_eq_false_1 in Hltc.
           wp_auto. wp_for_post.
           iDestruct ("Hrest" $! v with "Hel") as "Hs".
           iEval (rewrite (list_insert_id _ _ _ Hv')) in "Hs".
           iFrame "HΦ id". iExists (word.add i (W64 1)), v. iFrame.
           iPureIntro. split; [word |].
           apply Hstep. move=> Hinv. apply span_ids_elem in Hinv.
           destruct Hinv as (_ & _ & Hc). lia.
      * apply bool_decide_eq_false_1 in Hle.
        wp_auto. wp_for_post.
        iDestruct ("Hrest" $! v with "Hel") as "Hs".
        iEval (rewrite (list_insert_id _ _ _ Hv')) in "Hs".
        iFrame "HΦ id". iExists (word.add i (W64 1)), v. iFrame.
        iPureIntro. split; [word |].
        apply Hstep. move=> Hinv. apply span_ids_elem in Hinv.
        destruct Hinv as (_ & Hc & _). lia.
    + apply bool_decide_eq_false_1 in Hcid.
      wp_auto. wp_for_post.
      iDestruct ("Hrest" $! v with "Hel") as "Hs".
      iEval (rewrite (list_insert_id _ _ _ Hv')) in "Hs".
      iFrame "HΦ id". iExists (word.add i (W64 1)), v. iFrame.
      iPureIntro. split; [word |].
      apply Hstep. move=> Hinv. apply span_ids_elem in Hinv.
      destruct Hinv as (Hc & _ & _). exact (Hcid Hc).
  - apply bool_decide_eq_false in Hlt. wp_auto.
    have Hge : (length vs <= uint.nat i)%nat by word.
    rewrite (take_ge _ _ Hge) in Hnf.
    iEval (rewrite (bool_decide_eq_false_2 _ Hnf)) in "HΦ".
    iApply "HΦ". iFrame.
Qed.

(* [cell_has_id]'s decidability instance is [#[local]] in [store/model];
   the search lemmas here need it again (same idiom as [cell_le]'s
   merge_sort instances). *)
#[local] Instance cell_has_id_dec idv c : Decision (cell_has_id idv c).
Proof. rewrite /cell_has_id. apply _. Defined.

(** Under the isomorphism, the heap [cell_has_id] search and the model id search
    agree (same index, corresponding cell/item); position alignment needs the
    all-singleton invariant (issue #28). *)
Lemma list_find_cells_repr m cells items (idv : yjs.id.t) :
  Forall cell_unit cells ->
  cells_repr m cells items ->
  match list_find (cell_has_id idv) cells,
        list_find (fun it => item_id it = toYjsId idv) items with
  | Some (k1, c), Some (k2, yi) => k1 = k2 /\ cell_repr m c yi
  | None, None => True
  | _, _ => False
  end.
Proof.
  rewrite /cells_repr => Hunit ->.
  rewrite (run_flatten_singletons cells Hunit).
  move: Hunit.
  induction cells as [|c0 cs IH] => Hunit; first done.
  inversion Hunit as [|x l Hu0 Hus]; subst.
  rewrite fmap_cons /=.
  have Hiff : cell_has_id idv c0 <-> item_id (run_head c0) = toYjsId idv by rewrite /cell_has_id.
  case: (decide (cell_has_id idv c0)) => Hd1; case: (decide (item_id (run_head c0) = toYjsId idv)) => Hd2 /=.
  - split; [done |].
    rewrite /cell_repr /run_head. rewrite /cell_unit in Hu0.
    destruct (ic_run c0) as [|y [|y' r']]; simpl in Hu0; [lia | done | lia].
  - exfalso; apply Hd2; apply/Hiff; exact: Hd1.
  - exfalso; apply Hd1; apply/Hiff; exact: Hd2.
  - move: (IH Hus); case: (list_find (cell_has_id idv) cs) => [[k1 c]|];
      case: (list_find (fun it => item_id it = toYjsId idv) (run_head <$> cs)) => [[k2 yi']|] //=.
    by move=> [-> ?].
Qed.

(** Repair correspondence: [findById] returns the node at the model index of the
    item with the given id (or [null] when absent). *)
Lemma findById_res_correspond cells arr (idv : yjs.id.t) (k : nat) (yi : YjsItem A) :
  Forall cell_unit cells ->
  cells_repr arr cells arr ->
  list_find (fun it => item_id it = toYjsId idv) arr = Some (k, yi) ->
  findById_res cells idv = node_loc cells (Z.of_nat k).
Proof.
  move=> Hunit Hrepr Hfind.
  have Hmatch := list_find_cells_repr arr cells arr idv Hunit Hrepr.
  rewrite Hfind in Hmatch.
  move: Hmatch. case Hcf: (list_find (cell_has_id idv) cells) => [[k1 c]|]; last done.
  move=> [<- Hcr].
  rewrite /findById_res Hcf.
  have /list_find_Some [Hck _] := Hcf.
  rewrite /node_loc decide_True; last lia.
  by rewrite Nat2Z.id Hck.
Qed.

Lemma findById_res_none cells arr (idv : yjs.id.t) :
  Forall cell_unit cells ->
  cells_repr arr cells arr ->
  list_find (fun it => item_id it = toYjsId idv) arr = None ->
  findById_res cells idv = null.
Proof.
  move=> Hunit Hrepr Hfind. rewrite /findById_res.
  have Hmatch := list_find_cells_repr arr cells arr idv Hunit Hrepr.
  rewrite Hfind in Hmatch.
  by case: (list_find (cell_has_id idv) cells) Hmatch => [[k c]|].
Qed.

(* [findById] is gone from the Go (issue #49): origin resolution moved to
   [store.repair], which resolves through the store-wide [GetNode] instead of
   walking one type's list. The [findById_res] model search above is kept for
   the [GetNode]/[repair] specs. *)

(** Id uniqueness, index form: distinct positions carry distinct ids. *)
Lemma uniqueId_lookup_ne (arr : list (YjsItem A)) (i j : nat) (x y : YjsItem A) :
  uniqueId arr -> arr !! i = Some x -> arr !! j = Some y -> (i < j)%nat ->
  item_id x ≠ item_id y.
Proof.
  rewrite /uniqueId. move=> Hss Hi Hj Hij.
  have Hss' : StronglySorted (λ a b, item_id a ≠ item_id b)
                (take (S i) arr ++ drop (S i) arr)
    by rewrite take_drop.
  apply (StronglySorted_app_1_elem_of _ (take (S i) arr) (drop (S i) arr) x y Hss').
  - apply (list_elem_of_lookup_2 _ i). rewrite lookup_take_lt; [exact Hi | lia].
  - apply (list_elem_of_lookup_2 _ (j - S i)%nat). rewrite lookup_drop.
    have -> : (S i + (j - S i))%nat = j by lia. exact Hj.
Qed.

(** [findLeftIdx]/[findRightIdx] of an element's own id resolve to its exact
    index (ids are unique, so the first [list_find] hit is the element).
    Companions of [findById_res] for the #49 pre-linked-item path: they let
    [Text.Insert]/[applyUpdate] name the resolved neighbour indices the
    Integrate spec now takes. *)
Lemma list_find_id_at (arr : list (YjsItem A)) (kx : nat) (x : YjsItem A) :
  uniqueId arr -> arr !! kx = Some x ->
  list_find (λ item, item_id item = item_id x) arr = Some (kx, x).
Proof.
  move=> Huniq Hkx.
  destruct (list_find (λ item, item_id item = item_id x) arr) as [[k' y]|] eqn:Hf.
  - apply list_find_Some in Hf. destruct Hf as (Hky & Hidy & Hfirst).
    destruct (Nat.lt_trichotomy k' kx) as [Hlt | [Heq | Hgt]].
    + exfalso. exact (uniqueId_lookup_ne arr k' kx y x Huniq Hky Hkx Hlt Hidy).
    + subst k'. rewrite Hky in Hkx. injection Hkx as ->. reflexivity.
    + exfalso. exact (Hfirst kx x Hkx Hgt eq_refl).
  - exfalso. apply list_find_None in Hf.
    move: Hf. rewrite Forall_lookup. move=> Hall.
    exact (Hall kx x Hkx eq_refl).
Qed.

Lemma findLeftIdx_at (arr : list (YjsItem A)) (kx : nat) (x : YjsItem A) :
  uniqueId arr -> arr !! kx = Some x ->
  findLeftIdx (Some (item_id x)) arr = Some (Z.of_nat kx).
Proof.
  move=> Huniq Hkx. rewrite /findLeftIdx (list_find_id_at arr kx x Huniq Hkx) //.
Qed.

Lemma findRightIdx_at (arr : list (YjsItem A)) (kx : nat) (x : YjsItem A) :
  uniqueId arr -> arr !! kx = Some x ->
  findRightIdx (Some (item_id x)) arr = Some (Z.of_nat kx).
Proof.
  move=> Huniq Hkx. rewrite /findRightIdx (list_find_id_at arr kx x Huniq Hkx) //.
Qed.

(** Node locations across a cell splice: positions strictly before the splice
    keep their loc; positions at/after shift by one. Pure index bookkeeping,
    used to track the loop-constant [right] pointer through [Integrate]. *)
Lemma node_loc_splice_lt (cells : list item_cell) (c : item_cell) (idx : nat) (k : Z) :
  (k < Z.of_nat idx)%Z -> (idx <= length cells)%nat ->
  node_loc (take idx cells ++ c :: drop idx cells) k = node_loc cells k.
Proof.
  move=> Hk Hle. rewrite /node_loc.
  case: (decide (0 <= k)%Z) => H0; [| done].
  rewrite lookup_app_l; last (rewrite length_take_le; [lia | exact Hle]).
  rewrite lookup_take_lt; [done | lia].
Qed.

Lemma node_loc_splice_ge (cells : list item_cell) (c : item_cell) (idx : nat) (k : Z) :
  (Z.of_nat idx <= k)%Z -> (idx <= length cells)%nat ->
  node_loc (take idx cells ++ c :: drop idx cells) (k + 1) = node_loc cells k.
Proof.
  move=> Hk Hle. rewrite /node_loc.
  rewrite decide_True; last lia. rewrite decide_True; last lia.
  rewrite lookup_app_r; last (rewrite length_take_le; [lia | exact Hle]).
  rewrite length_take_le; last exact Hle.
  have -> : (Z.to_nat (k + 1) - idx)%nat = S (Z.to_nat k - idx)%nat by lia.
  simpl. rewrite lookup_drop.
  have -> : (idx + (Z.to_nat k - idx))%nat = Z.to_nat k by lia.
  done.
Qed.

(* ----- run prefix-sum toolkit for the cell-cursor scan (issue #28 C1d) ----
   The scan stack is stated over CELL cursors coupled to model indices by the
   prefix sum [length (run_flatten (take cur cells))]; these close the gaps the
   unit-only [cells_repr_length]/[cells_repr_take] identifications left. They
   live here (not [prelude]) to keep the root dependency stable; promote at
   stage C2 when the update path needs them too. *)

(** Non-strict monotonicity of the flattened-prefix length in the cursor. *)
Lemma run_flatten_take_length_le (cells : list item_cell) (cur1 cur2 : nat) :
  (cur1 <= cur2)%nat ->
  (length (run_flatten (take cur1 cells)) <= length (run_flatten (take cur2 cells)))%nat.
Proof.
  move=> Hle.
  have -> : take cur1 cells = take cur1 (take cur2 cells)
    by rewrite take_take Nat.min_l.
  set l2 := take cur2 cells.
  rewrite -{2}(take_drop cur1 l2) run_flatten_app length_app. lia.
Qed.

(** Reverse direction: a prefix-length [<=] forces the cursor [<=] (nonempty
    runs, the left cursor in range). *)
Lemma run_flatten_take_length_le_inv (cells : list item_cell) (cur1 cur2 : nat) :
  Forall (λ c, ic_run c ≠ []) cells ->
  (cur1 <= length cells)%nat ->
  (length (run_flatten (take cur1 cells)) <= length (run_flatten (take cur2 cells)))%nat ->
  (cur1 <= cur2)%nat.
Proof.
  move=> Hne Hb Hlen.
  destruct (decide (cur1 <= cur2)%nat) as [|Hgt]; first done.
  have := run_flatten_take_length_lt cells cur2 cur1 Hne ltac:(lia) Hb. lia.
Qed.

(** The flattened prefix of a cell [take] is the model [take] at the boundary:
    the run-general replacement for the unit-only [cells_repr_take]. *)
Lemma run_flatten_take_prefix (cells : list item_cell) (arr : list (YjsItem A)) (cur : nat) :
  arr = run_flatten cells ->
  run_flatten (take cur cells) = take (length (run_flatten (take cur cells))) arr.
Proof.
  move=> ->.
  rewrite -{3}(take_drop cur cells) run_flatten_app take_app_length //.
Qed.

(** The flattened suffix of a cell [drop] is the model [drop] at the boundary:
    the run-general replacement for the unit-only [cells_repr_drop]. *)
Lemma run_flatten_drop_suffix (cells : list item_cell) (arr : list (YjsItem A)) (cur : nat) :
  arr = run_flatten cells ->
  run_flatten (drop cur cells) = drop (length (run_flatten (take cur cells))) arr.
Proof.
  move=> ->.
  rewrite -{3}(take_drop cur cells) run_flatten_app drop_app_length //.
Qed.

(** The model item at a cell boundary is that cell's run head: the model
    lookup behind every head-field read of the scanned node. *)
Lemma run_head_at_prefix (cells : list item_cell) (arr : list (YjsItem A))
    (i : nat) (ci : item_cell) :
  arr = run_flatten cells ->
  cells !! i = Some ci ->
  ic_run ci ≠ [] ->
  arr !! (length (run_flatten (take i cells))) = Some (run_head ci).
Proof.
  move=> -> Hi Hne.
  have Hhd : ic_run ci !! 0%nat = Some (run_head ci).
  { rewrite /run_head. move: Hne. destruct (ic_run ci) as [|y r]; [by move=> H; destruct (H eq_refl) | done]. }
  have := run_flatten_take_lookup cells i ci 0%nat (run_head ci) Hi Hhd.
  rewrite Nat.add_0_r //.
Qed.

(** Comparing a node pointer with itself is always [true] (it has its own id).
    A stepping stone of [wp_itemPtrEqual_node]. *)
#[local] Lemma wp_itemPtrEqual_self (p : loc) (v : yjs.item.t) (dq : dfrac) :
  {{{ is_pkg_init yjs ∗ p ↦{dq} v }}}
    @! yjs.itemPtrEqual #p #p
  {{{ RET #true; p ↦{dq} v }}}.
Proof.
  wp_start as "Hp". iDestruct (typed_pointsto_not_null with "Hp") as %Hnn. wp_auto.
  rewrite (bool_decide_eq_false_2 (p = null) Hnn). wp_auto.
  rewrite (bool_decide_eq_false_2 (p = null) Hnn). wp_auto.
  rewrite (bool_decide_eq_false_2 (p = null) Hnn). wp_auto.
  wp_method_call; wp_call; wp_auto.
  wp_apply (wp_Id__Equal v.(yjs.item.id') v.(yjs.item.id')).
  rewrite bool_decide_eq_true_2; last reflexivity.
  iApply "HΦ". iFrame "Hp".
Qed.

(** Comparing two DLL nodes by [itemPtrEqual] decides CELL-index equality:
    distinct cells sit at distinct model boundaries (the prefix sum is strictly
    monotone for nonempty runs), so their head ids differ by id-uniqueness of
    [arr]. [a]/[b] range over [[0, length cells]] (the [length] sentinel is the
    [null] / [Last] boundary), with [a <= b]. Used for the [conflict == right]
    break test and the entry [left.right == right] test. *)
Lemma wp_itemPtrEqual_node (parent : loc) (dq : dfrac) (cells : list item_cell)
    (arr : list (YjsItem A)) (a b : Z) :
  YjsArrInvariant arr ->
  Forall (λ c, ic_run c ≠ []) cells ->
  (0 <= a)%Z -> (a <= b)%Z -> (b <= Z.of_nat (length cells))%Z ->
  {{{ is_pkg_init yjs ∗ own_ytype_cells parent dq cells arr }}}
    @! yjs.itemPtrEqual #(node_loc cells a) #(node_loc cells b)
  {{{ RET #(bool_decide (a = b)); own_ytype_cells parent dq cells arr }}}.
Proof.
  move=> Harr Hnec Ha0 Hab Hblen.
  iIntros (Φ) "[#Hpkg Ht] HΦ". iNamed "Ht".
  have Hrfl : arr = run_flatten cells := Hrepr.
  destruct (decide (a = b)) as [Heq | Hne].
  - subst b. rewrite bool_decide_eq_true_2; last reflexivity.
    destruct (decide (a < Z.of_nat (length cells))%Z) as [Halt | Hage].
    + have Ha_lt : (Z.to_nat a < length cells)%nat by lia.
      destruct (cells !! Z.to_nat a) as [ca|] eqn:Hca; last by (apply lookup_ge_None in Hca; lia).
      have Hpa : node_loc cells a = ic_loc ca by rewrite /node_loc decide_True; [rewrite Hca | lia].
      iDestruct (own_dll_lookup_acc_node _ _ _ _ _ _ _ _ Hca with "Hdll") as (pva nva) "(%Hruna & %Hclena & %Hpca & Hnode & Hback)".
      iDestruct "Hnode" as (iva olida orida)
        "(Hval & Hola & Hora & %Hinla & %Hinra & %Hida & %Hconta & %Hpara & %Hpreva & %Hnexta & %Hflagsa)".
      rewrite Hpa. wp_apply (wp_itemPtrEqual_self (ic_loc ca) iva dq with "[$Hpkg $Hval]").
      iIntros "Hval". iApply "HΦ". iExists yt, tl. iFrame "Hparent".
      iAssert (own_item_node (ic_loc ca) dq (input_of_run (cell_run ca))
                 (ic_deleted ca) (ic_parent ca) pva nva) with "[Hval Hola Hora]" as "Hnode".
      { iExists iva, olida, orida. iFrame "Hval Hola Hora".
        iPureIntro. split_and!;
          [exact Hinla | exact Hinra | exact Hida | exact Hconta | exact Hpara
          | exact Hpreva | exact Hnexta | exact Hflagsa]. }
      iDestruct ("Hback" with "Hnode") as "Hdll". iFrame "Hdll". done.
    + have Hpa : node_loc cells a = null.
      { rewrite /node_loc. case_decide; [|done]. rewrite lookup_ge_None_2; [done | lia]. }
      rewrite Hpa. wp_apply (wp_itemPtrEqual null null None None (DfracOwn 1) (DfracOwn 1) with "[$Hpkg]").
      { rewrite /item_or_null. iSplit; done. }
      rewrite (bool_decide_eq_true_2 (originId_of None = originId_of None)); last reflexivity.
      iIntros "_". iApply "HΦ". iExists yt, tl. iFrame "Hparent Hdll". done.
  - rewrite bool_decide_eq_false_2; last exact Hne.
    have Hab' : (a < b)%Z by lia.
    destruct (decide (b < Z.of_nat (length cells))%Z) as [Hblt | Hbge].
    + (* a < b < length: borrow both nodes, distinct ids by uniqueness *)
      have Ha_lt : (Z.to_nat a < length cells)%nat by lia.
      have Hb_lt : (Z.to_nat b < length cells)%nat by lia.
      destruct (cells !! Z.to_nat a) as [ca|] eqn:Hca; last by (apply lookup_ge_None in Hca; lia).
      destruct (cells !! Z.to_nat b) as [cb|] eqn:Hcb; last by (apply lookup_ge_None in Hcb; lia).
      have Hpa : node_loc cells a = ic_loc ca by rewrite /node_loc decide_True; [rewrite Hca | lia].
      have Hpb : node_loc cells b = ic_loc cb by rewrite /node_loc decide_True; [rewrite Hcb | lia].
      have Hab_nat : (Z.to_nat a < Z.to_nat b)%nat by lia.
      iDestruct (own_dll_lookup_acc_2_node _ _ _ _ _ cells (Z.to_nat a) (Z.to_nat b) ca cb Hab_nat Hca Hcb with "Hdll")
        as (preva nxta prevb nxtb) "(%Hruna & %Hrunb & Hnodea & Hnodeb & Hback)".
      iDestruct "Hnodea" as (iva olida orida)
        "(Hvala & Hola & Hora & %Hinla & %Hinra & %Hidan & %Hconta & %Hpara & %Hpreva & %Hnexta & %Hflagsa)".
      iDestruct "Hnodeb" as (ivb olidb oridb)
        "(Hval & Hol & Hor & %Hinlb & %Hinrb & %Hidbn & %Hcontb & %Hparb & %Hprevb & %Hnextb & %Hflagsb)".
      have Hida : item_id (run_head ca) = toYjsId iva.(yjs.item.id').
      { symmetry. exact Hidan. }
      have Hid : item_id (run_head cb) = toYjsId ivb.(yjs.item.id').
      { symmetry. exact Hidbn. }
      have Hids_unique := yai_unique _ Harr.
      have Hnea : ic_run ca ≠ [] := Forall_lookup_1 _ _ _ _ Hnec Hca.
      have Hneb : ic_run cb ≠ [] := Forall_lookup_1 _ _ _ _ Hnec Hcb.
      have Hma := run_head_at_prefix cells arr (Z.to_nat a) ca Hrfl Hca Hnea.
      have Hmb := run_head_at_prefix cells arr (Z.to_nat b) cb Hrfl Hcb Hneb.
      have Hlen_lt : (length (run_flatten (take (Z.to_nat a) cells))
                      < length (run_flatten (take (Z.to_nat b) cells)))%nat
        := run_flatten_take_length_lt cells (Z.to_nat a) (Z.to_nat b) Hnec ltac:(lia) ltac:(lia).
      have Hid_ne : item_id (run_head ca) ≠ item_id (run_head cb)
        := uniqueId_lookup_ne arr _ _ _ _ Hids_unique Hma Hmb Hlen_lt.
      have Hoid_ne : originId_of (Some iva) ≠ originId_of (Some ivb).
      { rewrite /originId_of /= => Heqsome. apply Hid_ne.
        have Heqid := Some_inj _ _ Heqsome.
        rewrite Hida Hid Heqid //. }
      rewrite Hpa Hpb.
      iDestruct (typed_pointsto_not_null with "Hvala") as %Hnna.
      iDestruct (typed_pointsto_not_null with "Hval") as %Hnnb.
      wp_apply (wp_itemPtrEqual (ic_loc ca) (ic_loc cb) (Some iva) (Some ivb) dq dq with "[$Hpkg Hvala Hval]").
      { rewrite /item_or_null. iFrame "Hvala Hval". iSplit; iPureIntro.
        - exact Hnna.
        - exact Hnnb. }
      rewrite (bool_decide_eq_false_2 (originId_of (Some iva) = originId_of (Some ivb)) Hoid_ne).
      iIntros "[Ha Hb]". rewrite /item_or_null.
      iDestruct "Ha" as "[_ Hvala]". iDestruct "Hb" as "[_ Hval]".
      iAssert (own_item_node (ic_loc ca) dq (input_of_run (cell_run ca))
                 (ic_deleted ca) (ic_parent ca) preva nxta) with "[Hvala Hola Hora]" as "Hnodea".
      { iExists iva, olida, orida. iFrame "Hvala Hola Hora".
        iPureIntro. split_and!;
          [exact Hinla | exact Hinra | exact Hidan | exact Hconta | exact Hpara
          | exact Hpreva | exact Hnexta | exact Hflagsa]. }
      iAssert (own_item_node (ic_loc cb) dq (input_of_run (cell_run cb))
                 (ic_deleted cb) (ic_parent cb) prevb nxtb) with "[Hval Hol Hor]" as "Hnodeb".
      { iExists ivb, olidb, oridb. iFrame "Hval Hol Hor".
        iPureIntro. split_and!;
          [exact Hinlb | exact Hinrb | exact Hidbn | exact Hcontb | exact Hparb
          | exact Hprevb | exact Hnextb | exact Hflagsb]. }
      iDestruct ("Hback" with "Hnodea Hnodeb") as "Hdll".
      iApply "HΦ". iExists yt, tl. iFrame "Hparent".
      iSplitL; last (iPureIntro; split_and!; [exact Hlen | exact Hrepr | exact Hcpar]).
      iFrame "Hdll".
    + (* b = length: [b] is null, [a] a node *)
      have Ha_lt : (Z.to_nat a < length cells)%nat by lia.
      destruct (cells !! Z.to_nat a) as [ca|] eqn:Hca; last by (apply lookup_ge_None in Hca; lia).
      have Hpa : node_loc cells a = ic_loc ca by rewrite /node_loc decide_True; [rewrite Hca | lia].
      have Hpb : node_loc cells b = null.
      { rewrite /node_loc. case_decide; [|done]. rewrite lookup_ge_None_2; [done | lia]. }
      iDestruct (own_dll_lookup_acc_node _ _ _ _ _ _ _ _ Hca with "Hdll") as (pva nva) "(%Hruna & %Hclena & %Hpca & Hnode & Hback)".
      iDestruct "Hnode" as (iva olida orida)
        "(Hval & Hola & Hora & %Hinla & %Hinra & %Hida & %Hconta & %Hpara & %Hpreva & %Hnexta & %Hflagsa)".
      iDestruct (typed_pointsto_not_null with "Hval") as %Hnna.
      rewrite Hpa Hpb.
      wp_apply (wp_itemPtrEqual (ic_loc ca) null (Some iva) None dq dq with "[$Hpkg Hval]").
      { rewrite /item_or_null. iSplitL "Hval"; [iFrame "Hval"; iPureIntro; exact Hnna | done]. }
      rewrite (bool_decide_eq_false_2 (originId_of (Some iva) = originId_of None)); last done.
      iIntros "[Ha _]". rewrite /item_or_null. iDestruct "Ha" as "[_ Hval]".
      iApply "HΦ". iExists yt, tl. iFrame "Hparent".
      iAssert (own_item_node (ic_loc ca) dq (input_of_run (cell_run ca))
                 (ic_deleted ca) (ic_parent ca) pva nva) with "[Hval Hola Hora]" as "Hnode".
      { iExists iva, olida, orida. iFrame "Hval Hola Hora".
        iPureIntro. split_and!;
          [exact Hinla | exact Hinra | exact Hida | exact Hconta | exact Hpara
          | exact Hpreva | exact Hnexta | exact Hflagsa]. }
      iDestruct ("Hback" with "Hnode") as "Hdll". iFrame "Hdll". done.
Qed.

(** No array item strictly to the right of the resolved left origin can BE that
    left origin: the origin (when present) sits at [leftIdx] with a unique id, so
    any item at an index [> leftIdx] carries a different id. This discharges
    [set_find_integration_block_step]'s [Hnotleft] for the scanned run block, whose chars all
    sit at model indices [> leftIdx] (issue #28 stage C1c). *)
Lemma findLeftIdx_scanned_ne (arr : list (YjsItem A)) (originId : option YjsId)
    (leftIdx : Z) (i : nat) (c : YjsItem A) :
  YjsArrInvariant arr ->
  findLeftIdx originId arr = Some leftIdx ->
  arr !! i = Some c ->
  (leftIdx < Z.of_nat i)%Z ->
  Some (item_id c) ≠ originId.
Proof.
  move=> Harr Hfind Hlk Hlt.
  destruct originId as [lid|]; last done.
  rewrite /findLeftIdx in Hfind.
  move: Hfind => /fmap_Some [j [Hj Hleft_eq]].
  move: Hj => /fmap_Some [[j' oitem] [Hlf Hj_eq]].
  simpl in Hj_eq. subst j.
  apply list_find_Some in Hlf as (Hoitem_lk & Hoitem_id & _).
  have Hlt' : (j' < i)%nat by lia.
  have Hne : item_id oitem ≠ item_id c
    := invariant_yjsarray_idx.ss_lookup_lt arr j' i oitem c (yai_unique _ Harr) Hoitem_lk Hlk Hlt'.
  move=> [= Heq]. apply Hne. by rewrite Hoitem_id Heq.
Qed.

(** Run-variant freshness lemmas: [own_linked_item] carries the same raw
    heap [Item], so location freshness holds identically (issue #28 U7). *)
Lemma linked_item_fresh2 (item_l parent lft rgt : loc)
    (input : IntegrateInput (A := A)) (dq : dfrac) (types : gmap loc type_state) :
  own_linked_item item_l input parent lft rgt -∗
  (own_type_pool dq types) -∗
  ⌜item_l ∉ ic_loc <$> all_cells types⌝.
Proof.
  iIntros "Hlinked Htypes".
  iDestruct "Hlinked" as (itemVal oleft oright) "(Hraw & _)".
  iDestruct "Hraw" as "(Hitem & _)".
  iAssert ([∗ map] p ↦ ts ∈ types,
      own_ytype_cells p dq (ty_cells ts) (ty_arr ts))%I with "[Htypes]" as "Htypes".
  { iApply (big_sepM_impl with "Htypes"). iIntros "!#" (p ts Hp) "($ & _)". }
  iApply (all_cells_fresh with "Hitem Htypes").
Qed.

Lemma linked_item_fresh_ytype (item_l parent2 lft rgt parent : loc)
    (input : IntegrateInput (A := A)) (dq : dfrac)
    (cells : list item_cell) (arr : list (YjsItem A)) :
  own_linked_item item_l input parent2 lft rgt -∗
  own_ytype_cells parent dq cells arr -∗
  ⌜item_l ∉ ic_loc <$> cells⌝.
Proof.
  iIntros "Hlinked Hyt".
  iDestruct "Hlinked" as (itemVal oleft oright) "(Hraw & _)".
  iDestruct "Hraw" as "(Hitem & _)".
  iDestruct "Hyt" as (yt tl) "(_ & Hdll & _)".
  iApply (own_dll_fresh with "Hitem Hdll").
Qed.

(** The algorithmic core (extracted Go function [scanConflicts]): starting at
    the cursor CELL [curL] (the boundary cell of model index [leftIdx + 1])
    with the anchor at cell [curL - 1], the scan returns the resolved left
    anchor: the cell just left of a run boundary [curD] whose model index is
    the pure [setfindIntegratedIndex]. This is the WP refinement of the loop
    onto [set_find_integration_loop]: the loop invariant [integrate_loop_inv] couples the
    heap loop state to a [set_find_integration_loop] run, and each Go iteration consumes one
    whole run block via [set_find_integration_block_step] (issue #28 C1c/C1d). *)
Lemma wp_scanConflicts (parent item_l : loc) (dq : dfrac)
    (cells : list item_cell) (arr : list (YjsItem A))
    (input : IntegrateInput (A := A)) (newItem : YjsItem A)
    (itemVal : yjs.item.t) (oleft oright : option yjs.id.t)
    (leftIdx rightIdx : Z) (destIdx : nat) (curL curR : nat) :
  YjsArrInvariant arr ->
  toItem input arr = Some newItem ->
  IsItemValid newItem ->
  maximalId newItem arr ->
  findLeftIdx (in_originId input) arr = Some leftIdx ->
  findRightIdx (in_rightOriginId input) arr = Some rightIdx ->
  setfindIntegratedIndex leftIdx rightIdx input arr = Some destIdx ->
  Forall (λ c, ic_run c ≠ []) cells ->
  (∀ c0, c0 ∈ cells -> cell_fits c0) ->
  (∀ c0, c0 ∈ cells -> cell_origin_clk c0) ->
  (Z.of_nat (length (run_flatten (take curL cells))) = leftIdx + 1)%Z ->
  (curL <= length cells)%nat ->
  (Z.of_nat (length (run_flatten (take curR cells))) = rightIdx)%Z ->
  (curR <= length cells)%nat ->
  {{{ is_pkg_init yjs ∗ own_ytype_cells parent dq cells arr ∗
      own_fresh_item_raw item_l input itemVal oleft oright }}}
    @! yjs.scanConflicts #item_l #(node_loc cells (Z.of_nat curL - 1))
        #(node_loc cells (Z.of_nat curL)) #(node_loc cells (Z.of_nat curR))
  {{{ (ret : loc), RET #ret;
      own_ytype_cells parent dq cells arr ∗
      own_fresh_item_raw item_l input itemVal oleft oright ∗
      ∃ curD : nat, ⌜ret = node_loc cells (Z.of_nat curD - 1)⌝ ∗
        ⌜(Z.of_nat (length (run_flatten (take curD cells))) = Z.of_nat destIdx)%Z⌝ ∗
        ⌜(curD <= length cells)%nat⌝ }}}.
Proof using Type*.
  move=> Harr Htoitem Hvalid Hmax HfindL HfindR HfindD Hnec Hfits Hoclk HcurL HcurLb HcurR HcurRb.
  wp_start as "(Htext & Hfresh)". iNamed "Htext". iNamed "Hfresh".
  (* Index bounds via the pure model. *)
  have Hids_unique := yai_unique _ Harr.
  have HfindLeftPtr : findPtrIdx (origin newItem) arr = Some leftIdx.
  { rewrite -(toitem_lemmas.findLeftIdx_findPtrIdx_eq input newItem arr Hids_unique Htoitem). exact HfindL. }
  have HfindRightPtr : findPtrIdx (rightOrigin newItem) arr = Some rightIdx.
  { rewrite -(toitem_lemmas.findRightIdx_findPtrIdx_eq input newItem arr Hids_unique Htoitem). exact HfindR. }
  have HoriginInArr := findptridx_getelem.findPtrIdx_ArrSet arr (origin newItem) leftIdx HfindLeftPtr.
  have HrightOriginInArr := findptridx_getelem.findPtrIdx_ArrSet arr (rightOrigin newItem) rightIdx HfindRightPtr.
  have HleftLB := insert_lemmas.findPtrIdx_ge_minus_1 arr (origin newItem) leftIdx HfindLeftPtr.
  have HleftLtRight := findptridx_order2.YjsLt'_findPtrIdx_lt arr (origin newItem) (rightOrigin newItem)
                leftIdx rightIdx Harr HoriginInArr HrightOriginInArr (iiv_origin_lt _ Hvalid) HfindLeftPtr HfindRightPtr.
  have HrightUB := insert_lemmas.findPtrIdx_le_size arr (rightOrigin newItem) rightIdx HfindRightPtr.
  have Hrfl : arr = run_flatten cells := Hrepr.
  wp_auto.
  (* the two id-set accumulators start empty *)
  wp_apply wp_slice_literal. iSplitR; first done. iIntros "%ci_sl [Hci_sl Hci_cap]". wp_auto.
  wp_apply wp_slice_literal. iSplitR; first done. iIntros "%ibo_sl [Hibo_sl Hibo_cap]". wp_auto.
  (* expose the pure loop result [d] (with [Z.to_nat d = destIdx]) *)
  rewrite /setfindIntegratedIndex in HfindD.
  destruct (set_find_integration_loop (Z.to_nat (rightIdx - leftIdx) - 1) 1 leftIdx rightIdx
              (in_originId input) (in_rightOriginId input) (in_id input) arr ∅ ∅ (leftIdx + 1))
    as [d|] eqn:Hset_find_integration; last by (simpl in HfindD; done).
  simpl in HfindD. injection HfindD as Hd_eq.
  (* loop invariant: offset = 1, cursor at the boundary cell [curL],
     accumulators empty, dest = leftIdx + 1 (anchor cursor [curL]) *)
  iAssert (∃ (offset cur curD : nat) (idsB conflictI : gset YjsId) (destL : Z),
    integrate_loop_inv parent dq cells arr leftIdx rightIdx curR input.(in_originId)
      input.(in_rightOriginId) input.(in_id) (Some d) conflict_ptr left_ptr right_ptr
      itemsBeforeOrigin_ptr conflictingItems_ptr offset cur curD idsB conflictI destL
    ∗ own_fresh_item_raw item_l input itemVal oleft oright)%I
    with "[Hparent Hdll conflict left right conflictingItems Hci_sl Hci_cap itemsBeforeOrigin Hibo_sl Hibo_cap Hitem Holeft Horight]" as "IH".
  { iExists 1%nat, curL, curL, ∅, ∅, (leftIdx + 1)%Z.
    rewrite /integrate_loop_inv /own_fresh_item_raw.
    iFrame "conflict left right Hitem Holeft Horight".
    iSplitL "Hparent Hdll itemsBeforeOrigin Hibo_sl Hibo_cap conflictingItems Hci_sl Hci_cap".
    - iSplitL "Hparent Hdll".
      { iExists yt, tl. iFrame "Hparent Hdll". done. }
      iSplitL "itemsBeforeOrigin Hibo_sl Hibo_cap".
      { iExists _. iFrame "itemsBeforeOrigin". iExists ([] : list yjs.idSpan.t). iFrame "Hibo_sl Hibo_cap".
        iPureIntro. split; [constructor | done]. }
      iSplitL "conflictingItems Hci_sl Hci_cap".
      { iExists _. iFrame "conflictingItems". iExists ([] : list yjs.idSpan.t). iFrame "Hci_sl Hci_cap".
        iPureIntro. split; [constructor | done]. }
      iPureIntro; split_and!;
        [lia | by rewrite HcurL | exact HcurLb | exact HcurL | exact HcurLb | lia | lia | lia | exact Hset_find_integration].
    - iPureIntro; split_and!; [exact Hin_l | exact Hin_r | exact Hid | exact Hcontent]. }
  wp_for "IH".
  iDestruct "IH" as "[Hinv Hfresh]". iNamed "Hinv". iNamed "Hfresh".
  iDestruct "Holeft" as "#Holeft". iDestruct "Horight" as "#Horight".
  wp_auto.
  destruct (decide (cur = length cells)%nat) as [Heq_len | Hne_len].
  - (* cursor reached the end: [conflict = nil], loop exits; fuel 0 pins [destL = d] *)
    have Hnull : node_loc cells (Z.of_nat cur) = null.
    { rewrite /node_loc decide_True; last lia.
      rewrite Nat2Z.id Heq_len lookup_ge_None_2; [done | lia]. }
    have Harrfull : (Z.of_nat (length arr) = leftIdx + Z.of_nat offset)%Z.
    { rewrite -Hcur Heq_len take_ge; [by rewrite Hrfl | lia]. }
    have HdestL : destL = d.
    { have Hfuel0 : (Z.to_nat (rightIdx - leftIdx) - offset = 0)%nat
        by (clear -Harrfull Hbound HrightUB Hoff; lia).
      rewrite Hfuel0 /= in Hloop. by injection Hloop. }
    rewrite Hnull bool_decide_eq_true_2; last reflexivity. simpl.
    rewrite decide_False; last done.
    wp_auto.
    rewrite decide_True; last reflexivity. wp_auto.
    iApply ("HΦ" $! (node_loc cells (Z.of_nat curD - 1))).
    iFrame "Htext".
    iSplitL. { rewrite /own_fresh_item_raw. iFrame "Hitem Holeft Horight". iPureIntro; split_and!; done. }
    iExists curD. iPureIntro. split_and!;
      [done | rewrite HcurD HdestL -Hd_eq Z2Nat.id; [done | clear -Hdest HdestL HleftLB; lia] | exact HcurDb].
  - (* cursor in range: run one scan step, matched to a [set_find_integration_block_step] unfold. *)
    have Hcur_lt : (cur < length cells)%nat by lia.
    destruct (cells !! cur) as [ci|] eqn:Hci;
      last by (apply lookup_ge_None in Hci; lia).
    have Hci_loc : node_loc cells (Z.of_nat cur) = ic_loc ci
      by rewrite /node_loc decide_True; [rewrite Nat2Z.id Hci | lia].
    iAssert (⌜ic_loc ci ≠ null⌝ ∗ own_ytype_cells parent dq cells arr)%I with "[Htext]" as "[%Hci_nn Htext]".
    { iNamed "Htext". iDestruct (own_dll_lookup_acc_node _ _ _ _ _ _ _ _ Hci with "Hdll") as (px nx) "(_ & _ & _ & Hnode & Hback)".
      iDestruct (own_item_node_not_null with "Hnode") as "[%Hnn Hnode]".
      iDestruct ("Hback" with "Hnode") as "Hdll".
      iSplitR; first (iPureIntro; exact Hnn). iExists yt0, tl0. iFrame "Hparent Hdll". done. }
    have Hnnull : node_loc cells (Z.of_nat cur) ≠ null by rewrite Hci_loc; exact Hci_nn.
    rewrite (bool_decide_eq_false_2 _ Hnnull). simpl. rewrite decide_True; last reflexivity.
    wp_auto.
    (* the cursor cannot be past the right cell: prefix sums are monotone *)
    have Hcur_le_R : (cur <= curR)%nat.
    { apply (run_flatten_take_length_le_inv cells cur curR Hnec Hcurb).
      clear -Hcur HcurR Hbound. lia. }
    wp_apply (wp_itemPtrEqual_node parent dq cells arr (Z.of_nat cur) (Z.of_nat curR) Harr Hnec
                ltac:(lia) ltac:(lia) ltac:(lia) with "[$Htext]").
    iIntros "Htext".
    destruct (decide (Z.of_nat cur = Z.of_nat curR)) as [Heqr | Hner].
    + (* conflict = right: break; fuel 0 pins [destL = d] *)
      rewrite (bool_decide_eq_true_2 _ Heqr).
      have Hcureq : cur = curR by lia.
      have HoffR : (leftIdx + Z.of_nat offset = rightIdx)%Z.
      { rewrite -Hcur -HcurR Hcureq //. }
      have HdestL : destL = d.
      { have Hfuel0 : (Z.to_nat (rightIdx - leftIdx) - offset = 0)%nat by (clear -HoffR Hbound; lia).
        rewrite Hfuel0 /= in Hloop. by injection Hloop. }
      wp_auto.
      wp_for_post.
      iApply ("HΦ" $! (node_loc cells (Z.of_nat curD - 1))).
      iFrame "Htext".
      iSplitL. { rewrite /own_fresh_item_raw. iFrame "Hitem Holeft Horight". iPureIntro; split_and!; done. }
      iExists curD. iPureIntro. split_and!;
        [done | rewrite HcurD HdestL -Hd_eq Z2Nat.id; [done | clear -Hdest HdestL HleftLB; lia] | exact HcurDb].
    + (* conflict ≠ right: scan one run block; match [set_find_integration_block_step]'s branches *)
      rewrite (bool_decide_eq_false_2 _ Hner).
      have Hcur_lt_R : (cur < curR)%nat by lia.
      have Hlt_pref : (length (run_flatten (take cur cells))
                       < length (run_flatten (take curR cells)))%nat
        := run_flatten_take_length_lt cells cur curR Hnec Hcur_lt_R HcurRb.
      have Hir : (leftIdx + Z.of_nat offset < rightIdx)%Z by (clear -Hcur HcurR Hlt_pref; lia).
      wp_auto.
      iNamed "Htext".
      iDestruct (own_dll_acc_node _ cells _ _ cur ci Hci with "Hdll")
        as (prev_ci nxt_ci) "(%Hcloc0 & %Hcl0p & %Hcr0p & %Hrunwf_ci & %Hclen_ci & %Hpc_ci & Hnode & Hback)".
      iDestruct "Hnode" as (iv_ci olid_ci orid_ci)
        "(Hcival & #Hcol & #Hcor & %Hinl_ci & %Hinr_ci & %Hcidn_ci & %Hccontn_ci & %Hcpar_ci & %Hprev_ci & %Hnext_ci & %Hcflags_ci)".
      have Hcid_ci : item_id (run_head ci) = toYjsId iv_ci.(yjs.item.id').
      { symmetry. exact Hcidn_ci. }
      have Hccont_ci : content <$> ic_run ci = explode (toContent iv_ci.(yjs.item.content')).
      { have Hstr : toContent iv_ci.(yjs.item.content') = items_string (ic_run ci) := Hccontn_ci.
        rewrite Hstr. exact Hpc_ci. }
      have Hcolid_ci : origin_id (origin (run_head ci)) = toYjsId <$> olid_ci.
      { symmetry. exact Hinl_ci. }
      have Hcorid_ci : origin_id (rightOrigin (run_head ci)) = toYjsId <$> orid_ci.
      { symmetry. exact Hinr_ci. }
      have Hcr0 : iv_ci.(yjs.item.right') = node_loc cells (Z.of_nat cur + 1).
      { rewrite Hnext_ci. exact Hcr0p. }
      iEval (rewrite Hcloc0) in "Hcival".
      wp_auto.
      iDestruct "Hids_before" as (ibo_s) "[Hibo_ref Hibo_setf]".
      iDestruct "Hibo_setf" as (vs_ibo) "(Hibo_sl & Hibo_cap & %Hibo_wf & %Hibo_set)".
      iDestruct "Hconflict_ids" as (ci_s) "[Hci_ref Hci_setf]".
      iDestruct "Hci_setf" as (vs_ci) "(Hci_sl & Hci_cap & %Hci_wf & %Hci_set)".
      wp_apply (wp_item__Len with "[$Hcival]"). iIntros "Hcival". wp_auto.
      (* the scanned node's run: split into head [hh] + tail [tl2] (nonempty by run_wf) *)
      destruct (ic_run ci) as [|hh tl2] eqn:Hrun; first by (exfalso; exact (proj1 Hrunwf_ci eq_refl)).
      rewrite -Hrun in Hccont_ci Hrunwf_ci.
      have Hrhead : run_head ci = hh by rewrite /run_head Hrun.
      have Hrunstep : run_step (hh :: tl2).
      { have Hrs := run_wf_run_step (ic_run ci) Hrunwf_ci. rewrite Hrun in Hrs. exact Hrs. }
      have Hlencont : (length (iv_ci.(yjs.item.content').(yjs.content.content')) = length (ic_run ci))%nat.
      { have Hl := f_equal length Hccont_ci.
        rewrite length_fmap explode_length /toContent in Hl. lia. }
      have Hfits_ci : cell_fits ci := Hfits ci (list_elem_of_lookup_2 _ _ _ Hci).
      have Hrunfits : (Z.of_nat (length (ic_run ci)) < 2^64)%Z.
      { have H := Hfits_ci. rewrite /cell_fits in H. clear -H. word. }
      have Hlen_w : (length (ic_run ci) = uint.nat (W64 (length (ic_run ci))))%nat
        by (clear -Hrunfits; word).
      have Hclk_ci : clock (item_id (run_head ci)) = uint.nat iv_ci.(yjs.item.id').(yjs.id.clock') by rewrite Hcid_ci /toYjsId.
      rewrite Hlencont.
      wp_apply wp_slice_literal. iSplitR; first done. iIntros "%sing1 [Hsing1 _]". wp_auto.
      wp_apply (wp_slice_append with "[$Hibo_sl $Hibo_cap $Hsing1]").
      iIntros "%ibo_s2 (Hibo_sl & Hibo_cap & _)". wp_auto.
      wp_apply wp_slice_literal. iSplitR; first done. iIntros "%sing2 [Hsing2 _]". wp_auto.
      wp_apply (wp_slice_append with "[$Hci_sl $Hci_cap $Hsing2]").
      iIntros "%ci_s2 (Hci_sl & Hci_cap & _)". wp_auto.
      have H0 : sint.nat (W64 0) = 0%nat by word.
      iEval (rewrite H0 /=) in "Hibo_sl".
      iEval (rewrite H0 /=) in "Hci_sl".
      set sp := yjs.idSpan.mk iv_ci.(yjs.item.id') (W64 (length (ic_run ci))).
      have Hwf_sp : span_no_overflow sp.
      { rewrite /sp /span_no_overflow /range_no_overflow /=.
        have H := Hfits_ci. rewrite /cell_fits /cell_clock Hclk_ci in H.
        clear -H Hrunfits. word. }
      have Hidhh : item_id hh = toYjsId iv_ci.(yjs.item.id') by rewrite -Hrhead; exact Hcid_ci.
      have Hsp_ids : span_ids sp = char_ids (ic_run ci).
      { rewrite /sp Hrun.
        apply (span_ids_char_ids iv_ci.(yjs.item.id') (W64 (length (hh :: tl2))) hh tl2 Hidhh Hrunstep).
        rewrite -Hrun. exact Hlen_w. }
      have Hibo_wf2 : Forall span_no_overflow (vs_ibo ++ [sp]).
      { apply Forall_app. split; [exact Hibo_wf | by apply Forall_singleton]. }
      have Hci_wf2 : Forall span_no_overflow (vs_ci ++ [sp]).
      { apply Forall_app. split; [exact Hci_wf | by apply Forall_singleton]. }
      have Hibo_set2 : ⋃ (span_ids <$> (vs_ibo ++ [sp])) = char_ids (ic_run ci) ∪ idsB.
      { rewrite span_union_snoc Hsp_ids Hibo_set //. }
      have Hci_set2 : ⋃ (span_ids <$> (vs_ci ++ [sp])) = char_ids (ic_run ci) ∪ conflictI.
      { rewrite span_union_snoc Hsp_ids Hci_set //. }
      (* head-char facts (run head = [hh]) matching [set_find_integration_block_step]'s decisions *)
      have HcId : item_id hh = toYjsId iv_ci.(yjs.item.id') := Hidhh.
      have HoL : origin_id (origin hh) = toYjsId <$> olid_ci by rewrite -Hrhead; exact Hcolid_ci.
      have HoR : origin_id (rightOrigin hh) = toYjsId <$> orid_ci by rewrite -Hrhead; exact Hcorid_ci.
      (* rewrite [Hloop] one whole run block via [set_find_integration_block_step]: the block
         fits under [rightIdx] because the NEXT cell boundary is still at most
         the right cell's boundary (prefix-sum monotonicity) *)
      have HlenS : (length (run_flatten (take (S cur) cells))
                    = length (run_flatten (take cur cells)) + length (ic_run ci))%nat
        by rewrite (run_flatten_take_S cells cur ci Hci) length_app.
      have HleS_R : (length (run_flatten (take (S cur) cells))
                     <= length (run_flatten (take curR cells)))%nat
        := run_flatten_take_length_le cells (S cur) curR ltac:(lia).
      have Hblockfits : (leftIdx + Z.of_nat offset + Z.of_nat (length (ic_run ci)) <= rightIdx)%Z
        by (clear -Hcur HcurR HlenS HleS_R; lia).
      have Hlook : forall k c0, (hh :: tl2) !! k = Some c0 ->
          arr !! (Z.to_nat (leftIdx + Z.of_nat (offset + k))) = Some c0.
      { move=> k c0 Hk.
        have Hrepr' : arr = run_flatten cells := Hrepr.
        rewrite Hrepr'.
        have Hprefix : (length (run_flatten (take cur cells)) = Z.to_nat (leftIdx + Z.of_nat offset))%nat.
        { apply Nat2Z.inj. rewrite Hcur Z2Nat.id; [done | clear -HleftLB Hoff; lia]. }
        have Hidx : (Z.to_nat (leftIdx + Z.of_nat (offset + k)) = length (run_flatten (take cur cells)) + k)%nat
          by (rewrite Hprefix; clear -HleftLB Hoff; lia).
        rewrite Hidx.
        apply (run_flatten_take_lookup cells cur ci k c0 Hci).
        rewrite Hrun. exact Hk. }
      have Hnotleft : forall c0, c0 ∈ hh :: tl2 -> Some (item_id c0) ≠ input.(in_originId).
      { move=> c0 Hc0. apply list_elem_of_lookup_1 in Hc0 as [k Hk].
        apply (findLeftIdx_scanned_ne arr input.(in_originId) leftIdx
                 (Z.to_nat (leftIdx + Z.of_nat (offset + k))) c0 Harr HfindL (Hlook k c0 Hk)).
        rewrite Z2Nat.id; last (clear -HleftLB Hoff; lia). clear -Hoff; lia. }
      have Hpos_off : (0 <= leftIdx + Z.of_nat offset)%Z by (clear -HleftLB Hoff; lia).
      have Hfuel_split : (Z.to_nat (rightIdx - leftIdx) - offset)%nat
        = (length (hh :: tl2) + (Z.to_nat (rightIdx - leftIdx) - (offset + length (hh :: tl2))))%nat
        by (rewrite -Hrun; clear -Hblockfits Hoff; lia).
      rewrite Hfuel_split in Hloop.
      rewrite (set_find_integration_block_step hh tl2 _ offset leftIdx rightIdx input.(in_originId)
                 input.(in_rightOriginId) input.(in_id) arr idsB conflictI destL
                 Hrunstep Hlook Hnotleft Hpos_off) in Hloop.
      rewrite -Hrun in Hloop.
      wp_apply (wp_idOptEqual itemVal.(yjs.item.originLeftId') iv_ci.(yjs.item.originLeftId')
                  oleft olid_ci with "[$Holeft $Hcol]").
      case_bool_decide as Hoeq.
      * (* same left origin as the new item *)
        have HoeqL : origin_id (origin hh) = input.(in_originId) by rewrite HoL -Hoeq Hin_l.
        rewrite (decide_True _ _ HoeqL) in Hloop.
        wp_auto.
        case_bool_decide as Hclt.
        -- (* smaller client id: advance the anchor (left := conflict) *)
           have HcltL : ((item_id hh).(clientId) < input.(in_id).(clientId))%nat
             by (rewrite HcId -Hid /toYjsId /=; word).
           rewrite (decide_True _ _ HcltL) in Hloop.
           wp_auto.
           wp_apply wp_slice_literal. iSplitR; first done.
           iIntros "%ci_empty [Hci_empty Hci_empty_cap]". wp_auto.
           wp_for_post.
           iEval (rewrite -Hcloc0) in "Hcival".
           iAssert (own_item_node (ic_loc ci) dq (input_of_run (cell_run ci)) (ic_deleted ci) (ic_parent ci) prev_ci nxt_ci) with "[Hcival]" as "Hnode_ci". { iExists iv_ci, olid_ci, orid_ci. iFrame "Hcival Hcol Hcor". iPureIntro. split_and!; [exact Hinl_ci | exact Hinr_ci | exact Hcidn_ci | exact Hccontn_ci | exact Hcpar_ci | exact Hprev_ci | exact Hnext_ci | exact Hcflags_ci]. } iDestruct ("Hback" with "Hnode_ci") as "Hdll".
           iFrame "HΦ item".
           iExists (offset + length (ic_run ci))%nat, (S cur), (S cur), (char_ids (ic_run ci) ∪ idsB), ∅, (leftIdx + Z.of_nat (offset + length (ic_run ci)))%Z.
           rewrite /integrate_loop_inv /own_fresh_item_raw.
           iSplitL "Hparent Hdll Hconflict Hleft Hright Hibo_ref Hibo_sl Hibo_cap Hci_ref Hci_empty Hci_empty_cap"; last first.
           { iFrame "Hitem Holeft Horight".
             iPureIntro; split_and!; [exact Hin_l0|exact Hin_r0|exact Hid0|exact Hcontent0]. }
           iSplitL "Hparent Hdll". { iExists yt0, tl0. iFrame "Hparent Hdll". done. }
           iSplitL "Hconflict".
           { rewrite Hcr0. replace (Z.of_nat (S cur))%Z with (Z.of_nat cur + 1)%Z by lia. iFrame "Hconflict". }
           iSplitL "Hleft".
           { replace (Z.of_nat (S cur) - 1)%Z with (Z.of_nat cur)%Z by lia. iFrame "Hleft". }
           iSplitL "Hright". { iFrame "Hright". }
           iSplitL "Hibo_ref Hibo_sl Hibo_cap".
           { iExists ibo_s2. iFrame "Hibo_ref". iExists _. iFrame "Hibo_sl Hibo_cap". iPureIntro.
             split; [exact Hibo_wf2 | exact Hibo_set2]. }
           iSplitL "Hci_ref Hci_empty Hci_empty_cap".
           { iExists _. iFrame "Hci_ref". iExists ([] : list yjs.idSpan.t). iFrame "Hci_empty Hci_empty_cap".
                 iPureIntro. split; [constructor | done]. }
           iPureIntro; split_and!;
             [lia
             | rewrite HlenS; clear -Hcur; lia
             | lia
             | rewrite HlenS; clear -Hcur; lia
             | lia | lia | lia
             | rewrite Nat2Z.inj_add; clear -Hblockfits; lia
             | exact Hloop].
        -- (* larger-or-equal client id: same right origin -> break, else keep scanning *)
           have HcltGe : ¬ ((item_id hh).(clientId) < input.(in_id).(clientId))%nat
             by (rewrite HcId -Hid /toYjsId /=; word).
           rewrite (decide_False _ _ HcltGe) in Hloop.
           wp_auto.
           wp_apply (wp_idOptEqual itemVal.(yjs.item.originRightId') iv_ci.(yjs.item.originRightId')
                       oright orid_ci with "[$Horight $Hcor]").
           case_bool_decide as HoeqR.
           ++ (* same right origin: integration points coincide -> break *)
              have HoeqRR : origin_id (rightOrigin hh) = input.(in_rightOriginId)
                by rewrite HoR -HoeqR Hin_r.
              rewrite (decide_True _ _ HoeqRR) in Hloop.
              injection Hloop as HdestL.
              wp_auto.
              iEval (rewrite -Hcloc0) in "Hcival". iAssert (own_item_node (ic_loc ci) dq (input_of_run (cell_run ci)) (ic_deleted ci) (ic_parent ci) prev_ci nxt_ci) with "[Hcival]" as "Hnode_ci". { iExists iv_ci, olid_ci, orid_ci. iFrame "Hcival Hcol Hcor". iPureIntro. split_and!; [exact Hinl_ci | exact Hinr_ci | exact Hcidn_ci | exact Hccontn_ci | exact Hcpar_ci | exact Hprev_ci | exact Hnext_ci | exact Hcflags_ci]. } iDestruct ("Hback" with "Hnode_ci") as "Hdll".
              wp_for_post.
              iApply ("HΦ" $! (node_loc cells (Z.of_nat curD - 1))).
              iSplitL "Hparent Hdll". { iExists yt0, tl0. iFrame "Hparent Hdll". done. }
              iSplitL. { rewrite /own_fresh_item_raw. iFrame "Hitem Holeft Horight". iPureIntro; split_and!; done. }
              iExists curD. iPureIntro. split_and!;
                [done | rewrite HcurD HdestL -Hd_eq Z2Nat.id; [done | clear -Hdest HdestL HleftLB; lia] | exact HcurDb].
           ++ (* different right origin: keep scanning, anchor unchanged *)
              have HneqRR : origin_id (rightOrigin hh) ≠ input.(in_rightOriginId).
              { rewrite HoR -Hin_r; move=> Heq; apply HoeqR; by rewrite Heq. }
              rewrite (decide_False _ _ HneqRR) in Hloop.
              wp_auto.
              wp_for_post.
              iEval (rewrite -Hcloc0) in "Hcival". iAssert (own_item_node (ic_loc ci) dq (input_of_run (cell_run ci)) (ic_deleted ci) (ic_parent ci) prev_ci nxt_ci) with "[Hcival]" as "Hnode_ci". { iExists iv_ci, olid_ci, orid_ci. iFrame "Hcival Hcol Hcor". iPureIntro. split_and!; [exact Hinl_ci | exact Hinr_ci | exact Hcidn_ci | exact Hccontn_ci | exact Hcpar_ci | exact Hprev_ci | exact Hnext_ci | exact Hcflags_ci]. } iDestruct ("Hback" with "Hnode_ci") as "Hdll".
              iFrame "HΦ item".
              iExists (offset + length (ic_run ci))%nat, (S cur), curD, (char_ids (ic_run ci) ∪ idsB), (char_ids (ic_run ci) ∪ conflictI), destL.
              rewrite /integrate_loop_inv /own_fresh_item_raw.
              iSplitL "Hparent Hdll Hconflict Hleft Hright Hibo_ref Hibo_sl Hibo_cap Hci_ref Hci_sl Hci_cap"; last first.
              { iFrame "Hitem Holeft Horight".
                iPureIntro; split_and!; [exact Hin_l0|exact Hin_r0|exact Hid0|exact Hcontent0]. }
              iSplitL "Hparent Hdll". { iExists yt0, tl0. iFrame "Hparent Hdll". done. }
              iSplitL "Hconflict".
              { rewrite Hcr0. replace (Z.of_nat (S cur))%Z with (Z.of_nat cur + 1)%Z by lia. iFrame "Hconflict". }
              iSplitL "Hleft". { iFrame "Hleft". }
              iSplitL "Hright". { iFrame "Hright". }
              iSplitL "Hibo_ref Hibo_sl Hibo_cap".
              { iExists ibo_s2. iFrame "Hibo_ref". iExists _. iFrame "Hibo_sl Hibo_cap". iPureIntro.
                split; [exact Hibo_wf2 | exact Hibo_set2]. }
              iSplitL "Hci_ref Hci_sl Hci_cap".
              { iExists ci_s2. iFrame "Hci_ref". iExists _. iFrame "Hci_sl Hci_cap". iPureIntro.
                split; [exact Hci_wf2 | exact Hci_set2]. }
              iPureIntro; split_and!;
                [lia
                | rewrite HlenS; clear -Hcur; lia
                | lia
                | exact HcurD | exact HcurDb
                | lia | clear -Hdest; lia
                | rewrite Nat2Z.inj_add; clear -Hblockfits; lia
                | exact Hloop].
      * (* different left origin from the new item *)
        have HoLne : origin_id (origin hh) ≠ input.(in_originId)
          by (rewrite HoL -Hin_l; move=> Heq; apply Hoeq; by rewrite Heq).
        rewrite (decide_False _ _ HoLne) in Hloop.
        rewrite HoL in Hloop.
        destruct olid_ci as [idv|] eqn:Hcoleft; last first.
        -- (* conflict has no left origin: origins would cross -> break *)
           iDestruct "Hcol" as "%Hcol_null".
           simpl in Hloop. injection Hloop as HdestL.
           wp_auto. rewrite Hcol_null. wp_auto.
           iEval (rewrite -Hcloc0) in "Hcival". iAssert (own_item_node (ic_loc ci) dq (input_of_run (cell_run ci)) (ic_deleted ci) (ic_parent ci) prev_ci nxt_ci) with "[Hcival]" as "Hnode_ci". { iExists iv_ci, None, orid_ci. iFrame "Hcival Hcor". iSplitR; [iPureIntro; exact Hcol_null|]. iPureIntro. split_and!; [exact Hinl_ci | exact Hinr_ci | exact Hcidn_ci | exact Hccontn_ci | exact Hcpar_ci | exact Hprev_ci | exact Hnext_ci | exact Hcflags_ci]. } iDestruct ("Hback" with "Hnode_ci") as "Hdll".
           wp_for_post.
           iApply ("HΦ" $! (node_loc cells (Z.of_nat curD - 1))).
           iSplitL "Hparent Hdll". { iExists yt0, tl0. iFrame "Hparent Hdll". done. }
           iSplitL. { rewrite /own_fresh_item_raw. iFrame "Hitem Holeft Horight". iPureIntro; split_and!; done. }
           iExists curD. iPureIntro. split_and!;
             [done | rewrite HcurD HdestL -Hd_eq Z2Nat.id; [done | clear -Hdest HdestL HleftLB; lia] | exact HcurDb].
        -- (* conflict has a left origin [idv] (different from the new item's) *)
           iDestruct "Hcol" as "[%Hcol_nn #Hcol_pt]".
           iAssert (is_origin_id iv_ci.(yjs.item.originLeftId') (Some idv)) as "#Hcol".
           { iSplit; [iPureIntro; exact Hcol_nn | iExact "Hcol_pt"]. }
           simpl in Hloop.
           wp_auto. rewrite bool_decide_eq_false_2; last exact Hcol_nn. wp_auto.
           (* the block-query bridge: the Go queries the whole run's span, [set_find_integration]
              decides the head-only set; they agree by the origin-clock invariant *)
           have Horig_eq : origin_id (origin (run_head ci)) = Some (toYjsId idv)
             by rewrite Hcolid_ci ?Hcoleft.
           have Hquery_clk : clientId (toYjsId idv) = clientId (item_id hh) -> (clock (toYjsId idv) < S (clock (item_id hh)))%nat.
           { move=> Hcl. have Hoc := Hoclk ci (list_elem_of_lookup_2 _ _ _ Hci).
             have Hlt := Hoc (toYjsId idv) Horig_eq. rewrite Hrhead in Hlt. specialize (Hlt Hcl). lia. }
           have Hbq_ibo : toYjsId idv ∈ char_ids (ic_run ci) ∪ idsB <-> toYjsId idv ∈ ({[item_id hh]} ∪ idsB : gset YjsId).
           { rewrite Hrun. apply (block_query_head hh tl2 (toYjsId idv) idsB Hrunstep Hquery_clk). }
           wp_apply (wp_containsId _ _ _ _ Hibo_wf2 with "[$Hibo_sl]"). iIntros "Hibo_sl".
           rewrite Hibo_set2.
           destruct (decide (toYjsId idv ∈ (char_ids (ic_run ci) ∪ idsB : gset YjsId))) as [Hin_ibo | Hnin_ibo].
           ++ (* conflict's left origin was already scanned (case 2) *)
              rewrite (bool_decide_eq_true_2 _ Hin_ibo).
              have Hin_ibo_head : toYjsId idv ∈ ({[item_id hh]} ∪ idsB : gset YjsId) by apply Hbq_ibo.
              rewrite (decide_True _ _ Hin_ibo_head) in Hloop.
              wp_auto.
              have Hbq_ci : toYjsId idv ∈ char_ids (ic_run ci) ∪ conflictI <-> toYjsId idv ∈ ({[item_id hh]} ∪ conflictI : gset YjsId).
              { rewrite Hrun. apply (block_query_head hh tl2 (toYjsId idv) conflictI Hrunstep Hquery_clk). }
              wp_apply (wp_containsId _ _ _ _ Hci_wf2 with "[$Hci_sl]"). iIntros "Hci_sl".
              rewrite Hci_set2.
              destruct (decide (toYjsId idv ∈ (char_ids (ic_run ci) ∪ conflictI : gset YjsId))) as [Hin_ci | Hnin_ci].
              ** (* already in conflictingItems: no anchor move, keep scanning (continue) *)
                 rewrite (bool_decide_eq_true_2 _ Hin_ci).
                 have Hin_ci_head : toYjsId idv ∈ ({[item_id hh]} ∪ conflictI : gset YjsId) by apply Hbq_ci.
                 have Hnn : ¬ (toYjsId idv ∉ ({[item_id hh]} ∪ conflictI : gset YjsId))
                   by (move=> Hcontra; exact (Hcontra Hin_ci_head)).
                 rewrite (decide_False _ _ Hnn) in Hloop.
                 wp_auto.
                 wp_for_post.
                 iEval (rewrite -Hcloc0) in "Hcival". iAssert (own_item_node (ic_loc ci) dq (input_of_run (cell_run ci)) (ic_deleted ci) (ic_parent ci) prev_ci nxt_ci) with "[Hcival]" as "Hnode_ci". { iExists iv_ci, (Some idv), orid_ci. iFrame "Hcival Hcol Hcor". iPureIntro. split_and!; [exact Hinl_ci | exact Hinr_ci | exact Hcidn_ci | exact Hccontn_ci | exact Hcpar_ci | exact Hprev_ci | exact Hnext_ci | exact Hcflags_ci]. } iDestruct ("Hback" with "Hnode_ci") as "Hdll".
                 iFrame "HΦ item".
                 iExists (offset + length (ic_run ci))%nat, (S cur), curD, (char_ids (ic_run ci) ∪ idsB), (char_ids (ic_run ci) ∪ conflictI), destL.
                 rewrite /integrate_loop_inv /own_fresh_item_raw.
                 iSplitL "Hparent Hdll Hconflict Hleft Hright Hibo_ref Hibo_sl Hibo_cap Hci_ref Hci_sl Hci_cap"; last first.
                 { iFrame "Hitem Holeft Horight".
                   iPureIntro; split_and!; [exact Hin_l0|exact Hin_r0|exact Hid0|exact Hcontent0]. }
                 iSplitL "Hparent Hdll". { iExists yt0, tl0. iFrame "Hparent Hdll". done. }
                 iSplitL "Hconflict".
                 { rewrite Hcr0. replace (Z.of_nat (S cur))%Z with (Z.of_nat cur + 1)%Z by lia. iFrame "Hconflict". }
                 iSplitL "Hleft". { iFrame "Hleft". }
                 iSplitL "Hright". { iFrame "Hright". }
                 iSplitL "Hibo_ref Hibo_sl Hibo_cap".
                 { iExists ibo_s2. iFrame "Hibo_ref". iExists _. iFrame "Hibo_sl Hibo_cap". iPureIntro.
                   split; [exact Hibo_wf2 | exact Hibo_set2]. }
                 iSplitL "Hci_ref Hci_sl Hci_cap".
                 { iExists ci_s2. iFrame "Hci_ref". iExists _. iFrame "Hci_sl Hci_cap". iPureIntro.
                   split; [exact Hci_wf2 | exact Hci_set2]. }
                 iPureIntro; split_and!;
                   [lia
                   | rewrite HlenS; clear -Hcur; lia
                   | lia
                   | exact HcurD | exact HcurDb
                   | lia | clear -Hdest; lia
                   | rewrite Nat2Z.inj_add; clear -Hblockfits; lia
                   | exact Hloop].
              ** (* not yet in conflictingItems: advance the anchor (left := conflict) *)
                 rewrite (bool_decide_eq_false_2 _ Hnin_ci).
                 have Hnin_ci_head : toYjsId idv ∉ ({[item_id hh]} ∪ conflictI : gset YjsId)
                   by (move=> Hcontra; apply Hnin_ci; apply Hbq_ci; exact Hcontra).
                 rewrite (decide_True _ _ Hnin_ci_head) in Hloop.
                 wp_auto.
                 wp_apply wp_slice_literal. iSplitR; first done.
                 iIntros "%ci_empty [Hci_empty Hci_empty_cap]". wp_auto.
                 wp_for_post.
                 iEval (rewrite -Hcloc0) in "Hcival". iAssert (own_item_node (ic_loc ci) dq (input_of_run (cell_run ci)) (ic_deleted ci) (ic_parent ci) prev_ci nxt_ci) with "[Hcival]" as "Hnode_ci". { iExists iv_ci, (Some idv), orid_ci. iFrame "Hcival Hcol Hcor". iPureIntro. split_and!; [exact Hinl_ci | exact Hinr_ci | exact Hcidn_ci | exact Hccontn_ci | exact Hcpar_ci | exact Hprev_ci | exact Hnext_ci | exact Hcflags_ci]. } iDestruct ("Hback" with "Hnode_ci") as "Hdll".
                 iFrame "HΦ item".
                 iExists (offset + length (ic_run ci))%nat, (S cur), (S cur), (char_ids (ic_run ci) ∪ idsB), ∅, (leftIdx + Z.of_nat (offset + length (ic_run ci)))%Z.
                 rewrite /integrate_loop_inv /own_fresh_item_raw.
                 iSplitL "Hparent Hdll Hconflict Hleft Hright Hibo_ref Hibo_sl Hibo_cap Hci_ref Hci_empty Hci_empty_cap"; last first.
                 { iFrame "Hitem Holeft Horight".
                   iPureIntro; split_and!; [exact Hin_l0|exact Hin_r0|exact Hid0|exact Hcontent0]. }
                 iSplitL "Hparent Hdll". { iExists yt0, tl0. iFrame "Hparent Hdll". done. }
                 iSplitL "Hconflict".
                 { rewrite Hcr0. replace (Z.of_nat (S cur))%Z with (Z.of_nat cur + 1)%Z by lia. iFrame "Hconflict". }
                 iSplitL "Hleft".
                 { replace (Z.of_nat (S cur) - 1)%Z with (Z.of_nat cur)%Z by lia. iFrame "Hleft". }
                 iSplitL "Hright". { iFrame "Hright". }
                 iSplitL "Hibo_ref Hibo_sl Hibo_cap".
                 { iExists ibo_s2. iFrame "Hibo_ref". iExists _. iFrame "Hibo_sl Hibo_cap". iPureIntro.
                   split; [exact Hibo_wf2 | exact Hibo_set2]. }
                 iSplitL "Hci_ref Hci_empty Hci_empty_cap".
                 { iExists _. iFrame "Hci_ref". iExists ([] : list yjs.idSpan.t). iFrame "Hci_empty Hci_empty_cap".
                 iPureIntro. split; [constructor | done]. }
                 iPureIntro; split_and!;
                   [lia
                   | rewrite HlenS; clear -Hcur; lia
                   | lia
                   | rewrite HlenS; clear -Hcur; lia
                   | lia | lia | lia
                   | rewrite Nat2Z.inj_add; clear -Hblockfits; lia
                   | exact Hloop].
           ++ (* conflict's left origin is before this run: origins cross -> break *)
              rewrite (bool_decide_eq_false_2 _ Hnin_ibo).
              have Hnin_ibo_head : toYjsId idv ∉ ({[item_id hh]} ∪ idsB : gset YjsId)
                by (move=> Hcontra; apply Hnin_ibo; apply Hbq_ibo; exact Hcontra).
              rewrite (decide_False _ _ Hnin_ibo_head) in Hloop.
              injection Hloop as HdestL.
              wp_auto.
              iEval (rewrite -Hcloc0) in "Hcival". iAssert (own_item_node (ic_loc ci) dq (input_of_run (cell_run ci)) (ic_deleted ci) (ic_parent ci) prev_ci nxt_ci) with "[Hcival]" as "Hnode_ci". { iExists iv_ci, (Some idv), orid_ci. iFrame "Hcival Hcol Hcor". iPureIntro. split_and!; [exact Hinl_ci | exact Hinr_ci | exact Hcidn_ci | exact Hccontn_ci | exact Hcpar_ci | exact Hprev_ci | exact Hnext_ci | exact Hcflags_ci]. } iDestruct ("Hback" with "Hnode_ci") as "Hdll".
              wp_for_post.
              iApply ("HΦ" $! (node_loc cells (Z.of_nat curD - 1))).
              iSplitL "Hparent Hdll". { iExists yt0, tl0. iFrame "Hparent Hdll". done. }
              iSplitL. { rewrite /own_fresh_item_raw. iFrame "Hitem Holeft Horight". iPureIntro; split_and!; done. }
              iExists curD. iPureIntro. split_and!;
                [done | rewrite HcurD HdestL -Hd_eq Z2Nat.id; [done | clear -Hdest HdestL HleftLB; lia] | exact HcurDb].
Qed.

(** The conflict scan with its entry guard: resolves whether to scan at all
    (y-octo's left/right-connection check), sets the initial cursor, and
    delegates to [scanConflicts]. The anchors are CELL cursors: [left_loc] is
    the cell before the boundary [curL] (model index [leftIdx + 1]),
    [right_loc] the cell at [curR] (model index [rightIdx]). When the guard is
    false the anchors are adjacent cells ([curL = curR], i.e.
    [leftIdx + 1 = rightIdx] by prefix-sum injectivity) so [destIdx = leftIdx
    + 1] and the unchanged [left] is the answer. *)
Lemma wp_findIntegrationLeft (parent item_l left_loc right_loc : loc) (dq : dfrac)
    (cells : list item_cell) (arr : list (YjsItem A))
    (input : IntegrateInput (A := A)) (newItem : YjsItem A)
    (itemVal : yjs.item.t) (oleft oright : option yjs.id.t)
    (leftIdx rightIdx : Z) (destIdx : nat) (curL curR : nat) :
  YjsArrInvariant arr ->
  toItem input arr = Some newItem ->
  IsItemValid newItem ->
  maximalId newItem arr ->
  findLeftIdx (in_originId input) arr = Some leftIdx ->
  findRightIdx (in_rightOriginId input) arr = Some rightIdx ->
  setfindIntegratedIndex leftIdx rightIdx input arr = Some destIdx ->
  left_loc = node_loc cells (Z.of_nat curL - 1) ->
  right_loc = node_loc cells (Z.of_nat curR) ->
  Forall (λ c, ic_run c ≠ []) cells ->
  (∀ c0, c0 ∈ cells -> cell_fits c0) ->
  (∀ c0, c0 ∈ cells -> cell_origin_clk c0) ->
  (Z.of_nat (length (run_flatten (take curL cells))) = leftIdx + 1)%Z ->
  (curL <= length cells)%nat ->
  (Z.of_nat (length (run_flatten (take curR cells))) = rightIdx)%Z ->
  (curR <= length cells)%nat ->
  {{{ is_pkg_init yjs ∗ own_ytype_cells parent dq cells arr ∗
      own_fresh_item_raw item_l input itemVal oleft oright }}}
    @! yjs.findIntegrationLeft #parent #item_l #left_loc #right_loc
  {{{ (ret : loc), RET #ret;
      own_ytype_cells parent dq cells arr ∗
      own_fresh_item_raw item_l input itemVal oleft oright ∗
      ∃ curD : nat, ⌜ret = node_loc cells (Z.of_nat curD - 1)⌝ ∗
        ⌜(Z.of_nat (length (run_flatten (take curD cells))) = Z.of_nat destIdx)%Z⌝ ∗
        ⌜(curD <= length cells)%nat⌝ }}}.
Proof using Type*.
  move=> Harr Htoitem Hvalid Hmax HfindL HfindR HfindD Hll Hrl Hnec Hfits Hoclk HcurL HcurLb HcurR HcurRb.
  wp_start as "(Htext & Hfresh)". iNamed "Htext". iNamed "Hfresh". wp_auto.
  (* Index bounds via the pure model (mirrors setintegrate_eq_integrate). *)
  have Huniq := yai_unique _ Harr.
  have HfLp : findPtrIdx (origin newItem) arr = Some leftIdx.
  { rewrite -(toitem_lemmas.findLeftIdx_findPtrIdx_eq input newItem arr Huniq Htoitem). exact HfindL. }
  have HfRp : findPtrIdx (rightOrigin newItem) arr = Some rightIdx.
  { rewrite -(toitem_lemmas.findRightIdx_findPtrIdx_eq input newItem arr Huniq Htoitem). exact HfindR. }
  have Horig := findptridx_getelem.findPtrIdx_ArrSet arr (origin newItem) leftIdx HfLp.
  have Hror := findptridx_getelem.findPtrIdx_ArrSet arr (rightOrigin newItem) rightIdx HfRp.
  have HlB := insert_lemmas.findPtrIdx_ge_minus_1 arr (origin newItem) leftIdx HfLp.
  have Hlr := findptridx_order2.YjsLt'_findPtrIdx_lt arr (origin newItem) (rightOrigin newItem)
                leftIdx rightIdx Harr Horig Hror (iiv_origin_lt _ Hvalid) HfLp HfRp.
  have HrUB := insert_lemmas.findPtrIdx_le_size arr (rightOrigin newItem) rightIdx HfRp.
  have Hrfl : arr = run_flatten cells := Hrepr.
  (* the left boundary cell precedes the right boundary cell *)
  have HcurLR : (curL <= curR)%nat.
  { apply (run_flatten_take_length_le_inv cells curL curR Hnec HcurLb).
    clear -HcurL HcurR Hlr. lia. }
  (* Entry guard: read the left/right neighbour connections to decide whether
     the conflict scan runs. Four boundary combos: left/right null? *)
  destruct (decide (curR = length cells)) as [HrN | HrNN].
  { (* right is null: rightIsNullOrHasLeft = true (no read of right.left) *)
    have Hrnull : right_loc = null.
    { rewrite Hrl HrN /node_loc decide_True; last lia. rewrite Nat2Z.id lookup_ge_None_2; [done | lia]. }
    rewrite (bool_decide_eq_true_2 (right_loc = null) Hrnull). wp_auto.
    destruct (decide (curL = 0%nat)) as [Hl0 | HlP].
    { (* combo 1: left null -> scan from parent.start *)
      have Hlnull : left_loc = null.
      { rewrite Hll Hl0 /node_loc. case_decide; [lia | done]. }
      rewrite Hlnull. wp_auto.
      iAssert (⌜yt.(yjs.yType.start') = node_loc cells 0⌝ ∗ own_dll dq parent yt.(yjs.yType.start') tl null null cells)%I with "[Hdll]" as "[%Hstart Hdll]".
      { destruct cells as [|c rest].
        { iDestruct "Hdll" as %[Hl Hlst]. iSplit; iPureIntro; [rewrite Hl /node_loc // | split; [exact Hl | exact Hlst]]. }
        iDestruct "Hdll" as (ivh olidh oridh) "(%Hloch & %Hprevh & %Hparh & %Hidh & %Hconth & %Holidh & %Horidh & %Hflagsh & %Hrunh & Hvalh & #Holefth & #Horighth & Hresth)".
        iSplitR.
        { iPureIntro. rewrite /node_loc /=. by destruct Hloch as [-> _]. }
        iExists ivh, olidh, oridh. iFrame "Hvalh Holefth Horighth Hresth".
        iPureIntro; split_and!; [exact (proj1 Hloch) | exact (proj2 Hloch) | exact Hprevh | exact Hparh | exact Hidh | exact Hconth | exact Holidh | exact Horidh | exact Hflagsh | exact Hrunh]. }
      replace (# null) with (# (node_loc cells (Z.of_nat curL - 1))) by (rewrite -Hll Hlnull //).
      replace (yt.(yjs.yType.start')) with (node_loc cells (Z.of_nat curL)) by (rewrite Hstart Hl0 //).
      rewrite Hrl.
      wp_apply (wp_scanConflicts parent item_l dq cells arr input newItem itemVal oleft oright leftIdx rightIdx destIdx curL curR
                  Harr Htoitem Hvalid Hmax HfindL HfindR HfindD Hnec Hfits Hoclk HcurL HcurLb HcurR HcurRb with "[Hparent Hdll Hitem Holeft Horight]").
      { iSplitL "Hparent Hdll".
        { iExists yt, tl. iFrame "Hparent".
          replace (yt.(yjs.yType.start')) with (node_loc cells (Z.of_nat curL)) by (rewrite Hstart Hl0 //).
          iFrame "Hdll". done. }
        rewrite /own_fresh_item_raw. iFrame "Hitem Holeft Horight". iPureIntro; split_and!; done. }
      iIntros (v) "(Htext & Hfresh & Hpost)". wp_auto.
      iApply ("HΦ" $! v). iFrame "Htext Hfresh Hpost". }
    { (* combo 3: left non-null, right null -> compare left.right with right *)
      have HlP' : (1 <= curL)%nat by lia.
      have Hi_lt : (curL - 1 < length cells)%nat by lia.
      destruct (cells !! (curL - 1)%nat) as [leftCell|] eqn:Hcl_lookup; last by (apply lookup_ge_None in Hcl_lookup; lia).
      have Hcl_loc : node_loc cells (Z.of_nat curL - 1) = ic_loc leftCell.
      { rewrite /node_loc decide_True; last lia.
        have -> : Z.to_nat (Z.of_nat curL - 1) = (curL - 1)%nat by lia.
        rewrite Hcl_lookup //. }
      iAssert (⌜ic_loc leftCell ≠ null⌝ ∗ own_dll dq parent yt.(yjs.yType.start') tl null null cells)%I with "[Hdll]" as "[%Hclnn Hdll]".
      { iDestruct (own_dll_lookup_acc_node _ _ _ _ _ _ _ _ Hcl_lookup with "Hdll") as (px nx) "(_ & _ & _ & Hnode & Hbk)".
        iDestruct (own_item_node_not_null with "Hnode") as "[%Hnn Hnode]".
        iDestruct ("Hbk" with "Hnode") as "Hdll". iSplitR; [done | iFrame "Hdll"]. }
      have Hlnn : left_loc ≠ null by rewrite Hll Hcl_loc; exact Hclnn.
      rewrite (bool_decide_eq_false_2 (left_loc = null) Hlnn).
      iDestruct (own_dll_acc_node _ cells _ _ (curL - 1)%nat leftCell Hcl_lookup with "Hdll")
        as (prevl nxtl) "(%Hcloc & %Hcl_l & %Hcr_l & %Hrunl & %Hclenl & %Hpcl & Hnode & Hback)".
      iDestruct "Hnode" as (ivl olidl oridl)
        "(Hcval & Hcol_l & Hcor_l & %Hinl_l & %Hinr_l & %Hidl & %Hcontl & %Hparl & %Hprevl & %Hnextl & %Hflagsl)".
      iEval (rewrite -Hcl_loc) in "Hcval". iEval (rewrite Hll) in "left". wp_auto.
      have Hcr_l' : ivl.(yjs.item.right') = node_loc cells (Z.of_nat curL).
      { rewrite Hnextl Hcr_l. f_equal. lia. }
      rewrite Hcr_l' Hrl.
      iEval (rewrite Hcl_loc) in "Hcval".
      iAssert (own_item_node (ic_loc leftCell) dq (input_of_run (cell_run leftCell))
                 (ic_deleted leftCell) (ic_parent leftCell) prevl nxtl) with "[Hcval Hcol_l Hcor_l]" as "Hnode".
      { iExists ivl, olidl, oridl. iFrame "Hcval Hcol_l Hcor_l".
        iPureIntro. split_and!;
          [exact Hinl_l | exact Hinr_l | exact Hidl | exact Hcontl | exact Hparl
          | exact Hprevl | exact Hnextl | exact Hflagsl]. }
      iDestruct ("Hback" with "Hnode") as "Hdll".
      iAssert (own_ytype_cells parent dq cells arr) with "[Hparent Hdll]" as "Htext".
      { iExists yt, tl. iFrame "Hparent Hdll". done. }
      wp_apply (wp_itemPtrEqual_node parent dq cells arr (Z.of_nat curL) (Z.of_nat curR) Harr Hnec ltac:(lia) ltac:(lia) ltac:(lia) with "[$Htext]").
      iIntros "Htext".
      destruct (decide (Z.of_nat curL = Z.of_nat curR)) as [Hadj | Hnadj].
      { (* no scan: curL = curR -> leftIdx+1 = rightIdx -> destIdx = leftIdx+1 *)
        rewrite (bool_decide_eq_true_2 _ Hadj). wp_auto.
        rewrite (bool_decide_eq_false_2 (node_loc cells (Z.of_nat curL - 1) = null) ltac:(rewrite -Hll; exact Hlnn)). wp_auto.
        have HcLR : curL = curR by lia.
        have Hadj' : (leftIdx + 1 = rightIdx)%Z by rewrite -HcurL -HcurR HcLR.
        have Hdestadj : Z.of_nat destIdx = (leftIdx + 1)%Z.
        { rewrite /setfindIntegratedIndex in HfindD.
          replace (Z.to_nat (rightIdx - leftIdx) - 1)%nat with 0%nat in HfindD by lia.
          simpl in HfindD. injection HfindD as HfindD'. rewrite -HfindD' Z2Nat.id; lia. }
        iApply ("HΦ" $! (node_loc cells (Z.of_nat curL - 1))).
        iFrame "Htext".
        iSplitL. { rewrite /own_fresh_item_raw. iFrame "Hitem Holeft Horight". iPureIntro; split_and!; done. }
        iExists curL. iPureIntro. split_and!;
          [done | rewrite HcurL Hdestadj // | exact HcurLb]. }
      { (* scan: curL < curR, conflict = left.right *)
        rewrite (bool_decide_eq_false_2 _ Hnadj). wp_auto.
        have Hlnn' : node_loc cells (Z.of_nat curL - 1) ≠ null by (rewrite -Hll; exact Hlnn).
        rewrite (bool_decide_eq_false_2 (node_loc cells (Z.of_nat curL - 1) = null) Hlnn'). wp_auto.
        rewrite (bool_decide_eq_false_2 (node_loc cells (Z.of_nat curL - 1) = null) Hlnn').
        iDestruct "Htext" as (yt' tl') "(Hparent & Hdll & %Hlen' & %Hrepr' & %Hcpar')".
        iDestruct (own_dll_acc_node _ cells _ _ (curL - 1)%nat leftCell Hcl_lookup with "Hdll")
          as (prevl2 nxtl2) "(%Hcloc2 & %Hcl_l2 & %Hcr_l2 & %Hrunl2 & %Hclenl2 & %Hpcl2 & Hnode & Hback)".
        iDestruct "Hnode" as (ivl2 olidl2 oridl2)
          "(Hcval & Hcol2 & Hcor2 & %Hinl2 & %Hinr2 & %Hidl2 & %Hcontl2 & %Hparl2 & %Hprevl2 & %Hnextl2 & %Hflagsl2)".
        have Hcr_l2' : ivl2.(yjs.item.right') = node_loc cells (Z.of_nat curL) by (rewrite Hnextl2 Hcr_l2; f_equal; lia).
        iEval (rewrite -Hcl_loc) in "Hcval". wp_auto. rewrite Hcr_l2'.
        iEval (rewrite Hcl_loc) in "Hcval".
        iAssert (own_item_node (ic_loc leftCell) dq (input_of_run (cell_run leftCell))
                   (ic_deleted leftCell) (ic_parent leftCell) prevl2 nxtl2) with "[Hcval Hcol2 Hcor2]" as "Hnode".
        { iExists ivl2, olidl2, oridl2. iFrame "Hcval Hcol2 Hcor2".
          iPureIntro. split_and!;
            [exact Hinl2 | exact Hinr2 | exact Hidl2 | exact Hcontl2 | exact Hparl2
            | exact Hprevl2 | exact Hnextl2 | exact Hflagsl2]. }
        iDestruct ("Hback" with "Hnode") as "Hdll".
        iAssert (own_ytype_cells parent dq cells arr) with "[Hparent Hdll]" as "Htext".
        { iExists yt', tl'. iFrame "Hparent Hdll". iPureIntro; split_and!; [exact Hlen' | exact Hrepr' | exact Hcpar']. }
        wp_apply (wp_scanConflicts parent item_l dq cells arr input newItem itemVal oleft oright leftIdx rightIdx destIdx curL curR
                    Harr Htoitem Hvalid Hmax HfindL HfindR HfindD Hnec Hfits Hoclk HcurL HcurLb HcurR HcurRb with "[Htext Hitem Holeft Horight]").
        { iSplitL "Htext"; [iFrame "Htext" | rewrite /own_fresh_item_raw; iFrame "Hitem Holeft Horight"; iPureIntro; split_and!; done]. }
        iIntros (v) "(Htext & Hfresh & Hpost)". wp_auto.
        iApply ("HΦ" $! v). iFrame "Htext Hfresh Hpost". } } }
  { (* right non-null (curR < length cells): read right.left *)
    have Hr_lt : (curR < length cells)%nat by lia.
    destruct (cells !! curR) as [rightCell|] eqn:Hcr_lookup; last by (apply lookup_ge_None in Hcr_lookup; lia).
    have Hcr_loc : node_loc cells (Z.of_nat curR) = ic_loc rightCell.
    { rewrite /node_loc decide_True; last lia. rewrite Nat2Z.id Hcr_lookup //. }
    iAssert (⌜ic_loc rightCell ≠ null⌝ ∗ own_dll dq parent yt.(yjs.yType.start') tl null null cells)%I with "[Hdll]" as "[%Hcrnn Hdll]".
    { iDestruct (own_dll_lookup_acc_node _ _ _ _ _ _ _ _ Hcr_lookup with "Hdll") as (px nx) "(_ & _ & _ & Hnode & Hbk)".
      iDestruct (own_item_node_not_null with "Hnode") as "[%Hnn Hnode]".
      iDestruct ("Hbk" with "Hnode") as "Hdll". iSplitR; [done | iFrame "Hdll"]. }
    have Hrnn : right_loc ≠ null by rewrite Hrl Hcr_loc; exact Hcrnn.
    rewrite (bool_decide_eq_false_2 (right_loc = null) Hrnn).
    iDestruct (own_dll_acc_node _ cells _ _ curR rightCell Hcr_lookup with "Hdll")
      as (prevr nxtr) "(%Hcloc_r & %Hclr0 & %Hcrr0 & %Hrunr & %Hclenr & %Hpcr & Hnode & Hback)".
    iDestruct "Hnode" as (ivr olidr oridr)
      "(Hcrval & Hcol_r & Hcor_r & %Hinlr & %Hinrr & %Hidrn & %Hcontrn & %Hparr & %Hprevr & %Hnextr & %Hflagsr)".
    have Hcl_r : ivr.(yjs.item.left') = node_loc cells (Z.of_nat curR - 1).
    { rewrite Hprevr. exact Hclr0. }
    have Hidr : item_id (run_head rightCell) = toYjsId ivr.(yjs.item.id').
    { symmetry. exact Hidrn. }
    have Holidr : origin_id (origin (run_head rightCell)) = toYjsId <$> olidr.
    { symmetry. exact Hinlr. }
    have Horidr : origin_id (rightOrigin (run_head rightCell)) = toYjsId <$> oridr.
    { symmetry. exact Hinrr. }
    iEval (rewrite -Hcr_loc) in "Hcrval". iEval (rewrite Hrl) in "right". wp_auto.
    iEval (rewrite Hcr_loc) in "Hcrval".
    iAssert (own_item_node (ic_loc rightCell) dq (input_of_run (cell_run rightCell))
               (ic_deleted rightCell) (ic_parent rightCell) prevr nxtr) with "[Hcrval Hcol_r Hcor_r]" as "Hnode".
    { iExists ivr, olidr, oridr. iFrame "Hcrval Hcol_r Hcor_r".
      iPureIntro. split_and!;
        [exact Hinlr | exact Hinrr | exact Hidrn | exact Hcontrn | exact Hparr
        | exact Hprevr | exact Hnextr | exact Hflagsr]. }
    iDestruct ("Hback" with "Hnode") as "Hdll".
    destruct (decide (curL = 0%nat)) as [Hl0 | HlP].
    { (* combo 2: left null; guard = rightIsNullOrHasLeft = (curR != 0) *)
      have Hlnull : left_loc = null by (rewrite Hll Hl0 /node_loc; case_decide; [lia | done]).
      rewrite Hlnull.
      destruct (decide (curR = 0%nat)) as [Hr0 | HrP].
      { (* curR = 0 (rightIdx = 0): no scan *)
        have Hcrl_null : ivr.(yjs.item.left') = null.
        { rewrite Hcl_r Hr0 /node_loc. case_decide; [lia | done]. }
        rewrite Hcrl_null. wp_auto.
        have Hlm1 : leftIdx = (-1)%Z.
        { have H := HcurL. rewrite Hl0 take_0 run_flatten_nil /= in H. lia. }
        have Hr0' : rightIdx = 0%Z.
        { have H := HcurR. rewrite Hr0 take_0 run_flatten_nil /= in H. lia. }
        have Hdest0 : destIdx = 0%nat.
        { rewrite /setfindIntegratedIndex in HfindD.
          replace (Z.to_nat (rightIdx - leftIdx) - 1)%nat with 0%nat in HfindD by lia.
          simpl in HfindD. injection HfindD as HfindD'. lia. }
        iApply ("HΦ" $! null).
        iSplitR "Hitem Holeft Horight".
        { iExists yt, tl. iFrame "Hparent Hdll". done. }
        iSplitL. { rewrite /own_fresh_item_raw. iFrame "Hitem Holeft Horight". iPureIntro; split_and!; done. }
        iExists 0%nat. iPureIntro. split_and!;
          [rewrite /node_loc; case_decide; [lia | done]
          | rewrite take_0 run_flatten_nil /= Hdest0 //
          | lia]. }
      { (* curR >= 1: scan from parent.start *)
        have Hcrl_eq : ivr.(yjs.item.left') = node_loc cells (Z.of_nat curR - 1) := Hcl_r.
        have Hr1_lt : (curR - 1 < length cells)%nat by lia.
        destruct (cells !! (curR - 1)%nat) as [crl|] eqn:Hcrl_lookup; last by (apply lookup_ge_None in Hcrl_lookup; lia).
        have Hcrl_loc : node_loc cells (Z.of_nat curR - 1) = ic_loc crl.
        { rewrite /node_loc decide_True; last lia.
          have -> : Z.to_nat (Z.of_nat curR - 1) = (curR - 1)%nat by lia.
          rewrite Hcrl_lookup //. }
        iAssert (⌜ic_loc crl ≠ null⌝ ∗ own_dll dq parent yt.(yjs.yType.start') tl null null cells)%I with "[Hdll]" as "[%Hcrlnn Hdll]".
        { iDestruct (own_dll_lookup_acc_node _ _ _ _ _ _ _ _ Hcrl_lookup with "Hdll") as (px nx) "(_ & _ & _ & Hnode & Hb)".
          iDestruct (own_item_node_not_null with "Hnode") as "[%Hnn2 Hnode]".
          iDestruct ("Hb" with "Hnode") as "Hdll". iSplitR; [done | iFrame "Hdll"]. }
        have Hcrl_nn : ivr.(yjs.item.left') ≠ null by rewrite Hcrl_eq Hcrl_loc; exact Hcrlnn.
        rewrite (bool_decide_eq_false_2 (ivr.(yjs.item.left') = null) Hcrl_nn). wp_auto.
        iAssert (⌜yt.(yjs.yType.start') = node_loc cells 0⌝ ∗ own_dll dq parent yt.(yjs.yType.start') tl null null cells)%I with "[Hdll]" as "[%Hstart Hdll]".
        { iDestruct (own_dll_headptr with "Hdll") as "[%Hhd Hdll]".
          iFrame "Hdll". iPureIntro.
          rewrite Hhd /node_loc. destruct cells as [|c rest]; simpl.
          - done.
          - first [ done
                  | (rewrite decide_True; last (simpl; lia)); done
                  | case_decide; [done | exfalso; simpl in *; lia] ]. }
        replace (# null) with (# (node_loc cells (Z.of_nat curL - 1))) by (rewrite -Hll Hlnull //).
        replace (yt.(yjs.yType.start')) with (node_loc cells (Z.of_nat curL)) by (rewrite Hstart Hl0 //).
        wp_apply (wp_scanConflicts parent item_l dq cells arr input newItem itemVal oleft oright leftIdx rightIdx destIdx curL curR
                    Harr Htoitem Hvalid Hmax HfindL HfindR HfindD Hnec Hfits Hoclk HcurL HcurLb HcurR HcurRb with "[Hparent Hdll Hitem Holeft Horight]").
        { iSplitL "Hparent Hdll".
          { iExists yt, tl. iFrame "Hparent".
            replace (yt.(yjs.yType.start')) with (node_loc cells (Z.of_nat curL)) by (rewrite Hstart Hl0 //).
            iFrame "Hdll". done. }
          rewrite /own_fresh_item_raw. iFrame "Hitem Holeft Horight". iPureIntro; split_and!; done. }
        iIntros (v) "(Htext & Hfresh & Hpost)". wp_auto.
        iApply ("HΦ" $! v). iFrame "Htext Hfresh Hpost". } }
    { (* combo 4: left non-null, right non-null -> compare left.right with right *)
      have HlP' : (1 <= curL)%nat by lia.
      have Hi_lt : (curL - 1 < length cells)%nat by lia.
      destruct (cells !! (curL - 1)%nat) as [leftCell|] eqn:Hcl_lookup; last by (apply lookup_ge_None in Hcl_lookup; lia).
      have Hcl_loc : node_loc cells (Z.of_nat curL - 1) = ic_loc leftCell.
      { rewrite /node_loc decide_True; last lia.
        have -> : Z.to_nat (Z.of_nat curL - 1) = (curL - 1)%nat by lia.
        rewrite Hcl_lookup //. }
      iAssert (⌜ic_loc leftCell ≠ null⌝ ∗ own_dll dq parent yt.(yjs.yType.start') tl null null cells)%I with "[Hdll]" as "[%Hclnn Hdll]".
      { iDestruct (own_dll_lookup_acc_node _ _ _ _ _ _ _ _ Hcl_lookup with "Hdll") as (px nx) "(_ & _ & _ & Hnode & Hbk)".
        iDestruct (own_item_node_not_null with "Hnode") as "[%Hnn3 Hnode]".
        iDestruct ("Hbk" with "Hnode") as "Hdll". iSplitR; [done | iFrame "Hdll"]. }
      have Hlnn : left_loc ≠ null by rewrite Hll Hcl_loc; exact Hclnn.
      rewrite (bool_decide_eq_false_2 (left_loc = null) Hlnn).
      iDestruct (own_dll_acc_node _ cells _ _ (curL - 1)%nat leftCell Hcl_lookup with "Hdll")
        as (prevl4 nxtl4) "(%Hcloc & %Hcl_l & %Hcr_l2 & %Hrunl & %Hclenl4 & %Hpcl4 & Hnode & Hback)".
      iDestruct "Hnode" as (ivl olidl oridl)
        "(Hcval & Hcol_l & Hcor_l & %Hinl_l & %Hinr_l & %Hidl & %Hcontl & %Hparl & %Hprevl & %Hnextl & %Hflagsl)".
      iEval (rewrite -Hcl_loc) in "Hcval". iEval (rewrite Hll) in "left". wp_auto.
      have Hcr_l' : ivl.(yjs.item.right') = node_loc cells (Z.of_nat curL).
      { rewrite Hnextl Hcr_l2. f_equal. lia. }
      rewrite Hcr_l'.
      iEval (rewrite Hcl_loc) in "Hcval".
      iAssert (own_item_node (ic_loc leftCell) dq (input_of_run (cell_run leftCell))
                 (ic_deleted leftCell) (ic_parent leftCell) prevl4 nxtl4) with "[Hcval Hcol_l Hcor_l]" as "Hnode".
      { iExists ivl, olidl, oridl. iFrame "Hcval Hcol_l Hcor_l".
        iPureIntro. split_and!;
          [exact Hinl_l | exact Hinr_l | exact Hidl | exact Hcontl | exact Hparl
          | exact Hprevl | exact Hnextl | exact Hflagsl]. }
      iDestruct ("Hback" with "Hnode") as "Hdll".
      iAssert (own_ytype_cells parent dq cells arr) with "[Hparent Hdll]" as "Htext".
      { iExists yt, tl. iFrame "Hparent Hdll". done. }
      wp_apply (wp_itemPtrEqual_node parent dq cells arr (Z.of_nat curL) (Z.of_nat curR) Harr Hnec ltac:(lia) ltac:(lia) ltac:(lia) with "[$Htext]").
      iIntros "Htext".
      destruct (decide (Z.of_nat curL = Z.of_nat curR)) as [Hadj | Hnadj].
      { (* no scan *)
        rewrite (bool_decide_eq_true_2 _ Hadj). wp_auto.
        rewrite (bool_decide_eq_false_2 (node_loc cells (Z.of_nat curL - 1) = null) ltac:(rewrite -Hll; exact Hlnn)). wp_auto.
        have HcLR : curL = curR by lia.
        have Hadj' : (leftIdx + 1 = rightIdx)%Z by rewrite -HcurL -HcurR HcLR.
        have Hdestadj : Z.of_nat destIdx = (leftIdx + 1)%Z.
        { rewrite /setfindIntegratedIndex in HfindD.
          replace (Z.to_nat (rightIdx - leftIdx) - 1)%nat with 0%nat in HfindD by lia.
          simpl in HfindD. injection HfindD as HfindD'. rewrite -HfindD' Z2Nat.id; lia. }
        iApply ("HΦ" $! (node_loc cells (Z.of_nat curL - 1))).
        iFrame "Htext".
        iSplitL. { rewrite /own_fresh_item_raw. iFrame "Hitem Holeft Horight". iPureIntro; split_and!; done. }
        iExists curL. iPureIntro. split_and!;
          [done | rewrite HcurL Hdestadj // | exact HcurLb]. }
      { (* scan *)
        rewrite (bool_decide_eq_false_2 _ Hnadj). wp_auto.
        have Hlnn' : node_loc cells (Z.of_nat curL - 1) ≠ null by (rewrite -Hll; exact Hlnn).
        rewrite (bool_decide_eq_false_2 (node_loc cells (Z.of_nat curL - 1) = null) Hlnn'). wp_auto.
        rewrite (bool_decide_eq_false_2 (node_loc cells (Z.of_nat curL - 1) = null) Hlnn').
        iDestruct "Htext" as (yt' tl') "(Hparent & Hdll & %Hlen' & %Hrepr' & %Hcpar')".
        iDestruct (own_dll_acc_node _ cells _ _ (curL - 1)%nat leftCell Hcl_lookup with "Hdll")
          as (prevl2 nxtl2) "(%Hcloc2 & %Hcl_l2b & %Hcr_l2b & %Hrunl2 & %Hclenl2 & %Hpcl2 & Hnode & Hback)".
        iDestruct "Hnode" as (ivl2 olidl2 oridl2)
          "(Hcval & Hcol2 & Hcor2 & %Hinl2 & %Hinr2 & %Hidl2 & %Hcontl2 & %Hparl2 & %Hprevl2 & %Hnextl2 & %Hflagsl2)".
        have Hcr_l2' : ivl2.(yjs.item.right') = node_loc cells (Z.of_nat curL) by (rewrite Hnextl2 Hcr_l2b; f_equal; lia).
        iEval (rewrite -Hcl_loc) in "Hcval". wp_auto. rewrite Hcr_l2'.
        iEval (rewrite Hcl_loc) in "Hcval".
        iAssert (own_item_node (ic_loc leftCell) dq (input_of_run (cell_run leftCell))
                   (ic_deleted leftCell) (ic_parent leftCell) prevl2 nxtl2) with "[Hcval Hcol2 Hcor2]" as "Hnode".
        { iExists ivl2, olidl2, oridl2. iFrame "Hcval Hcol2 Hcor2".
          iPureIntro. split_and!;
            [exact Hinl2 | exact Hinr2 | exact Hidl2 | exact Hcontl2 | exact Hparl2
            | exact Hprevl2 | exact Hnextl2 | exact Hflagsl2]. }
        iDestruct ("Hback" with "Hnode") as "Hdll".
        iAssert (own_ytype_cells parent dq cells arr) with "[Hparent Hdll]" as "Htext".
        { iExists yt', tl'. iFrame "Hparent Hdll". iPureIntro; split_and!; [exact Hlen' | exact Hrepr' | exact Hcpar']. }
        wp_apply (wp_scanConflicts parent item_l dq cells arr input newItem itemVal oleft oright leftIdx rightIdx destIdx curL curR
                    Harr Htoitem Hvalid Hmax HfindL HfindR HfindD Hnec Hfits Hoclk HcurL HcurLb HcurR HcurRb with "[Htext Hitem Holeft Horight]").
        { iSplitL "Htext"; [iFrame "Htext" | rewrite /own_fresh_item_raw; iFrame "Hitem Holeft Horight"; iPureIntro; split_and!; done]. }
        iIntros (v) "(Htext & Hfresh & Hpost)". wp_auto.
        iApply ("HΦ" $! v). iFrame "Htext Hfresh Hpost". } } }
Qed.

(** [IsItemValid] never reads the content: both clauses only walk the
    origin/rightOrigin fields (issue #28 U7: the run's head op carries the
    first char while validity was established for the whole wire item). *)
Lemma IsItemValid_content_irrel (o r : YjsPtr A) (id : YjsId) (c c' : A) :
  IsItemValid (Item o r id c) -> IsItemValid (Item o r id c').
Proof.
  move=> [Hlt Hreach].
  constructor; first exact Hlt.
  move=> x Hx. apply Hreach.
  have Hstep : forall y, OriginReachableStep (itemPtr (Item (A:=A) o r id c')) y ->
      OriginReachableStep (itemPtr (Item (A:=A) o r id c)) y.
  { move=> y Hy. inversion Hy; subst; [apply reachable | apply reachable_right]. }
  inversion Hx; subst.
  - apply reachable_single. exact (Hstep _ H).
  - apply (reachable_head _ y). { exact (Hstep _ H). } exact H0.
Qed.

(** Auxiliary spec (the raw refinement): integrating a valid run into a valid
    document yields the document updated per the pure per-char fold
    ([integrate_all] of [ops_of_input], issue #28 U7): the HEAD op scans
    exactly like the wire input (same origins/id) and lands the run's head;
    the tail chains off it adjacently ([integrate_chain]). Kept as the
    detailed functional characterisation (exposes the fold/[itemVal]); the
    [wp_Store__Integrate] spec below repackages it. Local: a stepping stone of
    [wp_Store__integrateCore_cells_run]. *)
#[local] Lemma wp_Store__integrateCore_aux (s parent item_l : loc) (arr arr' : list (YjsItem A))
    (input : IntegrateInput (A := A)) (newItem : YjsItem A) (cells : list item_cell)
    (itemVal : yjs.item.t) (oleft oright : option yjs.id.t) (leftIdx rightIdx : Z)
    (curL curR : nat) :
  YjsArrInvariant arr ->
  toItem input arr = Some newItem ->
  IsItemValid newItem ->
  maximalId newItem arr ->
  findLeftIdx (in_originId input) arr = Some leftIdx ->
  findRightIdx (in_rightOriginId input) arr = Some rightIdx ->
  (* the caller's item arrives already linked to its resolved origin
     neighbours and carrying its parent (store.repair / the local-edit
     creator set them, issue #49); the neighbours are the boundary CELLS of
     the resolved model indices (issue #28 C1d) *)
  itemVal.(yjs.item.left') = node_loc cells (Z.of_nat curL - 1) ->
  itemVal.(yjs.item.right') = node_loc cells (Z.of_nat curR) ->
  itemVal.(yjs.item.parent') = parent ->
  itemVal.(yjs.item.flags') = W8 2 ->   (* freshly built item is Countable (NewItem sets ItemCountable) *)
  (1 <= length (itemVal.(yjs.item.content').(yjs.content.content')))%nat ->   (* nonempty run *)
  Forall (λ c, ic_run c ≠ []) cells ->
  (∀ c0, c0 ∈ cells -> cell_fits c0) ->   (* run-fits: the scan's idSpan no-wrap *)
  (∀ c0, c0 ∈ cells -> cell_origin_clk c0) ->   (* origin-clock: the span query collapse *)
  (Z.of_nat (length (run_flatten (take curL cells))) = leftIdx + 1)%Z ->
  (curL <= length cells)%nat ->
  (Z.of_nat (length (run_flatten (take curR cells))) = rightIdx)%Z ->
  (curR <= length cells)%nat ->
  integrate_all (ops_of_input input (explode (toContent itemVal.(yjs.item.content')))) arr = Some arr' ->
  {{{ is_pkg_init yjs ∗ own_ytype_cells parent (DfracOwn 1) cells arr ∗
      own_fresh_item_raw item_l input itemVal oleft oright }}}
    s @! (go.PointerType yjs.store) @! "integrateCore" #parent #item_l
  {{{ (cells' : list item_cell) (idx midx : nat) (c : item_cell), RET #();
      own_ytype_cells parent (DfracOwn 1) cells' arr' ∗ ⌜YjsArrInvariant arr'⌝ ∗
      ⌜cells' = take idx cells ++ c :: drop idx cells⌝ ∗
      ⌜(idx <= length cells)%nat⌝ ∗
      ⌜length (run_flatten (take idx cells)) = midx⌝ ∗
      ⌜(midx <= length arr)%nat⌝ ∗
      ⌜arr' = take midx arr ++ ic_run c ++ drop midx arr⌝ ∗
      ⌜cells' !! idx = Some c⌝ ∗ ⌜ic_loc c = item_l⌝ ∗
      ⌜item_id (run_head c) = in_id input⌝ ∗ ⌜ic_deleted c = false⌝ ∗
      ⌜origin (run_head c) = origin newItem⌝ ∗ ⌜rightOrigin (run_head c) = rightOrigin newItem⌝ ∗
      ⌜length (ic_run c) = length (explode (toContent itemVal.(yjs.item.content')))⌝ ∗
      ⌜cells' ≡ₚ cells ++ [c]⌝ }}}.
Proof using Type*.
  move=> Harr Htoitem Hvalid Hmax HfindL HfindR HivL HivR Hivpar Hflags Hlen1 Hnec Hfits Hoclk HcurL HcurLb HcurR HcurRb Hall.
  (* --- issue #28 U7: split the fold. The head op [h] shares the wire
     input's origins/id, so its scan is literally the input's; decompose
     its setintegrate into the destIdx/itemM case shape the singleton
     proof used ([itemM] now carries the FIRST char). --- *)
  destruct (explode (toContent itemVal.(yjs.item.content'))) as [|ch0 chrest] eqn:Hchars.
  { exfalso. have Hle := f_equal length Hchars.
    rewrite explode_length /toContent /= in Hle. lia. }
  have Hideta : in_id input = MkYjsId (clientId (in_id input)) (clock (in_id input))
    by (destruct (in_id input); reflexivity).
  rewrite /ops_of_input /= -Hideta in Hall.
  set tailops := ops_from (clientId (in_id input)) (S (clock (in_id input)))
                   (Some (in_id input)) (in_rightOriginId input) chrest in Hall.
  set h := MkIntegrateInput (in_originId input) (in_rightOriginId input) ch0 (in_id input) in Hall.
  simpl in Hall.
  destruct (integrate h arr) as [arr1|] eqn:Hint1; last done.
  (* the head's model item: the wire item's resolution with the first char *)
  have Hdecomp := Htoitem.
  rewrite /toItem in Hdecomp.
  destruct (match in_originId input with
            | Some id => itemPtr <$> find_by_id id arr | None => Some First end)
    as [optr|] eqn:Hoptr; last done.
  destruct (match in_rightOriginId input with
            | Some id => itemPtr <$> find_by_id id arr | None => Some Last end)
    as [rptr0|] eqn:Hrptr0; last done.
  simpl in Hdecomp. injection Hdecomp as HnewItemEq.
  set headit := Item (A:=A) optr rptr0 (in_id input) ch0.
  have Htoith : toItem h arr = Some headit
    by rewrite /toItem /h /= Hoptr /= Hrptr0 /=.
  have Hvalidh : IsItemValid headit.
  { apply (IsItemValid_content_irrel optr rptr0 (in_id input) (in_content input)).
    rewrite -HnewItemEq in Hvalid. exact Hvalid. }
  have Hmaxh : maximalId headit arr.
  { move=> x Hx Hcx. rewrite /headit /= in Hcx.
    have Hcx' : clientId (item_id x) = clientId (item_id newItem)
      by rewrite -HnewItemEq /=.
    have := Hmax x Hx Hcx'. rewrite -HnewItemEq //. }
  have Hseteqh : setintegrate h arr = integrate h arr
    := setintegrate_eq_integrate h arr headit Harr Htoith Hvalidh Hmaxh.
  move: Hint1.
  rewrite -Hseteqh /setintegrate /h /= HfindL HfindR /=.
  case HfindD0: (setfindIntegratedIndex leftIdx rightIdx h arr) => [destIdx|] //=.
  case HmkI: (mkItemByIndex leftIdx rightIdx h arr) => [itemM|] //=.
  move=> [Harr1eq]. subst arr1.
  (* the scan equations transfer to the wire input by conversion (the scan
     only reads origins/id, shared between [h] and [input]) *)
  have HfindD : setfindIntegratedIndex leftIdx rightIdx input arr = Some destIdx := HfindD0.
  wp_start as "(Htext & Hfresh)".
  have Hinv := Harr.
  iNamed "Hfresh".
  have Huniq := yai_unique _ Harr.
  have HfLp : findPtrIdx (origin newItem) arr = Some leftIdx.
  { rewrite -(toitem_lemmas.findLeftIdx_findPtrIdx_eq input newItem arr Huniq Htoitem). exact HfindL. }
  have HfRp : findPtrIdx (rightOrigin newItem) arr = Some rightIdx.
  { rewrite -(toitem_lemmas.findRightIdx_findPtrIdx_eq input newItem arr Huniq Htoitem). exact HfindR. }
  have HlB := insert_lemmas.findPtrIdx_ge_minus_1 arr (origin newItem) leftIdx HfLp.
  have Horig := findptridx_getelem.findPtrIdx_ArrSet arr (origin newItem) leftIdx HfLp.
  have Hror := findptridx_getelem.findPtrIdx_ArrSet arr (rightOrigin newItem) rightIdx HfRp.
  have Hlr := findptridx_order2.YjsLt'_findPtrIdx_lt arr (origin newItem) (rightOrigin newItem)
                leftIdx rightIdx Harr Horig Hror (iiv_origin_lt _ Hvalid) HfLp HfRp.
  have HrUB := insert_lemmas.findPtrIdx_le_size arr (rightOrigin newItem) rightIdx HfRp.
  iDestruct "Htext" as (yt3 tl3) "(Hparent & Hdll & %Hlen3 & %Hrepr3 & %Hcpar3)".
  have Hrfl : arr = run_flatten cells := Hrepr3.
  iDestruct "Holeft" as "#Holeft". iDestruct "Horight" as "#Horight".
  (* the item's links are already resolved: no repair stepping (issue #49) *)
  set iv2 := itemVal.
  have Hiv2L : iv2.(yjs.item.left') = node_loc cells (Z.of_nat curL - 1) := HivL.
  have Hiv2R : iv2.(yjs.item.right') = node_loc cells (Z.of_nat curR) := HivR.
  have Hiv2oL : iv2.(yjs.item.originLeftId') = itemVal.(yjs.item.originLeftId') := eq_refl.
  have Hiv2oR : iv2.(yjs.item.originRightId') = itemVal.(yjs.item.originRightId') := eq_refl.
  have Hiv2id : iv2.(yjs.item.id') = itemVal.(yjs.item.id') := eq_refl.
  have Hiv2con : iv2.(yjs.item.content') = itemVal.(yjs.item.content') := eq_refl.
  have Hiv2flags : iv2.(yjs.item.flags') = itemVal.(yjs.item.flags') := eq_refl.
  wp_auto.
  (* Conflict scan (the extracted algorithmic core), via the proved spec. *)
  rewrite Hiv2L Hiv2R.
  iAssert (own_ytype_cells parent (DfracOwn 1) cells arr) with "[Hparent Hdll]" as "Htext".
  { iExists yt3, tl3. iFrame "Hparent Hdll". done. }
  iAssert (own_fresh_item_raw item_l input iv2 oleft oright) with "[Hitem]" as "Hfresh".
  { rewrite /own_fresh_item_raw. iFrame "Hitem". rewrite Hiv2oL Hiv2oR. iFrame "Holeft Horight".
    iPureIntro; split_and!; [exact Hin_l | exact Hin_r | rewrite Hiv2id; exact Hid | rewrite Hiv2con; exact Hcontent]. }
  wp_apply (wp_findIntegrationLeft parent item_l (node_loc cells (Z.of_nat curL - 1)) (node_loc cells (Z.of_nat curR))
              (DfracOwn 1) cells arr input newItem iv2 oleft oright leftIdx rightIdx destIdx curL curR
              Harr Htoitem Hvalid Hmax HfindL HfindR HfindD eq_refl eq_refl Hnec Hfits Hoclk HcurL HcurLb HcurR HcurRb with "[$Htext $Hfresh]").
  iIntros (v) "(Htext & Hfresh & Hpost)".
  iDestruct "Hpost" as (curD) "(%Hveq & %HcurDc & %HcurDb)". subst v.
  wp_auto.
  (* [destIdx] is in bounds ([≤ rightIdx ≤ length arr]), so the model splice
     index is valid and [insertIdxIfInBounds] actually inserts (mirrors
     setintegrate_eq_integrate to reach findIntegratedIndex_bounds); the CELL
     splice happens at the returned anchor boundary [curD]. *)
  have Hsameid : forall x, ArrSet arr (itemPtr x) -> item_id x = item_id newItem -> x = newItem.
  { move=> x Hx Hxid. exfalso.
    have Hcc : clientId (item_id x) = clientId (item_id newItem) by rewrite Hxid.
    have Hcl := Hmax x Hx Hcc. rewrite Hxid in Hcl. lia. }
  have Hclosed : IsClosedItemSet (ArrSet (newItem :: arr)) :=
    arr_set_closed_push arr newItem (yai_closed _ Harr) Horig Hror.
  have Hinv2 : ItemSetInvariant (ArrSet (newItem :: arr)) :=
    item_set_invariant_push arr newItem (yai_item_set_inv _ Harr) (yai_closed _ Harr)
      (iiv_origin_lt _ Hvalid) (iiv_reachable _ Hvalid) Hsameid.
  have Hsfeq := setfindIntegratedIndex_eq arr newItem input leftIdx rightIdx
    Harr Hclosed Hinv2 Hmax Htoitem HfLp HfRp HlB Hlr HrUB.
  have Hfii : findIntegratedIndex leftIdx rightIdx input arr = Some destIdx by (rewrite -Hsfeq; exact HfindD).
  have Hdle_r := findIntegratedIndex_bounds leftIdx rightIdx input arr destIdx HlB Hlr Hfii.
  have Hdle_arr : (destIdx <= length arr)%nat by (clear -Hdle_r HrUB; lia).
  have HcurD_nat : length (run_flatten (take curD cells)) = destIdx
    by (apply Nat2Z.inj; exact HcurDc).
  (* [wp_if_join]'s [wp_if_destruct] runs a bare [subst], which would consume
     the boundary equations ([Hrfl], [HcurD_nat], the [HcurR] premise) and
     rewrite [arr] / [rightIdx] / [destIdx] away mid-proof. Substitute them
     NOW under our control and re-bind [arr] / [destIdx] as local definitions:
     [subst] skips let-bound variables, so the names stay stable across the
     joins. *)
  clear Hrepr3.
  subst destIdx rightIdx arr.
  set (arr := run_flatten cells) in *.
  set (rightIdx := Z.of_nat (length (run_flatten (take curR cells)))) in *.
  set (destIdx := (length (run_flatten (take curD cells)))) in *.
  have Hrfl : arr = run_flatten cells := eq_refl.
  have HcurD_nat : length (run_flatten (take curD cells)) = destIdx := eq_refl.
  (* Splice [item] in at index [destIdx]: relink left.right / right.left / item /
     parent.start (own_dll_app to split at destIdx, wp_store to relink, rejoin via
     own_dll_insert_middle), bump parent.len, then conclude is_valid_ytype parent
     (insertIdxIfInBounds destIdx itemM arr) via cells_repr_insert and
     YjsArrInvariant_setintegrate. *)
  iDestruct "Htext" as (yt' tl') "(Hparent & Hdll & %Hlen' & %Hrepr' & %Hcpar')".
  iDestruct "Hfresh" as "(Hitem & #Holeft2 & #Horight2 & %Hin_l2 & %Hin_r2 & %Hid2 & %Hcont2)".
  iDestruct (typed_pointsto_not_null with "Hitem") as %Hitem_nn.
  (* First [if] (y-octo: link [item] after [left]/[parent.start]). The two index
     cases ([destIdx=0] head insertion vs [destIdx>=1]) converge to a uniform
     left fragment [cs1m] + an untouched right fragment [drop destIdx cells]. *)
  wp_if_join (λ v, ⌜v = execute_val⌝ ∗
    ∃ (cs1m : list item_cell) (hd' : loc) (ytv : yjs.yType.t) (ivL : yjs.item.t),
      "Hparent" ∷ parent ↦ ytv ∗
      "%Hyts" ∷ ⌜ytv.(yjs.yType.start') = hd'⌝ ∗
      "%Hytl" ∷ ⌜ytv.(yjs.yType.len') = W64 (num_visible cells)⌝ ∗
      "Hleftdll" ∷ own_dll (DfracOwn 1) parent hd' (node_loc cells (Z.of_nat curD - 1)) null item_l cs1m ∗
      "%Hcs1m" ∷ ⌜cells_repr arr cs1m (take destIdx arr)⌝ ∗
      "%Hcs1eq" ∷ ⌜cs1m = take curD cells⌝ ∗
      "Hitem" ∷ item_l ↦ ivL ∗
      "%HivLl" ∷ ⌜ivL.(yjs.item.left') = node_loc cells (Z.of_nat curD - 1)⌝ ∗
      "%HivLf" ∷ ⌜ivL.(yjs.item.flags') = iv2.(yjs.item.flags')⌝ ∗
      "%HivLc" ∷ ⌜ivL.(yjs.item.content') = iv2.(yjs.item.content')⌝ ∗
      "%HivLid" ∷ ⌜ivL.(yjs.item.id') = iv2.(yjs.item.id')⌝ ∗
      "%HivLoL" ∷ ⌜ivL.(yjs.item.originLeftId') = iv2.(yjs.item.originLeftId')⌝ ∗
      "%HivLoR" ∷ ⌜ivL.(yjs.item.originRightId') = iv2.(yjs.item.originRightId')⌝ ∗
      "%HivLpar" ∷ ⌜ivL.(yjs.item.parent') = iv2.(yjs.item.parent')⌝ ∗
      "Hrightdll" ∷ own_dll (DfracOwn 1) parent (node_loc cells (Z.of_nat curD)) tl' (node_loc cells (Z.of_nat curD - 1)) null (drop curD cells) ∗
      "Hrightptr" ∷ right_ptr ↦ node_loc cells (Z.of_nat curD) ∗
      "item" ∷ item_ptr ↦ item_l ∗
      "parent" ∷ parent_ptr ↦ parent)%I
    with "[Hparent Hdll Hitem left right item parent]".
  { (* curD = 0 : head insertion (else branch already executed) *)
    iAssert (⌜curD = 0%nat⌝ ∗ own_dll (DfracOwn 1) parent yt'.(yjs.yType.start') tl' null null cells)%I
      with "[Hdll]" as "(%Hd0 & Hdll)".
    { destruct (decide (curD = 0%nat)) as [Hd0c|Hne].
      - iFrame "Hdll". done.
      - iDestruct (node_loc_lt_not_null (DfracOwn 1) cells yt'.(yjs.yType.start') tl' (curD - 1) with "Hdll") as "(%Hnn & Hdll)".
        { lia. }
        iFrame "Hdll". iPureIntro. exfalso. apply Hnn.
        have -> : Z.of_nat (curD - 1) = (Z.of_nat curD - 1)%Z by lia.
        exact e. }
    have Hd0m : destIdx = 0%nat by rewrite -HcurD_nat Hd0 take_0 run_flatten_nil //.
    iDestruct (own_dll_head_node with "Hdll") as %Hhd.
    have Hhd2 : node_loc cells (Z.of_nat curD) = yt'.(yjs.yType.start').
    { rewrite Hhd. f_equal. lia. }
    have Hdrop : drop curD cells = cells by rewrite Hd0 //.
    iSplitR; first done.
    iExists [], item_l, (yt' <| yjs.yType.start' := item_l |>), (iv2 <| yjs.item.left' := null |>).
    iFrame "Hparent Hitem".
    iSplitR. { iPureIntro. done. }
    iSplitR. { iPureIntro. exact Hlen'. }
    iSplitR. { simpl. iPureIntro. split; [done | exact e]. }
    iSplitR. { iPureIntro. rewrite Hd0m /=. apply cells_repr_nil. }
    iSplitR. { iPureIntro. rewrite Hd0 take_0 //. }
    iSplitR. { iPureIntro. rewrite e //. }
    iSplitR. { iPureIntro. done. }
    iSplitR. { iPureIntro. done. }
    iSplitR. { iPureIntro. done. }
    iSplitR. { iPureIntro. done. }
    iSplitR. { iPureIntro. done. }
    iSplitR. { iPureIntro. done. }
    rewrite Hhd2 e Hdrop.
    iFrame "Hdll right item parent". }
  { (* curD >= 1 : splice [item] after cell (curD-1) (then branch). Relink
       that node's [right'] to [item] via own_dll_app + cons unfold + wp_store. *)
    have Hdpos : (1 <= curD)%nat.
    { destruct (decide (1 <= curD)%nat) as [?|Hlt]; [done | exfalso; apply n].
      have Hd0 : curD = 0%nat by lia.
      rewrite Hd0 /node_loc. case_decide as Hdc; [exfalso; lia | done]. }
    have Hltlen : (curD - 1 < length cells)%nat by lia.
    destruct (cells !! (curD - 1)%nat) as [lc|] eqn:Hlc; last by (apply lookup_ge_None in Hlc; lia).
    have Hlcloc : node_loc cells (Z.of_nat curD - 1) = ic_loc lc.
    { rewrite /node_loc decide_True; last lia.
      have -> : Z.to_nat (Z.of_nat curD - 1) = (curD - 1)%nat by lia.
      rewrite Hlc //. }
    have Hdrop_eq : drop (curD - 1)%nat cells = lc :: drop curD cells.
    { rewrite (drop_S cells lc (curD-1)%nat Hlc). have -> : S (curD - 1)%nat = curD by lia. done. }
    have Hce : cells = take (curD - 1)%nat cells ++ lc :: drop curD cells.
    { rewrite -Hdrop_eq. symmetry. apply take_drop. }
    have Htake : take curD cells = take (curD - 1)%nat cells ++ [lc].
    { rewrite -(take_S_r cells (curD-1)%nat lc Hlc). f_equal. lia. }
    iEval (rewrite {1}Hce) in "Hdll".
    iEval (rewrite own_dll_app) in "Hdll".
    iDestruct "Hdll" as (ml1 mf1) "[Hleft1 Hright1]".
    iDestruct (own_dll_cons_node_unfold with "Hright1") as (nxtlc) "(%Hhead1 & %Hrunlc & %Hpclc & Hnodelc & Hrest)".
    destruct Hhead1 as [Hmf1 Hmf1nn].
    iDestruct "Hnodelc" as (ivlc olidlc oridlc)
      "(Hval & Holc & Horc & %Hinllc & %Hinrlc & %Hidlcn & %Hcontlcn & %Hparlc & %Hprev1 & %Hnextlc & %Hflagslc)".
    iDestruct (own_dll_headptr with "Hrest") as "[%Hhd_rest Hrest]".
    have Hcr_rest : ivlc.(yjs.item.right') = node_loc cells (Z.of_nat curD).
    { rewrite Hnextlc Hhd_rest /node_loc decide_True; last lia. rewrite Nat2Z.id. f_equal. f_equal.
      rewrite head_lookup lookup_drop Nat.add_0_r //. }
    iEval (rewrite Hlcloc) in "left".
    rewrite Hlcloc.
    wp_auto.
    iSplitR; first done.
    iExists (take (curD - 1)%nat cells ++ [lc]), yt'.(yjs.yType.start'), yt', (iv2 <| yjs.item.left' := lc.(ic_loc) |>).
    iFrame "Hparent Hitem".
    iSplitR. { iPureIntro. done. }
    iSplitR. { iPureIntro. exact Hlen'. }
    iSplitL "Hleft1 Hval Holc Horc".
    { rewrite own_dll_app. iExists ml1, lc.(ic_loc).
      iEval (rewrite Hmf1) in "Hleft1". iFrame "Hleft1".
      set (ivlc2 := ivlc <| yjs.item.right' := item_l |>).
      have Hparlc : ic_parent lc = parent.
      { apply Hcpar'. exact (list_elem_of_lookup_2 _ _ _ Hlc). }
      iApply (own_dll_cons_node_fold (DfracOwn 1) _ _ _ item_l lc (@nil item_cell) Hparlc Hrunlc Hpclc).
      iSplitL "Hval Holc Horc".
      { iExists ivlc2, olidlc, oridlc.
        iFrame "Hval Holc Horc".
        iPureIntro. split_and!.
        - exact Hinllc.
        - exact Hinrlc.
        - rewrite /ivlc2 /=. exact Hidlcn.
        - rewrite /ivlc2 /=. exact Hcontlcn.
        - rewrite /ivlc2 /=. exact Hparlc.
        - rewrite /ivlc2 /=. exact Hprev1.
        - rewrite /ivlc2 /=. reflexivity.
        - rewrite /ivlc2 /=. exact Hflagslc. }
      iPureIntro. split; reflexivity. }
    iSplitR.
    { iPureIntro. rewrite -Htake /cells_repr -HcurD_nat.
      symmetry. exact (run_flatten_take_prefix cells arr curD Hrfl). }
    iSplitR. { iPureIntro. symmetry. exact Htake. }
    iSplitR. { iPureIntro. done. }
    iSplitR. { iPureIntro. done. }
    iSplitR. { iPureIntro. done. }
    iSplitR. { iPureIntro. done. }
    iSplitR. { iPureIntro. done. }
    iSplitR. { iPureIntro. done. }
    iSplitR. { iPureIntro. done. }
    have Hnxtlc_eq : nxtlc = node_loc cells (Z.of_nat curD) by rewrite -Hnextlc Hcr_rest.
    iEval (rewrite Hnxtlc_eq) in "Hrest".
    iEval (rewrite Hcr_rest) in "right".
    iFrame "Hrest right item parent". }
  iIntros (v) "[%Hv HQ]". iNamed "HQ". subst v. wp_auto.
  (* Second [if] (y-octo: link [right.left] to [item] when a right neighbour
     exists). The [destIdx<length] / [destIdx=length] cases converge to a right
     fragment [cs2m] whose first [left'] points at [item]. *)
  wp_if_join (λ v, ⌜v = execute_val⌝ ∗
    ∃ (cs2m : list item_cell) (tlN : loc),
      "Hrightdll2" ∷ own_dll (DfracOwn 1) parent (node_loc cells (Z.of_nat curD)) tlN item_l null cs2m ∗
      "%Hcs2m" ∷ ⌜cells_repr arr cs2m (drop destIdx arr)⌝ ∗
      "%Hcs2eq" ∷ ⌜cs2m = drop curD cells⌝ ∗
      "Hrightptr" ∷ right_ptr ↦ node_loc cells (Z.of_nat curD) ∗
      "item" ∷ item_ptr ↦ item_l)%I
    with "[Hrightdll Hrightptr item]".
  { (* curD = length cells: no right neighbour (else / no-op) *)
    destruct (drop curD cells) as [|rc rest] eqn:Hdrop.
    - iSplitR; first done. iExists [], item_l. iFrame "Hrightptr item".
      iSplitR. { simpl. iPureIntro. split; [exact e | reflexivity]. }
      iSplitR.
      { iPureIntro.
        have Hge : (length cells <= curD)%nat.
        { have Hlen0 : length (drop curD cells) = 0%nat by rewrite Hdrop //.
          rewrite length_drop in Hlen0. lia. }
        have Hdge : (length arr <= destIdx)%nat.
        { rewrite -HcurD_nat take_ge; last exact Hge. rewrite Hrfl //. }
        rewrite drop_ge; [apply cells_repr_nil | exact Hdge]. }
      iPureIntro. done.
    - iDestruct "Hrightdll" as (ivx olidx oridx) "(%Hl & _)". destruct Hl as [_ Hnn]. exfalso. exact (Hnn e). }
  { (* curD < length cells: relink right neighbour's left to item *)
    have Hltlen : (curD < length cells)%nat.
    { destruct (decide (curD < length cells)%nat) as [?|Hge]; [done|].
      exfalso. apply n. rewrite /node_loc decide_True; last lia.
      rewrite Nat2Z.id lookup_ge_None_2; [done | lia]. }
    destruct (drop curD cells) as [|rc rest] eqn:Hdrop.
    { exfalso. have Hl0 : length (drop curD cells) = 0%nat by rewrite Hdrop //.
      rewrite length_drop in Hl0. lia. }
    iDestruct "Hrightdll" as (ivr olidr oridr) "(%Hlocr & %Hprevr & %Hparr2 & %Hidr & %Hcontr & %Holidr & %Horidr & %Hflagsr & %Hrunr & Hvalr & #Holr & #Horr & Hrestr)".
    destruct Hlocr as [Hrcloc Hrcnn].
    rewrite Hrcloc.
    wp_auto.
    iDestruct (typed_pointsto_not_null with "Hvalr") as %Hrcnn2.
    iSplitR; first done.
    iExists (rc :: rest), tl'.
    iFrame "Hrightptr item".
    iSplitL "Hvalr Hrestr".
    { iExists (ivr <| yjs.item.left' := item_l |>), olidr, oridr. iFrame "Hvalr Holr Horr Hrestr".
      iPureIntro; split_and!;
        [reflexivity | exact Hrcnn2 | reflexivity | exact Hparr2 | exact Hidr | exact Hcontr | exact Holidr | exact Horidr | exact Hflagsr | exact Hrunr]. }
    iSplitR.
    { iPureIntro. rewrite /cells_repr -Hdrop -HcurD_nat.
      symmetry. exact (run_flatten_drop_suffix cells arr curD Hrfl). }
    iPureIntro. done. }
  iIntros (v) "[%Hv HQ2]". iNamed "HQ2". subst v. wp_auto.
  (* item.right := right (node_loc cells destIdx) already done; now [Countable()]
     is true (flags = ItemCountable) and [Len()] is the run length, so
     [parent.len += Len()]. Step the [Item.Countable] / [Item.Len] /
     [Content.Len] methods, resolving the symbolic word tests with [Hflv];
     the length stays symbolic ([Hclv] names it, issue #28 U7). *)
  have Hflv : ivL.(yjs.item.flags') = W8 2 by rewrite HivLf Hiv2flags Hflags.
  have Hclv : length ivL.(yjs.item.content').(yjs.content.content')
            = length (ch0 :: chrest).
  { rewrite HivLc Hiv2con.
    have Hle := f_equal length Hchars.
    rewrite explode_length /toContent /= in Hle. rewrite Hle //. }
  wp_method_call. wp_call. wp_auto. wp_method_call. wp_auto. wp_call. wp_auto.
  rewrite Hflv.
  rewrite (bool_decide_eq_false_2 (w8_word_instance.(word.and) (W8 2) (W8 2) = W8 0)); last by vm_compute.
  simpl negb. wp_auto.
  wp_method_call. wp_call. wp_auto. wp_method_call. wp_call. wp_call. wp_auto.
  wp_method_call. wp_call. wp_auto. wp_method_call. wp_call. wp_call. wp_auto.
  wp_apply strings.wp_string_len. iIntros "%Hslen". wp_auto. rewrite Hclv.
  (* Conclude: resolve [itemM]'s origins, land the WHOLE run's model splice
     ([integrate_chain] off the freshly inserted head, issue #28 U7), and
     reassemble the DLL with the run cell spliced in. *)
  destruct (findptridx_insert.findLeftIdx_getElemExcept arr input leftIdx HfindL) as [lptr [HgetL HisL]].
  destruct (findptridx_insert.findRightIdx_getElemExcept arr input rightIdx HfindR) as [rptr [HgetR HisR]].
  have HitemM : itemM = Item lptr rptr input.(in_id) ch0.
  { move: HmkI. rewrite /mkItemByIndex HgetL HgetR /=. by move=> [<-]. }
  have Hlpo : origin_id lptr = input.(in_originId).
  { destruct (input.(in_originId)) as [pid|] eqn:Hpid.
    - destruct HisL as [it [-> Hfind]]. by rewrite /= (toitem_lemmas.find_by_id_id _ _ _ Hfind).
    - by rewrite HisL. }
  have Hrpo : origin_id rptr = input.(in_rightOriginId).
  { destruct (input.(in_rightOriginId)) as [pid|] eqn:Hpid.
    - destruct HisR as [it [-> Hfind]]. by rewrite /= (toitem_lemmas.find_by_id_id _ _ _ Hfind).
    - by rewrite HisR. }
  have Hsetinth : setintegrate h arr = Some (insertIdxIfInBounds destIdx itemM arr).
  { rewrite /setintegrate /h /= HfindL /= HfindR /= HfindD0 /= HmkI //. }
  (* [itemM] is [headit] under the resolution-pointer identification *)
  have Hlopt : lptr = optr.
  { destruct (input.(in_originId)) as [pid|] eqn:Hpid.
    - destruct HisL as [it [-> Hfind]]. move: Hoptr. rewrite Hfind /=. by move=> [<-].
    - move: Hoptr. rewrite HisL /=. by move=> [<-]. }
  have Hropt : rptr = rptr0.
  { destruct (input.(in_rightOriginId)) as [pid|] eqn:Hpid.
    - destruct HisR as [it [-> Hfind]]. move: Hrptr0. rewrite Hfind /=. by move=> [<-].
    - move: Hrptr0. rewrite HisR /=. by move=> [<-]. }
  have HitemMh : itemM = headit by rewrite HitemM /headit Hlopt Hropt //.
  have HitemMvalid : IsItemValid itemM by rewrite HitemMh.
  have HitemMmax : maximalId itemM arr.
  { rewrite HitemMh. exact Hmaxh. }
  have HtoitM : toItem h arr = Some itemM by rewrite Htoith HitemMh //.
  have Hinv1 : YjsArrInvariant (insertIdxIfInBounds destIdx itemM arr).
  { eapply YjsArrInvariant_setintegrate;
      [exact Harr | exact HtoitM | exact HitemMvalid | exact HitemMmax | exact Hsetinth]. }
  have Harr'' : insertIdxIfInBounds destIdx itemM arr = take destIdx arr ++ itemM :: drop destIdx arr.
  { rewrite /insertIdxIfInBounds decide_True; [done | exact Hdle_arr]. }
  set arr1 := insertIdxIfInBounds destIdx itemM arr in Hall |- *.
  have Harr1v : arr1 = take destIdx arr ++ itemM :: drop destIdx arr := Harr''.
  (* --- integrate_chain premises at the head anchor --- *)
  have Hheadid : item_id itemM = in_id input by rewrite HitemM //.
  have Hj1 : arr1 !! destIdx = Some itemM.
  { rewrite Harr1v. apply list_lookup_middle. rewrite length_take_le //. }
  have Hchaint' : chained_after (item_id itemM) (in_rightOriginId input) tailops.
  { rewrite Hheadid. exact (ops_from_chained _ _ _ _ _). }
  have Htailid : forall i inp, tailops !! i = Some inp ->
      in_id inp = MkYjsId (clientId (in_id input)) (S (clock (in_id input)) + i)%nat.
  { move=> i inp Hinp.
    exact (proj1 (ops_from_lookup _ _ _ _ _ _ _ Hinp)). }
  have Hidfresharr : forall z, z ∈ arr -> forall i inp, tailops !! i = Some inp ->
      item_id z ≠ in_id inp.
  { move=> z Hz i inp Hinp Heq.
    rewrite (Htailid i inp Hinp) in Heq.
    have Hcz : clientId (item_id z) = clientId (item_id newItem).
    { rewrite -HnewItemEq /= Heq //. }
    have Hclt := Hmax z Hz Hcz.
    rewrite -HnewItemEq /= in Hclt.
    rewrite Heq /= in Hclt. lia. }
  have Hfresh1 : ids_fresh arr1 tailops.
  { split; last exact (ops_from_ids_nodup _ _ _ _ _).
    move=> z Hz i inp Hinp.
    rewrite Harr1v in Hz.
    move: Hz. rewrite elem_of_app elem_of_cons.
    move=> [Hz | [-> | Hz]].
    - exact (Hidfresharr z (subseteq_take _ _ _ Hz) i inp Hinp).
    - rewrite Hheadid (Htailid i inp Hinp). move=> Heq.
      have := f_equal clock Heq.
      rewrite Hideta /=. lia.
    - exact (Hidfresharr z (subseteq_drop _ _ _ Hz) i inp Hinp). }
  have Hxid1 : forall i inp, tailops !! i = Some inp -> item_id itemM ≠ in_id inp.
  { move=> i inp Hinp. rewrite Hheadid (Htailid i inp Hinp). move=> Heq.
    have := f_equal clock Heq. rewrite Hideta /=. lia. }
  have Hddler : (Z.of_nat destIdx <= rightIdx)%Z by (clear -Hdle_r; lia).
  have Hheadidfresh : forall z, z ∈ arr -> item_id z ≠ item_id itemM.
  { move=> z Hz Heq.
    have Hcz : clientId (item_id z) = clientId (item_id newItem).
    { rewrite -HnewItemEq /= Heq Hheadid //. }
    have Hclt := Hmax z Hz Hcz.
    rewrite -HnewItemEq /= in Hclt.
    rewrite Heq Hheadid /= in Hclt. lia. }
  have Hri1 : findRightIdx (in_rightOriginId input) arr1 = Some (rightIdx + 1)%Z.
  { rewrite Harr1v.
    exact (findRightIdx_insert_shift arr destIdx itemM _ rightIdx Hdle_arr Hddler HfindR Hheadidfresh). }
  have Hjr1 : (Z.of_nat destIdx < rightIdx + 1)%Z by lia.
  have Hgp1 : getPtrExcept arr1 (rightIdx + 1) = Some rptr.
  { rewrite Harr1v.
    exact (getPtrExcept_insert_shift arr destIdx itemM rightIdx rptr Hdle_arr Hddler HgetR). }
  have Hnosucc1 : forall z, z ∈ arr1 -> origin z ≠ itemPtr itemM.
  { move=> z Hz.
    rewrite Harr1v in Hz.
    move: Hz. rewrite elem_of_app elem_of_cons. move=> Hz Horigz.
    have Hzarr : z ∈ arr ∨ z = itemM.
    { move: Hz => [Hz | [-> | Hz]];
        [left; exact (subseteq_take _ _ _ Hz) | by right | left; exact (subseteq_drop _ _ _ Hz)]. }
    case: Hzarr => [Hzarr | Hzeq].
    - (* an old element's origin lives in [arr] (closedness); [itemM]'s id is fresh *)
      have Hcl := yai_closed _ Harr.
      destruct z as [oz rz idz cz]. simpl in Horigz. subst oz.
      have Hzin : ArrSet arr (itemPtr itemM)
        := closedLeft _ Hcl _ _ _ _ Hzarr.
      simpl in Hzin.
      exact (Hheadidfresh itemM Hzin eq_refl).
    - (* the head's own origin is [lptr], an old resolution *)
      subst z.
      rewrite HitemM /= in Horigz.
      destruct (input.(in_originId)) as [pid|] eqn:Hpid; last first.
      { rewrite HisL in Horigz. done. }
      destruct HisL as [it [Hlptr_it Hfind]].
      have Hitin : it ∈ arr.
      { move: Hfind. rewrite /find_by_id. move=> /fmap_Some [[k' it'] [Hlf /= ->]].
        apply list_find_Some in Hlf. destruct Hlf as (Hlk & _ & _).
        exact (list_elem_of_lookup_2 _ _ _ Hlk). }
      rewrite Hlptr_it in Horigz. injection Horigz as Horigz.
      apply (Hheadidfresh it Hitin). rewrite Horigz //. }
  have Hvalid1t : forall i0 rest0, tailops = i0 :: rest0 ->
      IsItemValid (Item (itemPtr itemM) rptr i0.(in_id) i0.(in_content)).
  { move=> i0 rest0 _.
    apply (chain_link_valid (ArrSet arr1) itemM rptr i0.(in_id) i0.(in_content)
             (yai_closed _ Hinv1) (yai_item_set_inv _ Hinv1)).
    - simpl. exact (list_elem_of_lookup_2 _ _ _ Hj1).
    - rewrite HitemM //.
    - exact HitemMvalid. }
  have Hmaxs1 : forall k inp, tailops !! k = Some inp ->
      forall z, z ∈ arr1 -> clientId (item_id z) = clientId inp.(in_id) ->
        (clock (item_id z) < clock inp.(in_id))%nat.
  { move=> k inp Hk z Hz Hcz.
    rewrite (Htailid k inp Hk) /= in Hcz *.
    rewrite Harr1v in Hz.
    move: Hz. rewrite elem_of_app elem_of_cons. move=> Hz.
    have Hzarr : z ∈ arr ∨ z = itemM.
    { move: Hz => [Hz | [-> | Hz]];
        [left; exact (subseteq_take _ _ _ Hz) | by right | left; exact (subseteq_drop _ _ _ Hz)]. }
    case: Hzarr => [Hzarr | Hzeq].
    - have Hcz' : clientId (item_id z) = clientId (item_id newItem)
        by rewrite -HnewItemEq /= Hcz //.
      have := Hmax z Hzarr Hcz'.
      rewrite -HnewItemEq /=. lia.
    - subst z. rewrite Hheadid Hideta /=. lia. }
  have Hchainclk1 : forall i k inpi inpk, (i < k)%nat ->
      tailops !! i = Some inpi -> tailops !! k = Some inpk ->
      clientId inpi.(in_id) = clientId inpk.(in_id) ->
      (clock inpi.(in_id) < clock inpk.(in_id))%nat.
  { move=> i k inpi inpk Hik Hi Hk _.
    rewrite (Htailid i inpi Hi) (Htailid k inpk Hk) /=. lia. }
  destruct (integrate_chain tailops arr1 destIdx itemM (in_rightOriginId input)
              (rightIdx + 1)%Z rptr Hinv1 Hj1 Hchaint' Hfresh1 Hxid1 Hri1 Hjr1
              Hgp1 Hnosucc1 Hvalid1t Hmaxs1 Hchainclk1)
    as (news & Htailint & Hnewslen & Hinvfin & Hnewsfacts).
  have Harr'some : Some (take (S destIdx) arr1 ++ news ++ drop (S destIdx) arr1) = Some arr'.
  { rewrite -Htailint. exact Hall. }
  injection Harr'some as Harr'run.
  set RUNITEMS := (itemM :: news).
  have Hlentake1 : length (take destIdx arr) = destIdx by (rewrite length_take_le //).
  have Htake1 : take (S destIdx) arr1 = take destIdx arr ++ [itemM].
  { rewrite Harr1v take_app_ge; last lia.
    rewrite Hlentake1.
    have -> : (S destIdx - destIdx)%nat = 1%nat by lia. done. }
  have Hdrop1 : drop (S destIdx) arr1 = drop destIdx arr.
  { rewrite Harr1v drop_app_ge; last lia.
    rewrite Hlentake1.
    have -> : (S destIdx - destIdx)%nat = 1%nat by lia. done. }
  have Harr'form : arr' = take destIdx arr ++ RUNITEMS ++ drop destIdx arr.
  { rewrite -Harr'run Htake1 Hdrop1 /RUNITEMS -app_assoc //. }
  have Hinvarr' : YjsArrInvariant arr'.
  { rewrite Harr'run in Hinvfin. exact Hinvfin. }
  (* the run cell's structural facts *)
  have Htailfacts : forall k it, news !! k = Some it ->
      item_id it = MkYjsId (clientId (in_id input)) (clock (in_id input) + S k)%nat ∧
      rightOrigin it = rptr ∧
      chrest !! k = Some (content it) ∧
      (k = 0%nat -> origin it = itemPtr itemM) ∧
      (forall k' itp, k = S k' -> news !! k' = Some itp -> origin it = itemPtr itp).
  { move=> k it Hk.
    have Hklen : (k < length tailops)%nat.
    { rewrite -Hnewslen. apply lookup_lt_Some in Hk. exact Hk. }
    destruct (lookup_lt_is_Some_2 tailops k Hklen) as [inp Hinp].
    destruct (Hnewsfacts k inp Hinp) as (it' & Hit' & Hitid & Hitc & Hitr & Hit0 & Hitchain).
    rewrite Hit' in Hk. injection Hk as <-.
    have Hops := ops_from_lookup _ _ _ _ _ _ _ Hinp.
    destruct Hops as (Hidk & Hrid & Hchk & _ & _).
    split_and!.
    - rewrite Hitid Hidk. f_equal. lia.
    - exact Hitr.
    - rewrite Hitc. exact Hchk.
    - exact Hit0.
    - exact Hitchain. }
  have Hrunwf : run_wf RUNITEMS.
  { apply (run_wf_of_chain itemM news (clientId (in_id input)) (clock (in_id input)) rptr).
    - rewrite Hheadid Hideta //.
    - rewrite HitemM //.
    - move=> k it Hk.
      destruct (Htailfacts k it Hk) as (Hidf & Hrof & _ & H0f & Hsf).
      split_and!; [exact Hidf | exact Hrof | exact H0f | exact Hsf]. }
  have Hruncont : content <$> RUNITEMS = (ch0 :: chrest).
  { rewrite /RUNITEMS fmap_cons HitemM /=.
    f_equal.
    apply list_eq. move=> k.
    rewrite list_lookup_fmap.
    destruct (news !! k) as [it|] eqn:Hk.
    - destruct (Htailfacts k it Hk) as (_ & _ & Hck & _ & _).
      rewrite Hck //.
    - simpl. symmetry. apply lookup_ge_None.
      apply lookup_ge_None in Hk.
      rewrite Hnewslen /tailops ops_from_length in Hk. lia. }
  have HRUNlen : length RUNITEMS = length (ch0 :: chrest).
  { rewrite /RUNITEMS /= Hnewslen.
    rewrite /tailops ops_from_length //. }
  (* --- the cell splice, now with the whole run --- *)
  have Hlen0 : length (cs1m ++ MkItemCell item_l RUNITEMS false parent :: cs2m) = (length cells + 1)%nat.
  { rewrite length_app /= Hcs1eq Hcs2eq length_take length_drop. lia. }
  have Hnv0 : num_visible (cs1m ++ MkItemCell item_l RUNITEMS false parent :: cs2m)
            = (num_visible cells + length RUNITEMS)%nat.
  { rewrite Hcs1eq Hcs2eq. apply num_visible_insert_visible_run; reflexivity. }
  have Hstart : (ytv <| yjs.yType.len' := w64_word_instance.(word.add) ytv.(yjs.yType.len') (W64 (length (ch0 :: chrest))%nat) |>).(yjs.yType.start') = hd'.
  { simpl. exact Hyts. }
  have Hcs1len : length cs1m = curD.
  { rewrite Hcs1eq length_take_le; [done | exact HcurDb]. }
  iApply ("HΦ" $! (cs1m ++ MkItemCell item_l RUNITEMS false parent :: cs2m) curD destIdx (MkItemCell item_l RUNITEMS false parent)).
  iSplitL "Hparent Hleftdll Hitem Hrightdll2".
  { iExists (ytv <| yjs.yType.len' := w64_word_instance.(word.add) ytv.(yjs.yType.len') (W64 (length (ch0 :: chrest))%nat) |>), tlN.
    iFrame "Hparent".
    iSplitL.
    { rewrite Hstart.
      have HrightEq : (ivL <| yjs.item.right' := node_loc cells (Z.of_nat curD) |>).(yjs.item.right') = node_loc cells (Z.of_nat curD) by reflexivity.
      have HleftEq : (ivL <| yjs.item.right' := node_loc cells (Z.of_nat curD) |>).(yjs.item.left') = node_loc cells (Z.of_nat curD - 1).
      { simpl. exact HivLl. }
      have Hidtr : item_id (run_head (MkItemCell item_l RUNITEMS false parent)) = toYjsId (ivL <| yjs.item.right' := node_loc cells (Z.of_nat curD) |>).(yjs.item.id').
      { rewrite /run_head /= Hheadid /= HivLid Hiv2id Hid //. }
      have Hconttr : content <$> ic_run (MkItemCell item_l RUNITEMS false parent) = explode (toContent (ivL <| yjs.item.right' := node_loc cells (Z.of_nat curD) |>).(yjs.item.content')).
      { rewrite /= HivLc Hiv2con Hchars. exact Hruncont. }
      have Holtr : origin_id (origin (run_head (MkItemCell item_l RUNITEMS false parent))) = toYjsId <$> oleft.
      { rewrite /run_head /= HitemM /= Hlpo -Hin_l2 //. }
      have Hortr : origin_id (rightOrigin (run_head (MkItemCell item_l RUNITEMS false parent))) = toYjsId <$> oright.
      { rewrite /run_head /= HitemM /= Hrpo -Hin_r2 //. }
      have Hpartr : (ivL <| yjs.item.right' := node_loc cells (Z.of_nat curD) |>).(yjs.item.parent')
                    = ic_parent (MkItemCell item_l RUNITEMS false parent).
      { simpl. rewrite HivLpar /iv2 Hivpar //. }
      have Hpcnew : run_per_char (cell_run (MkItemCell item_l RUNITEMS false parent))
        := run_per_char_intro _ _ _ Hconttr.
      iApply (own_dll_insert_middle_node (DfracOwn 1) cs1m cs2m (MkItemCell item_l RUNITEMS false parent)
                hd' tlN (node_loc cells (Z.of_nat curD - 1)) (node_loc cells (Z.of_nat curD))
                eq_refl Hrunwf Hpcnew).
      iSplitL "Hleftdll"; first iFrame "Hleftdll".
      iSplitL "Hitem Holeft2 Horight2"; last iFrame "Hrightdll2".
      iExists (ivL <| yjs.item.right' := node_loc cells (Z.of_nat curD) |>), oleft, oright.
      simpl. rewrite HivLoL HivLoR.
      iFrame "Hitem Holeft2 Horight2".
      iPureIntro. split_and!.
      - exact (eq_sym Holtr).
      - exact (eq_sym Hortr).
      - exact (eq_sym Hidtr).
      - symmetry. exact (items_string_explode _ _ Hconttr).
      - exact Hpartr.
      - exact HleftEq.
      - exact HrightEq.
      - exact Hflv. }
    iPureIntro. split_and!.
    - rewrite /= Hytl Hnv0 HRUNlen /=. word.
    - rewrite /cells_repr Harr'form run_flatten_app run_flatten_cons /=.
      f_equal; last f_equal.
      + move: Hcs1m. rewrite /cells_repr //.
      + move: Hcs2m. rewrite /cells_repr. by move=> ->.
    - move=> c Hc. rewrite Hcs1eq Hcs2eq in Hc.
      move: Hc. rewrite elem_of_app elem_of_cons.
      move=> [Hc | [-> | Hc]].
      + apply Hcpar'. rewrite -(take_drop curD cells) elem_of_app. by left.
      + done.
      + apply Hcpar'. rewrite -(take_drop curD cells) elem_of_app. by right. }
  iSplit; [iPureIntro; exact Hinvarr'|].
  iSplit; [iPureIntro; rewrite Hcs1eq Hcs2eq //|].
  iSplit; [iPureIntro; exact HcurDb|].
  iSplit; [iPureIntro; exact HcurD_nat|].
  iSplit; [iPureIntro; exact Hdle_arr|].
  iSplit; [iPureIntro; simpl; exact Harr'form|].
  iSplit; [iPureIntro; apply list_lookup_middle; by rewrite Hcs1len|].
  iSplit; [iPureIntro; reflexivity|].
  iSplit; [iPureIntro; rewrite /run_head /= Hheadid //|].
  iSplit; [iPureIntro; reflexivity|].
  iSplit; [iPureIntro; rewrite /run_head /= HitemMh /headit /= -HnewItemEq //|].
  iSplit; [iPureIntro; rewrite /run_head /= HitemMh /headit /= -HnewItemEq //|].
  iSplit; [iPureIntro; exact HRUNlen|].
  iPureIntro. rewrite Hcs1eq Hcs2eq.
  rewrite (Permutation_cons_append (drop curD cells) (MkItemCell item_l RUNITEMS false parent)).
  rewrite app_assoc take_drop //.
Qed.

(** When [newItem]'s left origin is the current tail element [a] of a valid
    [arr] and its right origin is [Last], the integrate insertion index can only
    be the end: [newItem] is greater than every element of [arr] (its origin is
    the maximum), so sortedness of the result forces it last. Hence integrating
    it yields [arr ++ [newItem]]. This keeps the freshly integrated node at the
    DLL tail across [Text.Insert]'s loop iterations. *)
Lemma insert_tail_snoc (arr : list (YjsItem A)) (a newItem : YjsItem A) (i : nat) :
  YjsArrInvariant arr ->
  YjsArrInvariant (insertIdxIfInBounds i newItem arr) ->
  (i <= length arr)%nat ->
  base.lookup (length arr - 1)%nat arr = Some a ->
  origin newItem = itemPtr a ->
  insertIdxIfInBounds i newItem arr = arr ++ [newItem].
Proof.
  intros Hinv Hinv' Hle Ha Horig.
  have Hisi' := yai_item_set_inv _ Hinv'.
  have Hclosed' := yai_closed _ Hinv'.
  assert (Hi : i = length arr).
  2:{ subst i. rewrite /insertIdxIfInBounds decide_True; [|done].
      rewrite take_ge; [|done]. rewrite drop_ge; [|done]. done. }
  destruct (decide (i = length arr)) as [Heq | Hne]; [exact Heq | exfalso].
  have Hlt : (i < length arr)%nat by lia.
  destruct (arr !! i) as [y|] eqn:Hy;
    [| apply lookup_lt_is_Some_2 in Hlt; rewrite Hy in Hlt; by destruct Hlt].
  have Htlen : length (take i arr) = i by rewrite length_take_le; [done | lia].
  have Harr' : insertIdxIfInBounds i newItem arr = take i arr ++ newItem :: drop i arr
    by rewrite /insertIdxIfInBounds decide_True; [done | exact Hle].
  have Hnewi : insertIdxIfInBounds i newItem arr !! i = Some newItem
    by rewrite Harr'; apply list_lookup_middle; rewrite Htlen.
  assert (Hyi1 : insertIdxIfInBounds i newItem arr !! S i = Some y)
    by (rewrite Harr' lookup_app_r; rewrite Htlen;
        [ replace (S i - i)%nat with 1%nat by lia;
          rewrite /= lookup_drop Nat.add_0_r; exact Hy | lia]).
  have HltNewY : YjsLt' newItem y
    by apply (invariant_yjsarray_idx.getElem_lt_YjsLt'
                (insertIdxIfInBounds i newItem arr) i (S i) newItem y Hinv' Hnewi Hyi1); lia.
  have PnewItem : newItem ∈ insertIdxIfInBounds i newItem arr
    by exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Hnewi).
  have Py : y ∈ insertIdxIfInBounds i newItem arr
    by exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Hyi1).
  have HltANew : YjsLt' a newItem by rewrite -Horig; apply item_origin_lt.
  have HltYNew : YjsLt' y newItem.
  { destruct (decide (i = length arr - 1)%nat) as [Hieq | Hilt].
    - rewrite Hieq in Hy. have Hya : y = a by congruence. rewrite Hya; exact HltANew.
    - have HltYA : YjsLt' y a
        by apply (invariant_yjsarray_idx.getElem_lt_YjsLt'
                    arr i (length arr - 1)%nat y a Hinv Hy Ha); lia.
      have HaArr : a ∈ arr by exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Ha).
      have Pa : a ∈ insertIdxIfInBounds i newItem arr
        by apply (proj2 (mem_insertIdxIfInBounds _ _ _ _ Hle)); right; exact HaArr.
      exact (transitivity.yjs_lt_trans Hisi' Hclosed'
               (itemPtr y) (itemPtr a) (itemPtr newItem) Py Pa PnewItem HltYA HltANew). }
  exact (asymmetry.yjs_lt_asymm Hclosed' Hisi'
           (itemPtr y) (itemPtr newItem) Py PnewItem HltYNew HltNewY).
Qed.

(** General placement: if [newItem] is order-bounded by position [p] of the
    valid [arr] (everything strictly before [p] is [<yjs newItem], everything
    from [p] on is [>yjs newItem]), then integrate places it at exactly [p].
    This generalises [insert_tail_snoc] (the [p = length arr] case) to head /
    middle insertion, which is what a non-tail [Text.Insert] needs. The two
    order bounds are discharged in the WP loop from the new item's origin /
    right-origin being the neighbours straddling position [p]. *)
Lemma insert_at_pos (arr : list (YjsItem A)) (newItem : YjsItem A) (i p : nat) :
  YjsArrInvariant arr ->
  YjsArrInvariant (insertIdxIfInBounds i newItem arr) ->
  (i <= length arr)%nat ->
  (p <= length arr)%nat ->
  (forall k (a : YjsItem A), (k < p)%nat -> base.lookup k arr = Some a -> YjsLt' a newItem) ->
  (forall k (b : YjsItem A), (p <= k)%nat -> (k < length arr)%nat -> base.lookup k arr = Some b -> YjsLt' newItem b) ->
  insertIdxIfInBounds i newItem arr = take p arr ++ newItem :: drop p arr.
Proof.
  intros Hinv Hinv' Hile Hp Hleft Hright.
  have Hisi' := yai_item_set_inv _ Hinv'.
  have Hclosed' := yai_closed _ Hinv'.
  have Harr' : insertIdxIfInBounds i newItem arr = take i arr ++ newItem :: drop i arr
    by rewrite /insertIdxIfInBounds decide_True; [done | exact Hile].
  have Htlen : length (take i arr) = i by rewrite length_take_le; [done | exact Hile].
  have Hnewi : insertIdxIfInBounds i newItem arr !! i = Some newItem
    by rewrite Harr'; apply list_lookup_middle; rewrite Htlen.
  have PnewItem : newItem ∈ insertIdxIfInBounds i newItem arr
    by exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Hnewi).
  have Hi : i = p.
  { destruct (Nat.lt_trichotomy i p) as [Hlt | [Heq | Hgt]].
    - exfalso.
      have HilenA : (i < length arr)%nat by lia.
      destruct (arr !! i) as [a|] eqn:Ha; [| apply lookup_lt_is_Some_2 in HilenA; rewrite Ha in HilenA; by destruct HilenA].
      have HaLt : YjsLt' a newItem by exact (Hleft i a Hlt Ha).
      have Hai : insertIdxIfInBounds i newItem arr !! S i = Some a.
      { rewrite Harr' lookup_app_r; rewrite Htlen;
        [ replace (S i - i)%nat with 1%nat by lia; rewrite /= lookup_drop Nat.add_0_r; exact Ha | lia]. }
      have Pa : a ∈ insertIdxIfInBounds i newItem arr by exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Hai).
      have HltNewA : YjsLt' newItem a
        by apply (invariant_yjsarray_idx.getElem_lt_YjsLt' (insertIdxIfInBounds i newItem arr) i (S i) newItem a Hinv' Hnewi Hai); lia.
      exact (asymmetry.yjs_lt_asymm Hclosed' Hisi' (itemPtr a) (itemPtr newItem) Pa PnewItem HaLt HltNewA).
    - exact Heq.
    - exfalso.
      have HplenB : (p < length arr)%nat by lia.
      destruct (arr !! p) as [b|] eqn:Hb; [| apply lookup_lt_is_Some_2 in HplenB; rewrite Hb in HplenB; by destruct HplenB].
      have HbGt : YjsLt' newItem b by exact (Hright p b (Nat.le_refl p) HplenB Hb).
      have Hbp : insertIdxIfInBounds i newItem arr !! p = Some b.
      { rewrite Harr' lookup_app_l; [| rewrite Htlen; lia]. rewrite lookup_take_lt; [exact Hb | lia]. }
      have Pb : b ∈ insertIdxIfInBounds i newItem arr by exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Hbp).
      have HltBNew : YjsLt' b newItem
        by apply (invariant_yjsarray_idx.getElem_lt_YjsLt' (insertIdxIfInBounds i newItem arr) p i b newItem Hinv' Hbp Hnewi); lia.
      exact (asymmetry.yjs_lt_asymm Hclosed' Hisi' (itemPtr newItem) (itemPtr b) PnewItem Pb HbGt HltBNew). }
  subst p. exact Harr'.
Qed.

(** Companion placement for [item_valid_at]: integrate places the straddling
    item at exactly [p] ([take p arr ++ newItem :: drop p arr]). Discharges the two
    order bounds of [insert_at_pos] from the origin / right-origin being the
    [p-1] / [p] neighbours (boundary cases [First] / [Last] make a bound
    vacuous). *)
Lemma insert_straddle (arr : list (YjsItem A)) (newItem : YjsItem A) (i p : nat) :
  YjsArrInvariant arr ->
  YjsArrInvariant (insertIdxIfInBounds i newItem arr) ->
  (i <= length arr)%nat -> (p <= length arr)%nat ->
  (p = 0%nat /\ origin newItem = First \/ (1 <= p)%nat /\ ∃ a, base.lookup (p-1)%nat arr = Some a /\ origin newItem = itemPtr a) ->
  (p = length arr /\ rightOrigin newItem = Last \/ ∃ b, base.lookup p arr = Some b /\ rightOrigin newItem = itemPtr b) ->
  insertIdxIfInBounds i newItem arr = take p arr ++ newItem :: drop p arr.
Proof.
  intros Hinv Hinv' Hile Hple Hleft Hright.
  have Hisi' := yai_item_set_inv _ Hinv'.
  have Hclosed' := yai_closed _ Hinv'.
  have Pnit : newItem ∈ insertIdxIfInBounds i newItem arr by (apply (proj2 (mem_insertIdxIfInBounds _ _ _ _ Hile)); left; reflexivity).
  apply (insert_at_pos arr newItem i p Hinv Hinv' Hile Hple).
  - intros k a Hk Hak.
    destruct Hleft as [[Hp0 _] | [Hp1 [a0 [Ha0 Horig]]]]; [exfalso; lia |].
    have Ha0nit : YjsLt' a0 newItem by (rewrite -Horig; apply item_origin_lt).
    destruct (decide (k = (p - 1)%nat)) as [Hkeq | Hne].
    + rewrite Hkeq Ha0 in Hak. injection Hak as ->. exact Ha0nit.
    + have Hka0 : YjsLt' a a0 by (apply (invariant_yjsarray_idx.getElem_lt_YjsLt' arr k (p-1)%nat a a0 Hinv Hak Ha0); lia).
      have Pa : a ∈ insertIdxIfInBounds i newItem arr by (apply (proj2 (mem_insertIdxIfInBounds _ _ _ _ Hile)); right; exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Hak)).
      have Pa0 : a0 ∈ insertIdxIfInBounds i newItem arr by (apply (proj2 (mem_insertIdxIfInBounds _ _ _ _ Hile)); right; exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Ha0)).
      exact (transitivity.yjs_lt_trans Hisi' Hclosed' (itemPtr a) (itemPtr a0) (itemPtr newItem) Pa Pa0 Pnit Hka0 Ha0nit).
  - intros k b Hk1 Hk2 Hbk.
    destruct Hright as [[Hplen _] | [b0 [Hb0 Horigr]]]; [exfalso; lia |].
    have Hnitb0 : YjsLt' newItem b0 by (rewrite -Horigr; apply item_lt_rightOrigin).
    destruct (decide (k = p)) as [Hkeq | Hne].
    + rewrite Hkeq Hb0 in Hbk. injection Hbk as ->. exact Hnitb0.
    + have Hb0b : YjsLt' b0 b by (apply (invariant_yjsarray_idx.getElem_lt_YjsLt' arr p k b0 b Hinv Hb0 Hbk); lia).
      have Pb : b ∈ insertIdxIfInBounds i newItem arr by (apply (proj2 (mem_insertIdxIfInBounds _ _ _ _ Hile)); right; exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Hbk)).
      have Pb0 : b0 ∈ insertIdxIfInBounds i newItem arr by (apply (proj2 (mem_insertIdxIfInBounds _ _ _ _ Hile)); right; exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Hb0)).
      exact (transitivity.yjs_lt_trans Hisi' Hclosed' (itemPtr newItem) (itemPtr b0) (itemPtr b) Pnit Pb0 Pb Hnitb0 Hb0b).
Qed.

(** In a valid (id-unique) array, [find_by_id] of an element's own id returns
    that element. The reverse of [cells_repr]: locates a model item by id. *)
Lemma find_by_id_self (arr : list (YjsItem A)) (a : YjsItem A) :
  YjsArrInvariant arr -> a ∈ arr -> find_by_id (item_id a) arr = Some a.
Proof.
  intros Hinv Hin. rewrite /find_by_id.
  destruct (list_find (λ item : YjsItem A, item_id item = item_id a) arr) as [[i y]|] eqn:Hlf; last first.
  { exfalso. destruct (list_find_elem_of (λ item : YjsItem A, item_id item = item_id a) arr a Hin eq_refl) as [r Hr]. rewrite Hlf in Hr. done. }
  apply list_find_Some in Hlf as (Hyi & Hpy & _).
  have HyIn : y ∈ arr by exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Hyi).
  have Hya : y = a by exact (id_unique (ArrSet arr) (yai_item_set_inv _ Hinv) y a Hpy HyIn Hin).
  rewrite /= Hya //.
Qed.

(** Companion to [item_valid_at] on the model side: [toItem] resolves the
    straddling input to the [Item] with origins [o]/[r], given each origin id is
    either absent (boundary) or the id of the named neighbour. *)
Lemma toItem_at (arr : list (YjsItem A)) (newid : YjsId) (cont : A) (o r : YjsPtr A)
    (originLeft originRight : option YjsId) :
  YjsArrInvariant arr ->
  (originLeft = None /\ o = First \/ ∃ a, originLeft = Some (item_id a) /\ a ∈ arr /\ o = itemPtr a) ->
  (originRight = None /\ r = Last \/ ∃ b, originRight = Some (item_id b) /\ b ∈ arr /\ r = itemPtr b) ->
  toItem (MkIntegrateInput originLeft originRight cont newid) arr = Some (Item o r newid cont).
Proof.
  intros Hinv Hleft Hright. rewrite /toItem /=.
  destruct Hleft as [[-> ->] | [a [-> [Ha ->]]]].
  - destruct Hright as [[-> ->] | [b [-> [Hb ->]]]].
    + reflexivity.
    + rewrite (find_by_id_self arr b Hinv Hb) /=. reflexivity.
  - rewrite (find_by_id_self arr a Hinv Ha) /=.
    destruct Hright as [[-> ->] | [b [-> [Hb ->]]]].
    + reflexivity.
    + rewrite (find_by_id_self arr b Hinv Hb) /=. reflexivity.
Qed.

(** [wp_Store__integrateCore_cells_run]: the cells-level spec of the DLL-splice
    core for an [n]-char run (issue #28 U7). It forwards
    [wp_Store__integrateCore_aux]'s [n]-char run post directly (no singleton
    collapse), so the produced cell holds the whole run [ic_run c] with
    [length = length (explode (in_content input))]. Unlike the single-char
    version, the model fold's success ([Hall]) is not derived from single
    integrate totality but supplied by the caller (the update path's replay /
    certificates). Local: a stepping stone of [wp_Store__Integrate]. *)
#[local] Lemma wp_Store__integrateCore_cells_run (s parent item_l : loc)
    (arr arr' : list (YjsItem A)) (input : IntegrateInput (A := A))
    (newItem : YjsItem A) (cells : list item_cell)
    (leftIdx rightIdx : Z) (curL curR : nat) :
  YjsArrInvariant arr ->
  toItem input arr = Some newItem ->
  IsItemValid newItem ->
  maximalId newItem arr ->
  findLeftIdx (in_originId input) arr = Some leftIdx ->
  findRightIdx (in_rightOriginId input) arr = Some rightIdx ->
  Forall (λ c, ic_run c ≠ []) cells ->
  (∀ c0, c0 ∈ cells -> cell_fits c0) ->
  (∀ c0, c0 ∈ cells -> cell_origin_clk c0) ->
  (Z.of_nat (length (run_flatten (take curL cells))) = leftIdx + 1)%Z ->
  (curL <= length cells)%nat ->
  (Z.of_nat (length (run_flatten (take curR cells))) = rightIdx)%Z ->
  (curR <= length cells)%nat ->
  integrate_all (ops_of_input input (explode (in_content input))) arr = Some arr' ->
  {{{ is_pkg_init yjs ∗ own_ytype_cells parent (DfracOwn 1) cells arr ∗
      own_linked_item item_l input parent (node_loc cells (Z.of_nat curL - 1)) (node_loc cells (Z.of_nat curR)) }}}
    s @! (go.PointerType yjs.store) @! "integrateCore" #parent #item_l
  {{{ (idx midx : nat) (cells' : list item_cell) (c : item_cell), RET #();
      own_ytype_cells parent (DfracOwn 1) cells' arr' ∗ ⌜YjsArrInvariant arr'⌝ ∗
      ⌜cells' = take idx cells ++ c :: drop idx cells⌝ ∗
      ⌜(idx <= length cells)%nat⌝ ∗
      ⌜length (run_flatten (take idx cells)) = midx⌝ ∗
      ⌜(midx <= length arr)%nat⌝ ∗
      ⌜arr' = take midx arr ++ ic_run c ++ drop midx arr⌝ ∗
      ⌜cells' !! idx = Some c⌝ ∗ ⌜ic_loc c = item_l⌝ ∗
      ⌜item_id (run_head c) = in_id input⌝ ∗ ⌜ic_deleted c = false⌝ ∗
      ⌜origin (run_head c) = origin newItem⌝ ∗ ⌜rightOrigin (run_head c) = rightOrigin newItem⌝ ∗
      ⌜length (ic_run c) = length (explode (in_content input))⌝ ∗
      ⌜cells' ≡ₚ cells ++ [c]⌝ }}}.
Proof using Type*.
  move=> Hinv Htoitem Hvalid Hmax HfindL HfindR Hnec Hfits Hoclk HcurL HcurLb HcurR HcurRb Hall.
  iIntros (Φ) "(Hpkg & Htext & Hfresh) HΦ".
  iDestruct "Hfresh" as (itemVal oleft oright) "(Hraw & %Hfl & %Hfr & %Hfpar & %Hflags & %Hrun)".
  iDestruct "Hraw" as "(Hitem & Holeft & Horight & %Hin_l & %Hin_r & %Hid & %Hcontent)".
  (* the caller's fold premise is over [in_content input]; rewrite it onto the
     item's own content ([toContent itemVal.content = in_content input]) so it feeds
     [integrateCore_aux] verbatim. *)
  have Hcc : explode (toContent itemVal.(yjs.item.content')) = explode (in_content input)
    by rewrite Hcontent.
  have Hall' : integrate_all (ops_of_input input (explode (toContent itemVal.(yjs.item.content')))) arr = Some arr'
    by rewrite Hcc.
  have Hlen1 : (1 <= length (itemVal.(yjs.item.content').(yjs.content.content')))%nat by exact Hrun.
  iAssert (own_fresh_item_raw item_l input itemVal oleft oright) with "[Hitem Holeft Horight]" as "Hraw".
  { iFrame "Hitem Holeft Horight". iPureIntro.
    split_and!; [exact Hin_l | exact Hin_r | exact Hid | exact Hcontent]. }
  wp_apply (wp_Store__integrateCore_aux s parent item_l arr arr' input newItem cells itemVal oleft oright
              leftIdx rightIdx curL curR
              Hinv Htoitem Hvalid Hmax HfindL HfindR Hfl Hfr Hfpar Hflags Hlen1 Hnec Hfits Hoclk
              HcurL HcurLb HcurR HcurRb Hall'
              with "[$Hpkg $Hraw $Htext]").
  iIntros (cells' idx midx c) "(Htext' & %Hinv' & %Hsplice & %Hidxb & %Hcoup & %Hmile & %Harrsp & %Hlook & %Hloc & %Hcid & %Hcdel & %Horig & %Hrorig & %Hclen & %Hperm)".
  iApply ("HΦ" $! idx midx cells' c).
  iFrame "Htext'".
  iPureIntro. split_and!;
    [exact Hinv' | exact Hsplice | exact Hidxb | exact Hcoup | exact Hmile | exact Harrsp
    | exact Hlook | exact Hloc | exact Hcid | exact Hcdel | exact Horig | exact Hrorig
    | rewrite Hclen Hcc // | exact Hperm].
Qed.

(* The former public model-level [wp_Store__integrateCore] (over [own_ytype])
   is retired by #49: the core's precondition now mentions the resolved origin
   neighbours' node locations (the item arrives pre-linked), which a pure
   model-level footprint cannot state. The public story lives one level up
   ([wp_Store__Integrate] and the doc-level [applyUpdate] specs). *)



(** [addNode items it]: append the freshly integrated item to its client's
    run list in [items] (y-octo: [store::add_item], a [&mut self] method
    there; a free function here so the footprint is visible, CLAUDE.md "Spec
    shape"). The cell [c] at [item_l] is the one just spliced into type
    [parent] ([cells' ≡ₚ cells ++ [c]]) and is its client's newest
    ([pool_clock_below]), so the append keeps [own_item_map]'s slices sorted
    by clock. [own_ytype_cells parent] owns [it]'s node, through which the
    function reads [it.id.clientId]. *)
#[local] Lemma wp_addNode (items_mref parent item_l : loc) (types : gmap loc type_state)
    (cells cells' : list item_cell) (arr arr' : list (YjsItem A)) (idx : nat) (c : item_cell) :
  types !! parent = Some (MkTypeState cells arr) ->
  cells' ≡ₚ cells ++ [c] ->
  cells' !! idx = Some c ->
  ic_loc c = item_l ->
  pool_clock_below types (item_id (run_head c)) ->
  {{{ is_pkg_init yjs ∗ own_ytype_cells parent (DfracOwn 1) cells' arr' ∗ own_item_map items_mref (DfracOwn 1) types }}}
    @! yjs.addNode #items_mref #item_l
  {{{ RET #(); own_ytype_cells parent (DfracOwn 1) cells' arr' ∗
      own_item_map items_mref (DfracOwn 1) (<[parent := MkTypeState cells' arr']> types) }}}.
Proof using Type*.
  move=> Htypes Hperm Hlook Hloc Hgmax.
  wp_start as "(Htext' & Hitemmap)".
  wp_auto.
  iDestruct "Htext'" as (yt tl) "(Hpar & Hdll & %Hlen' & %Hrepr' & %Hcpar')".
  iDestruct (own_dll_acc_node (DfracOwn 1) cells' yt.(yjs.yType.start') tl idx c Hlook with "Hdll")
    as (prevn nxtn) "(%Hcloc & %Hcl & %Hcr & %Hrun & %Hclen & %Hpc & Hnode & Hback)".
  iDestruct "Hnode" as (itemVal olid orid)
    "(Hcval & Hcol & Hcor & %Hinl & %Hinr & %Hidn & %Hcont & %Hpar & %Hprevn & %Hnextn & %Hflags)".
  have Hid : item_id (run_head c) = toYjsId itemVal.(yjs.item.id').
  { symmetry. exact Hidn. }
  iEval (rewrite Hloc) in "Hcval".
  wp_auto.
  iNamed "Hitemmap".
  have Hcc : cell_client c = itemVal.(yjs.item.id').(yjs.id.clientId')
    by (rewrite /cell_client Hid /toYjsId /=; word).
  wp_apply (wp_map_lookup1 with "Hmap"). iIntros "Hmap". wp_auto.
  have Hac2 : all_cells (<[parent := {| ty_cells := cells'; ty_arr := arr' |}]> types)
              ≡ₚ all_cells types ++ [c]
    by apply (all_cells_insert_snoc types parent cells arr cells' arr' c Htypes Hperm).
  have Hkp : cell_kp <$> all_cells (<[parent := {| ty_cells := cells'; ty_arr := arr' |}]> types)
             ≡ₚ (cell_kp <$> all_cells types) ++ [cell_kp c]
    by rewrite Hac2 fmap_app.
  have Hmax_arg : ∀ c0, c0 ∈ all_cells types → cell_client c0 = cell_client c →
                    ((cell_pr c0).1 < (cell_pr c).1)%Z.
  { intros c0 Hc0 Hcce. rewrite /cell_pr /=.
    have Hcc' : cell_client c0 = W64 (clientId (item_id (run_head c))) by rewrite Hcce.
    exact (proj1 (Hgmax c0 Hc0 Hcc')). }
  have Hrun_eq := client_run_loc_tail types
                    (<[parent := {| ty_cells := cells'; ty_arr := arr' |}]> types) c Hkp Hclkloc Hmax_arg.
  set (kc := itemVal.(yjs.item.id').(yjs.id.clientId')) in *.
  rewrite Hcc in Hrun_eq.
  iAssert ((default slice.nil (gm !! kc)) ↦* (ic_loc <$> client_run types kc) ∗
           own_slice_cap loc (default slice.nil (gm !! kc)) (DfracOwn 1) ∗
           ([∗ map] client↦s0 ∈ delete kc gm,
              "Hslice" ∷ s0 ↦* (ic_loc <$> client_run types client) ∗
              "Hcap" ∷ own_slice_cap loc s0 (DfracOwn 1)))%I
    with "[Hruns]" as "(Hlk_slice & Hlk_cap & Hrunsrest)".
  { destruct (gm !! kc) as [s_old|] eqn:Hgmk.
    - iDestruct (big_sepM_delete _ _ _ _ Hgmk with "Hruns") as "[Hkey Hrest]".
      iNamed "Hkey". simpl. iFrame "Hslice Hcap Hrest".
    - have Hempty : client_run types kc = [].
      { rewrite /client_run.
        destruct (filter (λ c0 : item_cell, cell_client c0 = kc) (all_cells types)) as [|a l'] eqn:Ef.
        - reflexivity.
        - exfalso.
          have Ha : a ∈ filter (λ c0 : item_cell, cell_client c0 = kc) (all_cells types)
            by (rewrite Ef; left).
          rewrite list_elem_of_filter in Ha. destruct Ha as [Hcck Hain].
          have Hin : kc ∈ cell_client <$> all_cells types
            by (rewrite -Hcck; apply list_elem_of_fmap_2; exact Hain).
          destruct (Hcomplete kc Hin) as [sx Hsome]. rewrite Hgmk in Hsome. discriminate. }
      simpl. rewrite Hempty /= (delete_id gm kc Hgmk).
      iFrame "Hruns". iSplitR; [iApply own_slice_nil | iApply own_slice_cap_nil]. }
  wp_apply wp_slice_literal. iSplitR; first done. iIntros "%s2 [Hs2 _]". wp_auto.
  wp_apply (wp_slice_append with "[$Hlk_slice $Hlk_cap $Hs2]").
  iIntros (snew) "(Hsnew & Hsnewcap & _)". wp_auto.
  have Heq : (ic_loc <$> client_run types kc) ++ <[sint.nat (W64 0):=item_l]> ([null] : list loc)
           = ic_loc <$> client_run (<[parent:={| ty_cells := cells'; ty_arr := arr' |}]> types) kc.
  { rewrite Hrun_eq. f_equal. rewrite Hloc. have H0 : sint.nat (W64 0) = 0%nat by word. rewrite H0 //. }
  iEval (rewrite Heq) in "Hsnew".
  wp_apply (wp_map_insert with "Hmap"). iIntros "Hmap". wp_auto.
  set (types2 := <[parent := {| ty_cells := cells'; ty_arr := arr' |}]> types).
  have Hdecomp : ∀ c0, c0 ∈ all_cells types2 → c0 ∈ all_cells types ∨ c0 = c.
  { intros c0 Hc0. rewrite Hac2 in Hc0.
    apply elem_of_app in Hc0 as [H|H]; [left; exact H | right; by apply list_elem_of_singleton]. }
  have Hcomplete' : ∀ c0 : w64, c0 ∈ cell_client <$> all_cells types2 → is_Some (<[kc:=snew]> gm !! c0).
  { intros c0 Hc0. apply list_elem_of_fmap in Hc0 as (cc & -> & Hcc0).
    destruct (Hdecomp cc Hcc0) as [Hin | ->].
    - destruct (decide (cell_client cc = kc)) as [Hek|Hne]; [rewrite Hek lookup_insert_eq; eauto |].
      rewrite lookup_insert_ne; [| congruence]. apply Hcomplete. apply list_elem_of_fmap_2. exact Hin.
    - rewrite Hcc lookup_insert_eq; eauto. }
  have Hclkloc' : ∀ c1 c2, c1 ∈ all_cells types2 → c2 ∈ all_cells types2 →
                    cell_client c1 = cell_client c2 → (cell_pr c1).1 = (cell_pr c2).1 → ic_loc c1 = ic_loc c2.
  { intros c1 c2 Hc1 Hc2 Hcce Hpre.
    destruct (Hdecomp c1 Hc1) as [Hin1 | ->]; destruct (Hdecomp c2 Hc2) as [Hin2 | ->];
      [exact (Hclkloc c1 c2 Hin1 Hin2 Hcce Hpre)
      | exfalso; have := Hmax_arg c1 Hin1 Hcce; lia
      | exfalso; have := Hmax_arg c2 Hin2 (eq_sym Hcce); lia
      | reflexivity]. }
  iEval (rewrite -Hloc) in "Hcval".
  iAssert (own_item_node (ic_loc c) (DfracOwn 1) (input_of_run (cell_run c))
             (ic_deleted c) (ic_parent c) prevn nxtn) with "[Hcval Hcol Hcor]" as "Hnode".
  { iExists itemVal, olid, orid. iFrame "Hcval Hcol Hcor".
    iPureIntro. split_and!;
      [exact Hinl | exact Hinr | exact Hidn | exact Hcont | exact Hpar
      | exact Hprevn | exact Hnextn | exact Hflags]. }
  iDestruct ("Hback" with "Hnode") as "Hdll".
  iAssert (own_item_map items_mref (DfracOwn 1) types2) with "[Hmap Hsnew Hsnewcap Hrunsrest]" as "Hitemmap'".
  { iExists (<[kc:=snew]> gm). iFrame "Hmap".
    iSplitL "Hsnew Hsnewcap Hrunsrest".
    - rewrite big_sepM_insert_delete. iSplitL "Hsnew Hsnewcap"; [iFrame "Hsnew Hsnewcap"|].
      iApply (big_sepM_impl with "Hrunsrest").
      iIntros "!#" (client s0 Hcs) "H". iNamed "H".
      have Hne : client ≠ cell_client c.
      { rewrite Hcc. intros ->. rewrite lookup_delete_eq in Hcs. discriminate. }
      rewrite (client_run_loc_other types types2 c client Hkp Hclkloc Hne).
      iFrame "Hslice Hcap".
    - iPureIntro. split; [exact Hcomplete' | exact Hclkloc']. }
  iApply "HΦ".
  iSplitL "Hpar Hdll".
  { iExists yt, tl. iFrame "Hpar Hdll". iPureIntro. split_and!; [exact Hlen' | exact Hrepr' | exact Hcpar']. }
  iFrame "Hitemmap'".
Qed.

(** [Store.Integrate parent item]: splice the fresh linked item [item_l] into
    the type [parent] of the store (the argument may be [null], in which case
    the item's own [parent] field names the type). The model takes the
    [integrate_all] step of the item's chars ([integrate_ready]), the type's
    cell list gets the run at the matching position ([integrate_splice]), the
    run is the input's ([run_denotes]), and the store's invariants survive:
    the item's chars fit ([input_fits]) and its id is its client's newest in
    the whole pool ([pool_clock_below]). *)
Lemma wp_Store__Integrate (s parent parent_arg item_l : loc) (st : store_state)
    (cells : list item_cell) (arr arr' : list (YjsItem A))
    (input : IntegrateInput (A := A)) (newItem : YjsItem A) (lft rgt : loc) :
  parent_arg = parent ∨ parent_arg = null ->
  ss_types st !! parent = Some (MkTypeState cells arr) ->
  integrate_ready arr input newItem ->
  input_fits input ->
  integrate_all (ops_of_input input (explode (in_content input))) arr = Some arr' ->
  origins_linked cells arr input lft rgt ->
  pool_clock_below (ss_types st) (in_id input) ->
  {{{ is_pkg_init yjs ∗ own_store_struct s st ∗ own_linked_item item_l input parent lft rgt }}}
    s @! (go.PointerType yjs.store) @! "Integrate" #parent_arg #item_l
  {{{ (cells' : list item_cell) (run : list (YjsItem A)), RET #();
      own_store_struct s (st <| ss_types := <[parent := MkTypeState cells' arr']> (ss_types st) |>) ∗
      ⌜YjsArrInvariant arr'⌝ ∗
      ⌜integrate_splice cells arr item_l run parent cells' arr'⌝ ∗
      ⌜run_denotes input newItem run⌝ }}}.
Proof using Type*.
  move=> Hparg Hts Hready Hfitsin Hall Hlinked Hbelow.
  destruct st as [client0 k0 types bind pend pdel]. simpl in *.
  have Htypes := Hts.
  have [Htoitem [Hvalid Hmax]] := Hready.
  have Hgmax := Hbelow.
  destruct Hlinked as (leftIdx & rightIdx & curL & curR & HfindL & HfindR & -> & -> & HcurL & HcurLb & HcurR & HcurRb).
  iIntros (Φ) "(#Hpkg & Hcells & Hfresh) HΦ".
  iDestruct "Hcells" as "(Hfields0 & %Hinvs0)".
  have Hpool : pool_invs types := proj1 Hinvs0.
  have Hreg : registry_coh bind types := proj2 Hinvs0.
  iDestruct "Hfields0" as "(Hclient & Hclock & HdeletedSet & Hitems & Hregistry & Htypes0 & Hpending & Hpdeletes)".
  iDestruct (linked_item_fresh2 with "Hfresh Htypes0") as %Hfreshloc.
  rewrite /own_type_pool.
  iDestruct (big_sepM_delete _ _ parent _ Hts with "Htypes0") as "[[Htext %Hinv] Htypesrest]".
  have Hidnew : item_id newItem = in_id input := commutativity.toItem_id input arr newItem Htoitem.
  (* the per-cell side conditions of the core, from the pool invariants *)
  have Hcellsall : ∀ c0, c0 ∈ cells -> c0 ∈ all_cells types.
  { move=> c0 Hc0. apply all_cells_elem_of. exists parent, (MkTypeState cells arr).
    split; [exact Htypes | exact Hc0]. }
  have [Hfitsall [_ [_ Hoclkall]]] := Hpool.
  have Hfits : ∀ c0, c0 ∈ cells -> cell_fits c0 := λ c0 Hc0, Hfitsall c0 (Hcellsall c0 Hc0).
  have Hoclk : ∀ c0, c0 ∈ cells -> cell_origin_clk c0 := λ c0 Hc0, Hoclkall c0 (Hcellsall c0 Hc0).
  iDestruct "Htext" as (yt0 tl0) "(Hparent0 & Hdll0 & %Hlen0 & %Hrepr0 & %Hcpar0)".
  iDestruct (own_dll_runs_wf with "Hdll0") as %Hwfs.
  have Hnec : Forall (λ c, ic_run c ≠ []) cells.
  { apply Forall_forall. move=> c0 Hc0. exact (proj1 (Hwfs c0 Hc0)). }
  iDestruct (typed_pointsto_not_null with "Hparent0") as %Hpnn.
  iAssert (own_ytype_cells parent (DfracOwn 1) cells arr) with "[Hparent0 Hdll0]" as "Htext".
  { iExists yt0, tl0. iFrame "Hparent0 Hdll0". iPureIntro.
    split_and!; [exact Hlen0 | exact Hrepr0 | exact Hcpar0]. }
  iDestruct "Hfresh" as (iv2 oleft2 oright2) "(Hraw & %Hfl2 & %Hfr2 & %Hfpar2 & %Hflags2 & %Hrun2)".
  iNamed "Hraw".
  wp_method_call. wp_call. wp_call. wp_auto.
  (* the parent argument: given, or read off the item (the update path) *)
  destruct Hparg as [-> | ->].
  - rewrite (bool_decide_eq_false_2 (parent = null) Hpnn). wp_auto.
    iAssert (own_linked_item item_l input parent (node_loc cells (Z.of_nat curL - 1)) (node_loc cells (Z.of_nat curR)))
      with "[Hitem Holeft Horight]" as "Hfresh".
    { iExists iv2, oleft2, oright2. rewrite /own_fresh_item_raw.
      iFrame "Hitem Holeft Horight". iPureIntro.
      split_and!; [exact Hin_l | exact Hin_r | exact Hid | exact Hcontent
                  | exact Hfl2 | exact Hfr2 | exact Hfpar2 | exact Hflags2 | exact Hrun2]. }
    wp_apply (wp_Store__integrateCore_cells_run s parent item_l arr arr' input newItem cells
                leftIdx rightIdx curL curR
                Hinv Htoitem Hvalid Hmax HfindL HfindR Hnec Hfits Hoclk
                HcurL HcurLb HcurR HcurRb Hall with "[$Hpkg $Htext $Hfresh]").
    iIntros (idx midx cells' c) "(Htext' & %Hinv' & %Hsplice & %Hidxb & %Hcoup & %Hmile & %Harrsp & %Hlook & %Hloc & %Hcid & %Hcdel & %Horig & %Hrorig & %Hclen & %Hperm)".
    wp_auto.
    have Hgmaxc : pool_clock_below types (item_id (run_head c)) by rewrite Hcid.
    iDestruct "Hitems" as (items_mref) "(Hitemsf & Hitemmap)".
    wp_auto.
    wp_apply (wp_addNode items_mref parent item_l types cells cells' arr arr' idx c
                Htypes Hperm Hlook Hloc Hgmaxc with "[$Hpkg $Htext' $Hitemmap]").
    iIntros "(Htext' & Hitemmap)".
    iAssert (own_items_field (s .[(yjs.store.t), "items"]) (<[parent := MkTypeState cells' arr']> types))%I
      with "[Hitemsf Hitemmap]" as "Hitems".
    { iExists items_mref. iFrame "Hitemsf Hitemmap". }
    wp_auto.
    iDestruct "Htext'" as (yt tl) "(Hpar & Hdll & %Hlen' & %Hrepr' & %Hcpar')".
    have Hcpar_c : ic_parent c = parent := Hcpar' c (list_elem_of_lookup_2 _ _ _ Hlook).
    have Hc_eq : c = MkItemCell item_l (ic_run c) false parent.
    { destruct c as [cl cr cd cp]. simpl in Hloc, Hcdel, Hcpar_c. rewrite Hloc Hcdel Hcpar_c //. }
    have Hsplice_post : integrate_splice cells arr item_l (ic_run c) parent cells' arr'.
    { exists idx. refine (conj Hidxb (conj _ (conj _ _))).
      - rewrite Hcoup. exact Hmile.
      - rewrite -Hc_eq. exact Hsplice.
      - rewrite Hcoup. exact Harrsp. }
    have Hrun_post : run_denotes input newItem (ic_run c)
      by (split_and!; [exact Hcid | exact Horig | exact Hrorig | rewrite Hclen explode_length //]).
    have Hbelowc : pool_clock_below types (item_id (run_head c)).
    { rewrite /run_head Hcid. exact Hgmax. }
    have Hfitsc : cell_fits c.
    { rewrite /cell_fits /cell_clock /run_head Hcid Hclen explode_length.
      move: Hfitsin. rewrite /input_fits. word. }
    have Hoc : cell_origin_clk c.
    { move=> originId Hoid Hcl. rewrite /run_head /= in Hoid Hcl *.
      rewrite Horig in Hoid. rewrite Hcid -Hidnew in Hcl *.
      exact (integrate_ready_origin_clk arr input newItem (conj Htoitem (conj Hvalid Hmax)) originId Hoid Hcl). }
    have Hfreshc : ic_loc c ∉ ic_loc <$> all_cells types by rewrite Hloc; exact Hfreshloc.
    have Hpool' : pool_invs (<[parent := MkTypeState cells' arr']> types)
      := pool_invs_integrate types parent cells arr cells' arr' c Hpool Htypes Hperm Hfreshc Hfitsc Hbelowc Hoc.
    have Hreg' : registry_coh bind (<[parent := MkTypeState cells' arr']> types)
      := registry_coh_insert _ _ parent _ _ Htypes Hreg.
    iAssert (own_type_pool (DfracOwn 1) (<[parent := MkTypeState cells' arr']> types))
      with "[Hpar Hdll Htypesrest]" as "Htypes1".
    { rewrite /own_type_pool -insert_delete_eq big_sepM_insert; last apply lookup_delete_eq.
      iFrame "Htypesrest". simpl. iSplitL; last (iPureIntro; exact Hinv').
      iExists yt, tl. iFrame "Hpar Hdll". iPureIntro. split_and!; [exact Hlen' | exact Hrepr' | exact Hcpar']. }
    iApply ("HΦ" $! cells' (ic_run c)).
    iSplitL "Hclient Hclock HdeletedSet Hitems Hregistry Htypes1 Hpending Hpdeletes";
      last by (iPureIntro; split_and!; [exact Hinv' | exact Hsplice_post | exact Hrun_post]).
    iSplitL; last by (iPureIntro; split; [exact Hpool' | exact Hreg']).
    simpl. iFrame.
  - wp_auto. rewrite Hfpar2 (bool_decide_eq_false_2 (parent = null) Hpnn).
    wp_auto.
    iAssert (own_linked_item item_l input parent (node_loc cells (Z.of_nat curL - 1)) (node_loc cells (Z.of_nat curR)))
      with "[Hitem Holeft Horight]" as "Hfresh".
    { iExists iv2, oleft2, oright2. rewrite /own_fresh_item_raw.
      iFrame "Hitem Holeft Horight". iPureIntro.
      split_and!; [exact Hin_l | exact Hin_r | exact Hid | exact Hcontent
                  | exact Hfl2 | exact Hfr2 | exact Hfpar2 | exact Hflags2 | exact Hrun2]. }
    rewrite Hfpar2.
    wp_apply (wp_Store__integrateCore_cells_run s parent item_l arr arr' input newItem cells
                leftIdx rightIdx curL curR
                Hinv Htoitem Hvalid Hmax HfindL HfindR Hnec Hfits Hoclk
                HcurL HcurLb HcurR HcurRb Hall with "[$Hpkg $Htext $Hfresh]").
    iIntros (idx midx cells' c) "(Htext' & %Hinv' & %Hsplice & %Hidxb & %Hcoup & %Hmile & %Harrsp & %Hlook & %Hloc & %Hcid & %Hcdel & %Horig & %Hrorig & %Hclen & %Hperm)".
    wp_auto.
    have Hgmaxc : pool_clock_below types (item_id (run_head c)) by rewrite Hcid.
    iDestruct "Hitems" as (items_mref) "(Hitemsf & Hitemmap)".
    wp_auto.
    wp_apply (wp_addNode items_mref parent item_l types cells cells' arr arr' idx c
                Htypes Hperm Hlook Hloc Hgmaxc with "[$Hpkg $Htext' $Hitemmap]").
    iIntros "(Htext' & Hitemmap)".
    iAssert (own_items_field (s .[(yjs.store.t), "items"]) (<[parent := MkTypeState cells' arr']> types))%I
      with "[Hitemsf Hitemmap]" as "Hitems".
    { iExists items_mref. iFrame "Hitemsf Hitemmap". }
    wp_auto.
    iDestruct "Htext'" as (yt tl) "(Hpar & Hdll & %Hlen' & %Hrepr' & %Hcpar')".
    have Hcpar_c : ic_parent c = parent := Hcpar' c (list_elem_of_lookup_2 _ _ _ Hlook).
    have Hc_eq : c = MkItemCell item_l (ic_run c) false parent.
    { destruct c as [cl cr cd cp]. simpl in Hloc, Hcdel, Hcpar_c. rewrite Hloc Hcdel Hcpar_c //. }
    have Hsplice_post : integrate_splice cells arr item_l (ic_run c) parent cells' arr'.
    { exists idx. refine (conj Hidxb (conj _ (conj _ _))).
      - rewrite Hcoup. exact Hmile.
      - rewrite -Hc_eq. exact Hsplice.
      - rewrite Hcoup. exact Harrsp. }
    have Hrun_post : run_denotes input newItem (ic_run c)
      by (split_and!; [exact Hcid | exact Horig | exact Hrorig | rewrite Hclen explode_length //]).
    have Hbelowc : pool_clock_below types (item_id (run_head c)).
    { rewrite /run_head Hcid. exact Hgmax. }
    have Hfitsc : cell_fits c.
    { rewrite /cell_fits /cell_clock /run_head Hcid Hclen explode_length.
      move: Hfitsin. rewrite /input_fits. word. }
    have Hoc : cell_origin_clk c.
    { move=> originId Hoid Hcl. rewrite /run_head /= in Hoid Hcl *.
      rewrite Horig in Hoid. rewrite Hcid -Hidnew in Hcl *.
      exact (integrate_ready_origin_clk arr input newItem (conj Htoitem (conj Hvalid Hmax)) originId Hoid Hcl). }
    have Hfreshc : ic_loc c ∉ ic_loc <$> all_cells types by rewrite Hloc; exact Hfreshloc.
    have Hpool' : pool_invs (<[parent := MkTypeState cells' arr']> types)
      := pool_invs_integrate types parent cells arr cells' arr' c Hpool Htypes Hperm Hfreshc Hfitsc Hbelowc Hoc.
    have Hreg' : registry_coh bind (<[parent := MkTypeState cells' arr']> types)
      := registry_coh_insert _ _ parent _ _ Htypes Hreg.
    iAssert (own_type_pool (DfracOwn 1) (<[parent := MkTypeState cells' arr']> types))
      with "[Hpar Hdll Htypesrest]" as "Htypes1".
    { rewrite /own_type_pool -insert_delete_eq big_sepM_insert; last apply lookup_delete_eq.
      iFrame "Htypesrest". simpl. iSplitL; last (iPureIntro; exact Hinv').
      iExists yt, tl. iFrame "Hpar Hdll". iPureIntro. split_and!; [exact Hlen' | exact Hrepr' | exact Hcpar']. }
    iApply ("HΦ" $! cells' (ic_run c)).
    iSplitL "Hclient Hclock HdeletedSet Hitems Hregistry Htypes1 Hpending Hpdeletes";
      last by (iPureIntro; split_and!; [exact Hinv' | exact Hsplice_post | exact Hrun_post]).
    iSplitL; last by (iPureIntro; split; [exact Hpool' | exact Hreg']).
    simpl. iFrame.
Qed.


(** [Store.Integrate] at run granularity: the origins are read at their run
    cursors ([origins_resolved]) and the two link addresses off the address
    list ([loc_at]); the postcondition splices the run and the fresh address
    at one shared cursor. Derived from [wp_Store__Integrate] through the
    [pool_of] / [locs_of] projections. *)
Lemma wp_store__Integrate_runs (s parent parent_arg item_l : loc)
    (str : store_state_runs) (tm : type_model) (ls : list loc)
    (arr' : list (YjsItem A)) (input : IntegrateInput (A := A))
    (newItem : YjsItem A) (kL kR : nat) :
  parent_arg = parent ∨ parent_arg = null ->
  sr_pool str !! parent = Some tm ->
  sr_locs str !! parent = Some ls ->
  integrate_ready (tm_arr tm) input newItem ->
  input_fits input ->
  (Z.of_nat (clientId (in_id input)) < 2^64)%Z ->
  integrate_all (ops_of_input input (explode (in_content input))) (tm_arr tm) = Some arr' ->
  origins_resolved (tm_runs tm) (tm_arr tm) input kL kR ->
  pool_run_clock_below (sr_pool str) (in_id input) ->
  {{{ is_pkg_init yjs ∗ own_store_runs s str ∗
      own_linked_item item_l input parent
        (loc_at ls (Z.of_nat kL - 1)) (loc_at ls (Z.of_nat kR)) }}}
    s @! (go.PointerType yjs.store) @! "Integrate" #parent_arg #item_l
  {{{ (runs' : list ItemRun) (ls' : list loc) (run : list (YjsItem A)), RET #();
      own_store_runs s (str <| sr_pool := <[parent := MkTypeModel runs' arr']> (sr_pool str) |>
                            <| sr_locs := <[parent := ls']> (sr_locs str) |>) ∗
      ⌜YjsArrInvariant arr'⌝ ∗
      ⌜∃ idx : nat, runs_integrate_splice_at idx (tm_runs tm) (tm_arr tm) run runs' arr' ∧
                    ls' = integrate_locs ls idx item_l⌝ ∗
      ⌜run_denotes input newItem run⌝ }}}.
Proof using Type*.
  move=> Hparg Hpl Hlocs Hready Hfitsin Hclbnd Hall Hres Hbelow.
  iIntros (Φ) "(#Hpkg & Hruns & Hfresh) HΦ".
  iEval (rewrite own_store_runs_as_state) in "Hruns".
  iDestruct "Hruns" as (st) "(%Hproj & Hcells)".
  subst str. destruct st as [client k0 types bind pend pdel]. simpl in *.
  rewrite /pool_of lookup_fmap in Hpl.
  destruct (types !! parent) as [ts|] eqn:Hts; simplify_eq/=.
  destruct ts as [cells arr]. simpl in *.
  have Hls : ls = ic_loc <$> cells.
  { rewrite /locs_of lookup_fmap Hts /= in Hlocs. congruence. }
  iDestruct "Hcells" as "(Hfields0 & %Hinvs0)".
  iDestruct "Hfields0" as "(Hclient & Hclock & HdeletedSet & Hitems & Hregistry & Htypes & Hpending & Hpdeletes)".
  iDestruct (own_type_pool_id_bounds with "Htypes") as %Hbndb.
  iDestruct (own_type_pool_runs_wf with "Htypes") as %Hwfb.
  iDestruct (own_store_struct_intro _ (MkStoreState client k0 types bind pend pdel) Hinvs0
               with "Hclient Hclock HdeletedSet Hitems Hregistry Htypes Hpending Hpdeletes") as "Hcells".
  have Hidck : (Z.of_nat (clock (in_id input)) < 2^64)%Z.
  { move: Hfitsin. rewrite /input_fits. lia. }
  have Hbelow' : pool_clock_below types (in_id input)
    := pool_run_clock_below_to_cell types (in_id input)
         (λ c Hc, proj2 (Hbndb c Hc)) (λ c Hc, proj1 (Hbndb c Hc))
         (λ c Hc, proj1 (Hwfb c Hc)) Hclbnd Hidck Hbelow.
  have Hlinked : origins_linked cells arr input
                   (loc_at ls (Z.of_nat kL - 1)) (loc_at ls (Z.of_nat kR)).
  { rewrite Hls -!node_loc_loc_at. apply/origins_linked_resolved.
    exists kL, kR. split_and!; [exact Hres | done | done]. }
  wp_apply (wp_Store__Integrate s parent parent_arg item_l
              (MkStoreState client k0 types bind pend pdel) cells arr arr' input newItem
              (loc_at ls (Z.of_nat kL - 1)) (loc_at ls (Z.of_nat kR))
              Hparg Hts Hready Hfitsin Hall Hlinked Hbelow'
              with "[$Hpkg $Hcells $Hfresh]").
  iIntros (cells' run) "(Hcells & %Hinv' & %Hsplice & %Hden)".
  iEval (simpl) in "Hcells".
  have Hrl := integrate_splice_runs_locs cells arr item_l run parent cells' arr' Hsplice.
  destruct Hrl as (idx & Hat & Hlocs').
  iApply ("HΦ" $! (cell_run <$> cells') (ic_loc <$> cells') run).
  iSplitL.
  { rewrite own_store_runs_as_state. iExists (MkStoreState client k0 (<[parent := MkTypeState cells' arr']> types) bind pend pdel).
    iFrame "Hcells". iPureIntro.
    rewrite /state_runs_of /= pool_of_insert locs_of_insert /type_model_of /=.
    reflexivity. }
  iPureIntro. split_and!.
  - exact Hinv'.
  - exists idx. split; [exact Hat | rewrite Hls; exact Hlocs'].
  - exact Hden.
Qed.

End store_integrate.
