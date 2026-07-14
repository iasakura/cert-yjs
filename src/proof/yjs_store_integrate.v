(** WP proofs for the [store] integration stack: the id-lookup helpers
    ([containsId] / [findById] / [itemPtrEqual]), the conflict scan
    ([scanConflicts] / [findIntegrationLeft]) refining [setfii_loop] (the
    splice lands at the pure [setfindIntegratedIndex] and the result inherits
    [YjsArrInvariant] from [YjsArrInvariant_integrate]), the item-validity /
    insertion helper lemmas ([item_valid_*], [insert_*], [toItem_at]), and the
    top-level [Store.Integrate] (cells-level and model-level, including the
    per-client item-map maintenance).

    Split out of [yjs_store_base] (the predicates and the lock layer) so
    these heavy loop proofs compile in their own [.vo]; the update path
    continues in [yjs_store_update], and downstream files see everything
    through the [yjs_store] facade. Same [Section] boilerplate; [Type*]
    footprints. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import yjs_core.
From New.proof Require Import yjs_common yjs_id yjs_item yjs_ytype.
From New.proof Require Import yjs_history.
From New.proof Require Import yjs_store_base.
From iris.algebra Require Import auth gmap gset.
From stdpp Require Import sorting.

(* iris.algebra / stdpp.sorting push [nat_scope], retuning the default [<] / [≤].
   The verified WP proofs write [Z] comparisons (e.g. [sint.Z i < …]) unannotated
   and annotate [nat] ones with [%nat], so restore [Z_scope] as the default. *)
Local Open Scope Z_scope.

(** Small-context set rewrites for the conflict-scan accumulators. After a Go
    [append] of the conflict id, an id slice abstracts to [X ∪ ({[a]} ∪ ∅)] (the
    trailing [∅] is [list_to_set []] from the singleton tail); these relate that
    to the [setfii_loop] accumulator form [{[a]} ∪ X]. Proving them as standalone
    lemmas keeps [set_solver] on a tiny context — calling [set_solver] inside
    [wp_scanConflicts] instead does [set_unfold in *] over the whole proof state
    (including the [list_to_set] slice hypotheses) and is prohibitively slow.

    They live at top level (outside [Section store]): [set_solver] runs
    [set_unfold in *], which would otherwise pull the heap section variables into
    the proof term and force them into the lemma's [Proof using] footprint. Only
    this module uses them, so they sit here rather than in [yjs_common]. *)
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
Local Notation DocM := (gmap TId (list (YjsItem A))).

(** [containsId] decides membership of the id slice as a [gset] (via [toYjsId]). *)
Lemma wp_containsId (s : slice.t) (vs : list yjs.id.t) (id : yjs.id.t) (dq : dfrac) :
  {{{ is_pkg_init yjs ∗ s ↦*{dq} vs }}}
    @! yjs.containsId #s #id
  {{{ RET #(bool_decide (toYjsId id ∈ (list_to_set (toYjsId <$> vs) : gset YjsId)));
      s ↦*{dq} vs }}}.
Proof.
  wp_start as "Hs". wp_auto.
  iAssert (∃ (i : w64) (xv : yjs.id.t),
    "Hi" ∷ i_ptr ↦ i ∗ "Hx" ∷ x_ptr ↦ xv ∗ "Hs" ∷ s ↦*{dq} vs ∗
    "%Hib" ∷ ⌜(0 ≤ uint.Z i ≤ Z.of_nat (length vs))%Z⌝ ∗
    "%Hnf" ∷ ⌜toYjsId id ∉ (list_to_set (toYjsId <$> take (uint.nat i) vs) : gset YjsId)⌝)%I
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
    wp_auto. wp_method_call; wp_call; wp_auto. wp_apply (wp_Id__Equal v id).
    have Hv' : vs !! sint.nat i = Some v.
    { replace (sint.nat i) with (uint.nat i) by word. exact Hv. }
    iDestruct ("Hrest" $! v with "Hel") as "Hs".
    iEval (rewrite (list_insert_id _ _ _ Hv')) in "Hs".
    wp_if_destruct.
    + wp_for_post.
      have Hin : toYjsId id ∈ (list_to_set (toYjsId <$> vs) : gset YjsId).
      { rewrite elem_of_list_to_set.
        apply (list_elem_of_fmap_2' toYjsId vs v);
          [ by eapply list_elem_of_lookup_2 | by rewrite e ]. }
      iEval (rewrite (bool_decide_eq_true_2 _ Hin)) in "HΦ". iApply "HΦ". iFrame.
    + wp_for_post.
      iFrame "HΦ id". iExists (word.add i (W64 1)), v. iFrame.
      iPureIntro. split.
      * word.
      * replace (uint.nat (word.add i (W64 1))) with (S (uint.nat i)) by word.
        rewrite (take_S_r _ _ v); [| exact Hv].
        rewrite fmap_app list_to_set_app.
        apply not_elem_of_union. split; [exact Hnf | set_solver].
  - apply bool_decide_eq_false in Hlt. wp_auto.
    have Hge : (length vs <= uint.nat i)%nat by word.
    rewrite (take_ge _ _ Hge) in Hnf.
    iEval (rewrite (bool_decide_eq_false_2 _ Hnf)) in "HΦ".
    iApply "HΦ". iFrame.
Qed.

(* ----- findById: locate a node by id in the DLL ------------------------- *)

(** The cell predicate [findById] decides: a cell whose model id is [toYjsId idv].
    [findById] returns the first matching node's location, or [null]. *)
Definition cell_has_id (idv : yjs.id.t) (c : item_cell) : Prop :=
  item_id (run_head c) = toYjsId idv.

#[local] Instance cell_has_id_dec idv c : Decision (cell_has_id idv c).
Proof. rewrite /cell_has_id. apply _. Defined.

(** Result location of [findById] over a cell list: first match, else [null]. *)
Definition findById_res (cells : list item_cell) (idv : yjs.id.t) : loc :=
  match list_find (cell_has_id idv) cells with
  | Some (_, c) => ic_loc c
  | None => null
  end.

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

(** Comparing a node pointer with itself is always [true] (it has its own id). *)
Lemma wp_itemPtrEqual_self (p : loc) (v : yjs.item.t) (dq : dfrac) :
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

(** Comparing two DLL nodes by [itemPtrEqual] decides index equality: under the
    id-uniqueness of [arr], two nodes have the same id exactly when they are the
    same node. [a]/[b] range over [[0, length cells]] (the [length] sentinel is
    the [null] / [Last] boundary), with [a <= b]. Used for the [conflict == right]
    break test and the entry [left.right == right] test. *)
Lemma wp_itemPtrEqual_node (parent : loc) (dq : dfrac) (cells : list item_cell)
    (arr : list (YjsItem A)) (a b : Z) :
  YjsArrInvariant arr ->
  Forall cell_unit cells ->
  (0 <= a)%Z -> (a <= b)%Z -> (b <= Z.of_nat (length cells))%Z ->
  {{{ is_pkg_init yjs ∗ own_ytype_cells parent dq cells arr }}}
    @! yjs.itemPtrEqual #(node_loc cells a) #(node_loc cells b)
  {{{ RET #(bool_decide (a = b)); own_ytype_cells parent dq cells arr }}}.
Proof.
  move=> Harr Hunitc Ha0 Hab Hblen.
  iIntros (Φ) "[#Hpkg Ht] HΦ". iNamed "Ht".
  have Hlen_eq : length cells = length arr := cells_repr_length _ _ _ Hunitc Hrepr.
  destruct (decide (a = b)) as [Heq | Hne].
  - subst b. rewrite bool_decide_eq_true_2; last reflexivity.
    destruct (decide (a < Z.of_nat (length cells))%Z) as [Halt | Hage].
    + have Ha_lt : (Z.to_nat a < length cells)%nat by lia.
      destruct (cells !! Z.to_nat a) as [ca|] eqn:Hca; last by (apply lookup_ge_None in Hca; lia).
      have Hpa : node_loc cells a = ic_loc ca by rewrite /node_loc decide_True; [rewrite Hca | lia].
      iDestruct (own_dll_lookup_acc _ _ _ _ _ _ _ _ Hca with "Hdll") as (iva olida orida) "Hacc". iNamed "Hacc".
      rewrite Hpa. wp_apply (wp_itemPtrEqual_self (ic_loc ca) iva dq with "[$Hpkg $Hval]").
      iIntros "Hval". iApply "HΦ". iExists yt, tl. iFrame "Hparent".
      iDestruct ("Hback" with "Hval") as "Hdll". iFrame "Hdll". done.
    + have Hpa : node_loc cells a = null.
      { rewrite /node_loc. case_decide; [|done]. rewrite lookup_ge_None_2; [done | lia]. }
      rewrite Hpa. wp_apply (wp_itemPtrEqual null null None None (DfracOwn 1) (DfracOwn 1) with "[$Hpkg]").
      { rewrite /item_or_null. iSplit; done. }
      rewrite (bool_decide_eq_true_2 (oid_of None = oid_of None)); last reflexivity.
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
      pose proof (take_drop_middle cells (Z.to_nat a) ca Hca) as Hsa.
      set (pre := take (Z.to_nat a) cells) in Hsa.
      set (suf := drop (S (Z.to_nat a)) cells) in Hsa.
      iEval (rewrite -Hsa own_dll_app) in "Hdll".
      iDestruct "Hdll" as (ml mf) "[Hpre Hrest]".
      iDestruct "Hrest" as (iva olida orida)
        "(%Hloca & %Hpreva & %Hpara & %Hida & %Hcontenta & %Holida & %Horida & %Hflagsa & %Hruna & Hvala & #Hola & #Hora & Htail)".
      have Hsuf_b : suf !! (Z.to_nat b - S (Z.to_nat a))%nat = Some cb.
      { rewrite /suf lookup_drop. rewrite -Hcb. f_equal. lia. }
      iDestruct (own_dll_lookup_acc _ _ _ _ _ _ _ _ Hsuf_b with "Htail") as (ivb olidb oridb) "Hacc". iNamed "Hacc".
      have Hids_unique := yai_unique _ Harr.
      have [ya [Hya Hcra]] := cells_repr_lookup _ _ _ _ _ Hunitc Hrepr Hca.
      have [yb [Hyb Hcrb]] := cells_repr_lookup _ _ _ _ _ Hunitc Hrepr Hcb.
      have Hlt : (Z.to_nat a < Z.to_nat b)%nat by lia.
      have Hid_ne : item_id ya ≠ item_id yb
        by apply: (invariant_yjsarray_idx.ss_lookup_lt arr (Z.to_nat a) (Z.to_nat b) ya yb Hids_unique Hya Hyb Hlt).
      have Hoid_ne : oid_of (Some iva) ≠ oid_of (Some ivb).
      { rewrite /oid_of /= => Heqsome. apply Hid_ne.
        have Heqid := Some_inj _ _ Heqsome.
        rewrite -(cell_repr_head _ _ _ Hcra) -(cell_repr_head _ _ _ Hcrb) Hida Hid Heqid //. }
      rewrite Hpa Hpb.
      iDestruct (typed_pointsto_not_null with "Hval") as %Hnnb.
      wp_apply (wp_itemPtrEqual (ic_loc ca) (ic_loc cb) (Some iva) (Some ivb) dq dq with "[$Hpkg Hvala Hval]").
      { rewrite /item_or_null. iFrame "Hvala Hval". iSplit; iPureIntro.
        - rewrite -(proj1 Hloca). exact (proj2 Hloca).
        - exact Hnnb. }
      rewrite (bool_decide_eq_false_2 (oid_of (Some iva) = oid_of (Some ivb)) Hoid_ne).
      iIntros "[Ha Hb]". rewrite /item_or_null.
      iDestruct "Ha" as "[_ Hvala]". iDestruct "Hb" as "[_ Hval]".
      iDestruct ("Hback" with "Hval") as "Htail".
      iApply "HΦ". iExists yt, tl. iFrame "Hparent".
      iSplitL; last (iPureIntro; split_and!; [exact Hlen | exact Hrepr | exact Hcpar]).
      rewrite -Hsa own_dll_app. iExists ml, mf. iFrame "Hpre".
      iExists iva, olida, orida. iFrame "Hvala Hola Hora Htail".
      iPureIntro; split_and!;
        [exact (proj1 Hloca) | exact (proj2 Hloca) | exact Hpreva | exact Hpara | exact Hida | exact Hcontenta | exact Holida | exact Horida | exact Hflagsa | exact Hruna].
    + (* b = length: [b] is null, [a] a node *)
      have Ha_lt : (Z.to_nat a < length cells)%nat by lia.
      destruct (cells !! Z.to_nat a) as [ca|] eqn:Hca; last by (apply lookup_ge_None in Hca; lia).
      have Hpa : node_loc cells a = ic_loc ca by rewrite /node_loc decide_True; [rewrite Hca | lia].
      have Hpb : node_loc cells b = null.
      { rewrite /node_loc. case_decide; [|done]. rewrite lookup_ge_None_2; [done | lia]. }
      iDestruct (own_dll_lookup_acc _ _ _ _ _ _ _ _ Hca with "Hdll") as (iva olida orida) "Hacc". iNamed "Hacc".
      iDestruct (typed_pointsto_not_null with "Hval") as %Hnna.
      rewrite Hpa Hpb.
      wp_apply (wp_itemPtrEqual (ic_loc ca) null (Some iva) None dq dq with "[$Hpkg Hval]").
      { rewrite /item_or_null. iSplitL "Hval"; [iFrame "Hval"; iPureIntro; exact Hnna | done]. }
      rewrite (bool_decide_eq_false_2 (oid_of (Some iva) = oid_of None)); last done.
      iIntros "[Ha _]". rewrite /item_or_null. iDestruct "Ha" as "[_ Hval]".
      iApply "HΦ". iExists yt, tl. iFrame "Hparent".
      iDestruct ("Hback" with "Hval") as "Hdll". iFrame "Hdll". done.
Qed.

(** Loop invariant for the conflict scan in [Integrate]. The heap loop refines
    the pure set-based loop [setfii_loop] *directly*: the heap slices
    [itemsBeforeOrigin] / [conflictingItems] literally carry the [setfii_loop]
    accumulators [idsBeforeOrigin] / [conflictIds] (as [gset]s), and the loop's
    progress is tracked by a fuel equation — the remaining run from the current
    state equals the fixed overall result [loopResult]. (The
    [setfii_loop ↔ fii_loop] equivalence is a separate, already-proved fact used
    only to inherit [YjsArrInvariant].)

    - [conflict_l] (Go [conflict]) sits at the cursor node, index [leftIdx+offset]
      — the next item to scan ([other = arr !! (leftIdx + offset)]);
    - [left_l] (Go [left]) is the anchor: the node just left of the insert point,
      index [destIdx - 1] (so [item] is spliced after it);
    - [right_l] (Go [right]) is loop-constant at index [rightIdx] (the right
      origin / [Last]); the [conflict == right] break is [leftIdx+offset = rightIdx];
    - [Hloop]: from the current accumulators, the remaining
      [Z.to_nat (rightIdx - leftIdx) - offset] steps of [setfii_loop] still
      compute [loopResult]. With [Hbound] / [Hdest] this makes the Go
      [for conflict ≠ nil] test (with the [== right] break) consume exactly the
      loop's fuel.
    [own_fresh_item_raw] and the [parent.len] field are loop-constant, framed outside. *)
Definition integrate_loop_inv
    (parent : loc) (dq : dfrac) (cells : list item_cell) (arr : list (YjsItem A))
    (leftIdx rightIdx : Z) (originLeftId originRightId : option YjsId) (newItemId : YjsId)
    (loopResult : option Z)
    (conflict_l left_l right_l idsBeforeOrigin_l conflictIds_l : loc)
    (offset : nat) (idsBeforeOrigin conflictIds : gset YjsId) (destIdx : Z) : iProp Σ :=
  "Htext" ∷ own_ytype_cells parent dq cells arr ∗
  "Hconflict" ∷ conflict_l ↦ node_loc cells (leftIdx + Z.of_nat offset) ∗
  "Hleft" ∷ left_l ↦ node_loc cells (destIdx - 1) ∗
  "Hright" ∷ right_l ↦ node_loc cells rightIdx ∗
  "Hids_before" ∷ (∃ s : slice.t, "Hids_before_ref" ∷ idsBeforeOrigin_l ↦ s ∗
                     "Hids_before_set" ∷ own_id_set s (DfracOwn 1) idsBeforeOrigin) ∗
  "Hconflict_ids" ∷ (∃ s : slice.t, "Hconflict_ids_ref" ∷ conflictIds_l ↦ s ∗
                     "Hconflict_ids_set" ∷ own_id_set s (DfracOwn 1) conflictIds) ∗
  "%Hoff" ∷ ⌜(1 <= offset)%nat⌝ ∗
  "%Hdest" ∷ ⌜(leftIdx + 1 <= destIdx <= leftIdx + Z.of_nat offset)%Z⌝ ∗
  "%Hbound" ∷ ⌜(leftIdx + Z.of_nat offset <= rightIdx)%Z⌝ ∗
  "%Hloop" ∷ ⌜setfii_loop (Z.to_nat (rightIdx - leftIdx) - offset) offset leftIdx rightIdx
                 originLeftId originRightId newItemId arr idsBeforeOrigin conflictIds destIdx
               = loopResult⌝.

(* ===== the Integrate WP specification ==================================== *)

(** [own_fresh_item_raw item_l input iv oleft oright]: [item_l] is a heap [Item] whose
    id / content and origin-id cells carry the integration [input]. Its abstract
    model item is [newItem = toItem input arr] — that link is a side condition of
    the spec (a fresh item's resolved origins depend on the current document
    [arr]), so it is *not* restated here. The [left']/[right'] fields are *not*
    constrained: the scan / entry-guard never read them, and [Store.Integrate]
    has already repaired (set) them by the time it calls the scan. *)
Definition own_fresh_item_raw (item_l : loc) (input : IntegrateInput (A := A))
    (iv : yjs.item.t) (oleft oright : option yjs.id.t) : iProp Σ :=
  "Hitem" ∷ item_l ↦ iv ∗
  "Holeft" ∷ is_origin_id iv.(yjs.item.originLeftId') oleft ∗
  "Horight" ∷ is_origin_id iv.(yjs.item.originRightId') oright ∗
  "%Hin_l" ∷ ⌜(toYjsId <$> oleft) = in_originId input⌝ ∗   (* heap ids = input ids *)
  "%Hin_r" ∷ ⌜(toYjsId <$> oright) = in_rightOriginId input⌝ ∗
  "%Hid" ∷ ⌜toYjsId iv.(yjs.item.id') = in_id input⌝ ∗
  "%Hcontent" ∷ ⌜toContent iv.(yjs.item.content') = in_content input⌝.

(** [own_linked_item item_l input parent lft rgt]: the not-yet-integrated heap
    [Item] that [Store.Integrate] is about to splice in — everything about the
    caller's item is encapsulated here (its model value [iv] and origin
    pointers are existentially hidden). On top of [own_fresh_item_raw] it
    records that the item is already linked to its resolved origin neighbours
    ([left'] = [lft], [right'] = [rgt] — set by [store.repair] on the update
    path or by the local-edit creator, issue #49), carries its parent, and is
    a countable, single-char insert ([flags'] = ItemCountable, content length
    1) — exactly what [newItem] + linking produces. This is the item-side half
    of the Integrate spec. *)
Definition own_linked_item (item_l : loc) (input : IntegrateInput (A := A))
    (parent lft rgt : loc) : iProp Σ :=
  ∃ (iv : yjs.item.t) (oleft oright : option yjs.id.t),
    own_fresh_item_raw item_l input iv oleft oright ∗
    ⌜iv.(yjs.item.left') = lft⌝ ∗
    ⌜iv.(yjs.item.right') = rgt⌝ ∗
    ⌜iv.(yjs.item.parent') = parent⌝ ∗
    ⌜iv.(yjs.item.flags') = W8 2⌝ ∗
    ⌜length (iv.(yjs.item.content').(yjs.content.content')) = 1%nat⌝.

(** The algorithmic core (extracted Go function [scanConflicts]): starting at the
    cursor [node_loc cells (leftIdx + 1)] with the anchor at [node_loc cells leftIdx],
    the scan returns the resolved left anchor [node_loc cells (destIdx - 1)], where
    [destIdx] is the pure [setfindIntegratedIndex]. This is the WP refinement of the
    loop onto [setfii_loop]: the loop invariant [integrate_loop_inv] couples the heap
    loop state to a [setfii_loop] run, and each Go branch matches a [setfii_loop]
    unfold (via [wp_idOptEqual] / [wp_itemPtrEqual_node] / [wp_containsId] and the
    [cell_repr] origin facts). *)
Lemma wp_scanConflicts (parent item_l : loc) (dq : dfrac)
    (cells : list item_cell) (arr : list (YjsItem A))
    (input : IntegrateInput (A := A)) (newItem : YjsItem A)
    (iv : yjs.item.t) (oleft oright : option yjs.id.t)
    (leftIdx rightIdx : Z) (destIdx : nat) :
  YjsArrInvariant arr ->
  toItem input arr = Some newItem ->
  IsItemValid newItem ->
  maximalId newItem arr ->
  findLeftIdx (in_originId input) arr = Some leftIdx ->
  findRightIdx (in_rightOriginId input) arr = Some rightIdx ->
  setfindIntegratedIndex leftIdx rightIdx input arr = Some destIdx ->
  Forall cell_unit cells ->
  {{{ is_pkg_init yjs ∗ own_ytype_cells parent dq cells arr ∗
      own_fresh_item_raw item_l input iv oleft oright }}}
    @! yjs.scanConflicts #item_l #(node_loc cells leftIdx)
        #(node_loc cells (leftIdx + 1)) #(node_loc cells rightIdx)
  {{{ RET #(node_loc cells (Z.of_nat destIdx - 1));
      own_ytype_cells parent dq cells arr ∗ own_fresh_item_raw item_l input iv oleft oright }}}.
Proof using Type*.
  move=> Harr Htoitem Hvalid Hmax HfindL HfindR HfindD Hunitc.
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
  have Hcells_len : length cells = length arr := cells_repr_length _ _ _ Hunitc Hrepr.
  have Hrlen : (rightIdx <= Z.of_nat (length cells))%Z by rewrite Hcells_len; exact HrightUB.
  wp_auto.
  (* the two id-set accumulators start empty *)
  wp_apply wp_slice_literal. iSplitR; first done. iIntros "%ci_sl [Hci_sl Hci_cap]". wp_auto.
  wp_apply wp_slice_literal. iSplitR; first done. iIntros "%ibo_sl [Hibo_sl Hibo_cap]". wp_auto.
  (* expose the pure loop result [d] (with [Z.to_nat d = destIdx]) *)
  rewrite /setfindIntegratedIndex in HfindD.
  destruct (setfii_loop (Z.to_nat (rightIdx - leftIdx) - 1) 1 leftIdx rightIdx
              (in_originId input) (in_rightOriginId input) (in_id input) arr ∅ ∅ (leftIdx + 1))
    as [d|] eqn:Hsetfii; last by (simpl in HfindD; done).
  simpl in HfindD. injection HfindD as Hd_eq.
  (* loop invariant: offset = 1, accumulators empty, dest = leftIdx + 1 *)
  iAssert (∃ (offset : nat) (idsB conflictI : gset YjsId) (destL : Z),
    integrate_loop_inv parent dq cells arr leftIdx rightIdx input.(in_originId)
      input.(in_rightOriginId) input.(in_id) (Some d) conflict_ptr left_ptr right_ptr
      itemsBeforeOrigin_ptr conflictingItems_ptr offset idsB conflictI destL
    ∗ own_fresh_item_raw item_l input iv oleft oright)%I
    with "[Hparent Hdll conflict left right conflictingItems Hci_sl Hci_cap itemsBeforeOrigin Hibo_sl Hibo_cap Hitem Holeft Horight]" as "IH".
  { iExists 1%nat, ∅, ∅, (leftIdx + 1)%Z.
    rewrite /integrate_loop_inv /own_fresh_item_raw.
    replace (leftIdx + 1 - 1)%Z with leftIdx by lia.
    replace (leftIdx + Z.of_nat 1)%Z with (leftIdx + 1)%Z by lia.
    iFrame "conflict left right Hitem Holeft Horight".
    iSplitL "Hparent Hdll itemsBeforeOrigin Hibo_sl Hibo_cap conflictingItems Hci_sl Hci_cap".
    - iSplitL "Hparent Hdll".
      { iExists yt, tl. iFrame "Hparent Hdll". done. }
      iSplitL "itemsBeforeOrigin Hibo_sl Hibo_cap".
      { iExists _. iFrame "itemsBeforeOrigin". iExists ([] : list yjs.id.t). iFrame "Hibo_sl Hibo_cap". done. }
      iSplitL "conflictingItems Hci_sl Hci_cap".
      { iExists _. iFrame "conflictingItems". iExists ([] : list yjs.id.t). iFrame "Hci_sl Hci_cap". done. }
      iPureIntro; split_and!; [lia | lia | lia | lia | exact Hsetfii].
    - iPureIntro; split_and!; [exact Hin_l | exact Hin_r | exact Hid | exact Hcontent]. }
  wp_for "IH".
  iDestruct "IH" as "[Hinv Hfresh]". iNamed "Hinv". iNamed "Hfresh".
  iDestruct "Holeft" as "#Holeft". iDestruct "Horight" as "#Horight".
  wp_auto.
  destruct (decide (leftIdx + offset = Z.of_nat (length cells))%Z) as [Heq_len | Hne_len].
  - (* cursor reached the end: [conflict = nil], loop exits; fuel 0 pins [destL = d] *)
    have Hnull : node_loc cells (leftIdx + offset) = null.
    { rewrite /node_loc decide_True; last lia.
      rewrite Heq_len Nat2Z.id lookup_ge_None_2; [done | lia]. }
    have HdestL : destL = d.
    { have Hfuel0 : (Z.to_nat (rightIdx - leftIdx) - offset = 0)%nat by lia.
      rewrite Hfuel0 /= in Hloop. by injection Hloop. }
    rewrite Hnull bool_decide_eq_true_2; last reflexivity. simpl.
    rewrite decide_False; last done.
    wp_auto. subst destL.
    have Hdpos : (0 <= d)%Z by lia.
    replace (node_loc cells (d - 1)) with (node_loc cells (Z.of_nat destIdx - 1))
      by (f_equal; rewrite -Hd_eq Z2Nat.id //).
    rewrite decide_True; last reflexivity. wp_auto.
    iApply "HΦ". iFrame "Htext". rewrite /own_fresh_item_raw. iFrame "Hitem Holeft Horight".
    iPureIntro; split_and!; done.
  - (* cursor in range: run one scan step, matched to a [setfii_loop] unfold. *)
    have Hlt : (leftIdx + offset < Z.of_nat (length cells))%Z by lia.
    have Hi_lt : (Z.to_nat (leftIdx + offset) < length cells)%nat by lia.
    destruct (cells !! Z.to_nat (leftIdx + offset)) as [ci|] eqn:Hci;
      last by (apply lookup_ge_None in Hci; lia).
    have Hci_loc : node_loc cells (leftIdx + offset) = ic_loc ci
      by rewrite /node_loc decide_True; [rewrite Hci | lia].
    iAssert (⌜ic_loc ci ≠ null⌝ ∗ own_ytype_cells parent dq cells arr)%I with "[Htext]" as "[%Hci_nn Htext]".
    { iNamed "Htext". iDestruct (own_dll_lookup_acc _ _ _ _ _ _ _ _ Hci with "Hdll") as (ivx olidx oridx) "Hacc".
      iDestruct "Hacc" as "(_ & _ & _ & _ & _ & _ & Hcival & _ & _ & Hback)".
      iDestruct (typed_pointsto_not_null with "Hcival") as %Hnn.
      iDestruct ("Hback" with "Hcival") as "Hdll".
      iSplitR; first (iPureIntro; exact Hnn). iExists yt0, tl0. iFrame "Hparent Hdll". done. }
    have Hnnull : node_loc cells (leftIdx + offset) ≠ null by rewrite Hci_loc; exact Hci_nn.
    rewrite (bool_decide_eq_false_2 _ Hnnull). simpl. rewrite decide_True; last reflexivity.
    wp_auto.
    wp_apply (wp_itemPtrEqual_node parent dq cells arr (leftIdx + offset) rightIdx Harr Hunitc
                ltac:(lia) Hbound Hrlen with "[$Htext]").
    iIntros "Htext".
    destruct (decide (leftIdx + offset = rightIdx)) as [Heqr | Hner].
    + (* conflict = right: break; fuel 0 pins [destL = d] *)
      rewrite (bool_decide_eq_true_2 _ Heqr).
      have HdestL : destL = d.
      { have Hfuel0 : (Z.to_nat (rightIdx - leftIdx) - offset = 0)%nat by lia.
        rewrite Hfuel0 /= in Hloop. by injection Hloop. }
      wp_auto. subst destL.
      have Hdpos : (0 <= d)%Z by lia.
      replace (node_loc cells (d - 1)) with (node_loc cells (Z.of_nat destIdx - 1))
        by (f_equal; rewrite -Hd_eq Z2Nat.id //).
      wp_for_post.
      iApply "HΦ". iFrame "Htext". rewrite /own_fresh_item_raw. iFrame "Hitem Holeft Horight".
      iPureIntro; split_and!; done.
    + (* conflict ≠ right: scan one item; match the [setfii_loop] branches *)
      rewrite (bool_decide_eq_false_2 _ Hner).
      have Hir : (leftIdx + offset < rightIdx)%Z by lia.
      wp_auto.
      have [yi [Hyi Hcr_repr]] := cells_repr_lookup _ _ _ _ _ Hunitc Hrepr Hci.
      have Hcr_head := cell_repr_head _ _ _ Hcr_repr.
      iNamed "Htext".
      iDestruct (own_dll_acc _ cells _ _ (Z.to_nat (leftIdx + offset)) ci Hci with "Hdll")
        as (iv_ci olid_ci orid_ci) "(%Hcloc0 & %Hcl0 & %Hcr0 & %Hcid_ci & %Hccont_ci & %Hcolid_ci & %Hcorid_ci & %Hcflags_ci & %Hccontlen_ci & %Hcpar_ci & Hcival & #Hcol & #Hcor & Hback)".
      iEval (rewrite -Hci_loc) in "Hcival".
      wp_auto.
      iDestruct "Hids_before" as (ibo_s) "[Hibo_ref Hibo_setf]".
      iDestruct "Hibo_setf" as (vs_ibo) "(Hibo_sl & Hibo_cap & %Hibo_set)".
      iDestruct "Hconflict_ids" as (ci_s) "[Hci_ref Hci_setf]".
      iDestruct "Hci_setf" as (vs_ci) "(Hci_sl & Hci_cap & %Hci_set)".
      wp_auto.
      wp_apply wp_slice_literal. iSplitR; first done. iIntros "%sing1 [Hsing1 _]". wp_auto.
      wp_apply (wp_slice_append with "[$Hibo_sl $Hibo_cap $Hsing1]").
      iIntros "%ibo_s2 (Hibo_sl & Hibo_cap & _)". wp_auto.
      wp_apply wp_slice_literal. iSplitR; first done. iIntros "%sing2 [Hsing2 _]". wp_auto.
      wp_apply (wp_slice_append with "[$Hci_sl $Hci_cap $Hsing2]").
      iIntros "%ci_s2 (Hci_sl & Hci_cap & _)". wp_auto.
      wp_apply (wp_idOptEqual iv.(yjs.item.originLeftId') iv_ci.(yjs.item.originLeftId')
                  oleft olid_ci with "[$Holeft $Hcol]").
      remember ((Z.to_nat (rightIdx - leftIdx) - offset)%nat) as fuel eqn:Hfuel_eq.
      destruct fuel as [|count']; first (exfalso; lia).
      cbn [setfii_loop] in Hloop. rewrite Hyi /= in Hloop.
      have HcId : item_id yi = toYjsId iv_ci.(yjs.item.id') by rewrite -Hcr_head; exact Hcid_ci.
      have HoL : origin_id (origin yi) = toYjsId <$> olid_ci by rewrite -Hcr_head; exact Hcolid_ci.
      have HoR : origin_id (rightOrigin yi) = toYjsId <$> orid_ci by rewrite -Hcr_head; exact Hcorid_ci.
      case_bool_decide as Hoeq.
      * (* same left origin as the new item *)
        have HoeqL : origin_id (origin yi) = input.(in_originId) by rewrite HoL -Hoeq Hin_l.
        rewrite (decide_True _ _ HoeqL) in Hloop.
        wp_auto.
        case_bool_decide as Hclt.
        -- (* smaller client id: advance the anchor (left := conflict) *)
           have HcltL : ((item_id yi).(clientId) < input.(in_id).(clientId))%nat
             by (rewrite HcId -Hid /toYjsId /=; word).
           rewrite (decide_True _ _ HcltL) in Hloop.
           wp_auto.
           wp_apply wp_slice_literal. iSplitR; first done.
           iIntros "%ci_empty [Hci_empty Hci_empty_cap]". wp_auto.
           wp_for_post.
           iEval (rewrite Hci_loc) in "Hcival".
           iDestruct ("Hback" with "Hcival") as "Hdll".
           iFrame "HΦ item".
           iExists (S offset), ({[item_id yi]} ∪ idsB), ∅, (leftIdx + Z.of_nat offset + 1)%Z.
           rewrite /integrate_loop_inv /own_fresh_item_raw.
           iSplitL "Hparent Hdll Hconflict Hleft Hright Hibo_ref Hibo_sl Hibo_cap Hci_ref Hci_empty Hci_empty_cap"; last first.
           { iFrame "Hitem Holeft Horight".
             iPureIntro; split_and!; [exact Hin_l0|exact Hin_r0|exact Hid0|exact Hcontent0]. }
           iSplitL "Hparent Hdll". { iExists yt0, tl0. iFrame "Hparent Hdll". done. }
           iSplitL "Hconflict".
           { rewrite Hcr0. replace (leftIdx + Z.of_nat (S offset))%Z with (Z.to_nat (leftIdx + offset) + 1)%Z by lia. iFrame "Hconflict". }
           iSplitL "Hleft".
           { replace (leftIdx + Z.of_nat offset + 1 - 1)%Z with (leftIdx + offset)%Z by lia. iFrame "Hleft". }
           iSplitL "Hright". { iFrame "Hright". }
           iSplitL "Hibo_ref Hibo_sl Hibo_cap".
           { iExists ibo_s2. iFrame "Hibo_ref". iExists _. iFrame "Hibo_sl Hibo_cap". iPureIntro.
             have H0 : sint.nat (W64 0) = 0%nat by word.
             rewrite H0 fmap_app list_to_set_app_L Hibo_set; cbn [insert list_insert fmap list_fmap list_to_set]; rewrite -HcId; apply gset_union_singleton_swap. }
           iSplitL "Hci_ref Hci_empty Hci_empty_cap".
           { iExists _. iFrame "Hci_ref". iExists ([] : list yjs.id.t). iFrame "Hci_empty Hci_empty_cap". done. }
           iPureIntro; split_and!;
             [lia | lia | lia | lia
             | replace (Z.to_nat (rightIdx - leftIdx) - S offset)%nat with count' by lia;
               replace (leftIdx + Z.of_nat offset + 1)%Z with (Z.of_nat (Z.to_nat (leftIdx + offset) + 1)) by lia;
               exact Hloop].
        -- (* larger-or-equal client id: same right origin -> break, else keep scanning *)
           have HcltGe : ¬ ((item_id yi).(clientId) < input.(in_id).(clientId))%nat
             by (rewrite HcId -Hid /toYjsId /=; word).
           rewrite (decide_False _ _ HcltGe) in Hloop.
           wp_auto.
           wp_apply (wp_idOptEqual iv.(yjs.item.originRightId') iv_ci.(yjs.item.originRightId')
                       oright orid_ci with "[$Horight $Hcor]").
           case_bool_decide as HoeqR.
           ++ (* same right origin: integration points coincide -> break *)
              have HoeqRR : origin_id (rightOrigin yi) = input.(in_rightOriginId)
                by rewrite HoR -HoeqR Hin_r.
              rewrite (decide_True _ _ HoeqRR) in Hloop.
              injection Hloop as HdestL.
              wp_auto. subst destL.
              iEval (rewrite Hci_loc) in "Hcival". iDestruct ("Hback" with "Hcival") as "Hdll".
              wp_for_post.
              have Hdpos : (0 <= d)%Z by lia.
              replace (node_loc cells (d - 1)) with (node_loc cells (Z.of_nat destIdx - 1))
                by (f_equal; rewrite -Hd_eq Z2Nat.id //).
              iApply "HΦ". iSplitL "Hparent Hdll". { iExists yt0, tl0. iFrame "Hparent Hdll". done. }
              rewrite /own_fresh_item_raw. iFrame "Hitem Holeft Horight". iPureIntro; split_and!; done.
           ++ (* different right origin: keep scanning, anchor unchanged *)
              have HneqRR : origin_id (rightOrigin yi) ≠ input.(in_rightOriginId).
              { rewrite HoR -Hin_r; move=> Heq; apply HoeqR; by rewrite Heq. }
              rewrite (decide_False _ _ HneqRR) in Hloop.
              wp_auto.
              wp_for_post.
              iEval (rewrite Hci_loc) in "Hcival". iDestruct ("Hback" with "Hcival") as "Hdll".
              iFrame "HΦ item".
              iExists (S offset), ({[item_id yi]} ∪ idsB), ({[item_id yi]} ∪ conflictI), destL.
              rewrite /integrate_loop_inv /own_fresh_item_raw.
              iSplitL "Hparent Hdll Hconflict Hleft Hright Hibo_ref Hibo_sl Hibo_cap Hci_ref Hci_sl Hci_cap"; last first.
              { iFrame "Hitem Holeft Horight".
                iPureIntro; split_and!; [exact Hin_l0|exact Hin_r0|exact Hid0|exact Hcontent0]. }
              iSplitL "Hparent Hdll". { iExists yt0, tl0. iFrame "Hparent Hdll". done. }
              iSplitL "Hconflict".
              { rewrite Hcr0. replace (leftIdx + Z.of_nat (S offset))%Z with (Z.to_nat (leftIdx + offset) + 1)%Z by lia. iFrame "Hconflict". }
              iSplitL "Hleft". { iFrame "Hleft". }
              iSplitL "Hright". { iFrame "Hright". }
              iSplitL "Hibo_ref Hibo_sl Hibo_cap".
              { iExists ibo_s2. iFrame "Hibo_ref". iExists _. iFrame "Hibo_sl Hibo_cap". iPureIntro.
                have H0 : sint.nat (W64 0) = 0%nat by word.
                rewrite H0 fmap_app list_to_set_app_L Hibo_set; cbn [insert list_insert fmap list_fmap list_to_set]; rewrite -HcId; apply gset_union_singleton_swap. }
              iSplitL "Hci_ref Hci_sl Hci_cap".
              { iExists ci_s2. iFrame "Hci_ref". iExists _. iFrame "Hci_sl Hci_cap". iPureIntro.
                have H0 : sint.nat (W64 0) = 0%nat by word.
                rewrite H0 fmap_app list_to_set_app_L Hci_set; cbn [insert list_insert fmap list_fmap list_to_set]; rewrite -HcId; apply gset_union_singleton_swap. }
              iPureIntro; split_and!;
                [lia | lia | lia | lia
                | replace (Z.to_nat (rightIdx - leftIdx) - S offset)%nat with count' by lia; exact Hloop].
      * (* different left origin from the new item *)
        have HoLne : origin_id (origin yi) ≠ input.(in_originId)
          by (rewrite HoL -Hin_l; move=> Heq; apply Hoeq; by rewrite Heq).
        rewrite (decide_False _ _ HoLne) in Hloop.
        rewrite HoL in Hloop.
        destruct olid_ci as [idv|] eqn:Hcoleft; last first.
        -- (* conflict has no left origin: origins would cross -> break *)
           iDestruct "Hcol" as "%Hcol_null".
           simpl in Hloop. injection Hloop as HdestL.
           wp_auto. rewrite Hcol_null. wp_auto. subst destL.
           iEval (rewrite Hci_loc) in "Hcival". iDestruct ("Hback" with "Hcival") as "Hdll".
           wp_for_post.
           have Hdpos : (0 <= d)%Z by lia.
           replace (node_loc cells (d - 1)) with (node_loc cells (Z.of_nat destIdx - 1))
             by (f_equal; rewrite -Hd_eq Z2Nat.id //).
           iApply "HΦ". iSplitL "Hparent Hdll". { iExists yt0, tl0. iFrame "Hparent Hdll". done. }
           rewrite /own_fresh_item_raw. iFrame "Hitem Holeft Horight". iPureIntro; split_and!; done.
        -- (* conflict has a left origin [idv] (different from the new item's) *)
           iDestruct "Hcol" as "[%Hcol_nn #Hcol_pt]".
           simpl in Hloop.
           wp_auto. rewrite bool_decide_eq_false_2; last exact Hcol_nn. wp_auto.
           wp_apply (wp_containsId with "[$Hibo_sl]"). iIntros "Hibo_sl".
           have H0 : sint.nat (W64 0) = 0%nat by word.
           rewrite H0 fmap_app list_to_set_app_L Hibo_set.
           cbn [insert list_insert fmap list_fmap list_to_set]. rewrite -HcId.
           destruct (decide (toYjsId idv ∈ ({[item_id yi]} ∪ idsB : gset YjsId))) as [Hin_ibo | Hnin_ibo].
           ++ (* conflict's left origin was already scanned (case 2) *)
              have Hmem_ibo := gset_elem_union_singleton_swap idsB (item_id yi) (toYjsId idv) Hin_ibo.
              rewrite (bool_decide_eq_true_2 _ Hmem_ibo).
              (* the [destruct (decide ... ∈ idsB)] above already reduced Hloop's
                 outer guard (it shares the Decision instance), so Hloop is now the
                 inner [if decide (... ∉ conflictI)]. *)
              wp_auto.
              wp_apply (wp_containsId with "[$Hci_sl]"). iIntros "Hci_sl".
              rewrite fmap_app list_to_set_app_L Hci_set.
              cbn [insert list_insert fmap list_fmap list_to_set]. rewrite -HcId.
              destruct (decide (toYjsId idv ∈ ({[item_id yi]} ∪ conflictI : gset YjsId))) as [Hin_ci | Hnin_ci].
              ** (* already in conflictingItems: no anchor move, keep scanning (continue) *)
                 have Hmem_ci := gset_elem_union_singleton_swap conflictI (item_id yi) (toYjsId idv) Hin_ci.
                 rewrite (bool_decide_eq_true_2 _ Hmem_ci).
                 have Hnn : ¬ (toYjsId idv ∉ ({[item_id yi]} ∪ conflictI : gset YjsId))
                   by (move=> Hcontra; exact (Hcontra Hin_ci)).
                 rewrite (decide_False _ _ Hnn) in Hloop.
                 wp_auto.
                 wp_for_post.
                 iEval (rewrite Hci_loc) in "Hcival". iDestruct ("Hback" with "Hcival") as "Hdll".
                 iFrame "HΦ item".
                 iExists (S offset), ({[item_id yi]} ∪ idsB), ({[item_id yi]} ∪ conflictI), destL.
                 rewrite /integrate_loop_inv /own_fresh_item_raw.
                 iSplitL "Hparent Hdll Hconflict Hleft Hright Hibo_ref Hibo_sl Hibo_cap Hci_ref Hci_sl Hci_cap"; last first.
                 { iFrame "Hitem Holeft Horight".
                   iPureIntro; split_and!; [exact Hin_l0|exact Hin_r0|exact Hid0|exact Hcontent0]. }
                 iSplitL "Hparent Hdll". { iExists yt0, tl0. iFrame "Hparent Hdll". done. }
                 iSplitL "Hconflict".
                 { rewrite Hcr0. replace (leftIdx + Z.of_nat (S offset))%Z with (Z.to_nat (leftIdx + offset) + 1)%Z by lia. iFrame "Hconflict". }
                 iSplitL "Hleft". { iFrame "Hleft". }
                 iSplitL "Hright". { iFrame "Hright". }
                 iSplitL "Hibo_ref Hibo_sl Hibo_cap".
                 { iExists ibo_s2. iFrame "Hibo_ref". iExists _. iFrame "Hibo_sl Hibo_cap". iPureIntro.
                   rewrite fmap_app list_to_set_app_L Hibo_set; cbn [insert list_insert fmap list_fmap list_to_set]; rewrite -HcId; apply gset_union_singleton_swap. }
                 iSplitL "Hci_ref Hci_sl Hci_cap".
                 { iExists ci_s2. iFrame "Hci_ref". iExists _. iFrame "Hci_sl Hci_cap". iPureIntro.
                   rewrite fmap_app list_to_set_app_L Hci_set; cbn [insert list_insert fmap list_fmap list_to_set]; rewrite -HcId; apply gset_union_singleton_swap. }
                 iPureIntro; split_and!;
                   [lia | lia | lia | lia
                   | replace (Z.to_nat (rightIdx - leftIdx) - S offset)%nat with count' by lia; exact Hloop].
              ** (* not yet in conflictingItems: advance the anchor (left := conflict) *)
                 have Hmem_ci_neg := gset_not_elem_union_singleton_swap conflictI (item_id yi) (toYjsId idv) Hnin_ci.
                 rewrite (bool_decide_eq_false_2 _ Hmem_ci_neg).
                 rewrite (decide_True _ _ Hnin_ci) in Hloop.
                 wp_auto.
                 wp_apply wp_slice_literal. iSplitR; first done.
                 iIntros "%ci_empty [Hci_empty Hci_empty_cap]". wp_auto.
                 wp_for_post.
                 iEval (rewrite Hci_loc) in "Hcival". iDestruct ("Hback" with "Hcival") as "Hdll".
                 iFrame "HΦ item".
                 iExists (S offset), ({[item_id yi]} ∪ idsB), ∅, (leftIdx + Z.of_nat offset + 1)%Z.
                 rewrite /integrate_loop_inv /own_fresh_item_raw.
                 iSplitL "Hparent Hdll Hconflict Hleft Hright Hibo_ref Hibo_sl Hibo_cap Hci_ref Hci_empty Hci_empty_cap"; last first.
                 { iFrame "Hitem Holeft Horight".
                   iPureIntro; split_and!; [exact Hin_l0|exact Hin_r0|exact Hid0|exact Hcontent0]. }
                 iSplitL "Hparent Hdll". { iExists yt0, tl0. iFrame "Hparent Hdll". done. }
                 iSplitL "Hconflict".
                 { rewrite Hcr0. replace (leftIdx + Z.of_nat (S offset))%Z with (Z.to_nat (leftIdx + offset) + 1)%Z by lia. iFrame "Hconflict". }
                 iSplitL "Hleft".
                 { replace (leftIdx + Z.of_nat offset + 1 - 1)%Z with (leftIdx + offset)%Z by lia. iFrame "Hleft". }
                 iSplitL "Hright". { iFrame "Hright". }
                 iSplitL "Hibo_ref Hibo_sl Hibo_cap".
                 { iExists ibo_s2. iFrame "Hibo_ref". iExists _. iFrame "Hibo_sl Hibo_cap". iPureIntro.
                   rewrite fmap_app list_to_set_app_L Hibo_set; cbn [insert list_insert fmap list_fmap list_to_set]; rewrite -HcId; apply gset_union_singleton_swap. }
                 iSplitL "Hci_ref Hci_empty Hci_empty_cap".
                 { iExists _. iFrame "Hci_ref". iExists ([] : list yjs.id.t). iFrame "Hci_empty Hci_empty_cap". done. }
                 iPureIntro; split_and!;
                   [lia | lia | lia | lia
                   | replace (Z.to_nat (rightIdx - leftIdx) - S offset)%nat with count' by lia;
                     replace (leftIdx + Z.of_nat offset + 1)%Z with (Z.of_nat (Z.to_nat (leftIdx + offset) + 1)) by lia;
                     exact Hloop].
           ++ (* conflict's left origin is before this run: origins cross -> break *)
              have Hmem_ibo_neg := gset_not_elem_union_singleton_swap idsB (item_id yi) (toYjsId idv) Hnin_ibo.
              rewrite (bool_decide_eq_false_2 _ Hmem_ibo_neg).
              (* the [destruct] already reduced Hloop's guard to its else branch. *)
              injection Hloop as HdestL.
              wp_auto. subst destL.
              iEval (rewrite Hci_loc) in "Hcival". iDestruct ("Hback" with "Hcival") as "Hdll".
              wp_for_post.
              have Hdpos : (0 <= d)%Z by lia.
              replace (node_loc cells (d - 1)) with (node_loc cells (Z.of_nat destIdx - 1))
                by (f_equal; rewrite -Hd_eq Z2Nat.id //).
              iApply "HΦ". iSplitL "Hparent Hdll". { iExists yt0, tl0. iFrame "Hparent Hdll". done. }
              rewrite /own_fresh_item_raw. iFrame "Hitem Holeft Horight". iPureIntro; split_and!; done.
Qed.

(** The conflict scan with its entry guard: resolves whether to scan at all
    (y-octo's left/right-connection check), sets the initial cursor, and delegates
    to [scanConflicts]. When the guard is false the anchors are adjacent
    ([leftIdx + 1 = rightIdx]) so [destIdx = leftIdx + 1] and the unchanged [left]
    already equals [node_loc cells (destIdx - 1)]. *)
Lemma wp_findIntegrationLeft (parent item_l left_loc right_loc : loc) (dq : dfrac)
    (cells : list item_cell) (arr : list (YjsItem A))
    (input : IntegrateInput (A := A)) (newItem : YjsItem A)
    (iv : yjs.item.t) (oleft oright : option yjs.id.t)
    (leftIdx rightIdx : Z) (destIdx : nat) :
  YjsArrInvariant arr ->
  toItem input arr = Some newItem ->
  IsItemValid newItem ->
  maximalId newItem arr ->
  findLeftIdx (in_originId input) arr = Some leftIdx ->
  findRightIdx (in_rightOriginId input) arr = Some rightIdx ->
  setfindIntegratedIndex leftIdx rightIdx input arr = Some destIdx ->
  left_loc = node_loc cells leftIdx ->
  right_loc = node_loc cells rightIdx ->
  Forall cell_unit cells ->
  {{{ is_pkg_init yjs ∗ own_ytype_cells parent dq cells arr ∗
      own_fresh_item_raw item_l input iv oleft oright }}}
    @! yjs.findIntegrationLeft #parent #item_l #left_loc #right_loc
  {{{ RET #(node_loc cells (Z.of_nat destIdx - 1));
      own_ytype_cells parent dq cells arr ∗ own_fresh_item_raw item_l input iv oleft oright }}}.
Proof using Type*.
  move=> Harr Htoitem Hvalid Hmax HfindL HfindR HfindD Hll Hrl Hunitc.
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
  have Hcells_len : length cells = length arr := cells_repr_length _ _ _ Hunitc Hrepr.
  have Hrlen : (rightIdx <= Z.of_nat (length cells))%Z by rewrite Hcells_len; exact HrUB.
  (* Entry guard: read the left/right neighbour connections to decide whether the
     conflict scan runs. The guard is false exactly when [leftIdx + 1 = rightIdx]
     (so [destIdx = leftIdx + 1] and the unchanged anchor is the answer); otherwise
     [scanConflicts] resolves the anchor. Four boundary combos: left/right null? *)
  destruct (decide (rightIdx = Z.of_nat (length cells))) as [HrN | HrNN].
  { (* right is null: rightIsNullOrHasLeft = true (no read of right.left) *)
    have Hrnull : right_loc = null.
    { rewrite Hrl HrN /node_loc decide_True; last lia. rewrite Nat2Z.id lookup_ge_None_2; [done | lia]. }
    rewrite (bool_decide_eq_true_2 (right_loc = null) Hrnull). wp_auto.
    destruct (decide (leftIdx = -1)) as [Hl0 | HlP].
    { (* combo 1: left null -> scan from parent.start *)
      have Hlnull : left_loc = null.
      { rewrite Hll Hl0 /node_loc. case_decide; [lia | done]. }
      rewrite Hlnull. wp_auto.
      iAssert (⌜yt.(yjs.yType.start') = node_loc cells 0⌝ ∗ own_dll dq yt.(yjs.yType.start') tl null null cells)%I with "[Hdll]" as "[%Hstart Hdll]".
      { destruct cells as [|c rest].
        { iDestruct "Hdll" as %[Hl Hlst]. iSplit; iPureIntro; [rewrite Hl /node_loc // | split; [exact Hl | exact Hlst]]. }
        iDestruct "Hdll" as (ivh olidh oridh) "(%Hloch & %Hprevh & %Hparh & %Hidh & %Hconth & %Holidh & %Horidh & %Hflagsh & %Hrunh & Hvalh & #Holefth & #Horighth & Hresth)".
        iSplitR.
        { iPureIntro. rewrite /node_loc /=. by destruct Hloch as [-> _]. }
        iExists ivh, olidh, oridh. iFrame "Hvalh Holefth Horighth Hresth".
        iPureIntro; split_and!; [exact (proj1 Hloch) | exact (proj2 Hloch) | exact Hprevh | exact Hparh | exact Hidh | exact Hconth | exact Holidh | exact Horidh | exact Hflagsh | exact Hrunh]. }
      replace (# null) with (# (node_loc cells leftIdx)) by (rewrite -Hll Hlnull //).
      replace (yt.(yjs.yType.start')) with (node_loc cells (leftIdx + 1)) by (rewrite Hstart Hl0; f_equal; lia).
      rewrite Hrl.
      wp_apply (wp_scanConflicts parent item_l dq cells arr input newItem iv oleft oright leftIdx rightIdx destIdx
                  Harr Htoitem Hvalid Hmax HfindL HfindR HfindD Hunitc with "[Hparent Hdll Hitem Holeft Horight]").
      { iSplitL "Hparent Hdll".
        { iExists yt, tl. iFrame "Hparent".
          replace (yt.(yjs.yType.start')) with (node_loc cells (leftIdx + 1)) by (rewrite Hstart Hl0; f_equal; lia).
          iFrame "Hdll". done. }
        rewrite /own_fresh_item_raw. iFrame "Hitem Holeft Horight". iPureIntro; split_and!; done. }
      iIntros "[Htext Hfresh]". wp_auto. iApply "HΦ". iFrame "Htext Hfresh". }
    { (* combo 3: left non-null, right null -> compare left.right with right *)
      have HlP' : (0 <= leftIdx)%Z by lia.
      have Hi_lt : (Z.to_nat leftIdx < length cells)%nat by lia.
      destruct (cells !! Z.to_nat leftIdx) as [cl|] eqn:Hcl_lookup; last by (apply lookup_ge_None in Hcl_lookup; lia).
      have Hcl_loc : node_loc cells leftIdx = ic_loc cl.
      { rewrite /node_loc decide_True; last lia. rewrite Hcl_lookup //. }
      iAssert (⌜ic_loc cl ≠ null⌝ ∗ own_dll dq yt.(yjs.yType.start') tl null null cells)%I with "[Hdll]" as "[%Hclnn Hdll]".
      { iDestruct (own_dll_lookup_acc _ _ _ _ _ _ _ _ Hcl_lookup with "Hdll") as (ivx olidx oridx) "Hacc".
        iDestruct "Hacc" as "(_&_&_&_&_&_&Hclval&_&_&Hbk)".
        iDestruct (typed_pointsto_not_null with "Hclval") as %Hnn.
        iDestruct ("Hbk" with "Hclval") as "Hdll". iSplitR; [done | iFrame "Hdll"]. }
      have Hlnn : left_loc ≠ null by rewrite Hll Hcl_loc; exact Hclnn.
      rewrite (bool_decide_eq_false_2 (left_loc = null) Hlnn).
      iDestruct (own_dll_acc _ cells _ _ (Z.to_nat leftIdx) cl Hcl_lookup with "Hdll")
        as (ivl olidl oridl) "(%Hcloc & %Hcl_l & %Hcr_l & %Hidl & %Hcontl & %Holidl & %Horidl & %Hflagsl & %Hrunl & %Hparl & Hcval & #Hcol_l & #Hcor_l & Hback)".
      iEval (rewrite -Hcl_loc) in "Hcval". iEval (rewrite Hll) in "left". wp_auto.
      have Hcr_l' : ivl.(yjs.item.right') = node_loc cells (leftIdx + 1).
      { rewrite Hcr_l. f_equal. rewrite Z2Nat.id; lia. }
      rewrite Hcr_l' Hrl.
      iEval (rewrite Hcl_loc) in "Hcval". iDestruct ("Hback" with "Hcval") as "Hdll".
      iAssert (own_ytype_cells parent dq cells arr) with "[Hparent Hdll]" as "Htext".
      { iExists yt, tl. iFrame "Hparent Hdll". done. }
      wp_apply (wp_itemPtrEqual_node parent dq cells arr (leftIdx + 1) rightIdx Harr Hunitc ltac:(lia) ltac:(lia) Hrlen with "[$Htext]").
      iIntros "Htext".
      destruct (decide (leftIdx + 1 = rightIdx)) as [Hadj | Hnadj].
      { (* no scan: leftIdx+1 = rightIdx -> destIdx = leftIdx+1 *)
        rewrite (bool_decide_eq_true_2 _ Hadj). wp_auto.
        rewrite (bool_decide_eq_false_2 (node_loc cells leftIdx = null) ltac:(rewrite -Hll; exact Hlnn)). wp_auto.
        have Hdestadj : Z.of_nat destIdx = leftIdx + 1.
        { rewrite /setfindIntegratedIndex in HfindD.
          replace (Z.to_nat (rightIdx - leftIdx) - 1)%nat with 0%nat in HfindD by lia.
          simpl in HfindD. injection HfindD as HfindD'. rewrite -HfindD' Z2Nat.id; lia. }
        replace (node_loc cells (Z.of_nat destIdx - 1)) with (node_loc cells leftIdx) by (f_equal; lia).
        iApply "HΦ". iFrame "Htext". rewrite /own_fresh_item_raw. iFrame "Hitem Holeft Horight". iPureIntro; split_and!; done. }
      { (* scan: leftIdx+1 < rightIdx, conflict = left.right *)
        rewrite (bool_decide_eq_false_2 _ Hnadj). wp_auto.
        have Hlnn' : node_loc cells leftIdx ≠ null by (rewrite -Hll; exact Hlnn).
        rewrite (bool_decide_eq_false_2 (node_loc cells leftIdx = null) Hlnn'). wp_auto.
        rewrite (bool_decide_eq_false_2 (node_loc cells leftIdx = null) Hlnn').
        iDestruct "Htext" as (yt' tl') "(Hparent & Hdll & %Hlen' & %Hrepr' & %Hcpar')".
        iDestruct (own_dll_acc _ cells _ _ (Z.to_nat leftIdx) cl Hcl_lookup with "Hdll") as (ivl2 olidl2 oridl2) "(%Hcloc2 & %Hcl_l2 & %Hcr_l2 & %Hidl2 & %Hcontl2 & %Holidl2 & %Horidl2 & %Hflagsl2 & %Hrunl2 & %Hparl2 & Hcval & #Hcol2 & #Hcor2 & Hback)".
        have Hcr_l2' : ivl2.(yjs.item.right') = node_loc cells (leftIdx + 1) by (rewrite Hcr_l2; f_equal; rewrite Z2Nat.id; lia).
        iEval (rewrite -Hcl_loc) in "Hcval". wp_auto. rewrite Hcr_l2'.
        iEval (rewrite Hcl_loc) in "Hcval". iDestruct ("Hback" with "Hcval") as "Hdll".
        iAssert (own_ytype_cells parent dq cells arr) with "[Hparent Hdll]" as "Htext".
        { iExists yt', tl'. iFrame "Hparent Hdll". iPureIntro; split_and!; [exact Hlen' | exact Hrepr' | exact Hcpar']. }
        wp_apply (wp_scanConflicts parent item_l dq cells arr input newItem iv oleft oright leftIdx rightIdx destIdx
                    Harr Htoitem Hvalid Hmax HfindL HfindR HfindD Hunitc with "[Htext Hitem Holeft Horight]").
        { iSplitL "Htext"; [iFrame "Htext" | rewrite /own_fresh_item_raw; iFrame "Hitem Holeft Horight"; iPureIntro; split_and!; done]. }
        iIntros "[Htext Hfresh]". wp_auto. iApply "HΦ". iFrame "Htext Hfresh". } } }
  { (* right non-null (rightIdx < length cells): read right.left *)
    have Hr_lt : (Z.to_nat rightIdx < length cells)%nat by lia.
    destruct (cells !! Z.to_nat rightIdx) as [cr|] eqn:Hcr_lookup; last by (apply lookup_ge_None in Hcr_lookup; lia).
    have Hcr_loc : node_loc cells rightIdx = ic_loc cr.
    { rewrite /node_loc decide_True; last lia. rewrite Hcr_lookup //. }
    iAssert (⌜ic_loc cr ≠ null⌝ ∗ own_dll dq yt.(yjs.yType.start') tl null null cells)%I with "[Hdll]" as "[%Hcrnn Hdll]".
    { iDestruct (own_dll_lookup_acc _ _ _ _ _ _ _ _ Hcr_lookup with "Hdll") as (ivx olidx oridx) "Hacc".
      iDestruct "Hacc" as "(_&_&_&_&_&_&Hcrval&_&_&Hbk)".
      iDestruct (typed_pointsto_not_null with "Hcrval") as %Hnn.
      iDestruct ("Hbk" with "Hcrval") as "Hdll". iSplitR; [done | iFrame "Hdll"]. }
    have Hrnn : right_loc ≠ null by rewrite Hrl Hcr_loc; exact Hcrnn.
    rewrite (bool_decide_eq_false_2 (right_loc = null) Hrnn).
    iDestruct (own_dll_acc _ cells _ _ (Z.to_nat rightIdx) cr Hcr_lookup with "Hdll") as (ivr olidr oridr) "(%Hcloc_r & %Hcl_r & %Hcr_r & %Hidr & %Hcontr & %Holidr & %Horidr & %Hflagsr & %Hrunr & %Hparr & Hcrval & #Hcol_r & #Hcor_r & Hback)".
    iEval (rewrite -Hcr_loc) in "Hcrval". iEval (rewrite Hrl) in "right". wp_auto.
    iEval (rewrite Hcr_loc) in "Hcrval". iDestruct ("Hback" with "Hcrval") as "Hdll".
    destruct (decide (leftIdx = -1)) as [Hl0 | HlP].
    { (* combo 2: left null; guard = rightIsNullOrHasLeft = (rightIdx != 0) *)
      have Hlnull : left_loc = null by (rewrite Hll Hl0 /node_loc; case_decide; [lia | done]).
      rewrite Hlnull.
      destruct (decide (rightIdx = 0)) as [Hr0 | HrP].
      { (* rightIdx = 0: no scan *)
        have Hcrl_null : ivr.(yjs.item.left') = null by (rewrite Hcl_r /node_loc; case_decide; [lia | done]).
        rewrite Hcrl_null. wp_auto.
        have Hdest0 : destIdx = 0%nat.
        { rewrite /setfindIntegratedIndex in HfindD.
          replace (Z.to_nat (rightIdx - leftIdx) - 1)%nat with 0%nat in HfindD by lia.
          simpl in HfindD. injection HfindD as HfindD'. lia. }
        replace (# null) with (# (node_loc cells (Z.of_nat destIdx - 1))).
        { iApply "HΦ". iSplitR "Hitem Holeft Horight".
          { iExists yt, tl. iFrame "Hparent Hdll". done. }
          rewrite /own_fresh_item_raw. iFrame "Hitem Holeft Horight". iPureIntro; split_and!; done. }
        f_equal. rewrite Hdest0 /node_loc /=. done. }
      { (* rightIdx >= 1: scan from parent.start *)
        have Hcrl_eq : ivr.(yjs.item.left') = node_loc cells (rightIdx - 1) by (rewrite Hcl_r; f_equal; rewrite Z2Nat.id; lia).
        have Hr1_lt : (Z.to_nat (rightIdx - 1) < length cells)%nat by lia.
        destruct (cells !! Z.to_nat (rightIdx - 1)) as [crl|] eqn:Hcrl_lookup; last by (apply lookup_ge_None in Hcrl_lookup; lia).
        have Hcrl_loc : node_loc cells (rightIdx - 1) = ic_loc crl by (rewrite /node_loc decide_True; [rewrite Hcrl_lookup // | lia]).
        iAssert (⌜ic_loc crl ≠ null⌝ ∗ own_dll dq yt.(yjs.yType.start') tl null null cells)%I with "[Hdll]" as "[%Hcrlnn Hdll]".
        { iDestruct (own_dll_lookup_acc _ _ _ _ _ _ _ _ Hcrl_lookup with "Hdll") as (ivx olidx oridx) "Hacc".
          iDestruct "Hacc" as "(_&_&_&_&_&_&Hv&_&_&Hb)".
          iDestruct (typed_pointsto_not_null with "Hv") as %Hnn2.
          iDestruct ("Hb" with "Hv") as "Hdll". iSplitR; [done | iFrame "Hdll"]. }
        have Hcrl_nn : ivr.(yjs.item.left') ≠ null by rewrite Hcrl_eq Hcrl_loc; exact Hcrlnn.
        rewrite (bool_decide_eq_false_2 (ivr.(yjs.item.left') = null) Hcrl_nn). wp_auto.
        iAssert (⌜yt.(yjs.yType.start') = node_loc cells 0⌝ ∗ own_dll dq yt.(yjs.yType.start') tl null null cells)%I with "[Hdll]" as "[%Hstart Hdll]".
        { destruct cells as [|c rest].
          { iDestruct "Hdll" as %[Hl Hlst]. iSplit; iPureIntro; [rewrite Hl /node_loc // | split; [exact Hl | exact Hlst]]. }
          iDestruct "Hdll" as (ivh olidh oridh) "(%Hloch & %Hprevh & %Hparh & %Hidh & %Hconth & %Holidh & %Horidh & %Hflagsh & %Hrunh & Hvalh & #Holefth & #Horighth & Hresth)".
          iSplitR.
          { iPureIntro. rewrite /node_loc /=. by destruct Hloch as [-> _]. }
          iExists ivh, olidh, oridh. iFrame "Hvalh Holefth Horighth Hresth".
          iPureIntro; split_and!; [exact (proj1 Hloch) | exact (proj2 Hloch) | exact Hprevh | exact Hparh | exact Hidh | exact Hconth | exact Holidh | exact Horidh | exact Hflagsh | exact Hrunh]. }
        replace (# null) with (# (node_loc cells leftIdx)) by (rewrite -Hll Hlnull //).
        replace (yt.(yjs.yType.start')) with (node_loc cells (leftIdx + 1)) by (rewrite Hstart Hl0; f_equal; lia).
        wp_apply (wp_scanConflicts parent item_l dq cells arr input newItem iv oleft oright leftIdx rightIdx destIdx
                    Harr Htoitem Hvalid Hmax HfindL HfindR HfindD Hunitc with "[Hparent Hdll Hitem Holeft Horight]").
        { iSplitL "Hparent Hdll".
          { iExists yt, tl. iFrame "Hparent".
            replace (yt.(yjs.yType.start')) with (node_loc cells (leftIdx + 1)) by (rewrite Hstart Hl0; f_equal; lia).
            iFrame "Hdll". done. }
          rewrite /own_fresh_item_raw. iFrame "Hitem Holeft Horight". iPureIntro; split_and!; done. }
        iIntros "[Htext Hfresh]". wp_auto. iApply "HΦ". iFrame "Htext Hfresh". } }
    { (* combo 4: left non-null, right non-null -> compare left.right with right *)
      have HlP' : (0 <= leftIdx)%Z by lia.
      have Hi_lt : (Z.to_nat leftIdx < length cells)%nat by lia.
      destruct (cells !! Z.to_nat leftIdx) as [cl|] eqn:Hcl_lookup; last by (apply lookup_ge_None in Hcl_lookup; lia).
      have Hcl_loc : node_loc cells leftIdx = ic_loc cl.
      { rewrite /node_loc decide_True; last lia. rewrite Hcl_lookup //. }
      iAssert (⌜ic_loc cl ≠ null⌝ ∗ own_dll dq yt.(yjs.yType.start') tl null null cells)%I with "[Hdll]" as "[%Hclnn Hdll]".
      { iDestruct (own_dll_lookup_acc _ _ _ _ _ _ _ _ Hcl_lookup with "Hdll") as (ivx olidx oridx) "Hacc".
        iDestruct "Hacc" as "(_&_&_&_&_&_&Hclval&_&_&Hbk)".
        iDestruct (typed_pointsto_not_null with "Hclval") as %Hnn3.
        iDestruct ("Hbk" with "Hclval") as "Hdll". iSplitR; [done | iFrame "Hdll"]. }
      have Hlnn : left_loc ≠ null by rewrite Hll Hcl_loc; exact Hclnn.
      rewrite (bool_decide_eq_false_2 (left_loc = null) Hlnn).
      iDestruct (own_dll_acc _ cells _ _ (Z.to_nat leftIdx) cl Hcl_lookup with "Hdll")
        as (ivl olidl oridl) "(%Hcloc & %Hcl_l & %Hcr_l2 & %Hidl & %Hcontl & %Holidl & %Horidl & %Hflagsl & %Hrunl & %Hparl & Hcval & #Hcol_l & #Hcor_l & Hback)".
      iEval (rewrite -Hcl_loc) in "Hcval". iEval (rewrite Hll) in "left". wp_auto.
      have Hcr_l' : ivl.(yjs.item.right') = node_loc cells (leftIdx + 1).
      { rewrite Hcr_l2. f_equal. rewrite Z2Nat.id; lia. }
      rewrite Hcr_l'.
      iEval (rewrite Hcl_loc) in "Hcval". iDestruct ("Hback" with "Hcval") as "Hdll".
      iAssert (own_ytype_cells parent dq cells arr) with "[Hparent Hdll]" as "Htext".
      { iExists yt, tl. iFrame "Hparent Hdll". done. }
      wp_apply (wp_itemPtrEqual_node parent dq cells arr (leftIdx + 1) rightIdx Harr Hunitc ltac:(lia) ltac:(lia) Hrlen with "[$Htext]").
      iIntros "Htext".
      destruct (decide (leftIdx + 1 = rightIdx)) as [Hadj | Hnadj].
      { (* no scan *)
        rewrite (bool_decide_eq_true_2 _ Hadj). wp_auto.
        rewrite (bool_decide_eq_false_2 (node_loc cells leftIdx = null) ltac:(rewrite -Hll; exact Hlnn)). wp_auto.
        have Hdestadj : Z.of_nat destIdx = leftIdx + 1.
        { rewrite /setfindIntegratedIndex in HfindD.
          replace (Z.to_nat (rightIdx - leftIdx) - 1)%nat with 0%nat in HfindD by lia.
          simpl in HfindD. injection HfindD as HfindD'. rewrite -HfindD' Z2Nat.id; lia. }
        replace (node_loc cells (Z.of_nat destIdx - 1)) with (node_loc cells leftIdx) by (f_equal; lia).
        iApply "HΦ". iFrame "Htext". rewrite /own_fresh_item_raw. iFrame "Hitem Holeft Horight". iPureIntro; split_and!; done. }
      { (* scan *)
        rewrite (bool_decide_eq_false_2 _ Hnadj). wp_auto.
        have Hlnn' : node_loc cells leftIdx ≠ null by (rewrite -Hll; exact Hlnn).
        rewrite (bool_decide_eq_false_2 (node_loc cells leftIdx = null) Hlnn'). wp_auto.
        rewrite (bool_decide_eq_false_2 (node_loc cells leftIdx = null) Hlnn').
        iDestruct "Htext" as (yt' tl') "(Hparent & Hdll & %Hlen' & %Hrepr' & %Hcpar')".
        iDestruct (own_dll_acc _ cells _ _ (Z.to_nat leftIdx) cl Hcl_lookup with "Hdll") as (ivl2 olidl2 oridl2) "(%Hcloc2 & %Hcl_l2b & %Hcr_l2b & %Hidl2 & %Hcontl2 & %Holidl2 & %Horidl2 & %Hflagsl2 & %Hrunl2 & %Hparl2 & Hcval & #Hcol2 & #Hcor2 & Hback)".
        have Hcr_l2' : ivl2.(yjs.item.right') = node_loc cells (leftIdx + 1) by (rewrite Hcr_l2b; f_equal; rewrite Z2Nat.id; lia).
        iEval (rewrite -Hcl_loc) in "Hcval". wp_auto. rewrite Hcr_l2'.
        iEval (rewrite Hcl_loc) in "Hcval". iDestruct ("Hback" with "Hcval") as "Hdll".
        iAssert (own_ytype_cells parent dq cells arr) with "[Hparent Hdll]" as "Htext".
        { iExists yt', tl'. iFrame "Hparent Hdll". iPureIntro; split_and!; [exact Hlen' | exact Hrepr' | exact Hcpar']. }
        wp_apply (wp_scanConflicts parent item_l dq cells arr input newItem iv oleft oright leftIdx rightIdx destIdx
                    Harr Htoitem Hvalid Hmax HfindL HfindR HfindD Hunitc with "[Htext Hitem Holeft Horight]").
        { iSplitL "Htext"; [iFrame "Htext" | rewrite /own_fresh_item_raw; iFrame "Hitem Holeft Horight"; iPureIntro; split_and!; done]. }
        iIntros "[Htext Hfresh]". wp_auto. iApply "HΦ". iFrame "Htext Hfresh". } } }
Qed.

(** Auxiliary spec (the raw refinement): integrating a valid item into a valid
    document yields the document updated per the pure [setintegrate]. Kept as the
    detailed functional characterisation (exposes [setintegrate]/[iv]); the
    public [wp_Store__Integrate] below repackages it as invariant preservation. *)
Lemma wp_Store__integrateCore_aux (s parent item_l : loc) (arr arr' : list (YjsItem A))
    (input : IntegrateInput (A := A)) (newItem : YjsItem A) (cells : list item_cell)
    (iv : yjs.item.t) (oleft oright : option yjs.id.t) (leftIdx rightIdx : Z) :
  YjsArrInvariant arr ->
  toItem input arr = Some newItem ->
  IsItemValid newItem ->
  maximalId newItem arr ->
  findLeftIdx (in_originId input) arr = Some leftIdx ->
  findRightIdx (in_rightOriginId input) arr = Some rightIdx ->
  (* the caller's item arrives already linked to its resolved origin
     neighbours and carrying its parent (store.repair / the local-edit
     creator set them, issue #49) *)
  iv.(yjs.item.left') = node_loc cells leftIdx ->
  iv.(yjs.item.right') = node_loc cells rightIdx ->
  iv.(yjs.item.parent') = parent ->
  iv.(yjs.item.flags') = W8 2 ->   (* freshly built item is Countable (NewItem sets ItemCountable) *)
  length (iv.(yjs.item.content').(yjs.content.content')) = 1%nat ->   (* single-char content => Len() = 1 *)
  Forall cell_unit cells ->   (* all-singleton invariant (issue #28, until M4) *)
  setintegrate input arr = Some arr' ->
  {{{ is_pkg_init yjs ∗ own_ytype_cells parent (DfracOwn 1) cells arr ∗
      own_fresh_item_raw item_l input iv oleft oright }}}
    s @! (go.PointerType yjs.store) @! "integrateCore" #parent #item_l
  {{{ (cells' : list item_cell) (idx : nat) (c : item_cell), RET #();
      own_ytype_cells parent (DfracOwn 1) cells' arr' ∗ ⌜YjsArrInvariant arr'⌝ ∗
      ⌜cells' = take idx cells ++ c :: drop idx cells⌝ ∗
      ⌜(idx <= length arr)%nat⌝ ∗
      ⌜arr' = take idx arr ++ run_head c :: drop idx arr⌝ ∗
      ⌜cells' !! idx = Some c⌝ ∗ ⌜ic_loc c = item_l⌝ ∗
      ⌜item_id (run_head c) = in_id input⌝ ∗ ⌜ic_deleted c = false⌝ ∗
      ⌜cell_unit c⌝ ∗
      ⌜cells' ≡ₚ cells ++ [c]⌝ }}}.
Proof using Type*.
  move=> Harr Htoitem Hvalid Hmax HfindL HfindR HivL HivR Hivpar Hflags Hrun Hunitc.
  (* Decompose the pure result: destIdx / itemM and
     arr' = insertIdxIfInBounds destIdx itemM arr. *)
  rewrite /setintegrate HfindL HfindR /=.
  case HfindD: (setfindIntegratedIndex leftIdx rightIdx input arr) => [destIdx|] //=.
  case HmkI: (mkItemByIndex leftIdx rightIdx input arr) => [itemM|] //=.
  move=> [<-].
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
  have Hcells_len : length cells = length arr := cells_repr_length _ _ _ Hunitc Hrepr3.
  have Hrlen : (rightIdx <= Z.of_nat (length cells))%Z by rewrite Hcells_len; exact HrUB.
  iDestruct "Holeft" as "#Holeft". iDestruct "Horight" as "#Horight".
  (* the item's links are already resolved: no repair stepping (issue #49) *)
  set iv2 := iv.
  have Hiv2L : iv2.(yjs.item.left') = node_loc cells leftIdx := HivL.
  have Hiv2R : iv2.(yjs.item.right') = node_loc cells rightIdx := HivR.
  have Hiv2oL : iv2.(yjs.item.originLeftId') = iv.(yjs.item.originLeftId') := eq_refl.
  have Hiv2oR : iv2.(yjs.item.originRightId') = iv.(yjs.item.originRightId') := eq_refl.
  have Hiv2id : iv2.(yjs.item.id') = iv.(yjs.item.id') := eq_refl.
  have Hiv2con : iv2.(yjs.item.content') = iv.(yjs.item.content') := eq_refl.
  have Hiv2flags : iv2.(yjs.item.flags') = iv.(yjs.item.flags') := eq_refl.
  wp_auto.
  (* Conflict scan (the extracted algorithmic core), via the proved spec. *)
  rewrite Hiv2L Hiv2R.
  iAssert (own_ytype_cells parent (DfracOwn 1) cells arr) with "[Hparent Hdll]" as "Htext".
  { iExists yt3, tl3. iFrame "Hparent Hdll". done. }
  iAssert (own_fresh_item_raw item_l input iv2 oleft oright) with "[Hitem]" as "Hfresh".
  { rewrite /own_fresh_item_raw. iFrame "Hitem". rewrite Hiv2oL Hiv2oR. iFrame "Holeft Horight".
    iPureIntro; split_and!; [exact Hin_l | exact Hin_r | rewrite Hiv2id; exact Hid | rewrite Hiv2con; exact Hcontent]. }
  wp_apply (wp_findIntegrationLeft parent item_l (node_loc cells leftIdx) (node_loc cells rightIdx)
              (DfracOwn 1) cells arr input newItem iv2 oleft oright leftIdx rightIdx destIdx
              Harr Htoitem Hvalid Hmax HfindL HfindR HfindD eq_refl eq_refl Hunitc with "[$Htext $Hfresh]").
  iIntros "[Htext Hfresh]".
  wp_auto.
  (* [destIdx] is in bounds ([≤ rightIdx ≤ length]), so the splice index is valid
     and [insertIdxIfInBounds] actually inserts (mirrors setintegrate_eq_integrate
     to reach findIntegratedIndex_bounds). *)
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
  have Hdle : (destIdx <= length cells)%nat by (rewrite Hcells_len; lia).
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
      "Hleftdll" ∷ own_dll (DfracOwn 1) hd' (node_loc cells (Z.of_nat destIdx - 1)) null item_l cs1m ∗
      "%Hcs1m" ∷ ⌜cells_repr arr cs1m (take destIdx arr)⌝ ∗
      "%Hcs1eq" ∷ ⌜cs1m = take destIdx cells⌝ ∗
      "Hitem" ∷ item_l ↦ ivL ∗
      "%HivLl" ∷ ⌜ivL.(yjs.item.left') = node_loc cells (Z.of_nat destIdx - 1)⌝ ∗
      "%HivLf" ∷ ⌜ivL.(yjs.item.flags') = iv2.(yjs.item.flags')⌝ ∗
      "%HivLc" ∷ ⌜ivL.(yjs.item.content') = iv2.(yjs.item.content')⌝ ∗
      "%HivLid" ∷ ⌜ivL.(yjs.item.id') = iv2.(yjs.item.id')⌝ ∗
      "%HivLoL" ∷ ⌜ivL.(yjs.item.originLeftId') = iv2.(yjs.item.originLeftId')⌝ ∗
      "%HivLoR" ∷ ⌜ivL.(yjs.item.originRightId') = iv2.(yjs.item.originRightId')⌝ ∗
      "%HivLpar" ∷ ⌜ivL.(yjs.item.parent') = iv2.(yjs.item.parent')⌝ ∗
      "Hrightdll" ∷ own_dll (DfracOwn 1) (node_loc cells (Z.of_nat destIdx)) tl' (node_loc cells (Z.of_nat destIdx - 1)) null (drop destIdx cells) ∗
      "Hrightptr" ∷ right_ptr ↦ node_loc cells (Z.of_nat destIdx) ∗
      "item" ∷ item_ptr ↦ item_l ∗
      "parent" ∷ parent_ptr ↦ parent)%I
    with "[Hparent Hdll Hitem left right item parent]".
  { (* destIdx = 0 : head insertion (else branch already executed) *)
    iAssert (⌜destIdx = 0%nat⌝ ∗ own_dll (DfracOwn 1) yt'.(yjs.yType.start') tl' null null cells)%I
      with "[Hdll]" as "(%Hd0 & Hdll)".
    { destruct (decide (destIdx = 0%nat)) as [->|Hne].
      - iFrame "Hdll". done.
      - iDestruct (node_loc_lt_not_null (DfracOwn 1) cells yt'.(yjs.yType.start') tl' (destIdx - 1) with "Hdll") as "(%Hnn & Hdll)".
        { lia. }
        iFrame "Hdll". iPureIntro. exfalso. apply Hnn.
        have -> : Z.of_nat (destIdx - 1) = (Z.of_nat destIdx - 1)%Z by lia.
        exact e. }
    iDestruct (own_dll_head_node with "Hdll") as %Hhd.
    have Hhd2 : node_loc cells (Z.of_nat destIdx) = yt'.(yjs.yType.start').
    { rewrite Hhd. f_equal. lia. }
    have Hdrop : drop destIdx cells = cells by rewrite Hd0 //.
    iSplitR; first done.
    iExists [], item_l, (yt' <| yjs.yType.start' := item_l |>), (iv2 <| yjs.item.left' := null |>).
    iFrame "Hparent Hitem".
    iSplitR. { iPureIntro. done. }
    iSplitR. { iPureIntro. exact Hlen'. }
    iSplitR. { simpl. iPureIntro. split; [done | exact e]. }
    iSplitR. { iPureIntro. rewrite Hd0 /=. apply cells_repr_nil. }
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
  { (* destIdx >= 1 : splice [item] after node (destIdx-1) (then branch). Relink
       that node's [right'] to [item] via own_dll_app + cons unfold + wp_store. *)
    have Hdpos : (1 <= destIdx)%nat.
    { destruct (decide (1 <= destIdx)%nat) as [?|Hlt]; [done | exfalso; apply n].
      have Hd0 : destIdx = 0%nat by lia.
      rewrite Hd0 /node_loc. case_decide as Hdc; [exfalso; lia | done]. }
    have Hltlen : (destIdx - 1 < length cells)%nat by lia.
    destruct (cells !! (destIdx - 1)%nat) as [lc|] eqn:Hlc; last by (apply lookup_ge_None in Hlc; lia).
    have Hlcloc : node_loc cells (Z.of_nat destIdx - 1) = ic_loc lc.
    { rewrite /node_loc decide_True; last lia.
      have -> : Z.to_nat (Z.of_nat destIdx - 1) = (destIdx - 1)%nat by lia.
      rewrite Hlc //. }
    have Hdrop_eq : drop (destIdx - 1)%nat cells = lc :: drop destIdx cells.
    { rewrite (drop_S cells lc (destIdx-1)%nat Hlc). have -> : S (destIdx - 1)%nat = destIdx by lia. done. }
    have Hce : cells = take (destIdx - 1)%nat cells ++ lc :: drop destIdx cells.
    { rewrite -Hdrop_eq. symmetry. apply take_drop. }
    have Htake : take destIdx cells = take (destIdx - 1)%nat cells ++ [lc].
    { rewrite -(take_S_r cells (destIdx-1)%nat lc Hlc). f_equal. lia. }
    iEval (rewrite {1}Hce) in "Hdll".
    iEval (rewrite own_dll_app) in "Hdll".
    iDestruct "Hdll" as (ml1 mf1) "[Hleft1 Hright1]".
    iDestruct "Hright1" as (ivlc olidlc oridlc) "(%Hloc1 & %Hprev1 & %Hparlc & %Hidlc & %Hcontlc & %Holidlc & %Horidlc & %Hflagslc & %Hrunlc & Hval & #Holc & #Horc & Hrest)".
    destruct Hloc1 as [Hmf1 Hmf1nn].
    iDestruct (own_dll_headptr with "Hrest") as "[%Hhd_rest Hrest]".
    have Hcr_rest : ivlc.(yjs.item.right') = node_loc cells (Z.of_nat destIdx).
    { rewrite Hhd_rest /node_loc decide_True; last lia. rewrite Nat2Z.id. f_equal. f_equal.
      rewrite head_lookup lookup_drop Nat.add_0_r //. }
    iEval (rewrite Hlcloc) in "left".
    rewrite Hlcloc.
    wp_auto.
    iSplitR; first done.
    iExists (take (destIdx - 1)%nat cells ++ [lc]), yt'.(yjs.yType.start'), yt', (iv2 <| yjs.item.left' := lc.(ic_loc) |>).
    iFrame "Hparent Hitem".
    iSplitR. { iPureIntro. done. }
    iSplitR. { iPureIntro. exact Hlen'. }
    iSplitL "Hleft1 Hval".
    { rewrite own_dll_app. iExists ml1, lc.(ic_loc).
      iEval (rewrite Hmf1) in "Hleft1". iFrame "Hleft1".
      simpl. iExists (ivlc <| yjs.item.right' := item_l |>), olidlc, oridlc.
      iFrame "Hval Holc Horc". iPureIntro; split_and!;
        [reflexivity | (rewrite -Hmf1; exact Hmf1nn) | exact Hprev1 | exact Hparlc | exact Hidlc
        | exact Hcontlc | exact Holidlc | exact Horidlc | exact Hflagslc | exact Hrunlc
        | reflexivity | reflexivity]. }
    iSplitR.
    { iPureIntro. rewrite -Htake. exact (cells_repr_take arr cells arr destIdx Hunitc Hrepr'). }
    iSplitR. { iPureIntro. symmetry. exact Htake. }
    iSplitR. { iPureIntro. done. }
    iSplitR. { iPureIntro. done. }
    iSplitR. { iPureIntro. done. }
    iSplitR. { iPureIntro. done. }
    iSplitR. { iPureIntro. done. }
    iSplitR. { iPureIntro. done. }
    iSplitR. { iPureIntro. done. }
    iEval (rewrite Hcr_rest Hmf1) in "Hrest".
    iEval (rewrite Hcr_rest) in "right".
    iFrame "Hrest right item parent". }
  iIntros (v) "[%Hv HQ]". iNamed "HQ". subst v. wp_auto.
  (* Second [if] (y-octo: link [right.left] to [item] when a right neighbour
     exists). The [destIdx<length] / [destIdx=length] cases converge to a right
     fragment [cs2m] whose first [left'] points at [item]. *)
  wp_if_join (λ v, ⌜v = execute_val⌝ ∗
    ∃ (cs2m : list item_cell) (tlN : loc),
      "Hrightdll2" ∷ own_dll (DfracOwn 1) (node_loc cells destIdx) tlN item_l null cs2m ∗
      "%Hcs2m" ∷ ⌜cells_repr arr cs2m (drop destIdx arr)⌝ ∗
      "%Hcs2eq" ∷ ⌜cs2m = drop destIdx cells⌝ ∗
      "Hrightptr" ∷ right_ptr ↦ node_loc cells (Z.of_nat destIdx) ∗
      "item" ∷ item_ptr ↦ item_l)%I
    with "[Hrightdll Hrightptr item]".
  { (* destIdx = length cells: no right neighbour (else / no-op) *)
    destruct (drop destIdx cells) as [|rc rest] eqn:Hdrop.
    - iSplitR; first done. iExists [], item_l. iFrame "Hrightptr item".
      iSplitR. { simpl. iPureIntro. split; [exact e | reflexivity]. }
      iSplitR.
      { iPureIntro.
        have Hge : (length cells <= destIdx)%nat.
        { have Hlen0 : length (drop destIdx cells) = 0%nat by rewrite Hdrop //.
          rewrite length_drop in Hlen0. lia. }
        rewrite drop_ge; [apply cells_repr_nil | lia]. }
      iPureIntro. done.
    - iDestruct "Hrightdll" as (ivx olidx oridx) "(%Hl & _)". destruct Hl as [_ Hnn]. exfalso. exact (Hnn e). }
  { (* destIdx < length cells: relink right neighbour's left to item *)
    have Hltlen : (destIdx < length cells)%nat.
    { destruct (decide (destIdx < length cells)%nat) as [?|Hge]; [done|].
      exfalso. apply n. rewrite /node_loc decide_True; last lia.
      rewrite Nat2Z.id lookup_ge_None_2; [done | lia]. }
    destruct (drop destIdx cells) as [|rc rest] eqn:Hdrop.
    { exfalso. have Hl0 : length (drop destIdx cells) = 0%nat by rewrite Hdrop //.
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
    { iPureIntro.
      have Hlenarr : (destIdx < length arr)%nat by (rewrite -Hcells_len; exact Hltlen).
      destruct (drop destIdx arr) as [|ra rest_a] eqn:Hdropa.
      { exfalso. have Hl0 : length (drop destIdx arr) = 0%nat by rewrite Hdropa //.
        rewrite length_drop in Hl0. lia. }
      rewrite -Hdrop -Hdropa. apply cells_repr_drop; [exact Hunitc | exact Hrepr']. }
    iPureIntro. done. }
  iIntros (v) "[%Hv HQ2]". iNamed "HQ2". subst v. wp_auto.
  (* item.right := right (node_loc cells destIdx) already done; now [Countable()]
     is true (flags = ItemCountable) and [Len()] is 1 (single-char content), so
     [parent.len += 1]. Step the [Item.Countable] / [Item.Len] / [Content.Len]
     methods, resolving the symbolic word tests with [Hflv] / [Hclv]. *)
  have Hflv : ivL.(yjs.item.flags') = W8 2 by rewrite HivLf Hiv2flags Hflags.
  have Hclv : length ivL.(yjs.item.content').(yjs.content.content') = 1%nat by rewrite HivLc Hiv2con //.
  wp_method_call. wp_call. wp_auto. wp_method_call. wp_auto. wp_call. wp_auto.
  rewrite Hflv.
  rewrite (bool_decide_eq_false_2 (w8_word_instance.(word.and) (W8 2) (W8 2) = W8 0)); last by vm_compute.
  simpl negb. wp_auto.
  wp_method_call. wp_call. wp_auto. wp_method_call. wp_call. wp_call. wp_auto.
  wp_method_call. wp_call. wp_auto. wp_method_call. wp_call. wp_call. wp_auto.
  wp_func_call. wp_auto. rewrite Hclv. wp_auto.
  (* Conclude [is_valid_ytype parent (insertIdxIfInBounds destIdx itemM arr)]:
     spell out [itemM]'s resolved origins, the validity of the result, and
     reassemble the DLL with the new node spliced in. *)
  destruct (findptridx_insert.findLeftIdx_getElemExcept arr input leftIdx HfindL) as [lptr [HgetL HisL]].
  destruct (findptridx_insert.findRightIdx_getElemExcept arr input rightIdx HfindR) as [rptr [HgetR HisR]].
  have HitemM : itemM = Item lptr rptr input.(in_id) input.(in_content).
  { move: HmkI. rewrite /mkItemByIndex HgetL HgetR /=. by move=> [<-]. }
  have Hlpo : origin_id lptr = input.(in_originId).
  { destruct (input.(in_originId)) as [pid|] eqn:Hpid.
    - destruct HisL as [it [-> Hfind]]. by rewrite /= (toitem_lemmas.find_by_id_id _ _ _ Hfind).
    - by rewrite HisL. }
  have Hrpo : origin_id rptr = input.(in_rightOriginId).
  { destruct (input.(in_rightOriginId)) as [pid|] eqn:Hpid.
    - destruct HisR as [it [-> Hfind]]. by rewrite /= (toitem_lemmas.find_by_id_id _ _ _ Hfind).
    - by rewrite HisR. }
  have Hsetint : setintegrate input arr = Some (insertIdxIfInBounds destIdx itemM arr).
  { rewrite /setintegrate HfindL /= HfindR /= HfindD /= HmkI //. }
  have Hinv'' : YjsArrInvariant (insertIdxIfInBounds destIdx itemM arr).
  { eapply YjsArrInvariant_setintegrate; (try eassumption); (try exact _). }
  have Harr'' : insertIdxIfInBounds destIdx itemM arr = take destIdx arr ++ itemM :: drop destIdx arr.
  { rewrite /insertIdxIfInBounds decide_True; [done | rewrite -Hcells_len; exact Hdle]. }
  have Hcellrepr : cell_repr arr (MkItemCell item_l [itemM] false parent) itemM by rewrite /cell_repr //.
  have Hunit1 : Forall cell_unit cs1m by rewrite Hcs1eq; apply Forall_take, Hunitc.
  have Hunit2 : Forall cell_unit cs2m by rewrite Hcs2eq; apply Forall_drop, Hunitc.
  have Hlen0 : length (cs1m ++ MkItemCell item_l [itemM] false parent :: cs2m) = (length cells + 1)%nat.
  { rewrite length_app /= (cells_repr_length _ _ _ Hunit1 Hcs1m) (cells_repr_length _ _ _ Hunit2 Hcs2m) length_take length_drop. lia. }
  have Hnv0 : num_visible (cs1m ++ MkItemCell item_l [itemM] false parent :: cs2m) = S (num_visible cells).
  { rewrite Hcs1eq Hcs2eq. apply num_visible_insert_visible; reflexivity. }
  have Hstart : (ytv <| yjs.yType.len' := w64_word_instance.(word.add) ytv.(yjs.yType.len') (W64 1%nat) |>).(yjs.yType.start') = hd'.
  { simpl. exact Hyts. }
  have Hcs1len : length cs1m = destIdx.
  { rewrite (cells_repr_length _ _ _ Hunit1 Hcs1m) length_take_le; [done | rewrite -Hcells_len; exact Hdle]. }
  iApply ("HΦ" $! (cs1m ++ MkItemCell item_l [itemM] false parent :: cs2m) destIdx (MkItemCell item_l [itemM] false parent)).
  iSplitL "Hparent Hleftdll Hitem Hrightdll2".
  { iExists (ytv <| yjs.yType.len' := w64_word_instance.(word.add) ytv.(yjs.yType.len') (W64 1%nat) |>), tlN.
    iFrame "Hparent".
    iSplitL.
    { rewrite Hstart.
      have HrightEq : (ivL <| yjs.item.right' := node_loc cells destIdx |>).(yjs.item.right') = node_loc cells destIdx by reflexivity.
      have HleftEq : (ivL <| yjs.item.right' := node_loc cells destIdx |>).(yjs.item.left') = node_loc cells (destIdx - 1).
      { simpl. exact HivLl. }
      have Hidtr : item_id (run_head (MkItemCell item_l [itemM] false parent)) = toYjsId (ivL <| yjs.item.right' := node_loc cells destIdx |>).(yjs.item.id').
      { rewrite /run_head /= HitemM /= HivLid Hiv2id Hid //. }
      have Hconttr : content <$> ic_run (MkItemCell item_l [itemM] false parent) = explode (toContent (ivL <| yjs.item.right' := node_loc cells destIdx |>).(yjs.item.content')).
      { rewrite /= HitemM /=.
        rewrite explode_singleton; last exact Hclv.
        rewrite HivLc Hiv2con Hcontent //. }
      have Holtr : origin_id (origin (run_head (MkItemCell item_l [itemM] false parent))) = toYjsId <$> oleft.
      { rewrite /run_head /= HitemM /= Hlpo -Hin_l2 //. }
      have Hortr : origin_id (rightOrigin (run_head (MkItemCell item_l [itemM] false parent))) = toYjsId <$> oright.
      { rewrite /run_head /= HitemM /= Hrpo -Hin_r2 //. }
      have Hpartr : (ivL <| yjs.item.right' := node_loc cells destIdx |>).(yjs.item.parent')
                    = ic_parent (MkItemCell item_l [itemM] false parent).
      { simpl. rewrite HivLpar /iv2 Hivpar //. }
      iApply (own_dll_insert_middle (DfracOwn 1) cs1m cs2m (MkItemCell item_l [itemM] false parent)
                (ivL <| yjs.item.right' := node_loc cells destIdx |>) oleft oright
                hd' tlN (node_loc cells (destIdx - 1)) (node_loc cells destIdx)
                Hitem_nn HleftEq HrightEq Hpartr Hidtr Hconttr Holtr Hortr Hflv (run_wf_singleton itemM)).
      simpl. rewrite HivLoL HivLoR. iFrame "Hleftdll Hitem Holeft2 Horight2 Hrightdll2". }
    iPureIntro. split_and!.
    - rewrite /= Hytl Hnv0. word.
    - rewrite Harr''. apply cells_repr_app.
      + apply (cells_repr_m_irrel arr). exact Hcs1m.
      + apply cells_repr_cons; [exact Hcellrepr | apply (cells_repr_m_irrel arr); exact Hcs2m].
    - move=> c Hc. rewrite Hcs1eq Hcs2eq in Hc.
      move: Hc. rewrite elem_of_app elem_of_cons.
      move=> [Hc | [-> | Hc]].
      + apply Hcpar'. rewrite -(take_drop destIdx cells) elem_of_app. by left.
      + done.
      + apply Hcpar'. rewrite -(take_drop destIdx cells) elem_of_app. by right. }
  iSplit; [iPureIntro; exact Hinv''|].
  iSplit; [iPureIntro; rewrite Hcs1eq Hcs2eq //|].
  iSplit; [iPureIntro; rewrite -Hcells_len; exact Hdle|].
  iSplit; [iPureIntro; simpl; exact Harr''|].
  iSplit; [iPureIntro; apply list_lookup_middle; by rewrite Hcs1len|].
  iSplit; [iPureIntro; reflexivity|].
  iSplit; [iPureIntro; rewrite /run_head /= HitemM // |].
  iSplit; [iPureIntro; reflexivity|].
  iSplit; [iPureIntro; reflexivity|].
  (* the splice grows the cell list by exactly the new cell: [cs1m = take destIdx
     cells], [cs2m = drop destIdx cells], so [cs1m ++ c :: cs2m ≡ₚ cells ++ [c]]. *)
  iPureIntro. rewrite Hcs1eq Hcs2eq.
  rewrite (Permutation_cons_append (drop destIdx cells) (MkItemCell item_l [itemM] false parent)).
  rewrite app_assoc take_drop //.
Qed.

(** Public top-level spec — [Store.Integrate] inserts the item and preserves the
    document invariant. The result [arr'] is the model document with [newItem]
    spliced in at *some* in-bounds position [i] (the position is existential, so
    the conflict-resolution algorithm is not exposed — only the abstract effect
    "the item was inserted somewhere, and the document stays valid"). The
    document invariant [is_valid_ytype] already carries [YjsArrInvariant], so it
    pins [arr'] uniquely given the item set; the caller's item is encapsulated in
    [own_fresh_item]; the document/input side conditions are the only premises.
    Proven from [wp_Store__Integrate_aux]: integration succeeds ([integrate_some]),
    bridges to [setintegrate] ([setintegrate_eq_integrate]); the insertion
    position and the post-state's validity come from the rocq-yjs preservation
    theorem [YjsArrInvariant_integrate]. *)

(** [item_valid_adjacent]: the pure (model-level) heart of the Text.Insert proof.
    An item whose origin / right-origin are two *adjacent* elements of a valid
    document array is [IsItemValid]. [iiv_origin_lt] is immediate from the array
    being sorted ([yai_sorted]); [iiv_reachable] follows from
    [origin_nearest_reachable] plus the fact that nothing in a sorted array lies
    strictly between adjacent elements (the index lemmas). This isolates the only
    hard obligation of an insert into the order theory, so the WP side only has
    to maintain that the chosen left/right neighbours are adjacent. *)
Lemma item_valid_adjacent (arr : list (YjsItem A)) (i : nat) (a b : YjsItem A)
    (newid : YjsId) (c : A) :
  YjsArrInvariant arr ->
  base.lookup i arr = Some a ->
  base.lookup (S i) arr = Some b ->
  IsItemValid (Item (itemPtr a) (itemPtr b) newid c).
Proof.
  intros Hinv Ha Hb.
  destruct a as [oa ra ida ca]. destruct b as [ob rb idb cb].
  pose proof (yai_item_set_inv _ Hinv) as Hisi.
  pose proof (yai_closed _ Hinv) as Hclosed.
  assert (HaIn : ArrSet arr (Item oa ra ida ca)) by exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Ha).
  assert (HbIn : ArrSet arr (Item ob rb idb cb)) by exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Hb).
  assert (Hab : YjsLt' (Item oa ra ida ca) (Item ob rb idb cb))
    by exact (invariant_yjsarray_idx.getElem_lt_YjsLt' arr i (S i) _ _ Hinv Ha Hb ltac:(lia)).
  assert (Hlo : forall p, ArrSet arr p -> YjsLt' p (Item ob rb idb cb) -> YjsLeq' p (Item oa ra ida ca)).
  { intros p Hp Hpb. destruct p as [q | | ].
    - destruct (list_basics.list.list_elem_of_lookup_1 _ _ Hp) as [iq Hiq].
      assert (iq < S i)%nat by exact (findptridx_order2.getElem_YjsLt'_index_lt arr iq (S i) q (Item ob rb idb cb) Hinv Hiq Hb Hpb).
      apply (invariant_yjsarray_idx.getElem_leq_YjsLeq' arr iq i q (Item oa ra ida ca) Hinv Hiq Ha). lia.
    - exact (YjsLeq'_leqLt _ _ (YjsLt'_ltOriginOrder _ _ (lt_first (Item oa ra ida ca)))).
    - exfalso. destruct Hpb as [h Hh]. exact (not_last_lt_ptr Hclosed Hisi h _ HbIn Hh). }
  assert (Hhi : forall p, ArrSet arr p -> YjsLt' (Item oa ra ida ca) p -> YjsLeq' (Item ob rb idb cb) p).
  { intros p Hp Hap. destruct p as [q | | ].
    - destruct (list_basics.list.list_elem_of_lookup_1 _ _ Hp) as [iq Hiq].
      assert (i < iq)%nat by exact (findptridx_order2.getElem_YjsLt'_index_lt arr i iq (Item oa ra ida ca) q Hinv Ha Hiq Hap).
      apply (invariant_yjsarray_idx.getElem_leq_YjsLeq' arr (S i) iq (Item ob rb idb cb) q Hinv Hb Hiq). lia.
    - exfalso. exact (not_ptr_lt'_first Hclosed Hisi _ HaIn Hap).
    - exact (YjsLeq'_leqLt _ _ (YjsLt'_ltOriginOrder _ _ (lt_last (Item ob rb idb cb)))). }
  assert (HF1 : YjsLeq' (Item ob rb idb cb) ra)
    by exact (Hhi ra (closedRight _ Hclosed oa ra ida ca HaIn) (item_lt_rightOrigin (Item oa ra ida ca))).
  assert (HF2 : YjsLeq' ob (Item oa ra ida ca))
    by exact (Hlo ob (closedLeft _ Hclosed ob rb idb cb HbIn) (item_origin_lt (Item ob rb idb cb))).
  apply Build_IsItemValid.
  - exact Hab.
  - intros x Hreach.
    inversion Hreach as [p1 q1 Hstep | p1 q1 r1 Hstep Hrest]; subst.
    + inversion Hstep; subst; [ left | right ]; apply YjsLeq'_leqSame.
    + inversion Hstep; subst.
      * pose proof (reachable_in arr (Item oa ra ida ca) Hclosed x Hrest HaIn) as HxIn.
        pose proof (origin_nearest_reachable (ArrSet arr) Hisi oa ra ca ida x HaIn Hrest) as [Hxoa | Hrax].
        -- left. apply YjsLeq'_leqLt.
           exact (transitivity.yjs_leq'_p_trans1 Hisi x oa (Item oa ra ida ca) HxIn (closedLeft _ Hclosed oa ra ida ca HaIn) HaIn Hclosed Hxoa (item_origin_lt (Item oa ra ida ca))).
        -- right.
           exact (transitivity.yjs_leq'_p_trans Hisi (Item ob rb idb cb) ra x HbIn (closedRight _ Hclosed oa ra ida ca HaIn) HxIn Hclosed HF1 Hrax).
      * pose proof (reachable_in arr (Item ob rb idb cb) Hclosed x Hrest HbIn) as HxIn.
        pose proof (origin_nearest_reachable (ArrSet arr) Hisi ob rb cb idb x HbIn Hrest) as [Hxob | Hrbx].
        -- left.
           exact (transitivity.yjs_leq'_p_trans Hisi x ob (Item oa ra ida ca) HxIn (closedLeft _ Hclosed ob rb idb cb HbIn) HaIn Hclosed Hxob HF2).
        -- right.
           exact (transitivity.yjs_leq'_p_trans Hisi (Item ob rb idb cb) rb x HbIn (closedRight _ Hclosed ob rb idb cb HbIn) HxIn Hclosed (YjsLeq'_leqLt _ _ (item_lt_rightOrigin (Item ob rb idb cb))) Hrbx).
Qed.

(** Boundary variants of [item_valid_adjacent] for the ends of the document:
    inserting before the head ([First] origin), after the tail ([Last]
    right-origin), or into an empty document ([First]/[Last]). *)
Lemma item_valid_empty (newid : YjsId) (c : A) : IsItemValid (Item First Last newid c).
Proof.
  apply Build_IsItemValid.
  - exact (YjsLt'_ltOriginOrder _ _ lt_first_last).
  - intros x Hreach.
    inversion Hreach as [p1 q1 Hstep | p1 q1 r1 Hstep Hrest]; subst.
    + inversion Hstep; subst; [left|right]; apply YjsLeq'_leqSame.
    + exfalso. inversion Hstep; subst; inversion Hrest as [u v Hs | u v w Hs Hr]; inversion Hs.
Qed.

Lemma item_valid_head (arr : list (YjsItem A)) (b : YjsItem A) (newid : YjsId) (c : A) :
  YjsArrInvariant arr -> base.lookup 0%nat arr = Some b ->
  IsItemValid (Item First (itemPtr b) newid c).
Proof.
  intros Hinv Hb. destruct b as [ob rb idb cb].
  pose proof (yai_item_set_inv _ Hinv) as Hisi.
  pose proof (yai_closed _ Hinv) as Hclosed.
  assert (HbIn : ArrSet arr (Item ob rb idb cb)) by exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Hb).
  assert (Hob : ob = First).
  { pose proof (closedLeft _ Hclosed ob rb idb cb HbIn) as Hobin.
    pose proof (item_origin_lt (Item ob rb idb cb)) as Hoblt.
    destruct ob as [q | | ].
    - exfalso. destruct (list_basics.list.list_elem_of_lookup_1 _ _ Hobin) as [iq Hiq].
      assert (iq < 0)%nat by exact (findptridx_order2.getElem_YjsLt'_index_lt arr iq 0 q (Item (itemPtr q) rb idb cb) Hinv Hiq Hb Hoblt). lia.
    - reflexivity.
    - exfalso. destruct Hoblt as [h Hh]. exact (not_last_lt_ptr Hclosed Hisi h _ HbIn Hh). }
  subst ob.
  apply Build_IsItemValid.
  - exact (YjsLt'_ltOriginOrder _ _ (lt_first (Item First rb idb cb))).
  - intros x Hreach.
    inversion Hreach as [p1 q1 Hstep | p1 q1 r1 Hstep Hrest]; subst.
    + inversion Hstep; subst; [left|right]; apply YjsLeq'_leqSame.
    + inversion Hstep; subst.
      * exfalso. inversion Hrest as [u v Hs | u v w Hs Hr]; inversion Hs.
      * pose proof (origin_nearest_reachable (ArrSet arr) Hisi First rb cb idb x HbIn Hrest) as [Hxob | Hrbx].
        -- left. exact Hxob.
        -- right.
           pose proof (reachable_in arr (Item First rb idb cb) Hclosed x Hrest HbIn) as HxIn.
           exact (transitivity.yjs_leq'_p_trans Hisi (Item First rb idb cb) rb x HbIn (closedRight _ Hclosed First rb idb cb HbIn) HxIn Hclosed (YjsLeq'_leqLt _ _ (item_lt_rightOrigin (Item First rb idb cb))) Hrbx).
Qed.

Lemma item_valid_tail (arr : list (YjsItem A)) (a : YjsItem A) (newid : YjsId) (c : A) :
  YjsArrInvariant arr -> base.lookup (length arr - 1)%nat arr = Some a ->
  IsItemValid (Item (itemPtr a) Last newid c).
Proof.
  intros Hinv Ha. destruct a as [oa ra ida ca].
  pose proof (yai_item_set_inv _ Hinv) as Hisi.
  pose proof (yai_closed _ Hinv) as Hclosed.
  assert (HaIn : ArrSet arr (Item oa ra ida ca)) by exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Ha).
  assert (Hra : ra = Last).
  { pose proof (closedRight _ Hclosed oa ra ida ca HaIn) as Hrain.
    pose proof (item_lt_rightOrigin (Item oa ra ida ca)) as Hralt.
    destruct ra as [q | | ].
    - exfalso. destruct (list_basics.list.list_elem_of_lookup_1 _ _ Hrain) as [iq Hiq].
      assert (length arr - 1 < iq)%nat by exact (findptridx_order2.getElem_YjsLt'_index_lt arr (length arr - 1) iq (Item oa (itemPtr q) ida ca) q Hinv Ha Hiq Hralt).
      pose proof (list_basics.list.lookup_lt_Some _ _ _ Hiq) as Hbound. lia.
    - exfalso. exact (not_ptr_lt'_first Hclosed Hisi _ HaIn Hralt).
    - reflexivity. }
  subst ra.
  apply Build_IsItemValid.
  - exact (YjsLt'_ltOriginOrder _ _ (lt_last (Item oa Last ida ca))).
  - intros x Hreach.
    inversion Hreach as [p1 q1 Hstep | p1 q1 r1 Hstep Hrest]; subst.
    + inversion Hstep; subst; [left|right]; apply YjsLeq'_leqSame.
    + inversion Hstep; subst.
      * pose proof (origin_nearest_reachable (ArrSet arr) Hisi oa Last ca ida x HaIn Hrest) as [Hxoa | Hrax].
        -- left.
           pose proof (reachable_in arr (Item oa Last ida ca) Hclosed x Hrest HaIn) as HxIn.
           apply YjsLeq'_leqLt.
           exact (transitivity.yjs_leq'_p_trans1 Hisi x oa (Item oa Last ida ca) HxIn (closedLeft _ Hclosed oa Last ida ca HaIn) HaIn Hclosed Hxoa (item_origin_lt (Item oa Last ida ca))).
        -- right. exact Hrax.
      * exfalso. inversion Hrest as [u v Hs | u v w Hs Hr]; inversion Hs.
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

(** Unified validity for an insert straddling position [p]: the new item's
    origin is either [First] (at the head, [p = 0]) or the element at [p-1], and
    its right-origin is either [Last] (at the tail, [p = length arr]) or the
    element at [p]. Dispatches to the four boundary lemmas. This is what a
    general [Text.Insert] needs: the loop only has to know the [findPos]
    neighbours straddle [p]. *)
Lemma item_valid_at (arr : list (YjsItem A)) (p : nat) (newid : YjsId) (c : A) (o r : YjsPtr A) :
  YjsArrInvariant arr ->
  (p = 0%nat /\ o = First \/ (1 <= p)%nat /\ ∃ a, base.lookup (p-1)%nat arr = Some a /\ o = itemPtr a) ->
  (p = length arr /\ r = Last \/ ∃ b, base.lookup p arr = Some b /\ r = itemPtr b) ->
  IsItemValid (Item o r newid c).
Proof.
  intros Hinv Hleft Hright.
  destruct Hleft as [[Hp0 ->] | [Hp1 [a [Ha ->]]]].
  - destruct Hright as [[Hplen ->] | [b [Hb ->]]].
    + exact (item_valid_empty newid c).
    + subst p. exact (item_valid_head arr b newid c Hinv Hb).
  - destruct Hright as [[Hplen ->] | [b [Hb ->]]].
    + subst p. exact (item_valid_tail arr a newid c Hinv Ha).
    + have Hb' : base.lookup (S (p-1)) arr = Some b by (replace (S (p-1)) with p by lia; exact Hb).
      exact (item_valid_adjacent arr (p-1) a b newid c Hinv Ha Hb').
Qed.

(** Companion placement for [item_valid_at]: integrate places the straddling
    item at exactly [p] ([take p arr ++ nit :: drop p arr]). Discharges the two
    order bounds of [insert_at_pos] from the origin / right-origin being the
    [p-1] / [p] neighbours (boundary cases [First] / [Last] make a bound
    vacuous). *)
Lemma insert_straddle (arr : list (YjsItem A)) (nit : YjsItem A) (i p : nat) :
  YjsArrInvariant arr ->
  YjsArrInvariant (insertIdxIfInBounds i nit arr) ->
  (i <= length arr)%nat -> (p <= length arr)%nat ->
  (p = 0%nat /\ origin nit = First \/ (1 <= p)%nat /\ ∃ a, base.lookup (p-1)%nat arr = Some a /\ origin nit = itemPtr a) ->
  (p = length arr /\ rightOrigin nit = Last \/ ∃ b, base.lookup p arr = Some b /\ rightOrigin nit = itemPtr b) ->
  insertIdxIfInBounds i nit arr = take p arr ++ nit :: drop p arr.
Proof.
  intros Hinv Hinv' Hile Hple Hleft Hright.
  have Hisi' := yai_item_set_inv _ Hinv'.
  have Hclosed' := yai_closed _ Hinv'.
  have Pnit : nit ∈ insertIdxIfInBounds i nit arr by (apply (proj2 (mem_insertIdxIfInBounds _ _ _ _ Hile)); left; reflexivity).
  apply (insert_at_pos arr nit i p Hinv Hinv' Hile Hple).
  - intros k a Hk Hak.
    destruct Hleft as [[Hp0 _] | [Hp1 [a0 [Ha0 Horig]]]]; [exfalso; lia |].
    have Ha0nit : YjsLt' a0 nit by (rewrite -Horig; apply item_origin_lt).
    destruct (decide (k = (p - 1)%nat)) as [Hkeq | Hne].
    + rewrite Hkeq Ha0 in Hak. injection Hak as ->. exact Ha0nit.
    + have Hka0 : YjsLt' a a0 by (apply (invariant_yjsarray_idx.getElem_lt_YjsLt' arr k (p-1)%nat a a0 Hinv Hak Ha0); lia).
      have Pa : a ∈ insertIdxIfInBounds i nit arr by (apply (proj2 (mem_insertIdxIfInBounds _ _ _ _ Hile)); right; exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Hak)).
      have Pa0 : a0 ∈ insertIdxIfInBounds i nit arr by (apply (proj2 (mem_insertIdxIfInBounds _ _ _ _ Hile)); right; exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Ha0)).
      exact (transitivity.yjs_lt_trans Hisi' Hclosed' (itemPtr a) (itemPtr a0) (itemPtr nit) Pa Pa0 Pnit Hka0 Ha0nit).
  - intros k b Hk1 Hk2 Hbk.
    destruct Hright as [[Hplen _] | [b0 [Hb0 Horigr]]]; [exfalso; lia |].
    have Hnitb0 : YjsLt' nit b0 by (rewrite -Horigr; apply item_lt_rightOrigin).
    destruct (decide (k = p)) as [Hkeq | Hne].
    + rewrite Hkeq Hb0 in Hbk. injection Hbk as ->. exact Hnitb0.
    + have Hb0b : YjsLt' b0 b by (apply (invariant_yjsarray_idx.getElem_lt_YjsLt' arr p k b0 b Hinv Hb0 Hbk); lia).
      have Pb : b ∈ insertIdxIfInBounds i nit arr by (apply (proj2 (mem_insertIdxIfInBounds _ _ _ _ Hile)); right; exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Hbk)).
      have Pb0 : b0 ∈ insertIdxIfInBounds i nit arr by (apply (proj2 (mem_insertIdxIfInBounds _ _ _ _ Hile)); right; exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Hb0)).
      exact (transitivity.yjs_lt_trans Hisi' Hclosed' (itemPtr nit) (itemPtr b0) (itemPtr b) Pnit Pb0 Pb Hnitb0 Hb0b).
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
    (oL oR : option YjsId) :
  YjsArrInvariant arr ->
  (oL = None /\ o = First \/ ∃ a, oL = Some (item_id a) /\ a ∈ arr /\ o = itemPtr a) ->
  (oR = None /\ r = Last \/ ∃ b, oR = Some (item_id b) /\ b ∈ arr /\ r = itemPtr b) ->
  toItem (MkIntegrateInput oL oR cont newid) arr = Some (Item o r newid cont).
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

(** Cells-level spec of the DLL-splice core: exposes the heap effect on the
    cells — the fresh cell [c] (located at the argument [item_l], carrying
    [newItem], visible) is spliced into [cells] at the resolved position [idx]
    (equivalently, appended as a multiset: [cells' ≡ₚ cells ++ [c]], the form
    the [AddNode] bookkeeping consumes). The [Text.Insert] loop and the
    [Store.Integrate] wrapper compose with this; the public model-level
    [wp_Store__integrateCore] below hides the cells. The inserted cell is
    identified with [newItem] by id-uniqueness of the valid result. *)
Lemma wp_Store__integrateCore_cells (s parent item_l : loc) (arr : list (YjsItem A))
    (input : IntegrateInput (A := A)) (newItem : YjsItem A) (cells : list item_cell)
    (leftIdx rightIdx : Z) :
  YjsArrInvariant arr ->
  toItem input arr = Some newItem ->
  IsItemValid newItem ->
  maximalId newItem arr ->
  findLeftIdx (in_originId input) arr = Some leftIdx ->
  findRightIdx (in_rightOriginId input) arr = Some rightIdx ->
  Forall cell_unit cells ->
  {{{ is_pkg_init yjs ∗ own_ytype_cells parent (DfracOwn 1) cells arr ∗
      own_linked_item item_l input parent (node_loc cells leftIdx) (node_loc cells rightIdx) }}}
    s @! (go.PointerType yjs.store) @! "integrateCore" #parent #item_l
  {{{ (arr' : list (YjsItem A)) (idx : nat) (cells' : list item_cell) (c : item_cell), RET #();
      ⌜(idx <= length arr)%nat⌝ ∗ ⌜arr' = insertIdxIfInBounds idx newItem arr⌝ ∗
      ⌜YjsArrInvariant arr'⌝ ∗ own_ytype_cells parent (DfracOwn 1) cells' arr' ∗
      ⌜cells' = take idx cells ++ c :: drop idx cells⌝ ∗
      ⌜cells' ≡ₚ cells ++ [c]⌝ ∗ ⌜setintegrate input arr = Some arr'⌝ ∗
      ⌜cells' !! idx = Some c⌝ ∗ ⌜ic_loc c = item_l⌝ ∗
      ⌜run_head c = newItem⌝ ∗ ⌜ic_deleted c = false⌝ ∗ ⌜cell_unit c⌝ }}}.
Proof using Type*.
  move=> Hinv Htoitem Hvalid Hmax HfindL HfindR Hunitc.
  iIntros (Φ) "(Hpkg & Htext & Hfresh) HΦ".
  iDestruct "Hfresh" as (iv oleft oright) "(Hraw & %Hfl & %Hfr & %Hfpar & %Hflags & %Hrun)".
  destruct (integrate_some input arr newItem Hinv Htoitem) as [arr' Hintegrate].
  have Hsi : setintegrate input arr = Some arr'.
  { rewrite (setintegrate_eq_integrate input arr newItem Hinv Htoitem Hvalid Hmax). exact Hintegrate. }
  wp_apply (wp_Store__integrateCore_aux s parent item_l arr arr' input newItem cells iv oleft oright
              leftIdx rightIdx
              Hinv Htoitem Hvalid Hmax HfindL HfindR Hfl Hfr Hfpar Hflags Hrun Hunitc Hsi
              with "[$Hpkg $Hraw $Htext]").
  iIntros (cells' idx c) "(Htext' & %Hinv' & %Hsplice & %Hile & %Harrsp & %Hlook & %Hloc & %Hcid & %Hcdel & %Hcunit & %Hperm)".
  (* identify the inserted cell with the argument: it is the unique [arr']-item of
     id [in_id input], and so equals [newItem] (= toItem input arr). *)
  iDestruct "Htext'" as (ytX tlX) "(HpX & HdllX & %HlenX & %HreprX & %HcparX)".
  have Hunitcs' : Forall cell_unit cells'
    by (rewrite Hsplice; exact (Forall_cell_unit_splice cells idx c Hunitc Hcunit)).
  have Hcin : run_head c ∈ arr'.
  { rewrite /cells_repr in HreprX. rewrite HreprX.
    rewrite (run_flatten_singletons cells' Hunitcs').
    apply (list_basics.list.list_elem_of_lookup_2 _ idx).
    rewrite list_lookup_fmap Hlook //. }
  have HnewIn : newItem ∈ arr'.
  { destruct (YjsArrInvariant_integrate input arr arr' newItem Hinv Htoitem Hvalid Hmax Hintegrate)
      as [i [Hile' [Harr'eq _]]].
    rewrite Harr'eq. apply (proj2 (mem_insertIdxIfInBounds _ _ _ _ Hile')). left. reflexivity. }
  have Hidnew : item_id newItem = in_id input := commutativity.toItem_id input arr newItem Htoitem.
  have Hcnew : run_head c = newItem.
  { apply (id_unique (ArrSet arr') (yai_item_set_inv _ Hinv') (run_head c) newItem);
      [rewrite Hcid Hidnew // | exact Hcin | exact HnewIn]. }
  iApply ("HΦ" $! arr' idx cells' c).
  iSplit; [iPureIntro; exact Hile|].
  iSplit; [iPureIntro; rewrite /insertIdxIfInBounds decide_True; [rewrite Harrsp Hcnew // | exact Hile]|].
  iSplit; [iPureIntro; exact Hinv'|].
  iSplitL "HpX HdllX".
  { iExists ytX, tlX. iFrame "HpX HdllX". iPureIntro; split_and!; [exact HlenX | exact HreprX | exact HcparX]. }
  iPureIntro. split_and!;
    [exact Hsplice | exact Hperm | exact Hsi | exact Hlook | exact Hloc | exact Hcnew | exact Hcdel | exact Hcunit].
Qed.

(* The former public model-level [wp_Store__integrateCore] (over [own_ytype])
   is retired by #49: the core's precondition now mentions the resolved origin
   neighbours' node locations (the item arrives pre-linked), which a pure
   model-level footprint cannot state. The public story lives one level up
   ([wp_Store__Integrate] and the doc-level [applyUpdate] specs). *)

(** Top-level [Store.Integrate] = [integrateCore] (DLL splice) then [AddNode]
    (record the item in [store.items]). Threads [own_item_map]: [AddNode] appends
    the new item's loc, which [client_run_loc_tail] shows lands at the tail of its
    client's clock-sorted run (other clients untouched, [client_run_loc_other]).
    [Hgmax] (the new item's clock strictly exceeds every same-client heap clock
    across all types, sourced from the store counter at the [Text.Insert] layer)
    puts the new loc at the tail. *)
Lemma wp_Store__Integrate (s parent item_l : loc) (arr : list (YjsItem A))
    (input : IntegrateInput (A := A)) (newItem : YjsItem A)
    (cells : list item_cell) (types : gmap loc type_state) (mref : loc)
    (leftIdx rightIdx : Z) :
  YjsArrInvariant arr ->
  toItem input arr = Some newItem ->
  IsItemValid newItem ->
  maximalId newItem arr ->
  findLeftIdx (in_originId input) arr = Some leftIdx ->
  findRightIdx (in_rightOriginId input) arr = Some rightIdx ->
  types !! parent = Some (MkTypeState cells arr) ->
  (∀ c0, c0 ∈ all_cells types -> cell_client c0 = W64 (clientId (item_id newItem)) ->
     (uint.Z (cell_clock c0) < uint.Z (W64 (clock (item_id newItem))))%Z) ->
  Forall cell_unit cells ->
  {{{ is_pkg_init yjs ∗ own_ytype_cells parent (DfracOwn 1) cells arr ∗
      own_linked_item item_l input parent (node_loc cells leftIdx) (node_loc cells rightIdx) ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types }}}
    s @! (go.PointerType yjs.store) @! "Integrate" #parent #item_l
  {{{ (arr' : list (YjsItem A)) (i : nat) (cells' : list item_cell) (c : item_cell), RET #();
      ⌜(i <= length arr)%nat⌝ ∗ ⌜arr' = insertIdxIfInBounds i newItem arr⌝ ∗
      ⌜YjsArrInvariant arr'⌝ ∗ own_ytype_cells parent (DfracOwn 1) cells' arr' ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗
      own_item_map mref (DfracOwn 1) (<[parent := MkTypeState cells' arr']> types) ∗
      ⌜cells' ≡ₚ cells ++ [c]⌝ ∗ ⌜setintegrate input arr = Some arr'⌝ ∗
      ∃ idx, ⌜cells' = take idx cells ++ c :: drop idx cells⌝ ∗
             ⌜arr' = take idx arr ++ newItem :: drop idx arr⌝ ∗
             ⌜cells' !! idx = Some c⌝ ∗ ⌜ic_loc c = item_l⌝ ∗ ⌜run_head c = newItem⌝ ∗
             ⌜cell_unit c⌝ }}}.
Proof using Type*.
  move=> Hinv Htoitem Hvalid Hmax HfindL HfindR Htypes Hgmax Hunitc.
  iIntros (Φ) "(Hpkg & Htext & Hfresh & Hitemsf & Hitemmap) HΦ".
  (* The explicit-parent fast path: [parent ≠ nil], so the resolution branch is
     skipped (y-octo's Option<&mut YType> Some case, issue #49). *)
  iDestruct "Htext" as (yt0 tl0) "(Hparent0 & Hdll0 & %Hlen0 & %Hrepr0 & %Hcpar0)".
  iDestruct (typed_pointsto_not_null with "Hparent0") as %Hpnn.
  iAssert (own_ytype_cells parent (DfracOwn 1) cells arr) with "[Hparent0 Hdll0]" as "Htext".
  { iExists yt0, tl0. iFrame "Hparent0 Hdll0". iPureIntro.
    split_and!; [exact Hlen0 | exact Hrepr0 | exact Hcpar0]. }
  (* Step the [Integrate] body: skip the nil-parent branch, then
     [integrateCore] (the DLL splice) and [AddNode]. *)
  wp_method_call. wp_call. wp_call. wp_auto.
  rewrite (bool_decide_eq_false_2 (parent = null) Hpnn). wp_auto.
  wp_apply (wp_Store__integrateCore_cells s parent item_l arr input newItem cells
              leftIdx rightIdx
              Hinv Htoitem Hvalid Hmax HfindL HfindR Hunitc with "[$Hpkg $Htext $Hfresh]").
  iIntros (arr' idx cells' c) "(%Hile & %Harr'eq & %Hinv' & Htext' & %Hsplice & %Hperm & %Hsi & %Hlook & %Hloc & %Hcid & %Hcdel & %Hcunit)".
  wp_auto.
  (* AddNode: read [it.id.clientId] off the integrated cell, look up its run list,
     append the new loc, and store it back. *)
  wp_method_call. wp_call. wp_call. wp_auto.
  iDestruct "Htext'" as (yt tl) "(Hpar & Hdll & %Hlen' & %Hrepr' & %Hcpar')".
  iDestruct (own_dll_acc (DfracOwn 1) cells' yt.(yjs.yType.start') tl idx c Hlook with "Hdll") as "Hacc".
  iNamed "Hacc".
  iEval (rewrite Hloc) in "Hcval".
  wp_auto.
  iNamed "Hitemmap".
  have Hcc : cell_client c = iv.(yjs.item.id').(yjs.id.clientId')
    by (rewrite /cell_client Hid /toYjsId /=; word).
  wp_apply (wp_map_lookup1 with "Hmap"). iIntros "Hmap". wp_auto.
  (* The new cell grows the global cell pool by exactly [c], hence the [cell_kp]
     multiset, hence (via [client_run_loc_tail]) its client's run list at the tail. *)
  have Hac2 : all_cells (<[parent := {| ty_cells := cells'; ty_arr := arr' |}]> types)
              ≡ₚ all_cells types ++ [c]
    by apply (all_cells_insert_snoc types parent cells arr cells' arr' c Htypes Hperm).
  have Hkp : cell_kp <$> all_cells (<[parent := {| ty_cells := cells'; ty_arr := arr' |}]> types)
             ≡ₚ (cell_kp <$> all_cells types) ++ [cell_kp c]
    by rewrite Hac2 fmap_app.
  have Hmax_arg : ∀ c0, c0 ∈ all_cells types → cell_client c0 = cell_client c →
                    ((cell_pr c0).1 < (cell_pr c).1)%Z.
  { intros c0 Hc0 Hcce. rewrite /cell_pr /=.
    have Hclkc : cell_clock c = W64 (clock (item_id newItem)) by rewrite /cell_clock Hcid.
    rewrite Hclkc. apply (Hgmax c0 Hc0). rewrite Hcce /cell_client Hcid //. }
  have Hrun_eq := client_run_loc_tail types
                    (<[parent := {| ty_cells := cells'; ty_arr := arr' |}]> types) c Hkp Hclkloc Hmax_arg.
  set (kc := iv.(yjs.item.id').(yjs.id.clientId')) in *.
  rewrite Hcc in Hrun_eq.
  (* The looked-up slice owns this client's current run (the empty/nil slice when
     absent), plus the untouched runs of the other clients. *)
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
  (* Re-establish [own_item_map] over the grown [types]: the new cell only adds [c]
     to the pool, so completeness / the clock-determines-loc side condition survive
     ([c] is strictly clock-maximal for its client, by [Hgmax]). *)
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
  iDestruct ("Hback" with "Hcval") as "Hdll".
  iNamed "Hpar".
  iAssert (own_item_map mref (DfracOwn 1) types2) with "[Hmap Hsnew Hsnewcap Hrunsrest]" as "Hitemmap'".
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
  iApply ("HΦ" $! arr' idx cells' c).
  iFrame "Hitemsf Hitemmap'".
  iSplitR; [iPureIntro; exact Hile|].
  iSplitR; [iPureIntro; exact Harr'eq|].
  iSplitR; [iPureIntro; exact Hinv'|].
  iSplitL "Hparent Hdll".
  { iExists yt, tl. iFrame "Hparent Hdll". iPureIntro. split_and!; [exact Hlen' | exact Hrepr' | exact Hcpar']. }
  iSplitR; [iPureIntro; exact Hperm|].
  iSplitR; [iPureIntro; exact Hsi|].
  have Harrsp : arr' = take idx arr ++ newItem :: drop idx arr
    by rewrite Harr'eq /insertIdxIfInBounds decide_True //.
  iExists idx. iPureIntro.
  split_and!; [exact Hsplice | exact Harrsp | exact Hlook | exact Hloc | exact Hcid | exact Hcunit].
Qed.


(** [Store.Integrate] with a nil parent argument (the update path, issue #49):
    the resolution branch reads the parent off the item itself (set by
    [store.repair]) — y-octo's Option<&mut YType> None case. The item's parent
    is [own_linked_item]'s [parent], pinned non-null by the type's heap struct,
    so the drop branch is dead and the spec coincides with
    [wp_Store__Integrate]. After the guard the code paths coincide; so do the
    proofs (kept in sync by hand — the guard stepping is the only delta). *)
Lemma wp_Store__Integrate_nil (s parent item_l : loc) (arr : list (YjsItem A))
    (input : IntegrateInput (A := A)) (newItem : YjsItem A)
    (cells : list item_cell) (types : gmap loc type_state) (mref : loc)
    (leftIdx rightIdx : Z) :
  YjsArrInvariant arr ->
  toItem input arr = Some newItem ->
  IsItemValid newItem ->
  maximalId newItem arr ->
  findLeftIdx (in_originId input) arr = Some leftIdx ->
  findRightIdx (in_rightOriginId input) arr = Some rightIdx ->
  types !! parent = Some (MkTypeState cells arr) ->
  (∀ c0, c0 ∈ all_cells types -> cell_client c0 = W64 (clientId (item_id newItem)) ->
     (uint.Z (cell_clock c0) < uint.Z (W64 (clock (item_id newItem))))%Z) ->
  Forall cell_unit cells ->
  {{{ is_pkg_init yjs ∗ own_ytype_cells parent (DfracOwn 1) cells arr ∗
      own_linked_item item_l input parent (node_loc cells leftIdx) (node_loc cells rightIdx) ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types }}}
    s @! (go.PointerType yjs.store) @! "Integrate" #null #item_l
  {{{ (arr' : list (YjsItem A)) (i : nat) (cells' : list item_cell) (c : item_cell), RET #();
      ⌜(i <= length arr)%nat⌝ ∗ ⌜arr' = insertIdxIfInBounds i newItem arr⌝ ∗
      ⌜YjsArrInvariant arr'⌝ ∗ own_ytype_cells parent (DfracOwn 1) cells' arr' ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗
      own_item_map mref (DfracOwn 1) (<[parent := MkTypeState cells' arr']> types) ∗
      ⌜cells' ≡ₚ cells ++ [c]⌝ ∗ ⌜setintegrate input arr = Some arr'⌝ ∗
      ∃ idx, ⌜cells' = take idx cells ++ c :: drop idx cells⌝ ∗
             ⌜arr' = take idx arr ++ newItem :: drop idx arr⌝ ∗
             ⌜cells' !! idx = Some c⌝ ∗ ⌜ic_loc c = item_l⌝ ∗ ⌜run_head c = newItem⌝ ∗
             ⌜cell_unit c⌝ }}}.
Proof using Type*.
  move=> Hinv Htoitem Hvalid Hmax HfindL HfindR Htypes Hgmax Hunitc.
  iIntros (Φ) "(Hpkg & Htext & Hfresh & Hitemsf & Hitemmap) HΦ".
  iDestruct "Htext" as (yt0 tl0) "(Hparent0 & Hdll0 & %Hlen0 & %Hrepr0 & %Hcpar0)".
  iDestruct (typed_pointsto_not_null with "Hparent0") as %Hpnn.
  iAssert (own_ytype_cells parent (DfracOwn 1) cells arr) with "[Hparent0 Hdll0]" as "Htext".
  { iExists yt0, tl0. iFrame "Hparent0 Hdll0". iPureIntro.
    split_and!; [exact Hlen0 | exact Hrepr0 | exact Hcpar0]. }
  (* [parent == nil]: take the resolution branch and read the item's own
     parent (set by [store.repair]) — y-octo's Option::None case, issue #49. *)
  iDestruct "Hfresh" as (iv2 oleft2 oright2) "(Hraw & %Hfl2 & %Hfr2 & %Hfpar2 & %Hflags2 & %Hrun2)".
  iNamed "Hraw".
  wp_method_call. wp_call. wp_call. wp_auto.
  rewrite Hfpar2 (bool_decide_eq_false_2 (parent = null) Hpnn).
  wp_auto.
  iAssert (own_linked_item item_l input parent (node_loc cells leftIdx) (node_loc cells rightIdx))
    with "[Hitem Holeft Horight]" as "Hfresh".
  { iExists iv2, oleft2, oright2. rewrite /own_fresh_item_raw.
    iFrame "Hitem Holeft Horight". iPureIntro.
    split_and!; [exact Hin_l | exact Hin_r | exact Hid | exact Hcontent
                | exact Hfl2 | exact Hfr2 | exact Hfpar2 | exact Hflags2 | exact Hrun2]. }
  rewrite Hfpar2.
  wp_apply (wp_Store__integrateCore_cells s parent item_l arr input newItem cells
              leftIdx rightIdx
              Hinv Htoitem Hvalid Hmax HfindL HfindR Hunitc with "[$Hpkg $Htext $Hfresh]").
  iIntros (arr' idx cells' c) "(%Hile & %Harr'eq & %Hinv' & Htext' & %Hsplice & %Hperm & %Hsi & %Hlook & %Hloc & %Hcid & %Hcdel & %Hcunit)".
  wp_auto.
  (* AddNode — identical to [wp_Store__Integrate] from here on. *)
  wp_method_call. wp_call. wp_call. wp_auto.
  iDestruct "Htext'" as (yt tl) "(Hpar & Hdll & %Hlen' & %Hrepr' & %Hcpar')".
  iDestruct (own_dll_acc (DfracOwn 1) cells' yt.(yjs.yType.start') tl idx c Hlook with "Hdll") as "Hacc".
  iNamed "Hacc".
  iEval (rewrite Hloc) in "Hcval".
  wp_auto.
  iNamed "Hitemmap".
  have Hcc : cell_client c = iv.(yjs.item.id').(yjs.id.clientId')
    by (rewrite /cell_client Hid0 /toYjsId /=; word).
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
    have Hclkc : cell_clock c = W64 (clock (item_id newItem)) by rewrite /cell_clock Hcid.
    rewrite Hclkc. apply (Hgmax c0 Hc0). rewrite Hcce /cell_client Hcid //. }
  have Hrun_eq := client_run_loc_tail types
                    (<[parent := {| ty_cells := cells'; ty_arr := arr' |}]> types) c Hkp Hclkloc Hmax_arg.
  set (kc := iv.(yjs.item.id').(yjs.id.clientId')) in *.
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
  iDestruct ("Hback" with "Hcval") as "Hdll".
  iNamed "Hpar".
  iAssert (own_item_map mref (DfracOwn 1) types2) with "[Hmap Hsnew Hsnewcap Hrunsrest]" as "Hitemmap'".
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
  iApply ("HΦ" $! arr' idx cells' c).
  iFrame "Hitemsf Hitemmap'".
  iSplitR; [iPureIntro; exact Hile|].
  iSplitR; [iPureIntro; exact Harr'eq|].
  iSplitR; [iPureIntro; exact Hinv'|].
  iSplitL "Hparent Hdll".
  { iExists yt, tl. iFrame "Hparent Hdll". iPureIntro. split_and!; [exact Hlen' | exact Hrepr' | exact Hcpar']. }
  iSplitR; [iPureIntro; exact Hperm|].
  iSplitR; [iPureIntro; exact Hsi|].
  have Harrsp : arr' = take idx arr ++ newItem :: drop idx arr
    by rewrite Harr'eq /insertIdxIfInBounds decide_True //.
  iExists idx. iPureIntro.
  split_and!; [exact Hsplice | exact Harrsp | exact Hlook | exact Hloc | exact Hcid | exact Hcunit].
Qed.

End store_integrate.
