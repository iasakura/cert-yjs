(** The wire delete path (issue #133, plan section 5): [store.deleteNode]
    tombstones one integrated node and [store.deleteRange] tombstones a whole
    clock range, splitting at the range boundaries so the deletion covers
    exactly the requested chars.

    Both are stated over the store's CELL-POOL bundle (the [items] field, its
    [own_item_map] and the per-type DLL big-op) rather than [own_store]: this
    is the layer the split helpers ([wp_store__splitAtAndGet{Left,Right}_inv])
    and the id lookup ([wp_store__GetNode_total]) already speak, and the
    caller ([applyDeleteSpans], D2b) reassembles the store invariant around
    it. The specs are safety-shaped for now: the resources and the pool
    invariants survive and no type's model list moves (tombstoning and
    splitting are both model no-ops). The content half, "the covered chars
    are now deleted", is the delete-set milestone D2b, where the ghost set of
    [store/heap.v] starts recording it. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core.
From New.proof Require Import algebra.
From New.proof Require Import prelude.
From New.proof Require Import history.
From New.proof.id Require Import id.
From New.proof.item Require Import item.
From New.proof.ytype Require Import ytype.
From New.proof.sync_proof Require Import base mutex rwmutex rwmutex_guard.
From New.proof Require Import tok_set.
From iris.algebra Require Import auth gmap gset.
From iris.algebra.lib Require Import dfrac_agree.
From stdpp Require Import sorting.
Local Open Scope Z_scope.
From New.proof.store Require Import model value heap wp_private GetNode splitNode repair.

Section store_deleteRange.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.

Notation P := go_string.

Local Notation TId := (TypeId P).

Local Notation Op := (TId * @YjsOperation A)%type.

Local Notation Ev := (@Event Op).

Local Notation DocModel := (gmap TId (list (YjsItem A))).

Context {sync_pkg : sync.Assumptions}.

Notation seqUR := (authR (gmapUR loc (gsetUR (YjsItem A)))).

Context {seq_inG : inG Σ seqUR}.

Notation accUR := (authR (gsetUR YjsId)).

Context {acc_inG : inG Σ accUR}.

Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO (gmap loc type_state)))}.

(* ===== lemmas ============================================================= *)

(** [store.deleteNode]: tombstone ONE pool cell, given its heap location. The
    cell's own type is the only one that moves, and only by its Deleted bit:
    the model list [ty_arr] is untouched (a tombstone is a model no-op) and
    the type's [len] field drops by the run's length, which is exactly what
    [num_visible] does under [flip_cell]. An already-tombstoned cell takes
    the [Indexable = false] branch, and the statement still holds on the nose
    because [flip_cell] is the identity there. *)
Lemma wp_store__deleteNode (s : loc) (types : gmap loc type_state)
    (p : loc) (ts : type_state) (k : nat) (c : item_cell) :
  types !! p = Some ts ->
  ty_cells ts !! k = Some c ->
  {{{ is_pkg_init yjs ∗
      ([∗ map] q ↦ tq ∈ types,
          own_ytype_cells q (DfracOwn 1) (ty_cells tq) (ty_arr tq) ∗
          ⌜YjsArrInvariant (ty_arr tq)⌝) }}}
    s @! (go.PointerType yjs.store) @! "deleteNode" #(ic_loc c)
  {{{ RET #();
      ([∗ map] q ↦ tq ∈ (<[p := MkTypeState (<[k := flip_cell c]> (ty_cells ts)) (ty_arr ts)]> types),
          own_ytype_cells q (DfracOwn 1) (ty_cells tq) (ty_arr tq) ∗
          ⌜YjsArrInvariant (ty_arr tq)⌝) }}}.
Proof using Type*.
  move=> Hp Hck.
  iIntros (Φ) "(#Hpkg & Htypes) HΦ".
  (* open the owning type and borrow its node [k] *)
  iDestruct (big_sepM_delete _ _ p _ Hp with "Htypes") as "[[Hpc %Harrinv] Hrest]".
  iDestruct "Hpc" as (yt tl) "(Hparent & Hdll & %Hlen & %Hrepr & %Hcpar)".
  iDestruct (own_dll_update_gen (ty_cells ts) _ tl k c Hck with "Hdll") as (itemVal) "H".
  iDestruct "H" as "(%Hcloc & %Hcr & %Hcpar0 & %Hflags & %Hrun & %Hcontent & Hval & Hback)".
  have Hcparc : ic_parent c = p := Hcpar c (list_elem_of_lookup_2 _ _ _ Hck).
  (* the heap node's own [parent] field is this type's loc, so the [len]
     update the Go performs through [it.parent] lands on [p] *)
  rewrite Hcparc in Hcpar0.
  wp_method_call. wp_call. wp_call. wp_auto.
  wp_apply (wp_item__Indexable (ic_loc c) (DfracOwn 1) itemVal
              (flags_if_countable itemVal (ic_deleted c) Hflags) with "[$Hval]").
  iIntros "Hval".
  rewrite (flags_if_deleted itemVal (ic_deleted c) Hflags).
  destruct (ic_deleted c) eqn:Hd; simpl negb.
  - (* already tombstoned: nothing happens, and [flip_cell] is the identity *)
    wp_auto.
    iDestruct ("Hback" $! itemVal true eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                 eq_refl Hflags with "Hval") as "Hdll".
    have Hins : <[k := flip_cell c]> (ty_cells ts) = ty_cells ts.
    { have -> : flip_cell c = c.
      { rewrite /flip_cell -Hd. by destruct c. }
      apply list_insert_id; exact Hck. }
    iApply "HΦ".
    iEval (rewrite big_sepM_insert_delete).
    iSplitR "Hrest"; last iExact "Hrest".
    simpl. rewrite Hins. iSplitL; last (iPureIntro; exact Harrinv).
    iExists yt, tl. iFrame "Hparent Hdll". iPureIntro.
    split_and!; [exact Hlen | exact Hrepr | exact Hcpar].
  - (* visible: set the bit and shrink the type's [len] by the run length *)
    wp_auto.
    (* [wp_auto] has already performed the flag write, so the node is at
       [set_deleted itemVal] when [Len] is read (the content is untouched) *)
    (* the node's [parent] field is this type's loc, so the [len] load and
       store the Go performs through [it.parent] land on [Hparent] *)
    rewrite Hcpar0. wp_auto.
    wp_apply (wp_item__Len (ic_loc c) (DfracOwn 1) (set_deleted itemVal) with "[$Hval]").
    iIntros "Hval".
    (* the [len] store resolves [it.parent] again, so re-point it at [p] *)
    wp_auto. rewrite Hcpar0. wp_auto.
    iDestruct ("Hback" $! (set_deleted itemVal) true eq_refl eq_refl eq_refl eq_refl
                 eq_refl eq_refl Hcpar0 (set_deleted_flags itemVal false Hflags)
                 with "Hval") as "Hdll".
    have Hflip : MkItemCell (ic_loc c) (ic_run c) true (ic_parent c) = flip_cell c
      by reflexivity.
    rewrite Hflip.
    have Hrunlen : length (ic_run c) = length (itemVal.(yjs.item.content').(yjs.content.content')).
    { by rewrite -(length_fmap content (ic_run c)) Hcontent /toContent explode_length. }
    have Hnv : num_visible (<[k := flip_cell c]> (ty_cells ts))
             = (num_visible (ty_cells ts) - length (ic_run c))%nat
      := num_visible_flip_run (ty_cells ts) k c Hck Hd.
    have Hnvge : (length (ic_run c) <= num_visible (ty_cells ts))%nat.
    { rewrite /num_visible -(take_drop_middle (ty_cells ts) k c Hck) fmap_app list_sum_app
        fmap_cons /=. rewrite Hd. lia. }
    iApply "HΦ".
    iEval (rewrite big_sepM_insert_delete).
    iSplitR "Hrest"; last iExact "Hrest".
    simpl. iSplitL; last (iPureIntro; exact Harrinv).
    iExists (yt <| yjs.yType.len' := w64_word_instance.(word.sub) yt.(yjs.yType.len')
                     (W64 (length (itemVal.(yjs.item.content').(yjs.content.content')))) |>), tl.
    iFrame "Hparent Hdll". iPureIntro.
    split_and!.
    + simpl. rewrite Hlen Hnv -Hrunlen. word.
    + exact (cells_repr_update_run (ty_arr ts) (ty_cells ts) (ty_arr ts) k c (flip_cell c)
               Hck eq_refl Hrepr).
    + move=> c0 Hc0.
      apply list_elem_of_lookup_1 in Hc0 as [i0 Hi0].
      destruct (decide (i0 = k)) as [-> | Hne].
      * rewrite list_lookup_insert_eq in Hi0; last (apply lookup_lt_Some in Hck; exact Hck).
        injection Hi0 as <-. rewrite /flip_cell /= Hcparc //.
      * rewrite list_lookup_insert_ne in Hi0; [| congruence].
        exact (Hcpar c0 (list_elem_of_lookup_2 _ _ _ Hi0)).
Qed.

End store_deleteRange.
