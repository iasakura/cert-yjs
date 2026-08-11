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

(** Read-only borrow of one pool cell out of the type-map bundle: the node's
    heap struct with the two pins the loop reads it for (its id and its
    content length), and a wand giving the bundle back unchanged. The delete
    loop needs it to learn how far the node it just tombstoned extends. *)
Lemma types_cell_acc (types : gmap loc type_state) (p : loc) (ts : type_state)
    (k : nat) (c : item_cell) :
  types !! p = Some ts ->
  ty_cells ts !! k = Some c ->
  ([∗ map] q ↦ tq ∈ types,
      own_ytype_cells q (DfracOwn 1) (ty_cells tq) (ty_arr tq) ∗
      ⌜YjsArrInvariant (ty_arr tq)⌝) -∗
  ∃ itemVal : yjs.item.t,
    "%Haccid" ∷ ⌜item_id (run_head c) = toYjsId itemVal.(yjs.item.id')⌝ ∗
    "%Hacccontent" ∷ ⌜content <$> ic_run c = explode (toContent itemVal.(yjs.item.content'))⌝ ∗
    "Haccval" ∷ ic_loc c ↦ itemVal ∗
    "Haccback" ∷ (ic_loc c ↦ itemVal -∗
       ([∗ map] q ↦ tq ∈ types,
          own_ytype_cells q (DfracOwn 1) (ty_cells tq) (ty_arr tq) ∗
          ⌜YjsArrInvariant (ty_arr tq)⌝)).
Proof.
  move=> Hp Hck. iIntros "Htypes".
  iDestruct (big_sepM_delete _ _ p _ Hp with "Htypes") as "[[Hpc %Harrinv] Hrest]".
  iDestruct "Hpc" as (yt tl) "(Hparent & Hdll & %Hlen & %Hrepr & %Hcpar)".
  iDestruct (own_dll_acc (DfracOwn 1) (ty_cells ts) _ tl k c Hck with "Hdll") as "H".
  iNamed "H".
  iExists itemVal. iFrame "Hcval".
  iSplitR; first (iPureIntro; exact Hid).
  iSplitR; first (iPureIntro; exact Hcontent).
  iIntros "Hval".
  iDestruct ("Hback" with "Hval") as "Hdll".
  iApply big_sepM_delete; first exact Hp.
  iFrame "Hrest". iSplitL; last (iPureIntro; exact Harrinv).
  iExists yt, tl. iFrame "Hparent Hdll". iPureIntro.
  split_and!; [exact Hlen | exact Hrepr | exact Hcpar].
Qed.

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

(** [store.deleteRange]: tombstone the clock range [clock, clock+length) of
    [client]'s clock space. Each step looks the current char up
    ([wp_store__GetNode_total]); a char with no node is skipped (its struct
    has not arrived, and the caller re-applies the span later), and otherwise
    the covering node is cut down to exactly the part of the range that starts
    there, by the clean-start / clean-end splits [store.repair] resolves
    origins with, and tombstoned whole ([wp_store__deleteNode]).

    Safety-shaped, as the file header says: the pool invariants survive and
    no type's model list moves ([delete_types_facts]), which is what the
    caller needs to put the store invariant back together. That the covered
    chars are now DELETED is the content half, and it lands with the ghost
    delete set in D2b. *)
(* NB: the range length binder is [dlen], not [length]: the Go parameter is
   called [length], but that name is [list]'s length in Rocq and shadowing it
   breaks every [length (ic_run c)] below. *)
Lemma wp_store__deleteRange (s mref : loc) (types : gmap loc type_state)
    (client clock dlen : w64) :
  pool_invs types ->
  {{{ is_pkg_init yjs ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types ∗
      ([∗ map] p ↦ ts ∈ types,
          own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) }}}
    s @! (go.PointerType yjs.store) @! "deleteRange" #client #clock #dlen
  {{{ (types' : gmap loc type_state) (covered : bool), RET #covered;
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types' ∗
      ([∗ map] p ↦ ts ∈ types',
          own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) ∗
      ⌜pool_invs types'⌝ ∗ ⌜delete_types_facts types types'⌝ }}}.
Proof using Type*.
  move=> Hpool0.
  iIntros (Φ) "(#Hpkg & Hitemsf & Hitemmap & Htypes) HΦ".
  wp_method_call. wp_call. wp_call. wp_auto.
  iAssert (∃ (cur : w64) (cov : bool) (types_i : gmap loc type_state),
    "Hcur" ∷ cur_ptr ↦ cur ∗
    "Hcov" ∷ covered_ptr ↦ cov ∗
    "Hitemsf" ∷ (s .[(yjs.store.t), "items"]) ↦ mref ∗
    "Hitemmap" ∷ own_item_map mref (DfracOwn 1) types_i ∗
    "Htypes" ∷ ([∗ map] p ↦ ts ∈ types_i,
        own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
        ⌜YjsArrInvariant (ty_arr ts)⌝) ∗
    "%Hpool" ∷ ⌜pool_invs types_i⌝ ∗
    "%Hfacts" ∷ ⌜delete_types_facts types types_i⌝)%I
    with "[cur covered Hitemsf Hitemmap Htypes]" as "IH".
  { iExists clock, true, types. iFrame "cur covered Hitemsf Hitemmap Htypes". iPureIntro.
    split; [exact Hpool0 | exact (delete_types_facts_refl types)]. }
  wp_for "IH".
  wp_if_destruct; last first.
  { (* the range is exhausted: hand back the current pool *)
    iApply ("HΦ" $! types_i cov). iFrame "Hitemsf Hitemmap Htypes". iPureIntro.
    split; [exact Hpool | exact Hfacts]. }
  wp_apply wp_NewId.
  destruct Hpool as (Hfits & Hnodup & Hrangedisj & Horiginclk).
  wp_apply (wp_store__GetNode_total s mref (DfracOwn 1) _ types_i
              Hfits Hnodup Hrangedisj with "[$Hitemsf $Hitemmap $Htypes]").
  iIntros (nl found) "(Hitemsf & Hitemmap & Htypes & %Hres)".
  wp_auto.
  destruct found; last first.
  { (* no node covers this char: skip it *)
    wp_auto. wp_for_post.
    iFrame "HΦ s client end".
    iExists (w64_word_instance.(word.add) cur (W64 1)), false, types_i.
    iFrame "Hcur Hcov Hitemsf Hitemmap Htypes". iPureIntro.
    split; [split_and!; assumption | exact Hfacts]. }
  (* the covering cell, from the lookup *)
  destruct Hres as (cw & Hcwmem & Hcwcc & Hcwle & Hcwlt & Hcwloc).
  have Hpool_i : pool_invs types_i by split_and!; assumption.
  wp_auto.
  wp_apply wp_NewId.
  wp_apply (wp_store__splitAtAndGetRight_inv s mref _ types_i cw
              Hcwmem Hcwcc Hcwle Hcwlt
              ltac:(split_and!; assumption)
              with "[$Hitemsf $Hitemmap $Htypes]").
  iIntros (rl types1) "(Hitemsf & Hitemmap & Htypes & %Hpool1 & %Hstep1 & %HcR)".
  destruct HcR as (cR & HcRmem & HcRloc & HcRcc & HcRclk & HcRpar).
  have HcRmem1 := HcRmem.
  have HcRccl : cell_client cR = client := HcRcc.
  wp_auto.
  (* locate the node in its type so its extent can be read *)
  apply all_cells_elem_of in HcRmem as (pR & tsR & HpR & HcRts).
  apply list_elem_of_lookup_1 in HcRts as (kR & HkR).
  iDestruct (types_cell_acc types1 pR tsR kR cR HpR HkR with "Htypes") as (ivR) "H".
  iNamed "H".
  rewrite -HcRloc.
  wp_auto.
  wp_apply (wp_item__Len (ic_loc cR) (DfracOwn 1) ivR with "[$Haccval]").
  iIntros "Haccval".
  iDestruct ("Haccback" with "Haccval") as "Htypes".
  (* the heap fields the loop just read, in cell terms *)
  have HivRclk : ivR.(yjs.item.id').(yjs.id.clock') = cell_clock cR.
  { rewrite /cell_clock Haccid /toYjsId /=. word. }
  have HivRlen : length (ivR.(yjs.item.content').(yjs.content.content'))
               = length (ic_run cR).
  { by rewrite -(length_fmap content (ic_run cR)) Hacccontent /toContent explode_length. }
  wp_auto.
  (* The node starts exactly at [cur]. Kept at the [uint.Z] level on purpose:
     [wp_if_destruct]'s bare [subst] would consume a [cell_clock cR = cur]
     equation and take the hypothesis with it. *)
  have HcRcurZ : (uint.Z (cell_clock cR) = uint.Z cur)%Z.
  { move: HcRclk. rewrite /= => Hz. word. }
  have Hcurlt : (uint.Z cur < uint.Z (w64_word_instance.(word.add) clock dlen))%Z by word.
  have HivRclkZ : (uint.Z (ivR.(yjs.item.id').(yjs.id.clock')) = uint.Z cur)%Z
    by rewrite HivRclk; word.
  (* [wp_if_destruct] names the branch condition [l0] / [n0] here (its bare
     subst renamed the [Heqb] the other branches get) *)
  wp_if_destruct.
  - (* the range stops inside this node: cut it at the range's last char *)
    (* [wp_if_destruct]'s bare subst has replaced [client] by [cell_client cR]
       (it consumed the [cell_client cR = client] equation), so the id the
       clean-end split is called with is spelled that way here. *)
    wp_apply wp_NewId.
    have Hfitsc := proj1 Hpool1 cR HcRmem1.
    have HcLle : (uint.Z (cell_clock cR)
                  <= uint.Z (w64_word_instance.(word.sub)
                               (w64_word_instance.(word.add) clock dlen) (W64 1)))%Z
      by word.
    have HcLlt : (uint.Z (w64_word_instance.(word.sub)
                            (w64_word_instance.(word.add) clock dlen) (W64 1))
                  < uint.Z (cell_clock cR) + Z.of_nat (length (ic_run cR)))%Z.
    { move: l0. rewrite HivRlen. word. }
    wp_apply (wp_store__splitAtAndGetLeft_inv s mref
                {| yjs.id.clientId' := cell_client cR;
                   yjs.id.clock' := w64_word_instance.(word.sub)
                     (w64_word_instance.(word.add) clock dlen) (W64 1) |}
                types1 cR HcRmem1 eq_refl HcLle HcLlt Hpool1
                with "[$Hitemsf $Hitemmap $Htypes]").
    iIntros (types2) "(Hitemsf & Hitemmap & Htypes & %Hpool2 & %Hstep2 & %HcL)".
    destruct HcL as (cL & HcLmem & HcLloc & HcLcc & HcLend & HcLpar).
    wp_auto.
    (* tombstone the truncated node *)
    apply all_cells_elem_of in HcLmem as (pL & tsL & HpL & HcLts).
    apply list_elem_of_lookup_1 in HcLts as (kL & HkL).
    rewrite -HcLloc.
    wp_apply (wp_store__deleteNode s types2 pL tsL kL cL HpL HkL with "[$Htypes]").
    iIntros "Htypes".
    set (types3 := <[pL := MkTypeState (<[kL := flip_cell cL]> (ty_cells tsL)) (ty_arr tsL)]> types2).
    iDestruct (own_item_map_kp_perm mref (DfracOwn 1) types2 types3
                 (locs_run_perm_kp _ _ (flip_locs_run_perm types2 pL tsL kL cL HpL HkL))
                 with "Hitemmap") as "Hitemmap".
    wp_auto. wp_for_post.
    iFrame "HΦ s client end".
    iExists (w64_word_instance.(word.add) clock dlen), cov, types3.
    iFrame "Hcur Hcov Hitemsf Hitemmap Htypes". iPureIntro. split.
    + exact (pool_invs_flip types2 pL tsL kL cL HpL HkL Hpool2).
    + eapply delete_types_facts_trans; first exact Hfacts.
      eapply delete_types_facts_trans;
        first exact (delete_types_facts_of_split _ _ _ Hstep1).
      eapply delete_types_facts_trans;
        first exact (delete_types_facts_of_split _ _ _ Hstep2).
      exact (delete_types_facts_of_flip types2 pL tsL _ HpL).
  - (* the node ends inside the range: tombstone it whole *)
    wp_apply (wp_store__deleteNode s types1 pR tsR kR cR HpR HkR with "[$Htypes]").
    iIntros "Htypes".
    set (types3 := <[pR := MkTypeState (<[kR := flip_cell cR]> (ty_cells tsR)) (ty_arr tsR)]> types1).
    iDestruct (own_item_map_kp_perm mref (DfracOwn 1) types1 types3
                 (locs_run_perm_kp _ _ (flip_locs_run_perm types1 pR tsR kR cR HpR HkR))
                 with "Hitemmap") as "Hitemmap".
    wp_auto. wp_for_post.
    iFrame "HΦ s client end".
    iExists (w64_word_instance.(word.add) (ivR.(yjs.item.id').(yjs.id.clock'))
               (W64 (length (ivR.(yjs.item.content').(yjs.content.content'))))), cov, types3.
    iFrame "Hcur Hcov Hitemsf Hitemmap Htypes". iPureIntro. split.
    + exact (pool_invs_flip types1 pR tsR kR cR HpR HkR Hpool1).
    + eapply delete_types_facts_trans; first exact Hfacts.
      eapply delete_types_facts_trans;
        first exact (delete_types_facts_of_split _ _ _ Hstep1).
      exact (delete_types_facts_of_flip types1 pR tsR _ HpR).
Qed.

(** [store.applyDeleteSpans]: apply a batch of decoded spans on top of the
    buffered ones and keep the ones that did not land in full. Safety-shaped
    like [deleteRange]: the pool survives with its invariants and no type's
    model list moves; which spans stay buffered is existential (pinning it
    needs the per-char coverage the delete set records, D3).

    The buffer's own spans and the batch's are both consumed as VALUES (a
    span is a triple of machine words), so the batch comes back untouched
    and the new buffer is a fresh slice. *)
Lemma wp_store__applyDeleteSpans (s mref : loc) (types : gmap loc type_state)
    (pdel_sl sp_sl : slice.t) (dq : dfrac)
    (pdel spans : list yjs.deleteSpan.t) :
  pool_invs types ->
  {{{ is_pkg_init yjs ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types ∗
      ([∗ map] p ↦ ts ∈ types,
          own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) ∗
      (s .[(yjs.store.t), "pendingDeletes"]) ↦ pdel_sl ∗
      own_delete_spans pdel_sl (DfracOwn 1) pdel ∗
      own_delete_spans sp_sl dq spans }}}
    s @! (go.PointerType yjs.store) @! "applyDeleteSpans" #sp_sl
  {{{ (types' : gmap loc type_state) (pdel_sl' : slice.t)
      (rest : list yjs.deleteSpan.t), RET #();
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types' ∗
      ([∗ map] p ↦ ts ∈ types',
          own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) ∗
      (s .[(yjs.store.t), "pendingDeletes"]) ↦ pdel_sl' ∗
      own_delete_spans pdel_sl' (DfracOwn 1) rest ∗
      own_delete_spans sp_sl dq spans ∗
      ⌜pool_invs types'⌝ ∗ ⌜delete_types_facts types types'⌝ }}}.
Proof using Type*.
  move=> Hpool0.
  iIntros (Φ) "(#Hpkg & Hitemsf & Hitemmap & Htypes & Hpddelf & Hpddel & Hsp) HΦ".
  iNamed "Hpddel". iDestruct "Hsp" as "[Hspsl2 Hspcap2]".
  wp_method_call. wp_call. wp_call. wp_auto.
  (* ---- loop 1: [all] accumulates the buffer plus the batch ---- *)
  iAssert (∃ (i : w64) (all_sl : slice.t),
    "Hi" ∷ i_ptr ↦ i ∗
    "Hallp" ∷ all_ptr ↦ all_sl ∗
    "Hall" ∷ all_sl ↦* (pdel ++ take (uint.nat i) spans) ∗
    "Hallcap" ∷ own_slice_cap yjs.deleteSpan.t all_sl (DfracOwn 1) ∗
    "Hspsl2" ∷ sp_sl ↦*{dq} spans ∗
    "%Hib" ∷ ⌜(uint.nat i <= length spans)%nat⌝)%I
    with "[i all Hspsl Hspcap Hspsl2]" as "IH".
  { iExists (W64 0), pdel_sl.
    rewrite (_ : uint.nat (W64 0) = 0%nat); last word.
    rewrite take_0 app_nil_r.
    iFrame "i all Hspsl Hspcap Hspsl2". iPureIntro. lia. }
  wp_for "IH".
  iDestruct (own_slice_len with "Hspsl2") as %[Hsplen _].
  wp_if_destruct; last first.
  { (* the batch is copied: [all] is the buffer plus the batch. Loop 2
       applies each span and keeps the ones that did not land. *)
    have Hiend : uint.nat i = length spans by word.
    rewrite Hiend take_ge; last lia.
    wp_apply wp_slice_literal. iSplitR; first done.
    iIntros "%rsl0 [Hrest Hrestcap]". wp_auto.
    iAssert (∃ (j : w64) (rest_sl : slice.t) (rest : list yjs.deleteSpan.t)
               (types_j : gmap loc type_state),
      "Hj" ∷ i_ptr ↦ j ∗
      "Hrestp" ∷ rest_ptr ↦ rest_sl ∗
      "Hrest" ∷ rest_sl ↦* rest ∗
      "Hrestcap" ∷ own_slice_cap yjs.deleteSpan.t rest_sl (DfracOwn 1) ∗
      "Hall" ∷ all_sl ↦* (pdel ++ spans) ∗
      "Hitemsf" ∷ (s .[(yjs.store.t), "items"]) ↦ mref ∗
      "Hitemmap" ∷ own_item_map mref (DfracOwn 1) types_j ∗
      "Htypes" ∷ ([∗ map] p ↦ ts ∈ types_j,
          own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) ∗
      "%Hjb" ∷ ⌜(uint.nat j <= length (pdel ++ spans))%nat⌝ ∗
      "%Hpoolj" ∷ ⌜pool_invs types_j⌝ ∗
      "%Hfactsj" ∷ ⌜delete_types_facts types types_j⌝)%I
      with "[i rest Hrest Hrestcap Hall Hitemsf Hitemmap Htypes]" as "IH".
    { iExists (W64 0), _, [], types.
      iFrame "i rest Hrest Hrestcap Hall Hitemsf Hitemmap Htypes". iPureIntro.
      split_and!; [word | exact Hpool0 | exact (delete_types_facts_refl types)]. }
    wp_for "IH".
    iDestruct (own_slice_len with "Hall") as %[Halllen _].
    wp_if_destruct; last first.
    { (* every span has been retried: install the leftover as the new buffer *)
      iApply ("HΦ" $! types_j rest_sl rest).
      iFrame "Hitemsf Hitemmap Htypes Hpddelf Hrest Hrestcap Hspsl2 Hspcap2".
      iPureIntro. split_and!; [exact Hpoolj | exact Hfactsj]. }
    (* retry one span *)
    destruct ((pdel ++ spans) !! uint.nat j) as [sp|] eqn:Hsp; last first.
    { exfalso. apply lookup_ge_None in Hsp. word. }
    iDestruct (own_slice_elem_acc (sint.Z j) sp all_sl (DfracOwn 1) _ with "Hall")
      as "[Hel Hgive]".
    { word. }
    { replace (Z.to_nat (sint.Z j)) with (uint.nat j) by word. exact Hsp. }
    rewrite decide_True; last word.
    wp_auto.
    iDestruct ("Hgive" with "Hel") as "Hall".
    rewrite list_insert_id; last first.
    { replace (Z.to_nat (sint.Z j)) with (uint.nat j) by word. exact Hsp. }
    wp_apply (wp_store__deleteRange s mref types_j _ _ _ Hpoolj
                with "[$Hitemsf $Hitemmap $Htypes]").
    iIntros (types_j' cov) "(Hitemsf & Hitemmap & Htypes & %Hpoolj' & %Hfactsj')".
    have Hfactsj'' : delete_types_facts types types_j'
      := delete_types_facts_trans _ _ _ Hfactsj Hfactsj'.
    destruct cov.
    - (* the span landed in full: drop it *)
      wp_auto. wp_for_post.
      iFrame "HΦ s Hpddelf Hspsl2 Hspcap2 Hallp Hallcap".
      iExists (w64_word_instance.(word.add) j (W64 1)), rest_sl, rest, types_j'.
      iFrame "Hj Hrestp Hrest Hrestcap Hall Hitemsf Hitemmap Htypes".
      iPureIntro. split_and!; [word | exact Hpoolj' | exact Hfactsj''].
    - (* not covered yet: keep it buffered *)
      wp_auto.
      wp_apply wp_slice_literal. iSplitR; first done.
      iIntros "%ssl [Hssl _]". wp_auto.
      wp_apply (wp_slice_append with "[$Hrest $Hrestcap $Hssl]").
      iIntros (rest_sl') "(Hrest & Hrestcap & _)".
      wp_auto. wp_for_post.
      iFrame "HΦ s Hpddelf Hspsl2 Hspcap2 Hallp Hallcap".
      iExists (w64_word_instance.(word.add) j (W64 1)), rest_sl', (rest ++ [sp]), types_j'.
      iFrame "Hj Hrestp Hrest Hrestcap Hall Hitemsf Hitemmap Htypes".
      iPureIntro. split_and!; [word | exact Hpoolj' | exact Hfactsj'']. }
  (* copy one span into [all] *)
  destruct (spans !! uint.nat i) as [sp|] eqn:Hsp; last first.
  { exfalso. apply lookup_ge_None in Hsp. word. }
  iDestruct (own_slice_elem_acc (sint.Z i) sp sp_sl dq _ with "Hspsl2") as "[Hel Hgive]".
  { word. }
  { replace (Z.to_nat (sint.Z i)) with (uint.nat i) by word. exact Hsp. }
  rewrite decide_True; last word.
  wp_auto.
  iDestruct ("Hgive" with "Hel") as "Hspsl2".
  rewrite list_insert_id; last first.
  { replace (Z.to_nat (sint.Z i)) with (uint.nat i) by word. exact Hsp. }
  wp_apply wp_slice_literal. iSplitR; first done.
  iIntros "%sl0 [Hsl0 _]". wp_auto.
  wp_apply (wp_slice_append with "[$Hall $Hallcap $Hsl0]").
  iIntros (all_sl') "(Hall & Hallcap & _)".
  wp_auto. wp_for_post.
  iFrame "HΦ s spans Hitemsf Hitemmap Htypes Hpddelf Hspcap2".
  iExists (w64_word_instance.(word.add) i (W64 1)), all_sl'.
  iFrame "Hi Hallp Hallcap Hspsl2".
  rewrite (_ : uint.nat (w64_word_instance.(word.add) i (W64 1))
             = S (uint.nat i)); last word.
  rewrite (take_S_r spans (uint.nat i) sp Hsp) app_assoc.
  iFrame "Hall". iPureIntro. word.
Qed.

End store_deleteRange.
