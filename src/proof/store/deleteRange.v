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

    The pool invariants survive and no type's model list moves
    ([delete_types_facts]), which is what the caller needs to put the store
    invariant back together. On top of that the loop REPORTS its coverage:
    when it returns [true], every id of the span sits in a cell that is now
    tombstoned. That is the content half, and it is what lets the caller mint
    an [is_delete_set_lb] certificate through [own_delete_set_grow], whose obligation
    [delete_set_tombstoned_char_ids] discharges from the pool invariants.

    Nothing is claimed about a span whose clock range WRAPS. Spans come off
    the wire, so a peer can send one; the Go loop's [cur < clock + length]
    test then fails immediately and the loop tombstones nothing, which is
    exactly what the guarded postcondition says. *)
(* NB: the two range binders are [dclock] / [dlen], not [clock] / [length]:
   the Go parameters are called [clock] and [length], but those are [YjsId]'s
   clock projection and [list]'s length in Rocq, and shadowing them breaks
   every [clock (item_id ...)] / [length (ic_run c)] below. *)
Lemma wp_store__deleteRange (s mref : loc) (types : gmap loc type_state)
    (client dclock dlen : w64) :
  pool_invs types ->
  {{{ is_pkg_init yjs ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types ∗
      ([∗ map] p ↦ ts ∈ types,
          own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) }}}
    s @! (go.PointerType yjs.store) @! "deleteRange" #client #dclock #dlen
  {{{ (types' : gmap loc type_state) (covered : bool), RET #covered;
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types' ∗
      ([∗ map] p ↦ ts ∈ types',
          own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) ∗
      ⌜pool_invs types'⌝ ∗ ⌜delete_types_facts types types'⌝ ∗
      ⌜range_no_overflow dclock dlen -> covered = true ->
         ids_tombstoned (range_ids client dclock dlen) (all_cells types')⌝ }}}.
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
    "%Hcurb" ∷ ⌜(uint.Z dclock <= uint.Z cur)%Z⌝ ∗
    "%Hcovj" ∷ ⌜range_no_overflow dclock dlen -> cov = true ->
        ids_tombstoned (range_ids client dclock (w64_word_instance.(word.sub) cur dclock))
                       (all_cells types_i)⌝ ∗
    "%Hfacts" ∷ ⌜delete_types_facts types types_i⌝)%I
    with "[cur covered Hitemsf Hitemmap Htypes]" as "IH".
  { iExists dclock, true, types. iFrame "cur covered Hitemsf Hitemmap Htypes". iPureIntro.
    split_and!; [exact Hpool0 | lia | | exact (delete_types_facts_refl types)].
    (* nothing is covered yet: the span from [dclock] to [dclock] is empty *)
    move=> _ _ i Hi. exfalso. move: Hi.
    rewrite range_ids_elem /=.
    have -> : uint.nat (w64_word_instance.(word.sub) dclock dclock) = 0%nat by word.
    lia. }
  wp_for "IH".
  wp_if_destruct; last first.
  { (* the range is exhausted: hand back the current pool *)
    iApply ("HΦ" $! types_i cov). iFrame "Hitemsf Hitemmap Htypes". iPureIntro.
    split_and!; [exact Hpool | exact Hfacts |].
    (* the loop stopped at [dclock + dlen], so its record covers the whole span *)
    move=> Hnw Hcov i Hi. apply (Hcovj Hnw Hcov i).
    move: Hi. rewrite !range_ids_elem.
    have -> : uint.nat (w64_word_instance.(word.sub) cur dclock)
            = (uint.nat cur - uint.nat dclock)%nat by word.
    move: n Hnw. rewrite /range_no_overflow /= => Hstop Hnw2. word. }
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
    split_and!; [split_and!; assumption | word | by move=> _ | exact Hfacts]. }
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
  iDestruct (types_runs_wf2 with "Htypes") as %Hrunwf1.
  iDestruct (types_cells_id_bounds2 with "Htypes") as %Hbnds1.
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
  have Hcurlt : (uint.Z cur < uint.Z (w64_word_instance.(word.add) dclock dlen))%Z by word.
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
                               (w64_word_instance.(word.add) dclock dlen) (W64 1)))%Z
      by word.
    have HcLlt : (uint.Z (w64_word_instance.(word.sub)
                            (w64_word_instance.(word.add) dclock dlen) (W64 1))
                  < uint.Z (cell_clock cR) + Z.of_nat (length (ic_run cR)))%Z.
    { move: l0. rewrite HivRlen. word. }
    wp_apply (wp_store__splitAtAndGetLeft_inv s mref
                {| yjs.id.clientId' := cell_client cR;
                   yjs.id.clock' := w64_word_instance.(word.sub)
                     (w64_word_instance.(word.add) dclock dlen) (W64 1) |}
                types1 cR HcRmem1 eq_refl HcLle HcLlt Hpool1
                with "[$Hitemsf $Hitemmap $Htypes]").
    iIntros (types2) "(Hitemsf & Hitemmap & Htypes & %Hpool2 & %Hstep2 & %HcL)".
    iDestruct (types_runs_wf2 with "Htypes") as %Hrunwf2.
    destruct HcL as (cL & HcLmem & HcLloc & HcLcc & HcLend & HcLpar & HcLstart).
    have HcLmem1 := HcLmem.
    iDestruct (types_cells_id_bounds2 with "Htypes") as %Hbnds2.
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
    iExists (w64_word_instance.(word.add) dclock dlen), cov, types3.
    iFrame "Hcur Hcov Hitemsf Hitemmap Htypes".
    have Hdk3 : dead_chars_kept types_i types3.
    { eapply dead_chars_kept_trans;
        first exact (proj1 (proj2 (proj2 (proj2 (delete_types_facts_of_split _ _ _ Hstep1))))).
      eapply dead_chars_kept_trans;
        first exact (proj1 (proj2 (proj2 (proj2 (delete_types_facts_of_split _ _ _ Hstep2))))).
      exact (dead_chars_kept_flip types2 pL tsL kL cL HpL HkL). }
    have HcLwf : run_wf (ic_run cL) := Hrunwf2 cL HcLmem1.
    iPureIntro. split_and!.
    + exact (pool_invs_flip types2 pL tsL kL cL HpL HkL Hpool2).
    + word.
    + (* the record grows by the truncated node's chars, which reach exactly
         the end of the requested range *)
      move=> Hnw Hcov i Hi.
      move: Hi. rewrite range_ids_elem /=.
      move=> [Hcid [Hlo Hhi]].
      destruct (decide (clock i < uint.nat cur)%nat) as [Hold | Hnew].
      * destruct (Hcovj Hnw Hcov i) as (c0 & Hc0 & Hdel0 & Hy0).
        { rewrite range_ids_elem /=. split_and!; [exact Hcid | | ].
          - move: Hlo. rewrite /=. word.
          - word. }
        rewrite /char_ids elem_of_list_to_set list_elem_of_fmap in Hy0.
        destruct Hy0 as (y & Hidy & Hy).
        destruct (Hdk3 c0 Hc0 Hdel0 y Hy) as (c1 & Hc1 & Hdel1 & Hy1).
        exists c1. split_and!; [exact Hc1 | exact Hdel1 |].
        rewrite /char_ids elem_of_list_to_set list_elem_of_fmap.
        exists y. split; [exact Hidy | exact Hy1].
      * have HcLclkZ : (uint.Z (cell_clock cL) = uint.Z cur)%Z
          by rewrite HcLstart HcRcurZ.
        have HcLfits : cell_fits cL := proj1 Hpool2 cL HcLmem1.
        have Hheadcl : clientId (item_id (run_head cL)) = uint.nat (cell_client cR).
        { have Hb := proj1 (Hbnds2 cL HcLmem1).
          move: HcLcc. rewrite /cell_client /=. word. }
        have Hheadclk : clock (item_id (run_head cL)) = uint.nat cur.
        { have Hbk := proj2 (Hbnds2 cL HcLmem1).
          move: HcLclkZ. rewrite /cell_clock. word. }
        exists (flip_cell cL). split_and!.
        -- rewrite /types3.
           destruct (flip_pool_perm types2 pL tsL kL cL HpL HkL) as (rest & _ & Hnewp).
           rewrite Hnewp. apply list_elem_of_here.
        -- done.
        -- rewrite /flip_cell /=.
           apply (run_wf_char_id_mem cL i HcLwf).
           ++ rewrite Hheadcl Hcid //.
           ++ rewrite Hheadclk. split; first lia.
              move: HcLend HcLclkZ Hhi Hnw. rewrite /cell_clock /=. word.
    + eapply delete_types_facts_trans; first exact Hfacts.
      eapply delete_types_facts_trans;
        first exact (delete_types_facts_of_split _ _ _ Hstep1).
      eapply delete_types_facts_trans;
        first exact (delete_types_facts_of_split _ _ _ Hstep2).
      exact (delete_types_facts_of_flip types2 pL tsL kL cL HpL HkL).
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
    iFrame "Hcur Hcov Hitemsf Hitemmap Htypes".
    have Hdk3 : dead_chars_kept types_i types3.
    { eapply dead_chars_kept_trans;
        first exact (proj1 (proj2 (proj2 (proj2 (delete_types_facts_of_split _ _ _ Hstep1))))).
      exact (dead_chars_kept_flip types1 pR tsR kR cR HpR HkR). }
    have Hcrun : run_wf (ic_run cR) := Hrunwf1 cR HcRmem1.
    have Hfits1 : cell_fits cR := proj1 Hpool1 cR HcRmem1.
    iPureIntro. split_and!.
    + exact (pool_invs_flip types1 pR tsR kR cR HpR HkR Hpool1).
    + move: Hcurb HivRclk HivRlen Hfits1. rewrite /cell_fits. word.
    + (* the record grows by exactly this node's chars *)
      move=> Hnw Hcov i Hi.
      move: Hi. rewrite range_ids_elem /=.
      have Hcurstep : uint.nat (w64_word_instance.(word.add)
            (ivR.(yjs.item.id').(yjs.id.clock'))
            (W64 (length (ivR.(yjs.item.content').(yjs.content.content'))))) 
          = (uint.nat cur + length (ic_run cR))%nat.
      { rewrite HivRlen. move: HivRclkZ HivRclk Hfits1. rewrite /cell_fits. word. }
      move=> [Hcid [Hlo Hhi]].
      destruct (decide (clock i < uint.nat cur)%nat) as [Hold | Hnew].
      * (* already recorded: transported across this iteration's surgeries *)
        destruct (Hcovj Hnw Hcov i) as (c0 & Hc0 & Hdel0 & Hy0).
        { rewrite range_ids_elem /=. split_and!; [exact Hcid | | ].
          - move: Hlo. rewrite /=. word.
          - word. }
        rewrite /char_ids elem_of_list_to_set list_elem_of_fmap in Hy0.
        destruct Hy0 as (y & Hidy & Hy).
        destruct (Hdk3 c0 Hc0 Hdel0 y Hy) as (c1 & Hc1 & Hdel1 & Hy1).
        exists c1. split_and!; [exact Hc1 | exact Hdel1 |].
        rewrite /char_ids elem_of_list_to_set list_elem_of_fmap.
        exists y. split; [exact Hidy | exact Hy1].
      * (* freshly covered: the node just tombstoned holds it *)
        have Hheadcl : clientId (item_id (run_head cR)) = uint.nat (cell_client cR).
        { have Hb := proj1 (Hbnds1 cR HcRmem1). rewrite /cell_client. word. }
        have Hheadclk : clock (item_id (run_head cR)) = uint.nat cur.
        { have Hbk := proj2 (Hbnds1 cR HcRmem1).
          move: HcRcurZ. rewrite /cell_clock. word. }
        exists (flip_cell cR). split_and!.
        -- rewrite /types3.
           destruct (flip_pool_perm types1 pR tsR kR cR HpR HkR) as (rest & _ & Hnewp).
           rewrite Hnewp. apply list_elem_of_here.
        -- done.
        -- rewrite /flip_cell /=.
           apply (run_wf_char_id_mem cR i Hcrun).
           ++ rewrite Hheadcl Hcid //.
           ++ rewrite Hheadclk. split; first lia.
              move: Hhi Hcurstep Hcurb Hnw. word.
    + eapply delete_types_facts_trans; first exact Hfacts.
      eapply delete_types_facts_trans;
        first exact (delete_types_facts_of_split _ _ _ Hstep1).
      exact (delete_types_facts_of_flip types1 pR tsR kR cR HpR HkR).
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
    (pdel spans : list delete_span) :
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
      (rest : list delete_span), RET #();
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types' ∗
      ([∗ map] p ↦ ts ∈ types',
          own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) ∗
      (s .[(yjs.store.t), "pendingDeletes"]) ↦ pdel_sl' ∗
      own_delete_spans pdel_sl' (DfracOwn 1) rest ∗
      own_delete_spans sp_sl dq spans ∗
      ⌜pool_invs types'⌝ ∗ ⌜delete_types_facts types types'⌝ ∗
      ⌜∃ D : gset YjsId,
         ids_tombstoned D (all_cells types') ∧
         (∀ sp, sp ∈ pdel ++ spans -> sp ∉ rest -> delete_span_no_overflow sp ->
            delete_span_ids sp ⊆ D)⌝ }}}.
Proof using Type*.
  move=> Hpool0.
  iIntros (Φ) "(#Hpkg & Hitemsf & Hitemmap & Htypes & Hpddelf & Hpddel & Hsp) HΦ".
  (* open the pure model: the decoded structs live only inside this proof *)
  iNamed "Hpddel".
  iDestruct "Hsp" as (spans_vs) "(Hspsl2 & Hspcap2 & %Hspansmodel)".
  rename vs into pdel_vs. rename Hspmodel into Hpdelmodel.
  (* the pure lists ARE the denotations of the concrete ones; substituting
     them away keeps the rest of the proof over the structs the loop walks *)
  subst pdel spans.
  wp_method_call. wp_call. wp_call. wp_auto.
  (* ---- loop 1: [all] accumulates the buffer plus the batch ---- *)
  iAssert (∃ (i : w64) (all_sl : slice.t),
    "Hi" ∷ i_ptr ↦ i ∗
    "Hallp" ∷ all_ptr ↦ all_sl ∗
    "Hall" ∷ all_sl ↦* (pdel_vs ++ take (uint.nat i) spans_vs) ∗
    "Hallcap" ∷ own_slice_cap yjs.deleteSpan.t all_sl (DfracOwn 1) ∗
    "Hspsl2" ∷ sp_sl ↦*{dq} spans_vs ∗
    "%Hib" ∷ ⌜(uint.nat i <= length spans_vs)%nat⌝)%I
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
    have Hiend : uint.nat i = length spans_vs by word.
    rewrite Hiend take_ge; last lia.
    wp_apply wp_slice_literal. iSplitR; first done.
    iIntros "%rsl0 [Hrest Hrestcap]". wp_auto.
    iAssert (∃ (j : w64) (rest_sl : slice.t) (rest_vs : list yjs.deleteSpan.t)
               (types_j : gmap loc type_state) (Dj : gset YjsId),
      "Hj" ∷ i_ptr ↦ j ∗
      "Hrestp" ∷ rest_ptr ↦ rest_sl ∗
      "Hrest" ∷ rest_sl ↦* rest_vs ∗
      "Hrestcap" ∷ own_slice_cap yjs.deleteSpan.t rest_sl (DfracOwn 1) ∗
      "Hall" ∷ all_sl ↦* (pdel_vs ++ spans_vs) ∗
      "Hitemsf" ∷ (s .[(yjs.store.t), "items"]) ↦ mref ∗
      "Hitemmap" ∷ own_item_map mref (DfracOwn 1) types_j ∗
      "Htypes" ∷ ([∗ map] p ↦ ts ∈ types_j,
          own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) ∗
      "%Hjb" ∷ ⌜(uint.nat j <= length (pdel_vs ++ spans_vs))%nat⌝ ∗
      "%Hpoolj" ∷ ⌜pool_invs types_j⌝ ∗
      "%HdelDj" ∷ ⌜ids_tombstoned Dj (all_cells types_j)⌝ ∗
      "%HspanDj" ∷ ⌜∀ sp, sp ∈ take (uint.nat j) (pdel_vs ++ spans_vs) -> sp ∉ rest_vs ->
          delete_span_no_overflow (delete_span_of_val sp) -> delete_span_ids (delete_span_of_val sp) ⊆ Dj⌝ ∗
      "%Hfactsj" ∷ ⌜delete_types_facts types types_j⌝)%I
      with "[i rest Hrest Hrestcap Hall Hitemsf Hitemmap Htypes]" as "IH".
    { iExists (W64 0), _, [], types, (∅ : gset YjsId).
      iFrame "i rest Hrest Hrestcap Hall Hitemsf Hitemmap Htypes". iPureIntro.
      split_and!; [word | exact Hpool0 | | | exact (delete_types_facts_refl types)].
      - move=> i0 Hi0. exfalso. set_solver.
      - move=> sp0 Hsp0. exfalso. move: Hsp0.
        rewrite (_ : uint.nat (W64 0) = 0%nat); last word.
        rewrite take_0. apply elem_of_nil. }
    wp_for "IH".
    iDestruct (own_slice_len with "Hall") as %[Halllen _].
    wp_if_destruct; last first.
    { (* every span has been retried: install the leftover as the new buffer,
         and hand the whole thing back over the PURE model *)
      iApply ("HΦ" $! types_j rest_sl (delete_span_of_val <$> rest_vs)).
      iFrame "Hitemsf Hitemmap Htypes Hpddelf".
      iSplitL "Hrest Hrestcap"; first (iExists rest_vs; by iFrame "Hrest Hrestcap").
      iSplitL "Hspsl2 Hspcap2"; first (iExists spans_vs; by iFrame "Hspsl2 Hspcap2").
      iPureIntro. split_and!; [exact Hpoolj | exact Hfactsj |].
      exists Dj. split; first exact HdelDj.
      (* transport the record from the decoded structs to the spans they
         denote: the denotation is injective, so "not among the leftover"
         survives it *)
      move=> sp Hsp Hnotrest Hnw.
      rewrite -fmap_app in Hsp.
      apply list_elem_of_fmap in Hsp as (v & -> & Hv).
      apply (HspanDj v); [by rewrite take_ge; last word | | exact Hnw].
      move=> Hin. apply Hnotrest. apply list_elem_of_fmap. by exists v. }
    (* retry one span *)
    destruct ((pdel_vs ++ spans_vs) !! uint.nat j) as [sp|] eqn:Hsp; last first.
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
    iIntros (types_j' cov) "(Hitemsf & Hitemmap & Htypes & %Hpoolj' & %Hfactsj' & %Hcovj')".
    have Hfactsj'' : delete_types_facts types types_j'
      := delete_types_facts_trans _ _ _ Hfactsj Hfactsj'.
    (* the tombstone record of everything applied so far moves to the new pool *)
    have Hdkj' : dead_chars_kept types_j types_j'
      := proj1 (proj2 (proj2 (proj2 Hfactsj'))).
    have Hmove : ∀ D : gset YjsId,
        ids_tombstoned D (all_cells types_j) -> ids_tombstoned D (all_cells types_j').
    { move=> D HD i0 Hi0.
      destruct (HD i0 Hi0) as (c0 & Hc0 & Hdel0 & Hy0).
      rewrite /char_ids elem_of_list_to_set list_elem_of_fmap in Hy0.
      destruct Hy0 as (y & Hidy & Hy).
      destruct (Hdkj' c0 Hc0 Hdel0 y Hy) as (c1 & Hc1 & Hdel1 & Hy1).
      exists c1. split_and!; [exact Hc1 | exact Hdel1 |].
      rewrite /char_ids elem_of_list_to_set list_elem_of_fmap.
      exists y. split; [exact Hidy | exact Hy1]. }
    have Htakestep : take (uint.nat (w64_word_instance.(word.add) j (W64 1)))
                          (pdel_vs ++ spans_vs)
                   = take (uint.nat j) (pdel_vs ++ spans_vs) ++ [sp].
    { rewrite (_ : uint.nat (w64_word_instance.(word.add) j (W64 1))
                 = S (uint.nat j)); last word.
      apply (take_S_r _ _ sp). exact Hsp. }
    destruct cov.
    - (* the span landed in full: drop it, and record its ids *)
      wp_auto. wp_for_post.
      iFrame "HΦ s Hpddelf Hspsl2 Hspcap2 Hallp Hallcap".
      iExists (w64_word_instance.(word.add) j (W64 1)), rest_sl, rest_vs, types_j',
        (Dj ∪ (if decide (delete_span_no_overflow (delete_span_of_val sp)) then delete_span_ids (delete_span_of_val sp) else ∅)).
      iFrame "Hj Hrestp Hrest Hrestcap Hall Hitemsf Hitemmap Htypes".
      iPureIntro. split_and!; [word | exact Hpoolj' | | | exact Hfactsj''].
      + move=> i0 /elem_of_union [Hi0 | Hi0]; first exact (Hmove Dj HdelDj i0 Hi0).
        destruct (decide (delete_span_no_overflow (delete_span_of_val sp))) as [Hnw | _]; last set_solver.
        exact (Hcovj' Hnw eq_refl i0 Hi0).
      + move=> sp' Hsp' Hnotrest Hnw'.
        rewrite Htakestep in Hsp'. apply elem_of_app in Hsp' as [Hsp' | Hsp'].
        * have := HspanDj sp' Hsp' Hnotrest Hnw'. set_solver.
        * apply list_elem_of_singleton in Hsp' as ->.
          rewrite decide_True //. set_solver.
    - (* not covered yet: keep it buffered *)
      wp_auto.
      wp_apply wp_slice_literal. iSplitR; first done.
      iIntros "%ssl [Hssl _]". wp_auto.
      wp_apply (wp_slice_append with "[$Hrest $Hrestcap $Hssl]").
      iIntros (rest_sl') "(Hrest & Hrestcap & _)".
      wp_auto. wp_for_post.
      iFrame "HΦ s Hpddelf Hspsl2 Hspcap2 Hallp Hallcap".
      iExists (w64_word_instance.(word.add) j (W64 1)), rest_sl', (rest_vs ++ [sp]), types_j',
        Dj.
      iFrame "Hj Hrestp Hrest Hrestcap Hall Hitemsf Hitemmap Htypes".
      iPureIntro. split_and!; [word | exact Hpoolj' | exact (Hmove Dj HdelDj) | | exact Hfactsj''].
      move=> sp' Hsp' Hnotrest Hnw'.
      rewrite Htakestep in Hsp'. apply elem_of_app in Hsp' as [Hsp' | Hsp'].
      + apply (HspanDj sp' Hsp'); last exact Hnw'.
        move=> Hin. apply Hnotrest. apply elem_of_app. by left.
      + apply list_elem_of_singleton in Hsp' as ->. exfalso. apply Hnotrest.
        apply elem_of_app. right. apply list_elem_of_here. }
  (* copy one span into [all] *)
  destruct (spans_vs !! uint.nat i) as [sp|] eqn:Hsp; last first.
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
  rewrite (take_S_r spans_vs (uint.nat i) sp Hsp) app_assoc.
  iFrame "Hall". iPureIntro. word.
Qed.

(** The public form of the wire delete step: [own_store] in, [own_store] out
    at the SAME model, history and pending buffer. Deletes are model no-ops in
    the insert-only document model (they only flip tombstone bits and split
    runs), which is exactly why the whole store predicate is preserved: the
    per-type item lists [ty_arr] do not move, so the registry coherence, the
    item-set authority and the counter clause all transfer verbatim, and the
    pool invariants come back from the loop.

    The inner loop's coverage record ([Hdels] below) is DROPPED here rather
    than turned into an [is_delete_set_lb] certificate, deliberately. At the inner
    level the record is worth something because the leftover buffer is a
    return value, so "this span is not in the leftover" pins which spans
    landed. [own_store] hides that buffer, so the same statement out here
    would be "there is a set, and the spans that landed are inside it" with
    nothing pinning which landed: a receipt the empty set satisfies, the same
    vacuity that made the first no-loss attempt worthless (PR #99).

    Making it enforceable wants the delete-side analogue of [is_accepted]: a
    per-span receipt the store invariant ties to covered-or-buffered, so a
    holder learns its span is in the delete set or still pending. That is its
    own milestone, not a line of plumbing. *)
Lemma wp_store__applyDeleteSpans_store (s_loc : loc) (γs : store_names)
    (γh : history_names) (c : ClientId) (h : list Ev) (m : DocModel)
    (pend : list (TId * IntegrateInput (A := A)))
    (sp_sl : slice.t) (dq : dfrac) (spans : list delete_span) :
  {{{ is_pkg_init yjs ∗ own_store s_loc γs γh c h m pend ∗
      own_delete_spans sp_sl dq spans }}}
    s_loc @! (go.PointerType yjs.store) @! "applyDeleteSpans" #sp_sl
  {{{ RET #(); own_store s_loc γs γh c h m pend ∗ own_delete_spans sp_sl dq spans }}}.
Proof using Type*.
  iIntros (Φ) "(#Hpkg & Hstore & Hsp) HΦ".
  iNamed "Hstore".
  destruct Hregcoh as (Hbindtypes & Hbindinj & Htypesbound & Hmtypes & Hmdom).
  have Hpool : pool_invs types by split_and!; assumption.
  wp_apply (wp_store__applyDeleteSpans s_loc items_mref types pdel_sl sp_sl dq pdel spans
              Hpool with "[$Hitemsf $Hitemmap $Htypes $Hpddelf $Hpddel $Hsp]").
  iIntros (types' pdel_sl' rest)
    "(Hitemsf & Hitemmap & Htypes & Hpddelf & Hpddel & Hsp & %Hpool' & %Hfacts & %_Hdels)".
  destruct Hfacts as (Harr & Hdom & Hlr & _ & Hcoord).
  (* the tombstone-set invariant follows the delete: both surgeries the loop
     performs (a split and a flip) only refine the live cells *)
  iDestruct (own_delete_set_refine γs m types types' Hlr with "Hdelete_set") as "Hdelete_set".
  (* equal domains and equal model lists, so the item-set authority is
     literally the same map *)
  have Hdomeq : ∀ q, is_Some (types !! q) <-> is_Some (types' !! q).
  { move=> q. split; first exact (Hdom q).
    move=> [ts' Hts']. destruct (Harr q ts' Hts') as (ts & Hts & _). by exists ts. }
  have Hfmapeq : ((λ ts, (list_to_set (ty_arr ts) : gset (YjsItem A))) <$> types')
               = ((λ ts, (list_to_set (ty_arr ts) : gset (YjsItem A))) <$> types).
  { apply map_eq => q. rewrite !lookup_fmap.
    destruct (types' !! q) as [ts'|] eqn:Hts'.
    - destruct (Harr q ts' Hts') as (ts & Hts & Heq). rewrite Hts /= Heq //.
    - destruct (types !! q) as [ts|] eqn:Hts; last done.
      exfalso. destruct (Hdom q (mk_is_Some _ _ Hts)) as [ts0 Hts0].
      rewrite Hts0 in Hts'. done. }
  iEval (rewrite -Hfmapeq) in "Hseq".
  destruct Hpool' as (Hrunfits' & Hlocdup' & Hrangedisj' & Horiginclk').
  iApply "HΦ". iFrame "Hsp".
  iExists client, k, items_mref, types_mref, deletedSetVal, pend_sl, pdel_sl', rest, types', bind, acc.
  iFrame "Hclient Hclock Hitemsf Hitemmap Htypesf Htypesmap HdeletedSet Hpendf Hpend
          Hpddelf Hpddel Hseq Htypes HtypesAuth Hhist Hacc Hdelete_set".
  iFrame "Hclientpin Hpendcert Hbinds".
  iPureIntro. split_and!.
  - exact Hclientc.
  - exact Hpendroot.
  - exact Hpendbnd.
  - (* the registry still describes the same documents *)
    rewrite /doc_registry_coh. split_and!.
    + move=> name p Hb. apply Hdom. exact (Hbindtypes name p Hb).
    + exact Hbindinj.
    + move=> p Hp. apply Htypesbound. by apply Hdomeq.
    + move=> name p ts' Hb Hts'.
      destruct (Harr p ts' Hts') as (ts & Hts & Heq).
      rewrite Heq. exact (Hmtypes name p ts Hb Hts).
    + exact Hmdom.
  - exact Hhcoh.
  - exact Hctr.
  - exact Hlocdup'.
  - exact Hrangedisj'.
  - exact Hrunfits'.
  - exact Horiginclk'.
  - exact Hacccoh.
Qed.

End store_deleteRange.
