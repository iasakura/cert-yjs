(** store update path, repair + applyUpdate layer: [getOrCreateYType],
    [store.repair] ([wp_store__repair]), their forms
    [wp_store__getOrCreateYType] (derived) / [wp_store__repair]
    (proved directly from the split helpers; over
    [own_store_state], stepping the registry by [pool_lookup_or_create] and
    the pool by [pool_after_repair]; [wp_store__repair_create] is its
    creation form, what [Transaction.integrateDecoded]'s unbound case
    steps by), [hasNode] / [originArrived] /
    [depsArrived] (proved directly,
    [wp_store__hasNode] / [wp_store__originArrived] /
    [wp_store__depsArrived], read against [pool_registry_models]
    through [docm_agree]), the [wire_*] drain machinery and the
    [own_store_data]-level certificate specs. Split out of [store/GetNode]; Requires the
    [store/splitNode] pool lemmas. Same boilerplate / [#[local]]
    instances. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core.
From New.proof Require Import prelude.
From New.proof.id Require Import id.
From New.proof.item Require Import item.
From New.proof.ytype Require Import ytype.
From New.proof.item Require Import run_theory model value heap.
From New.proof Require Import history.
From New.proof.store Require Import model value heap Integrate.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
From iris.algebra Require Import auth gmap gset.
From stdpp Require Import sorting.
From New.proof.store Require Import GetNode splitNode.

(* iris.algebra / stdpp.sorting push [nat_scope], retuning the default [<] / [≤].
   The verified WP proofs write [Z] comparisons (e.g. [sint.Z i < …]) unannotated
   and annotate [nat] ones with [%nat], so restore [Z_scope] as the default. *)
Local Open Scope Z_scope.

Section store_update.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.
Notation P := go_string.
Local Notation TId := (TypeId P).
Local Notation Op := (TId * @YjsOperation A)%type.
Local Notation Ev := (@Event Op).
Local Notation DocModel := (gmap TId (list (YjsItem A))).

(* the grow-only item-set RA (the certificate proofs grow the [sn_seq]
   authority and mint [is_type_lb] fragments) *)
Context {seq_inG : inG Σ (authR (gmapUR loc (gsetUR (YjsItem A))))}.
Context {acc_inG : inG Σ (authR (gsetUR YjsId))}.
(* The store's reader-count accounting ties the readers' share to the [types]
   map via a [dfrac_agree]; [store/heap] declares it up front, so the specs
   reached from here carry it too. *)
Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO addressed_pool))}.
(* the observers' tokens and registrations (issue #198 Part II), as [store/heap] *)
Context {observed_inG : ghost_varG Σ (list (YjsItem go_string * bool))}.
Context {observers_inG : inG Σ (authR (gsetUR (gname * go_string)))}.

(* [pending_item_rooted] / [is_pending_rooted] are pure [Prop]s (issue #54
   weakened them off their registration resource), so [store_inv_excl] /
   [own_store_data] carry them as [⌜..⌝] and no Persistent/Timeless instances are
   needed here. *)

(** [store.getOrCreateYType nm]: the root type bound to [nm], created empty
    and registered first when [nm] is unbound ([pool_lookup_or_create]).

    The creation branch crosses a window where no store state satisfies the
    invariants: around the [s.types[nm] = p] write, the registry binds [nm]
    to a type the pool does not hold yet. The window stays inside this
    proof, the fresh type carried as its own resource and refolded with
    [pool_invs_insert_empty] / [pool_registry_coh_bind_fresh] at the
    exit; the lemma's pre and post sit at the closed endpoints, where the
    invariants hold again (spec-shape "Specs of public functions use only
    public predicates": re-establishing the invariant is the function's
    job, never its caller's). *)
Lemma wp_store__getOrCreateYType (s : loc) (state : store_state) (nm : go_string) :
  {{{ is_pkg_init yjs ∗ own_store_state s state }}}
    s @! (go.PointerType yjs.store) @! "getOrCreateYType" #nm
  {{{ (q : loc) (p' : pool) (locs' : gmap loc (list loc)) (bind' : gmap P loc), RET #q;
      own_store_state s (state <| ss_pool := p' |> <| ss_locs := locs' |>
                            <| ss_bind := bind' |>) ∗
      ⌜pool_lookup_or_create (ss_pool state) (ss_locs state) (ss_bind state) nm q p' locs' bind'⌝ }}}.
Proof using Type*.
  iIntros (Φ) "(#Hpkg & Hruns) HΦ".
  destruct state as [client0 k0 locs p bind pend pdel]. simpl in *.
  iDestruct "Hruns" as "(Hfields & %Hinvs)".
  have Hrpi : pool_invs p := proj1 Hinvs.
  have Hreg : pool_registry_coh bind p := proj1 (proj2 Hinvs).
  have Hcontig : pool_clocks_contiguous p := proj2 (proj2 Hinvs).
  iDestruct "Hfields" as "(Hclient & Hclock & HdeletedSet & Hitems & Hregistry & Htypes & Hpending & Hpdeletes)".
  iEval (simpl) in "Hitems Htypes".
  iDestruct "Hregistry" as (types_mref) "(Htypesf & Htypesmap)".
  wp_method_call. wp_call. wp_call. wp_auto.
  wp_apply (wp_map_lookup2 with "Htypesmap"). iIntros "Htypesmap".
  destruct (bind !! nm) as [q|] eqn:Hb.
  - (* hit: the name is bound; nothing changes *)
    rewrite Hb /=. wp_auto.
    iApply ("HΦ" $! q p locs bind).
    iSplitL; last (iPureIntro; left; split_and!; [exact Hb | reflexivity | reflexivity | reflexivity]).
    iSplitL; last (iPureIntro; split_and!; [exact Hrpi | exact Hreg | exact Hcontig]).
    rewrite /own_store_fields /=.
    iFrame "Hclient Hclock HdeletedSet Hitems Htypes Hpending Hpdeletes".
    iExists types_mref. iFrame "Htypesf Htypesmap".
  - (* miss: allocate a fresh empty root type and register it *)
    rewrite Hb /=. wp_auto.
    wp_apply wp_newYType. iIntros (q) "Hnew".
    wp_auto.
    iDestruct (own_type_pool_fresh_type q [] (MkTypeModel []) locs p with "Hnew Htypes")
      as "(Hnew & Htypes & %Hfresh)".
    wp_apply (wp_map_insert with "Htypesmap"). iIntros "Htypesmap".
    wp_auto.
    iDestruct "Htypes" as "(%Hlocswf & Hpool)".
    iAssert (own_type_pool (DfracOwn 1) (<[q := []]> locs) (<[q := MkTypeModel []]> p))
      with "[Hpool Hnew]" as "Htypes".
    { iSplitR; first (iPureIntro; exact (locs_wf_insert_empty locs p q Hfresh Hlocswf)).
      rewrite big_sepM_insert; last exact Hfresh.
      iSplitL "Hnew".
      { iExists []. iFrame "Hnew". iPureIntro.
        split; [apply lookup_insert_eq | exact YjsArrInvariant_empty]. }
      iApply (big_sepM_impl with "Hpool"). iIntros "!>" (q0 tm0 Hq0) "H".
      iDestruct "H" as (ls0) "(%Hls0 & Hyt & %Hinv0)". iExists ls0. iFrame "Hyt".
      iPureIntro. split; [| exact Hinv0].
      rewrite lookup_insert_ne //. move=> Heq. rewrite -Heq Hfresh in Hq0. done. }
    (* the fresh type holds no run, so the item index is the same key list *)
    iDestruct "Hitems" as (items_mref) "(Hitemsf & Hitemmap)".
    iEval (rewrite /own_item_map) in "Hitemmap".
    iDestruct (own_item_map_key_pairs_keys_perm items_mref (DfracOwn 1) _
                 (entry_key_pair <$> pool_entries (<[q := []]> locs) (<[q := MkTypeModel []]> p))
                 (Permutation_sym (fmap_Permutation entry_key_pair _ _
                    (pool_entries_insert_empty locs p q Hfresh)))
                 with "Hitemmap") as "Hitemmap".
    iApply ("HΦ" $! q (<[q := MkTypeModel []]> p) (<[q := []]> locs) (<[nm := q]> bind)).
    iSplitL; last (iPureIntro; right; split_and!;
                   [exact Hb | exact Hfresh | reflexivity | reflexivity | reflexivity]).
    iSplitL; last (iPureIntro; split_and!;
                   [exact (pool_invs_insert_empty p q Hfresh Hrpi)
                   | exact (pool_registry_coh_bind_fresh bind p nm q _ Hb Hfresh Hreg)
                   | exact (pool_clocks_contiguous_insert_empty p q Hfresh Hcontig)]).
    rewrite /own_store_fields /=.
    iFrame "Hclient Hclock HdeletedSet Htypes Hpending Hpdeletes".
    iSplitL "Hitemsf Hitemmap"; first (iExists items_mref; iFrame "Hitemsf Hitemmap").
    iExists types_mref. iFrame "Htypesf Htypesmap".
Qed.

(* ----- the general repair (issue #28 stage D2b) ---------------------------
   [store.repair] over the invariant-carrying split wrappers: the origin ids
   may address ANY char of their covering cells' runs; the clean-end /
   clean-start splits put them on run boundaries. The two splits are
   sequenced by the wrappers' transport records. *)


(** [store.repair]: the origins are named by their pool slots [(q, k)]
    ([pool_origins_covered], [pool_repair_parent]); the item comes back
    linked to run-boundary addresses read off the updated address map
    ([pool_origins_split]) and the pool steps by [pool_after_repair].
    Proved directly from the split helpers and
    [wp_store__getOrCreateYType]: the clean-end split first, the right
    origin's slot relocated through [pool_after_split]'s coverage clause,
    the clean-start split second, and the left boundary carried across it
    by [pool_split_step_other_slot] (the two slots differ: the left result
    ends at the left origin, which same origin slots put strictly before
    the right one). *)
Lemma wp_store__repair (s item_l pname : loc)
    (input : IntegrateInput (A := A)) (opn : option go_string)
    (state : store_state) (orL orR : option (loc * nat)) (p_t : loc) :
  pool_origins_covered (ss_pool state) input orL orR ->
  pool_repair_parent (ss_bind state) opn orL orR p_t ->
  {{{ is_pkg_init yjs ∗
      own_linked_item item_l input null null null ∗
      is_parent_name pname opn ∗
      own_store_state s state }}}
    s @! (go.PointerType yjs.store) @! "repair" #item_l #pname
  {{{ (leftNode rightNode : loc) (p' : pool) (locs' : gmap loc (list loc)), RET #();
      own_linked_item item_l input p_t leftNode rightNode ∗
      own_store_state s (state <| ss_pool := p' |> <| ss_locs := locs' |>) ∗
      ⌜pool_after_repair (ss_pool state) p'⌝ ∗
      ⌜pool_origins_split p' locs' input orL orR leftNode rightNode⌝ ∗
      (* a repair only splits: the exact tombstone state is untouched *)
      ⌜pool_tombstoned p' = pool_tombstoned (ss_pool state)⌝ }}}.
Proof using Type*.
  move=> [HwL [HwR Hsame]] Hwpar.
  destruct state as [client0 k0 locs p bind pend pdel]. simpl in *.
  rewrite /pool_origin_covered in HwL HwR. rewrite /pool_repair_parent in Hwpar.
  iIntros (Φ) "(#Hpkg & Hlinked & #HisPN & Hruns) HΦ".
  iDestruct "Hlinked" as (itemVal oleft oright) "(Hraw & %Hfl & %Hfr & %Hfpar & %Hflags & %Hrunc)".
  iNamed "Hraw".
  iDestruct (own_store_state_run_wf with "Hruns") as %Hwf0.
  iDestruct (own_store_state_aligned with "Hruns") as %Haligned0.
  iDestruct (own_store_state_covers_unique with "Hruns") as %Huniq0.
  (* a run covers its own head *)
  have Hhead_cov : ∀ r, run_wf (run_items r) -> run_covers r (item_id (run_head_item r)).
  { move=> r Hwf. rewrite run_head_item_id /run_covers /=.
    destruct Hwf as [Hne _].
    have Hlen : (1 <= length (run_items r))%nat by (destruct (run_items r); [done | simpl; lia]).
    split_and!; [done | lia | lia]. }
  wp_method_call. wp_call. wp_call. wp_auto.
  destruct oleft as [idvL|].
  - (* left origin present: clean-end split *)
    have HinlS : input.(in_originId) = Some (toYjsId idvL) by rewrite -Hin_l //.
    rewrite HinlS in HwL. destruct orL as [[qL kL]|]; last done. simpl in HwL.
    destruct HwL as (tmL & rL & HpL & HrL & HrLcov).
    iDestruct "Holeft" as "[%HnnL #HolC]".
    rewrite (bool_decide_eq_false_2 (itemVal.(yjs.item.originLeftId') = null) HnnL) /=.
    wp_auto.
    destruct (locs_aligned_lens _ _ Haligned0 qL tmL HpL) as (lsL & HlsL & HlenL).
    have HkLlt : (kL < length lsL)%nat by (rewrite HlenL; exact (lookup_lt_Some _ _ _ HrL)).
    destruct (lookup_lt_is_Some_2 lsL kL HkLlt) as [lcL HlkL].
    wp_apply (wp_store__splitAtAndGetLeft s idvL (MkStoreState client0 k0 locs p bind pend pdel)
                qL tmL lsL kL rL lcL HpL HlsL HrL HlkL HrLcov with "[$Hpkg $Hruns]").
    iIntros (p1 locs1) "(Hruns & %Hlstep1)".
    iEval (simpl) in "Hruns".
    have HrLslot : ∃ tm, p !! qL = Some tm ∧ tm_runs tm !! kL = Some rL := ex_intro _ tmL (conj HpL HrL).
    have HrLmem : rL ∈ all_runs p.
    { apply (elem_of_all_runs p rL). exists qL, tmL. split; [exact HpL | exact (list_elem_of_lookup_2 _ _ _ HrL)]. }
    have HrLwf : run_wf (run_items rL) := Hwf0 rL HrLmem.
    have Hsstep1 : pool_split_step p locs qL kL p1 locs1
      := pool_split_step_of_left _ _ _ _ _ _ _ _ HrLslot HrLcov Hlstep1.
    have Hstep1 : pool_after_split p p1 qL kL := pool_after_split_of_split_step _ _ _ _ _ _ Hwf0 Hsstep1.
    have HlcLloc : (locs !! qL) ≫= (λ ls, ls !! kL) = Some lcL by rewrite HlsL /= HlkL.
    destruct (pool_split_left_step_ends_at _ _ _ _ _ _ _ _ _ HrLslot HlcLloc HrLwf HrLcov Hlstep1)
      as (HstartL1 & HendL1 & HlocL1).
    iDestruct (own_store_state_run_wf with "Hruns") as %Hwf1.
    iDestruct (own_store_state_aligned with "Hruns") as %Haligned1.
    have Hrepair1 : pool_after_repair p p1 := pool_after_repair_of_split _ _ _ _ Hstep1.
    wp_auto.
    destruct oright as [idvR|].
    + (* right origin present: relocate the witness, clean-start split *)
      have HinrS : input.(in_rightOriginId) = Some (toYjsId idvR) by rewrite -Hin_r //.
      rewrite HinrS in HwR. destruct orR as [[qR kR]|]; last done. simpl in HwR.
      destruct HwR as (tmR & rR & HpR & HrR & HrRcov).
      rewrite HinlS HinrS in Hsame.
      have Hsame' : (qL, kL) = (qR, kR) -> (clock (toYjsId idvL) < clock (toYjsId idvR))%nat := Hsame.
      iDestruct "Horight" as "[%HnnR #HorC]".
      rewrite (bool_decide_eq_false_2 (itemVal.(yjs.item.originRightId') = null) HnnR) /=.
      wp_auto.
      (* the right origin's covering slot after the first split *)
      have Hcover1 := proj1 (proj2 (proj2 (proj2 Hstep1))).
      have HrRcov' := HrRcov.
      destruct HrRcov as (HrRcl & HrRlo & HrRhi).
      destruct (Hcover1 (clientId (toYjsId idvR)) (clock (toYjsId idvR)) qR tmR kR rR HpR HrR HrRcl HrRlo HrRhi)
        as (tmR1 & kR1 & rR1 & HpR1 & HrR1 & HrR1cl & HrR1lo & HrR1hi & Hprov).
      have HrR1cov : run_covers rR1 (toYjsId idvR) by (split_and!; done).
      destruct (locs_aligned_lens _ _ Haligned1 qR tmR1 HpR1) as (lsR1 & HlsR1 & HlenR1).
      have HkR1lt : (kR1 < length lsR1)%nat by (rewrite HlenR1; exact (lookup_lt_Some _ _ _ HrR1)).
      destruct (lookup_lt_is_Some_2 lsR1 kR1 HkR1lt) as [lcR1 HlkR1].
      destruct HendL1 as (tmL1 & HpL1 & rL1 & HrL1 & HrL1cl & HrL1end).
      destruct HstartL1 as (tmL1' & HpL1' & rL1' & HrL1' & HrL1head).
      rewrite HpL1 in HpL1'. injection HpL1' as <-. rewrite HrL1 in HrL1'. injection HrL1' as <-.
      (* the right slot is not the left result's slot: the left result ends
         at [idvL] and covers [rL]'s head, so a right run there would put
         [idvR] at or before [idvL] while sitting at [rL]'s original slot *)
      have Hslotne : ¬ (qL = qR ∧ kL = kR1).
      { move=> [HqLR HkLR]. subst qR kR1.
        rewrite HpL1 in HpR1. injection HpR1 as <-. rewrite HrL1 in HrR1. injection HrR1 as <-.
        have Hle : (clock (toYjsId idvR) <= clock (toYjsId idvL))%nat by lia.
        destruct Hprov as [Heq | [_ [HkLeq _]]]; last first.
        { subst kR. have := Hsame' eq_refl. lia. }
        (* [rR] is the left result: it covers [rL]'s head, as [rL] does *)
        subst rR.
        have Hcl1 : run_client rL1 = run_client rL.
        { have := f_equal clientId HrL1head. rewrite !run_head_item_id //. }
        have Hck1 : run_clock rL1 = run_clock rL.
        { have := f_equal clock HrL1head. rewrite !run_head_item_id //. }
        have HrRmem : rL1 ∈ all_runs p.
        { apply (elem_of_all_runs p rL1). exists qL, tmR. split; [exact HpR | exact (list_elem_of_lookup_2 _ _ _ HrR)]. }
        have HrRwf : run_wf (run_items rL1) := Hwf0 rL1 HrRmem.
        have HcovR : pool_covers p qL kR (item_id (run_head_item rL)).
        { exists tmR, rL1. split_and!; [exact HpR | exact HrR |].
          rewrite -HrL1head. exact (Hhead_cov rL1 HrRwf). }
        have HcovL : pool_covers p qL kL (item_id (run_head_item rL)).
        { exists tmL, rL. split_and!; [exact HpL | exact HrL | exact (Hhead_cov rL HrLwf)]. }
        destruct (Huniq0 _ _ _ _ _ HcovR HcovL) as [_ HkeqLR]. subst kR.
        have := Hsame' eq_refl. lia. }
      wp_apply (wp_store__splitAtAndGetRight s idvR (MkStoreState client0 k0 locs1 p1 bind pend pdel)
                  qR tmR1 lsR1 kR1 rR1 lcR1 HpR1 HlsR1 HrR1 HlkR1 HrR1cov with "[$Hpkg $Hruns]").
      iIntros (rl p2 locs2) "(Hruns & %Hrstep2)".
      iEval (simpl) in "Hruns".
      have HrR1slot : ∃ tm, p1 !! qR = Some tm ∧ tm_runs tm !! kR1 = Some rR1 := ex_intro _ tmR1 (conj HpR1 HrR1).
      have HrR1wf : run_wf (run_items rR1).
      { apply Hwf1. apply (elem_of_all_runs p1 rR1). exists qR, tmR1.
        split; [exact HpR1 | exact (list_elem_of_lookup_2 _ _ _ HrR1)]. }
      have Hsstep2 : pool_split_step p1 locs1 qR kR1 p2 locs2
        := pool_split_step_of_right _ _ _ _ _ _ _ _ _ HrR1slot HrR1cov Hrstep2.
      have Hstep2 : pool_after_split p1 p2 qR kR1 := pool_after_split_of_split_step _ _ _ _ _ _ Hwf1 Hsstep2.
      destruct (pool_split_right_step_starts_at _ _ _ _ _ _ _ _ _ HrR1slot HrR1wf HrR1cov Hrstep2)
        as (kR2 & HstartR2 & HlocR2).
      (* the left boundary survives the second split at its address *)
      destruct (pool_split_step_other_slot _ _ _ _ _ _ qL kL tmL1 rL1 lcL Hsstep2 HpL1 HrL1 HlocL1 Hslotne)
        as (kL2 & tmL2 & HpL2 & HrL2 & HlocL2 & _).
      have HendL2 : pool_ends_at p2 qL kL2 (toYjsId idvL).
      { exists tmL2. split; first exact HpL2. exists rL1. split_and!; [exact HrL2 | exact HrL1cl | exact HrL1end]. }
      have Hrepair2 : pool_after_repair p p2
        := pool_after_repair_trans _ _ _ Hrepair1 (pool_after_repair_of_split _ _ _ _ Hstep2).
      wp_auto.
      destruct opn as [nm|].
      * (* Parent::String *)
        iDestruct "HisPN" as "[%HnnP #HpnC]".
        rewrite (bool_decide_eq_false_2 (pname = null) HnnP) /=.
        wp_auto.
        wp_apply (wp_store__getOrCreateYType s (MkStoreState client0 k0 locs2 p2 bind pend pdel) nm
                    with "[$Hpkg $Hruns]").
        iIntros (q p3 locs3 bind3) "(Hruns & %Hlc)". simpl in Hlc.
        destruct Hlc as [(Hb' & -> & -> & ->) | (Hb' & _)]; last by rewrite Hb' in Hwpar.
        rewrite Hwpar in Hb'. injection Hb' as <-.
        iEval (simpl) in "Hruns".
        wp_auto.
        iApply ("HΦ" $! lcL rl p2 locs2). simpl.
        iFrame "Hruns".
        iSplitL "Hitem".
        { iExists _, (Some idvL), (Some idvR). rewrite /own_fresh_item_raw. simpl.
          iFrame "Hitem". iFrame "HolC HorC".
          iPureIntro. split_and!; try done. }
        iPureIntro. split; first exact Hrepair2.
        split; last by rewrite (pool_tombstoned_split_step _ _ _ _ _ _ Hsstep2)
                                 (pool_tombstoned_split_step _ _ _ _ _ _ Hsstep1).
        split.
        { rewrite HinlS /=. exists kL2. split; [exact HendL2 | exact HlocL2]. }
        { rewrite HinrS /=. exists kR2. split; [exact HstartR2 | exact HlocR2]. }
      * (* Parent::None: borrow from the resolved left neighbour *)
        iDestruct "HisPN" as "%HpN".
        rewrite (bool_decide_eq_true_2 (pname = null) HpN) /=.
        destruct (locs2 !! qL) as [lsL2|] eqn:HlsL2; last done. simpl in HlocL2.
        iDestruct (own_store_state_node_acc s (MkStoreState client0 k0 locs2 p2 bind pend pdel)
                     qL lsL2 tmL2 kL2 lcL rL1 HlsL2 HpL2 HlocL2 HrL2 with "Hruns") as (ivL) "H".
        iNamed "H".
        iDestruct (typed_pointsto_not_null with "Haccval") as %HnnCL.
        wp_auto.
        rewrite (bool_decide_eq_false_2 (lcL = null) HnnCL) /=.
        wp_auto.
        iDestruct ("Haccback" with "Haccval") as "Hruns".
        rewrite Haccpar Hwpar.
        iApply ("HΦ" $! lcL rl p2 locs2). simpl.
        iFrame "Hruns".
        iSplitL "Hitem".
        { iExists _, (Some idvL), (Some idvR). rewrite /own_fresh_item_raw. simpl.
          iFrame "Hitem". iFrame "HolC HorC".
          iPureIntro. split_and!; try done. }
        iPureIntro. split; first exact Hrepair2.
        split; last by rewrite (pool_tombstoned_split_step _ _ _ _ _ _ Hsstep2)
                                 (pool_tombstoned_split_step _ _ _ _ _ _ Hsstep1).
        split.
        { rewrite HinlS /=. exists kL2. split; [exact HendL2 | rewrite HlsL2 /=; exact HlocL2]. }
        { rewrite HinrS /=. exists kR2. split; [exact HstartR2 | exact HlocR2]. }
    + (* no right origin *)
      have HinrN : input.(in_rightOriginId) = None by rewrite -Hin_r //.
      rewrite HinrN in HwR. destruct orR as [[qR kR]|]; first done.
      iDestruct "Horight" as "%HnR".
      rewrite (bool_decide_eq_true_2 (itemVal.(yjs.item.originRightId') = null) HnR) /=.
      wp_auto.
      destruct HendL1 as (tmL1 & HpL1 & rL1 & HrL1 & HrL1cl & HrL1end).
      have HendL1' : pool_ends_at p1 qL kL (toYjsId idvL).
      { exists tmL1. split; first exact HpL1. exists rL1. split_and!; [exact HrL1 | exact HrL1cl | exact HrL1end]. }
      destruct opn as [nm|].
      * (* Parent::String *)
        iDestruct "HisPN" as "[%HnnP #HpnC]".
        rewrite (bool_decide_eq_false_2 (pname = null) HnnP) /=.
        wp_auto.
        wp_apply (wp_store__getOrCreateYType s (MkStoreState client0 k0 locs1 p1 bind pend pdel) nm
                    with "[$Hpkg $Hruns]").
        iIntros (q p3 locs3 bind3) "(Hruns & %Hlc)". simpl in Hlc.
        destruct Hlc as [(Hb' & -> & -> & ->) | (Hb' & _)]; last by rewrite Hb' in Hwpar.
        rewrite Hwpar in Hb'. injection Hb' as <-.
        iEval (simpl) in "Hruns".
        wp_auto.
        iApply ("HΦ" $! lcL null p1 locs1). simpl.
        iFrame "Hruns".
        iSplitL "Hitem".
        { iExists _, (Some idvL), None. rewrite /own_fresh_item_raw. simpl.
          iFrame "Hitem". iFrame "HolC".
          iPureIntro. split_and!; try done. }
        iPureIntro. split; first exact Hrepair1.
        split; last by rewrite (pool_tombstoned_split_step _ _ _ _ _ _ Hsstep1).
        split.
        { rewrite HinlS /=. exists kL. split; [exact HendL1' | exact HlocL1]. }
        { rewrite HinrN //. }
      * (* Parent::None: borrow from the resolved left neighbour *)
        iDestruct "HisPN" as "%HpN".
        rewrite (bool_decide_eq_true_2 (pname = null) HpN) /=.
        destruct (locs1 !! qL) as [lsL1|] eqn:HlsL1; last done. simpl in HlocL1.
        iDestruct (own_store_state_node_acc s (MkStoreState client0 k0 locs1 p1 bind pend pdel)
                     qL lsL1 tmL1 kL lcL rL1 HlsL1 HpL1 HlocL1 HrL1 with "Hruns") as (ivL) "H".
        iNamed "H".
        iDestruct (typed_pointsto_not_null with "Haccval") as %HnnCL.
        wp_auto.
        rewrite (bool_decide_eq_false_2 (lcL = null) HnnCL) /=.
        wp_auto.
        iDestruct ("Haccback" with "Haccval") as "Hruns".
        rewrite Haccpar Hwpar.
        iApply ("HΦ" $! lcL null p1 locs1). simpl.
        iFrame "Hruns".
        iSplitL "Hitem".
        { iExists _, (Some idvL), None. rewrite /own_fresh_item_raw. simpl.
          iFrame "Hitem". iFrame "HolC".
          iPureIntro. split_and!; try done. }
        iPureIntro. split; first exact Hrepair1.
        split; last by rewrite (pool_tombstoned_split_step _ _ _ _ _ _ Hsstep1).
        split.
        { rewrite HinlS /=. exists kL. split; [exact HendL1' | rewrite HlsL1 /=; exact HlocL1]. }
        { rewrite HinrN //. }
  - (* no left origin *)
    have HinlN : input.(in_originId) = None by rewrite -Hin_l //.
    rewrite HinlN in HwL. destruct orL as [[qL kL]|]; first done.
    iDestruct "Holeft" as "%HnL".
    rewrite (bool_decide_eq_true_2 (itemVal.(yjs.item.originLeftId') = null) HnL) /=.
    wp_auto.
    destruct oright as [idvR|].
    + (* right origin present: clean-start split, no relocation *)
      have HinrS : input.(in_rightOriginId) = Some (toYjsId idvR) by rewrite -Hin_r //.
      rewrite HinrS in HwR. destruct orR as [[qR kR]|]; last done. simpl in HwR.
      destruct HwR as (tmR & rR & HpR & HrR & HrRcov).
      iDestruct "Horight" as "[%HnnR #HorC]".
      rewrite (bool_decide_eq_false_2 (itemVal.(yjs.item.originRightId') = null) HnnR) /=.
      wp_auto.
      destruct (locs_aligned_lens _ _ Haligned0 qR tmR HpR) as (lsR & HlsR & HlenR).
      have HkRlt : (kR < length lsR)%nat by (rewrite HlenR; exact (lookup_lt_Some _ _ _ HrR)).
      destruct (lookup_lt_is_Some_2 lsR kR HkRlt) as [lcR HlkR].
      wp_apply (wp_store__splitAtAndGetRight s idvR (MkStoreState client0 k0 locs p bind pend pdel)
                  qR tmR lsR kR rR lcR HpR HlsR HrR HlkR HrRcov with "[$Hpkg $Hruns]").
      iIntros (rl p1 locs1) "(Hruns & %Hrstep1)".
      iEval (simpl) in "Hruns".
      have HrRslot : ∃ tm, p !! qR = Some tm ∧ tm_runs tm !! kR = Some rR := ex_intro _ tmR (conj HpR HrR).
      have HrRwf : run_wf (run_items rR).
      { apply Hwf0. apply (elem_of_all_runs p rR). exists qR, tmR.
        split; [exact HpR | exact (list_elem_of_lookup_2 _ _ _ HrR)]. }
      have Hsstep1 : pool_split_step p locs qR kR p1 locs1
        := pool_split_step_of_right _ _ _ _ _ _ _ _ _ HrRslot HrRcov Hrstep1.
      have Hstep1 : pool_after_split p p1 qR kR := pool_after_split_of_split_step _ _ _ _ _ _ Hwf0 Hsstep1.
      destruct (pool_split_right_step_starts_at _ _ _ _ _ _ _ _ _ HrRslot HrRwf HrRcov Hrstep1)
        as (kR2 & HstartR2 & HlocR2).
      have Hrepair1 : pool_after_repair p p1 := pool_after_repair_of_split _ _ _ _ Hstep1.
      wp_auto.
      destruct opn as [nm|].
      * (* Parent::String *)
        iDestruct "HisPN" as "[%HnnP #HpnC]".
        rewrite (bool_decide_eq_false_2 (pname = null) HnnP) /=.
        wp_auto.
        wp_apply (wp_store__getOrCreateYType s (MkStoreState client0 k0 locs1 p1 bind pend pdel) nm
                    with "[$Hpkg $Hruns]").
        iIntros (q p3 locs3 bind3) "(Hruns & %Hlc)". simpl in Hlc.
        destruct Hlc as [(Hb' & -> & -> & ->) | (Hb' & _)]; last by rewrite Hb' in Hwpar.
        rewrite Hwpar in Hb'. injection Hb' as <-.
        iEval (simpl) in "Hruns".
        wp_auto.
        iApply ("HΦ" $! null rl p1 locs1). simpl.
        iFrame "Hruns".
        iSplitL "Hitem".
        { iExists _, None, (Some idvR). rewrite /own_fresh_item_raw. simpl.
          iFrame "Hitem". iFrame "HorC".
          iPureIntro. split_and!; try done. }
        iPureIntro. split; first exact Hrepair1.
        split; last by rewrite (pool_tombstoned_split_step _ _ _ _ _ _ Hsstep1).
        split.
        { rewrite HinlN //. }
        { rewrite HinrS /=. exists kR2. split; [exact HstartR2 | exact HlocR2]. }
      * (* Parent::None: borrow from the resolved right neighbour *)
        iDestruct "HisPN" as "%HpN".
        rewrite (bool_decide_eq_true_2 (pname = null) HpN) /=.
        have Hfl' : (itemVal <| yjs.item.right' := rl |>).(yjs.item.left') = null
          by simpl; exact Hfl.
        destruct HstartR2 as (tmR2 & HpR2 & rR2 & HrR2 & HrR2head).
        destruct (locs1 !! qR) as [lsR2|] eqn:HlsR2; last done. simpl in HlocR2.
        iDestruct (own_store_state_node_acc s (MkStoreState client0 k0 locs1 p1 bind pend pdel)
                     qR lsR2 tmR2 kR2 rl rR2 HlsR2 HpR2 HlocR2 HrR2 with "Hruns") as (ivR) "H".
        iNamed "H".
        iDestruct (typed_pointsto_not_null with "Haccval") as %HnnCR.
        wp_auto.
        rewrite (bool_decide_eq_true_2 _ Hfl') /=.
        wp_auto.
        rewrite (bool_decide_eq_false_2 (rl = null) HnnCR) /=.
        wp_auto.
        iDestruct ("Haccback" with "Haccval") as "Hruns".
        rewrite Haccpar Hwpar.
        iApply ("HΦ" $! null rl p1 locs1). simpl.
        iFrame "Hruns".
        iSplitL "Hitem".
        { iExists _, None, (Some idvR). rewrite /own_fresh_item_raw. simpl.
          iFrame "Hitem". iFrame "HorC".
          iPureIntro. split_and!; try done. }
        iPureIntro. split; first exact Hrepair1.
        split; last by rewrite (pool_tombstoned_split_step _ _ _ _ _ _ Hsstep1).
        split.
        { rewrite HinlN //. }
        { rewrite HinrS /=. exists kR2. split.
          - exists tmR2. split; first exact HpR2. exists rR2. split; [exact HrR2 | exact HrR2head].
          - rewrite HlsR2 /=. exact HlocR2. }
    + (* no origins at all: Parent::None is ruled out by the premise *)
      have HinrN : input.(in_rightOriginId) = None by rewrite -Hin_r //.
      rewrite HinrN in HwR. destruct orR as [[qR kR]|]; first done.
      iDestruct "Horight" as "%HnR".
      rewrite (bool_decide_eq_true_2 (itemVal.(yjs.item.originRightId') = null) HnR) /=.
      wp_auto.
      destruct opn as [nm|]; last done.
      iDestruct "HisPN" as "[%HnnP #HpnC]".
      rewrite (bool_decide_eq_false_2 (pname = null) HnnP) /=.
      wp_auto.
      wp_apply (wp_store__getOrCreateYType s (MkStoreState client0 k0 locs p bind pend pdel) nm
                  with "[$Hpkg $Hruns]").
      iIntros (q p3 locs3 bind3) "(Hruns & %Hlc)". simpl in Hlc.
      destruct Hlc as [(Hb' & -> & -> & ->) | (Hb' & _)]; last by rewrite Hb' in Hwpar.
      rewrite Hwpar in Hb'. injection Hb' as <-.
      iEval (simpl) in "Hruns".
      wp_auto.
      iApply ("HΦ" $! null null p locs). simpl.
      iFrame "Hruns".
      iSplitL "Hitem".
      { iExists _, None, None. rewrite /own_fresh_item_raw. simpl.
        iFrame "Hitem".
        iPureIntro. split_and!; try done. }
      iPureIntro. split; first exact (pool_after_repair_refl p).
      split; last reflexivity.
      split.
      { rewrite HinlN //. }
      { rewrite HinrN //. }
Qed.


(* ===== applyUpdate (doc-level, #49) ====================================== *)

(** Both origin indices of a successful [integrate], off its bind chain. *)
Lemma integrate_finds (input : IntegrateInput (A := A)) (arr arr2 : list (YjsItem A)) :
  integrate input arr = Some arr2 ->
  ∃ leftIdx rightIdx, findLeftIdx (in_originId input) arr = Some leftIdx /\
                      findRightIdx (in_rightOriginId input) arr = Some rightIdx.
Proof.
  rewrite /integrate.
  move=> /bind_Some [leftIdx [HfindLeft Hr1]].
  move: Hr1 => /bind_Some [rightIdx [HfindRight Hr2]].
  by exists leftIdx, rightIdx.
Qed.

(** A present origin's [find*Idx] hit names the origin item's exact index. *)
Lemma findLeftIdx_inv (originId : YjsId) (arr : list (YjsItem A)) (k : Z) :
  findLeftIdx (Some originId) arr = Some k ->
  ∃ (kn : nat) (it : YjsItem A), k = Z.of_nat kn /\ arr !! kn = Some it /\ item_id it = originId.
Proof.
  rewrite /findLeftIdx.
  destruct (list_find (fun item => item_id item = originId) arr) as [[kn it]|] eqn:Hf; last done.
  simpl. move=> [= <-]. apply list_find_Some in Hf. destruct Hf as (Hlk & Hidf & _).
  by exists kn, it.
Qed.

Lemma findRightIdx_inv (originId : YjsId) (arr : list (YjsItem A)) (k : Z) :
  findRightIdx (Some originId) arr = Some k ->
  ∃ (kn : nat) (it : YjsItem A), k = Z.of_nat kn /\ arr !! kn = Some it /\ item_id it = originId.
Proof.
  rewrite /findRightIdx.
  destruct (list_find (fun item => item_id item = originId) arr) as [[kn it]|] eqn:Hf; last done.
  simpl. move=> [= <-]. apply list_find_Some in Hf. destruct Hf as (Hlk & Hidf & _).
  by exists kn, it.
Qed.

(** ---- boundary-cell / cursor bridges (issue #28 U2): locating a flattened
    char inside its cell, and the id arithmetic along a well-formed run.
    These replace the unit-scaffold identifications (cell index = model
    index) once runs can be longer than one char. ---- *)

(** The char of a chained run carrying a covered id: at offset
    clock originId - head clock. *)
Lemma run_wf_char_at_clock (r : list (YjsItem A)) (originId : YjsId) :
  run_wf r ->
  clientId (item_id (hd inhabitant r)) = clientId originId ->
  (clock (item_id (hd inhabitant r)) <= clock originId)%nat ->
  (clock originId < clock (item_id (hd inhabitant r)) + length r)%nat ->
  ∃ ch, r !! (clock originId - clock (item_id (hd inhabitant r)))%nat = Some ch ∧
        item_id ch = originId.
Proof.
  move=> Hwf Hcl Hle Hlt.
  have Hlt3 : ((clock originId - clock (item_id (hd inhabitant r))) < length r)%nat by lia.
  destruct (lookup_lt_is_Some_2 _ _ Hlt3) as [ch Hch].
  exists ch. split; [exact Hch |].
  rewrite (run_wf_char_id _ _ _ Hwf Hch).
  destruct originId as [oc ok]. simpl in *.
  f_equal; [exact Hcl | lia].
Qed.


(** The model has an id exactly when some run of the pool covers it: the
    registry's model agreement read (the run form of
    [docm_cells_agree]). *)
Lemma docm_agree (m : DocModel) (bind : gmap P loc) (p : pool) (d : YjsId) :
  pool_registry_models m bind p ->
  pool_registry_coh bind p ->
  (∀ r, r ∈ all_runs p -> run_wf (run_items r)) ->
  (doc_model_has m d = true <-> ∃ q k, pool_covers p q k d).
Proof.
  move=> [Hmtypes Hmdom] [Hbindtypes [_ Htypesbound]] Hrunwf. split.
  - move=> /docm_has_spec [t [x [Hx Hid]]].
    have Hne : doc_model_get m t ≠ [].
    { move=> Heq. move: Hx. rewrite Heq elem_of_nil //. }
    destruct (Hmdom t Hne) as (nm & q & -> & Hbnm).
    destruct (Hbindtypes nm q Hbnm) as [tm Htm].
    have Hdg : doc_model_get m (RootId nm) = tm_arr tm := Hmtypes nm q tm Hbnm Htm.
    rewrite Hdg /tm_arr in Hx.
    apply list_elem_of_lookup_1 in Hx as [kn Hkn].
    destruct (runs_flatten_lookup_run (tm_runs tm) kn x Hkn) as (k & off & r & Hk & Hoff & _).
    have Hrall : r ∈ all_runs p.
    { apply (elem_of_all_runs p r). exists q, tm. split; [exact Htm | exact (list_elem_of_lookup_2 _ _ _ Hk)]. }
    have Hwf : run_wf (run_items r) := Hrunwf r Hrall.
    have Hofflt : (off < length (run_items r))%nat := lookup_lt_Some _ _ _ Hoff.
    have Hxid := run_wf_char_id (run_items r) off x Hwf Hoff.
    rewrite Hid in Hxid.
    exists q, k, tm, r. split_and!; [exact Htm | exact Hk |].
    rewrite /run_covers /run_client /run_clock /run_head_item. rewrite Hxid /=.
    split_and!; [done | lia | lia].
  - move=> [q [k [tm [r [Htm [Hk [Hcl [Hle Hlt]]]]]]]].
    apply docm_has_spec.
    have Hrall : r ∈ all_runs p.
    { apply (elem_of_all_runs p r). exists q, tm. split; [exact Htm | exact (list_elem_of_lookup_2 _ _ _ Hk)]. }
    have Hwf : run_wf (run_items r) := Hrunwf r Hrall.
    destruct (Htypesbound q (ex_intro _ tm Htm)) as [nm Hbnm].
    have Hdg : doc_model_get m (RootId nm) = tm_arr tm := Hmtypes nm q tm Hbnm Htm.
    destruct (run_wf_char_at_clock (run_items r) d Hwf Hcl Hle Hlt) as (ch & Hch & Hchid).
    exists (RootId nm), ch. split; [| exact Hchid].
    rewrite Hdg /tm_arr.
    apply (list_elem_of_lookup_2 _
             (length (runs_flatten (take k (tm_runs tm))) +
              (clock d - clock (item_id (hd inhabitant (run_items r)))))%nat).
    exact (runs_flatten_lookup_of_run (tm_runs tm) k _ r ch Hk Hch).
Qed.

(** [store.hasNode] (issue #40 x issue #28 U7c): the
    arrival test the pending gate runs. Its result IS the model presence
    [doc_model_has m (toYjsId idv)]: [GetNode]'s covering slot is bridged to
    [doc_model_has] through the registry's model agreement
    ([pool_registry_models], [docm_agree]). *)
Lemma wp_store__hasNode (s : loc) (idv : yjs.id.t) (m : DocModel) (state : store_state) :
  pool_registry_models m (ss_bind state) (ss_pool state) ->
  {{{ is_pkg_init yjs ∗ own_store_state s state }}}
    s @! (go.PointerType yjs.store) @! "hasNode" #idv
  {{{ (ok : bool), RET #ok;
      own_store_state s state ∗
      ⌜ok = true <-> doc_model_has m (toYjsId idv) = true⌝ }}}.
Proof using Type*.
  move=> Hregmodel.
  iIntros (Φ) "(#Hpkg & Hruns) HΦ".
  iDestruct (own_store_state_registry_coh with "Hruns") as %Hpreg.
  iDestruct (own_store_state_run_wf with "Hruns") as %Hwf.
  have Hagree : ∀ d : YjsId, doc_model_has m d = true <-> ∃ q k, pool_covers (ss_pool state) q k d
    := λ d, docm_agree m (ss_bind state) (ss_pool state) d Hregmodel Hpreg Hwf.
  wp_method_call. wp_call. wp_call. wp_auto.
  wp_apply (wp_store__GetNode_state s idv state with "[$Hpkg $Hruns]").
  iIntros (l ok) "(Hruns & %Hres)".
  wp_auto.
  iApply ("HΦ" $! ok). iFrame "Hruns".
  iPureIntro. destruct ok.
  - split; [move=> _ | done].
    destruct Hres as (q & k & Hcov & _).
    apply Hagree. by exists q, k.
  - split; [done | move=> Hdh].
    exfalso. apply Hagree in Hdh. destruct Hdh as (q & k & Hcov).
    exact (Hres q k Hcov).
Qed.

(* ===== #40 pending stack (issue #40) ===== *)
Lemma own_update_id_bounds (sl : slice.t) (dq : dfrac)
    (inputs : list (TId * IntegrateInput (A := A))) :
  own_update_structs sl dq inputs -∗
  ⌜∀ (i : nat) (typedInput : TId * IntegrateInput (A := A)), inputs !! i = Some typedInput →
     (Z.of_nat (clientId (in_id typedInput.2)) < 2^64)%Z ∧
     (Z.of_nat (clock (in_id typedInput.2)) < 2^64)%Z⌝.
Proof.
  iIntros "Hupd". iDestruct "Hupd" as (uivs) "(Hsl & Hcap & #Hitems)".
  iDestruct (big_sepL2_impl _ (λ _ updateItemVal typedInput,
      ⌜(Z.of_nat (clientId (in_id typedInput.2)) < 2^64)%Z ∧
       (Z.of_nat (clock (in_id typedInput.2)) < 2^64)%Z⌝)%I
    with "Hitems []") as "Hpure".
  { iIntros "!>" (i updateItemVal typedInput Hu Hi) "Hui".
    iDestruct "Hui" as (oleft oright opn)
      "(HisL & HisR & HisPN & %Hin_l & %Hin_r & %Hin_id & %Hin_c & %Hulen & %Htid & %Hborrow)".
    iPureIntro. rewrite -Hin_id /toYjsId /=. split; word. }
  iDestruct (big_sepL2_length with "Hitems") as %Hlen2.
  iDestruct (big_sepL2_pure_1 with "Hpure") as %Hb.
  iPureIntro. move=> i typedInput Hi.
  have [updateItemVal Huiv] : is_Some (uivs !! i).
  { apply lookup_lt_is_Some_2. rewrite Hlen2. exact (lookup_lt_Some _ _ _ Hi). }
  exact (Hb i updateItemVal typedInput Huiv Hi).
Qed.

(* ===== the pending gate, heap side (issue #40) ============================ *)

(** [containsUpdateItemId] (the in-pending dedup probe): scans a decoded pending
    slice for a struct carrying [idv]. *)
Lemma wp_containsUpdateItemId (sl : slice.t) (dq : dfrac)
    (inputs : list (TId * IntegrateInput (A := A))) (idv : yjs.id.t) :
  {{{ is_pkg_init yjs ∗ own_update_structs sl dq inputs }}}
    @! yjs.containsUpdateItemId #sl #idv
  {{{ RET #(existsb (λ typedInput2, bool_decide (in_id typedInput2.2 = toYjsId idv)) inputs);
      own_update_structs sl dq inputs }}}.
Proof using Type*.
  wp_start as "Hupd".
  iDestruct "Hupd" as (uivs) "(Hsl & Hcap & #Hitems)".
  iDestruct (big_sepL2_length with "Hitems") as %Hlen2.
  iDestruct (own_slice_len with "Hsl") as %[Hsllen Hsllen0].
  wp_auto.
  iAssert (∃ (j : nat),
    "Hi" ∷ i_ptr ↦ W64 j ∗ "Hitemsp" ∷ items_ptr ↦ sl ∗ "Hid" ∷ id_ptr ↦ idv ∗
    "Hsl" ∷ sl ↦*{dq} uivs ∗
    "Hcap" ∷ own_slice_cap yjs.updateItem.t sl dq ∗
    "%Hjbnd" ∷ ⌜(j <= length uivs)%nat⌝ ∗
    "%Hnomatch" ∷ ⌜existsb (λ typedInput2, bool_decide (in_id typedInput2.2 = toYjsId idv))
                    (take j inputs) = false⌝)%I
    with "[i items id Hsl Hcap]" as "IH".
  { iExists 0%nat. iFrame "i items id Hsl Hcap". iPureIntro.
    split; [lia | rewrite take_0 //]. }
  wp_for "IH".
  case_bool_decide as Hcond.
  - (* probe element j *)
    have Hjlt : (j < length uivs)%nat.
    { move: Hcond. rewrite Hsllen. word. }
    destruct (uivs !! j) as [updateItemVal|] eqn:Huiv;
      last by (apply lookup_ge_None in Huiv; lia).
    have [typedInput Hti] : is_Some (inputs !! j).
    { apply lookup_lt_is_Some_2. rewrite -Hlen2. exact Hjlt. }
    iDestruct (big_sepL2_lookup _ _ _ j with "Hitems") as "Hui";
      [exact Huiv | exact Hti |].
    iDestruct "Hui" as (oleft oright opn)
      "(HisL & HisR & HisPN & %Hin_l & %Hin_r & %Hin_id & %Hin_c & %Hulen & %Htid & %Hborrow)".
    wp_auto.
    rewrite decide_True; last by word.
    iDestruct (own_slice_elem_acc (sint.Z (W64 j)) updateItemVal sl dq uivs with "Hsl") as "[Hel Hgive]".
    { word. }
    { replace (Z.to_nat (sint.Z (W64 j))) with j by word. exact Huiv. }
    wp_auto.
    wp_method_call. wp_call. wp_auto.
    wp_apply (wp_Id__Equal updateItemVal.(yjs.updateItem.id') idv).
    iDestruct ("Hgive" $! updateItemVal with "Hel") as "Hsl".
    have Hinsid : (<[sint.nat (W64 j) := updateItemVal]> uivs) = uivs.
    { apply list_insert_id. replace (sint.nat (W64 j)) with j by word. exact Huiv. }
    iEval (rewrite Hinsid) in "Hsl".
    case_bool_decide as Heqid.
    + (* match: the whole scan is true *)
      wp_auto. wp_for_post.
      have -> : existsb (λ typedInput2, bool_decide (in_id typedInput2.2 = toYjsId idv)) inputs = true.
      { apply existsb_exists. exists typedInput.
        split; [by apply list_elem_of_In, (list_elem_of_lookup_2 _ j) |].
        apply bool_decide_eq_true_2. rewrite -Hin_id //. }
      iApply ("HΦ" with "[Hsl Hcap]").
      iExists uivs. iFrame "Hsl Hcap Hitems".
    + (* no match at j: advance *)
      wp_auto. wp_for_post.
      iFrame "HΦ".
      iExists (S j).
      replace (word.add (W64 j) (W64 1)) with (W64 (S j)) by word.
      iFrame "Hi Hitemsp Hid Hsl Hcap".
      iPureIntro. split; [lia |].
      erewrite take_S_r; last exact Hti.
      rewrite existsb_app Hnomatch /=.
      rewrite bool_decide_eq_false_2; first done.
      rewrite -Hin_id //.
  - (* scanned everything: the scan is false *)
    wp_auto.
    have Hjall : (j >= length uivs)%nat.
    { move: Hcond. rewrite Hsllen. rewrite Hsllen in Hjbnd. word. }
    have -> : existsb (λ typedInput2, bool_decide (in_id typedInput2.2 = toYjsId idv)) inputs = false.
    { rewrite -(take_ge inputs j); [exact Hnomatch | rewrite -Hlen2; lia]. }
    iApply ("HΦ" with "[Hsl Hcap]").
    iExists uivs. iFrame "Hsl Hcap Hitems".
Qed.


(* ----- the arrival gate ----- *)
(* (the pure gate lemmas [input_ready_false_of_dep] / [input_ready_true_of] /
   [input_deps_*] live in [network_model] with the pending theory) *)

(** [store.originArrived] (issue #40): the per-origin
    arrival check; a nil origin imposes no dependency. Its result is the
    model presence of the origin id (via [hasNode]). *)
Lemma wp_store__originArrived (s : loc) (p : loc)
    (originId : option yjs.id.t) (m : DocModel) (state : store_state) :
  pool_registry_models m (ss_bind state) (ss_pool state) ->
  {{{ is_pkg_init yjs ∗ is_origin_id p originId ∗ own_store_state s state }}}
    s @! (go.PointerType yjs.store) @! "originArrived" #p
  {{{ (ok : bool), RET #ok;
      own_store_state s state ∗
      ⌜ok = true <-> match originId with
                     | None => True
                     | Some idv => doc_model_has m (toYjsId idv) = true
                     end⌝ }}}.
Proof using Type*.
  move=> Hregmodel.
  iIntros (Φ) "(#Hpkg & #HisP & Hruns) HΦ".
  wp_method_call. wp_call. wp_call. wp_auto.
  destruct originId as [idv |]; simpl.
  - iDestruct "HisP" as "[%Hpne #Hpid]".
    rewrite bool_decide_eq_false_2; last first.
    { move=> Heq. exact (Hpne Heq). }
    wp_auto.
    wp_apply (wp_store__hasNode s idv m state Hregmodel with "[$Hpkg $Hruns]").
    iIntros (ok) "(Hruns & %Hok)".
    wp_auto.
    iApply ("HΦ" $! ok).
    iFrame "Hruns".
    iPureIntro. exact Hok.
  - iDestruct "HisP" as %->.
    rewrite bool_decide_eq_true_2 //.
    wp_auto.
    iApply ("HΦ" $! true).
    iFrame "Hruns".
    iPureIntro. done.
Qed.


(** [store.depsArrived] (issue #40): the structural
    gate, as arrival checks. The return value IS the pure gate [input_ready]
    of the decoded struct; each arrival check ([originArrived] / [hasNode])
    returns the model presence of a dependency, so the gate composes them by
    [input_ready_true_of] / [input_ready_false_of_dep]. *)
Lemma wp_store__depsArrived (s : loc) (updateItemVal : yjs.updateItem.t)
    (typedInput : TId * IntegrateInput (A := A)) (m : DocModel) (state : store_state) :
  pool_registry_models m (ss_bind state) (ss_pool state) ->
  {{{ is_pkg_init yjs ∗ is_update_item updateItemVal typedInput ∗ own_store_state s state }}}
    s @! (go.PointerType yjs.store) @! "depsArrived" #updateItemVal
  {{{ RET #(input_ready m typedInput.2); own_store_state s state }}}.
Proof using Type*.
  move=> Hregmodel.
  iIntros (Φ) "(#Hpkg & #Hui & Hruns) HΦ".
  iDestruct "Hui" as (oleft oright opn)
    "(HisL & HisR & HisPN & %Hin_l & %Hin_r & %Hin_id & %Hin_c & %Hunonempty & %Htid & %Hborrow)".
  have Hcid : clientId (in_id typedInput.2) = uint.nat updateItemVal.(yjs.updateItem.id').(yjs.id.clientId').
  { rewrite -Hin_id /toYjsId //. }
  have Hck : clock (in_id typedInput.2) = uint.nat updateItemVal.(yjs.updateItem.id').(yjs.id.clock').
  { rewrite -Hin_id /toYjsId //. }
  wp_method_call. wp_call. wp_call. wp_auto.
  (* ---- left origin ---- *)
  wp_apply (wp_store__originArrived s _ oleft m state Hregmodel with "[$Hpkg $HisL $Hruns]").
  iIntros (okL) "(Hruns & %HokL)".
  wp_auto.
  destruct okL; last first.
  { wp_auto.
    have Hready : input_ready m typedInput.2 = false.
    { destruct oleft as [idL |]; simpl in Hin_l; last first.
      { exfalso. destruct HokL as [_ H2]. have := H2 I. discriminate. }
      apply (input_ready_false_of_dep m typedInput.2 (toYjsId idL)).
      - apply input_deps_originL. rewrite -Hin_l //.
      - apply not_true_iff_false => Hd.
        destruct HokL as [_ H2]. have := H2 Hd. discriminate. }
    iEval (rewrite Hready) in "HΦ".
    iApply ("HΦ" with "[$Hruns]"). }
  wp_auto.
  (* ---- right origin ---- *)
  wp_apply (wp_store__originArrived s _ oright m state Hregmodel with "[$Hpkg $HisR $Hruns]").
  iIntros (okR) "(Hruns & %HokR)".
  wp_auto.
  destruct okR; last first.
  { wp_auto.
    have Hready : input_ready m typedInput.2 = false.
    { destruct oright as [idR |]; simpl in Hin_r; last first.
      { exfalso. destruct HokR as [_ H2]. have := H2 I. discriminate. }
      apply (input_ready_false_of_dep m typedInput.2 (toYjsId idR)).
      - apply input_deps_originR. rewrite -Hin_r //.
      - apply not_true_iff_false => Hd.
        destruct HokR as [_ H2]. have := H2 Hd. discriminate. }
    iEval (rewrite Hready) in "HΦ".
    iApply ("HΦ" with "[$Hruns]"). }
  wp_auto.
  have HLarr : ∀ originId, in_originId typedInput.2 = Some originId -> doc_model_has m originId = true.
  { move=> originId Hoid.
    destruct oleft as [idL |]; simpl in Hin_l; last by rewrite -Hin_l in Hoid.
    rewrite -Hin_l in Hoid. injection Hoid as <-.
    exact (proj1 HokL eq_refl). }
  have HRarr : ∀ originId, in_rightOriginId typedInput.2 = Some originId -> doc_model_has m originId = true.
  { move=> originId Hoid.
    destruct oright as [idR |]; simpl in Hin_r; last by rewrite -Hin_r in Hoid.
    rewrite -Hin_r in Hoid. injection Hoid as <-.
    exact (proj1 HokR eq_refl). }
  (* ---- the own-predecessor gate ---- *)
  destruct (bool_decide
      (uint.Z (W64 0) < uint.Z updateItemVal.(yjs.updateItem.id').(yjs.id.clock'))) eqn:Hckpos.
  - apply bool_decide_eq_true_1 in Hckpos.
    wp_auto.
    wp_apply (wp_NewId updateItemVal.(yjs.updateItem.id').(yjs.id.clientId')
                (word.sub updateItemVal.(yjs.updateItem.id').(yjs.id.clock') (W64 1))).
    wp_apply (wp_store__hasNode s _ m state Hregmodel with "[$Hpkg $Hruns]").
    iIntros (okP) "(Hruns & %HokP)".
    wp_auto.
    have Hpredid : toYjsId (yjs.id.mk updateItemVal.(yjs.updateItem.id').(yjs.id.clientId')
                     (word.sub updateItemVal.(yjs.updateItem.id').(yjs.id.clock') (W64 1)))
                 = MkYjsId (clientId (in_id typedInput.2)) (clock (in_id typedInput.2) - 1)%nat.
    { rewrite /toYjsId /= Hcid Hck. f_equal. word. }
    have Hckform : ∃ k, clock (in_id typedInput.2) = S k ∧ (k = clock (in_id typedInput.2) - 1)%nat.
    { exists (clock (in_id typedInput.2) - 1)%nat. rewrite Hck. split; [word | done]. }
    destruct Hckform as (k & HckS & Hkval).
    destruct okP; last first.
    + wp_auto.
      have Hready : input_ready m typedInput.2 = false.
      { apply (input_ready_false_of_dep m typedInput.2 (MkYjsId (clientId (in_id typedInput.2)) k)).
        - exact (input_deps_pred typedInput.2 k HckS).
        - apply not_true_iff_false => Hd.
          destruct HokP as [_ H2].
          rewrite Hpredid -Hkval in H2.
          have := H2 Hd. discriminate. }
      iEval (rewrite Hready) in "HΦ".
      iApply ("HΦ" with "[$Hruns]").
    + wp_auto.
      have Hready : input_ready m typedInput.2 = true.
      { apply input_ready_true_of; [exact HLarr | exact HRarr |].
        move=> k' Hk'.
        have Hkk : k' = k by lia.
        rewrite Hkk Hkval.
        have HP := proj1 HokP eq_refl. rewrite Hpredid in HP. exact HP. }
      iEval (rewrite Hready) in "HΦ".
      iApply ("HΦ" with "[$Hruns]").
  - apply bool_decide_eq_false_1 in Hckpos.
    wp_auto.
    have Hready : input_ready m typedInput.2 = true.
    { apply input_ready_true_of; [exact HLarr | exact HRarr |].
      move=> k' Hk'. exfalso. rewrite Hck in Hk'. word. }
    iEval (rewrite Hready) in "HΦ".
    iApply ("HΦ" with "[$Hruns]").
Qed.

(** A [toItem] success with a present origin resolved that origin inside the
    target array, so the array is nonempty. This is how the drain derives the
    target root's binding for origin-carrying structs: a nonempty model entry
    is a registered root by [Hmdom] (origin-less structs instead carry a
    [pending_item_rooted]-style witness). *)
Lemma toItem_nonempty_of_origin (input : IntegrateInput (A := A))
    (arr : list (YjsItem A)) (newItem : YjsItem A) :
  toItem input arr = Some newItem ->
  in_originId input ≠ None ∨ in_rightOriginId input ≠ None ->
  arr ≠ [].
Proof.
  move=> Htoit Hor Heq. subst arr.
  have [o [r [idx [cx [_ [HoL [HoR _]]]]]]] :=
    proj1 (toItem_ok_iff input [] newItem) Htoit.
  destruct Hor as [Ho | Ho].
  - destruct (in_originId input) as [originId|]; last by apply Ho.
    destruct HoL as (it & _ & Hf).
    rewrite /find_by_id /= in Hf. discriminate.
  - destruct (in_rightOriginId input) as [originId|]; last by apply Ho.
    destruct HoR as (it & _ & Hf).
    rewrite /find_by_id /= in Hf. discriminate.
Qed.

(* ----- the ready step: one decoded struct, repaired and integrated ----- *)

(** [store.repair], creation form (issue #54): an
    ORIGIN-FREE decoded item targeting a not-yet-registered root [nm]. Both
    origin [if]s are skipped, and the parent branch registers a fresh empty
    type through [getOrCreateYType]'s miss path; the item comes back linked
    to null/null under the fresh type [q]. A second spec of [store.repair]
    ([transaction/applyUpdate]'s unbound-parent branch,
    [wp_Transaction__integrateDecoded_unbound], uses it): it cannot be
    derived from [wp_store__repair], whose [pool_repair_parent] premise
    requires the wire parent name to be bound already, while here [nm] is
    unbound and the registration itself is the point. *)
Lemma wp_store__repair_create (s item_l pname : loc)
    (input : IntegrateInput (A := A)) (nm : go_string) (state : store_state) :
  in_originId input = None ->
  in_rightOriginId input = None ->
  ss_bind state !! nm = None ->
  {{{ is_pkg_init yjs ∗
      own_linked_item item_l input null null null ∗
      is_parent_name pname (Some nm) ∗
      own_store_state s state }}}
    s @! (go.PointerType yjs.store) @! "repair" #item_l #pname
  {{{ (q : loc), RET #();
      own_linked_item item_l input q null null ∗
      own_store_state s (state <| ss_pool := <[q := MkTypeModel []]> (ss_pool state) |>
                            <| ss_locs := <[q := []]> (ss_locs state) |>
                            <| ss_bind := <[nm := q]> (ss_bind state) |>) ∗
      ⌜ss_pool state !! q = None⌝ }}}.
Proof using Type*.
  move=> HoL HoR Hnm.
  destruct state as [client0 k0 locs p bind pend pdel]. simpl in *.
  iIntros (Φ) "(#Hpkg & Hlinked & #HisPN & Hruns) HΦ".
  iDestruct "Hlinked" as (itemVal oleft oright) "(Hraw & %Hfl & %Hfr & %Hfpar & %Hflags & %Hrunc)".
  iNamed "Hraw".
  have HoleftN : oleft = None by (move: Hin_l; rewrite HoL; by destruct oleft).
  have HorightN : oright = None by (move: Hin_r; rewrite HoR; by destruct oright).
  subst oleft oright.
  wp_method_call. wp_call. wp_call. wp_auto.
  iDestruct "Holeft" as "%HnL".
  rewrite (bool_decide_eq_true_2 (itemVal.(yjs.item.originLeftId') = null) HnL) /=.
  wp_auto.
  iDestruct "Horight" as "%HnR".
  rewrite (bool_decide_eq_true_2 (itemVal.(yjs.item.originRightId') = null) HnR) /=.
  wp_auto.
  iDestruct "HisPN" as "[%HnnP #HpnC]".
  rewrite (bool_decide_eq_false_2 (pname = null) HnnP) /=.
  wp_auto.
  wp_apply (wp_store__getOrCreateYType s (MkStoreState client0 k0 locs p bind pend pdel) nm
              with "[$Hpkg $Hruns]").
  iIntros (q p' locs' bind') "(Hruns & %Hlc)". simpl in Hlc.
  destruct Hlc as [(Hb' & _) | (_ & Hfresh & -> & -> & ->)]; first by rewrite Hb' in Hnm.
  iEval (simpl) in "Hruns".
  wp_auto.
  iApply ("HΦ" $! q). simpl.
  iFrame "Hruns".
  iSplitL "Hitem".
  { iExists _, None, None. rewrite /own_fresh_item_raw. simpl.
    iFrame "Hitem".
    iPureIntro. split_and!; try done. }
  done.
Qed.

Lemma wire_pass_kept_le (pending : list (TId * IntegrateInput (A := A))) :
  ∀ m kept app kept' m',
    wire_pass m pending kept = (app, kept', m') ->
    (length kept' + length app <= length kept + length pending)%nat.
Proof.
  elim: pending => [| typedInput tl IH] m kept app kept' m'.
  - move=> [= <- <- _] /=. lia.
  - have Hcl : length (typedInput :: tl) = S (length tl) by done.
    simpl. destruct (doc_model_has m (in_id typedInput.2)).
    { move=> Hwp. have Hle := IH _ _ _ _ _ Hwp. lia. }
    destruct (input_ready m typedInput.2); last first.
    { move=> Hwp. have Hle := IH _ _ _ _ _ Hwp.
      have Hkl : (length (pending_keep kept typedInput) <= S (length kept))%nat by apply pending_keep_length. lia. }
    destruct (wire_integrate m typedInput) as [arr' |]; last first.
    { move=> Hwp. have Hle := IH _ _ _ _ _ Hwp.
      have Hkl : (length (pending_keep kept typedInput) <= S (length kept))%nat by apply pending_keep_length. lia. }
    destruct (wire_pass (<[typedInput.1 := arr']> m) tl kept) as [[app0 kept0] m0] eqn:Hrec.
    move=> [= <- <- _]. have Hle := IH _ _ _ _ _ Hrec. simpl. lia.
Qed.

Lemma wire_pass_kept_lt (pending app kept' : list (TId * IntegrateInput (A := A)))
    (m m' : DocModel) :
  wire_pass m pending [] = (app, kept', m') ->
  app ≠ [] ->
  (length kept' < length pending)%nat.
Proof.
  move=> Hpass Hne.
  move: (wire_pass_kept_le pending m [] app kept' m' Hpass) => /=.
  destruct app; [done | simpl; lia].
Qed.

Lemma wire_drain_aux_fuel_agree (f1 : nat) :
  ∀ (f2 : nat) (m : DocModel) (pending : list (TId * IntegrateInput (A := A))),
    (length pending < f1)%nat -> (length pending < f2)%nat ->
    wire_drain_aux f1 m pending = wire_drain_aux f2 m pending.
Proof.
  elim: f1 => [| f1 IH] f2 m pending Hlt1 Hlt2; first lia.
  destruct f2 as [| f2]; first lia.
  simpl.
  destruct (wire_pass m pending []) as [[app kept] m'] eqn:Hpass.
  destruct app as [| a app0]; first done.
  have Hklt : (length kept < length pending)%nat
    by exact (wire_pass_kept_lt pending (a :: app0) kept m m' Hpass ltac:(done)).
  rewrite (IH f2 m' kept ltac:(lia) ltac:(lia)) //.
Qed.

Lemma wire_drain_aux_fuel_ge (fuel : nat) (m : DocModel)
    (pending : list (TId * IntegrateInput (A := A))) :
  (length pending < fuel)%nat ->
  wire_drain_aux fuel m pending = wire_drain_aux (S (length pending)) m pending.
Proof.
  move=> Hlt. exact (wire_drain_aux_fuel_agree fuel (S (length pending)) m pending Hlt ltac:(lia)).
Qed.

Lemma wire_drain_unfold (m : DocModel) (pending : list (TId * IntegrateInput (A := A))) :
  wire_drain m pending =
    let '(app, kept, m') := wire_pass m pending [] in
    match app with
    | [] => ([], kept, m')
    | _ :: _ =>
        let '(app2, rest, m'') := wire_drain m' kept in (app ++ app2, rest, m'')
    end.
Proof.
  rewrite {1}/wire_drain /=.
  destruct (wire_pass m pending []) as [[app kept] m'] eqn:Hpass.
  destruct app as [| a app0]; first done.
  have Hklt : (length kept < length pending)%nat
    by exact (wire_pass_kept_lt pending (a :: app0) kept m m' Hpass ltac:(done)).
  rewrite (wire_drain_aux_fuel_ge (length pending) m' kept Hklt) //.
Qed.

Lemma wire_pass_no_progress (pending : list (TId * IntegrateInput (A := A))) :
  ∀ m kept kept' m',
    wire_pass m pending kept = ([], kept', m') ->
    m' = m.
Proof.
  elim: pending => [| typedInput tl IH] m kept kept' m' /=.
  - move=> [= _ <-] //.
  - destruct (doc_model_has m (in_id typedInput.2)).
    { move=> /IH //. }
    destruct (input_ready m typedInput.2); last first.
    { move=> /IH //. }
    destruct (wire_integrate m typedInput) as [arr' |]; last first.
    { move=> /IH //. }
    destruct (wire_pass (<[typedInput.1 := arr']> m) tl kept) as [[app0 kept0] m0] eqn:Hrec.
    move=> [= Happ _ _]. discriminate.
Qed.

Lemma wire_drain_step_nil (m : DocModel)
    (pending kept : list (TId * IntegrateInput (A := A))) (m1 : DocModel) :
  wire_pass m pending [] = ([], kept, m1) ->
  wire_drain m pending = ([], kept, m1).
Proof. move=> Hpass. rewrite wire_drain_unfold Hpass //. Qed.

Lemma wire_drain_step_cons (m : DocModel)
    (pending : list (TId * IntegrateInput (A := A)))
    (a : TId * IntegrateInput (A := A))
    (app kept app2 rest2 : list (TId * IntegrateInput (A := A))) (m1 m2 : DocModel) :
  wire_pass m pending [] = (a :: app, kept, m1) ->
  wire_drain m1 kept = (app2, rest2, m2) ->
  wire_drain m pending = ((a :: app) ++ app2, rest2, m2).
Proof. move=> Hpass Hdrec. rewrite wire_drain_unfold Hpass Hdrec //. Qed.

Lemma WireReplay_app (m m1 m2 : DocModel)
    (a1 a2 : list (TId * IntegrateInput (A := A))) :
  WireReplay m a1 m1 -> WireReplay m1 a2 m2 -> WireReplay m (a1 ++ a2) m2.
Proof.
  move=> H1. elim: H1 a2 m2 => [m0 | m0 typedInput arr' rest m0' Hdup Hready Hint Hrest IH] a2 m2 H2 /=.
  - exact H2.
  - apply (WireReplay_cons m0 typedInput arr' (rest ++ a2) m2 Hdup Hready Hint).
    exact (IH a2 m2 H2).
Qed.

Lemma wire_pass_replay (pending : list (TId * IntegrateInput (A := A))) :
  ∀ m kept app kept' m',
    wire_pass m pending kept = (app, kept', m') ->
    WireReplay m app m'.
Proof.
  elim: pending => [| typedInput tl IH] m kept app kept' m' /=.
  - move=> [= <- _ <-]. constructor.
  - destruct (doc_model_has m (in_id typedInput.2)) eqn:Hdup.
    { move=> /IH //. }
    destruct (input_ready m typedInput.2) eqn:Hready; last first.
    { move=> /IH //. }
    destruct (wire_integrate m typedInput) as [arr' |] eqn:Hint; last first.
    { move=> /IH //. }
    destruct (wire_pass (<[typedInput.1 := arr']> m) tl kept) as [[app0 kept0] m0] eqn:Hrec.
    move=> [= <- _ <-].
    exact (WireReplay_cons m typedInput arr' app0 m0 Hdup Hready Hint (IH _ _ _ _ _ Hrec)).
Qed.

End store_update.
