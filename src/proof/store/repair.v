(** store update path, repair + applyUpdate layer: [getOrCreateYType],
    [store.repair] ([wp_store__repair]), their run-granular forms
    [wp_store__getOrCreateYType_runs] (derived) / [wp_store__repair_runs]
    (proved directly from the run-granular split helpers; over
    [own_store_runs], stepping the registry by [pool_lookup_or_create] and
    the pool by [pool_after_repair]), [integrateDecoded] (proved directly
    at run granularity, [wp_store__integrateDecoded_runs], over its
    bound-root and unbound-root cases; it reports [runs_within_or_from]
    and [runs_integrate_live_refine]), [hasNode] / [originArrived] /
    [depsArrived] (proved directly at run granularity,
    [wp_store__hasNode_runs] / [wp_store__originArrived_runs] /
    [wp_store__depsArrived_runs], read against [pool_registry_models]
    through [docm_runs_agree]), the [wire_*] drain machinery and the
    [own_store]-level certificate specs. Split out of [store/GetNode]; Requires the
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
Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO (gmap loc (list loc) * pool)))}.

(* [client_run]'s merge_sort instances are [#[local]] in [store/model];
   the run-list lemmas here need them again. *)
#[local] Instance cell_le_dec : RelDecision cell_le.
Proof. rewrite /cell_le. solve_decision. Defined.
#[local] Instance cell_le_trans : Transitive cell_le.
Proof. rewrite /cell_le. move=> x y z. lia. Qed.
#[local] Instance cell_le_total : Total cell_le.
Proof. rewrite /cell_le. move=> x y. lia. Qed.

(* [pending_item_rooted] / [is_pending_rooted] are pure [Prop]s (issue #54
   weakened them off their registration resource), so [store_inv_excl] /
   [own_store] carry them as [⌜..⌝] and no Persistent/Timeless instances are
   needed here. *)

(** [word] does not use [0 <= Z.of_nat l] on its own, so a [clock + length <
    2^64] bound needs the length-nonneg fact spelled out to recover the
    per-clock [< 2^64] word conversion (issue #28 U7c). Isolated here to keep
    [word] on clean variables. *)
#[local] Lemma wp_store__getOrCreateYType_hit (s : loc) (st : store_state)
    (nm : go_string) (p : loc) :
  ss_bind st !! nm = Some p ->
  {{{ is_pkg_init yjs ∗ own_store_struct s st }}}
    s @! (go.PointerType yjs.store) @! "getOrCreateYType" #nm
  {{{ RET #p; own_store_struct s st }}}.
Proof using Type*.
  move=> Hp.
  iIntros (Φ) "(#Hpkg & Hcells) HΦ". iNamed "Hcells". iNamed "Hfields".
  iDestruct "Hregistry" as (types_mref) "(Htypesf & Htypesmap)".
  wp_method_call. wp_call. wp_call. wp_auto.
  wp_apply (wp_map_lookup2 with "Htypesmap"). iIntros "Htypesmap".
  rewrite Hp /=.
  wp_auto.
  iApply "HΦ".
  iApply (own_store_struct_intro _ _ Hinvs
            with "Hclient Hclock HdeletedSet Hitems [Htypesf Htypesmap] Htypes Hpending Hpdeletes").
  iExists types_mref. iFrame "Htypesf Htypesmap".
Qed.

(** [store.getOrCreateYType], creation (miss) case (issue #54): the name is NOT
    bound, so the method allocates a fresh empty [yType] via [newYType],
    registers it under [nm], and returns it. The registry map grows by
    [nm -> p] and the per-type DLL big-op by a fresh EMPTY type at the
    genuinely fresh location [p]. Local: with the hit case above, a stepping
    stone of [wp_store__getOrCreateYType].

    This proof crosses a window where no [store_state] satisfies
    [store_invs]: around the [s.types[nm] = p] write, either the registry
    already binds [nm] to a [p] that [own_type_pool] does not yet hold
    (breaking [registry_coh]'s bound-names-are-live conjunct, the order
    taken here) or the pool would hold a live [p] that no name binds
    (breaking its live-types-are-bound conjunct). The window stays inside
    this one proof, the fresh type carried as its own resource and refolded
    with [pool_invs_insert_empty] / [registry_coh_bind_fresh] at the exit;
    the lemma's pre and post sit at the closed endpoints (CLAUDE.md "Spec
    shape", the open-receiver case). *)
#[local] Lemma wp_store__getOrCreateYType_miss (s : loc) (st : store_state) (nm : go_string) :
  ss_bind st !! nm = None ->
  {{{ is_pkg_init yjs ∗ own_store_struct s st }}}
    s @! (go.PointerType yjs.store) @! "getOrCreateYType" #nm
  {{{ (p : loc), RET #p;
      own_store_struct s (st <| ss_types := <[p := MkTypeState [] []]> (ss_types st) |>
                            <| ss_bind := <[nm := p]> (ss_bind st) |>) ∗
      ⌜ss_types st !! p = None⌝ }}}.
Proof using Type*.
  move=> Hp.
  destruct st as [client0 k0 types bind pend pdel]. simpl in *.
  iIntros (Φ) "(#Hpkg & Hcells) HΦ".
  iDestruct "Hcells" as "(Hfields0 & %Hinvs0)".
  have Hpool : pool_invs types := proj1 Hinvs0.
  have Hreg : registry_coh bind types := proj2 Hinvs0.
  iDestruct "Hfields0" as "(Hclient & Hclock & HdeletedSet & Hitems & Hregistry & Htypes & Hpending & Hpdeletes)".
  iDestruct "Hregistry" as (types_mref) "(Htypesf & Htypesmap)".
  wp_method_call. wp_call. wp_call. wp_auto.
  wp_apply (wp_map_lookup2 with "Htypesmap"). iIntros "Htypesmap".
  rewrite Hp /=.
  wp_auto.
  wp_apply wp_newYType. iIntros (p) "Hnew".
  wp_auto.
  iDestruct (own_type_pool_fresh_type p [] [] types with "Hnew Htypes") as "(Hnew & Htypes & %Hfresh)".
  wp_apply (wp_map_insert with "Htypesmap"). iIntros "Htypesmap".
  wp_auto.
  iAssert (own_type_pool (DfracOwn 1) (<[p := MkTypeState [] []]> types))
    with "[Htypes Hnew]" as "Htypes".
  { rewrite /own_type_pool big_sepM_insert; last exact Hfresh. iFrame "Htypes Hnew".
    iPureIntro. exact YjsArrInvariant_empty. }
  (* the fresh type is empty, so the item index is the same run map *)
  iDestruct "Hitems" as (items_mref) "(Hitemsf & Hitemmap)".
  have Hkpperm : cell_kp <$> all_cells (<[p := MkTypeState [] []]> types) ≡ₚ cell_kp <$> all_cells types
    by rewrite (all_cells_insert_empty types p [] Hfresh) //.
  iDestruct (own_item_map_kp_perm items_mref (DfracOwn 1) _ _ Hkpperm with "Hitemmap") as "Hitemmap".
  iApply ("HΦ" $! p).
  iSplitL "Hclient Hclock HdeletedSet Hitemsf Hitemmap Htypesf Htypesmap Htypes Hpending Hpdeletes"; last by iPureIntro.
  simpl.
  iApply (own_store_struct_intro _ (MkStoreState client0 k0 (<[p := MkTypeState [] []]> types) (<[nm := p]> bind) pend pdel)
            (conj (pool_invs_insert_empty types p Hfresh Hpool)
                  (registry_coh_bind_fresh bind types nm p _ Hp Hfresh Hreg))
            with "Hclient Hclock HdeletedSet [Hitemsf Hitemmap] [Htypesf Htypesmap] Htypes Hpending Hpdeletes").
  { iExists items_mref. iFrame "Hitemsf Hitemmap". }
  iExists types_mref. iFrame "Htypesf Htypesmap".
Qed.

(** [store.getOrCreateYType nm]: the root type bound to [nm], created empty
    and registered first when [nm] is unbound ([registry_lookup_or_create]). *)
Lemma wp_store__getOrCreateYType (s : loc) (st : store_state) (nm : go_string) :
  {{{ is_pkg_init yjs ∗ own_store_struct s st }}}
    s @! (go.PointerType yjs.store) @! "getOrCreateYType" #nm
  {{{ (p : loc) (types' : gmap loc type_state) (bind' : gmap P loc), RET #p;
      own_store_struct s (st <| ss_types := types' |> <| ss_bind := bind' |>) ∗
      ⌜registry_lookup_or_create (ss_types st) (ss_bind st) nm p types' bind'⌝ }}}.
Proof using Type*.
  iIntros (Φ) "(#Hpkg & Hcells) HΦ".
  destruct st as [client0 k0 types bind pend pdel]. simpl.
  destruct (bind !! nm) as [p|] eqn:Hb.
  - wp_apply (wp_store__getOrCreateYType_hit s (MkStoreState client0 k0 types bind pend pdel) nm p Hb with "[$Hcells]").
    iIntros "Hcells". iApply ("HΦ" $! p types bind). simpl. iFrame "Hcells".
    iPureIntro. left. split_and!; [exact Hb | reflexivity | reflexivity].
  - wp_apply (wp_store__getOrCreateYType_miss s (MkStoreState client0 k0 types bind pend pdel) nm Hb with "[$Hcells]").
    iIntros (p) "(Hcells & %Hfresh)".
    iApply ("HΦ" $! p _ _). iEval (simpl) in "Hcells". simpl. iFrame "Hcells".
    iPureIntro. right. split_and!; [exact Hb | exact Hfresh | reflexivity | reflexivity].
Qed.

(** [store.getOrCreateYType] at run granularity: the registry step read on
    [(locs, p)] ([pool_lookup_or_create]). Derived from
    [wp_store__getOrCreateYType] through the [pool_of] / [locs_of]
    projections. *)
Lemma wp_store__getOrCreateYType_runs (s : loc) (str : store_state_runs) (nm : go_string) :
  {{{ is_pkg_init yjs ∗ own_store_runs s str }}}
    s @! (go.PointerType yjs.store) @! "getOrCreateYType" #nm
  {{{ (q : loc) (p' : pool) (locs' : gmap loc (list loc)) (bind' : gmap P loc), RET #q;
      own_store_runs s (str <| sr_pool := p' |> <| sr_locs := locs' |>
                            <| sr_bind := bind' |>) ∗
      ⌜pool_lookup_or_create (sr_pool str) (sr_locs str) (sr_bind str) nm q p' locs' bind'⌝ }}}.
Proof using Type*.
  iIntros (Φ) "(#Hpkg & Hruns) HΦ".
  iEval (rewrite own_store_runs_as_state) in "Hruns".
  iDestruct "Hruns" as (st) "(%Hproj & Hcells)".
  subst str. destruct st as [client k0 types bind pend pdel]. simpl in *.
  wp_apply (wp_store__getOrCreateYType s (MkStoreState client k0 types bind pend pdel) nm
              with "[$Hpkg $Hcells]").
  iIntros (q types' bind') "(Hcells & %Hstep)".
  iEval (simpl) in "Hcells".
  iApply ("HΦ" $! q (pool_of types') (locs_of types') bind').
  iSplitL.
  { rewrite own_store_runs_as_state. iExists (MkStoreState client k0 types' bind' pend pdel).
    iFrame "Hcells". iPureIntro. rewrite /state_runs_of //=. }
  iPureIntro.
  exact (registry_lookup_or_create_to_pool types types' bind bind' nm q Hstep).
Qed.

(* ----- the general repair (issue #28 stage D2b) ---------------------------
   [store.repair] over the invariant-carrying split wrappers: the origin ids
   may address ANY char of their covering cells' runs; the clean-end /
   clean-start splits put them on run boundaries. The two splits are
   sequenced by the wrappers' transport records. *)




(** [store.repair] at run granularity: the origin slots [(q, k)] instead of
    cells ([pool_origins_covered], [pool_repair_parent]); the item comes back
    linked to run-boundary addresses read off the updated address map
    ([pool_origins_split]) and the pool steps by [pool_after_repair].
    Proved directly from the run-granular split helpers and
    [wp_store__getOrCreateYType_runs]: the clean-end split first, the right
    origin's slot relocated through [pool_after_split]'s coverage clause,
    the clean-start split second, and the left boundary carried across it
    by [pool_split_step_other_slot] (the two slots differ: the left result
    ends at the left origin, which same origin slots put strictly before
    the right one). *)
Lemma wp_store__repair_runs (s item_l pname : loc)
    (input : IntegrateInput (A := A)) (opn : option go_string)
    (str : store_state_runs) (orL orR : option (loc * nat)) (p_t : loc) :
  pool_origins_covered (sr_pool str) input orL orR ->
  pool_repair_parent (sr_bind str) opn orL orR p_t ->
  {{{ is_pkg_init yjs ∗
      own_linked_item item_l input null null null ∗
      is_parent_name pname opn ∗
      own_store_runs s str }}}
    s @! (go.PointerType yjs.store) @! "repair" #item_l #pname
  {{{ (lft rgt : loc) (p' : pool) (locs' : gmap loc (list loc)), RET #();
      own_linked_item item_l input p_t lft rgt ∗
      own_store_runs s (str <| sr_pool := p' |> <| sr_locs := locs' |>) ∗
      ⌜pool_after_repair (sr_pool str) p'⌝ ∗
      ⌜pool_origins_split p' locs' input orL orR lft rgt⌝ }}}.
Proof using Type*.
  move=> [HwL [HwR Hsame]] Hwpar.
  destruct str as [client0 k0 locs p bind pend pdel]. simpl in *.
  rewrite /pool_origin_covered in HwL HwR. rewrite /pool_repair_parent in Hwpar.
  iIntros (Φ) "(#Hpkg & Hlinked & #HisPN & Hruns) HΦ".
  iDestruct "Hlinked" as (itemVal oleft oright) "(Hraw & %Hfl & %Hfr & %Hfpar & %Hflags & %Hrunc)".
  iNamed "Hraw".
  iDestruct (own_store_runs_run_wf with "Hruns") as %Hwf0.
  iDestruct (own_store_runs_aligned with "Hruns") as %Haligned0.
  iDestruct (own_store_runs_covers_unique with "Hruns") as %Huniq0.
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
    wp_apply (wp_store__splitAtAndGetLeft_runs s idvL (MkStoreStateRuns client0 k0 locs p bind pend pdel)
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
    iDestruct (own_store_runs_run_wf with "Hruns") as %Hwf1.
    iDestruct (own_store_runs_aligned with "Hruns") as %Haligned1.
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
        have HcovR : pool_run_covers p qL kR (item_id (run_head_item rL)).
        { exists tmR, rL1. split_and!; [exact HpR | exact HrR |].
          rewrite -HrL1head. exact (Hhead_cov rL1 HrRwf). }
        have HcovL : pool_run_covers p qL kL (item_id (run_head_item rL)).
        { exists tmL, rL. split_and!; [exact HpL | exact HrL | exact (Hhead_cov rL HrLwf)]. }
        destruct (Huniq0 _ _ _ _ _ HcovR HcovL) as [_ HkeqLR]. subst kR.
        have := Hsame' eq_refl. lia. }
      wp_apply (wp_store__splitAtAndGetRight_runs s idvR (MkStoreStateRuns client0 k0 locs1 p1 bind pend pdel)
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
      have HendL2 : pool_run_ends_at p2 qL kL2 (toYjsId idvL).
      { exists tmL2. split; first exact HpL2. exists rL1. split_and!; [exact HrL2 | exact HrL1cl | exact HrL1end]. }
      have Hrepair2 : pool_after_repair p p2
        := pool_after_repair_trans _ _ _ Hrepair1 (pool_after_repair_of_split _ _ _ _ Hstep2).
      wp_auto.
      destruct opn as [nm|].
      * (* Parent::String *)
        iDestruct "HisPN" as "[%HnnP #HpnC]".
        rewrite (bool_decide_eq_false_2 (pname = null) HnnP) /=.
        wp_auto.
        wp_apply (wp_store__getOrCreateYType_runs s (MkStoreStateRuns client0 k0 locs2 p2 bind pend pdel) nm
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
        split.
        { rewrite HinlS /=. exists kL2. split; [exact HendL2 | exact HlocL2]. }
        { rewrite HinrS /=. exists kR2. split; [exact HstartR2 | exact HlocR2]. }
      * (* Parent::None: borrow from the resolved left neighbour *)
        iDestruct "HisPN" as "%HpN".
        rewrite (bool_decide_eq_true_2 (pname = null) HpN) /=.
        destruct (locs2 !! qL) as [lsL2|] eqn:HlsL2; last done. simpl in HlocL2.
        iDestruct (own_store_runs_node_acc s (MkStoreStateRuns client0 k0 locs2 p2 bind pend pdel)
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
      have HendL1' : pool_run_ends_at p1 qL kL (toYjsId idvL).
      { exists tmL1. split; first exact HpL1. exists rL1. split_and!; [exact HrL1 | exact HrL1cl | exact HrL1end]. }
      destruct opn as [nm|].
      * (* Parent::String *)
        iDestruct "HisPN" as "[%HnnP #HpnC]".
        rewrite (bool_decide_eq_false_2 (pname = null) HnnP) /=.
        wp_auto.
        wp_apply (wp_store__getOrCreateYType_runs s (MkStoreStateRuns client0 k0 locs1 p1 bind pend pdel) nm
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
        split.
        { rewrite HinlS /=. exists kL. split; [exact HendL1' | exact HlocL1]. }
        { rewrite HinrN //. }
      * (* Parent::None: borrow from the resolved left neighbour *)
        iDestruct "HisPN" as "%HpN".
        rewrite (bool_decide_eq_true_2 (pname = null) HpN) /=.
        destruct (locs1 !! qL) as [lsL1|] eqn:HlsL1; last done. simpl in HlocL1.
        iDestruct (own_store_runs_node_acc s (MkStoreStateRuns client0 k0 locs1 p1 bind pend pdel)
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
      wp_apply (wp_store__splitAtAndGetRight_runs s idvR (MkStoreStateRuns client0 k0 locs p bind pend pdel)
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
        wp_apply (wp_store__getOrCreateYType_runs s (MkStoreStateRuns client0 k0 locs1 p1 bind pend pdel) nm
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
        iDestruct (own_store_runs_node_acc s (MkStoreStateRuns client0 k0 locs1 p1 bind pend pdel)
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
      wp_apply (wp_store__getOrCreateYType_runs s (MkStoreStateRuns client0 k0 locs p bind pend pdel) nm
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
    registry's model agreement read at run granularity (the run form of
    [docm_cells_agree]). *)
Lemma docm_runs_agree (m : DocModel) (bind : gmap P loc) (p : pool) (d : YjsId) :
  pool_registry_models m bind p ->
  pool_registry_coh bind p ->
  (∀ parent tm, p !! parent = Some tm -> tm_arr tm = runs_flatten (tm_runs tm)) ->
  (∀ r, r ∈ all_runs p -> run_wf (run_items r)) ->
  (doc_model_has m d = true <-> ∃ q k, pool_run_covers p q k d).
Proof.
  move=> [Hmtypes Hmdom] [Hbindtypes [_ Htypesbound]] Harr Hrunwf. split.
  - move=> /docm_has_spec [t [x [Hx Hid]]].
    have Hne : doc_model_get m t ≠ [].
    { move=> Heq. move: Hx. rewrite Heq elem_of_nil //. }
    destruct (Hmdom t Hne) as (nm & q & -> & Hbnm).
    destruct (Hbindtypes nm q Hbnm) as [tm Htm].
    have Hdg : doc_model_get m (RootId nm) = tm_arr tm := Hmtypes nm q tm Hbnm Htm.
    rewrite Hdg (Harr q tm Htm) in Hx.
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
    rewrite Hdg (Harr q tm Htm).
    apply (list_elem_of_lookup_2 _
             (length (runs_flatten (take k (tm_runs tm))) +
              (clock d - clock (item_id (hd inhabitant (run_items r)))))%nat).
    exact (runs_flatten_lookup_of_run (tm_runs tm) k _ r ch Hk Hch).
Qed.

(** [store.hasNode] (issue #40 x issue #28 U7c) at run granularity: the
    arrival test the pending gate runs. Its result IS the model presence
    [doc_model_has m (toYjsId idv)]: [GetNode]'s covering slot is bridged to
    [doc_model_has] through the registry's model agreement
    ([pool_registry_models], [docm_runs_agree]). *)
Lemma wp_store__hasNode_runs (s : loc) (idv : yjs.id.t) (m : DocModel) (str : store_state_runs) :
  pool_registry_models m (sr_bind str) (sr_pool str) ->
  {{{ is_pkg_init yjs ∗ own_store_runs s str }}}
    s @! (go.PointerType yjs.store) @! "hasNode" #idv
  {{{ (ok : bool), RET #ok;
      own_store_runs s str ∗
      ⌜ok = true <-> doc_model_has m (toYjsId idv) = true⌝ }}}.
Proof using Type*.
  move=> Hregmodel.
  iIntros (Φ) "(#Hpkg & Hruns) HΦ".
  iDestruct (own_store_runs_registry_coh with "Hruns") as %Hpreg.
  iDestruct (own_store_runs_arr with "Hruns") as %Harr.
  iDestruct (own_store_runs_run_wf with "Hruns") as %Hwf.
  have Hagree : ∀ d : YjsId, doc_model_has m d = true <-> ∃ q k, pool_run_covers (sr_pool str) q k d
    := λ d, docm_runs_agree m (sr_bind str) (sr_pool str) d Hregmodel Hpreg Harr Hwf.
  wp_method_call. wp_call. wp_call. wp_auto.
  wp_apply (wp_store__GetNode_runs s idv str with "[$Hpkg $Hruns]").
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

(** [store.splitAtAndGetLeft] / [store.splitAtAndGetRight], unit fast path
    (issue #28 M2): with every run 1-char (the M1 all-singleton invariant) the
    found node already ends (resp. starts) at the requested id — the offset is
    0 and [Len() - 1] is 0 — so the split branch is dead and each helper
    coincides with [GetNode]. The general (actually splitting) specs arrive
    with the run-integrate milestone (M4), where runs become reachable. *)

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

(** [store.originArrived] (issue #40) at run granularity: the per-origin
    arrival check; a nil origin imposes no dependency. Its result is the
    model presence of the origin id (via [hasNode]). *)
Lemma wp_store__originArrived_runs (s : loc) (p : loc)
    (originId : option yjs.id.t) (m : DocModel) (str : store_state_runs) :
  pool_registry_models m (sr_bind str) (sr_pool str) ->
  {{{ is_pkg_init yjs ∗ is_origin_id p originId ∗ own_store_runs s str }}}
    s @! (go.PointerType yjs.store) @! "originArrived" #p
  {{{ (ok : bool), RET #ok;
      own_store_runs s str ∗
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
    wp_apply (wp_store__hasNode_runs s idv m str Hregmodel with "[$Hpkg $Hruns]").
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


(** [store.depsArrived] (issue #40) at run granularity: the structural
    gate, as arrival checks. The return value IS the pure gate [input_ready]
    of the decoded struct; each arrival check ([originArrived] / [hasNode])
    returns the model presence of a dependency, so the gate composes them by
    [input_ready_true_of] / [input_ready_false_of_dep]. *)
Lemma wp_store__depsArrived_runs (s : loc) (updateItemVal : yjs.updateItem.t)
    (typedInput : TId * IntegrateInput (A := A)) (m : DocModel) (str : store_state_runs) :
  pool_registry_models m (sr_bind str) (sr_pool str) ->
  {{{ is_pkg_init yjs ∗ is_update_item updateItemVal typedInput ∗ own_store_runs s str }}}
    s @! (go.PointerType yjs.store) @! "depsArrived" #updateItemVal
  {{{ RET #(input_ready m typedInput.2); own_store_runs s str }}}.
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
  wp_apply (wp_store__originArrived_runs s _ oleft m str Hregmodel with "[$Hpkg $HisL $Hruns]").
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
  wp_apply (wp_store__originArrived_runs s _ oright m str Hregmodel with "[$Hpkg $HisR $Hruns]").
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
    wp_apply (wp_store__hasNode_runs s _ m str Hregmodel with "[$Hpkg $Hruns]").
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

(** [store.repair], creation form (issue #54) at run granularity: an
    ORIGIN-FREE decoded item targeting a not-yet-registered root [nm]. Both
    origin [if]s are skipped, and the parent branch registers a fresh empty
    type through [getOrCreateYType]'s miss path; the item comes back linked
    to null/null under the fresh type [q]. Local: a stepping stone of
    [wp_store__integrateDecoded_unbound_runs]. *)
#[local] Lemma wp_store__repair_create_runs (s item_l pname : loc)
    (input : IntegrateInput (A := A)) (nm : go_string) (str : store_state_runs) :
  in_originId input = None ->
  in_rightOriginId input = None ->
  sr_bind str !! nm = None ->
  {{{ is_pkg_init yjs ∗
      own_linked_item item_l input null null null ∗
      is_parent_name pname (Some nm) ∗
      own_store_runs s str }}}
    s @! (go.PointerType yjs.store) @! "repair" #item_l #pname
  {{{ (q : loc), RET #();
      own_linked_item item_l input q null null ∗
      own_store_runs s (str <| sr_pool := <[q := MkTypeModel [] []]> (sr_pool str) |>
                            <| sr_locs := <[q := []]> (sr_locs str) |>
                            <| sr_bind := <[nm := q]> (sr_bind str) |>) ∗
      ⌜sr_pool str !! q = None⌝ }}}.
Proof using Type*.
  move=> HoL HoR Hnm.
  destruct str as [client0 k0 locs p bind pend pdel]. simpl in *.
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
  wp_apply (wp_store__getOrCreateYType_runs s (MkStoreStateRuns client0 k0 locs p bind pend pdel) nm
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

(** [store.integrateDecoded] (issue #40 x issue #28 U7c), the ready branch of
    the drain as a per-struct contract, at run granularity: the struct's
    target root is bound, its chained per-char op chunk realizes the run
    fold [Hall], and the pool advances to the model spliced at
    [typedInput.1]. The origins are resolved to slots of the target type
    through the flatten ([runs_flatten_lookup_run]), repaired onto run
    boundaries, and the resulting addresses fed to [Integrate] as cursors.
    Local: the bound-root case of [wp_store__integrateDecoded_runs]. *)
#[local] Lemma wp_store__integrateDecoded_bound_runs (s : loc)
    (updateItemVal : yjs.updateItem.t) (typedInput : TId * IntegrateInput (A := A))
    (m : DocModel) (str : store_state_runs)
    (newItem : YjsItem A) (arr2 : list (YjsItem A)) (nm : P) (p : loc) :
  typedInput.1 = RootId nm ->
  sr_bind str !! nm = Some p ->
  toItem typedInput.2 (doc_model_get m typedInput.1) = Some newItem ->
  IsItemValid newItem ->
  maximalId newItem (doc_model_get m typedInput.1) ->
  integrate_all (ops_of_input typedInput.2 (explode (in_content typedInput.2))) (doc_model_get m typedInput.1) = Some arr2 ->
  pool_run_clock_below (sr_pool str) (in_id typedInput.2) ->
  pool_registry_models m (sr_bind str) (sr_pool str) ->
  input_fits typedInput.2 ->
  {{{ is_pkg_init yjs ∗ is_update_item updateItemVal typedInput ∗ own_store_runs s str }}}
    s @! (go.PointerType yjs.store) @! "integrateDecoded" #updateItemVal
  {{{ (p' : pool) (locs' : gmap loc (list loc)), RET #();
      own_store_runs s (str <| sr_pool := p' |> <| sr_locs := locs' |>) ∗
      ⌜pool_registry_models (<[typedInput.1 := arr2]> m) (sr_bind str) p'⌝ ∗
      ⌜runs_within_or_from [typedInput] (all_runs (sr_pool str)) (all_runs p')⌝ ∗
      ⌜runs_integrate_live_refine typedInput.2 (all_runs (sr_pool str)) (all_runs p')⌝ }}}.
Proof using Type*.
  move=> Htieq Hbnm Htoit Hvld Hmax Hall Hgmax0 [Hmtypes Hmdom] Hnowrapc.
  destruct str as [client0 k0 locs p0 bind pend pdel]. simpl in *.
  iIntros (Φ) "(#Hpkg & #Hui & Hruns) HΦ".
  iDestruct "Hui" as (oleft oright opn)
    "(HisL & HisR & HisPN & %Hin_l & %Hin_r & %Hin_id & %Hin_c & %Hunonempty & %Htid & %Hborrow)".
  destruct typedInput as [typedInput2 input]. simpl in *. subst typedInput2.
  iDestruct (own_store_runs_run_wf with "Hruns") as %Hwf0.
  iDestruct (own_store_runs_arr with "Hruns") as %Harr0.
  iDestruct (own_store_runs_arr_inv with "Hruns") as %Harrinv0.
  iDestruct (own_store_runs_registry_coh with "Hruns") as %Hpreg0.
  have [Hbindtypes [Hbindinj Htypesbound]] := Hpreg0.
  have [tmj Htmj] : is_Some (p0 !! p) := Hbindtypes nm p Hbnm.
  have Hdgj : doc_model_get m (RootId nm) = tm_arr tmj := Hmtypes nm p tmj Hbnm Htmj.
  set (arrj := doc_model_get m (RootId nm)) in *.
  have Hinvj : YjsArrInvariant arrj by (rewrite Hdgj; exact (Harrinv0 p tmj Htmj)).
  have Hreprj : arrj = runs_flatten (tm_runs tmj) by (rewrite Hdgj; exact (Harr0 p tmj Htmj)).
  destruct (integrate_some input arrj newItem Hinvj Htoit) as [arrinput Hintginput].
  destruct (integrate_finds input arrj arrinput Hintginput) as (leftIdx & rightIdx & HfindL & HfindR).
  have Hwfj : ∀ r, r ∈ tm_runs tmj -> run_wf (run_items r).
  { move=> r Hr. apply Hwf0. apply (elem_of_all_runs p0 r). by exists p, tmj. }
  (* a char of the type's document sits in one of its runs *)
  have Hrunsw : ∀ (kn : nat) (it : YjsItem A), arrj !! kn = Some it ->
      ∃ (k off : nat) (r : ItemRun), tm_runs tmj !! k = Some r ∧ run_items r !! off = Some it ∧
        kn = (length (runs_flatten (take k (tm_runs tmj))) + off)%nat ∧
        run_client r = clientId (item_id it) ∧
        (run_clock r <= clock (item_id it))%nat ∧
        (clock (item_id it) < run_clock r + length (run_items r))%nat.
  { move=> kn it Hkn. rewrite Hreprj in Hkn.
    destruct (runs_flatten_lookup_run _ kn it Hkn) as (k & off & r & Hk & Hoff & Hpos).
    have Hwf : run_wf (run_items r) := Hwfj r (list_elem_of_lookup_2 _ _ _ Hk).
    have Hcid := run_wf_char_id (run_items r) off it Hwf Hoff.
    have Hlen := lookup_lt_Some _ _ _ Hoff.
    exists k, off, r. split_and!; [exact Hk | exact Hoff | exact Hpos | | |].
    - rewrite Hcid /run_client /run_head_item //=.
    - rewrite Hcid /run_clock /run_head_item /=. lia.
    - rewrite Hcid /run_clock /run_head_item /=. lia. }
  (* the origin slots: present origins resolve to the covering run of this
     type (that is where [toItem]'s find landed) *)
  have HocL : ∃ orL : option (loc * nat),
      pool_origin_covered p0 (in_originId input) orL ∧
      (match orL with Some qk => qk.1 = p | None => True end).
  { destruct (in_originId input) as [originIdLeft|] eqn:HoinL.
    - destruct (findLeftIdx_inv originIdLeft arrj leftIdx HfindL) as (kn & it & -> & Hkn & HidL).
      destruct (Hrunsw kn it Hkn) as (k & off & rL & HrLk & Hoff & Hpos & Hcl & Hle & Hlt).
      exists (Some (p, k)). split; last done. simpl.
      exists tmj, rL. split_and!;
        [exact Htmj | exact HrLk | rewrite -HidL; exact (conj Hcl (conj Hle Hlt))].
    - exists None. done. }
  have HocR : ∃ orR : option (loc * nat),
      pool_origin_covered p0 (in_rightOriginId input) orR ∧
      (match orR with Some qk => qk.1 = p | None => True end).
  { destruct (in_rightOriginId input) as [originIdRight|] eqn:HoinR.
    - destruct (findRightIdx_inv originIdRight arrj rightIdx HfindR) as (kn & it & -> & Hkn & HidR).
      destruct (Hrunsw kn it Hkn) as (k & off & rR & HrRk & Hoff & Hpos & Hcl & Hle & Hlt).
      exists (Some (p, k)). split; last done. simpl.
      exists tmj, rR. split_and!;
        [exact Htmj | exact HrRk | rewrite -HidR; exact (conj Hcl (conj Hle Hlt))].
    - exists None. done. }
  destruct HocL as (orL & HwL & HparL). destruct HocR as (orR & HwR & HparR).
  have Hwpar : pool_repair_parent bind opn orL orR p.
  { rewrite /pool_repair_parent. destruct opn as [nm'|].
    - have Hnmeq : RootId nm = RootId nm' := Htid nm' eq_refl. injection Hnmeq as <-. exact Hbnm.
    - destruct orL as [qk|]; [by rewrite HparL |].
      destruct orR as [qk|]; [by rewrite HparR |].
      destruct (Hborrow eq_refl) as [HL | HR].
      + move: HwL. by destruct (in_originId input).
      + move: HwR. by destruct (in_rightOriginId input). }
  (* both origins in one slot: doc order is clock order inside a run *)
  have Huniqj := yai_unique _ Hinvj.
  have HfLpj : findPtrIdx (origin newItem) arrj = Some leftIdx.
  { rewrite -(toitem_lemmas.findLeftIdx_findPtrIdx_eq input newItem arrj Huniqj Htoit). exact HfindL. }
  have HfRpj : findPtrIdx (rightOrigin newItem) arrj = Some rightIdx.
  { rewrite -(toitem_lemmas.findRightIdx_findPtrIdx_eq input newItem arrj Huniqj Htoit). exact HfindR. }
  have HorigAj := findptridx_getelem.findPtrIdx_ArrSet arrj (origin newItem) leftIdx HfLpj.
  have HrorAj := findptridx_getelem.findPtrIdx_ArrSet arrj (rightOrigin newItem) rightIdx HfRpj.
  have Hlrj := findptridx_order2.YjsLt'_findPtrIdx_lt arrj (origin newItem) (rightOrigin newItem)
                leftIdx rightIdx Hinvj HorigAj HrorAj (iiv_origin_lt _ Hvld) HfLpj HfRpj.
  have Hsameg : (match in_originId input, in_rightOriginId input, orL, orR with
    | Some a, Some b, Some qkL, Some qkR => qkL = qkR -> (clock a < clock b)%nat
    | _, _, _, _ => True end : Prop).
  { move: HwL HwR HparL HfindL HfindR.
    destruct (in_originId input) as [oL|] eqn:HoinL2; try done.
    destruct (in_rightOriginId input) as [oR|] eqn:HoinR2; try done.
    destruct orL as [[qL kL]|]; try done. destruct orR as [[qR kR]|]; try done.
    move=> [tmL [rL [HpL [HrL [HclL [HleL HltL]]]]]] [tmR [rR [HpR [HrR [HclR [HleR HltR]]]]]]
           HqL HfindL2 HfindR2 Heq.
    injection Heq as <- <-. simpl in HqL, HpL, HrL, HpR, HrR. subst qL.
    rewrite Htmj in HpL HpR. injection HpL as <-. injection HpR as <-.
    rewrite HrL in HrR. injection HrR as <-.
    have Hwf : run_wf (run_items rL) := Hwfj rL (list_elem_of_lookup_2 _ _ _ HrL).
    destruct (run_wf_char_at_clock (run_items rL) oL Hwf HclL HleL HltL) as (chL & HchL & HidchL).
    destruct (run_wf_char_at_clock (run_items rL) oR Hwf HclR HleR HltR) as (chR & HchR & HidchR).
    have HposL := runs_flatten_lookup_of_run (tm_runs tmj) kL _ rL chL HrL HchL.
    have HposR := runs_flatten_lookup_of_run (tm_runs tmj) kL _ rL chR HrL HchR.
    rewrite -Hreprj in HposL HposR.
    destruct (findLeftIdx_inv oL arrj leftIdx HfindL2) as (knL & itL & HeqL & HknL & HidL2).
    destruct (findRightIdx_inv oR arrj rightIdx HfindR2) as (knR & itR & HeqR & HknR & HidR2).
    set prefw := length (runs_flatten (take kL (tm_runs tmj))) in HposL HposR.
    have HknLp : knL = (prefw + (clock oL - clock (item_id (hd inhabitant (run_items rL)))))%nat.
    { set posL := (prefw + (clock oL - clock (item_id (hd inhabitant (run_items rL)))))%nat in HposL |- *.
      destruct (Nat.lt_trichotomy knL posL) as [Hlt2 | [Heq2 | Hgt2]]; [| exact Heq2 |]; exfalso.
      - have := uniqueId_lookup_ne arrj knL posL itL chL Huniqj HknL HposL Hlt2.
        rewrite HidL2 HidchL //.
      - have := uniqueId_lookup_ne arrj posL knL chL itL Huniqj HposL HknL Hgt2.
        rewrite HidL2 HidchL //. }
    have HknRp : knR = (prefw + (clock oR - clock (item_id (hd inhabitant (run_items rL)))))%nat.
    { set posR := (prefw + (clock oR - clock (item_id (hd inhabitant (run_items rL)))))%nat in HposR |- *.
      destruct (Nat.lt_trichotomy knR posR) as [Hlt2 | [Heq2 | Hgt2]]; [| exact Heq2 |]; exfalso.
      - have := uniqueId_lookup_ne arrj knR posR itR chR Huniqj HknR HposR Hlt2.
        rewrite HidR2 HidchR //.
      - have := uniqueId_lookup_ne arrj posR knR chR itR Huniqj HposR HknR Hgt2.
        rewrite HidR2 HidchR //. }
    have Hklt : (knL < knR)%nat by lia.
    lia. }
  wp_method_call. wp_call. wp_call. wp_auto.
  wp_func_call. wp_call. wp_auto.
  wp_alloc itv as "Hitv". wp_auto.
  set (itemVal := {| yjs.item.id' := updateItemVal.(yjs.updateItem.id');
                yjs.item.originLeftId' := updateItemVal.(yjs.updateItem.originLeftId');
                yjs.item.originRightId' := updateItemVal.(yjs.updateItem.originRightId');
                yjs.item.left' := null; yjs.item.right' := null;
                yjs.item.parent' := null;
                yjs.item.content' := {| yjs.content.content' := updateItemVal.(yjs.updateItem.content') |};
                yjs.item.flags' := W8 2 |}).
  iAssert (own_linked_item itv input null null null) with "[Hitv]" as "Hfresh".
  { iExists itemVal, oleft, oright. rewrite /own_fresh_item_raw.
    iFrame "Hitv HisL HisR". iPureIntro.
    split_and!;
      [exact Hin_l | exact Hin_r | exact Hin_id | exact Hin_c
      | reflexivity | reflexivity | reflexivity | reflexivity
      | exact Hunonempty]. }
  wp_apply (wp_store__repair_runs s itv (updateItemVal.(yjs.updateItem.parentName'))
              input opn (MkStoreStateRuns client0 k0 locs p0 bind pend pdel) orL orR p
              (conj HwL (conj HwR Hsameg)) Hwpar
              with "[$Hpkg $Hfresh $HisPN $Hruns]").
  iIntros (lft rgt p2 locs2) "(Hlinked & Hruns & %Hrep2 & %Hosplit)".
  iEval (simpl) in "Hruns".
  destruct Hosplit as [HbdL HbdR].
  iDestruct (own_store_runs_run_wf with "Hruns") as %Hwf2.
  iDestruct (own_store_runs_aligned with "Hruns") as %Haligned2.
  iDestruct (own_store_runs_arr with "Hruns") as %Harr2.
  have Hpres2 := proj1 Hrep2.
  have Hdom2 := proj1 (proj2 Hrep2).
  have Hwithin2 := proj1 (proj2 (proj2 (proj2 Hrep2))).
  have Hlive2 := proj2 (proj2 (proj2 (proj2 Hrep2))).
  destruct (Hdom2 p (mk_is_Some _ _ Htmj)) as [tm2 Htm2].
  destruct (Hpres2 p tm2 Htm2) as (tm0e & Htm0e & Harr2p & Hflat2p).
  rewrite Htmj in Htm0e. injection Htm0e as <-.
  have Harrj2 : tm_arr tm2 = arrj by rewrite Harr2p Hdgj //.
  have Hreprj2 : arrj = runs_flatten (tm_runs tm2) by rewrite -Harrj2; exact (Harr2 p tm2 Htm2).
  destruct (locs_aligned_lens _ _ Haligned2 p tm2 Htm2) as (ls2 & Hls2 & Hlen2).
  have Hwf2j : ∀ r, r ∈ tm_runs tm2 -> run_wf (run_items r).
  { move=> r Hr. apply Hwf2. apply (elem_of_all_runs p2 r). by exists p, tm2. }
  (* the cursors: the left boundary's successor and the right boundary *)
  have HcurLpack : ∃ curL2 : nat,
      (curL2 <= length (tm_runs tm2))%nat ∧
      (Z.of_nat (length (runs_flatten (take curL2 (tm_runs tm2)))) = leftIdx + 1)%Z ∧
      lft = loc_at ls2 (Z.of_nat curL2 - 1).
  { move: HbdL HparL HfindL.
    destruct (in_originId input) as [oL|] eqn:HoinL3; destruct orL as [[qL kL]|]; try done.
    - move=> [k' [HendL Hloc']] HqL HfindL3. simpl in HendL, Hloc', HqL. subst qL.
      destruct HendL as (tmE & HpE & rE & HrE & HclE & HendE).
      rewrite Htm2 in HpE. injection HpE as <-.
      have HwfE : run_wf (run_items rE) := Hwf2j rE (list_elem_of_lookup_2 _ _ _ HrE).
      have Hlen1 : (1 <= length (run_items rE))%nat.
      { destruct (run_items rE) eqn:Hrc; [exact (False_ind _ (proj1 HwfE eq_refl)) | simpl; lia]. }
      destruct (lookup_lt_is_Some_2 (run_items rE) (length (run_items rE) - 1)%nat ltac:(lia)) as [chL HchL].
      have HidchL : item_id chL = oL.
      { rewrite (run_wf_char_id _ _ _ HwfE HchL).
        destruct oL as [oc ok].
        (* no [simpl] here: it would unfold [inhabitant] under the [hd] *)
        have HclE' : clientId (item_id (hd inhabitant (run_items rE))) = oc := HclE.
        have HendE' : (clock (item_id (hd inhabitant (run_items rE))) + length (run_items rE))%nat
                    = (ok + 1)%nat := HendE.
        f_equal; [exact HclE' | lia]. }
      have HposL := runs_flatten_lookup_of_run (tm_runs tm2) k' _ rE chL HrE HchL.
      rewrite -Hreprj2 in HposL.
      destruct (findLeftIdx_inv oL arrj leftIdx HfindL3) as (knL & itL & HeqL & HknL & HidL2).
      have HknLp : knL = (length (runs_flatten (take k' (tm_runs tm2))) + (length (run_items rE) - 1))%nat.
      { set posL := (length (runs_flatten (take k' (tm_runs tm2))) + (length (run_items rE) - 1))%nat
          in HposL |- *.
        destruct (Nat.lt_trichotomy knL posL) as [Hlt2 | [Heq2 | Hgt2]]; [| exact Heq2 |]; exfalso.
        - have := uniqueId_lookup_ne arrj knL posL itL chL Huniqj HknL HposL Hlt2.
          rewrite HidL2 HidchL //.
        - have := uniqueId_lookup_ne arrj posL knL chL itL Huniqj HposL HknL Hgt2.
          rewrite HidL2 HidchL //. }
      exists (S k'). split_and!.
      + apply lookup_lt_Some in HrE. lia.
      + rewrite (runs_flatten_take_S _ _ _ HrE) length_app. lia.
      + rewrite Hls2 /= in Hloc'.
        rewrite /loc_at. replace (Z.of_nat (S k') - 1)%Z with (Z.of_nat k') by lia.
        rewrite decide_True; last lia. rewrite Nat2Z.id Hloc' //.
    - move=> Hlftnull _ HfindL3.
      move: HfindL3. rewrite /findLeftIdx. move=> [= <-].
      exists 0%nat. split_and!.
      + lia.
      + rewrite take_0 /runs_flatten /=. lia.
      + rewrite Hlftnull /loc_at. case_decide; [lia | done]. }
  have HcurRpack : ∃ curR2 : nat,
      (curR2 <= length (tm_runs tm2))%nat ∧
      (Z.of_nat (length (runs_flatten (take curR2 (tm_runs tm2)))) = rightIdx)%Z ∧
      rgt = loc_at ls2 (Z.of_nat curR2).
  { move: HbdR HparR HfindR.
    destruct (in_rightOriginId input) as [oR|] eqn:HoinR3; destruct orR as [[qR kR]|]; try done.
    - move=> [k' [HstartR Hloc']] HqR HfindR3. simpl in HstartR, Hloc', HqR. subst qR.
      destruct HstartR as (tmS & HpS & rS & HrS & HidS).
      rewrite Htm2 in HpS. injection HpS as <-.
      have HwfS : run_wf (run_items rS) := Hwf2j rS (list_elem_of_lookup_2 _ _ _ HrS).
      have Hhd : run_items rS !! 0%nat = Some (run_head_item rS).
      { rewrite /run_head_item. destruct HwfS as [Hne _]. by destruct (run_items rS). }
      have HposR := runs_flatten_lookup_of_run (tm_runs tm2) k' _ rS _ HrS Hhd.
      rewrite -Hreprj2 in HposR.
      destruct (findRightIdx_inv oR arrj rightIdx HfindR3) as (knR & itR & HeqR & HknR & HidR2).
      have HknRp : knR = (length (runs_flatten (take k' (tm_runs tm2))) + 0)%nat.
      { set posR := (length (runs_flatten (take k' (tm_runs tm2))) + 0)%nat in HposR |- *.
        destruct (Nat.lt_trichotomy knR posR) as [Hlt2 | [Heq2 | Hgt2]]; [| exact Heq2 |]; exfalso.
        - have := uniqueId_lookup_ne arrj knR posR itR _ Huniqj HknR HposR Hlt2.
          rewrite HidR2 HidS //.
        - have := uniqueId_lookup_ne arrj posR knR _ itR Huniqj HposR HknR Hgt2.
          rewrite HidR2 HidS //. }
      exists k'. split_and!.
      + apply lookup_lt_Some in HrS. lia.
      + lia.
      + rewrite Hls2 /= in Hloc'.
        rewrite /loc_at decide_True; last lia. rewrite Nat2Z.id Hloc' //.
    - move=> Hrgtnull _ HfindR3.
      move: HfindR3. rewrite /findRightIdx. move=> [= <-].
      exists (length (tm_runs tm2)). split_and!.
      + lia.
      + rewrite take_ge; last lia. rewrite -Hreprj2. lia.
      + rewrite Hrgtnull /loc_at. case_decide; [| lia].
        rewrite Nat2Z.id lookup_ge_None_2 //. lia. }
  destruct HcurLpack as (curL2 & HcurL2b & HcurL2 & HlftND).
  destruct HcurRpack as (curR2 & HcurR2b & HcurR2 & HrgtND).
  iEval (rewrite HlftND HrgtND) in "Hlinked".
  wp_auto.
  have Hgmaxj' : pool_run_clock_below p2 (in_id input) := pool_run_clock_below_within _ _ _ Hwithin2 Hgmax0.
  have Hres : origins_resolved (tm_runs tm2) (tm_arr tm2) input curL2 curR2.
  { exists leftIdx, rightIdx. rewrite Harrj2.
    split_and!; [exact HfindL | exact HfindR | exact HcurL2 | exact HcurL2b | exact HcurR2 | exact HcurR2b]. }
  have Hready : integrate_ready (tm_arr tm2) input newItem.
  { rewrite Harrj2. exact (conj Htoit (conj Hvld Hmax)). }
  have Hall' : integrate_all (ops_of_input input (explode (in_content input))) (tm_arr tm2) = Some arr2
    by rewrite Harrj2; exact Hall.
  wp_apply (wp_store__Integrate_runs s p null itv (MkStoreStateRuns client0 k0 locs2 p2 bind pend pdel)
              tm2 ls2 arr2 input newItem curL2 curR2
              (or_intror eq_refl) Htm2 Hls2 Hready Hnowrapc Hall' Hres Hgmaxj'
              with "[$Hpkg $Hruns $Hlinked]").
  iIntros (runs' ls' run) "(Hruns & %Hinv3 & %Hsplice & %Hden)".
  iEval (simpl) in "Hruns".
  destruct Hsplice as (idx & Hsp & Hls'eq).
  destruct Hsp as (Hidxb & Hile & Hruns'eq & Harr2eq).
  set (rn := MkItemRun run false).
  have Hperm : all_runs (<[p := MkTypeModel runs' arr2]> p2) ≡ₚ rn :: all_runs p2.
  { rewrite Hruns'eq. exact (all_runs_splice_perm p2 p tm2 idx rn arr2 Htm2). }
  destruct Hden as (Hrnid & Hrnorig & Hrnrorig & Hrnlen).
  have Hrnhead : item_id (run_head_item rn) = in_id input := Hrnid.
  have Hrncl : run_client rn = clientId (in_id input) by rewrite /run_client Hrnhead.
  have Hrnck : run_clock rn = clock (in_id input) by rewrite /run_clock Hrnhead.
  have Hrnlen' : length (run_items rn) = length (in_content input) := Hrnlen.
  iDestruct (own_store_runs_run_wf with "Hruns") as %Hwf3.
  have Hrnwf : run_wf (run_items rn).
  { apply Hwf3. simpl. rewrite Hperm. apply list_elem_of_here. }
  wp_auto.
  iApply ("HΦ" $! (<[p := MkTypeModel runs' arr2]> p2) (<[p := ls']> locs2)). simpl.
  iFrame "Hruns".
  iPureIntro. split_and!.
  - (* registry coherence at <[RootId nm := arr2]> m *)
    split; last first.
    { move=> t Hne. destruct (decide (t = RootId nm)) as [-> | Hnet].
      - exists nm, p. split; [reflexivity | exact Hbnm].
      - have Hnet' : t ≠ (RootId nm, input).1 := Hnet.
        rewrite docm_get_insert_ne // in Hne. exact (Hmdom t Hne). }
    move=> nm0 q0 tm Hbnm0.
    destruct (decide (q0 = p)) as [-> | Hne].
    + have Hnm0 : nm0 = nm := Hbindinj nm0 nm p Hbnm0 Hbnm.
      subst nm0. rewrite lookup_insert_eq. move=> [= <-].
      rewrite docm_get_insert_eq //.
    + rewrite lookup_insert_ne; last congruence.
      move=> Htm.
      have Hnenm : RootId nm0 ≠ RootId nm.
      { move=> [= Heqnm]. subst nm0. apply Hne.
        have : Some q0 = Some p by rewrite -Hbnm0 -Hbnm //.
        by move=> [=]. }
      rewrite docm_get_insert_ne //.
      destruct (Hpres2 q0 tm Htm) as (tmold & Hpold & Harrp & _).
      rewrite Harrp.
      exact (Hmtypes nm0 q0 tmold Hbnm0 Hpold).
  - (* provenance: an old run (inside a repaired one) or the new run *)
    move=> r Hr. rewrite Hperm in Hr. apply elem_of_cons in Hr as [-> | Hold].
    + right. exists (RootId nm, input). split_and!.
      * apply list_elem_of_singleton. reflexivity.
      * exact Hrncl.
      * change ((RootId nm, input).2) with input. rewrite Hrnck. lia.
      * change ((RootId nm, input).2) with input. rewrite Hrnck Hrnlen'. lia.
    + exact (runs_within_or_from_of_within [(RootId nm, input)] _ _ Hwithin2 r Hold).
  - (* the live refinement: repaired runs' chars come from live runs of the
       entry pool, and the spliced run's chars are the wire item's own *)
    apply (runs_integrate_live_refine_trans input _ (all_runs p2) _).
    { exact (runs_integrate_live_refine_of_live_refine input p0 p2 Hlive2). }
    apply (runs_integrate_live_refine_snoc input (all_runs p2) _ rn Hperm).
    move=> y Hy.
    apply list_elem_of_lookup in Hy as (o & Ho).
    have Hid := run_wf_char_id (run_items rn) o y Hrnwf Ho.
    have Hcl : clientId (item_id y) = clientId (in_id input).
    { rewrite Hid -Hrnhead /run_head_item //. }
    have Hck : clock (item_id y) = (clock (item_id (run_head_item rn)) + o)%nat by rewrite Hid //.
    rewrite Hrnhead in Hck.
    split; [exact Hcl | lia].
Qed.

(** [store.integrateDecoded], creation form (issue #54) at run granularity:
    an origin-free struct whose target root [nm] is not yet registered is
    integrated into a freshly created empty type, so the registry grows by
    [nm -> q] and the pool by a type at [q] carrying exactly this item's
    run. Local: the unbound-root case of [wp_store__integrateDecoded_runs]. *)
#[local] Lemma wp_store__integrateDecoded_unbound_runs (s : loc)
    (updateItemVal : yjs.updateItem.t) (typedInput : TId * IntegrateInput (A := A))
    (m : DocModel) (str : store_state_runs)
    (newItem : YjsItem A) (arr2 : list (YjsItem A)) (nm : P) :
  typedInput.1 = RootId nm ->
  sr_bind str !! nm = None ->
  in_originId typedInput.2 = None ->
  in_rightOriginId typedInput.2 = None ->
  doc_model_get m typedInput.1 = [] ->
  toItem typedInput.2 [] = Some newItem ->
  IsItemValid newItem ->
  maximalId newItem [] ->
  integrate_all (ops_of_input typedInput.2 (explode (in_content typedInput.2))) [] = Some arr2 ->
  pool_run_clock_below (sr_pool str) (in_id typedInput.2) ->
  pool_registry_models m (sr_bind str) (sr_pool str) ->
  input_fits typedInput.2 ->
  {{{ is_pkg_init yjs ∗ is_update_item updateItemVal typedInput ∗ own_store_runs s str }}}
    s @! (go.PointerType yjs.store) @! "integrateDecoded" #updateItemVal
  {{{ (p' : pool) (locs' : gmap loc (list loc)) (bind' : gmap P loc), RET #();
      own_store_runs s (str <| sr_pool := p' |> <| sr_locs := locs' |> <| sr_bind := bind' |>) ∗
      ⌜sr_bind str ⊆ bind'⌝ ∗
      ⌜pool_registry_models (<[typedInput.1 := arr2]> m) bind' p'⌝ ∗
      ⌜runs_within_or_from [typedInput] (all_runs (sr_pool str)) (all_runs p')⌝ ∗
      ⌜runs_integrate_live_refine typedInput.2 (all_runs (sr_pool str)) (all_runs p')⌝ }}}.
Proof using Type*.
  move=> Htieq Hbnm HoL HoR Hdgnil Htoit Hvld Hmax Hall Hgmax0 [Hmtypes Hmdom] Hnowrapc.
  destruct str as [client0 k0 locs p0 bind pend pdel]. simpl in *.
  iIntros (Φ) "(#Hpkg & #Hui & Hruns) HΦ".
  iDestruct "Hui" as (oleft oright opn)
    "(HisL & HisR & HisPN & %Hin_l & %Hin_r & %Hin_id & %Hin_c & %Hunonempty & %Htid & %Hborrow)".
  destruct typedInput as [typedInput2 input]. simpl in *. subst typedInput2.
  have HoleftN : oleft = None by (move: Hin_l; rewrite HoL; by destruct oleft).
  have HorightN : oright = None by (move: Hin_r; rewrite HoR; by destruct oright).
  subst oleft oright.
  have Hopn : opn = Some nm.
  { destruct opn as [nm'|].
    - have Ht := Htid nm' eq_refl. by injection Ht as ->.
    - exfalso. destruct (Hborrow eq_refl) as [Hc | Hc]; [exact (Hc HoL) | exact (Hc HoR)]. }
  subst opn.
  iDestruct (own_store_runs_registry_coh with "Hruns") as %Hpreg0.
  have [Hbindtypes [Hbindinj Htypesbound]] := Hpreg0.
  (* build the item *)
  wp_method_call. wp_call. wp_call. wp_auto.
  wp_func_call. wp_call. wp_auto.
  wp_alloc itv as "Hitv". wp_auto.
  set (itemVal := {| yjs.item.id' := updateItemVal.(yjs.updateItem.id');
                yjs.item.originLeftId' := updateItemVal.(yjs.updateItem.originLeftId');
                yjs.item.originRightId' := updateItemVal.(yjs.updateItem.originRightId');
                yjs.item.left' := null; yjs.item.right' := null;
                yjs.item.parent' := null;
                yjs.item.content' := {| yjs.content.content' := updateItemVal.(yjs.updateItem.content') |};
                yjs.item.flags' := W8 2 |}).
  iAssert (own_linked_item itv input null null null) with "[Hitv]" as "Hfresh".
  { iExists itemVal, None, None. rewrite /own_fresh_item_raw.
    iFrame "Hitv HisL HisR". iPureIntro.
    split_and!;
      [exact Hin_l | exact Hin_r | exact Hin_id | exact Hin_c
      | reflexivity | reflexivity | reflexivity | reflexivity
      | exact Hunonempty]. }
  wp_apply (wp_store__repair_create_runs s itv (updateItemVal.(yjs.updateItem.parentName'))
              input nm (MkStoreStateRuns client0 k0 locs p0 bind pend pdel) HoL HoR Hbnm
              with "[$Hpkg $Hfresh $HisPN $Hruns]").
  iIntros (q) "(Hlinked & Hruns & %Hfresh)".
  iEval (simpl) in "Hruns".
  (* [q] is not in the range of [bind] (it did not exist as a type) *)
  have Hpnotbound : ∀ name, bind !! name ≠ Some q.
  { move=> name Hb. have Hs := Hbindtypes name q Hb. rewrite Hfresh in Hs. by destruct Hs. }
  set (p2 := <[q := MkTypeModel [] []]> p0).
  set (locs2 := <[q := []]> locs).
  have Htm2 : p2 !! q = Some (MkTypeModel [] []) by rewrite /p2 lookup_insert_eq.
  have Hls2 : locs2 !! q = Some [] by rewrite /locs2 lookup_insert_eq.
  have Hac_empty : all_runs p2 ≡ₚ all_runs p0 := all_runs_insert_empty p0 q [] Hfresh.
  (* Integrate premises for the empty type *)
  have Hidnew_in : item_id newItem = in_id input := commutativity.toItem_id input [] newItem Htoit.
  have HfindL : findLeftIdx (in_originId input) (@nil (YjsItem A)) = Some (-1)%Z by rewrite HoL /findLeftIdx //.
  have HfindR : findRightIdx (in_rightOriginId input) (@nil (YjsItem A)) = Some 0%Z by rewrite HoR /findRightIdx /=.
  have Hgmaxj' : pool_run_clock_below p2 (in_id input).
  { move=> r Hr Hcl. apply Hgmax0; [| exact Hcl]. rewrite -Hac_empty. exact Hr. }
  have Hres : origins_resolved (@nil ItemRun) (@nil (YjsItem A)) input 0 0.
  { exists (-1)%Z, 0%Z. split_and!; [exact HfindL | exact HfindR | rewrite take_nil /runs_flatten /=; lia | lia | rewrite take_nil /runs_flatten /=; lia | lia]. }
  have HlinkL : (null : loc) = loc_at [] (Z.of_nat 0 - 1).
  { rewrite /loc_at. case_decide as Hd; [exfalso; lia | reflexivity]. }
  have HlinkR : (null : loc) = loc_at [] (Z.of_nat 0).
  { rewrite /loc_at. case_decide as Hd; [reflexivity | exfalso; lia]. }
  iEval (rewrite {1}HlinkL {1}HlinkR) in "Hlinked".
  have Hready : integrate_ready (tm_arr (MkTypeModel [] [])) input newItem := conj Htoit (conj Hvld Hmax).
  wp_auto.
  wp_apply (wp_store__Integrate_runs s q null itv (MkStoreStateRuns client0 k0 locs2 p2 (<[nm := q]> bind) pend pdel)
              (MkTypeModel [] []) [] arr2 input newItem 0 0
              (or_intror eq_refl) Htm2 Hls2 Hready Hnowrapc Hall Hres Hgmaxj'
              with "[$Hpkg $Hruns $Hlinked]").
  iIntros (runs' ls' run) "(Hruns & %Hinv3 & %Hsplice & %Hden)".
  iEval (simpl) in "Hruns".
  destruct Hsplice as (idx & Hsp & Hls'eq).
  destruct Hsp as (Hidxb & Hile & Hruns'eq & Harr2eq).
  set (rn := MkItemRun run false).
  have Hperm : all_runs (<[q := MkTypeModel runs' arr2]> p2) ≡ₚ rn :: all_runs p0.
  { rewrite Hruns'eq. rewrite (all_runs_splice_perm p2 q (MkTypeModel [] []) idx rn arr2 Htm2).
    rewrite Hac_empty //. }
  destruct Hden as (Hrnid & Hrnorig & Hrnrorig & Hrnlen).
  have Hrnhead : item_id (run_head_item rn) = in_id input := Hrnid.
  have Hrncl : run_client rn = clientId (in_id input) by rewrite /run_client Hrnhead.
  have Hrnck : run_clock rn = clock (in_id input) by rewrite /run_clock Hrnhead.
  have Hrnlen' : length (run_items rn) = length (in_content input) := Hrnlen.
  iDestruct (own_store_runs_run_wf with "Hruns") as %Hwf3.
  have Hrnwf : run_wf (run_items rn).
  { apply Hwf3. simpl. rewrite Hperm. apply list_elem_of_here. }
  wp_auto.
  iApply ("HΦ" $! (<[q := MkTypeModel runs' arr2]> p2) (<[q := ls']> locs2) (<[nm := q]> bind)). simpl.
  iFrame "Hruns".
  iPureIntro. split_and!.
  - exact (insert_subseteq bind nm q Hbnm).
  - (* registry coherence at <[RootId nm := arr2]> m *)
    split.
    { move=> name pl tm Hb Htm.
      rewrite /p2 insert_insert_eq in Htm.
      destruct (decide (name = nm)) as [-> | Hne].
      + rewrite lookup_insert_eq in Hb. injection Hb as <-.
        rewrite lookup_insert_eq in Htm. injection Htm as <-. simpl.
        rewrite docm_get_insert_eq //.
      + rewrite lookup_insert_ne // in Hb.
        have Hnenm : RootId name ≠ RootId nm by (move=> [= ?]; congruence).
        rewrite docm_get_insert_ne //.
        destruct (decide (pl = q)) as [-> | Hnep]; first by (exfalso; exact (Hpnotbound name Hb)).
        rewrite lookup_insert_ne // in Htm.
        exact (Hmtypes name pl tm Hb Htm). }
    { move=> t Hne.
      destruct (decide (t = RootId nm)) as [-> | Hnet].
      + exists nm, q. split; [done | by rewrite lookup_insert_eq].
      + rewrite docm_get_insert_ne // in Hne.
        destruct (Hmdom t Hne) as (name & pl & Heqt & Hb).
        exists name, pl. split; [exact Heqt |].
        rewrite lookup_insert_ne //. move=> ?; subst name. by rewrite Hbnm in Hb. }
  - (* provenance *)
    move=> r Hr. rewrite Hperm in Hr. apply elem_of_cons in Hr as [-> | Hold].
    + right. exists (RootId nm, input). split_and!.
      * apply list_elem_of_singleton. reflexivity.
      * exact Hrncl.
      * change ((RootId nm, input).2) with input. rewrite Hrnck. lia.
      * change ((RootId nm, input).2) with input. rewrite Hrnck Hrnlen'. lia.
    + left. exists r. split_and!; [exact Hold | done | lia | lia].
  - (* the live refinement: every old run survives verbatim and the only new
       run is the spliced one, whose chars are the wire item's own *)
    apply (runs_integrate_live_refine_snoc input (all_runs p0) _ rn Hperm).
    move=> y Hy.
    apply list_elem_of_lookup in Hy as (o & Ho).
    have Hid := run_wf_char_id (run_items rn) o y Hrnwf Ho.
    have Hcl : clientId (item_id y) = clientId (in_id input).
    { rewrite Hid -Hrnhead /run_head_item //. }
    have Hck : clock (item_id y) = (clock (item_id (run_head_item rn)) + o)%nat by rewrite Hid //.
    rewrite Hrnhead in Hck.
    split; [exact Hcl | lia].
Qed.

(** [store.integrateDecoded] at run granularity: the registry steps by
    [pool_registry_models] at the grown model, every new run sits inside an
    old one or inside the integrated item's range
    ([runs_within_or_from]), and the live chars refine up to the item's own
    ([runs_integrate_live_refine]). Proved directly: the bound-root and
    unbound-root cases above, dispatched on the registry. *)
Lemma wp_store__integrateDecoded_runs (s : loc)
    (updateItemVal : yjs.updateItem.t) (typedInput : TId * IntegrateInput (A := A))
    (m : DocModel) (str : store_state_runs)
    (newItem : YjsItem A) (arr2 : list (YjsItem A)) (nm : P) :
  typedInput.1 = RootId nm ->
  toItem typedInput.2 (doc_model_get m typedInput.1) = Some newItem ->
  IsItemValid newItem ->
  maximalId newItem (doc_model_get m typedInput.1) ->
  integrate_all (ops_of_input typedInput.2 (explode (in_content typedInput.2))) (doc_model_get m typedInput.1) = Some arr2 ->
  pool_run_clock_below (sr_pool str) (in_id typedInput.2) ->
  pool_registry_models m (sr_bind str) (sr_pool str) ->
  input_fits typedInput.2 ->
  {{{ is_pkg_init yjs ∗ is_update_item updateItemVal typedInput ∗ own_store_runs s str }}}
    s @! (go.PointerType yjs.store) @! "integrateDecoded" #updateItemVal
  {{{ (p' : pool) (locs' : gmap loc (list loc)) (bind' : gmap P loc), RET #();
      own_store_runs s (str <| sr_pool := p' |> <| sr_locs := locs' |> <| sr_bind := bind' |>) ∗
      ⌜sr_bind str ⊆ bind'⌝ ∗
      ⌜pool_registry_models (<[typedInput.1 := arr2]> m) bind' p'⌝ ∗
      ⌜runs_within_or_from [typedInput] (all_runs (sr_pool str)) (all_runs p')⌝ ∗
      ⌜runs_integrate_live_refine typedInput.2 (all_runs (sr_pool str)) (all_runs p')⌝ }}}.
Proof using Type*.
  move=> Htieq Htoit Hvld Hmax Hall Hgmax0 Hregmodel Hnowrapc.
  destruct str as [client0 k0 locs p0 bind pend pdel]. simpl in *.
  have [Hmtypes Hmdom] := Hregmodel.
  iIntros (Φ) "(#Hpkg & #Hui & Hruns) HΦ".
  destruct (bind !! nm) as [p|] eqn:Hbnm.
  - (* HIT: reuse the bound-root integrateDecoded; registry unchanged *)
    wp_apply (wp_store__integrateDecoded_bound_runs s updateItemVal typedInput m
                (MkStoreStateRuns client0 k0 locs p0 bind pend pdel)
                newItem arr2 nm p Htieq Hbnm Htoit Hvld Hmax Hall Hgmax0 Hregmodel Hnowrapc
                with "[$Hpkg $Hui $Hruns]").
    iIntros (p' locs') "(Hruns & %Hregmodel' & %Hprov' & %Hilr')".
    iApply ("HΦ" $! p' locs' bind). simpl.
    iFrame "Hruns".
    iPureIntro. split_and!; [done | exact Hregmodel' | exact Hprov' | exact Hilr'].
  - (* MISS: the target root is unbound, so origin-free; grow the registry *)
    have HoL : in_originId typedInput.2 = None.
    { destruct (in_originId typedInput.2) as [o|] eqn:Ho; [| done]. exfalso.
      have Hne : doc_model_get m typedInput.1 ≠ [].
      { apply (toItem_nonempty_of_origin _ _ newItem Htoit). left. by rewrite Ho. }
      destruct (Hmdom typedInput.1 Hne) as (name & pl & Heq & Hb).
      rewrite Htieq in Heq. injection Heq as ->. by rewrite Hb in Hbnm. }
    have HoR : in_rightOriginId typedInput.2 = None.
    { destruct (in_rightOriginId typedInput.2) as [o|] eqn:Ho; [| done]. exfalso.
      have Hne : doc_model_get m typedInput.1 ≠ [].
      { apply (toItem_nonempty_of_origin _ _ newItem Htoit). right. by rewrite Ho. }
      destruct (Hmdom typedInput.1 Hne) as (name & pl & Heq & Hb).
      rewrite Htieq in Heq. injection Heq as ->. by rewrite Hb in Hbnm. }
    have Hdgnil : doc_model_get m typedInput.1 = [].
    { destruct (doc_model_get m typedInput.1) as [|x l] eqn:Hdg; [done |]. exfalso.
      destruct (Hmdom typedInput.1 ltac:(rewrite Hdg //)) as (name & pl & Heq & Hb).
      rewrite Htieq in Heq. injection Heq as ->. by rewrite Hb in Hbnm. }
    rewrite Hdgnil in Htoit Hmax Hall.
    wp_apply (wp_store__integrateDecoded_unbound_runs s updateItemVal typedInput m
                (MkStoreStateRuns client0 k0 locs p0 bind pend pdel)
                newItem arr2 nm Htieq Hbnm HoL HoR Hdgnil Htoit Hvld Hmax Hall Hgmax0
                Hregmodel Hnowrapc
                with "[$Hpkg $Hui $Hruns]").
    iIntros (p' locs' bind') "Hpost".
    iApply ("HΦ" $! p' locs' bind' with "Hpost").
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
