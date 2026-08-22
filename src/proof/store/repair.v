(** store update path, repair + applyUpdate layer: [getOrCreateYType],
    [store.repair] ([wp_store__repair_split]), [integrateDecoded],
    [depsArrived], the [wire_*] drain machinery and the [own_store]-level
    certificate specs. Split out of [store/GetNode]; Requires the
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
Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO (gmap loc type_state)))}.

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
Lemma wp_store__getOrCreateYType (s : loc) (types : gmap loc type_state) (bind : gmap P loc)
    (nm : go_string) (p : loc) :
  bind !! nm = Some p ->
  {{{ is_pkg_init yjs ∗ own_store_core s types bind }}}
    s @! (go.PointerType yjs.store) @! "getOrCreateYType" #nm
  {{{ RET #p; own_store_core s types bind }}}.
Proof using Type*.
  move=> Hp.
  iIntros (Φ) "(#Hpkg & Hcore) HΦ". iNamed "Hcore". iNamed "Hregistry".
  wp_method_call. wp_call. wp_call. wp_auto.
  wp_apply (wp_map_lookup2 with "Htypesmap"). iIntros "Htypesmap".
  rewrite Hp /=.
  wp_auto.
  iApply "HΦ".
  iApply (own_store_core_intro _ _ _ Hpool Hreg with "Hitems [Htypesf Htypesmap] Htypes").
  iExists types_mref. iFrame "Htypesf Htypesmap".
Qed.

(** [store.getOrCreateYType], creation (miss) case (issue #54): the name is NOT
    bound, so the method allocates a fresh empty [yType] via [newYType],
    registers it under [nm], and returns it. The registry map grows by
    [nm -> p] and the per-type DLL big-op by a fresh EMPTY type at the
    genuinely fresh location [p]. The complement of [wp_store__getOrCreateYType]
    (the lookup-hit case); the ready branch of [applyUpdate] dispatches on the
    binding to pick between them. *)
Lemma wp_store__getOrCreateYType_miss (s : loc) (types : gmap loc type_state) (bind : gmap P loc)
    (nm : go_string) :
  bind !! nm = None ->
  {{{ is_pkg_init yjs ∗ own_store_core s types bind }}}
    s @! (go.PointerType yjs.store) @! "getOrCreateYType" #nm
  {{{ (p : loc), RET #p;
      own_store_core s (<[p := MkTypeState [] []]> types) (<[nm := p]> bind) ∗
      ⌜types !! p = None⌝ }}}.
Proof using Type*.
  move=> Hp.
  iIntros (Φ) "(#Hpkg & Hcore) HΦ". iNamed "Hcore". iNamed "Hregistry".
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
  iNamed "Hitems".
  have Hkpperm : cell_kp <$> all_cells (<[p := MkTypeState [] []]> types) ≡ₚ cell_kp <$> all_cells types
    by rewrite (all_cells_insert_empty types p [] Hfresh) //.
  iDestruct (own_item_map_kp_perm items_mref (DfracOwn 1) _ _ Hkpperm with "Hitemmap") as "Hitemmap".
  iApply ("HΦ" $! p). iSplitL; last done.
  iApply (own_store_core_intro _ _ _
            (pool_invs_insert_empty types p Hfresh Hpool)
            (registry_coh_bind_fresh bind types nm p _ Hp Hfresh Hreg)
            with "[Hitemsf Hitemmap] [Htypesf Htypesmap] Htypes").
  { iExists items_mref. iFrame "Hitemsf Hitemmap". }
  iExists types_mref. iFrame "Htypesf Htypesmap".
Qed.

(* ----- the general repair (issue #28 stage D2b) ---------------------------
   [store.repair] over the invariant-carrying split wrappers: the origin ids
   may address ANY char of their covering cells' runs; the clean-end /
   clean-start splits put them on run boundaries. The two splits are
   sequenced by the wrappers' transport records. *)

Lemma repair_types_update_rel_refl (types : gmap loc type_state) :
  repair_types_update_rel types types.
Proof.
  split_and!.
  - move=> p ts' Hp. exists ts'. split_and!; done.
  - move=> p Hp. exact Hp.
  - move=> kc. lia.
  - move=> p ts ts' Hp Hp' _. congruence.
  - move=> c' Hc'. exists c'. split_and!; [exact Hc' | done | lia | lia].
  - exact (live_refine_refl types).
Qed.

Lemma split_types_update_rel_single (types types1 : gmap loc type_state) (w : item_cell) :
  split_types_update_rel types types1 w -> repair_types_update_rel types types1.
Proof.
  move=> H. destruct H as (Hp & Hd & Hr & _ & _ & Hu & Hsub & Hlr & _).
  split_and!;
    [exact Hp | exact Hd | move=> kc; have := Hr kc; lia | exact Hu | exact Hsub | exact Hlr].
Qed.

Lemma split_types_update_rel_compose (types types1 types2 : gmap loc type_state) (w1 w2 : item_cell) :
  split_types_update_rel types types1 w1 -> split_types_update_rel types1 types2 w2 ->
  repair_types_update_rel types types2.
Proof.
  move=> H1 H2.
  destruct H1 as (Hp1 & Hd1 & Hr1 & _ & _ & Hu1 & Hsub1 & Hlr1 & _).
  destruct H2 as (Hp2 & Hd2 & Hr2 & _ & _ & Hu2 & Hsub2 & Hlr2 & _).
  split_and!.
  - move=> p ts2 Hp.
    destruct (Hp2 p ts2 Hp) as (ts1 & Hp1' & Ha2 & Hf2).
    destruct (Hp1 p ts1 Hp1') as (ts0 & Hp0 & Ha1 & Hf1).
    exists ts0. split_and!; [exact Hp0 | congruence | congruence].
  - move=> p Hp. exact (Hd2 p (Hd1 p Hp)).
  - move=> kc. have := Hr1 kc. have := Hr2 kc. lia.
  - move=> p ts ts2 Hpa Hpb Hunit.
    destruct (Hd1 p (mk_is_Some _ _ Hpa)) as [ts1 Hpm].
    have Hts1 : ts1 = ts := Hu1 p ts ts1 Hpa Hpm Hunit.
    subst ts1.
    exact (Hu2 p ts ts2 Hpm Hpb Hunit).
  - move=> c2 Hc2.
    destruct (Hsub2 c2 Hc2) as (c1 & Hc1 & Hcl2 & Hlo2 & Hhi2).
    destruct (Hsub1 c1 Hc1) as (c0 & Hc0 & Hcl1 & Hlo1 & Hhi1).
    exists c0. split_and!; [exact Hc0 | congruence | lia | lia].
  - exact (live_refine_trans types types1 types2 Hlr1 Hlr2).
Qed.

(** [store.repair], general splitting form (issue #28 stage D2b): the origin
    ids address arbitrary chars of their covering witness cells; repair puts
    both on run boundaries by splitting, and the item comes back linked to
    the boundary cells. The same-run premise (equal witnesses force the left
    origin strictly below the right one in clock) is what item validity
    provides: within one run, doc order is clock order, and an item's origin
    precedes its right origin. *)
Lemma wp_store__repair_split (s item_l pname : loc)
    (input : IntegrateInput (A := A)) (opn : option go_string)
    (types : gmap loc type_state) (bind : gmap P loc)
    (ocL ocR : option item_cell) (p_t : loc) :
  match in_originId input, ocL with
  | Some originId, Some c => c ∈ all_cells types ∧
      clientId (item_id (run_head c)) = clientId originId ∧
      (clock (item_id (run_head c)) <= clock originId)%nat ∧
      (clock originId < clock (item_id (run_head c)) + length (ic_run c))%nat
  | None, None => True
  | _, _ => False
  end ->
  match in_rightOriginId input, ocR with
  | Some originId, Some c => c ∈ all_cells types ∧
      clientId (item_id (run_head c)) = clientId originId ∧
      (clock (item_id (run_head c)) <= clock originId)%nat ∧
      (clock originId < clock (item_id (run_head c)) + length (ic_run c))%nat
  | None, None => True
  | _, _ => False
  end ->
  match in_originId input, in_rightOriginId input, ocL, ocR with
  | Some a, Some b, Some cL0, Some cR0 => cL0 = cR0 -> (clock a < clock b)%nat
  | _, _, _, _ => True
  end ->
  match opn with
  | Some nm => bind !! nm = Some p_t
  | None => match ocL with
            | Some c => p_t = ic_parent c
            | None => match ocR with
                      | Some c => p_t = ic_parent c
                      | None => False
                      end
            end
  end ->
  {{{ is_pkg_init yjs ∗
      own_linked_item_run item_l input null null null ∗
      is_parent_name pname opn ∗
      own_store_core s types bind }}}
    s @! (go.PointerType yjs.store) @! "repair" #item_l #pname
  {{{ (lft rgt : loc) (types2 : gmap loc type_state), RET #();
      own_linked_item_run item_l input p_t lft rgt ∗
      own_store_core s types2 bind ∗
      ⌜repair_types_update_rel types types2⌝ ∗
      ⌜match in_originId input, ocL with
       | Some originId, Some c0 => lft = ic_loc c0 ∧
           ∃ cL', cL' ∈ all_cells types2 ∧ ic_loc cL' = lft ∧
             cell_client cL' = W64 (clientId originId) ∧
             (uint.Z (cell_clock cL') + Z.of_nat (length (ic_run cL'))
              = Z.of_nat (clock originId) + 1)%Z ∧
             ic_parent cL' = ic_parent c0
       | None, None => lft = null
       | _, _ => False
       end⌝ ∗
      ⌜match in_rightOriginId input, ocR with
       | Some originId, Some c0 =>
           ∃ cR', cR' ∈ all_cells types2 ∧ ic_loc cR' = rgt ∧
             cell_client cR' = W64 (clientId originId) ∧
             (uint.Z (cell_clock cR') = Z.of_nat (clock originId))%Z ∧
             ic_parent cR' = ic_parent c0
       | None, None => rgt = null
       | _, _ => False
       end⌝ }}}.
Proof using Type*.
  move=> HwL HwR Hsame Hwpar.
  iIntros (Φ) "(#Hpkg & Hlinked & #HisPN & Hcore) HΦ". iNamed "Hcore".
  have [Hfits [Hnodup [Hrangedisj Horiginclk]]] := Hpool.
  iDestruct "Hlinked" as (itemVal oleft oright) "(Hraw & %Hfl & %Hfr & %Hfpar & %Hflags & %Hrunc)".
  iNamed "Hraw".
  iDestruct (own_type_pool_id_bounds with "Htypes") as %Hbnds0.
  have Hpinvs : pool_invs types := Hpool.

  wp_method_call. wp_call. wp_call. wp_auto.
  destruct oleft as [idvL|].
  - (* left origin present: clean-end split *)
    have HinlS : input.(in_originId) = Some (toYjsId idvL) by rewrite -Hin_l //.
    rewrite HinlS in HwL. destruct ocL as [cL|]; last done.
    destruct HwL as (HcLmem & HcLcl & HcLle & HcLlt).
    iDestruct "Holeft" as "[%HnnL #HolC]".
    rewrite (bool_decide_eq_false_2 (itemVal.(yjs.item.originLeftId') = null) HnnL) /=.
    wp_auto.
    have HcLbnd := proj2 (Hbnds0 cL HcLmem).
    have HcLccw : cell_client cL = idvL.(yjs.id.clientId').
    { rewrite /cell_client. move: HcLcl. rewrite /toYjsId /=. move=> ->. word. }
    have HcLleZ : (uint.Z (cell_clock cL) <= uint.Z idvL.(yjs.id.clock'))%Z.
    { move: HcLle. rewrite /toYjsId /= /cell_clock. move=> H. word. }
    have HcLltZ : (uint.Z idvL.(yjs.id.clock') < uint.Z (cell_clock cL) + Z.of_nat (length (ic_run cL)))%Z.
    { move: HcLlt. rewrite /toYjsId /= /cell_clock. move=> H. word. }
    wp_apply (wp_store__splitAtAndGetLeft_inv s idvL types cL
                HcLmem HcLccw HcLleZ HcLltZ Hpinvs
                with "[$Hpkg $Hitems $Htypes]").
    iIntros (types1) "(Hitems & Htypes & %Hpinvs1 & %Hstep1 & %HbdL)".
    have Hreg1 : registry_coh bind types1 := registry_coh_split_step _ _ _ _ Hstep1 Hreg.
    destruct HbdL as (cL1 & HcL1mem & HcL1loc & HcL1cl & HcL1end & HcL1par & HcL1start).
    wp_auto.
    destruct oright as [idvR|].
    + (* right origin present: relocate the witness, clean-start split *)
      have HinrS : input.(in_rightOriginId) = Some (toYjsId idvR) by rewrite -Hin_r //.
      rewrite HinrS in HwR. destruct ocR as [cR|]; last done.
      destruct HwR as (HcRmem & HcRcl & HcRle & HcRlt).
      rewrite HinlS HinrS in Hsame.
      have Hsame' : cL = cR -> (clock (toYjsId idvL) < clock (toYjsId idvR))%nat := Hsame.
      iDestruct "Horight" as "[%HnnR #HorC]".
      rewrite (bool_decide_eq_false_2 (itemVal.(yjs.item.originRightId') = null) HnnR) /=.
      wp_auto.
      have HcRbnd := proj2 (Hbnds0 cR HcRmem).
      have HcRccw : cell_client cR = idvR.(yjs.id.clientId').
      { rewrite /cell_client. move: HcRcl. rewrite /toYjsId /=. move=> ->. word. }
      have HcRleZ : (uint.Z (cell_clock cR) <= uint.Z idvR.(yjs.id.clock'))%Z.
      { move: HcRle. rewrite /toYjsId /= /cell_clock. move=> H. word. }
      have HcRltZ : (uint.Z idvR.(yjs.id.clock') < uint.Z (cell_clock cR) + Z.of_nat (length (ic_run cR)))%Z.
      { move: HcRlt. rewrite /toYjsId /= /cell_clock. move=> H. word. }
      have Hstep1' := Hstep1.
      destruct Hstep1' as (Hpres1 & Hdom1 & Hrl1 & Hstable1 & Hcover1 & Hunitp1 & Hsubc1 & Hlrc1 & Hdkc1).
      destruct (Hcover1 idvR.(yjs.id.clientId') (uint.Z idvR.(yjs.id.clock')) cR HcRmem HcRccw HcRleZ HcRltZ)
        as (cR1 & HcR1mem & HcR1cc & HcR1le & HcR1lt & HcR1parw & Hprov).
      destruct Hpinvs1 as (Hfits1 & Hnodup1 & Hrangedisj1 & Horiginclk1).
      have Hlocne : ic_loc cL1 ≠ ic_loc cR1.
      { move=> Heqloc.
        have Hceq : cL1 = cR1 := pool_loc_inj (all_cells types1) _ _ Hnodup1 HcL1mem HcR1mem Heqloc.
        have HleRL : (uint.Z idvR.(yjs.id.clock') <= uint.Z idvL.(yjs.id.clock'))%Z.
        { rewrite -Hceq in HcR1lt. clear -HcR1lt HcL1end. lia. }
        have Hfire : cL = cR -> False.
        { move=> HeqLR. have := Hsame' HeqLR. rewrite /toYjsId /=. move=> H.
          clear -H HleRL. word. }
        destruct Hprov as [Hc'c | [HcRcw _]].
        - have HlocRL : ic_loc cR = ic_loc cL.
          { rewrite -Hc'c -Hceq HcL1loc //. }
          exact (Hfire (eq_sym (pool_loc_inj (all_cells types) _ _ Hnodup HcRmem HcLmem HlocRL))).
        - exact (Hfire (eq_sym HcRcw)). }
      have Hpinvs1' : pool_invs types1 by (split_and!; assumption).
      wp_apply (wp_store__splitAtAndGetRight_inv s idvR types1 cR1
                  HcR1mem HcR1cc HcR1le HcR1lt Hpinvs1'
                  with "[$Hpkg $Hitems $Htypes]").
      iIntros (rl types2) "(Hitems & Htypes & %Hpinvs2 & %Hstep2 & %HbdR)".
      have Hreg2 : registry_coh bind types2 := registry_coh_split_step _ _ _ _ Hstep2 Hreg1.
      destruct HbdR as (cR2 & HcR2mem & HcR2loc & HcR2cl & HcR2clk & HcR2par).
      wp_auto.
      have Hstep2' := Hstep2.
      destruct Hstep2' as (Hpres2 & Hdom2 & Hrl2 & Hstable2 & Hcover2 & Hunitp2 & Hsubc2 & Hlrc2 & Hdkc2).
      have HcL2mem : cL1 ∈ all_cells types2 := Hstable2 cL1 HcL1mem Hlocne.
      have HparR : ic_parent cR2 = ic_parent cR by rewrite HcR2par HcR1parw //.
      destruct opn as [nm|].
      * (* Parent::String *)
        iDestruct "HisPN" as "[%HnnP #HpnC]".
        rewrite (bool_decide_eq_false_2 (pname = null) HnnP) /=.
        wp_auto.
        iDestruct (own_store_core_intro _ _ _ Hpinvs2 Hreg2 with "Hitems Hregistry Htypes") as "Hcore".
        wp_apply (wp_store__getOrCreateYType s types2 bind nm p_t Hwpar with "[$Hcore]").
        iIntros "Hcore".
        wp_auto.
        iApply ("HΦ" $! (ic_loc cL) rl types2).
        iFrame "Hcore".
        iSplitL "Hitem".
        { iExists _, (Some idvL), (Some idvR). rewrite /own_fresh_item_raw. simpl.
          iFrame "Hitem". iFrame "HolC HorC".
          iPureIntro. split_and!; try done. }
        iPureIntro. split_and!.
        { exact (split_types_update_rel_compose types types1 types2 cL cR1 Hstep1 Hstep2). }
        { rewrite HinlS /=. split; [done |].
          exists cL1. split_and!;
            [exact HcL2mem | rewrite HcL1loc // | | | rewrite HcL1par //].
          - rewrite HcL1cl /toYjsId /=. word.
          - move: HcL1end. rewrite /toYjsId /=. move=> H. word. }
        { rewrite HinrS /=.
          exists cR2. split_and!;
            [exact HcR2mem | exact HcR2loc | | | exact HparR].
          - rewrite HcR2cl /toYjsId /=. word.
          - move: HcR2clk. rewrite /toYjsId /=. move=> H. word. }
      * (* Parent::None: borrow from the resolved left neighbour *)
        iDestruct "HisPN" as "%HpN".
        rewrite (bool_decide_eq_true_2 (pname = null) HpN) /=.
        iDestruct (own_type_pool_acc types2 cL1 HcL2mem with "Htypes") as "Hacc".
        iNamed "Hacc".
        iDestruct (typed_pointsto_not_null with "Hval") as %HnnCL.
        iEval (rewrite HcL1loc) in "Hval".
        wp_auto.
        rewrite (bool_decide_eq_false_2 (cL.(ic_loc) = null) ltac:(rewrite -HcL1loc; exact HnnCL)) /=.
        wp_auto.
        iEval (rewrite -HcL1loc) in "Hval".
        iDestruct ("Hback" with "Hval") as "Htypes".
        rewrite Hpar HcL1par Hwpar.
        iDestruct (own_store_core_intro _ _ _ Hpinvs2 Hreg2 with "Hitems Hregistry Htypes") as "Hcore".
        iApply ("HΦ" $! (ic_loc cL) rl types2).
        iFrame "Hcore".
        iSplitL "Hitem".
        { iExists _, (Some idvL), (Some idvR). rewrite /own_fresh_item_raw. simpl.
          iFrame "Hitem". iFrame "HolC HorC".
          iPureIntro. split_and!; try done. }
        iPureIntro. split_and!.
        { exact (split_types_update_rel_compose types types1 types2 cL cR1 Hstep1 Hstep2). }
        { rewrite HinlS /=. split; [done |].
          exists cL1. split_and!;
            [exact HcL2mem | rewrite HcL1loc // | | | rewrite HcL1par //].
          - rewrite HcL1cl /toYjsId /=. word.
          - move: HcL1end. rewrite /toYjsId /=. move=> H. word. }
        { rewrite HinrS /=.
          exists cR2. split_and!;
            [exact HcR2mem | exact HcR2loc | | | exact HparR].
          - rewrite HcR2cl /toYjsId /=. word.
          - move: HcR2clk. rewrite /toYjsId /=. move=> H. word. }
    + (* no right origin *)
      have HinrN : input.(in_rightOriginId) = None by rewrite -Hin_r //.
      rewrite HinrN in HwR. destruct ocR as [cR|]; first done.
      iDestruct "Horight" as "%HnR".
      rewrite (bool_decide_eq_true_2 (itemVal.(yjs.item.originRightId') = null) HnR) /=.
      wp_auto.
      destruct opn as [nm|].
      * (* Parent::String *)
        iDestruct "HisPN" as "[%HnnP #HpnC]".
        rewrite (bool_decide_eq_false_2 (pname = null) HnnP) /=.
        wp_auto.
        iDestruct (own_store_core_intro _ _ _ Hpinvs1 Hreg1 with "Hitems Hregistry Htypes") as "Hcore".
        wp_apply (wp_store__getOrCreateYType s types1 bind nm p_t Hwpar with "[$Hcore]").
        iIntros "Hcore".
        wp_auto.
        iApply ("HΦ" $! (ic_loc cL) null types1).
        iFrame "Hcore".
        iSplitL "Hitem".
        { iExists _, (Some idvL), None. rewrite /own_fresh_item_raw. simpl.
          iFrame "Hitem". iFrame "HolC".
          iPureIntro. split_and!; try done. }
        iPureIntro. split_and!.
        { exact (split_types_update_rel_single types types1 cL Hstep1). }
        { rewrite HinlS /=. split; [done |].
          exists cL1. split_and!;
            [exact HcL1mem | rewrite HcL1loc // | | | rewrite HcL1par //].
          - rewrite HcL1cl /toYjsId /=. word.
          - move: HcL1end. rewrite /toYjsId /=. move=> H. word. }
        { rewrite HinrN //. }
      * (* Parent::None: borrow from the resolved left neighbour *)
        iDestruct "HisPN" as "%HpN".
        rewrite (bool_decide_eq_true_2 (pname = null) HpN) /=.
        iDestruct (own_type_pool_acc types1 cL1 HcL1mem with "Htypes") as "Hacc".
        iNamed "Hacc".
        iDestruct (typed_pointsto_not_null with "Hval") as %HnnCL.
        iEval (rewrite HcL1loc) in "Hval".
        wp_auto.
        rewrite (bool_decide_eq_false_2 (cL.(ic_loc) = null) ltac:(rewrite -HcL1loc; exact HnnCL)) /=.
        wp_auto.
        iEval (rewrite -HcL1loc) in "Hval".
        iDestruct ("Hback" with "Hval") as "Htypes".
        rewrite Hpar HcL1par Hwpar.
        iDestruct (own_store_core_intro _ _ _ Hpinvs1 Hreg1 with "Hitems Hregistry Htypes") as "Hcore".
        iApply ("HΦ" $! (ic_loc cL) null types1).
        iFrame "Hcore".
        iSplitL "Hitem".
        { iExists _, (Some idvL), None. rewrite /own_fresh_item_raw. simpl.
          iFrame "Hitem". iFrame "HolC".
          iPureIntro. split_and!; try done. }
        iPureIntro. split_and!.
        { exact (split_types_update_rel_single types types1 cL Hstep1). }
        { rewrite HinlS /=. split; [done |].
          exists cL1. split_and!;
            [exact HcL1mem | rewrite HcL1loc // | | | rewrite HcL1par //].
          - rewrite HcL1cl /toYjsId /=. word.
          - move: HcL1end. rewrite /toYjsId /=. move=> H. word. }
        { rewrite HinrN //. }
  - (* no left origin *)
    have HinlN : input.(in_originId) = None by rewrite -Hin_l //.
    rewrite HinlN in HwL. destruct ocL as [cL|]; first done.
    iDestruct "Holeft" as "%HnL".
    rewrite (bool_decide_eq_true_2 (itemVal.(yjs.item.originLeftId') = null) HnL) /=.
    wp_auto.
    destruct oright as [idvR|].
    + (* right origin present: clean-start split, no relocation *)
      have HinrS : input.(in_rightOriginId) = Some (toYjsId idvR) by rewrite -Hin_r //.
      rewrite HinrS in HwR. destruct ocR as [cR|]; last done.
      destruct HwR as (HcRmem & HcRcl & HcRle & HcRlt).
      iDestruct "Horight" as "[%HnnR #HorC]".
      rewrite (bool_decide_eq_false_2 (itemVal.(yjs.item.originRightId') = null) HnnR) /=.
      wp_auto.
      have HcRbnd := proj2 (Hbnds0 cR HcRmem).
      have HcRccw : cell_client cR = idvR.(yjs.id.clientId').
      { rewrite /cell_client. move: HcRcl. rewrite /toYjsId /=. move=> ->. word. }
      have HcRleZ : (uint.Z (cell_clock cR) <= uint.Z idvR.(yjs.id.clock'))%Z.
      { move: HcRle. rewrite /toYjsId /= /cell_clock. move=> H. word. }
      have HcRltZ : (uint.Z idvR.(yjs.id.clock') < uint.Z (cell_clock cR) + Z.of_nat (length (ic_run cR)))%Z.
      { move: HcRlt. rewrite /toYjsId /= /cell_clock. move=> H. word. }
      wp_apply (wp_store__splitAtAndGetRight_inv s idvR types cR
                  HcRmem HcRccw HcRleZ HcRltZ Hpinvs
                  with "[$Hpkg $Hitems $Htypes]").
      iIntros (rl types2) "(Hitems & Htypes & %Hpinvs2 & %Hstep2 & %HbdR)".
      have Hreg2 : registry_coh bind types2 := registry_coh_split_step _ _ _ _ Hstep2 Hreg.
      destruct HbdR as (cR2 & HcR2mem & HcR2loc & HcR2cl & HcR2clk & HcR2par).
      wp_auto.
      destruct opn as [nm|].
      * (* Parent::String *)
        iDestruct "HisPN" as "[%HnnP #HpnC]".
        rewrite (bool_decide_eq_false_2 (pname = null) HnnP) /=.
        wp_auto.
        iDestruct (own_store_core_intro _ _ _ Hpinvs2 Hreg2 with "Hitems Hregistry Htypes") as "Hcore".
        wp_apply (wp_store__getOrCreateYType s types2 bind nm p_t Hwpar with "[$Hcore]").
        iIntros "Hcore".
        wp_auto.
        iApply ("HΦ" $! null rl types2).
        iFrame "Hcore".
        iSplitL "Hitem".
        { iExists _, None, (Some idvR). rewrite /own_fresh_item_raw. simpl.
          iFrame "Hitem". iFrame "HorC".
          iPureIntro. split_and!; try done. }
        iPureIntro. split_and!.
        { exact (split_types_update_rel_single types types2 cR Hstep2). }
        { rewrite HinlN //. }
        { rewrite HinrS /=.
          exists cR2. split_and!;
            [exact HcR2mem | exact HcR2loc | | | exact HcR2par].
          - rewrite HcR2cl /toYjsId /=. word.
          - move: HcR2clk. rewrite /toYjsId /=. move=> H. word. }
      * (* Parent::None: borrow from the resolved right neighbour *)
        iDestruct "HisPN" as "%HpN".
        rewrite (bool_decide_eq_true_2 (pname = null) HpN) /=.
        have Hfl' : (itemVal <| yjs.item.right' := rl |>).(yjs.item.left') = null
          by simpl; exact Hfl.
        iDestruct (own_type_pool_acc types2 cR2 HcR2mem with "Htypes") as "Hacc".
        iNamed "Hacc".
        iDestruct (typed_pointsto_not_null with "Hval") as %HnnCR.
        iEval (rewrite HcR2loc) in "Hval".
        wp_auto.
        rewrite (bool_decide_eq_true_2 _ Hfl') /=.
        wp_auto.
        rewrite (bool_decide_eq_false_2 (rl = null) ltac:(rewrite -HcR2loc; exact HnnCR)) /=.
        wp_auto.
        iEval (rewrite -HcR2loc) in "Hval".
        iDestruct ("Hback" with "Hval") as "Htypes".
        rewrite Hpar HcR2par Hwpar.
        iDestruct (own_store_core_intro _ _ _ Hpinvs2 Hreg2 with "Hitems Hregistry Htypes") as "Hcore".
        iApply ("HΦ" $! null rl types2).
        iFrame "Hcore".
        iSplitL "Hitem".
        { iExists _, None, (Some idvR). rewrite /own_fresh_item_raw. simpl.
          iFrame "Hitem". iFrame "HorC".
          iPureIntro. split_and!; try done. }
        iPureIntro. split_and!.
        { exact (split_types_update_rel_single types types2 cR Hstep2). }
        { rewrite HinlN //. }
        { rewrite HinrS /=.
          exists cR2. split_and!;
            [exact HcR2mem | exact HcR2loc | | | exact HcR2par].
          - rewrite HcR2cl /toYjsId /=. word.
          - move: HcR2clk. rewrite /toYjsId /=. move=> H. word. }
    + (* no origins at all: Parent::None is ruled out by the premise *)
      have HinrN : input.(in_rightOriginId) = None by rewrite -Hin_r //.
      rewrite HinrN in HwR. destruct ocR as [cR|]; first done.
      iDestruct "Horight" as "%HnR".
      rewrite (bool_decide_eq_true_2 (itemVal.(yjs.item.originRightId') = null) HnR) /=.
      wp_auto.
      destruct opn as [nm|]; last done.
      iDestruct "HisPN" as "[%HnnP #HpnC]".
      rewrite (bool_decide_eq_false_2 (pname = null) HnnP) /=.
      wp_auto.
      iDestruct (own_store_core_intro _ _ _ Hpinvs Hreg with "Hitems Hregistry Htypes") as "Hcore".
      wp_apply (wp_store__getOrCreateYType s types bind nm p_t Hwpar with "[$Hcore]").
      iIntros "Hcore".
      wp_auto.
      iApply ("HΦ" $! null null types).
      iFrame "Hcore".
      iSplitL "Hitem".
      { iExists _, None, None. rewrite /own_fresh_item_raw. simpl.
        iFrame "Hitem".
        iPureIntro. split_and!; try done. }
      iPureIntro. split_and!.
      { exact (repair_types_update_rel_refl types). }
      { rewrite HinlN //. }
      { rewrite HinrN //. }
Qed.

(** [store.repair], creation form (issue #54): an ORIGIN-FREE decoded item
    targeting a not-yet-registered root [nm]. Both origin [if]s are skipped
    (the item has no origins), and the parent branch registers a fresh empty
    [yType] through [getOrCreateYType]'s miss path; the item comes back linked
    to null/null under the fresh type [p]. The complement of
    [wp_store__repair_split], which handles items whose target root is already
    bound; the per-client item map is untouched (no run is split). Local: a
    stepping stone of [wp_store__integrateDecoded_unbound]. *)
#[local] Lemma wp_store__repair_create (s item_l pname : loc)
    (input : IntegrateInput (A := A)) (nm : go_string)
    (types : gmap loc type_state) (bind : gmap P loc) :
  in_originId input = None ->
  in_rightOriginId input = None ->
  bind !! nm = None ->
  {{{ is_pkg_init yjs ∗
      own_linked_item_run item_l input null null null ∗
      is_parent_name pname (Some nm) ∗
      own_store_core s types bind }}}
    s @! (go.PointerType yjs.store) @! "repair" #item_l #pname
  {{{ (p : loc), RET #();
      own_linked_item_run item_l input p null null ∗
      own_store_core s (<[p := MkTypeState [] []]> types) (<[nm := p]> bind) ∗
      ⌜types !! p = None⌝ }}}.
Proof using Type*.
  move=> HoL HoR Hnm.
  iIntros (Φ) "(#Hpkg & Hlinked & #HisPN & Hcore) HΦ".
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
  wp_apply (wp_store__getOrCreateYType_miss s types bind nm Hnm with "[$Hcore]").
  iIntros (p) "(Hcore & %Hfresh)".
  wp_auto.
  iApply ("HΦ" $! p).
  iFrame "Hcore".
  iSplitL "Hitem".
  { iExists _, None, None. rewrite /own_fresh_item_raw. simpl.
    iFrame "Hitem".
    iPureIntro. split_and!; try done. }
  done.
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

(** A flattened index decomposes into (containing cell, offset, prefix sum). *)
Lemma run_flatten_lookup_cell (cells : list item_cell) (kn : nat) (it : YjsItem A) :
  run_flatten cells !! kn = Some it ->
  ∃ (ci off : nat) (c : item_cell), cells !! ci = Some c ∧ ic_run c !! off = Some it ∧
    kn = (length (run_flatten (take ci cells)) + off)%nat.
Proof.
  elim: cells kn => [| c0 cs IH] kn.
  { rewrite /run_flatten /= lookup_nil //. }
  rewrite run_flatten_cons => /lookup_app_Some [Hin | [Hge Hlk]].
  - exists 0%nat, kn, c0. split_and!; [done | done | rewrite take_0 /run_flatten //=].
  - destruct (IH _ Hlk) as (ci & off & c & Hci & Hoff & Hkn).
    exists (S ci), off, c. split_and!; [done | done |].
    rewrite /= run_flatten_cons length_app. lia.
Qed.

(** Under [uniqueId] the flattened position of a char is unique: any index
    holding the [off]-th char of cell [ci] IS prefix-sum + [off]. *)
Lemma uniqueId_flatten_char_index (cells : list item_cell)
    (ci off : nat) (c : item_cell) (x : YjsItem A) (kn : nat) :
  uniqueId (run_flatten cells) ->
  cells !! ci = Some c -> ic_run c !! off = Some x ->
  run_flatten cells !! kn = Some x ->
  kn = (length (run_flatten (take ci cells)) + off)%nat.
Proof.
  move=> Huniq Hci Hoff Hkn.
  have Hpos := run_flatten_lookup_of_cell cells ci off c x Hci Hoff.
  set pos := (length (run_flatten (take ci cells)) + off)%nat in Hpos |- *.
  destruct (Nat.lt_trichotomy kn pos) as [Hlt | [Heq | Hgt]]; [| exact Heq |].
  - exact (False_ind _ (uniqueId_lookup_ne _ kn pos x x Huniq Hkn Hpos Hlt eq_refl)).
  - exact (False_ind _ (uniqueId_lookup_ne _ pos kn x x Huniq Hpos Hkn Hgt eq_refl)).
Qed.


(** [store.hasNode] (issue #40 x issue #28 U7c): the arrival test the pending
    gate runs. Its result IS the model presence [doc_model_has m (toYjsId idv)]: the
    covering GetNode (W64 clock range) is bridged to the model per-char
    covering ([cell_covers], nat) through the cell id-bounds, then to
    [doc_model_has] through the store's model/cell agreement ([Hagree]). *)
Lemma wp_store__hasNode (s : loc) (idv : yjs.id.t)
    (m : DocModel) (types : gmap loc type_state) (bind : gmap P loc) :
  (∀ d : YjsId, doc_model_has m d = true <-> ∃ c, c ∈ all_cells types ∧ cell_covers c d) ->
  {{{ is_pkg_init yjs ∗ own_store_core s types bind }}}
    s @! (go.PointerType yjs.store) @! "hasNode" #idv
  {{{ (ok : bool), RET #ok;
      own_store_core s types bind ∗
      ⌜ok = true <-> doc_model_has m (toYjsId idv) = true⌝ }}}.
Proof using Type*.
  move=> Hagree.
  iIntros (Φ) "(#Hpkg & Hcore) HΦ". iNamed "Hcore".
  iDestruct (own_type_pool_id_bounds with "Htypes") as %Hcellbnd.
  (* the per-cell W64 <-> nat covering bridge *)
  have Hbridge : ∀ c, c ∈ all_cells types ->
      ((cell_client c = idv.(yjs.id.clientId') ∧
        (uint.Z (cell_clock c) <= uint.Z idv.(yjs.id.clock'))%Z ∧
        (uint.Z idv.(yjs.id.clock') < uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)))%Z)
       <-> cell_covers c (toYjsId idv)).
  { move=> c Hc. have [Hcb1 Hcb2] := Hcellbnd c Hc.
    rewrite /cell_covers /cell_client /cell_clock /toYjsId /=. split.
    - move=> [Ha [Hb Hd]]. split_and!.
      + have Hz : uint.Z (W64 (clientId (item_id (run_head c)))) = uint.Z idv.(yjs.id.clientId')
          by rewrite Ha. word.
      + word.
      + word.
    - move=> [Ha [Hb Hd]]. split_and!.
      + apply word.unsigned_inj. word.
      + word.
      + word. }
  wp_method_call. wp_call. wp_call. wp_auto.
  wp_apply (wp_store__GetNode_total s idv types Hpool with "[$Hitems $Htypes]").
  iIntros (l ok) "(Hitems & Htypes & %Hres)".
  wp_auto.
  iApply ("HΦ" $! ok).
  iSplitL "Hitems Hregistry Htypes";
    first (iApply (own_store_core_intro _ _ _ Hpool Hreg with "Hitems Hregistry Htypes")).
  iPureIntro. destruct ok.
  - split; [move=> _ | done].
    destruct Hres as (c & Hc & Hcc & Hle & Hlt & _).
    apply Hagree. exists c. split; [exact Hc |].
    apply (proj1 (Hbridge c Hc)). done.
  - split; [done | move=> Hdh].
    exfalso. apply Hagree in Hdh. destruct Hdh as (c & Hc & Hcov).
    have [Hcc [Hle Hlt]] := proj2 (Hbridge c Hc) Hcov.
    exact (Hres c Hc Hcc Hle Hlt).
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


Lemma docm_cells_agree (m : DocModel) (bind : gmap P loc)
    (types : gmap loc type_state) (d : YjsId) :
  (∀ name p ts, bind !! name = Some p -> types !! p = Some ts ->
     doc_model_get m (RootId name) = ty_arr ts) ->
  (∀ t, doc_model_get m t ≠ [] -> ∃ name p, t = RootId name ∧ bind !! name = Some p) ->
  (∀ name p, bind !! name = Some p -> is_Some (types !! p)) ->
  (∀ p, is_Some (types !! p) -> ∃ name, bind !! name = Some p) ->
  (∀ p ts, types !! p = Some ts -> cells_repr (ty_arr ts) (ty_cells ts) (ty_arr ts)) ->
  (∀ c, c ∈ all_cells types -> run_wf (ic_run c)) ->
  (doc_model_has m d = true <-> ∃ c, c ∈ all_cells types ∧ cell_covers c d).
Proof.
  move=> Hmtypes Hmdom Hbindtypes Htypesbound Hreprall Hrunwf. split.
  - move=> /docm_has_spec [t [x [Hx Hid]]].
    have Hne : doc_model_get m t ≠ [].
    { move=> Heq. move: Hx. rewrite Heq elem_of_nil //. }
    destruct (Hmdom t Hne) as (nm & p & -> & Hbnm).
    destruct (Hbindtypes nm p Hbnm) as [ts Hts].
    have Hdg : doc_model_get m (RootId nm) = ty_arr ts := Hmtypes nm p ts Hbnm Hts.
    have Hrep : ty_arr ts = run_flatten (ty_cells ts) := Hreprall p ts Hts.
    rewrite Hdg Hrep in Hx.
    apply list_elem_of_lookup_1 in Hx as [kn Hkn].
    destruct (run_flatten_lookup_cell (ty_cells ts) kn x Hkn) as (ci & off & c & Hci & Hoff & _).
    have Hcin : c ∈ ty_cells ts := list_elem_of_lookup_2 _ _ _ Hci.
    have Hcall : c ∈ all_cells types by (apply all_cells_elem_of; exists p, ts; by split).
    have Hwf : run_wf (ic_run c) := Hrunwf c Hcall.
    have Hofflt : (off < length (ic_run c))%nat := lookup_lt_Some _ _ _ Hoff.
    have Hxid := run_wf_char_id (ic_run c) off x Hwf Hoff.
    rewrite Hid in Hxid.
    exists c. split; [exact Hcall |].
    rewrite /cell_covers /run_head. rewrite Hxid /=.
    split_and!; [done | lia | lia].
  - move=> [c [Hc [Hcl [Hle Hlt]]]].
    apply docm_has_spec.
    have Hwf : run_wf (ic_run c) := Hrunwf c Hc.
    apply all_cells_elem_of in Hc. destruct Hc as (p & ts & Hts & Hcts).
    destruct (Htypesbound p (ex_intro _ ts Hts)) as [nm Hbnm].
    have Hdg : doc_model_get m (RootId nm) = ty_arr ts := Hmtypes nm p ts Hbnm Hts.
    have Hrep : ty_arr ts = run_flatten (ty_cells ts) := Hreprall p ts Hts.
    destruct (run_wf_char_at_clock (ic_run c) d Hwf Hcl Hle Hlt) as (ch & Hch & Hchid).
    exists (RootId nm), ch. split; [| exact Hchid].
    rewrite Hdg Hrep.
    apply list_elem_of_lookup_1 in Hcts as [ci Hci].
    apply (list_elem_of_lookup_2 _
             (length (run_flatten (take ci (ty_cells ts))) +
              (clock d - clock (item_id (run_head c))))%nat).
    exact (run_flatten_lookup_of_cell (ty_cells ts) ci _ c ch Hci Hch).
Qed.

(* ----- the arrival gate ----- *)
(* (the pure gate lemmas [input_ready_false_of_dep] / [input_ready_true_of] /
   [input_deps_*] live in [network_model] with the pending theory) *)

(** [store.originArrived] (issue #40): the per-origin arrival check; a nil
    origin imposes no dependency. Its result is the model presence of the
    origin id (via [hasNode]). *)
Lemma wp_store__originArrived (s : loc) (p : loc)
    (originId : option yjs.id.t) (m : DocModel) (types : gmap loc type_state)
    (bind : gmap P loc) :
  (∀ d : YjsId, doc_model_has m d = true <-> ∃ c, c ∈ all_cells types ∧ cell_covers c d) ->
  {{{ is_pkg_init yjs ∗ is_origin_id p originId ∗ own_store_core s types bind }}}
    s @! (go.PointerType yjs.store) @! "originArrived" #p
  {{{ (ok : bool), RET #ok;
      own_store_core s types bind ∗
      ⌜ok = true <-> match originId with
                     | None => True
                     | Some idv => doc_model_has m (toYjsId idv) = true
                     end⌝ }}}.
Proof using Type*.
  move=> Hagree.
  iIntros (Φ) "(#Hpkg & #HisP & Hcore) HΦ".
  wp_method_call. wp_call. wp_call. wp_auto.
  destruct originId as [idv |]; simpl.
  - (* a real origin: dereference and probe *)
    iDestruct "HisP" as "[%Hpne #Hpid]".
    rewrite bool_decide_eq_false_2; last first.
    { move=> Heq. exact (Hpne Heq). }
    wp_auto.
    wp_apply (wp_store__hasNode s idv m types bind Hagree with "[$Hcore]").
    iIntros (ok) "(Hcore & %Hok)".
    wp_auto.
    iApply ("HΦ" $! ok).
    iFrame "Hcore".
    iPureIntro. exact Hok.
  - (* nil origin: no dependency *)
    iDestruct "HisP" as %->.
    rewrite bool_decide_eq_true_2 //.
    wp_auto.
    iApply ("HΦ" $! true).
    iFrame "Hcore".
    iPureIntro. done.
Qed.

(** [store.depsArrived] (issue #40): the structural gate, as arrival checks.
    The return value IS the pure gate [input_ready] of the decoded struct; each
    arrival check ([originArrived] / [hasNode]) returns the model presence of a
    dependency, so the gate composes them by [input_ready_true_of] /
    [input_ready_false_of_dep]. *)
Lemma wp_store__depsArrived (s : loc) (updateItemVal : yjs.updateItem.t)
    (typedInput : TId * IntegrateInput (A := A)) (m : DocModel) (types : gmap loc type_state)
    (bind : gmap P loc) :
  (∀ d : YjsId, doc_model_has m d = true <-> ∃ c, c ∈ all_cells types ∧ cell_covers c d) ->
  {{{ is_pkg_init yjs ∗ is_update_item updateItemVal typedInput ∗ own_store_core s types bind }}}
    s @! (go.PointerType yjs.store) @! "depsArrived" #updateItemVal
  {{{ RET #(input_ready m typedInput.2); own_store_core s types bind }}}.
Proof using Type*.
  move=> Hagree.
  iIntros (Φ) "(#Hpkg & #Hui & Hcore) HΦ".
  iDestruct "Hui" as (oleft oright opn)
    "(HisL & HisR & HisPN & %Hin_l & %Hin_r & %Hin_id & %Hin_c & %Hunonempty & %Htid & %Hborrow)".
  have Hcid : clientId (in_id typedInput.2) = uint.nat updateItemVal.(yjs.updateItem.id').(yjs.id.clientId').
  { rewrite -Hin_id /toYjsId //. }
  have Hck : clock (in_id typedInput.2) = uint.nat updateItemVal.(yjs.updateItem.id').(yjs.id.clock').
  { rewrite -Hin_id /toYjsId //. }
  wp_method_call. wp_call. wp_call. wp_auto.
  (* ---- left origin ---- *)
  wp_apply (wp_store__originArrived s _ oleft m types bind Hagree with "[$HisL $Hcore]").
  iIntros (okL) "(Hcore & %HokL)".
  wp_auto.
  destruct okL; last first.
  { (* left origin missing *)
    wp_auto.
    have Hready : input_ready m typedInput.2 = false.
    { destruct oleft as [idL |]; simpl in Hin_l; last first.
      { exfalso. destruct HokL as [_ H2]. have := H2 I. discriminate. }
      apply (input_ready_false_of_dep m typedInput.2 (toYjsId idL)).
      - apply input_deps_originL. rewrite -Hin_l //.
      - apply not_true_iff_false => Hd.
        destruct HokL as [_ H2]. have := H2 Hd. discriminate. }
    iEval (rewrite Hready) in "HΦ".
    iApply ("HΦ" with "[$Hcore]"). }
  wp_auto.
  (* ---- right origin ---- *)
  wp_apply (wp_store__originArrived s _ oright m types bind Hagree with "[$HisR $Hcore]").
  iIntros (okR) "(Hcore & %HokR)".
  wp_auto.
  destruct okR; last first.
  { (* right origin missing *)
    wp_auto.
    have Hready : input_ready m typedInput.2 = false.
    { destruct oright as [idR |]; simpl in Hin_r; last first.
      { exfalso. destruct HokR as [_ H2]. have := H2 I. discriminate. }
      apply (input_ready_false_of_dep m typedInput.2 (toYjsId idR)).
      - apply input_deps_originR. rewrite -Hin_r //.
      - apply not_true_iff_false => Hd.
        destruct HokR as [_ H2]. have := H2 Hd. discriminate. }
    iEval (rewrite Hready) in "HΦ".
    iApply ("HΦ" with "[$Hcore]"). }
  wp_auto.
  (* the origin facts carried into the tail *)
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
  - (* clock > 0: probe (client, clock-1) *)
    apply bool_decide_eq_true_1 in Hckpos.
    wp_auto.
    wp_apply (wp_NewId updateItemVal.(yjs.updateItem.id').(yjs.id.clientId')
                (word.sub updateItemVal.(yjs.updateItem.id').(yjs.id.clock') (W64 1))).
    wp_apply (wp_store__hasNode s _ m types bind Hagree with "[$Hcore]").
    iIntros (okP) "(Hcore & %HokP)".
    wp_auto.
    have Hpredid : toYjsId (yjs.id.mk updateItemVal.(yjs.updateItem.id').(yjs.id.clientId')
                     (word.sub updateItemVal.(yjs.updateItem.id').(yjs.id.clock') (W64 1)))
                 = MkYjsId (clientId (in_id typedInput.2)) (clock (in_id typedInput.2) - 1)%nat.
    { rewrite /toYjsId /= Hcid Hck. f_equal. word. }
    have Hckform : ∃ k, clock (in_id typedInput.2) = S k ∧ (k = clock (in_id typedInput.2) - 1)%nat.
    { exists (clock (in_id typedInput.2) - 1)%nat. rewrite Hck. split; [word | done]. }
    destruct Hckform as (k & HckS & Hkval).
    destruct okP; last first.
    + (* predecessor missing *)
      wp_auto.
      have Hready : input_ready m typedInput.2 = false.
      { apply (input_ready_false_of_dep m typedInput.2 (MkYjsId (clientId (in_id typedInput.2)) k)).
        - exact (input_deps_pred typedInput.2 k HckS).
        - apply not_true_iff_false => Hd.
          destruct HokP as [_ H2].
          rewrite Hpredid -Hkval in H2.
          have := H2 Hd. discriminate. }
      iEval (rewrite Hready) in "HΦ".
      iApply ("HΦ" with "[$Hcore]").
    + (* everything arrived *)
      wp_auto.
      have Hready : input_ready m typedInput.2 = true.
      { apply input_ready_true_of; [exact HLarr | exact HRarr |].
        move=> k' Hk'.
        have Hkk : k' = k by lia.
        rewrite Hkk Hkval.
        have HP := proj1 HokP eq_refl. rewrite Hpredid in HP. exact HP. }
      iEval (rewrite Hready) in "HΦ".
      iApply ("HΦ" with "[$Hcore]").
  - (* clock 0: no predecessor *)
    apply bool_decide_eq_false_1 in Hckpos.
    wp_auto.
    have Hready : input_ready m typedInput.2 = true.
    { apply input_ready_true_of; [exact HLarr | exact HRarr |].
      move=> k' Hk'. exfalso. rewrite Hck in Hk'. word. }
    iEval (rewrite Hready) in "HΦ".
    iApply ("HΦ" with "[$Hcore]").
Qed.

(* ----- the ready step: one decoded struct, repaired and integrated ----- *)

(** [store.integrateDecoded] (issue #40 x issue #28 U7c): the ready branch of
    the drain, as a per-struct contract -- the loop-free core of the batch
    loop. The struct's target root must be bound ([Hbnm]; the #49 pre-bound-
    roots restriction), its chained per-char op chunk realizes the run fold
    [Hall = integrate_all (ops_of_input ...)], its head-op scan facts hold at
    the current model, and the heap advances to the model spliced at [typedInput.1]
    with the four store-lock pool invariants maintained. Mirrors one iteration
    of the whole-batch [wp_store__applyUpdate_unlocked] body. Local: the
    bound-root case of [wp_store__integrateDecoded] below. *)
#[local] Lemma wp_store__integrateDecoded_bound (s : loc)
    (updateItemVal : yjs.updateItem.t) (typedInput : TId * IntegrateInput (A := A))
    (m : DocModel) (types : gmap loc type_state) (bind : gmap P loc)
    (newItem : YjsItem A) (arr2 : list (YjsItem A)) (nm : P) (p : loc) :
  typedInput.1 = RootId nm ->
  bind !! nm = Some p ->
  toItem typedInput.2 (doc_model_get m typedInput.1) = Some newItem ->
  IsItemValid newItem ->
  maximalId newItem (doc_model_get m typedInput.1) ->
  integrate_all (ops_of_input typedInput.2 (explode (in_content typedInput.2))) (doc_model_get m typedInput.1) = Some arr2 ->
  (∀ c0, c0 ∈ all_cells types -> cell_client c0 = W64 (clientId (in_id typedInput.2)) ->
     (uint.Z (cell_clock c0) < uint.Z (W64 (clock (in_id typedInput.2))))%Z ∧
     (uint.Z (cell_clock c0) + Z.of_nat (length (ic_run c0)) <= uint.Z (W64 (clock (in_id typedInput.2))))%Z) ->
  (∀ name p' ts, bind !! name = Some p' -> types !! p' = Some ts ->
     doc_model_get m (RootId name) = ty_arr ts) ->
  (Z.of_nat (clock (in_id typedInput.2)) + Z.of_nat (length (in_content typedInput.2)) < 2^64)%Z ->
  {{{ is_pkg_init yjs ∗ is_update_item updateItemVal typedInput ∗ own_store_core s types bind }}}
    s @! (go.PointerType yjs.store) @! "integrateDecoded" #updateItemVal
  {{{ (types' : gmap loc type_state), RET #();
      own_store_core s types' bind ∗
      ⌜dom types' = dom types⌝ ∗
      ⌜∀ name p' ts', bind !! name = Some p' -> types' !! p' = Some ts' ->
         doc_model_get (<[typedInput.1 := arr2]> m) (RootId name) = ty_arr ts'⌝ ∗
      ⌜∀ c, c ∈ all_cells types' ->
         (∃ c0, c0 ∈ all_cells types ∧ cell_client c = cell_client c0 ∧
            (uint.Z (cell_clock c0) <= uint.Z (cell_clock c))%Z ∧
            (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) <=
             uint.Z (cell_clock c0) + Z.of_nat (length (ic_run c0)))%Z) ∨
         (cell_client c = W64 (clientId (in_id typedInput.2)) ∧
          (uint.Z (W64 (clock (in_id typedInput.2))) <= uint.Z (cell_clock c))%Z ∧
          (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) <=
           uint.Z (W64 (clock (in_id typedInput.2))) + Z.of_nat (length (in_content typedInput.2)))%Z)⌝ ∗
      ⌜integrate_live_refine typedInput.2 (all_cells types) (all_cells types')⌝ }}}.
Proof using Type*.
  move=> Htieq Hbnm Htoit Hvld Hmax Hall Hgmax0 Hmtypes Hnowrapc.
  iIntros (Φ) "(#Hpkg & #Hui & Hcore) HΦ". iNamed "Hcore".
  have [Hfits [Hlocdup [Hrangedisj Horiginclk]]] := Hpool.
  have [Hbindtypes [Hbindinj Htypesbound]] := Hreg.
  iDestruct "Hui" as (oleft oright opn)
    "(HisL & HisR & HisPN & %Hin_l & %Hin_r & %Hin_id & %Hin_c & %Hunonempty & %Htid & %Hborrow)".
  destruct typedInput as [typedInput2 input]. simpl in *. subst typedInput2.
  have Hts0 : is_Some (types !! p) := Hbindtypes nm p Hbnm.
  destruct Hts0 as [[cellsj arrj0] Htsj].
  have Hdgj : doc_model_get m (RootId nm) = arrj0 := Hmtypes nm p _ Hbnm Htsj.
  set (arrj := doc_model_get m (RootId nm)) in *.
  rewrite -Hdgj in Htsj.
  iDestruct (own_type_pool_arr_inv with "Htypes") as %Harrinvs.
  have Hinvj : YjsArrInvariant arrj := Harrinvs p _ Htsj.
  destruct (integrate_some input arrj newItem Hinvj Htoit) as [arrinput Hintginput].
  destruct (integrate_finds input arrj arrinput Hintginput) as (leftIdx & rightIdx & HfindL & HfindR).
  iDestruct (own_type_pool_entry types p _ Htsj with "Htypes") as %(Hreprj & Hcparj).
  simpl in Hreprj, Hcparj.
  iDestruct (own_type_pool_runs_wf with "Htypes") as %Hrunwfall.
  iDestruct (own_type_pool_parents with "Htypes") as %Hparall.
  (* uniform repair witnesses: present origins resolve to the covering cell in
     this type's own cells (that is where [toItem]'s find landed) *)
  have Hwits : ∃ (ocL ocR : option item_cell),
    ((match in_originId input, ocL with
      | Some originId, Some c => c ∈ all_cells types ∧
          clientId (item_id (run_head c)) = clientId originId ∧
          (clock (item_id (run_head c)) <= clock originId)%nat ∧
          (clock originId < clock (item_id (run_head c)) + length (ic_run c))%nat
      | None, None => True | _, _ => False end : Prop)) /\
    ((match in_rightOriginId input, ocR with
      | Some originId, Some c => c ∈ all_cells types ∧
          clientId (item_id (run_head c)) = clientId originId ∧
          (clock (item_id (run_head c)) <= clock originId)%nat ∧
          (clock originId < clock (item_id (run_head c)) + length (ic_run c))%nat
      | None, None => True | _, _ => False end : Prop)) /\
    (match opn with
     | Some nm' => bind !! nm' = Some p
     | None => match ocL with
               | Some c => p = ic_parent c
               | None => match ocR with
                         | Some c => p = ic_parent c
                         | None => False
                         end
               end
     end) /\
    (match ocL with Some c => c ∈ cellsj | None => True end) /\
    (match ocR with Some c => c ∈ cellsj | None => True end).
  { have Hcellsw : ∀ (kn : nat) (it : YjsItem A), arrj !! kn = Some it ->
      ∃ (ci off : nat) (c : item_cell), cellsj !! ci = Some c ∧ ic_run c !! off = Some it ∧
        kn = (length (run_flatten (take ci cellsj)) + off)%nat ∧
        clientId (item_id (run_head c)) = clientId (item_id it) ∧
        (clock (item_id (run_head c)) <= clock (item_id it))%nat ∧
        (clock (item_id it) < clock (item_id (run_head c)) + length (ic_run c))%nat.
    { move=> kn it Hkn. rewrite /cells_repr in Hreprj. rewrite Hreprj in Hkn.
      destruct (run_flatten_lookup_cell cellsj kn it Hkn) as (ci & off & c & Hci & Hoff & Hpos).
      have Hwf : run_wf (ic_run c).
      { apply Hrunwfall. rewrite (all_cells_lookup _ _ _ Htsj). apply elem_of_app.
        left. exact (list_elem_of_lookup_2 _ _ _ Hci). }
      have Hcid := run_wf_char_id (ic_run c) off it Hwf Hoff.
      have Hlen := lookup_lt_Some _ _ _ Hoff.
      exists ci, off, c. split_and!.
      - exact Hci.
      - exact Hoff.
      - exact Hpos.
      - rewrite Hcid /run_head //=.
      - rewrite Hcid /run_head /=. lia.
      - rewrite Hcid /run_head /=. lia. }
    have HocL : ∃ ocL,
      ((match in_originId input, ocL with
        | Some originId, Some c => c ∈ all_cells types ∧
            clientId (item_id (run_head c)) = clientId originId ∧
            (clock (item_id (run_head c)) <= clock originId)%nat ∧
            (clock originId < clock (item_id (run_head c)) + length (ic_run c))%nat
        | None, None => True | _, _ => False end : Prop)) /\
      (match ocL with Some c => ic_parent c = p | None => True end) /\
      (match ocL with Some c => c ∈ cellsj | None => True end).
    { destruct (in_originId input) as [originIdLeft|] eqn:HoinL.
      - destruct (findLeftIdx_inv originIdLeft arrj leftIdx HfindL) as (kn & it & -> & Hkn & HidL).
        destruct (Hcellsw kn it Hkn) as (ci & off & cL & HcLk & Hoff & Hpos & Hcl & Hle & Hlt).
        have HcLmem : cL ∈ cellsj := list_elem_of_lookup_2 _ _ _ HcLk.
        exists (Some cL). split_and!.
        + apply all_cells_elem_of. exists p, (MkTypeState cellsj arrj).
          split; [exact Htsj | exact HcLmem].
        + rewrite HidL in Hcl. exact Hcl.
        + rewrite HidL in Hle. exact Hle.
        + rewrite HidL in Hlt. exact Hlt.
        + exact (Hcparj cL HcLmem).
        + exact HcLmem.
      - exists None. split_and!; done. }
    have HocR : ∃ ocR,
      ((match in_rightOriginId input, ocR with
        | Some originId, Some c => c ∈ all_cells types ∧
            clientId (item_id (run_head c)) = clientId originId ∧
            (clock (item_id (run_head c)) <= clock originId)%nat ∧
            (clock originId < clock (item_id (run_head c)) + length (ic_run c))%nat
        | None, None => True | _, _ => False end : Prop)) /\
      (match ocR with Some c => ic_parent c = p | None => True end) /\
      (match ocR with Some c => c ∈ cellsj | None => True end).
    { destruct (in_rightOriginId input) as [originIdRight|] eqn:HoinR.
      - destruct (findRightIdx_inv originIdRight arrj rightIdx HfindR) as (kn & it & -> & Hkn & HidR).
        destruct (Hcellsw kn it Hkn) as (ci & off & cR & HcRk & Hoff & Hpos & Hcl & Hle & Hlt).
        have HcRmem2 : cR ∈ cellsj := list_elem_of_lookup_2 _ _ _ HcRk.
        exists (Some cR). split_and!.
        + apply all_cells_elem_of. exists p, (MkTypeState cellsj arrj).
          split; [exact Htsj | exact HcRmem2].
        + rewrite HidR in Hcl. exact Hcl.
        + rewrite HidR in Hle. exact Hle.
        + rewrite HidR in Hlt. exact Hlt.
        + exact (Hcparj cR HcRmem2).
        + exact HcRmem2.
      - exists None. split_and!; done. }
    destruct HocL as (ocL & HwL & HparL & HmemL).
    destruct HocR as (ocR & HwR & HparR & HmemR).
    exists ocL, ocR. split_and!; try done.
    destruct opn as [nm'|].
    - have Hnmeq : RootId nm = RootId nm' := Htid nm' eq_refl.
      injection Hnmeq as <-. exact Hbnm.
    - destruct ocL as [cL|]; [by rewrite -(HparL) |].
      destruct ocR as [cR|]; [by rewrite -(HparR) |].
      destruct (Hborrow eq_refl) as [HL | HR].
      + move: HwL. by destruct (in_originId input).
      + move: HwR. by destruct (in_rightOriginId input). }
  destruct Hwits as (ocL & ocR & HwLc & HwRc & Hwpar & HmemLc & HmemRc).
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
  iAssert (own_linked_item_run itv input null null null) with "[Hitv]" as "Hfresh".
  { iExists itemVal, oleft, oright. rewrite /own_fresh_item_raw.
    iFrame "Hitv HisL HisR". iPureIntro.
    split_and!;
      [exact Hin_l | exact Hin_r | exact Hin_id | exact Hin_c
      | reflexivity | reflexivity | reflexivity | reflexivity
      | exact Hunonempty]. }
  (* general-repair premises (issue #28 U1) *)
  iDestruct (own_type_pool_id_bounds with "Htypes") as %Hbnds0.
  have Huniqj := yai_unique _ Hinvj.
  have HfLpj : findPtrIdx (origin newItem) arrj = Some leftIdx.
  { rewrite -(toitem_lemmas.findLeftIdx_findPtrIdx_eq input newItem arrj Huniqj Htoit). exact HfindL. }
  have HfRpj : findPtrIdx (rightOrigin newItem) arrj = Some rightIdx.
  { rewrite -(toitem_lemmas.findRightIdx_findPtrIdx_eq input newItem arrj Huniqj Htoit). exact HfindR. }
  have HorigAj := findptridx_getelem.findPtrIdx_ArrSet arrj (origin newItem) leftIdx HfLpj.
  have HrorAj := findptridx_getelem.findPtrIdx_ArrSet arrj (rightOrigin newItem) rightIdx HfRpj.
  have Hlrj := findptridx_order2.YjsLt'_findPtrIdx_lt arrj (origin newItem) (rightOrigin newItem)
                leftIdx rightIdx Hinvj HorigAj HrorAj (iiv_origin_lt _ Hvld) HfLpj HfRpj.
  have Hsameg : ((match in_originId input, in_rightOriginId input, ocL, ocR with
    | Some a, Some b, Some cL0, Some cR0 => cL0 = cR0 -> (clock a < clock b)%nat
    | _, _, _, _ => True end : Prop)).
  { move: HwLc HwRc HmemLc HmemRc HfindL HfindR.
    destruct (in_originId input) as [originIdLeft|] eqn:HoinL2; try done.
    destruct (in_rightOriginId input) as [originIdRight|] eqn:HoinR2; try done.
    destruct ocL as [cL0|]; try done. destruct ocR as [cR0|]; try done.
    move=> [_ [HclL [HleL HltL]]] [_ [HclR [HleR HltR]]] HmemL2 HmemR2 HfindL2 HfindR2 Heq.
    subst cR0.
    destruct (list_elem_of_lookup_1 _ _ HmemL2) as [ciw Hciw].
    have Hwf : run_wf (ic_run cL0).
    { apply Hrunwfall. rewrite (all_cells_lookup _ _ _ Htsj). apply elem_of_app.
      by left. }
    destruct (run_wf_char_at_clock (ic_run cL0) originIdLeft Hwf HclL HleL HltL)
      as (chL & HchL & HidchL).
    destruct (run_wf_char_at_clock (ic_run cL0) originIdRight Hwf HclR HleR HltR)
      as (chR & HchR & HidchR).
    have HposL := run_flatten_lookup_of_cell cellsj ciw _ cL0 chL Hciw HchL.
    have HposR := run_flatten_lookup_of_cell cellsj ciw _ cL0 chR Hciw HchR.
    rewrite /cells_repr in Hreprj. rewrite -Hreprj in HposL HposR.
    destruct (findLeftIdx_inv originIdLeft arrj leftIdx HfindL2) as (knL & itL & HeqL & HknL & HidL2).
    destruct (findRightIdx_inv originIdRight arrj rightIdx HfindR2) as (knR & itR & HeqR & HknR & HidR2).
    set prefw := length (run_flatten (take ciw cellsj)) in HposL HposR.
    have HknLp : knL = (prefw + (clock originIdLeft - clock (item_id (run_head cL0))))%nat.
    { set posL := (prefw + (clock originIdLeft - clock (item_id (run_head cL0))))%nat in HposL |- *.
      destruct (Nat.lt_trichotomy knL posL) as [Hlt2 | [Heq2 | Hgt2]]; [| exact Heq2 |]; exfalso.
      - have := uniqueId_lookup_ne arrj knL posL itL chL Huniqj HknL HposL Hlt2.
        rewrite HidL2 HidchL //.
      - have := uniqueId_lookup_ne arrj posL knL chL itL Huniqj HposL HknL Hgt2.
        rewrite HidL2 HidchL //. }
    have HknRp : knR = (prefw + (clock originIdRight - clock (item_id (run_head cL0))))%nat.
    { set posR := (prefw + (clock originIdRight - clock (item_id (run_head cL0))))%nat in HposR |- *.
      destruct (Nat.lt_trichotomy knR posR) as [Hlt2 | [Heq2 | Hgt2]]; [| exact Heq2 |]; exfalso.
      - have := uniqueId_lookup_ne arrj knR posR itR chR Huniqj HknR HposR Hlt2.
        rewrite HidR2 HidchR //.
      - have := uniqueId_lookup_ne arrj posR knR chR itR Huniqj HposR HknR Hgt2.
        rewrite HidR2 HidchR //. }
    have Hklt : (knL < knR)%nat by lia.
    lia. }
  iDestruct (own_store_core_intro _ _ _ Hpool Hreg with "Hitems Hregistry Htypes") as "Hcore".
  wp_apply (wp_store__repair_split s itv (updateItemVal.(yjs.updateItem.parentName'))
              input opn types bind ocL ocR p
              HwLc HwRc Hsameg Hwpar
              with "[$Hfresh $HisPN $Hcore]").
  iIntros (lft rgt types2) "(Hlinked & Hcore & %Hrtf & %HbdL & %HbdR)".
  iDestruct "Hcore" as "(Hitems & Hregistry & Htypes & %Hpinvs2 & %Hreg2)".
  have Hpinv2 := Hpinvs2.
  destruct Hpinv2 as (Hfits2 & Hnodup2 & Hrangedisj2 & Horiginclk2).
  destruct Hrtf as (Hpres2 & Hdom2 & Hrl2 & Hunitpres2 & Hsub2 & Hlrep2).
  destruct (Hdom2 p (mk_is_Some _ _ Htsj)) as [ts2e Htsj2].
  destruct (Hpres2 p ts2e Htsj2) as (ts0e & Htsj0e & Harr2p & Hflat2p).
  have Hts0eq2 : ts0e = MkTypeState cellsj arrj by congruence.
  rewrite Hts0eq2 /= in Harr2p Hflat2p.
  destruct ts2e as [cellsj2 arrj2]. simpl in Harr2p, Hflat2p. subst arrj2.
  iDestruct (own_type_pool_runs_wf with "Htypes") as %Hrunwfall2.
  iDestruct (own_type_pool_parents with "Htypes") as %Hparall2.
  iDestruct (own_type_pool_id_bounds with "Htypes") as %Hbnds2.
  have Hcparj2 : ∀ c, c ∈ cellsj2 -> ic_parent c = p.
  { move=> c Hc. exact (Hparall2 p _ c Htsj2 Hc). }
  (* the range-form freshness transports through sub-range provenance *)
  have Hbndj2 : ∀ c0, c0 ∈ all_cells types2 ->
      cell_client c0 = W64 (clientId (in_id input)) ->
      (uint.Z (cell_clock c0) < uint.Z (W64 (clock (in_id input))))%Z ∧
      (uint.Z (cell_clock c0) + Z.of_nat (length (ic_run c0)) <= uint.Z (W64 (clock (in_id input))))%Z.
  { move=> c0 Hc0 Hcc.
    destruct (Hsub2 c0 Hc0) as (cold & Hcold & Hcl & Hlo & Hhi).
    have Hccold : cell_client cold = W64 (clientId (in_id input)) by rewrite -Hcl Hcc.
    have Hh := Hgmax0 cold Hcold Hccold.
    have Hlen1 : (1 <= length (ic_run c0))%nat.
    { have Hwf := Hrunwfall2 c0 Hc0.
      destruct (ic_run c0) eqn:Hrc; [exact (False_ind _ (proj1 Hwf eq_refl)) | simpl; lia]. }
    split; lia. }
  have Hreprj' : arrj = run_flatten cellsj2.
  { move: Hreprj. rewrite /cells_repr. move=> ->. by rewrite Hflat2p. }
  have HcurLpack : ∃ curL2 : nat,
      (curL2 <= length cellsj2)%nat ∧
      (Z.of_nat (length (run_flatten (take curL2 cellsj2))) = leftIdx + 1)%Z ∧
      lft = node_loc cellsj2 (Z.of_nat curL2 - 1).
  { move: HbdL HwLc HmemLc HfindL.
    destruct (in_originId input) as [originIdLeft|] eqn:HoinL3; destruct ocL as [c0|]; try done.
    - move=> [Hlft0 [cL' [HcL'mem [HcL'loc [HcL'cl [HcL'clk HcL'par]]]]]]
             [_ [Hclw [Hlew Hltw]]] Hmem0 HfindL3.
      have HparL0 : ic_parent c0 = p := Hcparj c0 Hmem0.
      have Hmem0a : c0 ∈ all_cells types
        by (rewrite (all_cells_lookup _ _ _ Htsj); apply elem_of_app; by left).
      have HcL'cells : cL' ∈ cellsj2.
      { have HcL'm := HcL'mem. apply all_cells_elem_of in HcL'm.
        destruct HcL'm as (p0 & ts0 & Hp0 & Hcts0).
        have Hpar0 : ic_parent cL' = p0 := Hparall2 p0 ts0 cL' Hp0 Hcts0.
        have Hpeq : p0 = p by rewrite -Hpar0 HcL'par HparL0.
        rewrite Hpeq in Hp0.
        have Hts0eq : ts0 = MkTypeState cellsj2 arrj by congruence.
        rewrite Hts0eq /= in Hcts0. exact Hcts0. }
      destruct (list_elem_of_lookup_1 _ _ HcL'cells) as [ciL Hciw].
      have Hwf' : run_wf (ic_run cL') := Hrunwfall2 cL' HcL'mem.
      have Hlen1 : (1 <= length (ic_run cL'))%nat.
      { destruct (ic_run cL') eqn:Hrc; [exact (False_ind _ (proj1 Hwf' eq_refl)) | simpl; lia]. }
      have HbL' := Hbnds2 cL' HcL'mem.
      have Hzck : (uint.Z (cell_clock cL') = Z.of_nat (clock (item_id (run_head cL'))))%Z
        by (rewrite /cell_clock; destruct HbL'; word).
      have Hpin : (clock (item_id (run_head cL')) + length (ic_run cL') = clock originIdLeft + 1)%nat.
      { move: HcL'clk. rewrite Hzck. lia. }
      have HclL' : clientId (item_id (run_head cL')) = clientId originIdLeft.
      { have Hb1 := proj1 (Hbnds2 cL' HcL'mem).
        have Hb2 := proj1 (Hbnds0 c0 Hmem0a).
        move: HcL'cl. rewrite /cell_client -Hclw. move=> Hcc.
        have Hz : uint.Z (W64 (clientId (item_id (run_head cL'))))
                = uint.Z (W64 (clientId (item_id (run_head c0)))) by rewrite Hcc.
        word. }
      destruct (lookup_lt_is_Some_2 (ic_run cL') (length (ic_run cL') - 1)%nat
                  ltac:(lia)) as [chL HchL].
      have HidchL : item_id chL = originIdLeft.
      { rewrite (run_wf_char_id _ _ _ Hwf' HchL).
        rewrite /run_head in Hpin.
        destruct originIdLeft as [oc ok].
        have Hpin' : ((item_id (hd inhabitant (ic_run cL'))).(clock)
                      + length (ic_run cL'))%nat = (ok + 1)%nat := Hpin.
        f_equal; [exact HclL' | lia]. }
      have HposL := run_flatten_lookup_of_cell cellsj2 ciL _ cL' chL Hciw HchL.
      rewrite -Hreprj' in HposL.
      destruct (findLeftIdx_inv originIdLeft arrj leftIdx HfindL3) as (knL & itL & HeqL & HknL & HidL2).
      have HknLp : knL = (length (run_flatten (take ciL cellsj2)) + (length (ic_run cL') - 1))%nat.
      { set posL := (length (run_flatten (take ciL cellsj2)) + (length (ic_run cL') - 1))%nat
          in HposL |- *.
        destruct (Nat.lt_trichotomy knL posL) as [Hlt2 | [Heq2 | Hgt2]]; [| exact Heq2 |]; exfalso.
        - have := uniqueId_lookup_ne arrj knL posL itL chL Huniqj HknL HposL Hlt2.
          rewrite HidL2 HidchL //.
        - have := uniqueId_lookup_ne arrj posL knL chL itL Huniqj HposL HknL Hgt2.
          rewrite HidL2 HidchL //. }
      exists (S ciL). split_and!.
      + apply lookup_lt_Some in Hciw. lia.
      + rewrite (run_flatten_take_S cellsj2 ciL cL' Hciw) length_app. lia.
      + replace (Z.of_nat (S ciL) - 1)%Z with (Z.of_nat ciL) by lia.
        rewrite /node_loc decide_True; last lia.
        rewrite Nat2Z.id Hciw /= HcL'loc //.
    - move=> Hlftnull _ _ HfindL3.
      move: HfindL3. rewrite /findLeftIdx. move=> [= <-].
      exists 0%nat. split_and!.
      + lia.
      + rewrite take_0 /run_flatten /=. lia.
      + rewrite Hlftnull /node_loc. case_decide; [lia | done]. }
  have HcurRpack : ∃ curR2 : nat,
      (curR2 <= length cellsj2)%nat ∧
      (Z.of_nat (length (run_flatten (take curR2 cellsj2))) = rightIdx)%Z ∧
      rgt = node_loc cellsj2 (Z.of_nat curR2).
  { move: HbdR HwRc HmemRc HfindR.
    destruct (in_rightOriginId input) as [originIdRight|] eqn:HoinR3; destruct ocR as [c0|]; try done.
    - move=> [cR' [HcR'mem [HcR'loc [HcR'cl [HcR'clk HcR'par]]]]]
             [_ [Hclw [Hlew Hltw]]] Hmem0 HfindR3.
      have HparR0 : ic_parent c0 = p := Hcparj c0 Hmem0.
      have Hmem0a : c0 ∈ all_cells types
        by (rewrite (all_cells_lookup _ _ _ Htsj); apply elem_of_app; by left).
      have HcR'cells : cR' ∈ cellsj2.
      { have HcR'm := HcR'mem. apply all_cells_elem_of in HcR'm.
        destruct HcR'm as (p0 & ts0 & Hp0 & Hcts0).
        have Hpar0 : ic_parent cR' = p0 := Hparall2 p0 ts0 cR' Hp0 Hcts0.
        have Hpeq : p0 = p by rewrite -Hpar0 HcR'par HparR0.
        rewrite Hpeq in Hp0.
        have Hts0eq : ts0 = MkTypeState cellsj2 arrj by congruence.
        rewrite Hts0eq /= in Hcts0. exact Hcts0. }
      destruct (list_elem_of_lookup_1 _ _ HcR'cells) as [ciR Hciw].
      have Hwf' : run_wf (ic_run cR') := Hrunwfall2 cR' HcR'mem.
      have Hlen1 : (1 <= length (ic_run cR'))%nat.
      { destruct (ic_run cR') eqn:Hrc; [exact (False_ind _ (proj1 Hwf' eq_refl)) | simpl; lia]. }
      have HbR' := Hbnds2 cR' HcR'mem.
      have Hzck : (uint.Z (cell_clock cR') = Z.of_nat (clock (item_id (run_head cR'))))%Z
        by (rewrite /cell_clock; destruct HbR'; word).
      have Hpin : (clock (item_id (run_head cR')) = clock originIdRight)%nat.
      { move: HcR'clk. rewrite Hzck. lia. }
      have HclR' : clientId (item_id (run_head cR')) = clientId originIdRight.
      { have Hb1 := proj1 (Hbnds2 cR' HcR'mem).
        have Hb2 := proj1 (Hbnds0 c0 Hmem0a).
        move: HcR'cl. rewrite /cell_client -Hclw. move=> Hcc.
        have Hz : uint.Z (W64 (clientId (item_id (run_head cR'))))
                = uint.Z (W64 (clientId (item_id (run_head c0)))) by rewrite Hcc.
        word. }
      destruct (lookup_lt_is_Some_2 (ic_run cR') 0%nat ltac:(lia)) as [chR HchR].
      have HidchR : item_id chR = originIdRight.
      { rewrite (run_wf_char_id _ _ _ Hwf' HchR).
        rewrite /run_head in Hpin.
        destruct originIdRight as [oc ok].
        have Hpin' : (item_id (hd inhabitant (ic_run cR'))).(clock) = ok := Hpin.
        f_equal; [exact HclR' | lia]. }
      have HposR := run_flatten_lookup_of_cell cellsj2 ciR _ cR' chR Hciw HchR.
      rewrite -Hreprj' in HposR.
      destruct (findRightIdx_inv originIdRight arrj rightIdx HfindR3) as (knR & itR & HeqR & HknR & HidR2).
      have HknRp : knR = (length (run_flatten (take ciR cellsj2)) + 0)%nat.
      { set posR := (length (run_flatten (take ciR cellsj2)) + 0)%nat in HposR |- *.
        destruct (Nat.lt_trichotomy knR posR) as [Hlt2 | [Heq2 | Hgt2]]; [| exact Heq2 |]; exfalso.
        - have := uniqueId_lookup_ne arrj knR posR itR chR Huniqj HknR HposR Hlt2.
          rewrite HidR2 HidchR //.
        - have := uniqueId_lookup_ne arrj posR knR chR itR Huniqj HposR HknR Hgt2.
          rewrite HidR2 HidchR //. }
      exists ciR. split_and!.
      + apply lookup_lt_Some in Hciw. lia.
      + lia.
      + rewrite /node_loc decide_True; last lia.
        rewrite Nat2Z.id Hciw /= HcR'loc //.
    - move=> Hrgtnull _ _ HfindR3.
      move: HfindR3. rewrite /findRightIdx. move=> [= <-].
      exists (length cellsj2). split_and!.
      + lia.
      + rewrite take_ge; last lia. rewrite -Hreprj'. lia.
      + rewrite Hrgtnull /node_loc. case_decide; [| lia].
        rewrite Nat2Z.id lookup_ge_None_2 //. }
  iDestruct (linked_item_run_fresh2 with "Hlinked Htypes") as %Hfreshloc.
  iDestruct (own_type_pool_repr with "Htypes") as %Hreprallj.
  wp_auto.
  have Hidnit : item_id newItem = in_id input := commutativity.toItem_id input arrj newItem Htoit.
  have Hgmaxj : ∀ c0, c0 ∈ all_cells types2 → cell_client c0 = W64 (clientId (item_id newItem)) →
                  (uint.Z (cell_clock c0) < uint.Z (W64 (clock (item_id newItem))))%Z ∧
                  (uint.Z (cell_clock c0) + Z.of_nat (length (ic_run c0)) <= uint.Z (W64 (clock (item_id newItem))))%Z.
  { intros c0 Hc0 Hcc0. rewrite Hidnit in Hcc0 |- *.
    exact (Hbndj2 c0 Hc0 Hcc0). }
  iDestruct (big_sepM_delete _ _ p _ Htsj2 with "Htypes") as "[[Hyt _] Htypesrest]".
  have Hfitscj : ∀ c0, c0 ∈ cellsj2 -> cell_fits c0.
  { move=> c0 Hc0. apply Hfits2.
    rewrite (all_cells_lookup _ _ _ Htsj2). apply elem_of_app. by left. }
  have Hoclkcj : ∀ c0, c0 ∈ cellsj2 -> cell_origin_clk c0.
  { move=> c0 Hc0. apply Horiginclk2.
    rewrite (all_cells_lookup _ _ _ Htsj2). apply elem_of_app. by left. }
  have Hreprj2 : cells_repr arrj cellsj2 arrj := Hreprallj p _ Htsj2.
  have Hnecj2 : Forall (λ c, ic_run c ≠ []) cellsj2.
  { apply Forall_forall. move=> c Hc.
    have Hwf : run_wf (ic_run c).
    { apply Hrunwfall2. rewrite (all_cells_lookup _ _ _ Htsj2). apply elem_of_app. by left. }
    exact (proj1 Hwf). }
  destruct HcurLpack as (curL2 & HcurL2b & HcurL2 & HlftND).
  destruct HcurRpack as (curR2 & HcurR2b & HcurR2 & HrgtND).
  iEval (rewrite HlftND HrgtND) in "Hlinked".
  wp_apply (wp_Store__Integrate_nil_run s p itv arrj arr2 input newItem cellsj2 types2 leftIdx rightIdx
              curL2 curR2
              Hinvj Htoit Hvld Hmax HfindL HfindR Htsj2 Hgmaxj Hnecj2 Hfitscj Hoclkcj
              HcurL2 HcurL2b HcurR2 HcurR2b Hall
              with "[$Hyt $Hlinked $Hitems]").
  iIntros (idx2 iidx2 cells'' c2)
    "(%Hinv2 & Htext2 & Hitems & %Hperm2 & %Hsplice2 & %Hidx2b & %Hcoup2 & %Hile2 & %Harrsp2 & %Hc2look & %Hc2loc & %Hc2id & %Hc2del & %Hc2orig & %Hc2rorig & %Hc2len)".
  have Hac_step : all_cells (<[p := MkTypeState cells'' arr2]> types2)
                ≡ₚ all_cells types2 ++ [c2]
    by apply (all_cells_insert_snoc types2 p cellsj2 arrj cells'' arr2 c2 Htsj2 Hperm2).
  have Hcc2 : cell_client c2 = W64 (clientId (in_id input))
    by rewrite /cell_client Hc2id //.
  have Hclk2 : cell_clock c2 = W64 (clock (in_id input))
    by rewrite /cell_clock Hc2id //.
  have Hlocdup' : NoDup (ic_loc <$> all_cells (<[p := MkTypeState cells'' arr2]> types2)).
  { apply (nodup_locs_snoc (all_cells types2) _ c2 Hac_step);
      [rewrite Hc2loc; exact Hfreshloc | exact Hnodup2]. }
  have Hrangedisj' : cells_range_disjoint (all_cells (<[p := MkTypeState cells'' arr2]> types2)).
  { apply (rangedisj_snoc (all_cells types2) _ c2 Hac_step); [| exact Hrangedisj2].
    move=> c0 Hc0 Hcc0.
    have Hccnit : cell_client c0 = W64 (clientId (item_id newItem)).
    { rewrite Hcc0 Hcc2 Hidnit //. }
    have Hle := proj2 (Hgmaxj c0 Hc0 Hccnit).
    rewrite Hidnit in Hle.
    rewrite Hclk2. clear -Hle. lia. }
  have Horiginclk' : ∀ c0, c0 ∈ all_cells (<[p := MkTypeState cells'' arr2]> types2) ->
      cell_origin_clk c0.
  { apply (originclk_snoc (all_cells types2) _ c2 Hac_step); [| exact Horiginclk2].
    move=> originId Hoid Hcl.
    rewrite Hc2orig in Hoid.
    rewrite Hc2id -Hidnit in Hcl.
    rewrite Hc2id -Hidnit.
    rewrite (in_originId_origin_id arrj newItem input Htoit) in Hoid.
    have [o0 [r0 [id0 [c0x [Hnitdef [HoLp [_ [_ _]]]]]]]]
      := proj1 (toItem_ok_iff input arrj newItem) Htoit.
    rewrite Hoid /isLeftIdPtr in HoLp.
    destruct HoLp as (x & Ho & Hfind).
    have Hxid : item_id x = originId by apply (find_by_id_id originId arrj x Hfind).
    have Hxmem : x ∈ arrj by apply (find_by_id_mem originId arrj x Hfind).
    have Hxmem2 := Hxmem. rewrite Hreprj' in Hxmem2.
    apply list_elem_of_lookup_1 in Hxmem2 as [kx Hkx].
    destruct (run_flatten_lookup_cell cellsj2 kx x Hkx) as (cix & offx & c0' & Hcix & Hoffx & _).
    have Hc0'mem : c0' ∈ cellsj2 := list_elem_of_lookup_2 _ _ _ Hcix.
    have Hc0'all : c0' ∈ all_cells types2.
    { rewrite (all_cells_lookup _ _ _ Htsj2). apply elem_of_app. by left. }
    have Hwfx : run_wf (ic_run c0') := Hrunwfall2 c0' Hc0'all.
    have Hxid2 := run_wf_char_id _ _ _ Hwfx Hoffx.
    have Hoffb := lookup_lt_Some _ _ _ Hoffx.
    have Hcl' : cell_client c0' = W64 (clientId (in_id input)).
    { rewrite /cell_client /run_head.
      have Hclx : clientId (item_id x) = clientId (item_id (hd inhabitant (ic_run c0')))
        by rewrite Hxid2 //.
      rewrite -Hclx Hxid Hcl Hidnit //. }
    have Hbnd := proj2 (Hbndj2 c0' Hc0'all Hcl').
    have Hclkx : clock originId = (clock (item_id (hd inhabitant (ic_run c0'))) + offx)%nat
      by rewrite -Hxid Hxid2 //.
    have [_ Hkb] := Hbnds2 c0' Hc0'all.
    have Hzc0 : (uint.Z (cell_clock c0') = Z.of_nat (clock (item_id (run_head c0'))))%Z
      by (rewrite /cell_clock; word).
    rewrite /run_head in Hzc0.
    have Hb : uint.Z (W64 (clock (in_id input))) = Z.of_nat (clock (in_id input))
      := uint_W64_nat_bound (clock (in_id input)) (length (in_content input)) Hnowrapc.
    rewrite Hb in Hbnd.
    rewrite Hidnit. lia. }
  iAssert (own_type_pool (DfracOwn 1) (<[p := MkTypeState cells'' arr2]> types2))%I
    with "[Htext2 Htypesrest]" as "Htypes".
  { rewrite /own_type_pool -insert_delete_eq.
    rewrite big_sepM_insert; last apply lookup_delete_eq.
    iFrame "Htypesrest". simpl. iFrame "Htext2".
    iPureIntro. exact Hinv2. }
  iDestruct (own_type_pool_runs_wf with "Htypes") as %Hrunwfpost.
  wp_auto.
  have Hpool' : pool_invs (<[p := MkTypeState cells'' arr2]> types2).
  { split_and!.
    - (* fits for the grown pool *)
      move=> c0 Hc0.
      rewrite Hac_step in Hc0. apply elem_of_app in Hc0 as [Hold | Hnew].
      + exact (Hfits2 c0 Hold).
      + apply list_elem_of_singleton in Hnew as ->.
        have Hlen2 : length (ic_run c2) = length (in_content input) by rewrite Hc2len explode_length.
        rewrite /cell_fits Hclk2 Hlen2.
        exact (uint_W64_nat_add_bound (clock (in_id input)) (length (in_content input)) Hnowrapc).
    - exact Hlocdup'.
    - exact Hrangedisj'.
    - exact Horiginclk'. }
  have Hreg' : registry_coh bind (<[p := MkTypeState cells'' arr2]> types2)
    := registry_coh_insert bind types2 p _ _ Htsj2 Hreg2.
  iApply ("HΦ" $! (<[p := MkTypeState cells'' arr2]> types2)).
  iSplitL "Hitems Hregistry Htypes";
    first (iApply (own_store_core_intro _ _ _ Hpool' Hreg' with "Hitems Hregistry Htypes")).
  iPureIntro. split_and!.
  - (* dom eq *)
    have Hdomeq2 : dom types2 = dom types.
    { apply set_eq => p0. rewrite !elem_of_dom. split.
      - move=> [ts0 Hp0]. destruct (Hpres2 p0 ts0 Hp0) as (tsold & Hpold & _). eauto.
      - move=> Hp0. exact (Hdom2 p0 Hp0). }
    rewrite dom_insert_lookup_L; [rewrite Hdomeq2; reflexivity | eauto].
  - (* per-name coherence at <[RootId nm := arr2]> m *)
    move=> nm0 p0 ts Hbnm0.
    destruct (decide (p0 = p)) as [-> | Hne].
    + have Hnm0 : nm0 = nm := Hbindinj nm0 nm p Hbnm0 Hbnm.
      subst nm0. rewrite lookup_insert_eq. move=> [= <-].
      rewrite docm_get_insert_eq //.
    + rewrite lookup_insert_ne; last congruence.
      move=> Hts.
      have Hnenm : RootId nm0 ≠ RootId nm.
      { move=> [= Heqnm]. subst nm0. apply Hne.
        have : Some p0 = Some p by rewrite -Hbnm0 -Hbnm //.
        by move=> [=]. }
      rewrite docm_get_insert_ne //.
      destruct (Hpres2 p0 ts Hts) as (tsold & Hpold & Harrp & _).
      rewrite Harrp.
      exact (Hmtypes nm0 p0 tsold Hbnm0 Hpold).
  - (* provenance: old cell (transported) or the new cell *)
    move=> c0 Hc0.
    rewrite Hac_step in Hc0. apply elem_of_app in Hc0 as [Hold | Hnew].
    + destruct (Hsub2 c0 Hold) as (cold & Hcold & Hcl & Hlo & Hhi).
      left. exists cold. split_and!; [exact Hcold | congruence | lia | lia].
    + apply list_elem_of_singleton in Hnew as ->.
      have Hlen2 : length (ic_run c2) = length (in_content input) by rewrite Hc2len explode_length.
      right. split_and!.
      * exact Hcc2.
      * rewrite Hclk2. lia.
      * rewrite Hclk2 Hlen2. lia.
  - (* the live-cell refinement: a repaired cell's chars come from a live cell
       of the entry pool, and the spliced cell's chars are the wire item's own
       (its run starts at the item's id and runs up its clock space) *)
    apply (integrate_live_refine_trans input _ (all_cells types2) _).
    { exact (integrate_live_refine_of_live_refine input types types2 Hlrep2). }
    apply (integrate_live_refine_snoc input (all_cells types2) _ c2 Hac_step).
    move=> y Hy.
    have Hc2mem : c2 ∈ all_cells (<[p := MkTypeState cells'' arr2]> types2)
      by (rewrite Hac_step; apply elem_of_app; right; apply list_elem_of_here).
    have Hwf2 : run_wf (ic_run c2) := Hrunwfpost c2 Hc2mem.
    have [Hcl [Hlo _]] := run_wf_char_id_bound c2 y Hwf2 Hy.
    rewrite Hc2id in Hcl Hlo. split; [exact Hcl | exact Hlo].
Qed.

(** [store.integrateDecoded], creation form (issue #54): the ready branch for an
    ORIGIN-FREE struct whose target root [nm] is not yet registered. The struct
    is integrated into a freshly created empty type (repair's [getOrCreateYType]
    miss), so the registry grows by [nm -> p] and the type map by a fresh type
    at [p] carrying exactly this item's run. The uniform "grown" postcondition
    matches [wp_store__integrateDecoded]'s (the loop calls that dispatcher).
    Because the target starts empty, [doc_model_get m typedInput.1 = []].
    Local: the unbound-root case of [wp_store__integrateDecoded] below. *)
#[local] Lemma wp_store__integrateDecoded_unbound (s : loc)
    (updateItemVal : yjs.updateItem.t) (typedInput : TId * IntegrateInput (A := A))
    (m : DocModel) (types : gmap loc type_state) (bind : gmap P loc)
    (newItem : YjsItem A) (arr2 : list (YjsItem A)) (nm : P) :
  typedInput.1 = RootId nm ->
  bind !! nm = None ->
  in_originId typedInput.2 = None ->
  in_rightOriginId typedInput.2 = None ->
  doc_model_get m typedInput.1 = [] ->
  toItem typedInput.2 [] = Some newItem ->
  IsItemValid newItem ->
  maximalId newItem [] ->
  integrate_all (ops_of_input typedInput.2 (explode (in_content typedInput.2))) [] = Some arr2 ->
  (∀ c0, c0 ∈ all_cells types -> cell_client c0 = W64 (clientId (in_id typedInput.2)) ->
     (uint.Z (cell_clock c0) < uint.Z (W64 (clock (in_id typedInput.2))))%Z ∧
     (uint.Z (cell_clock c0) + Z.of_nat (length (ic_run c0)) <= uint.Z (W64 (clock (in_id typedInput.2))))%Z) ->
  (∀ name p' ts, bind !! name = Some p' -> types !! p' = Some ts ->
     doc_model_get m (RootId name) = ty_arr ts) ->
  (∀ t, doc_model_get m t ≠ [] -> ∃ name p', t = RootId name ∧ bind !! name = Some p') ->
  (Z.of_nat (clock (in_id typedInput.2)) + Z.of_nat (length (in_content typedInput.2)) < 2^64)%Z ->
  {{{ is_pkg_init yjs ∗ is_update_item updateItemVal typedInput ∗ own_store_core s types bind }}}
    s @! (go.PointerType yjs.store) @! "integrateDecoded" #updateItemVal
  {{{ (types' : gmap loc type_state) (bind' : gmap P loc), RET #();
      own_store_core s types' bind' ∗
      ⌜bind ⊆ bind'⌝ ∗
      ⌜dom types ⊆ dom types'⌝ ∗
      ⌜∀ name p' ts', bind' !! name = Some p' -> types' !! p' = Some ts' ->
         doc_model_get (<[typedInput.1 := arr2]> m) (RootId name) = ty_arr ts'⌝ ∗
      ⌜∀ t, doc_model_get (<[typedInput.1 := arr2]> m) t ≠ [] ->
         ∃ name p', t = RootId name ∧ bind' !! name = Some p'⌝ ∗
      ⌜∀ c, c ∈ all_cells types' ->
         (∃ c0, c0 ∈ all_cells types ∧ cell_client c = cell_client c0 ∧
            (uint.Z (cell_clock c0) <= uint.Z (cell_clock c))%Z ∧
            (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) <=
             uint.Z (cell_clock c0) + Z.of_nat (length (ic_run c0)))%Z) ∨
         (cell_client c = W64 (clientId (in_id typedInput.2)) ∧
          (uint.Z (W64 (clock (in_id typedInput.2))) <= uint.Z (cell_clock c))%Z ∧
          (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) <=
           uint.Z (W64 (clock (in_id typedInput.2))) + Z.of_nat (length (in_content typedInput.2)))%Z)⌝ ∗
      ⌜integrate_live_refine typedInput.2 (all_cells types) (all_cells types')⌝ }}}.
Proof using Type*.
  move=> Htieq Hbnm HoL HoR Hdgnil Htoit Hvld Hmax Hall Hgmax0 Hmtypes Hmdom Hnowrapc.
  iIntros (Φ) "(#Hpkg & #Hui & Hcore) HΦ". iNamed "Hcore".
  have [Hfits [Hlocdup [Hrangedisj Horiginclk]]] := Hpool.
  have [Hbindtypes [Hbindinj Htypesbound]] := Hreg.
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
  iAssert (own_linked_item_run itv input null null null) with "[Hitv]" as "Hfresh".
  { iExists itemVal, None, None. rewrite /own_fresh_item_raw.
    iFrame "Hitv HisL HisR". iPureIntro.
    split_and!;
      [exact Hin_l | exact Hin_r | exact Hin_id | exact Hin_c
      | reflexivity | reflexivity | reflexivity | reflexivity
      | exact Hunonempty]. }
  iDestruct (own_store_core_intro _ _ _ Hpool Hreg with "Hitems Hregistry Htypes") as "Hcore".
  wp_apply (wp_store__repair_create s itv (updateItemVal.(yjs.updateItem.parentName'))
              input nm types bind HoL HoR Hbnm
              with "[$Hfresh $HisPN $Hcore]").
  iIntros (p) "(Hlinked & Hcore & %Hfresh)".
  iDestruct "Hcore" as "(Hitems & Hregistry & Htypes & %Hpinvs2 & %Hreg2)".
  (* [p] is not in the range of [bind] (it did not exist as a type) *)
  have Hpnotbound : ∀ name, bind !! name ≠ Some p.
  { move=> name Hb. have Hs := Hbindtypes name p Hb. rewrite Hfresh in Hs. by destruct Hs. }
  set types2 := <[p := MkTypeState [] []]> types.
  have Htsj2 : types2 !! p = Some (MkTypeState [] []) by rewrite /types2 lookup_insert_eq.
  have Hac_empty : all_cells types2 ≡ₚ all_cells types := all_cells_insert_empty types p [] Hfresh.
  have Hnodup2 : NoDup (ic_loc <$> all_cells types2) by (rewrite Hac_empty; exact Hlocdup).
  have Hrangedisj2 : cells_range_disjoint (all_cells types2).
  { move=> c1 c2 Hc1 Hc2. rewrite Hac_empty in Hc1 Hc2. exact (Hrangedisj c1 c2 Hc1 Hc2). }
  have Hfits2 : ∀ c, c ∈ all_cells types2 -> cell_fits c
    by (move=> c Hc; rewrite Hac_empty in Hc; exact (Hfits c Hc)).
  have Horiginclk2 : ∀ c, c ∈ all_cells types2 -> cell_origin_clk c
    by (move=> c Hc; rewrite Hac_empty in Hc; exact (Horiginclk c Hc)).
  (* Integrate premises for the empty type *)
  have Hidnit : item_id newItem = in_id input
    by apply (commutativity.toItem_id input (@nil (YjsItem A)) newItem Htoit).
  have Hinvj : YjsArrInvariant ([] : list (YjsItem A)) := YjsArrInvariant_empty.
  have HfindL : findLeftIdx (in_originId input) (@nil (YjsItem A)) = Some (-1)%Z by rewrite HoL /findLeftIdx //.
  have HfindR : findRightIdx (in_rightOriginId input) (@nil (YjsItem A)) = Some 0%Z by rewrite HoR /findRightIdx /=.
  have Hgmaxj : ∀ c0, c0 ∈ all_cells types2 → cell_client c0 = W64 (clientId (item_id newItem)) →
                  (uint.Z (cell_clock c0) < uint.Z (W64 (clock (item_id newItem))))%Z ∧
                  (uint.Z (cell_clock c0) + Z.of_nat (length (ic_run c0)) <= uint.Z (W64 (clock (item_id newItem))))%Z.
  { move=> c0 Hc0 Hcc0. rewrite Hac_empty in Hc0. rewrite Hidnit in Hcc0 |- *.
    exact (Hgmax0 c0 Hc0 Hcc0). }
  iDestruct (linked_item_run_fresh2 with "Hlinked Htypes") as %Hfreshloc.
  have Hfreshloc' : itv ∉ ic_loc <$> all_cells types
    by (move=> Hin; apply Hfreshloc; rewrite Hac_empty; exact Hin).
  iDestruct (big_sepM_delete _ _ p _ Htsj2 with "Htypes") as "[[Hyt _] Htypesrest]".
  have Hln1 : (null : loc) = node_loc ([] : list item_cell) (Z.of_nat 0 - 1)%Z
    by rewrite /node_loc; case_decide; [lia | done].
  have Hln2 : (null : loc) = node_loc ([] : list item_cell) (Z.of_nat 0)
    by rewrite /node_loc; case_decide; [rewrite /= // | lia].
  iEval (rewrite {1}Hln1 {1}Hln2) in "Hlinked".
  have Hnec0 : Forall (λ c : item_cell, ic_run c ≠ []) [] by constructor.
  have Hfits0 : ∀ c0 : item_cell, c0 ∈ [] -> cell_fits c0
    by (move=> ? H; by apply elem_of_nil in H).
  have Hoclk0 : ∀ c0 : item_cell, c0 ∈ [] -> cell_origin_clk c0
    by (move=> ? H; by apply elem_of_nil in H).
  have HcurLeq : (Z.of_nat (length (run_flatten (take 0 ([] : list item_cell)))) = (-1) + 1)%Z
    by (rewrite take_nil /run_flatten /=; lia).
  have HcurReq : (Z.of_nat (length (run_flatten (take 0 ([] : list item_cell)))) = 0)%Z
    by (rewrite take_nil /run_flatten /=; lia).
  wp_auto.
  wp_apply (wp_Store__Integrate_nil_run s p itv [] arr2 input newItem [] types2 (-1)%Z 0%Z
              0%nat 0%nat
              Hinvj Htoit Hvld Hmax HfindL HfindR Htsj2 Hgmaxj Hnec0 Hfits0 Hoclk0
              HcurLeq ltac:(simpl; lia) HcurReq ltac:(simpl; lia) Hall
              with "[$Hyt $Hlinked $Hitems]").
  iIntros (idx2 iidx2 cells'' c2)
    "(%Hinv2 & Htext2 & Hitems & %Hperm2 & %Hsplice2 & %Hidx2b & %Hcoup2 & %Hile2 & %Harrsp2 & %Hc2look & %Hc2loc & %Hc2id & %Hc2del & %Hc2orig & %Hc2rorig & %Hc2len)".
  have Hac_step : all_cells (<[p := MkTypeState cells'' arr2]> types2)
                ≡ₚ all_cells types2 ++ [c2]
    by apply (all_cells_insert_snoc types2 p [] [] cells'' arr2 c2 Htsj2 Hperm2).
  have Hac_step' : all_cells (<[p := MkTypeState cells'' arr2]> types2) ≡ₚ all_cells types ++ [c2].
  { rewrite Hac_step Hac_empty //. }
  have Hcc2 : cell_client c2 = W64 (clientId (in_id input)) by rewrite /cell_client Hc2id //.
  have Hclk2 : cell_clock c2 = W64 (clock (in_id input)) by rewrite /cell_clock Hc2id //.
  have Hlen2 : length (ic_run c2) = length (in_content input) by rewrite Hc2len explode_length.
  have Hlocdup' : NoDup (ic_loc <$> all_cells (<[p := MkTypeState cells'' arr2]> types2)).
  { apply (nodup_locs_snoc (all_cells types) _ c2 Hac_step');
      [rewrite Hc2loc; exact Hfreshloc' | exact Hlocdup]. }
  have Hrangedisj' : cells_range_disjoint (all_cells (<[p := MkTypeState cells'' arr2]> types2)).
  { apply (rangedisj_snoc (all_cells types) _ c2 Hac_step'); [| exact Hrangedisj].
    move=> c0 Hc0 Hcc0.
    have Hle := proj2 (Hgmax0 c0 Hc0 ltac:(rewrite Hcc0 Hcc2 //)).
    rewrite Hclk2. clear -Hle. lia. }
  have Hoc2 : cell_origin_clk c2.
  { rewrite /cell_origin_clk. move=> originId Hoid _.
    rewrite Hc2orig (in_originId_origin_id [] newItem input Htoit) HoL in Hoid. discriminate. }
  have Horiginclk' : ∀ c0, c0 ∈ all_cells (<[p := MkTypeState cells'' arr2]> types2) ->
      cell_origin_clk c0
    by (apply (originclk_snoc (all_cells types) _ c2 Hac_step'); [exact Hoc2 | exact Horiginclk]).
  have Hfits' : ∀ c0, c0 ∈ all_cells (<[p := MkTypeState cells'' arr2]> types2) -> cell_fits c0.
  { move=> c0 Hc0. rewrite Hac_step' in Hc0. apply elem_of_app in Hc0 as [Hold | Hnew].
    - exact (Hfits c0 Hold).
    - apply list_elem_of_singleton in Hnew as ->.
      rewrite /cell_fits Hclk2 Hlen2.
      exact (uint_W64_nat_add_bound (clock (in_id input)) (length (in_content input)) Hnowrapc). }
  iAssert (own_type_pool (DfracOwn 1) (<[p := MkTypeState cells'' arr2]> types2))%I
    with "[Htext2 Htypesrest]" as "Htypes".
  { rewrite /own_type_pool -insert_delete_eq.
    rewrite big_sepM_insert; last apply lookup_delete_eq.
    iFrame "Htypesrest". simpl. iFrame "Htext2". iPureIntro. exact Hinv2. }
  iDestruct (own_type_pool_runs_wf with "Htypes") as %Hrunwfpost.
  wp_auto.
  (* [types'] as a map is [<[p := ..]> types] (overwrites the fresh empty entry) *)
  have Htypes'eq : <[p := MkTypeState cells'' arr2]> types2 = <[p := MkTypeState cells'' arr2]> types
    by rewrite /types2 insert_insert_eq.
  have Hpool' : pool_invs (<[p := MkTypeState cells'' arr2]> types2).
  { split_and!; [exact Hfits' | exact Hlocdup' | exact Hrangedisj' | exact Horiginclk']. }
  have Hreg' : registry_coh (<[nm := p]> bind) (<[p := MkTypeState cells'' arr2]> types2).
  { rewrite Htypes'eq. exact (registry_coh_bind_fresh bind types nm p _ Hbnm Hfresh Hreg). }
  iApply ("HΦ" $! (<[p := MkTypeState cells'' arr2]> types2) (<[nm := p]> bind)).
  iSplitL "Hitems Hregistry Htypes";
    first (iApply (own_store_core_intro _ _ _ Hpool' Hreg' with "Hitems Hregistry Htypes")).
  iPureIntro. split_and!.
  - (* bind ⊆ <[nm:=p]>bind *)
    exact (insert_subseteq bind nm p Hbnm).
  - (* dom types ⊆ dom types' *)
    rewrite Htypes'eq dom_insert_L. set_solver.
  - (* mtypes' at <[RootId nm := arr2]> m *)
    move=> name pl ts' Hb Hts'.
    rewrite Htypes'eq in Hts'.
    destruct (decide (name = nm)) as [-> | Hne].
    + rewrite lookup_insert_eq in Hb. injection Hb as <-.
      rewrite lookup_insert_eq in Hts'. injection Hts' as <-. simpl.
      rewrite docm_get_insert_eq //.
    + rewrite lookup_insert_ne // in Hb.
      have Hnenm : RootId name ≠ RootId nm by (move=> [= ?]; congruence).
      rewrite docm_get_insert_ne //.
      destruct (decide (pl = p)) as [-> | Hnep]; first by (exfalso; exact (Hpnotbound name Hb)).
      rewrite lookup_insert_ne // in Hts'.
      exact (Hmtypes name pl ts' Hb Hts').
  - (* mdom' at <[RootId nm := arr2]> m *)
    move=> t Hne.
    destruct (decide (t = RootId nm)) as [-> | Hnet].
    + exists nm, p. split; [done | by rewrite lookup_insert_eq].
    + rewrite docm_get_insert_ne // in Hne.
      destruct (Hmdom t Hne) as (name & pl & Heqt & Hb).
      exists name, pl. split; [exact Heqt |].
      rewrite lookup_insert_ne //. move=> ?; subst name. by rewrite Hbnm in Hb.
  - (* provenance *)
    move=> c0 Hc0. rewrite Hac_step' in Hc0. apply elem_of_app in Hc0 as [Hold | Hnew].
    + left. exists c0. split_and!; [exact Hold | done | lia | lia].
    + apply list_elem_of_singleton in Hnew as ->. right. split_and!.
      * exact Hcc2.
      * rewrite Hclk2. lia.
      * rewrite Hclk2 Hlen2. lia.
  - (* the live-cell refinement: this branch registers a fresh empty type, so
       every old cell survives verbatim and the only new one is the spliced
       cell, whose chars are the wire item's own *)
    apply (integrate_live_refine_snoc input _ _ c2 Hac_step').
    move=> y Hy.
    have Hc2mem' : c2 ∈ all_cells (<[p := MkTypeState cells'' arr2]> types2)
      by (rewrite Hac_step'; apply elem_of_app; right; apply list_elem_of_here).
    have Hwf2 : run_wf (ic_run c2) := Hrunwfpost c2 Hc2mem'.
    have [Hcl [Hlo _]] := run_wf_char_id_bound c2 y Hwf2 Hy.
    rewrite Hc2id in Hcl Hlo. split; [exact Hcl | exact Hlo].
Qed.

(* ===== the total applyUpdate loop (issue #40) ============================= *)

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


(** [store.integrateDecoded] (issue #54): the drain loop's uniform per-item
    entry point. It does NOT require the target root to be already bound; it
    dispatches on the registry: a HIT is [wp_store__integrateDecoded_bound]
    (registry unchanged), a MISS is [wp_store__integrateDecoded_unbound]
    (registry grows by one fresh type). A
    miss is necessarily an origin-free struct: an origin would resolve inside a
    nonempty -- hence, by [Hmdom], registered -- target root. Either way the
    postcondition is the same "grown" shape ([bind ⊆ bind'],
    [dom types ⊆ dom types'], coherence over the grown maps), so the loop
    threads a single monotone registry. *)
Lemma wp_store__integrateDecoded (s : loc)
    (updateItemVal : yjs.updateItem.t) (typedInput : TId * IntegrateInput (A := A))
    (m : DocModel) (types : gmap loc type_state) (bind : gmap P loc)
    (newItem : YjsItem A) (arr2 : list (YjsItem A)) (nm : P) :
  typedInput.1 = RootId nm ->
  toItem typedInput.2 (doc_model_get m typedInput.1) = Some newItem ->
  IsItemValid newItem ->
  maximalId newItem (doc_model_get m typedInput.1) ->
  integrate_all (ops_of_input typedInput.2 (explode (in_content typedInput.2))) (doc_model_get m typedInput.1) = Some arr2 ->
  (∀ c0, c0 ∈ all_cells types -> cell_client c0 = W64 (clientId (in_id typedInput.2)) ->
     (uint.Z (cell_clock c0) < uint.Z (W64 (clock (in_id typedInput.2))))%Z ∧
     (uint.Z (cell_clock c0) + Z.of_nat (length (ic_run c0)) <= uint.Z (W64 (clock (in_id typedInput.2))))%Z) ->
  (∀ name p' ts, bind !! name = Some p' -> types !! p' = Some ts ->
     doc_model_get m (RootId name) = ty_arr ts) ->
  (∀ t, doc_model_get m t ≠ [] -> ∃ name p', t = RootId name ∧ bind !! name = Some p') ->
  (Z.of_nat (clock (in_id typedInput.2)) + Z.of_nat (length (in_content typedInput.2)) < 2^64)%Z ->
  {{{ is_pkg_init yjs ∗ is_update_item updateItemVal typedInput ∗ own_store_core s types bind }}}
    s @! (go.PointerType yjs.store) @! "integrateDecoded" #updateItemVal
  {{{ (types' : gmap loc type_state) (bind' : gmap P loc), RET #();
      own_store_core s types' bind' ∗
      ⌜bind ⊆ bind'⌝ ∗
      ⌜dom types ⊆ dom types'⌝ ∗
      ⌜∀ name p' ts', bind' !! name = Some p' -> types' !! p' = Some ts' ->
         doc_model_get (<[typedInput.1 := arr2]> m) (RootId name) = ty_arr ts'⌝ ∗
      ⌜∀ t, doc_model_get (<[typedInput.1 := arr2]> m) t ≠ [] ->
         ∃ name p', t = RootId name ∧ bind' !! name = Some p'⌝ ∗
      ⌜∀ c, c ∈ all_cells types' ->
         (∃ c0, c0 ∈ all_cells types ∧ cell_client c = cell_client c0 ∧
            (uint.Z (cell_clock c0) <= uint.Z (cell_clock c))%Z ∧
            (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) <=
             uint.Z (cell_clock c0) + Z.of_nat (length (ic_run c0)))%Z) ∨
         (cell_client c = W64 (clientId (in_id typedInput.2)) ∧
          (uint.Z (W64 (clock (in_id typedInput.2))) <= uint.Z (cell_clock c))%Z ∧
          (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) <=
           uint.Z (W64 (clock (in_id typedInput.2))) + Z.of_nat (length (in_content typedInput.2)))%Z)⌝ ∗
      ⌜integrate_live_refine typedInput.2 (all_cells types) (all_cells types')⌝ }}}.
Proof using Type*.
  move=> Htieq Htoit Hvld Hmax Hall Hgmax0 Hmtypes Hmdom Hnowrapc.
  iIntros (Φ) "(#Hpkg & #Hui & Hcore) HΦ".
  destruct (bind !! nm) as [p|] eqn:Hbnm.
  - (* HIT: reuse the bound-root integrateDecoded; registry unchanged *)
    wp_apply (wp_store__integrateDecoded_bound s updateItemVal typedInput m types bind
                newItem arr2 nm p Htieq Hbnm Htoit Hvld Hmax Hall Hgmax0 Hmtypes Hnowrapc
                with "[$Hui $Hcore]").
    iIntros (types') "(Hcore & %Hdom' & %Hmtypes' & %Hprov' & %Hilr')".
    iApply ("HΦ" $! types' bind).
    iFrame "Hcore".
    iPureIntro. split_and!.
    + done.
    + rewrite Hdom'. done.
    + exact Hmtypes'.
    + move=> t Hne. destruct (decide (t = typedInput.1)) as [-> | Hnet].
      * exists nm, p. split; [exact Htieq | exact Hbnm].
      * rewrite docm_get_insert_ne // in Hne.
        exact (Hmdom t Hne).
    + exact Hprov'.
    + exact Hilr'.
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
    wp_apply (wp_store__integrateDecoded_unbound s updateItemVal typedInput m types bind
                newItem arr2 nm Htieq Hbnm HoL HoR Hdgnil Htoit Hvld Hmax Hall Hgmax0
                Hmtypes Hmdom Hnowrapc
                with "[$Hui $Hcore]").
    iIntros (types' bind') "Hpost".
    iApply ("HΦ" $! types' bind' with "Hpost").
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
