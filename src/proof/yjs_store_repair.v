(** store update path, repair + applyUpdate layer: [getOrCreateYType],
    [store.repair] ([wp_store__repair_split]), [integrateDecoded],
    [depsArrived], the [wire_*] drain machinery and the [own_store]-level
    certificate specs. Split out of [yjs_store_node]; Requires the
    [yjs_store_split] pool lemmas. Same boilerplate / [#[local]]
    instances. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import yjs_core.
From New.proof Require Import yjs_common yjs_id yjs_item yjs_ytype.
From New.proof Require Import yjs_run_theory.
From New.proof Require Import yjs_history.
From New.proof Require Import yjs_store_base yjs_store_integrate.
From iris.algebra Require Import auth gmap gset.
From stdpp Require Import sorting.
From New.proof Require Import yjs_store_node yjs_store_split.

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

(* [client_run]'s merge_sort instances are [#[local]] in [yjs_store_base];
   the run-list lemmas here need them again. *)
#[local] Instance cell_le_dec : RelDecision cell_le.
Proof. rewrite /cell_le. solve_decision. Defined.
#[local] Instance cell_le_trans : Transitive cell_le.
Proof. rewrite /cell_le. move=> x y z. lia. Qed.
#[local] Instance cell_le_total : Total cell_le.
Proof. rewrite /cell_le. move=> x y. lia. Qed.

(* [is_pending_rooted]'s instances are declared in [yjs_store_base] under its
   wider section context ([Proof using Type*] closes them over instances this
   file's section lacks), so re-declare them here (the [cell_le] pattern
   above); without them [iNamed] stalls at the persistent [#Hpendroot]
   conjunct of [store_inv_excl] / [own_store]. *)
#[local] Instance pending_item_rooted_persistent' γs typedInput :
  Persistent (pending_item_rooted γs typedInput).
Proof. rewrite /pending_item_rooted. destruct (decide _); apply _. Qed.
#[local] Instance is_pending_rooted_persistent' γs pending :
  Persistent (is_pending_rooted γs pending).
Proof. apply _. Qed.
#[local] Instance pending_item_rooted_timeless' γs typedInput :
  Timeless (pending_item_rooted γs typedInput).
Proof. rewrite /pending_item_rooted. destruct (decide _); apply _. Qed.
#[local] Instance is_pending_rooted_timeless' γs pending :
  Timeless (is_pending_rooted γs pending).
Proof. apply _. Qed.

(** [word] does not use [0 <= Z.of_nat l] on its own, so a [clock + length <
    2^64] bound needs the length-nonneg fact spelled out to recover the
    per-clock [< 2^64] word conversion (issue #28 U7c). Isolated here to keep
    [word] on clean variables. *)
Lemma wp_store__getOrCreateYType (s tref : loc) (dq : dfrac) (bind : gmap P loc)
    (nm : go_string) (p : loc) :
  bind !! nm = Some p ->
  {{{ is_pkg_init yjs ∗ (s .[(yjs.store.t), "types"]) ↦ tref ∗ own_map tref dq bind }}}
    s @! (go.PointerType yjs.store) @! "getOrCreateYType" #nm
  {{{ RET #p; (s .[(yjs.store.t), "types"]) ↦ tref ∗ own_map tref dq bind }}}.
Proof using Type*.
  move=> Hp.
  iIntros (Φ) "(#Hpkg & Htypesf & Hmap) HΦ".
  wp_method_call. wp_call. wp_call. wp_auto.
  wp_apply (wp_map_lookup2 with "Hmap"). iIntros "Hmap".
  rewrite Hp /=.
  wp_auto.
  iApply "HΦ". iFrame "Htypesf Hmap".
Qed.

(* ----- the general repair (issue #28 stage D2b) ---------------------------
   [store.repair] over the invariant-carrying split wrappers: the origin ids
   may address ANY char of their covering cells' runs; the clean-end /
   clean-start splits put them on run boundaries. The two splits are
   sequenced by the wrappers' transport records. *)

(** Loc-NoDup makes the location injective on the pool. *)
Lemma pool_loc_inj (pool : list item_cell) :
  NoDup (ic_loc <$> pool) ->
  ∀ x y, x ∈ pool → y ∈ pool → ic_loc x = ic_loc y → x = y.
Proof.
  move=> Hnd x y Hx Hy Hxy.
  apply list_elem_of_lookup_1 in Hx as [ix Hix].
  apply list_elem_of_lookup_1 in Hy as [iy Hiy].
  have Hlix : (ic_loc <$> pool) !! ix = Some (ic_loc y) by (rewrite list_lookup_fmap Hix /= Hxy //).
  have Hliy : (ic_loc <$> pool) !! iy = Some (ic_loc y) by (rewrite list_lookup_fmap Hiy //).
  have Hijeq : ix = iy := NoDup_lookup _ _ _ _ Hnd Hlix Hliy.
  congruence.
Qed.

(** What [repair] guarantees about the type map: per-type model documents and
    the domain survive, and each client's run list grows by at most the two
    possible splits. *)
Definition repair_types_facts (types types2 : gmap loc type_state) : Prop :=
  (∀ p ts', types2 !! p = Some ts' ->
     ∃ ts, types !! p = Some ts ∧ ty_arr ts' = ty_arr ts ∧
           run_flatten (ty_cells ts') = run_flatten (ty_cells ts)) ∧
  (∀ p, is_Some (types !! p) -> is_Some (types2 !! p)) ∧
  (∀ kc, (length (client_run types2 kc) <= 2 + length (client_run types kc))%nat) ∧
  (∀ p ts ts', types !! p = Some ts -> types2 !! p = Some ts' ->
     Forall cell_unit (ty_cells ts) -> ts' = ts) ∧
  (∀ c', c' ∈ all_cells types2 -> ∃ c, c ∈ all_cells types ∧
     cell_client c' = cell_client c ∧
     (uint.Z (cell_clock c) <= uint.Z (cell_clock c'))%Z ∧
     (uint.Z (cell_clock c') + Z.of_nat (length (ic_run c')) <=
      uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)))%Z).

Lemma repair_types_facts_refl (types : gmap loc type_state) :
  repair_types_facts types types.
Proof.
  split_and!.
  - move=> p ts' Hp. exists ts'. split_and!; done.
  - move=> p Hp. exact Hp.
  - move=> kc. lia.
  - move=> p ts ts' Hp Hp' _. congruence.
  - move=> c' Hc'. exists c'. split_and!; [exact Hc' | done | lia | lia].
Qed.

Lemma split_step_facts_single (types types1 : gmap loc type_state) (w : item_cell) :
  split_step_facts types types1 w -> repair_types_facts types types1.
Proof.
  move=> H. destruct H as (Hp & Hd & Hr & _ & _ & Hu & Hsub).
  split_and!; [exact Hp | exact Hd | move=> kc; have := Hr kc; lia | exact Hu | exact Hsub].
Qed.

Lemma split_step_facts_compose (types types1 types2 : gmap loc type_state) (w1 w2 : item_cell) :
  split_step_facts types types1 w1 -> split_step_facts types1 types2 w2 ->
  repair_types_facts types types2.
Proof.
  move=> H1 H2.
  destruct H1 as (Hp1 & Hd1 & Hr1 & _ & _ & Hu1 & Hsub1).
  destruct H2 as (Hp2 & Hd2 & Hr2 & _ & _ & Hu2 & Hsub2).
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
Qed.

(** [store.repair], general splitting form (issue #28 stage D2b): the origin
    ids address arbitrary chars of their covering witness cells; repair puts
    both on run boundaries by splitting, and the item comes back linked to
    the boundary cells. The same-run premise (equal witnesses force the left
    origin strictly below the right one in clock) is what item validity
    provides: within one run, doc order is clock order, and an item's origin
    precedes its right origin. *)
Lemma wp_store__repair_split (s mref tref item_l pname : loc)
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
  (∀ c, c ∈ all_cells types -> (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) < 2^64)%Z) ->
  NoDup (ic_loc <$> all_cells types) ->
  cells_range_disjoint (all_cells types) ->
  (∀ c, c ∈ all_cells types -> cell_origin_clk c) ->
  {{{ is_pkg_init yjs ∗
      own_linked_item_run item_l input null null null ∗
      is_parent_name pname opn ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types ∗
      (s .[(yjs.store.t), "types"]) ↦ tref ∗ own_map tref (DfracOwn 1) bind ∗
      ([∗ map] p ↦ ts ∈ types,
          own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) }}}
    s @! (go.PointerType yjs.store) @! "repair" #item_l #pname
  {{{ (lft rgt : loc) (types2 : gmap loc type_state), RET #();
      own_linked_item_run item_l input p_t lft rgt ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types2 ∗
      (s .[(yjs.store.t), "types"]) ↦ tref ∗ own_map tref (DfracOwn 1) bind ∗
      ([∗ map] p ↦ ts ∈ types2,
          own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) ∗
      ⌜pool_invs types2⌝ ∗
      ⌜repair_types_facts types types2⌝ ∗
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
  move=> HwL HwR Hsame Hwpar Hfits Hnodup Hrangedisj Horiginclk.
  iIntros (Φ) "(#Hpkg & Hlinked & #HisPN & Hitemsf & Hitemmap & Htypesf & Htypesmap & Htypes) HΦ".
  iDestruct "Hlinked" as (itemVal oleft oright) "(Hraw & %Hfl & %Hfr & %Hfpar & %Hflags & %Hrunc)".
  iNamed "Hraw".
  iDestruct (types_cells_id_bounds2 with "Htypes") as %Hbnds0.
  have Hpinvs : pool_invs types by (split_and!; assumption).

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
    wp_apply (wp_store__splitAtAndGetLeft_inv s mref idvL types cL
                HcLmem HcLccw HcLleZ HcLltZ Hpinvs
                with "[$Hpkg $Hitemsf $Hitemmap $Htypes]").
    iIntros (types1) "(Hitemsf & Hitemmap & Htypes & %Hpinvs1 & %Hstep1 & %HbdL)".
    destruct HbdL as (cL1 & HcL1mem & HcL1loc & HcL1cl & HcL1end & HcL1par).
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
      destruct Hstep1' as (Hpres1 & Hdom1 & Hrl1 & Hstable1 & Hcover1 & Hunitp1).
      destruct (Hcover1 idvR.(yjs.id.clientId') (uint.Z idvR.(yjs.id.clock')) cR HcRmem HcRccw HcRleZ HcRltZ)
        as (cR1 & HcR1mem & HcR1cc & HcR1le & HcR1lt & HcR1parw & Hprov).
      destruct Hpinvs1 as (Hfits1 & Hnodup1 & Hrangedisj1 & Horiginclk1).
      have Hlocne : ic_loc cL1 ≠ ic_loc cR1.
      { move=> Heqloc.
        have Hceq : cL1 = cR1 := pool_loc_inj (all_cells types1) Hnodup1 _ _ HcL1mem HcR1mem Heqloc.
        have HleRL : (uint.Z idvR.(yjs.id.clock') <= uint.Z idvL.(yjs.id.clock'))%Z.
        { rewrite -Hceq in HcR1lt. clear -HcR1lt HcL1end. lia. }
        have Hfire : cL = cR -> False.
        { move=> HeqLR. have := Hsame' HeqLR. rewrite /toYjsId /=. move=> H.
          clear -H HleRL. word. }
        destruct Hprov as [Hc'c | [HcRcw _]].
        - have HlocRL : ic_loc cR = ic_loc cL.
          { rewrite -Hc'c -Hceq HcL1loc //. }
          exact (Hfire (eq_sym (pool_loc_inj (all_cells types) Hnodup _ _ HcRmem HcLmem HlocRL))).
        - exact (Hfire (eq_sym HcRcw)). }
      have Hpinvs1' : pool_invs types1 by (split_and!; assumption).
      wp_apply (wp_store__splitAtAndGetRight_inv s mref idvR types1 cR1
                  HcR1mem HcR1cc HcR1le HcR1lt Hpinvs1'
                  with "[$Hpkg $Hitemsf $Hitemmap $Htypes]").
      iIntros (rl types2) "(Hitemsf & Hitemmap & Htypes & %Hpinvs2 & %Hstep2 & %HbdR)".
      destruct HbdR as (cR2 & HcR2mem & HcR2loc & HcR2cl & HcR2clk & HcR2par).
      wp_auto.
      have Hstep2' := Hstep2.
      destruct Hstep2' as (Hpres2 & Hdom2 & Hrl2 & Hstable2 & Hcover2 & Hunitp2).
      have HcL2mem : cL1 ∈ all_cells types2 := Hstable2 cL1 HcL1mem Hlocne.
      have HparR : ic_parent cR2 = ic_parent cR by rewrite HcR2par HcR1parw //.
      destruct opn as [nm|].
      * (* Parent::String *)
        iDestruct "HisPN" as "[%HnnP #HpnC]".
        rewrite (bool_decide_eq_false_2 (pname = null) HnnP) /=.
        wp_auto.
        wp_apply (wp_store__getOrCreateYType s tref (DfracOwn 1) bind nm p_t Hwpar
                    with "[$Htypesf $Htypesmap]").
        iIntros "(Htypesf & Htypesmap)".
        wp_auto.
        iApply ("HΦ" $! (ic_loc cL) rl types2).
        iFrame "Hitemsf Hitemmap Htypesf Htypesmap Htypes".
        iSplitL "Hitem".
        { iExists _, (Some idvL), (Some idvR). rewrite /own_fresh_item_raw. simpl.
          iFrame "Hitem". iFrame "HolC HorC".
          iPureIntro. split_and!; try done. }
        iPureIntro. split_and!.
        { destruct Hpinvs2 as (?&?&?&?). split_and!; assumption. }
        { exact (split_step_facts_compose types types1 types2 cL cR1 Hstep1 Hstep2). }
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
        iDestruct (types_cell_acc_gen types2 cL1 HcL2mem with "Htypes") as "Hacc".
        iNamed "Hacc".
        iDestruct (typed_pointsto_not_null with "Hval") as %HnnCL.
        iEval (rewrite HcL1loc) in "Hval".
        wp_auto.
        rewrite (bool_decide_eq_false_2 (cL.(ic_loc) = null) ltac:(rewrite -HcL1loc; exact HnnCL)) /=.
        wp_auto.
        iEval (rewrite -HcL1loc) in "Hval".
        iDestruct ("Hback" with "Hval") as "Htypes".
        rewrite Hpar HcL1par Hwpar.
        iApply ("HΦ" $! (ic_loc cL) rl types2).
        iFrame "Hitemsf Hitemmap Htypesf Htypesmap Htypes".
        iSplitL "Hitem".
        { iExists _, (Some idvL), (Some idvR). rewrite /own_fresh_item_raw. simpl.
          iFrame "Hitem". iFrame "HolC HorC".
          iPureIntro. split_and!; try done. }
        iPureIntro. split_and!.
        { destruct Hpinvs2 as (?&?&?&?). split_and!; assumption. }
        { exact (split_step_facts_compose types types1 types2 cL cR1 Hstep1 Hstep2). }
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
        wp_apply (wp_store__getOrCreateYType s tref (DfracOwn 1) bind nm p_t Hwpar
                    with "[$Htypesf $Htypesmap]").
        iIntros "(Htypesf & Htypesmap)".
        wp_auto.
        iApply ("HΦ" $! (ic_loc cL) null types1).
        iFrame "Hitemsf Hitemmap Htypesf Htypesmap Htypes".
        iSplitL "Hitem".
        { iExists _, (Some idvL), None. rewrite /own_fresh_item_raw. simpl.
          iFrame "Hitem". iFrame "HolC".
          iPureIntro. split_and!; try done. }
        iPureIntro. split_and!.
        { destruct Hpinvs1 as (?&?&?&?). split_and!; assumption. }
        { exact (split_step_facts_single types types1 cL Hstep1). }
        { rewrite HinlS /=. split; [done |].
          exists cL1. split_and!;
            [exact HcL1mem | rewrite HcL1loc // | | | rewrite HcL1par //].
          - rewrite HcL1cl /toYjsId /=. word.
          - move: HcL1end. rewrite /toYjsId /=. move=> H. word. }
        { rewrite HinrN //. }
      * (* Parent::None: borrow from the resolved left neighbour *)
        iDestruct "HisPN" as "%HpN".
        rewrite (bool_decide_eq_true_2 (pname = null) HpN) /=.
        iDestruct (types_cell_acc_gen types1 cL1 HcL1mem with "Htypes") as "Hacc".
        iNamed "Hacc".
        iDestruct (typed_pointsto_not_null with "Hval") as %HnnCL.
        iEval (rewrite HcL1loc) in "Hval".
        wp_auto.
        rewrite (bool_decide_eq_false_2 (cL.(ic_loc) = null) ltac:(rewrite -HcL1loc; exact HnnCL)) /=.
        wp_auto.
        iEval (rewrite -HcL1loc) in "Hval".
        iDestruct ("Hback" with "Hval") as "Htypes".
        rewrite Hpar HcL1par Hwpar.
        iApply ("HΦ" $! (ic_loc cL) null types1).
        iFrame "Hitemsf Hitemmap Htypesf Htypesmap Htypes".
        iSplitL "Hitem".
        { iExists _, (Some idvL), None. rewrite /own_fresh_item_raw. simpl.
          iFrame "Hitem". iFrame "HolC".
          iPureIntro. split_and!; try done. }
        iPureIntro. split_and!.
        { destruct Hpinvs1 as (?&?&?&?). split_and!; assumption. }
        { exact (split_step_facts_single types types1 cL Hstep1). }
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
      wp_apply (wp_store__splitAtAndGetRight_inv s mref idvR types cR
                  HcRmem HcRccw HcRleZ HcRltZ Hpinvs
                  with "[$Hpkg $Hitemsf $Hitemmap $Htypes]").
      iIntros (rl types2) "(Hitemsf & Hitemmap & Htypes & %Hpinvs2 & %Hstep2 & %HbdR)".
      destruct HbdR as (cR2 & HcR2mem & HcR2loc & HcR2cl & HcR2clk & HcR2par).
      wp_auto.
      destruct opn as [nm|].
      * (* Parent::String *)
        iDestruct "HisPN" as "[%HnnP #HpnC]".
        rewrite (bool_decide_eq_false_2 (pname = null) HnnP) /=.
        wp_auto.
        wp_apply (wp_store__getOrCreateYType s tref (DfracOwn 1) bind nm p_t Hwpar
                    with "[$Htypesf $Htypesmap]").
        iIntros "(Htypesf & Htypesmap)".
        wp_auto.
        iApply ("HΦ" $! null rl types2).
        iFrame "Hitemsf Hitemmap Htypesf Htypesmap Htypes".
        iSplitL "Hitem".
        { iExists _, None, (Some idvR). rewrite /own_fresh_item_raw. simpl.
          iFrame "Hitem". iFrame "HorC".
          iPureIntro. split_and!; try done. }
        iPureIntro. split_and!.
        { destruct Hpinvs2 as (?&?&?&?). split_and!; assumption. }
        { exact (split_step_facts_single types types2 cR Hstep2). }
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
        iDestruct (types_cell_acc_gen types2 cR2 HcR2mem with "Htypes") as "Hacc".
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
        iApply ("HΦ" $! null rl types2).
        iFrame "Hitemsf Hitemmap Htypesf Htypesmap Htypes".
        iSplitL "Hitem".
        { iExists _, None, (Some idvR). rewrite /own_fresh_item_raw. simpl.
          iFrame "Hitem". iFrame "HorC".
          iPureIntro. split_and!; try done. }
        iPureIntro. split_and!.
        { destruct Hpinvs2 as (?&?&?&?). split_and!; assumption. }
        { exact (split_step_facts_single types types2 cR Hstep2). }
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
      wp_apply (wp_store__getOrCreateYType s tref (DfracOwn 1) bind nm p_t Hwpar
                  with "[$Htypesf $Htypesmap]").
      iIntros "(Htypesf & Htypesmap)".
      wp_auto.
      iApply ("HΦ" $! null null types).
      iFrame "Hitemsf Hitemmap Htypesf Htypesmap Htypes".
      iSplitL "Hitem".
      { iExists _, None, None. rewrite /own_fresh_item_raw. simpl.
        iFrame "Hitem".
        iPureIntro. split_and!; try done. }
      iPureIntro. split_and!.
      { split_and!; assumption. }
      { exact (repair_types_facts_refl types). }
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

(** The id of the [o]-th char of a chained run: same client, head clock + o. *)
Lemma run_wf_char_id (r : list (YjsItem A)) (o : nat) (x : YjsItem A) :
  run_wf r -> r !! o = Some x ->
  item_id x = MkYjsId (clientId (item_id (hd inhabitant r)))
                      (clock (item_id (hd inhabitant r)) + o).
Proof.
  move=> [Hne Hstep].
  elim: o x => [| o IH] x Hx.
  - destruct r as [| h t]; first done.
    move: Hx => /= [= <-]. rewrite Nat.add_0_r. by destruct (item_id h).
  - have Hprev : is_Some (r !! o).
    { apply lookup_lt_is_Some. apply lookup_lt_Some in Hx. lia. }
    destruct Hprev as [y Hy].
    have [Hid _] := Hstep o y x Hy Hx.
    rewrite Hid (IH y Hy) /=. f_equal. lia.
Qed.

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

(** Converse: the [off]-th char of cell [ci] sits at prefix-sum + [off]. *)
Lemma run_flatten_lookup_of_cell (cells : list item_cell) (ci off : nat)
    (c : item_cell) (it : YjsItem A) :
  cells !! ci = Some c -> ic_run c !! off = Some it ->
  run_flatten cells !! (length (run_flatten (take ci cells)) + off)%nat = Some it.
Proof.
  move=> Hci Hoff.
  have Hsplit := take_drop_middle cells ci c Hci.
  have Hdec : run_flatten cells
            = run_flatten (take ci cells) ++ ic_run c ++ run_flatten (drop (S ci) cells).
  { transitivity (run_flatten (take ci cells ++ c :: drop (S ci) cells)).
    - by rewrite Hsplit.
    - by rewrite run_flatten_app run_flatten_cons. }
  rewrite Hdec lookup_app_r; last lia.
  replace (length (run_flatten (take ci cells)) + off -
           length (run_flatten (take ci cells)))%nat with off by lia.
  rewrite lookup_app_l; [exact Hoff | by apply lookup_lt_Some in Hoff].
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

(** Every cell of a DLL segment carries a well-formed run (pure extraction;
    the run-aware counterpart of the unit scaffold's per-cell length pin). *)
Lemma own_dll_runs_wf (dq : dfrac) (l last prev next : loc) (cells : list item_cell) :
  own_dll dq l last prev next cells -∗
  ⌜∀ c, c ∈ cells → run_wf (ic_run c)⌝.
Proof.
  iInduction cells as [|c0 cells] "IH" forall (l prev).
  - iIntros "_". iPureIntro. move=> c Hc. rewrite elem_of_nil in Hc. done.
  - iIntros "H". iNamed "H".
    iDestruct ("IH" with "Hrest") as %Hrest.
    iPureIntro. move=> c Hc.
    apply elem_of_cons in Hc as [-> | Hc]; last exact (Hrest c Hc).
    exact Hrun.
Qed.

(** Pure extractions read off the types big-sep: pool-wide run
    well-formedness, parent discipline, the per-entry document invariant,
    and the cells/model isomorphism. *)
Lemma types_runs_wf2 (types : gmap loc type_state) :
  ([∗ map] parent ↦ ts ∈ types,
      own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
      ⌜YjsArrInvariant (ty_arr ts)⌝) -∗
  ⌜∀ c, c ∈ all_cells types → run_wf (ic_run c)⌝.
Proof.
  iIntros "Htypes".
  iAssert ([∗ map] p ↦ ts ∈ types, ⌜∀ c, c ∈ ty_cells ts → run_wf (ic_run c)⌝)%I
    with "[Htypes]" as "H".
  { iApply (big_sepM_impl with "Htypes").
    iIntros "!#" (p ts Hp) "(Hyt & _)".
    iDestruct "Hyt" as (yt tl) "(Hp' & Hdll & %Hlen & %Hrepr & %Hcpar)".
    iApply (own_dll_runs_wf with "Hdll"). }
  iDestruct (big_sepM_pure with "H") as %Hall.
  iPureIntro. move=> c Hc.
  apply all_cells_elem_of in Hc. destruct Hc as (p & ts & Hp & Hcts).
  exact (Hall p ts Hp c Hcts).
Qed.

Lemma types_parents_all2 (types : gmap loc type_state) :
  ([∗ map] parent ↦ ts ∈ types,
      own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
      ⌜YjsArrInvariant (ty_arr ts)⌝) -∗
  ⌜∀ p ts c, types !! p = Some ts → c ∈ ty_cells ts → ic_parent c = p⌝.
Proof.
  iIntros "Htypes".
  iAssert ([∗ map] p ↦ ts ∈ types, ⌜∀ c, c ∈ ty_cells ts → ic_parent c = p⌝)%I
    with "[Htypes]" as "H".
  { iApply (big_sepM_impl with "Htypes").
    iIntros "!#" (p ts Hp) "(Hyt & _)".
    iDestruct "Hyt" as (yt tl) "(Hp' & Hdll & %Hlen & %Hrepr & %Hcpar)".
    by iPureIntro. }
  iDestruct (big_sepM_pure with "H") as %Hall.
  iPureIntro. move=> p ts c Hp Hc. exact (Hall p ts Hp c Hc).
Qed.

Lemma types_arr_inv2 (types : gmap loc type_state) :
  ([∗ map] parent ↦ ts ∈ types,
      own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
      ⌜YjsArrInvariant (ty_arr ts)⌝) -∗
  ⌜∀ p ts, types !! p = Some ts -> YjsArrInvariant (ty_arr ts)⌝.
Proof.
  iIntros "Htypes".
  iAssert ([∗ map] p ↦ ts ∈ types, ⌜YjsArrInvariant (ty_arr ts)⌝)%I
    with "[Htypes]" as "H".
  { iApply (big_sepM_impl with "Htypes").
    iIntros "!#" (p ts Hp) "(_ & %Hi)". by iPureIntro. }
  iDestruct (big_sepM_pure with "H") as %Hall.
  iPureIntro. move=> p ts Hp. exact (Hall p ts Hp).
Qed.

Lemma types_repr_all2 (types : gmap loc type_state) :
  ([∗ map] parent ↦ ts ∈ types,
      own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
      ⌜YjsArrInvariant (ty_arr ts)⌝) -∗
  ⌜∀ p ts, types !! p = Some ts -> cells_repr (ty_arr ts) (ty_cells ts) (ty_arr ts)⌝.
Proof.
  iIntros "Htypes".
  iAssert ([∗ map] p ↦ ts ∈ types,
      ⌜cells_repr (ty_arr ts) (ty_cells ts) (ty_arr ts)⌝)%I
    with "[Htypes]" as "H".
  { iApply (big_sepM_impl with "Htypes").
    iIntros "!#" (p ts Hp) "(Hyt & _)".
    iDestruct "Hyt" as (yt tl) "(Hp' & Hdll & %Hlen & %Hrepr & %Hcpar)".
    by iPureIntro. }
  iDestruct (big_sepM_pure with "H") as %Hall.
  iPureIntro. move=> p ts Hp. exact (Hall p ts Hp).
Qed.

Lemma types_entry_pures2 (types : gmap loc type_state) (p : loc) (ts : type_state) :
  types !! p = Some ts ->
  ([∗ map] parent ↦ ts0 ∈ types,
      own_ytype_cells parent (DfracOwn 1) (ty_cells ts0) (ty_arr ts0) ∗
      ⌜YjsArrInvariant (ty_arr ts0)⌝) -∗
  ⌜cells_repr (ty_arr ts) (ty_cells ts) (ty_arr ts) ∧
   (∀ c, c ∈ ty_cells ts -> ic_parent c = p)⌝.
Proof.
  move=> Hp. iIntros "Htypes".
  iDestruct (big_sepM_lookup_acc _ _ p ts Hp with "Htypes") as "[(Hyt & _) _]".
  iDestruct "Hyt" as (yt tl) "(Hp' & Hdll & %Hlen & %Hrepr & %Hcpar)".
  iPureIntro. split; [exact Hrepr | exact Hcpar].
Qed.
(** [store_inv] is exactly [own_store] with the model existentially closed.
    The forward direction restates the per-client counter clause at the
    model; the backward direction re-derives the [types]-level and the W64
    cell-level counter bounds from the model-level one, via the registry
    coherence and the DLL id-bound pins. A lock-holding caller uses this to
    trade the lock body for [own_store] (feeding a store-state spec such as
    [wp_store__applyUpdate_certs]) and back. The pending buffer (issue #40) is
    threaded through unchanged. *)
Lemma store_inv_own_store (s_loc : loc) (γs : store_names) (γh : history_names) :
  store_inv s_loc γs γh ⊣⊢
  ∃ (c : ClientId) (h : list Ev) (m : DocModel)
    (pend : list (TId * IntegrateInput (A := A))),
    own_store s_loc γs γh c h m pend.
Proof.
  iSplit.
  - iIntros "H". iNamed "H". iNamed "Hexcl". iNamed "Hro".
    iExists (uint.nat client), h, m, pend.
    iExists client, k, items_mref, types_mref, dset, pend_sl, types, bind, acc.
    iFrame "∗#".
    iPureIntro. split_and!.
    + reflexivity.
    + exact Hpendbnd.
    + rewrite /doc_registry_coh. split_and!; assumption.
    + exact Hhcoh.
    + (* the model-level counter from the [types]-level one *)
      move=> t x Hx Hcx.
      have Hne : doc_model_get m t ≠ [].
      { move=> Heq. move: Hx. rewrite Heq elem_of_nil. done. }
      destruct (Hmdom t Hne) as (nm & p & -> & Hbnm).
      destruct (Hbindtypes nm p Hbnm) as [ts Hts].
      have Hdg : doc_model_get m (RootId nm) = ty_arr ts := Hmtypes nm p ts Hbnm Hts.
      rewrite Hdg in Hx.
      exact (Hctr p ts x Hts Hx Hcx).
    + exact Hlocdup.
    + exact Hrangedisj.
    + exact Hrunfits.
    + exact Horiginclk.
    + exact Hacccoh.
  - iIntros "H". iDestruct "H" as (c h m pend) "H". iNamed "H". subst c.
    iDestruct (types_repr_all2 with "Htypes") as %Hreprall.
    iDestruct (types_cells_id_bounds2 with "Htypes") as %Hcellbnd.
    destruct Hregcoh as (Hbindtypes & Hbindinj & Htypesbound & Hmtypes & Hmdom).
    (* the [types]-level counter from the model-level one *)
    have Hctrt : ∀ parent ts x, types !! parent = Some ts -> x ∈ ty_arr ts ->
        clientId (item_id x) = uint.nat client -> (clock (item_id x) < uint.nat k)%nat.
    { move=> parent ts x Hts Hx Hcx.
      destruct (Htypesbound parent (ex_intro _ ts Hts)) as [nm Hbnm].
      have Hdg : doc_model_get m (RootId nm) = ty_arr ts := Hmtypes nm parent ts Hbnm Hts.
      apply (Hctr (RootId nm) x); [by rewrite Hdg | exact Hcx]. }
    (* the W64 cell-level shadow, via the id-bound pins *)
    iDestruct (types_runs_wf2 with "Htypes") as %Hrunwfall0.
    have Hcellctr : ∀ c0, c0 ∈ all_cells types -> cell_client c0 = client ->
        (uint.Z (cell_clock c0) + Z.of_nat (length (ic_run c0)) <= uint.Z k)%Z.
    { move=> c0 Hc0 Hcc.
      have Hc0m := Hc0. apply all_cells_elem_of in Hc0m.
      destruct Hc0m as (p & ts & Hts & Hcts).
      have Hwf : run_wf (ic_run c0) := Hrunwfall0 c0 Hc0.
      have Hlen1 : (1 <= length (ic_run c0))%nat.
      { destruct (ic_run c0) eqn:Hrc; [exact (False_ind _ (proj1 Hwf eq_refl)) | simpl; lia]. }
      destruct (lookup_lt_is_Some_2 (ic_run c0) (length (ic_run c0) - 1)%nat ltac:(lia)) as [xl Hxl].
      have Hxlid := run_wf_char_id _ _ _ Hwf Hxl.
      apply list_elem_of_lookup_1 in Hcts as [ci Hci].
      have Hxlmem : xl ∈ ty_arr ts.
      { rewrite (Hreprall p ts Hts).
        apply (list_elem_of_lookup_2 _
                 (length (run_flatten (take ci (ty_cells ts))) + (length (ic_run c0) - 1))%nat).
        exact (run_flatten_lookup_of_cell (ty_cells ts) ci _ c0 xl Hci Hxl). }
      have [Hcb Hkb] := Hcellbnd c0 Hc0.
      have Hceq : clientId (item_id xl) = uint.nat client.
      { move: Hcc. rewrite /cell_client /run_head. move=> Hcc.
        have Hz : uint.Z (W64 (clientId (item_id (hd inhabitant (ic_run c0))))) = uint.Z client
          by rewrite Hcc.
        have Hcb' : (Z.of_nat (clientId (item_id (hd inhabitant (ic_run c0)))) < 2^64)%Z := Hcb.
        have Hcl2 : clientId (item_id (hd inhabitant (ic_run c0))) = uint.nat client.
        { clear -Hz Hcb'. word. }
        rewrite Hxlid. exact Hcl2. }
      have Hlt := Hctrt p ts xl Hts Hxlmem Hceq.
      rewrite Hxlid in Hlt.
      have Hlt2 : (clock (item_id (hd inhabitant (ic_run c0))) + (length (ic_run c0) - 1)
                   < uint.nat k)%nat := Hlt.
      rewrite /run_head in Hkb.
      have Hlt3 : (clock (item_id (hd inhabitant (ic_run c0))) + length (ic_run c0)
                   <= uint.nat k)%nat.
      { clear -Hlt2 Hlen1. lia. }
      rewrite /cell_clock /run_head. clear -Hlt3 Hkb. word. }
    iExists client, k, items_mref, types_mref, dset, pend_sl, types, bind, h, m, pend.
    iSplitR "Hseq Htypes"; last by iFrame "Hseq Htypes".
    iExists acc.
    iFrame "Hclient Hclock Hitemsf Hitemmap Htypesf Htypesmap Hdset Hpendf Hpend Hpendcert Hpendroot HtypesAuth Hbinds Hhist Hacc".
    iPureIntro. split_and!;
      [exact Hpendbnd | exact Hctrt | exact Hcellctr | exact Hlocdup | exact Hrangedisj
      | exact Hrunfits | exact Horiginclk | exact Hbindtypes | exact Hbindinj
      | exact Htypesbound | exact Hhcoh | exact Hmtypes | exact Hmdom | exact Hacccoh].
Qed.

(* ===== #40 gate toolkit (getNodeIndex/GetNode covering-total, hasNode) =====
   The pending gate probes ids that may address ANY char of a run cell (a
   mid-run origin) and that may be absent, so the total form returns a found
   bool over the COVERING relation (issue #40 x issue #28 U7c): [ok] iff some
   run cell's clock range [cell_clock, cell_clock + len) covers [clk]. Index-
   wise range-disjointness of the run ([Hidisj], from the pool's
   [cells_range_disjoint] + loc-NoDup at the call site) makes the covering cell
   unique so the binary search corners it; the empty-window exit certifies that
   no run cell covers [clk]. *)
Lemma wp_getNodeIndex_total (sl : slice.t) (dq : dfrac) (types : gmap loc type_state)
    (run : list item_cell) (clk : w64) :
  StronglySorted cell_le run ->
  (∀ c, c ∈ run -> c ∈ all_cells types) ->
  (∀ c, c ∈ run -> (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) < 2^64)%Z) ->
  (∀ (k1 k2 : nat) (c1 c2 : item_cell),
     run !! k1 = Some c1 -> run !! k2 = Some c2 -> k1 ≠ k2 ->
     (uint.Z (cell_clock c1) + Z.of_nat (length (ic_run c1)) <= uint.Z (cell_clock c2))%Z ∨
     (uint.Z (cell_clock c2) + Z.of_nat (length (ic_run c2)) <= uint.Z (cell_clock c1))%Z) ->
  {{{ is_pkg_init yjs ∗ sl ↦*{dq} (ic_loc <$> run) ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) }}}
    @! yjs.getNodeIndex #sl #clk
  {{{ (i : w64) (ok : bool), RET (#i, #ok);
      sl ↦*{dq} (ic_loc <$> run) ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) ∗
      ⌜if ok then ∃ c, run !! uint.nat i = Some c ∧
             (uint.Z (cell_clock c) <= uint.Z clk)%Z ∧
             (uint.Z clk < uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)))%Z
       else ∀ (k : nat) (c : item_cell), run !! k = Some c ->
             (uint.Z (cell_clock c) <= uint.Z clk)%Z ->
             (uint.Z clk < uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)))%Z -> False⌝ }}}.
Proof using Type*.
  move=> Hsort Hmem Hrunfits Hidisj.
  wp_start as "(Hsl & Htypes)".
  iDestruct (own_slice_len with "Hsl") as %[Hsllen Hsllen0].
  rewrite length_fmap in Hsllen Hsllen0.
  wp_auto.
  (* loop invariant: the window [lo, hi) contains every COVERING cell *)
  iAssert (∃ (lo hi : w64),
    "Hleft" ∷ left_ptr ↦ lo ∗ "Hright" ∷ right_ptr ↦ hi ∗
    "Hnodes" ∷ nodes_ptr ↦ sl ∗ "Hclock" ∷ clock_ptr ↦ clk ∗
    "Hsl" ∷ sl ↦*{dq} (ic_loc <$> run) ∗
    "Htypes" ∷ ([∗ map] parent ↦ ts ∈ types,
        own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
        ⌜YjsArrInvariant (ty_arr ts)⌝) ∗
    "%Hbnd" ∷ ⌜(0 <= uint.Z lo /\ uint.Z hi <= Z.of_nat (length run))%Z⌝ ∗
    "%Hwin" ∷ ⌜∀ (k : nat) (c : item_cell), run !! k = Some c ->
                (uint.Z (cell_clock c) <= uint.Z clk)%Z ->
                (uint.Z clk < uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)))%Z ->
                (uint.Z lo <= Z.of_nat k < uint.Z hi)%Z⌝)%I
    with "[left right nodes clock Hsl Htypes]" as "IH".
  { iExists (W64 0), sl.(slice.len).
    iFrame "left right nodes clock Hsl Htypes".
    iPureIntro. split; [word |].
    move=> k c Hk _ _. have Hklt := lookup_lt_Some _ _ _ Hk. word. }
  wp_for "IH".
  case_bool_decide as Hcond.
  - (* probe the middle *)
    set (mid := word.add lo (word.divu (word.sub hi lo) (W64 2))).
    have Hmid : (uint.Z lo <= uint.Z mid < uint.Z hi)%Z.
    { rewrite /mid. destruct Hbnd as [Hb1 Hb2]. word. }
    wp_auto.
    rewrite decide_True; last word.
    have Hmidlt : (uint.nat mid < length run)%nat by word.
    destruct (run !! uint.nat mid) as [cmid|] eqn:Hcmid;
      last by (apply lookup_ge_None in Hcmid; lia).
    have Hlocmid : (ic_loc <$> run) !! uint.nat mid = Some cmid.(ic_loc)
      by rewrite list_lookup_fmap Hcmid //.
    iDestruct (own_slice_elem_acc (sint.Z mid) (ic_loc cmid) sl dq (ic_loc <$> run) with "Hsl") as "[Hel Hgive]".
    { word. }
    { replace (Z.to_nat (sint.Z mid)) with (uint.nat mid) by word. exact Hlocmid. }
    wp_auto.
    iDestruct ("Hgive" $! cmid.(ic_loc) with "Hel") as "Hsl".
    have Hinsid : (<[sint.nat mid := cmid.(ic_loc)]> (ic_loc <$> run)) = (ic_loc <$> run).
    { apply list_insert_id. replace (sint.nat mid) with (uint.nat mid) by word. exact Hlocmid. }
    iEval (rewrite Hinsid) in "Hsl".
    have Hcmemall : cmid ∈ all_cells types
      by (apply Hmem; exact (list_elem_of_lookup_2 _ _ _ Hcmid)).
    iDestruct (types_cell_acc_gen types cmid Hcmemall with "Htypes") as "Hacc".
    iNamed "Hacc".
    wp_auto.
    have Hmcv : cell_clock cmid = itemVal.(yjs.item.id').(yjs.id.clock')
      by (rewrite /cell_clock Hid /toYjsId /=; word).
    have HlenEq : length (itemVal.(yjs.item.content').(yjs.content.content')) = length (ic_run cmid).
    { have H := f_equal length Hcontent.
      rewrite length_fmap explode_length /toContent in H. lia. }
    have Hlenpos : (1 <= Z.of_nat (length (ic_run cmid)))%Z.
    { have [Hne _] := Hrun. destruct (ic_run cmid) as [|? ?]; [done | simpl; lia]. }
    have Hnw : (uint.Z (cell_clock cmid) + Z.of_nat (length (ic_run cmid)) < 2^64)%Z
      by (apply Hrunfits; exact (list_elem_of_lookup_2 _ _ _ Hcmid)).
    wp_apply (wp_item__Len cmid.(ic_loc) (DfracOwn 1) itemVal with "[$Hval]"). iIntros "Hval".
    rewrite HlenEq.
    iDestruct ("Hback" with "Hval") as "Htypes".
    wp_auto.
    destruct (bool_decide (uint.Z clk < uint.Z itemVal.(yjs.item.id').(yjs.id.clock'))) eqn:Hcmp1.
    + (* clk < middleClock: every covering cell sits strictly left of [mid] *)
      apply bool_decide_eq_true_1 in Hcmp1.
      wp_auto. wp_for_post.
      iFrame "HΦ". iExists lo, mid.
      iFrame "Hleft Hright Hnodes Hclock Hsl Htypes".
      iPureIntro. split.
      { lia. }
      move=> k c Hk Hcov1 Hcov2.
      have [Hlo Hhi] := Hwin k c Hk Hcov1 Hcov2.
      split; [exact Hlo |].
      destruct (Nat.lt_trichotomy k (uint.nat mid)) as [Hlt | [Heq | Hgt]].
      * lia.
      * exfalso. subst k. rewrite Hcmid in Hk. injection Hk as <-.
        rewrite Hmcv in Hcov1. lia.
      * exfalso.
        have Hle := StronglySorted_lookup_le cell_le run (uint.nat mid) k cmid c Hsort Hcmid Hk Hgt.
        rewrite /cell_le Hmcv in Hle. lia.
    + apply bool_decide_eq_false_1 in Hcmp1.
      rewrite Hmcv in Hnw.
      wp_auto.
      case_bool_decide as Hcmp2.
      * (* clk >= middleEnd: every covering cell sits strictly right of [mid] *)
        wp_auto. wp_for_post.
        iFrame "HΦ". iExists (word.add mid (W64 1)), hi.
        iFrame "Hleft Hright Hnodes Hclock Hsl Htypes".
        have Hmide : (uint.Z (w64_word_instance.(word.add) itemVal.(yjs.item.id').(yjs.id.clock') (W64 (length (ic_run cmid))))
                      = uint.Z itemVal.(yjs.item.id').(yjs.id.clock') + Z.of_nat (length (ic_run cmid)))%Z by word.
        rewrite Hmide in Hcmp2.
        iPureIntro. split.
        { word. }
        move=> k c Hk Hcov1 Hcov2.
        have [Hlo Hhi] := Hwin k c Hk Hcov1 Hcov2.
        split; [| exact Hhi].
        destruct (Nat.lt_trichotomy k (uint.nat mid)) as [Hlt | [Heq | Hgt]].
        { exfalso.
          have Hle := StronglySorted_lookup_le cell_le run k (uint.nat mid) c cmid Hsort Hk Hcmid Hlt.
          rewrite /cell_le Hmcv in Hle.
          destruct (Hidisj k (uint.nat mid) c cmid Hk Hcmid ltac:(lia)) as [Hd | Hd];
            rewrite Hmcv in Hd; lia. }
        { exfalso. subst k. rewrite Hcmid in Hk. injection Hk as <-.
          rewrite Hmcv in Hcov2. lia. }
        word.
      * (* middleClock <= clk < middleEnd: the probe COVERS clk *)
        wp_auto. wp_for_post.
        iApply ("HΦ" $! mid true). iFrame "Hsl Htypes".
        iExists cmid. iPureIntro. split; [exact Hcmid |].
        split; rewrite Hmcv; word.
  - (* the window is empty: no run cell covers [clk] *)
    wp_auto.
    iApply ("HΦ" $! (W64 0) false). iFrame "Hsl Htypes".
    iPureIntro. move=> k c Hk Hcov1 Hcov2.
    have := Hwin k c Hk Hcov1 Hcov2. lia.
Qed.

(** [cell_covers c d]: the model id [d] addresses a char of cell [c]'s run
    (issue #28 U7c): same client as the run head, and clock inside the run's
    range [head clock, head clock + run length). The per-char [run_wf] id law
    ([run_wf_char_id]) makes this exactly "[d] is the id of some [ic_run c]
    char". Replaces the all-singleton head-only [item_id (run_head c) = d]. *)
Definition cell_covers (c : item_cell) (d : YjsId) : Prop :=
  clientId (item_id (run_head c)) = clientId d ∧
  (clock (item_id (run_head c)) <= clock d)%nat ∧
  (clock d < clock (item_id (run_head c)) + length (ic_run c))%nat.

(** [store.GetNode], covering-TOTAL (issue #40 x issue #28 U7c): the pending
    gate probes ids that may address ANY char of a run cell and that may be
    absent, so both miss paths (unknown client, clock not covered by any run)
    are live. [ok = true] pins the returned loc to a store cell whose run
    covers the probed id; [ok = false] certifies no store cell's run covers it.
    Range-disjointness + loc-NoDup make the covering cell unique. *)
Lemma wp_store__GetNode_total (s mref : loc) (dq : dfrac) (idv : yjs.id.t)
    (types : gmap loc type_state) :
  (∀ c, c ∈ all_cells types -> (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) < 2^64)%Z) ->
  NoDup (ic_loc <$> all_cells types) ->
  cells_range_disjoint (all_cells types) ->
  {{{ is_pkg_init yjs ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref dq types ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) }}}
    s @! (go.PointerType yjs.store) @! "GetNode" #idv
  {{{ (l : loc) (ok : bool), RET (#l, #ok);
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref dq types ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) ∗
      ⌜if ok
       then ∃ c, c ∈ all_cells types ∧ cell_client c = idv.(yjs.id.clientId') ∧
                 (uint.Z (cell_clock c) <= uint.Z idv.(yjs.id.clock'))%Z ∧
                 (uint.Z idv.(yjs.id.clock') < uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)))%Z ∧
                 ic_loc c = l
       else ∀ c, c ∈ all_cells types -> cell_client c = idv.(yjs.id.clientId') ->
                 (uint.Z (cell_clock c) <= uint.Z idv.(yjs.id.clock'))%Z ->
                 (uint.Z idv.(yjs.id.clock') < uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)))%Z -> False⌝ }}}.
Proof using Type*.
  move=> Hrunfits Hnodup Hrangedisj.
  iIntros (Φ) "(#Hpkg & Hitemsf & Hitemmap & Htypes) HΦ".
  set (kc := idv.(yjs.id.clientId')).
  iNamed "Hitemmap".
  wp_method_call. wp_call. wp_call. wp_auto.
  wp_apply (wp_map_lookup2 with "Hmap"). iIntros "Hmap".
  destruct (gm !! kc) as [slk |] eqn:Hslk; rewrite Hslk /=.
  - (* known client: run the binary search *)
    wp_auto.
    iDestruct (big_sepM_lookup_acc _ _ kc slk Hslk with "Hruns") as "[Hrun Hrunsback]".
    iNamed "Hrun".
    (* index-wise clock-range disjointness of the client's run *)
    have Hrunfits' : ∀ c, c ∈ client_run types kc ->
        (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) < 2^64)%Z.
    { move=> c Hc. exact (Hrunfits c (proj1 (proj1 (client_run_mem types kc c) Hc))). }
    have HndAll : NoDup (all_cells types) := NoDup_fmap_1 ic_loc _ Hnodup.
    have Hndrun : NoDup (client_run types kc).
    { rewrite /client_run (merge_sort_Permutation cell_le _). apply NoDup_filter. exact HndAll. }
    have Hinj : ∀ x y, x ∈ client_run types kc → y ∈ client_run types kc → ic_loc x = ic_loc y → x = y.
    { move=> x y Hx Hy Hxy.
      have Hxa : x ∈ all_cells types := proj1 (proj1 (client_run_mem types kc x) Hx).
      have Hya : y ∈ all_cells types := proj1 (proj1 (client_run_mem types kc y) Hy).
      apply list_elem_of_lookup_1 in Hxa as [ix Hix]. apply list_elem_of_lookup_1 in Hya as [iy Hiy].
      have Hlix : (ic_loc <$> all_cells types) !! ix = Some (ic_loc y) by (rewrite list_lookup_fmap Hix /= Hxy //).
      have Hliy : (ic_loc <$> all_cells types) !! iy = Some (ic_loc y) by (rewrite list_lookup_fmap Hiy //).
      have Hijeq : ix = iy := NoDup_lookup _ _ _ _ Hnodup Hlix Hliy.
      congruence. }
    have Hidisj : ∀ (k1 k2 : nat) (c1 c2 : item_cell),
        client_run types kc !! k1 = Some c1 -> client_run types kc !! k2 = Some c2 -> k1 ≠ k2 ->
        (uint.Z (cell_clock c1) + Z.of_nat (length (ic_run c1)) <= uint.Z (cell_clock c2))%Z ∨
        (uint.Z (cell_clock c2) + Z.of_nat (length (ic_run c2)) <= uint.Z (cell_clock c1))%Z.
    { move=> k1 k2 c1 c2 Hk1 Hk2 Hkne.
      have Hc1r : c1 ∈ client_run types kc := list_elem_of_lookup_2 _ _ _ Hk1.
      have Hc2r : c2 ∈ client_run types kc := list_elem_of_lookup_2 _ _ _ Hk2.
      have Hlocne : ic_loc c1 ≠ ic_loc c2.
      { move=> Heq. have Hceq : c1 = c2 := Hinj c1 c2 Hc1r Hc2r Heq.
        rewrite Hceq in Hk1. exact (Hkne (NoDup_lookup _ _ _ _ Hndrun Hk1 Hk2)). }
      apply (Hrangedisj c1 c2
               (proj1 (proj1 (client_run_mem types kc c1) Hc1r))
               (proj1 (proj1 (client_run_mem types kc c2) Hc2r)));
        [| exact Hlocne].
      rewrite (proj2 (proj1 (client_run_mem types kc c1) Hc1r))
              (proj2 (proj1 (client_run_mem types kc c2) Hc2r)) //. }
    wp_apply (wp_getNodeIndex_total slk dq types (client_run types kc) idv.(yjs.id.clock')
                (client_run_sorted types kc)
                (fun c Hc => proj1 (proj1 (client_run_mem types kc c) Hc))
                Hrunfits' Hidisj
                with "[$Hslice $Htypes]").
    iIntros (i ok) "(Hslice & Htypes & %Hires)".
    destruct ok.
    + (* hit: the probe covers the id *)
      destruct Hires as (cres & Hcres & Hcresle & Hcreslt).
      wp_auto.
      iDestruct (own_slice_len with "Hslice") as %[Hsllen Hsllen0].
      rewrite length_fmap in Hsllen Hsllen0.
      have Hilt : (uint.nat i < length (client_run types kc))%nat
        by (apply lookup_lt_Some in Hcres; lia).
      rewrite decide_True; last word.
      have Hlocres : (ic_loc <$> client_run types kc) !! uint.nat i = Some cres.(ic_loc)
        by rewrite list_lookup_fmap Hcres //.
      iDestruct (own_slice_elem_acc (sint.Z i) (ic_loc cres) slk dq (ic_loc <$> client_run types kc) with "Hslice") as "[Hel Hgive]".
      { word. }
      { replace (Z.to_nat (sint.Z i)) with (uint.nat i) by word. exact Hlocres. }
      wp_auto.
      iDestruct ("Hgive" $! cres.(ic_loc) with "Hel") as "Hslice".
      have Hinsid : (<[sint.nat i := cres.(ic_loc)]> (ic_loc <$> client_run types kc)) = (ic_loc <$> client_run types kc).
      { apply list_insert_id. replace (sint.nat i) with (uint.nat i) by word. exact Hlocres. }
      iEval (rewrite Hinsid) in "Hslice".
      have Hcresmem : cres ∈ all_cells types /\ cell_client cres = kc.
      { apply client_run_mem. exact (list_elem_of_lookup_2 _ _ _ Hcres). }
      iApply ("HΦ" $! (ic_loc cres) true).
      iFrame "Hitemsf".
      iDestruct ("Hrunsback" with "[$Hslice $Hcap]") as "Hruns".
      iSplitL "Hmap Hruns".
      { iExists gm. iFrame "Hmap Hruns". iPureIntro. split; [exact Hcomplete | exact Hclkloc]. }
      iFrame "Htypes".
      iPureIntro. exists cres.
      split_and!; [exact (proj1 Hcresmem) | exact (proj2 Hcresmem) | exact Hcresle | exact Hcreslt | done].
    + (* clock miss within a known client: no run of this client covers the id *)
      wp_auto.
      iApply ("HΦ" $! null false).
      iFrame "Hitemsf".
      iDestruct ("Hrunsback" with "[$Hslice $Hcap]") as "Hruns".
      iSplitL "Hmap Hruns".
      { iExists gm. iFrame "Hmap Hruns". iPureIntro. split; [exact Hcomplete | exact Hclkloc]. }
      iFrame "Htypes".
      iPureIntro. move=> c Hc Hcc Hcov1 Hcov2.
      have Hcrun : c ∈ client_run types kc by (apply client_run_mem; split; [exact Hc | exact Hcc]).
      apply list_elem_of_lookup_1 in Hcrun. destruct Hcrun as [kx Hkx].
      exact (Hires kx c Hkx Hcov1 Hcov2).
  - (* unknown client: no cell of this author at all *)
    wp_auto.
    iApply ("HΦ" $! null false).
    iFrame "Hitemsf".
    iSplitL "Hmap Hruns".
    { iExists gm. iFrame "Hmap Hruns". iPureIntro. split; [exact Hcomplete | exact Hclkloc]. }
    iFrame "Htypes".
    iPureIntro. move=> c Hc Hcc Hcov1 Hcov2.
    have Hkcin : kc ∈ (cell_client <$> all_cells types).
    { rewrite -Hcc. apply list_elem_of_fmap_2. exact Hc. }
    destruct (Hcomplete kc Hkcin) as [slk Hslk'].
    rewrite Hslk in Hslk'. discriminate.
Qed.

(** [store.hasNode] (issue #40 x issue #28 U7c): the arrival test the pending
    gate runs. Its result IS the model presence [doc_model_has m (toYjsId idv)]: the
    covering GetNode (W64 clock range) is bridged to the model per-char
    covering ([cell_covers], nat) through the cell id-bounds, then to
    [doc_model_has] through the store's model/cell agreement ([Hagree]). *)
Lemma wp_store__hasNode (s mref : loc) (dq : dfrac) (idv : yjs.id.t)
    (m : DocModel) (types : gmap loc type_state) :
  (∀ d : YjsId, doc_model_has m d = true <-> ∃ c, c ∈ all_cells types ∧ cell_covers c d) ->
  (∀ c, c ∈ all_cells types -> (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) < 2^64)%Z) ->
  NoDup (ic_loc <$> all_cells types) ->
  cells_range_disjoint (all_cells types) ->
  {{{ is_pkg_init yjs ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref dq types ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) }}}
    s @! (go.PointerType yjs.store) @! "hasNode" #idv
  {{{ (ok : bool), RET #ok;
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref dq types ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) ∗
      ⌜ok = true <-> doc_model_has m (toYjsId idv) = true⌝ }}}.
Proof using Type*.
  move=> Hagree Hrunfits Hnodup Hrangedisj.
  iIntros (Φ) "(#Hpkg & Hitemsf & Hitemmap & Htypes) HΦ".
  iDestruct (types_cells_id_bounds2 with "Htypes") as %Hcellbnd.
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
  wp_apply (wp_store__GetNode_total s mref dq idv types Hrunfits Hnodup Hrangedisj
              with "[$Hitemsf $Hitemmap $Htypes]").
  iIntros (l ok) "(Hitemsf & Hitemmap & Htypes & %Hres)".
  wp_auto.
  iApply ("HΦ" $! ok).
  iFrame "Hitemsf Hitemmap Htypes".
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
   [input_deps_*] live in [yjs_network_model] with the pending theory) *)

(** [store.originArrived] (issue #40): the per-origin arrival check; a nil
    origin imposes no dependency. Its result is the model presence of the
    origin id (via [hasNode]). *)
Lemma wp_store__originArrived (s mref : loc) (dq : dfrac) (p : loc)
    (originId : option yjs.id.t) (m : DocModel) (types : gmap loc type_state) :
  (∀ d : YjsId, doc_model_has m d = true <-> ∃ c, c ∈ all_cells types ∧ cell_covers c d) ->
  (∀ c, c ∈ all_cells types -> (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) < 2^64)%Z) ->
  NoDup (ic_loc <$> all_cells types) ->
  cells_range_disjoint (all_cells types) ->
  {{{ is_pkg_init yjs ∗ is_origin_id p originId ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref dq types ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) }}}
    s @! (go.PointerType yjs.store) @! "originArrived" #p
  {{{ (ok : bool), RET #ok;
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref dq types ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) ∗
      ⌜ok = true <-> match originId with
                     | None => True
                     | Some idv => doc_model_has m (toYjsId idv) = true
                     end⌝ }}}.
Proof using Type*.
  move=> Hagree Hrunfits Hnodup Hrangedisj.
  iIntros (Φ) "(#Hpkg & #HisP & Hitemsf & Hitemmap & Htypes) HΦ".
  wp_method_call. wp_call. wp_call. wp_auto.
  destruct originId as [idv |]; simpl.
  - (* a real origin: dereference and probe *)
    iDestruct "HisP" as "[%Hpne #Hpid]".
    rewrite bool_decide_eq_false_2; last first.
    { move=> Heq. exact (Hpne Heq). }
    wp_auto.
    wp_apply (wp_store__hasNode s mref dq idv m types Hagree Hrunfits Hnodup Hrangedisj
                with "[$Hitemsf $Hitemmap $Htypes]").
    iIntros (ok) "(Hitemsf & Hitemmap & Htypes & %Hok)".
    wp_auto.
    iApply ("HΦ" $! ok).
    iFrame "Hitemsf Hitemmap Htypes".
    iPureIntro. exact Hok.
  - (* nil origin: no dependency *)
    iDestruct "HisP" as %->.
    rewrite bool_decide_eq_true_2 //.
    wp_auto.
    iApply ("HΦ" $! true).
    iFrame "Hitemsf Hitemmap Htypes".
    iPureIntro. done.
Qed.

(** [store.depsArrived] (issue #40): the structural gate, as arrival checks.
    The return value IS the pure gate [input_ready] of the decoded struct; each
    arrival check ([originArrived] / [hasNode]) returns the model presence of a
    dependency, so the gate composes them by [input_ready_true_of] /
    [input_ready_false_of_dep]. *)
Lemma wp_store__depsArrived (s mref : loc) (dq : dfrac) (updateItemVal : yjs.updateItem.t)
    (typedInput : TId * IntegrateInput (A := A)) (m : DocModel) (types : gmap loc type_state) :
  (∀ d : YjsId, doc_model_has m d = true <-> ∃ c, c ∈ all_cells types ∧ cell_covers c d) ->
  (∀ c, c ∈ all_cells types -> (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) < 2^64)%Z) ->
  NoDup (ic_loc <$> all_cells types) ->
  cells_range_disjoint (all_cells types) ->
  {{{ is_pkg_init yjs ∗ is_update_item updateItemVal typedInput ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref dq types ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) }}}
    s @! (go.PointerType yjs.store) @! "depsArrived" #updateItemVal
  {{{ RET #(input_ready m typedInput.2);
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref dq types ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) }}}.
Proof using Type*.
  move=> Hagree Hrunfits Hnodup Hrangedisj.
  iIntros (Φ) "(#Hpkg & #Hui & Hitemsf & Hitemmap & Htypes) HΦ".
  iDestruct "Hui" as (oleft oright opn)
    "(HisL & HisR & HisPN & %Hin_l & %Hin_r & %Hin_id & %Hin_c & %Hunonempty & %Htid & %Hborrow)".
  have Hcid : clientId (in_id typedInput.2) = uint.nat updateItemVal.(yjs.updateItem.id').(yjs.id.clientId').
  { rewrite -Hin_id /toYjsId //. }
  have Hck : clock (in_id typedInput.2) = uint.nat updateItemVal.(yjs.updateItem.id').(yjs.id.clock').
  { rewrite -Hin_id /toYjsId //. }
  wp_method_call. wp_call. wp_call. wp_auto.
  (* ---- left origin ---- *)
  wp_apply (wp_store__originArrived s mref dq _ oleft m types Hagree Hrunfits Hnodup Hrangedisj
              with "[$HisL $Hitemsf $Hitemmap $Htypes]").
  iIntros (okL) "(Hitemsf & Hitemmap & Htypes & %HokL)".
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
    iApply ("HΦ" with "[$Hitemsf $Hitemmap $Htypes]"). }
  wp_auto.
  (* ---- right origin ---- *)
  wp_apply (wp_store__originArrived s mref dq _ oright m types Hagree Hrunfits Hnodup Hrangedisj
              with "[$HisR $Hitemsf $Hitemmap $Htypes]").
  iIntros (okR) "(Hitemsf & Hitemmap & Htypes & %HokR)".
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
    iApply ("HΦ" with "[$Hitemsf $Hitemmap $Htypes]"). }
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
    wp_apply (wp_store__hasNode s mref dq _ m types Hagree Hrunfits Hnodup Hrangedisj
                with "[$Hitemsf $Hitemmap $Htypes]").
    iIntros (okP) "(Hitemsf & Hitemmap & Htypes & %HokP)".
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
      iApply ("HΦ" with "[$Hitemsf $Hitemmap $Htypes]").
    + (* everything arrived *)
      wp_auto.
      have Hready : input_ready m typedInput.2 = true.
      { apply input_ready_true_of; [exact HLarr | exact HRarr |].
        move=> k' Hk'.
        have Hkk : k' = k by lia.
        rewrite Hkk Hkval.
        have HP := proj1 HokP eq_refl. rewrite Hpredid in HP. exact HP. }
      iEval (rewrite Hready) in "HΦ".
      iApply ("HΦ" with "[$Hitemsf $Hitemmap $Htypes]").
  - (* clock 0: no predecessor *)
    apply bool_decide_eq_false_1 in Hckpos.
    wp_auto.
    have Hready : input_ready m typedInput.2 = true.
    { apply input_ready_true_of; [exact HLarr | exact HRarr |].
      move=> k' Hk'. exfalso. rewrite Hck in Hk'. word. }
    iEval (rewrite Hready) in "HΦ".
    iApply ("HΦ" with "[$Hitemsf $Hitemmap $Htypes]").
Qed.

(* ----- the ready step: one decoded struct, repaired and integrated ----- *)

(** [store.integrateDecoded] (issue #40 x issue #28 U7c): the ready branch of
    the drain, as a per-struct contract -- the loop-free core of the batch
    loop. The struct's target root must be bound ([Hbnm]; the #49 pre-bound-
    roots restriction), its chained per-char op chunk realizes the run fold
    [Hall = integrate_all (ops_of_input ...)], its head-op scan facts hold at
    the current model, and the heap advances to the model spliced at [typedInput.1]
    with the four store-lock pool invariants maintained. Mirrors one iteration
    of main's whole-batch [wp_store__applyUpdate] body. *)
Lemma wp_store__integrateDecoded (s mref tref : loc)
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
  (∀ name p', bind !! name = Some p' -> is_Some (types !! p')) ->
  (∀ n1 n2 p', bind !! n1 = Some p' -> bind !! n2 = Some p' -> n1 = n2) ->
  (∀ name p' ts, bind !! name = Some p' -> types !! p' = Some ts ->
     doc_model_get m (RootId name) = ty_arr ts) ->
  (Z.of_nat (clock (in_id typedInput.2)) + Z.of_nat (length (in_content typedInput.2)) < 2^64)%Z ->
  NoDup (ic_loc <$> all_cells types) ->
  cells_range_disjoint (all_cells types) ->
  (∀ c, c ∈ all_cells types -> cell_fits c) ->
  (∀ c, c ∈ all_cells types -> cell_origin_clk c) ->
  {{{ is_pkg_init yjs ∗ is_update_item updateItemVal typedInput ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types ∗
      (s .[(yjs.store.t), "types"]) ↦ tref ∗ own_map tref (DfracOwn 1) bind ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) }}}
    s @! (go.PointerType yjs.store) @! "integrateDecoded" #updateItemVal
  {{{ (types' : gmap loc type_state), RET #();
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types' ∗
      (s .[(yjs.store.t), "types"]) ↦ tref ∗ own_map tref (DfracOwn 1) bind ∗
      ([∗ map] parent ↦ ts ∈ types',
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) ∗
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
      ⌜NoDup (ic_loc <$> all_cells types')⌝ ∗
      ⌜cells_range_disjoint (all_cells types')⌝ ∗
      ⌜∀ c, c ∈ all_cells types' -> cell_fits c⌝ ∗
      ⌜∀ c, c ∈ all_cells types' -> cell_origin_clk c⌝ }}}.
Proof using Type*.
  move=> Htieq Hbnm Htoit Hvld Hmax Hall Hgmax0 Hbindtypes Hbindinj Hmtypes
         Hnowrapc Hlocdup Hrangedisj Hfits Horiginclk.
  iIntros (Φ) "(#Hpkg & #Hui & Hitemsf & Hitemmap & Htypesf & Htypesmap & Htypes) HΦ".
  iDestruct "Hui" as (oleft oright opn)
    "(HisL & HisR & HisPN & %Hin_l & %Hin_r & %Hin_id & %Hin_c & %Hunonempty & %Htid & %Hborrow)".
  destruct typedInput as [typedInput2 input]. simpl in *. subst typedInput2.
  have Hts0 : is_Some (types !! p) := Hbindtypes nm p Hbnm.
  destruct Hts0 as [[cellsj arrj0] Htsj].
  have Hdgj : doc_model_get m (RootId nm) = arrj0 := Hmtypes nm p _ Hbnm Htsj.
  set (arrj := doc_model_get m (RootId nm)) in *.
  rewrite -Hdgj in Htsj.
  iDestruct (types_arr_inv2 with "Htypes") as %Harrinvs.
  have Hinvj : YjsArrInvariant arrj := Harrinvs p _ Htsj.
  destruct (integrate_some input arrj newItem Hinvj Htoit) as [arrinput Hintginput].
  destruct (integrate_finds input arrj arrinput Hintginput) as (leftIdx & rightIdx & HfindL & HfindR).
  iDestruct (types_entry_pures2 types p _ Htsj with "Htypes") as %(Hreprj & Hcparj).
  simpl in Hreprj, Hcparj.
  iDestruct (types_runs_wf2 with "Htypes") as %Hrunwfall.
  iDestruct (types_parents_all2 with "Htypes") as %Hparall.
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
  iDestruct (types_cells_id_bounds2 with "Htypes") as %Hbnds0.
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
  wp_apply (wp_store__repair_split s mref tref itv (updateItemVal.(yjs.updateItem.parentName'))
              input opn types bind ocL ocR p
              HwLc HwRc Hsameg Hwpar Hfits Hlocdup Hrangedisj Horiginclk
              with "[$Hfresh $HisPN $Hitemsf $Hitemmap $Htypesf $Htypesmap $Htypes]").
  iIntros (lft rgt types2) "(Hlinked & Hitemsf & Hitemmap & Htypesf & Htypesmap & Htypes & %Hpinv2 & %Hrtf & %HbdL & %HbdR)".
  destruct Hpinv2 as (Hfits2 & Hnodup2 & Hrangedisj2 & Horiginclk2).
  destruct Hrtf as (Hpres2 & Hdom2 & Hrl2 & Hunitpres2 & Hsub2).
  destruct (Hdom2 p (mk_is_Some _ _ Htsj)) as [ts2e Htsj2].
  destruct (Hpres2 p ts2e Htsj2) as (ts0e & Htsj0e & Harr2p & Hflat2p).
  have Hts0eq2 : ts0e = MkTypeState cellsj arrj by congruence.
  rewrite Hts0eq2 /= in Harr2p Hflat2p.
  destruct ts2e as [cellsj2 arrj2]. simpl in Harr2p, Hflat2p. subst arrj2.
  iDestruct (types_runs_wf2 with "Htypes") as %Hrunwfall2.
  iDestruct (types_parents_all2 with "Htypes") as %Hparall2.
  iDestruct (types_cells_id_bounds2 with "Htypes") as %Hbnds2.
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
  iDestruct (types_repr_all2 with "Htypes") as %Hreprallj.
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
  wp_apply (wp_Store__Integrate_nil_run s p itv arrj arr2 input newItem cellsj2 types2 mref leftIdx rightIdx
              curL2 curR2
              Hinvj Htoit Hvld Hmax HfindL HfindR Htsj2 Hgmaxj Hnecj2 Hfitscj Hoclkcj
              HcurL2 HcurL2b HcurR2 HcurR2b Hall
              with "[$Hyt $Hlinked $Hitemsf $Hitemmap]").
  iIntros (idx2 iidx2 cells'' c2)
    "(%Hinv2 & Htext2 & Hitemsf & Hitemmap & %Hperm2 & %Hsplice2 & %Hidx2b & %Hcoup2 & %Hile2 & %Harrsp2 & %Hc2look & %Hc2loc & %Hc2id & %Hc2del & %Hc2orig & %Hc2rorig & %Hc2len)".
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
  iAssert ([∗ map] p0 ↦ ts ∈ <[p := MkTypeState cells'' arr2]> types2,
      own_ytype_cells p0 (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
      ⌜YjsArrInvariant (ty_arr ts)⌝)%I
    with "[Htext2 Htypesrest]" as "Htypes".
  { rewrite -insert_delete_eq.
    rewrite big_sepM_insert; last apply lookup_delete_eq.
    iFrame "Htypesrest". simpl. iFrame "Htext2".
    iPureIntro. exact Hinv2. }
  wp_auto.
  iApply ("HΦ" $! (<[p := MkTypeState cells'' arr2]> types2)).
  iFrame "Hitemsf Hitemmap Htypesf Htypesmap Htypes".
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
  - exact Hlocdup'.
  - exact Hrangedisj'.
  - (* fits for the grown pool *)
    move=> c0 Hc0.
    rewrite Hac_step in Hc0. apply elem_of_app in Hc0 as [Hold | Hnew].
    + exact (Hfits2 c0 Hold).
    + apply list_elem_of_singleton in Hnew as ->.
      have Hlen2 : length (ic_run c2) = length (in_content input) by rewrite Hc2len explode_length.
      rewrite /cell_fits Hclk2 Hlen2.
      exact (uint_W64_nat_add_bound (clock (in_id input)) (length (in_content input)) Hnowrapc).
  - exact Horiginclk'.
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


(* ===== wire-level drain (issue #40 x issue #28 U7c) =======================
   The Go [applyUpdate] loop drains WIRE items (whole [updateItem] structs),
   integrating each ready one as ONE run cell -- a whole [expand_input] chunk of
   [integrate_all]. [wire_pass] / [wire_drain] mirror the per-char [pending_pass]
   / [pending_drain] ([yjs_network_model]) but step by [integrate_all] over a
   wire item's ops, so the drain loop refines them 1:1. The bridge to the
   per-char model (for the certificate [ValidReplay]) is
   [WireReplay_to_PendingReplay] in [yjs_store_update]: it turns a [WireReplay]
   into a [PendingReplay] of the [expand_inputs], re-deriving each chunk's
   freshness from head-freshness via [delivered_clock_bound]. Reuses
   [pending_keep] / [doc_model_has] / [input_ready] (a wire item's readiness is its
   head op's, since [typedInput.2]'s origins are the head's). *)

Definition wire_integrate (m : DocModel) (typedInput : TId * IntegrateInput (A := A))
    : option (list (YjsItem A)) :=
  integrate_all (ops_of_input typedInput.2 (explode (in_content typedInput.2))) (doc_model_get m typedInput.1).

Fixpoint wire_pass (m : DocModel) (pending kept : list (TId * IntegrateInput (A := A)))
    : list (TId * IntegrateInput (A := A)) * list (TId * IntegrateInput (A := A)) * DocModel :=
  match pending with
  | [] => ([], kept, m)
  | typedInput :: tl =>
      if doc_model_has m (in_id typedInput.2) then wire_pass m tl kept
      else if input_ready m typedInput.2 then
        match wire_integrate m typedInput with
        | Some arr' =>
            let '(app, kept', m') := wire_pass (<[typedInput.1 := arr']> m) tl kept in
            (typedInput :: app, kept', m')
        | None => wire_pass m tl (pending_keep kept typedInput)
        end
      else wire_pass m tl (pending_keep kept typedInput)
  end.

Fixpoint wire_drain_aux (fuel : nat) (m : DocModel)
    (pending : list (TId * IntegrateInput (A := A)))
    : list (TId * IntegrateInput (A := A)) * list (TId * IntegrateInput (A := A)) * DocModel :=
  match fuel with
  | 0%nat => ([], pending, m)
  | S f =>
      let '(app, kept, m') := wire_pass m pending [] in
      match app with
      | [] => ([], kept, m')
      | _ :: _ =>
          let '(app2, rest, m'') := wire_drain_aux f m' kept in
          (app ++ app2, rest, m'')
      end
  end.

Definition wire_drain (m : DocModel) (pending : list (TId * IntegrateInput (A := A)))
    : list (TId * IntegrateInput (A := A)) * list (TId * IntegrateInput (A := A)) * DocModel :=
  wire_drain_aux (S (length pending)) m pending.

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

(** The wire-level replay view of a drain: each applied wire item was fresh and
    ready and its whole op chunk integrated ([wire_integrate]). Mirrors
    [PendingReplay] with [integrate] replaced by [wire_integrate]. *)
Inductive WireReplay : DocModel -> list (TId * IntegrateInput (A := A)) -> DocModel -> Prop :=
  | WireReplay_nil m : WireReplay m [] m
  | WireReplay_cons m typedInput arr' rest m' :
      doc_model_has m (in_id typedInput.2) = false ->
      input_ready m typedInput.2 = true ->
      wire_integrate m typedInput = Some arr' ->
      WireReplay (<[typedInput.1 := arr']> m) rest m' ->
      WireReplay m (typedInput :: rest) m'.

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

(** [wire_ready_total]: along the wire drain, a fresh, ready pending wire item
    always integrates its whole chunk (the exclusion of the ready-but-stuck
    branch: the Go loop integrates on [depsArrived], so its applied set is the
    ready set, which coincides with [wire_pass]'s only when this holds). The
    certificate layer supplies it (a ready certified chunk always folds). *)
Definition wire_ready_total (m : DocModel)
    (pending applied : list (TId * IntegrateInput (A := A))) : Prop :=
  ∀ pre suf mx (typedInput : TId * IntegrateInput (A := A)),
    applied = pre ++ suf -> WireReplay m pre mx ->
    typedInput ∈ pending ->
    doc_model_has mx (in_id typedInput.2) = false ->
    input_ready mx typedInput.2 = true ->
    is_Some (wire_integrate mx typedInput).

End store_update.
