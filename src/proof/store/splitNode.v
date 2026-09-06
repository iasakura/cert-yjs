(** store update path, split layer at run granularity: the DLL half
    [wp_splitItem_runs] (over the type's [own_ytype_runs]), [store.splitNode]
    over the whole store ([wp_store__splitNode_runs], adding the per-client
    run-list insertion), and
    [wp_store__splitAtAndGetLeft_runs] / [wp_store__splitAtAndGetRight_runs]
    (proved from [wp_store__GetNode_runs] and [wp_store__splitNode_runs],
    stepping the pool and the address map by the index-explicit
    [pool_split_left_step] / [pool_split_right_step]).
    Split out of [store/GetNode] so it proof-checks in parallel; same
    [Section] boilerplate and [#[local]] instances. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core.
From New.proof Require Import prelude.
From New.proof Require Import algebra.
From New.proof.id Require Import id.
From New.proof.item Require Import item.
From New.proof.ytype Require Import ytype.
From New.proof.item Require Import run_theory model value heap.
From New.proof Require Import history.
From New.proof.store Require Import model value heap Integrate.
From iris.algebra Require Import auth gmap gset.
From stdpp Require Import sorting.
From New.proof.store Require Import GetNode.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

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

(** [store.getOrCreateYType], lookup-hit case: the name is already bound in
    the registry, so the creation branch is dead and the bound type comes
    back. This is the only case the verified update path needs — see
    [wp_store__applyUpdate]'s bound-names precondition (the on-the-fly type
    creation of y-octo's update path is outside the verified subset for now:
    it would grow [types]/[bind]/[m] with a fresh empty type mid-batch). *)


(** [splitItem n diff] at run granularity: the node at address [lc], the
    [k]-th run [r] of the type at [parent], is split at offset [diff] in
    the type's DLL: [lc] keeps the first [diff] chars, the fresh address
    [rloc] gets the rest ([split_locs] / [split_runs]), and [rloc] is new to
    the type. The DLL half of [store.splitNode] (y-octo: [Item::split_at]). *)
Lemma wp_splitItem_runs (parent lc : loc) (ls : list loc) (runs : list ItemRun)
    (arr : list (YjsItem A)) (k : nat) (r : ItemRun) (diff : w64) :
  ls !! k = Some lc ->
  runs !! k = Some r ->
  (0 < uint.nat diff < length (run_items r))%nat ->
  run_fits r ->
  {{{ is_pkg_init yjs ∗ own_ytype_runs parent (DfracOwn 1) ls (MkTypeModel runs) }}}
    @! yjs.splitItem #lc #diff
  {{{ (rloc : loc), RET #rloc;
      own_ytype_runs parent (DfracOwn 1) (split_locs ls k rloc)
        (MkTypeModel (split_runs runs k (uint.nat diff))) ∗
      ⌜rloc ≠ null ∧ rloc ∉ ls⌝ }}}.
Proof using Type*.
  move=> Hlk Hrk Hdiff Hfits.
  wp_start as "Htext". iNamed "Htext".
  iEval (cbn [tm_runs]) in "Hdll".
  iDestruct (own_dll_runs_length with "Hdll") as %Hlenl.
  pose proof (take_drop_middle ls k lc Hlk) as Hsl.
  pose proof (take_drop_middle runs k r Hrk) as Hsr.
  set (prel := take k ls) in Hsl.
  set (sufl := drop (S k) ls) in Hsl.
  set (prer := take k runs) in Hsr.
  set (sufr := drop (S k) runs) in Hsr.
  have Hlent : length prel = length prer by rewrite /prel /prer !length_take Hlenl.
  iEval (rewrite -Hsl -Hsr (own_dll_runs_app _ _ _ _ _ _ _ _ _ _ Hlent)) in "Hdll".
  iDestruct "Hdll" as (ml mf) "[Hseg1 Hseg2]".
  iDestruct (own_dll_runs_cons_unfold with "Hseg2") as (nxtcw) "(%Hhead & %Hpccw & %Hrun & Hnodecw & Hrest)".
  destruct Hhead as [Hmfeq Hmfnn]. subst mf.
  iDestruct "Hnodecw" as (itemVal olidcw oridcw)
    "(Hval & Holeft & Horight & %Hinlcw & %Hinrcw & %Hidn & %Hcontn & %Hpar & %Hprev & %Hnextcw & %Hflags)".
  have Hid : item_id (run_head_item r) = toYjsId itemVal.(yjs.item.id').
  { symmetry. exact Hidn. }
  have Hcontent : content <$> run_items r = explode (toContent itemVal.(yjs.item.content')).
  { have Hstr : toContent itemVal.(yjs.item.content') = items_string (run_items r) := Hcontn.
    rewrite Hstr. exact Hpccw. }
  have Holid : origin_id (origin (run_head_item r)) = toYjsId <$> olidcw.
  { symmetry. exact Hinlcw. }
  have Horid : origin_id (rightOrigin (run_head_item r)) = toYjsId <$> oridcw.
  { symmetry. exact Hinrcw. }
  iDestruct (typed_pointsto_not_null with "Hval") as %Hcwnn.
  wp_auto.
  (* olid := newId(client, clock+diff-1) *)
  wp_apply wp_NewId.
  (* cb := []byte(n.content.content) via the byte round-trip *)
  wp_apply wp_string_to_bytes. iIntros (cbs) "[Hcb Hcbcap]". wp_auto.
  (* the right node's id := newId(client, clock+diff) *)
  wp_apply wp_NewId.
  have Hsclen : length (itemVal.(yjs.item.content').(yjs.content.content')) = length (run_items r).
  { have H := f_equal length Hcontent. rewrite length_fmap explode_length /toContent in H. lia. }
  iDestruct (own_slice_len with "Hcb") as %Hcbwf.
  iDestruct (own_slice_wf with "Hcb") as %Hcapwf.
  destruct Hcbwf as [Hcbwf1 Hcbwf2].
  have Hdiffb : 0 ≤ sint.Z diff ≤ sint.Z cbs.(slice.len) by word.
  (* right.content := string(cb[diff:]) *)
  rewrite decide_True; last (split; [word | word]).
  have Hslbound : 0 ≤ sint.Z diff ≤ sint.Z cbs.(slice.len) ≤ sint.Z cbs.(slice.len) by word.
  iDestruct (own_slice_slice diff cbs.(slice.len) cbs (DfracOwn 1) _ Hslbound with "Hcb") as "(Hcb_lo & Hcb_mid & Hcb_hi)".
  wp_apply (wp_bytes_to_string with "Hcb_mid"). iIntros "Hcb_mid".
  wp_auto.
  wp_alloc rs as "Hrs". wp_auto.
  (* n.content := string(cb[:diff]) *)
  rewrite decide_True; last word.
  wp_apply (wp_bytes_to_string with "Hcb_lo"). iIntros "Hcb_lo".
  wp_auto.
  (* ===== branch-agnostic pure run-telescoping facts (the split's model core) *)
  iDestruct (typed_pointsto_not_null with "Hrs") as %Hrsnn.
  (* the fresh right node's address misses the whole type: the two opened
     segments by the DLL's freshness law, the split node by pointsto conflict *)
  iDestruct (own_dll_runs_fresh with "Hrs Hseg1") as %Hfr_pre.
  iDestruct (own_dll_runs_fresh with "Hrs Hrest") as %Hfr_suf.
  iAssert (⌜rs ≠ lc⌝)%I as %Hfr_cw.
  { destruct (decide (rs = lc)) as [Heqloc | Hneloc]; last by iPureIntro.
    subst rs.
    iDestruct (item_pointsto_conflict with "Hrs Hval") as %[]. }
  have Hrsfresh : rs ∉ ls.
  { rewrite -Hsl. move=> Hin. apply elem_of_app in Hin as [Hin | Hin]; [exact (Hfr_pre Hin) |].
    apply elem_of_cons in Hin as [Heq | Hin]; [exact (Hfr_cw Heq) | exact (Hfr_suf Hin)]. }
  set (o := uint.nat diff).
  have Hnowrapcw : (Z.of_nat (run_clock r) + Z.of_nat (length (run_items r)) < 2^64)%Z := Hfits.
  have Hckbnd : (Z.of_nat (clock (item_id (run_head_item r))) < 2^64)%Z
    by (rewrite Hid /toYjsId /=; word).
  have Hcwck : run_clock r = uint.nat itemVal.(yjs.item.id').(yjs.id.clock')
    by (rewrite /run_clock Hid /toYjsId /=).
  have Hsintlen : sint.nat cbs.(slice.len) = length (run_items r).
  { rewrite -Hsclen. symmetry. exact Hcbwf1. }
  have Hsintdiff : sint.nat diff = o.
  { rewrite /o. word. }
  have Hoinrun : (o < length (run_items r))%nat by (rewrite /o; lia).
  have Hole : (o <= length (run_items r))%nat by lia.
  have Hrun0 : run_items r !! 0%nat = Some (run_head_item r).
  { rewrite /run_head_item. destruct Hrun as [Hne _]. destruct (run_items r) as [|a r']; [done | reflexivity]. }
  destruct (run_items r !! o) as [yo|] eqn:Hyo; [| apply lookup_ge_None in Hyo; lia].
  have Hyoid := run_wf_lookup_clock (run_items r) o (run_head_item r) yo Hrun Hrun0 Hyo.
  have Hyoro := run_wf_lookup_rightOrigin (run_items r) o (run_head_item r) yo Hrun Hrun0 Hyo.
  iDestruct (typed_pointsto_not_null with "olid") as %Holidnn.
  iPersist "olid".
  have Hrhcl : run_head_item (split_run_left r o) = run_head_item r.
  { rewrite /run_head_item /split_run_left /=. apply hd_inhabitant_take. rewrite /o; lia. }
  have Hrhcr : run_head_item (split_run_right r o) = yo.
  { rewrite /run_head_item /split_run_right /=. exact (hd_inhabitant_drop _ o yo Hyo). }
  have Hcontl : content <$> take o (run_items r) = explode (take (sint.nat diff) itemVal.(yjs.item.content').(yjs.content.content')).
  { rewrite Hsintdiff fmap_take Hcontent /toContent /explode fmap_take //. }
  have Hsubdrop : subslice (sint.nat diff) (sint.nat cbs.(slice.len)) itemVal.(yjs.item.content').(yjs.content.content')
                = drop o itemVal.(yjs.item.content').(yjs.content.content').
  { rewrite Hsintdiff Hsintlen -Hsclen /subslice. rewrite take_ge; [reflexivity | lia]. }
  have Hcontr : content <$> drop o (run_items r) = explode (drop o itemVal.(yjs.item.content').(yjs.content.content')).
  { rewrite fmap_drop Hcontent /toContent /explode fmap_drop //. }
  (* ----- the two halves' facts (origin telescoping), branch-agnostic ----- *)
  set (leftRun := split_run_left r o).
  set (rightRun := split_run_right r o).
  set (originId := {| yjs.id.clientId' := itemVal.(yjs.item.id').(yjs.id.clientId');
                 yjs.id.clock' := word.sub (word.add itemVal.(yjs.item.id').(yjs.id.clock') diff) (W64 1) |}).
  have Hopos : (0 < o)%nat by (rewrite /o; lia).
  have Hnowrap_add : (uint.Z itemVal.(yjs.item.id').(yjs.id.clock') + uint.Z diff < 2^64)%Z.
  { have H1 := Hnowrapcw. rewrite Hcwck in H1. have H2 := Hdiff. word. }
  have Hadd_eq : (uint.nat itemVal.(yjs.item.id').(yjs.id.clock') + o)%nat = uint.nat (word.add itemVal.(yjs.item.id').(yjs.id.clock') diff).
  { rewrite /o. clear -Hnowrap_add. word. }
  have [xprev Hxprev] : is_Some (run_items r !! (o - 1)%nat).
  { apply lookup_lt_is_Some. rewrite /o. lia. }
  have Hyo2 : run_items r !! S (o - 1)%nat = Some yo.
  { replace (S (o - 1))%nat with o by (rewrite /o; lia). exact Hyo. }
  have Hstep := proj2 Hrun (o - 1)%nat xprev yo Hxprev Hyo2.
  have Horig : origin yo = itemPtr xprev by (destruct Hstep as [_ [Hh _]]; exact Hh).
  have Hxpid := run_wf_lookup_clock (run_items r) (o - 1)%nat (run_head_item r) xprev Hrun Hrun0 Hxprev.
  have Hcrorig : origin_id (origin (run_head_item rightRun)) = toYjsId <$> Some originId.
  { rewrite /rightRun Hrhcr Horig /origin_id /=. f_equal.
    rewrite Hxpid Hid /toYjsId /originId /=. f_equal. clear -Hnowrap_add Hdiff. word. }
  have Hrhck : clock (item_id (run_head_item r)) = uint.nat itemVal.(yjs.item.id').(yjs.id.clock') by (rewrite Hid /toYjsId /=).
  have Hrhcli : clientId (item_id (run_head_item r)) = uint.nat itemVal.(yjs.item.id').(yjs.id.clientId') by (rewrite Hid /toYjsId /=).
  set (ivl := itemVal <| yjs.item.content' := {| yjs.content.content' := take (sint.nat diff) itemVal.(yjs.item.content').(yjs.content.content') |} |> <| yjs.item.right' := rs |>).
  set (ivr := {| yjs.item.id' := {| yjs.id.clientId' := itemVal.(yjs.item.id').(yjs.id.clientId'); yjs.id.clock' := word.add itemVal.(yjs.item.id').(yjs.id.clock') diff |};
                 yjs.item.originLeftId' := olid_ptr;
                 yjs.item.originRightId' := itemVal.(yjs.item.originRightId');
                 yjs.item.left' := lc;
                 yjs.item.right' := itemVal.(yjs.item.right');
                 yjs.item.parent' := itemVal.(yjs.item.parent');
                 yjs.item.content' := {| yjs.content.content' := subslice (sint.nat diff) (sint.nat cbs.(slice.len)) itemVal.(yjs.item.content').(yjs.content.content') |};
                 yjs.item.flags' := itemVal.(yjs.item.flags') |}).
  have Hivl_ol : ivl.(yjs.item.originLeftId') = itemVal.(yjs.item.originLeftId') by (rewrite /ivl /=).
  have Hivl_or : ivl.(yjs.item.originRightId') = itemVal.(yjs.item.originRightId') by (rewrite /ivl /=).
  have Hivl_left : ivl.(yjs.item.left') = ml by (rewrite /ivl /=; exact Hprev).
  have Hivr_r : ivr.(yjs.item.right') = itemVal.(yjs.item.right') by reflexivity.
  have Hivr_ol : ivr.(yjs.item.originLeftId') = olid_ptr by (rewrite /ivr /=).
  have Hivr_or : ivr.(yjs.item.originRightId') = itemVal.(yjs.item.originRightId') by (rewrite /ivr /=).
  have Hp4 : ivl.(yjs.item.right') = rs by (rewrite /ivl /=).
  have Hp5 : ivl.(yjs.item.parent') = parent by (rewrite /ivl /=; exact Hpar).
  have Hp6 : item_id (run_head_item leftRun) = toYjsId ivl.(yjs.item.id'). { rewrite /leftRun Hrhcl /ivl /=. exact Hid. }
  have Hp7 : content <$> run_items leftRun = explode (toContent ivl.(yjs.item.content')). { rewrite /leftRun /ivl /toContent /=. exact Hcontl. }
  have Hp8 : origin_id (origin (run_head_item leftRun)) = toYjsId <$> olidcw. { rewrite /leftRun Hrhcl. exact Holid. }
  have Hp9 : origin_id (rightOrigin (run_head_item leftRun)) = toYjsId <$> oridcw. { rewrite /leftRun Hrhcl. exact Horid. }
  have Hp10 : ivl.(yjs.item.flags') = (if run_deleted leftRun then W8 6 else W8 2). { rewrite /ivl /leftRun /=. exact Hflags. }
  have Hp11 : run_wf (run_items leftRun). { rewrite /leftRun /=. exact (run_wf_take (run_items r) o Hopos Hrun). }
  have Hp12 : ivr.(yjs.item.left') = lc. { rewrite /ivr /=. reflexivity. }
  have Hp13 : ivr.(yjs.item.parent') = parent. { rewrite /ivr /=. exact Hpar. }
  have Hp14 : item_id (run_head_item rightRun) = toYjsId ivr.(yjs.item.id'). { rewrite /rightRun Hrhcr Hyoid /ivr /toYjsId /=. rewrite Hrhck Hrhcli Hadd_eq. reflexivity. }
  have Hp15 : content <$> run_items rightRun = explode (toContent ivr.(yjs.item.content')). { rewrite /rightRun /ivr /toContent /= Hsubdrop. exact Hcontr. }
  have Hp17 : origin_id (rightOrigin (run_head_item rightRun)) = toYjsId <$> oridcw. { rewrite /rightRun Hrhcr Hyoro. exact Horid. }
  have Hp18 : ivr.(yjs.item.flags') = (if run_deleted rightRun then W8 6 else W8 2). { rewrite /ivr /rightRun /=. exact Hflags. }
  have Hp19 : run_wf (run_items rightRun). { rewrite /rightRun /=. exact (run_wf_drop (run_items r) o Hoinrun Hrun). }
  have Hpcl : run_per_char leftRun := run_per_char_intro _ _ _ Hp7.
  have Hpcr : run_per_char rightRun := run_per_char_intro _ _ _ Hp15.
  iDestruct "Horight" as "#HorightP".
  (* [if n.right != nil] branches on whether [lc] is the type's last node *)
  destruct sufl as [|d0l sufl'] eqn:Hsufleq; destruct sufr as [|d0r sufr'] eqn:Hsufreq;
    [| iDestruct "Hrest" as %[] | iDestruct "Hrest" as %[] |].
  - (* lc is last: no downstream relink *)
    iDestruct "Hrest" as %[Hrnull0 Htl0eq].
    have Hrnull : itemVal.(yjs.item.right') = null by rewrite Hnextcw Hrnull0.
    rewrite (bool_decide_eq_true_2 (itemVal.(yjs.item.right') = null) Hrnull).
    wp_auto.
    have Hsl' : split_locs ls k rs = prel ++ [lc; rs] ++ [].
    { rewrite /split_locs Hlk -/prel -/sufl Hsufleq //. }
    have Hsr' : split_runs runs k o = prer ++ [leftRun; rightRun] ++ [].
    { rewrite /split_runs Hrk -/prer -/sufr Hsufreq //. }
    iApply ("HΦ" $! rs).
    iSplitL; last (iPureIntro; split; [exact Hrsnn | exact Hrsfresh]).
    iExists yt, rs. iFrame "Hparent".
    iSplitL.
    { iEval (cbn [tm_runs]). rewrite Hsl' Hsr'.
      iApply (own_dll_runs_split (DfracOwn 1) parent prel [] prer [] lc rs r o
                yt.(yjs.yType.start') rs ml null Hlent Hmfnn Hrsnn Hpcl Hpcr Hp11 Hp19).
      iSplitL "Hseg1"; first iFrame "Hseg1".
      iSplitL "Hval Holeft".
      { iExists ivl, olidcw, oridcw.
        rewrite Hivl_ol Hivl_or.
        iFrame "Hval Holeft HorightP".
        iPureIntro. split_and!.
        - exact (eq_sym Hp8).
        - exact (eq_sym Hp9).
        - exact (eq_sym Hp6).
        - symmetry. exact (items_string_explode _ _ Hp7).
        - exact Hp5.
        - exact Hivl_left.
        - exact Hp4.
        - exact Hp10. }
      iSplitL "Hrs".
      { iExists ivr, (Some originId), oridcw.
        rewrite Hivr_ol Hivr_or.
        iFrame "Hrs HorightP".
        iSplitR; first (simpl; iFrame "olid"; iPureIntro; exact Holidnn).
        iPureIntro. split_and!.
        - exact (eq_sym Hcrorig).
        - exact (eq_sym Hp17).
        - exact (eq_sym Hp14).
        - symmetry. exact (items_string_explode _ _ Hp15).
        - exact Hp13.
        - exact Hp12.
        - rewrite Hivr_r. exact Hrnull.
        - exact Hp18. }
      iEval (simpl). iPureIntro. split; reflexivity. }
    iPureIntro. simpl. rewrite (split_runs_visible runs k o r Hrk Hole). exact Hlen.
  - (* lc has a right neighbour d0: relink d0.left := right first *)
    iDestruct (own_dll_runs_cons_unfold with "Hrest") as (nxtd) "(%Hlocd & %Hpcd0 & %Hrund & Hnoded & Hrestd)".
    destruct Hlocd as [Hlocd1n Hlocdnn].
    iDestruct "Hnoded" as (ivd olidd oridd)
      "(Hvald & Holeftd & Horightd & %Hinld & %Hinrd & %Hiddn & %Hcontdn & %Hpard & %Hprevd & %Hnextd & %Hflagsd)".
    have Hlocd1 : itemVal.(yjs.item.right') = d0l by rewrite Hnextcw Hlocd1n.
    have Hrnnd : itemVal.(yjs.item.right') ≠ null by rewrite Hlocd1.
    rewrite (bool_decide_eq_false_2 (itemVal.(yjs.item.right') = null) Hrnnd).
    iEval (rewrite -Hlocd1) in "Hvald".
    wp_auto.
    iEval (rewrite Hlocd1) in "Hvald".
    set (ivd2 := ivd <| yjs.item.left' := rs |>).
    have Hd2l : ivd2.(yjs.item.left') = rs by reflexivity.
    have Hd2r : ivd2.(yjs.item.right') = ivd.(yjs.item.right') by reflexivity.
    have Hd2p : ivd2.(yjs.item.parent') = ivd.(yjs.item.parent') by reflexivity.
    have Hd2id : ivd2.(yjs.item.id') = ivd.(yjs.item.id') by reflexivity.
    have Hd2c : ivd2.(yjs.item.content') = ivd.(yjs.item.content') by reflexivity.
    have Hd2ol : ivd2.(yjs.item.originLeftId') = ivd.(yjs.item.originLeftId') by reflexivity.
    have Hd2or : ivd2.(yjs.item.originRightId') = ivd.(yjs.item.originRightId') by reflexivity.
    have Hd2f : ivd2.(yjs.item.flags') = ivd.(yjs.item.flags') by reflexivity.
    iAssert (own_dll_runs (DfracOwn 1) parent itemVal.(yjs.item.right') tl rs null (d0l :: sufl') (d0r :: sufr'))
      with "[Hvald Holeftd Horightd Hrestd]" as "Hsufdll".
    { rewrite Hlocd1.
      iApply (own_dll_runs_cons_fold (DfracOwn 1) parent tl rs null nxtd d0l sufl' d0r sufr' Hlocdnn Hrund Hpcd0).
      iSplitL "Hvald Holeftd Horightd".
      { iExists ivd2, olidd, oridd.
        rewrite Hd2ol Hd2or.
        iFrame "Hvald Holeftd Horightd".
        iPureIntro. split_and!.
        - exact Hinld.
        - exact Hinrd.
        - rewrite Hd2id. exact Hiddn.
        - rewrite Hd2c. exact Hcontdn.
        - rewrite Hd2p. exact Hpard.
        - exact Hd2l.
        - rewrite Hd2r. exact Hnextd.
        - rewrite Hd2f. exact Hflagsd. }
      iFrame "Hrestd". }
    have Hsl' : split_locs ls k rs = prel ++ [lc; rs] ++ d0l :: sufl'.
    { rewrite /split_locs Hlk -/prel -/sufl Hsufleq //. }
    have Hsr' : split_runs runs k o = prer ++ [leftRun; rightRun] ++ d0r :: sufr'.
    { rewrite /split_runs Hrk -/prer -/sufr Hsufreq //. }
    iApply ("HΦ" $! rs).
    iSplitL; last (iPureIntro; split; [exact Hrsnn | exact Hrsfresh]).
    iExists yt, tl. iFrame "Hparent".
    iSplitL.
    { iEval (cbn [tm_runs]). rewrite Hsl' Hsr'.
      iApply (own_dll_runs_split (DfracOwn 1) parent prel (d0l :: sufl') prer (d0r :: sufr') lc rs r o
                yt.(yjs.yType.start') tl ml itemVal.(yjs.item.right') Hlent Hmfnn Hrsnn Hpcl Hpcr Hp11 Hp19).
      iSplitL "Hseg1"; first iFrame "Hseg1".
      iSplitL "Hval Holeft".
      { iExists ivl, olidcw, oridcw.
        rewrite Hivl_ol Hivl_or.
        iFrame "Hval Holeft HorightP".
        iPureIntro. split_and!.
        - exact (eq_sym Hp8).
        - exact (eq_sym Hp9).
        - exact (eq_sym Hp6).
        - symmetry. exact (items_string_explode _ _ Hp7).
        - exact Hp5.
        - exact Hivl_left.
        - exact Hp4.
        - exact Hp10. }
      iSplitL "Hrs".
      { iExists ivr, (Some originId), oridcw.
        rewrite Hivr_ol Hivr_or.
        iFrame "Hrs HorightP".
        iSplitR; first (simpl; iFrame "olid"; iPureIntro; exact Holidnn).
        iPureIntro. split_and!.
        - exact (eq_sym Hcrorig).
        - exact (eq_sym Hp17).
        - exact (eq_sym Hp14).
        - symmetry. exact (items_string_explode _ _ Hp15).
        - exact Hp13.
        - exact Hp12.
        - exact Hivr_r.
        - exact Hp18. }
      iExact "Hsufdll". }
    iPureIntro. simpl. rewrite (split_runs_visible runs k o r Hrk Hole). exact Hlen.
Qed.

(** [store.splitNode] at run granularity (plan-item-run-split stage 2):
    split the [k]-th run of the type at [parent] at offset [diff]; the pool
    gets the two halves ([split_runs]) and the address list the fresh right
    half's address after [k] ([split_locs]), the fresh address new to the
    WHOLE address map. The DLL half is [wp_splitItem_runs]; the per-client
    address slice ([own_item_map_runs]) gets the right half's address
    inserted after the split node's, the pool and address-map laws being
    [run_pool_invs_split] / [locs_wf_split] / [pool_entries_split]. *)
Lemma wp_store__splitNode_runs (s : loc) (state : store_state_runs)
    (parent l : loc) (ls : list loc) (tm : type_model) (k : nat) (r : ItemRun) (diff : w64) :
  sr_pool state !! parent = Some tm ->
  sr_locs state !! parent = Some ls ->
  tm_runs tm !! k = Some r ->
  ls !! k = Some l ->
  (0 < uint.nat diff < length (run_items r))%nat ->
  {{{ is_pkg_init yjs ∗ own_store_runs s state }}}
    s @! (go.PointerType yjs.store) @! "splitNode" #l #diff
  {{{ (rloc : loc), RET (#l, #rloc);
      own_store_runs s
        (state <| sr_pool := <[parent := MkTypeModel (split_runs (tm_runs tm) k (uint.nat diff))]> (sr_pool state) |>
             <| sr_locs := <[parent := split_locs ls k rloc]> (sr_locs state) |>) ∗
      ⌜rloc ≠ null ∧ rloc ∉ concat ((map_to_list (sr_locs state)).*2)⌝ }}}.
Proof using Type*.
  move=> Hp Hl Hr Hlk Hdiff.
  destruct state as [client0 k0 locs p bind pend pdel]. simpl in *.
  iIntros (Φ) "(#Hpkg & Hruns) HΦ".
  iDestruct "Hruns" as "(Hfields & %Hinvs)".
  have Hrpi : run_pool_invs p := proj1 Hinvs.
  have Hreg : pool_registry_coh bind p := proj2 Hinvs.
  have [Hinvall Hdisj] := Hrpi.
  have Hfits : ∀ r0, r0 ∈ all_runs p -> run_fits r0
    := λ r0 Hr0, proj1 (proj2 (Hinvall r0 Hr0)).
  have Hoc : ∀ r0, r0 ∈ all_runs p -> run_origin_clk r0
    := λ r0 Hr0, proj2 (proj2 (proj2 (Hinvall r0 Hr0))).
  iDestruct "Hfields" as "(Hclient & Hclock & HdeletedSet & Hitems & Hregistry & Htypes & Hpending & Hpdeletes)".
  iEval (simpl) in "Hitems Htypes".
  iDestruct (own_type_pool_runs_id_bounds with "Htypes") as %Hbnds.
  iDestruct (own_type_pool_runs_run_wf with "Htypes") as %Hwfall.
  iDestruct "Htypes" as "(%Hlocswf & Hpool)".
  have Hlocswf0 := Hlocswf. destruct Hlocswf as (Hdom & Hnd & Hlens).
  have Hlens' : ∀ parent' tm', p !! parent' = Some tm' ->
      ∃ ls', locs !! parent' = Some ls' ∧ length ls' = length (tm_runs tm').
  { move=> parent' tm' Hp'.
    have His : is_Some (locs !! parent').
    { apply elem_of_dom. rewrite Hdom. apply elem_of_dom. by exists tm'. }
    destruct His as [ls' Hls']. exists ls'. split; [done | exact (Hlens parent' ls' tm' Hls' Hp')]. }
  have Hlsl : length ls = length (tm_runs tm) := Hlens parent ls tm Hl Hp.
  have Hrmem : r ∈ all_runs p.
  { apply elem_of_all_runs. exists parent, tm. split; [exact Hp | exact (list_elem_of_lookup_2 _ _ _ Hr)]. }
  have Hfitsr : run_fits r := Hfits r Hrmem.
  have Hwfr : run_wf (run_items r) := Hwfall r Hrmem.
  have Hclb : (Z.of_nat (run_client r) < 2^64)%Z := proj1 (Hbnds r Hrmem).
  have Hckb : (Z.of_nat (run_clock r) < 2^64)%Z := proj2 (Hbnds r Hrmem).
  have Hob : (0 < uint.nat diff < length (run_items r))%nat := Hdiff.
  have Hopos : (0 < uint.nat diff)%nat by lia.
  have Hoinrun : (uint.nat diff < length (run_items r))%nat by lia.
  have Hfitsr' : (Z.of_nat (run_clock r) + Z.of_nat (length (run_items r)) < 2^64)%Z := Hfitsr.
  destruct (split_run_facts r (uint.nat diff) Hwfr Hob)
    as (Hheadl & Hlenl & Hlenr & Hclientl & Hclientr & Hclockl & Hclockr).
  (* this type's run view; the split node's struct (its id keys the item-map
     surgery) *)
  iDestruct (big_sepM_delete _ _ parent _ Hp with "Hpool") as "[Hpc Hrest]".
  iDestruct "Hpc" as (ls0) "(%Hls0 & Hyt & %Harrinv)". rewrite Hl in Hls0. injection Hls0 as <-.
  iDestruct "Hyt" as (yt0 tl0) "(Hparent0 & Hdll0 & %Hlen0)".
  iDestruct (own_dll_runs_acc (DfracOwn 1) parent _ tl0 ls (tm_runs tm) k l r Hlk Hr with "Hdll0")
    as (prev0 nxt0) "(%Hcl0 & %Hcr0 & %Hrun0 & %Hpc0 & %Hclen0 & Hnode0 & Hback0)".
  iDestruct "Hnode0" as (itemVal olid0 orid0)
    "(Hval0 & Hol0 & Hor0 & %Hinl0 & %Hinr0 & %Hidn0 & %Hcont0 & %Hpar0 & %Hprev0 & %Hnext0 & %Hflags0)".
  have Hid : item_id (run_head_item r) = toYjsId itemVal.(yjs.item.id') by (symmetry; exact Hidn0).
  iAssert (own_item_node l (DfracOwn 1) (input_of_run r) (run_deleted r) parent prev0 nxt0)
    with "[Hval0 Hol0 Hor0]" as "Hnode0".
  { iExists itemVal, olid0, orid0. iFrame "Hval0 Hol0 Hor0". iPureIntro.
    split_and!; [exact Hinl0 | exact Hinr0 | exact Hidn0 | exact Hcont0 | exact Hpar0
                | exact Hprev0 | exact Hnext0 | exact Hflags0]. }
  iDestruct ("Hback0" with "Hnode0") as "Hdll0".
  iAssert (own_ytype_runs parent (DfracOwn 1) ls (MkTypeModel (tm_runs tm)))
    with "[Hparent0 Hdll0]" as "Hyt".
  { iExists yt0, tl0. iFrame "Hparent0 Hdll0". iPureIntro. exact Hlen0. }
  wp_method_call. wp_call. wp_call. wp_auto.
  (* the DLL half *)
  wp_apply (wp_splitItem_runs parent l ls (tm_runs tm) (tm_arr tm) k r diff Hlk Hr Hdiff Hfitsr
              with "[$Hpkg $Hyt]").
  iIntros (rs) "(Hyt2 & %Hrsnn & %Hrsls)".
  (* the fresh address misses the other types too: borrow its node against
     the rest of the pool *)
  have Hlk' : split_locs ls k rs !! S k = Some rs := split_locs_lookup_right ls k rs l Hlk.
  have Hrk' : split_runs (tm_runs tm) k (uint.nat diff) !! S k = Some (split_run_right r (uint.nat diff))
    := split_runs_lookup_right _ _ _ _ Hr.
  iDestruct "Hyt2" as (yt2 tl2) "(Hparent2 & Hdll2 & %Hlen2)".
  iEval (cbn [tm_runs]) in "Hdll2".
  iDestruct (own_dll_runs_lookup_acc _ _ _ _ _ _ _ _ _ _ _ Hlk' Hrk' with "Hdll2") as (pr nr) "(Hnoder & Hbackr)".
  iDestruct "Hnoder" as (ivr olr orr) "(Hrsval & Hrsol & Hrsor & %Hf1 & %Hf2 & %Hf3 & %Hf4 & %Hf5 & %Hf6 & %Hf7 & %Hf8)".
  iDestruct (own_type_pool_runs_fresh rs ivr (DfracOwn 1) locs (delete parent p) with "Hrsval Hrest") as %Hfr_rest.
  iAssert (own_item_node rs (DfracOwn 1) (input_of_run (split_run_right r (uint.nat diff)))
             (run_deleted (split_run_right r (uint.nat diff))) parent pr nr)
    with "[Hrsval Hrsol Hrsor]" as "Hnoder".
  { iExists ivr, olr, orr. iFrame "Hrsval Hrsol Hrsor". iPureIntro.
    split_and!; [exact Hf1 | exact Hf2 | exact Hf3 | exact Hf4 | exact Hf5 | exact Hf6 | exact Hf7 | exact Hf8]. }
  iDestruct ("Hbackr" with "Hnoder") as "Hdll2".
  have Hrsfresh : rs ∉ concat ((map_to_list locs).*2).
  { move=> Hin. apply list_elem_of_concat in Hin as (lsq & Hin & Hlsq).
    apply list_elem_of_fmap in Hlsq as ([q lsq'] & -> & Hq). simpl in Hin.
    apply elem_of_map_to_list in Hq.
    destruct (decide (q = parent)) as [-> | Hne].
    - rewrite Hl in Hq. injection Hq as <-. exact (Hrsls Hin).
    - have Hqp : is_Some (p !! q).
      { apply elem_of_dom. rewrite -Hdom. apply elem_of_dom. by exists lsq'. }
      destruct Hqp as [tmq Htmq].
      have Hdq : delete parent p !! q = Some tmq by (rewrite lookup_delete_ne; [exact Htmq | congruence]).
      exact (Hfr_rest q lsq' tmq Hq Hdq Hin). }
  destruct (pool_entries_split locs p parent ls tm k l r (uint.nat diff) rs Hl Hp Hlk Hr Hlsl)
    as (rest & Hperm1 & Hperm2).
  set (o := uint.nat diff) in *.
  set (ls2 := split_locs ls k rs) in *.
  set (runs2 := split_runs (tm_runs tm) k o) in *.
  set (tm2 := MkTypeModel runs2) in *.
  set (locs2 := <[parent := ls2]> locs) in *.
  set (p2 := <[parent := tm2]> p) in *.
  set (leftRun := split_run_left r o) in *.
  set (rightRun := split_run_right r o) in *.
  (* the pool at (locs2, p2) *)
  iAssert (own_ytype_runs parent (DfracOwn 1) ls2 tm2) with "[Hparent2 Hdll2]" as "Hyt2".
  { iExists yt2, tl2. iFrame "Hparent2 Hdll2". iPureIntro. exact Hlen2. }
  have Hlocswf2 : locs_wf locs2 p2 := locs_wf_split locs p parent ls tm k l r o rs Hl Hp Hlk Hr Hrsfresh Hlocswf0.
  have Hrpi2 : run_pool_invs p2 := run_pool_invs_split p parent tm k o r Hp Hr Hwfr Hob Hrpi.
  have Hreg2 : pool_registry_coh bind p2 := pool_registry_coh_insert_existing bind p parent tm tm2 Hp Hreg.
  have Hp2 : p2 !! parent = Some tm2 by apply lookup_insert_eq.
  have Hl2 : locs2 !! parent = Some ls2 by apply lookup_insert_eq.
  have Hlk2 : ls2 !! k = Some l := split_locs_lookup_left ls k rs l Hlk.
  have Hrk2 : runs2 !! k = Some leftRun := split_runs_lookup_left _ _ _ _ Hr.
  have Harrinv2 : YjsArrInvariant (tm_arr tm2).
  { rewrite /tm2 /tm_arr /= /runs2 (split_runs_flatten (tm_runs tm) k o r Hr). exact Harrinv. }
  iAssert (own_type_pool_runs (DfracOwn 1) locs2 p2)%I with "[Hyt2 Hrest]" as "Htypes2".
  { iSplitR; first (iPureIntro; exact Hlocswf2).
    rewrite /p2 big_sepM_insert_delete.
    iSplitL "Hyt2".
    { iExists ls2. iFrame "Hyt2". iPureIntro. split; [exact Hl2 | exact Harrinv2]. }
    iApply (big_sepM_impl with "Hrest"). iIntros "!>" (q tmq Hq) "H".
    iDestruct "H" as (lsq) "(%Hlsq & Hyt & %Hinv)". iExists lsq. iFrame "Hyt".
    iPureIntro. split; [| exact Hinv].
    apply lookup_delete_Some in Hq as [Hne _]. rewrite /locs2 lookup_insert_ne //. }
  have Hlocswf2' := Hlocswf2. destruct Hlocswf2' as (Hdom2 & Hnd2 & Hlens2).
  have Hlens2' : ∀ parent' tm', p2 !! parent' = Some tm' ->
      ∃ ls', locs2 !! parent' = Some ls' ∧ length ls' = length (tm_runs tm').
  { move=> parent' tm' Hp'.
    have His : is_Some (locs2 !! parent').
    { apply elem_of_dom. rewrite Hdom2. apply elem_of_dom. by exists tm'. }
    destruct His as [ls' Hls']. exists ls'. split; [done | exact (Hlens2 parent' ls' tm' Hls' Hp')]. }
  (* ----- the item-map surgery ----- *)
  iDestruct "Hitems" as (mref) "(Hitemsf & Hitemmap)".
  iDestruct "Hitemmap" as (gm) "(Hmap & Hruns & %Hcomplete & %Hclockunique)".
  set (kc := itemVal.(yjs.item.id').(yjs.id.clientId')) in *.
  have Hecl : entry_client (l, r) = kc.
  { rewrite /entry_client /= /run_client Hid /toYjsId /=. rewrite /kc. word. }
  have Hlr_mem : (l, r) ∈ pool_entries locs p by (rewrite Hperm1; apply list_elem_of_here).
  set (E := client_entries locs p kc) in *.
  set (key_pairs := entry_key_pair <$> pool_entries locs p) in *.
  set (key_pairs2 := entry_key_pair <$> pool_entries locs2 p2) in *.
  have Hce : client_locs locs p kc = E.*1 := client_locs_entries locs p kc Hclockunique.
  have Hprs : merge_sort clock_loc_le ((filter (λ key_pair0 : w64 * (Z * loc), key_pair0.1 = kc) key_pairs).*2) = entry_clock_loc <$> E
    := client_entries_clock_locs locs p kc Hclockunique.
  have Hndl : NoDup (pool_entries locs p).*1 := pool_entries_locs_NoDup locs p Hdom Hlens' Hnd.
  have HE : sorted_client_entries locs p kc E := client_entries_sorted_client locs p kc Hndl.
  have HndE : NoDup E.*1 := proj1 (proj2 HE).
  have HsortE : StronglySorted entry_le E := proj1 HE.
  have HidisjE := sorted_client_entries_disjoint locs p kc E Hdom Hlens' Hndl
                    (λ r' Hr', proj1 (Hbnds r' Hr')) Hdisj HE.
  have HEmem : ∀ e, e ∈ E -> e.2 ∈ all_runs p.
  { move=> [le re] He. apply client_entries_mem in He as [Hpe _].
    apply pool_entries_slot in Hpe as (parent' & ls' & tm' & k' & _ & Hp' & _ & Hr').
    apply elem_of_all_runs. exists parent', tm'. split; [exact Hp' | exact (list_elem_of_lookup_2 _ _ _ Hr')]. }
  have Hlr_E : (l, r) ∈ E by (apply client_entries_mem; split; [exact Hlr_mem | exact Hecl]).
  apply list_elem_of_lookup in Hlr_E as [kw Hkw].
  have Hkwlt : (kw < length E)%nat := lookup_lt_Some _ _ _ Hkw.
  have Hkcin : kc ∈ key_pairs.*1.
  { rewrite -Hecl. apply list_elem_of_fmap. exists (entry_key_pair (l, r)).
    split; [reflexivity | apply list_elem_of_fmap_2; exact Hlr_mem]. }
  destruct (Hcomplete kc Hkcin) as [slk Hslk].
  iDestruct (big_sepM_lookup_acc _ _ kc slk Hslk with "Hruns") as "[Hrunslk Hrunsback]".
  iNamed "Hrunslk".
  iEval (rewrite -/(client_locs locs p kc) Hce) in "Hslice".
  (* the key read: the truncated left half keeps the run's head id *)
  iDestruct (own_type_pool_runs_node_acc locs2 p2 parent ls2 tm2 k l leftRun Hl2 Hp2 Hlk2 Hrk2 with "Htypes2")
    as (iv2) "Hacc2". iNamed "Hacc2".
  have Hid2 : toYjsId iv2.(yjs.item.id') = toYjsId itemVal.(yjs.item.id').
  { rewrite -Haccid /leftRun Hheadl Hid //. }
  have Hkey : iv2.(yjs.item.id').(yjs.id.clientId') = kc.
  { have Hc1 := f_equal clientId Hid2. simpl in Hc1. rewrite /kc. clear -Hc1. word. }
  have Hkeyck : iv2.(yjs.item.id').(yjs.id.clock') = itemVal.(yjs.item.id').(yjs.id.clock').
  { have Hc1 := f_equal clock Hid2. simpl in Hc1. clear -Hc1. word. }
  wp_auto.
  wp_apply (wp_map_lookup1 with "Hmap"). iIntros "Hmap".
  rewrite Hkey Hslk /=.
  wp_auto.
  rewrite Hkeyck.
  iDestruct ("Haccback" with "Haccval") as "Htypes2".
  (* getNodeIndex over the split run: the index's entries with the split run
     truncated *)
  set (E' := <[kw := (l, leftRun)]> E) in *.
  have HE'fst : E'.*1 = E.*1.
  { rewrite /E' list_fmap_insert /=. apply list_insert_id. rewrite list_lookup_fmap Hkw //. }
  have Hkw' : E' !! kw = Some (l, leftRun) by (rewrite /E' list_lookup_insert_eq //).
  have Hss_replace : ∀ (ll : list (loc * ItemRun)) (i : nat) (a b : loc * ItemRun),
      StronglySorted entry_le ll → ll !! i = Some a → entry_clock b = entry_clock a →
      StronglySorted entry_le (<[i:=b]> ll).
  { elim => [| c ll IH] i a b Hss Hi Hclk.
    - by rewrite /=.
    - apply StronglySorted_inv in Hss as [Hssll Hfa].
      destruct i as [|i']; simpl.
      + simpl in Hi. injection Hi as Hca. rewrite Hca in Hfa.
        apply SSorted_cons; [exact Hssll |].
        apply Forall_forall => x Hx. rewrite /entry_le Hclk.
        exact (proj1 (Forall_forall _ _) Hfa x Hx).
      + apply SSorted_cons; [exact (IH i' a b Hssll Hi Hclk) |].
        apply Forall_insert; [exact Hfa |].
        rewrite /entry_le Hclk.
        exact (proj1 (Forall_forall _ _) Hfa a (list_elem_of_lookup_2 ll i' a Hi)). }
  have Hclkl : entry_clock (l, leftRun) = entry_clock (l, r).
  { rewrite /entry_clock /= /leftRun Hclockl //. }
  have HE'mem : ∀ e, e ∈ E' -> e ∈ pool_entries locs2 p2 ∧ entry_client e = kc.
  { move=> e He. apply list_elem_of_lookup_1 in He as [j Hj]. rewrite /E' in Hj.
    apply list_lookup_insert_Some in Hj as [(_ & <- & _) | (Hne & Hj)].
    - split; [rewrite Hperm2; apply list_elem_of_here |].
      rewrite /entry_client /= /leftRun Hclientl. exact Hecl.
    - have HeE : e ∈ E := list_elem_of_lookup_2 _ _ _ Hj.
      apply client_entries_mem in HeE as [Hpe Hcl]. split; [| exact Hcl].
      rewrite Hperm1 in Hpe. apply elem_of_cons in Hpe as [-> | Hpe].
      + exfalso. apply Hne. apply (NoDup_lookup _ kw j l HndE);
          rewrite list_lookup_fmap; [rewrite Hkw // | rewrite Hj //].
      + rewrite Hperm2. apply elem_of_cons; right. apply elem_of_cons; right. exact Hpe. }
  have HE' : sorted_client_entries locs2 p2 kc E'.
  { split_and!; [exact (Hss_replace E kw (l, r) (l, leftRun) HsortE Hkw Hclkl)
                | rewrite HE'fst; exact HndE | exact HE'mem]. }
  iEval (rewrite -HE'fst) in "Hslice".
  wp_apply (wp_getNodeIndex_runs slk (DfracOwn 1) locs2 p2 kc itemVal.(yjs.item.id').(yjs.id.clock') E' Hrpi2 HE'
              with "[$Hslice $Htypes2]").
  iIntros (idx ok) "(Hslice & Htypes2 & %Hires)".
  (* the covering entry is the left half, at [kw] *)
  have Hclkr : uint.nat itemVal.(yjs.item.id').(yjs.id.clock') = run_clock r.
  { rewrite /run_clock Hid /toYjsId //. }
  have Hlcov : run_covers_clock leftRun (uint.nat itemVal.(yjs.item.id').(yjs.id.clock')).
  { rewrite /run_covers_clock Hclkr /leftRun Hclockl Hlenl. lia. }
  destruct ok; last first.
  { exfalso. exact (Hires l leftRun (list_elem_of_lookup_2 _ _ _ Hkw') Hlcov). }
  destruct Hires as (lres & rres & Hres & Hcov).
  iDestruct (own_type_pool_runs_id_bounds with "Htypes2") as %Hbnds2.
  have Hndl2 : NoDup (pool_entries locs2 p2).*1 := pool_entries_locs_NoDup locs2 p2 Hdom2 Hlens2' Hnd2.
  have Hidisj2 := sorted_client_entries_disjoint locs2 p2 kc E' Hdom2 Hlens2' Hndl2
                    (λ r' Hr', proj1 (Hbnds2 r' Hr'))
                    (proj2 Hrpi2) HE'.
  have Hidxkw : uint.nat idx = kw.
  { destruct (decide (uint.nat idx = kw)) as [? | Hne]; [done | exfalso].
    destruct (Hidisj2 (uint.nat idx) kw lres l rres leftRun Hres Hkw' Hne) as [Hd | Hd];
      destruct Hcov as [Hc1 Hc2]; destruct Hlcov as [Hlc1 Hlc2]; lia. }
  have Hcresl : lres = l ∧ rres = leftRun.
  { rewrite Hidxkw Hkw' in Hres. injection Hres as -> ->. done. }
  destruct Hcresl as [-> ->].
  iEval (rewrite HE'fst) in "Hslice".
  (* ----- the append-based item-map surgery (no length-fit side condition:
     append's growth is modeled with an overflow assume, so no client-run
     capacity premise is needed, unlike a pre-sized make) ----- *)
  iDestruct (own_slice_len with "Hslice") as %[Hslklen Hslklen0].
  rewrite length_fmap in Hslklen Hslklen0.
  have Hidxsint : sint.Z idx = Z.of_nat kw by (move: Hslklen Hslklen0 Hkwlt; rewrite -Hidxkw => ? ? ?; word).
  wp_auto.
  iDestruct (own_slice_wf with "Hslice") as %Hslkwf.
  (* newNodes = append(nil, nodes[:index+1]...) *)
  rewrite decide_True; last word.
  wp_auto.
  have Hsplitbnd : (0 ≤ sint.Z (w64_word_instance.(word.add) idx (W64 1)) ≤ sint.Z slk.(slice.len) ≤ sint.Z slk.(slice.len))%Z by word.
  iDestruct (own_slice_slice (w64_word_instance.(word.add) idx (W64 1)) slk.(slice.len) slk (DfracOwn 1) E.*1 Hsplitbnd with "Hslice") as "(Hsl_pre & Hsl_suf & Hsl_tail)".
  iAssert (slice.nil ↦* ([] : list loc))%I with "[]" as "Hnil0"; first iApply own_slice_nil.
  iAssert (own_slice_cap loc slice.nil (DfracOwn 1))%I with "[]" as "Hnilcap"; first iApply own_slice_cap_nil.
  wp_apply (wp_slice_append with "[Hnil0 Hnilcap Hsl_pre]"); first (iFrame "Hnil0 Hnilcap Hsl_pre").
  iIntros (sl1) "(Hsl1 & Hsl1cap & Hsl_pre)".
  wp_auto.
  (* newNodes = append(newNodes, right) *)
  wp_apply wp_slice_literal. iSplitR; first done. iIntros "%slit [Hslit _]". wp_auto.
  wp_apply (wp_slice_append with "[Hsl1 Hsl1cap Hslit]"); first (iFrame "Hsl1 Hsl1cap Hslit").
  iIntros (sl2) "(Hsl2 & Hsl2cap & _)".
  wp_auto.
  (* newNodes = append(newNodes, nodes[index+1:]...) *)
  rewrite decide_True; last word.
  wp_auto.
  wp_apply (wp_slice_append with "[Hsl2 Hsl2cap Hsl_suf]"); first (iFrame "Hsl2 Hsl2cap Hsl_suf").
  iIntros (newSl) "(HnewNodes & HnewCap & Hsl_suf)".
  wp_auto.
  have HnkB : sint.nat (w64_word_instance.(word.add) idx (W64 1)) = (kw + 1)%nat.
  { move: Hslklen Hslklen0 Hkwlt Hidxsint => ? ? ? ?. word. }
  have Esrc : subslice (sint.nat (w64_word_instance.(word.add) idx (W64 1))) (sint.nat slk.(slice.len)) E.*1 = drop (kw + 1) E.*1.
  { rewrite HnkB -Hslklen /subslice take_ge; [reflexivity | rewrite length_fmap; clear -Hkwlt; lia]. }
  have Elit : <[sint.nat (W64 0) := rs]> ([null] : list loc) = [rs].
  { have -> : sint.nat (W64 0) = 0%nat by word. reflexivity. }
  have Eall : (([] ++ take (sint.nat (w64_word_instance.(word.add) idx (W64 1))) E.*1) ++ <[sint.nat (W64 0) := rs]> ([null] : list loc)) ++ subslice (sint.nat (w64_word_instance.(word.add) idx (W64 1))) (sint.nat slk.(slice.len)) E.*1 = take (kw + 1) E.*1 ++ rs :: drop (kw + 1) E.*1.
  { rewrite Esrc Elit HnkB app_nil_l -app_assoc /=. reflexivity. }
  iEval (rewrite Eall) in "HnewNodes".
  iAssert (slk ↦* E.*1)%I with "[Hsl_pre Hsl_suf Hsl_tail]" as "Hslice".
  { rewrite (own_slice_slice (w64_word_instance.(word.add) idx (W64 1)) slk.(slice.len) slk (DfracOwn 1) E.*1 Hsplitbnd). iFrame. }
  (* s.items[client] = newNodes: the key read borrows the left half's node again *)
  iDestruct (own_type_pool_runs_node_acc locs2 p2 parent ls2 tm2 k l leftRun Hl2 Hp2 Hlk2 Hrk2 with "Htypes2")
    as (iv3) "Hacc3". iNamed "Hacc3".
  have Hid3 : toYjsId iv3.(yjs.item.id') = toYjsId itemVal.(yjs.item.id').
  { rewrite -Haccid0 /leftRun Hheadl Hid //. }
  have Hkey3 : iv3.(yjs.item.id').(yjs.id.clientId') = kc.
  { have Hc1 := f_equal clientId Hid3. simpl in Hc1. rewrite /kc. clear -Hc1. word. }
  wp_auto.
  wp_apply (wp_map_insert with "Hmap").
  iIntros "Hmap".
  iEval (rewrite Hkey3) in "Hmap".
  iDestruct ("Haccback" with "Haccval") as "Htypes2".
  (* the item-map model surgery: the right half's address lands at position
     kw+1 of the client's slice *)
  have Hkp_left : entry_key_pair (l, leftRun) = entry_key_pair (l, r) := entry_key_pair_split_left l r o Hopos.
  set (key_pair := entry_key_pair (rs, rightRun)) in *.
  have Hkps2 : key_pairs2 ≡ₚ key_pairs ++ [key_pair].
  { rewrite /key_pairs2 /key_pairs Hperm2 Hperm1 !fmap_cons Hkp_left /key_pair.
    apply perm_skip. apply Permutation_cons_append. }
  have Hkc_kp : key_pair.1 = kc.
  { rewrite /key_pair /entry_key_pair /entry_client /= /rightRun Hclientr. exact Hecl. }
  have Hkp_clock : key_pair.2.1 = (Z.of_nat (run_clock r) + Z.of_nat o)%Z.
  { rewrite /key_pair /entry_key_pair /entry_clock_loc /entry_clock /= /rightRun Hclockr. word. }
  have Hdisj_E : ∀ j e, E !! j = Some e -> j ≠ kw ->
      (run_clock e.2 + length (run_items e.2) <= run_clock r)%nat ∨
      (run_clock r + length (run_items r) <= run_clock e.2)%nat.
  { move=> j [le re] Hj Hne. exact (HidisjE j kw le l re r Hj Hkw Hne). }
  (* [clock_loc_le]'s decision instance is local to [store/value_cells], so the
     two order premises are stated over the sorted entries and carried to
     [merge_sort]'s form through [Hprs] *)
  have Hbef : ∀ a, a ∈ take (kw + 1) (entry_clock_loc <$> E) -> (a.1 < key_pair.2.1)%Z.
  { rewrite -fmap_take. move=> a Ha. apply list_elem_of_fmap in Ha as (e & -> & He).
    apply list_elem_of_lookup_1 in He as [j Hj]. apply lookup_take_Some in Hj as [Hj Hjlt].
    have Hbe : (Z.of_nat (run_clock e.2) < 2^64)%Z := proj2 (Hbnds e.2 (HEmem e (list_elem_of_lookup_2 _ _ _ Hj))).
    destruct e as [le re]. simpl in Hbe.
    rewrite Hkp_clock /entry_clock_loc /= (entry_clock_Z le re Hbe).
    destruct (decide (j = kw)) as [-> | Hne].
    - rewrite Hkw in Hj. injection Hj as <- <-. lia.
    - have Hle := StronglySorted_lookup_le entry_le E j kw (le, re) (l, r) HsortE Hj Hkw ltac:(lia).
      rewrite /entry_le (entry_clock_Z le re Hbe) (entry_clock_Z l r Hckb) in Hle. lia. }
  have Haft : ∀ a, a ∈ drop (kw + 1) (entry_clock_loc <$> E) -> (key_pair.2.1 < a.1)%Z.
  { rewrite -fmap_drop. move=> a Ha. apply list_elem_of_fmap in Ha as (e & -> & He).
    apply list_elem_of_lookup_1 in He as [j Hj]. rewrite lookup_drop in Hj.
    have Hmem := HEmem e (list_elem_of_lookup_2 _ _ _ Hj).
    have Hbe : (Z.of_nat (run_clock e.2) < 2^64)%Z := proj2 (Hbnds e.2 Hmem).
    have Hwe : run_wf (run_items e.2) := Hwfall e.2 Hmem.
    destruct e as [le re]. simpl in Hbe, Hwe, Hmem.
    have Hne : (kw + 1 + j)%nat ≠ kw by lia.
    rewrite Hkp_clock /entry_clock_loc /= (entry_clock_Z le re Hbe).
    destruct (Hdisj_E (kw + 1 + j)%nat (le, re) Hj Hne) as [Hd | Hd]; simpl in Hd.
    - exfalso.
      have Hle := StronglySorted_lookup_le entry_le E kw (kw + 1 + j)%nat (l, r) (le, re) HsortE Hkw Hj ltac:(lia).
      rewrite /entry_le (entry_clock_Z l r Hckb) (entry_clock_Z le re Hbe) in Hle.
      have [Hne0 _] := Hwe. destruct (run_items re); [done | simpl in Hd; lia].
    - lia. }
  have Hnokey : ∀ a, a ∈ key_pairs -> a.1 = key_pair.1 -> a.2.1 = key_pair.2.1 -> False.
  { move=> a Ha Hac Hapr. apply list_elem_of_fmap in Ha as (e & -> & He).
    destruct e as [le re].
    have HeE : (le, re) ∈ E.
    { apply client_entries_mem. split; [exact He |]. rewrite Hkc_kp entry_key_pair_split /= in Hac. exact Hac. }
    have Hmem := HEmem (le, re) HeE. simpl in Hmem.
    have Hbe : (Z.of_nat (run_clock re) < 2^64)%Z := proj2 (Hbnds re Hmem).
    apply list_elem_of_lookup in HeE as [j Hj].
    rewrite Hkp_clock entry_key_pair_split /= /entry_clock_loc /= (entry_clock_Z le re Hbe) in Hapr.
    destruct (decide (j = kw)) as [-> | Hne].
    - rewrite Hkw in Hj. injection Hj as <- <-. lia.
    - destruct (Hdisj_E j (le, re) Hj Hne) as [Hd | Hd]; simpl in Hd; lia. }
  have Hkpc : key_pairs_clock_unique (key_pairs ++ [key_pair]).
  { move=> a b Ha Hb Hab Hpr.
    apply elem_of_app in Ha as [Ha | Ha]; apply elem_of_app in Hb as [Hb | Hb].
    - exact (Hclockunique a b Ha Hb Hab Hpr).
    - apply list_elem_of_singleton in Hb as ->. exfalso. exact (Hnokey a Ha Hab Hpr).
    - apply list_elem_of_singleton in Ha as ->. exfalso. apply (Hnokey b Hb); [symmetry; exact Hab | symmetry; exact Hpr].
    - apply list_elem_of_singleton in Ha as ->. apply list_elem_of_singleton in Hb as ->. reflexivity. }
  have Hclockunique2 : key_pairs_clock_unique key_pairs2.
  { move=> a b Ha Hb. rewrite Hkps2 in Ha Hb. exact (Hkpc a b Ha Hb). }
  have Hbef' := Hbef. rewrite -Hprs in Hbef'.
  have Haft' := Haft. rewrite -Hprs in Haft'.
  have Hnew_kc : key_pair_client_locs kc key_pairs2 = take (kw + 1) E.*1 ++ rs :: drop (kw + 1) E.*1.
  { rewrite (key_pair_client_locs_perm kc key_pairs2 (key_pairs ++ [key_pair]) Hclockunique2 Hkps2).
    rewrite (key_pair_client_locs_insert kc key_pairs key_pair (kw + 1) Hclockunique Hkc_kp Hbef' Haft').
    rewrite -/(client_locs locs p kc) Hce. reflexivity. }
  have Hnew_other : ∀ c', c' ≠ kc -> key_pair_client_locs c' key_pairs2 = key_pair_client_locs c' key_pairs.
  { move=> c' Hne. rewrite (key_pair_client_locs_perm c' key_pairs2 (key_pairs ++ [key_pair]) Hclockunique2 Hkps2).
    apply key_pair_client_locs_other. rewrite Hkc_kp. exact (λ H, Hne (eq_sym H)). }
  have Hcomplete2 : ∀ c, c ∈ key_pairs2.*1 -> is_Some (<[kc := newSl]> gm !! c).
  { move=> c Hc. rewrite Hkps2 fmap_app in Hc. apply elem_of_app in Hc as [Hc | Hc].
    - destruct (decide (c = kc)) as [-> | Hne].
      + rewrite lookup_insert_eq. eauto.
      + rewrite lookup_insert_ne; [| congruence]. exact (Hcomplete c Hc).
    - apply list_elem_of_fmap in Hc as (a & -> & Ha). apply list_elem_of_singleton in Ha as ->.
      rewrite Hkc_kp lookup_insert_eq. eauto. }
  iEval (rewrite -Hce /client_locs) in "Hslice".
  iDestruct ("Hrunsback" with "[Hslice Hcap]") as "Hruns";
    first (iSplitL "Hslice"; [iExact "Hslice" | iExact "Hcap"]).
  iAssert (own_item_map_runs mref (DfracOwn 1) locs2 p2) with "[Hmap HnewNodes HnewCap Hruns]" as "Hitemmap2".
  { iExists (<[kc := newSl]> gm). iFrame "Hmap".
    iSplitL "HnewNodes HnewCap Hruns".
    - rewrite big_sepM_insert_delete. iSplitL "HnewNodes HnewCap".
      { rewrite -/key_pairs2 Hnew_kc. iFrame. }
      iDestruct (big_sepM_delete _ _ kc slk Hslk with "Hruns") as "[_ Hrest]".
      iApply (big_sepM_impl with "Hrest").
      iIntros "!#" (client s0 Hcs) "H". iNamed "H".
      have Hne2 : client ≠ kc.
      { move=> Heqc. rewrite Heqc lookup_delete_eq in Hcs. discriminate. }
      rewrite -/key_pairs2 (Hnew_other client Hne2). iFrame.
    - iPureIntro. split; [exact Hcomplete2 | exact Hclockunique2]. }
  wp_auto.
  iAssert (own_store_runs s (MkStoreStateRuns client0 k0 locs2 p2 bind pend pdel))
    with "[Hclient Hclock HdeletedSet Hitemsf Hitemmap2 Hregistry Htypes2 Hpending Hpdeletes]" as "Hfinal".
  { iSplitL; last (iPureIntro; split; [exact Hrpi2 | exact Hreg2]).
    rewrite /own_store_fields_runs /=.
    iFrame "Hclient Hclock HdeletedSet Hregistry Htypes2 Hpending Hpdeletes".
    iExists mref. iFrame "Hitemsf Hitemmap2". }
  iApply ("HΦ" $! rs).
  iSplitL "Hfinal"; first iExact "Hfinal".
  iPureIntro. split; [exact Hrsnn | exact Hrsfresh].
Qed.



(** [store.splitAtAndGetLeft] at run granularity: make the char [idv],
    covered by the [k]-th run of the type at [parent] (the node at [lc]),
    END a node. Nothing changes when [idv] is the run's last char; else the
    node is split just after [idv] and the truncated left half keeps its
    address. Either way the node at [lc] comes back and the pool and the
    address map step by [pool_split_left_step] (index-explicit; the
    boundary it pins is [pool_split_left_step_ends_at], and it weakens to
    [pool_after_split] through [pool_split_step_of_left]). Proved directly
    from [wp_store__GetNode_runs] and [wp_store__splitNode_runs]. *)
Lemma wp_store__splitAtAndGetLeft_runs (s : loc) (idv : yjs.id.t) (state : store_state_runs)
    (parent : loc) (tm : type_model) (ls : list loc) (k : nat) (r : ItemRun) (lc : loc) :
  sr_pool state !! parent = Some tm ->
  sr_locs state !! parent = Some ls ->
  tm_runs tm !! k = Some r ->
  ls !! k = Some lc ->
  run_covers r (toYjsId idv) ->
  {{{ is_pkg_init yjs ∗ own_store_runs s state }}}
    s @! (go.PointerType yjs.store) @! "splitAtAndGetLeft" #idv
  {{{ (p' : pool) (locs' : gmap loc (list loc)), RET (#lc, #true);
      own_store_runs s (state <| sr_pool := p' |> <| sr_locs := locs' |>) ∗
      ⌜pool_split_left_step (sr_pool state) (sr_locs state) parent k (toYjsId idv) p' locs'⌝ }}}.
Proof using Type*.
  move=> Hp Hls Hr Hlk Hcov.
  destruct state as [client0 k0 locs p bind pend pdel]. simpl in *.
  iIntros (Φ) "(#Hpkg & Hruns) HΦ".
  wp_method_call. wp_call. wp_call. wp_auto.
  have Hcovp : pool_run_covers p parent k (toYjsId idv) by (exists tm, r).
  wp_apply (wp_store__GetNode_runs s idv (MkStoreStateRuns client0 k0 locs p bind pend pdel)
              with "[$Hpkg $Hruns]").
  iIntros (nl ok) "(Hruns & %Hres)". simpl in Hres.
  destruct ok; last first.
  { exfalso. exact (Hres parent k Hcovp). }
  destruct Hres as (q' & k' & Hcov' & Hloc').
  iDestruct (own_store_runs_covers_unique with "Hruns") as %Huniq.
  destruct (Huniq _ _ _ _ _ Hcov' Hcovp) as [-> ->].
  rewrite Hls /= Hlk in Hloc'. injection Hloc' as <-.
  iDestruct (own_store_runs_run_wf with "Hruns") as %Hwf.
  iDestruct (own_store_runs_run_pool_invs with "Hruns") as %Hrinv.
  have Hrmem : r ∈ all_runs p.
  { apply (elem_of_all_runs p r). exists parent, tm. split; [exact Hp | exact (list_elem_of_lookup_2 _ _ _ Hr)]. }
  have Hrwf : run_wf (run_items r) := Hwf r Hrmem.
  have Hrfits : run_fits r := proj1 (proj2 (proj1 Hrinv r Hrmem)).
  wp_auto.
  iDestruct (own_store_runs_node_acc s (MkStoreStateRuns client0 k0 locs p bind pend pdel)
               parent ls tm k lc r Hls Hp Hlk Hr with "Hruns") as (ivR) "H".
  iNamed "H".
  (* the parent pin names [parent]; [wp_if_destruct]'s bare [subst] would take it *)
  clear Haccpar.
  (* the node's clock and length, at the [uint.Z] level ([wp_if_destruct]'s
     bare [subst] must not eat an equation naming a variable) *)
  have Hivclk : uint.Z ivR.(yjs.item.id').(yjs.id.clock') = Z.of_nat (run_clock r).
  { rewrite /run_clock Haccid /toYjsId /=. word. }
  destruct Hcov as (Hcl & Hlo & Hhi). rewrite /toYjsId /= in Hcl Hlo Hhi.
  have Hlenpos : (1 <= length (run_items r))%nat.
  { destruct Hrwf as [Hne _]. destruct (run_items r); [done | simpl; lia]. }
  have Hrfits' : (Z.of_nat (run_clock r) + Z.of_nat (length (run_items r)) < 2^64)%Z := Hrfits.
  have Hosub : uint.Z (w64_word_instance.(word.sub) idv.(yjs.id.clock') ivR.(yjs.item.id').(yjs.id.clock'))
             = Z.of_nat (uint.nat idv.(yjs.id.clock') - run_clock r)%nat.
  { move: Hivclk Hlo. word. }
  wp_auto.
  wp_apply (wp_item__Len lc (DfracOwn 1) ivR with "[$Haccval]"). iIntros "Haccval".
  iDestruct ("Haccback" with "Haccval") as "Hruns".
  rewrite Haccle.
  wp_auto.
  wp_if_destruct.
  - (* offset = Len-1: the run already ends at [idv]; no split *)
    iApply ("HΦ" $! p locs). simpl.
    iFrame "Hruns". iPureIntro.
    exists tm, ls, r. split_and!; [exact Hp | exact Hls | exact Hr |].
    left. split_and!; [| done | done].
    move: Hosub Hlo Hhi Hrfits'. rewrite /toYjsId /=. word.
  - (* the id sits strictly inside the run: split just after it *)
    have Hnlt : (uint.nat idv.(yjs.id.clock') - run_clock r < length (run_items r) - 1)%nat.
    { move: Hosub Hlo Hhi Hrfits'. rewrite /toYjsId /=. word. }
    have Hdiffnat : uint.nat (w64_word_instance.(word.add)
                      (w64_word_instance.(word.sub) idv.(yjs.id.clock') ivR.(yjs.item.id').(yjs.id.clock'))
                      (W64 1))
                  = (uint.nat idv.(yjs.id.clock') - run_clock r + 1)%nat.
    { move: Hosub Hnlt Hrfits' Hlenpos. word. }
    have Hdiffb : (0 < uint.nat (w64_word_instance.(word.add)
                      (w64_word_instance.(word.sub) idv.(yjs.id.clock') ivR.(yjs.item.id').(yjs.id.clock'))
                      (W64 1)) < length (run_items r))%nat.
    { rewrite Hdiffnat. lia. }
    wp_apply (wp_store__splitNode_runs s (MkStoreStateRuns client0 k0 locs p bind pend pdel)
                parent lc ls tm k r _ Hp Hls Hr Hlk Hdiffb with "[$Hpkg $Hruns]").
    iIntros (rloc) "(Hruns & %Hfresh)". simpl in Hfresh.
    wp_auto.
    iApply ("HΦ" $! _ _). simpl.
    iFrame "Hruns". iPureIntro.
    exists tm, ls, r. split_and!; [exact Hp | exact Hls | exact Hr |].
    right. split; [exact Hnlt |].
    exists rloc. split_and!; [exact (proj1 Hfresh) | exact (proj2 Hfresh) | | done].
    rewrite Hdiffnat /toYjsId //=.
Qed.

(** [store.splitAtAndGetRight] at run granularity: make the char [idv],
    covered by the [k]-th run of the type at [parent] (the node at [lc]),
    START a node. Nothing changes when [idv] is the run's head and the node
    itself comes back; else the node is split at [idv] and the fresh right
    half comes back. The returned address and the step are
    [pool_split_right_step] (the boundary it pins is
    [pool_split_right_step_starts_at]). Proved directly from
    [wp_store__GetNode_runs] and [wp_store__splitNode_runs]. *)
Lemma wp_store__splitAtAndGetRight_runs (s : loc) (idv : yjs.id.t) (state : store_state_runs)
    (parent : loc) (tm : type_model) (ls : list loc) (k : nat) (r : ItemRun) (lc : loc) :
  sr_pool state !! parent = Some tm ->
  sr_locs state !! parent = Some ls ->
  tm_runs tm !! k = Some r ->
  ls !! k = Some lc ->
  run_covers r (toYjsId idv) ->
  {{{ is_pkg_init yjs ∗ own_store_runs s state }}}
    s @! (go.PointerType yjs.store) @! "splitAtAndGetRight" #idv
  {{{ (l : loc) (p' : pool) (locs' : gmap loc (list loc)), RET (#l, #true);
      own_store_runs s (state <| sr_pool := p' |> <| sr_locs := locs' |>) ∗
      ⌜pool_split_right_step (sr_pool state) (sr_locs state) parent k (toYjsId idv) l p' locs'⌝ }}}.
Proof using Type*.
  move=> Hp Hls Hr Hlk Hcov.
  destruct state as [client0 k0 locs p bind pend pdel]. simpl in *.
  iIntros (Φ) "(#Hpkg & Hruns) HΦ".
  wp_method_call. wp_call. wp_call. wp_auto.
  have Hcovp : pool_run_covers p parent k (toYjsId idv) by (exists tm, r).
  wp_apply (wp_store__GetNode_runs s idv (MkStoreStateRuns client0 k0 locs p bind pend pdel)
              with "[$Hpkg $Hruns]").
  iIntros (nl ok) "(Hruns & %Hres)". simpl in Hres.
  destruct ok; last first.
  { exfalso. exact (Hres parent k Hcovp). }
  destruct Hres as (q' & k' & Hcov' & Hloc').
  iDestruct (own_store_runs_covers_unique with "Hruns") as %Huniq.
  destruct (Huniq _ _ _ _ _ Hcov' Hcovp) as [-> ->].
  rewrite Hls /= Hlk in Hloc'. injection Hloc' as <-.
  iDestruct (own_store_runs_run_wf with "Hruns") as %Hwf.
  iDestruct (own_store_runs_run_pool_invs with "Hruns") as %Hrinv.
  have Hrmem : r ∈ all_runs p.
  { apply (elem_of_all_runs p r). exists parent, tm. split; [exact Hp | exact (list_elem_of_lookup_2 _ _ _ Hr)]. }
  have Hrwf : run_wf (run_items r) := Hwf r Hrmem.
  have Hrfits : run_fits r := proj1 (proj2 (proj1 Hrinv r Hrmem)).
  wp_auto.
  iDestruct (own_store_runs_node_acc s (MkStoreStateRuns client0 k0 locs p bind pend pdel)
               parent ls tm k lc r Hls Hp Hlk Hr with "Hruns") as (ivR) "H".
  iNamed "H".
  (* the parent pin names [parent]; [wp_if_destruct]'s bare [subst] would take it *)
  clear Haccpar.
  have Hivclk : uint.Z ivR.(yjs.item.id').(yjs.id.clock') = Z.of_nat (run_clock r).
  { rewrite /run_clock Haccid /toYjsId /=. word. }
  destruct Hcov as (Hcl & Hlo & Hhi). rewrite /toYjsId /= in Hcl Hlo Hhi.
  have Hlenpos : (1 <= length (run_items r))%nat.
  { destruct Hrwf as [Hne _]. destruct (run_items r); [done | simpl; lia]. }
  have Hrfits' : (Z.of_nat (run_clock r) + Z.of_nat (length (run_items r)) < 2^64)%Z := Hrfits.
  have Hosub : uint.Z (w64_word_instance.(word.sub) idv.(yjs.id.clock') ivR.(yjs.item.id').(yjs.id.clock'))
             = Z.of_nat (uint.nat idv.(yjs.id.clock') - run_clock r)%nat.
  { move: Hivclk Hlo. word. }
  wp_auto.
  wp_if_destruct.
  - (* offset > 0: split at the offset, return the fresh right half *)
    iDestruct ("Haccback" with "Haccval") as "Hruns".
    have Hopos : (0 < uint.nat idv.(yjs.id.clock') - run_clock r)%nat.
    { move: Hosub. word. }
    have Hdiffnat : uint.nat (w64_word_instance.(word.sub) idv.(yjs.id.clock') ivR.(yjs.item.id').(yjs.id.clock'))
                  = (uint.nat idv.(yjs.id.clock') - run_clock r)%nat.
    { move: Hosub. word. }
    have Hdiffb : (0 < uint.nat (w64_word_instance.(word.sub) idv.(yjs.id.clock') ivR.(yjs.item.id').(yjs.id.clock'))
                   < length (run_items r))%nat.
    { rewrite Hdiffnat. lia. }
    wp_apply (wp_store__splitNode_runs s (MkStoreStateRuns client0 k0 locs p bind pend pdel)
                parent lc ls tm k r _ Hp Hls Hr Hlk Hdiffb with "[$Hpkg $Hruns]").
    iIntros (rloc) "(Hruns & %Hfresh)". simpl in Hfresh.
    wp_auto.
    iApply ("HΦ" $! rloc _ _). simpl.
    iFrame "Hruns". iPureIntro.
    exists tm, ls, r, lc. split_and!; [exact Hp | exact Hls | exact Hr | exact Hlk |].
    right. split_and!; [exact Hopos | exact (proj1 Hfresh) | exact (proj2 Hfresh) | | done].
    rewrite Hdiffnat //.
  - (* offset = 0: the run already starts at [idv]; no split *)
    iDestruct ("Haccback" with "Haccval") as "Hruns".
    iApply ("HΦ" $! lc p locs). simpl.
    iFrame "Hruns". iPureIntro.
    exists tm, ls, r, lc. split_and!; [exact Hp | exact Hls | exact Hr | exact Hlk |].
    left. split_and!; [| done | done | done].
    rewrite /toYjsId /=. move: Hosub. word.
Qed.

End store_update.
