(** [store.notify] and its walk [textDelta] (issue #198 Part II C2): at the
    end of a transaction, for every root type it changed that somebody
    observes, one walk of the type's runs classifies each char by the
    transaction's record ([record_step]) into the Yjs delta, and every
    callback registered on the type is called with it.

    - [wp_textDelta]: the walk over one type at its run view, against the
      record's two span slices ([own_id_spans]): the returned slice denotes
      [delta_normal_form (record_delta inserted tombstoned current)], the
      current snapshot classified by the record and merged. The walk is
      [Poll]'s ([textobserver/Poll.v]) with the record in place of the
      observer's token: the two proofs share [wp_deltaSnoc] and the
      trailing-retain trim, and stay separate as the Go loops do. *)
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
From iris.algebra Require Import auth gmap gset.
From iris.algebra.lib Require Import dfrac_agree.
From New.proof.store Require Import model value heap wp_private Integrate.
From New.proof.transaction Require Import transaction.
From New.proof.delta Require Import delta.

(* iris.algebra pushes [nat_scope], retuning the default [<] / [≤]; the
   word-arithmetic proofs write [Z] comparisons unannotated, so restore
   [Z_scope] as the default. *)
Local Open Scope Z_scope.

Section store_notify.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.

Notation P := go_string.

Local Notation TId := (TypeId P).

Local Notation Op := (TId * @YjsOperation A)%type.

Local Notation Ev := (@Event Op).

Local Notation DocModel := (gmap TId (list (YjsItem A))).

Local Notation Input := (TId * IntegrateInput (A := A))%type.

Local Notation snapshot := (list (YjsItem A * bool)).

Context {seq_inG : inG Σ (authR (gmapUR loc (gsetUR (YjsItem A))))}.

Context {acc_inG : inG Σ (authR (gsetUR YjsId))}.

Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO addressed_pool))}.
(* the observers' tokens and registrations (issue #198 Part II), as [store/heap] *)
Context {observed_inG : ghost_varG Σ (list (YjsItem go_string * bool))}.
Context {observers_inG : inG Σ (authR (gsetUR (gname * go_string)))}.

(** The walk: one type at its run view, the record's two span slices read
    only. Every run fits a word ([run_fits], the pool's invariant), which
    is what makes the per-char clock arithmetic exact. *)
Lemma wp_textDelta (parent : loc) (dq : dfrac) (ls : list loc) (tm : type_model)
    (insert_sl delete_sl : slice.t) (dq_insert dq_delete : dfrac)
    (inserted tombstoned : gset YjsId) :
  {{{ is_pkg_init yjs ∗ own_ytype parent dq ls tm ∗
      own_id_spans insert_sl dq_insert inserted ∗ own_id_spans delete_sl dq_delete tombstoned ∗
      ⌜∀ r, r ∈ tm_runs tm -> run_fits r⌝ }}}
    @! yjs.textDelta #parent #insert_sl #delete_sl
  {{{ (sl : slice.t), RET #sl;
      own_ytype parent dq ls tm ∗
      own_id_spans insert_sl dq_insert inserted ∗ own_id_spans delete_sl dq_delete tombstoned ∗
      own_delta sl (DfracOwn 1)
        (delta_normal_form (record_delta inserted tombstoned (runs_model (tm_runs tm)))) }}}.
Proof.
  wp_start as "(Hyt & Hins & Hdel & %Hfits_all)".
  iNamed "Hyt".
  iDestruct "Hins" as (insert_vs) "(Hins & %Hinswf & %Hinsids)".
  iDestruct "Hdel" as (delete_vs) "(Hdel & %Hdelwf & %Hdelids)".
  wp_auto.
  iDestruct (own_dll_headptr with "Hdll") as "[%Hhd Hdll]".
  have Hhead : yt.(yjs.yType.start') = loc_at ls 0.
  { rewrite Hhd /loc_at. case_decide as Hd0; last lia. rewrite /= head_lookup //. }
  iDestruct (own_dll_length with "Hdll") as %Hlenls.
  (* the walk: after [kk] runs, the delta is the record's classification of
     the snapshot's first [kk] runs, merged *)
  iAssert (∃ (kk : nat) (dsl : slice.t),
    "Hcur" ∷ cur_ptr ↦ loc_at ls (Z.of_nat kk) ∗
    "Hdll" ∷ own_dll dq parent yt.(yjs.yType.start') tl null null ls tm.(tm_runs) ∗
    "Hdelta_ptr" ∷ delta_ptr ↦ dsl ∗
    "Hdelta" ∷ own_delta dsl (DfracOwn 1)
                 (delta_merge (record_delta inserted tombstoned (runs_model (take kk tm.(tm_runs))))) ∗
    "%Hkk" ∷ ⌜(kk <= length tm.(tm_runs))%nat⌝)%I
    with "[cur Hdll delta]" as "IH".
  { iExists 0%nat, slice.nil. rewrite take_0 /= -Hhead.
    iFrame "cur Hdll delta".
    iSplitR; first iApply own_delta_nil.
    iPureIntro. lia. }
  wp_for "IH".
  destruct (decide (kk < length tm.(tm_runs))%nat) as [Hlt | Hge].
  - (* ---- one more run ---- *)
    iDestruct (loc_at_lt_not_null dq parent yt.(yjs.yType.start') tl ls tm.(tm_runs) kk ltac:(lia) with "Hdll") as "[%Hnn Hdll]".
    rewrite (bool_decide_eq_false_2 (loc_at ls (Z.of_nat kk) = null) Hnn). simpl negb.
    destruct (ls !! kk) as [lk|] eqn:Hlk; [| apply lookup_ge_None in Hlk; lia].
    destruct (tm.(tm_runs) !! kk) as [r|] eqn:Hrk; [| apply lookup_ge_None in Hrk; lia].
    iDestruct (own_dll_acc dq parent yt.(yjs.yType.start') tl ls tm.(tm_runs) kk lk r Hlk Hrk with "Hdll")
      as (prevk nxtk) "(%Hcl & %Hcrn & %Hrun & %Hpck & %Hclen & Hnode & Hback)".
    iDestruct "Hnode" as (itemVal olidk oridk)
      "(Hcval & Hcol & Hcor & %Hinl & %Hinr & %Hid & %Hcontent & %Hpark & %Hprevk & %Hnextk & %Hflags)".
    have Hcloc : lk = loc_at ls (Z.of_nat kk).
    { rewrite /loc_at decide_True; last lia. rewrite Nat2Z.id Hlk //. }
    have Hcr : itemVal.(yjs.item.right') = loc_at ls (Z.of_nat kk + 1).
    { rewrite Hnextk. exact Hcrn. }
    iEval (rewrite -Hcloc) in "Hcur".
    rewrite decide_True; [| reflexivity].
    wp_auto.
    wp_apply (wp_item__Len lk dq itemVal with "[$Hcval]"). iIntros "[Hcval %Hcontlen]".
    wp_auto.
    wp_apply (wp_item__Deleted lk dq itemVal with "[$Hcval]"). iIntros "Hcval".
    rewrite (flags_if_deleted itemVal (run_deleted r) Hflags).
    wp_auto.
    (* the run's client, clock and content, off the node's fields *)
    have Hidw := Hid. rewrite /toYjsId /input_of_run /= in Hidw.
    have Hclient_w : uint.nat itemVal.(yjs.item.id').(yjs.id.clientId') = run_client r by rewrite /run_client -Hidw //.
    have Hclock_w : uint.nat itemVal.(yjs.item.id').(yjs.id.clock') = run_clock r by rewrite /run_clock -Hidw //.
    have Hstr : itemVal.(yjs.item.content').(yjs.content.content') = items_string (run_items r) := Hcontent.
    have Hfits : run_fits r := Hfits_all r (list_elem_of_lookup_2 _ _ _ Hrk).
    rewrite /run_fits in Hfits.
    (* ---- the classification, char by char ---- *)
    iAssert (∃ (i : nat) (dsl : slice.t),
      "Hi" ∷ i_ptr ↦ W64 i ∗
      "Hdelta_ptr" ∷ delta_ptr ↦ dsl ∗
      "Hdelta" ∷ own_delta dsl (DfracOwn 1)
                   (delta_merge (record_delta inserted tombstoned
                      (runs_model (take kk tm.(tm_runs)) ++ take i (run_models r)))) ∗
      "%Hile" ∷ ⌜(i <= length (run_items r))%nat⌝)%I
      with "[i Hdelta_ptr Hdelta]" as "IHi".
    { iExists 0%nat, dsl. rewrite take_0 app_nil_r. iFrame "i Hdelta_ptr Hdelta". iPureIntro. lia. }
    wp_for "IHi".
    destruct (decide (i < length (run_items r))%nat) as [Hilt | Hige].
    + (* one more char [x] of the run *)
      rewrite (bool_decide_eq_true_2 (uint.Z (W64 i) < uint.Z (W64 (length itemVal.(yjs.item.content').(yjs.content.content'))))%Z); last (rewrite Hstr Hclen; word).
      destruct (lookup_lt_is_Some_2 (run_items r) i Hilt) as [x Hx].
      have Hxid : item_id x = MkYjsId (run_client r) (run_clock r + i) := run_wf_char_id _ i x Hrun Hx.
      have Hxcont : ∃ b, itemVal.(yjs.item.content').(yjs.content.content') !! i = Some b ∧ content x = [b].
      { have H1 : (content <$> run_items r) !! i = Some (content x) by rewrite list_lookup_fmap Hx //.
        rewrite Hpck /explode list_lookup_fmap in H1.
        destruct (items_string (run_items r) !! i) as [b|] eqn:Hb; rewrite Hb /= in H1; last discriminate.
        exists b. split; [rewrite Hstr; exact Hb | injection H1 as <-; done]. }
      destruct Hxcont as (b & Hb & Hxb).
      have Hrm : run_models r !! i = Some (x, run_deleted r) by rewrite /run_models list_lookup_fmap Hx //.
      have Hstep_i : runs_model (take kk tm.(tm_runs)) ++ take (S i) (run_models r)
                   = (runs_model (take kk tm.(tm_runs)) ++ take i (run_models r)) ++ [(x, run_deleted r)].
      { rewrite (take_S_r _ _ _ Hrm) app_assoc //. }
      have Hclock_i : uint.nat (w64_word_instance.(word.add) itemVal.(yjs.item.id').(yjs.id.clock') (W64 i)) = (run_clock r + i)%nat by word.
      wp_auto.
      wp_apply wp_NewId.
      have Hidx : toYjsId (yjs.id.mk itemVal.(yjs.item.id').(yjs.id.clientId')
                    (w64_word_instance.(word.add) itemVal.(yjs.item.id').(yjs.id.clock') (W64 i)))
                  = item_id x.
      { rewrite /toYjsId /= Hclient_w Hclock_i Hxid //. }
      wp_apply (wp_containsId _ _ _ _ Hinswf with "[$Hins]"). iIntros "Hins".
      rewrite Hidx -Hinsids.
      destruct (decide (item_id x ∈ inserted)) as [Hxins | Hxnins].
      * (* a char this transaction inserted *)
        rewrite (bool_decide_eq_true_2 (item_id x ∈ inserted) Hxins).
        wp_auto.
        destruct (run_deleted r) eqn:Hdel.
        { (* inserted and tombstoned by the same transaction: nothing *)
          wp_auto. wp_for_post.
          iFrame "HΦ insertSet deleteSet Hparent Hins Hdel Hcur Hcol Hcor Hback length tombstoned Hcval".
          iExists (S i), dsl0.
          replace (w64_word_instance.(word.add) (W64 i) (W64 1)) with (W64 (S i)) by word.
          iFrame "Hi Hdelta_ptr".
          have Hmerge : delta_merge (record_delta inserted tombstoned (runs_model (take kk tm.(tm_runs)) ++ take (S i) (run_models r)))
                      = delta_merge (record_delta inserted tombstoned (runs_model (take kk tm.(tm_runs)) ++ take i (run_models r))).
          { rewrite Hstep_i record_delta_app record_delta_singleton /record_step /=.
            rewrite decide_True; last exact Hxins. rewrite app_nil_r //. }
          rewrite Hmerge. iFrame "Hdelta". iPureIntro. lia. }
        (* inserted and live: insert its char; the content is a Go string, so
           the [uint64] offset is a valid [int] index ([Len] said so) *)
        wp_auto.
        have Hi63z : (Z.of_nat i < 2^63)%Z by (rewrite Hstr Hclen in Hcontlen; lia).
        replace (sint.nat (W64 i)) with i by word.
        rewrite Hb.
        wp_auto.
        wp_apply (wp_deltaSnoc _ _ _ (Insert (content x)) with "[$Hdelta]").
        { iPureIntro. split; [reflexivity | rewrite Hxb //]. }
        iIntros (dsl') "Hdelta". wp_auto. wp_for_post.
        iFrame "HΦ insertSet deleteSet Hparent Hins Hdel Hcur Hcol Hcor Hback length tombstoned Hcval".
        iExists (S i), dsl'.
        replace (w64_word_instance.(word.add) (W64 i) (W64 1)) with (W64 (S i)) by word.
        iFrame "Hi Hdelta_ptr".
        have Hmerge : delta_merge (record_delta inserted tombstoned (runs_model (take kk tm.(tm_runs)) ++ take (S i) (run_models r)))
                    = delta_snoc (delta_merge (record_delta inserted tombstoned (runs_model (take kk tm.(tm_runs)) ++ take i (run_models r)))) (Insert (content x)).
        { rewrite Hstep_i record_delta_app record_delta_singleton delta_merge_snoc_option /record_step /=.
          rewrite decide_True; last exact Hxins. done. }
        rewrite Hmerge. iFrame "Hdelta". iPureIntro. lia.
      * (* an older char *)
        rewrite (bool_decide_eq_false_2 (item_id x ∈ inserted) Hxnins).
        wp_auto.
        wp_apply (wp_containsId _ _ _ _ Hdelwf with "[$Hdel]"). iIntros "Hdel".
        rewrite Hidx -Hdelids.
        destruct (decide (item_id x ∈ tombstoned)) as [Hxt | Hxnt].
        { (* tombstoned by this transaction: one delete *)
          rewrite (bool_decide_eq_true_2 (item_id x ∈ tombstoned) Hxt).
          wp_auto.
          wp_apply (wp_deltaSnoc _ _ _ (Delete 1) with "[$Hdelta]").
          { iPureIntro. split; reflexivity. }
          iIntros (dsl') "Hdelta". wp_auto. wp_for_post.
          iFrame "HΦ insertSet deleteSet Hparent Hins Hdel Hcur Hcol Hcor Hback length tombstoned Hcval".
          iExists (S i), dsl'.
          replace (w64_word_instance.(word.add) (W64 i) (W64 1)) with (W64 (S i)) by word.
          iFrame "Hi Hdelta_ptr".
          have Hmerge : delta_merge (record_delta inserted tombstoned (runs_model (take kk tm.(tm_runs)) ++ take (S i) (run_models r)))
                      = delta_snoc (delta_merge (record_delta inserted tombstoned (runs_model (take kk tm.(tm_runs)) ++ take i (run_models r)))) (Delete 1).
          { rewrite Hstep_i record_delta_app record_delta_singleton delta_merge_snoc_option /record_step /=.
            rewrite decide_False; last exact Hxnins. rewrite decide_True; last exact Hxt. rewrite Hxb //. }
          rewrite Hmerge. iFrame "Hdelta". iPureIntro. lia. }
        rewrite (bool_decide_eq_false_2 (item_id x ∈ tombstoned) Hxnt).
        wp_auto.
        destruct (run_deleted r) eqn:Hdel.
        { (* an older tombstone: nothing *)
          wp_auto. wp_for_post.
          iFrame "HΦ insertSet deleteSet Hparent Hins Hdel Hcur Hcol Hcor Hback length tombstoned Hcval".
          iExists (S i), dsl0.
          replace (w64_word_instance.(word.add) (W64 i) (W64 1)) with (W64 (S i)) by word.
          iFrame "Hi Hdelta_ptr".
          have Hmerge : delta_merge (record_delta inserted tombstoned (runs_model (take kk tm.(tm_runs)) ++ take (S i) (run_models r)))
                      = delta_merge (record_delta inserted tombstoned (runs_model (take kk tm.(tm_runs)) ++ take i (run_models r))).
          { rewrite Hstep_i record_delta_app record_delta_singleton /record_step /=.
            rewrite decide_False; last exact Hxnins. rewrite decide_False; last exact Hxnt. rewrite app_nil_r //. }
          rewrite Hmerge. iFrame "Hdelta". iPureIntro. lia. }
        { (* an older live char: one retain *)
          wp_auto.
          wp_apply (wp_deltaSnoc _ _ _ (Retain 1) with "[$Hdelta]").
          { iPureIntro. split; reflexivity. }
          iIntros (dsl') "Hdelta". wp_auto. wp_for_post.
          iFrame "HΦ insertSet deleteSet Hparent Hins Hdel Hcur Hcol Hcor Hback length tombstoned Hcval".
          iExists (S i), dsl'.
          replace (w64_word_instance.(word.add) (W64 i) (W64 1)) with (W64 (S i)) by word.
          iFrame "Hi Hdelta_ptr".
          have Hmerge : delta_merge (record_delta inserted tombstoned (runs_model (take kk tm.(tm_runs)) ++ take (S i) (run_models r)))
                      = delta_snoc (delta_merge (record_delta inserted tombstoned (runs_model (take kk tm.(tm_runs)) ++ take i (run_models r)))) (Retain 1).
          { rewrite Hstep_i record_delta_app record_delta_singleton delta_merge_snoc_option /record_step /=.
            rewrite decide_False; last exact Hxnins. rewrite decide_False; last exact Hxnt. rewrite Hxb //. }
          rewrite Hmerge. iFrame "Hdelta". iPureIntro. lia. }
    + (* the run's chars are classified: on to the next node *)
      rewrite (bool_decide_eq_false_2 (uint.Z (W64 i) < uint.Z (W64 (length itemVal.(yjs.item.content').(yjs.content.content'))))%Z); last (rewrite Hstr Hclen; word).
      have Hieq : i = length (run_items r) by lia.
      wp_auto.
      wp_for_post.
      iAssert (own_item_node lk dq (input_of_run r) (run_deleted r) parent prevk nxtk)
        with "[Hcval Hcol Hcor]" as "Hnode".
      { iExists itemVal, olidk, oridk. iFrame "Hcval Hcol Hcor". iPureIntro.
        split_and!; [exact Hinl | exact Hinr | exact Hid | exact Hcontent | exact Hpark | exact Hprevk | exact Hnextk | exact Hflags]. }
      iDestruct ("Hback" with "Hnode") as "Hdll".
      iFrame "HΦ insertSet deleteSet Hparent Hins Hdel".
      iExists (S kk), dsl0.
      rewrite Hcr. replace (Z.of_nat kk + 1)%Z with (Z.of_nat (S kk)) by lia.
      iFrame "Hcur Hdll Hdelta_ptr".
      have Hfull : runs_model (take kk tm.(tm_runs)) ++ take i (run_models r) = runs_model (take (S kk) tm.(tm_runs)).
      { have Hlenrm : length (run_models r) = length (run_items r) by rewrite /run_models length_fmap //.
        rewrite Hieq (take_ge (run_models r) (length (run_items r))); last lia.
        rewrite (take_S_r _ _ _ Hrk) runs_model_app runs_model_singleton //. }
      iEval (rewrite Hfull) in "Hdelta". iFrame "Hdelta".
      iPureIntro. lia.
  - (* ---- the walk is done ---- *)
    have Hkeq : kk = length tm.(tm_runs) by lia.
    have Hnull : loc_at ls (Z.of_nat kk) = null.
    { rewrite /loc_at decide_True; [| lia]. rewrite Nat2Z.id lookup_ge_None_2; [done | lia]. }
    rewrite (bool_decide_eq_true_2 (loc_at ls (Z.of_nat kk) = null) Hnull).
    simpl negb.
    rewrite decide_False; [| done]. rewrite decide_True; [| done].
    iEval (rewrite Hkeq take_ge; last lia) in "Hdelta".
    wp_auto.
    iAssert (own_ytype parent dq ls tm) with "[Hparent Hdll]" as "Hyt".
    { iExists yt, tl. iFrame "Hparent Hdll". iPureIntro. exact Hlen. }
    iAssert (own_id_spans insert_sl dq_insert inserted) with "[Hins]" as "Hins".
    { iExists insert_vs. iFrame "Hins". done. }
    iAssert (own_id_spans delete_sl dq_delete tombstoned) with "[Hdel]" as "Hdel".
    { iExists delete_vs. iFrame "Hdel". done. }
    (* ---- the trailing retain is implicit ---- *)
    iNamed "Hdelta".
    iDestruct (own_slice_len with "Hsl") as %[Hsllen Hsllen0].
    iDestruct (own_slice_wf with "Hsl") as %Hslwf.
    set (dm := delta_merge (record_delta inserted tombstoned (runs_model tm.(tm_runs)))).
    have Hlenvs : length vs = length dm by eapply Forall2_length; exact Hdenote.
    have Htd : delta_normal_form (record_delta inserted tombstoned (runs_model tm.(tm_runs)))
               = delta_drop_trailing_retain dm by done.
    destruct (decide (0 < length vs)%nat) as [Hpos | Hzero]; last first.
    { (* the empty delta: nothing to drop *)
      rewrite (bool_decide_eq_false_2 (sint.Z (W64 0) < sint.Z dsl.(slice.len))%Z); last word.
      have Hvs : vs = [] by destruct vs; [done | simpl in Hzero; lia].
      have Hdm : dm = [] by destruct dm; [done | rewrite Hvs in Hlenvs; simpl in Hlenvs; lia].
      wp_auto.
      iApply ("HΦ" $! dsl). iFrame "Hyt Hins Hdel".
      rewrite Htd Hdm /delta_drop_trailing_retain /=. iExists vs. iFrame "Hsl Hcap". iPureIntro.
      rewrite Hvs. constructor. }
    rewrite (bool_decide_eq_true_2 (sint.Z (W64 0) < sint.Z dsl.(slice.len))%Z); last word.
    destruct (lookup_lt_is_Some_2 vs (length vs - 1) ltac:(lia)) as [lastv Hlastv].
    destruct (lookup_lt_is_Some_2 dm (length vs - 1) ltac:(lia)) as [lastop Hlastop].
    have Hdenlast : delta_op_denotes lastv lastop := Forall2_lookup_lr _ _ _ _ _ _ Hdenote Hlastv Hlastop.
    have Hlastdm : last dm = Some lastop.
    { rewrite last_lookup -Hlenvs. replace (pred (length vs)) with (length vs - 1)%nat by lia. exact Hlastop. }
    wp_auto.
    rewrite decide_True; last word.
    iDestruct (own_slice_elem_acc (sint.Z (w64_word_instance.(word.sub) dsl.(slice.len) (W64 1))) lastv dsl (DfracOwn 1) vs with "Hsl") as "[Hel Hgive]".
    { word. }
    { replace (Z.to_nat (sint.Z (w64_word_instance.(word.sub) dsl.(slice.len) (W64 1)))) with (length vs - 1)%nat by word. exact Hlastv. }
    wp_auto.
    iDestruct ("Hgive" $! lastv with "Hel") as "Hsl".
    rewrite list_insert_id; last (replace (Z.to_nat (sint.Z (w64_word_instance.(word.sub) dsl.(slice.len) (W64 1)))) with (length vs - 1)%nat by word; exact Hlastv).
    destruct lastop as [nn | t | nn]; destruct Hdenlast as [Hk1 Hv1].
    + (* a trailing retain: dropped *)
      rewrite Hk1 (bool_decide_eq_true_2 (W8 0 = W8 0)); last done.
      wp_auto.
      rewrite decide_True; last (split_and!; word).
      wp_auto.
      have Hbnd : (0 ≤ sint.Z (W64 0) ≤ sint.Z (w64_word_instance.(word.sub) dsl.(slice.len) (W64 1)) ≤ sint.Z dsl.(slice.len))%Z by split_and!; word.
      iDestruct (own_slice_slice_with_cap (W64 0) (w64_word_instance.(word.sub) dsl.(slice.len) (W64 1)) dsl vs Hbnd with "[$Hsl $Hcap]") as "(_ & Hsl' & Hcap')".
      iApply ("HΦ" $! _). iFrame "Hyt Hins Hdel".
      iExists _. iFrame "Hsl' Hcap'". iPureIntro.
      rewrite Htd /delta_drop_trailing_retain Hlastdm /subslice.
      replace (sint.nat (W64 0)) with 0%nat by word. rewrite drop_0.
      replace (sint.nat (w64_word_instance.(word.sub) dsl.(slice.len) (W64 1))) with (length vs - 1)%nat by word.
      rewrite removelast_firstn_len -Hlenvs.
      replace (pred (length vs)) with (length vs - 1)%nat by lia.
      apply Forall2_take. exact Hdenote.
    + (* a trailing insert: kept *)
      rewrite Hk1 (bool_decide_eq_false_2 (W8 1 = W8 0)); last done.
      wp_auto.
      iApply ("HΦ" $! dsl). iFrame "Hyt Hins Hdel".
      rewrite Htd /delta_drop_trailing_retain Hlastdm. iExists vs. iFrame "Hsl Hcap". iPureIntro. exact Hdenote.
    + (* a trailing delete: kept *)
      rewrite Hk1 (bool_decide_eq_false_2 (W8 2 = W8 0)); last done.
      wp_auto.
      iApply ("HΦ" $! dsl). iFrame "Hyt Hins Hdel".
      rewrite Htd /delta_drop_trailing_retain Hlastdm. iExists vs. iFrame "Hsl Hcap". iPureIntro. exact Hdenote.
Qed.

End store_notify.
