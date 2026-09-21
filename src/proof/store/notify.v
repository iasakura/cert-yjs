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
      trailing-retain trim, and stay separate as the Go loops do.
    - [wp_store__notify]: the transaction handle in, the store and the
      registry at the transaction's end state out: every observer of a
      changed root is called once with the delta from the root's start
      snapshot to its current one ([text_delta_transaction]), certified
      ([own_store_text_snapshot]); the other roots' observers have nothing
      to hear ([type_snapshot_untouched]). *)
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

(** Moving an address the registry does not hold into the told set changes
    nothing for its entries. *)
#[local] Lemma type_observers_told_grow (γs : store_names) (γh : history_names)
    (registry : gmap loc slice.t) (registered : gmap loc (P * list gname))
    (m m0 : DocModel) (deleted deleted0 : gset YjsId) (done : gset loc) (key : loc) :
  registry !! key = None ->
  ([∗ map] parent ↦ cbs_sl; entry ∈ registry; registered,
     own_type_observers γs γh entry.1
       (if decide (parent ∈ done) then type_snapshot m deleted entry.1
        else type_snapshot m0 deleted0 entry.1) cbs_sl entry.2) -∗
  ([∗ map] parent ↦ cbs_sl; entry ∈ registry; registered,
     own_type_observers γs γh entry.1
       (if decide (parent ∈ done ∪ {[key]}) then type_snapshot m deleted entry.1
        else type_snapshot m0 deleted0 entry.1) cbs_sl entry.2).
Proof.
  move=> Hnone. iApply big_sepM2_mono. iIntros (parent cbs_sl entry Hr Hd) "H".
  have Hne : parent ≠ key.
  { move=> Heq. rewrite Heq Hnone in Hr. discriminate. }
  destruct (decide (parent ∈ done)) as [Hin | Hnin].
  - rewrite decide_True; [iExact "H" | apply elem_of_union_l; exact Hin].
  - rewrite decide_False; [iExact "H" |].
    move=> Hu. apply elem_of_union in Hu as [Hu | Hu]; [exact (Hnin Hu) | apply elem_of_singleton in Hu; exact (Hne Hu)].
Qed.

(** [store.notify]: every observer of a root the transaction changed is told
    the delta from the transaction's start snapshot of that root to its
    current one, with the current snapshot's certificate; the registry
    moves to the current state, the observers of the other roots having
    nothing new to hear. The transaction's record is consumed:
    [transact] releases the lock right after. *)
Lemma wp_store__notify (s_loc tr : loc) (γs : store_names) (γh : history_names)
    (c : ClientId) (h : list Ev) (m : DocModel) (pend : list Input)
    (deleted inserted tombstoned : gset YjsId) (changed : gset P) :
  {{{ is_pkg_init yjs ∗ own_transaction tr s_loc γs γh c h m pend deleted inserted tombstoned changed }}}
    s_loc @! (go.PointerType yjs.store) @! "notify" #tr
  {{{ RET #(); own_store s_loc γs γh c h m pend deleted ∗
      ∃ observers_mref : loc, own_observer_registry observers_mref γs γh m deleted }}}.
Proof.
  wp_start as "Htx".
  iDestruct "Htx" as (changed_locs m0 deleted0 observers_mref) "Htx". iNamed "Htx".
  iNamed "Hchanges". iNamed "Hregistry".
  iAssert (own_id_spans trv.(yjs.Transaction.insertSet') (DfracOwn 1) inserted) with "[Hinsert]" as "Hinsert".
  { iExists insert_vs. iFrame "Hinsert". done. }
  iAssert (own_id_spans trv.(yjs.Transaction.deleteSet') (DfracOwn 1) tombstoned) with "[Hdelete]" as "Hdelete".
  { iExists delete_vs. iFrame "Hdelete". done. }
  iClear "Hinsertcap Hdeletecap".
  wp_auto.
  (* the walk over the changed types: after [i] of them, their observers are
     at the end state and the others still at the start state *)
  wp_apply (wp_map_for_range (λ (keys : list loc) (i : Z),
    ∃ (done : gset loc) (tyv : loc),
      "%Hdone" ∷ ⌜done = list_to_set (take (Z.to_nat i) keys) ∧ (0 ≤ i)%Z⌝ ∗
      "ty" ∷ ty_ptr ↦ tyv ∗
      "tr" ∷ tr_ptr ↦ tr ∗
      "s" ∷ s_ptr ↦ s_loc ∗
      "Htr" ∷ tr ↦ trv ∗
      "Hinsert" ∷ own_id_spans trv.(yjs.Transaction.insertSet') (DfracOwn 1) inserted ∗
      "Hdelete" ∷ own_id_spans trv.(yjs.Transaction.deleteSet') (DfracOwn 1) tombstoned ∗
      "Hstore" ∷ own_store s_loc γs γh c h m pend deleted ∗
      "Hobserversmap" ∷ own_map observers_mref (DfracOwn 1) registry ∗
      "Hobserversauth" ∷ own γs.(sn_observers) (● registered_tokens registered : authR (gsetUR (gname * P))) ∗
      "Hobservers" ∷ ([∗ map] parent ↦ cbs_sl; entry ∈ registry; registered,
         own_type_observers γs γh entry.1
           (if decide (parent ∈ done) then type_snapshot m deleted entry.1
            else type_snapshot m0 deleted0 entry.1) cbs_sl entry.2))%I
    with "Hchanged").
  iIntros (keys) "%Hkeys". destruct Hkeys as (Hkeysdom & Hkeyslen & Hkeysnodup).
  rewrite dom_gset_to_gmap in Hkeysdom.
  iSplitL "ty tr s Htr Hinsert Hdelete Hstore Hobserversmap Hobserversauth Hobservers".
  { iExists ∅, _. iFrame "ty tr s Htr Hinsert Hdelete Hstore Hobserversmap Hobserversauth".
    iSplitR. { iPureIntro. split; [rewrite /= ?take_0 ?list_to_set_nil // | lia]. }
    iApply (big_sepM2_mono with "Hobservers"). iIntros (parent cbs_sl entry Hr Hd) "H".
    first [iExact "H" | rewrite decide_False; [iExact "H" | apply not_elem_of_empty]]. }
  iSplitR "HΦ".
  { (* ---- one changed type ---- *)
    iModIntro. iIntros (i key v [Hkey Hval]) "HP".
    iDestruct "HP" as (done tyv) "HP". iNamed "HP". destruct Hdone as [Hdone Hi0].
    have Hkeyin : key ∈ changed_locs.
    { rewrite -Hkeysdom elem_of_list_to_set. exact (list_elem_of_lookup_2 _ _ _ Hkey). }
    have Hkeynot : key ∉ done.
    { rewrite Hdone elem_of_list_to_set. move=> Hin.
      apply list_elem_of_lookup in Hin as [j Hj].
      apply lookup_take_Some in Hj as [Hj Hjlt].
      have := NoDup_lookup _ _ _ _ Hkeysnodup Hj Hkey. lia. }
    have Hdone' : (list_to_set (take (Z.to_nat (i + 1)) keys) : gset loc) = done ∪ {[key]}.
    { rewrite Hdone. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
      rewrite (take_S_r _ _ _ Hkey) list_to_set_app_L list_to_set_cons list_to_set_nil (right_id_L ∅ (∪)) //. }
    (* the [observers] field, read off the store: the registry's map *)
    iDestruct (own_store_observers_acc with "Hstore") as (observers_mref') "(#Hpin' & Hobserversf & Hstoreback)".
    iDestruct (is_store_observers_agree with "Hpin' Hregistrypin") as %Heqref. subst observers_mref'.
    wp_auto.
    wp_apply (wp_map_lookup1 with "Hobserversmap"). iIntros "Hobserversmap".
    iDestruct ("Hstoreback" with "Hobserversf") as "Hstore".
    wp_auto.
    iDestruct (big_sepM2_dom with "Hobservers") as %Hdomeq.
    destruct (registry !! key) as [cbs_sl |] eqn:Hrkey; last first.
    { (* nobody observes this type *)
      have Hdkey : registered !! key = None.
      { apply not_elem_of_dom. rewrite -Hdomeq. apply not_elem_of_dom. exact Hrkey. }
      rewrite (bool_decide_eq_false_2 (sint.Z (W64 0) < sint.Z (default slice.nil None).(slice.len))%Z); last (simpl; word).
      wp_auto.
      unfold for_map_postcondition. iRight. iLeft. iSplitR; first done.
      iExists (done ∪ {[key]}), key.
      iFrame "ty tr s Htr Hinsert Hdelete Hstore Hobserversmap Hobserversauth".
      iSplitR; first (iPureIntro; split; [symmetry; exact Hdone' | lia]).
      iApply (type_observers_told_grow with "Hobservers"). exact Hrkey. }
    (* the type is observed: its callbacks hear the delta *)
    have [entry Hdkey] : is_Some (registered !! key).
    { apply elem_of_dom. rewrite -Hdomeq. apply elem_of_dom. by exists cbs_sl. }
    iEval (rewrite (big_sepM2_delete _ _ _ key cbs_sl entry Hrkey Hdkey)) in "Hobservers".
    iDestruct "Hobservers" as "[Hentry Hobservers]".
    destruct (decide (key ∈ done)) as [Hbad | _]; first (exfalso; exact (Hkeynot Hbad)).
    iDestruct "Hentry" as (cbs) "Hentry". iNamed "Hentry".
    iDestruct (own_slice_len with "Hentry_slice") as %[Hcbslen Hcbslen0].
    iDestruct (big_sepL2_length with "Hentry_callbacks") as %Hlencbs.
    destruct (decide (0 < length cbs)%nat) as [Hpos | Hzero]; last first.
    { (* no callbacks: nothing to tell *)
      rewrite (bool_decide_eq_false_2 (sint.Z (W64 0) < sint.Z (default slice.nil (Some cbs_sl)).(slice.len))%Z); last (simpl; word).
      have Hcbs : cbs = [] by (destruct cbs; [done | simpl in Hzero; lia]).
      subst cbs.
      iDestruct (big_sepL2_nil_inv_l with "Hentry_callbacks") as %Hγos.
      wp_auto.
      unfold for_map_postcondition. iRight. iLeft. iSplitR; first done.
      iExists (done ∪ {[key]}), key.
      iFrame "ty tr s Htr Hinsert Hdelete Hstore Hobserversmap Hobserversauth".
      iSplitR; first (iPureIntro; split; [symmetry; exact Hdone' | lia]).
      rewrite (big_sepM2_delete _ _ _ key cbs_sl entry Hrkey Hdkey).
      iSplitL "Hentry_slice Hentry_cap".
      { rewrite decide_True; last (apply elem_of_union_r; by apply elem_of_singleton).
        iExists []. iFrame "Hentry_slice Hentry_cap". rewrite Hγos big_sepL2_nil //. }
      iApply (type_observers_told_grow with "Hobservers"). apply lookup_delete_eq. }
    rewrite (bool_decide_eq_true_2 (sint.Z (W64 0) < sint.Z (default slice.nil (Some cbs_sl)).(slice.len))%Z); last (simpl; word).
    wp_auto.
    (* ---- the walk over this type ---- *)
    iDestruct "Hstore" as (client k pdel locs p bind acc observers_mref0) "Hown". iNamed "Hown".
    iDestruct (big_sepM_lookup _ _ key entry Hdkey with "Hregistered_bind") as "#Hbind_key".
    iDestruct (ghost_map_lookup with "HtypesAuth Hbind_key") as %Hbindlk.
    iDestruct (own_store_state_registry_coh with "Hstate") as %Hregcoh.
    iDestruct (own_store_state_run_pool_invs with "Hstate") as %Hpoolinv.
    iDestruct (own_store_state_arr_inv with "Hstate") as %Harrinv.
    iDestruct (own_store_state_aligned with "Hstate") as %Haligned.
    simpl in Hregcoh, Hpoolinv, Harrinv, Haligned.
    destruct (proj1 Hregcoh entry.1 key Hbindlk) as [tm Htmp].
    have [ls Hls] : is_Some (locs !! key).
    { apply elem_of_dom. rewrite (proj1 Haligned). apply elem_of_dom. by exists tm. }
    have Hdoc : doc_model_get m (RootId entry.1) = tm_arr tm := proj1 Hregmodel entry.1 key tm Hbindlk Htmp.
    have Hfits_all : ∀ r, r ∈ tm_runs tm -> run_fits r.
    { move=> r Hr. have Hrall : r ∈ all_runs p by (apply elem_of_all_runs; exists key, tm).
      exact (proj1 (proj2 (proj1 Hpoolinv r Hrall))). }
    iDestruct (own_store_state_ytype_acc s_loc (MkStoreState client k locs p bind pend pdel) key ls tm Hls Htmp with "Hstate") as "[Hyt Hclose]".
    wp_apply (wp_textDelta with "[$Hyt $Hinsert $Hdelete]").
    { iPureIntro. exact Hfits_all. }
    iIntros (dsl) "(Hyt & Hinsert & Hdelete & Hdelta)".
    iDestruct ("Hclose" with "Hyt") as "Hstate".
    (* the delta is the one the callbacks are told, from the start snapshot *)
    have Hrm : runs_model (tm_runs tm) = type_snapshot m deleted entry.1.
    { rewrite Hdeleted. exact (type_snapshot_runs_model m bind p entry.1 key tm Hpoolinv Hregmodel Hbindlk Htmp). }
    have Harr : YjsArrInvariant (doc_model_get m (RootId entry.1)) by (rewrite Hdoc; exact (Harrinv _ _ Htmp)).
    destruct (text_delta_transaction m deleted inserted tombstoned m0 deleted0 entry.1 Hstart Htombstoned_sub Harr) as [Hdeltaeq Hgrows].
    iEval (rewrite Hrm -Hdeltaeq) in "Hdelta".
    iAssert (own_store s_loc γs γh c h m pend deleted) with "[Hstate Hseq HtypesAuth Hhist Hacc Hdelete_set Hobserversf]" as "Hstore".
    { iExists client, k, pdel, locs, p, bind, acc, observers_mref0. iFrame "∗#". iPureIntro.
      split_and!; [exact Hclientc | exact Hpendroot | exact Hpendbnd | exact Hregmodel | exact Hhcoh | exact Hctr | exact Hacccoh | exact Hdeleted]. }
    iMod (own_store_text_snapshot with "Hbind_key Hstore") as "[Hstore #Hsnap]".
    wp_auto.
    (* ---- every callback of this type, in the slice's order ---- *)
    iAssert (∃ (j : nat),
      "Hj" ∷ i_ptr ↦ W64 j ∗
      "Hdelta" ∷ own_delta dsl (DfracOwn 1) (text_delta (type_snapshot m0 deleted0 entry.1) (type_snapshot m deleted entry.1)) ∗
      "Htold" ∷ ([∗ list] cb; γo ∈ take j cbs; take j entry.2,
                   is_text_callback γs γh entry.1 cb γo ∗ own_observed γo (type_snapshot m deleted entry.1)) ∗
      "Htotell" ∷ ([∗ list] cb; γo ∈ drop j cbs; drop j entry.2,
                   is_text_callback γs γh entry.1 cb γo ∗ own_observed γo (type_snapshot m0 deleted0 entry.1)) ∗
      "%Hjle" ∷ ⌜(j <= length cbs)%nat⌝)%I
      with "[i Hdelta Hentry_callbacks]" as "IH".
    { iExists 0%nat. rewrite !take_0 !drop_0. iFrame "i Hdelta Hentry_callbacks".
      iSplitR; [rewrite big_sepL2_nil // | iPureIntro; lia]. }
    wp_for "IH".
    destruct (decide (j < length cbs)%nat) as [Hjlt | Hjge].
    - (* one callback *)
      rewrite (bool_decide_eq_true_2 (sint.Z (W64 j) < sint.Z cbs_sl.(slice.len))%Z); last word.
      wp_auto.
      rewrite decide_True; last (split; word).
      destruct (lookup_lt_is_Some_2 cbs j Hjlt) as [cb Hcb].
      destruct (lookup_lt_is_Some_2 entry.2 j ltac:(lia)) as [γo Hγo].
      iDestruct (own_slice_elem_acc (sint.Z (W64 j)) cb cbs_sl (DfracOwn 1) cbs with "Hentry_slice") as "[Hel Hgive]".
      { word. }
      { replace (Z.to_nat (sint.Z (W64 j))) with j by word. exact Hcb. }
      wp_auto.
      iDestruct ("Hgive" $! cb with "Hel") as "Hentry_slice".
      rewrite list_insert_id; last (replace (Z.to_nat (sint.Z (W64 j))) with j by word; exact Hcb).
      rewrite (drop_S cbs cb j Hcb) (drop_S entry.2 γo j Hγo).
      iDestruct (big_sepL2_cons with "Htotell") as "[[#Hcb Hobs] Htotell]".
      wp_apply ("Hcb" $! dsl (DfracOwn 1) (type_snapshot m0 deleted0 entry.1) (type_snapshot m deleted entry.1) with "[Hobs Hdelta]").
      { iFrame "Hobs Hdelta Hsnap". iPureIntro. exact Hgrows. }
      iIntros "[Hobs Hdelta]".
      wp_auto. wp_for_post.
      iFrame "ty tr s Htr Hinsert Hdelete Hstore Hobserversmap Hobserversauth Hobservers Hentry_slice Hentry_cap callbacks delta".
      iExists (S j).
      replace (w64_word_instance.(word.add) (W64 j) (W64 1)) with (W64 (S j)) by word.
      iFrame "Hj Hdelta Htotell".
      rewrite (take_S_r cbs j cb Hcb) (take_S_r entry.2 j γo Hγo).
      iSplitL; last (iPureIntro; lia).
      rewrite big_sepL2_snoc. iFrame "Htold Hcb Hobs".
    - (* every callback told: the type's observers are at the end state *)
      rewrite (bool_decide_eq_false_2 (sint.Z (W64 j) < sint.Z cbs_sl.(slice.len))%Z); last word.
      have Hjeq : j = length cbs by lia.
      wp_auto.
      unfold for_map_postcondition. iRight. iLeft. iSplitR; first done.
      iExists (done ∪ {[key]}), key.
      iFrame "ty tr s Htr Hinsert Hdelete Hstore Hobserversmap Hobserversauth".
      iSplitR; first (iPureIntro; split; [symmetry; exact Hdone' | lia]).
      rewrite (big_sepM2_delete _ _ _ key cbs_sl entry Hrkey Hdkey).
      iSplitL "Hentry_slice Hentry_cap Htold".
      { rewrite decide_True; last (apply elem_of_union_r; by apply elem_of_singleton).
        iExists cbs. iFrame "Hentry_slice Hentry_cap".
        rewrite Hjeq (take_ge cbs (length cbs)); last lia.
        rewrite (take_ge entry.2 (length cbs)); last lia.
        iFrame "Htold". }
      iApply (type_observers_told_grow with "Hobservers"). apply lookup_delete_eq. }
  (* ---- every changed type told: the registry is at the end state ---- *)
  iIntros "HP". iDestruct "HP" as (done tyv) "HP". iNamed "HP". destruct Hdone as [Hdone _].
  have Hdoneall : done = changed_locs.
  { rewrite Hdone Nat2Z.id -Hkeyslen take_ge; [exact Hkeysdom | lia]. }
  iDestruct "Hstore" as (client k pdel locs p bind acc observers_mref0) "Hown". iNamed "Hown".
  iDestruct (registered_bindings_lookup with "HtypesAuth Hregistered_bind") as %Hregbind.
  iDestruct (changed_types_bound_names with "HtypesAuth Hchanged_bound") as %Hbound.
  iDestruct (own_store_state_registry_coh with "Hstate") as %Hregcoh.
  iDestruct (own_store_state_run_pool_invs with "Hstate") as %Hpoolinv.
  simpl in Hregcoh, Hpoolinv.
  wp_auto.
  iApply "HΦ".
  iSplitL "Hstate Hseq HtypesAuth Hhist Hacc Hdelete_set Hobserversf".
  { iExists client, k, pdel, locs, p, bind, acc, observers_mref0. iFrame "∗#". iPureIntro.
    split_and!; [exact Hclientc | exact Hpendroot | exact Hpendbnd | exact Hregmodel | exact Hhcoh | exact Hctr | exact Hacccoh | exact Hdeleted]. }
  iExists observers_mref, registry, registered.
  iFrame "Hregistrypin Hobserversmap Hobserversauth Hregistered_bind".
  iApply (big_sepM2_mono with "Hobservers"). iIntros (parent cbs_sl entry Hr Hd) "H".
  destruct (decide (parent ∈ done)) as [Hin | Hnin]; first iExact "H".
  rewrite (type_snapshot_untouched m deleted inserted tombstoned m0 deleted0 entry.1 Hstart); first iExact "H".
  apply (type_untouched_by_record m bind p inserted tombstoned changed changed_locs entry.1 parent
           Hpoolinv Hregcoh Hregmodel Hrecorded Hbound (Hregbind parent entry Hd)).
  rewrite -Hdoneall. exact Hnin.
Qed.

End store_notify.