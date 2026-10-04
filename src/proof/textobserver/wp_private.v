(** The unexported helpers of [TextObserver.Poll] (issue #198).

    - [wp_deltaSnoc]: append one entry to a delta, merging it into a
      same-kind last entry: the model's [delta_snoc].
    - [wp_TextObserver__deletedContains]: whether a char is in the
      observer's deleted-span map: membership in the ids the map denotes. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core.
From New.proof Require Import algebra.
From New.proof Require Import prelude.
From New.proof Require Import history.
From New.proof.sync_proof Require Import mutex.
From iris.algebra Require Import auth gmap gset.
From iris.algebra.lib Require Import dfrac_agree.
From New.proof.id Require Import id.
From New.proof.item Require Import item.
From New.proof.ytype Require Import ytype.
From New.proof.store Require Import store.
From New.proof.text Require Import text.
From New.proof.delta Require Import delta.
From New.proof.textobserver Require Import model value heap.

Section text_observer.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Context {sync_pkg : sync.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.

Context {seq_inG : inG Σ (authR (gmapUR loc (gsetUR (YjsItem A))))}.

Context {acc_inG : inG Σ (authR (gsetUR YjsId))}.

Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO addressed_pool))}.
(* the observers' tokens and registrations (issue #198 Part II), as [store/heap] *)
Context {observed_inG : ghost_varG Σ (list (YjsItem go_string * bool))}.
Context {observers_inG : inG Σ (authR (gsetUR (gname * go_string)))}.

Local Notation P := go_string.

Lemma wp_TextObserver__deletedContains (obs : loc) (dq : dfrac) (ov : yjs.TextObserver.t)
    (deleted_ids : gset YjsId) (client clock : w64) :
  {{{ is_pkg_init yjs ∗ obs ↦{dq} ov ∗
      own_deleted_spans ov.(yjs.TextObserver.deleted') deleted_ids }}}
    obs @! (go.PointerType yjs.TextObserver) @! "deletedContains" #client #clock
  {{{ RET #(bool_decide (MkYjsId (uint.nat client) (uint.nat clock) ∈ deleted_ids));
      obs ↦{dq} ov ∗ own_deleted_spans ov.(yjs.TextObserver.deleted') deleted_ids }}}.
Proof.
  wp_start as "[Hobs Hdel]". iNamed "Hdel".
  wp_auto.
  wp_apply (wp_map_lookup1 with "Hdm"). iIntros "Hdm".
  wp_auto.
  iDestruct (big_sepM2_lookup_iff with "Hspans") as %Hiff.
  (* the client's span list: the slice in the map, or the nil slice *)
  iAssert (∃ (ssl : slice.t) (sps : list (yjs.span.t w64)) (q : dfrac),
    ⌜default slice.nil (dm !! client) = ssl⌝ ∗
    ⌜∀ sp, sp ∈ sps <-> ∃ sps', spans !! client = Some sps' ∧ sp ∈ sps'⌝ ∗
    ssl ↦*{q} sps ∗
    (ssl ↦*{q} sps -∗ [∗ map] sl;sps ∈ dm;spans, sl ↦* sps ∗ own_slice_cap (yjs.span.t w64) sl (DfracOwn 1)))%I
    with "[Hspans]" as (ssl sps q Hssl Hlink) "[Hsl Hback]".
  { destruct (dm !! client) as [ssl |] eqn:Hdmc.
    - have [sps Hspc] : is_Some (spans !! client) by apply Hiff; eauto.
      iDestruct (big_sepM2_insert_acc _ _ _ client ssl sps Hdmc Hspc with "Hspans") as "[[Hsl Hslcap] Hback]".
      iExists ssl, sps, (DfracOwn 1). iFrame "Hsl". iSplitR; first done.
      iSplitR.
      { iPureIntro. move=> sp. split.
        - move=> Hin. exists sps. split; [exact Hspc | exact Hin].
        - intros (sps' & Hsps' & Hin). rewrite Hspc in Hsps'. injection Hsps' as <-. exact Hin. }
      iIntros "Hsl". iDestruct ("Hback" $! ssl sps with "[$Hsl $Hslcap]") as "Hspans".
      rewrite (insert_id dm client ssl Hdmc) (insert_id spans client sps Hspc). iFrame "Hspans".
    - have Hspc : spans !! client = None.
      { destruct (spans !! client) as [sps |] eqn:E; last done.
        exfalso. have Hsome : is_Some (dm !! client) by apply Hiff; eauto.
        rewrite Hdmc in Hsome. destruct Hsome as [? Habs]. discriminate. }
      iExists slice.nil, [], (DfracOwn 1). iSplitR; first done.
      iSplitR.
      { iPureIntro. move=> sp. split.
        - move=> Hin. exfalso. by apply elem_of_nil in Hin.
        - intros (sps' & Hsps' & _). rewrite Hspc in Hsps'. discriminate. }
      iSplitR; first iApply own_slice_nil.
      iIntros "_". iFrame "Hspans". }
  rewrite Hssl.
  iDestruct (own_slice_len with "Hsl") as %[Hsllen Hsllen0].
  (* the scan: no span before [i] covers the char *)
  iAssert (∃ (i : nat),
    "Hi" ∷ i_ptr ↦ W64 i ∗
    "Hsl" ∷ ssl ↦*{q} sps ∗
    "Hspans_ptr" ∷ spans_ptr ↦ ssl ∗
    "Hclock" ∷ clock_ptr ↦ clock ∗
    "%Hile" ∷ ⌜(i <= length sps)%nat⌝ ∗
    "%Hnone" ∷ ⌜∀ j sp, (j < i)%nat -> sps !! j = Some sp ->
                 ¬ span_covers client sp (MkYjsId (uint.nat client) (uint.nat clock))⌝)%I
    with "[i Hsl spans clock]" as "IH".
  { iExists 0%nat. iFrame "i Hsl spans clock". iPureIntro. split; [lia | intros; lia]. }
  wp_for "IH".
  destruct (decide (i < length sps)%nat) as [Hlt | Hge].
  - rewrite (bool_decide_eq_true_2 (sint.Z (W64 i) < sint.Z ssl.(slice.len))%Z); last word.
    destruct (lookup_lt_is_Some_2 sps i Hlt) as [sp Hsp].
    wp_auto.
    rewrite decide_True; last word.
    iDestruct (own_slice_elem_acc (sint.Z (W64 i)) sp ssl q sps with "Hsl") as "[Hel Hgive]".
    { word. }
    { replace (Z.to_nat (sint.Z (W64 i))) with i by word. exact Hsp. }
    wp_auto.
    iDestruct ("Hgive" $! sp with "Hel") as "Hsl".
    rewrite list_insert_id; last (replace (Z.to_nat (sint.Z (W64 i))) with i by word; exact Hsp).
    destruct (decide (uint.Z sp.(yjs.span.start') ≤ uint.Z clock)%Z) as [Hlo | Hlo]; last first.
    { rewrite (bool_decide_eq_false_2 (uint.Z sp.(yjs.span.start') ≤ uint.Z clock)%Z Hlo).
      wp_auto. wp_for_post.
      iFrame "Hobs HΦ Hdm Hback". iExists (S i).
      replace (w64_word_instance.(word.add) (W64 i) (W64 1)) with (W64 (S i)) by word.
      iFrame "Hi Hsl Hspans_ptr Hclock". iPureIntro. split; first lia.
      move=> j sp0 Hj Hsp0. destruct (decide (j = i)) as [-> | Hne].
      - rewrite Hsp in Hsp0. injection Hsp0 as <-. move=> [_ [Hlo' _]]. simpl in Hlo'. apply Hlo. word.
      - apply (Hnone j sp0); [lia | exact Hsp0]. }
    rewrite (bool_decide_eq_true_2 (uint.Z sp.(yjs.span.start') ≤ uint.Z clock)%Z Hlo).
    wp_auto.
    destruct (decide (uint.Z clock < uint.Z sp.(yjs.span.end'))%Z) as [Hhi | Hhi]; last first.
    { rewrite (bool_decide_eq_false_2 (uint.Z clock < uint.Z sp.(yjs.span.end'))%Z Hhi).
      wp_auto. wp_for_post.
      iFrame "Hobs HΦ Hdm Hback". iExists (S i).
      replace (w64_word_instance.(word.add) (W64 i) (W64 1)) with (W64 (S i)) by word.
      iFrame "Hi Hsl Hspans_ptr Hclock". iPureIntro. split; first lia.
      move=> j sp0 Hj Hsp0. destruct (decide (j = i)) as [-> | Hne].
      - rewrite Hsp in Hsp0. injection Hsp0 as <-. move=> [_ [_ Hhi']]. simpl in Hhi'. apply Hhi. word.
      - apply (Hnone j sp0); [lia | exact Hsp0]. }
    rewrite (bool_decide_eq_true_2 (uint.Z clock < uint.Z sp.(yjs.span.end'))%Z Hhi).
    wp_auto. wp_for_post.
    (* a hit: the char is covered, so it is a deleted id *)
    have Hd : MkYjsId (uint.nat client) (uint.nat clock) ∈ deleted_ids.
    { apply Hcover. destruct (proj1 (Hlink sp) (list_elem_of_lookup_2 _ _ _ Hsp)) as (sps' & Hsps' & Hin).
      exists client, sps', sp. split_and!; [exact Hsps' | exact Hin |].
      split_and!; [reflexivity | simpl; word | simpl; word]. }
    rewrite (bool_decide_eq_true_2 _ Hd).
    iApply "HΦ". iFrame "Hobs". iExists dm, spans. iFrame "Hdm".
    iSplitL; [iApply "Hback"; iFrame "Hsl" | done].
  - rewrite (bool_decide_eq_false_2 (sint.Z (W64 i) < sint.Z ssl.(slice.len))%Z); last word.
    wp_auto.
    (* no span covers the char: it is not a deleted id (a cover would be a
       span of THIS client's list, which the scan visited) *)
    have Hnd : MkYjsId (uint.nat client) (uint.nat clock) ∉ deleted_ids.
    { move=> Hd. apply Hcover in Hd. destruct Hd as (client' & sps' & sp' & Hsps' & Hin' & Hcov').
      have Hcl : client' = client.
      { destruct Hcov' as [Hc _]. simpl in Hc. word. }
      subst client'.
      have Hin : sp' ∈ sps by apply Hlink; exists sps'.
      apply list_elem_of_lookup_1 in Hin as [j Hj].
      have Hjlt : (j < length sps)%nat := lookup_lt_Some _ _ _ Hj.
      exact (Hnone j sp' ltac:(lia) Hj Hcov'). }
    rewrite (bool_decide_eq_false_2 _ Hnd).
    iApply "HΦ". iFrame "Hobs". iExists dm, spans. iFrame "Hdm".
    iSplitL; [iApply "Hback"; iFrame "Hsl" | done].
Qed.

End text_observer.
