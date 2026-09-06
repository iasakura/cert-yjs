(** Text handle: the top-level [wp_Text__Insert] (lock-based per-byte
    Integrate loop at run granularity over [own_store_runs], one op
    certificate per inserted item). Split out of [text/text]; shares
    [is_Text] etc. via [text/heap]. *)
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
From New.proof.store Require Import store.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
From New.proof.sync_proof Require Import mutex.
From iris.algebra Require Import auth gmap gset.
From iris.algebra.lib Require Import dfrac_agree.
From stdpp Require Import sorting.
From New.proof.text Require Import heap.

(* iris.algebra / stdpp.sorting push [nat_scope], retuning the default [<] / [≤];
   the verified word-arithmetic proofs write [Z] comparisons unannotated, so
   restore [Z_scope] as the default. *)
Local Open Scope Z_scope.

Section text.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.
(** Store lock = a [sync.RWMutex] (write path here, via [wp_Store__wlock] /
    [wp_Store__wunlock]); the per-text item set lives in a grow-only auth
    (the same RA as [store/store], used by [is_type_lb]). *)
Context {sync_pkg : sync.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.
Context {seq_inG : inG Σ (authR (gmapUR loc (gsetUR (YjsItem A))))}.
Context {acc_inG : inG Σ (authR (gsetUR YjsId))}.
(* [is_Store]'s reader-count accounting ties the readers' share to the store's
   [types] map via a [dfrac_agree]; threaded here so [is_Text]/[is_Store] uses
   in this file (Insert/Delete/Len) can discharge the instance. *)
Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO addressed_pool))}.

(* The ghost op-history types at the document content type; type names are Go
   strings (issue #49). *)
Local Notation P := go_string.
Local Notation TId := (TypeId P).
Local Notation Op := (TId * @YjsOperation A)%type.
Local Notation Ev := (@Event Op).
Local Notation DocModel := (gmap TId (list (YjsItem A))).

Lemma wp_Text__Insert (t : loc) (idx : w64) (cs : go_string) (γs : store_names) (γh : history_names)
    (name : P) (L : list (YjsItem A)) :
  {{{ is_pkg_init yjs ∗ is_Text t γs γh name L }}}
    t @! (go.PointerType yjs.Text) @! "Insert" #idx #cs
  {{{ (L' ins : list (YjsItem A)) (client k0 : nat) (originLeft originRight : YjsPtr A), RET #();
      is_Text t γs γh name L' ∗
      ⌜inserted_run L L' ins cs client k0 originLeft originRight⌝ ∗
      (* the op certificates: one broadcast fragment per inserted item
         (issues #42/#49; the doc-level op an item denotes is
         [(RootId name, OpInsert (input_of_item it))]) *)
      ([∗ list] it ∈ ins,
         is_op_cert γh (RootId name, OpInsert (input_of_item it))) }}}.
Proof.
  (* ---- Prologue: take the store lock, extract THIS text. ---- *)
  wp_start as "Hpre". iNamed "Hpre".
  iDestruct "His_store" as "#His_store".
  wp_auto.
  subst s_loc.
  wp_apply (wp_Store__wlock with "[$His_store]"). iIntros "[Hlk Hinv]".
  iDestruct "Hinv" as (c0 h m pend) "Hown".
  iDestruct "Hown" as (client k pdel locs0 p0 bind acc) "Hown". iNamed "Hown". subst c0.
  iDestruct (own_store_runs_registry_coh with "Hcells") as %Hreg.
  iDestruct (own_store_runs_aligned with "Hcells") as %Haligned.
  iDestruct (own_store_runs_run_wf with "Hcells") as %Hwf0.
  have [Hbindtypes [Hbindinj Htypesbound]] := Hreg.
  have [Hmtypes Hmdom] := Hregmodel.
  (* snapshot the lock-time history: only appends happen under the lock, so at
     Unlock the accepted-set coherence transports across the (grown) history *)
  iDestruct (own_client_history_lb with "Hhist") as "[Hhist #Hlb_h]".
  iDestruct (auth_gmap_gset_lookup with "Hseq His_lb") as %(S' & HmS & HLsub).
  rewrite lookup_fmap in HmS.
  apply fmap_Some in HmS as (ts & Htsp & ->).
  (* the registry binds [name] to this text, so the history's [RootId name]
     component is exactly this text's document (issue #49) *)
  iDestruct (ghost_map_lookup with "HtypesAuth Hbind") as %Hbindlk.
  have Hmt : doc_model_get m (RootId name) = tm_arr ts := Hmtypes name parent ts Hbindlk Htsp.
  subst parent.
  iRename "Hcells" into "Hruns".
  set (runs0 := tm_runs ts).
  have Hp0 : p0 !! tv.(yjs.Text.inner') = Some (MkTypeModel runs0 ts.(tm_arr)).
  { rewrite /runs0. destruct ts; exact Htsp. }
  have [ls0 Hl0] : ∃ ls0, locs0 !! tv.(yjs.Text.inner') = Some ls0.
  { apply elem_of_dom. rewrite (proj1 Haligned). apply elem_of_dom. by exists ts. }
  have Hlsl0 : length ls0 = length runs0 := proj2 Haligned _ _ _ Hl0 Htsp.
  (* the type's [len] field *)
  iDestruct (own_store_runs_ytype_acc tv.(yjs.Text.store') (MkStoreStateRuns client k locs0 p0 bind pend pdel) tv.(yjs.Text.inner') ls0 (MkTypeModel runs0 ts.(tm_arr)) Hl0 Hp0 with "Hruns") as "[Hyt Hytback]".
  iDestruct "Hyt" as (yt0 tl0) "(Hparent & Hdll & %Hlen & %Hrepr)".
  wp_auto.
  case_bool_decide as Hbound.
  { (* ---- out-of-range: index past the visible length, nothing inserted. ---- *)
    wp_auto.
    iAssert (own_ytype_runs tv.(yjs.Text.inner') (DfracOwn 1) ls0 (MkTypeModel runs0 ts.(tm_arr)))
      with "[Hparent Hdll]" as "Hyt".
    { iExists yt0, tl0. iFrame "Hparent Hdll". iPureIntro. split; [exact Hlen | exact Hrepr]. }
    iDestruct ("Hytback" with "Hyt") as "Hruns".
    wp_apply (wp_Store__wunlock _ _ _ (uint.nat client) h m pend
                with "[$His_store $Hlk Hruns Hseq HtypesAuth Hhist Hacc Hdelete_set]").
    { iExists client, k, pdel, locs0, p0, bind, acc.
      iFrame "∗#". iPureIntro.
      split_and!;
        [reflexivity | exact Hpendroot | exact Hpendbnd | exact Hregmodel | exact Hhcoh
        | exact Hctr | exact Hacccoh]. }
    iApply ("HΦ" $! L [] 0%nat 0%nat First Last).
    iSplit.
    { iExists tv, tv.(yjs.Text.store'), tv.(yjs.Text.inner').
      iFrame "Ht His_store His_hist Hbind His_lb". iPureIntro. split_and!; [reflexivity | reflexivity | exact Hsorted]. }
    iSplit.
    { iPureIntro. split_and!; [reflexivity | left; reflexivity |].
      intros i it b Hii. rewrite lookup_nil in Hii. inversion Hii. }
    rewrite big_sepL_nil. done. }
  (* ---- in-range: insert one 1-char item per byte. ---- *)
  iAssert (own_ytype_runs tv.(yjs.Text.inner') (DfracOwn 1) ls0 (MkTypeModel runs0 ts.(tm_arr)))
    with "[Hparent Hdll]" as "Hyt".
  { iExists yt0, tl0. iFrame "Hparent Hdll". iPureIntro. split; [exact Hlen | exact Hrepr]. }
  iDestruct ("Hytback" with "Hyt") as "Hruns".
  (* the clock-overflow guard reads the store's clock *)
  iDestruct (own_store_runs_clock_acc with "Hruns") as "[Hclock Hclockback]".
  iEval (simpl) in "Hclock".
  wp_auto.
  wp_apply strings.wp_string_len. iIntros "%Hlcb".
  wp_auto.
  case_bool_decide as Hovf.
  { (* clock-overflow guard fired: nothing inserted (like OOB). *)
    wp_auto.
    iDestruct ("Hclockback" with "Hclock") as "Hruns".
    iEval (simpl) in "Hruns".
    wp_apply (wp_Store__wunlock _ _ _ (uint.nat client) h m pend
                with "[$His_store $Hlk Hruns Hseq HtypesAuth Hhist Hacc Hdelete_set]").
    { iExists client, k, pdel, locs0, p0, bind, acc.
      iFrame "∗#". iPureIntro.
      split_and!;
        [reflexivity | exact Hpendroot | exact Hpendbnd | exact Hregmodel | exact Hhcoh
        | exact Hctr | exact Hacccoh]. }
    iApply ("HΦ" $! L [] 0%nat 0%nat First Last).
    iSplit.
    { iExists tv, tv.(yjs.Text.store'), tv.(yjs.Text.inner').
      iFrame "Ht His_store His_hist Hbind His_lb". iPureIntro. split_and!; [reflexivity | reflexivity | exact Hsorted]. }
    iSplit.
    { iPureIntro. split_and!; [reflexivity | left; reflexivity |].
      intros i it b Hii. rewrite lookup_nil in Hii. inversion Hii. }
    rewrite big_sepL_nil. done. }
  (* no overflow: the run fits. *)
  have Hnoof : (uint.Z k + Z.of_nat (length cs) < 2^64)%Z by word.
  iDestruct ("Hclockback" with "Hclock") as "Hruns".
  iEval (simpl) in "Hruns".
  wp_auto.
  iDestruct (own_store_runs_ytype_acc tv.(yjs.Text.store') (MkStoreStateRuns client k locs0 p0 bind pend pdel) tv.(yjs.Text.inner') ls0 (MkTypeModel runs0 ts.(tm_arr)) Hl0 Hp0 with "Hruns") as "[Hyt Hytback]".
  wp_apply (wp_yType__findPos tv.(yjs.Text.inner') (DfracOwn 1) ls0 (MkTypeModel runs0 ts.(tm_arr)) idx with "[$Hyt]").
  iIntros (leftNode rightNode p off) "(Hyt & %Hfp)".
  iDestruct ("Hytback" with "Hyt") as "Hruns".
  simpl in Hfp.
  destruct Hfp as (Hpbound & Hlftloc & Hrgtloc & Hoff).
  wp_auto.
  (* normalize the position (issue #28 M3): when the index lands inside a
     multi-char run, split the straddled node at the offset so the insertion
     point sits on a run boundary. The flatten is unchanged, so only the
     address list, the run list and the cursor move; both branches rebind
     the state under the shared boundary-form names. *)
  wp_if_join (λ v : val, ⌜v = execute_val⌝ ∗
      ∃ (locs1 : gmap loc (list loc)) (p1 : pool) (ls1 : list loc) (runs1 : list ItemRun) (p1i : nat),
      "s" ∷ s_ptr ↦ tv.(yjs.Text.store') ∗
      "Hruns" ∷ own_store_runs tv.(yjs.Text.store') (MkStoreStateRuns client k locs1 p1 bind pend pdel) ∗
      "left" ∷ left_ptr ↦ loc_at ls1 (Z.of_nat p1i - 1) ∗
      "right" ∷ right_ptr ↦ loc_at ls1 (Z.of_nat p1i) ∗
      "%Hp1" ∷ ⌜p1 !! tv.(yjs.Text.inner') = Some (MkTypeModel runs1 ts.(tm_arr))⌝ ∗
      "%Hl1" ∷ ⌜locs1 !! tv.(yjs.Text.inner') = Some ls1⌝ ∗
      "%Hdomp1" ∷ ⌜∀ q, q ≠ tv.(yjs.Text.inner') → p1 !! q = p0 !! q⌝ ∗
      "%Hdoml1" ∷ ⌜∀ q, q ≠ tv.(yjs.Text.inner') → locs1 !! q = locs0 !! q⌝ ∗
      "%Hpb1" ∷ ⌜(p1i <= length runs1)%nat⌝ ∗
      "%Hlr1" ∷ ⌜pool_after_delete p0 p1⌝)%I
      with "[s left right offset Hruns]".
  { (* offset > 0: split [left] at the offset *)
    destruct Hoff as [Hoffeq | (Hoffpos & Hpge1 & (r & Hr & Hrdel & Hofflen))];
      first (exfalso; subst off; move: l; word).
    have Hdiffb : (0 < uint.nat off < length (run_items r))%nat by word.
    have Hrmem0 : r ∈ all_runs p0.
    { apply elem_of_all_runs. exists tv.(yjs.Text.inner'), (MkTypeModel runs0 ts.(tm_arr)).
      split; [exact Hp0 | exact (list_elem_of_lookup_2 _ _ _ Hr)]. }
    have Hrlt : (p - 1 < length ls0)%nat by (rewrite Hlsl0; exact (lookup_lt_Some _ _ _ Hr)).
    have Hlk : ls0 !! (p - 1)%nat = Some (loc_at ls0 (Z.of_nat p - 1)).
    { rewrite /loc_at decide_True; last lia.
      have -> : Z.to_nat (Z.of_nat p - 1) = (p - 1)%nat by lia.
      destruct (ls0 !! (p - 1)%nat) as [l0|] eqn:Hl0k; [done | apply lookup_ge_None in Hl0k; lia]. }
    wp_apply (wp_store__splitNode_runs tv.(yjs.Text.store') (MkStoreStateRuns client k locs0 p0 bind pend pdel)
                tv.(yjs.Text.inner') (loc_at ls0 (Z.of_nat p - 1)) ls0 (MkTypeModel runs0 ts.(tm_arr)) (p - 1)%nat r off
                Hp0 Hl0 Hr Hlk Hdiffb with "[$Hruns]").
    iIntros (rloc) "(Hruns & %Hrlocfresh)".
    iEval (simpl) in "Hruns".
    wp_auto.
    set (runs1 := split_runs runs0 (p - 1)%nat (uint.nat off)).
    set (ls1 := split_locs ls0 (p - 1)%nat rloc).
    have Hll1 : ls1 !! (p - 1)%nat = Some (loc_at ls0 (Z.of_nat p - 1))
      := split_locs_lookup_left ls0 (p - 1)%nat rloc _ Hlk.
    have Hlr1 : ls1 !! p = Some rloc.
    { have H := split_locs_lookup_right ls0 (p - 1)%nat rloc _ Hlk.
      have -> : p = S (p - 1)%nat by lia. exact H. }
    have Hlen1 : length runs1 = S (length runs0) := split_runs_length runs0 (p - 1)%nat (uint.nat off) r Hr.
    have Hleftloc1 : loc_at ls0 (Z.of_nat p - 1) = loc_at ls1 (Z.of_nat p - 1).
    { rewrite {2}/loc_at decide_True; last lia.
      have -> : Z.to_nat (Z.of_nat p - 1) = (p - 1)%nat by lia.
      rewrite Hll1 //. }
    have Hrightloc1 : rloc = loc_at ls1 (Z.of_nat p).
    { rewrite /loc_at decide_True; last lia. rewrite Nat2Z.id Hlr1 //. }
    iSplitR; first done.
    iExists (<[tv.(yjs.Text.inner') := ls1]> locs0), (<[tv.(yjs.Text.inner') := MkTypeModel runs1 ts.(tm_arr)]> p0), ls1, runs1, p.
    iEval (rewrite Hleftloc1) in "left". iEval (rewrite Hrightloc1) in "right".
    iFrame "s Hruns left right".
    iPureIntro. split_and!.
    - apply lookup_insert_eq.
    - apply lookup_insert_eq.
    - move=> q Hne. rewrite lookup_insert_ne //.
    - move=> q Hne. rewrite lookup_insert_ne //.
    - rewrite Hlen1. lia.
    - apply pool_after_split_delete with (parent := tv.(yjs.Text.inner')) (k := (p - 1)%nat).
      rewrite /runs1.
      exact (pool_after_split_of_split_runs p0 tv.(yjs.Text.inner') (MkTypeModel runs0 ts.(tm_arr))
               (p - 1)%nat (uint.nat off) r Hp0 Hr (Hwf0 r Hrmem0) Hdiffb). }
  { (* offset = 0: the index already sits on a boundary *)
    have Hoffeq : off = W64 0.
    { destruct Hoff as [-> | (Hoffpos & _)]; [done | exfalso; apply n; word]. }
    subst off.
    iSplitR; first done.
    iExists locs0, p0, ls0, runs0, p.
    iFrame "s Hruns left right".
    iPureIntro. split_and!;
      [exact Hp0 | exact Hl0 | move=> q _; reflexivity | move=> q _; reflexivity
      | exact Hpbound | exact (pool_after_delete_refl p0)]. }
  iIntros (v) "[%Hv HQ]". subst v. iNamed "HQ".
  clear Hoff Hbound Hovf Hlen Hrepr yt0 tl0.
  (* the store's readings of the normalized type *)
  iDestruct (own_store_runs_arr with "Hruns") as %Harrs1.
  have Harr1 : ts.(tm_arr) = runs_flatten runs1 := Harrs1 _ _ Hp1.
  iDestruct (own_store_runs_arr_inv with "Hruns") as %Harrinvs1.
  have Hinvarr : YjsArrInvariant ts.(tm_arr) := Harrinvs1 _ _ Hp1.
  iDestruct (own_store_runs_run_wf with "Hruns") as %Hwfall1.
  have Hwf1 : ∀ r, r ∈ runs1 -> run_wf (run_items r).
  { move=> r Hr. apply Hwfall1. apply elem_of_all_runs.
    exists tv.(yjs.Text.inner'), (MkTypeModel runs1 ts.(tm_arr)). split; [exact Hp1 | exact Hr]. }
  have Hnec1 : Forall (λ r, run_items r ≠ []) runs1.
  { apply Forall_forall. move=> r Hr. exact (proj1 (Hwf1 r Hr)). }
  iDestruct (own_store_runs_aligned with "Hruns") as %Hal1.
  have Hlsl1 : length ls1 = length runs1.
  { destruct (locs_aligned_lens _ _ Hal1 tv.(yjs.Text.inner') _ Hp1) as (ls' & Hls' & Hlen').
    simpl in Hls'. rewrite Hl1 in Hls'. injection Hls' as <-. exact Hlen'. }
  (* the tombstone-set invariant follows the normalization: a split only
     refines the live cells (plan-delete-set.md section 3) *)
  iDestruct (own_delete_set_runs_refine γs m p0 p1 (proj1 (proj2 (proj2 Hlr1))) with "Hdelete_set") as "Hdelete_set".
  (* [client := s.client] *)
  iDestruct (own_store_runs_client_acc with "Hruns") as "[Hclient Hclientback]".
  iEval (simpl) in "Hclient".
  wp_auto.
  iDestruct ("Hclientback" with "Hclient") as "Hruns".
  (* the model position of the run boundary [p1i] *)
  have [mp Hmpdef] : ∃ mp0 : nat, mp0 = length (runs_flatten (take p1i runs1))
    by (eexists; reflexivity).
  (* shared right origin *)
  wp_if_join (λ v : val, ⌜v = execute_val⌝ ∗ ∃ (oRptr : loc) (in_rO : option yjs.id.t),
      "HoR" ∷ originRightId_ptr ↦ oRptr ∗ "HisR" ∷ is_origin_id oRptr in_rO ∗
      "Hruns" ∷ own_store_runs tv.(yjs.Text.store') (MkStoreStateRuns client k locs1 p1 bind pend pdel) ∗
      "Hright" ∷ right_ptr ↦ loc_at ls1 (Z.of_nat p1i) ∗
      "%Hrightinit" ∷ ⌜(in_rO = None ∧ (p1i = length runs1)%nat) ∨
        (∃ (ri : YjsItem A) (rightOriginId : yjs.id.t), ts.(tm_arr) !! mp = Some ri ∧ in_rO = Some rightOriginId ∧ item_id ri = toYjsId rightOriginId)⌝)%I
      with "[right Hruns originRightId]".
  { iSplitR; [done|].
    destruct (decide (p1i = length runs1)%nat) as [Hpeq|Hne].
    - iExists null, None. iFrame "originRightId right Hruns".
      iSplit; [by rewrite /is_origin_id | iPureIntro; left; split; [reflexivity | exact Hpeq]].
    - have Hlt : (p1i < length runs1)%nat by lia.
      destruct (runs1 !! p1i) as [rr|] eqn:Hrr; [| apply lookup_ge_None in Hrr; lia].
      destruct (ls1 !! p1i) as [lr|] eqn:Hlr; [| apply lookup_ge_None in Hlr; lia].
      iDestruct (own_store_runs_node_acc _ (MkStoreStateRuns _ _ _ _ _ _ _) _ _ _ _ _ _ Hl1 Hp1 Hlr Hrr with "Hruns") as (itemVal) "H".
      iNamed "H".
      iDestruct (typed_pointsto_not_null with "Haccval") as %Hnn.
      exfalso. apply Hnn. rewrite -e /loc_at decide_True; last lia. rewrite Nat2Z.id Hlr //. }
  { have Hposlt : (p1i < length runs1)%nat.
    { destruct (decide (p1i < length runs1)%nat) as [Hlt|Hge]; [exact Hlt|exfalso].
      apply n. rewrite /loc_at decide_True; [|lia].
      have Hpe : (p1i = length runs1)%nat by lia.
      rewrite Hpe Nat2Z.id lookup_ge_None_2; [done|lia]. }
    destruct (runs1 !! p1i) as [rr|] eqn:Hrr; [| apply lookup_ge_None in Hrr; lia].
    destruct (ls1 !! p1i) as [lr|] eqn:Hlr; [| apply lookup_ge_None in Hlr; lia].
    have Hlrloc : loc_at ls1 (Z.of_nat p1i) = lr.
    { rewrite /loc_at decide_True; last lia. rewrite Nat2Z.id Hlr //. }
    iDestruct (own_store_runs_node_acc _ (MkStoreStateRuns _ _ _ _ _ _ _) _ _ _ _ _ _ Hl1 Hp1 Hlr Hrr with "Hruns") as (itemVal) "H".
    iNamed "H".
    iEval (rewrite -Hlrloc) in "Haccval".
    wp_load. wp_pures. wp_store.
    iDestruct (typed_pointsto_not_null with "rid") as %Hridnn.
    iPersist "rid".
    wp_auto.
    iEval (rewrite Hlrloc) in "Haccval".
    iDestruct ("Haccback" with "Haccval") as "Hruns".
    iSplitR; [done|].
    iExists rid_ptr, (Some itemVal.(yjs.item.id')).
    iFrame "originRightId right Hruns".
    iSplitR.
    { rewrite /is_origin_id. iSplit; [iPureIntro; exact Hridnn | iFrame "rid"]. }
    iPureIntro. right. exists (run_head_item rr), itemVal.(yjs.item.id').
    split_and!; [| reflexivity | exact Haccid].
    try rewrite Hmpdef.
    apply (runs_head_at_prefix runs1 _ p1i rr Harr1 Hrr).
    exact (proj1 (Hwf1 rr (list_elem_of_lookup_2 _ _ _ Hrr))). }
  iIntros (v) "[%Hv HQ]". subst v. iNamed "HQ". wp_auto.
  (* fix the run's shared right origin and the first item's left origin as values *)
  assert (∃ (originRight : YjsPtr A),
     (in_rO = None ∧ originRight = Last ∧ (mp = length ts.(tm_arr))%nat) ∨
     (∃ (ri : YjsItem A) (rightOriginId : yjs.id.t), ts.(tm_arr) !! mp = Some ri ∧ in_rO = Some rightOriginId ∧ item_id ri = toYjsId rightOriginId ∧ originRight = itemPtr ri))
     as [originRight HoRspec].
  { destruct Hrightinit as [[Hn Hpe] | (ri & rightOriginId & Hria & Hrs & Hrid)].
    - exists Last. left. split_and!; [exact Hn | reflexivity |].
      rewrite Hmpdef Hpe take_ge; last lia. rewrite Harr1 //.
    - exists (itemPtr ri). right. exists ri, rightOriginId. split_and!; [exact Hria | exact Hrs | exact Hrid | reflexivity]. }
  have Hmple : (mp <= length ts.(tm_arr))%nat.
  { rewrite Hmpdef Harr1.
    have Htg : take (length runs1) runs1 = runs1 by (apply take_ge; lia).
    have := runs_flatten_take_length_le runs1 p1i (length runs1) Hpb1.
    rewrite Htg. lia. }
  have Hmp1 : (1 <= p1i)%nat -> (1 <= mp)%nat.
  { move=> Hp1i. rewrite Hmpdef.
    have := runs_flatten_take_length_lt runs1 0 p1i Hnec1 Hp1i Hpb1.
    rewrite take_0 runs_flatten_nil /=. lia. }
  assert (∃ (originLeft : YjsPtr A),
     (originLeft = First ∧ (p1i = 0)%nat) ∨
     (∃ (lr : ItemRun) (li : YjsItem A), (1 <= p1i)%nat ∧
        runs1 !! (p1i - 1)%nat = Some lr ∧
        run_items lr !! (length (run_items lr) - 1)%nat = Some li ∧
        ts.(tm_arr) !! (mp - 1)%nat = Some li ∧ originLeft = itemPtr li))
     as [originLeft HoLspec].
  { destruct (decide (p1i = 0)%nat) as [Hidx0 | Hidxpos].
    - exists First. left. split; [reflexivity | exact Hidx0].
    - have Hidxm : (p1i - 1 < length runs1)%nat by lia.
      destruct (runs1 !! (p1i - 1)%nat) as [lr|] eqn:Hlr0; [| apply lookup_ge_None in Hlr0; lia].
      have Hwflr : run_wf (run_items lr) := Hwf1 lr (list_elem_of_lookup_2 _ _ _ Hlr0).
      have Hlen1lr : (1 <= length (run_items lr))%nat.
      { destruct (run_items lr) eqn:Hrc; [exact (False_ind _ (proj1 Hwflr eq_refl)) | simpl; lia]. }
      destruct (lookup_lt_is_Some_2 (run_items lr) (length (run_items lr) - 1)%nat ltac:(lia)) as [lch Hlch].
      have Hpos := runs_flatten_lookup_of_run runs1 (p1i - 1)%nat _ lr lch Hlr0 Hlch.
      have Hpstep : length (runs_flatten (take p1i runs1))
                  = (length (runs_flatten (take (p1i - 1)%nat runs1)) + length (run_items lr))%nat.
      { have Hps : p1i = S (p1i - 1)%nat by lia.
        rewrite {1}Hps (runs_flatten_take_S _ _ _ Hlr0) length_app //. }
      exists (itemPtr lch). right. exists lr, lch. split_and!; [lia | reflexivity | exact Hlch | | reflexivity].
      rewrite Hmpdef Harr1.
      replace (length (runs_flatten (take p1i runs1)) - 1)%nat
        with (length (runs_flatten (take (p1i - 1)%nat runs1)) + (length (run_items lr) - 1))%nat
        by lia.
      exact Hpos. }
  (* loop invariant: [j] inserted so far, the type's runs and addresses grow by
     one unit run per item at the cursor, [ins] is the run; the ghost history
     [hj] grows by one mint per inserted item, staying coherent with [arr], and
     the certificates of the run accumulate in [Hcertsj]. The store is carried
     whole ([own_store_runs]); the delete-set ghost still speaks of the
     materialized cells until C6. *)
  iAssert (∃ (j : nat) (arr : list (YjsItem A)) (locsj : gmap loc (list loc)) (pj : pool)
             (lsj : list loc) (runsj : list ItemRun) (ins : list (YjsItem A)) (hj : list Ev),
    "Hi" ∷ i_ptr ↦ W64 j ∗
    "Htptr" ∷ t_ptr ↦ t ∗
    "Hcontentp" ∷ content_ptr ↦ cs ∗
    "Hclientp" ∷ client_ptr ↦ client ∗
    "HoRp" ∷ originRightId_ptr ↦ oRptr ∗
    "Hleftp" ∷ left_ptr ↦ loc_at lsj (Z.of_nat (p1i + j) - 1) ∗
    "Hsp" ∷ s_ptr ↦ tv.(yjs.Text.store') ∗
    "Hruns" ∷ own_store_runs tv.(yjs.Text.store') (MkStoreStateRuns client (W64 (uint.Z k + Z.of_nat j)) locsj pj bind pend pdel) ∗
    "Hlk" ∷ own_wlock γs ∗
    "Hdelete_set" ∷ own_delete_set_runs γs m (all_runs pj) ∗
    "Hseq" ∷ own γs.(sn_seq) (● ((λ tm : type_model, (list_to_set tm.(tm_arr) : gset (YjsItem A))) <$> p0) : authR (gmapUR loc (gsetUR (YjsItem A)))) ∗
    "HtypesAuth" ∷ ghost_map_auth γs.(sn_types) 1 bind ∗
    "Hrightp" ∷ right_ptr ↦ loc_at lsj (Z.of_nat (p1i + j)) ∗
    "%Hpj" ∷ ⌜pj !! tv.(yjs.Text.inner') = Some (MkTypeModel runsj arr)⌝ ∗
    "%Hlj" ∷ ⌜locsj !! tv.(yjs.Text.inner') = Some lsj⌝ ∗
    "%Hdompj" ∷ ⌜∀ q, q ≠ tv.(yjs.Text.inner') → pj !! q = p0 !! q⌝ ∗
    "%Hdomlj" ∷ ⌜∀ q, q ≠ tv.(yjs.Text.inner') → locsj !! q = locs0 !! q⌝ ∗
    "%Hinvj" ∷ ⌜YjsArrInvariant arr⌝ ∗
    "%Hlenarr" ∷ ⌜length arr = (length ts.(tm_arr) + j)%nat⌝ ∗
    "%Hrlensj" ∷ ⌜length runsj = (length runs1 + j)%nat⌝ ∗
    "%Hjle" ∷ ⌜(j <= length cs)%nat⌝ ∗
    "%Hctrj" ∷ ⌜∀ x : YjsItem A, ArrSet arr (itemPtr x) → clientId (item_id x) = uint.nat client → (clock (item_id x) < uint.nat k + j)%nat⌝ ∗
    "%Hleftj" ∷ ⌜(p1i + j = 0)%nat
      ∨ (∃ (lr : ItemRun) (li : YjsItem A),
           runsj !! (p1i + j - 1)%nat = Some lr ∧
           arr !! (mp + j - 1)%nat = Some li ∧
           run_items lr !! (length (run_items lr) - 1)%nat = Some li ∧ (1 <= p1i + j)%nat ∧
           (j = 0%nat → itemPtr li = originLeft) ∧ (∀ j', j = S j' → ins !! j' = Some li))⌝ ∗
    "%Hrightj" ∷ ⌜(in_rO = None ∧ originRight = Last ∧ (mp + j = length arr)%nat)
      ∨ (∃ (ri : YjsItem A) (rightOriginId : yjs.id.t),
           arr !! (mp + j)%nat = Some ri ∧ in_rO = Some rightOriginId ∧ item_id ri = toYjsId rightOriginId ∧ originRight = itemPtr ri)⌝ ∗
    "%Hinslen" ∷ ⌜length ins = j⌝ ∗
    "%Hins" ∷ ⌜∀ (i : nat) (it : YjsItem A), ins !! i = Some it →
       it ∈ arr ∧
       (∀ b : w8, cs !! i = Some b → content it = [b]) ∧
       item_id it = MkYjsId (uint.nat client) (uint.nat k + i)%nat ∧
       rightOrigin it = originRight ∧
       (i = 0%nat → origin it = originLeft) ∧
       (∀ (j' : nat) (itj : YjsItem A), i = S j' → ins !! j' = Some itj → origin it = itemPtr itj)⌝ ∗
    "%Hsubold" ∷ ⌜∀ x : YjsItem A, x ∈ ts.(tm_arr) → x ∈ arr⌝ ∗
    "%Hcoupj" ∷ ⌜length (runs_flatten (take (p1i + j)%nat runsj)) = (mp + j)%nat⌝ ∗
    "%Hpjb" ∷ ⌜(p1i + j <= length runsj)%nat⌝ ∗
    "Hhistj" ∷ own_client_history γh (uint.nat client) hj ∗
    "%Hhcohj" ∷ ⌜history_state_coh hj (<[RootId name := arr]> m)⌝ ∗
    "Hcertsj" ∷ ([∗ list] it ∈ ins,
                   is_op_cert γh (RootId name, OpInsert (input_of_item it)))
    )%I with "[i t content client HoR left s Hruns Hlk Hdelete_set Hseq HtypesAuth Hright Hhist]" as "IH".
  { iExists 0%nat, ts.(tm_arr), locs1, p1, ls1, runs1, [], h.
    replace (W64 (uint.Z k + Z.of_nat 0)) with k by word.
    rewrite !Nat.add_0_r.
    iFrame "i t content client HoR left s Hruns Hlk Hdelete_set Hseq HtypesAuth Hright Hhist".
    rewrite big_sepL_nil sep_emp.
    iPureIntro. split_and!.
    - exact Hp1.
    - exact Hl1.
    - exact Hdomp1.
    - exact Hdoml1.
    - exact Hinvarr.
    - lia.
    - lia.
    - lia.
    - intros x Hx Hc. have := Hctr tv.(yjs.Text.inner') ts x Htsp Hx Hc. lia.
    - destruct HoLspec as [[HoLF Hidx0] | (lr & li & Hge1 & Hlr0 & Hlast & Hli & HoLi)].
      + left. exact Hidx0.
      + right. exists lr, li. split_and!;
          [exact Hlr0 | exact Hli | exact Hlast | exact Hge1 | intros _; rewrite HoLi // | intros j' Hj'; lia].
    - destruct HoRspec as [(Hn & HoRl & Hidxlen) | (ri & rightOriginId & Hria & Hrs & Hrid & HoRi)].
      + left. split_and!; [exact Hn | exact HoRl | exact Hidxlen].
      + right. exists ri, rightOriginId. split_and!; [exact Hria | exact Hrs | exact Hrid | exact HoRi].
    - reflexivity.
    - intros i it Hii. rewrite lookup_nil in Hii. inversion Hii.
    - intros x Hx. exact Hx.
    - rewrite Hmpdef //.
    - exact Hpb1.
    - destruct Hhcoh as (sdoc & Hsd & Hmd). exists sdoc. split; [exact Hsd|].
      move=> t'. destruct (decide (t' = RootId name)) as [-> | Hne'].
      + rewrite docm_get_insert_eq (Hmd (RootId name)). exact Hmt.
      + rewrite docm_get_insert_ne //. }
  wp_for "IH".
  wp_apply strings.wp_string_len. iIntros "%Hlcb2". wp_auto. case_bool_decide as Hjlt.
  { (* loop body: integrate the [j]-th character *)
    have Hjpos : (j < length cs)%nat by word.
    rewrite decide_True; [| reflexivity].
    (* [clk := s.clock; s.clock = clk + 1] through the clock borrow *)
    iDestruct (own_store_runs_clock_acc with "Hruns") as "[Hclock Hclockback]".
    iEval (simpl) in "Hclock".
    wp_auto.
    iDestruct ("Hclockback" with "Hclock") as "Hruns".
    iEval (simpl) in "Hruns".
    (* the store's readings of the current type *)
    iDestruct (own_store_runs_run_wf with "Hruns") as %Hwfallj.
    have Hwfj : ∀ r, r ∈ runsj -> run_wf (run_items r).
    { move=> r Hr. apply Hwfallj. apply elem_of_all_runs.
      exists tv.(yjs.Text.inner'), (MkTypeModel runsj arr). split; [exact Hpj | exact Hr]. }
    have Hnecj : Forall (λ r, run_items r ≠ []) runsj.
    { apply Forall_forall. move=> r Hr. exact (proj1 (Hwfj r Hr)). }
    iDestruct (own_store_runs_run_pool_invs with "Hruns") as %Hrpj.
    iDestruct (own_store_runs_aligned with "Hruns") as %Halj.
    have Hlslj : length lsj = length runsj.
    { destruct (locs_aligned_lens _ _ Halj tv.(yjs.Text.inner') _ Hpj) as (ls' & Hls' & Hlen').
      simpl in Hls'. rewrite Hlj in Hls'. injection Hls' as <-. exact Hlen'. }
    (* left origin = current [left] (the previously inserted item, or findPos's left) *)
    wp_if_join (λ v : val, ⌜v = execute_val⌝ ∗
      ∃ (oLptr : loc) (olo : option yjs.id.t),
        "HoL" ∷ originLeftId_ptr ↦ oLptr ∗
        "HisL" ∷ is_origin_id oLptr olo ∗
        "Hruns" ∷ own_store_runs tv.(yjs.Text.store') (MkStoreStateRuns client (w64_word_instance.(word.add) (W64 (uint.Z k + Z.of_nat j)) (W64 1)) locsj pj bind pend pdel) ∗
        "Hleftp" ∷ left_ptr ↦ loc_at lsj (Z.of_nat (p1i + j) - 1) ∗
        "%Hleftspec" ∷ ⌜(olo = None ∧ (p1i + length ins = 0)%nat) ∨
           (∃ (li : YjsItem A), (1 <= p1i + length ins)%nat ∧ arr !! (mp + length ins - 1)%nat = Some li ∧ (toYjsId <$> olo) = Some (item_id li))⌝)%I
      with "[Hleftp Hruns originLeftId]".
    { destruct Hleftj as [Hpe0 | (lr & li & Hlrj & Hliarr & Hliitem & Hge1 & _)].
      - iSplitR; [done|]. iExists null, None. iFrame "originLeftId Hruns Hleftp".
        iSplit; [by rewrite /is_origin_id|]. iPureIntro. left. split; [reflexivity | exact Hpe0].
      - have Hlrlt : (p1i + length ins - 1 < length lsj)%nat by (rewrite Hlslj; exact (lookup_lt_Some _ _ _ Hlrj)).
        destruct (lsj !! (p1i + length ins - 1)%nat) as [lc|] eqn:Hlcj; [| apply lookup_ge_None in Hlcj; lia].
        iDestruct (own_store_runs_node_acc _ (MkStoreStateRuns _ _ _ _ _ _ _) _ _ _ _ _ _ Hlj Hpj Hlcj Hlrj with "Hruns") as (itemVal) "H".
        iNamed "H".
        iDestruct (typed_pointsto_not_null with "Haccval") as %Hlcnn.
        exfalso. apply Hlcnn. rewrite -e /loc_at decide_True; last lia.
        have -> : Z.to_nat (Z.of_nat (p1i + length ins) - 1) = (p1i + length ins - 1)%nat by lia.
        rewrite Hlcj //. }
    { destruct Hleftj as [Hpe0 | (lr & li & Hlrj & Hliarr & Hliitem & Hge1 & _)].
      { exfalso. apply n. rewrite /loc_at. case_decide; [lia | done]. }
      have Hlrlt : (p1i + length ins - 1 < length lsj)%nat by (rewrite Hlslj; exact (lookup_lt_Some _ _ _ Hlrj)).
      destruct (lsj !! (p1i + length ins - 1)%nat) as [lc|] eqn:Hlcj; [| apply lookup_ge_None in Hlcj; lia].
      have Hlcloc : loc_at lsj (Z.of_nat (p1i + length ins) - 1) = lc.
      { rewrite /loc_at decide_True; last lia.
        have -> : Z.to_nat (Z.of_nat (p1i + length ins) - 1) = (p1i + length ins - 1)%nat by lia.
        rewrite Hlcj //. }
      iDestruct (own_store_runs_node_acc _ (MkStoreStateRuns _ _ _ _ _ _ _) _ _ _ _ _ _ Hlj Hpj Hlcj Hlrj with "Hruns") as (itemVal) "H".
      iNamed "H".
      have Hrun : run_wf (run_items lr) := Hwfj lr (list_elem_of_lookup_2 _ _ _ Hlrj).
      iEval (rewrite -Hlcloc) in "Haccval".
      wp_method_call. wp_call. wp_auto.
      wp_method_call. wp_call. rewrite /yjs.item__LastIdⁱᵐᵖˡ. wp_auto.
      wp_alloc icopy as "Hic". wp_auto.
      wp_bind (icopy @! (go.PointerType yjs.item) @! "Len" (# ()))%E.
      wp_apply (wp_item__Len icopy (DfracOwn 1) itemVal with "[$Hic]"). iIntros "Hic".
      wp_pures. wp_store.
      iDestruct (typed_pointsto_not_null with "lid") as %Hlidnn.
      iPersist "lid". wp_auto.
      iEval (rewrite Hlcloc) in "Haccval".
      iDestruct ("Haccback" with "Haccval") as "Hruns".
      iSplitR; [done|].
      iExists lid_ptr, (Some {| yjs.id.clientId' := itemVal.(yjs.item.id').(yjs.id.clientId'); yjs.id.clock' := w64_word_instance.(word.sub) (w64_word_instance.(word.add) itemVal.(yjs.item.id').(yjs.id.clock') (W64 (length (itemVal.(yjs.item.content').(yjs.content.content'))))) (W64 1) |}).
      iFrame "originLeftId Hleftp Hruns".
      iSplitR.
      { rewrite /is_origin_id. iSplit; [iPureIntro; exact Hlidnn | iFrame "lid"]. }
      (* the produced id is the LAST char of the left run:
         head clock + run length - 1 (run_wf), no-wrap from the pool fits *)
      have Hfitslr : run_fits lr.
      { apply (λ H, proj1 (proj2 (proj1 Hrpj lr H))). apply elem_of_all_runs.
        exists tv.(yjs.Text.inner'), (MkTypeModel runsj arr). split; [exact Hpj | exact (list_elem_of_lookup_2 _ _ _ Hlrj)]. }
      have Hlen1lr : (1 <= length (run_items lr))%nat.
      { destruct (run_items lr) eqn:Hrc; [exact (False_ind _ (proj1 Hrun eq_refl)) | simpl; lia]. }
      have Hnw : (uint.Z (itemVal.(yjs.item.id').(yjs.id.clock')) + Z.of_nat (length (run_items lr)) < 2^64)%Z.
      { move: Hfitslr. rewrite /run_fits /run_clock Haccid /toYjsId /=. move=> H. word. }
      iPureIntro. right. exists li. split_and!.
      - exact Hge1.
      - exact Hliarr.
      - rewrite (run_wf_char_id _ _ _ Hrun Hliitem) /=.
        rewrite /run_head_item in Haccid.
        rewrite Haccid /toYjsId /=.
        do 2 f_equal.
        rewrite Haccle. clear -Hnw Hlen1lr. word. }
    iIntros (v) "[%Hv HQL]". subst v. iNamed "HQL". wp_auto.
    iDestruct (own_store_runs_arr with "Hruns") as %Harrsj.
    have Harrj : arr = runs_flatten runsj := Harrsj _ _ Hpj.
    wp_func_call. wp_call.
    destruct (cs !! sint.nat (W64 j)) as [b|] eqn:Hb;
      [ wp_auto | exfalso; apply lookup_ge_None in Hb; revert Hb Hjlt Hlcb2; word ].
    wp_alloc client_l as "Hcl2". wp_auto.
    rewrite Hb. wp_auto. wp_func_call. wp_call.
    wp_alloc oR2 as "HoR2". wp_auto. wp_alloc oL2 as "HoL2". wp_auto.
    (* build the model item [newItem] and integrate *)
    have Hclocknit : uint.nat (W64 (uint.Z k + j)) = (uint.nat k + j)%nat by word.
    rewrite Hinslen in Hleftspec.
    have Horig : ∃ (o : YjsPtr A),
       (toYjsId <$> olo = None ∧ o = First ∧ (mp + j)%nat = 0%nat) ∨
       (∃ li, (1 <= mp + j)%nat ∧ arr !! (mp + j - 1)%nat = Some li ∧ toYjsId <$> olo = Some (item_id li) ∧ o = itemPtr li).
    { destruct Hleftspec as [[Hon Hp0'] | (li & Hge & Hla & Hom)].
      - exists First. left. subst olo. split_and!; [reflexivity | reflexivity |].
        have Hp00 : p1i = 0%nat by lia.
        have Hj00 : j = 0%nat by lia.
        rewrite Hmpdef Hp00 take_0 runs_flatten_nil /= Hj00 //.
      - exists (itemPtr li). right. exists li. split_and!; [| exact Hla | exact Hom | reflexivity].
        destruct j as [|j']; [| lia].
        have Hp1' : (1 <= p1i)%nat by lia.
        have := Hmp1 Hp1'. lia. }
    destruct Horig as [morigin Horig].
    have Hrorig : ∃ (r : YjsPtr A),
       (toYjsId <$> in_rO = None ∧ r = Last ∧ (mp + j)%nat = length arr) ∨
       (∃ ri, arr !! (mp + j)%nat = Some ri ∧ toYjsId <$> in_rO = Some (item_id ri) ∧ r = itemPtr ri).
    { destruct Hrightj as [(Hrn & Hoeq & Hpl) | (ri & rightOriginId & Hria & Hros & Hrii & HoRi)].
      - exists Last. left. subst in_rO. split_and!; [reflexivity | reflexivity | exact Hpl].
      - exists (itemPtr ri). right. exists ri. split_and!; [exact Hria | rewrite Hros /= Hrii // | reflexivity]. }
    destruct Hrorig as [mrightorigin Hrorig].
    set (in_id1 := MkYjsId (uint.nat client) (uint.nat (W64 (uint.Z k + j)))).
    set (input := MkIntegrateInput (toYjsId <$> olo) (toYjsId <$> in_rO) ([b] : A) in_id1).
    set (newItem := Item (A:=A) morigin mrightorigin in_id1 [b]).
    have Htoitem : toItem input arr = Some newItem.
    { apply (toItem_at arr in_id1 [b] morigin mrightorigin (toYjsId <$> olo) (toYjsId <$> in_rO) Hinvj).
      - destruct Horig as [(Hon & Ho & _) | (li & _ & Hla & Hom & Ho)]; [left; split; [exact Hon | exact Ho] | right; exists li; split_and!; [exact Hom | exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Hla) | exact Ho]].
      - destruct Hrorig as [(Hrn & Hr & _) | (ri & Hria & Hri & Hr)]; [left; split; [exact Hrn | exact Hr] | right; exists ri; split_and!; [exact Hri | exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Hria) | exact Hr]]. }
    have Hvalid : IsItemValid newItem :=
      insert_item_valid arr (mp + j) in_id1 [b] morigin mrightorigin
        (toYjsId <$> olo) (toYjsId <$> in_rO) Hinvj Horig Hrorig.
    have Hmax' : maximalId newItem arr.
    { apply (insert_maximalId arr morigin mrightorigin (uint.nat client) (uint.nat (W64 (uint.Z k + j))) [b]).
      intros x Hx Hc. rewrite Hclocknit. exact (Hctrj x Hx Hc). }
    iDestruct "HisR" as "#HisRp".
    (* the resolved neighbour indices the Integrate spec takes (issue #49) *)
    have HfindLj : findLeftIdx (in_originId input) arr = Some (Z.of_nat (mp + j) - 1).
    { destruct Horig as [(Hon & _ & Hp0') | (li & Hge & Hla & Hom & _)].
      - rewrite /input /= Hon /findLeftIdx Hp0' //.
      - rewrite /input /= Hom
          (findLeftIdx_at arr (mp + j - 1) li (yai_unique _ Hinvj) Hla).
        f_equal. lia. }
    have HfindRj : findRightIdx (in_rightOriginId input) arr = Some (Z.of_nat (mp + j)).
    { destruct Hrorig as [(Hrn & _ & Hpl) | (ri & Hria & Hri & _)].
      - rewrite /input /= Hrn /findRightIdx Hpl //.
      - rewrite /input /= Hri
          (findRightIdx_at arr (mp + j) ri (yai_unique _ Hinvj) Hria) //. }
    (* the local item is created pre-linked (left/right/parent stores) *)
    iAssert (own_linked_item oL2 input tv.(yjs.Text.inner')
               (loc_at lsj (Z.of_nat (p1i + j) - 1)) (loc_at lsj (Z.of_nat (p1i + j))))
      with "[HoL2 HisL]" as "Hfresh".
    { iExists _, olo, in_rO. rewrite /own_fresh_item_raw /=. iFrame "HoL2 HisL HisRp".
      iPureIntro. split_and!;
        [reflexivity | reflexivity | reflexivity | reflexivity
        | reflexivity | reflexivity | reflexivity | reflexivity | simpl; lia]. }
    have Hres : origins_resolved runsj arr input (p1i + j)%nat (p1i + j)%nat.
    { exists (Z.of_nat (mp + j) - 1)%Z, (Z.of_nat (mp + j)).
      split_and!; [exact HfindLj | exact HfindRj | rewrite Hcoupj; lia | exact Hpjb | rewrite Hcoupj; lia | exact Hpjb]. }
    (* the one-char input's model step *)
    destruct (integrate_some input arr newItem Hinvj Htoitem) as [arr' Hintegrate].
    have Hsi : setintegrate input arr = Some arr'.
    { rewrite (setintegrate_eq_integrate input arr newItem Hinvj Htoitem Hvalid Hmax'). exact Hintegrate. }
    have Hlen1 : length (in_content input) = 1%nat := eq_refl.
    have Hall : integrate_all (ops_of_input input (explode (in_content input))) arr = Some arr'.
    { rewrite (explode_singleton _ Hlen1) ops_of_input_singleton integrate_all_singleton. exact Hintegrate. }
    have Hidnew_in : item_id newItem = in_id input := commutativity.toItem_id input arr newItem Htoitem.
    have Hfitsin : input_fits input.
    { rewrite /input_fits /input /in_id1 /=. rewrite Hclocknit. word. }
    (* the pool-level client clock bound the splice needs, from the
       model-level bounds (this text's [Hctrj], the others' lock-time [Hctr]) *)
    have Hbelowj : pool_run_clock_below pj (in_id input).
    { have -> : in_id input = MkYjsId (uint.nat client) (uint.nat k + j)%nat.
      { rewrite /input /in_id1 /= Hclocknit //. }
      apply (pool_run_clock_below_of_arrs pj (uint.nat client) (uint.nat k + j)%nat Harrsj Hwfallj).
      move=> q tm x Hq Hx Hcx.
      destruct (decide (q = tv.(yjs.Text.inner'))) as [-> | Hne].
      - rewrite Hpj in Hq. injection Hq as <-. simpl in Hx. exact (Hctrj x Hx Hcx).
      - rewrite (Hdompj q Hne) in Hq.
        have := Hctr _ _ x Hq Hx Hcx. lia. }
    wp_apply (wp_store__Integrate_runs tv.(yjs.Text.store') tv.(yjs.Text.inner') tv.(yjs.Text.inner') oL2
                (MkStoreStateRuns client (w64_word_instance.(word.add) (W64 (uint.Z k + Z.of_nat j)) (W64 1)) locsj pj bind pend pdel)
                (MkTypeModel runsj arr) lsj arr' input newItem (p1i + j)%nat (p1i + j)%nat
                (or_introl eq_refl) Hpj Hlj (conj Htoitem (conj Hvalid Hmax')) Hfitsin Hall Hres Hbelowj
                with "[$Hfresh $Hruns]").
    iIntros (runs' ls' run) "(Hruns & %Hinv' & %Hsp & %Hden)".
    iEval (simpl) in "Hruns".
    destruct Hsp as (nx & Hat & Hls'eq).
    destruct Hat as (Hnxb & Hile & Hruns'eq & Harrsp2').
    set (iidx := length (runs_flatten (take nx runsj))) in Hile, Harrsp2'.
    have Hcoupx : length (runs_flatten (take nx runsj)) = iidx := eq_refl.
    have Hrunsub : ∀ x, x ∈ run -> x ∈ arr'.
    { rewrite Harrsp2'. move=> x Hx. apply elem_of_app. right. apply elem_of_app. by left. }
    have Hruneq : run = [newItem]
      := integrate_unit_run arr arr' input newItem run Hinvj (conj Htoitem (conj Hvalid Hmax'))
           Hintegrate Hinv' Hden Hlen1 Hrunsub.
    subst run.
    have Harrsp2 : arr' = take iidx arr ++ newItem :: drop iidx arr := Harrsp2'.
    have Harr'eq : arr' = insertIdxIfInBounds iidx newItem arr.
    { rewrite /insertIdxIfInBounds decide_True; [exact Harrsp2 | exact Hile]. }
    (* --- mint the op certificate (issue #42): the heap integrate above is
       mirrored by a ghost broadcast(+self-delivery) of the op this item
       denotes, keeping the history coherent with the new [arr']. --- *)
    rewrite (setintegrate_eq_integrate input arr newItem Hinvj Htoitem Hvalid Hmax') in Hsi.
    have HmaskN : ↑histN ⊆ (⊤ : coPset) by solve_ndisj.
    have Hdg : doc_model_get (<[RootId name := arr]> m) (RootId name) = arr
      := docm_get_insert_eq m (RootId name) arr.
    have Htoitem2 : toItem input (doc_model_get (<[RootId name := arr]> m) (RootId name)) = Some newItem
      by rewrite Hdg.
    have Hmax2 : maximalId newItem (doc_model_get (<[RootId name := arr]> m) (RootId name))
      by rewrite Hdg.
    have Hsi2' : integrate input (doc_model_get (<[RootId name := arr]> m) (RootId name)) = Some arr'
      by rewrite Hdg.
    have Hboundj : ∀ (t' : TId) (x : YjsItem A),
        x ∈ doc_model_get (<[RootId name := arr]> m) t' → clientId (item_id x) = uint.nat client →
        (clock (item_id x) < uint.nat (W64 (uint.Z k + j)))%nat.
    { move=> t' x Hx Hcx. rewrite Hclocknit.
      destruct (decide (t' = RootId name)) as [-> | Hne'].
      - rewrite Hdg in Hx. exact (Hctrj x Hx Hcx).
      - rewrite docm_get_insert_ne // in Hx.
        have Hnem : doc_model_get m t' ≠ [] by (move=> Hnil; rewrite Hnil in Hx; set_solver).
        destruct (Hmdom t' Hnem) as (name' & p' & -> & Hbind').
        destruct (Hbindtypes name' p' Hbind') as [ts' Hts'].
        rewrite (Hmtypes name' p' ts' Hbind' Hts') in Hx.
        have := Hctr p' ts' x Hts' Hx Hcx. lia. }
    iMod (history_broadcast γh (uint.nat client) (uint.nat (W64 (uint.Z k + j))) hj
            (<[RootId name := arr]> m) (RootId name) arr'
            input newItem ⊤ HmaskN Htoitem2 Hvalid Hmax2 eq_refl Hboundj Hsi2' Hhcohj
            with "His_hist Hhistj") as "(Hhistj & #Hlbj & #Hcertj & %Hhcohj2)".
    have Hcollm : <[RootId name := arr']> (<[RootId name := arr]> m) = <[RootId name := arr']> m
      by (rewrite insert_insert; case_decide; [reflexivity | congruence]).
    rewrite Hcollm in Hhcohj2.
    pose proof (toItem_input_of_item input arr newItem Htoitem) as Hinputeq.
    iEval (rewrite Hinputeq) in "Hcertj".
    iAssert ([∗ list] it ∈ (ins ++ [newItem]),
               is_op_cert γh (RootId name, OpInsert (input_of_item it)))%I
      with "[Hcertsj]" as "Hcertsj".
    { rewrite big_sepL_snoc. iFrame "Hcertsj". iApply "Hcertj". }
    wp_auto.
    (* place the new item, identify its index *)
    have Hple : (mp + j <= length arr)%nat by (rewrite Hlenarr; lia).
    have Hplace : arr' = take (mp + j)%nat arr ++ newItem :: drop (mp + j)%nat arr.
    { rewrite Harr'eq. apply (insert_straddle arr newItem iidx (mp + j)%nat Hinvj ltac:(rewrite -Harr'eq; exact Hinv') Hile Hple).
      - destruct Horig as [(_ & Ho & Hp0') | (li & Hge & Hla & _ & Ho)]; [left; split; [exact Hp0' | rewrite /newItem /=; exact Ho] | right; split; [exact Hge | exists li; split; [exact Hla | rewrite /newItem /=; exact Ho]]].
      - destruct Hrorig as [(_ & Hr & Hpl) | (ri & Hria & _ & Hr)]; [left; split; [exact Hpl | rewrite /newItem /=; exact Hr] | right; exists ri; split; [exact Hria | rewrite /newItem /=; exact Hr]]. }
    have Hnitpos : arr' !! (mp + j)%nat = Some newItem.
    { rewrite Hplace. apply list_lookup_middle. symmetry. apply length_take_le. exact Hple. }
    have Hshift : arr' !! (mp + j + 1)%nat = arr !! (mp + j)%nat.
    { rewrite Hplace. rewrite lookup_app_r; last (rewrite length_take_le; [lia | exact Hple]).
      rewrite length_take_le; last exact Hple.
      replace (mp + j + 1 - (mp + j))%nat with 1%nat by lia.
      simpl. rewrite lookup_drop. f_equal. lia. }
    have HnitIn : newItem ∈ arr' by exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Hnitpos).
    (* the splice index is the run cursor: the model index of the new run is
       mp + j (order theory), and prefix-sum injectivity pins nx *)
    have Hiidx0 : iidx = (mp + j)%nat.
    { have Hnit_i0 : arr' !! iidx = Some newItem.
      { rewrite Harrsp2. apply list_lookup_middle. rewrite length_take_le //. }
      destruct (Nat.lt_trichotomy iidx (mp + j)%nat) as [Hlt|[Heq|Hgt]]; [exfalso|exact Heq|exfalso].
      - have HH := invariant_yjsarray_idx.getElem_lt_YjsLt' arr' iidx (mp + j)%nat newItem newItem Hinv' Hnit_i0 Hnitpos Hlt.
        exact (asymmetry.yjs_lt_asymm (yai_closed _ Hinv') (yai_item_set_inv _ Hinv') (itemPtr newItem) (itemPtr newItem) HnitIn HnitIn HH HH).
      - have HH := invariant_yjsarray_idx.getElem_lt_YjsLt' arr' (mp + j)%nat iidx newItem newItem Hinv' Hnitpos Hnit_i0 Hgt.
        exact (asymmetry.yjs_lt_asymm (yai_closed _ Hinv') (yai_item_set_inv _ Hinv') (itemPtr newItem) (itemPtr newItem) HnitIn HnitIn HH HH). }
    have Hnxpos0 : nx = (p1i + j)%nat.
    { apply (runs_flatten_take_length_inj runsj nx (p1i + j)%nat Hnecj Hnxb Hpjb).
      rewrite Hcoupx Hcoupj Hiidx0 //. }
    rewrite Hnxpos0 in Hnxb Hile Hruns'eq Hls'eq Hcoupx.
    set (rnew := MkItemRun [newItem] false).
    have Hrx : runs' !! (p1i + j)%nat = Some rnew.
    { rewrite Hruns'eq. apply list_lookup_middle. rewrite length_take_le //. }
    have Hlx : ls' !! (p1i + j)%nat = Some oL2.
    { rewrite Hls'eq /integrate_locs. apply list_lookup_middle.
      rewrite length_take_le; [done | rewrite Hlslj; exact Hnxb]. }
    (* the tombstone-set invariant across the splice: the pool grows by the
       one fresh LIVE cell, whose single char cannot be in the delete set
       because the set only holds ids already in [m] and this id's clock sits
       at the counter, above every same-client item of [m] *)
    have Hac_ds : all_runs (<[tv.(yjs.Text.inner') := MkTypeModel runs' arr']> pj)
                ≡ₚ all_runs pj ++ [MkItemRun [newItem] false].
    { have Hsp : take (p1i + j)%nat runsj ++ MkItemRun [newItem] false :: drop (p1i + j)%nat runsj
               ≡ₚ runsj ++ [MkItemRun [newItem] false].
      { rewrite -(Permutation_middle (take (p1i + j)%nat runsj) (drop (p1i + j)%nat runsj)
                    (MkItemRun [newItem] false)) take_drop.
        apply Permutation_cons_append. }
      rewrite (all_runs_insert pj tv.(yjs.Text.inner') (MkTypeModel runsj arr) _ Hpj)
              (all_runs_lookup pj tv.(yjs.Text.inner') (MkTypeModel runsj arr) Hpj).
      cbn [tm_runs]. rewrite Hruns'eq Hsp -!app_assoc.
      apply Permutation_app_head. apply Permutation_app_comm. }
    have Hfresh_ds : ∀ y, y ∈ run_items (MkItemRun [newItem] false) -> doc_model_has m (item_id y) = false.
    { move=> y Hy.
      have Hyn : y = newItem.
      { move: Hy. simpl. move=> Hy'. by apply list_elem_of_singleton in Hy'. }
      subst y.
      apply (pool_docm_has_registry_false bind p0 m (item_id newItem)
               Hmtypes Hmdom Hbindtypes).
      move=> q tq x Hq Hx Hid.
      have Hxcl : clientId (item_id x) = uint.nat client
        by rewrite Hid /newItem /in_id1 /=.
      have := Hctr q tq x Hq Hx Hxcl.
      rewrite Hid /newItem /in_id1 /=. rewrite Hclocknit. lia. }
    iDestruct (own_delete_set_runs_snoc γs m _ _ (MkItemRun [newItem] false) Hac_ds Hfresh_ds
                 with "Hdelete_set") as "Hdelete_set".
    wp_for_post.
    (* re-establish the loop invariant for [S j] with [ins ++ [newItem]] *)
    iFrame "Ht His_lb HΦ HisRp Hacc".
    iExists (S j), arr', (<[tv.(yjs.Text.inner') := ls']> locsj), (<[tv.(yjs.Text.inner') := MkTypeModel runs' arr']> pj), ls', runs', (ins ++ [newItem]),
      (hj ++ [EvBroadcast (RootId name, OpInsert input);
              EvDeliver (RootId name, OpInsert input)]).
    replace (W64 (uint.Z k + Z.of_nat (S j))) with (w64_word_instance.(word.add) (W64 (uint.Z k + j)) (W64 1)) by word.
    replace (W64 (S j)) with (w64_word_instance.(word.add) (W64 j) (W64 1)) by word.
    have Hleft' : loc_at ls' (Z.of_nat (p1i + S j) - 1) = oL2.
    { rewrite /loc_at decide_True; last lia.
      have -> : Z.to_nat (Z.of_nat (p1i + S j) - 1) = (p1i + j)%nat by lia.
      rewrite Hlx //. }
    have Hright' : loc_at ls' (Z.of_nat (p1i + S j)) = loc_at lsj (Z.of_nat (p1i + j)).
    { rewrite Hls'eq /integrate_locs.
      have -> : Z.of_nat (p1i + S j) = (Z.of_nat (p1i + j) + 1)%Z by lia.
      apply loc_at_splice_ge; [lia | rewrite Hlslj; exact Hnxb]. }
    iEval (rewrite -Hleft') in "Hleftp".
    iEval (rewrite -Hright') in "Hrightp".
    iFrame "Hi Htptr Hcontentp Hclientp HoRp Hleftp Hsp Hruns Hlk Hdelete_set Hseq HtypesAuth Hrightp Hhistj Hcertsj".
    have HmroR : mrightorigin = originRight.
    { destruct in_rO as [rightOriginId|] eqn:Hino.
      - destruct Hrorig as [(Hrn & _ & _) | (ri & Hria & _ & Hmr)]; [simpl in Hrn; discriminate |].
        destruct Hrightj as [(Hrn2 & _ & _) | (ri2 & rid2 & Hria2 & _ & _ & HoRi)]; [discriminate |].
        rewrite Hmr HoRi. rewrite Hria in Hria2. injection Hria2 as ->. reflexivity.
      - destruct Hrorig as [(_ & Hmr & _) | (ri & _ & Hri & _)]; [| simpl in Hri; discriminate].
        destruct Hrightj as [(_ & HoRl & _) | (ri2 & rid2 & _ & Hros2 & _ & _)]; [| discriminate].
        rewrite Hmr HoRl //. }
    iPureIntro. split_and!.
    - apply lookup_insert_eq.
    - apply lookup_insert_eq.
    - move=> q Hne. rewrite lookup_insert_ne; [exact (Hdompj q Hne) | congruence].
    - move=> q Hne. rewrite lookup_insert_ne; [exact (Hdomlj q Hne) | congruence].
    - exact Hinv'.
    - rewrite Hplace length_app length_take_le; [| exact Hple]. simpl. rewrite length_drop. lia.
    - rewrite Hruns'eq length_app /= length_take_le; last exact Hnxb.
      rewrite length_drop. lia.
    - lia.
    - intros x Hx Hc. rewrite Hplace in Hx.
      apply elem_of_app in Hx as [Hxt | Hxc].
      + have Hxa : ArrSet arr x by (rewrite -(take_drop (mp + j)%nat arr); apply elem_of_app; left; exact Hxt).
        have := Hctrj x Hxa Hc. lia.
      + apply elem_of_cons in Hxc as [-> | Hxd].
        * rewrite /newItem /in_id1 /=. rewrite Hclocknit. lia.
        * have Hxa : ArrSet arr x by (rewrite -(take_drop (mp + j)%nat arr); apply elem_of_app; right; exact Hxd).
          have := Hctrj x Hxa Hc. lia.
    - right. exists rnew, newItem. split_and!.
      + replace (p1i + S j - 1)%nat with (p1i + j)%nat by lia. exact Hrx.
      + replace (mp + S j - 1)%nat with (mp + j)%nat by lia. exact Hnitpos.
      + reflexivity.
      + lia.
      + intros Hsj. lia.
      + intros j' Hsj. injection Hsj as ->. rewrite lookup_app_r; [| rewrite Hinslen; lia]. rewrite Hinslen. rewrite Nat.sub_diag. reflexivity.
    - destruct Hrightj as [(Hrn & HoRl & Hpl) | (ri & rightOriginId & Hria & Hros & Hrii & HoRi)].
      + left. split_and!; [exact Hrn | exact HoRl |].
        rewrite Hplace length_app length_take_le; [| exact Hple]. simpl. rewrite length_drop. lia.
      + right. exists ri, rightOriginId. split_and!.
        * replace (mp + S j)%nat with (mp + j + 1)%nat by lia. rewrite Hshift. exact Hria.
        * exact Hros.
        * exact Hrii.
        * exact HoRi.
    - rewrite length_app Hinslen /=. lia.
    - intros i it Hii.
      destruct (decide (i < length ins)%nat) as [Hilt | Hige].
      + rewrite lookup_app_l in Hii; [| exact Hilt].
        have [Hitin [Hcont [Hid [Hror [Horg Hchain]]]]] := Hins i it Hii.
        split_and!.
        * rewrite Hplace. rewrite -(take_drop (mp + j)%nat arr) in Hitin. apply elem_of_app in Hitin as [H1 | H2]; [apply elem_of_app; left; exact H1 | apply elem_of_app; right; apply elem_of_cons; right; exact H2].
        * exact Hcont.
        * exact Hid.
        * exact Hror.
        * exact Horg.
        * intros j' itj Hisj Hlookj'. rewrite lookup_app_l in Hlookj'; [| lia]. exact (Hchain j' itj Hisj Hlookj').
      + have Hieq : i = length ins.
        { apply lookup_lt_Some in Hii. rewrite length_app /= in Hii. lia. }
        rewrite Hieq lookup_app_r in Hii; [| lia]. rewrite Nat.sub_diag /= in Hii. injection Hii as <-.
        split_and!.
        * exact HnitIn.
        * intros b0 Hcsb. have Hsn : sint.nat (W64 j) = j by word. rewrite Hsn in Hb. rewrite Hieq Hinslen in Hcsb. rewrite Hb in Hcsb. injection Hcsb as Hbb. rewrite /newItem /= Hbb //.
        * rewrite /newItem /in_id1 /=. rewrite Hieq Hinslen Hclocknit. reflexivity.
        * rewrite /newItem /=. exact HmroR.
        * intros Hi0. rewrite /newItem /=. rewrite Hieq Hinslen in Hi0.
          destruct Horig as [(_ & Hmo & Hp0') | (li & Hge & Hla & _ & Hmo)].
          -- rewrite Hmo. destruct HoLspec as [[HoLF _] | (lr2 & li2 & Hge2 & _)]; [rewrite HoLF // | lia].
          -- rewrite Hmo. destruct Hleftj as [Hp0'' | (lr2 & li2 & _ & Hla2 & _ & _ & Hlk0 & _)].
             { exfalso. have Hp00 : p1i = 0%nat by lia. have Hj00 : j = 0%nat by lia.
               move: Hge. rewrite Hmpdef Hp00 take_0 runs_flatten_nil /= Hj00. lia. }
             have -> : li = li2 by (rewrite Hla in Hla2; injection Hla2 as ->; reflexivity). exact (Hlk0 Hi0).
        * intros j' itj Hisj Hlookj'. rewrite /newItem /=. rewrite Hieq Hinslen in Hisj. rewrite lookup_app_l in Hlookj'; [| rewrite Hinslen; lia].
          destruct Horig as [(_ & _ & Hp0') | (li & Hge & Hla & _ & Hmo)]; [lia |].
          rewrite Hmo. destruct Hleftj as [Hp0'' | (lr2 & li2 & _ & Hla2 & _ & _ & _ & Hlk)]; [lia |]. have -> : li = li2 by (rewrite Hla in Hla2; injection Hla2 as ->; reflexivity). have Hli2 := Hlk j' Hisj. rewrite Hli2 in Hlookj'. injection Hlookj' as <-. reflexivity.
    - intros x Hx. have Hxa := Hsubold x Hx. rewrite Hplace. rewrite -(take_drop (mp + j)%nat arr) in Hxa. apply elem_of_app in Hxa as [H1 | H2]; [apply elem_of_app; left; exact H1 | apply elem_of_app; right; apply elem_of_cons; right; exact H2].
    - (* Hcoupj at S j: the splice adds one unit run at the cursor *)
      replace (p1i + S j)%nat with (S (p1i + j))%nat by lia.
      rewrite Hruns'eq.
      have Htk : take (S (p1i + j)) (take (p1i + j)%nat runsj ++ rnew :: drop (p1i + j)%nat runsj)
               = take (p1i + j)%nat runsj ++ [rnew].
      { rewrite take_app_ge; last (rewrite length_take_le; lia).
        rewrite length_take_le; last lia.
        replace (S (p1i + j) - (p1i + j))%nat with 1%nat by lia. done. }
      rewrite Htk runs_flatten_app length_app Hcoupj runs_flatten_cons runs_flatten_nil /rnew /=. lia.
    - rewrite Hruns'eq length_app /= length_take_le; last exact Hnxb. rewrite length_drop. lia.
    - exact Hhcohj2. }
  (* loop exit: the whole run is integrated; rebuild [store_inv] and return. *)
  have Hjend : (j = length cs)%nat by word.
  rewrite decide_False; [| done]. wp_auto.
  rewrite decide_True; [| reflexivity]. wp_auto.
  have Hk'val : uint.nat (W64 (uint.Z k + j)) = (uint.nat k + j)%nat by word.
  have Hsubarr : list_to_set (ts.(tm_arr)) ⊆ (list_to_set arr : gset (YjsItem A)).
  { intros y Hy. rewrite elem_of_list_to_set in Hy. rewrite elem_of_list_to_set. apply Hsubold. exact Hy. }
  have Hmk : ((λ tm : type_model, (list_to_set (tm_arr tm) : gset (YjsItem A))) <$> p0) !! tv.(yjs.Text.inner') = Some (list_to_set ts.(tm_arr)).
  { rewrite lookup_fmap Htsp //. }
  iMod (auth_gmap_gset_grow γs.(sn_seq) _ tv.(yjs.Text.inner') (list_to_set ts.(tm_arr)) (list_to_set arr) Hmk Hsubarr with "Hseq") as "[Hseq Hfrag]".
  (* transport the accepted-set coherence across the history the loop grew:
     only appends happened under the lock ([h] is a prefix of [hj]), so
     [delivered_ids] only grew and [accepted_coh] still holds at [hj] *)
  iDestruct (is_history_lb_prefix with "Hhistj Hlb_h") as %Hpref_hj.
  have Hacccoh' : accepted_coh acc hj pend.
  { eapply accepted_coh_hist_grow; [exact Hacccoh | exact (delivered_ids_prefix _ _ Hpref_hj)]. }
  (* the delete set's model-domain bound survives the insert: the type's list
     only grew (Hsubarr), so every id present before is still present *)
  iDestruct (own_delete_set_runs_insert γs m (all_runs pj) (RootId name) arr with "Hdelete_set") as "Hdelete_set".
  { move=> x Hx.
    rewrite Hmt in Hx.
    have Hxg : x ∈ (list_to_set arr : gset (YjsItem A)).
    { apply Hsubarr. rewrite elem_of_list_to_set. exact Hx. }
    rewrite elem_of_list_to_set in Hxg. exact Hxg. }
  have Hregmodel_close : pool_registry_models (<[RootId name := arr]> m) bind pj.
  { rewrite /pool_registry_models. split.
    { move=> name' q tm' Hb' Hts'.
      destruct (decide (q = tv.(yjs.Text.inner'))) as [-> | Hne].
      + have Heqn : name' = name := Hbindinj name' name _ Hb' Hbindlk.
        subst name'. rewrite Hpj in Hts'. injection Hts' as <-.
        rewrite docm_get_insert_eq //.
      + rewrite (Hdompj q Hne) in Hts'.
        rewrite docm_get_insert_ne.
        * exact (Hmtypes name' q tm' Hb' Hts').
        * move=> Heqr. injection Heqr as Heqn. subst name'.
          rewrite Hbindlk in Hb'. injection Hb' as He'. exact (Hne (eq_sym He')). }
    { move=> t' Hne'.
      destruct (decide (t' = RootId name)) as [-> | Hnr].
      + exists name, tv.(yjs.Text.inner'). split; [reflexivity | exact Hbindlk].
      + rewrite docm_get_insert_ne // in Hne'. exact (Hmdom t' Hne'). }
  }
  have Hctr_close : ∀ parent' tm' x, pj !! parent' = Some tm' → x ∈ tm_arr tm' →
      clientId (item_id x) = uint.nat client → (clock (item_id x) < uint.nat (W64 (uint.Z k + j)))%nat.
  { intros parent' tm' x Hlook Hxin Hxc. rewrite Hk'val.
      destruct (decide (parent' = tv.(yjs.Text.inner'))) as [-> | Hne].
      + rewrite Hpj in Hlook. injection Hlook as <-. simpl in Hxin. exact (Hctrj x Hxin Hxc).
      + rewrite (Hdompj parent' Hne) in Hlook.
        have := Hctr parent' tm' x Hlook Hxin Hxc. lia. }
  wp_apply (wp_Store__wunlock _ _ _ (uint.nat client) hj (<[RootId name := arr]> m) pend
              with "[$His_store $Hlk Hruns Hseq HtypesAuth Hhistj Hacc Hdelete_set]").
  { iExists client, (W64 (uint.Z k + j)), pdel, locsj, pj, bind, acc.
    rewrite (pool_seq_map_insert_at p0 pj tv.(yjs.Text.inner') ts (MkTypeModel runsj arr) Hdompj Htsp Hpj) /=.
    iFrame "∗#". iPureIntro. split_and!;
      [reflexivity | exact Hpendroot | exact Hpendbnd | exact Hregmodel_close
      | exact Hhcohj | exact Hctr_close | exact Hacccoh']. }
  iApply ("HΦ" $! arr ins (uint.nat client) (uint.nat k) originLeft originRight).
  iSplitL "Hfrag Ht".
  { iExists tv, tv.(yjs.Text.store'), tv.(yjs.Text.inner'). iFrame "Ht His_store His_hist Hbind Hfrag". iPureIntro. split_and!; [reflexivity | reflexivity | exact (yai_sorted _ Hinvj)]. }
  iSplit.
  { iPureIntro. split_and!.
    - apply (sorted_subseteq_sublist L arr Hinvj Hsorted (yai_sorted _ Hinvj)).
      intros x Hx. have Hxg : x ∈ (list_to_set arr : gset (YjsItem A)).
      { apply Hsubarr. apply HLsub. rewrite elem_of_list_to_set. exact Hx. }
      rewrite elem_of_list_to_set in Hxg. exact Hxg.
    - right. rewrite Hinslen. exact Hjend.
    - intros i it b Hii Hcsb.
      have [Hitin [Hcont [Hid [Hror [Horg Hchain]]]]] := Hins i it Hii.
      split_and!.
      + exact Hitin.
      + intros HinL. have HitTs : it ∈ ts.(tm_arr).
        { have Htg : it ∈ (list_to_set ts.(tm_arr) : gset (YjsItem A)).
          { apply HLsub. rewrite elem_of_list_to_set. exact HinL. }
          rewrite elem_of_list_to_set in Htg. exact Htg. }
        have Hclk := Hctr tv.(yjs.Text.inner') ts it Htsp HitTs. rewrite Hid in Hclk. simpl in Hclk. specialize (Hclk eq_refl). lia.
      + exact (Hcont b Hcsb).
      + exact Hid.
      + exact Hror.
      + exact Horg.
      + exact Hchain. }
  iFrame "Hcertsj".
Qed.

End text.
