(** [wp_TextObserver__Poll]: one poll of the observer (issue #198). Under the
    store's write lock, one walk of the text's item list classifies every
    char against the observer's token exactly as the model's
    [text_delta observed current] does, rebuilds the token for the current
    snapshot and re-mints the certificates that carry
    [snapshot_grows_to current] to the next poll. The postcondition is the
    read API's ([text_snapshot], [history_reflected], [visible_excludes],
    all about [current]) plus the two observer facts: the returned slice
    denotes [text_delta observed current], and
    [snapshot_grows_to observed current]. *)
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
From stdpp Require Import sorting.
From New.proof.id Require Import id.
From New.proof.item Require Import item.
From New.proof.ytype Require Import ytype.
From New.proof.store Require Import store.
From New.proof.text Require Import text.
From New.proof.textobserver Require Import model value heap wp_private.
From New.proof.github_com.mit_pdos.perennial.goose.model Require Import strings.

(* iris.algebra / stdpp.sorting push [nat_scope], retuning the default [<] / [≤];
   the verified word-arithmetic proofs write [Z] comparisons unannotated, so
   restore [Z_scope] as the default. *)
Local Open Scope Z_scope.

Section text_observer.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Context {sync_pkg : sync.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.

Context {seq_inG : inG Σ (authR (gmapUR loc (gsetUR (YjsItem A))))}.

Context {acc_inG : inG Σ (authR (gsetUR YjsId))}.

Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO addressed_pool))}.

Local Notation P := go_string.

Local Notation TId := (TypeId P).

Local Notation Op := (TId * @YjsOperation A)%type.

Local Notation Ev := (@Event Op).

Local Notation DocModel := (gmap TId (list (YjsItem A))).

Local Notation snapshot := (list (YjsItem A * bool)).

(** The observer's certificates, read against the locked store: the
    snapshot it observed grows to the type's current one. [Hincl] is the
    whole-pool fragment against the item-set authority, [Hthis] its entry at
    this root, [Hbelow] the clocks below the observed state vector, [Hdelsub]
    the deleted-ids fragment against the delete-set authority. *)
#[local] Lemma observed_grows_to (observed : snapshot)
    (pool_items : gmap loc (gset (YjsItem A))) (p : pool) (parent : loc) (tm : type_model)
    (delete_set : gset YjsId) :
  pool_invs p ->
  p !! parent = Some tm ->
  YjsArrInvariant (tm_arr tm) ->
  YjsArrInvariant observed.*1 ->
  (∀ q S, pool_items !! q = Some S ->
     ∃ tm', p !! q = Some tm' ∧ S ⊆ (list_to_set (tm_arr tm') : gset (YjsItem A))) ->
  pool_items !! parent = Some (list_to_set observed.*1) ->
  (∀ c j, (j < sv_get (snapshot_state_vector observed) c)%nat ->
     ∃ q S y, pool_items !! q = Some S ∧ y ∈ S ∧ item_id y = MkYjsId c j) ->
  snapshot_deleted_ids observed ⊆ delete_set ->
  delete_set_tombstoned delete_set (all_runs p) ->
  snapshot_grows_to observed (runs_model (tm_runs tm)).
Proof.
  move=> Hinvs Hp Harr Hobs Hincl Hthis Hbelow Hdelsub Htomb.
  have Hcur : (runs_model (tm_runs tm)).*1 = tm_arr tm := runs_model_fst (tm_runs tm).
  have Hsub : ∀ x, x ∈ observed.*1 -> x ∈ tm_arr tm.
  { move=> x Hx. destruct (Hincl parent _ Hthis) as (tm' & Hp' & HS).
    rewrite Hp in Hp'. injection Hp' as <-.
    have Hx' : x ∈ (list_to_set observed.*1 : gset (YjsItem A)) by rewrite elem_of_list_to_set.
    have Hx'' := HS x Hx'. rewrite elem_of_list_to_set in Hx''. exact Hx''. }
  split_and!.
  - rewrite Hcur.
    exact (sorted_subseteq_sublist observed.*1 (tm_arr tm) Harr (yai_sorted _ Hobs) (yai_sorted _ Harr) Hsub).
  - move=> x Hx.
    have Hid : item_id x ∈ delete_set.
    { apply Hdelsub. apply elem_of_snapshot_deleted_ids. exists x. split; [exact Hx | reflexivity]. }
    have Hxarr : x ∈ tm_arr tm := Hsub x (elem_of_snapshot_fst _ _ _ Hx).
    (* the run holding [x] is tombstoned *)
    rewrite /tm_arr /runs_flatten list_elem_of_join in Hxarr.
    destruct Hxarr as (items & Hxitems & Hitems).
    apply list_elem_of_fmap in Hitems as (r & -> & Hr).
    have Hrall : r ∈ all_runs p by apply elem_of_all_runs; exists parent, tm.
    have Hdel : run_deleted r = true := Htomb r Hrall x Hxitems Hid.
    rewrite /runs_model list_elem_of_join. exists (run_models r). split.
    + rewrite /run_models list_elem_of_fmap. exists x. split; [by rewrite Hdel | exact Hxitems].
    + apply list_elem_of_fmap. exists r. split; [reflexivity | exact Hr].
  - move=> x y Hx Hy Hcl Hclk.
    rewrite Hcur in Hx.
    have Hbound := snapshot_state_vector_bound observed y Hy.
    have Hlt : (clock (item_id x) < sv_get (snapshot_state_vector observed) (clientId (item_id x)))%nat
      by rewrite Hcl; lia.
    destruct (Hbelow _ _ Hlt) as (q & S & z & Hq & Hz & Hzid).
    destruct (Hincl q S Hq) as (tm' & Hp' & HS).
    have Hzarr : z ∈ tm_arr tm'.
    { have Hz' := HS z Hz. rewrite elem_of_list_to_set in Hz'. exact Hz'. }
    have Hzx : item_id z = item_id x by rewrite Hzid; destruct (item_id x).
    destruct (pool_item_unique p q parent tm' tm z x Hinvs Hp' Hzarr Hp Hx Hzx) as [Hqp Hzx'].
    subst q z.
    rewrite Hq in Hthis. injection Hthis as HS'.
    rewrite HS' elem_of_list_to_set in Hz. exact Hz.
Qed.

(** The current snapshot's own contiguity certificate: every clock below its
    state vector is a char of some type ([pool_clocks_contiguous]). *)
#[local] Lemma current_below (p : pool) (parent : loc) (tm : type_model) (c j : nat) :
  pool_clocks_contiguous p ->
  p !! parent = Some tm ->
  (j < sv_get (snapshot_state_vector (runs_model (tm_runs tm))) c)%nat ->
  ∃ q S y, ((λ tm, (list_to_set (tm_arr tm) : gset (YjsItem A))) <$> p) !! q = Some S ∧
           y ∈ S ∧ item_id y = MkYjsId c j.
Proof.
  move=> Hcontig Hp Hj.
  destruct (snapshot_state_vector_witness _ c j Hj) as (y & Hy & Hc & Hle).
  rewrite runs_model_fst in Hy.
  have Hhas : pool_has p (item_id y) by exists parent, tm, y.
  destruct (decide (j = clock (item_id y))) as [-> | Hne].
  - exists parent, (list_to_set (tm_arr tm)), y.
    split_and!; [rewrite lookup_fmap Hp // | rewrite elem_of_list_to_set; exact Hy
                 | rewrite -Hc; by destruct (item_id y)].
  - destruct (Hcontig _ Hhas j ltac:(lia)) as (q & tm' & z & Hq & Hz & Hzid).
    exists q, (list_to_set (tm_arr tm')), z.
    split_and!; [rewrite lookup_fmap Hq // | rewrite elem_of_list_to_set; exact Hz | rewrite Hzid Hc //].
Qed.

(** The current snapshot's deleted ids are chars of the document, sitting in
    tombstoned runs: what growing the delete set by them takes. *)
#[local] Lemma current_deleted_ids_grow (m : DocModel) (bind : gmap P loc) (p : pool)
    (parent : loc) (tm : type_model) :
  pool_registry_coh bind p -> pool_registry_models m bind p ->
  p !! parent = Some tm ->
  (∀ i, i ∈ snapshot_deleted_ids (runs_model (tm_runs tm)) -> doc_model_has m i = true) ∧
  ids_tombstoned (snapshot_deleted_ids (runs_model (tm_runs tm))) (all_runs p).
Proof.
  move=> Hreg Hregmodel Hp. split.
  - move=> i Hi. apply elem_of_snapshot_deleted_ids in Hi as (x & Hx & <-).
    apply (pool_has_doc_model_has m bind p _ Hreg Hregmodel).
    exists parent, tm, x. split_and!; [exact Hp | | reflexivity].
    rewrite /tm_arr -runs_model_fst. exact (elem_of_snapshot_fst _ _ _ Hx).
  - move=> i Hi. apply elem_of_snapshot_deleted_ids in Hi as (x & Hx & <-).
    destruct (runs_model_elem_of _ _ _ Hx) as (r & Hr & Hxr & Hdel).
    exists r. split_and!.
    + apply elem_of_all_runs. exists parent, tm. split; [exact Hp | exact Hr].
    + symmetry. exact Hdel.
    + rewrite /char_ids elem_of_list_to_set list_elem_of_fmap. exists x. split; [reflexivity | exact Hxr].
Qed.

Lemma wp_TextObserver__Poll (obs t : loc) (γs : store_names) (γh : history_names)
    (c : ClientId) (name : P) (L : list (YjsItem A)) (deleted_ids : gset YjsId)
    (observed : snapshot) (h0 : list Ev) :
  {{{ is_pkg_init yjs ∗ own_TextObserver obs t γs γh name observed ∗
      is_Text t γs γh name L deleted_ids ∗ is_store_client γs c ∗ is_history_lb γh c h0 }}}
    obs @! (go.PointerType yjs.TextObserver) @! "Poll" #()
  {{{ (sl : slice.t) (current : snapshot), RET #sl;
      own_TextObserver obs t γs γh name current ∗
      own_delta sl (DfracOwn 1) (text_delta observed current) ∗
      ⌜snapshot_grows_to observed current⌝ ∗
      ⌜text_snapshot L current⌝ ∗ ⌜history_reflected h0 name current⌝ ∗
      ⌜visible_excludes deleted_ids current⌝ }}}.
Proof.
  wp_start as "(Hobs & #Htext & #Hpin & #Hlb)".
  iNamed "Hobs".
  iDestruct "Htext" as (tv' s_loc' parent' deleted_items)
    "(#Ht' & %Hstore' & %Hinner' & #His_store' & #His_hist & #Hbind' & #His_lb & #Hdeleted_lb' & #Hdeleted_items & %Hdeleted_known & %HsortedL)".
  iCombine "Ht Ht'" gives %Heqtv. subst tv'.
  subst s_loc' parent'.
  wp_auto.
  rewrite Hotext. subst s_loc parent.
  wp_auto.
  (* ---- the write lock: the store at its current model ---- *)
  wp_apply (wp_Store__wlock with "[$His_store]"). iIntros "[Hlk Hinv]".
  iDestruct "Hinv" as (c0 h m pend) "Hown".
  iDestruct "Hown" as (client k pdel locs p bind acc) "Hown". iNamed "Hown". subst c0.
  wp_auto.
  wp_apply wp_map_make1. iIntros (sv_mref) "Hsvm". wp_auto.
  wp_apply wp_map_make1. iIntros (del_mref) "Hdm". wp_auto.
  (* ---- what the locked store says, and what the certificates say against it ---- *)
  iDestruct (own_store_state_registry_coh with "Hstate") as %Hreg.
  iDestruct (own_store_state_run_pool_invs with "Hstate") as %Hpoolinv.
  iDestruct (own_store_state_arr_inv with "Hstate") as %Harrinv.
  iDestruct (own_store_state_clocks_contiguous with "Hstate") as %Hcontig.
  iDestruct (own_store_state_aligned with "Hstate") as %[Hdom Hlens].
  iDestruct (auth_gmap_gset_frag_lookup γs.(sn_seq) pool_items tv.(yjs.Text.inner') _ Hthis with "Hitems") as "#Hitems_this".
  iDestruct (auth_gmap_gset_lookup with "Hseq Hitems_this") as %(S' & HmS & Hobssub).
  rewrite lookup_fmap in HmS. apply fmap_Some in HmS as (tm & Htmp & ->).
  iDestruct (auth_gmap_gset_included with "Hseq Hitems") as %Hincl0.
  have Hincl : ∀ q S, pool_items !! q = Some S ->
      ∃ tm', p !! q = Some tm' ∧ S ⊆ (list_to_set (tm_arr tm') : gset (YjsItem A)).
  { move=> q S Hq. destruct (Hincl0 q S Hq) as (S'' & HS'' & Hsub).
    rewrite lookup_fmap in HS''. apply fmap_Some in HS'' as (tm' & Htm' & ->). eauto. }
  iDestruct "Hdelete_set" as (delete_set) "Hdelete_set". iNamed "Hdelete_set".
  iDestruct (auth_gset_frag_sub with "Hdelete_set_auth Hdeleted_lb") as %Hdelsub.
  iDestruct (auth_gset_frag_sub with "Hdelete_set_auth Hdeleted_lb'") as %Hdelsub'.
  have Harr : YjsArrInvariant (tm_arr tm) := Harrinv _ _ Htmp.
  have Hgrows : snapshot_grows_to observed (runs_model (tm_runs tm))
    := observed_grows_to observed pool_items p _ tm delete_set Hpoolinv Htmp Harr Hsorted Hincl Hthis Hbelow Hdelsub Hdelete_set_tomb.
  have [ls Hls] : is_Some (locs !! tv.(yjs.Text.inner')).
  { apply elem_of_dom. rewrite Hdom. apply elem_of_dom. eauto. }
  simpl in Hreg, Hpoolinv, Harrinv, Hcontig, Hdom, Hlens.
  (* ---- borrow this type's spine for the walk ---- *)
  iDestruct (own_store_state_ytype_acc tv.(yjs.Text.store') (MkStoreState client k locs p bind pend pdel) tv.(yjs.Text.inner') ls tm Hls Htmp with "Hstate") as "[Hyt Hclose]".
  iNamed "Hyt".
  subst t.
  wp_auto.
  iDestruct (own_dll_headptr with "Hdll") as "[%Hhd Hdll]".
  have Hhead : yt.(yjs.yType.start') = loc_at ls 0.
  { rewrite Hhd /loc_at. case_decide as Hd0; last lia. rewrite /= head_lookup //. }
  iDestruct (own_dll_length with "Hdll") as %Hlenls.
  (* the walk: after [kk] runs, the delta, the state vector and the deleted
     ids are those of the snapshot's first [kk] runs *)
  iAssert (∃ (kk : nat) (dsl : slice.t) (svm : gmap w64 w64),
    "Hcur" ∷ cur_ptr ↦ loc_at ls (Z.of_nat kk) ∗
    "Hdll" ∷ own_dll (DfracOwn 1) tv.(yjs.Text.inner') yt.(yjs.yType.start') tl null null ls tm.(tm_runs) ∗
    "Hdelta_ptr" ∷ delta_ptr ↦ dsl ∗
    "Hdelta" ∷ own_delta dsl (DfracOwn 1)
                 (delta_merge (per_char_delta observed (runs_model (take kk tm.(tm_runs))))) ∗
    "Hsv_ptr" ∷ stateVector_ptr ↦ sv_mref ∗
    "Hsvm" ∷ own_map sv_mref (DfracOwn 1) svm ∗
    "%Hsvm" ∷ ⌜state_vector_denotes svm (snapshot_state_vector (runs_model (take kk tm.(tm_runs))))⌝ ∗
    "Hdel_ptr" ∷ deleted_ptr ↦ del_mref ∗
    "Hdel" ∷ own_deleted_spans del_mref (snapshot_deleted_ids (runs_model (take kk tm.(tm_runs)))) ∗
    "%Hkk" ∷ ⌜(kk <= length tm.(tm_runs))%nat⌝)%I
    with "[cur Hdll delta stateVector Hsvm deleted Hdm]" as "IH".
  { iExists 0%nat, slice.nil, ∅. rewrite take_0 /= -Hhead.
    iFrame "cur Hdll delta stateVector Hsvm deleted".
    iSplitR; first iApply own_delta_nil.
    iSplitR.
    { iPureIntro. move=> cl. rewrite lookup_empty /sv_get lookup_empty /=. word. }
    iSplitL; first (iApply (own_deleted_spans_empty with "Hdm")).
    iPureIntro. lia. }
  wp_for "IH".
  destruct (decide (kk < length tm.(tm_runs))%nat) as [Hlt | Hge].
  - (* ---- one more run ---- *)
    iDestruct (loc_at_lt_not_null (DfracOwn 1) tv.(yjs.Text.inner') yt.(yjs.yType.start') tl ls tm.(tm_runs) kk ltac:(lia) with "Hdll") as "[%Hnn Hdll]".
    rewrite (bool_decide_eq_false_2 (loc_at ls (Z.of_nat kk) = null) Hnn). simpl negb.
    destruct (ls !! kk) as [lk|] eqn:Hlk; [| apply lookup_ge_None in Hlk; lia].
    destruct (tm.(tm_runs) !! kk) as [r|] eqn:Hrk; [| apply lookup_ge_None in Hrk; lia].
    iDestruct (own_dll_acc (DfracOwn 1) tv.(yjs.Text.inner') yt.(yjs.yType.start') tl ls tm.(tm_runs) kk lk r Hlk Hrk with "Hdll")
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
    wp_apply (wp_item__Len lk (DfracOwn 1) itemVal with "[$Hcval]"). iIntros "[Hcval %Hcontlen]".
    wp_auto.
    wp_apply (wp_item__Deleted lk (DfracOwn 1) itemVal with "[$Hcval]"). iIntros "Hcval".
    rewrite (flags_if_deleted itemVal (run_deleted r) Hflags).
    wp_auto.
    wp_apply (wp_map_lookup1 with "Hsvm"). iIntros "Hsvm".
    wp_auto.
    (* the run's client, clock range and content, off the node's fields *)
    have Hidw := Hid. rewrite /toYjsId /input_of_run /= in Hidw.
    have Hclient_w : uint.nat itemVal.(yjs.item.id').(yjs.id.clientId') = run_client r by rewrite /run_client -Hidw //.
    have Hclock_w : uint.nat itemVal.(yjs.item.id').(yjs.id.clock') = run_clock r by rewrite /run_clock -Hidw //.
    have Hstr : itemVal.(yjs.item.content').(yjs.content.content') = items_string (run_items r) := Hcontent.
    have Hrall : r ∈ all_runs p.
    { apply elem_of_all_runs. exists tv.(yjs.Text.inner'), tm. split; [exact Htmp | exact (list_elem_of_lookup_2 _ _ _ Hrk)]. }
    have Hfits : run_fits r := proj1 (proj2 (proj1 Hpoolinv r Hrall)).
    have Hend_w : uint.nat (w64_word_instance.(word.add) itemVal.(yjs.item.id').(yjs.id.clock') (W64 (length itemVal.(yjs.item.content').(yjs.content.content')))) = (run_clock r + length (run_items r))%nat.
    { rewrite Hstr Hclen. rewrite /run_fits in Hfits. word. }
    have Hstep_sv : snapshot_state_vector (runs_model (take (S kk) tm.(tm_runs)))
        = sv_join (snapshot_state_vector (runs_model (take kk tm.(tm_runs)))) (snapshot_state_vector (run_models r)).
    { rewrite (take_S_r _ _ _ Hrk) runs_model_app runs_model_singleton snapshot_state_vector_app //. }
    (* the token of this poll: the client's next clock ... *)
    wp_if_join (λ v, ⌜v = execute_val⌝ ∗
      "end" ∷ end_ptr ↦ w64_word_instance.(word.add) itemVal.(yjs.item.id').(yjs.id.clock') (W64 (length itemVal.(yjs.item.content').(yjs.content.content'))) ∗
      "Hsv_ptr" ∷ stateVector_ptr ↦ sv_mref ∗
      "client" ∷ client_ptr ↦ itemVal.(yjs.item.id').(yjs.id.clientId') ∗
      ∃ (svm' : gmap w64 w64),
        "Hsvm" ∷ own_map sv_mref (DfracOwn 1) svm' ∗
        "%Hsvm'" ∷ ⌜state_vector_denotes svm' (snapshot_state_vector (runs_model (take (S kk) tm.(tm_runs))))⌝)%I
      with "[end Hsv_ptr client Hsvm]".
    { wp_apply (wp_map_insert with "Hsvm"). iIntros "Hsvm". wp_auto.
      iSplitR; first done. iFrame "end Hsv_ptr client".
      iExists _. iFrame "Hsvm". iPureIntro. rewrite Hstep_sv.
      have Hsv' := state_vector_denotes_run svm _ _ _ r Hrun Hclient_w Hend_w Hsvm.
      rewrite decide_True in Hsv'; last exact l. exact Hsv'. }
    { iSplitR; first done. iFrame "end Hsv_ptr client".
      iExists svm. iFrame "Hsvm". iPureIntro. rewrite Hstep_sv.
      have Hsv' := state_vector_denotes_run svm _ _ _ r Hrun Hclient_w Hend_w Hsvm.
      rewrite decide_False in Hsv'; last (move=> Hbad; lia). exact Hsv'. }
    iIntros (v) "(-> & Hjoin)". iNamed "Hjoin". iDestruct "Hjoin" as (svm') "Hjoin". iNamed "Hjoin".
    wp_auto.
    (* ... and its tombstoned ids, one span per tombstoned run *)
    have Hstep_del : snapshot_deleted_ids (runs_model (take (S kk) tm.(tm_runs)))
        = snapshot_deleted_ids (runs_model (take kk tm.(tm_runs)))
          ∪ (if run_deleted r then char_ids (run_items r) else ∅).
    { rewrite (take_S_r _ _ _ Hrk) runs_model_app runs_model_singleton snapshot_deleted_ids_app
        snapshot_deleted_ids_run_models //. }
    wp_bind (If _ _ _)%E.
    iApply (wp_wand _ _ _ (λ v, ⌜v = execute_val⌝ ∗
      "start" ∷ start_ptr ↦ itemVal.(yjs.item.id').(yjs.id.clock') ∗
      "end" ∷ end_ptr ↦ w64_word_instance.(word.add) itemVal.(yjs.item.id').(yjs.id.clock') (W64 (length itemVal.(yjs.item.content').(yjs.content.content'))) ∗
      "client" ∷ client_ptr ↦ itemVal.(yjs.item.id').(yjs.id.clientId') ∗
      "Hdel_ptr" ∷ deleted_ptr ↦ del_mref ∗
      "Hdel" ∷ own_deleted_spans del_mref (snapshot_deleted_ids (runs_model (take (S kk) tm.(tm_runs)))))%I
      with "[start end client Hdel_ptr Hdel]").
    { destruct (run_deleted r) eqn:Hdel.
      - (* tombstoned: record the run's span at its client *)
        have Hjoin : ∀ d, d ∈ snapshot_deleted_ids (runs_model (take (S kk) tm.(tm_runs)))
            <-> d ∈ snapshot_deleted_ids (runs_model (take kk tm.(tm_runs)))
                ∨ span_covers itemVal.(yjs.item.id').(yjs.id.clientId')
                    (yjs.span.mk w64 itemVal.(yjs.item.id').(yjs.id.clock')
                       (w64_word_instance.(word.add) itemVal.(yjs.item.id').(yjs.id.clock')
                          (W64 (length itemVal.(yjs.item.content').(yjs.content.content'))))) d.
        { move=> d. rewrite Hstep_del elem_of_union. apply or_iff_compat_l. split.
          - move=> Hd. destruct (char_ids_run_covers r d Hrun Hd) as (Hc & Hlo & Hhi).
            split_and!; [rewrite Hclient_w; symmetry; exact Hc
                        | simpl; rewrite Hclock_w; exact Hlo
                        | simpl; rewrite Hend_w; exact Hhi].
          - move=> [Hc [Hlo Hhi]]. simpl in Hlo, Hhi.
            apply (run_covers_char_ids r d Hrun).
            split_and!; [rewrite -Hclient_w; symmetry; exact Hc
                        | rewrite -Hclock_w; exact Hlo
                        | rewrite -Hend_w; exact Hhi]. }
        iDestruct (own_deleted_spans_snoc del_mref _ _ _ _ Hjoin with "Hdel") as (dm sps) "(Hdm & Hssl & Hsslcap & Hdelback)".
        wp_auto.
        wp_apply (wp_map_lookup1 with "Hdm"). iIntros "Hdm". wp_auto.
        wp_apply wp_slice_literal. iSplitR; first done. iIntros "%s2 [Hs2 _]". wp_auto.
        wp_apply (wp_slice_append with "[$Hssl $Hsslcap $Hs2]"). iIntros (snew) "(Hsnew & Hsnewcap & _)". wp_auto.
        wp_apply (wp_map_insert with "Hdm"). iIntros "Hdm". wp_auto.
        iDestruct ("Hdelback" with "Hsnew Hsnewcap Hdm") as "Hdel".
        iSplitR; first done. iFrame "start end client Hdel_ptr Hdel".
      - (* live: nothing to record *)
        wp_auto. iSplitR; first done. iFrame "start end client Hdel_ptr".
        rewrite Hstep_del union_empty_r_L. iFrame "Hdel". }
    iIntros (v) "(-> & Hjoin)". iNamed "Hjoin".
    wp_auto.
    wp_apply (wp_map_lookup1 with "Hstate_vector"). iIntros "Hstate_vector".
    wp_auto.
    (* ---- the classification, char by char ---- *)
    rewrite /run_fits in Hfits.
    have Huniq : uniqueId (runs_model tm.(tm_runs)).*1 by rewrite runs_model_fst; exact (yai_unique _ Harr).
    have HuniqObs : uniqueId observed.*1 := yai_unique _ Hsorted.
    have Hoe : uint.nat (default (W64 0) (state_vector !! itemVal.(yjs.item.id').(yjs.id.clientId')))
               = sv_get (snapshot_state_vector observed) (run_client r).
    { rewrite (Hstate_vector _) Hclient_w //. }
    iAssert (∃ (i : nat) (dsl : slice.t),
      "Hi" ∷ i_ptr ↦ W64 i ∗
      "Hdelta_ptr" ∷ delta_ptr ↦ dsl ∗
      "Hdelta" ∷ own_delta dsl (DfracOwn 1)
                   (delta_merge (per_char_delta observed
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
      have Hxcur : x ∈ (runs_model tm.(tm_runs)).*1.
      { rewrite runs_model_fst /tm_arr /runs_flatten list_elem_of_join. exists (run_items r).
        split; [exact (list_elem_of_lookup_2 _ _ _ Hx) |].
        apply list_elem_of_fmap. exists r. split; [done | exact (list_elem_of_lookup_2 _ _ _ Hrk)]. }
      have Hclass := state_vector_classifies observed _ x Hgrows Huniq Hxcur.
      rewrite Hxid /= in Hclass.
      have Hrm : run_models r !! i = Some (x, run_deleted r) by rewrite /run_models list_lookup_fmap Hx //.
      have Hstep_i : runs_model (take kk tm.(tm_runs)) ++ take (S i) (run_models r)
                   = (runs_model (take kk tm.(tm_runs)) ++ take i (run_models r)) ++ [(x, run_deleted r)].
      { rewrite (take_S_r _ _ _ Hrm) app_assoc //. }
      have Hclock_i : uint.nat (w64_word_instance.(word.add) itemVal.(yjs.item.id').(yjs.id.clock') (W64 i)) = (run_clock r + i)%nat by word.
      wp_auto.
      have Hidx : MkYjsId (uint.nat itemVal.(yjs.item.id').(yjs.id.clientId'))
                    (uint.nat (w64_word_instance.(word.add) itemVal.(yjs.item.id').(yjs.id.clock') (W64 i)))
                  = item_id x by rewrite Hclient_w Hclock_i Hxid //.
      destruct (decide (x ∈ observed.*1)) as [Hxobs | Hxnew].
      * (* a known char *)
        have Hlt_nat := proj2 Hclass Hxobs.
        rewrite (bool_decide_eq_true_2 (uint.Z (w64_word_instance.(word.add) itemVal.(yjs.item.id').(yjs.id.clock') (W64 i)) < uint.Z (default (W64 0) (state_vector !! itemVal.(yjs.item.id').(yjs.id.clientId'))))%Z); last word.
        wp_auto.
        wp_apply (wp_TextObserver__deletedContains with "[$Hobs $Hdeleted]").
        iIntros "[Hobs Hdeleted]".
        rewrite Hidx.
        have Hdelclass := deleted_ids_classify observed x HuniqObs Hxobs.
        destruct (decide ((x, true) ∈ observed)) as [Hxdel | Hxlive].
        { (* known and already tombstoned: nothing *)
          rewrite (bool_decide_eq_true_2 (item_id x ∈ snapshot_deleted_ids observed)); last by apply Hdelclass.
          wp_auto. wp_for_post.
          iFrame "Hobs Hdeleted HΦ o s Hlk Hseq HtypesAuth Hhist Hacc Hdelete_set_auth Hparent Hclose Hcur Hcol Hcor Hback length tombstoned Hcval Hsv_ptr Hsvm start client Hdel_ptr Hdel observedEnd Hstate_vector".
          iExists (S i), dsl0.
          replace (w64_word_instance.(word.add) (W64 i) (W64 1)) with (W64 (S i)) by word.
          iFrame "Hi Hdelta_ptr".
          have Hmerge : delta_merge (per_char_delta observed (runs_model (take kk tm.(tm_runs)) ++ take (S i) (run_models r)))
                      = delta_merge (per_char_delta observed (runs_model (take kk tm.(tm_runs)) ++ take i (run_models r))).
          { rewrite Hstep_i per_char_delta_app per_char_delta_singleton /delta_step /=.
            rewrite decide_True; last exact Hxobs. rewrite decide_True; last exact Hxdel. rewrite app_nil_r //. }
          rewrite Hmerge. iFrame "Hdelta". iPureIntro. lia. }
        rewrite (bool_decide_eq_false_2 (item_id x ∈ snapshot_deleted_ids observed)); last (move=> Hin; apply Hxlive; apply Hdelclass; exact Hin).
        wp_auto.
        destruct (run_deleted r) eqn:Hdel.
        { (* known, live before, tombstoned now: one delete *)
          wp_auto.
          wp_apply (wp_deltaSnoc _ _ _ (Delete 1) with "[$Hdelta]").
          { iPureIntro. split; reflexivity. }
          iIntros (dsl') "Hdelta". wp_auto. wp_for_post.
          iFrame "Hobs Hdeleted HΦ o s Hlk Hseq HtypesAuth Hhist Hacc Hdelete_set_auth Hparent Hclose Hcur Hcol Hcor Hback length tombstoned Hcval Hsv_ptr Hsvm start client Hdel_ptr Hdel observedEnd Hstate_vector".
          iExists (S i), dsl'.
          replace (w64_word_instance.(word.add) (W64 i) (W64 1)) with (W64 (S i)) by word.
          iFrame "Hi Hdelta_ptr".
          have Hmerge : delta_merge (per_char_delta observed (runs_model (take kk tm.(tm_runs)) ++ take (S i) (run_models r)))
                      = delta_snoc (delta_merge (per_char_delta observed (runs_model (take kk tm.(tm_runs)) ++ take i (run_models r)))) (Delete 1).
          { rewrite Hstep_i per_char_delta_app per_char_delta_singleton delta_merge_snoc_option /delta_step /=.
            rewrite decide_True; last exact Hxobs. rewrite decide_False; last exact Hxlive. rewrite Hxb //. }
          rewrite Hmerge. iFrame "Hdelta". iPureIntro. lia. }
        { (* known and still live: one retain *)
          wp_auto.
          wp_apply (wp_deltaSnoc _ _ _ (Retain 1) with "[$Hdelta]").
          { iPureIntro. split; reflexivity. }
          iIntros (dsl') "Hdelta". wp_auto. wp_for_post.
          iFrame "Hobs Hdeleted HΦ o s Hlk Hseq HtypesAuth Hhist Hacc Hdelete_set_auth Hparent Hclose Hcur Hcol Hcor Hback length tombstoned Hcval Hsv_ptr Hsvm start client Hdel_ptr Hdel observedEnd Hstate_vector".
          iExists (S i), dsl'.
          replace (w64_word_instance.(word.add) (W64 i) (W64 1)) with (W64 (S i)) by word.
          iFrame "Hi Hdelta_ptr".
          have Hmerge : delta_merge (per_char_delta observed (runs_model (take kk tm.(tm_runs)) ++ take (S i) (run_models r)))
                      = delta_snoc (delta_merge (per_char_delta observed (runs_model (take kk tm.(tm_runs)) ++ take i (run_models r)))) (Retain 1).
          { rewrite Hstep_i per_char_delta_app per_char_delta_singleton delta_merge_snoc_option /delta_step /=.
            rewrite decide_True; last exact Hxobs. rewrite decide_False; last exact Hxlive. rewrite Hxb //. }
          rewrite Hmerge. iFrame "Hdelta". iPureIntro. lia. }
      * (* a new char *)
        have Hnlt : ¬ (run_clock r + i < sv_get (snapshot_state_vector observed) (run_client r))%nat.
        { move=> Hlt'. apply Hxnew. apply Hclass. exact Hlt'. }
        rewrite (bool_decide_eq_false_2 (uint.Z (w64_word_instance.(word.add) itemVal.(yjs.item.id').(yjs.id.clock') (W64 i)) < uint.Z (default (W64 0) (state_vector !! itemVal.(yjs.item.id').(yjs.id.clientId'))))%Z); last (move=> Hlt'; apply Hnlt; word).
        wp_auto.
        destruct (run_deleted r) eqn:Hdel.
        { (* new and already tombstoned: nothing *)
          wp_auto. wp_for_post.
          iFrame "Hobs Hdeleted HΦ o s Hlk Hseq HtypesAuth Hhist Hacc Hdelete_set_auth Hparent Hclose Hcur Hcol Hcor Hback length tombstoned Hcval Hsv_ptr Hsvm start client Hdel_ptr Hdel observedEnd Hstate_vector".
          iExists (S i), dsl0.
          replace (w64_word_instance.(word.add) (W64 i) (W64 1)) with (W64 (S i)) by word.
          iFrame "Hi Hdelta_ptr".
          have Hmerge : delta_merge (per_char_delta observed (runs_model (take kk tm.(tm_runs)) ++ take (S i) (run_models r)))
                      = delta_merge (per_char_delta observed (runs_model (take kk tm.(tm_runs)) ++ take i (run_models r))).
          { rewrite Hstep_i per_char_delta_app per_char_delta_singleton /delta_step /=.
            rewrite decide_False; last exact Hxnew. rewrite app_nil_r //. }
          rewrite Hmerge. iFrame "Hdelta". iPureIntro. lia. }
        (* new and live: insert its char; the content is a Go string, so the
           [uint64] offset is a valid [int] index ([Len] said so) *)
        wp_auto.
        have Hi63z : (Z.of_nat i < 2^63)%Z by (rewrite Hstr Hclen in Hcontlen; lia).
        replace (sint.nat (W64 i)) with i by word.
        rewrite Hb.
        wp_auto.
        wp_apply (wp_deltaSnoc _ _ _ (Insert (content x)) with "[$Hdelta]").
        { iPureIntro. split; [reflexivity | rewrite Hxb //]. }
        iIntros (dsl') "Hdelta". wp_auto. wp_for_post.
        iFrame "Hobs Hdeleted HΦ o s Hlk Hseq HtypesAuth Hhist Hacc Hdelete_set_auth Hparent Hclose Hcur Hcol Hcor Hback length tombstoned Hcval Hsv_ptr Hsvm start client Hdel_ptr Hdel observedEnd Hstate_vector".
        iExists (S i), dsl'.
        replace (w64_word_instance.(word.add) (W64 i) (W64 1)) with (W64 (S i)) by word.
        iFrame "Hi Hdelta_ptr".
        have Hmerge : delta_merge (per_char_delta observed (runs_model (take kk tm.(tm_runs)) ++ take (S i) (run_models r)))
                    = delta_snoc (delta_merge (per_char_delta observed (runs_model (take kk tm.(tm_runs)) ++ take i (run_models r)))) (Insert (content x)).
        { rewrite Hstep_i per_char_delta_app per_char_delta_singleton delta_merge_snoc_option /delta_step /=.
          rewrite decide_False; last exact Hxnew. done. }
        rewrite Hmerge. iFrame "Hdelta". iPureIntro. lia.
    + (* the run's chars are classified: on to the next node *)
      rewrite (bool_decide_eq_false_2 (uint.Z (W64 i) < uint.Z (W64 (length itemVal.(yjs.item.content').(yjs.content.content'))))%Z); last (rewrite Hstr Hclen; word).
      have Hieq : i = length (run_items r) by lia.
      wp_auto.
      wp_for_post.
      iAssert (own_item_node lk (DfracOwn 1) (input_of_run r) (run_deleted r) tv.(yjs.Text.inner') prevk nxtk)
        with "[Hcval Hcol Hcor]" as "Hnode".
      { iExists itemVal, olidk, oridk. iFrame "Hcval Hcol Hcor". iPureIntro.
        split_and!; [exact Hinl | exact Hinr | exact Hid | exact Hcontent | exact Hpark | exact Hprevk | exact Hnextk | exact Hflags]. }
      iDestruct ("Hback" with "Hnode") as "Hdll".
      iFrame "Hobs Hstate_vector Hdeleted HΦ o s Hlk Hseq HtypesAuth Hhist Hacc Hdelete_set_auth Hparent Hclose".
      iExists (S kk), dsl0, svm'.
      rewrite Hcr. replace (Z.of_nat kk + 1)%Z with (Z.of_nat (S kk)) by lia.
      iFrame "Hcur Hdll Hdelta_ptr Hsv_ptr Hsvm Hdel_ptr Hdel".
      have Hfull : runs_model (take kk tm.(tm_runs)) ++ take i (run_models r) = runs_model (take (S kk) tm.(tm_runs)).
      { have Hlenrm : length (run_models r) = length (run_items r) by rewrite /run_models length_fmap //.
        rewrite Hieq (take_ge (run_models r) (length (run_items r))); last lia.
        rewrite (take_S_r _ _ _ Hrk) runs_model_app runs_model_singleton //. }
      iEval (rewrite Hfull) in "Hdelta". iFrame "Hdelta".
      iPureIntro. split; [exact Hsvm' | lia].
  - (* ---- the walk is done: the current snapshot is the observed one now ---- *)
    have Hkeq : kk = length tm.(tm_runs) by lia.
    have Hnull : loc_at ls (Z.of_nat kk) = null.
    { rewrite /loc_at decide_True; [| lia]. rewrite Nat2Z.id lookup_ge_None_2; [done | lia]. }
    rewrite (bool_decide_eq_true_2 (loc_at ls (Z.of_nat kk) = null) Hnull).
    simpl negb.
    rewrite decide_False; [| done]. rewrite decide_True; [| done].
    rewrite Hkeq take_ge in Hsvm; last lia.
    iEval (rewrite Hkeq take_ge; last lia) in "Hdelta".
    iEval (rewrite Hkeq take_ge; last lia) in "Hdel".
    wp_auto.
    (* the certificates for the next poll: the whole pool's item sets and
       the current deleted ids, minted from the authorities *)
    set (M := (λ tm0 : type_model, (list_to_set (tm_arr tm0) : gset (YjsItem A))) <$> p).
    have HMsub : ∀ (q : loc) (S1 S2 : gset (YjsItem A)), M !! q = Some S1 -> M !! q = Some S2 -> S1 ⊆ S2.
    { move=> q S1 S2 H1 H2. rewrite H1 in H2. injection H2 as <-. done. }
    iMod (auth_gmap_gset_grow_snap γs.(sn_seq) M M (reflexivity _) HMsub with "Hseq") as "[Hseq #Hitems_new]".
    iAssert (own_delete_set γs m (all_runs p)) with "[Hdelete_set_auth]" as "Hdelete_set".
    { iExists delete_set. iFrame "Hdelete_set_auth". iPureIntro.
      split; [exact Hdelete_set_dom | exact Hdelete_set_tomb]. }
    destruct (current_deleted_ids_grow m bind p _ tm Hreg Hregmodel Htmp) as [Hdom_cur Htomb_cur].
    iMod (own_delete_set_grow γs m p (snapshot_deleted_ids (runs_model tm.(tm_runs))) Hpoolinv Hdom_cur Htomb_cur with "Hdelete_set") as "[Hdelete_set #Hdellb_new]".
    (* the read API's facts about the current snapshot *)
    iDestruct (is_store_client_agree with "Hclientpin Hpin") as %Heqc. subst c.
    iDestruct (is_history_lb_prefix with "Hhist Hlb") as %Hpref.
    iDestruct (ghost_map_lookup with "HtypesAuth Hbind") as %Hbindlk.
    iDestruct (auth_gmap_gset_lookup with "Hseq His_lb") as %(SL & HmSL & HLsub).
    rewrite /M lookup_fmap Htmp /= in HmSL. injection HmSL as <-.
    have Hsnap : text_snapshot L (runs_model tm.(tm_runs)).
    { split; rewrite runs_model_fst; [exact HLsub | exact Harr]. }
    have Hhistref : history_reflected h0 name (runs_model tm.(tm_runs)).
    { move=> input Hin.
      have Hin' : (RootId name, OpInsert input) ∈ delivered_ops h.
      { destruct (delivered_ops_prefix h0 h Hpref) as [rest ->]. rewrite elem_of_app. by left. }
      destruct (delivered_docm_mem h m (RootId name) input Hhcoh Hin') as (it & Hitid & Hitmem).
      destruct Hregmodel as [Hmtypes _].
      rewrite (Hmtypes name _ tm Hbindlk Htmp) in Hitmem.
      exists it. split; [exact Hitid | rewrite runs_model_fst; exact Hitmem]. }
    have Hexcl : visible_excludes deleted_ids (runs_model tm.(tm_runs)).
    { apply visible_excludes_of_bits => x b Hin Hid.
      destruct (runs_model_elem_of _ _ _ Hin) as (r & Hr & Hx & ->).
      have Hrall : r ∈ all_runs p by apply elem_of_all_runs; exists tv.(yjs.Text.inner'), tm.
      exact (Hdelete_set_tomb r Hrall x Hx (Hdelsub' (item_id x) Hid)). }
    (* the store goes back whole, and the lock is released *)
    iDestruct ("Hclose" with "[Hparent Hdll]") as "Hstate".
    { iExists yt, tl. iFrame "Hparent Hdll". iPureIntro. exact Hlen. }
    wp_apply (wp_Store__wunlock _ _ _ (uint.nat client) h m pend with "[$His_store $Hlk Hstate Hseq HtypesAuth Hhist Hacc Hdelete_set]").
    { iExists client, k, pdel, locs, p, bind, acc. iFrame "∗#". iPureIntro.
      split_and!; [reflexivity | exact Hpendroot | exact Hpendbnd | exact Hregmodel | exact Hhcoh | exact Hctr | exact Hacccoh]. }
    iAssert (own_TextObserver obs ov.(yjs.TextObserver.text') γs γh name (runs_model tm.(tm_runs)))
      with "[Hobs Hsvm Hdel]" as "Hobs_new".
    { iExists (ov <| yjs.TextObserver.stateVector' := sv_mref |> <| yjs.TextObserver.deleted' := del_mref |>),
        tv, tv.(yjs.Text.store'), tv.(yjs.Text.inner'), svm, M.
      iFrame "Hobs Ht His_store Hbind Hitems_new Hdellb_new". simpl. iFrame "Hsvm Hdel".
      iPureIntro. split_and!;
        [reflexivity | reflexivity | reflexivity | exact Hsvm
        | rewrite /M lookup_fmap Htmp /= runs_model_fst //
        | move=> c0 j Hj; exact (current_below p _ tm c0 j Hcontig Htmp Hj)
        | rewrite runs_model_fst; exact Harr]. }
    (* ---- the trailing retain is implicit ---- *)
    iNamed "Hdelta".
    iDestruct (own_slice_len with "Hsl") as %[Hsllen Hsllen0].
    iDestruct (own_slice_wf with "Hsl") as %Hslwf.
    set (dm := delta_merge (per_char_delta observed (runs_model tm.(tm_runs)))).
    have Hlenvs : length vs = length dm by eapply Forall2_length; exact Hdenote.
    have Htd : text_delta observed (runs_model tm.(tm_runs)) = delta_drop_trailing_retain dm by done.
    destruct (decide (0 < length vs)%nat) as [Hpos | Hzero]; last first.
    { (* the empty delta: nothing to drop *)
      rewrite (bool_decide_eq_false_2 (sint.Z (W64 0) < sint.Z dsl.(slice.len))%Z); last word.
      have Hvs : vs = [] by destruct vs; [done | simpl in Hzero; lia].
      have Hdm : dm = [] by destruct dm; [done | rewrite Hvs in Hlenvs; simpl in Hlenvs; lia].
      wp_auto.
      iApply ("HΦ" $! dsl (runs_model tm.(tm_runs))).
      iFrame "Hobs_new". iSplitL.
      { rewrite Htd Hdm /delta_drop_trailing_retain /=. iExists vs. iFrame "Hsl Hcap". iPureIntro.
        rewrite Hvs. constructor. }
      iPureIntro. split_and!; [exact Hgrows | exact Hsnap | exact Hhistref | exact Hexcl]. }
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
      iApply ("HΦ" $! _ (runs_model tm.(tm_runs))).
      iFrame "Hobs_new". iSplitL.
      { iExists _. iFrame "Hsl' Hcap'". iPureIntro.
        rewrite Htd /delta_drop_trailing_retain Hlastdm /subslice.
        replace (sint.nat (W64 0)) with 0%nat by word. rewrite drop_0.
        replace (sint.nat (w64_word_instance.(word.sub) dsl.(slice.len) (W64 1))) with (length vs - 1)%nat by word.
        rewrite removelast_firstn_len -Hlenvs.
        replace (pred (length vs)) with (length vs - 1)%nat by lia.
        apply Forall2_take. exact Hdenote. }
      iPureIntro. split_and!; [exact Hgrows | exact Hsnap | exact Hhistref | exact Hexcl].
    + (* a trailing insert: kept *)
      rewrite Hk1 (bool_decide_eq_false_2 (W8 1 = W8 0)); last done.
      wp_auto.
      iApply ("HΦ" $! dsl (runs_model tm.(tm_runs))).
      iFrame "Hobs_new". iSplitL.
      { rewrite Htd /delta_drop_trailing_retain Hlastdm. iExists vs. iFrame "Hsl Hcap". iPureIntro. exact Hdenote. }
      iPureIntro. split_and!; [exact Hgrows | exact Hsnap | exact Hhistref | exact Hexcl].
    + (* a trailing delete: kept *)
      rewrite Hk1 (bool_decide_eq_false_2 (W8 2 = W8 0)); last done.
      wp_auto.
      iApply ("HΦ" $! dsl (runs_model tm.(tm_runs))).
      iFrame "Hobs_new". iSplitL.
      { rewrite Htd /delta_drop_trailing_retain Hlastdm. iExists vs. iFrame "Hsl Hcap". iPureIntro. exact Hdenote. }
      iPureIntro. split_and!; [exact Hgrows | exact Hsnap | exact Hhistref | exact Hexcl].
Qed.

End text_observer.
