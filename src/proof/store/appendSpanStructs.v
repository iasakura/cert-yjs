(** Reading integrated nodes back as wire structs (issue #131):
    [store.rootName] (the name a root type is registered under, by a scan of
    the registry), [store.updateItemOfNode] (the decoded struct of one node)
    and [store.appendSpanStructs] (the structs of the nodes covering one
    recorded span). The first two are private to the store and their specs
    are stated over the store's data fields, [own_store_state], at any
    fraction. [appendSpanStructs] is called by [Transaction.insertedStructs]
    ([transaction/insertedStructs]), so its spec takes and returns the store
    whole, [own_store]. *)
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
From New.proof.sync_proof Require Import base mutex rwmutex rwmutex_guard.
From New.proof Require Import tok_set.
From iris.algebra Require Import auth gmap gset.
From iris.algebra.lib Require Import dfrac_agree.
From stdpp Require Import sorting.
Local Open Scope Z_scope.
From New.proof Require Import map_range.
From New.proof.store Require Import model value heap wp_private GetNode.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Section store_appendSpanStructs.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

Notation A := (list w16).

Notation P := go_string.

Local Notation TId := (TypeId P).

Local Notation Op := (TId * @YjsOperation A)%type.

Local Notation Ev := (@Event Op).

Local Notation DocModel := (gmap TId (list (YjsItem A))).

Context {sync_pkg : sync.Assumptions}.

Notation seqUR := (authR (gmapUR loc (gsetUR (YjsItem A)))).

Context {seq_inG : inG Σ seqUR}.

Notation accUR := (authR (gsetUR YjsId)).

Context {acc_inG : inG Σ accUR}.

Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO store_state))}.
(* the observers' tokens and registrations (issue #198 Part II), as [store/heap] *)
Context {observed_inG : ghost_varG Σ (list (YjsItem A * bool))}.
Context {observers_inG : inG Σ (authR (gsetUR (gname * go_string)))}.
Context {observers_agree_inG : inG Σ (dfrac_agreeR (leibnizO registered_entries))}.

(* ===== lemmas ============================================================= *)

(** [store.rootName]: the name the registry binds to a registered type. The
    registry's coherence ([pool_registry_coh]) gives every type of the pool
    exactly one name, so the scan's one match is that name. *)
Lemma wp_store__rootName (s parent : loc) (q : Qp) (state : store_state) :
  {{{ is_pkg_init yjs ∗ own_store_state s q state ∗
      ⌜is_Some (ss_pool state !! parent)⌝ }}}
    s @! (go.PointerType yjs.store) @! "rootName" #parent
  {{{ (name : go_string), RET #name;
      own_store_state s q state ∗ ⌜ss_bind state !! name = Some parent⌝ }}}.
Proof using Type*.
  iIntros (Φ) "(#Hpkg & Hstate & %Hregistered) HΦ".
  destruct state as [client0 clock0 locs p bind pend pdel]. simpl in *.
  iDestruct "Hstate" as "(Hfields & %Hinvs)".
  have Hcoh : pool_registry_coh bind p := proj1 (proj2 Hinvs).
  destruct Hcoh as (Hbound & Hinjective & Hnamed).
  destruct (Hnamed parent Hregistered) as [name0 Hname0].
  iDestruct "Hfields" as "(Hclient & Hclock & HdeletedSet & Hitems & Hregistry & Htypes & Hpending & Hpdeletes)".
  iDestruct "Hregistry" as (types_mref) "(Htypesf & Htypesmap)".
  iEval (simpl) in "Hclient Hclock Hitems Htypesmap Htypes Hpending Hpdeletes".
  wp_method_call. wp_call. wp_call. wp_auto.
  (* the scan keeps half of the registry map for its lookups; the range
     holds the other half until the loop ends *)
  iAssert (types_mref ↦${DfracOwn (q / 2 + q / 2)} bind)%I with "[Htypesmap]" as "Htypesmap";
    first by rewrite Qp.div_2.
  iDestruct (own_map_dfrac_split with "Htypesmap") as "[Htypesmap Htypesmap_lookup]".
  (* once the type's one name has been passed, [result] holds it *)
  wp_apply (wp_map_for_range_keep (λ (keys : list go_string) (i : Z),
      ∃ (result name : go_string),
        "s" ∷ s_ptr ↦ s ∗ "Htypesf" ∷ s.[yjs.store.t, "types"] ↦{#q} types_mref ∗
        "Htypesmap_lookup" ∷ types_mref ↦${DfracOwn (q/2)} bind ∗
        "parent" ∷ parent_ptr ↦ parent ∗ "result" ∷ result_ptr ↦ result ∗
        "name" ∷ name_ptr ↦ name ∗
        "%Hfound" ∷ ⌜(0 ≤ i)%Z ∧ (name0 ∈ take (Z.to_nat i) keys → result = name0)⌝)%I
      with "Htypesmap").
  iIntros (keys) "%Hkeys". destruct Hkeys as (Hkeysdom & Hkeyslen & Hkeysnodup).
  iSplitL "s Htypesf Htypesmap_lookup parent result name".
  { iExists _, _. iFrame. iPureIntro. split; first lia. rewrite take_0. by move=> /elem_of_nil. }
  iSplitR.
  { iModIntro. iIntros (i key v [Hkey Hval]) "Hinv". iNamed "Hinv". destruct Hfound as [Hi Hfound].
    wp_auto.
    wp_apply (wp_map_lookup1 with "Htypesmap_lookup"). iIntros "Htypesmap_lookup".
    rewrite Hval /=.
    have Hstep : ∀ result', (key = name0 → result' = name0) → (key ≠ name0 → result' = result) →
        name0 ∈ take (Z.to_nat (i + 1)) keys → result' = name0.
    { move=> result' Hyes Hno. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
      rewrite (take_S_r _ _ _ Hkey) elem_of_app list_elem_of_singleton.
      destruct (decide (key = name0)) as [Heq | Hne]; first (move=> _; exact (Hyes Heq)).
      move=> [Hin | Heq]; [rewrite (Hno Hne); exact (Hfound Hin) | by subst]. }
    wp_auto.
    destruct (decide (v = parent)) as [-> | Hne].
    - rewrite bool_decide_eq_true_2 //. wp_auto. iSplitR; first done.
      iExists _, _. iFrame. iPureIntro. split; first lia.
      have Hkey_name : key = name0 := Hinjective key name0 parent Hval Hname0.
      apply Hstep; [done | by move=> Hne].
    - rewrite bool_decide_eq_false_2 //. wp_auto. iSplitR; first done.
      iExists _, _. iFrame. iPureIntro. split; first lia.
      apply Hstep; last done. move=> Heq. subst key. rewrite Hname0 in Hval. by injection Hval. }
  iIntros "Hinv Htypesmap". iNamed "Hinv". destruct Hfound as [_ Hfound]. wp_auto.
  iDestruct (own_map_dfrac_split with "[$Htypesmap $Htypesmap_lookup]") as "Htypesmap".
  iEval (rewrite Qp.div_2) in "Htypesmap".
  have Hresult : result = name0.
  { apply Hfound. rewrite -Hkeyslen firstn_all2; last lia.
    apply (elem_of_list_to_set (C := gset go_string)). rewrite Hkeysdom. apply elem_of_dom. by eexists. }
  subst result.
  iApply ("HΦ" $! name0). iSplitL; last done.
  iSplitL; last done. rewrite /own_store_fields /=.
  iFrame "Hclient Hclock HdeletedSet Hitems Htypes Hpending Hpdeletes".
  iExists types_mref. iFrame "Htypesf Htypesmap".
Qed.

(** The wire item of a well-formed per-char run expands to its items'
    inputs: the head keeps the run's origins, every later unit has the unit
    before it as left origin and the run's right origin. *)
#[local] Lemma expand_input_input_of_run (tid : TId) (r : ItemRun) :
  run_wf (run_items r) -> run_per_char r ->
  expand_input (tid, input_of_run r) = (λ it, (tid, input_of_item it)) <$> run_items r.
Proof.
  move=> Hrun Hper_char.
  have Hhead : run_items r !! 0%nat = Some (run_head_item r).
  { rewrite /run_head_item. destruct Hrun as [Hrun_nonempty _].
    destruct (run_items r); [done | reflexivity]. }
  rewrite /expand_input /ops_of_input /=.
  rewrite /run_per_char in Hper_char. rewrite -Hper_char.
  apply list_eq => index. rewrite !list_lookup_fmap.
  destruct (run_items r !! index) as [it |] eqn:Hit; last first.
  { rewrite lookup_ge_None_2 //. rewrite ops_from_length length_fmap.
    by apply lookup_ge_None. }
  have [op Hop] : is_Some (ops_from (clientId (item_id (run_head_item r))) (clock (item_id (run_head_item r)))
      (origin_id (origin (run_head_item r))) (origin_id (rightOrigin (run_head_item r)))
      (content <$> run_items r) !! index).
  { apply lookup_lt_is_Some. rewrite ops_from_length length_fmap. exact (lookup_lt_Some _ _ _ Hit). }
  rewrite Hop /=. f_equal. f_equal.
  destruct (ops_from_lookup _ _ _ _ _ _ _ Hop) as (Hop_id & Hop_right & Hop_content & Hop_first & Hop_later).
  rewrite list_lookup_fmap Hit /= in Hop_content. injection Hop_content as Hop_content.
  destruct op as [op_origin op_right op_content op_id]. simpl in *. rewrite /input_of_item. subst.
  f_equal.
  - destruct index as [| before_index].
    + rewrite Hhead in Hit. injection Hit as <-. exact (Hop_first eq_refl).
    + rewrite (Hop_later before_index eq_refl).
      have [before_item Hbefore_item] : is_Some (run_items r !! before_index).
      { apply lookup_lt_is_Some. apply lookup_lt_Some in Hit. lia. }
      destruct ((proj2 Hrun) before_index before_item it Hbefore_item Hit) as (_ & Horigin & _).
      rewrite Horigin /=.
      by rewrite (run_wf_lookup_clock (run_items r) before_index (run_head_item r) before_item Hrun Hhead Hbefore_item).
  - by rewrite (run_wf_lookup_rightOrigin (run_items r) index (run_head_item r) it Hrun Hhead Hit).
  - by rewrite (run_wf_lookup_clock (run_items r) index (run_head_item r) it Hrun Hhead Hit).
Qed.

(** [store.updateItemOfNode]: the decoded struct of the part [start, stop) of
    the node at slot [k] of the type at [parent] denotes the wire item of
    that part of the slot's run (the run cut at both ends, [split_run_right]
    then [split_run_left]), under the name the registry binds to the type.
    The struct shares the node's right origin cell and content, both
    read-only. *)
Lemma wp_store__updateItemOfNode (s lc parent : loc) (q : Qp) (state : store_state)
    (ls : list loc) (tm : type_model) (k : nat) (r : ItemRun) (start stop : w64) :
  ss_locs state !! parent = Some ls ->
  ss_pool state !! parent = Some tm ->
  ls !! k = Some lc ->
  tm_runs tm !! k = Some r ->
  (uint.nat start < uint.nat stop <= length (run_items r))%nat ->
  {{{ is_pkg_init yjs ∗ own_store_state s q state }}}
    s @! (go.PointerType yjs.store) @! "updateItemOfNode" #lc #start #stop
  {{{ (updateItemVal : yjs.updateItem.t) (name : go_string), RET #updateItemVal;
      own_store_state s q state ∗ ⌜ss_bind state !! name = Some parent⌝ ∗
      is_update_item updateItemVal
        (RootId name,
         input_of_run (split_run_left (split_run_right r (uint.nat start))
                         (uint.nat stop - uint.nat start))) }}}.
Proof using Type*.
  move=> Hls Hp Hlk Hrk Hpart.
  iIntros (Φ) "(#Hpkg & Hstate) HΦ".
  iDestruct (own_store_state_registry_coh with "Hstate") as %(_ & _ & Hnamed).
  destruct (Hnamed parent ltac:(by eexists)) as [name0 Hname0].
  iDestruct (own_store_state_run_pool_invs with "Hstate") as %[Hrun_invs _].
  have Hr_all : r ∈ all_runs (ss_pool state).
  { apply elem_of_all_runs. exists parent, tm. split; [exact Hp | exact (list_elem_of_lookup_2 _ _ _ Hrk)]. }
  destruct (Hrun_invs r Hr_all) as (_ & Hfits & Hclient_fits & _).
  wp_method_call. wp_call. wp_call. wp_auto.
  iDestruct (own_store_state_item_node_acc s q state parent ls tm k lc r Hls Hp Hlk Hrk with "Hstate")
    as (prev nxt) "(%Hrun & %Hper_char & %Hcontent_length & Hnode & Hback)".
  iDestruct "Hnode" as (itemVal origin_left origin_right)
    "(Hval & #Horigin_left & #Horigin_right & %Hin_left & %Hin_right & %Hid & #Hcontent & %Hparent & %Hprev & %Hnext & %Hflags)".
  (* what the model says of the part's head; no local names for the part or
     its offset, because [wp_if_join] substitutes every variable equation *)
  have Hhead : run_items r !! 0%nat = Some (run_head_item r).
  { rewrite /run_head_item. destruct Hrun as [Hrun_nonempty _].
    destruct (run_items r); [done | reflexivity]. }
  have Hpart_head : run_items r !! (uint.nat start) = Some (run_head_item (split_run_left (split_run_right r (uint.nat start)) (uint.nat stop - uint.nat start))).
  { have [part_head Hlookup] : is_Some (run_items r !! (uint.nat start)) by (apply lookup_lt_is_Some; lia).
    rewrite Hlookup. f_equal. symmetry.
    rewrite /run_head_item /split_run_left /split_run_right /=.
    rewrite hd_inhabitant_take; last lia. exact (hd_inhabitant_drop _ _ part_head Hlookup). }
  have Hpart_id : item_id (run_head_item (split_run_left (split_run_right r (uint.nat start)) (uint.nat stop - uint.nat start))) = MkYjsId (run_client r) (run_clock r + (uint.nat start))
    := run_wf_lookup_clock (run_items r) _ (run_head_item r) _ Hrun Hhead Hpart_head.
  have Hpart_right : rightOrigin (run_head_item (split_run_left (split_run_right r (uint.nat start)) (uint.nat stop - uint.nat start))) = rightOrigin (run_head_item r)
    := run_wf_lookup_rightOrigin (run_items r) _ (run_head_item r) _ Hrun Hhead Hpart_head.
  have Hid_client : uint.nat itemVal.(yjs.item.id').(yjs.id.clientId') = run_client r.
  { rewrite /run_client. move: Hid. rewrite /toYjsId /=. by move=> <-. }
  have Hid_clock : uint.nat itemVal.(yjs.item.id').(yjs.id.clock') = run_clock r.
  { rewrite /run_clock. move: Hid. rewrite /toYjsId /=. by move=> <-. }
  have Hfits' : (Z.of_nat (run_clock r) + Z.of_nat (length (run_items r)) < 2^64)%Z := Hfits.
  wp_auto.
  (* the left origin: the node's own at the node's first unit, the unit
     before the part otherwise *)
  wp_if_join (λ v : val, ⌜v = execute_val⌝ ∗ ∃ (left_ptr : loc) (left_id : option yjs.id.t),
      "it" ∷ it_ptr ↦ lc ∗ "start" ∷ start_ptr ↦ start ∗ "Hval" ∷ lc ↦{#q} itemVal ∗
      "originLeftId" ∷ originLeftId_ptr ↦ left_ptr ∗
      "Hleft_cell" ∷ (is_origin_id left_ptr left_id ∨
                      ∃ before : yjs.id.t, ⌜left_id = Some before ∧ left_ptr ≠ null⌝ ∗ left_ptr ↦ before) ∗
      "%Hleft_model" ∷ ⌜toYjsId <$> left_id = origin_id (origin (run_head_item (split_run_left (split_run_right r (uint.nat start)) (uint.nat stop - uint.nat start))))⌝)%I
      with "[it start Hval originLeftId]".
  { (* start > 0 *)
    wp_apply wp_NewId.
    iDestruct (typed_pointsto_not_null with "before") as %Hbefore_nonnull.
    iSplitR; first done. iExists before_ptr, (Some _). iFrame "it start Hval originLeftId".
    iSplitL "before"; first (iRight; iExists _; iFrame "before"; done).
    iPureIntro.
    have [before_index Hbefore_index] : ∃ n, (uint.nat start) = S n by (exists ((uint.nat start) - 1)%nat; word).
    have [before_item Hbefore_item] : is_Some (run_items r !! before_index).
    { apply lookup_lt_is_Some. lia. }
    have Hpart_lookup := Hpart_head. rewrite {1}Hbefore_index in Hpart_lookup.
    destruct ((proj2 Hrun) before_index before_item _ Hbefore_item Hpart_lookup) as (_ & Horigin & _).
    rewrite Horigin /=.
    rewrite (run_wf_lookup_clock (run_items r) before_index (run_head_item r) before_item Hrun Hhead Hbefore_item).
    rewrite /toYjsId /=. f_equal. f_equal; first exact Hid_client.
    move: Hid_clock Hfits' Hpart Hbefore_index. rewrite /run_clock. word. }
  { (* start = 0: the node's own left origin *)
    iSplitR; first done. iExists _, origin_left. iFrame "it start Hval originLeftId".
    iSplitR; first (iLeft; iFrame "Horigin_left").
    iPureIntro. have Hzero : (uint.nat start) = 0%nat by word.
    have Hpart_lookup := Hpart_head. rewrite {1}Hzero Hhead in Hpart_lookup.
    injection Hpart_lookup as Hsame_head. rewrite -Hsame_head. exact Hin_left. }
  iIntros (v) "[%Hv HQ]". subst v. iNamed "HQ".
  iAssert (|==> is_origin_id left_ptr left_id)%I with "[Hleft_cell]" as ">#Hleft".
  { iDestruct "Hleft_cell" as "[#Hleft | (%before & [-> %Hnonnull] & Hcell)]"; first done.
    iPersist "Hcell". iModIntro. iSplit; [done | iFrame "Hcell"]. }
  wp_auto.
  (* the parent name: read off the registry exactly when neither origin is
     there; either way the node goes back into the store *)
  wp_bind (if: _ then _ else _)%E.
  iApply (wp_wand _ _ _ (λ v : val, ⌜v = execute_val⌝ ∗
      ∃ (name_ptr : loc) (name_opt : option go_string) (name : go_string),
      "it" ∷ it_ptr ↦ lc ∗ "s" ∷ s_ptr ↦ s ∗ "Hstate" ∷ own_store_state s q state ∗
      "parentName" ∷ parentName_ptr ↦ name_ptr ∗
      "Hname_cell" ∷ (⌜name_opt = None ∧ name_ptr = null⌝ ∨
                      ⌜name_opt = Some name ∧ name_ptr ≠ null⌝ ∗ name_ptr ↦ name) ∗
      "%Hname" ∷ ⌜ss_bind state !! name = Some parent⌝ ∗
      "%Hname_some" ∷ ⌜∀ other, name_opt = Some other -> other = name⌝ ∗
      "%Hname_opt" ∷ ⌜name_opt = None <-> (left_id ≠ None ∨ origin_right ≠ None)⌝)%I
    with "[it s Hval Hback parentName]").
  { iPoseProof "Horigin_right" as "Hright".
    destruct left_id as [left_id_value |].
    - iDestruct "Hleft" as "[%Hleft_nonnull _]".
      rewrite (bool_decide_eq_false_2 _ Hleft_nonnull). wp_auto.
      iDestruct ("Hback" with "[Hval]") as "Hstate".
      { iExists itemVal, _, _. iFrame "Hval Horigin_left Horigin_right Hcontent". done. }
      iSplitR; first done. iExists null, None, name0. iFrame "it s Hstate parentName".
      iSplitR; first (iLeft; done). iPureIntro. split; first done. split; first done. split; [by left | done].
    - iDestruct "Hleft" as %Hleft_null.
      rewrite (bool_decide_eq_true_2 _ Hleft_null). wp_auto.
      destruct origin_right as [right_id |].
      + iDestruct "Hright" as "[%Hright_nonnull _]".
        rewrite (bool_decide_eq_false_2 _ Hright_nonnull). wp_auto.
        iDestruct ("Hback" with "[Hval]") as "Hstate".
        { iExists itemVal, _, _. iFrame "Hval Horigin_left Horigin_right Hcontent". done. }
        iSplitR; first done. iExists null, None, name0. iFrame "it s Hstate parentName".
        iSplitR; first (iLeft; done). iPureIntro. split; first done. split; first done. split; [by right | done].
      + iDestruct "Hright" as %Hright_null.
        rewrite (bool_decide_eq_true_2 _ Hright_null). wp_auto.
        iDestruct ("Hback" with "[Hval]") as "Hstate".
        { iExists itemVal, _, _. iFrame "Hval Horigin_left Horigin_right Hcontent". done. }
        rewrite Hparent.
        wp_apply (wp_store__rootName with "[$Hpkg $Hstate]"); first (iPureIntro; by eexists).
        iIntros (name) "[Hstate %Hname]".
        wp_auto.
        iDestruct (typed_pointsto_not_null with "name") as %Hname_nonnull.
        iSplitR; first done. iExists name_ptr, (Some name), name. iFrame "it s Hstate parentName".
        iSplitL "name"; first (iRight; iFrame "name"; done).
        iPureIntro. split; first done. split; first by move=> other [= <-].
        split; first done. by move=> [? | ?]. }
  iIntros (v) "[%Hv HQ]". subst v. iNamed "HQ".
  iAssert (|==> is_parent_name name_ptr name_opt)%I with "[Hname_cell]" as ">#Hparent_name".
  { iDestruct "Hname_cell" as "[[-> ->] | [[-> %Hnonnull] Hcell]]"; first done.
    iPersist "Hcell". iModIntro. iSplit; [done | iFrame "Hcell"]. }
  (* the struct's fields, read off the node again *)
  iDestruct (own_store_state_item_node_acc s q state parent ls tm k lc r Hls Hp Hlk Hrk with "Hstate")
    as (prev' nxt') "(_ & _ & _ & Hnode & Hback)".
  iDestruct "Hnode" as (node_value node_left node_right)
    "(Hval & #Hnode_left & #Hnode_right & %Hnode_in_left & %Hnode_in_right & %Hnode_id & #Hnode_content & %Hnode_parent & %Hnode_prev & %Hnode_next & %Hnode_flags)".
  wp_auto. wp_apply wp_NewId.
  (* the content: the part's units, a read-only subslice of the node's *)
  have Hpart_string : items_string (run_items (split_run_left (split_run_right r (uint.nat start)) (uint.nat stop - uint.nat start))) =
      take (uint.nat stop - uint.nat start) (drop (uint.nat start) (items_string (run_items r))).
  { apply items_string_explode. rewrite /= fmap_take fmap_drop.
    rewrite /run_per_char in Hper_char. rewrite Hper_char /explode fmap_take fmap_drop //. }
  iEval (rewrite /is_content /=) in "Hnode_content".
  iDestruct (own_slice_len with "Hnode_content") as %[Hslice_length _].
  iDestruct (own_slice_wf with "Hnode_content") as %Hslice_cap.
  have Hslice_bound : 0 ≤ sint.Z start ≤ sint.Z stop ≤ sint.Z node_value.(yjs.item.content').(yjs.content.content').(slice.len).
  { move: Hslice_length Hpart. rewrite Hcontent_length. word. }
  rewrite decide_True; last (clear -Hslice_bound Hslice_cap; word).
  iDestruct (own_slice_slice start stop _ DfracDiscarded _ Hslice_bound with "Hnode_content")
    as "(_ & #Hpart_content & _)".
  wp_auto.
  iDestruct ("Hback" with "[Hval]") as "Hstate".
  { iExists node_value, _, _. iFrame "Hval Hnode_left Hnode_right". iSplitR; first done.
    iSplitR; first done. iSplitR; first done. iSplitR; first (rewrite /is_content /=; iFrame "Hnode_content"). done. }
  iApply ("HΦ" $! _ name). iFrame "Hstate". iSplitR; first done.
  iExists left_id, node_right, name_opt. iFrame "Hleft Hnode_right Hparent_name".
  have Hsubslice : subslice (sint.nat start) (sint.nat stop) (items_string (run_items r)) =
      items_string (run_items (split_run_left (split_run_right r (uint.nat start)) (uint.nat stop - uint.nat start))).
  { rewrite Hpart_string /subslice take_drop_commute.
    congr (drop _ (take _ _)); clear -Hslice_bound; word. }
  iEval (rewrite Hsubslice) in "Hpart_content". iFrame "Hpart_content".
  iPureIntro. split_and!.
  - exact Hleft_model.
  - rewrite /= Hpart_right. exact Hnode_in_right.
  - rewrite /= Hpart_id /toYjsId /=.
    move: Hnode_id Hfits' Hpart. rewrite /toYjsId /run_client /run_clock /=.
    destruct (item_id (run_head_item r)) as [head_client head_clock]. simpl.
    move=> [= Hclient Hclock] Hbound Hrange. f_equal; [exact Hclient | word].
  - rewrite /= Hpart_string length_take length_drop. lia.
  - move=> other Hother. by rewrite (Hname_some other Hother).
  - rewrite Hname_opt /input_has_origin /= -Hleft_model Hpart_right.
    have Hright_model : toYjsId <$> origin_right = origin_id (rightOrigin (run_head_item r)) := Hin_right.
    rewrite -Hright_model. destruct left_id, origin_right; simpl; naive_solver.
Qed.

(** An entry's covered clock is an id of the pool. *)
#[local] Lemma pool_entry_covered_clock_has (locs : gmap loc (list loc)) (p : pool) (l : loc) (r : ItemRun) (k : nat) :
  pool_invs p ->
  (l, r) ∈ pool_entries locs p ->
  run_covers_clock r k ->
  pool_has p (MkYjsId (run_client r) k).
Proof.
  move=> Hinvs /pool_entries_slot [parent [ls [tm [slot [Hls [Hp [Hlk Hrk]]]]]]] [Hlow Hhigh].
  have Hr_all : r ∈ all_runs p.
  { apply elem_of_all_runs. exists parent, tm. split; [exact Hp | exact (list_elem_of_lookup_2 _ _ _ Hrk)]. }
  have Hwf : run_wf (run_items r) := proj1 (proj1 Hinvs r Hr_all).
  rewrite /run_client /run_clock /run_head_item in Hlow Hhigh |- *.
  have [item Hitem] : is_Some (run_items r !! (k - clock (item_id (hd inhabitant (run_items r))))%nat).
  { apply lookup_lt_is_Some. lia. }
  exists parent, tm, item. split_and!; first exact Hp.
  - rewrite /tm_arr /runs_flatten list_elem_of_join. exists (run_items r).
    split; first exact (list_elem_of_lookup_2 _ _ _ Hitem).
    apply list_elem_of_fmap. exists r. split; [done | exact (list_elem_of_lookup_2 _ _ _ Hrk)].
  - rewrite (run_wf_char_id _ _ _ Hwf Hitem). f_equal. lia.
Qed.

(** An item of the pool sits in an entry of its creator, which covers its
    clock. *)
#[local] Lemma pool_item_entry (locs : gmap loc (list loc)) (p : pool) (parent : loc) (tm : type_model)
    (item : YjsItem A) :
  pool_invs p ->
  (∀ parent tm, p !! parent = Some tm -> ∃ ls, locs !! parent = Some ls ∧ length ls = length (tm_runs tm)) ->
  p !! parent = Some tm -> item ∈ tm_arr tm ->
  ∃ l r, (l, r) ∈ pool_entries locs p ∧ run_client r = clientId (item_id item) ∧
         run_covers_clock r (clock (item_id item)).
Proof.
  move=> Hinvs Hlens Hp Hitem. apply list_elem_of_lookup_1 in Hitem as [n Hn].
  destruct (runs_flatten_lookup_run (tm_runs tm) n item Hn) as (slot & offset & r & Hslot & Hoffset & _).
  have Hr_all : r ∈ all_runs p.
  { apply elem_of_all_runs. exists parent, tm. split; [exact Hp | exact (list_elem_of_lookup_2 _ _ _ Hslot)]. }
  have Hwf : run_wf (run_items r) := proj1 (proj1 Hinvs r Hr_all).
  destruct (Hlens parent tm Hp) as (ls & Hls & Hlength).
  have [l Hl] : is_Some (ls !! slot).
  { apply lookup_lt_is_Some. rewrite Hlength. exact (lookup_lt_Some _ _ _ Hslot). }
  exists l, r. split.
  { apply pool_entries_slot. by exists parent, ls, tm, slot. }
  rewrite (run_wf_char_id _ _ _ Hwf Hoffset) /run_covers_clock /run_client /run_clock /run_head_item /=.
  split; first reflexivity. split; first lia.
  have := lookup_lt_Some _ _ _ Hoffset. lia.
Qed.

(** The walk of [appendSpanStructs] reaches every clock of the span that an
    entry of the client covers: it starts at the entry covering the span's
    first clock, and it stops past the last entry or at one that begins at
    or past the span's end. *)
#[local] Lemma span_walk_reaches_span_entries (E : list (loc * ItemRun)) (first span_end found exit_index : nat)
    (reached : ItemRun -> nat -> Prop) :
  StronglySorted entry_le E ->
  (∀ l r, (l, r) ∈ E -> (Z.of_nat (run_clock r) < 2^64)%Z) ->
  (∀ (i j : nat) (l1 l2 : loc) (r1 r2 : ItemRun),
     E !! i = Some (l1, r1) -> E !! j = Some (l2, r2) -> i ≠ j ->
     (run_clock r1 + length (run_items r1) <= run_clock r2)%nat ∨
     (run_clock r2 + length (run_items r2) <= run_clock r1)%nat) ->
  (∃ l r, E !! found = Some (l, r) ∧ run_covers_clock r first) ->
  (∀ (j : nat) l r k, (found <= j < exit_index)%nat -> E !! j = Some (l, r) ->
     run_covers_clock r k -> (first <= k < span_end)%nat -> reached r k) ->
  ((length E <= exit_index)%nat ∨
   ∃ l r, E !! exit_index = Some (l, r) ∧ (span_end <= run_clock r)%nat) ->
  ∀ l r k, (l, r) ∈ E -> run_covers_clock r k -> (first <= k < span_end)%nat -> reached r k.
Proof.
  move=> Hsorted Hbound Hdisjoint [l0 [r0 [Hfound [Hfound_low Hfound_high]]]] Hwalked Hexit l r k
    Hentry [Hlow Hhigh] [Hfirst Hend].
  apply list_elem_of_lookup_1 in Hentry as [j Hj].
  have Hclock : ∀ (i i' : nat) l1 r1 l2 r2, E !! i = Some (l1, r1) -> E !! i' = Some (l2, r2) ->
      (i < i')%nat -> (run_clock r1 <= run_clock r2)%nat.
  { move=> i i' l1 r1 l2 r2 Hi Hi' Hlt.
    have Hle := StronglySorted_lookup_le entry_le E i i' _ _ Hsorted Hi Hi' Hlt.
    move: Hle. rewrite /entry_le (entry_clock_Z l1 r1 (Hbound l1 r1 (list_elem_of_lookup_2 _ _ _ Hi)))
      (entry_clock_Z l2 r2 (Hbound l2 r2 (list_elem_of_lookup_2 _ _ _ Hi'))). lia. }
  destruct (decide (j < found)%nat) as [Hbefore | Hfrom].
  { exfalso.
    have Hle := Hclock j found l r l0 r0 Hj Hfound Hbefore.
    destruct (Hdisjoint j found l l0 r r0 Hj Hfound ltac:(lia)) as [Hd | Hd]; lia. }
  destruct (decide (j < exit_index)%nat) as [Hin | Hpast].
  { apply (Hwalked j l r k); [lia | exact Hj | done | done]. }
  exfalso. destruct Hexit as [Hlength | (l1 & r1 & Hexit & Hbeyond)].
  { have := lookup_lt_Some _ _ _ Hj. lia. }
  destruct (decide (j = exit_index)) as [-> | Hne].
  { rewrite Hexit in Hj. injection Hj as <- <-. lia. }
  have Hle := Hclock exit_index j l1 r1 l r Hexit Hj ltac:(lia). lia.
Qed.

(** When no entry of the client covers the span's first clock, none covers
    a later one either: a client's clocks are gap-free
    ([pool_clocks_contiguous]). *)
#[local] Lemma span_without_first_clock_reaches_nothing (locs : gmap loc (list loc)) (p : pool) (client : w64)
    (E : list (loc * ItemRun)) (first : nat) :
  pool_invs p -> pool_clocks_contiguous p ->
  (∀ parent tm, p !! parent = Some tm -> ∃ ls, locs !! parent = Some ls ∧ length ls = length (tm_runs tm)) ->
  (∀ e, e ∈ E -> e ∈ pool_entries locs p ∧ entry_client e = client) ->
  (∀ e, e ∈ pool_entries locs p -> entry_client e = client -> e ∈ E) ->
  (∀ l r, (l, r) ∈ E -> ¬ run_covers_clock r first) ->
  ∀ l r k, (l, r) ∈ E -> run_covers_clock r k -> (first <= k)%nat -> False.
Proof.
  move=> Hinvs Hcontiguous Hlens Hsound Hcomplete Hnone l r k Hentry Hcovers Hfirst.
  destruct (Hsound _ Hentry) as [Hpool_entry Hclient].
  have Hhas := pool_entry_covered_clock_has locs p l r k Hinvs Hpool_entry Hcovers.
  have Hhas_first : pool_has p (MkYjsId (run_client r) first).
  { destruct (decide (first = k)) as [-> | Hne]; first exact Hhas.
    exact (Hcontiguous _ Hhas first ltac:(simpl; lia)). }
  destruct Hhas_first as (parent & tm & item & Hp & Hitem & Hid).
  destruct (pool_item_entry locs p parent tm item Hinvs Hlens Hp Hitem) as (l' & r' & Hentry' & Hclient' & Hcovers').
  rewrite Hid /= in Hclient' Hcovers'.
  apply (Hnone l' r'); last exact Hcovers'.
  apply Hcomplete; first exact Hentry'.
  rewrite -Hclient /entry_client /=. by rewrite Hclient'.
Qed.

(** From the walk to the items: when the walk reached every clock of the
    span that an entry covers, and every character it appended is an item of
    the registry with an id of the span, the appended batch holds exactly
    those items. *)
#[local] Lemma span_structs_hold_span_items (locs : gmap loc (list loc)) (p : pool) (bind : gmap P loc)
    (span : yjs.idSpan.t) (E : list (loc * ItemRun))
    (appended : list (TId * IntegrateInput (A := A))) :
  pool_invs p -> pool_registry_coh bind p ->
  (∀ parent tm, p !! parent = Some tm -> ∃ ls, locs !! parent = Some ls ∧ length ls = length (tm_runs tm)) ->
  (∀ e, e ∈ pool_entries locs p -> entry_client e = span.(yjs.idSpan.id').(yjs.id.clientId') -> e ∈ E) ->
  (∀ l r k, (l, r) ∈ E -> run_covers_clock r k ->
     (uint.nat span.(yjs.idSpan.id').(yjs.id.clock') <= k <
      uint.nat span.(yjs.idSpan.id').(yjs.id.clock') + uint.nat span.(yjs.idSpan.len'))%nat ->
     ∃ op, op ∈ expand_inputs appended ∧ in_id op.2 = MkYjsId (run_client r) k) ->
  (∀ op, op ∈ expand_inputs appended ->
     ∃ (name : go_string) (item : YjsItem A),
       (registry_has_item bind p name item ∧ item_id item ∈ span_ids span) ∧
       op = (RootId name, input_of_item item)) ->
  structs_expand_to_items appended (λ name item,
    registry_has_item bind p name item ∧ item_id item ∈ span_ids span).
Proof.
  move=> Hinvs [_ [Hone_name _]] Hlens Hcomplete Hwalk Hsound op. split; first exact (Hsound op).
  move=> [name [item [[[parent [tm [Hname [Hparent Hitem]]]] Hid] ->]]].
  destruct (pool_item_entry locs p parent tm item Hinvs Hlens Hparent Hitem) as (l & r & Hentry & Hclient & Hcovers).
  move: Hid. rewrite /span_ids /range_ids elem_of_list_to_set list_elem_of_fmap.
  move=> [offset [Hid /elem_of_seq Hoffset]].
  have Hentry_client : entry_client (l, r) = span.(yjs.idSpan.id').(yjs.id.clientId').
  { rewrite /entry_client /= Hclient Hid /=. word. }
  destruct (Hwalk l r (clock (item_id item)) (Hcomplete _ Hentry Hentry_client) Hcovers)
    as (walked & Hwalked & Hwalked_id).
  { rewrite Hid /=. lia. }
  destruct (Hsound walked Hwalked) as (name' & item' & [(parent' & tm' & Hname' & Hparent' & Hitem') _] & ->).
  have Hsame_id : item_id item' = item_id item.
  { move: Hwalked_id. rewrite /= Hclient. by destruct (item_id item). }
  destruct (pool_item_unique p parent' parent tm' tm item' item Hinvs Hparent' Hitem' Hparent Hitem Hsame_id)
    as [-> ->].
  by rewrite (Hone_name name' name parent Hname' Hname) in Hwalked.
Qed.

(** [store.appendSpanStructs] over the store's data fields: the stepping
    stone of the public spec below. The walk hands half of the store to
    [updateItemOfNode] and reads the client's node list through the other
    half. *)
#[local] Lemma wp_store__appendSpanStructs_state (s : loc) (state : store_state)
    (structs_slice : slice.t) (structs : list (TId * IntegrateInput (A := A)))
    (span : yjs.idSpan.t) :
  span_no_overflow span ->
  {{{ is_pkg_init yjs ∗ own_store_state s 1 state ∗
      own_update_structs structs_slice (DfracOwn 1) structs }}}
    s @! (go.PointerType yjs.store) @! "appendSpanStructs" #structs_slice #span
  {{{ (result_slice : slice.t) (appended : list (TId * IntegrateInput (A := A))),
      RET #result_slice;
      own_store_state s 1 state ∗
      own_update_structs result_slice (DfracOwn 1) (structs ++ appended) ∗
      ⌜structs_expand_to_items appended (λ name item,
         registry_has_item (ss_bind state) (ss_pool state) name item ∧
         item_id item ∈ span_ids span)⌝ }}}.
Proof using Type*.
  move=> Hspan.
  iIntros (Φ) "(#Hpkg & Hstate & Hstructs) HΦ".
  iAssert (own_store_state s (1 / 2 + 1 / 2) state) with "[Hstate]" as "Hstate";
    first by rewrite Qp.div_2.
  iDestruct (own_store_state_split with "Hstate") as "[Hcall Hread]".
  destruct state as [client0 clock0 locs p bind pend pdel]. simpl in *.
  iDestruct "Hread" as "(Hfields & %Hinvs)".
  have Hpool_invs : pool_invs p := proj1 Hinvs.
  have Hregistry_coh : pool_registry_coh bind p := proj1 (proj2 Hinvs).
  have Hcontiguous : pool_clocks_contiguous p := proj2 (proj2 Hinvs).
  iDestruct "Hfields" as "(Hclient & Hclock & HdeletedSet & Hitems & Hregistry & Htypes & Hpending & Hpdeletes)".
  iEval (simpl) in "Hclient Hclock Hitems Hregistry Htypes Hpending Hpdeletes".
  iDestruct "Hitems" as (items_mref) "(Hitemsf & Hitemmap)".
  iDestruct "Hitemmap" as (gm) "(Hmap & Hruns & %Hcomplete & %Hclockunique)".
  iAssert (⌜locs_wf locs p⌝)%I as %Hlocswf; first by iDestruct "Htypes" as "[%Hwf _]".
  destruct Hlocswf as (Hdom & Hnd & Hlens).
  have Hlens' : ∀ parent tm, p !! parent = Some tm ->
      ∃ ls, locs !! parent = Some ls ∧ length ls = length (tm_runs tm).
  { move=> parent tm Hp.
    have His : is_Some (locs !! parent).
    { apply elem_of_dom. rewrite Hdom. apply elem_of_dom. by exists tm. }
    destruct His as [ls Hls]. exists ls. split; [done | exact (Hlens parent ls tm Hls Hp)]. }
  have Hndl : NoDup (pool_entries locs p).*1 := pool_entries_locs_NoDup locs p Hdom Hlens' Hnd.
  (* the client's node list: its slice in the index, or no slice and no node *)
  iAssert (∃ (nodes : slice.t) (E : list (loc * ItemRun)),
      ⌜default slice.nil (gm !! span.(yjs.idSpan.id').(yjs.id.clientId')) = nodes⌝ ∗
      ⌜sorted_client_entries locs p span.(yjs.idSpan.id').(yjs.id.clientId') E⌝ ∗
      ⌜∀ e, e ∈ pool_entries locs p -> entry_client e = span.(yjs.idSpan.id').(yjs.id.clientId') -> e ∈ E⌝ ∗
      nodes ↦*{#1/2} E.*1 ∗
      (nodes ↦*{#1/2} E.*1 -∗
       [∗ map] client ↦ client_slice ∈ gm,
         client_slice ↦*{#1/2} key_pair_client_locs client (entry_key_pair <$> pool_entries locs p) ∗
         own_slice_cap loc client_slice (DfracOwn (1/2))))%I
    with "[Hruns]" as (nodes E) "(%Hnodes & %Hsorted & %Hentries & Hslice & Hrunsback)".
  { destruct (gm !! span.(yjs.idSpan.id').(yjs.id.clientId')) as [client_slice |] eqn:Hclient_slice.
    - iDestruct (big_sepM_lookup_acc _ _ _ client_slice Hclient_slice with "Hruns") as "[Hrun Hrunsback]".
      iNamed "Hrun".
      iExists client_slice, (client_entries locs p span.(yjs.idSpan.id').(yjs.id.clientId')).
      iSplitR; first done.
      iSplitR; first (iPureIntro; exact (client_entries_sorted_client locs p _ Hndl)).
      iSplitR. { iPureIntro. move=> e He Hc. by apply client_entries_mem. }
      rewrite -(client_locs_entries locs p _ Hclockunique). iFrame "Hslice".
      iIntros "Hslice". iApply "Hrunsback". iFrame "Hslice Hcap".
    - iExists slice.nil, []. iSplitR; first done.
      iSplitR. { iPureIntro. split_and!; [constructor | constructor | by move=> e /elem_of_nil]. }
      iSplitR.
      { (* a client with no slice in the index has no node *)
        iPureIntro. move=> e He Hc. exfalso.
        have Hsome : is_Some (gm !! span.(yjs.idSpan.id').(yjs.id.clientId')).
        { apply Hcomplete. rewrite -Hc. apply list_elem_of_fmap. exists (entry_key_pair e).
          split; first reflexivity. apply list_elem_of_fmap. by exists e. }
        rewrite Hclient_slice in Hsome. destruct Hsome as [client_slice Hclient_some]. discriminate. }
      iSplitR; first iApply own_slice_nil. iIntros "_". iFrame "Hruns". }
  have Hentry_clock : ∀ l r, (l, r) ∈ E -> (Z.of_nat (run_clock r) < 2^64)%Z.
  { move=> l r Hlr. destruct (proj2 (proj2 Hsorted) (l, r) Hlr) as [Hpool_entry _].
    apply pool_entries_slot in Hpool_entry as (parent & ls & tm & k & Hls & Hp & Hlk & Hrk).
    have Hr_all : r ∈ all_runs p.
    { apply elem_of_all_runs. exists parent, tm. split; [exact Hp | exact (list_elem_of_lookup_2 _ _ _ Hrk)]. }
    have Hfits : run_fits r := proj1 (proj2 (proj1 Hpool_invs r Hr_all)).
    move: Hfits. rewrite /run_fits. lia. }
  have Hentries_disjoint := sorted_client_entries_disjoint locs p _ E Hdom Hlens' Hndl
    (λ r Hr, proj1 (proj2 (proj2 (proj1 Hpool_invs r Hr)))) (proj2 Hpool_invs) Hsorted.
  wp_method_call. wp_call. wp_call. wp_auto.
  wp_apply (wp_map_lookup1 with "Hmap"). iIntros "Hmap".
  rewrite Hnodes. wp_auto.
  (* the binary search reads the whole pool: lend it the other half's pool *)
  iDestruct "Hcall" as "(Hcall_fields & _)".
  iDestruct "Hcall_fields" as "(Hcall_client & Hcall_clock & Hcall_deletedSet & Hcall_items & Hcall_registry & Hcall_types & Hcall_pending & Hcall_pdeletes)".
  iEval (simpl) in "Hcall_types".
  iAssert (own_type_pool (DfracOwn (1 / 2 + 1 / 2)) locs p) with "[Hcall_types Htypes]" as "Hpool".
  { iApply (own_type_pool_fractional locs p (1 / 2)%Qp (1 / 2)%Qp). iFrame "Hcall_types Htypes". }
  iEval (rewrite Qp.div_2) in "Hpool".
  wp_apply (wp_getNodeIndex nodes (DfracOwn (1 / 2)%Qp) locs p _ _ E Hpool_invs Hsorted
              with "[$Hslice $Hpool]").
  iIntros (found_index found) "(Hslice & Hpool & %Hfound)".
  iAssert (own_type_pool (DfracOwn (1 / 2 + 1 / 2)) locs p) with "[Hpool]" as "Hpool";
    first by rewrite Qp.div_2.
  iDestruct (own_type_pool_fractional locs p (1 / 2)%Qp (1 / 2)%Qp with "Hpool") as "[Hcall_types Htypes]".
  iAssert (own_store_state s (1 / 2) (MkStoreState client0 clock0 locs p bind pend pdel))
    with "[Hcall_client Hcall_clock Hcall_deletedSet Hcall_items Hcall_registry Hcall_types Hcall_pending Hcall_pdeletes]"
    as "Hcall".
  { iSplitL; last done. rewrite /own_store_fields /=.
    iFrame "Hcall_client Hcall_clock Hcall_deletedSet Hcall_items Hcall_registry Hcall_types Hcall_pending Hcall_pdeletes". }
  wp_auto.
  wp_if_join (λ v : val, ⌜v = execute_val⌝ ∗
      ∃ (result_slice : slice.t) (appended : list (TId * IntegrateInput (A := A))),
      "structs" ∷ structs_ptr ↦ result_slice ∗
      "Hstructs" ∷ own_update_structs result_slice (DfracOwn 1) (structs ++ appended) ∗
      "Hcall" ∷ own_store_state s (1 / 2) (MkStoreState client0 clock0 locs p bind pend pdel) ∗
      "Hslice" ∷ nodes ↦*{#1/2} E.*1 ∗
      "Htypes" ∷ own_type_pool (DfracOwn (1 / 2)) locs p ∗
      "%Happended" ∷ ⌜(∀ op, op ∈ expand_inputs appended ->
           ∃ (name : go_string) (parent : loc) (tm : type_model) (r : ItemRun) (it : YjsItem A),
             bind !! name = Some parent ∧ p !! parent = Some tm ∧
             r ∈ tm_runs tm ∧ it ∈ run_items r ∧
             op = (RootId name, input_of_item it) ∧ item_id it ∈ span_ids span)⌝ ∗
      "%Hwalk" ∷ ⌜∀ l r k, (l, r) ∈ E -> run_covers_clock r k ->
           (uint.nat span.(yjs.idSpan.id').(yjs.id.clock') <= k <
            uint.nat span.(yjs.idSpan.id').(yjs.id.clock') + uint.nat span.(yjs.idSpan.len'))%nat ->
           ∃ op, op ∈ expand_inputs appended ∧ in_id op.2 = MkYjsId (run_client r) k⌝)%I
      with "[s structs nodes first end index Hstructs Hcall Hslice Htypes]".
  { (* the walk *)
    iAssert (∃ (index : w64) (result_slice : slice.t) (appended : list (TId * IntegrateInput (A := A))),
      "s" ∷ s_ptr ↦ s ∗ "nodes" ∷ nodes_ptr ↦ nodes ∗
      "first" ∷ first_ptr ↦ span.(yjs.idSpan.id').(yjs.id.clock') ∗
      "end" ∷ end_ptr ↦ w64_word_instance.(word.add) span.(yjs.idSpan.id').(yjs.id.clock') span.(yjs.idSpan.len') ∗
      "index" ∷ index_ptr ↦ index ∗
      "structs" ∷ structs_ptr ↦ result_slice ∗
      "Hstructs" ∷ own_update_structs result_slice (DfracOwn 1) (structs ++ appended) ∗
      "Hcall" ∷ own_store_state s (1 / 2) (MkStoreState client0 clock0 locs p bind pend pdel) ∗
      "Hslice" ∷ nodes ↦*{#1/2} E.*1 ∗
      "Htypes" ∷ own_type_pool (DfracOwn (1 / 2)) locs p ∗
      "%Happended" ∷ ⌜(∀ op, op ∈ expand_inputs appended ->
           ∃ (name : go_string) (parent : loc) (tm : type_model) (r : ItemRun) (it : YjsItem A),
             bind !! name = Some parent ∧ p !! parent = Some tm ∧
             r ∈ tm_runs tm ∧ it ∈ run_items r ∧
             op = (RootId name, input_of_item it) ∧ item_id it ∈ span_ids span)⌝ ∗
      "%Hcovered" ∷ ⌜∀ (j : nat) l r k, (uint.nat found_index <= j < uint.nat index)%nat ->
           E !! j = Some (l, r) -> run_covers_clock r k ->
           (uint.nat span.(yjs.idSpan.id').(yjs.id.clock') <= k <
            uint.nat span.(yjs.idSpan.id').(yjs.id.clock') + uint.nat span.(yjs.idSpan.len'))%nat ->
           ∃ op, op ∈ expand_inputs appended ∧ in_id op.2 = MkYjsId (run_client r) k⌝)%I
      with "[s structs nodes first end index Hstructs Hcall Hslice Htypes]" as "IH".
    { iExists found_index, structs_slice, []. rewrite app_nil_r.
      iFrame "s structs nodes first end index Hstructs Hcall Hslice Htypes".
      iPureIntro. split; first by move=> op /elem_of_nil.
      move=> j entry_loc entry_run covered Hj. exfalso. lia. }
    wp_for "IH".
    iDestruct (own_slice_len with "Hslice") as %[Hnodes_length Hnodes_nonneg].
    rewrite length_fmap in Hnodes_length.
    destruct (decide (uint.Z index < uint.Z nodes.(slice.len))) as [Hinside | Hpast]; last first.
    { (* past the last node *)
      rewrite bool_decide_eq_false_2 //.
      iSplitR; first done. iExists result_slice, appended.
      iFrame "structs Hstructs Hcall Hslice Htypes".
      iPureIntro. split; first exact Happended.
      apply (span_walk_reaches_span_entries E _ _ (uint.nat found_index) (uint.nat index) _
               (proj1 Hsorted) Hentry_clock Hentries_disjoint Hfound Hcovered).
      left. clear -Hpast Hnodes_length Hnodes_nonneg. word. }
    rewrite bool_decide_eq_true_2 //.
    wp_auto.
    rewrite decide_True; last (clear -Hinside Hnodes_nonneg; word).
    have [[node_loc r] Hentry] : is_Some (E !! uint.nat index).
    { apply lookup_lt_is_Some. clear -Hinside Hnodes_length Hnodes_nonneg. word. }
    have Hnode_loc : E.*1 !! uint.nat index = Some node_loc by rewrite list_lookup_fmap Hentry.
    iDestruct (own_slice_elem_acc (sint.Z index) node_loc nodes (DfracOwn (1 / 2)%Qp) E.*1 with "Hslice")
      as "[Helem Hgive]".
    { clear -Hinside Hnodes_nonneg. word. }
    { replace (Z.to_nat (sint.Z index)) with (uint.nat index) by (clear -Hinside Hnodes_nonneg; word).
      exact Hnode_loc. }
    wp_auto.
    iDestruct ("Hgive" $! node_loc with "Helem") as "Hslice".
    have Hinsert_same : <[sint.nat index := node_loc]> E.*1 = E.*1.
    { apply list_insert_id.
      replace (sint.nat index) with (uint.nat index) by (clear -Hinside Hnodes_nonneg; word).
      exact Hnode_loc. }
    iEval (rewrite Hinsert_same) in "Hslice".
    (* the node's slot in the pool *)
    destruct (proj2 (proj2 Hsorted) (node_loc, r) (list_elem_of_lookup_2 _ _ _ Hentry))
      as [Hpool_entry Hentry_client].
    apply pool_entries_slot in Hpool_entry as (parent & ls & tm & k & Hls & Hp & Hlk & Hrk).
    have Hr_all : r ∈ all_runs p.
    { apply elem_of_all_runs. exists parent, tm. split; [exact Hp | exact (list_elem_of_lookup_2 _ _ _ Hrk)]. }
    destruct (proj1 Hpool_invs r Hr_all) as (_ & Hfits & Hclient_fits & _).
    iDestruct (own_type_pool_item_node_acc _ locs p parent ls tm k node_loc r Hls Hp Hlk Hrk with "Htypes")
      as (prev nxt) "(%Hrun & %Hper_char & %Hcontent_length & Hnode & Hback)".
    iDestruct "Hnode" as (node_value node_left node_right)
      "(Hval & #Hnode_left & #Hnode_right & %Hnode_in_left & %Hnode_in_right & %Hnode_id & #Hnode_content & %Hnode_parent & %Hnode_prev & %Hnode_next & %Hnode_flags)".
    wp_auto.
    have Hnode_client : uint.nat node_value.(yjs.item.id').(yjs.id.clientId') = run_client r.
    { rewrite /run_client. move: Hnode_id. rewrite /toYjsId /=. by move=> <-. }
    have Hnode_clock : uint.nat node_value.(yjs.item.id').(yjs.id.clock') = clock (item_id (run_head_item r)).
    { move: Hnode_id. rewrite /toYjsId /=. by move=> <-. }
    have Hfits' : (Z.of_nat (clock (item_id (run_head_item r))) + Z.of_nat (length (run_items r)) < 2^64)%Z := Hfits.
    have Hspan' : (uint.Z span.(yjs.idSpan.id').(yjs.id.clock') + uint.Z span.(yjs.idSpan.len') < 2^64)%Z := Hspan.
    destruct (decide (uint.Z (w64_word_instance.(word.add) span.(yjs.idSpan.id').(yjs.id.clock') span.(yjs.idSpan.len'))
                      ≤ uint.Z node_value.(yjs.item.id').(yjs.id.clock'))) as [Hbeyond | Hbefore_end].
    { (* the node begins at or past the span's end: stop *)
      rewrite bool_decide_eq_true_2 //. wp_auto.
      iDestruct ("Hback" with "[Hval]") as "Htypes".
      { iExists node_value, _, _. iFrame "Hval Hnode_left Hnode_right Hnode_content". done. }
      wp_for_post.
      iSplitR; first done. iExists result_slice, appended.
      iFrame "structs Hstructs Hcall Hslice Htypes".
      iPureIntro. split; first exact Happended.
      apply (span_walk_reaches_span_entries E _ _ (uint.nat found_index) (uint.nat index) _
               (proj1 Hsorted) Hentry_clock Hentries_disjoint Hfound Hcovered).
      right. exists node_loc, r. split; first exact Hentry.
      rewrite /run_clock. move: Hbeyond Hnode_clock Hspan'. word. }
    rewrite bool_decide_eq_false_2 //. wp_auto.
    (* start: where the span begins in the node *)
    wp_if_join (λ v : val, ⌜v = execute_val⌝ ∗ ∃ (start_value : w64),
        "start" ∷ start_ptr ↦ start_value ∗ "node" ∷ node_ptr ↦ node_loc ∗
        "first" ∷ first_ptr ↦ span.(yjs.idSpan.id').(yjs.id.clock') ∗
        "Hval" ∷ node_loc ↦{#1/2} node_value ∗
        "%Hstart" ∷ ⌜(uint.Z node_value.(yjs.item.id').(yjs.id.clock') + uint.Z start_value =
                      Z.max (uint.Z node_value.(yjs.item.id').(yjs.id.clock'))
                            (uint.Z span.(yjs.idSpan.id').(yjs.id.clock')))%Z⌝)%I
        with "[start node first Hval]".
    { iSplitR; first done. iExists _. iFrame "start node first Hval". iPureIntro. word. }
    { iSplitR; first done. iExists _. iFrame "start node first Hval". iPureIntro. word. }
    iIntros (v) "[%Hv HQ]". subst v. iNamed "HQ".
    wp_auto.
    wp_apply (wp_item__Len node_loc _ node_value (items_string (run_items r)) with "[$Hpkg $Hval]");
      first iExact "Hnode_content".
    iIntros "Hval". wp_auto.
    (* stop: where the span ends in the node *)
    wp_if_join (λ v : val, ⌜v = execute_val⌝ ∗ ∃ (stop_value : w64),
        "stop" ∷ stop_ptr ↦ stop_value ∗ "node" ∷ node_ptr ↦ node_loc ∗
        "end" ∷ end_ptr ↦ w64_word_instance.(word.add) span.(yjs.idSpan.id').(yjs.id.clock') span.(yjs.idSpan.len') ∗
        "Hval" ∷ node_loc ↦{#1/2} node_value ∗
        "%Hstop" ∷ ⌜(uint.Z stop_value =
                     Z.min (Z.of_nat (length (run_items r)))
                           (uint.Z span.(yjs.idSpan.id').(yjs.id.clock') + uint.Z span.(yjs.idSpan.len') -
                            uint.Z node_value.(yjs.item.id').(yjs.id.clock')))%Z⌝)%I
        with "[stop node end Hval]".
    { iSplitR; first done. iExists _. iFrame "stop node end Hval". iPureIntro.
      move: Hcontent_length l. word. }
    { iSplitR; first done. iExists _. iFrame "stop node end Hval". iPureIntro.
      move: Hcontent_length n. word. }
    iIntros (v) "[%Hv HQ]". subst v. iNamed "HQ".
    wp_auto.
    (* append the part's struct when the part is not empty *)
    wp_if_join (λ v : val, ⌜v = execute_val⌝ ∗
        ∃ (result_now : slice.t) (appended_now : list (TId * IntegrateInput (A := A))),
        "s" ∷ s_ptr ↦ s ∗ "structs" ∷ structs_ptr ↦ result_now ∗
        "node" ∷ node_ptr ↦ node_loc ∗ "start" ∷ start_ptr ↦ start_value ∗ "stop" ∷ stop_ptr ↦ stop_value ∗
        "Hstructs" ∷ own_update_structs result_now (DfracOwn 1) (structs ++ appended_now) ∗
        "Hcall" ∷ own_store_state s (1 / 2) (MkStoreState client0 clock0 locs p bind pend pdel) ∗
        "%Happended_now" ∷ ⌜(∀ op, op ∈ expand_inputs appended_now ->
           ∃ (name : go_string) (parent : loc) (tm : type_model) (r : ItemRun) (it : YjsItem A),
             bind !! name = Some parent ∧ p !! parent = Some tm ∧
             r ∈ tm_runs tm ∧ it ∈ run_items r ∧
             op = (RootId name, input_of_item it) ∧ item_id it ∈ span_ids span)⌝ ∗
        "%Hgrown" ∷ ⌜∀ op, op ∈ expand_inputs appended -> op ∈ expand_inputs appended_now⌝ ∗
        "%Hnode_reached" ∷ ⌜∀ k, run_covers_clock r k ->
           (uint.nat span.(yjs.idSpan.id').(yjs.id.clock') <= k <
            uint.nat span.(yjs.idSpan.id').(yjs.id.clock') + uint.nat span.(yjs.idSpan.len'))%nat ->
           ∃ op, op ∈ expand_inputs appended_now ∧ in_id op.2 = MkYjsId (run_client r) k⌝)%I
        with "[s structs node start stop Hstructs Hcall]".
    { have Hpart : (uint.nat start_value < uint.nat stop_value <= length (run_items r))%nat.
      { move: l Hstop. word. }
      wp_apply (wp_store__updateItemOfNode s node_loc _ (1 / 2)%Qp (MkStoreState client0 clock0 locs p bind pend pdel) ls tm k r start_value stop_value
                  Hls Hp Hlk Hrk Hpart with "[$Hpkg $Hcall]").
      iIntros (updateItemVal name) "(Hcall & %Hname & #Hitem)".
      wp_auto.
      wp_apply wp_slice_literal. iSplitR; first done. iIntros "%literal [Hliteral _]". wp_auto.
      iNamed "Hstructs".
      wp_apply (wp_slice_append with "[$Hsl $Hcap $Hliteral]").
      iIntros (result_now) "(Hsl & Hcap & _)". wp_auto.
      iSplitR; first done.
      iExists result_now, (appended ++ [(RootId name, input_of_run (split_run_left (split_run_right r (uint.nat start_value)) (uint.nat stop_value - uint.nat start_value)))]).
      iFrame "s structs node start stop Hcall".
      iSplitL "Hsl Hcap Hitems".
      { iExists (uivs ++ [updateItemVal]). rewrite app_assoc.
        iSplitL "Hsl".
        { iExactEq "Hsl". f_equal. }
        iFrame "Hcap".
        iApply (big_sepL2_app with "Hitems"). iSplit; last done. iExact "Hitem". }
      iPureIntro.
      have Hhead : run_items r !! 0%nat = Some (run_head_item r).
      { rewrite /run_head_item. destruct Hrun as [Hrun_nonempty _].
        destruct (run_items r); [done | reflexivity]. }
      have Hpart_wf : run_wf (run_items (split_run_left (split_run_right r (uint.nat start_value)) (uint.nat stop_value - uint.nat start_value))).
      { rewrite /split_run_left /split_run_right /=.
        apply run_wf_take; first lia. apply run_wf_drop; [lia | exact Hrun]. }
      have Hpart_per_char : run_per_char (split_run_left (split_run_right r (uint.nat start_value)) (uint.nat stop_value - uint.nat start_value))
        := run_per_char_split_left _ _ (run_per_char_split_right r _ Hper_char).
      split_and!; last first.
      { (* every clock of the span that the node covers is in the part *)
        move=> covered [Hk_low Hk_high] [Hk_first Hk_end].
        rewrite /run_clock in Hk_low Hk_high.
        have [it Hit] : is_Some (run_items r !! (covered - clock (item_id (run_head_item r)))%nat).
        { apply lookup_lt_is_Some. lia. }
        exists (RootId name, input_of_item it). split.
        - rewrite expand_inputs_app elem_of_app. right.
          rewrite /expand_inputs /= app_nil_r.
          rewrite (expand_input_input_of_run _ (split_run_left (split_run_right r (uint.nat start_value)) (uint.nat stop_value - uint.nat start_value)) Hpart_wf Hpart_per_char).
          apply list_elem_of_fmap. exists it. split; first reflexivity.
          rewrite /split_run_left /split_run_right /=.
          apply (list_elem_of_lookup_2 _ (covered - clock (item_id (run_head_item r)) - uint.nat start_value)%nat).
          apply lookup_take_Some. split.
          + rewrite lookup_drop.
            replace (uint.nat start_value + (covered - clock (item_id (run_head_item r)) - uint.nat start_value))%nat
              with (covered - clock (item_id (run_head_item r)))%nat; first exact Hit.
            move: Hstart Hnode_clock Hk_low Hk_first. word.
          + move: Hstart Hstop Hnode_clock Hk_low Hk_high Hk_first Hk_end Hspan'. word.
        - rewrite /= (run_wf_lookup_clock (run_items r) _ (run_head_item r) it Hrun Hhead Hit) /run_client.
          f_equal. lia. }
      { move=> op Hop. rewrite expand_inputs_app elem_of_app. by left. }
      move=> op. rewrite expand_inputs_app elem_of_app.
      move=> [Hold | Hnew]; first exact (Happended op Hold).
      move: Hnew. rewrite /expand_inputs /= app_nil_r.
      rewrite (expand_input_input_of_run _ (split_run_left (split_run_right r (uint.nat start_value)) (uint.nat stop_value - uint.nat start_value)) Hpart_wf Hpart_per_char).
      move=> /list_elem_of_fmap [it [-> Hit]].
      rewrite /split_run_left /split_run_right /= in Hit.
      apply list_elem_of_lookup in Hit as [offset Hoffset].
      apply lookup_take_Some in Hoffset as [Hoffset Hoffset_bound].
      rewrite lookup_drop in Hoffset.
      have Hit_id := run_wf_lookup_clock (run_items r) _ (run_head_item r) it Hrun Hhead Hoffset.
      have Hspan_client : uint.nat span.(yjs.idSpan.id').(yjs.id.clientId') = clientId (item_id (run_head_item r)).
      { rewrite -Hentry_client /entry_client /run_client /=. move: Hclient_fits. rewrite /run_client. word. }
      eexists name, _, tm, r, it.
      split_and!; [exact Hname | exact Hp | exact (list_elem_of_lookup_2 _ _ _ Hrk)
                  | exact (list_elem_of_lookup_2 _ _ _ Hoffset) | reflexivity |].
      rewrite Hit_id /span_ids /range_ids elem_of_list_to_set list_elem_of_fmap.
      exists (clock (item_id (run_head_item r)) + (uint.nat start_value + offset)
              - uint.nat span.(yjs.idSpan.id').(yjs.id.clock'))%nat.
      split.
      - rewrite Hspan_client. f_equal. move: Hstart Hnode_clock. word.
      - apply elem_of_seq. move: Hstart Hstop Hnode_clock Hoffset_bound Hspan'. word. }
    { iSplitR; first done. iExists result_slice, appended.
      iFrame "s structs node start stop Hstructs Hcall".
      iPureIntro. split_and!; [exact Happended | done |].
      (* a node whose part is empty covers no clock of the span *)
      move=> covered [Hk_low Hk_high] [Hk_first Hk_end]. exfalso.
      rewrite /run_clock in Hk_low Hk_high.
      move: n Hstart Hstop Hnode_clock Hk_low Hk_high Hk_first Hk_end Hspan'. word. }
    iIntros (v) "[%Hv HQ]". subst v. iNamed "HQ".
    wp_auto.
    iDestruct ("Hback" with "[Hval]") as "Htypes".
    { iExists node_value, _, _. iFrame "Hval Hnode_left Hnode_right Hnode_content". done. }
    wp_for_post.
    iExists _, result_now, appended_now.
    iFrame "s nodes first end index structs Hstructs Hcall Hslice Htypes".
    iPureIntro. split; first exact Happended_now.
    move=> j entry_loc entry_run covered Hj Hlookup Hcovers Hin_span.
    destruct (decide (j = uint.nat index)) as [-> | Hne].
    - rewrite Hentry in Hlookup. injection Hlookup as <- <-. exact (Hnode_reached covered Hcovers Hin_span).
    - have Hj' : (uint.nat found_index <= j < uint.nat index)%nat.
      { clear -Hj Hne Hinside Hnodes_nonneg. word. }
      destruct (Hcovered j entry_loc entry_run covered Hj' Hlookup Hcovers Hin_span) as (op & Hop & Hop_id).
      exists op. split; [exact (Hgrown op Hop) | exact Hop_id]. }
  { (* no node covers the span's first clock: nothing to append *)
    iSplitR; first done. iExists structs_slice, []. rewrite app_nil_r.
    iFrame "structs Hstructs Hcall Hslice Htypes". iPureIntro.
    split; first by move=> op /elem_of_nil.
    move=> entry_loc entry_run covered Hlr Hcovers [Hk_first _]. exfalso.
    exact (span_without_first_clock_reaches_nothing locs p _ E _ Hpool_invs Hcontiguous Hlens'
             (proj2 (proj2 Hsorted)) Hentries Hfound entry_loc entry_run covered Hlr Hcovers Hk_first). }
  iIntros (v) "[%Hv HQ]". subst v. iNamed "HQ".
  wp_auto.
  (* put the read half back together and rejoin the two halves *)
  iDestruct ("Hrunsback" with "Hslice") as "Hruns".
  iAssert (own_store_state s (1 / 2) (MkStoreState client0 clock0 locs p bind pend pdel))
    with "[Hclient Hclock HdeletedSet Hitemsf Hmap Hruns Hregistry Htypes Hpending Hpdeletes]"
    as "Hread".
  { iSplitL; last done. rewrite /own_store_fields /=.
    iFrame "Hclient Hclock HdeletedSet Hregistry Htypes Hpending Hpdeletes".
    iExists items_mref. iFrame "Hitemsf". iExists gm. iFrame "Hmap Hruns". done. }
  iDestruct (own_store_state_split with "[$Hcall $Hread]") as "Hstate".
  iEval (rewrite Qp.div_2) in "Hstate".
  iApply ("HΦ" $! result_slice appended). iFrame "Hstate Hstructs".
  iPureIntro.
  apply (span_structs_hold_span_items locs p bind span E appended Hpool_invs Hregistry_coh Hlens'
           Hentries Hwalk).
  move=> op Hop.
  destruct (Happended op Hop) as (name & parent & tm & r & item & Hname & Hparent & Hr & Hitem & -> & Hid).
  exists name, item. split; last reflexivity. split; last exact Hid.
  exists parent, tm. split_and!; [exact Hname | exact Hparent |].
  rewrite /tm_arr /runs_flatten list_elem_of_join.
  exists (run_items r). split; first exact Hitem. apply list_elem_of_fmap. by exists r.
Qed.

(** [store.appendSpanStructs]: the store taken and returned whole
    ([own_store]) at an unchanged state. The structs appended for a span
    are, character by character, exactly the items of the store's registry
    whose ids are ids of the span, each under the name of its root: every
    such item is in the batch, and nothing else is. *)
Lemma wp_store__appendSpanStructs (s : loc) (γs : store_names) (γh : history_names)
    (state : store_state) (ds : gset YjsId) (m0 : DocModel) (deleted0 : gset YjsId)
    (structs_slice : slice.t) (structs : list (TId * IntegrateInput (A := A)))
    (span : yjs.idSpan.t) :
  span_no_overflow span ->
  {{{ is_pkg_init yjs ∗ own_store s γs γh 1 state ds m0 deleted0 ∗
      own_update_structs structs_slice (DfracOwn 1) structs }}}
    s @! (go.PointerType yjs.store) @! "appendSpanStructs" #structs_slice #span
  {{{ (result_slice : slice.t) (appended : list (TId * IntegrateInput (A := A))),
      RET #result_slice;
      own_store s γs γh 1 state ds m0 deleted0 ∗
      own_update_structs result_slice (DfracOwn 1) (structs ++ appended) ∗
      ⌜structs_expand_to_items appended (λ name item,
         registry_has_item (ss_bind state) (ss_pool state) name item ∧
         item_id item ∈ span_ids span)⌝ }}}.
Proof using Type*.
  move=> Hspan.
  iIntros (Φ) "(#Hpkg & Hstore & Hstructs) HΦ".
  iNamed "Hstore". iNamed "Hcore".
  wp_apply (wp_store__appendSpanStructs_state s state structs_slice structs span Hspan
              with "[$Hpkg $Hstate $Hstructs]").
  iIntros (result_slice appended) "(Hstate & Hstructs & %Happended)".
  iApply "HΦ". iFrame "Hstructs". iSplitL.
  { iFrame "Hstate Hobservers Hclientpin Hseq HtypesAuth Hbinds Hdelete_set_auth Hstate_agree".
    iPureIntro. exact Hds_tomb. }
  iPureIntro. exact Happended.
Qed.

End store_appendSpanStructs.
