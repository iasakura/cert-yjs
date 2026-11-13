(** Reading integrated nodes back as wire structs (issue #131):
    [store.rootName] (the name a root type is registered under, by a scan of
    the registry), [store.updateItemOfNode] (the decoded struct of one node)
    and [store.appendSpanStructs] (the structs of the nodes covering one
    recorded span). Private to the store: the specs are stated over the
    store's state, [own_store_state], and [Transaction.insertedStructs]
    ([transaction/insertedStructs]) is their one caller. *)
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
Lemma wp_store__rootName (s parent : loc) (state : store_state) :
  {{{ is_pkg_init yjs ∗ own_store_state s 1 state ∗
      ⌜is_Some (ss_pool state !! parent)⌝ }}}
    s @! (go.PointerType yjs.store) @! "rootName" #parent
  {{{ (name : go_string), RET #name;
      own_store_state s 1 state ∗ ⌜ss_bind state !! name = Some parent⌝ }}}.
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
  iEval (rewrite -(Qp.div_2 1)) in "Htypesmap".
  iDestruct (own_map_dfrac_split with "Htypesmap") as "[Htypesmap Htypesmap_lookup]".
  (* once the type's one name has been passed, [result] holds it *)
  wp_apply (wp_map_for_range_keep (λ (keys : list go_string) (i : Z),
      ∃ (result name : go_string),
        "s" ∷ s_ptr ↦ s ∗ "Htypesf" ∷ s.[yjs.store.t, "types"] ↦ types_mref ∗
        "Htypesmap_lookup" ∷ types_mref ↦${DfracOwn (1/2)} bind ∗
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
  iCombine "Htypesmap Htypesmap_lookup" as "Htypesmap".
  iEval (rewrite -own_map_dfrac_split Qp.div_2) in "Htypesmap".
  have Hresult : result = name0.
  { apply Hfound. rewrite -Hkeyslen firstn_all2; last lia.
    apply (elem_of_list_to_set (C := gset go_string)). rewrite Hkeysdom. apply elem_of_dom. by eexists. }
  subst result.
  iApply ("HΦ" $! name0). iSplitL; last done.
  iSplitL; last done. rewrite /own_store_fields /=.
  iFrame "Hclient Hclock HdeletedSet Hitems Htypes Hpending Hpdeletes".
  iExists types_mref. iFrame "Htypesf Htypesmap".
Qed.

(** Borrow one node of the store whole ([own_item_node]): the WP below reads
    its origin cells, which the narrower borrows of [store/heap] do not
    expose. *)
#[local] Lemma own_store_state_item_node_acc (s : loc) (state : store_state)
    (parent : loc) (ls : list loc) (tm : type_model) (k : nat) (lc : loc) (r : ItemRun) :
  ss_locs state !! parent = Some ls ->
  ss_pool state !! parent = Some tm ->
  ls !! k = Some lc ->
  tm_runs tm !! k = Some r ->
  own_store_state s 1 state -∗
  ∃ (prev nxt : loc),
    ⌜run_wf (run_items r)⌝ ∗
    ⌜length (items_string (run_items r)) = length (run_items r)⌝ ∗
    own_item_node lc (DfracOwn 1) (input_of_run r) (run_deleted r) parent prev nxt ∗
    (own_item_node lc (DfracOwn 1) (input_of_run r) (run_deleted r) parent prev nxt -∗
     own_store_state s 1 state).
Proof.
  move=> Hls Hp Hlk Hrk.
  destruct state as [client0 clock0 locs p bind pend pdel]. simpl in *.
  iIntros "(Hfields & %Hinvs)".
  iDestruct "Hfields" as "(Hclient & Hclock & HdeletedSet & Hitems & Hregistry & Htypes & Hpending & Hpdeletes)".
  iEval (simpl) in "Htypes".
  iDestruct "Htypes" as "(%Hlocswf & Hpool)".
  iDestruct (big_sepM_delete _ _ parent _ Hp with "Hpool") as "[Htype Hrest]".
  iDestruct "Htype" as (ls0) "(%Hls0 & Hyt & %Harrinv)".
  rewrite Hls in Hls0. injection Hls0 as <-.
  iDestruct "Hyt" as (yt tl) "(Hparent & Hdll & %Hlen)".
  iDestruct (own_dll_acc (DfracOwn 1) parent _ tl ls (tm_runs tm) k lc r Hlk Hrk with "Hdll")
    as (prev nxt) "(_ & _ & %Hrun & _ & %Hcontent_length & Hnode & Hback)".
  iExists prev, nxt. iFrame "Hnode".
  iSplitR; first done. iSplitR; first done.
  iIntros "Hnode". iDestruct ("Hback" with "Hnode") as "Hdll".
  iSplitL; last done. rewrite /own_store_fields /=.
  iFrame "Hclient Hclock HdeletedSet Hitems Hregistry Hpending Hpdeletes".
  iSplitR; first done.
  iApply big_sepM_delete; first exact Hp.
  iFrame "Hrest". iExists ls. iSplitR; first done. iSplitL; last done.
  iExists yt, tl. iFrame "Hparent Hdll". done.
Qed.

(** [store.updateItemOfNode]: the decoded struct of the node at slot [k] of
    the type at [parent] denotes the wire item of that slot's run
    ([input_of_run]), under the name the registry binds to the type. The
    struct shares the node's origin cells and content, both read-only. *)
Lemma wp_store__updateItemOfNode (s lc parent : loc) (state : store_state)
    (ls : list loc) (tm : type_model) (k : nat) (r : ItemRun) :
  ss_locs state !! parent = Some ls ->
  ss_pool state !! parent = Some tm ->
  ls !! k = Some lc ->
  tm_runs tm !! k = Some r ->
  {{{ is_pkg_init yjs ∗ own_store_state s 1 state }}}
    s @! (go.PointerType yjs.store) @! "updateItemOfNode" #lc
  {{{ (updateItemVal : yjs.updateItem.t) (name : go_string), RET #updateItemVal;
      own_store_state s 1 state ∗ ⌜ss_bind state !! name = Some parent⌝ ∗
      is_update_item updateItemVal (RootId name, input_of_run r) }}}.
Proof using Type*.
  move=> Hls Hp Hlk Hrk.
  iIntros (Φ) "(#Hpkg & Hstate) HΦ".
  iDestruct (own_store_state_registry_coh with "Hstate") as %(_ & _ & Hnamed).
  destruct (Hnamed parent ltac:(by eexists)) as [name0 Hname0].
  wp_method_call. wp_call. wp_call. wp_auto.
  iDestruct (own_store_state_item_node_acc s state parent ls tm k lc r Hls Hp Hlk Hrk with "Hstate")
    as (prev nxt) "(%Hrun & %Hcontent_length & Hnode & Hback)".
  iDestruct "Hnode" as (itemVal origin_left origin_right)
    "(Hval & #Horigin_left & #Horigin_right & %Hin_left & %Hin_right & %Hid & #Hcontent & %Hparent & %Hprev & %Hnext & %Hflags)".
  have Hnonempty : (1 <= length (in_content (input_of_run r)))%nat.
  { rewrite /= Hcontent_length. destruct Hrun as [Hrun_nonempty _].
    destruct (run_items r); [done | simpl; lia]. }
  iPoseProof "Horigin_left" as "Hleft". iPoseProof "Horigin_right" as "Hright".
  wp_auto.
  destruct origin_left as [left_id |].
  - (* a left origin: no parent name *)
    iDestruct "Hleft" as "[%Hleft_nonnull _]".
    rewrite (bool_decide_eq_false_2 _ Hleft_nonnull). wp_auto.
    iDestruct ("Hback" with "[Hval]") as "Hstate".
    { iExists itemVal, _, _. iFrame "Hval Horigin_left Horigin_right Hcontent". done. }
    iApply ("HΦ" $! _ name0). iFrame "Hstate". iSplitR; first done.
    iExists (Some left_id), origin_right, None. iFrame "Horigin_left Horigin_right Hcontent".
    iPureIntro. split_and!; try done; try exact Hnonempty.
    split; last done. move=> _. left. by rewrite -Hin_left.
  - iDestruct "Hleft" as %Hleft_null.
    rewrite (bool_decide_eq_true_2 _ Hleft_null). wp_auto.
    destruct origin_right as [right_id |].
    + (* a right origin only: no parent name *)
      iDestruct "Hright" as "[%Hright_nonnull _]".
      rewrite (bool_decide_eq_false_2 _ Hright_nonnull). wp_auto.
      iDestruct ("Hback" with "[Hval]") as "Hstate".
      { iExists itemVal, _, _. iFrame "Hval Horigin_left Horigin_right Hcontent". done. }
      iApply ("HΦ" $! _ name0). iFrame "Hstate". iSplitR; first done.
      iExists None, (Some right_id), None. iFrame "Horigin_left Horigin_right Hcontent".
      iPureIntro. split_and!; try done; try exact Hnonempty.
      split; last done. move=> _. right. by rewrite -Hin_right.
    + (* no origin: the struct names its root *)
      iDestruct "Hright" as %Hright_null.
      rewrite (bool_decide_eq_true_2 _ Hright_null). wp_auto.
      iDestruct ("Hback" with "[Hval]") as "Hstate".
      { iExists itemVal, _, _. iFrame "Hval Horigin_left Horigin_right Hcontent". done. }
      rewrite Hparent.
      wp_apply (wp_store__rootName with "[$Hpkg $Hstate]"); first (iPureIntro; by eexists).
      iIntros (name) "[Hstate %Hname]".
      wp_auto.
      iDestruct (typed_pointsto_not_null with "name") as %Hname_nonnull.
      iPersist "name".
      iDestruct (own_store_state_item_node_acc s state parent ls tm k lc r Hls Hp Hlk Hrk with "Hstate")
        as (prev' nxt') "(_ & _ & Hnode & Hback)".
      iDestruct "Hnode" as (itemVal' origin_left' origin_right')
        "(Hval & #Horigin_left' & #Horigin_right' & %Hin_left' & %Hin_right' & %Hid' & #Hcontent' & %Hparent' & %Hprev' & %Hnext' & %Hflags')".
      wp_auto.
      iDestruct ("Hback" with "[Hval]") as "Hstate".
      { iExists itemVal', _, _. iFrame "Hval Horigin_left' Horigin_right' Hcontent'". done. }
      iApply ("HΦ" $! _ name). iFrame "Hstate". iSplitR; first done.
      iExists origin_left', origin_right', (Some name).
      iFrame "Horigin_left' Horigin_right' Hcontent' name".
      iPureIntro. split_and!; try done; try exact Hnonempty.
      all: first
        [ exact Hname_nonnull
        | by move=> nm [= <-]
        | split; first done;
          move=> [Horigin | Horigin];
          [by rewrite -Hin_left in Horigin | by rewrite -Hin_right in Horigin] ].
Qed.

End store_appendSpanStructs.
