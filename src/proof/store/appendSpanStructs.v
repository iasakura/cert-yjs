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

End store_appendSpanStructs.
