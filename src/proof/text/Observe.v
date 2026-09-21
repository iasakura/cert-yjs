(** [wp_Text__Observe]: registering a push observer (issue #198 Part II C2).
    Under the store's write lock the callback is told the delta from the
    empty snapshot to the text's current one first (the whole visible text
    as one insert, [text_delta_from_empty]), certified by the store, and is
    then appended to the type's callback slice with its token registered
    at the authority; the caller keeps the registration witness
    [is_text_observed]. The store's half of the observer's token comes in
    at the empty snapshot and the callback's own contract moves it. *)
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
From New.proof.transaction Require Import transaction.
From New.proof.delta Require Import delta.
From New.proof.store Require Import store.
From New.proof.sync_proof Require Import mutex.
From iris.algebra Require Import auth gmap gset.
From iris.algebra.lib Require Import dfrac_agree.
From stdpp Require Import sorting.
From New.proof.text Require Import model heap.
From New.proof.github_com.mit_pdos.perennial.goose.model Require Import strings.

(* iris.algebra / stdpp.sorting push [nat_scope], retuning the default [<] / [≤];
   the verified word-arithmetic proofs write [Z] comparisons unannotated, so
   restore [Z_scope] as the default. *)
Local Open Scope Z_scope.

Section text.
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
Local Notation TId := (TypeId P).
Local Notation Op := (TId * @YjsOperation A)%type.
Local Notation Ev := (@Event Op).
Local Notation DocModel := (gmap TId (list (YjsItem A))).
Local Notation snapshot := (list (YjsItem A * bool)).

(** [Text.Observe] registers [cb], whose contract is [is_text_callback] with
    the token [γo], on this text: the callback hears the current text first
    (from the empty snapshot), then every transaction that changes the text
    ([store.notify]). The store's half of the token comes in at the empty
    snapshot. *)
Lemma wp_Text__Observe (t : loc) (γs : store_names) (γh : history_names) (name : P)
    (L : list (YjsItem A)) (deleted_ids : gset YjsId) (cb : func.t) (γo : gname) :
  {{{ is_pkg_init yjs ∗ is_Text t γs γh name L deleted_ids ∗
      is_text_callback γs γh name cb γo ∗ own_observed γo [] }}}
    t @! (go.PointerType yjs.Text) @! "Observe" #cb
  {{{ RET #(); is_text_observed γs name γo }}}.
Proof.
  wp_start as "(Htext & #Hcb & Hobs)".
  iDestruct "Htext" as (tv text_store parent deleted_items) "Htext". iNamed "Htext".
  iDestruct "His_store" as "#His_store". iDestruct "Ht" as "#Ht". iDestruct "His_lb" as "#His_lb".
  subst text_store parent.
  wp_auto.
  wp_apply (wp_Store__wlock with "[$His_store]"). iIntros "[Hlk Hinv]".
  iDestruct "Hinv" as (c h m pend deleted observers_mref) "[Hstore Hreg]".
  wp_auto.
  (* ---- the current text ---- *)
  iDestruct "Hstore" as (client k pdel locs p bind acc observers_mref0) "Hown". iNamed "Hown".
  iDestruct (ghost_map_lookup with "HtypesAuth Hbind") as %Hbindlk.
  iDestruct (own_store_state_registry_coh with "Hstate") as %Hregcoh.
  iDestruct (own_store_state_run_pool_invs with "Hstate") as %Hpoolinv.
  iDestruct (own_store_state_aligned with "Hstate") as %Haligned.
  simpl in Hregcoh, Hpoolinv, Haligned.
  destruct (proj1 Hregcoh name _ Hbindlk) as [ts Htsp].
  have Hmt : doc_model_get m (RootId name) = tm_arr ts := proj1 Hregmodel name _ ts Hbindlk Htsp.
  have [ls Hls] : ∃ ls, locs !! tv.(yjs.Text.inner') = Some ls.
  { apply elem_of_dom. rewrite (proj1 Haligned). apply elem_of_dom. by exists ts. }
  have Hsnap : runs_model (tm_runs ts) = type_snapshot m deleted name.
  { rewrite Hdeleted. exact (type_snapshot_runs_model m bind p name _ ts Hpoolinv Hregmodel Hbindlk Htsp). }
  iDestruct (own_store_state_ytype_acc tv.(yjs.Text.store') (MkStoreState client k locs p bind pend pdel)
               tv.(yjs.Text.inner') ls ts Hls Htsp with "Hstate") as "[Hyt Hytback]".
  iDestruct "Hyt" as (yt tl) "Hyt". iNamed "Hyt".
  iDestruct (own_dll_run_per_char with "Hdll") as %Hperchar.
  iAssert (own_ytype tv.(yjs.Text.inner') (DfracOwn 1) ls ts) with "[Hparent Hdll]" as "Hyt".
  { iExists yt, tl. iFrame "Hparent Hdll". iPureIntro. exact Hlen. }
  wp_apply (wp_yType__Text with "[$Hyt]"). iIntros "Hyt".
  iDestruct ("Hytback" with "Hyt") as "Hstate".
  rewrite Hsnap.
  (* every visible char carries one byte, so the string is empty exactly
     when nothing is visible *)
  have Hnonempty : ∀ x, x ∈ visible_items (type_snapshot m deleted name) -> content x ≠ [].
  { move=> x Hx.
    have Hx1 : x ∈ (type_snapshot m deleted name).*1.
    { rewrite /visible_items in Hx. apply list_elem_of_fmap in Hx as (y & -> & Hy).
      apply list_elem_of_filter in Hy as [_ Hy]. apply list_elem_of_fmap. by exists y. }
    rewrite type_snapshot_fst Hmt /tm_arr /runs_flatten list_elem_of_join in Hx1.
    destruct Hx1 as (items & Hxitems & Hitems).
    apply list_elem_of_fmap in Hitems as (r & -> & Hr).
    destruct (run_per_char_content (run_items r) x (Hperchar r Hr) Hxitems) as [b Hb].
    rewrite Hb. discriminate. }
  iNamed "Hreg".
  (* the registry's map is the store's [observers] field *)
  iDestruct (is_store_observers_agree with "Hobserverspin Hregistrypin") as %Heqref. subst observers_mref0.
  iDestruct (registered_bindings_lookup with "HtypesAuth Hregistered_bind") as %Hregbind.
  iAssert (own_store tv.(yjs.Text.store') γs γh c h m pend deleted)
    with "[Hstate Hseq HtypesAuth Hhist Hacc Hdelete_set Hobserversf]" as "Hstore".
  { iExists client, k, pdel, locs, p, bind, acc, observers_mref. iFrame "∗#". iPureIntro. split_and!;
      [exact Hclientc | exact Hpendroot | exact Hpendbnd | exact Hregmodel | exact Hhcoh
      | exact Hctr | exact Hacccoh | exact Hdeleted]. }
  iMod (own_store_text_snapshot with "Hbind Hstore") as "[Hstore #Hsnapshot]".
  wp_auto.
  (* ---- the initial delta: the whole visible text, as one insert ---- *)
  wp_apply wp_string_len. iIntros "%Hstrlen".
  wp_auto.
  (* [wp_if_join] substitutes every variable equation; keep [deleted] *)
  clear Hdeleted.
  wp_if_join (λ v, ⌜v = execute_val⌝ ∗
    ∃ (initial_sl : slice.t),
      "initial" ∷ initial_ptr ↦ initial_sl ∗
      "Hdelta" ∷ own_delta initial_sl (DfracOwn 1) (text_delta [] (type_snapshot m deleted name)))%I
    with "[initial text]".
  { (* nonempty: one insert *)
    wp_apply wp_slice_literal. iSplitR; first done. iIntros "%s2 [Hs2 _]". wp_auto.
    wp_apply (wp_slice_append with "[Hs2]").
    { iSplitR; [iApply own_slice_nil | iSplitR; [iApply own_slice_cap_nil | iFrame "Hs2"]]. }
    iIntros (sl') "(Hsl' & Hcap' & _)". wp_auto.
    iSplitR; first done. iExists sl'. iFrame "initial".
    rewrite (text_delta_from_empty_string _ Hnonempty).
    rewrite decide_False; last first.
    { move=> Heq. rewrite Heq /= in l. word. }
    iExists [_]. iFrame "Hsl' Hcap'". iPureIntro. simpl. constructor; [split; reflexivity | constructor]. }
  { (* empty: nothing to say *)
    iSplitR; first done. iExists slice.nil. iFrame "initial".
    rewrite (text_delta_from_empty_string _ Hnonempty).
    rewrite decide_True; last first.
    { destruct (visible_string (type_snapshot m deleted name)) as [| b bs] eqn:Hvs; first done.
      exfalso. apply n. simpl in Hstrlen |- *. word. }
    iApply own_delta_nil. }
  iIntros (v) "(-> & Hjoin)". iDestruct "Hjoin" as (initial_sl) "Hjoin". iNamed "Hjoin".
  wp_auto.
  (* ---- the callback hears the current text ---- *)
  wp_apply ("Hcb" $! initial_sl (DfracOwn 1) [] (type_snapshot m deleted name) with "[Hobs Hdelta]").
  { iFrame "Hobs Hdelta Hsnapshot". iPureIntro. apply snapshot_grows_to_nil. }
  iIntros "[Hobs Hdelta]".
  (* ---- the registration: the type's callback slice grows by [cb], the
     authority by the token; the [observers] field is read off the store ---- *)
  iDestruct (own_store_observers_acc with "Hstore") as (observers_mref1) "(#Hpin1 & Hobserversf & Hstoreback)".
  iDestruct (is_store_observers_agree with "Hpin1 Hregistrypin") as %Heqref1. subst observers_mref1.
  wp_auto.
  wp_apply (wp_map_lookup1 with "Hobserversmap"). iIntros "Hobserversmap".
  wp_auto.
  iDestruct (big_sepM2_dom with "Hobservers") as %Hdomeq.
  destruct (registry !! tv.(yjs.Text.inner')) as [cbs_sl |] eqn:Hrkey.
  - (* the type already has observers *)
    have [entry Hdkey] : is_Some (registered !! tv.(yjs.Text.inner')).
    { apply elem_of_dom. rewrite -Hdomeq. apply elem_of_dom. by exists cbs_sl. }
    have Hentryname : entry.1 = name.
    { exact (proj1 (proj2 Hregcoh) _ _ _ (Hregbind _ _ Hdkey) Hbindlk). }
    destruct entry as [ename γos]. simpl in Hentryname. subst ename.
    iEval (rewrite (big_sepM2_delete _ _ _ _ cbs_sl (name, γos) Hrkey Hdkey)) in "Hobservers".
    iDestruct "Hobservers" as "[Hentry Hobservers]".
    iDestruct "Hentry" as (cbs) "Hentry". iNamed "Hentry". iEval (simpl) in "Hentry_callbacks".
    wp_apply wp_slice_literal. iSplitR; first done. iIntros "%s2 [Hs2 _]". wp_auto.
    wp_apply (wp_slice_append with "[$Hentry_slice $Hentry_cap $Hs2]").
    iIntros (sl') "(Hsl' & Hcap' & _)". wp_auto.
    wp_apply (wp_map_insert with "Hobserversmap"). iIntros "Hobserversmap". wp_auto.
    iDestruct ("Hstoreback" with "Hobserversf") as "Hstore".
    iMod (observers_register γs _ γo name with "Hobserversauth") as "[Hobserversauth #Hobserved]".
    wp_apply (wp_Store__wunlock with "[$His_store $Hlk $Hstore Hobserversmap Hobserversauth Hobservers Hsl' Hcap' Hentry_callbacks Hobs]").
    { iExists (<[tv.(yjs.Text.inner') := sl']> registry),
        (<[tv.(yjs.Text.inner') := (name, γos ++ [γo])]> registered).
      iFrame "Hregistrypin Hobserversmap".
      rewrite (registered_tokens_register registered _ name γos γo (or_introl Hdkey)).
      iFrame "Hobserversauth".
      iSplitR.
      { iApply big_sepM_insert_2; [iEval (simpl); iFrame "Hbind" | iFrame "Hregistered_bind"]. }
      rewrite big_sepM2_insert_delete. iFrame "Hobservers".
      iExists (cbs ++ [cb]). iFrame "Hsl' Hcap'". iEval (cbn [fst snd]).
      rewrite big_sepL2_snoc. iFrame "Hentry_callbacks Hcb Hobs". }
    iApply ("HΦ" with "Hobserved").
  - (* the first observer of this type *)
    have Hdkey : registered !! tv.(yjs.Text.inner') = None.
    { apply not_elem_of_dom. rewrite -Hdomeq. by apply not_elem_of_dom. }
    wp_apply wp_slice_literal. iSplitR; first done. iIntros "%s2 [Hs2 _]". wp_auto.
    wp_apply (wp_slice_append with "[Hs2]").
    { iSplitR; [iApply own_slice_nil | iSplitR; [iApply own_slice_cap_nil | iFrame "Hs2"]]. }
    iIntros (sl') "(Hsl' & Hcap' & _)". wp_auto.
    wp_apply (wp_map_insert with "Hobserversmap"). iIntros "Hobserversmap". wp_auto.
    iDestruct ("Hstoreback" with "Hobserversf") as "Hstore".
    iMod (observers_register γs _ γo name with "Hobserversauth") as "[Hobserversauth #Hobserved]".
    wp_apply (wp_Store__wunlock with "[$His_store $Hlk $Hstore Hobserversmap Hobserversauth Hobservers Hsl' Hcap' Hobs]").
    { iExists (<[tv.(yjs.Text.inner') := sl']> registry),
        (<[tv.(yjs.Text.inner') := (name, [] ++ [γo])]> registered).
      iFrame "Hregistrypin Hobserversmap".
      rewrite (registered_tokens_register registered _ name [] γo (or_intror (conj Hdkey eq_refl))).
      iFrame "Hobserversauth".
      iSplitR.
      { iApply big_sepM_insert_2; [iEval (simpl); iFrame "Hbind" | iFrame "Hregistered_bind"]. }
      rewrite (big_sepM2_insert _ _ _ _ _ _ Hrkey Hdkey). iFrame "Hobservers".
      iExists ([] ++ [cb]). iFrame "Hsl' Hcap'". iEval (cbn [fst snd]).
      rewrite big_sepL2_snoc big_sepL2_nil. iSplitR; first done. iFrame "Hcb Hobs". }
    iApply ("HΦ" with "Hobserved").
Qed.

End text.