(** [wp_Text__StringIn]: the text as the transaction sees it (issue #206
    T1): a read inside [Doc.Transact], over [own_transaction], returning
    the visible string of the type's snapshot at the transaction's current
    model and tombstone state ([type_snapshot]). Shares [is_Text] etc. via
    [text/heap]. *)
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
From New.proof.store Require Import store.
From New.proof.sync_proof Require Import mutex.
From iris.algebra Require Import auth gmap gset.
From iris.algebra.lib Require Import dfrac_agree.
From stdpp Require Import sorting.
From New.proof.text Require Import model heap.

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


(** [Text.StringIn] reads the text inside a transaction: the visible string
    of this text's snapshot at the transaction's model and tombstone state,
    which is exact (the tombstone set is [own_store]'s, not a lower bound).
    Nothing changes: the handle and the transaction come back as they were. *)
Lemma wp_Text__StringIn (t tr s_loc : loc) (γs : store_names) (γh : history_names)
    (name : P) (L : list (YjsItem A)) (deleted_ids : gset YjsId)
    (c : ClientId) (h : list Ev) (m : DocModel) (pend : list (TId * IntegrateInput (A := A)))
    (deleted inserted tombstoned : gset YjsId) (changed : gset P) :
  {{{ is_pkg_init yjs ∗ is_Text t γs γh name L deleted_ids ∗
      own_transaction tr s_loc γs γh c h m pend deleted inserted tombstoned changed }}}
    t @! (go.PointerType yjs.Text) @! "StringIn" #tr
  {{{ RET #(visible_string (type_snapshot m deleted name));
      is_Text t γs γh name L deleted_ids ∗
      own_transaction tr s_loc γs γh c h m pend deleted inserted tombstoned changed }}}.
Proof.
  wp_start as "(Htext & Htx)".
  iDestruct "Htext" as (tv text_store parent deleted_items) "Htext". iNamed "Htext".
  iDestruct "His_store" as "#His_store". iDestruct "Ht" as "#Ht". iDestruct "His_lb" as "#His_lb".
  subst text_store parent.
  iDestruct "Htx" as (changed_locs m0 deleted0 registry_mref) "Htx". iNamed "Htx".
  iDestruct "Hstore" as (client k pdel locs p bind acc observers_mref) "Hown". iNamed "Hown".
  (* the registry binds [name] to this text, whose document is the model's *)
  iDestruct (ghost_map_lookup with "HtypesAuth Hbind") as %Hbindlk.
  iDestruct (own_store_state_registry_coh with "Hstate") as %Hreg.
  iDestruct (own_store_state_run_pool_invs with "Hstate") as %Hpoolinv.
  iDestruct (own_store_state_aligned with "Hstate") as %Haligned.
  have [Hbindtypes _] := Hreg.
  have [Hmtypes _] := Hregmodel.
  destruct (Hbindtypes name _ Hbindlk) as [ts Htsp].
  have Hmt : doc_model_get m (RootId name) = tm_arr ts := Hmtypes name _ ts Hbindlk Htsp.
  have [ls Hls] : ∃ ls, locs !! tv.(yjs.Text.inner') = Some ls.
  { apply elem_of_dom. rewrite (proj1 Haligned). apply elem_of_dom. by exists ts. }
  (* the walk sees the runs' bits, which are the tombstone set's membership *)
  have Hsnap : runs_model (tm_runs ts) = type_snapshot m deleted name.
  { rewrite /type_snapshot Hmt Hdeleted. exact (runs_model_tombstoned p _ ts Hpoolinv Htsp). }
  wp_auto.
  iDestruct (own_store_state_ytype_acc s_loc (MkStoreState client k locs p bind pend pdel)
               tv.(yjs.Text.inner') ls ts Hls Htsp with "Hstate") as "[Hyt Hytback]".
  wp_apply (wp_yType__Text with "[$Hyt]"). iIntros "Hyt".
  iDestruct ("Hytback" with "Hyt") as "Hstate".
  wp_auto.
  rewrite Hsnap.
  iApply "HΦ".
  iSplitR.
  { iExists tv, tv.(yjs.Text.store'), tv.(yjs.Text.inner'), deleted_items.
    iFrame "Ht His_store His_hist Hbind His_lb Hdeleted_lb Hdeleted_items".
    iPureIntro. split_and!; [reflexivity | reflexivity | exact Hdeleted_known | exact Hsorted]. }
  iExists changed_locs, m0, deleted0, registry_mref. iFrame "Hchanges Hregistry Hchanged_bound".
  iSplitL.
  { iExists client, k, pdel, locs, p, bind, acc, observers_mref. iFrame "∗#". iPureIntro. split_and!;
      [exact Hclientc | exact Hpendroot | exact Hpendbnd | exact Hregmodel | exact Hhcoh
      | exact Hctr | exact Hacccoh | exact Hdeleted]. }
  iPureIntro. split_and!; [exact Hstart | exact Hinserted_dom | exact Htombstoned_sub | exact Hrecorded].
Qed.

End text.
