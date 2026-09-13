(** [wp_Text__NewObserver]: a fresh observer of a [Text] has observed the
    empty snapshot, so its first [Poll] reports the whole visible text as
    inserts (issue #198). *)
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

Local Notation P := go_string.

Lemma wp_Text__NewObserver (t : loc) (γs : store_names) (γh : history_names)
    (name : P) (L : list (YjsItem A)) (deleted_ids : gset YjsId) :
  {{{ is_pkg_init yjs ∗ is_Text t γs γh name L deleted_ids }}}
    t @! (go.PointerType yjs.Text) @! "NewObserver" #()
  {{{ (obs : loc), RET #obs; own_TextObserver obs t γs γh name [] }}}.
Proof.
  wp_start as "Htext". iNamed "Htext".
  iDestruct "His_store" as "#His_store". iDestruct "His_lb" as "#His_lb".
  iMod (is_delete_set_lb_empty γs) as "#Hdlb".
  wp_auto.
  wp_apply wp_map_make1. iIntros (sv_mref) "Hsv".
  wp_auto.
  wp_apply wp_map_make1. iIntros (deleted_mref) "Hdm".
  wp_auto.
  wp_alloc obs as "Hobs".
  wp_auto.
  (* the empty item set at this root: the handle's lower bound, weakened *)
  iDestruct (auth_gmap_gset_frag_weaken γs.(sn_seq) parent ∅ (list_to_set L) (empty_subseteq _)
               with "His_lb") as "#Hitems0".
  iApply "HΦ".
  iExists _, tv, s_loc, parent, ∅, {[parent := ∅]}.
  iFrame "Hobs Ht His_store Hbind Hsv Hitems0 Hdlb".
  iSplitR; first done.
  iSplitR; first done.
  iSplitR; first done.
  iSplitR.
  { iPureIntro. move=> client. rewrite lookup_empty /sv_get lookup_empty //. }
  iSplitL.
  { iExists ∅, ∅. iFrame "Hdm". rewrite big_sepM2_empty. iSplit; first done.
    iPureIntro. move=> d. split.
    - move=> Hd. exfalso. move: Hd. rewrite /snapshot_deleted_ids /= elem_of_empty //.
    - intros (client & sps & sp & Hlk & _). rewrite lookup_empty in Hlk. discriminate. }
  iPureIntro. split_and!.
  - rewrite lookup_insert_eq //.
  - move=> c j. rewrite /sv_get lookup_empty /=. lia.
  - exact YjsArrInvariant_empty.
Qed.

End text_observer.
