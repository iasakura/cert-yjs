(** The application theorem of issue #198 (docs/plan-issue-198-observe.md,
    section 4): a [Mirror] that syncs by one [Poll] and one [ApplyDelta]
    keeps the application invariant [app_synced], the mirror spells the last
    observed snapshot. After a sync the mirror is the visible text of the
    snapshot the poll took, a document state that holds every item a history
    certificate the caller brings has delivered ([history_reflected]), as a
    concurrent read would. The patch never fails: the delta is
    [text_delta observed current] and the mirror is the observed text, so
    [apply_text_delta] applies and its counts fit ([apply_delta_fits]). *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import observeapp.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import observeapp.
From New.proof Require Import core.
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
From New.proof.textobserver Require Import textobserver.

Section observe_app.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Context {sync_pkg : sync.Assumptions}.

Context {observeapp_pkg : observeapp.Assumptions}.

#[global] Instance : IsPkgInit (iProp Σ) observeapp := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) observeapp := build_get_is_pkg_init_wf.

Set Default Proof Using "Type*".

Notation A := go_string.

Context {seq_inG : inG Σ (authR (gmapUR loc (gsetUR (YjsItem A))))}.

Context {acc_inG : inG Σ (authR (gsetUR YjsId))}.

Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO addressed_pool))}.

Local Notation P := go_string.

Local Notation TId := (TypeId P).

Local Notation Op := (TId * @YjsOperation A)%type.

Local Notation Ev := (@Event Op).

Local Notation snapshot := (list (YjsItem A * bool)).

(** [own_mirror m app]: the mirror at [m] holds the string [app]. *)
Definition own_mirror (m : loc) (app : go_string) : iProp Σ :=
  m ↦ observeapp.Mirror.mk app.

Lemma wp_NewMirror :
  {{{ is_pkg_init observeapp }}}
    @! observeapp.NewMirror #()
  {{{ (m : loc), RET #m; own_mirror m ""%go }}}.
Proof.
  wp_start. wp_alloc m as "Hm". wp_auto.
  iApply "HΦ". iFrame "Hm".
Qed.

(** One sync: the mirror spelled the observed snapshot ([app_synced app
    observed]) and spells the current one afterwards; the current snapshot
    is what a read of the text sees ([text_snapshot], [history_reflected],
    [visible_excludes]), and it grows from the observed one. *)
Lemma wp_Mirror__Sync (m obs t : loc) (γs : store_names) (γh : history_names)
    (c : ClientId) (name : P) (L : list (YjsItem A)) (deleted_ids : gset YjsId)
    (app : go_string) (observed : snapshot) (h0 : list Ev) :
  {{{ is_pkg_init observeapp ∗ own_mirror m app ∗ ⌜app_synced app observed⌝ ∗
      own_TextObserver obs t γs γh name observed ∗
      is_Text t γs γh name L deleted_ids ∗ is_store_client γs c ∗ is_history_lb γh c h0 }}}
    m @! (go.PointerType observeapp.Mirror) @! "Sync" #obs
  {{{ (current : snapshot), RET #true;
      own_mirror m (visible_string current) ∗
      own_TextObserver obs t γs γh name current ∗
      ⌜snapshot_grows_to observed current⌝ ∗
      ⌜text_snapshot L current⌝ ∗ ⌜history_reflected h0 name current⌝ ∗
      ⌜visible_excludes deleted_ids current⌝ }}}.
Proof.
  wp_start as "(Hm & %Hsync & Hobs & #Htext & #Hpin & #Hlb)".
  have Happ : app = visible_string observed := Hsync.
  wp_auto.
  wp_apply (wp_TextObserver__Poll with "[$Hobs $Htext $Hpin $Hlb]").
  iIntros (sl current) "(Hobs & Hdelta & %Hgrows & %Hsnap & %Hhist & %Hexcl)".
  wp_auto.
  have Huniq : uniqueId current.*1 := yai_unique _ (proj2 Hsnap).
  have Hpatch : apply_delta (text_delta observed current) app = Some (visible_string current).
  { rewrite Happ. exact (apply_text_delta observed current Hgrows Huniq). }
  wp_apply (wp_ApplyDelta with "[$Hdelta]").
  { iPureIntro. move=> Hlen. exact (apply_delta_fits _ _ _ Hpatch ltac:(lia)). }
  iIntros "Hdelta".
  rewrite Hpatch /=.
  wp_auto.
  iApply "HΦ". iFrame "Hm Hobs". iPureIntro. split_and!; assumption.
Qed.

End observe_app.
