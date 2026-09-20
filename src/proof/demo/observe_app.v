(** The application theorem of issue #198, Part II
    (docs/plan-issue-198-observe.md, section 15): a [Mirror] that registers
    a callback on a text ([Text.Observe]) and patches its view with every
    delta it is told keeps the application invariant [app_synced]: the view
    spells the snapshot the callback was last told, a certified document
    state ([is_text_snapshot]). [wp_Mirror__Check] is the final theorem:
    read inside one transaction, the view IS the text, since a transaction
    that wrote nothing left the text's snapshot where the last notification
    put it ([own_transaction_observed_agree]). The patch never fails: the
    delta is [text_delta observed current] and the view is the observed
    text, so [apply_text_delta] gives exactly the premise of
    [wp_ApplyDelta]. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import observeapp.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import observeapp.
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
From New.proof.delta Require Import delta.
From New.proof.transaction Require Import transaction.
From New.proof.store Require Import store.
From New.proof.text Require Import text.
From New.proof.doc Require Import doc.

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
(* the observers' tokens and registrations (issue #198 Part II), as [store/heap] *)
Context {observed_inG : ghost_varG Σ (list (YjsItem go_string * bool))}.
Context {observers_inG : inG Σ (authR (gsetUR (gname * go_string)))}.

Local Notation P := go_string.

Local Notation TId := (TypeId P).

Local Notation Op := (TId * @YjsOperation A)%type.

Local Notation Ev := (@Event Op).

Local Notation DocModel := (gmap TId (list (YjsItem A))).

Local Notation snapshot := (list (YjsItem A * bool)).

(** [mirror_inv m γs γh name γo]: the mirror's lock invariant: its view
    spells the snapshot the callback was last told, held with the
    application's half of the observer's token and the snapshot's
    certificate. *)
Definition mirror_inv (m : loc) (γs : store_names) (γh : history_names) (name : P) (γo : gname) : iProp Σ :=
  ∃ (s : snapshot),
    "Hview" ∷ (m .[(observeapp.Mirror.t), "view"]) ↦ visible_string s ∗
    "Hown_half" ∷ own_observed γo s ∗
    "#Hsnap" ∷ is_text_snapshot γs γh name s.

(** [is_Mirror m d t γs γh name γo]: a mirror of the text [t] (root [name])
    of the document [d], registered as observer [γo] of that root. *)
Definition is_Mirror (m d t : loc) (γs : store_names) (γh : history_names) (name : P) (γo : gname) : iProp Σ :=
  ∃ (s_loc : loc) (L : list (YjsItem A)) (deleted_ids : gset YjsId),
    "#Hdocf" ∷ (m .[(observeapp.Mirror.t), "doc"]) ↦□ d ∗
    "#Htextf" ∷ (m .[(observeapp.Mirror.t), "text"]) ↦□ t ∗
    "#His_doc" ∷ is_Doc d s_loc γs γh ∗
    "#His_text" ∷ is_Text t γs γh name L deleted_ids ∗
    "#Hobserved" ∷ is_text_observed γs name γo ∗
    "#Hmu" ∷ is_Mutex (m .[(observeapp.Mirror.t), "mu"]) (mirror_inv m γs γh name γo).

#[global] Instance is_Mirror_persistent m d t γs γh name γo : Persistent (is_Mirror m d t γs γh name γo).
Proof. rewrite /is_Mirror. apply _. Qed.

(** The empty snapshot of a root is certified by an empty history: what the
    mirror's view is before the callback hears the current text. *)
#[local] Lemma is_text_snapshot_nil (t : loc) (γs : store_names) (γh : history_names)
    (c : ClientId) (name : P) (L : list (YjsItem A)) (deleted_ids : gset YjsId) :
  is_Text t γs γh name L deleted_ids -∗
  is_store_client γs c -∗
  is_history_lb γh c ([] : list Ev) -∗
  |==> is_text_snapshot γs γh name [].
Proof.
  iIntros "Htext #Hpin #Hlb".
  iDestruct "Htext" as (tv s_loc parent deleted_items) "Htext". iNamed "Htext".
  iMod (auth_gset_frag_empty γs.(sn_delete_set)) as "#Hdellb".
  iModIntro. iExists parent, c, []. iFrame "Hbind Hpin Hlb".
  iSplit.
  { rewrite /is_type_lb /=. iApply (auth_gmap_gset_frag_weaken _ _ ∅ (list_to_set L) with "His_lb").
    apply empty_subseteq. }
  iSplit; first iExact "Hdellb".
  iPureIntro. split; [exact YjsArrInvariant_nil | move=> input Hin; by apply elem_of_nil in Hin].
Qed.

(** [NewMirror]: the mirror's callback meets [is_text_callback] with a fresh
    token, both halves at the empty snapshot; [Observe] then tells it the
    current text and registers it. *)
Lemma wp_NewMirror (d t s_loc : loc) (γs : store_names) (γh : history_names)
    (c : ClientId) (name : P) (L : list (YjsItem A)) (deleted_ids : gset YjsId) :
  {{{ is_pkg_init observeapp ∗ is_Doc d s_loc γs γh ∗ is_Text t γs γh name L deleted_ids ∗
      is_store_client γs c ∗ is_history_lb γh c ([] : list Ev) }}}
    @! observeapp.NewMirror #d #t
  {{{ (m : loc) (γo : gname), RET #m; is_Mirror m d t γs γh name γo }}}.
Proof.
  wp_start as "(#His_doc & #His_text & #Hpin & #Hlb)".
  iApply wp_fupd.
  wp_auto. wp_alloc m as "Hm". wp_auto.
  iMod (own_observed_alloc []) as (γo) "[Hhalf_app Hhalf_store]".
  iMod (is_text_snapshot_nil with "His_text Hpin Hlb") as "#Hsnap_nil".
  iStructNamed "Hm".
  (* the closure reads the local [m]; the fields it does not write and the
     local itself become read-only *)
  iPersist "doc text".
  iPersist "m".
  iMod (init_Mutex (mirror_inv m γs γh name γo) with "[$mu] [view Hhalf_app]") as "#Hmu".
  { iNext. iExists []. iFrame "view Hhalf_app Hsnap_nil". }
  wp_apply (wp_Text__Observe with "[$His_text $Hhalf_store]").
  { (* the callback's contract, from the mirror's lock alone *)
    rewrite /is_text_callback.
    iIntros (sl dq observed current Φ') "!> (Hobs & Hdelta & %Hgrows & #Hsnap_current) HΦ'".
    wp_auto.
    wp_apply (wp_Mutex__Lock with "[$Hmu]"). iIntros "[Hlocked Hinv]".
    iEval (rewrite /mirror_inv) in "Hinv". iDestruct "Hinv" as (s) "(Hview & Hown_half & #Hsnap)".
    iDestruct (own_observed_agree with "Hown_half Hobs") as %<-.
    wp_auto.
    iDestruct "Hsnap_current" as (parent c' h) "Hsnap'". iNamed "Hsnap'".
    have Huniq : uniqueId current.*1 := yai_unique _ Hsnapshot_invariant.
    have Hpatch : apply_delta (text_delta s current) (visible_string s) = Some (visible_string current)
      := apply_text_delta s current Hgrows Huniq.
    wp_apply (wp_ApplyDelta _ _ _ _ _ Hpatch with "[$Hdelta]"). iIntros "Hdelta".
    wp_auto.
    iMod (own_observed_update _ _ _ current with "Hown_half Hobs") as "[Hown_half Hobs]".
    wp_apply (wp_Mutex__Unlock with "[$Hmu $Hlocked Hview Hown_half]").
    { iNext. iExists current. iFrame "Hview Hown_half".
      iExists parent, c', h. iFrame "#". iPureIntro. split; assumption. }
    iApply "HΦ'". iFrame "Hobs Hdelta". }
  iIntros "#Hobserved".
  wp_auto.
  iModIntro. iApply ("HΦ" $! m γo).
  iExists s_loc, L, deleted_ids. iFrame "#".
Qed.

(** [Mirror.Text] reads the view under the mirror's lock: the visible string
    of the snapshot the callback was last told, certified. At that moment
    the caller may learn what it likes from the mirror's token half
    ([Ψ], through the wand): what [Check] uses to tie the view's snapshot to
    the transaction's. *)
Lemma wp_Mirror__Text (m d t : loc) (γs : store_names) (γh : history_names) (name : P) (γo : gname)
    (Ψ : snapshot -> iProp Σ) :
  {{{ is_pkg_init observeapp ∗ is_Mirror m d t γs γh name γo ∗
      (∀ s, own_observed γo s -∗ own_observed γo s ∗ Ψ s) }}}
    m @! (go.PointerType observeapp.Mirror) @! "Text" #()
  {{{ (s : snapshot), RET #(visible_string s); is_text_snapshot γs γh name s ∗ Ψ s }}}.
Proof.
  wp_start as "(#Hmirror & Hwand)". iNamed "Hmirror".
  wp_auto.
  wp_apply (wp_Mutex__Lock with "[$Hmu]"). iIntros "[Hlocked Hinv]".
  iEval (rewrite /mirror_inv) in "Hinv". iDestruct "Hinv" as (s) "(Hview & Hown_half & #Hsnap)".
  iDestruct ("Hwand" $! s with "Hown_half") as "[Hown_half HΨ]".
  wp_auto.
  wp_apply (wp_Mutex__Unlock with "[$Hmu $Hlocked Hview Hown_half]").
  { iNext. iExists s. iFrame "Hview Hown_half Hsnap". }
  iApply ("HΦ" $! s). iFrame "Hsnap HΨ".
Qed.

(** THE theorem: inside one transaction the view equals the text. The
    transaction writes nothing, so the text's snapshot is the one the last
    notification told the mirror ([own_transaction_observed_agree]), and
    [StringIn] reads exactly that snapshot's visible string. *)
Lemma wp_Mirror__Check (m d t : loc) (γs : store_names) (γh : history_names) (name : P) (γo : gname) :
  {{{ is_pkg_init observeapp ∗ is_Mirror m d t γs γh name γo }}}
    m @! (go.PointerType observeapp.Mirror) @! "Check" #()
  {{{ RET #true; True }}}.
Proof.
  wp_start as "#Hmirror".
  iPoseProof "Hmirror" as (s_loc L deleted_ids) "Hparts". iNamed "Hparts".
  wp_auto.
  wp_apply (wp_Doc__Transact _ _ _ _ _ (λ _ _ _ _ _, ok_ptr ↦ true)%I with "[$His_doc ok m]").
  { rewrite /closure_runs_transaction.
    iIntros (tr c h m0 pend deleted Ψ') "Htx HΨ'".
    wp_auto.
    wp_apply (wp_Text__StringIn with "[$His_text $Htx]"). iIntros "[_ Htx]".
    wp_auto.
    (* the mirror's view, its snapshot tied to the transaction's at the
       lock's linearization point *)
    wp_apply (wp_Mirror__Text _ _ _ _ _ _ _
                (λ s, own_transaction tr s_loc γs γh c h m0 pend deleted ∅ ∅ ∅ ∗
                      ⌜s = type_snapshot m0 deleted name⌝)%I
                with "[$Hmirror Htx]").
    { iIntros (s) "Hhalf".
      iDestruct (own_transaction_observed_agree _ _ _ _ _ _ _ _ _ _ _ _ name γo s
                   (not_elem_of_empty name) with "Htx Hobserved Hhalf") as %Heq.
      iFrame "Hhalf Htx". iPureIntro. exact Heq. }
    iIntros (s) "(#Hsnap_s & Htx & %Heq)". subst s.
    wp_auto.
    (* the stored comparison is of one string with itself *)
    rewrite bool_decide_eq_true_2; last reflexivity.
    iApply ("HΨ'" $! h m0 pend deleted ∅ ∅ ∅). iFrame "Htx ok". }
  iIntros "HQ". iDestruct "HQ" as (c h' m' pend' deleted') "ok".
  wp_auto.
  iApply "HΦ". done.
Qed.

End observe_app.
