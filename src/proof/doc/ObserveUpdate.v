(** [wp_Doc__ObserveUpdate] (issue #131): registering a callback for the
    updates of the document. The caller gives the callback's contract
    ([is_update_callback]), the encoder's ([encoder_spec]) and the global
    history's invariant; from then on the store calls the callback at the
    end of every transaction that integrated something. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core.
From New.proof Require Import prelude.
From New.proof Require Import history.
From New.proof.id Require Import id.
From New.proof.item Require Import item.
From New.proof.ytype Require Import ytype.
From New.proof.transaction Require Import transaction.
From New.proof.store Require Import store.
From New.proof.text Require Import text.
From New.proof.sync_proof Require Import mutex.
From iris.algebra Require Import auth gmap gset.
From iris.algebra.lib Require Import dfrac_agree.
From New.proof.doc Require Import model heap.

Section doc_ObserveUpdate.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

(* [is_store_ref] (from store/store) is generalized over the store lock + item-set RA,
   so mirror its Context here to apply it. *)
Context {sync_pkg : sync.Assumptions}.

Set Default Proof Using "Type*".

Notation A := (list w16).

Notation P := go_string.

Local Notation TId := (TypeId P).

Local Notation Op := (TId * @YjsOperation A)%type.

Local Notation Ev := (@Event Op).

Local Notation DocModel := (gmap TId (list (YjsItem A))).

Context {seq_inG : inG Σ (authR (gmapUR loc (gsetUR (YjsItem A))))}.

Context {acc_inG : inG Σ (authR (gsetUR YjsId))}.

(* [is_store_ref]'s reader-count accounting ties the readers' share to the store's
   [types] map via a [dfrac_agree]; mirror the instance here to apply [is_store_ref]. *)
Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO store_state))}.
(* the observers' tokens and registrations (issue #198 Part II), as [store/heap] *)
Context {observed_inG : ghost_varG Σ (list (YjsItem A * bool))}.
Context {observers_inG : inG Σ (authR (gsetUR (gname * go_string)))}.
Context {observers_agree_inG : inG Σ (dfrac_agreeR (leibnizO registered_entries))}.


(** [Doc.ObserveUpdate]: the registration gives nothing back. What the
    caller gains is in the callback's contract: every later call of the
    callback comes with that contract's precondition. *)
Lemma wp_Doc__ObserveUpdate (dv ref : loc) (γs : store_names) (γh : history_names)
    (may_insert : go_string -> w16 -> Prop)
    (encode : list (TId * IntegrateInput (A := A)) -> list u8) (encoder callback : func.t) :
  {{{ is_pkg_init yjs ∗ is_Doc dv ref γs γh may_insert ∗ is_history (A := A) (P := P) γh ∗
      encoder_spec encode encoder ∗ is_update_callback may_insert γh encode callback }}}
    dv @! (go.PointerType yjs.Doc) @! "ObserveUpdate" #encoder #callback
  {{{ RET #(); True }}}.
Proof.
  wp_start as "(#His_doc & #Hishist & #Hencoder & #Hcallback)".
  iNamed "His_doc". subst ref may_insert. wp_auto.
  wp_apply (wp_Store__wlock with "[$His_store]"). iIntros "[Hlk Hinv]".
  iDestruct "Hinv" as (c h m) "Hstore".
  wp_auto.
  iDestruct "Hstore" as (state ds) "(Hstore & Hreplica_history)".
  iDestruct "Hstore" as "[Hcore Hobservers]".
  iDestruct "Hobservers" as (observers_mref) "(Hobserversf & Hregistry & Hupdate_observers)".
  iDestruct "Hupdate_observers" as (observers_slice observers) "(Hfield & Hslice & Hcap & #Hspecs)".
  wp_auto.
  wp_apply wp_slice_literal. iSplitR; first done. iIntros "%literal_slice [Hliteral _]". wp_auto.
  wp_apply (wp_slice_append with "[$Hslice $Hcap $Hliteral]").
  iIntros (appended_slice) "(Hslice & Hcap & _)". wp_auto.
  wp_apply (wp_Store__wunlock with "[$His_store $Hlk Hcore Hobserversf Hregistry Hfield Hslice Hcap $Hreplica_history]").
  { iFrame "Hcore". iExists observers_mref. iFrame "Hobserversf Hregistry".
    iExists appended_slice, _. iFrame "Hfield Hslice Hcap".
    rewrite big_sepL_snoc. iFrame "Hspecs". iExists encode. iFrame "Hishist Hencoder Hcallback". }
  iApply "HΦ". done.
Qed.

End doc_ObserveUpdate.
