(** [wp_Doc__TransactEncoded] (issue #131): one transaction whose update is
    handed back as bytes. The closure edits as it likes; what the caller
    gets is the encoding of a batch that is, character by character, exactly
    what the transaction recorded as inserted, and that batch is well formed
    and certified in the global history. Nothing is asked of the closure
    for that: the certificates of whatever a transaction integrated are in
    the history already ([own_transaction_model_certified]), and the
    store's items fit machine words. A sender adds only what it knows about
    the content (that it holds no surrogate code unit) to own the wire
    protocol for the bytes ([yjs_prot_encode]). *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core.
From New.proof Require Import prelude.
From New.proof Require Import history.
From New.proof Require Import yjs_prot.
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

Section doc_TransactEncoded.

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


(* ===== lemmas ============================================================= *)

Lemma wp_Doc__TransactEncoded (dv ref : loc) (γs : store_names) (γh : history_names)
    (f : func.t) (encode : list (TId * IntegrateInput (A := A)) -> list u8) (encoder : func.t)
    (Q : ClientId -> list Ev -> DocModel -> list (TId * IntegrateInput (A := A)) ->
         gset YjsId -> gset YjsId -> iProp Σ) :
  {{{ is_pkg_init yjs ∗ is_Doc dv ref γs γh ∗ is_history (A := A) (P := P) γh ∗
      encoder_spec encode encoder ∗
      closure_runs_recorded_transaction γs γh f Q }}}
    dv @! (go.PointerType yjs.Doc) @! "TransactEncoded" #f #encoder
  {{{ (bytes_slice : slice.t) (c : ClientId) (h' : list Ev) (m' : DocModel)
      (pend' : list (TId * IntegrateInput (A := A))) (deleted' inserted : gset YjsId)
      (structs : list (TId * IntegrateInput (A := A))), RET #bytes_slice;
      Q c h' m' pend' deleted' inserted ∗
      bytes_slice ↦* encode structs ∗ own_slice_cap w8 bytes_slice (DfracOwn 1) ∗
      ⌜structs_expand_to_items structs (λ name item,
         item ∈ doc_model_get m' (RootId name) ∧ item_id item ∈ inserted)⌝ ∗
      is_update_certified γh structs }}}.
Proof.
  wp_start as "(#His_doc & #Hishist & #Hencoder & Hf)".
  iNamed "His_doc". subst ref.
  wp_auto.
  wp_apply (wp_transact _ γs γh _
              (λ c h' m' pend' deleted',
                 ∃ (inserted : gset YjsId) (structs_slice : slice.t)
                   (structs : list (TId * IntegrateInput (A := A))),
                   Q c h' m' pend' deleted' inserted ∗
                   structs_ptr ↦ structs_slice ∗
                   own_update_structs structs_slice (DfracOwn 1) structs ∗
                   ⌜structs_expand_to_items structs (λ name item,
                      item ∈ doc_model_get m' (RootId name) ∧ item_id item ∈ inserted)⌝ ∗
                   is_update_certified γh structs)%I
              with "[$His_store f structs Hf]").
  { rewrite /closure_runs_transaction.
    iIntros (tr c h m pend deleted Ψ) "Htx HΨ".
    wp_auto.
    wp_apply ("Hf" with "Htx").
    iIntros (h' m' pend' deleted' inserted tombstoned changed) "[Htx HQ]".
    wp_auto.
    wp_apply (wp_Transaction__insertedStructs with "[$Htx]").
    iIntros (structs_slice structs) "(Htx & Hstructs & %Hstructs)".
    iDestruct (own_transaction_item_clock_fits with "Htx") as %Hfits.
    iMod (own_transaction_model_certified _ _ _ _ _ _ _ _ _ _ _ _ ⊤ with "Hishist Htx")
      as "[Htx #Hcerts]"; first done.
    wp_auto.
    iApply ("HΨ" $! h' m' pend' deleted' inserted tombstoned changed).
    iFrame "Htx".
    iExists inserted, structs_slice, structs.
    iFrame "HQ structs Hstructs". iSplitR; first done.
    (* a character of the batch is an item of the model *)
    have Hchar : ∀ input, input ∈ expand_inputs structs ->
        ∃ (name : P) (item : YjsItem A),
          item ∈ doc_model_get m' (RootId name) ∧ input = (RootId name, input_of_item item).
    { move=> input Hinput.
      destruct (proj1 (Hstructs input) Hinput) as (name & item & [Hitem _] & ->).
      by exists name, item. }
    rewrite /is_update_certified.
    iSplitR.
    { iPureIntro. split.
      - move=> input Hinput.
        have Hone := expand_inputs_unit_content structs input Hinput.
        destruct (Hchar input Hinput) as (name & item & Hitem & ->).
        rewrite /input_fits Hone /=. exact (Hfits name item Hitem).
      - move=> input Hinput.
        destruct (Hchar input Hinput) as (name & item & _ & ->).
        rewrite /pending_item_rooted. case_decide; last done. by exists name. }
    rewrite /is_pending_certified. iApply big_sepL_forall. iIntros (k input Hk).
    destruct (Hchar input (list_elem_of_lookup_2 _ _ _ Hk)) as (name & item & Hitem & ->).
    iApply ("Hcerts" $! (RootId name) item Hitem). }
  iIntros "HQ". iDestruct "HQ" as (c h' m' pend' deleted') "HQ".
  iDestruct "HQ" as (inserted structs_slice structs)
    "(HQ & structs & Hstructs & %Hstructs & #Hcertified)".
  wp_auto.
  wp_apply ("Hencoder" with "[$Hstructs]").
  iIntros (bytes_slice) "(Hstructs & Hbytes & Hbytes_cap)".
  wp_auto.
  iApply ("HΦ" $! bytes_slice c h' m' pend' deleted' inserted structs).
  iFrame "HQ Hbytes Hbytes_cap Hcertified". done.
Qed.

End doc_TransactEncoded.
