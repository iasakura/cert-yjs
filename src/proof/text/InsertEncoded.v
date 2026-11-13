(** Text handle: [wp_Text__InsertEncoded] (issue #131), one local insert as
    one transaction that also reads back the structs it integrated
    ([Transaction.insertedStructs]) and returns their encoding. The insert
    is [text/InsertIn]'s; what this file adds is the meaning of the bytes:
    they are the encoder's output for a batch that is, character by
    character, the inserted items under the text's root. *)
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
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
From New.proof.sync_proof Require Import mutex.
From iris.algebra Require Import auth gmap gset.
From iris.algebra.lib Require Import dfrac_agree.
From stdpp Require Import sorting.
From New.proof Require Import yjs_prot.
From New.proof.text Require Import heap InsertIn.

(* iris.algebra / stdpp.sorting push [nat_scope], retuning the default [<] / [≤];
   the verified word-arithmetic proofs write [Z] comparisons unannotated, so
   restore [Z_scope] as the default. *)
Local Open Scope Z_scope.

Section text.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.
(** The store's write lock is taken by the transaction ([wp_transact]);
    the per-text item set lives in a grow-only auth (the same RA as
    [store/store], used by [is_type_lb]). *)
Context {sync_pkg : sync.Assumptions}.

Set Default Proof Using "Type*".

Notation A := (list w16).
Context {seq_inG : inG Σ (authR (gmapUR loc (gsetUR (YjsItem A))))}.
Context {acc_inG : inG Σ (authR (gsetUR YjsId))}.
(* [is_store_ref]'s reader-count accounting ties the readers' share to the store's
   [types] map via a [dfrac_agree]; threaded here so [is_Text]/[is_store_ref] uses
   in this file (Insert/Delete/Len) can discharge the instance. *)
Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO store_state))}.
(* the observers' tokens and registrations (issue #198 Part II), as [store/heap] *)
Context {observed_inG : ghost_varG Σ (list (YjsItem A * bool))}.
Context {observers_inG : inG Σ (authR (gsetUR (gname * go_string)))}.
Context {observers_agree_inG : inG Σ (dfrac_agreeR (leibnizO registered_entries))}.

(* The ghost op-history types at the document content type; type names are Go
   strings (issue #49). *)
Local Notation P := go_string.
Local Notation TId := (TypeId P).
Local Notation Op := (TId * @YjsOperation A)%type.
Local Notation Ev := (@Event Op).
Local Notation DocModel := (gmap TId (list (YjsItem A))).

(* ===== lemmas ============================================================= *)

Lemma wp_Text__InsertEncoded (t : loc) (idx : w64) (cs : slice.t) (dq : dfrac) (units : A)
    (γs : store_names) (γh : history_names)
    (name : P) (L : list (YjsItem A)) (deleted_ids : gset YjsId)
    (encode : list (TId * IntegrateInput (A := A)) -> list u8) (encoder : func.t) :
  {{{ is_pkg_init yjs ∗ is_Text t γs γh name L deleted_ids ∗ cs ↦*{dq} units ∗
      encoder_spec encode encoder }}}
    t @! (go.PointerType yjs.Text) @! "InsertEncoded" #idx #cs #encoder
  {{{ (bytes_slice : slice.t) (L' ins : list (YjsItem A)) (client k0 : nat)
      (originLeft originRight : YjsPtr A) (structs : list (TId * IntegrateInput (A := A))),
      RET #bytes_slice;
      is_Text t γs γh name L' deleted_ids ∗ cs ↦*{dq} units ∗
      ⌜inserted_run L L' ins units client k0 originLeft originRight⌝ ∗
      ([∗ list] it ∈ ins, is_op_cert γh (RootId name, OpInsert (input_of_item it))) ∗
      bytes_slice ↦* encode structs ∗ own_slice_cap w8 bytes_slice (DfracOwn 1) ∗
      ⌜structs_expand_to_items structs (λ root item, root = name ∧ item ∈ ins)⌝ }}}.
Proof.
  wp_start as "(#Htext & Hcs & #Hencoder)".
  iPoseProof "Htext" as (tv text_store parent deleted_items) "Hhandle". iNamed "Hhandle".
  subst text_store.
  wp_auto.
  wp_apply (wp_transact tv.(yjs.Text.store') γs γh _
              (λ c h' m' pend' deleted',
                 ∃ (L' ins : list (YjsItem A)) (k0 : nat) (originLeft originRight : YjsPtr A)
                   (structs_slice : slice.t) (structs : list (TId * IntegrateInput (A := A))),
                   is_Text t γs γh name L' deleted_ids ∗ cs ↦*{dq} units ∗
                   ⌜inserted_run L L' ins units c k0 originLeft originRight⌝ ∗
                   ([∗ list] it ∈ ins, is_op_cert γh (RootId name, OpInsert (input_of_item it))) ∗
                   structs_ptr ↦ structs_slice ∗
                   own_update_structs structs_slice (DfracOwn 1) structs ∗
                   ⌜structs_expand_to_items structs (λ root item, root = name ∧ item ∈ ins)⌝)%I
              with "[$His_store t index content structs Hcs]").
  { rewrite /closure_runs_transaction.
    iIntros (tr c h m pend deleted Ψ) "Htx HΨ".
    wp_auto.
    wp_apply (wp_Text__InsertIn with "[$Htext $Htx $Hcs]").
    iIntros (L' ins h' m' k0 originLeft originRight) "(#Htext' & Htx & Hcs & %Hrun & %Hreplaced & Hcerts)".
    wp_auto.
    wp_apply (wp_Transaction__insertedStructs with "[$Htx]").
    iIntros (structs_slice structs) "(Htx & Hstructs & %Hstructs)".
    iDestruct (own_transaction_item_unique with "Htx") as %Hunique.
    wp_auto.
    iApply ("HΨ" $! h' m' pend deleted (∅ ∪ char_ids ins) ∅
              (∅ ∪ (if decide (ins = []) then ∅ else {[name]}))).
    iFrame "Htx".
    iExists L', ins, k0, originLeft, originRight, structs_slice, structs.
    iFrame "Htext' Hcerts Hcs structs Hstructs". iPureIntro. split; first exact Hrun.
    (* a struct's character has an inserted id, so it is the inserted item *)
    move=> op Hop.
    destruct (Hstructs op Hop) as (op_name & op_item & [Hop_item Hop_id] & ->).
    rewrite left_id_L in Hop_id. apply elem_of_char_ids in Hop_id as (it & Hit & Hit_id).
    have Hit_model : it ∈ doc_model_get m' (RootId name).
    { rewrite (proj1 Hreplaced).
      destruct Hrun as (_ & Hlength & Hitems).
      apply list_elem_of_lookup in Hit as [position Hposition].
      destruct Hlength as [-> | Hlength]; first by rewrite lookup_nil in Hposition.
      have [unit Hunit] : is_Some (units !! position).
      { apply lookup_lt_is_Some. rewrite -Hlength. exact (lookup_lt_Some _ _ _ Hposition). }
      exact (proj1 (Hitems position it unit Hposition Hunit)). }
    destruct (Hunique name op_name it op_item Hit_model Hop_item Hit_id) as [<- <-].
    exists name, it. split; [split; [reflexivity | exact Hit] | reflexivity]. }
  iIntros "HQ". iDestruct "HQ" as (c h' m' pend' deleted') "HQ".
  iDestruct "HQ" as (L' ins k0 originLeft originRight structs_slice structs)
    "(#Htext' & Hcs & %Hrun & Hcerts & structs & Hstructs & %Hstructs)".
  wp_auto.
  wp_apply ("Hencoder" with "[$Hstructs]").
  iIntros (bytes_slice) "(Hstructs & Hbytes & Hbytes_cap)".
  wp_auto.
  iApply ("HΦ" $! bytes_slice L' ins c k0 originLeft originRight structs).
  iFrame "Htext' Hcerts Hcs Hbytes Hbytes_cap". iPureIntro. split; [exact Hrun | exact Hstructs].
Qed.

End text.
