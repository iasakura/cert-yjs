(** Text handle: the top-level [wp_Text__Insert], one write as one
    transaction ([store.transact] around [Text.InsertIn], issue #206 T1).
    The per-byte Integrate loop is [text/InsertIn]; this file only wraps it
    and hides the transaction. Shares [is_Text] etc. via [text/heap]. *)
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
From New.proof.text Require Import heap InsertIn.

(* iris.algebra / stdpp.sorting push [nat_scope], retuning the default [<] / [≤];
   the verified word-arithmetic proofs write [Z] comparisons unannotated, so
   restore [Z_scope] as the default. *)
Local Open Scope Z_scope.

Section text.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.
(** The store's write lock is taken by the transaction ([wp_store__transact]);
    the per-text item set lives in a grow-only auth (the same RA as
    [store/store], used by [is_type_lb]). *)
Context {sync_pkg : sync.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.
Context {seq_inG : inG Σ (authR (gmapUR loc (gsetUR (YjsItem A))))}.
Context {acc_inG : inG Σ (authR (gsetUR YjsId))}.
(* [is_Store]'s reader-count accounting ties the readers' share to the store's
   [types] map via a [dfrac_agree]; threaded here so [is_Text]/[is_Store] uses
   in this file (Insert/Delete/Len) can discharge the instance. *)
Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO addressed_pool))}.

(* The ghost op-history types at the document content type; type names are Go
   strings (issue #49). *)
Local Notation P := go_string.
Local Notation TId := (TypeId P).
Local Notation Op := (TId * @YjsOperation A)%type.
Local Notation Ev := (@Event Op).
Local Notation DocModel := (gmap TId (list (YjsItem A))).

Lemma wp_Text__Insert (t : loc) (idx : w64) (cs : go_string) (γs : store_names) (γh : history_names)
    (name : P) (L : list (YjsItem A)) (deleted_ids : gset YjsId) :
  {{{ is_pkg_init yjs ∗ is_Text t γs γh name L deleted_ids }}}
    t @! (go.PointerType yjs.Text) @! "Insert" #idx #cs
  {{{ (L' ins : list (YjsItem A)) (client k0 : nat) (originLeft originRight : YjsPtr A), RET #();
      is_Text t γs γh name L' deleted_ids ∗
      ⌜inserted_run L L' ins cs client k0 originLeft originRight⌝ ∗
      (* the op certificates: one broadcast fragment per inserted item
         (issues #42/#49; the doc-level op an item denotes is
         [(RootId name, OpInsert (input_of_item it))]) *)
      ([∗ list] it ∈ ins,
         is_op_cert γh (RootId name, OpInsert (input_of_item it))) }}}.
Proof.
  wp_start as "#Htext".
  iPoseProof "Htext" as (tv text_store parent deleted_items) "Hhandle". iNamed "Hhandle".
  subst text_store.
  wp_auto.
  (* the one write, as one transaction: the closure runs [InsertIn] on the
     transaction it is handed and reports what the handle learns *)
  wp_apply (wp_store__transact tv.(yjs.Text.store') γs γh _
              (λ c h' m' pend' deleted',
                 ∃ (L' ins : list (YjsItem A)) (k0 : nat) (originLeft originRight : YjsPtr A),
                   is_Text t γs γh name L' deleted_ids ∗
                   ⌜inserted_run L L' ins cs c k0 originLeft originRight⌝ ∗
                   [∗ list] it ∈ ins, is_op_cert γh (RootId name, OpInsert (input_of_item it)))%I
              with "[$His_store t index content]").
  { rewrite /closure_runs_transaction.
    iIntros (tr c h m pend deleted Ψ) "Htx HΨ".
    wp_auto.
    wp_apply (wp_Text__InsertIn with "[$Htext $Htx]").
    iIntros (L' ins h' m' k0 originLeft originRight) "(#Htext' & Htx & %Hrun & %Hrepl & Hcerts)".
    wp_auto.
    iApply ("HΨ" $! h' m' pend deleted (∅ ∪ char_ids ins) ∅
              (∅ ∪ (if decide (ins = []) then ∅ else {[name]}))).
    iFrame "Htx".
    iExists L', ins, k0, originLeft, originRight. iFrame "Htext' Hcerts". iPureIntro. exact Hrun. }
  iIntros "HQ". iDestruct "HQ" as (c h' m' pend' deleted') "HQ".
  iDestruct "HQ" as (L' ins k0 originLeft originRight) "(#Htext' & %Hrun & Hcerts)".
  wp_auto.
  iApply ("HΦ" $! L' ins c k0 originLeft originRight).
  iFrame "Htext' Hcerts". iPureIntro. exact Hrun.
Qed.

End text.
