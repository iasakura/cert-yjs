(** Text handle: the top-level [wp_Text__Insert], one write as one
    transaction ([store.transact] around [Text.InsertIn], issue #206 T1).
    The per-code-unit Integrate loop is [text/InsertIn]; this file only wraps it
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

(** What one [InsertIn] inserted is the code units it was given: an item of
    the end model whose id is one of the run's is the run's item of that
    id (ids are unique in the model), which carries one of the units. *)
#[local] Lemma inserted_run_units_allowed (allowed : w16 -> Prop) (m' : DocModel) (name : P)
    (L L' ins : list (YjsItem A)) (units : A) (client k0 : nat)
    (originLeft originRight : YjsPtr A) :
  inserted_run L L' ins units client k0 originLeft originRight ->
  doc_model_get m' (RootId name) = L' ->
  (∀ (name1 name2 : P) (item1 item2 : YjsItem A),
     item1 ∈ doc_model_get m' (RootId name1) -> item2 ∈ doc_model_get m' (RootId name2) ->
     item_id item1 = item_id item2 -> name1 = name2 ∧ item1 = item2) ->
  Forall allowed units ->
  inserted_units_allowed allowed m' (∅ ∪ char_ids ins).
Proof.
  move=> [_ [Hlength Hitems]] Hmodel Hunique Hunits root item [Hitem Hid].
  rewrite left_id_L in Hid.
  apply elem_of_char_ids in Hid as (inserted_item & Hinserted & Hsame).
  apply list_elem_of_lookup in Hinserted as [i Hi].
  destruct Hlength as [Hnil | Hlength]; first by rewrite Hnil in Hi.
  have [unit Hunit] : is_Some (units !! i).
  { apply lookup_lt_is_Some. rewrite -Hlength. exact (lookup_lt_Some _ _ _ Hi). }
  destruct (Hitems i inserted_item unit Hi Hunit) as (Hin & _ & Hcontent & _).
  rewrite -Hmodel in Hin.
  destruct (Hunique root name item inserted_item Hitem Hin (eq_sym Hsame)) as [_ ->].
  rewrite Hcontent. apply Forall_singleton.
  exact (proj1 (Forall_forall _ _) Hunits unit (list_elem_of_lookup_2 _ _ _ Hunit)).
Qed.

Lemma wp_Text__Insert (t : loc) (idx : w64) (cs : slice.t) (dq : dfrac) (units : A)
    (γs : store_names) (γh : history_names)
    (may_insert : go_string -> w16 -> Prop)
    (name : P) (L : list (YjsItem A)) (deleted_ids : gset YjsId) :
  {{{ is_pkg_init yjs ∗ is_Text t γs γh may_insert name L deleted_ids ∗ cs ↦*{dq} units ∗
      ⌜Forall (may_insert ""%go) units⌝ }}}
    t @! (go.PointerType yjs.Text) @! "Insert" #idx #cs
  {{{ (L' ins : list (YjsItem A)) (client k0 : nat) (originLeft originRight : YjsPtr A), RET #();
      is_Text t γs γh may_insert name L' deleted_ids ∗ cs ↦*{dq} units ∗
      ⌜inserted_run L L' ins units client k0 originLeft originRight⌝ ∗
      (* the op certificates: one broadcast fragment per inserted item
         (issues #42/#49; the doc-level op an item denotes is
         [(RootId name, OpInsert (input_of_item it))]) *)
      ([∗ list] it ∈ ins,
         is_op_cert γh (RootId name, OpInsert (input_of_item it))) }}}.
Proof.
  wp_start as "(#Htext & Hcs & %Hunits)".
  iPoseProof "Htext" as (tv text_store parent deleted_items) "Hhandle". iNamed "Hhandle".
  subst text_store.
  wp_auto.
  (* the one write, as one transaction: the closure runs [InsertIn] on the
     transaction it is handed and reports what the handle learns *)
  wp_apply (wp_transact tv.(yjs.Text.store') γs γh ""%go _
              (λ c h' m' pend' deleted',
                 ∃ (L' ins : list (YjsItem A)) (k0 : nat) (originLeft originRight : YjsPtr A),
                   is_Text t γs γh may_insert name L' deleted_ids ∗ cs ↦*{dq} units ∗
                   ⌜inserted_run L L' ins units c k0 originLeft originRight⌝ ∗
                   [∗ list] it ∈ ins, is_op_cert γh (RootId name, OpInsert (input_of_item it)))%I
              with "[$His_store t index content Hcs]").
  { rewrite /closure_runs_transaction.
    iIntros (tr c h m pend deleted Ψ) "Htx HΨ".
    wp_auto.
    wp_apply (wp_Text__InsertIn with "[$Htext $Htx $Hcs]").
    iIntros (L' ins h' m' k0 originLeft originRight) "(#Htext' & Htx & Hcs & %Hrun & %Hrepl & Hcerts)".
    iDestruct (own_transaction_item_unique with "Htx") as %Hunique.
    wp_auto.
    iApply ("HΨ" $! h' m' pend deleted (∅ ∪ char_ids ins) ∅
              (∅ ∪ (if decide (ins = []) then ∅ else {[name]}))).
    iFrame "Htx".
    iSplitR.
    { (* what the transaction inserted is the caller's code units *)
      iPureIntro. rewrite Hmay_insert.
      exact (inserted_run_units_allowed _ m' name L L' ins units c k0 originLeft originRight
               Hrun (proj1 Hrepl) Hunique Hunits). }
    iExists L', ins, k0, originLeft, originRight. iFrame "Htext' Hcerts Hcs". iPureIntro. exact Hrun. }
  iIntros "HQ". iDestruct "HQ" as (c h' m' pend' deleted') "HQ".
  iDestruct "HQ" as (L' ins k0 originLeft originRight) "(#Htext' & Hcs & %Hrun & Hcerts)".
  wp_auto.
  iApply ("HΦ" $! L' ins c k0 originLeft originRight).
  iFrame "Htext' Hcerts Hcs". iPureIntro. exact Hrun.
Qed.

End text.
