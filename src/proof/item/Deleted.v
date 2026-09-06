(** [item.Deleted]: a node's tombstone bit, read exactly as
    [is_deleted_flag] computes it ([flags & 0x04 ≠ 0]). Read-only, so stated at
    a generic [dfrac]. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core prelude.
From New.proof.id Require Import id.
From New.proof.item Require Import run_theory model value heap.

Section item_Deleted.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.



Lemma wp_item__Deleted (l : loc) (dq : dfrac) (v : yjs.item.t) :
  {{{ is_pkg_init yjs ∗ l ↦{dq} v }}}
    l @! (go.PointerType yjs.item) @! "Deleted" #()
  {{{ RET #(is_deleted_flag v); l ↦{dq} v }}}.
Proof.
  wp_start as "Hl". wp_auto.
  wp_method_call. wp_call. rewrite /yjs.item__Deletedⁱᵐᵖˡ. wp_auto.
  iApply "HΦ". iFrame "Hl".
Qed.

(** [item.Deleted] over the node predicate: the tombstone bit. *)
Lemma wp_item__Deleted_node (l : loc) (dq : dfrac) (input : IntegrateInput (A := A))
    (d : bool) (parent prev nxt : loc) :
  {{{ is_pkg_init yjs ∗ own_item_node l dq input d parent prev nxt }}}
    l @! (go.PointerType yjs.item) @! "Deleted" #()
  {{{ RET #d; own_item_node l dq input d parent prev nxt }}}.
Proof.
  iIntros (Φ) "(#Hpkg & Hnode) HΦ".
  iDestruct "Hnode" as (v olid orid) "H". iNamed "H".
  have Hd : is_deleted_flag v = d.
  { rewrite /is_deleted_flag Hflags. destruct d; vm_compute; reflexivity. }
  wp_apply (wp_item__Deleted l dq v with "[$Hpkg $Hval]").
  iIntros "Hval".
  rewrite Hd.
  iApply "HΦ". iExists v, olid, orid. iFrame "Hval Holeft Horight".
  iPureIntro. split_and!; assumption.
Qed.

End item_Deleted.
