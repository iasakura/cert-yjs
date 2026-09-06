(** [item.Len]: a node's length is its content's byte length. Read-only, so
    stated at a generic [dfrac]. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core prelude.
From New.proof.id Require Import id.
From New.proof.item Require Import run_theory model value heap.

Section item_Len.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.



Lemma wp_item__Len (l : loc) (dq : dfrac) (v : yjs.item.t) :
  {{{ is_pkg_init yjs ∗ l ↦{dq} v }}}
    l @! (go.PointerType yjs.item) @! "Len" #()
  {{{ RET #(W64 (length (v.(yjs.item.content').(yjs.content.content')))); l ↦{dq} v }}}.
Proof.
  wp_start as "Hl". wp_auto.
  wp_method_call. wp_call. rewrite /yjs.item__Lenⁱᵐᵖˡ. wp_auto.
  wp_method_call. wp_call. rewrite /yjs.content__Lenⁱᵐᵖˡ. wp_auto.
  wp_method_call. wp_call. rewrite /yjs.content__Lenⁱᵐᵖˡ. wp_auto.
  wp_apply strings.wp_string_len. iIntros "_". wp_auto.
  iApply "HΦ". iFrame "Hl".
Qed.

(** [item.Len] over the node predicate: the byte length of the wire item's
    content. *)
Lemma wp_item__Len_node (l : loc) (dq : dfrac) (input : IntegrateInput (A := A))
    (d : bool) (parent prev nxt : loc) :
  {{{ is_pkg_init yjs ∗ own_item_node l dq input d parent prev nxt }}}
    l @! (go.PointerType yjs.item) @! "Len" #()
  {{{ RET #(W64 (length (in_content input)));
      own_item_node l dq input d parent prev nxt }}}.
Proof.
  iIntros (Φ) "(#Hpkg & Hnode) HΦ".
  iDestruct "Hnode" as (v olid orid) "H". iNamed "H".
  have Hcontent' : v.(yjs.item.content').(yjs.content.content') = in_content input
    := Hcontent.
  wp_apply (wp_item__Len l dq v with "[$Hpkg $Hval]").
  iIntros "Hval".
  rewrite Hcontent'.
  iApply "HΦ". iExists v, olid, orid. iFrame "Hval Holeft Horight".
  iPureIntro. split_and!; assumption.
Qed.

End item_Len.
