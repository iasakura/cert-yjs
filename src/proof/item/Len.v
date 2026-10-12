(** [item.Len]: a node's length is the number of code units of its content.
    Read-only, so stated at a generic [dfrac]; the content is read through
    the persistent [is_content], which the caller keeps. The length fits a Go
    [int] (the slice's [len] reports so); the postcondition passes that on for
    callers that index the content by a [uint64] offset ([Poll]). *)
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

Notation A := (list w16).



Lemma wp_item__Len (l : loc) (dq : dfrac) (v : yjs.item.t) (units : A) :
  {{{ is_pkg_init yjs ∗ l ↦{dq} v ∗ is_content v.(yjs.item.content') units }}}
    l @! (go.PointerType yjs.item) @! "Len" #()
  {{{ RET #(W64 (length units));
      l ↦{dq} v ∗ ⌜(Z.of_nat (length units) < 2^63)%Z⌝ }}}.
Proof.
  wp_start as "[Hl #Hcontent]". wp_auto.
  wp_method_call. wp_call. rewrite /yjs.item__Lenⁱᵐᵖˡ. wp_auto.
  wp_method_call. wp_call. rewrite /yjs.content__Lenⁱᵐᵖˡ. wp_auto.
  wp_method_call. wp_call. rewrite /yjs.content__Lenⁱᵐᵖˡ. wp_auto.
  iDestruct (own_slice_len with "Hcontent") as %[Hlen Hlen0].
  have Hbound : (Z.of_nat (length units) < 2^63)%Z by word.
  have -> : v.(yjs.item.content').(yjs.content.content').(slice.len) = W64 (length units) by word.
  iApply "HΦ". iFrame "Hl". iPureIntro. exact Hbound.
Qed.

(** [item.Len] over the node predicate: the length of the wire item's
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
  wp_apply (wp_item__Len l dq v (in_content input) with "[$Hpkg $Hval $Hcontent]").
  iIntros "[Hval _]".
  iApply "HΦ". iExists v, olid, orid. iFrame "Hval Holeft Horight Hcontent".
  iPureIntro. split_and!; assumption.
Qed.

End item_Len.
