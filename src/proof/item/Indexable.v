(** [item.Indexable]: a node counts towards the visible index exactly when it
    is Countable and not Deleted. Read-only, so stated at a generic [dfrac].
    This is what [yType.findPos]'s walk tests at each cursor node. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core prelude.
From New.proof.id Require Import id.
From New.proof.item Require Import run_theory model value heap.

Section item_Indexable.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.



(** Per-node method specs [findPos] reads off each cursor node. Every cell is
    Countable ([is_countable_flag]) with single-byte content, so [Indexable] is
    "not Deleted" and [Len] is the content byte length (1 for our cells). Proving
    these once keeps the [findPos] loop free of nested method-call stepping.
    Read-only, hence stated at a generic [dq]. *)
Lemma wp_item__Indexable (l : loc) (dq : dfrac) (v : yjs.item.t) :
  is_countable_flag v = true ->
  {{{ is_pkg_init yjs ∗ l ↦{dq} v }}}
    l @! (go.PointerType yjs.item) @! "Indexable" #()
  {{{ RET #(negb (is_deleted_flag v)); l ↦{dq} v }}}.
Proof.
  intros Hcount.
  rewrite /is_countable_flag in Hcount. apply negb_true_iff in Hcount.
  wp_start as "Hl".
  wp_auto.
  wp_method_call. wp_call. rewrite /yjs.item__Indexableⁱᵐᵖˡ. wp_auto.
  wp_method_call. wp_call. wp_auto.
  wp_method_call. wp_call. rewrite /yjs.item__Countableⁱᵐᵖˡ. wp_auto.
  wp_alloc i2 as "Hi2". wp_auto.
  rewrite Hcount. simpl negb. wp_auto.
  wp_method_call. wp_call. rewrite /yjs.item__Deletedⁱᵐᵖˡ. wp_auto.
  wp_method_call. wp_call. rewrite /yjs.item__Deletedⁱᵐᵖˡ. wp_auto.
  rewrite -/(is_deleted_flag v). iApply "HΦ". iFrame "Hl".
Qed.

(** [item.Indexable] over the node predicate: "not tombstoned". The
    [is_countable_flag] premise disappears: the node predicate pins the flag
    byte, and every cert-yjs item is Countable
    (docs/plan-item-run-split.md stage 3). *)
Lemma wp_item__Indexable_node (l : loc) (dq : dfrac) (input : IntegrateInput (A := A))
    (d : bool) (parent prev nxt : loc) :
  {{{ is_pkg_init yjs ∗ own_item_node l dq input d parent prev nxt }}}
    l @! (go.PointerType yjs.item) @! "Indexable" #()
  {{{ RET #(negb d); own_item_node l dq input d parent prev nxt }}}.
Proof.
  iIntros (Φ) "(#Hpkg & Hnode) HΦ".
  iDestruct "Hnode" as (v olid orid) "H". iNamed "H".
  have Hcnt : is_countable_flag v = true.
  { rewrite /is_countable_flag Hflags. destruct d; vm_compute; reflexivity. }
  have Hd : is_deleted_flag v = d.
  { rewrite /is_deleted_flag Hflags. destruct d; vm_compute; reflexivity. }
  wp_apply (wp_item__Indexable l dq v Hcnt with "[$Hpkg $Hval]").
  iIntros "Hval".
  rewrite Hd.
  iApply "HΦ". iExists v, olid, orid. iFrame "Hval Holeft Horight".
  iPureIntro. split_and!; assumption.
Qed.

End item_Indexable.
