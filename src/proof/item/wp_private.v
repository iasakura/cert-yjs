(** Specs of the package's unexported helpers over [item]: [itemPtrEqual]
    (yjs/store.go), which compares two item pointers by identity, i.e. by model
    id, with the null cases of y-octo's [Somr] comparison.

    The exported methods have a file each ([item/Indexable.v], [item/Len.v],
    [item/Deleted.v]). *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core prelude.
From New.proof.id Require Import id.
From New.proof.item Require Import run_theory model value heap.

Section item_wp_private.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.


(* ===== lemmas ============================================================= *)

(* ===== per-method WP specs for individual items ======================== *)

(* The node / GC / Skip enum is codec-only now (refs.go is //go:build !goose), so
   its projections are no longer part of the verified model. *)

(** [itemPtrEqual] compares two item pointers by identity (= model id, ids being
    unique), with the null cases of y-octo's [Somr] comparison. *)
Lemma wp_itemPtrEqual (pa pb : loc) (ova ovb : option yjs.item.t) (dqa dqb : dfrac) :
  {{{ is_pkg_init yjs ∗ item_or_null pa ova dqa ∗ item_or_null pb ovb dqb }}}
    @! yjs.itemPtrEqual #pa #pb
  {{{ RET #(bool_decide (originId_of ova = originId_of ovb));
      item_or_null pa ova dqa ∗ item_or_null pb ovb dqb }}}.
Proof.
  wp_start as "[Ha Hb]". wp_auto.
  destruct ova as [va|]; destruct ovb as [vb|].
  - iDestruct "Ha" as "[%Hpa Hpa]". iDestruct "Hb" as "[%Hpb Hpb]".
    rewrite (bool_decide_eq_false_2 (pa = null) Hpa). wp_auto.
    rewrite (bool_decide_eq_false_2 (pa = null) Hpa). wp_auto.
    rewrite (bool_decide_eq_false_2 (pb = null) Hpb). wp_auto.
    wp_method_call; wp_call; wp_auto.
    wp_apply (wp_Id__Equal va.(yjs.item.id') vb.(yjs.item.id')).
    have Heq : bool_decide (originId_of (Some va) = originId_of (Some vb))
             = bool_decide (toYjsId va.(yjs.item.id') = toYjsId vb.(yjs.item.id')).
    { apply bool_decide_ext. rewrite /originId_of /=. by split; congruence. }
    iEval (rewrite Heq) in "HΦ". iApply "HΦ". rewrite /item_or_null. iFrame.
    iSplit; iPureIntro; assumption.
  - iDestruct "Ha" as "[%Hpa Hpa]". iDestruct "Hb" as "%Hpb". subst pb.
    rewrite (bool_decide_eq_false_2 (pa = null) Hpa). wp_auto.
    rewrite (bool_decide_eq_false_2 (pa = null) Hpa). wp_auto.
    iApply "HΦ". rewrite /item_or_null. iFrame.
    iSplit; iPureIntro; [assumption | reflexivity].
  - iDestruct "Ha" as "%Hpa". iDestruct "Hb" as "[%Hpb Hpb]". subst pa.
    wp_auto. rewrite (bool_decide_eq_false_2 (pb = null) Hpb). wp_auto.
    iApply "HΦ". rewrite /item_or_null. iFrame.
    iSplit; iPureIntro; [reflexivity | assumption].
  - iDestruct "Ha" as "%Hpa". iDestruct "Hb" as "%Hpb". subst pa pb.
    wp_auto. iApply "HΦ". rewrite /item_or_null. iSplit; iPureIntro; reflexivity.
Qed.

End item_wp_private.
