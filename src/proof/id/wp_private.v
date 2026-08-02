(** Specs of the package's unexported helpers over [id]: [newId] (yjs/id.go)
    and [idOptEqual] (yjs/store.go), the null-tolerant id comparison the store's
    origin checks run on.

    The exported methods have a file each ([id/Add.v], [id/Sub.v],
    [id/Equal.v]). *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core.
From New.proof Require Import prelude.
From New.proof.id Require Import value heap.
From New.proof.id Require Import Equal.

Section id_wp_private.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".


(* ===== lemmas ============================================================= *)

(* ----- Id ----------------------------------------------------------------- *)

(* NewId builds the expected struct value. *)
Lemma wp_NewId (client clock : w64) :
  {{{ is_pkg_init yjs }}}
    @! yjs.newId #client #clock
  {{{ RET #(yjs.id.mk client clock); True }}}.
Proof.
  wp_start. wp_auto. iApply "HΦ". done.
Qed.


(** [idOptEqual] on two optional-id pointers ([is_origin_id]) decides equality of
    the abstract model ids. (Both origin facts are persistent, so kept.) *)
Lemma wp_idOptEqual (pa pb : loc) (oa ob : option yjs.id.t) :
  {{{ is_pkg_init yjs ∗ is_origin_id pa oa ∗ is_origin_id pb ob }}}
    @! yjs.idOptEqual #pa #pb
  {{{ RET #(bool_decide ((toYjsId <$> oa) = (toYjsId <$> ob))); True }}}.
Proof.
  wp_start as "[Ha Hb]". wp_auto.
  destruct oa as [ida|]; destruct ob as [idb|].
  - iDestruct "Ha" as "[%Hpa Hpa]". iDestruct "Hb" as "[%Hpb Hpb]".
    rewrite (bool_decide_eq_false_2 (pa = null) Hpa). wp_auto.
    rewrite (bool_decide_eq_false_2 (pa = null) Hpa). wp_auto.
    rewrite (bool_decide_eq_false_2 (pb = null) Hpb). wp_auto.
    wp_method_call; wp_call; wp_auto. wp_apply (wp_Id__Equal ida idb).
    have Heq : bool_decide (toYjsId <$> Some ida = toYjsId <$> Some idb)
             = bool_decide (toYjsId ida = toYjsId idb).
    { apply bool_decide_ext. simpl. by split; congruence. }
    iEval (rewrite Heq) in "HΦ". iApply "HΦ". done.
  - iDestruct "Ha" as "[%Hpa Hpa]". iDestruct "Hb" as "%Hpb". subst pb.
    rewrite (bool_decide_eq_false_2 (pa = null) Hpa). wp_auto.
    rewrite (bool_decide_eq_false_2 (pa = null) Hpa). wp_auto.
    iApply "HΦ". done.
  - iDestruct "Ha" as "%Hpa". iDestruct "Hb" as "[%Hpb Hpb]". subst pa.
    wp_auto. rewrite (bool_decide_eq_false_2 (pb = null) Hpb). wp_auto.
    iApply "HΦ". done.
  - iDestruct "Ha" as "%Hpa". iDestruct "Hb" as "%Hpb". subst pa pb.
    wp_auto. iApply "HΦ". done.
Qed.

End id_wp_private.
