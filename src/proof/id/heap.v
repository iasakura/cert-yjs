(** The [id] type, Iris layer.

    Definitions
    - [is_origin_id p oid]: an origin pointer is either null (no origin) or a
      read-only [Id] cell. Origins are immutable once integrated, so the
      predicate is persistent.

    The WP specs of the [Id] methods are [id/wp_private.v]. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core.
From New.proof Require Import prelude.
From New.proof.id Require Import value.

Section id_heap.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

(* ===== definitions ======================================================== *)

(** An origin pointer is either null (no origin) or a read-only [Id] cell.
    Origins are immutable once integrated, hence persistent ([↦□]). *)
Definition is_origin_id (p : loc) (originId : option yjs.id.t) : iProp Σ :=
  match originId with
  | None => ⌜p = null⌝
  | Some idv => ⌜p ≠ null⌝ ∗ p ↦□ idv
  end.

(** Origins are read-only, hence the predicate is persistent. *)
Global Instance is_origin_id_persistent p originId : Persistent (is_origin_id p originId).
Proof. rewrite /is_origin_id. by destruct originId; apply _. Qed.

End id_heap.
