(** The text delta, VALUE layer: what the Go [DeltaOp] denotes, as far as a
    pure value can say it. Go values, no Iris.

    Definitions
    - [delta_op_kind v op]: the [DeltaOp] struct value [v] has the kind byte
      of the entry [op], and, for a retain or a delete, its count as a
      machine word. The count is the model's [nat] taken modulo [2^64]
      ([W64]), the way [yType.len] denotes [runs_visible]: a walk adds
      [uint64] counts, and nothing bounds a text below [2^64] code units;
      [delta_fits] is the bound under which the word is the count. An
      insert's content is a slice, so it is not a value-layer fact:
      [delta/heap]'s [is_delta_op] adds its read-only ownership on top of
      this.

    Laws: none; [delta/heap]'s [own_delta] reads a slice through it. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core.
From New.proof.delta Require Import model.

Section delta_value.

Set Default Proof Using "Type*".

Notation A := (list w16).

(* ===== definitions ======================================================== *)

(** The kind bytes of the Go [DeltaKind]: retain 0, insert 1, delete 2. *)
Definition delta_op_kind (v : yjs.DeltaOp.t) (op : DeltaOp) : Prop :=
  match op with
  | Retain n => v.(yjs.DeltaOp.Kind') = W8 0 ∧ v.(yjs.DeltaOp.Length') = W64 (Z.of_nat n)
  | Insert _ => v.(yjs.DeltaOp.Kind') = W8 1
  | Delete n => v.(yjs.DeltaOp.Kind') = W8 2 ∧ v.(yjs.DeltaOp.Length') = W64 (Z.of_nat n)
  end.

End delta_value.
