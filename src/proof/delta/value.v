(** The text delta, VALUE layer: what the Go [DeltaOp] denotes. Go values,
    no Iris.

    Definitions
    - [delta_op_denotes v op]: the [DeltaOp] struct value [v] is the entry
      [op]: its kind byte, and its count as a machine word or its content.
      The count is the model's [nat] taken modulo [2^64] ([W64]), the way
      [yType.len] denotes [runs_visible]: a walk adds [uint64] counts, and
      nothing bounds a text below [2^64] chars; [delta_fits] is the bound
      under which the word is the count.

    Laws: none; [delta/heap]'s [own_delta] reads a slice through it. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core.
From New.proof.delta Require Import model.

Section delta_value.

Set Default Proof Using "Type*".

Notation A := go_string.

(* ===== definitions ======================================================== *)

(** The kind bytes of the Go [DeltaKind]: retain 0, insert 1, delete 2. *)
Definition delta_op_denotes (v : yjs.DeltaOp.t) (op : DeltaOp) : Prop :=
  match op with
  | Retain n => v.(yjs.DeltaOp.Kind') = W8 0 ∧ v.(yjs.DeltaOp.Length') = W64 (Z.of_nat n)
  | Insert t => v.(yjs.DeltaOp.Kind') = W8 1 ∧ v.(yjs.DeltaOp.Content') = t
  | Delete n => v.(yjs.DeltaOp.Kind') = W8 2 ∧ v.(yjs.DeltaOp.Length') = W64 (Z.of_nat n)
  end.

End delta_value.
