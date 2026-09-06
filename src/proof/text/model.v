(** The [Text] handle, PURE model layer: what a reader's walk means.

    Definitions
    - [text_snapshot L model]: the walked list [model] is a valid document
      holding every item of the handle's model [L].
    - [history_reflected h0 name model]: every insert into the root [name]
      that the history prefix [h0] delivered has its item in [model].

    Laws: none; [Text.Len] / [Text.String] state their reads over these
    directly. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core network_model.
From New.proof.doc Require Import model.
From stdpp Require Import gmap.

Section text_model.

Notation A := go_string.

(* Type names are Go strings (issue #49). *)
Local Notation P := go_string.
Local Notation TId := (TypeId P).
Local Notation Op := (TId * @YjsOperation A)%type.
Local Notation Ev := (@Event Op).

(* ===== definitions ======================================================== *)

(** [text_snapshot L model]: the list a reader walked, with tombstones
    ([model]), is a valid document holding every item of the handle's model
    [L] (the handle's list is a lower bound of what the reader sees). *)
Definition text_snapshot (L : list (YjsItem A)) (model : list (YjsItem A * bool)) : Prop :=
  list_to_set L ⊆ (list_to_set model.*1 : gset (YjsItem A)) ∧
  YjsArrInvariant model.*1.

(** [history_reflected h0 name model]: every insert into the root [name] that
    the history prefix [h0] delivered has its item in the walked list. *)
Definition history_reflected (h0 : list Ev) (name : P) (model : list (YjsItem A * bool)) : Prop :=
  ∀ input : IntegrateInput (A := A),
    (RootId name, OpInsert input) ∈ delivered_ops h0 ->
    ∃ it, item_id it = in_id input ∧ it ∈ model.*1.

End text_model.
