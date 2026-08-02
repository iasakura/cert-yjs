(** The [yType] container, VALUE layer: what a cell list denotes as a sequence.
    Go values but no Iris.

    Definitions
    - [cell_models] / [cells_model]: a cell list read as the abstract sequence
      [list (YjsItem A * bool)], each document item paired with its tombstone
      bit.

    Laws
    - [cells_model_fst]: its first projection is the document list
      [run_flatten], so the public model and the cells-level model agree on
      content and differ only by the tombstone bits. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core prelude.
From stdpp Require Import sorting.
From New.proof.ytype Require Import model.
From New.proof.id Require Import value heap.
From New.proof.item Require Import run_theory model value heap.

Section ytype_value.

Set Default Proof Using "Type*".

Notation A := go_string.

(* ===== definitions ======================================================== *)

(* ----- the abstract model and the public predicate ----------------------- *)

(** The abstract per-char cells a heap cell denotes: each model item of its run
    paired with the cell's tombstone bit. The heap location is dropped — this
    is the abstraction wall (the model stays per-char; runs are invisible,
    issue #28). *)
Definition cell_models (c : item_cell) : list (YjsItem A * bool) :=
  (λ x, (x, ic_deleted c)) <$> ic_run c.

Definition cells_model (cells : list item_cell) : list (YjsItem A * bool) :=
  mjoin (cell_models <$> cells).

(* ===== lemmas ============================================================= *)


(* ===== lemmas ============================================================= *)

Lemma fmap_pair_fst (d : bool) (r : list (YjsItem A)) :
  ((λ x : YjsItem A, (x, d)) <$> r).*1 = r.
Proof. induction r as [|x r IH]; [done | by rewrite !fmap_cons IH]. Qed.

Lemma cells_model_fst (cells : list item_cell) :
  (cells_model cells).*1 = run_flatten cells.
Proof.
  induction cells as [|c cs IH]; first done.
  rewrite /cells_model /run_flatten /= fmap_app IH /cell_models fmap_pair_fst //.
Qed.

End ytype_value.
