(** The [yType] container, Iris layer.

    In y-octo [YType] is the lock-guarded inner data structure while the [YText]
    handle lives outside the lock; this directory owns the [YType] side and is
    closed over implementation ([yjs/ytype.go]), spec, and proof.

    Definitions
    - [own_ytype parent dq m]: the PUBLIC representation predicate. [parent] is
      a heap [yType] representing the abstract model [m], with the heap cells
      (node locations, spine links) existentially hidden, so public specs speak
      only about [m]. [dfrac]-parameterized (idiom: plain owned heap data).
    - [own_ytype_cells parent dq cells arr]: the cells-level predicate under it,
      a heap [yType] whose [start] heads an item DLL ([own_dll], from
      [item/heap.v]), with [len] counting the visible cells. Internal proofs
      ([findPos], the Integrate scan / splice, the Insert / Delete loops) work
      at this level because they track node locations.

    Laws
    - [own_ytype_intro]: any cells-level view is the public view at its cell
      model, which is the only way the two levels are ever connected.

    The method proofs are [ytype/newYType.v] and [ytype/findPos.v]. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core prelude.
(* The [findPos] word-arithmetic proof writes [Z] comparisons unannotated, so fix
   [Z_scope] as the default (matching the environment it was developed in). *)
Local Open Scope Z_scope.
From New.proof.ytype Require Import model value.
From New.proof.id Require Import value heap.
From New.proof.item Require Import run_theory model value heap.

Section ytype_heap.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.

(* ===== definitions ======================================================== *)

(** [own_ytype_cells parent dq cells arr]: [parent] is a heap [yType] whose
    [start] heads the DLL [cells], which is isomorphic to the model [arr]. [len]
    counts the visible (non-deleted) cells ([num_visible]); a deletion tombstones
    a cell (set its [ic_deleted] bit) without removing it, so [cells] / [arr]
    keep every item. Every cell's [ic_parent] is this type's own loc (issue #49:
    items carry their parent; [store.repair]'s borrow-from-neighbour reads it). *)
Definition own_ytype_cells (parent : loc) (dq : dfrac)
    (cells : list item_cell) (arr : list (YjsItem A)) : iProp Σ :=
  ∃ (yt : yjs.yType.t) (tl : loc),
    "Hparent" ∷ parent ↦{dq} yt ∗
    "Hdll" ∷ own_dll dq yt.(yjs.yType.start') tl null null cells ∗
    "%Hlen" ∷ ⌜yt.(yjs.yType.len') = W64 (num_visible cells)⌝ ∗
    "%Hrepr" ∷ ⌜cells_repr arr cells arr⌝ ∗
    "%Hcpar" ∷ ⌜∀ c, c ∈ cells -> ic_parent c = parent⌝.

(** [own_ytype parent dq m]: the public [yType] predicate. [m] pairs each
    document (per-char) item with its tombstone bit, in document order; [m.*1]
    is the document list ([YjsArrInvariant] etc. are stated about it as pure
    side conditions of the specs, not baked in here). *)
Definition own_ytype (parent : loc) (dq : dfrac) (m : list (YjsItem A * bool)) : iProp Σ :=
  ∃ (cells : list item_cell),
    "Hcells" ∷ own_ytype_cells parent dq cells m.*1 ∗
    "%Hm" ∷ ⌜m = cells_model cells⌝.

(* ===== lemmas ============================================================= *)

(** Introduction: any cells-level view is the public view at its cell model
    (whose item list is the cells-level [arr]). *)
Lemma own_ytype_intro (parent : loc) (dq : dfrac)
    (cells : list item_cell) (arr : list (YjsItem A)) :
  own_ytype_cells parent dq cells arr ⊢
    own_ytype parent dq (cells_model cells) ∗ ⌜(cells_model cells).*1 = arr⌝.
Proof.
  iIntros "H". iDestruct "H" as (yt tl) "(Hp & Hdll & %Hlen & %Hrepr & %Hcpar)".
  have Harr : (cells_model cells).*1 = arr.
  { rewrite cells_model_fst. rewrite /cells_repr in Hrepr. rewrite Hrepr //. }
  iSplitL; last (iPureIntro; exact Harr).
  iExists cells. rewrite Harr. iSplitL; last done.
  iExists yt, tl. iFrame "Hp Hdll". iPureIntro. split_and!; [exact Hlen | exact Hrepr | exact Hcpar].
Qed.

End ytype_heap.
