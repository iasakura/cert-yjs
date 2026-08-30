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
    - [own_ytype_cells_flatten]: the model list is the flatten of the cells
      (the internal [cells_repr] fact, projected without opening the
      predicate).

    The method proofs are [ytype/newYType.v], [ytype/findPos.v] and
    [ytype/Text.v].

    Run granularity (plan-item-run-split stages 2 and 3): [own_ytype_runs
    parent dq ls tm], the type's DLL at its address list and [type_model],
    PRIMITIVE over [own_dll_runs] (stage 3c); [own_ytype_runs_intro] reads
    it off the cells-level view and [own_ytype_runs_as_cells] reads it back
    at the re-materialized cells ([cells_of_locs_runs]). *)
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

(** [own_ytype_runs parent dq ls tm]: the type at its run-granular model,
    PRIMITIVE (plan-item-run-split stage 3c): [parent] is a heap [yType]
    whose [start] heads the run-granular DLL [own_dll_runs] at the node
    addresses [ls] and the runs [tm_runs tm]; [len] counts the visible
    chars and the document list is the runs' flatten. The [(locs, p)]-keyed
    pool ([store/heap.v]'s [own_type_pool_runs]) is a big-op of these;
    [own_ytype_runs_intro] / [own_ytype_runs_as_cells] fold and unfold the
    cells-level view through it during the migration. *)
Definition own_ytype_runs (parent : loc) (dq : dfrac)
    (ls : list loc) (tm : type_model) : iProp Σ :=
  ∃ (yt : yjs.yType.t) (tl : loc),
    "Hparent" ∷ parent ↦{dq} yt ∗
    "Hdll" ∷ own_dll_runs dq parent yt.(yjs.yType.start') tl null null ls (tm_runs tm) ∗
    "%Hlen" ∷ ⌜yt.(yjs.yType.len') = W64 (runs_visible (tm_runs tm))⌝ ∗
    "%Harr" ∷ ⌜tm_arr tm = runs_flatten (tm_runs tm)⌝.

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

(** Projection: the model list is the flatten of the cells (the [cells_repr]
    conjunct, extracted without opening the predicate; the read API relates
    a borrowed type's [cells_model] snapshot to its item list this way). *)
Lemma own_ytype_cells_flatten (parent : loc) (dq : dfrac)
    (cells : list item_cell) (arr : list (YjsItem A)) :
  own_ytype_cells parent dq cells arr -∗
  own_ytype_cells parent dq cells arr ∗ ⌜arr = run_flatten cells⌝.
Proof.
  iIntros "H". iDestruct "H" as (yt tl) "(Hp & Hdll & %Hlen & %Hrepr & %Hcpar)".
  iSplitL; last (iPureIntro; exact Hrepr).
  iExists yt, tl. iFrame "Hp Hdll". iPureIntro. split_and!; [exact Hlen | exact Hrepr | exact Hcpar].
Qed.

(** [own_ytype_runs] is the cells-level view at the projected model. *)
Lemma own_ytype_runs_intro (parent : loc) (dq : dfrac)
    (cells : list item_cell) (arr : list (YjsItem A)) :
  own_ytype_cells parent dq cells arr -∗
  own_ytype_runs parent dq (ic_loc <$> cells) (MkTypeModel (cell_run <$> cells) arr).
Proof.
  iIntros "H". iDestruct "H" as (yt tl) "(Hp & Hdll & %Hlen & %Hrepr & %Hcpar)".
  iExists yt, tl.
  iEval (rewrite (own_dll_as_runs dq yt.(yjs.yType.start') tl null null parent cells Hcpar)) in "Hdll".
  iFrame "Hp Hdll".
  iPureIntro. simpl. split.
  - rewrite Hlen num_visible_runs //.
  - rewrite /cells_repr in Hrepr. rewrite Hrepr run_flatten_runs //.
Qed.

(** The primitive run view read back at cells: exactly the zip of the
    addresses with the runs ([cells_of_locs_runs]). What lets a cells-level
    proof consume [own_ytype_runs] during the migration; the projection pins
    follow from the exposed length through [cells_of_locs_runs_run] /
    [_loc]. *)
Lemma own_ytype_runs_as_cells (parent : loc) (dq : dfrac)
    (ls : list loc) (tm : type_model) :
  own_ytype_runs parent dq ls tm -∗
  ⌜length ls = length (tm_runs tm)⌝ ∗
  own_ytype_cells parent dq (cells_of_locs_runs parent ls (tm_runs tm)) (tm_arr tm).
Proof.
  iIntros "H". iDestruct "H" as (yt tl) "(Hp & Hdll & %Hlen & %Harr)".
  iDestruct (own_dll_runs_length with "Hdll") as %Hlenls.
  set (cells := cells_of_locs_runs parent ls (tm_runs tm)).
  have Hcr : cell_run <$> cells = tm_runs tm
    := cells_of_locs_runs_run parent ls (tm_runs tm) Hlenls.
  have Hlc : ic_loc <$> cells = ls
    := cells_of_locs_runs_loc parent ls (tm_runs tm) Hlenls.
  have Hcp : ∀ c, c ∈ cells -> ic_parent c = parent
    := cells_of_locs_runs_parent parent ls (tm_runs tm).
  iSplitR; [by iPureIntro |].
  iExists yt, tl.
  iEval (rewrite -Hcr -Hlc
           -(own_dll_as_runs dq yt.(yjs.yType.start') tl null null parent cells Hcp)) in "Hdll".
  iFrame "Hp Hdll".
  iPureIntro. split_and!.
  - rewrite Hlen num_visible_runs Hcr //.
  - rewrite /cells_repr Harr run_flatten_runs Hcr //.
  - exact Hcp.
Qed.

End ytype_heap.
