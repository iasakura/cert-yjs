(** The cert-yjs heap representation of a [YText] — invariant DESIGN.

    Links the heap structure produced by goose (a [YText] whose [start] heads a
    doubly linked list of [Item] cells) to the direct pure model
    [arr : list (YjsItem A)] of iris-yjs.

    Design goals (so the [Integrate] refinement is tractable):
    - Direct model [YjsItem] (origins are structural [YjsPtr]), so the order
      theory ([YjsLt'], sortedness) applies to [arr] without re-resolution.
    - Track each cell together with its index: the abstraction is stated by
      positional lookup ([cs !! j] ↔ [arr !! j]), and the heap left/right
      pointers are tied to adjacent indices. This is what lets the Go loop's
      pointer walk mirror the pure loop's index walk.
    - Bake in the local origin/index ordering "origin sits at a strictly
      smaller index, right origin at a strictly larger index" — a structural
      (topological-order) fact the loop relies on, available directly rather
      than re-derived from sortedness each time.

    Two layers, kept separate:
    - [is_ytext parent arr]       — heap <-> model representation, with the
                                    structural/index facts above. Used by the
                                    refinement.
    - [is_valid_ytext parent arr] — [is_ytext] plus [YjsArrInvariant arr]
                                    (full [YjsLt']-sortedness, unique ids).

    Phase-2 simplification: content is a 1-char string, so the content type is
    [go_string].

    NOTE: this file is the invariant design — definitions only, proofs come
    after the shape is agreed. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import yjs_core.

Section invariant.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

(** Document content type. *)
Notation A := go_string.

(* ----- abstraction of scalar fields -------------------------------------- *)

(** Heap id (two [w64]s) to model id (two [nat]s). *)
Definition toYjsId (i : yjs.Id.t) : YjsId :=
  MkYjsId (uint.nat i.(yjs.Id.clientId')) (uint.nat i.(yjs.Id.clock')).

Definition toContent (c : yjs.Content.t) : A := c.(yjs.Content.content').

(* ----- physical layer: cells of the doubly linked list ------------------- *)

(** One node of the heap list: its location, the [Item] struct value, and the
    optional origin ids it carries (the contents of its [originLeftId] /
    [originRightId] pointers). The cell's *index* is its position in the list. *)
Record item_cell := MkItemCell {
  ic_loc : loc;
  ic_val : yjs.Item.t;
  ic_oleft : option yjs.Id.t;
  ic_oright : option yjs.Id.t;
}.

(** An origin pointer is either null (no origin) or a read-only [Id] cell.
    Origins are immutable once integrated, hence persistent ([↦□]). *)
Definition is_origin_id (p : loc) (oid : option yjs.Id.t) : iProp Σ :=
  match oid with
  | None => ⌜p = null⌝
  | Some idv => ⌜p ≠ null⌝ ∗ p ↦□ idv
  end.

(** Ownership of all cells: each cell owns its [Item] struct and its two
    origin-id cells. Distinctness of the [ic_loc]s is forced by separation. *)
Definition cells_own (cs : list item_cell) : iProp Σ :=
  [∗ list] c ∈ cs,
    ic_loc c ↦ ic_val c ∗
    is_origin_id (ic_val c).(yjs.Item.originLeftId') (ic_oleft c) ∗
    is_origin_id (ic_val c).(yjs.Item.originRightId') (ic_oright c).

(** Location of the cell after / before index [j] in [cs], or [null] at the
    ends. *)
Definition next_loc (cs : list item_cell) (j : nat) : loc :=
  match cs !! S j with Some c' => ic_loc c' | None => null end.
Definition prev_loc (cs : list item_cell) (j : nat) : loc :=
  match j with
  | O => null
  | S j' => match cs !! j' with Some c => ic_loc c | None => null end
  end.

(** The doubly-linked layout: [start] is the head loc, and every cell's [right]
    / [left] point to its successor / predecessor (null at the ends). Pure (it
    constrains the [Item] struct values held in [cs]). *)
Definition linked_layout (cs : list item_cell) (start : loc) : Prop :=
  start = (match cs with [] => null | c :: _ => ic_loc c end) /\
  (forall j c, cs !! j = Some c ->
     (ic_val c).(yjs.Item.right') = next_loc cs j /\
     (ic_val c).(yjs.Item.left') = prev_loc cs j).

(* ----- abstraction layer: heap cells <-> direct model, with indices ------- *)

(** A left origin id resolves, at document position [j], to a model pointer:
    [None] is [First]; [Some idv] is the item carrying that id, and it sits at a
    strictly smaller index [i < j]. *)
Definition origin_at (arr : list (YjsItem A)) (j : nat)
    (oid : option yjs.Id.t) (p : YjsPtr A) : Prop :=
  match oid with
  | None => p = First
  | Some idv => exists (i : nat) (it : YjsItem A),
      (i < j)%nat /\ arr !! i = Some it /\ item_id it = toYjsId idv /\ p = itemPtr it
  end.

(** A right origin id resolves at position [j]: [None] is [Last]; [Some idv] is
    the item carrying that id, sitting at a strictly larger index [j < k]. *)
Definition rightorigin_at (arr : list (YjsItem A)) (j : nat)
    (oid : option yjs.Id.t) (p : YjsPtr A) : Prop :=
  match oid with
  | None => p = Last
  | Some idv => exists (k : nat) (it : YjsItem A),
      (j < k)%nat /\ arr !! k = Some it /\ item_id it = toYjsId idv /\ p = itemPtr it
  end.

(** [cell_repr arr j c yi]: the model item [yi] at index [j] is the one heap
    cell [c] represents — matching id/content, and origins resolved (with the
    index ordering) against [arr]. *)
Definition cell_repr (arr : list (YjsItem A)) (j : nat)
    (c : item_cell) (yi : YjsItem A) : Prop :=
  item_id yi = toYjsId (ic_val c).(yjs.Item.id') /\
  content yi = toContent (ic_val c).(yjs.Item.content') /\
  origin_at arr j (ic_oleft c) (origin yi) /\
  rightorigin_at arr j (ic_oright c) (rightOrigin yi).

(** [cells_repr cs arr]: same length, and cellwise/indexwise [cell_repr]. *)
Definition cells_repr (cs : list item_cell) (arr : list (YjsItem A)) : Prop :=
  length cs = length arr /\
  (forall j c yi, cs !! j = Some c -> arr !! j = Some yi -> cell_repr arr j c yi).

(* ----- the representation predicate and its validity layer ---------------- *)

(** [is_ytext parent arr]: [parent] is a heap [YText] whose doubly linked list
    of cells represents [arr] — ownership ([cells_own]), the linked layout
    ([linked_layout]), the indexed abstraction ([cells_repr]), and the visible
    length field tracking the item count (all items countable, none deleted in
    Phase 2). Structural facts are baked in; sortedness is not. *)
Definition is_ytext (parent : loc) (arr : list (YjsItem A)) : iProp Σ :=
  ∃ (yt : yjs.YText.t) (cs : list item_cell),
    "Hparent" ∷ parent ↦ yt ∗
    "Hcells" ∷ cells_own cs ∗
    "%Hlayout" ∷ ⌜linked_layout cs yt.(yjs.YText.start')⌝ ∗
    "%Hrepr" ∷ ⌜cells_repr cs arr⌝ ∗
    "%Hlen" ∷ ⌜uint.nat yt.(yjs.YText.len') = length arr⌝.

(** [is_valid_ytext parent arr]: the representation plus full model validity. *)
Definition is_valid_ytext (parent : loc) (arr : list (YjsItem A)) : iProp Σ :=
  "Htext" ∷ is_ytext parent arr ∗
  "%Hinv" ∷ ⌜YjsArrInvariant arr⌝.

(* -------------------------------------------------------------------------- *)
(* Planned use in the [Integrate] proof (sketch, not yet formalised).
   The while-loop refinement will carry a loop invariant mirroring iris-yjs
   [LInv] (insert_loop.v), tying the heap loop state to the pure set-based
   scan via these index facts:
     - the [conflict] pointer at offset [k] is [ic_loc (cs !! (leftIdx+k))],
       so [conflict.right] / [conflict.left] step the index by ±1
       ([linked_layout]);
     - [itemsBeforeOrigin] (ids scanned so far) corresponds to the index range
       [(leftIdx, i)], and [conflictingItems] to the candidate range
       [[destIdx, i)] (cleared exactly when the insertion point [left] advances
       to [conflict]);
     - [origin_at] / [rightorigin_at] supply "origin index < item index", which
       under [is_valid_ytext] aligns with [YjsLt'] via
       [getElem_lt_YjsLt'] / [getElem_YjsLt'_index_lt].
   [is_ytext] (no sortedness) suffices for the structural pointer<->index
   reasoning; [is_valid_ytext] is needed only where the order decides the
   insertion position. *)
(* -------------------------------------------------------------------------- *)

End invariant.
