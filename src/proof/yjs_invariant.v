(** The cert-yjs heap representation of a [YText].

    Links the heap data structure produced by the goose translation (a [YText]
    whose [start] heads a linked list of [Item] cells) to the pure model of
    iris-yjs.

    The heap [Item] stores its origins as *ids* ([originLeftId],
    [originRightId]), so the faithful model is the iris-yjs *indirect* (by-id)
    item [IYjsItem], whose origins are id references ([YjsRef]). No structural
    origin resolution is needed: a cell maps to an [IYjsItem] field-for-field.
    Validity (sortedness etc.) is the direct-model invariant [YjsArrInvariant],
    carried over via erasure [ofDirectItem].

    Two layers, kept separate on purpose:
    - [is_ytext parent iarr]       — pure heap <-> by-id model. All the
                                      refinement of [Integrate] needs.
    - [is_valid_ytext parent iarr] — [is_ytext] plus model validity.

    Phase-2 simplification: content is a 1-char string, so the content type is
    [go_string]. *)
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

(* ----- physical layer: the heap item list -------------------------------- *)

(** One node of the heap item list: its location, struct value, and the
    optional origin ids it points at (resolved out of the
    [originLeftId]/[originRightId] pointers). *)
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

(** [is_item_list head cells]: [head] is the start of the heap linked list that,
    following [Item.right], visits exactly [cells]. *)
Fixpoint is_item_list (head : loc) (cells : list item_cell) : iProp Σ :=
  match cells with
  | [] => ⌜head = null⌝
  | c :: rest =>
      "%Hhd" ∷ ⌜head = ic_loc c⌝ ∗
      "Hval" ∷ ic_loc c ↦ ic_val c ∗
      "Holeft" ∷ is_origin_id (ic_val c).(yjs.Item.originLeftId') (ic_oleft c) ∗
      "Horight" ∷ is_origin_id (ic_val c).(yjs.Item.originRightId') (ic_oright c) ∗
      "Hrest" ∷ is_item_list (ic_val c).(yjs.Item.right') rest
  end.

(* ----- abstraction layer: heap cells <-> by-id model items --------------- *)

(** [cell_repr c iy]: the by-id model item [iy] is the one heap cell [c]
    represents. Origins map straight to id references — a left origin id [None]
    is the [First] boundary, a right origin id [None] is [Last] (iris-yjs
    [ofOriginId] / [ofRightOriginId]). *)
Definition cell_repr (c : item_cell) (iy : IYjsItem A) : Prop :=
  iid iy = toYjsId (ic_val c).(yjs.Item.id') /\
  icontent iy = toContent (ic_val c).(yjs.Item.content') /\
  iorigin iy = ofOriginId (toYjsId <$> ic_oleft c) /\
  irightOrigin iy = ofRightOriginId (toYjsId <$> ic_oright c).

(** [cells_repr cells iarr]: the heap cell list represents the by-id model list
    cellwise. Unlike the structural model, no whole-document context is needed —
    each cell determines its model item on its own. *)
Inductive cells_repr : list item_cell -> list (IYjsItem A) -> Prop :=
  | cells_repr_nil : cells_repr [] []
  | cells_repr_cons c iy cs ys :
      cell_repr c iy ->
      cells_repr cs ys ->
      cells_repr (c :: cs) (iy :: ys).

(* ----- the representation predicate and its validity layer ---------------- *)

(** [is_ytext parent iarr]: [parent] is a heap [YText] whose item list
    represents the by-id model document [iarr]. Pure representation — no
    invariant. *)
Definition is_ytext (parent : loc) (iarr : list (IYjsItem A)) : iProp Σ :=
  ∃ (yt : yjs.YText.t) (cells : list item_cell),
    "Hparent" ∷ parent ↦ yt ∗
    "Hlist" ∷ is_item_list yt.(yjs.YText.start') cells ∗
    "%Hrepr" ∷ ⌜cells_repr cells iarr⌝.

(** A by-id document is valid when it is the erasure of a valid direct document
    (iris-yjs [YjsArrInvariant], transported by [ofDirectItem]). If iris-yjs
    later exposes an intrinsic by-id invariant, this is the place to swap it. *)
Definition valid_iarr (iarr : list (IYjsItem A)) : Prop :=
  ∃ arr : list (YjsItem A), iarr = ofDirectItem <$> arr /\ YjsArrInvariant arr.

(** [is_valid_ytext parent iarr]: a heap [YText] representing a *valid* by-id
    model document. *)
Definition is_valid_ytext (parent : loc) (iarr : list (IYjsItem A)) : iProp Σ :=
  "Htext" ∷ is_ytext parent iarr ∗
  "%Hvalid" ∷ ⌜valid_iarr iarr⌝.

End invariant.
