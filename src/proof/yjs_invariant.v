(** The cert-yjs heap representation of a [YText].

    Links the heap data structure produced by the goose translation (a [YText]
    whose [start] heads a linked list of [Item] cells) to the pure model
    [arr : list (YjsItem A)] of iris-yjs.

    Two layers, kept separate on purpose:
    - [is_ytext parent arr]  — the pure representation predicate (heap <-> model).
      This is all the refinement of [Integrate] needs.
    - [is_valid_ytext parent arr] — [is_ytext] plus the model invariant
      [YjsArrInvariant arr]. Validity is carried alongside, not baked into the
      representation.

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

(* ----- abstraction layer: heap cells <-> model items --------------------- *)

(** Resolve a left origin id against the model [m]: [None] is the [First]
    sentinel, otherwise the model item carrying that id. *)
Definition resolve_left (m : list (YjsItem A)) (oid : option yjs.Id.t) : YjsPtr A :=
  match oid with
  | None => First
  | Some idv =>
      match list_find (λ it, item_id it = toYjsId idv) m with
      | Some (_, it) => itemPtr it
      | None => First
      end
  end.

(** Resolve a right origin id: [None] is the [Last] sentinel. *)
Definition resolve_right (m : list (YjsItem A)) (oid : option yjs.Id.t) : YjsPtr A :=
  match oid with
  | None => Last
  | Some idv =>
      match list_find (λ it, item_id it = toYjsId idv) m with
      | Some (_, it) => itemPtr it
      | None => Last
      end
  end.

(** [cell_repr m c yi]: the model item [yi] is the one the heap cell [c]
    represents — same id and content, with [yi]'s origins being [c]'s origin
    ids resolved against the model [m]. *)
Definition cell_repr (m : list (YjsItem A)) (c : item_cell) (yi : YjsItem A) : Prop :=
  item_id yi = toYjsId (ic_val c).(yjs.Item.id') /\
  content yi = toContent (ic_val c).(yjs.Item.content') /\
  origin yi = resolve_left m (ic_oleft c) /\
  rightOrigin yi = resolve_right m (ic_oright c).

(** [cells_repr m cells items]: the heap cell list [cells] represents the model
    item list [items], cellwise via [cell_repr], with all origins resolved
    against the *full* model [m] (a right origin may point past the current
    cell, so [m] is a fixed context rather than a growing prefix). *)
Inductive cells_repr (m : list (YjsItem A)) : list item_cell -> list (YjsItem A) -> Prop :=
  | cells_repr_nil : cells_repr m [] []
  | cells_repr_cons c yi cs ys :
      cell_repr m c yi ->
      cells_repr m cs ys ->
      cells_repr m (c :: cs) (yi :: ys).

(* ----- the representation predicate and its validity layer ---------------- *)

(** [is_ytext parent arr]: [parent] is a heap [YText] whose item list represents
    the model document [arr]. Pure representation — no invariant. *)
Definition is_ytext (parent : loc) (arr : list (YjsItem A)) : iProp Σ :=
  ∃ (yt : yjs.YText.t) (cells : list item_cell),
    "Hparent" ∷ parent ↦ yt ∗
    "Hlist" ∷ is_item_list yt.(yjs.YText.start') cells ∗
    "%Hrepr" ∷ ⌜cells_repr arr cells arr⌝.

(** [is_valid_ytext parent arr]: a heap [YText] representing a *valid* model
    [arr] (i.e. also [YjsArrInvariant arr]). *)
Definition is_valid_ytext (parent : loc) (arr : list (YjsItem A)) : iProp Σ :=
  "Htext" ∷ is_ytext parent arr ∗
  "%Hinv" ∷ ⌜YjsArrInvariant arr⌝.

End invariant.
