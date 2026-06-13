(** The cert-yjs document invariant.

    Links the heap data structure produced by the goose translation (a [YText]
    whose [start] heads a linked list of [Item] cells) to the pure model
    [arr : list (YjsItem A)] of iris-yjs, and asserts that the model is valid
    ([YjsArrInvariant], via [yjs_core]). [Integrate]'s spec will be stated as
    preserving [is_valid_doc].

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

(* ----- physical layer: the heap chain ------------------------------------ *)

(** One cell of the document: its heap location, struct value, and the optional
    origin ids it points at (resolved out of the [originLeftId]/[originRightId]
    pointers). *)
Record CellRep := MkCellRep {
  cr_loc : loc;
  cr_item : yjs.Item.t;
  cr_oleft : option yjs.Id.t;
  cr_oright : option yjs.Id.t;
}.

(** An origin pointer is either null (no origin) or a read-only [Id] cell.
    Origins are immutable once integrated, hence persistent ([↦□]). *)
Definition origin_id_rep (p : loc) (oid : option yjs.Id.t) : iProp Σ :=
  match oid with
  | None => ⌜p = null⌝
  | Some idv => ⌜p ≠ null⌝ ∗ p ↦□ idv
  end.

(** The forward spine of the document, following [right], collecting one
    [CellRep] per item. *)
Fixpoint doc_chain (head : loc) (cells : list CellRep) : iProp Σ :=
  match cells with
  | [] => ⌜head = null⌝
  | c :: rest =>
      "%Hhd" ∷ ⌜head = cr_loc c⌝ ∗
      "Hitem" ∷ cr_loc c ↦ cr_item c ∗
      "Holeft" ∷ origin_id_rep (cr_item c).(yjs.Item.originLeftId') (cr_oleft c) ∗
      "Horight" ∷ origin_id_rep (cr_item c).(yjs.Item.originRightId') (cr_oright c) ∗
      "Hrest" ∷ doc_chain (cr_item c).(yjs.Item.right') rest
  end.

(* ----- abstraction layer: cells to model --------------------------------- *)

(** Resolve a left origin id to a model pointer: [None] is the [First] sentinel,
    otherwise the model item carrying that id. *)
Definition resolve_left (arr : list (YjsItem A)) (oid : option yjs.Id.t) : YjsPtr A :=
  match oid with
  | None => First
  | Some idv =>
      match list_find (λ it, item_id it = toYjsId idv) arr with
      | Some (_, it) => itemPtr it
      | None => First
      end
  end.

(** Resolve a right origin id: [None] is the [Last] sentinel. *)
Definition resolve_right (arr : list (YjsItem A)) (oid : option yjs.Id.t) : YjsPtr A :=
  match oid with
  | None => Last
  | Some idv =>
      match list_find (λ it, item_id it = toYjsId idv) arr with
      | Some (_, it) => itemPtr it
      | None => Last
      end
  end.

(** A cell abstracts to a model item when their id/content agree and the model
    item's origins are the resolved heap origins. *)
Definition cell_abstracts (arr : list (YjsItem A)) (c : CellRep) (yi : YjsItem A) : Prop :=
  item_id yi = toYjsId (cr_item c).(yjs.Item.id') /\
  content yi = toContent (cr_item c).(yjs.Item.content') /\
  origin yi = resolve_left arr (cr_oleft c) /\
  rightOrigin yi = resolve_right arr (cr_oright c).

(** The heap chain abstracts to the model list positionwise. *)
Definition cells_abstract (cells : list CellRep) (arr : list (YjsItem A)) : Prop :=
  length cells = length arr /\
  (forall i c yi, cells !! i = Some c -> arr !! i = Some yi -> cell_abstracts arr c yi).

(* ----- the document invariant -------------------------------------------- *)

(** [parent] is a heap document representing the valid model [arr]. *)
Definition is_valid_doc (parent : loc) (arr : list (YjsItem A)) : iProp Σ :=
  ∃ (yt : yjs.YText.t) (cells : list CellRep),
    "Hparent" ∷ parent ↦ yt ∗
    "Hchain" ∷ doc_chain yt.(yjs.YText.start') cells ∗
    "%Habs" ∷ ⌜cells_abstract cells arr⌝ ∗
    "%Hinv" ∷ ⌜YjsArrInvariant arr⌝.

End invariant.
