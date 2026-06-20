(** The cert-yjs heap<->model isomorphism for a [YText].

    On top of the doubly-linked spine [is_dll] (in [yjs_dll]), this module
    relates a heap node sequence to a [list (YjsItem A)] of the pure model:

    - [resolve_left] / [resolve_right]: resolve an origin id against the model;
    - [cell_repr] / [cells_repr]: the cellwise correspondence between heap
      [item_cell]s and model [YjsItem]s (ids, content, origins-by-id);
    - [is_ytext] / [is_valid_ytext]: a heap [YText] whose [start] heads such a
      DLL, isomorphic to a model list that satisfies [YjsArrInvariant];
    - [is_id_set]: a heap [[]Id] slice abstracted to a [gset YjsId].

    This is the data-structure invariant the [Store.Integrate] / [Text.Insert]
    proofs (in [yjs_store] / [yjs_text]) are stated against.

    Phase-2 simplification: content is a 1-char string ([go_string]); every item
    is countable and non-deleted, so [YText.len] = number of nodes. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import yjs_core.
From New.proof Require Import yjs_common yjs_dll.

Section invariant.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.

(* ----- isomorphism to a YjsArrInvariant model ---------------------------- *)

(** Resolve a left origin id against the model [m]: [None] is the [First]
    sentinel, otherwise the model item carrying that id. *)
Definition resolve_left (m : list (YjsItem A)) (oid : option yjs.id.t) : YjsPtr A :=
  match oid with
  | None => First
  | Some idv =>
      match list_find (λ it, item_id it = toYjsId idv) m with
      | Some (_, it) => itemPtr it
      | None => First
      end
  end.

(** Resolve a right origin id: [None] is the [Last] sentinel. *)
Definition resolve_right (m : list (YjsItem A)) (oid : option yjs.id.t) : YjsPtr A :=
  match oid with
  | None => Last
  | Some idv =>
      match list_find (λ it, item_id it = toYjsId idv) m with
      | Some (_, it) => itemPtr it
      | None => Last
      end
  end.

(** [cell_repr m c yi]: the model item [yi] is the one the heap cell [c]
    represents — same id and content, and [yi]'s origins carry exactly [c]'s
    heap origin ids (as model ids). Stating origins by id (rather than by
    resolution against [m]) is what the conflict scan needs to match
    [setfii_loop]'s id tests, and rules out a heap origin id that fails to
    resolve. ([m] is kept for uniformity with [cells_repr] / [resolve_*].)

    The last two conjuncts pin the heap flags / content length uniformly:
    every cell is Countable and non-Deleted ([flags' = W8 2], y-octo's
    ITEM_COUNTABLE) and one clock wide ([Len() = 1]). The Go model has no
    [Delete] in the goose build (it is [//go:build !goose]) and [newItem]
    always sets exactly [ITEM_COUNTABLE] over single-byte content, so this
    holds of every node ever integrated. [yText.findPos] reads [Deleted] /
    [Indexable] / [Len] off each node, so it needs these facts to walk by
    visible index.

    TODO: both pins are current-model simplifications and must relax as the
    verified model grows. Once deletions enter the goose build ([Delete] is
    presently [//go:build !goose]), [flags' = W8 2] weakens to "the Countable
    bit is set" (the Deleted bit may also be set, and [Indexable] / [findPos]
    must then skip deleted nodes); once items can span several clocks or split,
    [Len() = 1] goes ([content yi] becomes the whole run and [LastId]/[Len]
    reasoning generalises). [cell_repr] and its readers would then need these
    general forms. *)
Definition cell_repr (m : list (YjsItem A)) (c : item_cell) (yi : YjsItem A) : Prop :=
  item_id yi = toYjsId (ic_val c).(yjs.item.id') /\
  content yi = toContent (ic_val c).(yjs.item.content') /\
  origin_id (origin yi) = toYjsId <$> ic_oleft c /\
  origin_id (rightOrigin yi) = toYjsId <$> ic_oright c /\
  (ic_val c).(yjs.item.flags') = W8 2 /\
  length ((ic_val c).(yjs.item.content').(yjs.content.content')) = 1%nat.

(** [cells_repr m cells items]: the heap cell list represents the model item
    list cellwise (origins resolved against the full model [m]). This is the
    "isomorphism" between the heap node sequence and a [list (YjsItem A)]. *)
Inductive cells_repr (m : list (YjsItem A)) : list item_cell -> list (YjsItem A) -> Prop :=
  | cells_repr_nil : cells_repr m [] []
  | cells_repr_cons c yi cs ys :
      cell_repr m c yi ->
      cells_repr m cs ys ->
      cells_repr m (c :: cs) (yi :: ys).

(** The isomorphism is length-preserving and cellwise. *)
Lemma cells_repr_length m cells items :
  cells_repr m cells items -> length cells = length items.
Proof. by elim=> [|c yi cs ys _ _ IH] //=; rewrite IH. Qed.

Lemma cells_repr_lookup m cells items k c :
  cells_repr m cells items -> cells !! k = Some c ->
  ∃ yi, items !! k = Some yi ∧ cell_repr m c yi.
Proof.
  move=> H; elim: H k c => [|c0 yi cs ys Hc _ IH] k c.
  - by case: k.
  - case: k => [|k'] /=; first by move=> [<-]; exists yi.
    exact: IH.
Qed.

(** Inserting a corresponding cell/item at the same position preserves the
    isomorphism (the splice's model side). *)
Lemma cells_repr_insert m cells items (k : nat) c yi :
  cells_repr m cells items -> cell_repr m c yi ->
  cells_repr m (take k cells ++ c :: drop k cells) (take k items ++ yi :: drop k items).
Proof.
  move=> H Hc; elim: H k => [|c0 yi0 cs ys Hc0 Hrec IH] k.
  - rewrite !take_nil !drop_nil /=. apply: cells_repr_cons; [exact Hc | exact: cells_repr_nil].
  - case: k => [|k'] /=.
    + apply: cells_repr_cons; first exact Hc.
      apply: cells_repr_cons; [exact Hc0 | exact Hrec].
    + apply: cells_repr_cons; [exact Hc0 | exact: IH].
Qed.

(** [cell_repr] constrains only id / content / origin-ids — it ignores both the
    resolution context [m] and the cell's [left']/[right'] heap fields. The splice
    relinks boundary nodes' [left']/[right'] and threads a fresh resolution model,
    so these congruences keep the isomorphism intact across the surgery. *)
Lemma cells_repr_m_irrel (m m' : list (YjsItem A)) cells items :
  cells_repr m cells items -> cells_repr m' cells items.
Proof.
  elim=> [|c yi cs ys Hc _ IH]; [apply: cells_repr_nil | apply: cells_repr_cons; [exact Hc | exact IH]].
Qed.

Lemma cells_repr_app (m : list (YjsItem A)) cs1 cs2 ys1 ys2 :
  cells_repr m cs1 ys1 -> cells_repr m cs2 ys2 -> cells_repr m (cs1 ++ cs2) (ys1 ++ ys2).
Proof.
  move=> H1 H2. elim: H1 => [|c yi cs ys Hc _ IH] //=.
  apply: cells_repr_cons; [exact Hc | exact IH].
Qed.

Lemma cells_repr_take (m : list (YjsItem A)) cells items k :
  cells_repr m cells items -> cells_repr m (take k cells) (take k items).
Proof.
  move=> H. elim: H k => [|c yi cs ys Hc _ IH] k.
  - rewrite !take_nil. apply: cells_repr_nil.
  - case: k => [|k'] /=; [apply: cells_repr_nil | apply: cells_repr_cons; [exact Hc | exact: IH]].
Qed.

Lemma cells_repr_drop (m : list (YjsItem A)) cells items k :
  cells_repr m cells items -> cells_repr m (drop k cells) (drop k items).
Proof.
  move=> H. elim: H k => [|c yi cs ys Hc Htl IH] k.
  - rewrite !drop_nil. apply: cells_repr_nil.
  - case: k => [|k'] /=; [apply: cells_repr_cons; [exact Hc | exact Htl] | exact: IH].
Qed.

Lemma cell_repr_val_irrel (m : list (YjsItem A)) (c : item_cell) (v' : yjs.item.t) yi :
  cell_repr m c yi ->
  (ic_val c).(yjs.item.id') = v'.(yjs.item.id') ->
  (ic_val c).(yjs.item.content') = v'.(yjs.item.content') ->
  (ic_val c).(yjs.item.flags') = v'.(yjs.item.flags') ->
  cell_repr m (MkItemCell (ic_loc c) v' (ic_oleft c) (ic_oright c)) yi.
Proof.
  rewrite /cell_repr /=. move=> [Hid [Hcon [Hol [Hor [Hfl Hcl]]]]] Hid' Hcon' Hfl'.
  split_and!;
    [rewrite Hid Hid' // | rewrite Hcon Hcon' // | exact Hol | exact Hor
    | rewrite -Hfl' // | rewrite -Hcon' // ].
Qed.

(** [is_ytext parent cells arr]: [parent] is a heap [YText] whose [start] heads
    the DLL [cells], which is isomorphic to the model [arr]. (Phase-2: every item
    is countable / non-deleted, so [len] = number of nodes.) *)
Definition is_ytext (parent : loc) (cells : list item_cell) (arr : list (YjsItem A)) : iProp Σ :=
  ∃ (yt : yjs.yText.t) (tl : loc),
    "Hparent" ∷ parent ↦ yt ∗
    "Hdll" ∷ is_dll yt.(yjs.yText.start') tl null null cells ∗
    "%Hlen" ∷ ⌜yt.(yjs.yText.len') = W64 (length cells)⌝ ∗
    "%Hrepr" ∷ ⌜cells_repr arr cells arr⌝.

(** The full data-structure invariant: a heap [YText] representing a *valid*
    model [arr] — DLL structure + isomorphism to a [YjsArrInvariant] list. *)
Definition is_valid_ytext (parent : loc) (arr : list (YjsItem A)) : iProp Σ :=
  ∃ cells,
    "Htext" ∷ is_ytext parent cells arr ∗
    "%Hinv" ∷ ⌜YjsArrInvariant arr⌝.

(* ----- id-slice abstraction to a gset ----------------------------------- *)

(** A heap id-slice abstracts to a [gset YjsId]: its elements, mapped to model
    ids, are exactly [gs]. The Go set ops are [containsId] / [append] / reset to
    [[]]; [list_to_set] makes membership (not order/duplicates) the observable,
    matching the pure [gset] with [∪] / [∈]. *)
Definition is_id_set (s : slice.t) (gs : gset YjsId) : iProp Σ :=
  ∃ (vs : list yjs.id.t),
    "Hsl" ∷ s ↦* vs ∗
    "Hcap" ∷ own_slice_cap yjs.id.t s (DfracOwn 1) ∗
    "%Hset" ∷ ⌜list_to_set (toYjsId <$> vs) = gs⌝.

End invariant.
