(** The cert-yjs heap representation of a [YText] and the invariants for
    verifying [Store.Integrate].

    Design (two combined invariants, per the plan):

    1. DATA-STRUCTURE invariant.
       - [is_dll]: the doubly-linked-list structure invariant, adapted from the
         reference sorted-DLL proof (iasakura/perennial-sandbox, dll/list.go,
         [is_dlist_node]). Each node is an [Item] with [left]=prev / [right]=next
         pointers; a segment is described by its head [l], last node [last], the
         prev-pointer of the head [prev] and the next-pointer of the last [next].
       - [is_ytext] / [is_valid_ytext]: a heap [YText] whose [start] heads such a
         DLL, where the node list is ISOMORPHIC to a [list (YjsItem A)] that
         satisfies [YjsArrInvariant] (origins resolved by id via [cell_repr]).
         This combines the DLL structure invariant with the order/origin
         well-formedness of the pure model, as requested.

    2. LOOP invariant ([integrate_loop_inv]) for [Integrate]'s conflict scan:
       it couples the heap loop state (the [conflict]/[left] pointers and the
       [itemsBeforeOrigin]/[conflictingItems] slices) to the pure set-based loop
       [setfii_loop] of iris-yjs (via [Couple]), so the scan refines
       [setfindIntegratedIndex].

    Phase-2 simplification: content is a 1-char string ([go_string]); every item
    is countable and non-deleted, so [YText.len] = number of nodes. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import yjs_core.

Section invariant.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

#[global] Instance : IsPkgInit (iProp Σ) yjs := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) yjs := build_get_is_pkg_init_wf.

(** Document content type. *)
Notation A := go_string.

(* ===== abstraction of scalar fields ====================================== *)

(** Heap id (two [w64]s) to model id (two [nat]s). *)
Definition toYjsId (i : yjs.Id.t) : YjsId :=
  MkYjsId (uint.nat i.(yjs.Id.clientId')) (uint.nat i.(yjs.Id.clock')).

Definition toContent (c : yjs.Content.t) : A := c.(yjs.Content.content').

(** One node of the heap DLL: its location, struct value, and the optional
    origin ids it points at (resolved out of the [originLeftId]/[originRightId]
    pointers). *)
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

(* ===== (1) DATA-STRUCTURE invariant ====================================== *)

(* ----- the doubly-linked spine (adapted from the reference DLL) ----------- *)

(** [is_dll l last prev next cells]: the DLL segment whose head node is [l] and
    whose last node is [last]; [prev] is the [left]-pointer of [l] and [next] is
    the [right]-pointer of [last]. Mirrors the reference [is_dlist_node], with
    each node carrying its [Item] struct and the two origin-id cells. *)
Fixpoint is_dll (l last prev next : loc) (cells : list item_cell) : iProp Σ :=
  match cells with
  | [] => ⌜l = next ∧ last = prev⌝
  | c :: rest =>
      "%Hloc" ∷ ⌜l = ic_loc c ∧ l ≠ null⌝ ∗
      "%Hprev" ∷ ⌜(ic_val c).(yjs.Item.left') = prev⌝ ∗
      "Hval" ∷ ic_loc c ↦ ic_val c ∗
      "Holeft" ∷ is_origin_id (ic_val c).(yjs.Item.originLeftId') (ic_oleft c) ∗
      "Horight" ∷ is_origin_id (ic_val c).(yjs.Item.originRightId') (ic_oright c) ∗
      "Hrest" ∷ is_dll (ic_val c).(yjs.Item.right') last l next rest
  end.

(* ----- isomorphism to a YjsArrInvariant model ---------------------------- *)

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
    represents — same id and content, with [yi]'s origins being [c]'s origin ids
    resolved against the model [m]. *)
Definition cell_repr (m : list (YjsItem A)) (c : item_cell) (yi : YjsItem A) : Prop :=
  item_id yi = toYjsId (ic_val c).(yjs.Item.id') /\
  content yi = toContent (ic_val c).(yjs.Item.content') /\
  origin yi = resolve_left m (ic_oleft c) /\
  rightOrigin yi = resolve_right m (ic_oright c).

(** [cells_repr m cells items]: the heap cell list represents the model item
    list cellwise (origins resolved against the full model [m]). This is the
    "isomorphism" between the heap node sequence and a [list (YjsItem A)]. *)
Inductive cells_repr (m : list (YjsItem A)) : list item_cell -> list (YjsItem A) -> Prop :=
  | cells_repr_nil : cells_repr m [] []
  | cells_repr_cons c yi cs ys :
      cell_repr m c yi ->
      cells_repr m cs ys ->
      cells_repr m (c :: cs) (yi :: ys).

(** [is_ytext parent cells arr]: [parent] is a heap [YText] whose [start] heads
    the DLL [cells], which is isomorphic to the model [arr]. (Phase-2: every item
    is countable / non-deleted, so [len] = number of nodes.) *)
Definition is_ytext (parent : loc) (cells : list item_cell) (arr : list (YjsItem A)) : iProp Σ :=
  ∃ (yt : yjs.YText.t) (tl : loc),
    "Hparent" ∷ parent ↦ yt ∗
    "Hdll" ∷ is_dll yt.(yjs.YText.start') tl null null cells ∗
    "%Hlen" ∷ ⌜yt.(yjs.YText.len') = W64 (length cells)⌝ ∗
    "%Hrepr" ∷ ⌜cells_repr arr cells arr⌝.

(** The full data-structure invariant: a heap [YText] representing a *valid*
    model [arr] — DLL structure + isomorphism to a [YjsArrInvariant] list. *)
Definition is_valid_ytext (parent : loc) (arr : list (YjsItem A)) : iProp Σ :=
  ∃ cells,
    "Htext" ∷ is_ytext parent cells arr ∗
    "%Hinv" ∷ ⌜YjsArrInvariant arr⌝.

(* ===== (2) LOOP invariant for Integrate ================================== *)

(** The loc of the node at index [k] of [cells] ([null] outside [0, len)).
    Used to place the heap [conflict] / [left] pointers within the DLL. *)
Definition node_loc (cells : list item_cell) (k : Z) : loc :=
  if decide (0 <= k)%Z then default null (ic_loc <$> cells !! Z.to_nat k) else null.

(** A heap id-slice abstracts to a [gset YjsId]: its elements, mapped to model
    ids, are exactly [gs]. The Go set ops are [containsId] / [append] / reset to
    [[]]; [list_to_set] makes membership (not order/duplicates) the observable,
    matching the pure [gset] with [∪] / [∈]. *)
Definition is_id_set (s : slice.t) (gs : gset YjsId) : iProp Σ :=
  ∃ (vs : list yjs.Id.t),
    "Hsl" ∷ s ↦* vs ∗
    "%Hset" ∷ ⌜list_to_set (toYjsId <$> vs) = gs⌝.

(** Loop invariant for the conflict scan in [Integrate]. The heap loop refs
    track the pure [setfii_loop] state [(offset, ibo, ci, destIdx)] via [Couple]:
    - [conflict_l] (Go [conflict]) sits at the cursor node, index [leftIdx+offset]
      — the next item to scan ([other = arr !! (leftIdx + offset)]);
    - [left_l] (Go [left]) is the anchor: the node just left of the insert point,
      index [destIdx - 1] (so [item] will be spliced after it);
    - [right_l] (Go [right]) is loop-constant at index [rightIdx] (the right
      origin / [Last]); the loop's [conflict == right] break is [leftIdx+offset = rightIdx];
    - [ibo_l] / [ci_l] are the two id slices ([itemsBeforeOrigin] / [conflictingItems]).
    The DLL is owned throughout; [Hbound] keeps the cursor within [(leftIdx, rightIdx]]
    so the Go [for conflict ≠ nil] test (with the [== right] break) matches the
    pure loop's [count = rightIdx - leftIdx - 1] fuel. [is_fresh_item] and the
    [parent.len] field are loop-constant and framed outside this predicate. *)
Definition integrate_loop_inv (parent : loc) (cells : list item_cell)
    (arr : list (YjsItem A)) (newItem : YjsItem A) (leftIdx rightIdx : Z)
    (conflict_l left_l right_l ibo_l ci_l : loc)
    (offset : nat) (ibo ci : gset YjsId) (destIdx : Z) : iProp Σ :=
  "Htext" ∷ is_ytext parent cells arr ∗
  "Hconflict" ∷ conflict_l ↦ node_loc cells (leftIdx + Z.of_nat offset) ∗
  "Hleft" ∷ left_l ↦ node_loc cells (destIdx - 1) ∗
  "Hright" ∷ right_l ↦ node_loc cells rightIdx ∗
  "Hibo" ∷ (∃ ibo_sl : slice.t, "Hiboref" ∷ ibo_l ↦ ibo_sl ∗ "Hiboset" ∷ is_id_set ibo_sl ibo) ∗
  "Hci" ∷ (∃ ci_sl : slice.t, "Hciref" ∷ ci_l ↦ ci_sl ∗ "Hciset" ∷ is_id_set ci_sl ci) ∗
  "%Hbound" ∷ ⌜(leftIdx + Z.of_nat offset <= rightIdx)%Z⌝ ∗
  "%Hcouple" ∷ ⌜Couple arr newItem leftIdx offset ibo ci destIdx
                  (bool_decide (destIdx ≠ leftIdx + Z.of_nat offset)%Z)⌝.

(* ===== the Integrate WP specification ==================================== *)

(** [is_fresh_item item_l input iv oleft oright]: [item_l] is a freshly-built
    heap [Item] (not yet linked) whose id / content and origin-id cells carry the
    integration [input]. Its abstract model item is [newItem = toItem input arr]
    — that link is a side condition of the spec (a fresh item's resolved origins
    depend on the current document [arr]), so it is *not* restated here. The
    integrate algorithm resolves [left]/[right] from the origin ids and splices
    [item_l] into the document. *)
Definition is_fresh_item (item_l : loc) (input : IntegrateInput (A := A))
    (iv : yjs.Item.t) (oleft oright : option yjs.Id.t) : iProp Σ :=
  "Hitem" ∷ item_l ↦ iv ∗
  "Holeft" ∷ is_origin_id iv.(yjs.Item.originLeftId') oleft ∗
  "Horight" ∷ is_origin_id iv.(yjs.Item.originRightId') oright ∗
  "%Hin_l" ∷ ⌜(toYjsId <$> oleft) = in_originId input⌝ ∗   (* heap ids = input ids *)
  "%Hin_r" ∷ ⌜(toYjsId <$> oright) = in_rightOriginId input⌝ ∗
  "%Hid" ∷ ⌜toYjsId iv.(yjs.Item.id') = in_id input⌝ ∗
  "%Hcontent" ∷ ⌜toContent iv.(yjs.Item.content') = in_content input⌝.

(** Top-level spec: integrating a valid item into a valid document yields the
    document updated per the pure [setintegrate]; validity (hence order /
    convergence, via [setintegrate_eq_integrate]) is preserved. *)
Lemma wp_Store__Integrate (s parent item_l : loc) (arr arr' : list (YjsItem A))
    (input : IntegrateInput (A := A)) (newItem : YjsItem A)
    (iv : yjs.Item.t) (oleft oright : option yjs.Id.t) :
  YjsArrInvariant arr ->
  toItem input arr = Some newItem ->
  IsItemValid newItem ->
  maximalId newItem arr ->
  setintegrate input arr = Some arr' ->
  {{{ is_pkg_init yjs ∗ is_valid_ytext parent arr ∗
      is_fresh_item item_l input iv oleft oright }}}
    s @! (go.PointerType yjs.Store) @! "Integrate" #parent #item_l
  {{{ RET #(); is_valid_ytext parent arr' }}}.
Proof using All.
Admitted.

End invariant.
