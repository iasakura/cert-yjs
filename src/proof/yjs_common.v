(** Common definitions shared across the cert-yjs proof modules.

    Split out of the original single-file invariant development so the
    per-module proof files ([yjs_item], [yjs_proof], [yjs_store], [yjs_text])
    can share one base layer:

    - scalar abstractions [toYjsId] / [toContent] (heap [w64] ids/content to
      the model);
    - the heap-node record [item_cell] and the cursor helper [node_loc];
    - the persistent origin-pointer predicate [is_origin_id];
    - the item-pointer helpers [oid_of] / [item_or_null];
    - the id-slice abstraction [is_id_set] (a heap [[]Id] as a [gset YjsId]).

    None of these depend on the item DLL spine or the heap<->model isomorphism,
    so every other module imports this one. The goose package-init instances
    live here too (declared once and inherited via [Require]). *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import yjs_core.
(* The Go package now imports sync (store.mu : sync.Mutex), so the generated yjs
   package imports sync; building [IsPkgInit yjs] below needs [IsPkgInit sync]
   (and [GetIsPkgInitWf sync]) in scope, provided by the sync proof base. The
   required [sync.Assumptions] comes from [yjs.Assumptions] (its
   [import_sync_Assumption ::] field). *)
From New.proof.sync_proof Require Import base.

(* ===== Countable (YjsItem A) ============================================== *)

(** [YjsItem]/[YjsPtr] are mutually inductive, so [solve_decision]-style
    derivation can't break the cycle (rocq-yjs derives only [EqDecision] this
    way). We get [Countable] by encoding the item tree into stdpp's [gen_tree]
    (leaves carry an id or a content character) and back, with the round-trip
    proved by the mutual induction scheme [YjsItem_mut]. This is what lets the
    store's grow-only item-set ghost use [gset (YjsItem A)] (pinning each known
    item to a genuine document item), rather than the weaker [gset YjsId] (which
    only pins ids and cannot witness a subsequence/[sublist] lower bound). *)
Section item_countable.
Context {A : Type} `{Countable A}.

Notation leaf := (YjsId + A)%type.

Fixpoint YjsItem_enc (i : YjsItem A) : gen_tree leaf :=
  match i with
  | Item o r id c => GenNode 0 [YjsPtr_enc o; YjsPtr_enc r; GenLeaf (inl id); GenLeaf (inr c)]
  end
with YjsPtr_enc (p : YjsPtr A) : gen_tree leaf :=
  match p with
  | itemPtr i => GenNode 1 [YjsItem_enc i]
  | First => GenNode 2 []
  | Last => GenNode 3 []
  end.

Fixpoint YjsItem_dec (t : gen_tree leaf) : option (YjsItem A) :=
  match t with
  | GenNode 0 [to; tr; GenLeaf (inl id); GenLeaf (inr c)] =>
      match YjsPtr_dec to, YjsPtr_dec tr with
      | Some o, Some r => Some (Item o r id c)
      | _, _ => None
      end
  | _ => None
  end
with YjsPtr_dec (t : gen_tree leaf) : option (YjsPtr A) :=
  match t with
  | GenNode 1 [ti] => match YjsItem_dec ti with Some i => Some (itemPtr i) | None => None end
  | GenNode 2 [] => Some First
  | GenNode 3 [] => Some Last
  | _ => None
  end.

Lemma YjsItem_dec_enc (i : YjsItem A) : YjsItem_dec (YjsItem_enc i) = Some i.
Proof.
  apply (YjsItem_mut A
    (fun p => YjsPtr_dec (YjsPtr_enc p) = Some p)
    (fun i => YjsItem_dec (YjsItem_enc i) = Some i)).
  - intros i0 IH. simpl. rewrite IH. reflexivity.
  - reflexivity.
  - reflexivity.
  - intros o IHo r IHr id c. simpl. rewrite IHo IHr. reflexivity.
Qed.

Global Instance YjsItem_countable : Countable (YjsItem A) :=
  inj_countable YjsItem_enc YjsItem_dec YjsItem_dec_enc.
End item_countable.

Section common.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

#[global] Instance : IsPkgInit (iProp Σ) yjs := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) yjs := build_get_is_pkg_init_wf.

Set Default Proof Using "Type*".

(** Document content type. *)
Notation A := go_string.

(* ===== abstraction of scalar fields ====================================== *)

(** Heap id (two [w64]s) to model id (two [nat]s). *)
Definition toYjsId (i : yjs.id.t) : YjsId :=
  MkYjsId (uint.nat i.(yjs.id.clientId')) (uint.nat i.(yjs.id.clock')).

Definition toContent (c : yjs.content.t) : A := c.(yjs.content.content').

(** One node of the heap DLL: its location, struct value, and the optional
    origin ids it points at (resolved out of the [originLeftId]/[originRightId]
    pointers). *)
Record item_cell := MkItemCell {
  ic_loc : loc;
  ic_val : yjs.item.t;
  ic_oleft : option yjs.id.t;
  ic_oright : option yjs.id.t;
}.

(** The loc of the node at index [k] of [cells] ([null] outside [0, len)).
    Used to place the heap [conflict] / [left] pointers within the DLL. *)
Definition node_loc (cells : list item_cell) (k : Z) : loc :=
  if decide (0 <= k)%Z then default null (ic_loc <$> cells !! Z.to_nat k) else null.

(** An origin pointer is either null (no origin) or a read-only [Id] cell.
    Origins are immutable once integrated, hence persistent ([↦□]). *)
Definition is_origin_id (p : loc) (oid : option yjs.id.t) : iProp Σ :=
  match oid with
  | None => ⌜p = null⌝
  | Some idv => ⌜p ≠ null⌝ ∗ p ↦□ idv
  end.

(** Origins are read-only, hence the predicate is persistent. *)
Global Instance is_origin_id_persistent p oid : Persistent (is_origin_id p oid).
Proof. rewrite /is_origin_id. by destruct oid; apply _. Qed.

(* ----- item-pointer helpers --------------------------------------------- *)

(** A heap item pointer is null or owns a node; [oid_of] is its model id. *)
Definition oid_of (ov : option yjs.item.t) : option YjsId :=
  (λ v, toYjsId v.(yjs.item.id')) <$> ov.

Definition item_or_null (p : loc) (ov : option yjs.item.t) (dq : dfrac) : iProp Σ :=
  match ov with
  | None => ⌜p = null⌝
  | Some v => ⌜p ≠ null⌝ ∗ p ↦{dq} v
  end.

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

End common.
