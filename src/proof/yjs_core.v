(** Boundary to the reusable Yjs order theory.

    cert-yjs proves that the goose-translated [Integrate] refines the *pure*
    integration algorithm, and inherits order preservation from it. That pure
    theory lives in iasakura/iris-yjs ([theories/core] + [theories/algorithm])
    and is being packaged as the opam libraries coq-yjs-core / coq-yjs.

    Until those packages are available in this (Perennial) switch, this file is
    the parametric stand-in for them:

    - The *model types* cert-yjs has to pattern-match on in its representation
      predicate ([YjsId], [YjsPtr], [YjsItem], [IntegrateInput]) are given
      concretely, copied verbatim from iris-yjs so the eventual swap is a no-op.
    - The *order theory*, the pure [integrate], and its order-preservation
      theorem are declared as [Parameter]/[Axiom] here. They are fully proved in
      iris-yjs; the names and signatures match so that replacing the marked
      section below with [From yjs Require Import ...] discharges every axiom.

    Source map (iris-yjs):
      YjsId, YjsPtr, YjsItem, accessors   theories/core/item.v
      ClientId                            theories/crdt/client_id.v
      YjsLt' / YjsLeq'                     theories/core/order/item_order.v
      IsClosedItemSet, ItemSetInvariant   theories/core/item_set.v, order/item_set_invariant.v
      ArrSet, YjsArrInvariant             theories/algorithm/invariant_yjsarray.v
      IntegrateInput, toItem, integrate*  theories/algorithm/insert_basic.v
      YjsArrInvariant_integrateSafe       theories/algorithm/insert_loop.v
*)
From stdpp Require Import base numbers list.

(* ========================================================================= *)
(* Concrete model types (port of iris-yjs theories/core/item.v).             *)
(* ========================================================================= *)

Definition ClientId := nat.

(** An identifier pairs the originating client with a per-client clock. *)
Record YjsId := MkYjsId {
  clientId : ClientId;
  clock : nat;
}.
Add Printing Constructor YjsId.

Global Instance YjsId_eq_dec : EqDecision YjsId.
Proof. solve_decision. Defined.

(** Within the same client a larger clock is "smaller" (more to the left);
    across clients we compare client ids. *)
Definition YjsId_lt (id1 id2 : YjsId) : Prop :=
  if bool_decide (id1.(clientId) = id2.(clientId))
  then id2.(clock) < id1.(clock)
  else id1.(clientId) < id2.(clientId).

(** The document is a tree of items. A pointer is either an item or one of the
    two sentinels [First]/[Last]. *)
Inductive YjsPtr (A : Type) : Type :=
  | itemPtr : YjsItem A -> YjsPtr A
  | First : YjsPtr A
  | Last : YjsPtr A
with YjsItem (A : Type) : Type :=
  | Item : YjsPtr A -> YjsPtr A -> YjsId -> A -> YjsItem A.

Arguments itemPtr {A} _.
Arguments First {A}.
Arguments Last {A}.
Arguments Item {A} _ _ _ _.

Coercion itemPtr : YjsItem >-> YjsPtr.

Definition origin {A} (i : YjsItem A) : YjsPtr A :=
  match i with Item o _ _ _ => o end.
Definition rightOrigin {A} (i : YjsItem A) : YjsPtr A :=
  match i with Item _ r _ _ => r end.
Definition item_id {A} (i : YjsItem A) : YjsId :=
  match i with Item _ _ id _ => id end.
Definition content {A} (i : YjsItem A) : A :=
  match i with Item _ _ _ c => c end.

(** Input to one integration step (port of algorithm/insert_basic.v). *)
Record IntegrateInput (A : Type) := MkIntegrateInput {
  in_originId : option YjsId;
  in_rightOriginId : option YjsId;
  in_content : A;
  in_id : YjsId;
}.
Arguments MkIntegrateInput {A} _ _ _ _.
Arguments in_originId {A} _.
Arguments in_rightOriginId {A} _.
Arguments in_content {A} _.
Arguments in_id {A} _.

(* ========================================================================= *)
(* Reused order theory + pure integrate (provided by coq-yjs / coq-yjs-core).*)
(*                                                                           *)
(* Concrete and fully proved in iris-yjs; abstract here so cert-yjs compiles *)
(* before the opam package lands. Replace everything below this banner with  *)
(* the corresponding [From yjs Require Import ...] to discharge the axioms.   *)
(* ========================================================================= *)

(** Item order. [YjsLt'] is the strict order; [YjsLeq'] its reflexive closure. *)
Parameter YjsLt' : forall {A}, YjsPtr A -> YjsPtr A -> Prop.
Parameter YjsLeq' : forall {A}, YjsPtr A -> YjsPtr A -> Prop.

(** [ArrSet arr] is the item set induced by a document list. *)
Parameter ArrSet : forall {A}, list (YjsItem A) -> YjsPtr A -> Prop.

(** Document well-formedness = cert-yjs's [valid]: the induced set is closed and
    satisfies the item-set invariant, the list is [YjsLt']-sorted, and ids are
    unique (iris-yjs [YjsArrInvariant]). *)
Parameter YjsArrInvariant : forall {A}, list (YjsItem A) -> Prop.

(** Build the new item from an input by resolving its origin ids against the
    current document (iris-yjs [toItem]). *)
Parameter toItem : forall {A}, IntegrateInput A -> list (YjsItem A) -> option (YjsItem A).

(** Side condition on the item being integrated (iris-yjs [IsItemValid]). *)
Parameter IsItemValid : forall {A}, YjsItem A -> Prop.

(** The pure integration step on the list model (iris-yjs [integrateSafe]):
    resolves origins, finds the integrated index via the conflict scan, and
    splices the item in. [None] on a malformed input. *)
Parameter integrateSafe : forall {A}, IntegrateInput A -> list (YjsItem A) -> option (list (YjsItem A)).

(** The order-preservation theorem cert-yjs inherits: integrating a valid item
    into a valid document yields a valid document (iris-yjs
    [YjsArrInvariant_integrateSafe] / [YjsStateInvariant_insert]). *)
Axiom YjsArrInvariant_integrateSafe :
  forall {A} (input : IntegrateInput A) (arr arr' : list (YjsItem A)) (newItem : YjsItem A),
    YjsArrInvariant arr ->
    toItem input arr = Some newItem ->
    IsItemValid newItem ->
    integrateSafe input arr = Some arr' ->
    YjsArrInvariant arr'.
