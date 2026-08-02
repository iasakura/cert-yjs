(** Boundary to the reusable Yjs order theory.

    cert-yjs proves that the goose-translated [Integrate] refines the *pure*
    integration algorithm and inherits order preservation from it. That pure
    theory lives in iasakura/rocq-yjs, packaged as the opam libraries
    rocq-yjs-core (namespace [yjs.crdt]) and rocq-yjs (namespace [yjs]).

    This module re-exports the pieces cert-yjs consumes so the rest of the
    development imports a single name:

      ClientId                            yjs.crdt.client_id
      YjsId, YjsPtr, YjsItem, accessors   yjs.item
      ItemSet, IsClosedItemSet            yjs.item_set
      YjsLt'/YjsLeq', ItemSetInvariant    yjs.order.{item_order,item_set_invariant}
      IntegrateInput, toItem, integrate*  yjs.algorithm.{basic,insert_basic}
      ArrSet, YjsArrInvariant             yjs.algorithm.invariant_yjsarray
      IsItemValid                         yjs.algorithm.invariant_basic
      YjsArrInvariant_integrateSafe       yjs.algorithm.insert_loop
      set_find_integration_loop, setintegrate, Couple,  yjs.algorithm.insert_set
        setintegrate_eq_integrate, ...
      integrate_some (integrate totality) yjs.algorithm.commutativity
*)
From yjs.crdt Require Export client_id.
From yjs Require Export item item_set util.
From yjs.order Require Export item_order item_set_invariant.
From yjs.algorithm Require Export basic insert_basic invariant_basic invariant_yjsarray insert_loop insert_set commutativity.


From stdpp Require Import countable gmap.
(* [Import], not [Export]: the derivation below is written in ssreflect's
   multi-rewrite style, but downstream files pick their own tactic dialect. *)
From stdpp Require Import ssreflect.

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
  | GenNode 1 [child] => match YjsItem_dec child with Some i => Some (itemPtr i) | None => None end
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
