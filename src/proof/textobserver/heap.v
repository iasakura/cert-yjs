(** The [TextObserver], Iris layer.

    Definitions
    - [own_delta sl dq delta]: the [[]DeltaOp] slice at [sl] denotes the
      delta [delta].
    - [own_deleted_spans dref deleted_ids]: the observer's
      [map[Client][]span[uint64]] at [dref] covers exactly [deleted_ids].
    - [own_TextObserver obs t γs γh name observed]: the observer at [obs]
      watches the [Text] [t] (root [name]) and last observed the snapshot
      [observed]: its token denotes [observed]'s state vector and deleted
      ids, and it holds the three certificates that carry
      [snapshot_grows_to observed current] to the next poll: every type's
      item set at the observation (a whole-map fragment of the item-set
      authority, [observed]'s items at this root, and every client's clocks
      below its observed state vector present in it), the observed deleted
      ids as a delete-set lower bound, and [observed]'s document invariant.

    Laws: none yet; the method proofs are [NewObserver.v] and
    [ApplyDelta.v], with [Poll.v] to follow (issue #198, O4b). *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core.
From New.proof Require Import algebra.
From New.proof Require Import prelude.
From New.proof Require Import history.
From New.proof.sync_proof Require Import mutex.
From iris.algebra Require Import auth gmap gset.
From iris.algebra.lib Require Import dfrac_agree.
From New.proof.id Require Import value heap.
From New.proof.item Require Import run_theory model value heap.
From New.proof.ytype Require Import model value heap.
From New.proof.store Require Import model value heap.
From New.proof.text Require Import model heap.
From New.proof.textobserver Require Import model value.

Section text_observer_heap.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Context {sync_pkg : sync.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.

Context {seq_inG : inG Σ (authR (gmapUR loc (gsetUR (YjsItem A))))}.

Context {acc_inG : inG Σ (authR (gsetUR YjsId))}.

Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO addressed_pool))}.

Local Notation P := go_string.

Local Notation snapshot := (list (YjsItem A * bool)).

(* ===== definitions ======================================================== *)

Definition own_delta (sl : slice.t) (dq : dfrac) (delta : list DeltaOp) : iProp Σ :=
  ∃ (vs : list yjs.DeltaOp.t),
    "Hsl" ∷ sl ↦*{dq} vs ∗
    "Hcap" ∷ own_slice_cap yjs.DeltaOp.t sl dq ∗
    "%Hdenote" ∷ ⌜Forall2 delta_op_denotes vs delta⌝.

Definition own_deleted_spans (dref : loc) (deleted_ids : gset YjsId) : iProp Σ :=
  ∃ (dm : gmap w64 slice.t) (spans : gmap w64 (list (yjs.span.t w64))),
    "Hdm" ∷ own_map dref (DfracOwn 1) dm ∗
    "Hspans" ∷ ([∗ map] client ↦ sl; sps ∈ dm; spans,
                  sl ↦* sps ∗ own_slice_cap (yjs.span.t w64) sl (DfracOwn 1)) ∗
    "%Hcover" ∷ ⌜∀ d, d ∈ deleted_ids <-> spans_cover spans d⌝.

Definition own_TextObserver (obs t : loc) (γs : store_names) (γh : history_names)
    (name : P) (observed : snapshot) : iProp Σ :=
  ∃ (ov : yjs.TextObserver.t) (tv : yjs.Text.t) (s_loc parent : loc)
    (state_vector : gmap w64 w64) (pool_items : gmap loc (gset (YjsItem A))),
    "Hobs" ∷ obs ↦ ov ∗
    "%Hotext" ∷ ⌜ov.(yjs.TextObserver.text') = t⌝ ∗
    "#Ht" ∷ t ↦□ tv ∗
    "%Hstore" ∷ ⌜tv.(yjs.Text.store') = s_loc⌝ ∗
    "%Hinner" ∷ ⌜tv.(yjs.Text.inner') = parent⌝ ∗
    "#His_store" ∷ is_Store s_loc γs γh ∗
    "#Hbind" ∷ is_type_binding γs.(sn_types) name parent ∗
    "Hstate_vector" ∷ own_map ov.(yjs.TextObserver.stateVector') (DfracOwn 1) state_vector ∗
    "%Hstate_vector" ∷ ⌜state_vector_denotes state_vector (snapshot_state_vector observed)⌝ ∗
    "Hdeleted" ∷ own_deleted_spans ov.(yjs.TextObserver.deleted') (snapshot_deleted_ids observed) ∗
    "#Hitems" ∷ own γs.(sn_seq) (◯ pool_items : authR (gmapUR loc (gsetUR (YjsItem A)))) ∗
    "%Hthis" ∷ ⌜pool_items !! parent = Some (list_to_set observed.*1)⌝ ∗
    "%Hbelow" ∷ ⌜∀ (c j : nat), (j < sv_get (snapshot_state_vector observed) c)%nat ->
                   ∃ q S y, pool_items !! q = Some S ∧ y ∈ S ∧ item_id y = MkYjsId c j⌝ ∗
    "#Hdeleted_lb" ∷ is_delete_set_lb γs (snapshot_deleted_ids observed) ∗
    "%Hsorted" ∷ ⌜YjsArrInvariant observed.*1⌝.

(* ===== lemmas ============================================================= *)

End text_observer_heap.
