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

    Laws
    - [own_delta_nil] / [own_deleted_spans_empty]: the nil slice is the
      empty delta, an empty map covers no id.
    - [own_deleted_spans_snoc]: borrow a client's span slice (the nil slice
      when absent) to append one span; the map then covers that span too.

    The method proofs are [NewObserver.v], [Poll.v] and [ApplyDelta.v]; the
    helpers of [Poll] are in [wp_private.v]. *)
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

Lemma own_delta_nil : ⊢ own_delta slice.nil (DfracOwn 1) [].
Proof.
  iExists []. iSplitR; [iApply own_slice_nil | iSplitR; [iApply own_slice_cap_nil | done]].
Qed.

Lemma own_deleted_spans_empty (dref : loc) :
  own_map dref (DfracOwn 1) (∅ : gmap w64 slice.t) -∗ own_deleted_spans dref ∅.
Proof.
  iIntros "Hdm". iExists ∅, ∅. iFrame "Hdm". rewrite big_sepM2_empty. iSplit; first done.
  iPureIntro. move=> d. split.
  - move=> Hd. exfalso. move: Hd. rewrite elem_of_empty //.
  - intros (client & sps & sp & Hlk & _). rewrite lookup_empty in Hlk. discriminate.
Qed.

(** Appending one span to a client's list: borrow the client's slice (the nil
    slice when the client is absent), and give the map back with the appended
    slice at that client; the covered ids gain the span's. *)
Lemma own_deleted_spans_snoc (dref : loc) (D D' : gset YjsId) (client : w64)
    (sp : yjs.span.t w64) :
  (∀ d, d ∈ D' <-> d ∈ D ∨ span_covers client sp d) ->
  own_deleted_spans dref D -∗
  ∃ (dm : gmap w64 slice.t) (sps : list (yjs.span.t w64)),
    own_map dref (DfracOwn 1) dm ∗
    default slice.nil (dm !! client) ↦* sps ∗
    own_slice_cap (yjs.span.t w64) (default slice.nil (dm !! client)) (DfracOwn 1) ∗
    (∀ ssl' : slice.t,
       ssl' ↦* (sps ++ [sp]) -∗ own_slice_cap (yjs.span.t w64) ssl' (DfracOwn 1) -∗
       own_map dref (DfracOwn 1) (<[client := ssl']> dm) -∗
       own_deleted_spans dref D').
Proof.
  iIntros (HD') "H". iNamed "H".
  iDestruct (big_sepM2_lookup_iff with "Hspans") as %Hiff.
  destruct (dm !! client) as [ssl |] eqn:Hdmc.
  - have [sps Hspc] : is_Some (spans !! client) by apply Hiff; eauto.
    iDestruct (big_sepM2_insert_acc _ _ _ client ssl sps Hdmc Hspc with "Hspans") as "[[Hsl Hcap] Hback]".
    iExists dm, sps. rewrite Hdmc /=. iFrame "Hdm Hsl Hcap".
    iIntros (ssl') "Hsl' Hcap' Hdm".
    iDestruct ("Hback" $! ssl' (sps ++ [sp]) with "[$Hsl' $Hcap']") as "Hspans".
    iExists (<[client := ssl']> dm), (<[client := sps ++ [sp]]> spans). iFrame "Hdm Hspans".
    iPureIntro. move=> d. rewrite HD' Hcover.
    have -> : sps = default [] (spans !! client) by rewrite Hspc.
    symmetry. exact (spans_cover_insert spans client sp d).
  - have Hspc : spans !! client = None.
    { destruct (spans !! client) as [sps |] eqn:E; last done.
      exfalso. have Hsome : is_Some (dm !! client) by apply Hiff; eauto.
      rewrite Hdmc in Hsome. destruct Hsome as [? Habs]. discriminate. }
    iExists dm, []. rewrite Hdmc /=. iFrame "Hdm".
    iSplitR; first iApply own_slice_nil. iSplitR; first iApply own_slice_cap_nil.
    iIntros (ssl') "Hsl' Hcap' Hdm".
    iExists (<[client := ssl']> dm), (<[client := [sp]]> spans). iFrame "Hdm".
    iSplitL "Hspans Hsl' Hcap'".
    { rewrite big_sepM2_insert; [| exact Hdmc | exact Hspc]. iFrame "Hspans Hsl' Hcap'". }
    iPureIntro. move=> d. rewrite HD' Hcover.
    have Heq : [sp] = default [] (spans !! client) ++ [sp] by rewrite Hspc.
    rewrite Heq. symmetry. exact (spans_cover_insert spans client sp d).
Qed.

End text_observer_heap.
