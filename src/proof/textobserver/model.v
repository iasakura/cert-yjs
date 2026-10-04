(** The [TextObserver], PURE model layer: the pull observer's token (issue
    #198). The delta itself, its patch law and [snapshot_grows_to] are
    [delta/model], shared with the push observer.

    Definitions
    - [snapshot_state_vector]: the observer's state-vector token (Yjs
      [beforeState], y-octo [last_update]) as a function of the observed
      snapshot; its deleted-ids token is [delta/model]'s
      [snapshot_deleted_ids].

    Laws
    - [state_vector_classifies] / [deleted_ids_classify]: the token tests the
      Go performs are membership in the observed snapshot.
    - the walk's laws: [snapshot_state_vector_app] (a snapshot is walked one
      char at a time) and [snapshot_state_vector_run_models] (the token of
      one run's chars: its client's next clock). *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core network_model.
From New.proof.item Require Import run_theory model.
From New.proof.ytype Require Import model value.
From stdpp Require Import gmap sorting.

From New.proof.delta Require Import model.

Section text_observer_model.

Set Default Proof Using "Type*".

Notation A := go_string.

Local Notation snapshot := (list (YjsItem A * bool)).

(* ===== definitions ======================================================== *)

(** The observer's token: per client, one plus the largest observed clock,
    and the observed tombstoned ids. *)
Definition snapshot_state_vector (observed : snapshot) : gmap ClientId nat :=
  foldr (λ x acc, sv_join {[ clientId (item_id x) := S (clock (item_id x)) ]} acc)
        ∅ observed.*1.

(* ===== lemmas ============================================================= *)

(* ----- the token ----- *)

Lemma snapshot_state_vector_bound (observed : snapshot) (x : YjsItem A) :
  x ∈ observed.*1 ->
  (clock (item_id x) < sv_get (snapshot_state_vector observed) (clientId (item_id x)))%nat.
Proof.
  rewrite /snapshot_state_vector. elim: (observed.*1) => [| y l IH]; first by rewrite elem_of_nil.
  rewrite elem_of_cons /= sv_get_join. move=> [-> | Hin].
  - rewrite /sv_get lookup_singleton_eq /=. lia.
  - have := IH Hin. lia.
Qed.

Lemma snapshot_state_vector_witness (observed : snapshot) (c : ClientId) (k : nat) :
  (k < sv_get (snapshot_state_vector observed) c)%nat ->
  ∃ y, y ∈ observed.*1 ∧ clientId (item_id y) = c ∧ (k <= clock (item_id y))%nat.
Proof.
  rewrite /snapshot_state_vector. elim: (observed.*1) => [| y l IH].
  { rewrite /sv_get lookup_empty /=. lia. }
  rewrite /= sv_get_join. move=> Hlt.
  destruct (decide (k < sv_get {[ clientId (item_id y) := S (clock (item_id y)) ]} c)%nat) as [Hy | Hy].
  - destruct (decide (clientId (item_id y) = c)) as [Heq | Hne].
    + exists y. split_and!; [apply list_elem_of_here | done |].
      move: Hy. rewrite /sv_get Heq lookup_singleton_eq /=. lia.
    + exfalso. move: Hy. rewrite /sv_get lookup_singleton_ne //=. lia.
  - destruct (IH ltac:(lia)) as (y' & Hy' & Hc & Hle).
    exists y'. split_and!; [apply list_elem_of_further, Hy' | done | done].
Qed.

(** The state-vector test the Go performs is membership in the observed
    snapshot (per-client contiguity makes the two agree). *)
Lemma state_vector_classifies (observed current : snapshot) (x : YjsItem A) :
  snapshot_grows_to observed current -> uniqueId current.*1 -> x ∈ current.*1 ->
  (clock (item_id x) < sv_get (snapshot_state_vector observed) (clientId (item_id x)))%nat
    <-> x ∈ observed.*1.
Proof.
  move=> [Hsub [_ Hcontig]] Huniq Hx. split; last exact (snapshot_state_vector_bound observed x).
  move=> Hlt.
  destruct (snapshot_state_vector_witness observed _ _ Hlt) as (y & Hy & Hc & Hle).
  destruct (decide (clock (item_id x) = clock (item_id y))) as [Heq | Hne].
  - have Hy' : y ∈ current.*1 := elem_of_submseteq _ _ _ Hy (sublist_submseteq _ _ Hsub).
    have Hid : item_id x = item_id y.
    { destruct (item_id x) as [cx kx], (item_id y) as [cy ky]. simpl in *. congruence. }
    rewrite (uniqueId_id_eq_implies_eq _ Huniq x y Hx Hy' Hid). exact Hy.
  - apply (Hcontig x y Hx Hy (eq_sym Hc)). lia.
Qed.

(** The delete-set test the Go performs is the tombstone bit of the observed
    snapshot. *)
Lemma deleted_ids_classify (observed : snapshot) (x : YjsItem A) :
  uniqueId observed.*1 -> x ∈ observed.*1 ->
  (x, true) ∈ observed <-> item_id x ∈ snapshot_deleted_ids observed.
Proof.
  move=> Huniq Hx.
  rewrite /snapshot_deleted_ids /char_ids elem_of_list_to_set list_elem_of_fmap. split.
  - move=> Hin. exists x. split; first done.
    rewrite list_elem_of_fmap. exists (x, true). split; first done.
    apply list_elem_of_filter. by split.
  - move=> [y [Hid Hy]].
    rewrite list_elem_of_fmap in Hy. destruct Hy as ([y' b] & -> & Hyb).
    apply list_elem_of_filter in Hyb as [Hb Hyb]. simpl in *. subst b.
    have Hy1 : y' ∈ observed.*1 := elem_of_snapshot_fst _ _ _ Hyb.
    rewrite (uniqueId_id_eq_implies_eq _ Huniq x y' Hx Hy1 Hid). exact Hyb.
Qed.

Lemma snapshot_state_vector_app (m1 m2 : snapshot) :
  snapshot_state_vector (m1 ++ m2) =
  sv_join (snapshot_state_vector m1) (snapshot_state_vector m2).
Proof.
  rewrite /snapshot_state_vector fmap_app.
  elim: m1.*1 => [| x l IH] /=; first by rewrite sv_join_empty_l.
  rewrite IH sv_join_assoc //.
Qed.

(** The token of one run's chars ([run_models r], the per-char sequence of a
    heap node): the run's client is at its next clock and no other client is
    known. *)
Lemma snapshot_state_vector_run_models (r : ItemRun) (c : ClientId) :
  run_wf (run_items r) ->
  sv_get (snapshot_state_vector (run_models r)) c =
    (if decide (c = run_client r) then run_clock r + length (run_items r) else 0)%nat.
Proof.
  move=> Hwf.
  have Hids : ∀ y, y ∈ run_items r ->
      ∃ o, (o < length (run_items r))%nat ∧
           item_id y = MkYjsId (run_client r) (run_clock r + o).
  { move=> y Hy. apply list_elem_of_lookup_1 in Hy as [o Ho].
    exists o. split; [exact (lookup_lt_Some _ _ _ Ho) | exact (run_wf_char_id _ o y Hwf Ho)]. }
  have Hwit : ∀ k, (k < sv_get (snapshot_state_vector (run_models r)) c)%nat ->
      ∃ o, (o < length (run_items r))%nat ∧ c = run_client r ∧ (k <= run_clock r + o)%nat.
  { move=> k Hk.
    destruct (snapshot_state_vector_witness (run_models r) c k Hk) as (y & Hy & Hc & Hle).
    rewrite run_models_fst in Hy.
    destruct (Hids y Hy) as (o & Ho & Hidy).
    rewrite Hidy /= in Hc Hle. exists o. split_and!; [exact Ho | by rewrite Hc | exact Hle]. }
  case_decide as Hc.
  - subst c.
    have Hne : run_items r ≠ [] := proj1 Hwf.
    have Hlen : (0 < length (run_items r))%nat.
    { destruct (run_items r) as [| h l]; [done | simpl; lia]. }
    (* the last char is observed: the bound is reached *)
    destruct (lookup_lt_is_Some_2 (run_items r) (length (run_items r) - 1) ltac:(lia)) as [z Hz].
    have Hzin : z ∈ run_items r := list_elem_of_lookup_2 _ _ _ Hz.
    have Hzid := run_wf_char_id (run_items r) _ z Hwf Hz.
    have Hlow := snapshot_state_vector_bound (run_models r) z ltac:(rewrite run_models_fst; exact Hzin).
    rewrite Hzid /= in Hlow.
    apply Nat.le_antisymm.
    + apply Nat.nlt_ge => Hgt.
      destruct (Hwit _ Hgt) as (o & Ho & _ & Hle). lia.
    + (* [Hlow] spells [run_clock] / [run_client] out; restate it so lia sees one atom *)
      have Hlow' : (run_clock r + (length (run_items r) - 1)
                    < sv_get (snapshot_state_vector (run_models r)) (run_client r))%nat := Hlow.
      lia.
  - apply Nat.le_antisymm; last lia.
    apply Nat.nlt_ge => Hgt.
    destruct (Hwit _ Hgt) as (o & _ & Heq & _). done.
Qed.

End text_observer_model.
