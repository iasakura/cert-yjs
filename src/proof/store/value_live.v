(** The [store] VALUE layer, part 2: the LIVE-CELL REFINEMENT and the
    TOMBSTONE-SET invariant, over the cell bookkeeping of
    [store/value_cells.v].

    Definitions
    - [live_refine]: every live cell of the new pool is covered, chars and
      all, by a live cell of the old one, and [delete_set_tombstoned]: no live cell
      holds an id of the delete set. The pair is what gives the ghost delete
      set its meaning (plan-delete-set.md section 3). Integration breaks
      [live_refine] (it adds a live cell with no ancestor), so it reports the
      weaker [integrate_live_refine] (the escape is "this char is the wire
      item's own"), which the apply loop turns into [apply_live_refine] (the
      escape is "the model did not have this id") with the replay's client
      bound. [dead_chars_kept] is the dual, carrying a delete loop's record of
      what it has already tombstoned across the next iteration's surgeries.
    - [ids_tombstoned]: the ids are held by cells that are tombstoned, what a
      delete reports about what it just did ([ids_tombstoned_runs_of]
      carries it to the projected runs, [ids_tombstoned_of_runs] back).

    Laws
    - a well-formed run denotes exactly its cell's coordinate window
      ([run_wf_char_id_bound] and its converse [run_wf_char_id_mem]), which
      gives store-global id uniqueness out of the pool invariants alone
      ([cells_char_id_unique], via [pool_loc_inj]) and hence the obligation a
      delete must discharge to mint a certificate ([delete_set_tombstoned_char_ids],
      [delete_set_tombstoned_of_witnesses]); [delete_set_tombstoned_runs_of]
      reads it at runs.
    - [live_refine] is reflexive, transitive, and holds of a tombstone flip
      ([live_refine_flip], over the cell-level [flip_pool_perm]) and of a
      cell-preserving permutation; [delete_set_tombstoned] travels along it
      ([delete_set_tombstoned_refine]) and along an integrate splice whose fresh run
      misses the set ([delete_set_tombstoned_snoc]).
    - the same shape for [apply_live_refine] / [integrate_live_refine]
      (reflexivity, transitivity, the splice, and the bridge
      [apply_live_refine_of_integrate]) and for [dead_chars_kept]; at the
      projected runs, [integrate_live_refine] carries over
      ([integrate_live_refine_to_runs]) and [runs_apply_live_refine] reads
      back ([apply_live_refine_of_runs]).

    Sits above [store/value_cells.v] and below [store/value_split.v]. *)

From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core prelude network_model.
From iris.algebra Require Import auth gmap gset.
From stdpp Require Import sorting.
Local Open Scope Z_scope.
From New.proof.store Require Import model value_cells.
From New.proof.id Require Import value heap.
From New.proof.item Require Import run_theory model value heap.
From New.proof.ytype Require Import model value heap.

Section store_value_live.

Set Default Proof Using "Type*".

Notation A := go_string.

Notation P := go_string.

Local Notation TId := (TypeId P).

Local Notation Op := (TId * @YjsOperation A)%type.

Local Notation Ev := (@Event Op).

Local Notation DocModel := (gmap TId (list (YjsItem A))).

(* ===== definitions ======================================================== *)

(* ----- the live-cell refinement and the tombstone-set invariant --------- *)

(** [live_refine types types']: every LIVE (untombstoned) cell of the new pool
    has a LIVE cell of the old pool holding all of its chars. Three of the
    four surgeries the store performs satisfy it: a split's halves inherit the
    node's [ic_deleted] bit and share out its run, a tombstone flip only turns
    bits ON, and registering a type adds no cells. Integration does NOT (it
    adds a live cell with no ancestor); that step re-establishes
    [delete_set_tombstoned] from the new id's freshness instead ([delete_set_tombstoned_snoc]).

    Stated over chars, not coordinates, because the tombstone set is a set of
    [YjsId]s: the coordinate clause of the records below is about where a cell
    sits in its client's clock space, which is the wrong currency here.

    Used as: a conjunct of [split_types_update_rel], [repair_types_update_rel] and
    [delete_types_update_rel], consumed by [delete_set_tombstoned_refine] and its Iris
    wrapper [own_delete_set_refine] to carry the tombstone-set invariant across a
    surgery. Discharged by [split_pool_live_refine], [live_refine_flip] and
    [live_refine_perm]. *)
Definition live_refine (types types' : gmap loc type_state) : Prop :=
  ∀ c', c' ∈ all_cells types' -> ic_deleted c' = false ->
    ∃ c, c ∈ all_cells types ∧ ic_deleted c = false ∧
         (∀ y, y ∈ ic_run c' -> y ∈ ic_run c).

(** [apply_live_refine m pool pool']: the growth-tolerant form of
    [live_refine], which the remote apply path needs because integration adds
    a LIVE cell with no ancestor. Every char of every live cell of the new
    pool either sat in a live cell of the old one, or is an id the model [m]
    did not have at all, i.e. a char this apply just integrated. Both
    disjuncts keep the char out of the delete set: the first by the invariant
    itself, the second by the domain bound (the set only holds ids of [m]).

    Composable across steps against a FIXED [m], the model the apply started
    from: the second disjunct only gets easier as the model grows, so a char
    fresh to a later model is fresh to [m] too.

    Used as: the pool-refinement clause of [wp_store__applyUpdate] and of both
    loops inside it, consumed by [own_delete_set_apply] to carry the tombstone-set
    invariant across a remote apply. Built from
    [apply_live_refine_of_live_refine] on the repair steps and
    [apply_live_refine_of_integrate] on the integrate steps. *)
Definition apply_live_refine (m : DocModel) (pool pool' : list item_cell) : Prop :=
  ∀ c', c' ∈ pool' -> ic_deleted c' = false -> ∀ y, y ∈ ic_run c' ->
    (∃ c, c ∈ pool ∧ ic_deleted c = false ∧ y ∈ ic_run c)
    ∨ doc_model_has m (item_id y) = false.

(** [integrate_live_refine input pool pool']: what one integrate step gives,
    stated without a model so the step itself stays model-agnostic (like the
    coordinate provenance clause next to it). A char of a live cell of the new
    pool either sat in a live cell of the old one, or is one of the integrated
    wire item's own chars, recognised by its client and a clock at or above
    the item's.

    Used as: the pool-refinement clause of [wp_store__integrateDecoded] (and
    its two local cases), which have no model of their own to
    speak about. Their caller, the apply loop in [store/applyUpdate], turns
    the second disjunct into "the model did not have this id" with the
    replay's client bound ([apply_live_refine_of_integrate]). *)
Definition integrate_live_refine (input : IntegrateInput (A := A))
    (pool pool' : list item_cell) : Prop :=
  ∀ c', c' ∈ pool' -> ic_deleted c' = false -> ∀ y, y ∈ ic_run c' ->
    (∃ c, c ∈ pool ∧ ic_deleted c = false ∧ y ∈ ic_run c)
    ∨ (clientId (item_id y) = clientId (in_id input) ∧
       (clock (in_id input) <= clock (item_id y))%nat).

(** [dead_chars_kept types types']: every char of a TOMBSTONED cell of the old
    pool is still held by a tombstoned cell of the new one. The dual of
    [live_refine], which says the same about live cells.

    Used as: a conjunct of [split_types_update_rel] and [delete_types_update_rel], so a
    delete loop can carry its "everything covered so far is tombstoned"
    record ([ids_tombstoned]) across the split and flip the next iteration
    performs. Discharged by [split_pool_dead_chars_kept] and
    [dead_chars_kept_flip], since a split's halves inherit the bit and
    partition the run, and a flip only turns bits on. *)
Definition dead_chars_kept (types types' : gmap loc type_state) : Prop :=
  ∀ c, c ∈ all_cells types -> ic_deleted c = true -> ∀ y, y ∈ ic_run c ->
    ∃ c', c' ∈ all_cells types' ∧ ic_deleted c' = true ∧ y ∈ ic_run c'.

(** [delete_set_tombstoned delete_set pool]: the pool conforms to the set. An
    id in [delete_set] that a pool cell holds forces that cell tombstoned.

    This is the direction of #37's [deleted_match] that gives the delete set
    its MEANING: without it an [is_delete_set_lb] certificate is a receipt any
    implementation could mint, including one whose [Delete] does nothing. With
    it, the certificate says the ids are gone from every live node, hence from
    the visible document a reader observes (issue #125).

    Note the premise "that a pool cell holds": this says nothing about an id
    that occurs in NO cell, so it is not a domain bound and does not subsume
    [delete_set_dom]. The two clauses face opposite ways, and [own_delete_set]
    carries both for that reason.

    The converse (every tombstoned char is recorded in [delete_set]) is
    deliberately NOT carried: nothing consumes it, and it would force every
    delete to grow the ghost set eagerly, which is exactly the bookkeeping
    y-octo's [delete_item_inner] does and ours does not. *)
Definition delete_set_tombstoned (delete_set : gset YjsId) (pool : list item_cell) : Prop :=
  ∀ c, c ∈ pool -> ∀ y, y ∈ ic_run c -> item_id y ∈ delete_set -> ic_deleted c = true.

(** [ids_tombstoned ids pool]: every id of [ids] is held by a cell of [pool]
    that is tombstoned. It WITNESSES the ids as present and dead, which is
    strictly more than [delete_set_tombstoned], which only forbids them from
    being present and alive; store-global id uniqueness turns this into that
    ([delete_set_tombstoned_of_witnesses]).

    Used as: what a delete reports about what it just did. It is the
    postcondition of [wp_store__deleteRange] (over the range it was asked to
    cover) and of [wp_store__applyDeleteSpans_runs] (over the union of the spans
    that landed), it is carried through the latter's loop, and it is the
    premise a caller discharges to mint an [is_delete_set_lb] certificate
    through [own_delete_set_grow]. *)
Definition ids_tombstoned (ids : gset YjsId) (pool : list item_cell) : Prop :=
  ∀ i, i ∈ ids -> ∃ c, c ∈ pool ∧ ic_deleted c = true ∧ i ∈ char_ids (ic_run c).

(* ===== lemmas ============================================================= *)

(** A well-formed run's chars all carry the head's client and a clock at or
    above the head's: [run_wf] makes the run one client's consecutive clocks
    starting at the head ([run_wf_lookup_clock]). This is what turns a cell's
    coordinates into a statement about its chars' ids. *)
Lemma run_wf_char_id_bound (c : item_cell) (y : YjsItem A) :
  run_wf (ic_run c) -> y ∈ ic_run c ->
  clientId (item_id y) = clientId (item_id (run_head c)) ∧
  (clock (item_id (run_head c)) <= clock (item_id y) <
     clock (item_id (run_head c)) + length (ic_run c))%nat.
Proof.
  move=> Hwf Hy.
  have Hne : ic_run c ≠ [] by (move: Hwf => [Hne _]; exact Hne).
  have Hhd : ic_run c !! 0%nat = Some (run_head c).
  { rewrite /run_head. by destruct (ic_run c). }
  apply list_elem_of_lookup_1 in Hy as [o Ho].
  have Holt : (o < length (ic_run c))%nat := lookup_lt_Some _ _ _ Ho.
  rewrite (run_wf_lookup_clock (ic_run c) o (run_head c) y Hwf Hhd Ho) /=.
  split; [reflexivity | lia].
Qed.

(** The converse: every id in a run's client/clock window IS one of its chars.
    Together with [run_wf_char_id_bound] this says a run denotes exactly its
    coordinate window, which is what lets a delete loop turn "this node is
    tombstoned" into "these span ids are tombstoned". *)
Lemma run_wf_char_id_mem (c : item_cell) (i : YjsId) :
  run_wf (ic_run c) ->
  clientId i = clientId (item_id (run_head c)) ->
  (clock (item_id (run_head c)) <= clock i <
     clock (item_id (run_head c)) + length (ic_run c))%nat ->
  i ∈ char_ids (ic_run c).
Proof.
  move=> Hwf Hcl [Hlo Hhi].
  have Hhd : ic_run c !! 0%nat = Some (run_head c).
  { rewrite /run_head. move: Hwf => [Hne _]. by destruct (ic_run c). }
  set (o := (clock i - clock (item_id (run_head c)))%nat).
  have [y Hy] : is_Some (ic_run c !! o).
  { apply lookup_lt_is_Some. rewrite /o. lia. }
  have Hid := run_wf_lookup_clock (ic_run c) o (run_head c) y Hwf Hhd Hy.
  rewrite /char_ids elem_of_list_to_set list_elem_of_fmap.
  exists y. split; last exact (list_elem_of_lookup_2 _ _ _ Hy).
  rewrite Hid. destruct i as [ci ki]. simpl in *. rewrite /o. f_equal; lia.
Qed.

(** Locations identify pooled cells ([NoDup] of the pool's locations is one of
    the pool invariants), which is what lets a cell-level disjointness
    hypothesis be applied to two cells known to differ. *)
Lemma pool_loc_inj (pool : list item_cell) (c1 c2 : item_cell) :
  NoDup (ic_loc <$> pool) -> c1 ∈ pool -> c2 ∈ pool ->
  ic_loc c1 = ic_loc c2 -> c1 = c2.
Proof.
  move=> Hnd Hc1 Hc2 Heq.
  apply list_elem_of_lookup_1 in Hc1 as [i Hi].
  apply list_elem_of_lookup_1 in Hc2 as [j Hj].
  have Hij : i = j.
  { apply (NoDup_lookup (ic_loc <$> pool) i j (ic_loc c1) Hnd).
    - rewrite list_lookup_fmap Hi //.
    - rewrite list_lookup_fmap Hj /= Heq //. }
  subst j. rewrite Hi in Hj. by injection Hj.
Qed.

(** Store-global id uniqueness, out of the pool invariants alone: two cells at
    different locations never share a char id. Same client puts their clock
    ranges apart ([cells_range_disjoint]) and a run's chars sit exactly inside
    its own cell's range, with [cell_fits] keeping the [w64] coordinates
    honest; different clients differ in the id's client field outright.

    This is the fact docs/plan-delete-set.md expected to need real plumbing
    ("store-global id uniqueness"): the pool invariants already carry it. *)
Lemma cells_char_id_unique (pool : list item_cell) (c1 c2 : item_cell)
    (y1 y2 : YjsItem A) :
  cells_range_disjoint pool ->
  (∀ c, c ∈ pool -> run_wf (ic_run c)) ->
  (∀ c, c ∈ pool -> (Z.of_nat (clock (item_id (run_head c))) < 2^64)%Z) ->
  c1 ∈ pool -> c2 ∈ pool -> ic_loc c1 ≠ ic_loc c2 ->
  y1 ∈ ic_run c1 -> y2 ∈ ic_run c2 -> item_id y1 ≠ item_id y2.
Proof.
  move=> Hdisj Hwf Hclkb Hc1 Hc2 Hloc Hy1 Hy2 Hideq.
  have [Hcl1 Hrg1] := run_wf_char_id_bound c1 y1 (Hwf c1 Hc1) Hy1.
  have [Hcl2 Hrg2] := run_wf_char_id_bound c2 y2 (Hwf c2 Hc2) Hy2.
  have Hclheads : clientId (item_id (run_head c1)) = clientId (item_id (run_head c2)).
  { rewrite -Hcl1 -Hcl2 Hideq //. }
  have Hccells : cell_client c1 = cell_client c2
    by rewrite /cell_client Hclheads.
  have Hb1 := Hclkb c1 Hc1. have Hb2 := Hclkb c2 Hc2.
  have Hz1 : uint.Z (cell_clock c1) = Z.of_nat (clock (item_id (run_head c1)))
    by (rewrite /cell_clock; word).
  have Hz2 : uint.Z (cell_clock c2) = Z.of_nat (clock (item_id (run_head c2)))
    by (rewrite /cell_clock; word).
  have Hclk : clock (item_id y1) = clock (item_id y2) by rewrite Hideq.
  destruct (Hdisj c1 c2 Hc1 Hc2 Hccells Hloc) as [Hle | Hle]; lia.
Qed.

Lemma dead_chars_kept_flip (types : gmap loc type_state) (p : loc)
    (ts : type_state) (k : nat) (c : item_cell) :
  types !! p = Some ts -> ty_cells ts !! k = Some c ->
  dead_chars_kept types
    (<[p := MkTypeState (<[k := flip_cell c]> (ty_cells ts)) (ty_arr ts)]> types).
Proof.
  move=> Hp Hck.
  destruct (flip_pool_perm types p ts k c Hp Hck) as (rest & Hold & Hnew).
  move=> c0 Hc0 Hdel y Hy. rewrite Hold in Hc0.
  apply elem_of_cons in Hc0 as [-> | Hc0].
  - exists (flip_cell c). split_and!;
      [rewrite Hnew; apply list_elem_of_here | done | exact Hy].
  - exists c0. split_and!;
      [rewrite Hnew; apply elem_of_cons; by right | exact Hdel | exact Hy].
Qed.

Lemma live_refine_flip (types : gmap loc type_state) (p : loc)
    (ts : type_state) (k : nat) (c : item_cell) :
  types !! p = Some ts -> ty_cells ts !! k = Some c ->
  live_refine types
    (<[p := MkTypeState (<[k := flip_cell c]> (ty_cells ts)) (ty_arr ts)]> types).
Proof.
  move=> Hp Hck.
  destruct (flip_pool_perm types p ts k c Hp Hck) as (rest & Hold & Hnew).
  move=> c' Hc' Hlive. rewrite Hnew in Hc'.
  apply elem_of_cons in Hc' as [-> | Hc'].
  { by rewrite /flip_cell /= in Hlive. }
  exists c'. split_and!; [rewrite Hold; by apply elem_of_cons; right | exact Hlive | done].
Qed.

Lemma live_refine_refl (types : gmap loc type_state) : live_refine types types.
Proof. move=> c' Hc' Hlive. exists c'. split_and!; [exact Hc' | exact Hlive | done]. Qed.

Lemma live_refine_trans (t1 t2 t3 : gmap loc type_state) :
  live_refine t1 t2 -> live_refine t2 t3 -> live_refine t1 t3.
Proof.
  move=> H12 H23 c3 Hc3 Hlive3.
  destruct (H23 c3 Hc3 Hlive3) as (c2 & Hc2 & Hlive2 & Hrun2).
  destruct (H12 c2 Hc2 Hlive2) as (c1 & Hc1 & Hlive1 & Hrun1).
  exists c1. split_and!; [exact Hc1 | exact Hlive1 |].
  move=> y Hy. exact (Hrun1 y (Hrun2 y Hy)).
Qed.

(** Registering a fresh empty type moves no cells. *)
Lemma live_refine_perm (types types' : gmap loc type_state) :
  all_cells types' ≡ₚ all_cells types -> live_refine types types'.
Proof.
  move=> Hperm c' Hc' Hlive. exists c'.
  split_and!; [by rewrite -Hperm | exact Hlive | done].
Qed.

(** The tombstone-set invariant travels forward along any of the three
    surgeries, since each of them only ever shrinks the live chars. *)
Lemma delete_set_tombstoned_refine (delete_set : gset YjsId) (types types' : gmap loc type_state) :
  live_refine types types' ->
  delete_set_tombstoned delete_set (all_cells types) -> delete_set_tombstoned delete_set (all_cells types').
Proof.
  move=> Hlr Htomb c' Hc' y Hy Hin.
  destruct (ic_deleted c') eqn:Hlive; first done.
  destruct (Hlr c' Hc' Hlive) as (c & Hc & Hlivec & Hrun).
  by rewrite (Htomb c Hc y (Hrun y Hy) Hin) in Hlivec.
Qed.

Lemma delete_set_tombstoned_perm (delete_set : gset YjsId) (pool pool' : list item_cell) :
  pool' ≡ₚ pool -> delete_set_tombstoned delete_set pool -> delete_set_tombstoned delete_set pool'.
Proof. move=> Hperm Htomb c Hc. apply Htomb. by rewrite -Hperm. Qed.

(** Integration is the one step with no live ancestor for its new cell: the
    fresh run's ids must be outside the set, which is where the domain bound
    [delete_set_dom] plus the id's freshness comes in (see [store/heap.v]). *)
Lemma delete_set_tombstoned_snoc (delete_set : gset YjsId) (pool pool' : list item_cell)
    (c : item_cell) :
  pool' ≡ₚ pool ++ [c] ->
  delete_set_tombstoned delete_set pool ->
  (∀ y, y ∈ ic_run c -> item_id y ∉ delete_set) ->
  delete_set_tombstoned delete_set pool'.
Proof.
  move=> Hperm Htomb Hfresh c0 Hc0. rewrite Hperm in Hc0.
  apply elem_of_app in Hc0 as [Hc0 | Hc0].
  - exact (Htomb c0 Hc0).
  - apply list_elem_of_singleton in Hc0 as ->.
    move=> y Hy Hin. exfalso. exact (Hfresh y Hy Hin).
Qed.

(** Growing the set: the new ids must miss every live cell. This is the
    obligation a delete discharges to mint its [is_delete_set_lb] certificate. *)
Lemma delete_set_tombstoned_union (delete_set S : gset YjsId) (pool : list item_cell) :
  delete_set_tombstoned delete_set pool -> delete_set_tombstoned S pool -> delete_set_tombstoned (delete_set ∪ S) pool.
Proof.
  move=> Htomb HS c Hc y Hy /elem_of_union [Hin | Hin];
    [exact (Htomb c Hc y Hy Hin) | exact (HS c Hc y Hy Hin)].
Qed.

(** A tombstoned cell's chars are gone from every LIVE cell of the pool: they
    are gone from every OTHER cell by id uniqueness, and the cell itself is
    not live. This is the obligation [own_delete_set_grow] puts on a delete before it
    hands out an [is_delete_set_lb] certificate. *)
(** The general form: a set every one of whose ids is witnessed by SOME
    tombstoned cell of the pool is absent from every live cell, by
    [cells_char_id_unique]. This is the obligation [own_delete_set_grow] puts on a
    delete, discharged from the pool invariants and the delete's own record of
    what it tombstoned. *)
Lemma delete_set_tombstoned_of_witnesses (pool : list item_cell) (D : gset YjsId) :
  cells_range_disjoint pool ->
  (∀ c0, c0 ∈ pool -> run_wf (ic_run c0)) ->
  (∀ c0, c0 ∈ pool -> (Z.of_nat (clock (item_id (run_head c0))) < 2^64)%Z) ->
  NoDup (ic_loc <$> pool) ->
  ids_tombstoned D pool ->
  delete_set_tombstoned D pool.
Proof.
  move=> Hdisj Hwf Hclkb Hnd Hwit c0 Hc0 y Hy Hin.
  destruct (ic_deleted c0) eqn:Hlive; first done. exfalso.
  destruct (Hwit (item_id y) Hin) as (c & Hc & Hdel & Hz).
  rewrite /char_ids elem_of_list_to_set list_elem_of_fmap in Hz.
  destruct Hz as (z & Hidz & Hz).
  have Hne : ic_loc c0 ≠ ic_loc c.
  { move=> Hloc. have Heqc := pool_loc_inj pool c0 c Hnd Hc0 Hc Hloc.
    subst c0. by rewrite Hdel in Hlive. }
  exact (cells_char_id_unique pool c0 c y z Hdisj Hwf Hclkb Hc0 Hc Hne Hy Hz Hidz).
Qed.

Lemma delete_set_tombstoned_char_ids (pool : list item_cell) (c : item_cell) :
  cells_range_disjoint pool ->
  (∀ c0, c0 ∈ pool -> run_wf (ic_run c0)) ->
  (∀ c0, c0 ∈ pool -> (Z.of_nat (clock (item_id (run_head c0))) < 2^64)%Z) ->
  NoDup (ic_loc <$> pool) ->
  c ∈ pool -> ic_deleted c = true ->
  delete_set_tombstoned (char_ids (ic_run c)) pool.
Proof.
  move=> Hdisj Hwf Hclkb Hnd Hc Hdel c0 Hc0 y Hy Hin.
  destruct (ic_deleted c0) eqn:Hlive; first done. exfalso.
  rewrite /char_ids elem_of_list_to_set list_elem_of_fmap in Hin.
  destruct Hin as (z & Hidz & Hz).
  have Hne : ic_loc c0 ≠ ic_loc c.
  { move=> Hloc. have Heqc := pool_loc_inj pool c0 c Hnd Hc0 Hc Hloc.
    subst c0. by rewrite Hdel in Hlive. }
  exact (cells_char_id_unique pool c0 c y z Hdisj Hwf Hclkb Hc0 Hc Hne Hy Hz
           Hidz).
Qed.

Lemma delete_set_tombstoned_mono (delete_set delete_set' : gset YjsId) (pool : list item_cell) :
  delete_set' ⊆ delete_set -> delete_set_tombstoned delete_set pool -> delete_set_tombstoned delete_set' pool.
Proof. move=> Hsub Htomb c Hc y Hy Hin. exact (Htomb c Hc y Hy (Hsub _ Hin)). Qed.

(** [delete_set_tombstoned] is its run form over the cells' runs. *)
Lemma delete_set_tombstoned_runs_of (delete_set : gset YjsId) (pool : list item_cell) :
  delete_set_tombstoned delete_set pool <-> delete_set_tombstoned_runs delete_set (cell_run <$> pool).
Proof.
  split.
  - move=> Ht r Hr y Hy Hd. apply list_elem_of_fmap in Hr as (c & -> & Hc). exact (Ht c Hc y Hy Hd).
  - move=> Ht c Hc y Hy Hd. exact (Ht (cell_run c) (list_elem_of_fmap_2 _ _ _ Hc) y Hy Hd).
Qed.

Lemma apply_live_refine_refl (m : DocModel) (pool : list item_cell) :
  apply_live_refine m pool pool.
Proof. move=> c' Hc' Hlive y Hy. left. by exists c'. Qed.

Lemma apply_live_refine_of_live_refine (m : DocModel) (types types' : gmap loc type_state) :
  live_refine types types' ->
  apply_live_refine m (all_cells types) (all_cells types').
Proof.
  move=> Hlr c' Hc' Hlive y Hy. left.
  destruct (Hlr c' Hc' Hlive) as (c & Hc & Hlivec & Hrun).
  exists c. split_and!; [exact Hc | exact Hlivec | exact (Hrun y Hy)].
Qed.

(** Composition: the middle step is stated against the LATER model, and its
    freshness disjunct transfers to [m] because the model only grew. *)
Lemma apply_live_refine_trans (m m1 : DocModel) (pool pool1 pool2 : list item_cell) :
  (∀ i, doc_model_has m i = true -> doc_model_has m1 i = true) ->
  apply_live_refine m pool pool1 ->
  apply_live_refine m1 pool1 pool2 ->
  apply_live_refine m pool pool2.
Proof.
  move=> Hmono H01 H12 c2 Hc2 Hlive2 y Hy.
  destruct (H12 c2 Hc2 Hlive2 y Hy) as [(c1 & Hc1 & Hlive1 & Hy1) | Hfresh1].
  - exact (H01 c1 Hc1 Hlive1 y Hy1).
  - right. destruct (doc_model_has m (item_id y)) eqn:Hh; last done.
    by rewrite (Hmono _ Hh) in Hfresh1.
Qed.

(** The integrate splice: the pool grows by one live cell whose chars the
    model does not have yet. *)
Lemma apply_live_refine_snoc (m : DocModel) (pool pool' : list item_cell)
    (c : item_cell) :
  pool' ≡ₚ pool ++ [c] ->
  (∀ y, y ∈ ic_run c -> doc_model_has m (item_id y) = false) ->
  apply_live_refine m pool pool'.
Proof.
  move=> Hperm Hfresh c' Hc' Hlive y Hy. rewrite Hperm in Hc'.
  apply elem_of_app in Hc' as [Hc' | Hc'].
  - left. by exists c'.
  - apply list_elem_of_singleton in Hc' as ->. right. exact (Hfresh y Hy).
Qed.

Lemma integrate_live_refine_of_live_refine (input : IntegrateInput (A := A))
    (types types' : gmap loc type_state) :
  live_refine types types' ->
  integrate_live_refine input (all_cells types) (all_cells types').
Proof.
  move=> Hlr c' Hc' Hlive y Hy. left.
  destruct (Hlr c' Hc' Hlive) as (c & Hc & Hlivec & Hrun).
  exists c. split_and!; [exact Hc | exact Hlivec | exact (Hrun y Hy)].
Qed.

Lemma integrate_live_refine_trans (input : IntegrateInput (A := A))
    (pool pool1 pool2 : list item_cell) :
  integrate_live_refine input pool pool1 ->
  integrate_live_refine input pool1 pool2 ->
  integrate_live_refine input pool pool2.
Proof.
  move=> H01 H12 c2 Hc2 Hlive2 y Hy.
  destruct (H12 c2 Hc2 Hlive2 y Hy) as [(c1 & Hc1 & Hlive1 & Hy1) | Hnew]; last by right.
  exact (H01 c1 Hc1 Hlive1 y Hy1).
Qed.

(** The splice itself: the pool grows by one cell all of whose chars carry the
    integrated item's client and a clock at or above its own. That is read off
    the cell's coordinates ([cell_client] / [cell_clock]) plus the run's own
    well-formedness, which is why the caller passes [run_wf]. *)
Lemma integrate_live_refine_snoc (input : IntegrateInput (A := A))
    (pool pool' : list item_cell) (c : item_cell) :
  pool' ≡ₚ pool ++ [c] ->
  (∀ y, y ∈ ic_run c -> clientId (item_id y) = clientId (in_id input) ∧
     (clock (in_id input) <= clock (item_id y))%nat) ->
  integrate_live_refine input pool pool'.
Proof.
  move=> Hperm Hnew c' Hc' Hlive y Hy. rewrite Hperm in Hc'.
  apply elem_of_app in Hc' as [Hc' | Hc'].
  - left. by exists c'.
  - apply list_elem_of_singleton in Hc' as ->. right. exact (Hnew y Hy).
Qed.

(** The bridge the apply loop uses: an integrate step's second disjunct (the
    char carries the wire item's client and a clock at or above its own) is
    exactly freshness against the model, because the replay's [VR_cons] bound
    puts every same-client item of the model strictly below the item's clock. *)
Lemma apply_live_refine_of_integrate (input : IntegrateInput (A := A))
    (mc : DocModel) (pool pool' : list item_cell) :
  (∀ (t' : TId) x, x ∈ doc_model_get mc t' ->
     clientId (item_id x) = clientId (in_id input) ->
     (clock (item_id x) < clock (in_id input))%nat) ->
  integrate_live_refine input pool pool' ->
  apply_live_refine mc pool pool'.
Proof.
  move=> Hbound Hilr c' Hc' Hlive y Hy.
  destruct (Hilr c' Hc' Hlive y Hy) as [Hold | [Hcl Hlo]]; first by left.
  right. destruct (doc_model_has mc (item_id y)) eqn:Hh; last done.
  exfalso. apply docm_has_spec in Hh as (t' & x & Hx & Hid).
  have Hcx : clientId (item_id x) = clientId (in_id input) by rewrite Hid.
  have := Hbound t' x Hx Hcx. rewrite Hid. lia.
Qed.

Lemma dead_chars_kept_refl (types : gmap loc type_state) : dead_chars_kept types types.
Proof. move=> c Hc Hdel y Hy. exists c. split_and!; done. Qed.

Lemma dead_chars_kept_trans (t1 t2 t3 : gmap loc type_state) :
  dead_chars_kept t1 t2 -> dead_chars_kept t2 t3 -> dead_chars_kept t1 t3.
Proof.
  move=> H12 H23 c1 Hc1 Hdel1 y Hy.
  destruct (H12 c1 Hc1 Hdel1 y Hy) as (c2 & Hc2 & Hdel2 & Hy2).
  exact (H23 c2 Hc2 Hdel2 y Hy2).
Qed.

Lemma dead_chars_kept_perm (types types' : gmap loc type_state) :
  all_cells types' ≡ₚ all_cells types -> dead_chars_kept types types'.
Proof.
  move=> Hperm c Hc Hdel y Hy. exists c. split_and!; [by rewrite Hperm | exact Hdel | exact Hy].
Qed.

(** [ids_tombstoned] carried to the projected runs: what carries the delete
    path's coverage record to the run-granular specs
    ([wp_store__deleteRange_runs] / [wp_store__applyDeleteSpans_runs]). *)
Lemma ids_tombstoned_runs_of (ids : gset YjsId) (pool : list item_cell) :
  ids_tombstoned ids pool ->
  ids_tombstoned_runs ids (cell_run <$> pool).
Proof.
  move=> H i Hi. destruct (H i Hi) as (c & Hc & Hdel & Hin).
  exists (cell_run c). split_and!.
  - apply list_elem_of_fmap_2. exact Hc.
  - rewrite /cell_run /= Hdel //.
  - exact Hin.
Qed.

(** ...and read back: the converse, for the cell-level delete specs derived
    from the run-granular proofs. *)
Lemma ids_tombstoned_of_runs (ids : gset YjsId) (pool : list item_cell) :
  ids_tombstoned_runs ids (cell_run <$> pool) ->
  ids_tombstoned ids pool.
Proof.
  move=> H i Hi. destruct (H i Hi) as (r & Hr & Hdel & Hin).
  apply list_elem_of_fmap in Hr as (c & -> & Hc).
  exists c. split_and!; [exact Hc | exact Hdel | exact Hin].
Qed.

(** The live-refinement records at the projected runs and back:
    [integrate_live_refine] carries to [runs_integrate_live_refine] (what
    derives [wp_store__integrateDecoded_runs]), and [runs_apply_live_refine]
    reads back as [apply_live_refine] (what the [own_store] form of
    [applyUpdate] hands to [own_delete_set_apply]). *)
Lemma integrate_live_refine_to_runs (input : IntegrateInput (A := A))
    (before after : list item_cell) :
  integrate_live_refine input before after ->
  runs_integrate_live_refine input (cell_run <$> before) (cell_run <$> after).
Proof.
  move=> H r' Hr' Hlive y Hy.
  apply list_elem_of_fmap in Hr' as (c' & -> & Hc').
  destruct (H c' Hc' Hlive y Hy) as [(c & Hc & Hlivec & Hyc) | Hown]; [left | by right].
  exists (cell_run c). split_and!; [apply list_elem_of_fmap; eauto | exact Hlivec | exact Hyc].
Qed.

Lemma apply_live_refine_of_runs (m : DocModel) (before after : list item_cell) :
  runs_apply_live_refine m (cell_run <$> before) (cell_run <$> after) ->
  apply_live_refine m before after.
Proof.
  move=> H c' Hc' Hlive y Hy.
  have Hr' : cell_run c' ∈ cell_run <$> after by (apply list_elem_of_fmap; eauto).
  destruct (H (cell_run c') Hr' Hlive y Hy) as [(r & Hr & Hliver & Hyr) | Hfresh]; [left | by right].
  apply list_elem_of_fmap in Hr as (c & -> & Hc).
  exists c. split_and!; [exact Hc | exact Hliver | exact Hyr].
Qed.

End store_value_live.
