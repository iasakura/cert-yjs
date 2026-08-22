(** The [store] VALUE layer, part 3: the SPLIT SURGERY on abstract cells and
    the per-step transport records, over [store/value_cells.v] and
    [store/value_live.v].

    Definitions
    - the split surgery [split_cell_left] / [split_cell_right] / [split_cells].
    - the records one store step hands its caller: [split_types_update_rel] (one
      [splitNode]), [repair_types_update_rel] (the at-most-two splits of [repair])
      and [delete_types_update_rel] (the unbounded split-and-tombstone loop of the
      wire delete path).

    Laws
    - splitting a node is invisible to the model: [split_cells_flatten] and
      [split_cells_num_visible].
    - [delete_types_update_rel] is reflexive and transitive (which is what lets the
      delete loop compose one record per step), and is implied by a split step
      ([delete_types_update_rel_of_split]) and by a tombstone flip
      ([delete_types_update_rel_of_flip]).

    Sits above [store/value_cells.v] and [store/value_live.v]. *)

From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core prelude network_model.
From iris.algebra Require Import auth gmap gset.
From stdpp Require Import sorting.
Local Open Scope Z_scope.
From New.proof.store Require Import model value_cells value_live.
From New.proof.id Require Import value heap.
From New.proof.item Require Import run_theory model value heap.
From New.proof.ytype Require Import model value heap.

Section store_value_split.

Set Default Proof Using "Type*".

Notation A := go_string.

Notation P := go_string.

Local Notation TId := (TypeId P).

Local Notation Op := (TId * @YjsOperation A)%type.

Local Notation Ev := (@Event Op).

Local Notation DocModel := (gmap TId (list (YjsItem A))).

(* ===== definitions ======================================================== *)

(* ===== the split surgery on abstract cells (issue #28 M2) ================
   Splitting a run node is pure cell surgery: the left half keeps the node
   location and the first [o] model items, the right half is a fresh node
   carrying the rest, and BOTH halves inherit the deleted bit and parent (the
   yjs splitItem semantics; y-octo drops the right half's flags, a reported
   divergence). The flatten and the visible count are unchanged, which is why
   every public predicate is invariant under splits. *)

Definition split_cell_left (c : item_cell) (o : nat) : item_cell :=
  MkItemCell (ic_loc c) (take o (ic_run c)) (ic_deleted c) (ic_parent c).

Definition split_cell_right (c : item_cell) (o : nat) (r_loc : loc) : item_cell :=
  MkItemCell r_loc (drop o (ic_run c)) (ic_deleted c) (ic_parent c).

Definition split_cells (cells : list item_cell) (k o : nat) (r_loc : loc) : list item_cell :=
  match cells !! k with
  | Some c => take k cells ++ [split_cell_left c o; split_cell_right c o r_loc] ++ drop (S k) cells
  | None => cells
  end.

(** [split_types_update_rel before after w]: what one [splitNode] step does to
    the type map, as everything a caller is told about the two maps. The
    clauses are of mixed character on purpose, because re-establishing the
    store invariant needs all of them: each type's model list and flattened
    run survive, no type disappears, one client's run list grows by at most
    one, cells away from the split location survive verbatim, a covered clock
    stays covered (with provenance for the two halves), a type of unit cells
    is untouched, every new cell sits inside an old one's range, and the live
    and dead chars refine ([live_refine] / [dead_chars_kept]).

    Used as: the postcondition of [wp_store__splitAtAndGetLeft_inv] and
    [wp_store__splitAtAndGetRight_inv], composed by [repair] into
    [repair_types_update_rel] and weakened by the delete loop into
    [delete_types_update_rel]. *)
Definition split_types_update_rel (before after : gmap loc type_state) (w : item_cell) : Prop :=
  (∀ p ts', after !! p = Some ts' ->
     ∃ ts, before !! p = Some ts ∧ ty_arr ts' = ty_arr ts ∧
           run_flatten (ty_cells ts') = run_flatten (ty_cells ts)) ∧
  (∀ p, is_Some (before !! p) -> is_Some (after !! p)) ∧
  (∀ kc, (length (client_run after kc) <= S (length (client_run before kc)))%nat) ∧
  (∀ c, c ∈ all_cells before -> ic_loc c ≠ ic_loc w -> c ∈ all_cells after) ∧
  (∀ (ccl : w64) (clkZ : Z) (c : item_cell), c ∈ all_cells before ->
     cell_client c = ccl -> (uint.Z (cell_clock c) <= clkZ)%Z ->
     (clkZ < uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)))%Z ->
     ∃ c', c' ∈ all_cells after ∧ cell_client c' = ccl ∧
           (uint.Z (cell_clock c') <= clkZ)%Z ∧
           (clkZ < uint.Z (cell_clock c') + Z.of_nat (length (ic_run c')))%Z ∧
           ic_parent c' = ic_parent c ∧
           (c' = c ∨ (c = w ∧ (1 < length (ic_run w))%nat ∧
                      (ic_loc c' = ic_loc w ∨
                       ic_loc c' ∉ (ic_loc <$> all_cells before))))) ∧
  (∀ p ts ts', before !! p = Some ts -> after !! p = Some ts' ->
     Forall cell_unit (ty_cells ts) -> ts' = ts) ∧
  (∀ c', c' ∈ all_cells after -> ∃ c, c ∈ all_cells before ∧
     cell_client c' = cell_client c ∧
     (uint.Z (cell_clock c) <= uint.Z (cell_clock c'))%Z ∧
     (uint.Z (cell_clock c') + Z.of_nat (length (ic_run c')) <=
      uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)))%Z) ∧
  live_refine before after ∧
  dead_chars_kept before after.

(** [repair_types_update_rel before after]: what [store.repair] does to the type
    map. The same shape as [split_types_update_rel] minus the clauses about a
    single split location, since repair performs up to two of them: each
    client's run list therefore grows by at most two.

    Used as: the postcondition of [wp_store__repair_split], consumed by
    [store/applyUpdate] to carry the pool invariants across the origin
    resolution. *)
Definition repair_types_update_rel (before after : gmap loc type_state) : Prop :=
  (∀ p ts', after !! p = Some ts' ->
     ∃ ts, before !! p = Some ts ∧ ty_arr ts' = ty_arr ts ∧
           run_flatten (ty_cells ts') = run_flatten (ty_cells ts)) ∧
  (∀ p, is_Some (before !! p) -> is_Some (after !! p)) ∧
  (∀ kc, (length (client_run after kc) <= 2 + length (client_run before kc))%nat) ∧
  (∀ p ts ts', before !! p = Some ts -> after !! p = Some ts' ->
     Forall cell_unit (ty_cells ts) -> ts' = ts) ∧
  (∀ c', c' ∈ all_cells after -> ∃ c, c ∈ all_cells before ∧
     cell_client c' = cell_client c ∧
     (uint.Z (cell_clock c) <= uint.Z (cell_clock c'))%Z ∧
     (uint.Z (cell_clock c') + Z.of_nat (length (ic_run c')) <=
      uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)))%Z) ∧
  live_refine before after.

(** [delete_types_update_rel before after]: what the wire delete path does to the
    type map (issue #133). Both surgeries it performs, a split and a
    tombstone, are model no-ops, so the per-type model lists are untouched and
    no type disappears; the live chars only shrink and the dead ones stay dead
    ([live_refine] / [dead_chars_kept]).

    It carries NO run-length bound, unlike the two above, because the delete
    loop splits an unbounded number of times. That is also what makes it
    TRANSITIVE, which is what lets the loop compose one of these per iteration
    instead of tracking the whole surgery at once.

    Used as: the postcondition of [wp_store__deleteRange] and
    [wp_store__applyDeleteSpans], and the source of the [dead_chars_kept] step
    the delete loop needs to carry its coverage record forward. *)
Definition delete_types_update_rel (before after : gmap loc type_state) : Prop :=
  (∀ p ts', after !! p = Some ts' ->
     ∃ ts, before !! p = Some ts ∧ ty_arr ts' = ty_arr ts) ∧
  (∀ p, is_Some (before !! p) -> is_Some (after !! p)) ∧
  live_refine before after ∧
  dead_chars_kept before after ∧
  (∀ c', c' ∈ all_cells after -> ∃ c, c ∈ all_cells before ∧
     cell_client c' = cell_client c ∧
     (uint.Z (cell_clock c) <= uint.Z (cell_clock c'))%Z ∧
     (uint.Z (cell_clock c') + Z.of_nat (length (ic_run c'))
      <= uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)))%Z).

(* ===== lemmas ============================================================= *)

(** A split step keeps the registry coherent: no type appears or disappears. *)
Lemma registry_coh_split_step (bind : gmap P loc) (before after : gmap loc type_state)
    (w : item_cell) :
  split_types_update_rel before after w ->
  registry_coh bind before -> registry_coh bind after.
Proof.
  move=> [Hpres [Hdom _]] Hreg.
  apply (registry_coh_dom_eq bind before after); [exact Hdom | | exact Hreg].
  move=> p [ts' Hts']. destruct (Hpres p ts' Hts') as (ts & Hts & _). by exists ts.
Qed.

(** The same along a repair, which is at most two splits. *)
Lemma registry_coh_repair_step (bind : gmap P loc) (before after : gmap loc type_state) :
  repair_types_update_rel before after ->
  registry_coh bind before -> registry_coh bind after.
Proof.
  move=> [Hpres [Hdom _]] Hreg.
  apply (registry_coh_dom_eq bind before after); [exact Hdom | | exact Hreg].
  move=> p [ts' Hts']. destruct (Hpres p ts' Hts') as (ts & Hts & _). by exists ts.
Qed.

(** And along the wire delete path. *)
Lemma registry_coh_delete_step (bind : gmap P loc) (before after : gmap loc type_state) :
  delete_types_update_rel before after ->
  registry_coh bind before -> registry_coh bind after.
Proof.
  move=> [Hpres [Hdom _]] Hreg.
  apply (registry_coh_dom_eq bind before after); [exact Hdom | | exact Hreg].
  move=> p [ts' Hts']. destruct (Hpres p ts' Hts') as (ts & Hts & _). by exists ts.
Qed.

(** The split is invisible to the per-char document: the flatten is unchanged. *)
Lemma split_cells_flatten (cells : list item_cell) (k o : nat) (r_loc : loc) (c : item_cell) :
  cells !! k = Some c ->
  run_flatten (split_cells cells k o r_loc) = run_flatten cells.
Proof.
  move=> Hk. rewrite /split_cells Hk.
  rewrite -[in X in _ = X](take_drop_middle cells k c Hk).
  rewrite !run_flatten_app !run_flatten_cons run_flatten_nil.
  rewrite /split_cell_left /split_cell_right /=.
  rewrite app_nil_r take_drop //.
Qed.

(** ... and to the visible count. *)
Lemma split_cells_num_visible (cells : list item_cell) (k o : nat) (r_loc : loc) (c : item_cell) :
  cells !! k = Some c ->
  num_visible (split_cells cells k o r_loc) = num_visible cells.
Proof.
  move=> Hk. rewrite /split_cells Hk.
  rewrite -[in X in _ = X](take_drop_middle cells k c Hk).
  rewrite /num_visible !fmap_app !fmap_cons !list_sum_app /=.
  rewrite /split_cell_left /split_cell_right /=.
  destruct (ic_deleted c); [lia |].
  rewrite !length_take !length_drop. lia.
Qed.

Lemma delete_types_update_rel_refl (types : gmap loc type_state) :
  delete_types_update_rel types types.
Proof.
  split_and!; [move=> p ts' Hp; by exists ts' | done | exact (live_refine_refl types)
              | exact (dead_chars_kept_refl types) |].
  move=> c' Hc'. exists c'. split_and!; [exact Hc' | done | lia | lia].
Qed.

Lemma delete_types_update_rel_trans (t1 t2 t3 : gmap loc type_state) :
  delete_types_update_rel t1 t2 -> delete_types_update_rel t2 t3 -> delete_types_update_rel t1 t3.
Proof.
  move=> [Harr1 [Hdom1 [Hlr1 [Hdk1 Hco1]]]] [Harr2 [Hdom2 [Hlr2 [Hdk2 Hco2]]]]. split_and!.
  - move=> p ts3 Hp3.
    destruct (Harr2 p ts3 Hp3) as (ts2 & Hp2 & Heq2).
    destruct (Harr1 p ts2 Hp2) as (ts1 & Hp1 & Heq1).
    exists ts1. split; [exact Hp1 | congruence].
  - move=> p Hp. exact (Hdom2 p (Hdom1 p Hp)).
  - exact (live_refine_trans t1 t2 t3 Hlr1 Hlr2).
  - exact (dead_chars_kept_trans t1 t2 t3 Hdk1 Hdk2).
  - move=> c3 Hc3.
    destruct (Hco2 c3 Hc3) as (c2 & Hc2 & Hcc2 & Hlo2 & Hhi2).
    destruct (Hco1 c2 Hc2) as (c1 & Hc1 & Hcc1 & Hlo1 & Hhi1).
    exists c1. split_and!; [exact Hc1 | congruence | lia | lia].
Qed.

(** A split step is a delete step: [split_types_update_rel]'s model and coordinate
    clauses. *)
Lemma delete_types_update_rel_of_split (types types' : gmap loc type_state) (w : item_cell) :
  split_types_update_rel types types' w -> delete_types_update_rel types types'.
Proof.
  move=> [Harr [Hdom [_ [_ [_ [_ [Hco [Hlr Hdk]]]]]]]].
  split_and!; [| exact Hdom | exact Hlr | exact Hdk | exact Hco].
  move=> p ts' Hp'. destruct (Harr p ts' Hp') as (ts & Hp & Heq & _).
  exists ts. split; [exact Hp | exact Heq].
Qed.

(** A tombstone step is a delete step: one type is replaced by one whose
    cells changed but whose model list did not, and (in the only use,
    [flip_cell] at one index) whose cells keep their coordinates. *)
Lemma delete_types_update_rel_of_flip (types : gmap loc type_state) (p : loc)
    (ts : type_state) (k : nat) (c : item_cell) :
  types !! p = Some ts -> ty_cells ts !! k = Some c ->
  delete_types_update_rel types
    (<[p := MkTypeState (<[k := flip_cell c]> (ty_cells ts)) (ty_arr ts)]> types).
Proof.
  move=> Hp Hck. split_and!.
  - move=> q tq Hq.
    destruct (decide (q = p)) as [-> | Hne].
    + rewrite lookup_insert_eq in Hq. injection Hq as <-.
      exists ts. split; [exact Hp | reflexivity].
    + rewrite lookup_insert_ne // in Hq. by exists tq.
  - move=> q Hq.
    destruct (decide (q = p)) as [-> | Hne].
    + rewrite lookup_insert_eq. by eexists.
    + rewrite lookup_insert_ne //.
  - exact (live_refine_flip types p ts k c Hp Hck).
  - exact (dead_chars_kept_flip types p ts k c Hp Hck).
  - (* the pool is the same up to the flipped cell, which keeps its run and
       hence its coordinates *)
    move=> c' Hc'.
    have Hlr := flip_locs_run_perm types p ts k c Hp Hck.
    have Hin : (ic_loc c', ic_run c') ∈ ((λ c0, (ic_loc c0, ic_run c0)) <$> all_cells types).
    { rewrite -Hlr. apply list_elem_of_fmap.
      exists c'. split; [reflexivity | exact Hc']. }
    apply list_elem_of_fmap in Hin as (cw0 & Heq & Hcw0).
    have Hrun : ic_run c' = ic_run cw0 := f_equal snd Heq.
    exists cw0. rewrite /cell_client /cell_clock /run_head Hrun.
    split_and!; [exact Hcw0 | done | lia | lia].
Qed.

End store_value_split.
