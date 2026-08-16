(** The [store] VALUE layer, part 3: the SPLIT SURGERY on abstract cells and
    the per-step transport records, over [store/value_cells.v] and
    [store/value_live.v].

    Definitions
    - the split surgery [split_cell_left] / [split_cell_right] / [split_cells].
    - the records one store step hands its caller: [split_step_facts] (one
      [splitNode]), [repair_types_facts] (the at-most-two splits of [repair])
      and [delete_types_facts] (the unbounded split-and-tombstone loop of the
      wire delete path).

    Laws
    - splitting a node is invisible to the model: [split_cells_flatten] and
      [split_cells_num_visible].
    - [delete_types_facts] is reflexive and transitive (which is what lets the
      delete loop compose one record per step), and is implied by a split step
      ([delete_types_facts_of_split]) and by a tombstone flip
      ([delete_types_facts_of_flip]).

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

(* ----- invariant-carrying split wrappers (issue #28 stage D2b) ------------
   The D1b heap specs packaged with the D1c/D2a pool bookkeeping: pool
   invariants out for pool invariants in, plus the transport facts [repair]
   needs to sequence two splits (document/domain preservation, coverage
   transport with provenance, stability away from the split location, run
   list growth) and the boundary cell itself. *)

Definition split_step_facts (types types' : gmap loc type_state) (w : item_cell) : Prop :=
  (∀ p ts', types' !! p = Some ts' ->
     ∃ ts, types !! p = Some ts ∧ ty_arr ts' = ty_arr ts ∧
           run_flatten (ty_cells ts') = run_flatten (ty_cells ts)) ∧
  (∀ p, is_Some (types !! p) -> is_Some (types' !! p)) ∧
  (∀ kc, (length (client_run types' kc) <= S (length (client_run types kc)))%nat) ∧
  (∀ c, c ∈ all_cells types -> ic_loc c ≠ ic_loc w -> c ∈ all_cells types') ∧
  (∀ (ccl : w64) (clkZ : Z) (c : item_cell), c ∈ all_cells types ->
     cell_client c = ccl -> (uint.Z (cell_clock c) <= clkZ)%Z ->
     (clkZ < uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)))%Z ->
     ∃ c', c' ∈ all_cells types' ∧ cell_client c' = ccl ∧
           (uint.Z (cell_clock c') <= clkZ)%Z ∧
           (clkZ < uint.Z (cell_clock c') + Z.of_nat (length (ic_run c')))%Z ∧
           ic_parent c' = ic_parent c ∧
           (c' = c ∨ (c = w ∧ (1 < length (ic_run w))%nat ∧
                      (ic_loc c' = ic_loc w ∨
                       ic_loc c' ∉ (ic_loc <$> all_cells types))))) ∧
  (∀ p ts ts', types !! p = Some ts -> types' !! p = Some ts' ->
     Forall cell_unit (ty_cells ts) -> ts' = ts) ∧
  (∀ c', c' ∈ all_cells types' -> ∃ c, c ∈ all_cells types ∧
     cell_client c' = cell_client c ∧
     (uint.Z (cell_clock c) <= uint.Z (cell_clock c'))%Z ∧
     (uint.Z (cell_clock c') + Z.of_nat (length (ic_run c')) <=
      uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)))%Z) ∧
  live_refine types types' ∧
  dead_chars_kept types types'.

(** What [repair] guarantees about the type map: per-type model documents and
    the domain survive, and each client's run list grows by at most the two
    possible splits. *)
Definition repair_types_facts (types types2 : gmap loc type_state) : Prop :=
  (∀ p ts', types2 !! p = Some ts' ->
     ∃ ts, types !! p = Some ts ∧ ty_arr ts' = ty_arr ts ∧
           run_flatten (ty_cells ts') = run_flatten (ty_cells ts)) ∧
  (∀ p, is_Some (types !! p) -> is_Some (types2 !! p)) ∧
  (∀ kc, (length (client_run types2 kc) <= 2 + length (client_run types kc))%nat) ∧
  (∀ p ts ts', types !! p = Some ts -> types2 !! p = Some ts' ->
     Forall cell_unit (ty_cells ts) -> ts' = ts) ∧
  (∀ c', c' ∈ all_cells types2 -> ∃ c, c ∈ all_cells types ∧
     cell_client c' = cell_client c ∧
     (uint.Z (cell_clock c) <= uint.Z (cell_clock c'))%Z ∧
     (uint.Z (cell_clock c') + Z.of_nat (length (ic_run c')) <=
      uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)))%Z) ∧
  live_refine types types2.

(** What the wire delete path guarantees about the type map (issue #133): the
    per-type MODEL documents are untouched (both surgeries it performs, a
    split and a tombstone, are model no-ops), no type disappears, and the live
    cells only shrink. Unlike [repair_types_facts] this carries no run-length
    bound, because the delete loop splits an unbounded number of times; that
    is also what makes it transitive, so the loop can compose one record per
    step. *)
Definition delete_types_facts (types types' : gmap loc type_state) : Prop :=
  (∀ p ts', types' !! p = Some ts' ->
     ∃ ts, types !! p = Some ts ∧ ty_arr ts' = ty_arr ts) ∧
  (∀ p, is_Some (types !! p) -> is_Some (types' !! p)) ∧
  live_refine types types' ∧
  dead_chars_kept types types' ∧
  (∀ c', c' ∈ all_cells types' -> ∃ c, c ∈ all_cells types ∧
     cell_client c' = cell_client c ∧
     (uint.Z (cell_clock c) <= uint.Z (cell_clock c'))%Z ∧
     (uint.Z (cell_clock c') + Z.of_nat (length (ic_run c'))
      <= uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)))%Z).

(* ===== lemmas ============================================================= *)

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

Lemma delete_types_facts_refl (types : gmap loc type_state) :
  delete_types_facts types types.
Proof.
  split_and!; [move=> p ts' Hp; by exists ts' | done | exact (live_refine_refl types)
              | exact (dead_chars_kept_refl types) |].
  move=> c' Hc'. exists c'. split_and!; [exact Hc' | done | lia | lia].
Qed.

Lemma delete_types_facts_trans (t1 t2 t3 : gmap loc type_state) :
  delete_types_facts t1 t2 -> delete_types_facts t2 t3 -> delete_types_facts t1 t3.
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

(** A split step is a delete step: [split_step_facts]'s model and coordinate
    clauses. *)
Lemma delete_types_facts_of_split (types types' : gmap loc type_state) (w : item_cell) :
  split_step_facts types types' w -> delete_types_facts types types'.
Proof.
  move=> [Harr [Hdom [_ [_ [_ [_ [Hco [Hlr Hdk]]]]]]]].
  split_and!; [| exact Hdom | exact Hlr | exact Hdk | exact Hco].
  move=> p ts' Hp'. destruct (Harr p ts' Hp') as (ts & Hp & Heq & _).
  exists ts. split; [exact Hp | exact Heq].
Qed.

(** A tombstone step is a delete step: one type is replaced by one whose
    cells changed but whose model list did not, and (in the only use,
    [flip_cell] at one index) whose cells keep their coordinates. *)
Lemma delete_types_facts_of_flip (types : gmap loc type_state) (p : loc)
    (ts : type_state) (k : nat) (c : item_cell) :
  types !! p = Some ts -> ty_cells ts !! k = Some c ->
  delete_types_facts types
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
