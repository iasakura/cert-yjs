(** The [store] VALUE layer, part 3: the SPLIT SURGERY on abstract cells and
    the per-step transport records, over [store/value_cells.v] and
    [store/value_live.v].

    Definitions
    - the split surgery [split_cell_left] / [split_cell_right] / [split_cells].
    - the records one store step hands its caller: [split_types_update_rel] (one
      [splitNode]), [repair_types_update_rel] (the at-most-two splits of [repair])
      and [delete_types_update_rel] (the unbounded split-and-tombstone loop of the
      wire delete path).
    - what the node lookups and splits say about the pool: [pool_cell_covers]
      (a pool cell holds an id), [cell_covers_clock] (a clock within a run),
      [sorted_client_run] (one client's clock-sorted node list), [cell_starts_at]
      / [cell_ends_at] (the cell at a location begins / ends at an id),
      [fresh_loc] (a location no pool cell uses), and the [repair] contract
      [origins_covered] / [repair_parent] / [origins_split].

    Laws
    - splitting a node is invisible to the model: [split_cells_flatten] and
      [split_cells_num_visible].
    - [delete_types_update_rel] is reflexive and transitive (which is what lets the
      delete loop compose one record per step), and is implied by a split step
      ([delete_types_update_rel_of_split]) and by a tombstone flip
      ([delete_types_update_rel_of_flip]).
    - [cell_covers_w64] reads [cell_covers] at a runtime id in [w64] arithmetic;
      [pool_cell_covers_loc]: one id lives in one node; [split_cell_right_head_id]:
      the id the right half of a split starts at.

    Sits above [store/value_cells.v] and [store/value_live.v]. *)

From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core prelude network_model.
From iris.algebra Require Import auth gmap gset.
From stdpp Require Import sorting.
Local Open Scope Z_scope.
From New.proof.store Require Import model value_cells value_live value_span.
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

    Used as: the postcondition of [wp_store__splitAtAndGetLeft] and
    [wp_store__splitAtAndGetRight], composed by [repair] into
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
  cells_within (all_cells before) (all_cells after) ∧
  live_refine before after ∧
  dead_chars_kept before after.

(** [repair_types_update_rel before after]: what [store.repair] does to the type
    map. The same shape as [split_types_update_rel] minus the clauses about a
    single split location, since repair performs up to two of them: each
    client's run list therefore grows by at most two.

    Used as: the postcondition of [wp_store__repair], consumed by
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
  cells_within (all_cells before) (all_cells after) ∧
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
  cells_within (all_cells before) (all_cells after).

(* ===== what lookups and splits say about the pool ======================= *)

(** [cell_covers_clock c k]: the run of [c] has a char with clock [k], whatever
    the client ([getNodeIndex] searches one client's run). *)
Definition cell_covers_clock (c : item_cell) (k : nat) : Prop :=
  (clock (item_id (run_head c)) <= k)%nat ∧
  (k < clock (item_id (run_head c)) + length (ic_run c))%nat.

(** [pool_cell_covers types c d]: [c] is a cell of the pool [types] and its run
    has the char with id [d]. *)
Definition pool_cell_covers (types : gmap loc type_state) (c : item_cell) (d : YjsId) : Prop :=
  c ∈ all_cells types ∧ cell_covers c d.

(** [sorted_client_run types kc run]: [run] lists cells of client [kc] from the
    pool [types], clock-sorted and without a repeated node: the item map's run
    for [kc], or that run with one cell rewritten during a split. *)
Definition sorted_client_run (types : gmap loc type_state) (kc : w64)
    (run : list item_cell) : Prop :=
  StronglySorted cell_le run ∧ NoDup (ic_loc <$> run) ∧
  (∀ c, c ∈ run -> c ∈ client_run types kc).

(** [cell_starts_at types parent l d]: the pool [types] holds, under the type
    [parent], a cell at location [l] whose first char has id [d]. *)
Definition cell_starts_at (types : gmap loc type_state) (parent l : loc) (d : YjsId) : Prop :=
  ∃ c, c ∈ all_cells types ∧ ic_loc c = l ∧ ic_parent c = parent ∧
       item_id (run_head c) = d.

(** [cell_ends_at types parent l d]: the pool [types] holds, under the type
    [parent], a cell at location [l] whose last char has id [d]. *)
Definition cell_ends_at (types : gmap loc type_state) (parent l : loc) (d : YjsId) : Prop :=
  ∃ c, c ∈ all_cells types ∧ ic_loc c = l ∧ ic_parent c = parent ∧
       clientId (item_id (run_head c)) = clientId d ∧
       (clock (item_id (run_head c)) + length (ic_run c) = clock d + 1)%nat.

(** [fresh_loc l types]: [l] is a non-null location no cell of the pool [types]
    lives at (where a split puts its new right half). *)
Definition fresh_loc (l : loc) (types : gmap loc type_state) : Prop :=
  l ≠ null ∧ l ∉ ic_loc <$> all_cells types.

(** [origin_covered types o oc]: the optional origin id [o] resolves to the
    optional cell [oc]: both absent, or [oc] the pool cell whose run has [o]. *)
Definition origin_covered (types : gmap loc type_state) (o : option YjsId)
    (oc : option item_cell) : Prop :=
  match o, oc with
  | Some d, Some c => pool_cell_covers types c d
  | None, None => True
  | _, _ => False
  end.

(** [origins_covered types input ocL ocR]: both origins of [input] resolve in
    the pool ([origin_covered]), and when they fall in one cell the left origin
    precedes the right one in clock (so splitting at the left origin leaves the
    right one in place). *)
Definition origins_covered (types : gmap loc type_state) (input : IntegrateInput (A := A))
    (ocL ocR : option item_cell) : Prop :=
  origin_covered types (in_originId input) ocL ∧
  origin_covered types (in_rightOriginId input) ocR ∧
  match in_originId input, in_rightOriginId input, ocL, ocR with
  | Some a, Some b, Some cL0, Some cR0 => cL0 = cR0 -> (clock a < clock b)%nat
  | _, _, _, _ => True
  end.

(** [repair_parent bind opn ocL ocR p_t]: the type a repaired item lands in:
    the root bound to its wire parent name when it carries one, otherwise the
    type of its left, else right, origin cell. *)
Definition repair_parent (bind : gmap P loc) (opn : option go_string)
    (ocL ocR : option item_cell) (p_t : loc) : Prop :=
  match opn with
  | Some nm => bind !! nm = Some p_t
  | None => match ocL with
            | Some c => p_t = ic_parent c
            | None => match ocR with
                      | Some c => p_t = ic_parent c
                      | None => False
                      end
            end
  end.

(** [origins_split types input ocL ocR lft rgt]: after [repair] the item's
    [left] is the origin cell's location, now a cell ending at the left origin
    (in the origin cell's type), and its [right] a cell starting at the right
    origin; an absent origin links to [null]. *)
Definition origins_split (types : gmap loc type_state) (input : IntegrateInput (A := A))
    (ocL ocR : option item_cell) (lft rgt : loc) : Prop :=
  match in_originId input, ocL with
  | Some d, Some c0 => lft = ic_loc c0 ∧ cell_ends_at types (ic_parent c0) lft d
  | None, None => lft = null
  | _, _ => False
  end ∧
  match in_rightOriginId input, ocR with
  | Some d, Some c0 => cell_starts_at types (ic_parent c0) rgt d
  | None, None => rgt = null
  | _, _ => False
  end.

(* ===== lemmas ============================================================= *)

(** [cell_covers] at a runtime id, read in the [w64] arithmetic the node
    lookups compute with; needs the cell's ids to fit a word. *)
Lemma cell_covers_w64 (c : item_cell) (idv : yjs.id.t) :
  (Z.of_nat (clientId (item_id (run_head c))) < 2^64)%Z ->
  (Z.of_nat (clock (item_id (run_head c))) < 2^64)%Z ->
  cell_fits c ->
  cell_covers c (toYjsId idv) <->
  (cell_client c = idv.(yjs.id.clientId') ∧
   (uint.Z (cell_clock c) <= uint.Z idv.(yjs.id.clock'))%Z ∧
   (uint.Z idv.(yjs.id.clock') < uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)))%Z).
Proof.
  move=> Hcl Hck Hfit.
  rewrite /cell_covers /cell_client /cell_clock /cell_fits /toYjsId /= in Hfit |- *.
  split.
  - move=> [H1 [H2 H3]]. split_and!; [rewrite H1; word | word | word].
  - move=> [H1 [H2 H3]]. split_and!; [| word | word].
    have H1' := f_equal uint.Z H1. word.
Qed.

(** One id lives in one node: two pool cells covering the same id share a
    location ([cells_range_disjoint]). *)
Lemma pool_cell_covers_loc (types : gmap loc type_state) (c1 c2 : item_cell) (d : YjsId) :
  pool_invs types ->
  (∀ c, c ∈ all_cells types -> (Z.of_nat (clock (item_id (run_head c))) < 2^64)%Z) ->
  pool_cell_covers types c1 d -> pool_cell_covers types c2 d -> ic_loc c1 = ic_loc c2.
Proof.
  move=> [Hfits [_ [Hdisj _]]] Hbnd [Hc1 [Hcl1 [Hle1 Hlt1]]] [Hc2 [Hcl2 [Hle2 Hlt2]]].
  destruct (decide (ic_loc c1 = ic_loc c2)) as [He | Hne]; [exact He | exfalso].
  have Hcc : cell_client c1 = cell_client c2 by rewrite /cell_client Hcl1 Hcl2.
  have Hb1 := Hbnd c1 Hc1. have Hb2 := Hbnd c2 Hc2.
  have Hf1 := Hfits c1 Hc1. have Hf2 := Hfits c2 Hc2.
  rewrite /cell_fits /cell_clock in Hf1 Hf2.
  destruct (Hdisj c1 c2 Hc1 Hc2 Hcc Hne) as [H | H]; rewrite /cell_clock in H; word.
Qed.

(** The right half of a split starts [o] chars into the run. *)
Lemma split_cell_right_head_id (cw : item_cell) (o : nat) (rloc : loc) :
  run_wf (ic_run cw) -> (o < length (ic_run cw))%nat ->
  item_id (run_head (split_cell_right cw o rloc))
    = MkYjsId (clientId (item_id (run_head cw))) (clock (item_id (run_head cw)) + o).
Proof.
  move=> Hwf Ho.
  destruct (lookup_lt_is_Some_2 (ic_run cw) o Ho) as [yo Hyo].
  have Hheadr : run_head (split_cell_right cw o rloc) = yo.
  { rewrite /run_head /split_cell_right /= (drop_S _ _ _ Hyo) //. }
  rewrite Hheadr. exact (run_wf_char_id (ic_run cw) o yo Hwf Hyo).
Qed.

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
