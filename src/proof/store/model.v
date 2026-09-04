(** The [store], PURE model layer: the document model and the wire it replays.
    No Go values, no Iris.

    Definitions
    - [expand_input] / [expand_inputs]: one wire item expands to its per-char
      integrate inputs, which is how a run-granular update refines the
      per-char model.
    - what a decoded batch must satisfy: [input_fits] per struct,
      [pending_item_rooted] / [is_pending_rooted], bundled as [update_wf].
    - the wire-level drain: [wire_integrate] applies one ready item,
      [wire_pass] one sweep over the pending list, [wire_drain(_aux)] the fixed
      point, [WireReplay] the resulting replay relation and [wire_ready_total]
      the readiness gate.
    - [accepted_coh] / [pending_id_set] / [input_accounted]: which delivered
      ids a replica has accounted for, either integrated or still pending. This
      is what the no-loss spec is stated with.
    - [inputs_rooted_in_bind] / [doc_registry_coh]: the pending inputs and the
      doc model only mention registered root types.

    Laws
    - [elem_of_pending_id_set]: membership in the pending id set is exactly
      "some pending input has that id".
    - [accepted_coh] survives history growth ([accepted_coh_hist_grow]) and the
      applyUpdate step ([accepted_coh_applyUpdate]): the two state-transition
      laws the no-loss argument runs on.

    The cell bookkeeping that shadows this model is [store/value.v].

    The run-granular pool (plan-item-run-split stage 2): [pool], every
    registered type at its [type_model] ([addressed_pool] pairs it with the
    types' node addresses); [all_runs] and the clock-sorted
    [client_runs]; [run_pool_invs], the pure pool invariants at run
    granularity ([pool_invs] minus the heap-side [NoDup] of addresses);
    [pool_run_covers], the index-based [pool_cell_covers];
    [pool_run_starts_at] / [pool_run_ends_at], the run at an index begins /
    ends at an id; [runs_live_refine] / [runs_dead_kept], the pool-level
    live-character refinement and tombstone preservation; [pool_after_split],
    what one [splitNode] leaves of the pool at run granularity
    ([pool_after_repair] the same for [store.repair]'s at most two splits,
    [pool_after_delete] for the wire delete path's unbounded sweep);
    [pool_run_clock_below], the index-based [pool_clock_below]
    ([pool_run_clock_below_of_arrs] reads it off a per-type clock bound on
    the flattened lists);
    [all_runs] under a registry insert or lookup ([all_runs_insert] /
    [all_runs_lookup], membership across one slot [elem_of_all_runs_insert]
    / [elem_of_all_runs_lookup]) and [run_pool_invs] surviving one node
    split ([run_pool_invs_split]), one integrate splice
    ([run_pool_invs_integrate]) and one tombstoning
    ([run_pool_invs_flip]); [pool_after_delete] is a preorder containing
    one split and one tombstoning ([pool_after_delete_refl] /
    [pool_after_delete_trans] / [pool_after_split_delete] /
    [pool_after_delete_flip]), and the tombstone record survives a step
    that keeps dead chars dead ([ids_tombstoned_runs_dead_kept]);
    [delete_set_tombstoned_runs], the tombstone-set clause at runs, refined
    along [runs_live_refine] ([delete_set_tombstoned_runs_refine]) and
    transported along a permutation, a growth by a fresh run, a set union
    or shrink;
    membership in [all_runs] is membership in some type
    ([elem_of_all_runs]) and [all_runs] around one split is the two halves
    in place of the split run ([all_runs_split_perm]); [pool_after_split]
    holds of no change and of one [split_runs] surgery
    ([pool_after_split_refl] / [pool_after_split_of_split_runs]). The apply path's step records at run
    granularity: [runs_within_or_from] (every new run sits inside an old
    one or inside an integrated input's range; reflexive and composing
    across appended inputs, [runs_within_or_from_refl] / [_trans]),
    [runs_apply_live_refine] (live chars are old live chars or chars the
    model did not have; reflexive, transitive against a growing model,
    and following from one integrate step under the replay's client bound,
    [runs_apply_live_refine_refl] / [_trans] / [_of_integrate]) and
    [runs_integrate_live_refine] (what one integrate step reports;
    transitive, implied by [runs_live_refine], and holding of a splice
    whose new run carries the item's own chars,
    [runs_integrate_live_refine_trans] / [_of_live_refine] / [_snoc]);
    [runs_within] is the origin-free half of [runs_within_or_from]
    ([runs_within_or_from_of_within]); [all_runs] around an integrate
    splice and a fresh empty type ([all_runs_splice_perm] /
    [all_runs_insert_empty]); the per-client clock bound survives a step
    whose runs sit inside old ones ([pool_run_clock_below_within]). *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core prelude algebra network_model.
From iris.algebra Require Import auth gmap gset.
From stdpp Require Import sorting.
From New.proof.item Require Import run_theory model value heap.
From New.proof.ytype Require Import model value heap.
Local Open Scope Z_scope.

Section store_model.

Set Default Proof Using "Type*".

Notation A := go_string.

Notation P := go_string.

Local Notation TId := (TypeId P).

Local Notation Op := (TId * @YjsOperation A)%type.

Local Notation Ev := (@Event Op).

Local Notation DocModel := (gmap TId (list (YjsItem A))).

(* ===== definitions ======================================================== *)

(** The run-granular pool (plan-item-run-split stage 2): every registered
    type at its [type_model], keyed by the yType's address (the key only
    names the type; no pure lemma computes with it). *)
Definition pool := gmap loc type_model.

(** [addressed_pool]: a pool together with each registered type's node
    addresses, the pair the whole store speaks in ([sr_locs], [sr_pool]).
    Named because it is also the ghost value the readers agree on
    ([store_names]'s [sn_types_agree], read by [pool_frag] /
    [own_read_locked] and pinned by [store_inv_ro]). *)
Definition addressed_pool := (gmap loc (list loc) * pool)%type.

(** All runs across all types: the loc-free [all_cells]. *)
Definition all_runs (p : pool) : list ItemRun :=
  concat (tm_runs <$> (map_to_list p).*2).

(** [client_runs p c]: client [c]'s runs across every type, clock-sorted:
    the loc-free model of the [store.items] run list ([client_run] projects
    onto it). *)
Definition client_runs (p : pool) (c : nat) : list ItemRun :=
  merge_sort run_le (filter (λ r, run_client r = c) (all_runs p)).

(** [pool_run_starts_at p parent k d] / [pool_run_ends_at p parent k d]:
    the [k]-th run of the type at [parent] starts (ends) at the id [d]: the
    index-based [cell_starts_at] / [cell_ends_at], whose node address is the
    address list's [k]-th entry. *)
Definition pool_run_starts_at (p : pool) (parent : loc) (k : nat) (d : YjsId) : Prop :=
  ∃ tm, p !! parent = Some tm ∧ runs_start_at (tm_runs tm) k d.

Definition pool_run_ends_at (p : pool) (parent : loc) (k : nat) (d : YjsId) : Prop :=
  ∃ tm, p !! parent = Some tm ∧ runs_end_at (tm_runs tm) k d.

(** [run_pool_invs p]: the pure pool invariants at run granularity: every
    run's clock range fits a word, same-client ranges are disjoint (runs
    told apart by index), and every head's same-client origin is older.
    [pool_invs]'s [NoDup] of node addresses is a heap fact and stays with
    the heap layer. *)
(** [runs_live_refine p p'] / [runs_dead_kept p p']: the tombstone-side
    refinements at run granularity (the loc-free [live_refine] /
    [dead_chars_kept]): every live char of [p'] was live in [p], and every
    dead char of [p] stays dead in [p']. *)
Definition runs_live_refine (p p' : pool) : Prop :=
  ∀ r', r' ∈ all_runs p' -> run_deleted r' = false ->
    ∃ r, r ∈ all_runs p ∧ run_deleted r = false ∧
         (∀ y, y ∈ run_items r' -> y ∈ run_items r).

Definition runs_dead_kept (p p' : pool) : Prop :=
  ∀ r, r ∈ all_runs p -> run_deleted r = true -> ∀ y, y ∈ run_items r ->
    ∃ r', r' ∈ all_runs p' ∧ run_deleted r' = true ∧ y ∈ run_items r'.

(** [delete_set_tombstoned_runs delete_set runs]: no live run of [runs]
    holds a char whose id is in [delete_set]: the tombstone-set clause at
    run granularity (what [own_delete_set_runs] carries). *)
Definition delete_set_tombstoned_runs (delete_set : gset YjsId) (runs : list ItemRun) : Prop :=
  ∀ r, r ∈ runs -> ∀ y, y ∈ run_items r -> item_id y ∈ delete_set -> run_deleted r = true.

(** [pool_after_split p p' parent k]: [p'] is [p] after one node split at
    the [k]-th run of the type at [parent]: the loc-free
    [split_types_update_rel], its address clauses become index facts. Each
    type's document and flatten survive, no type disappears, every run away from the split spot survives,
    a covered clock stays covered in the same type (the covering run is the
    survivor, or a half of the split run; which half is an address-map
    matter the spec states on [sr_locs]), a type of
    one-char runs is untouched, every new run sits inside an old one's
    range, and live and dead chars refine. *)
Definition pool_after_split (p p' : pool) (parent : loc) (k : nat) : Prop :=
  (∀ q tm', p' !! q = Some tm' ->
     ∃ tm, p !! q = Some tm ∧ tm_arr tm' = tm_arr tm ∧
           runs_flatten (tm_runs tm') = runs_flatten (tm_runs tm)) ∧
  (∀ q, is_Some (p !! q) -> is_Some (p' !! q)) ∧
  (∀ q tm k' r, p !! q = Some tm -> tm_runs tm !! k' = Some r ->
     ¬ (q = parent ∧ k' = k) -> r ∈ all_runs p') ∧
  (∀ (ccl clk : nat) q tm k0 r, p !! q = Some tm -> tm_runs tm !! k0 = Some r ->
     run_client r = ccl -> (run_clock r <= clk)%nat ->
     (clk < run_clock r + length (run_items r))%nat ->
     ∃ tm' k' r', p' !! q = Some tm' ∧ tm_runs tm' !! k' = Some r' ∧
       run_client r' = ccl ∧ (run_clock r' <= clk)%nat ∧
       (clk < run_clock r' + length (run_items r'))%nat ∧
       (r' = r ∨ (q = parent ∧ k0 = k ∧ (1 < length (run_items r))%nat))) ∧
  (∀ q tm tm', p !! q = Some tm -> p' !! q = Some tm' ->
     Forall (λ r, length (run_items r) = 1%nat) (tm_runs tm) -> tm' = tm) ∧
  runs_within (all_runs p) (all_runs p') ∧
  runs_live_refine p p' ∧
  runs_dead_kept p p'.

(** [pool_after_repair p p']: [p'] is [p] after [store.repair]'s at most two
    node splits: the loc-free [repair_types_update_rel]. The same clauses as
    [pool_after_split] minus the ones about a single split spot: each type's
    document and flatten survive, no type disappears, a client's run list
    grows by at most two, a type of one-char runs is untouched, every new
    run sits inside an old one's range, and live chars refine. *)
Definition pool_after_repair (p p' : pool) : Prop :=
  (∀ q tm', p' !! q = Some tm' ->
     ∃ tm, p !! q = Some tm ∧ tm_arr tm' = tm_arr tm ∧
           runs_flatten (tm_runs tm') = runs_flatten (tm_runs tm)) ∧
  (∀ q, is_Some (p !! q) -> is_Some (p' !! q)) ∧
  (∀ q tm tm', p !! q = Some tm -> p' !! q = Some tm' ->
     Forall (λ r, length (run_items r) = 1%nat) (tm_runs tm) -> tm' = tm) ∧
  runs_within (all_runs p) (all_runs p') ∧
  runs_live_refine p p'.

(** [pool_after_delete p p']: [p'] is [p] after a sweep of the wire delete
    path ([deleteRange] / [applyDeleteSpans]): the loc-free
    [delete_types_update_rel]. Each type's document survives, no type
    disappears, live and dead chars refine, and every new run sits inside an
    old one's range. No run-count bound: the delete loop splits an unbounded
    number of times. *)
Definition pool_after_delete (p p' : pool) : Prop :=
  (∀ q tm', p' !! q = Some tm' -> ∃ tm, p !! q = Some tm ∧ tm_arr tm' = tm_arr tm) ∧
  (∀ q, is_Some (p !! q) -> is_Some (p' !! q)) ∧
  runs_live_refine p p' ∧
  runs_dead_kept p p' ∧
  runs_within (all_runs p) (all_runs p').

(** [pool_run_covers p parent k d]: the [k]-th run of the type at [parent]
    has the char with id [d]: the index-based [pool_cell_covers]. *)
Definition pool_run_covers (p : pool) (parent : loc) (k : nat) (d : YjsId) : Prop :=
  ∃ tm r, p !! parent = Some tm ∧ tm_runs tm !! k = Some r ∧ run_covers r d.

Definition run_pool_invs (p : pool) : Prop :=
  (∀ r, r ∈ all_runs p -> run_fits r) ∧
  runs_disjoint (all_runs p) ∧
  (∀ r, r ∈ all_runs p -> run_origin_clk r).

(** [all_runs] under a registry insert or lookup: one type's runs out, the
    rest untouched (the run form of [all_cells_insert] / [all_cells_lookup]). *)
Lemma all_runs_insert (p : pool) (parent : loc) (tm tm' : type_model) :
  p !! parent = Some tm ->
  all_runs (<[parent := tm']> p) ≡ₚ tm_runs tm' ++ all_runs (delete parent p).
Proof.
  move=> Hp. rewrite /all_runs.
  apply (concat_perm (tm_runs <$> (map_to_list (<[parent := tm']> p)).*2)
                     (tm_runs tm' :: (tm_runs <$> (map_to_list (delete parent p)).*2))).
  rewrite (map_to_list_insert_existing p parent tm tm' Hp). simpl. reflexivity.
Qed.

Lemma all_runs_lookup (p : pool) (parent : loc) (tm : type_model) :
  p !! parent = Some tm ->
  all_runs p ≡ₚ tm_runs tm ++ all_runs (delete parent p).
Proof.
  move=> Hp.
  pose proof (all_runs_insert p parent tm tm Hp) as H.
  rewrite (insert_id p parent tm Hp) in H. exact H.
Qed.

(** Membership in [all_runs] across one registry slot: a run of the new
    type model, or a run of another type. *)
Lemma elem_of_all_runs_insert (p : pool) (parent : loc) (tm tm' : type_model) (r : ItemRun) :
  p !! parent = Some tm ->
  r ∈ all_runs (<[parent := tm']> p) <-> r ∈ tm_runs tm' ∨ r ∈ all_runs (delete parent p).
Proof.
  move=> Hp. rewrite (all_runs_insert p parent tm tm' Hp) elem_of_app //.
Qed.

Lemma elem_of_all_runs_lookup (p : pool) (parent : loc) (tm : type_model) (r : ItemRun) :
  p !! parent = Some tm ->
  r ∈ all_runs p <-> r ∈ tm_runs tm ∨ r ∈ all_runs (delete parent p).
Proof.
  move=> Hp. rewrite (all_runs_lookup p parent tm Hp) elem_of_app //.
Qed.

(** Membership in [all_runs]: a run of some registered type (the run form
    of [all_cells_elem_of]). *)
Lemma elem_of_all_runs (p : pool) (r : ItemRun) :
  r ∈ all_runs p <-> ∃ q tm, p !! q = Some tm ∧ r ∈ tm_runs tm.
Proof.
  rewrite /all_runs list_elem_of_concat. split.
  - move=> [runs [Hr Hruns]].
    apply list_elem_of_fmap in Hruns as (tm & -> & Htm).
    apply list_elem_of_fmap in Htm as ([q tm'] & -> & Hq). simpl in *.
    apply elem_of_map_to_list in Hq. eauto.
  - move=> [q [tm [Hq Hr]]]. exists (tm_runs tm). split; first exact Hr.
    apply list_elem_of_fmap. exists tm. split; first done.
    apply list_elem_of_fmap. exists (q, tm). split; first done.
    by apply elem_of_map_to_list.
Qed.

(** [run_pool_invs] survives one node split: the pure half of the
    [splitNode] surgery (fits, range disjointness and origin-clock in one
    bundle; runs are told apart by index, so no address [NoDup] premise). *)
Lemma run_pool_invs_split (p : pool) (parent : loc) (tm : type_model)
    (k o : nat) (r : ItemRun) :
  p !! parent = Some tm ->
  tm_runs tm !! k = Some r ->
  run_wf (run_items r) ->
  (0 < o < length (run_items r))%nat ->
  run_pool_invs p ->
  run_pool_invs (<[parent := MkTypeModel (split_runs (tm_runs tm) k o) (tm_arr tm)]> p).
Proof.
  move=> Hp Hrk Hwf Ho [Hfits [Hdisj Hoclk]].
  destruct (split_run_facts r o Hwf Ho)
    as (Hheadl & Hlenl & Hlenr & Hclientl & Hclientr & Hclockl & Hclockr).
  set (rest := take k (tm_runs tm) ++ drop (S k) (tm_runs tm) ++ all_runs (delete parent p)).
  have Hsplit : split_runs (tm_runs tm) k o
              = take k (tm_runs tm)
                ++ [split_run_left r o; split_run_right r o] ++ drop (S k) (tm_runs tm).
  { rewrite /split_runs Hrk //. }
  have Hmid := take_drop_middle (tm_runs tm) k r Hrk.
  have Hnew : all_runs (<[parent := MkTypeModel (split_runs (tm_runs tm) k o) (tm_arr tm)]> p)
            ≡ₚ split_run_left r o :: split_run_right r o :: rest.
  { rewrite (all_runs_insert p parent tm _ Hp) /= Hsplit /rest.
    rewrite -!app_assoc /=.
    rewrite -Permutation_middle.
    rewrite -Permutation_middle //. }
  have Hold : all_runs p ≡ₚ r :: rest.
  { rewrite (all_runs_lookup p parent tm Hp) /rest.
    rewrite -{1}Hmid -app_assoc /=.
    rewrite -Permutation_middle //. }
  have Hrmem : r ∈ all_runs p by (rewrite Hold; apply list_elem_of_here).
  have Hrfits := Hfits r Hrmem.
  split_and!.
  - (* fits *)
    move=> r0 Hr0. rewrite Hnew in Hr0.
    apply elem_of_cons in Hr0 as [-> | Hr0].
    + rewrite /run_fits Hclockl Hlenl. move: Hrfits. rewrite /run_fits. lia.
    + apply elem_of_cons in Hr0 as [-> | Hr0].
      * rewrite /run_fits Hclockr Hlenr. move: Hrfits. rewrite /run_fits. lia.
      * apply Hfits. rewrite Hold. apply elem_of_cons. by right.
  - (* disjoint *)
    have Hdisj1 : runs_disjoint (r :: rest) := runs_disjoint_perm _ _ Hold Hdisj.
    have Hsub : ∀ j' r2, rest !! j' = Some r2 -> run_client r2 = run_client r ->
        (run_clock r2 + length (run_items r2) <= run_clock r)%nat ∨
        (run_clock r + length (run_items r) <= run_clock r2)%nat.
    { move=> j' r2 Hj' Hcl2.
      have := Hdisj1 (S j') 0%nat r2 r ltac:(rewrite /= Hj' //) ltac:(done)
                ltac:(lia) Hcl2.
      move=> [Hl | Hr2]; [by left | by right]. }
    apply (runs_disjoint_perm (split_run_left r o :: split_run_right r o :: rest));
      [by symmetry |].
    move=> i j r1 r2 Hi Hj Hij Hcl.
    destruct i as [|[|i']]; destruct j as [|[|j']]; simpl in Hi, Hj; simplify_eq.
    + (* left vs right *)
      left. rewrite Hclockl Hlenl Hclockr. lia.
    + (* left vs rest *)
      have := Hsub j' r2 Hj ltac:(by rewrite -Hcl Hclientl).
      move=> [Hle | Hge].
      * right. rewrite Hclockl. lia.
      * left. rewrite Hclockl Hlenl. lia.
    + (* right vs left *)
      right. rewrite Hclockl Hlenl Hclockr. lia.
    + (* right vs rest *)
      have := Hsub j' r2 Hj ltac:(by rewrite -Hcl Hclientr).
      move=> [Hle | Hge].
      * right. rewrite Hclockr. lia.
      * left. rewrite Hclockr Hlenr. lia.
    + (* rest vs left *)
      have := Hsub i' r1 Hi ltac:(by rewrite Hcl Hclientl).
      move=> [Hle | Hge].
      * left. rewrite Hclockl. lia.
      * right. rewrite Hclockl Hlenl. lia.
    + (* rest vs right *)
      have := Hsub i' r1 Hi ltac:(by rewrite Hcl Hclientr).
      move=> [Hle | Hge].
      * left. rewrite Hclockr. lia.
      * right. rewrite Hclockr Hlenr. lia.
    + (* rest vs rest *)
      have := Hdisj1 (S i') (S j') r1 r2 ltac:(rewrite /= Hi //) ltac:(rewrite /= Hj //)
                ltac:(lia) Hcl.
      done.
  - (* origin clock *)
    move=> r0 Hr0. rewrite Hnew in Hr0.
    apply elem_of_cons in Hr0 as [-> | Hr0].
    + rewrite /run_origin_clk Hheadl Hclientl Hclockl. exact (Hoclk r Hrmem).
    + apply elem_of_cons in Hr0 as [-> | Hr0].
      * rewrite /run_origin_clk.
        have Hrun0 : run_items r !! 0%nat = Some (run_head_item r).
        { rewrite /run_head_item. destruct Hwf as [Hne _].
          destruct (run_items r) as [|a r']; [done | reflexivity]. }
        destruct (run_items r !! o) as [yo|] eqn:Hyo;
          last by (apply lookup_ge_None in Hyo; lia).
        destruct (run_items r !! (o - 1)%nat) as [yp|] eqn:Hyp;
          last by (apply lookup_ge_None in Hyp; lia).
        have Hheadr' : run_head_item (split_run_right r o) = yo.
        { rewrite /run_head_item /split_run_right /=.
          exact (hd_inhabitant_drop _ o yo Hyo). }
        have Hso : S (o - 1)%nat = o by lia.
        have Hstep := proj2 Hwf (o - 1)%nat yp yo Hyp ltac:(rewrite Hso //).
        destruct Hstep as (Hidyo & Horigyo & _).
        have Hidyp := run_wf_lookup_clock (run_items r) (o - 1)%nat
                        (run_head_item r) yp Hwf Hrun0 Hyp.
        move=> originId Hoid Hcl.
        rewrite Hheadr' Horigyo /= in Hoid.
        injection Hoid as <-.
        rewrite /run_clock Hheadr' Hidyo Hidyp /=. lia.
      * apply Hoclk. rewrite Hold. apply elem_of_cons. by right.
Qed.

(** [run_pool_invs] survives one integrate splice: the new run fits, its
    same-client origin precedes it, and every same-client run of the pool
    ends at or before its clock (the pure half of [store.Integrate]'s
    [addNode] step). *)
Lemma run_pool_invs_integrate (p : pool) (parent : loc) (tm : type_model)
    (idx : nat) (r : ItemRun) (arr' : list (YjsItem A)) :
  p !! parent = Some tm ->
  run_fits r ->
  run_origin_clk r ->
  (∀ r0, r0 ∈ all_runs p -> run_client r0 = run_client r ->
     (run_clock r0 + length (run_items r0) <= run_clock r)%nat) ->
  run_pool_invs p ->
  run_pool_invs (<[parent := MkTypeModel (take idx (tm_runs tm) ++ r :: drop idx (tm_runs tm)) arr']> p).
Proof.
  move=> Hp Hfitsr Hoclkr Hbelow [Hfits [Hdisj Hoclk]].
  have Hnew : all_runs (<[parent := MkTypeModel (take idx (tm_runs tm) ++ r :: drop idx (tm_runs tm)) arr']> p)
            ≡ₚ r :: all_runs p.
  { rewrite (all_runs_insert p parent tm _ Hp) /= (all_runs_lookup p parent tm Hp).
    rewrite -app_assoc /=.
    rewrite -{3}(take_drop idx (tm_runs tm)) -app_assoc.
    symmetry. apply Permutation_middle. }
  have Hmem : ∀ r0, r0 ∈ all_runs (<[parent := MkTypeModel (take idx (tm_runs tm) ++ r :: drop idx (tm_runs tm)) arr']> p)
                 -> r0 = r ∨ r0 ∈ all_runs p.
  { move=> r0 Hr0. rewrite Hnew in Hr0. apply elem_of_cons in Hr0. exact Hr0. }
  split_and!.
  - move=> r0 Hr0. destruct (Hmem r0 Hr0) as [-> | Hr0']; [exact Hfitsr | exact (Hfits r0 Hr0')].
  - apply (runs_disjoint_perm (r :: all_runs p)); [by symmetry |].
    move=> i j r1 r2 Hi Hj Hij Hcl.
    destruct i as [|i']; destruct j as [|j']; simpl in Hi, Hj; simplify_eq.
    + right. apply Hbelow; [exact (list_elem_of_lookup_2 _ _ _ Hj) | symmetry; exact Hcl].
    + left. apply Hbelow; [exact (list_elem_of_lookup_2 _ _ _ Hi) | exact Hcl].
    + exact (Hdisj i' j' r1 r2 Hi Hj ltac:(lia) Hcl).
  - move=> r0 Hr0. destruct (Hmem r0 Hr0) as [-> | Hr0']; [exact Hoclkr | exact (Hoclk r0 Hr0')].
Qed.

(** [run_pool_invs] survives one tombstoning: a flip changes no run's id,
    client, clock, or chars. *)
Lemma run_pool_invs_flip (p : pool) (parent : loc) (tm : type_model) (k : nat) (r : ItemRun) :
  p !! parent = Some tm ->
  tm_runs tm !! k = Some r ->
  run_pool_invs p ->
  run_pool_invs (<[parent := MkTypeModel (<[k := flip_run r]> (tm_runs tm)) (tm_arr tm)]> p).
Proof.
  move=> Hp Hrk [Hfits [Hdisj Hoclk]].
  set (rest := take k (tm_runs tm) ++ drop (S k) (tm_runs tm) ++ all_runs (delete parent p)).
  have Hk : (k < length (tm_runs tm))%nat := lookup_lt_Some _ _ _ Hrk.
  have Hmid := take_drop_middle (tm_runs tm) k r Hrk.
  have Hnew : all_runs (<[parent := MkTypeModel (<[k := flip_run r]> (tm_runs tm)) (tm_arr tm)]> p)
            ≡ₚ flip_run r :: rest.
  { rewrite (all_runs_insert p parent tm _ Hp) /= /rest.
    rewrite insert_take_drop; last exact Hk.
    rewrite -app_assoc /=.
    rewrite -Permutation_middle //. }
  have Hold : all_runs p ≡ₚ r :: rest.
  { rewrite (all_runs_lookup p parent tm Hp) /rest.
    rewrite -{1}Hmid -app_assoc /=.
    rewrite -Permutation_middle //. }
  have Hrmem : r ∈ all_runs p by (rewrite Hold; apply list_elem_of_here).
  have Hcl : run_client (flip_run r) = run_client r by rewrite /run_client /run_head_item flip_run_items.
  have Hck : run_clock (flip_run r) = run_clock r by rewrite /run_clock /run_head_item flip_run_items.
  have Hhd : run_head_item (flip_run r) = run_head_item r by rewrite /run_head_item flip_run_items.
  split_and!.
  - (* fits *)
    move=> r0 Hr0. rewrite Hnew in Hr0.
    apply elem_of_cons in Hr0 as [-> | Hr0].
    + rewrite /run_fits Hck flip_run_items. exact (Hfits r Hrmem).
    + apply Hfits. rewrite Hold. apply elem_of_cons. by right.
  - (* disjoint *)
    have Hdisj1 : runs_disjoint (r :: rest) := runs_disjoint_perm _ _ Hold Hdisj.
    apply (runs_disjoint_perm (flip_run r :: rest)); [by symmetry |].
    move=> i j r1 r2 Hi Hj Hij Hcl12.
    destruct i as [|i']; destruct j as [|j']; simpl in Hi, Hj; simplify_eq.
    + (* flipped vs rest *)
      have := Hdisj1 0%nat (S j') r r2 ltac:(done) ltac:(rewrite /= Hj //) ltac:(lia)
                ltac:(by rewrite -Hcl).
      rewrite Hck flip_run_items. done.
    + (* rest vs flipped *)
      have := Hdisj1 (S i') 0%nat r1 r ltac:(rewrite /= Hi //) ltac:(done) ltac:(lia)
                ltac:(by rewrite Hcl12 Hcl).
      rewrite Hck flip_run_items. done.
    + (* rest vs rest *)
      exact (Hdisj1 (S i') (S j') r1 r2 ltac:(rewrite /= Hi //) ltac:(rewrite /= Hj //)
               ltac:(lia) Hcl12).
  - (* origin clock *)
    move=> r0 Hr0. rewrite Hnew in Hr0.
    apply elem_of_cons in Hr0 as [-> | Hr0].
    + rewrite /run_origin_clk Hhd Hcl Hck. exact (Hoclk r Hrmem).
    + apply Hoclk. rewrite Hold. apply elem_of_cons. by right.
Qed.

(** [pool_after_delete] is a preorder, contains one split, and contains
    one tombstoning: the laws the delete loops step their invariant by. *)
Lemma pool_after_delete_refl (p : pool) : pool_after_delete p p.
Proof.
  split_and!.
  - move=> q tm' Hq. exists tm'. done.
  - done.
  - move=> r' Hr' Hd. exists r'. done.
  - move=> r Hr Hd y Hy. exists r. done.
  - apply runs_within_refl.
Qed.

Lemma pool_after_delete_trans (p1 p2 p3 : pool) :
  pool_after_delete p1 p2 -> pool_after_delete p2 p3 -> pool_after_delete p1 p3.
Proof.
  move=> [A1 [A2 [A3 [A4 A5]]]] [B1 [B2 [B3 [B4 B5]]]].
  split_and!.
  - move=> q tm3 Hq. destruct (B1 q tm3 Hq) as (tm2 & Hq2 & Harr2).
    destruct (A1 q tm2 Hq2) as (tm1 & Hq1 & Harr1).
    exists tm1. split; [exact Hq1 | congruence].
  - move=> q Hq. apply B2, A2, Hq.
  - move=> r3 Hr3 Hd3. destruct (B3 r3 Hr3 Hd3) as (r2 & Hr2 & Hd2 & Hin2).
    destruct (A3 r2 Hr2 Hd2) as (r1 & Hr1 & Hd1 & Hin1).
    exists r1. split_and!; [exact Hr1 | exact Hd1 | move=> y Hy; apply Hin1, Hin2, Hy].
  - move=> r1 Hr1 Hd1 y Hy. destruct (A4 r1 Hr1 Hd1 y Hy) as (r2 & Hr2 & Hd2 & Hy2).
    exact (B4 r2 Hr2 Hd2 y Hy2).
  - exact (runs_within_trans _ _ _ A5 B5).
Qed.

Lemma pool_after_split_delete (p p' : pool) (parent : loc) (k : nat) :
  pool_after_split p p' parent k -> pool_after_delete p p'.
Proof.
  move=> [H1 [H2 [_ [_ [_ [H7 [H8 H9]]]]]]].
  split_and!; [| exact H2 | exact H8 | exact H9 | exact H7].
  move=> q tm' Hq. destruct (H1 q tm' Hq) as (tm & Hq0 & Harr & _). eauto.
Qed.

(** [all_runs] around one split: the two halves in place of the split run,
    everything else untouched. *)
Lemma all_runs_split_perm (p : pool) (parent : loc) (tm : type_model) (k o : nat) (r : ItemRun) :
  p !! parent = Some tm ->
  tm_runs tm !! k = Some r ->
  all_runs (<[parent := MkTypeModel (split_runs (tm_runs tm) k o) (tm_arr tm)]> p)
    ≡ₚ split_run_left r o :: split_run_right r o
       :: (take k (tm_runs tm) ++ drop (S k) (tm_runs tm) ++ all_runs (delete parent p)) ∧
  all_runs p ≡ₚ r :: (take k (tm_runs tm) ++ drop (S k) (tm_runs tm) ++ all_runs (delete parent p)).
Proof.
  move=> Hp Hrk.
  have Hmid := take_drop_middle (tm_runs tm) k r Hrk.
  have Hsplit : split_runs (tm_runs tm) k o
              = take k (tm_runs tm)
                ++ [split_run_left r o; split_run_right r o] ++ drop (S k) (tm_runs tm).
  { rewrite /split_runs Hrk //. }
  split.
  - rewrite (all_runs_insert p parent tm _ Hp) /= Hsplit.
    rewrite -!app_assoc /=.
    rewrite -Permutation_middle.
    rewrite -Permutation_middle //.
  - rewrite (all_runs_lookup p parent tm Hp).
    rewrite -{1}Hmid -app_assoc /=.
    rewrite -Permutation_middle //.
Qed.

(** [pool_after_split] holds of no change, and of one [split_runs] surgery
    at a proper offset of a chained run: what the direct run-granular
    proofs of the split helpers report. *)
Lemma pool_after_split_refl (p : pool) (parent : loc) (k : nat) :
  pool_after_split p p parent k.
Proof.
  split_and!.
  - move=> q tm' Hq. exists tm'. done.
  - done.
  - move=> q tm k' r Hq Hr _. apply (elem_of_all_runs p r). eauto using list_elem_of_lookup_2.
  - move=> ccl clk q tm k0 r Hq Hr Hcl Hlo Hhi. exists tm, k0, r. split_and!; try done. by left.
  - move=> q tm tm' Hq Hq' _. congruence.
  - apply runs_within_refl.
  - move=> r' Hr' Hd. exists r'. done.
  - move=> r Hr Hd y Hy. exists r. done.
Qed.

Lemma pool_after_split_of_split_runs (p : pool) (parent : loc) (tm : type_model)
    (k o : nat) (r : ItemRun) :
  p !! parent = Some tm ->
  tm_runs tm !! k = Some r ->
  run_wf (run_items r) ->
  (0 < o < length (run_items r))%nat ->
  pool_after_split p (<[parent := MkTypeModel (split_runs (tm_runs tm) k o) (tm_arr tm)]> p) parent k.
Proof.
  move=> Hp Hrk Hwf Ho.
  set (tm' := MkTypeModel (split_runs (tm_runs tm) k o) (tm_arr tm)).
  set (rest := take k (tm_runs tm) ++ drop (S k) (tm_runs tm) ++ all_runs (delete parent p)).
  destruct (all_runs_split_perm p parent tm k o r Hp Hrk) as [Hnew Hold].
  destruct (split_run_facts r o Hwf Ho)
    as (Hheadl & Hlenl & Hlenr & Hclientl & Hclientr & Hclockl & Hclockr).
  have Hrmem : r ∈ all_runs p by (rewrite Hold; apply list_elem_of_here).
  have Hrestin : ∀ r0, r0 ∈ rest -> r0 ∈ all_runs p.
  { move=> r0 Hr0. rewrite Hold. apply elem_of_cons. by right. }
  have Hitemsl : run_items (split_run_left r o) = take o (run_items r) by done.
  have Hitemsr : run_items (split_run_right r o) = drop o (run_items r) by done.
  have Hdell : run_deleted (split_run_left r o) = run_deleted r by done.
  have Hdelr : run_deleted (split_run_right r o) = run_deleted r by done.
  split_and!.
  - (* documents and flattens survive *)
    move=> q tmq Hq. destruct (decide (parent = q)) as [<- | Hne].
    + rewrite lookup_insert_eq in Hq. injection Hq as <-. exists tm.
      split_and!; [done | done | exact (split_runs_flatten _ _ _ _ Hrk)].
    + rewrite lookup_insert_ne in Hq; last exact Hne. exists tmq. done.
  - (* no type disappears *)
    move=> q Hq. destruct (decide (parent = q)) as [<- | Hne].
    + rewrite lookup_insert_eq. done.
    + rewrite lookup_insert_ne; [exact Hq | exact Hne].
  - (* every run away from the split spot survives *)
    move=> q tmq k' r' Hq Hr' Hnot.
    apply (elem_of_all_runs_insert p parent tm tm' r' Hp).
    destruct (decide (parent = q)) as [<- | Hne].
    + left. rewrite Hq in Hp. injection Hp as <-. simpl.
      destruct (decide (k' < k)%nat) as [Hlt | Hge].
      * apply list_elem_of_lookup. exists k'. rewrite (split_runs_lookup_before _ _ _ _ _ Hrk Hlt) //.
      * have Hgt : (k < k')%nat.
        { destruct (decide (k' = k)) as [-> | Hne']; [exfalso; apply Hnot; done | lia]. }
        apply list_elem_of_lookup. exists (S k'). rewrite (split_runs_lookup_after _ _ _ _ _ Hrk Hgt) //.
    + right. apply (elem_of_all_runs (delete parent p) r'). exists q, tmq.
      rewrite lookup_delete_ne; [| exact Hne]. split; [exact Hq | exact (list_elem_of_lookup_2 _ _ _ Hr')].
  - (* a covered clock stays covered in the same type *)
    move=> ccl clk q tmq k0 r0 Hq Hr0 Hcl Hlo Hhi.
    destruct (decide (parent = q)) as [<- | Hne]; last first.
    { exists tmq, k0, r0. rewrite lookup_insert_ne; last exact Hne. split_and!; try done. by left. }
    rewrite Hq in Hp. injection Hp as <-.
    exists tm'. rewrite lookup_insert_eq.
    destruct (decide (k0 = k)) as [-> | Hnek]; last first.
    { destruct (decide (k0 < k)%nat) as [Hlt | Hge].
      - exists k0, r0. rewrite /tm' /= (split_runs_lookup_before _ _ _ _ _ Hrk Hlt).
        split_and!; try done. by left.
      - have Hgt : (k < k0)%nat by lia.
        exists (S k0), r0. rewrite /tm' /= (split_runs_lookup_after _ _ _ _ _ Hrk Hgt).
        split_and!; try done. by left. }
    rewrite Hrk in Hr0. injection Hr0 as <-.
    have Hlen1 : (1 < length (run_items r))%nat by lia.
    destruct (decide (clk < run_clock r + o)%nat) as [Hleft | Hright].
    + exists k, (split_run_left r o).
      split_and!.
      * done.
      * exact (split_runs_lookup_left _ _ _ _ Hrk).
      * rewrite Hclientl. exact Hcl.
      * rewrite Hclockl. lia.
      * rewrite Hclockl Hlenl. lia.
      * right. done.
    + exists (S k), (split_run_right r o).
      split_and!.
      * done.
      * exact (split_runs_lookup_right _ _ _ _ Hrk).
      * rewrite Hclientr. exact Hcl.
      * rewrite Hclockr. lia.
      * rewrite Hclockr Hlenr. lia.
      * right. done.
  - (* a type of one-char runs is untouched *)
    move=> q tmq tmq' Hq Hq' Hunit.
    destruct (decide (parent = q)) as [<- | Hne].
    + rewrite Hq in Hp. injection Hp as <-.
      exfalso. have Hu := Forall_lookup_1 _ _ _ _ Hunit Hrk. lia.
    + rewrite lookup_insert_ne in Hq'; last exact Hne.
      rewrite Hq in Hq'. by injection Hq' as ->.
  - (* every new run sits inside an old one *)
    move=> r' Hr'. rewrite Hnew in Hr'.
    apply elem_of_cons in Hr' as [-> | Hr'].
    { exists r. split_and!; [exact Hrmem | exact Hclientl | rewrite Hclockl; lia | rewrite Hclockl Hlenl; lia]. }
    apply elem_of_cons in Hr' as [-> | Hr'].
    { exists r. split_and!; [exact Hrmem | exact Hclientr | rewrite Hclockr; lia | rewrite Hclockr Hlenr; lia]. }
    exists r'. split_and!; [exact (Hrestin r' Hr') | done | lia | lia].
  - (* live chars refine *)
    move=> r' Hr' Hlive. rewrite Hnew in Hr'.
    apply elem_of_cons in Hr' as [-> | Hr'].
    { exists r. split_and!; [exact Hrmem | rewrite -Hdell // |].
      move=> y Hy. rewrite Hitemsl in Hy. apply elem_of_take in Hy as (i & Hi & _).
      exact (list_elem_of_lookup_2 _ _ _ Hi). }
    apply elem_of_cons in Hr' as [-> | Hr'].
    { exists r. split_and!; [exact Hrmem | rewrite -Hdelr // |].
      move=> y Hy. rewrite Hitemsr in Hy. apply list_elem_of_lookup in Hy as (i & Hi).
      rewrite lookup_drop in Hi. exact (list_elem_of_lookup_2 _ _ _ Hi). }
    exists r'. split_and!; [exact (Hrestin r' Hr') | exact Hlive | done].
  - (* dead chars stay dead *)
    move=> r0 Hr0 Hdead y Hy. rewrite Hold in Hr0.
    apply elem_of_cons in Hr0 as [-> | Hr0].
    { rewrite -(take_drop o (run_items r)) in Hy. apply elem_of_app in Hy as [Hy | Hy].
      - exists (split_run_left r o). split_and!;
          [rewrite Hnew; apply list_elem_of_here | rewrite Hdell // | rewrite Hitemsl //].
      - exists (split_run_right r o). split_and!;
          [rewrite Hnew; apply elem_of_cons; right; apply list_elem_of_here | rewrite Hdelr // | rewrite Hitemsr //]. }
    exists r0. split_and!; [| exact Hdead | exact Hy].
    rewrite Hnew. apply elem_of_cons; right. apply elem_of_cons; right. exact Hr0.
Qed.

(** [pool_after_repair] is reflexive, transitive, and contains one
    split: what composes [store.repair]'s at most two split steps. *)
Lemma pool_after_repair_refl (p : pool) : pool_after_repair p p.
Proof.
  split_and!.
  - move=> q tm' Hq. exists tm'. done.
  - done.
  - move=> q tm tm' Hq Hq' _. congruence.
  - apply runs_within_refl.
  - move=> r' Hr' Hd. exists r'. done.
Qed.

Lemma pool_after_repair_of_split (p p' : pool) (parent : loc) (k : nat) :
  pool_after_split p p' parent k -> pool_after_repair p p'.
Proof.
  move=> [H1 [H2 [_ [_ [H6 [H7 [H8 _]]]]]]].
  split_and!; [exact H1 | exact H2 | exact H6 | exact H7 | exact H8].
Qed.

Lemma pool_after_repair_trans (p1 p2 p3 : pool) :
  pool_after_repair p1 p2 -> pool_after_repair p2 p3 -> pool_after_repair p1 p3.
Proof.
  move=> [A1 [A2 [A3 [A4 A5]]]] [B1 [B2 [B3 [B4 B5]]]].
  split_and!.
  - move=> q tm3 Hq. destruct (B1 q tm3 Hq) as (tm2 & Hq2 & Harr2 & Hfl2).
    destruct (A1 q tm2 Hq2) as (tm1 & Hq1 & Harr1 & Hfl1).
    exists tm1. split_and!; [exact Hq1 | congruence | congruence].
  - move=> q Hq. apply B2, A2, Hq.
  - move=> q tm tm' Hq Hq' Hunit.
    destruct (A2 q (mk_is_Some _ _ Hq)) as [tm2 Hq2].
    have Heq2 : tm2 = tm := A3 q tm tm2 Hq Hq2 Hunit.
    subst tm2. exact (B3 q tm tm' Hq2 Hq' Hunit).
  - exact (runs_within_trans _ _ _ A4 B4).
  - move=> r3 Hr3 Hd3. destruct (B5 r3 Hr3 Hd3) as (r2 & Hr2 & Hd2 & Hin2).
    destruct (A5 r2 Hr2 Hd2) as (r1 & Hr1 & Hd1 & Hin1).
    exists r1. split_and!; [exact Hr1 | exact Hd1 | move=> y Hy; apply Hin1, Hin2, Hy].
Qed.



Lemma pool_after_delete_flip (p : pool) (parent : loc) (tm : type_model) (k : nat) (r : ItemRun) :
  p !! parent = Some tm ->
  tm_runs tm !! k = Some r ->
  pool_after_delete p (<[parent := MkTypeModel (<[k := flip_run r]> (tm_runs tm)) (tm_arr tm)]> p).
Proof.
  move=> Hp Hrk.
  set (tm' := MkTypeModel (<[k := flip_run r]> (tm_runs tm)) (tm_arr tm)).
  have Hmem : ∀ r', r' ∈ all_runs (<[parent := tm']> p) ->
      r' = flip_run r ∨ r' ∈ all_runs p.
  { move=> r' Hr'. apply (elem_of_all_runs_insert p parent tm tm' r' Hp) in Hr'.
    destruct Hr' as [Hr' | Hr'].
    - simpl in Hr'. apply elem_of_list_insert_inv in Hr' as [-> | Hr']; [by left |].
      right. apply (elem_of_all_runs_lookup p parent tm r' Hp). by left.
    - right. apply (elem_of_all_runs_lookup p parent tm r' Hp). by right. }
  split_and!.
  - move=> q tmq Hq. destruct (decide (parent = q)) as [<- | Hne].
    + rewrite lookup_insert_eq in Hq. injection Hq as <-. exists tm. done.
    + rewrite lookup_insert_ne in Hq; last exact Hne. exists tmq. done.
  - move=> q Hq. destruct (decide (parent = q)) as [<- | Hne].
    + rewrite lookup_insert_eq. done.
    + rewrite lookup_insert_ne; last exact Hne. exact Hq.
  - move=> r' Hr' Hd. destruct (Hmem r' Hr') as [-> | Hr0].
    + rewrite /flip_run /= in Hd. discriminate.
    + exists r'. done.
  - move=> r0 Hr0 Hd y Hy.
    apply (elem_of_all_runs_lookup p parent tm r0 Hp) in Hr0.
    destruct Hr0 as [Hr0 | Hr0]; last first.
    { exists r0. split_and!; [| exact Hd | exact Hy].
      apply (elem_of_all_runs_insert p parent tm tm' _ Hp). by right. }
    apply list_elem_of_lookup in Hr0 as (i & Hi).
    destruct (decide (k = i)) as [<- | Hne].
    + rewrite Hi in Hrk. injection Hrk as Heq. subst r0.
      exists (flip_run r). split_and!.
      * apply (elem_of_all_runs_insert p parent tm tm' _ Hp). left. simpl.
        apply list_elem_of_insert. apply lookup_lt_Some in Hi. exact Hi.
      * done.
      * rewrite flip_run_items. exact Hy.
    + exists r0. split_and!; [| exact Hd | exact Hy].
      apply (elem_of_all_runs_insert p parent tm tm' _ Hp). left. simpl.
      apply list_elem_of_lookup. exists i.
      rewrite list_lookup_insert_ne; [exact Hi | exact Hne].
  - move=> r' Hr'. destruct (Hmem r' Hr') as [-> | Hr0].
    + exists r. split_and!;
        [| rewrite /run_client /run_head_item flip_run_items //
         | rewrite /run_clock /run_head_item flip_run_items //
         | rewrite /run_clock /run_head_item flip_run_items //].
      apply (elem_of_all_runs_lookup p parent tm r Hp). left.
      exact (list_elem_of_lookup_2 _ _ _ Hrk).
    + exists r'. split_and!; [exact Hr0 | reflexivity | lia | lia].
Qed.

(** The tombstone record survives a step that keeps dead chars dead. *)
Lemma ids_tombstoned_runs_dead_kept (ids : gset YjsId) (p p' : pool) :
  runs_dead_kept p p' ->
  ids_tombstoned_runs ids (all_runs p) ->
  ids_tombstoned_runs ids (all_runs p').
Proof.
  move=> Hkept H i Hi. destruct (H i Hi) as (r & Hr & Hd & Hin).
  rewrite /char_ids elem_of_list_to_set in Hin.
  apply list_elem_of_fmap in Hin as (y & Hid & Hy).
  destruct (Hkept r Hr Hd y Hy) as (r' & Hr' & Hd' & Hy').
  exists r'. split_and!; [exact Hr' | exact Hd' |].
  rewrite /char_ids elem_of_list_to_set. apply list_elem_of_fmap. eauto.
Qed.

(** The apply path's step records at run granularity (the loc-free
    [cells_within_or_from] / [apply_live_refine] / [integrate_live_refine]
    of [store/value_cells] and [store/value_live]).

    [runs_within_or_from inputs before after]: every run of [after] sits
    inside a run of [before] or inside the clock range of one of the
    integrated [inputs]. [runs_apply_live_refine m before after]: every char
    of a live run of [after] sat in a live run of [before] or is an id the
    model [m] did not have (a char this apply integrated).
    [runs_integrate_live_refine input before after]: the same with "is one
    of [input]'s own chars" as the escape, what one integrate step reports.
    Used as: the loop invariant and the postcondition of
    [wp_store__applyUpdate_unlocked] and the postcondition of
    [wp_store__integrateDecoded_runs]. *)
Definition runs_within_or_from (inputs : list (TId * IntegrateInput (A := A)))
    (before after : list ItemRun) : Prop :=
  ∀ r, r ∈ after ->
    (∃ r0, r0 ∈ before ∧ run_client r = run_client r0 ∧
       (run_clock r0 <= run_clock r)%nat ∧
       (run_clock r + length (run_items r) <= run_clock r0 + length (run_items r0))%nat) ∨
    (∃ typedInput : TId * IntegrateInput (A := A), typedInput ∈ inputs ∧
       run_client r = clientId (in_id typedInput.2) ∧
       (clock (in_id typedInput.2) <= run_clock r)%nat ∧
       (run_clock r + length (run_items r) <=
        clock (in_id typedInput.2) + length (in_content typedInput.2))%nat).

Definition runs_apply_live_refine (m : DocModel) (before after : list ItemRun) : Prop :=
  ∀ r', r' ∈ after -> run_deleted r' = false -> ∀ y, y ∈ run_items r' ->
    (∃ r, r ∈ before ∧ run_deleted r = false ∧ y ∈ run_items r)
    ∨ doc_model_has m (item_id y) = false.

Definition runs_integrate_live_refine (input : IntegrateInput (A := A))
    (before after : list ItemRun) : Prop :=
  ∀ r', r' ∈ after -> run_deleted r' = false -> ∀ y, y ∈ run_items r' ->
    (∃ r, r ∈ before ∧ run_deleted r = false ∧ y ∈ run_items r)
    ∨ (clientId (item_id y) = clientId (in_id input) ∧
       (clock (in_id input) <= clock (item_id y))%nat).

(** [runs_within_or_from] is reflexive and composes across a step whose
    inputs are appended; [runs_apply_live_refine] is reflexive, transitive
    against a growing model, and follows from one integrate step under the
    replay's client bound. *)
Lemma runs_within_or_from_refl (inputs : list (TId * IntegrateInput (A := A)))
    (runs : list ItemRun) :
  runs_within_or_from inputs runs runs.
Proof.
  move=> r Hr. left. exists r. split_and!; [exact Hr | reflexivity | lia | lia].
Qed.

Lemma runs_within_or_from_trans (inputs1 inputs2 : list (TId * IntegrateInput (A := A)))
    (r1 r2 r3 : list ItemRun) :
  runs_within_or_from inputs1 r1 r2 ->
  runs_within_or_from inputs2 r2 r3 ->
  runs_within_or_from (inputs1 ++ inputs2) r1 r3.
Proof.
  move=> H12 H23 r Hr.
  destruct (H23 r Hr) as [(rb & Hrb & Hcl & Hlo & Hhi) | (ti & Hti & Hcl & Hlo & Hhi)].
  - destruct (H12 rb Hrb) as [(ra & Hra & Hcl' & Hlo' & Hhi') | (ti & Hti & Hcl' & Hlo' & Hhi')].
    + left. exists ra. split_and!; [exact Hra | congruence | lia | lia].
    + right. exists ti. split_and!; [apply elem_of_app; by left | congruence | lia | lia].
  - right. exists ti. split_and!; [apply elem_of_app; by right | exact Hcl | exact Hlo | exact Hhi].
Qed.

Lemma runs_apply_live_refine_refl (m : DocModel) (runs : list ItemRun) :
  runs_apply_live_refine m runs runs.
Proof. move=> r' Hr' Hlive y Hy. left. by exists r'. Qed.

Lemma runs_apply_live_refine_trans (m m1 : DocModel) (r0 r1 r2 : list ItemRun) :
  (∀ i, doc_model_has m i = true -> doc_model_has m1 i = true) ->
  runs_apply_live_refine m r0 r1 ->
  runs_apply_live_refine m1 r1 r2 ->
  runs_apply_live_refine m r0 r2.
Proof.
  move=> Hmono H01 H12 r Hr Hlive y Hy.
  destruct (H12 r Hr Hlive y Hy) as [(r' & Hr' & Hlive' & Hy') | Hfresh].
  - exact (H01 r' Hr' Hlive' y Hy').
  - right. destruct (doc_model_has m (item_id y)) eqn:Hm; last done.
    rewrite (Hmono _ Hm) in Hfresh. discriminate.
Qed.

Lemma runs_apply_live_refine_of_integrate (input : IntegrateInput (A := A))
    (mc : DocModel) (before after : list ItemRun) :
  (∀ (t' : TId) x, x ∈ doc_model_get mc t' ->
     clientId (item_id x) = clientId (in_id input) ->
     (clock (item_id x) < clock (in_id input))%nat) ->
  runs_integrate_live_refine input before after ->
  runs_apply_live_refine mc before after.
Proof.
  move=> Hbound Hilr r Hr Hlive y Hy.
  destruct (Hilr r Hr Hlive y Hy) as [Hold | [Hcl Hclk]]; [by left | right].
  destruct (doc_model_has mc (item_id y)) eqn:Hm; last done.
  exfalso. apply docm_has_spec in Hm as (t' & x & Hx & Hid).
  have Hcx : clientId (item_id x) = clientId (in_id input) by rewrite Hid.
  have := Hbound t' x Hx Hcx. rewrite Hid. lia.
Qed.

(** [all_runs] around one integrate splice: the fresh run and the old pool. *)
Lemma all_runs_splice_perm (p : pool) (parent : loc) (tm : type_model) (idx : nat)
    (r : ItemRun) (arr' : list (YjsItem A)) :
  p !! parent = Some tm ->
  all_runs (<[parent := MkTypeModel (take idx (tm_runs tm) ++ r :: drop idx (tm_runs tm)) arr']> p)
    ≡ₚ r :: all_runs p.
Proof.
  move=> Hp.
  rewrite (all_runs_insert p parent tm _ Hp) /= (all_runs_lookup p parent tm Hp).
  rewrite -app_assoc /=.
  rewrite -Permutation_middle.
  apply Permutation_cons; first done.
  rewrite app_assoc take_drop //.
Qed.

(** A fresh empty type adds no run. *)
Lemma all_runs_insert_empty (p : pool) (q : loc) (arr : list (YjsItem A)) :
  p !! q = None ->
  all_runs (<[q := MkTypeModel [] arr]> p) ≡ₚ all_runs p.
Proof.
  move=> Hq. rewrite /all_runs.
  apply (concat_perm (tm_runs <$> (map_to_list (<[q := MkTypeModel [] arr]> p)).*2)
                     ([] :: (tm_runs <$> (map_to_list p).*2))).
  rewrite (map_to_list_insert p q _ Hq) /=. reflexivity.
Qed.

(** [runs_integrate_live_refine] composes, follows from [runs_live_refine],
    and holds of a splice whose new run carries the item's own chars. *)
Lemma runs_integrate_live_refine_trans (input : IntegrateInput (A := A))
    (r0 r1 r2 : list ItemRun) :
  runs_integrate_live_refine input r0 r1 ->
  runs_integrate_live_refine input r1 r2 ->
  runs_integrate_live_refine input r0 r2.
Proof.
  move=> H01 H12 r Hr Hlive y Hy.
  destruct (H12 r Hr Hlive y Hy) as [(r' & Hr' & Hlive' & Hy') | Hnew]; last by right.
  exact (H01 r' Hr' Hlive' y Hy').
Qed.

Lemma runs_integrate_live_refine_of_live_refine (input : IntegrateInput (A := A)) (p p' : pool) :
  runs_live_refine p p' ->
  runs_integrate_live_refine input (all_runs p) (all_runs p').
Proof.
  move=> Hlr r' Hr' Hlive y Hy. left.
  destruct (Hlr r' Hr' Hlive) as (r & Hr & Hliver & Hin).
  exists r. split_and!; [exact Hr | exact Hliver | exact (Hin y Hy)].
Qed.

Lemma runs_integrate_live_refine_snoc (input : IntegrateInput (A := A))
    (runs runs' : list ItemRun) (r : ItemRun) :
  runs' ≡ₚ r :: runs ->
  (∀ y, y ∈ run_items r -> clientId (item_id y) = clientId (in_id input) ∧
     (clock (in_id input) <= clock (item_id y))%nat) ->
  runs_integrate_live_refine input runs runs'.
Proof.
  move=> Hperm Hnew r' Hr' Hlive y Hy. rewrite Hperm in Hr'.
  apply elem_of_cons in Hr' as [-> | Hr'].
  - right. exact (Hnew y Hy).
  - left. by exists r'.
Qed.

(** [runs_within] is the origin-free half of [runs_within_or_from]. *)
Lemma runs_within_or_from_of_within (inputs : list (TId * IntegrateInput (A := A)))
    (before after : list ItemRun) :
  runs_within before after ->
  runs_within_or_from inputs before after.
Proof.
  move=> Hw r Hr. destruct (Hw r Hr) as (r0 & Hr0 & Hcl & Hlo & Hhi).
  left. exists r0. split_and!; [exact Hr0 | exact Hcl | exact Hlo | exact Hhi].
Qed.


(** [pool_run_clock_below p id]: every run of [id]'s client in the pool ends
    at or below [id]'s clock: the item about to be integrated is its client's
    newest, [pool_clock_below] with the [w64] comparisons replaced by [nat]
    ones (a run is nonempty, so the strict head bound follows). *)
Definition pool_run_clock_below (p : pool) (id : YjsId) : Prop :=
  ∀ r, r ∈ all_runs p -> run_client r = clientId id ->
    (run_clock r + length (run_items r) <= clock id)%nat.

(** Per-char op expansion of a wire batch (issue #28 U7c), lifted here from
    [store/GetNode] (which had defined it downstream). The pending-buffer
    certificate [Hpendcert] must be stated PER-CHAR
    ([is_pending_certified (expand_inputs pend)]): the ghost op history holds
    one certificate per character, so a multi-char wire item's head-id op is
    not itself in the log, only its per-char ops are. The bulk of the
    [expand_input] theory (lookup / length / singleton / chunk chaining) stays
    in [store/GetNode]; only the two definitions live here so [own_store] and
    [store_inv_excl] can name them. *)
Definition expand_input (typedInput : TId * IntegrateInput (A := A)) : list (TId * IntegrateInput (A := A)) :=
  (λ op, (typedInput.1, op)) <$> ops_of_input typedInput.2 (explode (in_content typedInput.2)).

Definition expand_inputs (inputs : list (TId * IntegrateInput (A := A))) : list (TId * IntegrateInput (A := A)) :=
  mjoin (expand_input <$> inputs).

(** [input_fits input]: the wire item's chars fit a word of clocks (the 2^64
    no-wrap seam per struct); what lets its cell satisfy [cell_fits]. *)
Definition input_fits (input : IntegrateInput (A := A)) : Prop :=
  (Z.of_nat (clock (in_id input)) + Z.of_nat (length (in_content input)) < 2^64)%Z.

(** [pending_item_rooted]/[is_pending_rooted] (issue #40, weakened in #54):
    every HEAD struct of a decoded buffer (both origins absent, so it carries
    its root's name on the wire) targets a named root [RootId nm]. Issue #49
    additionally required that root to be ALREADY REGISTERED ([is_root γs nm]);
    issue #54 LIFTS that pre-bound-roots restriction now that
    [getOrCreateYType]'s miss branch is verified -- a head struct may target a
    not-yet-created root, which [applyUpdate]'s drain registers on first use.
    All that remains is that the target is a root and not an [AnchorId]
    (Parent::Id / type-as-item is out of the verified subset, #43). With the
    registration ([is_root], the only resource-bearing conjunct) gone, this is
    a pure syntactic fact about the batch, so it is a [Prop] (carried as
    [⌜..⌝] where an [iProp] is expected) and mentions no store; the wire
    protocol ([yjs_prot], issue #107) states rootedness over it directly.
    Structs WITH an origin derive their binding from the origin's arrival at
    integration time, so carry no obligation here. *)
Definition pending_item_rooted
    (typedInput : TId * IntegrateInput (A := A)) : Prop :=
  if decide (in_originId typedInput.2 = None ∧ in_rightOriginId typedInput.2 = None)
  then (∃ nm : P, typedInput.1 = RootId nm)
  else True.

Definition is_pending_rooted
    (pending : list (TId * IntegrateInput (A := A))) : Prop :=
  ∀ typedInput, typedInput ∈ pending -> pending_item_rooted typedInput.

(** [update_wf inputs]: what a batch must satisfy to be applied: every
    struct's chars fit a word of clocks ([input_fits]) and origin-free structs
    name a root type ([is_pending_rooted]). Facts about the
    sender's output, so the wire protocol ([yjs_prot]) states them and
    [applyUpdate] / [Doc.ApplySyncUpdate] assume them. *)
Definition update_wf (inputs : list (TId * IntegrateInput (A := A))) : Prop :=
  (∀ typedInput : TId * IntegrateInput (A := A), typedInput ∈ inputs -> input_fits typedInput.2) ∧
  is_pending_rooted inputs.

(* ----- accepted-id no-loss layer (this branch) ---------------------------- *)

(** The ids currently held in the pending buffer. *)
Definition pending_id_set (pend : list (TId * IntegrateInput (A := A))) : gset YjsId :=
  list_to_set ((λ x, in_id x.2) <$> pend).

(** The store invariant's no-loss coherence: every accepted id is either
    delivered into the history [h] or currently buffered in [pend]. Because
    [acc] only grows and the RHS is re-established by every store op, an
    accepted id is never dropped without being delivered. *)
Definition accepted_coh (acc : gset YjsId) (h : list Ev)
    (pend : list (TId * IntegrateInput (A := A))) : Prop :=
  acc ⊆ delivered_ids h ∪ pending_id_set pend.

(** Delete-set domain (docs/plan-delete-set.md, D1): every deleted id names
    an integrated item of the current doc model. Stated over the MODEL, so
    the store ops transport it with the model lemmas they already produce
    ([docm_has_integrate_mono], [ValidReplay_mem]); the cells-level tombstone
    mirror ([deleted_match]) is the D2 half. *)
Definition delete_set_dom (delete_set : gset YjsId) (m : DocModel) : Prop :=
  ∀ i, i ∈ delete_set -> doc_model_has m i = true.

(** The two transport laws of [delete_set_dom]: pointwise model growth, and the
    applyUpdate batch step. *)
Lemma delete_set_dom_mono (delete_set : gset YjsId) (m m' : DocModel) :
  (∀ i, doc_model_has m i = true -> doc_model_has m' i = true) ->
  delete_set_dom delete_set m -> delete_set_dom delete_set m'.
Proof. move=> Hmono Hdom i Hi. exact (Hmono i (Hdom i Hi)). Qed.

Lemma delete_set_dom_grow (delete_set S : gset YjsId) (m : DocModel) :
  delete_set_dom delete_set m -> (∀ i, i ∈ S -> doc_model_has m i = true) ->
  delete_set_dom (delete_set ∪ S) m.
Proof.
  move=> Hdom HS i /elem_of_union [Hi | Hi]; [exact (Hdom i Hi) | exact (HS i Hi)].
Qed.

(** Growing ONE type's list (the [Text.Insert] step): ids present before are
    present after. *)
Lemma delete_set_dom_insert (delete_set : gset YjsId) (m : DocModel) (t : TId)
    (arr' : list (YjsItem A)) :
  (∀ x, x ∈ doc_model_get m t -> x ∈ arr') ->
  delete_set_dom delete_set m -> delete_set_dom delete_set (<[t := arr']> m).
Proof.
  move=> Hgrow. apply delete_set_dom_mono => i /docm_has_spec [t0 [x [Hx Hid]]].
  apply docm_has_spec.
  destruct (decide (t0 = t)) as [-> | Hne].
  - exists t, x. rewrite docm_get_insert_eq. split; [exact (Hgrow x Hx) | exact Hid].
  - exists t0, x. rewrite docm_get_insert_ne //.
Qed.

Lemma delete_set_dom_ValidReplay (delete_set : gset YjsId)
    (inputs : list (TId * IntegrateInput (A := A))) (m m' : DocModel) :
  ValidReplay inputs m m' -> delete_set_dom delete_set m -> delete_set_dom delete_set m'.
Proof.
  move=> Hvr. apply delete_set_dom_mono => i /docm_has_spec [t [x [Hx Hid]]].
  apply docm_has_spec. exists t, x.
  split; [exact (ValidReplay_mem inputs m m' Hvr t x Hx) | exact Hid].
Qed.

Definition wire_integrate (m : DocModel) (typedInput : TId * IntegrateInput (A := A))
    : option (list (YjsItem A)) :=
  integrate_all (ops_of_input typedInput.2 (explode (in_content typedInput.2))) (doc_model_get m typedInput.1).

Fixpoint wire_pass (m : DocModel) (pending kept : list (TId * IntegrateInput (A := A)))
    : list (TId * IntegrateInput (A := A)) * list (TId * IntegrateInput (A := A)) * DocModel :=
  match pending with
  | [] => ([], kept, m)
  | typedInput :: tl =>
      if doc_model_has m (in_id typedInput.2) then wire_pass m tl kept
      else if input_ready m typedInput.2 then
        match wire_integrate m typedInput with
        | Some arr' =>
            let '(app, kept', m') := wire_pass (<[typedInput.1 := arr']> m) tl kept in
            (typedInput :: app, kept', m')
        | None => wire_pass m tl (pending_keep kept typedInput)
        end
      else wire_pass m tl (pending_keep kept typedInput)
  end.

Fixpoint wire_drain_aux (fuel : nat) (m : DocModel)
    (pending : list (TId * IntegrateInput (A := A)))
    : list (TId * IntegrateInput (A := A)) * list (TId * IntegrateInput (A := A)) * DocModel :=
  match fuel with
  | 0%nat => ([], pending, m)
  | S f =>
      let '(app, kept, m') := wire_pass m pending [] in
      match app with
      | [] => ([], kept, m')
      | _ :: _ =>
          let '(app2, rest, m'') := wire_drain_aux f m' kept in
          (app ++ app2, rest, m'')
      end
  end.

Definition wire_drain (m : DocModel) (pending : list (TId * IntegrateInput (A := A)))
    : list (TId * IntegrateInput (A := A)) * list (TId * IntegrateInput (A := A)) * DocModel :=
  wire_drain_aux (S (length pending)) m pending.

(** The wire-level replay view of a drain: each applied wire item was fresh and
    ready and its whole op chunk integrated ([wire_integrate]). Mirrors
    [PendingReplay] with [integrate] replaced by [wire_integrate]. *)
Inductive WireReplay : DocModel -> list (TId * IntegrateInput (A := A)) -> DocModel -> Prop :=
  | WireReplay_nil m : WireReplay m [] m
  | WireReplay_cons m typedInput arr' rest m' :
      doc_model_has m (in_id typedInput.2) = false ->
      input_ready m typedInput.2 = true ->
      wire_integrate m typedInput = Some arr' ->
      WireReplay (<[typedInput.1 := arr']> m) rest m' ->
      WireReplay m (typedInput :: rest) m'.

(** [wire_ready_total]: along the wire drain, a fresh, ready pending wire item
    always integrates its whole chunk (the exclusion of the ready-but-stuck
    branch: the Go loop integrates on [depsArrived], so its applied set is the
    ready set, which coincides with [wire_pass]'s only when this holds). The
    certificate layer supplies it (a ready certified chunk always folds). *)
Definition wire_ready_total (m : DocModel)
    (pending applied : list (TId * IntegrateInput (A := A))) : Prop :=
  ∀ pre suf mx (typedInput : TId * IntegrateInput (A := A)),
    applied = pre ++ suf -> WireReplay m pre mx ->
    typedInput ∈ pending ->
    doc_model_has mx (in_id typedInput.2) = false ->
    input_ready mx typedInput.2 = true ->
    is_Some (wire_integrate mx typedInput).

(** No-loss accounting for one input [x] after a drain, over the resulting
    delivered history [h'] and the leftover pending buffer [rest]: either [x]'s
    id was DELIVERED into [h'] (registered as some op there, whether freshly
    applied by this batch or already present from a prior delivery) or it is
    BUFFERED by id in [rest]. This is the per-input guarantee that no update is
    silently dropped. (Interference means we cannot pin down WHICH of the two
    happens, nor the exact op, only that one of them does: [wire_drain] dedups
    by id and skips already-integrated ids, so the guarantee is at the id
    level.) *)
Definition input_accounted (h' : list Ev)
    (rest : list (TId * IntegrateInput (A := A)))
    (x : TId * IntegrateInput (A := A)) : Prop :=
  (∃ (t : TId) (input : IntegrateInput (A := A)),
     (t, OpInsert input) ∈ delivered_ops h' ∧ in_id input = in_id x.2) ∨
  (∃ y, y ∈ rest ∧ in_id y.2 = in_id x.2).

Lemma elem_of_pending_id_set (pend : list (TId * IntegrateInput (A := A))) (i : YjsId) :
  i ∈ pending_id_set pend ↔ ∃ x, x ∈ pend ∧ in_id x.2 = i.
Proof.
  rewrite /pending_id_set elem_of_list_to_set list_elem_of_fmap.
  split; [move=> [x [-> Hx]] | move=> [x [Hx <-]]]; by exists x.
Qed.

(** Expansion preserves the target type: every per-char op of a wire batch
    carries the type id of the wire item it came from (issue #125: this is
    how a reader routes an applied input's item to the root it reads). *)
Lemma expand_inputs_tid (inputs : list (TId * IntegrateInput (A := A)))
    (x : TId * IntegrateInput (A := A)) :
  x ∈ expand_inputs inputs -> ∃ x', x' ∈ inputs ∧ x.1 = x'.1.
Proof.
  rewrite /expand_inputs list_elem_of_join.
  move=> [l [Hx Hl]].
  apply list_elem_of_fmap in Hl as (x' & -> & Hx').
  exists x'. split; first exact Hx'.
  move: Hx. rewrite /expand_input list_elem_of_fmap.
  move=> [op [-> _]] //.
Qed.

(** History only grows: an op that appends to [h] (delivered ids only grow) and
    leaves [pend] preserves [accepted_coh]. This is the trivial transport that
    Insert/Delete apply at each store_inv rebuild. *)
Lemma accepted_coh_hist_grow (acc : gset YjsId) (h h' : list Ev)
    (pend : list (TId * IntegrateInput (A := A))) :
  accepted_coh acc h pend -> delivered_ids h ⊆ delivered_ids h' ->
  accepted_coh acc h' pend.
Proof.
  rewrite /accepted_coh => Hcoh Hsub.
  etrans; [exact Hcoh | apply union_mono; [exact Hsub | done]].
Qed.

(** The applyUpdate transport: the drain grows the history ([delivered_ids h ⊆
    delivered_ids h']) and moves each OLD pending id either into the history or
    into the NEW pending [rest]. So the accepted set stays coherent at the new
    (h', rest). *)
Lemma accepted_coh_applyUpdate (acc : gset YjsId) (h h' : list Ev)
    (pend rest : list (TId * IntegrateInput (A := A))) :
  accepted_coh acc h pend ->
  delivered_ids h ⊆ delivered_ids h' ->
  (∀ x, x ∈ pend -> in_id x.2 ∈ delivered_ids h' ∪ pending_id_set rest) ->
  accepted_coh acc h' rest.
Proof.
  rewrite /accepted_coh. move=> Hcoh Hdsub Hpend i Hi.
  destruct (elem_of_union (delivered_ids h) (pending_id_set pend) i) as [Hsplit _].
  destruct (Hsplit (elem_of_weaken _ _ _ Hi Hcoh)) as [Hd | Hp].
  - apply elem_of_union_l. by apply Hdsub.
  - apply elem_of_pending_id_set in Hp as [x [Hx Hxid]]. rewrite -Hxid. exact (Hpend x Hx).
Qed.

(** The per-client clock bound survives a step whose runs sit inside old
    ones. *)
Lemma pool_run_clock_below_within (p p' : pool) (d : YjsId) :
  runs_within (all_runs p) (all_runs p') ->
  pool_run_clock_below p d ->
  pool_run_clock_below p' d.
Proof.
  move=> Hw Hb r' Hr' Hcl.
  destruct (Hw r' Hr') as (r & Hr & Hcl0 & Hlo & Hhi).
  have := Hb r Hr ltac:(congruence). lia.
Qed.

(** The per-client clock bound of a pool at run granularity, from the
    model-level bound on every type's document: a run's last char is its
    head clock plus its length minus one ([run_wf_char_id]), and it sits in
    the type's flatten. What [Text.Insert] feeds [wp_store__Integrate_runs]. *)
Lemma pool_run_clock_below_of_arrs (p : pool) (c k : nat) :
  (∀ q tm, p !! q = Some tm -> tm_arr tm = runs_flatten (tm_runs tm)) ->
  (∀ r, r ∈ all_runs p -> run_wf (run_items r)) ->
  (∀ q tm x, p !! q = Some tm -> x ∈ tm_arr tm -> clientId (item_id x) = c ->
     (clock (item_id x) < k)%nat) ->
  pool_run_clock_below p (MkYjsId c k).
Proof.
  move=> Harr Hwf Hb r Hr Hcl.
  have Hwfr := Hwf r Hr.
  destruct (proj1 (elem_of_all_runs p r) Hr) as (q & tm & Hq & Hrtm).
  have Hlen1 : (1 <= length (run_items r))%nat.
  { destruct (run_items r) eqn:Hrc; [exact (False_ind _ (proj1 Hwfr eq_refl)) | simpl; lia]. }
  destruct (lookup_lt_is_Some_2 (run_items r) (length (run_items r) - 1)%nat ltac:(lia)) as [li Hli].
  apply list_elem_of_lookup_1 in Hrtm as [i Hi].
  have Hin : li ∈ tm_arr tm.
  { rewrite (Harr q tm Hq).
    exact (list_elem_of_lookup_2 _ _ _ (runs_flatten_lookup_of_run (tm_runs tm) i _ r li Hi Hli)). }
  have Hid := run_wf_char_id (run_items r) _ li Hwfr Hli.
  have Hcl' : clientId (item_id (hd inhabitant (run_items r))) = c := Hcl.
  have Hclid : clientId (item_id li) = c by rewrite Hid; exact Hcl'.
  have Hlt := Hb q tm li Hq Hin Hclid.
  have Hlt' : (clock (item_id (hd inhabitant (run_items r))) + (length (run_items r) - 1) < k)%nat
    by rewrite Hid in Hlt; exact Hlt.
  change ((clock (item_id (hd inhabitant (run_items r))) + length (run_items r) <= k)%nat). lia.
Qed.

(** The tombstone-set clause travels along [runs_live_refine] (a split, a
    flip, a registry insert), a permutation of the runs, a growth by a run
    none of whose ids the set holds (an integrate), and a set union or
    shrink. *)
Lemma delete_set_tombstoned_runs_refine (delete_set : gset YjsId) (p p' : pool) :
  runs_live_refine p p' ->
  delete_set_tombstoned_runs delete_set (all_runs p) ->
  delete_set_tombstoned_runs delete_set (all_runs p').
Proof.
  move=> Hlr Ht r' Hr' y Hy Hd.
  destruct (run_deleted r') eqn:Hdel; [done |].
  destruct (Hlr r' Hr' Hdel) as (r & Hr & Hrdel & Hsub).
  have := Ht r Hr y (Hsub y Hy) Hd. congruence.
Qed.

Lemma delete_set_tombstoned_runs_perm (delete_set : gset YjsId) (runs runs' : list ItemRun) :
  runs' ≡ₚ runs ->
  delete_set_tombstoned_runs delete_set runs -> delete_set_tombstoned_runs delete_set runs'.
Proof. move=> Hperm Ht r Hr. apply Ht. by rewrite -Hperm. Qed.

Lemma delete_set_tombstoned_runs_snoc (delete_set : gset YjsId) (runs runs' : list ItemRun) (r : ItemRun) :
  runs' ≡ₚ runs ++ [r] ->
  (∀ y, y ∈ run_items r -> item_id y ∉ delete_set) ->
  delete_set_tombstoned_runs delete_set runs -> delete_set_tombstoned_runs delete_set runs'.
Proof.
  move=> Hperm Hfresh Ht r0 Hr0 y Hy Hd. rewrite Hperm in Hr0.
  apply elem_of_app in Hr0 as [Hr0 | Hr0]; [exact (Ht r0 Hr0 y Hy Hd) |].
  apply list_elem_of_singleton in Hr0 as ->. exfalso. exact (Hfresh y Hy Hd).
Qed.

Lemma delete_set_tombstoned_runs_union (delete_set S : gset YjsId) (runs : list ItemRun) :
  delete_set_tombstoned_runs delete_set runs -> delete_set_tombstoned_runs S runs ->
  delete_set_tombstoned_runs (delete_set ∪ S) runs.
Proof.
  move=> H1 H2 r Hr y Hy Hin. apply elem_of_union in Hin as [Hin | Hin];
    [exact (H1 r Hr y Hy Hin) | exact (H2 r Hr y Hy Hin)].
Qed.

Lemma delete_set_tombstoned_runs_mono (delete_set delete_set' : gset YjsId) (runs : list ItemRun) :
  delete_set' ⊆ delete_set ->
  delete_set_tombstoned_runs delete_set runs -> delete_set_tombstoned_runs delete_set' runs.
Proof. move=> Hsub Ht r Hr y Hy Hin. exact (Ht r Hr y Hy (Hsub _ Hin)). Qed.

End store_model.
