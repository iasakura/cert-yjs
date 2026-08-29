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
    registered type at its [type_model]; [all_runs] and the clock-sorted
    [client_runs]; [run_pool_invs], the pure pool invariants at run
    granularity ([pool_invs] minus the heap-side [NoDup] of addresses);
    [pool_run_covers], the index-based [pool_cell_covers];
    [pool_run_starts_at] / [pool_run_ends_at], the run at an index begins /
    ends at an id; [runs_live_refine] / [runs_dead_kept], the pool-level
    live-character refinement and tombstone preservation; [pool_after_split],
    what one [splitNode] leaves of the pool at run granularity
    ([pool_after_repair] the same for [store.repair]'s at most two splits,
    [pool_after_delete] for the wire delete path's unbounded sweep);
    [pool_run_clock_below], the index-based [pool_clock_below]. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core prelude network_model.
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

(** [pool_after_split p p' parent k]: [p'] is [p] after one node split at
    the [k]-th run of the type at [parent]: the loc-free
    [split_types_update_rel], its address clauses become index facts. Each
    type's document and flatten survive, no type disappears, a client's run
    list grows by at most one, every run away from the split spot survives,
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
  (∀ c, (length (client_runs p' c) <= S (length (client_runs p c)))%nat) ∧
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
  (∀ c, (length (client_runs p' c) <= 2 + length (client_runs p c))%nat) ∧
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

End store_model.
