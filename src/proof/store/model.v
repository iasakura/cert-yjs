(** The [store], PURE model layer: the document model and the wire it replays.
    No Go values, no Iris.

    Definitions
    - [expand_input] / [expand_inputs]: one wire item expands to its per-char
      integrate inputs, which is how a run-granular update refines the
      per-char model.
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

    The cell bookkeeping that shadows this model is [store/value.v]. *)
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
