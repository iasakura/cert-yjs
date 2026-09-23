(** The [TextObserver], PURE model layer: what a poll's delta means and why
    patching with it keeps an application in sync (issue #198).

    A snapshot is the read API's tombstone-tagged per-char sequence
    [list (YjsItem A * bool)] ([runs_model] reads one off a type's runs;
    [visible_string] is what it spells).

    Definitions
    - [DeltaOp]: one entry of a text delta, [Retain] / [Insert] / [Delete]
      (Yjs [YTextEvent.delta]).
    - [delta_run delta s] / [apply_delta delta s]: the patch: the output and
      the unconsumed rest, [None] when a retain or a delete runs past the
      end; [apply_delta] keeps the rest (the implicit trailing retain).
    - [delta_join] / [delta_push] / [delta_merge] / [delta_snoc]: joining
      adjacent same-kind ops, from the right ([delta_merge]) and one op at a
      time from the left ([delta_snoc], the step a walk takes);
      [delta_normal_form] also drops a trailing retain.
    - [delta_step observed x]: Yjs's classification of one char of the
      current snapshot against the observed one; [per_char_delta] is it over
      a whole snapshot and [text_delta observed current] its normal form: the
      delta a poll returns.
    - [snapshot_grows_to observed current]: what the document guarantees
      between two observations of one text: new items only interleave,
      tombstones never clear, and a client's items arrive in clock order.
    - [snapshot_state_vector] / [snapshot_deleted_ids]: the observer's token
      (Yjs [beforeState], y-octo [last_update] / [last_deletes]) as functions
      of the observed snapshot.
    - [app_synced app observed]: the application invariant, its state spells
      the observed snapshot.
    - [delta_fits delta]: every retain and delete count is below [2^64], the
      bound up to which a Go delta (counts as [uint64] words) denotes its
      model.

    Laws
    - [apply_text_delta]: THE patch law: under [snapshot_grows_to], the delta
      patches the observed string to the current one; [app_synced_patch] is
      its application form.
    - [delta_run_merge] / [apply_delta_normal_form]: merging is invisible to
      the patch, dropping the trailing retain is invisible to a patch that
      succeeds.
    - [delta_merge_snoc] / [delta_merge_app_foldl]: the merge is computed
      left to right, one op at a time.
    - [state_vector_classifies] / [deleted_ids_classify]: the token tests the
      Go performs are membership in the observed snapshot.
    - [uniqueId_NoDup] / [uniqueId_sublist]: rocq-yjs's id uniqueness of a
      document gives [NoDup] and is inherited by a sublist (how the observed
      snapshot inherits it from the current one).
    - [snapshot_grows_to_nil], [text_delta_refl], [text_delta_from_empty]:
      the empty observation grows to anything, an unchanged snapshot has the
      empty delta, the first poll inserts the whole visible text.
    - [apply_delta_fits]: a delta that patches a string shorter than [2^64]
      fits (how the application discharges [ApplyDelta]'s bound).
    - [elem_of_snapshot_deleted_ids]: a deleted id is a tombstoned char's.
    - the walk's laws: [snapshot_state_vector_app] / [snapshot_deleted_ids_app]
      / [per_char_delta_app] / [per_char_delta_singleton] /
      [delta_merge_snoc_option] (a snapshot is walked one char at a time)
      and [snapshot_state_vector_run_models] / [snapshot_deleted_ids_run_models]
      (the token of one run's chars: its client's next clock, its ids when
      tombstoned). *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core network_model.
From New.proof.item Require Import run_theory model.
From New.proof.ytype Require Import model value.
From stdpp Require Import gmap sorting.

Section text_observer_model.

Set Default Proof Using "Type*".

Notation A := go_string.

Local Notation snapshot := (list (YjsItem A * bool)).

(* ===== definitions ======================================================== *)

(** One entry of a text delta: keep the next [retained] chars, emit
    [inserted], or drop the next [deleted] chars. *)
Inductive DeltaOp : Type :=
  | Retain (retained : nat)
  | Insert (inserted : A)
  | Delete (deleted : nat).

Global Instance DeltaOp_eq_dec : EqDecision DeltaOp.
Proof. solve_decision. Defined.

(** [delta_run delta s]: run a delta over a string: the output produced and
    the unconsumed rest of [s]; [None] when a retain or a delete runs past
    the end. [apply_delta] appends the rest to the output: a Yjs delta
    leaves its trailing retain implicit. *)
Fixpoint delta_run (delta : list DeltaOp) (s : A) : option (A * A) :=
  match delta with
  | [] => Some ([], s)
  | Retain n :: rest =>
      if decide (n <= length s)%nat
      then (λ p, (take n s ++ p.1, p.2)) <$> delta_run rest (drop n s)
      else None
  | Insert t :: rest => (λ p, (t ++ p.1, p.2)) <$> delta_run rest s
  | Delete n :: rest =>
      if decide (n <= length s)%nat then delta_run rest (drop n s) else None
  end.

Definition apply_delta (delta : list DeltaOp) (s : A) : option A :=
  (λ p, p.1 ++ p.2) <$> delta_run delta s.

(** Joining two adjacent ops of the same kind; [delta_push op delta] puts
    [op] in front of a merged list, [delta_snoc delta op] behind it, and
    [delta_merge] is the merged form of any delta. *)
Definition delta_join (op1 op2 : DeltaOp) : list DeltaOp :=
  match op1, op2 with
  | Retain n, Retain m => [Retain (n + m)]
  | Insert s, Insert t => [Insert (s ++ t)]
  | Delete n, Delete m => [Delete (n + m)]
  | _, _ => [op1; op2]
  end.

Definition delta_push (op : DeltaOp) (delta : list DeltaOp) : list DeltaOp :=
  match delta with
  | [] => [op]
  | op' :: rest => delta_join op op' ++ rest
  end.

Definition delta_merge (delta : list DeltaOp) : list DeltaOp :=
  foldr delta_push [] delta.

Fixpoint delta_snoc (delta : list DeltaOp) (op : DeltaOp) : list DeltaOp :=
  match delta with
  | [] => [op]
  | [op'] => delta_join op' op
  | op' :: rest => op' :: delta_snoc rest op
  end.

Definition delta_drop_trailing_retain (delta : list DeltaOp) : list DeltaOp :=
  match last delta with
  | Some (Retain _) => removelast delta
  | _ => delta
  end.

Definition delta_normal_form (delta : list DeltaOp) : list DeltaOp :=
  delta_drop_trailing_retain (delta_merge delta).

(** Yjs's classification of one char [x] of the current snapshot against the
    observed one ([YTextEvent.delta]): a char the observer knew and saw live
    is retained, or deleted if it has been tombstoned since; a char it knew
    tombstoned, or a new char already tombstoned, contributes nothing; a new
    live char is inserted. Lengths are the char's content length ([Len()]
    in the Go). *)
Definition delta_step (observed : snapshot) (x : YjsItem A * bool) : option DeltaOp :=
  if decide (x.1 ∈ observed.*1) then
    if decide ((x.1, true) ∈ observed) then None
    else if x.2 then Some (Delete (length (content x.1)))
    else Some (Retain (length (content x.1)))
  else if x.2 then None else Some (Insert (content x.1)).

Definition per_char_delta (observed current : snapshot) : list DeltaOp :=
  omap (delta_step observed) current.

Definition text_delta (observed current : snapshot) : list DeltaOp :=
  delta_normal_form (per_char_delta observed current).

(** [snapshot_grows_to observed current]: the current snapshot is the
    observed one plus an update: every observed item is still there in the
    same order with new ones interleaved, an observed tombstone is still a
    tombstone, and no item of a client with a clock below one the observer
    saw arrives later (per-client contiguity). *)
Definition snapshot_grows_to (observed current : snapshot) : Prop :=
  sublist observed.*1 current.*1 ∧
  (∀ x, (x, true) ∈ observed -> (x, true) ∈ current) ∧
  (∀ x y, x ∈ current.*1 -> y ∈ observed.*1 ->
     clientId (item_id x) = clientId (item_id y) ->
     (clock (item_id x) < clock (item_id y))%nat -> x ∈ observed.*1).

(** The observer's token: per client, one plus the largest observed clock,
    and the observed tombstoned ids. *)
Definition snapshot_state_vector (observed : snapshot) : gmap ClientId nat :=
  foldr (λ x acc, sv_join {[ clientId (item_id x) := S (clock (item_id x)) ]} acc)
        ∅ observed.*1.

Definition snapshot_deleted_ids (observed : snapshot) : gset YjsId :=
  char_ids (filter (λ p : YjsItem A * bool, p.2 = true) observed).*1.

(** The application invariant: its state spells the snapshot it last
    observed. *)
Definition app_synced (app : A) (observed : snapshot) : Prop :=
  app = visible_string observed.

(** [delta_fits delta]: every retain and delete count is below [2^64]. The
    Go carries counts as [uint64] words, so a Go delta denotes its model
    only up to this bound ([value.v]'s [delta_op_denotes]); a delta that
    patches a Go string fits ([apply_delta_fits]). *)
Definition delta_op_fits (op : DeltaOp) : Prop :=
  match op with
  | Retain n | Delete n => (Z.of_nat n < 2^64)%Z
  | Insert _ => True
  end.

Definition delta_fits (delta : list DeltaOp) : Prop := Forall delta_op_fits delta.

(* ===== lemmas ============================================================= *)

(* ----- the patch ----- *)

Lemma delta_run_join (op1 op2 : DeltaOp) (d : list DeltaOp) (s : A) :
  delta_run (delta_join op1 op2 ++ d) s = delta_run (op1 :: op2 :: d) s.
Proof.
  destruct op1 as [n | t | n], op2 as [m | u | m]; simpl; try done.
  - (* two retains *)
    rewrite length_drop.
    destruct (decide (n <= length s)%nat) as [Hn | Hn]; last first.
    { rewrite decide_False; [done | lia]. }
    destruct (decide (m <= length s - n)%nat) as [Hm | Hm]; last first.
    { rewrite decide_False; [done | lia]. }
    rewrite decide_True; last lia.
    rewrite drop_drop.
    destruct (delta_run d (drop (n + m) s)) as [p |]; simpl; [| done].
    f_equal. f_equal. rewrite app_assoc take_take_drop //.
  - (* two inserts *)
    destruct (delta_run d s) as [p |]; simpl; [| done].
    f_equal. f_equal. rewrite app_assoc //.
  - (* two deletes *)
    rewrite length_drop.
    destruct (decide (n <= length s)%nat) as [Hn | Hn]; last first.
    { rewrite decide_False; [done | lia]. }
    destruct (decide (m <= length s - n)%nat) as [Hm | Hm]; last first.
    { rewrite decide_False; [done | lia]. }
    rewrite decide_True; last lia.
    rewrite drop_drop //.
Qed.

Lemma delta_run_push (op : DeltaOp) (d : list DeltaOp) (s : A) :
  delta_run (delta_push op d) s = delta_run (op :: d) s.
Proof. destruct d as [| op' rest]; [done | apply delta_run_join]. Qed.

Lemma delta_run_merge (d : list DeltaOp) (s : A) :
  delta_run (delta_merge d) s = delta_run d s.
Proof.
  elim: d s => [| op d IH] s; first done.
  rewrite /= delta_run_push.
  destruct op as [n | t | n]; simpl; rewrite ?IH //.
Qed.

Lemma apply_delta_merge (d : list DeltaOp) (s : A) :
  apply_delta (delta_merge d) s = apply_delta d s.
Proof. rewrite /apply_delta delta_run_merge //. Qed.

(** Running a delta piecewise: the second piece runs on the first's rest. *)
Lemma delta_run_app (d1 d2 : list DeltaOp) (s : A) :
  delta_run (d1 ++ d2) s =
    match delta_run d1 s with
    | Some p1 => (λ p2, (p1.1 ++ p2.1, p2.2)) <$> delta_run d2 p1.2
    | None => None
    end.
Proof.
  elim: d1 s => [| op d1 IH] s.
  - simpl. destruct (delta_run d2 s) as [[o r] |]; simpl; done.
  - destruct op as [n | t | n]; simpl.
    + destruct (decide (n <= length s)%nat); [| done]. rewrite IH.
      destruct (delta_run d1 (drop n s)) as [[o1 r1] |]; simpl; [| done].
      destruct (delta_run d2 r1) as [[o2 r2] |]; simpl; [| done].
      rewrite app_assoc //.
    + rewrite IH.
      destruct (delta_run d1 s) as [[o1 r1] |]; simpl; [| done].
      destruct (delta_run d2 r1) as [[o2 r2] |]; simpl; [| done].
      rewrite app_assoc //.
    + destruct (decide (n <= length s)%nat); [| done]. rewrite IH //.
Qed.

Lemma apply_delta_drop_trailing_retain (d : list DeltaOp) (s s' : A) :
  apply_delta d s = Some s' -> apply_delta (delta_drop_trailing_retain d) s = Some s'.
Proof.
  rewrite /delta_drop_trailing_retain.
  destruct (last d) as [[n | t | n] |] eqn:Hlast; try done.
  apply last_Some in Hlast as [d' ->].
  rewrite removelast_last /apply_delta delta_run_app.
  destruct (delta_run d' s) as [[o r] |]; simpl; [| done].
  destruct (decide (n <= length r)%nat); simpl; [| done].
  move=> [= <-]. f_equal. rewrite app_nil_r -app_assoc take_drop //.
Qed.

Lemma apply_delta_normal_form (d : list DeltaOp) (s s' : A) :
  apply_delta d s = Some s' -> apply_delta (delta_normal_form d) s = Some s'.
Proof. move=> H. apply apply_delta_drop_trailing_retain. rewrite apply_delta_merge //. Qed.

(* ----- the merge, left to right ----- *)

Lemma delta_snoc_cons (op' op : DeltaOp) (d : list DeltaOp) :
  d ≠ [] -> delta_snoc (op' :: d) op = op' :: delta_snoc d op.
Proof. move=> Hne. destruct d; [by exfalso; apply Hne | done]. Qed.

Lemma delta_snoc_app (d1 d2 : list DeltaOp) (op : DeltaOp) :
  d2 ≠ [] -> delta_snoc (d1 ++ d2) op = d1 ++ delta_snoc d2 op.
Proof.
  elim: d1 => [| op' d1 IH] Hne; first done.
  rewrite -app_comm_cons delta_snoc_cons; last by move=> /app_eq_nil [_ ?].
  rewrite IH //.
Qed.

Lemma delta_push_snoc (op1 op2 : DeltaOp) (d : list DeltaOp) :
  delta_push op1 (delta_snoc d op2) = delta_snoc (delta_push op1 d) op2.
Proof.
  destruct d as [| op' [| op'' rest]].
  - destruct op1, op2; simpl; done.
  - destruct op1 as [n | t | n], op' as [m | u | m], op2 as [k | v | k]; simpl; try done;
      by rewrite ?Nat.add_assoc ?app_assoc.
  - have Hne : op'' :: rest ≠ [] by done.
    rewrite /= (delta_snoc_app (delta_join op1 op') (op'' :: rest) op2 Hne).
    destruct op1, op'; done.
Qed.

Lemma delta_merge_cons (op : DeltaOp) (d : list DeltaOp) :
  delta_merge (op :: d) = delta_push op (delta_merge d).
Proof. done. Qed.

Lemma delta_merge_snoc (d : list DeltaOp) (op : DeltaOp) :
  delta_merge (d ++ [op]) = delta_snoc (delta_merge d) op.
Proof. elim: d => [| op' d IH]; first done. rewrite /= IH delta_push_snoc //. Qed.

Lemma delta_merge_app_foldl (d1 d2 : list DeltaOp) :
  delta_merge (d1 ++ d2) = foldl delta_snoc (delta_merge d1) d2.
Proof.
  elim: d2 d1 => [| op d2 IH] d1; first by rewrite app_nil_r.
  have -> : d1 ++ op :: d2 = (d1 ++ [op]) ++ d2 by rewrite -app_assoc.
  rewrite IH delta_merge_snoc //.
Qed.

(* ----- the snapshot relation and the patch law ----- *)

Lemma uniqueId_NoDup (l : list (YjsItem A)) : uniqueId l -> NoDup l.
Proof.
  rewrite /uniqueId. elim: l => [| x l IH] Hss; first constructor.
  apply StronglySorted_inv in Hss as [Hss Hall].
  apply NoDup_cons. split; [| exact (IH Hss)].
  move=> Hin. rewrite Forall_forall in Hall. exact (Hall x Hin eq_refl).
Qed.

Lemma uniqueId_sublist (l k : list (YjsItem A)) :
  sublist l k -> uniqueId k -> uniqueId l.
Proof.
  rewrite /uniqueId. move=> Hsub. elim: Hsub => [| x l' k' Hsub IH | x l' k' Hsub IH] Hss.
  - constructor.
  - apply StronglySorted_inv in Hss as [Hss Hall].
    constructor; [exact (IH Hss) |].
    rewrite Forall_forall in Hall. rewrite Forall_forall. move=> y Hy.
    apply Hall. exact (elem_of_submseteq _ _ _ Hy (sublist_submseteq _ _ Hsub)).
  - apply StronglySorted_inv in Hss as [Hss _]. exact (IH Hss).
Qed.

Lemma visible_string_cons_live (x : YjsItem A) (m : snapshot) :
  visible_string ((x, false) :: m) = content x ++ visible_string m.
Proof. rewrite /visible_string /visible_items filter_cons_True //. Qed.

Lemma visible_string_cons_tombstoned (x : YjsItem A) (m : snapshot) :
  visible_string ((x, true) :: m) = visible_string m.
Proof. rewrite /visible_string /visible_items filter_cons_False //. Qed.

Lemma elem_of_snapshot_fst (x : YjsItem A) (b : bool) (m : snapshot) :
  (x, b) ∈ m -> x ∈ m.*1.
Proof. move=> Hin. rewrite list_elem_of_fmap. by exists (x, b). Qed.

(** A char the observer knows that heads the current snapshot heads the
    observed one too (the order is shared and the char occurs once). *)
Lemma snapshot_sublist_head (observed : snapshot) (x : YjsItem A) (k : list (YjsItem A)) :
  sublist observed.*1 (x :: k) -> x ∉ k -> x ∈ observed.*1 ->
  ∃ (b0 : bool) (observed' : snapshot),
    observed = (x, b0) :: observed' ∧ sublist observed'.*1 k.
Proof.
  move=> Hsub Hnotin Hx.
  apply sublist_cons_r in Hsub as [Hsub | (l' & Heq & Hsub)].
  - exfalso. apply Hnotin. exact (elem_of_submseteq _ _ _ Hx (sublist_submseteq _ _ Hsub)).
  - destruct observed as [| [y b0] observed']; first done.
    rewrite fmap_cons in Heq. injection Heq as Heq1 Heq2. simpl in Heq1. subst y l'.
    by exists b0, observed'.
Qed.

Lemma snapshot_sublist_tail (observed : snapshot) (x : YjsItem A) (k : list (YjsItem A)) :
  sublist observed.*1 (x :: k) -> x ∉ observed.*1 -> sublist observed.*1 k.
Proof.
  move=> Hsub Hnotin.
  apply sublist_cons_r in Hsub as [Hsub | (l' & Heq & Hsub)]; first done.
  exfalso. apply Hnotin. rewrite Heq. apply list_elem_of_here.
Qed.

(** The classification of a char that is not the observed head does not see
    the observed head. *)
Lemma delta_step_cons_ne (x : YjsItem A) (b0 : bool) (observed : snapshot)
    (z : YjsItem A * bool) :
  z.1 ≠ x -> delta_step ((x, b0) :: observed) z = delta_step observed z.
Proof.
  move=> Hne. rewrite /delta_step fmap_cons /=.
  have Hmem1 : z.1 ∈ x :: observed.*1 <-> z.1 ∈ observed.*1.
  { rewrite elem_of_cons. split; [move=> [Heq | ?]; [by destruct (Hne Heq) | done] | by right]. }
  have Hmem2 : (z.1, true) ∈ (x, b0) :: observed <-> (z.1, true) ∈ observed.
  { rewrite elem_of_cons. split; [| by right].
    move=> [Heq | ?]; [| done]. injection Heq as Heq _. by destruct (Hne Heq). }
  destruct (decide (z.1 ∈ x :: observed.*1)) as [H1 | H1];
    destruct (decide (z.1 ∈ observed.*1)) as [H2 | H2]; try (exfalso; tauto).
  - destruct (decide ((z.1, true) ∈ (x, b0) :: observed)) as [H3 | H3];
      destruct (decide ((z.1, true) ∈ observed)) as [H4 | H4]; try (exfalso; tauto); done.
  - done.
Qed.

Lemma per_char_delta_cons_ne (x : YjsItem A) (b0 : bool) (observed current : snapshot) :
  x ∉ current.*1 ->
  per_char_delta ((x, b0) :: observed) current = per_char_delta observed current.
Proof.
  move=> Hnotin. rewrite /per_char_delta.
  elim: current Hnotin => [| z current IH] Hnotin; first done.
  rewrite fmap_cons not_elem_of_cons in Hnotin. destruct Hnotin as [Hne Hnotin].
  rewrite !omap_cons (delta_step_cons_ne x b0 observed z); last by move=> Heq; apply Hne.
  rewrite IH //.
Qed.

(** The per-char delta runs the observed string to exactly the current one,
    with nothing left over. *)
Lemma per_char_delta_run (current observed : snapshot) :
  sublist observed.*1 current.*1 ->
  NoDup current.*1 ->
  (∀ x, (x, true) ∈ observed -> (x, true) ∈ current) ->
  delta_run (per_char_delta observed current) (visible_string observed) =
    Some (visible_string current, []).
Proof.
  elim: current observed => [| [x b] current IH] observed Hsub Hnodup Htomb.
  - apply sublist_nil_r in Hsub. apply fmap_nil_inv in Hsub. subst observed. done.
  - rewrite fmap_cons /= in Hsub Hnodup.
    apply NoDup_cons in Hnodup as [Hnotin Hnodup].
    destruct (decide (x ∈ observed.*1)) as [Hx | Hx].
    + (* a known char: it heads the observed snapshot as well *)
      destruct (snapshot_sublist_head observed x current.*1 Hsub Hnotin Hx)
        as (b0 & observed' & -> & Hsub').
      have Htomb' : ∀ z, (z, true) ∈ observed' -> (z, true) ∈ current.
      { move=> z Hz.
        have Hz' : (z, true) ∈ (x, b0) :: observed' by apply list_elem_of_further.
        apply Htomb in Hz'. apply elem_of_cons in Hz' as [Heq | ?]; [| done].
        exfalso. injection Heq as -> _. apply Hnotin.
        exact (elem_of_submseteq _ _ _ (elem_of_snapshot_fst _ _ _ Hz)
                 (sublist_submseteq _ _ Hsub')). }
      have IH' := IH observed' Hsub' Hnodup Htomb'.
      have Hrest : omap (delta_step ((x, b0) :: observed')) current = per_char_delta observed' current
        by exact (per_char_delta_cons_ne x b0 observed' current Hnotin).
      have Hxhead : x ∈ ((x, b0) :: observed').*1 by rewrite fmap_cons; apply list_elem_of_here.
      rewrite /per_char_delta omap_cons Hrest /delta_step /=.
      rewrite decide_True; last exact Hxhead.
      destruct b0.
      * (* known tombstoned: contributes nothing, and it is still tombstoned *)
        rewrite decide_True; last by apply list_elem_of_here.
        have Hb : b = true.
        { have Hin := Htomb x (list_elem_of_here _ _).
          apply elem_of_cons in Hin as [Heq | Hin]; first by injection Heq.
          exfalso. apply Hnotin. exact (elem_of_snapshot_fst _ _ _ Hin). }
        subst b. rewrite !visible_string_cons_tombstoned. exact IH'.
      * (* known live: retained or deleted *)
        rewrite decide_False; last first.
        { move=> Hin. apply elem_of_cons in Hin as [Heq | Hin]; first by injection Heq.
          apply Hnotin.
          exact (elem_of_submseteq _ _ _ (elem_of_snapshot_fst _ _ _ Hin)
                   (sublist_submseteq _ _ Hsub')). }
        rewrite visible_string_cons_live.
        destruct b; simpl.
        -- rewrite decide_True; last by rewrite length_app; lia.
           rewrite drop_app_length IH' visible_string_cons_tombstoned //.
        -- rewrite decide_True; last by rewrite length_app; lia.
           rewrite drop_app_length take_app_length IH' visible_string_cons_live //.
    + (* a new char *)
      have Hsub' := snapshot_sublist_tail observed x current.*1 Hsub Hx.
      have Htomb' : ∀ z, (z, true) ∈ observed -> (z, true) ∈ current.
      { move=> z Hz. have Hz' := Htomb z Hz.
        apply elem_of_cons in Hz' as [Heq | ?]; [| done].
        exfalso. injection Heq as -> _. apply Hx. exact (elem_of_snapshot_fst _ _ _ Hz). }
      have IH' := IH observed Hsub' Hnodup Htomb'.
      rewrite /per_char_delta omap_cons /delta_step /=.
      rewrite decide_False; last done.
      destruct b; simpl.
      * rewrite visible_string_cons_tombstoned. exact IH'.
      * rewrite -/(per_char_delta observed current) IH' visible_string_cons_live //.
Qed.

Lemma apply_text_delta (observed current : snapshot) :
  snapshot_grows_to observed current -> uniqueId current.*1 ->
  apply_delta (text_delta observed current) (visible_string observed) =
    Some (visible_string current).
Proof.
  move=> [Hsub [Htomb _]] Huniq.
  apply apply_delta_normal_form.
  rewrite /apply_delta per_char_delta_run //; last exact (uniqueId_NoDup _ Huniq).
  by rewrite /= app_nil_r.
Qed.

Lemma app_synced_patch (app : A) (observed current : snapshot) :
  app_synced app observed -> snapshot_grows_to observed current -> uniqueId current.*1 ->
  ∃ app', apply_delta (text_delta observed current) app = Some app' ∧ app_synced app' current.
Proof.
  move=> -> Hgrow Huniq. exists (visible_string current).
  split; [exact (apply_text_delta _ _ Hgrow Huniq) | done].
Qed.

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

(* ----- sanity: the first, the unchanged and the empty poll ----- *)

Lemma snapshot_grows_to_nil (current : snapshot) : snapshot_grows_to [] current.
Proof.
  split_and!; [apply sublist_nil_l | by move=> x; rewrite elem_of_nil | by move=> x y _; rewrite elem_of_nil].
Qed.

(** A merged list of retains is one retain (or nothing). *)
Lemma delta_merge_all_retain (d : list DeltaOp) :
  (∀ op, op ∈ d -> ∃ n, op = Retain n) ->
  delta_merge d = [] ∨ ∃ n, delta_merge d = [Retain n].
Proof.
  elim: d => [| op d IH] Hall; first by left.
  have [n ->] := Hall op (list_elem_of_here _ _).
  destruct IH as [Hnil | [m Hm]]; first by move=> op' Hop'; apply Hall, list_elem_of_further.
  - right. exists n. rewrite /= Hnil //.
  - right. exists (n + m). rewrite /= Hm //.
Qed.

(** An unchanged snapshot has the empty delta. *)
Lemma text_delta_refl (m : snapshot) : uniqueId m.*1 -> text_delta m m = [].
Proof.
  move=> Huniq.
  have Hall : ∀ op, op ∈ per_char_delta m m -> ∃ n, op = Retain n.
  { move=> op. rewrite /per_char_delta list_elem_of_omap. move=> [[x b] [Hin Hstep]].
    move: Hstep. rewrite /delta_step /=.
    rewrite decide_True; last exact (elem_of_snapshot_fst _ _ _ Hin).
    destruct b.
    - rewrite decide_True //.
    - rewrite decide_False; first by move=> [= <-]; eexists.
      move=> Hin'. have Hx := elem_of_snapshot_fst _ _ _ Hin.
      (* the same item would carry both bits *)
      have := uniqueId_NoDup _ Huniq.
      move: Hin Hin'. clear. elim: m => [| [y c] m IH]; first by rewrite elem_of_nil.
      rewrite !elem_of_cons fmap_cons NoDup_cons. move=> Hin Hin' [Hnotin Hnodup].
      destruct Hin as [Heq | Hin]; destruct Hin' as [Heq' | Hin'].
      + injection Heq as _ Hc1. injection Heq' as _ Hc2. congruence.
      + injection Heq as Hxy _. subst y. apply Hnotin. exact (elem_of_snapshot_fst _ _ _ Hin').
      + injection Heq' as Hxy _. subst y. apply Hnotin. exact (elem_of_snapshot_fst _ _ _ Hin).
      + exact (IH Hin Hin' Hnodup). }
  rewrite /text_delta /delta_normal_form.
  destruct (delta_merge_all_retain _ Hall) as [-> | [n ->]]; first done.
  rewrite /delta_drop_trailing_retain //.
Qed.

(** The first poll inserts the whole visible text: from the empty
    observation every live char is new. *)
Lemma text_delta_from_empty (current : snapshot) :
  text_delta [] current =
    (if decide (visible_items current = []) then [] else [Insert (visible_string current)]).
Proof.
  rewrite /text_delta /delta_normal_form.
  have Hraw : per_char_delta [] current = (λ x, Insert (content x)) <$> visible_items current.
  { rewrite /per_char_delta /visible_items.
    elim: current => [| [x b] current IH]; first done.
    (* [simpl] decides membership in the empty list on its own *)
    rewrite omap_cons IH /delta_step /=. destruct b; simpl.
    - rewrite filter_cons_False //.
    - done. }
  rewrite Hraw.
  have Hstring : ∀ l : list (YjsItem A), l ≠ [] ->
      delta_merge ((λ x, Insert (content x)) <$> l) = [Insert (items_string l)].
  { elim => [| x l IH] Hne; first done.
    rewrite fmap_cons delta_merge_cons.
    destruct l as [| y l'].
    - rewrite /= app_nil_r //.
    - rewrite IH // /delta_push /delta_join //. }
  destruct (decide (visible_items current = [])) as [Hnil | Hnil].
  - rewrite Hnil //.
  - rewrite (Hstring _ Hnil) //.
Qed.

(** A retain or a delete that ran is no longer than the string it ran on. *)
Lemma delta_run_counts_bounded (d : list DeltaOp) (s : A) (p : A * A) :
  delta_run d s = Some p ->
  Forall (λ op, match op with
                | Retain n | Delete n => (n <= length s)%nat
                | Insert _ => True
                end) d.
Proof.
  elim: d s p => [| op d IH] s p /=; first by move=> _; apply Forall_nil.
  destruct op as [n | t | n].
  - case_decide as Hle; last done.
    destruct (delta_run d (drop n s)) as [p' |] eqn:Hrun; last done.
    move=> _. constructor; first exact Hle.
    eapply Forall_impl; first exact (IH _ _ Hrun).
    move=> [k | u | k] //=; rewrite length_drop; lia.
  - destruct (delta_run d s) as [p' |] eqn:Hrun; last done.
    move=> _. constructor; first done. exact (IH _ _ Hrun).
  - case_decide as Hle; last done.
    move=> Hrun. constructor; first exact Hle.
    eapply Forall_impl; first exact (IH _ _ Hrun).
    move=> [k | u | k] //=; rewrite length_drop; lia.
Qed.

Lemma apply_delta_fits (d : list DeltaOp) (s s' : A) :
  apply_delta d s = Some s' -> (Z.of_nat (length s) < 2^64)%Z -> delta_fits d.
Proof.
  rewrite /apply_delta. destruct (delta_run d s) as [p |] eqn:Hrun; last done.
  move=> _ Hlen.
  eapply Forall_impl; first exact (delta_run_counts_bounded d s p Hrun).
  move=> [k | u | k] //=; lia.
Qed.

(** A deleted id of a snapshot is the id of one of its tombstoned chars. *)
Lemma elem_of_snapshot_deleted_ids (m : snapshot) (i : YjsId) :
  i ∈ snapshot_deleted_ids m <-> ∃ x, (x, true) ∈ m ∧ item_id x = i.
Proof.
  rewrite /snapshot_deleted_ids /char_ids elem_of_list_to_set list_elem_of_fmap.
  split.
  - intros (x & -> & Hx). rewrite list_elem_of_fmap in Hx.
    destruct Hx as ([y b] & -> & Hy). rewrite list_elem_of_filter /= in Hy.
    destruct Hy as [-> Hy]. exists y. split; [exact Hy | reflexivity].
  - intros (x & Hx & <-). exists x. split; first reflexivity.
    rewrite list_elem_of_fmap. exists (x, true). split; first reflexivity.
    rewrite list_elem_of_filter /=. split; [reflexivity | exact Hx].
Qed.

(** The token over an append: the state vectors join, the deleted ids
    union; the per-char delta over an append, and over one char. *)
Lemma snapshot_state_vector_app (m1 m2 : snapshot) :
  snapshot_state_vector (m1 ++ m2) =
  sv_join (snapshot_state_vector m1) (snapshot_state_vector m2).
Proof.
  rewrite /snapshot_state_vector fmap_app.
  elim: m1.*1 => [| x l IH] /=; first by rewrite sv_join_empty_l.
  rewrite IH sv_join_assoc //.
Qed.

Lemma snapshot_deleted_ids_app (m1 m2 : snapshot) :
  snapshot_deleted_ids (m1 ++ m2) = snapshot_deleted_ids m1 ∪ snapshot_deleted_ids m2.
Proof.
  rewrite /snapshot_deleted_ids /char_ids filter_app !fmap_app list_to_set_app_L //.
Qed.

Lemma per_char_delta_app (observed m1 m2 : snapshot) :
  per_char_delta observed (m1 ++ m2) =
  per_char_delta observed m1 ++ per_char_delta observed m2.
Proof. rewrite /per_char_delta omap_app //. Qed.

Lemma per_char_delta_singleton (observed : snapshot) (x : YjsItem A * bool) :
  per_char_delta observed [x] = option_list (delta_step observed x).
Proof. rewrite /per_char_delta /=. by destruct (delta_step observed x). Qed.

(** The merge over one more char: nothing, or one [delta_snoc]. *)
Lemma delta_merge_snoc_option (d : list DeltaOp) (o : option DeltaOp) :
  delta_merge (d ++ option_list o) =
  match o with Some op => delta_snoc (delta_merge d) op | None => delta_merge d end.
Proof. destruct o as [op |]; [exact (delta_merge_snoc d op) | rewrite app_nil_r //]. Qed.

(** The token of one run's chars ([run_models r], the per-char sequence of a
    heap node): the run's client is at its next clock and no other client is
    known; the run's ids are deleted iff the run is tombstoned. *)
Lemma run_models_fst (r : ItemRun) : (run_models r).*1 = run_items r.
Proof.
  rewrite /run_models -list_fmap_compose -{2}(list_fmap_id (run_items r)).
  apply list_fmap_ext. move=> i x _. reflexivity.
Qed.

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

Lemma snapshot_deleted_ids_run_models (r : ItemRun) :
  snapshot_deleted_ids (run_models r) =
    if run_deleted r then char_ids (run_items r) else ∅.
Proof.
  rewrite /snapshot_deleted_ids /run_models.
  destruct (run_deleted r).
  - elim: (run_items r) => [| x l IH]; first done.
    simpl. rewrite !char_ids_cons IH //.
  - elim: (run_items r) => [| x l IH]; first done.
    simpl. exact IH.
Qed.


End text_observer_model.
