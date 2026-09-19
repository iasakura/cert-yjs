(** The text delta, PURE model layer: what a delta means and why patching
    with it keeps an application in sync (issue #198). Shared by the pull
    observer ([textobserver/], [Poll]) and the push observer ([Text.Observe],
    [store.notify], issue #198 Part II), so it sits below the store.

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
      delta an observer is told.
    - [snapshot_grows_to observed current]: what the document guarantees
      between two observations of one text: new items only interleave,
      tombstones never clear, and a client's items arrive in clock order.
    - [app_synced app observed]: the application invariant, its state spells
      the observed snapshot.
    - [snapshot_before inserted tombstoned now] / [record_step inserted
      tombstoned x]: a transaction's start snapshot read off its current one
      and its record, and the record's classification of one char (the push
      observer, issue #198 Part II).
    - [snapshot_deleted_ids s]: the tombstoned ids of a snapshot.
    - [history_reflected h0 name s]: every insert into the root [name] that
      the history prefix [h0] delivered has its item in [s].
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
    - [uniqueId_NoDup] / [uniqueId_sublist]: rocq-yjs's id uniqueness of a
      document gives [NoDup] and is inherited by a sublist (how the observed
      snapshot inherits it from the current one).
    - [snapshot_grows_to_nil], [text_delta_refl], [text_delta_from_empty]:
      the empty observation grows to anything, an unchanged snapshot has the
      empty delta, the first observation inserts the whole visible text.
    - [apply_delta_fits]: a delta that patches a string shorter than [2^64]
      fits (how the application discharges [ApplyDelta]'s bound).
    - [text_delta_before] / [snapshot_before_grows_to]: the delta from the
      start snapshot is the record's classification merged, and the start
      snapshot grows to the current one ([delta_step_before] per char).
    - [elem_of_snapshot_deleted_ids]: a deleted id is a tombstoned char's;
      [snapshot_deleted_ids_app] / [snapshot_deleted_ids_run_models]: over a
      walk, and over one run's chars (its ids when tombstoned).
    - the walk's laws: [per_char_delta_app] / [per_char_delta_singleton] /
      [delta_merge_snoc_option] (a snapshot is walked one char at a time)
      and [run_models_fst] (a run's per-char sequence lists its items). *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core network_model.
From New.proof.item Require Import run_theory model.
From New.proof.ytype Require Import model value.
From stdpp Require Import gmap sorting.


Section delta_model.

Set Default Proof Using "Type*".

Notation A := go_string.

Local Notation snapshot := (list (YjsItem A * bool)).

(* Type names are Go strings (issue #49). *)
Local Notation P := go_string.
Local Notation TId := (TypeId P).
Local Notation Op := (TId * @YjsOperation A)%type.
Local Notation Ev := (@Event Op).

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

(** The application invariant: its state spells the snapshot it last
    observed. *)
Definition app_synced (app : A) (observed : snapshot) : Prop :=
  app = visible_string observed.

(** The tombstoned ids of a snapshot (the pull observer's deleted-ids token,
    the delete-set certificate a push observer's snapshot carries). *)
Definition snapshot_deleted_ids (observed : snapshot) : gset YjsId :=
  char_ids (filter (λ p : YjsItem A * bool, p.2 = true) observed).*1.


(** [history_reflected h0 name model]: every insert into the root [name] that
    the history prefix [h0] delivered has its item in the walked list. *)
Definition history_reflected (h0 : list Ev) (name : P) (model : list (YjsItem A * bool)) : Prop :=
  ∀ input : IntegrateInput (A := A),
    (RootId name, OpInsert input) ∈ delivered_ops h0 ->
    ∃ it, item_id it = in_id input ∧ it ∈ model.*1.


(** [snapshot_before inserted tombstoned now]: the snapshot a transaction
    started from, read off the current one and its record (issue #198 Part
    II): without the chars it inserted, and with the tombstones it set
    cleared. What a push observer was last told. *)
Definition snapshot_before (inserted tombstoned : gset YjsId) (now : snapshot) : snapshot :=
  (λ x : YjsItem A * bool, (x.1, x.2 && bool_decide (item_id x.1 ∉ tombstoned))) <$>
    filter (λ x : YjsItem A * bool, item_id x.1 ∉ inserted) now.

(** [record_step inserted tombstoned x]: the record's classification of one
    char of the current snapshot, what the Go walk ([textDelta]) emits for
    it: a char the transaction inserted is an insert when live and nothing
    when it tombstoned it too; an older char is a delete when the
    transaction tombstoned it, nothing when it was already a tombstone, and
    a retain when live. *)
Definition record_step (inserted tombstoned : gset YjsId) (x : YjsItem A * bool) : option DeltaOp :=
  if decide (item_id x.1 ∈ inserted) then (if x.2 then None else Some (Insert (content x.1)))
  else if decide (item_id x.1 ∈ tombstoned) then Some (Delete (length (content x.1)))
  else if x.2 then None else Some (Retain (length (content x.1))).

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
Lemma snapshot_deleted_ids_app (m1 m2 : snapshot) :
  snapshot_deleted_ids (m1 ++ m2) = snapshot_deleted_ids m1 ∪ snapshot_deleted_ids m2.
Proof.
  rewrite /snapshot_deleted_ids /char_ids filter_app !fmap_app list_to_set_app_L //.
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


(* ----- the record's view of a snapshot (issue #198 Part II) ----- *)

Lemma snapshot_before_fst (inserted tombstoned : gset YjsId) (now : snapshot) :
  (snapshot_before inserted tombstoned now).*1 = filter (λ x : YjsItem A, item_id x ∉ inserted) now.*1.
Proof.
  rewrite /snapshot_before -list_fmap_compose.
  elim: now => [| x l IH]; first done.
  rewrite filter_cons fmap_cons filter_cons. simpl.
  destruct (decide (item_id x.1 ∉ inserted)) as [Hx|Hx]; [rewrite fmap_cons IH // | exact IH].
Qed.

Lemma elem_of_snapshot_before_fst (inserted tombstoned : gset YjsId) (now : snapshot) (x : YjsItem A) :
  x ∈ (snapshot_before inserted tombstoned now).*1 <-> x ∈ now.*1 ∧ item_id x ∉ inserted.
Proof. rewrite snapshot_before_fst list_elem_of_filter. tauto. Qed.

Lemma elem_of_snapshot_before_tombstoned (inserted tombstoned : gset YjsId) (now : snapshot) (x : YjsItem A) :
  (x, true) ∈ snapshot_before inserted tombstoned now <->
  (x, true) ∈ now ∧ item_id x ∉ inserted ∧ item_id x ∉ tombstoned.
Proof.
  rewrite /snapshot_before list_elem_of_fmap. split.
  - move=> [[y b] [Heq Hin]]. simpl in Heq. injection Heq as <- Hb.
    apply list_elem_of_filter in Hin as [Hni Hin]. simpl in Hni.
    symmetry in Hb. apply andb_true_iff in Hb as [-> Hnt]. apply bool_decide_eq_true in Hnt.
    split_and!; [exact Hin | exact Hni | exact Hnt].
  - move=> [Hin [Hni Hnt]]. exists (x, true). split.
    + simpl. rewrite bool_decide_eq_true_2 //.
    + apply list_elem_of_filter. split; [exact Hni | exact Hin].
Qed.

(** Yjs's classification against the start snapshot is the record's, char
    by char, when the snapshot's items are distinct and every char the
    transaction tombstoned is a tombstone now. *)
Lemma delta_step_before (inserted tombstoned : gset YjsId) (now : snapshot) (x : YjsItem A * bool) :
  NoDup now.*1 -> x ∈ now -> (item_id x.1 ∈ tombstoned -> x.2 = true) ->
  delta_step (snapshot_before inserted tombstoned now) x = record_step inserted tombstoned x.
Proof.
  move=> Hnodup Hx Htomb. rewrite /delta_step /record_step.
  have Hx1 : x.1 ∈ now.*1 by (apply list_elem_of_fmap; by exists x).
  have Hxt : (x.1, true) ∈ now <-> x.2 = true.
  { split.
    - move=> Hin. destruct x as [y b]. simpl in *.
      destruct b; first done. exfalso.
      have Hi1 : (y, true) ∈ now := Hin. have Hi2 : (y, false) ∈ now := Hx.
      apply list_elem_of_lookup in Hi1 as [i1 Hi1]. apply list_elem_of_lookup in Hi2 as [i2 Hi2].
      have Hne : i1 ≠ i2 by (move=> Heq; rewrite Heq Hi2 in Hi1; discriminate).
      have Hf1 : now.*1 !! i1 = Some y by rewrite list_lookup_fmap Hi1 //.
      have Hf2 : now.*1 !! i2 = Some y by rewrite list_lookup_fmap Hi2 //.
      exact (Hne (NoDup_lookup _ _ _ _ Hnodup Hf1 Hf2)).
    - move=> Hb. destruct x as [y b]. simpl in Hb. subst b. exact Hx. }
  destruct (decide (item_id x.1 ∈ inserted)) as [Hins | Hnins].
  - rewrite decide_False; last first.
    { rewrite elem_of_snapshot_before_fst. tauto. }
    reflexivity.
  - rewrite decide_True; last first.
    { rewrite elem_of_snapshot_before_fst. tauto. }
    destruct (decide (item_id x.1 ∈ tombstoned)) as [Ht | Hnt].
    + rewrite decide_False; last first.
      { rewrite elem_of_snapshot_before_tombstoned. tauto. }
      rewrite (Htomb Ht) //.
    + destruct x.2 eqn:Hb.
      * rewrite decide_True; first done.
        rewrite elem_of_snapshot_before_tombstoned. split_and!; [by apply Hxt | exact Hnins | exact Hnt].
      * rewrite decide_False; first done.
        rewrite elem_of_snapshot_before_tombstoned. move=> [Hin _]. apply Hxt in Hin. discriminate.
Qed.

(** The delta from the start snapshot to the current one is the record's
    classification of the current snapshot, merged: what [textDelta] walks. *)
Lemma text_delta_before (inserted tombstoned : gset YjsId) (now : snapshot) :
  NoDup now.*1 -> (∀ x, x ∈ now -> item_id x.1 ∈ tombstoned -> x.2 = true) ->
  text_delta (snapshot_before inserted tombstoned now) now =
  delta_normal_form (omap (record_step inserted tombstoned) now).
Proof.
  move=> Hnodup Htomb. rewrite /text_delta /per_char_delta. f_equal.
  apply list_omap_ext. apply Forall_Forall2_diag. apply Forall_forall => x Hx.
  apply (delta_step_before inserted tombstoned now x Hnodup Hx (Htomb x Hx)).
Qed.

(** The start snapshot grows to the current one when an inserted char is
    above every older char of its client. *)
Lemma snapshot_before_grows_to (inserted tombstoned : gset YjsId) (now : snapshot) :
  (∀ x y : YjsItem A, x ∈ now.*1 -> y ∈ now.*1 ->
     clientId (item_id x) = clientId (item_id y) -> item_id x ∈ inserted ->
     (clock (item_id x) < clock (item_id y))%nat -> item_id y ∈ inserted) ->
  snapshot_grows_to (snapshot_before inserted tombstoned now) now.
Proof.
  move=> Htop. split_and!.
  - rewrite snapshot_before_fst. apply sublist_filter.
  - move=> x Hx. apply elem_of_snapshot_before_tombstoned in Hx as [Hx _]. exact Hx.
  - move=> x y Hx Hy Hcl Hlt.
    apply elem_of_snapshot_before_fst in Hy as [Hy Hny].
    apply elem_of_snapshot_before_fst. split; first exact Hx.
    move=> Hxi. apply Hny. exact (Htop x y Hx Hy Hcl Hxi Hlt).
Qed.

(** A run's per-char sequence lists its items. *)
Lemma run_models_fst (r : ItemRun) : (run_models r).*1 = run_items r.
Proof.
  rewrite /run_models -list_fmap_compose -{2}(list_fmap_id (run_items r)).
  apply list_fmap_ext. move=> i x _. reflexivity.
Qed.

End delta_model.
