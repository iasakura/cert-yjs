(** The transaction's pure model (issue #206 T1, issue #198 Part II): the
    relation between the state a transaction started from and the state it
    is at, given what it recorded.

    Definitions
    - [transaction_start m deleted inserted tombstoned m0 deleted0]: [(m0,
      deleted0)] is the start state of a transaction at [(m, deleted)] that
      recorded the char ids [inserted] and [tombstoned]: every type's
      document was the current one without the inserted chars, the
      tombstones were the current ones without those tombstoned here, which
      were live, and an inserted char is above every older char of its
      client.

    Laws
    - [type_snapshot_start] / [text_delta_transaction]: a type's start
      snapshot is its current one read through the record
      ([snapshot_before]), so the record's delta is the delta from the start
      snapshot to the current one and the start snapshot grows to it.
    - [type_snapshot_untouched]: a type none of whose chars the record
      mentions has the snapshot it started with.
    - [transaction_start_fresh] / [_replay] / [_tombstone]: how the relation
      is born (nothing recorded, start = now) and how it survives a replay
      of delivered inputs ([applyUpdate]) and a tombstone sweep
      ([applyDeleteSpans]).
    - [filter_not_in_union]: chars outside a set are filtered the same with
      that set added (what lets a write's fresh chars leave the other types'
      filters alone, [text/InsertIn]). *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core prelude algebra network_model.
From iris.algebra Require Import auth gmap gset.
From stdpp Require Import sorting.
From New.proof.item Require Import run_theory model value heap.
From New.proof.ytype Require Import model value heap.
From New.proof.delta Require Import model.
From New.proof.store Require Import model.
Local Open Scope Z_scope.

Section transaction_model.

Set Default Proof Using "Type*".

Notation A := go_string.

Notation P := go_string.

Local Notation TId := (TypeId P).

Local Notation Op := (TId * @YjsOperation A)%type.

Local Notation Ev := (@Event Op).

Local Notation DocModel := (gmap TId (list (YjsItem A))).

(* ===== definitions ======================================================== *)

(** [transaction_start m deleted inserted tombstoned m0 deleted0]: [(m0, deleted0)]
    is the state a transaction started from, given the state it is at,
    [(m, deleted)], and what it recorded: every type's document was the
    current one without the chars inserted here (integration keeps the
    order of the others); the tombstones were the current ones without those
    tombstoned here, which were live; and a char inserted here is above every
    older char of its client (every integrate takes its client's next clock).
    What makes a type's start snapshot grow to its current one
    ([snapshot_grows_to]) and the transaction's record classify the current
    snapshot's chars ([text_delta]). [own_transaction]'s clause; the
    registry of observers sits at the start state until [notify]. *)
Definition transaction_start (m : DocModel) (deleted inserted tombstoned : gset YjsId)
    (m0 : DocModel) (deleted0 : gset YjsId) : Prop :=
  (∀ t : TId, doc_model_get m0 t = filter (λ x : YjsItem A, item_id x ∉ inserted) (doc_model_get m t)) ∧
  deleted = deleted0 ∪ tombstoned ∧
  tombstoned ## deleted0 ∧
  (∀ i j : YjsId, i ∈ inserted -> doc_model_has m j = true ->
     clientId j = clientId i -> (clock i < clock j)%nat -> j ∈ inserted).


(* ===== lemmas ============================================================= *)

(** Chars outside a set are filtered the same with that set added: what
    lets a write's fresh chars leave the other types' filters alone. *)
Lemma filter_not_in_union (S T : gset YjsId) (l : list (YjsItem A)) :
  (∀ x, x ∈ l -> item_id x ∉ T) ->
  filter (λ x : YjsItem A, item_id x ∉ S ∪ T) l = filter (λ x : YjsItem A, item_id x ∉ S) l.
Proof.
  elim: l => [| y l IH] Hl; first done.
  have Hy : item_id y ∉ T := Hl y (list_elem_of_here _ _).
  have Hl' : ∀ x, x ∈ l -> item_id x ∉ T := λ x Hx, Hl x (list_elem_of_further _ _ _ Hx).
  rewrite !filter_cons (IH Hl').
  have Hiff : item_id y ∉ S ∪ T ↔ item_id y ∉ S.
  { split.
    - move=> Hn Hin. apply Hn. apply elem_of_union_l. exact Hin.
    - move=> Hn Hin. apply elem_of_union in Hin as [Hin | Hin]; [exact (Hn Hin) | exact (Hy Hin)]. }
  destruct (decide (item_id y ∉ S ∪ T)) as [Hd | Hd]; destruct (decide (item_id y ∉ S)) as [Hd' | Hd'];
    [done | exfalso; apply Hd'; by apply Hiff | exfalso; apply Hd; by apply Hiff | done].
Qed.

(** A type's start snapshot is its current one read through the record
    ([snapshot_before]), so the record classifies the current snapshot's
    chars ([text_delta_before]) and the start snapshot grows to the current
    one ([snapshot_before_grows_to]): what [store.notify] tells an observer. *)
Lemma type_snapshot_start (m : DocModel) (deleted inserted tombstoned : gset YjsId)
    (m0 : DocModel) (deleted0 : gset YjsId) (name : P) :
  transaction_start m deleted inserted tombstoned m0 deleted0 ->
  type_snapshot m0 deleted0 name = snapshot_before inserted tombstoned (type_snapshot m deleted name).
Proof.
  move=> [Hfilter [Hdel [Hdisj _]]]. rewrite /type_snapshot /snapshot_before Hfilter.
  elim: (doc_model_get m (RootId name)) => [| x l IH]; first done.
  rewrite fmap_cons filter_cons filter_cons. simpl.
  destruct (decide (item_id x ∉ inserted)) as [Hni | Hi]; last exact IH.
  rewrite !fmap_cons -IH. f_equal. f_equal.
  rewrite Hdel. case_bool_decide as H0.
  - rewrite bool_decide_eq_true_2; last (apply elem_of_union_l; exact H0).
    rewrite bool_decide_eq_true_2; first done.
    move=> Ht. exact (Hdisj _ Ht H0).
  - case_bool_decide as Hd; last done.
    apply elem_of_union in Hd as [Hd | Hd]; first done.
    rewrite bool_decide_eq_false_2; first done. move=> Hnt. exact (Hnt Hd).
Qed.

(** What [store.notify] tells an observer of [name]: the record's delta,
    and that the start snapshot grew to the current one. *)
Lemma text_delta_transaction (m : DocModel) (deleted inserted tombstoned : gset YjsId)
    (m0 : DocModel) (deleted0 : gset YjsId) (name : P) :
  transaction_start m deleted inserted tombstoned m0 deleted0 ->
  tombstoned ⊆ deleted ->
  YjsArrInvariant (doc_model_get m (RootId name)) ->
  text_delta (type_snapshot m0 deleted0 name) (type_snapshot m deleted name) =
    delta_normal_form (record_delta inserted tombstoned (type_snapshot m deleted name)) ∧
  snapshot_grows_to (type_snapshot m0 deleted0 name) (type_snapshot m deleted name).
Proof.
  move=> Hstart Hsub Hinv.
  have Htop := proj2 (proj2 (proj2 Hstart)).
  rewrite (type_snapshot_start _ _ _ _ _ _ name Hstart).
  have Hnodup : NoDup (type_snapshot m deleted name).*1.
  { rewrite type_snapshot_fst. exact (uniqueId_NoDup _ (yai_unique _ Hinv)). }
  split.
  - apply text_delta_before; first exact Hnodup.
    move=> x Hx Ht. exact (type_snapshot_tombstoned_bit m deleted name x Hx (Hsub _ Ht)).
  - apply snapshot_before_grows_to.
    move=> x y Hx Hy Hcl Hxi Hlt. rewrite type_snapshot_fst in Hx Hy.
    apply (Htop (item_id x) (item_id y) Hxi); [| exact (eq_sym Hcl) | exact Hlt].
    apply docm_has_spec. exists (RootId name), y. split; [exact Hy | reflexivity].
Qed.

(** Such a type's snapshot is the one it started with: what lets [notify]
    leave its observers alone. *)
Lemma type_snapshot_untouched (m : DocModel) (deleted inserted tombstoned : gset YjsId)
    (m0 : DocModel) (deleted0 : gset YjsId) (name : P) :
  transaction_start m deleted inserted tombstoned m0 deleted0 ->
  (∀ x, x ∈ doc_model_get m (RootId name) -> item_id x ∉ inserted ∧ item_id x ∉ tombstoned) ->
  type_snapshot m0 deleted0 name = type_snapshot m deleted name.
Proof.
  move=> Hstart Hout. rewrite (type_snapshot_start _ _ _ _ _ _ name Hstart).
  apply snapshot_before_untouched. move=> x Hx. apply Hout.
  rewrite -(type_snapshot_fst m deleted name). apply list_elem_of_fmap. exists x. split; [reflexivity | exact Hx].
Qed.

Lemma transaction_start_fresh (m : DocModel) (deleted : gset YjsId) :
  transaction_start m deleted ∅ ∅ m deleted.
Proof.
  split_and!.
  - move=> t. elim: (doc_model_get m t) => [| x l IH]; first done.
    rewrite filter_cons_True; [by rewrite -IH | apply not_elem_of_empty].
  - rewrite (right_id_L ∅ (∪)) //.
  - apply disjoint_empty_l.
  - move=> i j Hi. exfalso. exact (not_elem_of_empty i Hi).
Qed.

(** The start relation survives a replay of delivered inputs
    ([store.applyUpdate]): the documents filtered of the batch's chars are
    the ones before, and its chars sit above every older char of their
    client. *)
Lemma transaction_start_replay (m m' : DocModel) (deleted inserted tombstoned : gset YjsId)
    (m0 : DocModel) (deleted0 : gset YjsId) (applied : list (TId * IntegrateInput (A := A))) :
  ValidReplay (expand_inputs applied) m m' ->
  transaction_start m deleted inserted tombstoned m0 deleted0 ->
  transaction_start m' deleted (inserted ∪ inputs_char_ids applied) tombstoned m0 deleted0.
Proof.
  move=> Hvr [Hfilter [Hdel [Hdisj Htop]]]. rewrite inputs_char_ids_replay.
  split_and!; [| exact Hdel | exact Hdisj |].
  - move=> t. rewrite (Hfilter t) -(ValidReplay_filter_new _ _ _ Hvr t) list_filter_filter.
    apply list_filter_iff => x. rewrite not_elem_of_union. tauto.
  - exact (ValidReplay_inserted_top _ _ _ inserted Hvr Htop).
Qed.

(** The start relation survives a tombstone sweep ([store.applyDeleteSpans]):
    the same documents, the tombstones grown by the sweep's fresh ones, which
    were live before. *)
Lemma transaction_start_tombstone (m : DocModel) (deleted deleted' inserted tombstoned tombstoned' : gset YjsId)
    (m0 : DocModel) (deleted0 : gset YjsId) :
  transaction_start m deleted inserted tombstoned m0 deleted0 ->
  tombstoned ⊆ tombstoned' ->
  deleted' = deleted ∪ tombstoned' ->
  (tombstoned' ∖ tombstoned) ## deleted ->
  transaction_start m deleted' inserted tombstoned' m0 deleted0.
Proof.
  move=> [Hfilter [Hdel [Hdisj Htop]]] Htsub Hdel' Hfresh. split_and!; [exact Hfilter | | | exact Htop].
  - rewrite Hdel' Hdel -assoc_L. f_equal. apply subseteq_union_1_L. exact Htsub.
  - rewrite elem_of_disjoint => i Hi Hi0.
    destruct (decide (i ∈ tombstoned)) as [Hin | Hnin].
    + exact (proj1 (elem_of_disjoint _ _) Hdisj i Hin Hi0).
    + apply (proj1 (elem_of_disjoint _ _) Hfresh i).
      * apply elem_of_difference. split; assumption.
      * rewrite Hdel. apply elem_of_union_l. exact Hi0.
Qed.

End transaction_model.
