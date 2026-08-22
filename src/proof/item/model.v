(** The [item] type, PURE model layer: no Go values, no Iris.

    A heap node covers a RUN of consecutive per-char model items (issue #28);
    this file is the theory of such runs.

    Definitions
    - [run_wf r]: [r] is a run, its items chained by left origin and sharing
      one right origin.
    - [explode s]: a content string as the list of its per-char contents.

    Laws
    - [run_wf] holds of a singleton, and of any chain minted from a head
      ([run_wf_singleton], [run_wf_of_chain]).
    - [run_wf] is preserved by [take] and [drop] ([run_wf_take],
      [run_wf_drop]): splitting a node leaves two runs.
    - inside a run the [o]-th item's clock is the head's plus [o] and its right
      origin is the head's ([run_wf_lookup_clock], [run_wf_char_id],
      [run_wf_lookup_rightOrigin]).
    - [run_wf] implies [item/run_theory]'s [run_step] ([run_wf_run_step]).
    - [explode] preserves length and is the singleton list on a one-char
      string.

    The deep run-integration theory is [item/run_theory.v]; the heap node that
    carries a run is [item/value.v]. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core prelude.
From New.proof.item Require Import run_theory.

Section item_model.

Set Default Proof Using "Type*".

Notation A := go_string.

(* ===== definitions ======================================================== *)

(** Model items are inhabited (needed to make [run_head] total; [run_wf]
    guarantees the run is nonempty wherever the head matters). *)
#[global] Instance YjsItem_inhabited : Inhabited (YjsItem A) :=
  populate (Item First Last (MkYjsId O O) inhabitant).

(** Run well-formedness: the model shadow of the reference implementations'
    split/merge invariant (yjs [splitItem] / y-octo [split_node_at] / yrs
    [ItemPtr::splice]): nonempty, consecutive clocks from the head, each
    non-head item's left origin is exactly the previous item, and every item
    shares the head's right origin. Everything about a non-head item is thus
    a function of the head, which is why the heap stores one id/origin pair
    per node. *)
Definition run_wf (r : list (YjsItem A)) : Prop :=
  r ≠ [] ∧
  ∀ (k : nat) (x y : YjsItem A), r !! k = Some x → r !! S k = Some y →
    item_id y = MkYjsId (clientId (item_id x)) (S (clock (item_id x))) ∧
    origin y = itemPtr x ∧
    rightOrigin y = rightOrigin x.

(** Per-char explosion of a heap content string: byte k becomes the content of
    the run's k-th model item. (For future non-string content types, this is
    the per-content-type element decomposition.) *)
Definition explode (s : go_string) : list A := (λ b, [b]) <$> s.

(* ===== lemmas ============================================================= *)

(** A singleton run is trivially well-formed; every current creator mints
    these. *)
Lemma run_wf_singleton (y : YjsItem A) : run_wf [y].
Proof.
  split; first done.
  intros k x y' Hx Hy'. destruct k; simpl in *; [done | by destruct k].
Qed.

(** Materialize [run_wf] from the per-position facts a chained integrate
    produces (issue #28 U7): consecutive ids under one (client, clock+·)
    ladder, the tail chaining off the previous element, everything sharing
    the head's right origin. *)
Lemma run_wf_of_chain (h : YjsItem A) (news : list (YjsItem A)) (client clock : nat)
    (rp : YjsPtr A) :
  item_id h = MkYjsId client clock ->
  rightOrigin h = rp ->
  (∀ (k : nat) (it : YjsItem A), news !! k = Some it ->
     item_id it = MkYjsId client (clock + S k)%nat ∧ rightOrigin it = rp ∧
     (k = 0%nat -> origin it = itemPtr h) ∧
     (∀ (k' : nat) (itp : YjsItem A), k = S k' -> news !! k' = Some itp ->
        origin it = itemPtr itp)) ->
  run_wf (h :: news).
Proof.
  move=> Hhid Hhro Hfacts.
  split; first done.
  move=> k x y Hx Hy.
  destruct k as [| k].
  - simpl in Hx. injection Hx as <-.
    simpl in Hy.
    destruct (Hfacts 0%nat y Hy) as (Hid & Hro & Ho0 & _).
    split_and!.
    + rewrite Hid Hhid /=. f_equal. lia.
    + exact (Ho0 eq_refl).
    + rewrite Hro Hhro //.
  - simpl in Hx, Hy.
    destruct (Hfacts k x Hx) as (Hidx & Hrox & _ & _).
    destruct (Hfacts (S k) y Hy) as (Hidy & Hroy & _ & Hos).
    split_and!.
    + rewrite Hidy Hidx /=. f_equal. lia.
    + exact (Hos k x eq_refl Hx).
    + rewrite Hroy Hrox //.
Qed.

(** [run_wf] telescoping: the [o]-th char's id sits exactly [o] clocks past the
    head's (same client). Feeds the RIGHT half's [id] field condition, where
    [splitNode] sets [right.id = (client, head_clock + diff)]. *)
Lemma run_wf_lookup_clock (r : list (YjsItem A)) (o : nat) (x y : YjsItem A) :
  run_wf r -> r !! 0%nat = Some x -> r !! o = Some y ->
  item_id y = MkYjsId (clientId (item_id x)) (clock (item_id x) + o).
Proof.
  move=> [_ Hstep] Hx. revert y. induction o as [|o IH] => y Hy.
  - rewrite Hx in Hy. injection Hy as <-. rewrite Nat.add_0_r.
    destruct (item_id x) as [client clock]; done.
  - have [z Hz] : is_Some (r !! o).
    { apply lookup_lt_is_Some. apply lookup_lt_Some in Hy. lia. }
    have [Hidy _] := Hstep o z y Hz Hy.
    rewrite Hidy (IH z Hz) /= Nat.add_succ_r //.
Qed.

(** [run_wf] telescoping: every char shares the run's right origin. Feeds the
    RIGHT half's [rightOrigin] condition ([splitNode] keeps [n.originRightId]). *)
Lemma run_wf_lookup_rightOrigin (r : list (YjsItem A)) (o : nat) (x y : YjsItem A) :
  run_wf r -> r !! 0%nat = Some x -> r !! o = Some y ->
  rightOrigin y = rightOrigin x.
Proof.
  move=> [_ Hstep] Hx. revert y. induction o as [|o IH] => y Hy.
  - rewrite Hx in Hy. by injection Hy as <-.
  - have [z Hz] : is_Some (r !! o).
    { apply lookup_lt_is_Some. apply lookup_lt_Some in Hy. lia. }
    have [_ [_ Hro]] := Hstep o z y Hz Hy.
    rewrite Hro (IH z Hz) //.
Qed.

Lemma explode_length (s : go_string) : length (explode s) = length s.
Proof. by rewrite /explode length_fmap. Qed.

Lemma explode_singleton (s : go_string) :
  length s = 1%nat → explode s = [s].
Proof.
  destruct s as [|b s']; first done.
  destruct s' as [|b' s'']; [done | done].
Qed.

(** [run_wf]'s chaining clause is [item/run_theory]'s [run_step]. *)
Lemma run_wf_run_step (r : list (YjsItem A)) : run_wf r -> run_step r.
Proof. move=> [_ Hstep]. exact Hstep. Qed.



(* ===== lemmas ============================================================= *)

(** Both halves of a well-formed run are well-formed (offset strictly inside). *)
Lemma run_wf_take (r : list (YjsItem A)) (o : nat) :
  (0 < o)%nat -> run_wf r -> run_wf (take o r).
Proof.
  move=> Ho [Hne Hstep]. split.
  - destruct r as [|y r']; [done |]. destruct o; [lia | done].
  - move=> k x y Hx Hy.
    apply lookup_take_Some in Hx as [Hx _]. apply lookup_take_Some in Hy as [Hy _].
    exact (Hstep k x y Hx Hy).
Qed.


Lemma run_wf_drop (r : list (YjsItem A)) (o : nat) :
  (o < length r)%nat -> run_wf r -> run_wf (drop o r).
Proof.
  move=> Ho [Hne Hstep]. split.
  - move=> Hnil. have := f_equal length Hnil. rewrite length_drop /=. lia.
  - move=> k x y Hx Hy.
    rewrite lookup_drop in Hx. rewrite lookup_drop in Hy.
    replace (o + S k)%nat with (S (o + k))%nat in Hy by lia.
    exact (Hstep (o + k)%nat x y Hx Hy).
Qed.

(** The id of the [o]-th char of a chained run: same client, head clock + o. *)
Lemma run_wf_char_id (r : list (YjsItem A)) (o : nat) (x : YjsItem A) :
  run_wf r -> r !! o = Some x ->
  item_id x = MkYjsId (clientId (item_id (hd inhabitant r)))
                      (clock (item_id (hd inhabitant r)) + o).
Proof.
  move=> [Hne Hstep].
  elim: o x => [| o IH] x Hx.
  - destruct r as [| h t]; first done.
    move: Hx => /= [= <-]. rewrite Nat.add_0_r. by destruct (item_id h).
  - have Hprev : is_Some (r !! o).
    { apply lookup_lt_is_Some. apply lookup_lt_Some in Hx. lia. }
    destruct Hprev as [y Hy].
    have [Hid _] := Hstep o y x Hy Hx.
    rewrite Hid (IH y Hy) /=. f_equal. lia.
Qed.

End item_model.
