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

    Second section ([item_run], docs/plan-item-run-split.md stage 1): the
    run as pure DATA.
    - [ItemRun]: a node's run of items and its tombstone bit, no [loc].
    - its vocabulary: [run_head_item], [run_client] / [run_clock] (pure
      [nat]s), [runs_flatten], [runs_visible], [flip_run], [run_fits],
      [run_covers] / [run_covers_clock], [run_origin_clk], [run_le]
      (the clock order on runs), [runs_disjoint]
      (runs told apart by index, not address), and the split surgery
      [split_run_left] / [split_run_right] / [split_runs]; the index-based
      forms of the pool statements: [runs_start_at] / [runs_end_at],
      [origins_resolved] (cursor indices), [runs_integrate_splice] (the
      cursor-explicit [runs_integrate_splice_at] under an exists), and
      [runs_within]: every run after a step sits inside a run before it,
      and [ids_tombstoned_runs]: a set of ids all covered by tombstoned
      runs; [items_string], the string a run of per-char items spells
      (append-homomorphic, [items_string_app], and recovering an exploded
      string, [items_string_explode]); [input_of_run], the wire item a run
      denotes, and [run_per_char]: each of the run's items carries exactly
      one byte of that wire content ([explode] is append-homomorphic,
      [explode_app], and [run_per_char] survives the split surgery,
      [run_per_char_split_left] / [run_per_char_split_right]); the split
      halves' head / length / client / clock facts in one bundle
      ([split_run_facts], over [hd_inhabitant_take] / [_drop]), and
      [runs_disjoint] is permutation-invariant ([runs_disjoint_perm]).
    - laws: a split is invisible to the flatten and the visible count
      ([split_runs_flatten], [split_runs_visible]); [runs_flatten] is
      app-morphic ([runs_flatten_app]).

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

(* ===== the run record (ItemRun), the loc-free half of item_cell ==========
   Stage 1 of docs/plan-item-run-split.md: the pure theory of runs as data,
   next to the [item_cell]-based one it will replace. [item_cell] pairs a run
   with heap addresses ([ic_loc], [ic_parent]); [ItemRun] is the run alone,
   so clock-range reasoning, splits and tombstones need no [loc] and no
   [w64]. [item/value.v]'s [cell_run] projects a cell to its run, and each
   cell-level definition comes with a projection lemma there. *)

Section item_run.

Set Default Proof Using "Type*".

Notation A := go_string.

(* ===== definitions ======================================================== *)

(** [ItemRun]: what one heap node holds, as pure data: the run of consecutive
    per-char model items ([run_wf]) and its tombstone bit. *)
Record ItemRun := MkItemRun {
  run_items : list (YjsItem A);
  run_deleted : bool;
}.

(** The head model item of a run: the one the node's id / origin fields
    denote ([run_wf] makes every other item a function of it). *)
Definition run_head_item (r : ItemRun) : YjsItem A := hd inhabitant (run_items r).

(** The creator and start clock of a run, off its head id. Pure [nat]s: the
    [w64] the heap stores round-trips on the value layer ([cell_client] /
    [cell_clock]). *)
Definition run_client (r : ItemRun) : nat := clientId (item_id (run_head_item r)).

Definition run_clock (r : ItemRun) : nat := clock (item_id (run_head_item r)).

(** The flattened per-char document list a run list denotes. *)
Definition runs_flatten (runs : list ItemRun) : list (YjsItem A) :=
  mjoin (run_items <$> runs).

(** Number of visible (non-tombstoned) characters: the value the heap keeps
    in [yType.len]. *)
Definition runs_visible (runs : list ItemRun) : nat :=
  list_sum ((λ r, if run_deleted r then 0%nat else length (run_items r)) <$> runs).

(** The run with its tombstone bit set (its items unchanged): what one
    [deleteNode] does. *)
Definition flip_run (r : ItemRun) : ItemRun :=
  MkItemRun (run_items r) true.

(** The run's clock range [run_clock, run_clock + length) fits [w64]
    arithmetic without wrapping: the pure content of [cell_fits]. *)
Definition run_fits (r : ItemRun) : Prop :=
  (Z.of_nat (run_clock r) + Z.of_nat (length (run_items r)) < 2^64)%Z.

(** [run_covers r d]: the id [d] addresses a char of [r]: same creator as the
    head, clock inside the run's range. Under [run_wf] this is exactly "[d]
    is the id of some item of [r]" ([run_wf_char_id]). *)
Definition run_covers (r : ItemRun) (d : YjsId) : Prop :=
  run_client r = clientId d ∧
  (run_clock r <= clock d)%nat ∧
  (clock d < run_clock r + length (run_items r))%nat.

(** [run_covers_clock r k]: some char of [r] has clock [k], whatever the
    creator (the per-client index search only compares clocks). *)
Definition run_covers_clock (r : ItemRun) (k : nat) : Prop :=
  (run_clock r <= k)%nat ∧ (k < run_clock r + length (run_items r))%nat.

(** A run head's same-client left origin strictly precedes it in clock
    (causal creation order): the pure content of [cell_origin_clk]. *)
Definition run_origin_clk (r : ItemRun) : Prop :=
  ∀ originId, origin_id (origin (run_head_item r)) = Some originId →
    clientId originId = run_client r →
    (clock originId < run_clock r)%nat.

(** The clock order on runs: what sorts a client's run list. *)
Definition run_le (r1 r2 : ItemRun) : Prop := (run_clock r1 <= run_clock r2)%nat.

#[global] Instance run_le_dec : RelDecision run_le.
Proof. rewrite /run_le. solve_decision. Defined.

#[global] Instance run_le_trans : Transitive run_le.
Proof. rewrite /run_le. move=> x y z. lia. Qed.

#[global] Instance run_le_total : Total run_le.
Proof. rewrite /run_le. move=> x y. lia. Qed.

(** Per-client clock-range disjointness of a run list, with runs told apart
    BY INDEX (the loc-free replacement of [cells_range_disjoint], which tells
    cells apart by [ic_loc]; the two agree when node addresses are distinct,
    the heap-layer [NoDup]). *)
Definition runs_disjoint (runs : list ItemRun) : Prop :=
  ∀ i j r1 r2, runs !! i = Some r1 → runs !! j = Some r2 → i ≠ j →
    run_client r1 = run_client r2 →
    (run_clock r1 + length (run_items r1) <= run_clock r2)%nat ∨
    (run_clock r2 + length (run_items r2) <= run_clock r1)%nat.

(** [runs_within before after]: every run of [after] sits inside a
    same-client run of [before]'s clock range: the loc-free [cells_within]. *)
Definition runs_within (before after : list ItemRun) : Prop :=
  ∀ r, r ∈ after -> ∃ r0, r0 ∈ before ∧ run_client r = run_client r0 ∧
    (run_clock r0 <= run_clock r)%nat ∧
    (run_clock r + length (run_items r) <= run_clock r0 + length (run_items r0))%nat.

(** Splitting the [k]-th run at offset [o]: the left half keeps the first [o]
    items, the right half the rest, both inheriting the tombstone bit (the
    yjs [splitItem] semantics). The fresh node's ADDRESS, which
    [split_cells] threads as [r_loc], is a heap matter and does not appear. *)
Definition split_run_left (r : ItemRun) (o : nat) : ItemRun :=
  MkItemRun (take o (run_items r)) (run_deleted r).

Definition split_run_right (r : ItemRun) (o : nat) : ItemRun :=
  MkItemRun (drop o (run_items r)) (run_deleted r).

Definition split_runs (runs : list ItemRun) (k o : nat) : list ItemRun :=
  match runs !! k with
  | Some r => take k runs ++ [split_run_left r o; split_run_right r o] ++ drop (S k) runs
  | None => runs
  end.

(** [runs_start_at runs k d] / [runs_end_at runs k d]: the [k]-th run starts
    (ends) at the id [d]: the index-based content of [cell_starts_at] /
    [cell_ends_at], whose node address and owning type are heap matters. *)
Definition runs_start_at (runs : list ItemRun) (k : nat) (d : YjsId) : Prop :=
  ∃ r, runs !! k = Some r ∧ item_id (run_head_item r) = d.

Definition runs_end_at (runs : list ItemRun) (k : nat) (d : YjsId) : Prop :=
  ∃ r, runs !! k = Some r ∧ run_client r = clientId d ∧
       (run_clock r + length (run_items r) = clock d + 1)%nat.

(** [origins_resolved runs arr input kL kR]: the cursor indices at which the
    resolved origins of [input] in [arr] sit: the run cursor [kL] whose
    prefix sum is one past the left origin's model index ([findLeftIdx]) and
    [kR] whose prefix sum is the right origin's ([findRightIdx]). The
    index-based content of [origins_linked]: the linked node ADDRESSES are
    [node_loc] of these cursors, a value-layer fact. *)
Definition origins_resolved (runs : list ItemRun) (arr : list (YjsItem A))
    (input : IntegrateInput (A := A)) (kL kR : nat) : Prop :=
  ∃ (leftIdx rightIdx : Z),
    findLeftIdx (in_originId input) arr = Some leftIdx ∧
    findRightIdx (in_rightOriginId input) arr = Some rightIdx ∧
    (Z.of_nat (length (runs_flatten (take kL runs))) = leftIdx + 1)%Z ∧
    (kL <= length runs)%nat ∧
    (Z.of_nat (length (runs_flatten (take kR runs))) = rightIdx)%Z ∧
    (kR <= length runs)%nat.

(** [runs_integrate_splice_at idx runs arr run runs' arr']: what one
    integrate does, loc-free: a fresh live run is spliced into [runs] at the
    cursor [idx], and its items into [arr] at the matching model index (the
    prefix sum of the runs before it). The new node's address and type are
    heap matters ([integrate_splice] carries them; the address list gets the
    same splice, [store/value_cells]'s [integrate_locs]).
    [runs_integrate_splice] hides the cursor. *)
Definition runs_integrate_splice_at (idx : nat) (runs : list ItemRun)
    (arr : list (YjsItem A)) (run : list (YjsItem A))
    (runs' : list ItemRun) (arr' : list (YjsItem A)) : Prop :=
  (idx <= length runs)%nat ∧
  (length (runs_flatten (take idx runs)) <= length arr)%nat ∧
  runs' = take idx runs ++ MkItemRun run false :: drop idx runs ∧
  arr' = take (length (runs_flatten (take idx runs))) arr ++ run ++
         drop (length (runs_flatten (take idx runs))) arr.

Definition runs_integrate_splice (runs : list ItemRun) (arr : list (YjsItem A))
    (run : list (YjsItem A)) (runs' : list ItemRun) (arr' : list (YjsItem A)) : Prop :=
  ∃ idx : nat, runs_integrate_splice_at idx runs arr run runs' arr'.

(** [ids_tombstoned_runs ids runs]: every id of [ids] is a char of some
    tombstoned run of [runs]: the loc-free [ids_tombstoned], what a
    run-granular delete reports about what it just did. *)
Definition ids_tombstoned_runs (ids : gset YjsId) (runs : list ItemRun) : Prop :=
  ∀ i, i ∈ ids -> ∃ r, r ∈ runs ∧ run_deleted r = true ∧ i ∈ char_ids (run_items r).

(** [items_string l]: the string a list of per-char items spells (the
    concatenation of their contents). A bespoke [foldr], NOT
    [mjoin (content <$> ...)]: using [content] as [fmap]'s function argument
    together with [mjoin] entangles rocq-yjs's [YjsPtr.u0] universe with
    stdpp's monad-class universes, and in any file that also loads
    Perennial's [New.ghost] universal-[own] syntax codes that chain
    contradicts [syntax.cmra]'s universe bound (the [IsCmra] instances for
    [gset (YjsItem A)] then fail with "no instance found"). The
    fully-applied [content x] avoids the entanglement. Moved here from
    [ytype/value.v] for [input_of_run] (stage 3). *)
Definition items_string (l : list (YjsItem A)) : A :=
  foldr (λ x acc, content x ++ acc) [] l.

(** [input_of_run r]: the wire item a run denotes: its head's id and origin
    ids, and the string its chars spell. What the stage-3 node predicate
    ([own_item_node]) is pinned to when it holds a DLL node. *)
Definition input_of_run (r : ItemRun) : IntegrateInput (A := A) :=
  MkIntegrateInput
    (origin_id (origin (run_head_item r)))
    (origin_id (rightOrigin (run_head_item r)))
    (items_string (run_items r))
    (item_id (run_head_item r)).

(** [run_per_char r]: each item of the run carries exactly one byte of the
    string the run spells: the per-char granularity of the model
    (issue #28). The wire view ([input_of_run]) alone cannot recover how
    its content splits over the run's items; today the heap content pin
    ([own_dll]'s explode equation) carries it, and the run-granular DLL
    ([own_dll_runs]) states it per run. *)
Definition run_per_char (r : ItemRun) : Prop :=
  content <$> run_items r = explode (items_string (run_items r)).

(* ===== lemmas ============================================================= *)

(** The flatten and the visible count are invariant under a split, and a flip
    only drops the flipped run's characters from the visible count: the run
    halves of [split_cells_flatten] / [split_cells_num_visible] /
    [num_visible_flip_run], loc-free. *)
Lemma runs_flatten_nil : runs_flatten [] = [].
Proof. reflexivity. Qed.

Lemma items_string_app (l1 l2 : list (YjsItem A)) :
  items_string (l1 ++ l2) = items_string l1 ++ items_string l2.
Proof.
  induction l1 as [|x l1 IH]; first done.
  rewrite /items_string /= -/(items_string (l1 ++ l2)) -/(items_string l1)
    IH app_assoc //.
Qed.

(** A run whose per-char contents explode a heap content string spells exactly
    that string (the [own_dll] node fact, consumed by the [yType.Text] walk
    and the stage-3 node borrows). *)
Lemma items_string_explode (r : list (YjsItem A)) (s : go_string) :
  content <$> r = explode s -> items_string r = s.
Proof.
  revert s. induction r as [|x r IH] => s Hc.
  - destruct s; [done | discriminate].
  - destruct s as [|b s']; first discriminate.
    injection Hc as Hx Hr.
    rewrite /items_string /= -/(items_string r) (IH s' Hr) Hx //.
Qed.

Lemma explode_app (s1 s2 : go_string) :
  explode (s1 ++ s2) = explode s1 ++ explode s2.
Proof. rewrite /explode fmap_app //. Qed.

(** The head model item survives a nonempty left truncation ([take]): the
    split's LEFT half keeps the head. *)
Lemma hd_inhabitant_take (r : list (YjsItem A)) (o : nat) :
  (0 < o)%nat -> hd inhabitant (take o r) = hd inhabitant r.
Proof.
  move=> Ho. destruct r as [|a r']; first by rewrite take_nil.
  destruct o; [lia | done].
Qed.

(** The head of a right drop is the element at the drop offset: where the
    split's RIGHT half heads. *)
Lemma hd_inhabitant_drop (r : list (YjsItem A)) (o : nat) (y : YjsItem A) :
  r !! o = Some y -> hd inhabitant (drop o r) = y.
Proof. move=> Ho. rewrite (drop_S r y o Ho) //=. Qed.

(** The two halves' head / length / client / clock facts of a run split, in
    one bundle ([split_cell_facts] at nat granularity). *)
Lemma split_run_facts (r : ItemRun) (o : nat) :
  run_wf (run_items r) ->
  (0 < o < length (run_items r))%nat ->
  run_head_item (split_run_left r o) = run_head_item r ∧
  length (run_items (split_run_left r o)) = o ∧
  length (run_items (split_run_right r o)) = (length (run_items r) - o)%nat ∧
  run_client (split_run_left r o) = run_client r ∧
  run_client (split_run_right r o) = run_client r ∧
  run_clock (split_run_left r o) = run_clock r ∧
  run_clock (split_run_right r o) = (run_clock r + o)%nat.
Proof.
  move=> Hrunwf [Hopos Holt].
  have Hrun0 : run_items r !! 0%nat = Some (run_head_item r).
  { rewrite /run_head_item. destruct Hrunwf as [Hne _].
    destruct (run_items r) as [|a r']; [done | reflexivity]. }
  destruct (run_items r !! o) as [yo|] eqn:Hyo; last by (apply lookup_ge_None in Hyo; lia).
  have Hidy := run_wf_lookup_clock (run_items r) o (run_head_item r) yo Hrunwf Hrun0 Hyo.
  have Hheadl : run_head_item (split_run_left r o) = run_head_item r.
  { rewrite /run_head_item /split_run_left /=. apply hd_inhabitant_take. lia. }
  have Hheadr : run_head_item (split_run_right r o) = yo.
  { rewrite /run_head_item /split_run_right /=. exact (hd_inhabitant_drop _ o yo Hyo). }
  split_and!.
  - exact Hheadl.
  - rewrite /split_run_left /= length_take. lia.
  - rewrite /split_run_right /= length_drop //.
  - rewrite /run_client Hheadl //.
  - rewrite /run_client Hheadr Hidy //=.
  - rewrite /run_clock Hheadl //.
  - rewrite /run_clock Hheadr Hidy //=.
Qed.

(** [runs_disjoint] is permutation-invariant: the index pairs transport
    along [Permutation_inj]'s bijection. *)
Lemma runs_disjoint_perm (runs1 runs2 : list ItemRun) :
  runs1 ≡ₚ runs2 -> runs_disjoint runs1 -> runs_disjoint runs2.
Proof.
  move=> Hperm Hdisj.
  symmetry in Hperm.
  apply Permutation_inj in Hperm as [_ (f & Hinj & Hf)].
  move=> i j r1 r2 Hi Hj Hij Hcl.
  apply (Hdisj (f i) (f j) r1 r2).
  - rewrite -Hf //.
  - rewrite -Hf //.
  - move=> Hfij. apply Hij. exact (Hinj _ _ Hfij).
  - exact Hcl.
Qed.

(** Peeling one item off a per-char run: its content is one byte, and the
    tail is per-char again. The induction step of the split-surgery
    preservation below. *)
Lemma per_char_cons_inv (x : YjsItem A) (l : list (YjsItem A)) :
  content <$> (x :: l) = explode (items_string (x :: l)) ->
  (∃ b, content x = [b]) ∧ content <$> l = explode (items_string l).
Proof.
  move=> Hpc.
  have Hs : items_string (x :: l) = content x ++ items_string l by reflexivity.
  have Hf : content <$> (x :: l) = content x :: (content <$> l) by reflexivity.
  rewrite Hs explode_app Hf in Hpc.
  destruct (content x) as [|b bs] eqn:Hcx.
  - simpl in Hpc.
    destruct (items_string l) as [|b' s'].
    + discriminate Hpc.
    + have He : explode (b' :: s') = [b'] :: explode s' by reflexivity.
      idtac "B1C". Set Printing All. Show.
      rewrite He in Hpc. injection Hpc as Hh _. discriminate Hh.
  - have He : explode (b :: bs) = [b] :: explode bs by reflexivity.
    rewrite He in Hpc. simpl in Hpc.
    injection Hpc as Hx Hrest.
    simplify_eq/=.
    split; [by exists b | exact Hrest].
Qed.

(** [run_per_char] survives the split surgery: each half of a split run is
    per-char again (the premises of [own_dll_runs_split], discharged from
    the split node's original pin). *)
Lemma run_per_char_split_left (r : ItemRun) (o : nat) :
  run_per_char r -> run_per_char (split_run_left r o).
Proof.
  rewrite /run_per_char /split_run_left /=.
  move: o. induction (run_items r) as [|x l IH] => o Hpc.
  - rewrite take_nil //.
  - destruct o as [|o']; [done |].
    destruct (per_char_cons_inv x l Hpc) as [[b Hb] Htail].
    have Ht : take (S o') (x :: l) = x :: take o' l by reflexivity.
    have Hf : content <$> (x :: take o' l) = content x :: (content <$> take o' l)
      by reflexivity.
    have Hs : items_string (x :: take o' l) = content x ++ items_string (take o' l)
      by reflexivity.
    have He : explode [b] = [[b]] by reflexivity.
    rewrite Ht Hf Hs explode_app Hb He /=.
    f_equal; try done. exact (IH o' Htail).
Qed.

Lemma run_per_char_split_right (r : ItemRun) (o : nat) :
  run_per_char r -> run_per_char (split_run_right r o).
Proof.
  rewrite /run_per_char /split_run_right /=.
  move: o. induction (run_items r) as [|x l IH] => o Hpc.
  - rewrite drop_nil //.
  - destruct o as [|o']; [exact Hpc |].
    destruct (per_char_cons_inv x l Hpc) as [_ Htail].
    rewrite /=. exact (IH o' Htail).
Qed.

Lemma runs_flatten_cons (r : ItemRun) (runs : list ItemRun) :
  runs_flatten (r :: runs) = run_items r ++ runs_flatten runs.
Proof. reflexivity. Qed.

Lemma runs_flatten_app (rs1 rs2 : list ItemRun) :
  runs_flatten (rs1 ++ rs2) = runs_flatten rs1 ++ runs_flatten rs2.
Proof. rewrite /runs_flatten fmap_app join_app //. Qed.

Lemma split_runs_flatten (runs : list ItemRun) (k o : nat) (r : ItemRun) :
  runs !! k = Some r ->
  runs_flatten (split_runs runs k o) = runs_flatten runs.
Proof.
  move=> Hk.
  have Hmid : runs_flatten runs
            = runs_flatten (take k runs) ++ run_items r ++ runs_flatten (drop (S k) runs).
  { rewrite -{1}(take_drop_middle runs k r Hk) runs_flatten_app runs_flatten_cons //. }
  rewrite /split_runs Hk Hmid.
  rewrite !runs_flatten_app !runs_flatten_cons runs_flatten_nil app_nil_r /=.
  rewrite take_drop //.
Qed.

Lemma split_runs_visible (runs : list ItemRun) (k o : nat) (r : ItemRun) :
  runs !! k = Some r ->
  (o <= length (run_items r))%nat ->
  runs_visible (split_runs runs k o) = runs_visible runs.
Proof.
  move=> Hk Ho.
  have Hmid : runs_visible runs
            = (runs_visible (take k runs)
               + ((if run_deleted r then 0%nat else length (run_items r))
                  + runs_visible (drop (S k) runs)))%nat.
  { rewrite -{1}(take_drop_middle runs k r Hk) /runs_visible fmap_app fmap_cons list_sum_app /=.
    lia. }
  rewrite /split_runs Hk Hmid /runs_visible !fmap_app !fmap_cons !list_sum_app /=.
  destruct (run_deleted r); simpl; [lia |].
  rewrite length_take length_drop. lia.
Qed.

Lemma flip_run_items (r : ItemRun) : run_items (flip_run r) = run_items r.
Proof. reflexivity. Qed.

End item_run.
