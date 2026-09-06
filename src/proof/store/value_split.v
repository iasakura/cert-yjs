(** The [store] VALUE layer, part 2: the SPLIT SURGERY at run granularity and
    the [repair] contract, over [store/value_cells.v].

    Definitions
    - [split_locs]: the address-list half of one split, the fresh node's
      address inserted right after the node it was cut from.
    - the [repair] contract at slots [(q, k)] instead of addresses:
      [pool_origin_covered] / [pool_origins_covered] / [pool_repair_parent] /
      [pool_origins_split].
    - the index-explicit split steps at [(locs, p)]: [pool_split_step] (one
      surgery or nothing) and the precise [pool_split_left_step] /
      [pool_split_right_step] the split helpers report.

    Laws
    - a split step weakens to [pool_after_split]
      ([pool_after_split_of_split_step]) and is what the halves report
      ([pool_split_step_of_left] / [_of_right]); each half pins the boundary
      it cut at ([pool_split_left_step_ends_at] /
      [pool_split_right_step_starts_at]) and leaves every other slot alone
      ([pool_split_step_other_slot]).
    - [split_locs] at each slot ([split_locs_lookup_left] / [_right] /
      [_before] / [_after]), and a run's head id read as its client and clock
      ([run_head_item_id]).
    - what one split does to the pool's entries and to the address map
      ([pool_entries_split] / [locs_wf_split]).

    Sits above [store/value_cells.v]. *)

From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core prelude algebra network_model.
From iris.algebra Require Import auth gmap gset.
From stdpp Require Import sorting.
Local Open Scope Z_scope.
From New.proof.store Require Import model value_cells value_span.
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

(** The address-list half of the split: the left half keeps the node's
    address at [k] and the fresh right half's address [r_loc] lands right
    after it ([split_runs] is the run half, at the same cursor). *)
Definition split_locs (ls : list loc) (k : nat) (r_loc : loc) : list loc :=
  match ls !! k with
  | Some l => take k ls ++ [l; r_loc] ++ drop (S k) ls
  | None => ls
  end.

(* ===== what lookups and splits say about the pool ======================= *)

(** [pool_origin_covered p o or]: the optional origin id [o] resolves at run
    granularity to the optional pool slot [or = Some (q, k)]: the [k]-th run
    of the type at [q] has the char [o]. The run is named by its slot, not by
    a node address. *)
Definition pool_origin_covered (p : pool) (o : option YjsId)
    (or : option (loc * nat)) : Prop :=
  match o, or with
  | Some d, Some qk => pool_run_covers p qk.1 qk.2 d
  | None, None => True
  | _, _ => False
  end.

(** [pool_origins_covered p input orL orR]: what [repair] must find for a
    wire item: both origins resolve ([pool_origin_covered]), and when they
    fall in one slot the left origin precedes the right one in clock. *)
Definition pool_origins_covered (p : pool) (input : IntegrateInput (A := A))
    (orL orR : option (loc * nat)) : Prop :=
  pool_origin_covered p (in_originId input) orL ∧
  pool_origin_covered p (in_rightOriginId input) orR ∧
  match in_originId input, in_rightOriginId input, orL, orR with
  | Some a, Some b, Some qkL, Some qkR => qkL = qkR -> (clock a < clock b)%nat
  | _, _, _, _ => True
  end.

(** [pool_repair_parent bind opn orL orR p_t]: the type a repaired item
    lands in is the root bound to its wire parent name, otherwise the pool
    key of its left, else right, origin slot. *)
Definition pool_repair_parent (bind : gmap P loc) (opn : option go_string)
    (orL orR : option (loc * nat)) (p_t : loc) : Prop :=
  match opn with
  | Some nm => bind !! nm = Some p_t
  | None => match orL with
            | Some qk => p_t = qk.1
            | None => match orR with
                      | Some qk => p_t = qk.1
                      | None => False
                      end
            end
  end.

(** [pool_origins_split p' locs' input orL orR leftNode rightNode]: after [repair] the
    item's [left] is the address of a run ending at the left origin, its
    [right] of a run starting at the right origin, each in its origin slot's
    type and read off the address map [locs']; an absent origin links to
    [null]. *)
Definition pool_origins_split (p' : pool) (locs' : gmap loc (list loc))
    (input : IntegrateInput (A := A)) (orL orR : option (loc * nat))
    (leftNode rightNode : loc) : Prop :=
  match in_originId input, orL with
  | Some d, Some qk => ∃ k', pool_run_ends_at p' qk.1 k' d ∧
                             (locs' !! qk.1) ≫= (λ ls, ls !! k') = Some leftNode
  | None, None => leftNode = null
  | _, _ => False
  end ∧
  match in_rightOriginId input, orR with
  | Some d, Some qk => ∃ k', pool_run_starts_at p' qk.1 k' d ∧
                             (locs' !! qk.1) ≫= (λ ls, ls !! k') = Some rightNode
  | None, None => rightNode = null
  | _, _ => False
  end.

(* ===== lemmas ============================================================= *)

(** [pool_split_step p locs parent k p' locs']: what one of the split
    helpers ([splitAtAndGetLeft] / [splitAtAndGetRight]) does to the run
    pool and the address map at slot [(parent, k)]: nothing, or one
    [split_runs] / [split_locs] surgery at a proper offset with a fresh
    address for the right half. The index-explicit form of
    [pool_after_split], which it implies ([pool_after_split_of_split_step]);
    what the two precise forms below weaken to and what
    [store.repair]'s run-granular proof steps by. *)
Definition pool_split_step (p : pool) (locs : gmap loc (list loc)) (parent : loc) (k : nat)
    (p' : pool) (locs' : gmap loc (list loc)) : Prop :=
  (p' = p ∧ locs' = locs) ∨
  (∃ (tm : type_model) (ls : list loc) (r : ItemRun) (o : nat) (rloc : loc),
     p !! parent = Some tm ∧ locs !! parent = Some ls ∧ tm_runs tm !! k = Some r ∧
     (0 < o < length (run_items r))%nat ∧
     rloc ≠ null ∧ rloc ∉ concat ((map_to_list locs).*2) ∧
     p' = <[parent := MkTypeModel (split_runs (tm_runs tm) k o)]> p ∧
     locs' = <[parent := split_locs ls k rloc]> locs).

Lemma pool_after_split_of_split_step (p : pool) (locs : gmap loc (list loc)) (parent : loc) (k : nat)
    (p' : pool) (locs' : gmap loc (list loc)) :
  (∀ r, r ∈ all_runs p -> run_wf (run_items r)) ->
  pool_split_step p locs parent k p' locs' ->
  pool_after_split p p' parent k.
Proof.
  move=> Hwf Hstep.
  destruct Hstep as [[-> ->] | (tm & ls & r & o & rloc & Hp & Hls & Hr & Ho & _ & _ & -> & ->)].
  - exact (pool_after_split_refl p parent k).
  - apply (pool_after_split_of_split_runs p parent tm k o r Hp Hr); last exact Ho.
    apply Hwf. apply (elem_of_all_runs p r). exists parent, tm.
    split; [exact Hp | exact (list_elem_of_lookup_2 _ _ _ Hr)].
Qed.

(** Where the address surgery leaves each slot: the split node's address at
    [k], the fresh right address at [S k] (the address half of
    [split_runs_lookup_left] / [_right]). *)
Lemma split_locs_lookup_left (ls : list loc) (k : nat) (rloc lc : loc) :
  ls !! k = Some lc ->
  split_locs ls k rloc !! k = Some lc.
Proof.
  move=> Hk. rewrite /split_locs Hk.
  have Hklen : (k < length ls)%nat := lookup_lt_Some _ _ _ Hk.
  have Htk : length (take k ls) = k by (rewrite length_take_le; lia).
  rewrite lookup_app_r; last lia.
  rewrite Htk Nat.sub_diag //.
Qed.

Lemma split_locs_lookup_right (ls : list loc) (k : nat) (rloc lc : loc) :
  ls !! k = Some lc ->
  split_locs ls k rloc !! (S k) = Some rloc.
Proof.
  move=> Hk. rewrite /split_locs Hk.
  have Hklen : (k < length ls)%nat := lookup_lt_Some _ _ _ Hk.
  have Htk : length (take k ls) = k by (rewrite length_take_le; lia).
  rewrite lookup_app_r; last lia.
  rewrite Htk.
  have -> : (S k - k)%nat = 1%nat by lia.
  done.
Qed.

Lemma split_locs_lookup_before (ls : list loc) (k : nat) (rloc : loc) (j : nat) :
  (j < k)%nat ->
  split_locs ls k rloc !! j = ls !! j.
Proof.
  move=> Hj. rewrite /split_locs.
  destruct (ls !! k) as [lc|] eqn:Hk; last done.
  have Hklen : (k < length ls)%nat := lookup_lt_Some _ _ _ Hk.
  have Htk : length (take k ls) = k by (rewrite length_take_le; lia).
  rewrite lookup_app_l; last lia.
  rewrite lookup_take_lt; [done | lia].
Qed.

Lemma split_locs_lookup_after (ls : list loc) (k : nat) (rloc lc : loc) (j : nat) :
  ls !! k = Some lc -> (k < j)%nat ->
  split_locs ls k rloc !! (S j) = ls !! j.
Proof.
  move=> Hk Hj. rewrite /split_locs Hk.
  have Hklen : (k < length ls)%nat := lookup_lt_Some _ _ _ Hk.
  have Htk : length (take k ls) = k by (rewrite length_take_le; lia).
  rewrite lookup_app_r; last lia.
  rewrite Htk /=.
  have -> : (S j - k)%nat = S (S (j - S k)) by lia.
  simpl. rewrite lookup_drop. f_equal. lia.
Qed.

(** [pool_split_left_step p locs parent k d p' locs'] /
    [pool_split_right_step p locs parent k d l p' locs']: what
    [splitAtAndGetLeft] / [splitAtAndGetRight] do at the slot [(parent, k)]
    whose run covers [d]. Left: nothing when [d] is the run's last char,
    else the split just after [d]. Right: nothing when [d] is the run's
    head (the node's own address [l] comes back), else the split at [d]
    with the fresh right address [l] coming back. Both are one
    [pool_split_step] ([pool_split_step_of_left] / [_of_right]), and both
    pin where the requested boundary now sits
    ([pool_split_left_step_ends_at], [pool_split_right_step_starts_at]).
    What [wp_store__splitAtAndGetLeft_runs] / [_Right_runs] report. *)
Definition pool_split_left_step (p : pool) (locs : gmap loc (list loc)) (parent : loc) (k : nat)
    (d : YjsId) (p' : pool) (locs' : gmap loc (list loc)) : Prop :=
  ∃ (tm : type_model) (ls : list loc) (r : ItemRun),
    p !! parent = Some tm ∧ locs !! parent = Some ls ∧ tm_runs tm !! k = Some r ∧
    (((clock d - run_clock r)%nat = (length (run_items r) - 1)%nat ∧ p' = p ∧ locs' = locs) ∨
     ((clock d - run_clock r < length (run_items r) - 1)%nat ∧
      ∃ rloc : loc, rloc ≠ null ∧ rloc ∉ concat ((map_to_list locs).*2) ∧
        p' = <[parent := MkTypeModel (split_runs (tm_runs tm) k (clock d - run_clock r + 1))]> p ∧
        locs' = <[parent := split_locs ls k rloc]> locs)).

Definition pool_split_right_step (p : pool) (locs : gmap loc (list loc)) (parent : loc) (k : nat)
    (d : YjsId) (l : loc) (p' : pool) (locs' : gmap loc (list loc)) : Prop :=
  ∃ (tm : type_model) (ls : list loc) (r : ItemRun) (lc : loc),
    p !! parent = Some tm ∧ locs !! parent = Some ls ∧ tm_runs tm !! k = Some r ∧ ls !! k = Some lc ∧
    (((clock d - run_clock r)%nat = 0%nat ∧ l = lc ∧ p' = p ∧ locs' = locs) ∨
     ((0 < clock d - run_clock r)%nat ∧ l ≠ null ∧ l ∉ concat ((map_to_list locs).*2) ∧
      p' = <[parent := MkTypeModel (split_runs (tm_runs tm) k (clock d - run_clock r))]> p ∧
      locs' = <[parent := split_locs ls k l]> locs)).

Lemma pool_split_step_of_left (p : pool) (locs : gmap loc (list loc)) (parent : loc) (k : nat)
    (d : YjsId) (p' : pool) (locs' : gmap loc (list loc)) (r : ItemRun) :
  (∃ tm, p !! parent = Some tm ∧ tm_runs tm !! k = Some r) ->
  run_covers r d ->
  pool_split_left_step p locs parent k d p' locs' ->
  pool_split_step p locs parent k p' locs'.
Proof.
  move=> [tm0 [Hp0 Hr0]] [Hcl [Hlo Hhi]] [tm [ls [r' [Hp [Hls [Hr Hcase]]]]]].
  rewrite Hp0 in Hp. injection Hp as <-. rewrite Hr0 in Hr. injection Hr as <-.
  destruct Hcase as [[_ [-> ->]] | [Hlt (rloc & Hnn & Hfresh & -> & ->)]]; [by left | right].
  exists tm0, ls, r, (clock d - run_clock r + 1)%nat, rloc.
  split_and!; [exact Hp0 | exact Hls | exact Hr0 | lia | lia | exact Hnn | exact Hfresh | done | done].
Qed.

Lemma pool_split_step_of_right (p : pool) (locs : gmap loc (list loc)) (parent : loc) (k : nat)
    (d : YjsId) (l : loc) (p' : pool) (locs' : gmap loc (list loc)) (r : ItemRun) :
  (∃ tm, p !! parent = Some tm ∧ tm_runs tm !! k = Some r) ->
  run_covers r d ->
  pool_split_right_step p locs parent k d l p' locs' ->
  pool_split_step p locs parent k p' locs'.
Proof.
  move=> [tm0 [Hp0 Hr0]] [Hcl [Hlo Hhi]] [tm [ls [r' [lc [Hp [Hls [Hr [Hlk Hcase]]]]]]]].
  rewrite Hp0 in Hp. injection Hp as <-. rewrite Hr0 in Hr. injection Hr as <-.
  destruct Hcase as [[_ [_ [-> ->]]] | [Hpos (Hnn & Hfresh & -> & ->)]]; [by left | right].
  exists tm0, ls, r, (clock d - run_clock r)%nat, l.
  split_and!; [exact Hp0 | exact Hls | exact Hr0 | lia | lia | exact Hnn | exact Hfresh | done | done].
Qed.

(** The head id of a run is its client and clock. *)
Lemma run_head_item_id (r : ItemRun) :
  item_id (run_head_item r) = MkYjsId (run_client r) (run_clock r).
Proof. rewrite /run_client /run_clock. by destruct (item_id (run_head_item r)). Qed.

Lemma pool_split_left_step_ends_at (p : pool) (locs : gmap loc (list loc)) (parent : loc) (k : nat)
    (d : YjsId) (p' : pool) (locs' : gmap loc (list loc)) (r : ItemRun) (lc : loc) :
  (∃ tm, p !! parent = Some tm ∧ tm_runs tm !! k = Some r) ->
  (locs !! parent) ≫= (λ ls, ls !! k) = Some lc ->
  run_wf (run_items r) ->
  run_covers r d ->
  pool_split_left_step p locs parent k d p' locs' ->
  pool_run_starts_at p' parent k (item_id (run_head_item r)) ∧
  pool_run_ends_at p' parent k d ∧
  (locs' !! parent) ≫= (λ ls, ls !! k) = Some lc.
Proof.
  move=> [tm0 [Hp0 Hr0]] Hlc Hwf [Hcl [Hlo Hhi]] [tm [ls [r' [Hp [Hls [Hr Hcase]]]]]].
  rewrite Hp0 in Hp. injection Hp as <-. rewrite Hr0 in Hr. injection Hr as <-.
  rewrite Hls /= in Hlc.
  destruct Hcase as [[Hlast [-> ->]] | [Hlt (rloc & _ & _ & -> & ->)]].
  - split_and!.
    + exists tm0. split; first exact Hp0. exists r. done.
    + exists tm0. split; first exact Hp0. exists r. split_and!; [exact Hr0 | exact Hcl | lia].
    + rewrite Hls /=. exact Hlc.
  - have Ho : (0 < clock d - run_clock r + 1 < length (run_items r))%nat by lia.
    destruct (split_run_facts r _ Hwf Ho)
      as (Hheadl & Hlenl & Hlenr & Hclientl & Hclientr & Hclockl & Hclockr).
    split_and!.
    + exists (MkTypeModel (split_runs (tm_runs tm0) k (clock d - run_clock r + 1))).
      rewrite lookup_insert_eq. split; first done.
      exists (split_run_left r (clock d - run_clock r + 1)). simpl.
      split; [exact (split_runs_lookup_left _ _ _ _ Hr0) | rewrite Hheadl //].
    + exists (MkTypeModel (split_runs (tm_runs tm0) k (clock d - run_clock r + 1))).
      rewrite lookup_insert_eq. split; first done.
      exists (split_run_left r (clock d - run_clock r + 1)). simpl.
      split_and!; [exact (split_runs_lookup_left _ _ _ _ Hr0) | rewrite Hclientl // | rewrite Hclockl Hlenl; lia].
    + rewrite lookup_insert_eq /=. exact (split_locs_lookup_left ls k rloc lc Hlc).
Qed.

Lemma pool_split_right_step_starts_at (p : pool) (locs : gmap loc (list loc)) (parent : loc) (k : nat)
    (d : YjsId) (l : loc) (p' : pool) (locs' : gmap loc (list loc)) (r : ItemRun) :
  (∃ tm, p !! parent = Some tm ∧ tm_runs tm !! k = Some r) ->
  run_wf (run_items r) ->
  run_covers r d ->
  pool_split_right_step p locs parent k d l p' locs' ->
  ∃ k', pool_run_starts_at p' parent k' d ∧ (locs' !! parent) ≫= (λ ls, ls !! k') = Some l.
Proof.
  move=> [tm0 [Hp0 Hr0]] Hwf [Hcl [Hlo Hhi]] [tm [ls [r' [lc [Hp [Hls [Hr [Hlk Hcase]]]]]]]].
  rewrite Hp0 in Hp. injection Hp as <-. rewrite Hr0 in Hr. injection Hr as <-.
  destruct Hcase as [[Hhead [-> [-> ->]]] | [Hpos (_ & _ & -> & ->)]].
  - exists k. split.
    + exists tm0. split; first exact Hp0. exists r. split; first exact Hr0.
      rewrite run_head_item_id. destruct d as [dc dk]. simpl in *. f_equal; lia.
    + rewrite Hls /=. exact Hlk.
  - have Ho : (0 < clock d - run_clock r < length (run_items r))%nat by lia.
    destruct (split_run_facts r _ Hwf Ho)
      as (Hheadl & Hlenl & Hlenr & Hclientl & Hclientr & Hclockl & Hclockr).
    exists (S k). split.
    + exists (MkTypeModel (split_runs (tm_runs tm0) k (clock d - run_clock r))).
      rewrite lookup_insert_eq. split; first done.
      exists (split_run_right r (clock d - run_clock r)). simpl.
      split; first exact (split_runs_lookup_right _ _ _ _ Hr0).
      rewrite run_head_item_id Hclientr Hclockr. destruct d as [dc dk]. simpl in *. f_equal; lia.
    + rewrite lookup_insert_eq /=. exact (split_locs_lookup_right ls k l lc Hlk).
Qed.

(** Under one split step at [(parent, k)], the run at another slot
    [(q, j)] survives at [j] (a different type, or [j < k]) or at [S j]
    ([k < j]), with its address. *)
Lemma pool_split_step_other_slot (p : pool) (locs : gmap loc (list loc)) (parent : loc) (k : nat)
    (p' : pool) (locs' : gmap loc (list loc)) (q : loc) (j : nat) (tm : type_model) (r : ItemRun) (l : loc) :
  pool_split_step p locs parent k p' locs' ->
  p !! q = Some tm -> tm_runs tm !! j = Some r ->
  (locs !! q) ≫= (λ ls, ls !! j) = Some l ->
  ¬ (q = parent ∧ j = k) ->
  ∃ j' tm', p' !! q = Some tm' ∧ tm_runs tm' !! j' = Some r ∧
            (locs' !! q) ≫= (λ ls, ls !! j') = Some l ∧
            (j' = j ∨ (q = parent ∧ (k < j)%nat ∧ j' = S j)).
Proof.
  move=> Hstep Hq Hr Hl Hnot.
  destruct Hstep as [[-> ->] | (tm0 & ls0 & r0 & o & rloc & Hp0 & Hls0 & Hr0 & Ho & _ & _ & -> & ->)].
  { exists j, tm. split_and!; [exact Hq | exact Hr | exact Hl | by left]. }
  destruct (decide (parent = q)) as [<- | Hne]; last first.
  { exists j, tm. rewrite !lookup_insert_ne; [| exact Hne | exact Hne].
    split_and!; [exact Hq | exact Hr | exact Hl | by left]. }
  rewrite Hq in Hp0. injection Hp0 as <-.
  destruct (locs !! parent) as [ls|] eqn:Hls; last done. simpl in Hl.
  injection Hls0 as <-.
  rewrite !lookup_insert_eq /=.
  destruct (decide (j < k)%nat) as [Hlt | Hge].
  - exists j, (MkTypeModel (split_runs (tm_runs tm) k o)). simpl.
    split_and!; [done | rewrite (split_runs_lookup_before _ _ _ _ _ Hr0 Hlt) // |
                 rewrite (split_locs_lookup_before _ _ _ _ Hlt) // | by left].
  - have Hgt : (k < j)%nat.
    { destruct (decide (j = k)) as [-> | Hne']; [exfalso; apply Hnot; done | lia]. }
    exists (S j), (MkTypeModel (split_runs (tm_runs tm) k o)). simpl.
    destruct (ls !! k) as [lk|] eqn:Hlk; last first.
    { exfalso. apply lookup_ge_None in Hlk.
      have := lookup_lt_Some _ _ _ Hl. lia. }
    split_and!; [done | rewrite (split_runs_lookup_after _ _ _ _ _ Hr0 Hgt) // |
                 rewrite (split_locs_lookup_after _ _ _ _ _ Hlk Hgt) // | right; done].
Qed.

(** The pool's entries across a node split: the split entry becomes its two
    halves (the right one at the fresh address), every other entry stays
    (the run form of the cell-level split permutation). *)
Lemma pool_entries_split (locs : gmap loc (list loc)) (p : pool) (parent : loc)
    (ls : list loc) (tm : type_model) (k : nat) (l : loc) (r : ItemRun) (o : nat) (rloc : loc) :
  locs !! parent = Some ls -> p !! parent = Some tm ->
  ls !! k = Some l -> tm_runs tm !! k = Some r ->
  length ls = length (tm_runs tm) ->
  ∃ rest : list (loc * ItemRun),
    pool_entries locs p ≡ₚ (l, r) :: rest ∧
    pool_entries (<[parent := split_locs ls k rloc]> locs)
                 (<[parent := MkTypeModel (split_runs (tm_runs tm) k o)]> p)
      ≡ₚ (l, split_run_left r o) :: (rloc, split_run_right r o) :: rest.
Proof.
  move=> Hls Hp Hlk Hrk Hlen.
  set (F := λ (locs' : gmap loc (list loc)) (kv : loc * type_model),
              zip (default [] (locs' !! kv.1)) (tm_runs kv.2)).
  set (others := concat (F locs <$> map_to_list (delete parent p))).
  have Hpe : ∀ (locs' : gmap loc (list loc)) (tm' : type_model),
      (∀ q, q ≠ parent -> locs' !! q = locs !! q) ->
      pool_entries locs' (<[parent := tm']> p) ≡ₚ F locs' (parent, tm') ++ others.
  { move=> locs' tm' Hq. rewrite /pool_entries.
    have Hm : F locs' <$> map_to_list (<[parent := tm']> p)
            ≡ₚ F locs' <$> ((parent, tm') :: map_to_list (delete parent p)).
    { apply Permutation_map. exact (map_to_list_insert_existing p parent tm tm' Hp). }
    rewrite (concat_perm _ _ Hm) fmap_cons concat_cons. apply Permutation_app_head. rewrite /others.
    have -> : F locs' <$> map_to_list (delete parent p) = F locs <$> map_to_list (delete parent p);
      last reflexivity.
    apply list_fmap_ext. move=> i [q tmq] Hi. rewrite /F /=.
    have Hq' : delete parent p !! q = Some tmq
      by (apply elem_of_map_to_list; exact (list_elem_of_lookup_2 _ _ _ Hi)).
    apply lookup_delete_Some in Hq' as [Hne _]. rewrite (Hq q (λ H, Hne (eq_sym H))) //. }
  set (A := zip (take k ls) (take k (tm_runs tm))).
  set (B := zip (drop (S k) ls) (drop (S k) (tm_runs tm))).
  have HlenA : length (take k ls) = length (take k (tm_runs tm)) by rewrite !length_take Hlen.
  have Hother : ∀ q, q ≠ parent -> <[parent := split_locs ls k rloc]> locs !! q = locs !! q.
  { move=> q Hne. rewrite lookup_insert_ne //. }
  exists (A ++ B ++ others). split.
  - rewrite -{1}(insert_id p parent tm Hp) (Hpe locs tm (λ q _, eq_refl)) /F /= Hls /=.
    rewrite -{1}(take_drop_middle ls k l Hlk) -{1}(take_drop_middle (tm_runs tm) k r Hrk).
    rewrite zip_with_app; last exact HlenA.
    simpl. rewrite -/A -/B -app_assoc /=.
    symmetry. apply Permutation_middle.
  - rewrite (Hpe (<[parent := split_locs ls k rloc]> locs) _ Hother) /F /=.
    rewrite lookup_insert_eq /= /split_locs /split_runs Hlk Hrk /=.
    rewrite zip_with_app; last exact HlenA.
    simpl. rewrite -/A -/B -app_assoc /=.
    etransitivity; first (symmetry; apply Permutation_middle).
    apply perm_skip. symmetry. apply Permutation_middle.
Qed.

(** The address map stays well formed across a split whose right half lands
    at a fresh address. *)
Lemma locs_wf_split (locs : gmap loc (list loc)) (p : pool) (parent : loc)
    (ls : list loc) (tm : type_model) (k : nat) (l : loc) (r : ItemRun) (o : nat) (rloc : loc) :
  locs !! parent = Some ls -> p !! parent = Some tm ->
  ls !! k = Some l -> tm_runs tm !! k = Some r ->
  rloc ∉ concat ((map_to_list locs).*2) ->
  locs_wf locs p ->
  locs_wf (<[parent := split_locs ls k rloc]> locs)
          (<[parent := MkTypeModel (split_runs (tm_runs tm) k o)]> p).
Proof.
  move=> Hls Hp Hlk Hrk Hfresh [Hdom [Hnd Hlens]].
  have Hklt : (k < length ls)%nat := lookup_lt_Some _ _ _ Hlk.
  have Hperm0 : concat ((map_to_list locs).*2) ≡ₚ ls ++ concat ((map_to_list (delete parent locs)).*2).
  { rewrite -{1}(insert_id locs parent ls Hls).
    rewrite (concat_perm _ _ (Permutation_map snd (map_to_list_insert_existing locs parent ls ls Hls))) //. }
  have Hperm : concat ((map_to_list (<[parent := split_locs ls k rloc]> locs)).*2)
             ≡ₚ split_locs ls k rloc ++ concat ((map_to_list (delete parent locs)).*2).
  { rewrite (concat_perm _ _ (Permutation_map snd (map_to_list_insert_existing locs parent ls _ Hls))) //. }
  have Hsl : split_locs ls k rloc ≡ₚ rloc :: ls.
  { rewrite /split_locs Hlk -{3}(take_drop_middle ls k l Hlk).
    have -> : take k ls ++ [l; rloc] ++ drop (S k) ls = (take k ls ++ [l]) ++ rloc :: drop (S k) ls
      by rewrite -app_assoc //.
    have -> : take k ls ++ l :: drop (S k) ls = (take k ls ++ [l]) ++ drop (S k) ls
      by rewrite -app_assoc //.
    symmetry. apply Permutation_middle. }
  split_and!.
  - rewrite !dom_insert_L Hdom //.
  - rewrite Hperm Hsl. rewrite Hperm0 in Hnd Hfresh.
    apply NoDup_cons. split; [exact Hfresh | exact Hnd].
  - move=> q lsq tmq. destruct (decide (q = parent)) as [-> | Hne].
    + rewrite !lookup_insert_eq. move=> [<-] [<-]. simpl.
      have Hlsl := Hlens parent ls tm Hls Hp.
      rewrite /split_locs Hlk /= !length_app /= length_take_le; last lia.
      rewrite length_drop (split_runs_length _ _ _ _ Hrk). lia.
    + rewrite !lookup_insert_ne //. exact (Hlens q lsq tmq).
Qed.

End store_value_split.
