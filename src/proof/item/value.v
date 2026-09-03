(** The [item] type, VALUE layer: the heap node as the proofs see it, and what
    it denotes. Go values but no Iris.

    Definitions
    - [item_cell]: one node, its location plus the run of model items it
      carries, its tombstone bit and its resolved parent type; [node_loc] is
      the cursor into a cell list ([loc_at] the same cursor over a bare
      address list, [node_loc_loc_at] relating them); [run_head] its first
      item, [cell_unit] the one-item case.
    - [run_flatten cells]: the document list a cell list denotes.
    - [cell_repr] / [cells_repr]: the isomorphism from a cell list to a model
      item list.
    - [cells_of_locs_runs]: the cell list an address list and a run list
      determine under one type (the run-granular elimination's zip,
      [cells_of_locs_runs_run] / [_loc] / [_parent]; on the projections it
      is the identity, [cells_of_locs_runs_projections]; with one slot
      tombstoned it is the cell list with that cell flipped,
      [cells_of_locs_runs_flip], and with one run spliced in it is the
      cell list with the matching cell spliced in,
      [cells_of_locs_runs_splice]).
    - the flag accessors [is_deleted_flag] / [is_countable_flag] reading the
      heap struct's bits, [set_deleted] / [flip_cell] flipping the tombstone,
      and [num_visible], the visible-character count [yType.len] shadows.
    - [toContent] and [originId_of], the remaining scalar readings.
    - [cell_run]: the pure half of a cell, its [ItemRun]
      (docs/plan-item-run-split.md stage 1).

    Laws
    - the run vocabulary projects along [cell_run]: [cell_run_head],
      [run_flatten_runs], [num_visible_runs], [cell_run_flip],
      [cell_unit_runs].
    - [run_flatten] is a monoid morphism ([run_flatten_nil] / [_cons] / [_app])
      and collapses to [run_head <$> cells] on unit cells.
    - the cell-cursor prefix sums: [run_flatten (take k cells)] grows by one
      cell at a time, is strictly monotone and injective in [k]
      ([run_flatten_take_S], [_length_lt], [_length_inj]), and a cell's
      [off]-th char sits at prefix-sum + [off] ([run_flatten_lookup_of_cell]).
      This is what makes a cell index and a character index interchangeable.
    - [cells_repr] is closed under [cons] / [app] / [take] / [drop] / [insert],
      determines lengths and lookups, and is insensitive to its model
      parameter.
    - the deletion layer: [num_visible] is additive over [app], drops by one
      when a visible cell is flipped, and is unchanged by an insert of a
      deleted cell ([num_visible_app], [num_visible_flip(_run)],
      [num_visible_insert_visible(_run)]); flipping preserves [cell_repr].
    - the heap flags pin the tombstone bit exactly ([flags_if_deleted],
      [flags_if_countable], [set_deleted_flags]).

    The Iris layer over these cells is [item/heap.v]. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core prelude.
From New.proof.item Require Import run_theory model.
From New.proof.id Require Import value heap.

Section item_value.

Set Default Proof Using "Type*".

Notation A := go_string.

(* ===== definitions ======================================================== *)

(** One node of the heap DLL: its location and the *model* items it carries.

    A node covers a RUN of consecutive per-char model items ([ic_run], issue
    #28): the heap item's content of clock-length n denotes n model items with
    consecutive clocks, each chained to the previous one by its left origin and
    all sharing the run's right origin ([run_wf] below). Every current creator
    mints runs of length 1, but the representation layer is stated for any
    length so splitting (and later multi-element content, #25) is pure cell
    surgery with the flattened model unchanged.

    The cell holds only stable, model-relevant data — the heap struct
    ([yjs.item.t]) with its volatile [left']/[right'] links, its [w64] id /
    content / origin-id pointers, and its flags is *not* stored here; it is
    existentially quantified inside [own_dll] (see [item/item]) and constrained to
    *translate* to the run's HEAD item (heap id [toYjsId]-maps to
    [item_id (run_head c)], the content explodes to the per-char contents,
    etc.); the non-head items carry no heap data of their own — [run_wf]
    reconstructs their ids and origins from the head. This keeps the abstract
    cell list invariant under [Store.Integrate]'s neighbour relinking —
    relinking changes only the existential heap struct, not [ic_run], so the
    abstract [cells] is unchanged across the splice. Origins live in the model
    items (they are order-defining model data), so order recovery
    ([YjsLt'] / [YjsArrInvariant.yai_sorted]) is intact.

    One non-link flag is promoted out of the existential heap struct: [ic_deleted]
    mirrors the heap node's Deleted bit (y-octo ITEM_DELETED). [own_dll] pins the
    existential struct's flags to [ic_deleted] (Countable, Deleted = [ic_deleted]),
    so the visible-character count is a pure function of the abstract cells
    ([num_visible], the source of truth for [yType.len]). [Text.Delete] tombstones
    a cell by flipping [ic_deleted]; [ic_item] (hence the abstract document list)
    is untouched, so deletion never reorders or removes a document item.

    [ic_parent] mirrors the heap node's [parent] pointer (issue #49: items carry
    their resolved parent type, y-octo [Some (Parent::Type)]). Like [ic_deleted]
    it is promoted out of the existential struct — [own_dll] pins the struct's
    [parent'] field to it — so [store.repair]'s borrow-from-neighbour reads it
    through the abstract cells; [own_ytype_cells] pins every cell of a type's
    DLL to that type's own loc. *)
Record item_cell := MkItemCell {
  ic_loc : loc;
  ic_run : list (YjsItem A);
  ic_deleted : bool;
  ic_parent : loc;
}.

(** The head model item of a cell's run: the one the heap struct's id /
    origin-id fields translate to. *)
Definition run_head (c : item_cell) : YjsItem A := hd inhabitant (ic_run c).

(** The flattened per-char document list a cell list denotes. *)
Definition run_flatten (cells : list item_cell) : list (YjsItem A) :=
  mjoin (ic_run <$> cells).

(** Under the all-singleton invariant (every creator today mints 1-char runs;
    temporary until the run-scan bridge of issue #28 M4), the flatten is a
    plain head map, recovering the pre-#28 cell/model 1:1 correspondence. *)
Definition cell_unit (c : item_cell) : Prop := length (ic_run c) = 1%nat.

(** The loc of the node at index [k] of [cells] ([null] outside [0, len)).
    Used to place the heap [conflict] / [left] pointers within the DLL. *)
Definition node_loc (cells : list item_cell) (k : Z) : loc :=
  if decide (0 <= k)%Z then default null (ic_loc <$> cells !! Z.to_nat k) else null.

(** [loc_at ls k]: [node_loc] over a bare address list ([null] outside
    [0, len)): how a run-granular spec reads a node address off the
    [sr_locs] half of the store state (plan-item-run-split stage 2). *)
Definition loc_at (ls : list loc) (k : Z) : loc :=
  if decide (0 <= k)%Z then default null (ls !! Z.to_nat k) else null.

(* ----- per-node accessors read by yType.findPos -------------------------- *)

(** The Deleted bit (y-octo ITEM_DELETED = 0x04) of a heap item's [flags], read
    exactly as [item.Deleted] computes it ([flags & 0x04 ≠ 0]). This boolean is
    the heap source of truth for visibility (a tombstoned node has it set). *)
Definition is_deleted_flag (v : yjs.item.t) : bool :=
  negb (bool_decide (w8_word_instance.(word.and) v.(yjs.item.flags') (W8 4) = W8 0)).

(** The Countable bit (ITEM_COUNTABLE = 0x02), read as [item.Countable] does.
    Every string item NewItem builds is countable, so this is [true] of every
    integrated node; it is what [item.Indexable] gates visibility on. *)
Definition is_countable_flag (v : yjs.item.t) : bool :=
  negb (bool_decide (w8_word_instance.(word.and) v.(yjs.item.flags') (W8 2) = W8 0)).

(** Number of visible (non-deleted) CHARACTERS: the value carried in the heap
    [yType.len] field. Every cell is Countable, so visible ⇔ not Deleted; the
    flag is promoted onto the abstract cell as [ic_deleted], and a visible cell
    contributes its whole run length (issue #28; the Go bumps [parent.len] by
    [item.Len()]). *)
Definition num_visible (cells : list item_cell) : nat :=
  list_sum ((λ c, if ic_deleted c then 0%nat else length (ic_run c)) <$> cells).

(* ----- isomorphism to a YjsArrInvariant model ---------------------------- *)

(** [cell_repr m c yi]: the heap cell [c] represents the SINGLE model item
    [yi], i.e. its run is the singleton [[yi]]. Every current creator mints
    such cells; multi-element cells relate to the model only through
    [cells_repr]'s flatten. ([m] is kept for signature uniformity with the
    call sites.) *)
Definition cell_repr (m : list (YjsItem A)) (c : item_cell) (yi : YjsItem A) : Prop :=
  ic_run c = [yi].

(** [cells_repr m cells items]: the heap cell list represents the model item
    list by flattening the runs (issue #28): [items = run_flatten cells]. *)
Definition cells_repr (m : list (YjsItem A)) (cells : list item_cell) (items : list (YjsItem A)) : Prop :=
  items = run_flatten cells.

(** [cells_of_locs_runs parent ls runs]: the cell list an address list and a
    run list determine under one type: the zip re-materializing cells from
    the run-granular state (the [own_ytype_runs] elimination,
    [own_ytype_runs_as_cells]). *)
Definition cells_of_locs_runs (parent : loc) (ls : list loc) (runs : list ItemRun) : list item_cell :=
  zip_with (λ lc r, MkItemCell lc (run_items r) (run_deleted r) parent) ls runs.

(** The heap effect of [item.flags |= itemDeleted]: set the Deleted bit. *)
Definition set_deleted (v : yjs.item.t) : yjs.item.t :=
  v <| yjs.item.flags' := w8_word_instance.(word.or) v.(yjs.item.flags') (W8 4) |>.

(** The cell with its [ic_deleted] bit set (its model run [ic_run] unchanged). *)
Definition flip_cell (c : item_cell) : item_cell :=
  MkItemCell (ic_loc c) (ic_run c) true (ic_parent c).

Definition toContent (c : yjs.content.t) : A := c.(yjs.content.content').

(** [cell_run c]: the pure half of a cell, its run as data ([ItemRun],
    docs/plan-item-run-split.md stage 1); [ic_loc] and [ic_parent] stay heap
    facts. The run-level definitions project along it (the [_runs] lemmas
    below and in [store/value_cells] / [store/value_split]). *)
Definition cell_run (c : item_cell) : ItemRun :=
  MkItemRun (ic_run c) (ic_deleted c).

(* ----- item-pointer helpers --------------------------------------------- *)

(** A heap item pointer is null or owns a node; [originId_of] is its model id. *)
Definition originId_of (ov : option yjs.item.t) : option YjsId :=
  (λ v, toYjsId v.(yjs.item.id')) <$> ov.

(* ===== lemmas ============================================================= *)

Lemma node_loc_loc_at (cells : list item_cell) (k : Z) :
  node_loc cells k = loc_at (ic_loc <$> cells) k.
Proof. by rewrite /node_loc /loc_at list_lookup_fmap. Qed.

(** Addresses across a splice of the address list: positions strictly before
    the splice keep their address; positions at/after shift by one. *)
Lemma loc_at_splice_lt (ls : list loc) (l : loc) (idx : nat) (k : Z) :
  (k < Z.of_nat idx)%Z -> (idx <= length ls)%nat ->
  loc_at (take idx ls ++ l :: drop idx ls) k = loc_at ls k.
Proof.
  move=> Hk Hle. rewrite /loc_at.
  case: (decide (0 <= k)%Z) => H0; [| done].
  rewrite lookup_app_l; last (rewrite length_take_le; [lia | exact Hle]).
  rewrite lookup_take_lt; [done | lia].
Qed.

Lemma loc_at_splice_ge (ls : list loc) (l : loc) (idx : nat) (k : Z) :
  (Z.of_nat idx <= k)%Z -> (idx <= length ls)%nat ->
  loc_at (take idx ls ++ l :: drop idx ls) (k + 1) = loc_at ls k.
Proof.
  move=> Hk Hle. rewrite /loc_at.
  rewrite decide_True; last lia. rewrite decide_True; last lia.
  rewrite lookup_app_r; last (rewrite length_take_le; [lia | exact Hle]).
  rewrite length_take_le; last exact Hle.
  have -> : (Z.to_nat (k + 1) - idx)%nat = S (Z.to_nat k - idx)%nat by lia.
  simpl. rewrite lookup_drop.
  have -> : (idx + (Z.to_nat k - idx))%nat = Z.to_nat k by lia.
  done.
Qed.

(** The cell-level run vocabulary says the same thing as the pure one under
    [cell_run]: head, flatten, visible count, tombstone flip, unit length. *)
Lemma cell_run_head (c : item_cell) : run_head_item (cell_run c) = run_head c.
Proof. reflexivity. Qed.

Lemma run_flatten_runs (cells : list item_cell) :
  run_flatten cells = runs_flatten (cell_run <$> cells).
Proof. rewrite /run_flatten /runs_flatten -list_fmap_compose. reflexivity. Qed.

Lemma num_visible_runs (cells : list item_cell) :
  num_visible cells = runs_visible (cell_run <$> cells).
Proof. rewrite /num_visible /runs_visible -list_fmap_compose. reflexivity. Qed.

Lemma cells_of_locs_runs_run (parent : loc) (ls : list loc) (runs : list ItemRun) :
  length ls = length runs ->
  cell_run <$> cells_of_locs_runs parent ls runs = runs.
Proof.
  rewrite /cells_of_locs_runs. revert runs.
  induction ls as [|lc ls IH] => runs Hlen.
  - destruct runs; [done | discriminate].
  - destruct runs as [|r runs]; [discriminate |].
    injection Hlen as Hlen.
    destruct r as [items del].
    cbn [zip_with]. rewrite fmap_cons.
    f_equal; try done. exact (IH runs Hlen).
Qed.

Lemma cells_of_locs_runs_loc (parent : loc) (ls : list loc) (runs : list ItemRun) :
  length ls = length runs ->
  ic_loc <$> cells_of_locs_runs parent ls runs = ls.
Proof.
  rewrite /cells_of_locs_runs. revert runs.
  induction ls as [|lc ls IH] => runs Hlen.
  - destruct runs; [done | discriminate].
  - destruct runs as [|r runs]; [discriminate |].
    injection Hlen as Hlen.
    cbn [zip_with]. rewrite fmap_cons.
    f_equal; try done. exact (IH runs Hlen).
Qed.

Lemma cells_of_locs_runs_projections (parent : loc) (cells : list item_cell) :
  (∀ c, c ∈ cells -> ic_parent c = parent) ->
  cells_of_locs_runs parent (ic_loc <$> cells) (cell_run <$> cells) = cells.
Proof.
  rewrite /cells_of_locs_runs.
  induction cells as [|c cells IH] => Hpar; [done |].
  have Hparc : ic_parent c = parent := Hpar c (list_elem_of_here _ _).
  have Hpar' : ∀ c0, c0 ∈ cells -> ic_parent c0 = parent
    := λ c0 Hc0, Hpar c0 (list_elem_of_further _ _ _ Hc0).
  rewrite !fmap_cons. cbn [zip_with].
  rewrite IH; [| exact Hpar'].
  destruct c. simpl in Hparc. rewrite Hparc //.
Qed.

Lemma cells_of_locs_runs_parent (parent : loc) (ls : list loc) (runs : list ItemRun) :
  ∀ c, c ∈ cells_of_locs_runs parent ls runs -> ic_parent c = parent.
Proof.
  rewrite /cells_of_locs_runs. revert runs.
  induction ls as [|lc ls IH] => runs c Hc.
  - by apply elem_of_nil in Hc.
  - destruct runs as [|r runs]; [by apply elem_of_nil in Hc |].
    cbn [zip_with] in Hc.
    apply elem_of_cons in Hc as [-> | Hc]; [done | exact (IH runs c Hc)].
Qed.

(** Materializing a run list with one slot tombstoned: the cell list with
    that slot's cell flipped. *)
Lemma cells_of_locs_runs_flip (parent : loc) (ls : list loc) (runs : list ItemRun)
    (k : nat) (lc : loc) (r : ItemRun) :
  ls !! k = Some lc ->
  runs !! k = Some r ->
  cells_of_locs_runs parent ls (<[k := flip_run r]> runs)
  = <[k := flip_cell (MkItemCell lc (run_items r) (run_deleted r) parent)]>
      (cells_of_locs_runs parent ls runs).
Proof.
  move=> Hlk Hrk. rewrite /cells_of_locs_runs.
  have Hkl : (k < length ls)%nat := lookup_lt_Some _ _ _ Hlk.
  have Hkr : (k < length runs)%nat := lookup_lt_Some _ _ _ Hrk.
  apply list_eq => i.
  destruct (decide (i = k)) as [-> | Hne].
  - rewrite list_lookup_insert_eq; last (rewrite length_zip_with; lia).
    rewrite lookup_zip_with Hlk list_lookup_insert_eq; last exact Hkr.
    rewrite /flip_cell /flip_run //=.
  - have Hne' : k ≠ i := λ H, Hne (eq_sym H).
    rewrite list_lookup_insert_ne; last exact Hne'.
    rewrite !lookup_zip_with list_lookup_insert_ne; last exact Hne'. done.
Qed.

(** Materializing a run list with one run spliced in at [idx]: the cell
    list with the matching cell spliced in. *)
Lemma cells_of_locs_runs_splice (parent : loc) (ls : list loc) (runs : list ItemRun)
    (idx : nat) (l : loc) (r : ItemRun) :
  length ls = length runs ->
  cells_of_locs_runs parent (take idx ls ++ l :: drop idx ls) (take idx runs ++ r :: drop idx runs)
  = take idx (cells_of_locs_runs parent ls runs)
    ++ MkItemCell l (run_items r) (run_deleted r) parent :: drop idx (cells_of_locs_runs parent ls runs).
Proof.
  move=> Hlen. rewrite /cells_of_locs_runs.
  rewrite zip_with_app; last by rewrite !length_take Hlen.
  rewrite -zip_with_take /=. rewrite -zip_with_drop. done.
Qed.

Lemma cell_run_flip (c : item_cell) :
  cell_run (flip_cell c) = flip_run (cell_run c).
Proof. reflexivity. Qed.

Lemma cell_unit_runs (c : item_cell) :
  cell_unit c ↔ length (run_items (cell_run c)) = 1%nat.
Proof. reflexivity. Qed.

Lemma run_flatten_nil : run_flatten [] = [].
Proof. done. Qed.

Lemma run_flatten_cons (c : item_cell) (cells : list item_cell) :
  run_flatten (c :: cells) = ic_run c ++ run_flatten cells.
Proof. done. Qed.

Lemma run_flatten_app (cs1 cs2 : list item_cell) :
  run_flatten (cs1 ++ cs2) = run_flatten cs1 ++ run_flatten cs2.
Proof. by rewrite /run_flatten fmap_app join_app. Qed.

Lemma run_flatten_singletons (cells : list item_cell) :
  Forall cell_unit cells →
  run_flatten cells = run_head <$> cells.
Proof.
  induction 1 as [|c cells Hc Hcells IH]; first done.
  rewrite run_flatten_cons IH fmap_cons /run_head.
  rewrite /cell_unit in Hc.
  destruct (ic_run c) as [|y [|y' r']]; simpl in Hc; [lia | done | lia].
Qed.

(* ----- cell-cursor prefix sums (issue #28 M4, stage C1c) ----------------- *)

(** Advancing the cell cursor by one appends that cell's whole run to the
    flattened prefix. The scan steps NODE by node while the model steps CHAR
    by char, so a cursor over cells couples to a [set_find_integration_loop] offset over
    chars via these prefix sums. *)
Lemma run_flatten_take_S (cells : list item_cell) (cur : nat) (ci : item_cell) :
  cells !! cur = Some ci ->
  run_flatten (take (S cur) cells) = run_flatten (take cur cells) ++ ic_run ci.
Proof.
  move=> Hcur.
  rewrite (take_S_r _ _ ci Hcur) run_flatten_app run_flatten_cons run_flatten_nil app_nil_r //.
Qed.

(** The chars of the cell at the cursor sit at consecutive model indices
    starting at the flattened-prefix length — [set_find_integration_block_step]'s [Hlook]
    premise, read off [cells_repr]'s [arr = run_flatten cells]. *)
Lemma run_flatten_take_lookup (cells : list item_cell) (cur : nat) (ci : item_cell)
    (k : nat) (y : YjsItem A) :
  cells !! cur = Some ci ->
  ic_run ci !! k = Some y ->
  run_flatten cells !! (length (run_flatten (take cur cells)) + k)%nat = Some y.
Proof.
  move=> Hcur Hk.
  have Hdec : run_flatten cells
            = run_flatten (take cur cells) ++ (ic_run ci ++ run_flatten (drop (S cur) cells)).
  { rewrite -{1}(take_drop_middle cells cur ci Hcur) run_flatten_app run_flatten_cons //. }
  rewrite Hdec lookup_app_r; last lia.
  have -> : (length (run_flatten (take cur cells)) + k
             - length (run_flatten (take cur cells)))%nat = k by lia.
  rewrite lookup_app_l; last (apply lookup_lt_Some in Hk; lia).
  exact Hk.
Qed.

(** Under the unit scaffold the cell cursor and the model offset coincide:
    each cell contributes exactly one char, so the flattened prefix length is
    the cursor (clamped to the cell count). *)
Lemma run_flatten_take_length_unit (cells : list item_cell) (cur : nat) :
  Forall cell_unit cells ->
  length (run_flatten (take cur cells)) = (cur `min` length cells)%nat.
Proof.
  move=> Hunit.
  have Hunit' : Forall cell_unit (take cur cells) := Forall_take _ _ _ Hunit.
  rewrite (run_flatten_singletons _ Hunit') length_fmap length_take //.
Qed.

(** Advancing the cursor past one more cell adds at least one char (the run is
    nonempty), so the flattened prefix length strictly grows. Foundation for the
    C2 boundary matching, where the cursor and the model offset no longer
    coincide but the prefix sum stays injective. *)
Lemma run_flatten_take_length_step (cells : list item_cell) (k : nat) :
  Forall (λ c, ic_run c ≠ []) cells ->
  (k < length cells)%nat ->
  (length (run_flatten (take k cells)) < length (run_flatten (take (S k) cells)))%nat.
Proof.
  move=> Hne Hk.
  destruct (lookup_lt_is_Some_2 cells k Hk) as [ci Hci].
  rewrite (run_flatten_take_S cells k ci Hci) length_app.
  have Hnn : ic_run ci ≠ [] := Forall_lookup_1 _ _ _ _ Hne Hci.
  destruct (ic_run ci) as [|y r]; [done | simpl; lia].
Qed.

(** Strict monotonicity of the flattened-prefix length in the cursor, given
    nonempty runs: the C2 counterpart of [run_flatten_take_length_unit] for
    matching run boundaries without the all-singleton scaffold. *)
Lemma run_flatten_take_length_lt (cells : list item_cell) (cur1 cur2 : nat) :
  Forall (λ c, ic_run c ≠ []) cells ->
  (cur1 < cur2)%nat -> (cur2 <= length cells)%nat ->
  (length (run_flatten (take cur1 cells)) < length (run_flatten (take cur2 cells)))%nat.
Proof.
  move=> Hne. move: cur1. induction cur2 as [|c2 IH]; move=> cur1 Hlt Hle; first lia.
  have Hstep : (length (run_flatten (take c2 cells)) < length (run_flatten (take (S c2) cells)))%nat
    := run_flatten_take_length_step cells c2 Hne ltac:(lia).
  destruct (decide (cur1 = c2)) as [-> | Hne2]; first lia.
  have := IH cur1 ltac:(lia) ltac:(lia). lia.
Qed.

(** Injectivity of the prefix sum on cursors within range: two cursors with the
    same flattened-prefix length are equal. Lets the [conflict == right] break
    (a cell-loc comparison) recover the model-index test at C2. *)
Lemma run_flatten_take_length_inj (cells : list item_cell) (cur1 cur2 : nat) :
  Forall (λ c, ic_run c ≠ []) cells ->
  (cur1 <= length cells)%nat -> (cur2 <= length cells)%nat ->
  length (run_flatten (take cur1 cells)) = length (run_flatten (take cur2 cells)) ->
  cur1 = cur2.
Proof.
  move=> Hne H1 H2 Heq.
  destruct (Nat.lt_trichotomy cur1 cur2) as [Hlt | [Heq' | Hgt]]; [| exact Heq' |].
  - have := run_flatten_take_length_lt cells cur1 cur2 Hne Hlt H2. lia.
  - have := run_flatten_take_length_lt cells cur2 cur1 Hne Hgt H1. lia.
Qed.

(** Read the promoted Deleted / Countable bits back off the [own_dll] flag pin
    ([flags'] = [if d then W8 6 else W8 2]): the struct is always Countable, and
    its Deleted bit is exactly [d]. Used by [findPos] / [Delete] after opening a
    node, to learn its visibility from the cell's [ic_deleted]. *)
Lemma flags_if_deleted (v : yjs.item.t) (d : bool) :
  v.(yjs.item.flags') = (if d then W8 6 else W8 2) -> is_deleted_flag v = d.
Proof. rewrite /is_deleted_flag => ->. by destruct d. Qed.

Lemma flags_if_countable (v : yjs.item.t) (d : bool) :
  v.(yjs.item.flags') = (if d then W8 6 else W8 2) -> is_countable_flag v = true.
Proof. rewrite /is_countable_flag => ->. by destruct d. Qed.

(** A [cell_repr] cell is a unit cell. *)
Lemma cell_repr_unit m c yi : cell_repr m c yi -> cell_unit c.
Proof. rewrite /cell_repr /cell_unit => -> //. Qed.

Lemma cell_repr_head m c yi : cell_repr m c yi -> run_head c = yi.
Proof. rewrite /cell_repr /run_head => -> //. Qed.

(** Under the all-singleton invariant the isomorphism is length-preserving and
    cellwise (the pre-#28 1:1 correspondence). *)
Lemma cells_repr_length m cells items :
  Forall cell_unit cells ->
  cells_repr m cells items -> length cells = length items.
Proof.
  rewrite /cells_repr => Hunit ->.
  by rewrite (run_flatten_singletons cells Hunit) length_fmap.
Qed.

Lemma cells_repr_lookup m cells items k c :
  Forall cell_unit cells ->
  cells_repr m cells items -> cells !! k = Some c ->
  ∃ yi, items !! k = Some yi ∧ cell_repr m c yi.
Proof.
  rewrite /cells_repr /cell_repr => Hunit -> Hk. exists (run_head c).
  rewrite (run_flatten_singletons cells Hunit) list_lookup_fmap Hk /=.
  split; first done.
  have Hu : cell_unit c := Forall_lookup_1 _ _ _ _ Hunit Hk.
  rewrite /cell_unit in Hu. rewrite /run_head.
  destruct (ic_run c) as [|y [|y' r']]; simpl in Hu; [lia | done | lia].
Qed.

(** Inserting a corresponding cell/item at the same position preserves the
    isomorphism (the splice's model side); position alignment needs the
    all-singleton invariant. *)
Lemma cells_repr_insert m cells items (k : nat) c yi :
  Forall cell_unit cells ->
  cells_repr m cells items -> cell_repr m c yi ->
  cells_repr m (take k cells ++ c :: drop k cells) (take k items ++ yi :: drop k items).
Proof.
  rewrite /cells_repr /cell_repr => Hunit -> Hc.
  rewrite run_flatten_app run_flatten_cons Hc.
  rewrite (run_flatten_singletons _ (Forall_take _ _ _ Hunit)).
  rewrite (run_flatten_singletons _ (Forall_drop _ _ _ Hunit)).
  by rewrite (run_flatten_singletons cells Hunit) fmap_take fmap_drop.
Qed.

(** [cells_repr] does not depend on the resolution context [m] (it is a plain
    fmap equality), so threading a fresh model is a no-op. *)
Lemma cells_repr_m_irrel (m m' : list (YjsItem A)) cells items :
  cells_repr m cells items -> cells_repr m' cells items.
Proof. by rewrite /cells_repr. Qed.

Lemma cells_repr_app (m : list (YjsItem A)) cs1 cs2 ys1 ys2 :
  cells_repr m cs1 ys1 -> cells_repr m cs2 ys2 -> cells_repr m (cs1 ++ cs2) (ys1 ++ ys2).
Proof. rewrite /cells_repr => -> ->. by rewrite run_flatten_app. Qed.

Lemma cells_repr_take (m : list (YjsItem A)) cells items k :
  Forall cell_unit cells ->
  cells_repr m cells items -> cells_repr m (take k cells) (take k items).
Proof.
  rewrite /cells_repr => Hunit ->.
  rewrite (run_flatten_singletons _ (Forall_take _ _ _ Hunit)).
  by rewrite (run_flatten_singletons cells Hunit) fmap_take.
Qed.

Lemma cells_repr_drop (m : list (YjsItem A)) cells items k :
  Forall cell_unit cells ->
  cells_repr m cells items -> cells_repr m (drop k cells) (drop k items).
Proof.
  rewrite /cells_repr => Hunit ->.
  rewrite (run_flatten_singletons _ (Forall_drop _ _ _ Hunit)).
  by rewrite (run_flatten_singletons cells Hunit) fmap_drop.
Qed.

(** Replacing a cell with one carrying the SAME run preserves the isomorphism
    (the flatten never reads [ic_deleted] / [ic_loc]). [Text.Delete] flips a
    cell's [ic_deleted] without touching its [ic_run]. *)
Lemma cells_repr_update_run m cells items (k : nat) c c' :
  cells !! k = Some c -> ic_run c' = ic_run c ->
  cells_repr m cells items -> cells_repr m (<[k := c']> cells) items.
Proof.
  rewrite /cells_repr => Hck Hrun ->.
  rewrite /run_flatten list_fmap_insert Hrun. f_equal. symmetry.
  apply list_insert_id. rewrite list_lookup_fmap Hck //.
Qed.

(* ----- the deletion layer: tombstoning a cell ---------------------------- *)

(** Visible count is additive over append. *)
Lemma num_visible_app (l1 l2 : list item_cell) :
  num_visible (l1 ++ l2) = (num_visible l1 + num_visible l2)%nat.
Proof. rewrite /num_visible fmap_app list_sum_app //. Qed.

(** Inserting a *visible* unit cell increments the visible count. Read by
    [Store.Integrate] / [Text.Insert], whose new items are always visible
    1-char runs. *)
Lemma num_visible_insert_visible (cells : list item_cell) (k : nat) (c : item_cell) :
  ic_deleted c = false -> cell_unit c ->
  num_visible (take k cells ++ c :: drop k cells) = S (num_visible cells).
Proof.
  rewrite /cell_unit => Hc Hu. rewrite /num_visible.
  rewrite fmap_app fmap_cons list_sum_app /=. rewrite Hc Hu.
  rewrite -[in S (list_sum _)](take_drop k cells) fmap_app list_sum_app. lia.
Qed.

(** [set_deleted] forces flags to [W8 6] (Countable + Deleted) regardless of the
    prior Deleted bit ([W8 2] or [W8 6] both [or] to [W8 6]). *)
Lemma set_deleted_flags (v : yjs.item.t) (d : bool) :
  v.(yjs.item.flags') = (if d then W8 6 else W8 2) ->
  (set_deleted v).(yjs.item.flags') = W8 6.
Proof. rewrite /set_deleted /= => ->. by destruct d. Qed.

(** Flipping a cell's Deleted bit preserves [cell_repr]: [ic_run] is untouched. *)
Lemma cell_repr_flip (m : list (YjsItem A)) (c : item_cell) (yi : YjsItem A) :
  cell_repr m c yi -> cell_repr m (flip_cell c) yi.
Proof. rewrite /cell_repr /flip_cell /=. tauto. Qed.

(** Tombstoning a visible unit cell drops the visible count by one. *)
Lemma num_visible_flip (cells : list item_cell) (k : nat) (c : item_cell) :
  cells !! k = Some c -> ic_deleted c = false -> cell_unit c ->
  num_visible (<[k := flip_cell c]> cells) = pred (num_visible cells).
Proof.
  rewrite /cell_unit => Hk Hd Hu.
  have Hins : <[k := flip_cell c]> cells = take k cells ++ flip_cell c :: drop (S k) cells
    by (apply insert_take_drop; apply lookup_lt_Some in Hk; exact Hk).
  rewrite Hins /num_visible fmap_app fmap_cons list_sum_app /flip_cell /=.
  rewrite -[in pred (list_sum _)](take_drop_middle cells k c Hk).
  rewrite fmap_app fmap_cons list_sum_app /=. rewrite Hd Hu. lia.
Qed.

(* ----- run-aware generalizations (issue #28 part 6) ----------------------- *)

(** Tombstoning a visible cell drops the visible count by its run length: the
    general form of [num_visible_flip]. *)
Lemma num_visible_flip_run (cells : list item_cell) (k : nat) (c : item_cell) :
  cells !! k = Some c -> ic_deleted c = false ->
  num_visible (<[k := flip_cell c]> cells) = (num_visible cells - length (ic_run c))%nat.
Proof.
  move=> Hk Hd.
  have Hins : <[k := flip_cell c]> cells = take k cells ++ flip_cell c :: drop (S k) cells
    by (apply insert_take_drop; apply lookup_lt_Some in Hk; exact Hk).
  rewrite Hins /num_visible fmap_app fmap_cons list_sum_app /flip_cell /=.
  rewrite -[in X in _ = (X - _)%nat](take_drop_middle cells k c Hk).
  rewrite fmap_app fmap_cons list_sum_app /=. rewrite Hd. lia.
Qed.



(* ===== lemmas ============================================================= *)

(** A cell's head model item is in the flatten (nonempty run via the unit
    invariant; issue #28). *)
Lemma run_head_in_flatten (cells : list item_cell) (c : item_cell) :
  c ∈ cells -> cell_unit c -> run_head c ∈ run_flatten cells.
Proof.
  intros Hc Hu. rewrite /cell_unit in Hu.
  apply list_elem_of_join. exists (ic_run c).
  split; last (apply list_elem_of_fmap_2; exact Hc).
  rewrite /run_head. destruct (ic_run c) as [|y [|y' r']]; simpl in Hu; [lia | | lia].
  simpl. apply list_elem_of_singleton. reflexivity.
Qed.


(** The all-singleton invariant survives a cell splice (issue #28, M1). *)
Lemma Forall_cell_unit_splice (cells : list item_cell) (k : nat) (c : item_cell) :
  Forall cell_unit cells -> cell_unit c ->
  Forall cell_unit (take k cells ++ c :: drop k cells).
Proof.
  intros H Hc. apply Forall_app_2; [by apply Forall_take |].
  constructor; [exact Hc | by apply Forall_drop].
Qed.

(** Converse: the [off]-th char of cell [ci] sits at prefix-sum + [off]. *)
Lemma run_flatten_lookup_of_cell (cells : list item_cell) (ci off : nat)
    (c : item_cell) (it : YjsItem A) :
  cells !! ci = Some c -> ic_run c !! off = Some it ->
  run_flatten cells !! (length (run_flatten (take ci cells)) + off)%nat = Some it.
Proof.
  move=> Hci Hoff.
  have Hsplit := take_drop_middle cells ci c Hci.
  have Hdec : run_flatten cells
            = run_flatten (take ci cells) ++ ic_run c ++ run_flatten (drop (S ci) cells).
  { transitivity (run_flatten (take ci cells ++ c :: drop (S ci) cells)).
    - by rewrite Hsplit.
    - by rewrite run_flatten_app run_flatten_cons. }
  rewrite Hdec lookup_app_r; last lia.
  replace (length (run_flatten (take ci cells)) + off -
           length (run_flatten (take ci cells)))%nat with off by lia.
  rewrite lookup_app_l; [exact Hoff | by apply lookup_lt_Some in Hoff].
Qed.

End item_value.
