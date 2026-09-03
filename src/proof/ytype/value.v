(** The [yType] container, VALUE layer: what a cell list denotes as a sequence.
    Go values but no Iris.

    Definitions
    - [cell_models] / [cells_model]: a cell list read as the abstract sequence
      [list (YjsItem A * bool)], each document item paired with its tombstone
      bit.
    - [find_pos_runs]: what [yType.findPos] resolves an index to, at run
      granularity (the cursor into the run list, the node addresses off the
      address list).
    - [visible_items] / [visible_string]: the non-tombstoned items of such a
      sequence and the string they spell, the read API's snapshot content
      (issue #125).

    Laws
    - [cells_model_fst]: its first projection is the document list
      [run_flatten], so the public model and the cells-level model agree on
      content and differ only by the tombstone bits.
    - [cells_model] / [visible_items] / [visible_string] are append
      homomorphisms; one cell contributes its run when live and nothing when
      tombstoned ([visible_items_cell_models], [visible_string_take_S]).
    - [num_visible_model]: the heap [len] counter counts the model's visible
      items.
    - [cells_model_runs]: the cells-level model is the run-level one under
      [cell_run]; [runs_model_fst] / [runs_visible_model], the run model's
      items and visible count. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core prelude.
From stdpp Require Import sorting.
From New.proof.ytype Require Import model.
From New.proof.id Require Import value heap.
From New.proof.item Require Import run_theory model value heap.

Section ytype_value.

Set Default Proof Using "Type*".

Notation A := go_string.

(* ===== definitions ======================================================== *)

(* ----- the abstract model and the public predicate ----------------------- *)

(** The abstract per-char cells a heap cell denotes: each model item of its run
    paired with the cell's tombstone bit. The heap location is dropped — this
    is the abstraction wall (the model stays per-char; runs are invisible,
    issue #28). *)
Definition cell_models (c : item_cell) : list (YjsItem A * bool) :=
  (λ x, (x, ic_deleted c)) <$> ic_run c.

Definition cells_model (cells : list item_cell) : list (YjsItem A * bool) :=
  mjoin (cell_models <$> cells).

(** The visible (non-tombstoned) items of an abstract sequence, and the string
    they spell (the concatenation of their per-char contents): what the read
    API ([Text.Len] / [Text.String]) exposes about a snapshot (issue #125).
    The bound a read hands back is at the ITEM level ([m.*1] contains a set);
    a tombstoned item is in [m.*1] but not in [visible_items m].
    [items_string] is [item/model.v]'s. *)
Definition visible_items (m : list (YjsItem A * bool)) : list (YjsItem A) :=
  (filter (λ p, p.2 = false) m).*1.

Definition visible_string (m : list (YjsItem A * bool)) : A :=
  items_string (visible_items m).

(** [find_pos_runs ls runs p lft rgt off]: what [yType.findPos] resolves a
    visible index to, at run granularity: the cursor [p] into the run list,
    the node addresses around it read off the address list [ls], and the
    offset inside the run before the cursor. *)
Definition find_pos_runs (ls : list loc) (runs : list ItemRun)
    (p : nat) (lft rgt : loc) (off : w64) : Prop :=
  (p <= length runs)%nat ∧
  lft = loc_at ls (Z.of_nat p - 1) ∧
  rgt = loc_at ls (Z.of_nat p) ∧
  (off = W64 0 ∨
   (0 < uint.Z off)%Z ∧ (1 <= p)%nat ∧
   (∃ r, runs !! (p - 1)%nat = Some r ∧ run_deleted r = false ∧
         (uint.nat off < length (run_items r))%nat)).

(* ===== lemmas ============================================================= *)

Lemma fmap_pair_fst (d : bool) (r : list (YjsItem A)) :
  ((λ x : YjsItem A, (x, d)) <$> r).*1 = r.
Proof. induction r as [|x r IH]; [done | by rewrite !fmap_cons IH]. Qed.

Lemma cells_model_fst (cells : list item_cell) :
  (cells_model cells).*1 = run_flatten cells.
Proof.
  induction cells as [|c cs IH]; first done.
  rewrite /cells_model /run_flatten /= fmap_app IH /cell_models fmap_pair_fst //.
Qed.

Lemma cells_model_app (cs1 cs2 : list item_cell) :
  cells_model (cs1 ++ cs2) = cells_model cs1 ++ cells_model cs2.
Proof. rewrite /cells_model fmap_app join_app //. Qed.

Lemma visible_items_app (m1 m2 : list (YjsItem A * bool)) :
  visible_items (m1 ++ m2) = visible_items m1 ++ visible_items m2.
Proof. rewrite /visible_items filter_app fmap_app //. Qed.

Lemma visible_string_app (m1 m2 : list (YjsItem A * bool)) :
  visible_string (m1 ++ m2) = visible_string m1 ++ visible_string m2.
Proof. rewrite /visible_string visible_items_app items_string_app //. Qed.

(** One cell's visible items: its whole run when live, nothing when
    tombstoned. *)
Lemma visible_items_cell_models (c : item_cell) :
  visible_items (cell_models c) = if ic_deleted c then [] else ic_run c.
Proof.
  rewrite /visible_items /cell_models.
  induction (ic_run c) as [|x r IH].
  - destruct (ic_deleted c); done.
  - rewrite fmap_cons. destruct (ic_deleted c) eqn:Hd.
    + rewrite filter_cons_False; [exact IH | done].
    + rewrite filter_cons_True; [| done].
      rewrite fmap_cons IH //.
Qed.

(** The visible length of the model is the heap [len] counter's value. *)
Lemma num_visible_model (cells : list item_cell) :
  num_visible cells = length (visible_items (cells_model cells)).
Proof.
  induction cells as [|c cs IH]; first done.
  have -> : cells_model (c :: cs) = cell_models c ++ cells_model cs by done.
  rewrite visible_items_app length_app /num_visible fmap_cons /= -/(num_visible cs) IH.
  f_equal. rewrite visible_items_cell_models.
  destruct (ic_deleted c); done.
Qed.

(** The walk step of [yType.Text]: extending a snapshot prefix by one cell
    appends that cell's visible content ([s] is the cell's heap content
    string, tied to the run by the [own_dll] node fact). *)
Lemma visible_string_take_S (cells : list item_cell) (k : nat) (c : item_cell)
    (s : go_string) :
  cells !! k = Some c ->
  content <$> ic_run c = explode s ->
  visible_string (cells_model (take (S k) cells))
  = visible_string (cells_model (take k cells))
    ++ (if ic_deleted c then [] else s).
Proof.
  move=> Hk Hc.
  rewrite (take_S_r cells k c Hk) cells_model_app visible_string_app. f_equal.
  have -> : cells_model [c] = cell_models c ++ [] by done.
  rewrite app_nil_r /visible_string visible_items_cell_models.
  destruct (ic_deleted c); [done | exact (items_string_explode _ _ Hc)].
Qed.

(** The cells-level model and cursor say the same thing as the run-level ones
    under the cells' projections (docs/plan-item-run-split.md: the loc-free
    model is [runs_model], the addresses live in the [ls] list). *)
Lemma cells_model_runs (cells : list item_cell) :
  cells_model cells = runs_model (cell_run <$> cells).
Proof.
  rewrite /cells_model /runs_model -list_fmap_compose.
  f_equal.
Qed.

(** The run model's items are the runs' flatten, and its visible items are
    counted by [runs_visible]: the run forms of [cells_model_fst] /
    [num_visible_model], what the read API reports off a type's run view. *)
Lemma runs_model_fst (runs : list ItemRun) : (runs_model runs).*1 = runs_flatten runs.
Proof.
  induction runs as [|r rs IH]; first done.
  have -> : runs_model (r :: rs) = run_models r ++ runs_model rs by done.
  have -> : runs_flatten (r :: rs) = run_items r ++ runs_flatten rs by done.
  rewrite fmap_app IH. f_equal.
  rewrite /run_models -list_fmap_compose -{2}(list_fmap_id (run_items r)).
  apply list_fmap_ext. move=> i x _. reflexivity.
Qed.

Lemma visible_items_run_models (r : ItemRun) :
  visible_items (run_models r) = if run_deleted r then [] else run_items r.
Proof.
  rewrite /visible_items /run_models.
  induction (run_items r) as [|x l IH].
  - destruct (run_deleted r); done.
  - rewrite fmap_cons. destruct (run_deleted r) eqn:Hd.
    + rewrite filter_cons_False; [exact IH | done].
    + rewrite filter_cons_True; [| done].
      rewrite fmap_cons IH //.
Qed.

Lemma runs_visible_model (runs : list ItemRun) :
  runs_visible runs = length (visible_items (runs_model runs)).
Proof.
  induction runs as [|r rs IH]; first done.
  have -> : runs_model (r :: rs) = run_models r ++ runs_model rs by done.
  rewrite visible_items_app length_app runs_visible_cons IH. f_equal.
  rewrite visible_items_run_models. destruct (run_deleted r); done.
Qed.

(** The run form of [visible_string_take_S]: one more run contributes its
    string when live and nothing when tombstoned. Proved by materializing a
    cell list over dummy addresses, which the cells-level lemma then walks. *)
Lemma visible_string_runs_take_S (runs : list ItemRun) (k : nat) (r : ItemRun)
    (s : go_string) :
  runs !! k = Some r ->
  content <$> run_items r = explode s ->
  visible_string (runs_model (take (S k) runs))
  = visible_string (runs_model (take k runs))
    ++ (if run_deleted r then [] else s).
Proof.
  move=> Hk Hc.
  set (ls := replicate (length runs) null).
  have Hlenls : length ls = length runs by rewrite /ls length_replicate.
  set (cells := cells_of_locs_runs null ls runs).
  have Hcr : cell_run <$> cells = runs := cells_of_locs_runs_run null ls runs Hlenls.
  have Hlencells : length cells = length runs by rewrite -Hcr length_fmap.
  destruct (cells !! k) as [c|] eqn:Hck; last first.
  { exfalso. apply lookup_ge_None in Hck. apply lookup_lt_Some in Hk. lia. }
  have Hcrk : cell_run c = r.
  { have Hlk : (cell_run <$> cells) !! k = runs !! k by rewrite Hcr.
    rewrite list_lookup_fmap Hck /= Hk in Hlk. by injection Hlk. }
  have Hmodel : ∀ j, runs_model (take j runs) = cells_model (take j cells).
  { move=> j. rewrite cells_model_runs.
    have -> : cell_run <$> take j cells = take j runs by rewrite fmap_take Hcr.
    reflexivity. }
  rewrite !Hmodel.
  have Hdel : run_deleted r = ic_deleted c by rewrite -Hcrk.
  rewrite Hdel.
  apply (visible_string_take_S cells k c s Hck).
  have Hrun : ic_run c = run_items r by rewrite -Hcrk.
  rewrite Hrun. exact Hc.
Qed.

End ytype_value.
