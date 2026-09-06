(** The [yType] container, VALUE layer: what a type's runs denote as a
    sequence. Go values but no Iris.

    Definitions
    - [visible_items] / [visible_string]: the non-tombstoned items of a
      sequence [list (YjsItem A * bool)] (each document item paired with its
      tombstone bit) and the string they spell, the read API's snapshot
      content (issue #125).
    - [find_pos_runs]: what [yType.findPos] resolves an index to (the cursor
      into the run list, the node addresses off the address list, the offset
      inside the run before the cursor).

    Laws
    - [visible_items] / [visible_string] are append homomorphisms; one run
      contributes its items when live and nothing when tombstoned
      ([visible_items_run_models] / [visible_string_run_models]).
    - [runs_model_fst]: the sequence's first projection is the document list
      [runs_flatten], so the public model and this one differ only by the
      tombstone bits; [runs_visible_model], the [len] counter counts the
      sequence's visible items.
    - [visible_string_runs_take_S]: one more run appends its string when live
      and nothing when tombstoned, the step [Text.String] walks. *)
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

(* ----- the abstract sequence a type denotes ------------------------------ *)

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

Lemma visible_items_app (m1 m2 : list (YjsItem A * bool)) :
  visible_items (m1 ++ m2) = visible_items m1 ++ visible_items m2.
Proof. rewrite /visible_items filter_app fmap_app //. Qed.

Lemma visible_string_app (m1 m2 : list (YjsItem A * bool)) :
  visible_string (m1 ++ m2) = visible_string m1 ++ visible_string m2.
Proof. rewrite /visible_string visible_items_app items_string_app //. Qed.

(** The run model's items are the runs' flatten, and its visible items are
    counted by [runs_visible]: what the read API reports off a type's run
    view. *)
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

(** One more run contributes its string when live and nothing when
    tombstoned: the step [yType.Text]'s walk takes, with [s] the node's heap
    content string (tied to the run by [own_item_node]'s content pin). *)
Lemma visible_string_run_models (r : ItemRun) (s : go_string) :
  content <$> run_items r = explode s ->
  visible_string (run_models r) = (if run_deleted r then [] else s).
Proof.
  move=> Hc. rewrite /visible_string visible_items_run_models.
  destruct (run_deleted r); [done | exact (items_string_explode _ s Hc)].
Qed.

Lemma visible_string_runs_take_S (runs : list ItemRun) (k : nat) (r : ItemRun)
    (s : go_string) :
  runs !! k = Some r ->
  content <$> run_items r = explode s ->
  visible_string (runs_model (take (S k) runs))
  = visible_string (runs_model (take k runs))
    ++ (if run_deleted r then [] else s).
Proof.
  move=> Hk Hc.
  rewrite (take_S_r _ _ r Hk) runs_model_app visible_string_app runs_model_singleton.
  f_equal. exact (visible_string_run_models r s Hc).
Qed.

End ytype_value.
