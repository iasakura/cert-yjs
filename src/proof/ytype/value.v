(** The [yType] container, VALUE layer: what a type's runs denote as a
    sequence. Go values but no Iris.

    Definitions
    - [visible_items] / [visible_string]: the non-tombstoned items of a
      sequence [list (YjsItem A * bool)] (each document item paired with its
      tombstone bit) and the string they spell, the read API's snapshot
      content (issue #125).
    - [visible_excludes deleted_ids m]: none of the ids a reader knows
      deleted is among [m]'s visible chars ([visible_excludes_of_bits] reads
      it off the tombstone bits), the delete-side guarantee of a read.
    - [find_pos]: what [yType.findPos] resolves an index to (the cursor
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
    - [visible_string_take_S]: one more run appends its string when live
      and nothing when tombstoned, the step [Text.CodeUnits] walks.
    - [snapshot_char] / [snapshot_chars]: the [SnapshotChar] values a read
      reports for a snapshot's characters ([Text.Snapshot], issue #239),
      with the steps its walks take ([snapshot_chars_take_S], one more run;
      [run_models_take_S] and [snapshot_char_run], one more character of a
      run: the head id advanced by the offset and the unit at it). *)
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

Notation A := (list w16).

(* ===== definitions ======================================================== *)

(* ----- the abstract sequence a type denotes ------------------------------ *)

(** The visible (non-tombstoned) items of an abstract sequence, and the string
    they spell (the concatenation of their per-char contents): what the read
    API ([Text.Len] / [Text.CodeUnits]) exposes about a snapshot (issue #125).
    The bound a read hands back is at the ITEM level ([m.*1] contains a set);
    a tombstoned item is in [m.*1] but not in [visible_items m].
    [items_string] is [item/model.v]'s. *)
Definition visible_items (m : list (YjsItem A * bool)) : list (YjsItem A) :=
  (filter (λ p, p.2 = false) m).*1.

Definition visible_string (m : list (YjsItem A * bool)) : A :=
  items_string (visible_items m).

(** [snapshot_char p]: the [SnapshotChar] value a read reports for one
    tombstone-tagged char of a snapshot ([Text.Snapshot], issue #239): its
    item's id as the heap holds it, its tag, and its one code unit (a char's
    content is a one-unit list, [run_per_char]; the empty case cannot occur
    and reads as 0). *)
Definition snapshot_char (p : YjsItem A * bool) : yjs.SnapshotChar.t :=
  yjs.SnapshotChar.mk (W64 (Z.of_nat (clientId (item_id p.1))))
                      (W64 (Z.of_nat (clock (item_id p.1))))
                      p.2
                      (default (W16 0) (content p.1 !! 0%nat)).

(** The slice [Text.Snapshot] returns for a snapshot. *)
Definition snapshot_chars (m : list (YjsItem A * bool)) : list yjs.SnapshotChar.t :=
  snapshot_char <$> m.

(** [visible_excludes deleted_ids m]: none of the ids the reader knows deleted
    is among the snapshot's visible chars, so [visible_string m] does not
    spell them. What a read adds for a handle that has deleted: the ids its
    [is_delete_set_lb] certificate names are gone from what the read
    returns. *)
Definition visible_excludes (deleted_ids : gset YjsId) (m : list (YjsItem A * bool)) : Prop :=
  ∀ x, x ∈ visible_items m -> item_id x ∉ deleted_ids.

(** [find_pos ls runs p leftNode rightNode off]: what [yType.findPos] resolves a
    visible index to,: the cursor [p] into the run list,
    the node addresses around it read off the address list [ls], and the
    offset inside the run before the cursor. *)
Definition find_pos (ls : list loc) (runs : list ItemRun)
    (p : nat) (leftNode rightNode : loc) (off : w64) : Prop :=
  (p <= length runs)%nat ∧
  leftNode = loc_at ls (Z.of_nat p - 1) ∧
  rightNode = loc_at ls (Z.of_nat p) ∧
  (off = W64 0 ∨
   (0 < uint.Z off)%Z ∧ (1 <= p)%nat ∧
   (∃ r, runs !! (p - 1)%nat = Some r ∧ run_deleted r = false ∧
         (uint.nat off < length (run_items r))%nat)).

(** Read [visible_excludes] off the tombstone bits: a char whose id the reader
    knows deleted carries the bit, so the visible filter drops it. *)
Lemma visible_excludes_of_bits (deleted_ids : gset YjsId) (m : list (YjsItem A * bool)) :
  (∀ x b, (x, b) ∈ m -> item_id x ∈ deleted_ids -> b = true) ->
  visible_excludes deleted_ids m.
Proof.
  move=> Hbits x Hx Hid.
  rewrite /visible_items in Hx.
  apply list_elem_of_fmap in Hx as ([y b] & Heq & Hmem). simpl in Heq. subst y.
  apply list_elem_of_filter in Hmem as [Hb Hmem]. simpl in Hb.
  have Hb' := Hbits x b Hmem Hid. congruence.
Qed.

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
    tombstoned: the step [yType.Text]'s walk takes, with [s] the node's
    content, its code units (tied to the run by [own_item_node]'s content
    pin). *)
Lemma visible_string_run_models (r : ItemRun) (s : A) :
  content <$> run_items r = explode s ->
  visible_string (run_models r) = (if run_deleted r then [] else s).
Proof.
  move=> Hc. rewrite /visible_string visible_items_run_models.
  destruct (run_deleted r); [done | exact (items_string_explode _ s Hc)].
Qed.

Lemma snapshot_chars_app (m1 m2 : list (YjsItem A * bool)) :
  snapshot_chars (m1 ++ m2) = snapshot_chars m1 ++ snapshot_chars m2.
Proof. rewrite /snapshot_chars fmap_app //. Qed.

(** One more run contributes its chars: the step [yType.Snapshot]'s outer
    walk takes. *)
Lemma snapshot_chars_take_S (runs : list ItemRun) (k : nat) (r : ItemRun) :
  runs !! k = Some r ->
  snapshot_chars (runs_model (take (S k) runs))
  = snapshot_chars (runs_model (take k runs)) ++ snapshot_chars (run_models r).
Proof.
  move=> Hk.
  rewrite (take_S_r _ _ r Hk) runs_model_app runs_model_singleton snapshot_chars_app //.
Qed.

(** One more char of a run: the step [yType.Snapshot]'s inner walk takes. *)
Lemma run_models_take_S (r : ItemRun) (j : nat) (x : YjsItem A) :
  run_items r !! j = Some x ->
  take (S j) (run_models r) = take j (run_models r) ++ [(x, run_deleted r)].
Proof.
  move=> Hx. rewrite /run_models.
  apply (take_S_r _ _ (x, run_deleted r)).
  rewrite list_lookup_fmap Hx //.
Qed.

(** The [j]-th char of a run, as a read reports it: the run's head id with
    the clock advanced by [j] ([run_wf]), the run's tag, and the [j]-th unit
    of the string the run spells ([run_per_char]). *)
Lemma snapshot_char_run (r : ItemRun) (j : nat) (x : YjsItem A) (u : w16) :
  run_wf (run_items r) -> run_per_char r ->
  run_items r !! j = Some x ->
  items_string (run_items r) !! j = Some u ->
  snapshot_char (x, run_deleted r)
  = yjs.SnapshotChar.mk (W64 (Z.of_nat (run_client r)))
      (word.add (W64 (Z.of_nat (run_clock r))) (W64 (Z.of_nat j)))
      (run_deleted r) u.
Proof.
  move=> Hwf Hpc Hx Hu.
  have Hhd : run_items r !! 0%nat = Some (run_head_item r).
  { rewrite /run_head_item. destruct (run_items r) as [| y l]; [by destruct Hwf | done]. }
  have Hid := run_wf_lookup_clock (run_items r) j (run_head_item r) x Hwf Hhd Hx.
  have Hcontent : content x = [u].
  { have Hfm : (content <$> run_items r) !! j = Some (content x) by rewrite list_lookup_fmap Hx.
    rewrite Hpc /explode list_lookup_fmap Hu in Hfm. by injection Hfm. }
  rewrite /snapshot_char /= Hid Hcontent /run_client /run_clock /=.
  f_equal. word.
Qed.

Lemma visible_string_take_S (runs : list ItemRun) (k : nat) (r : ItemRun)
    (s : A) :
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
