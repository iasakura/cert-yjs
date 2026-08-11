(** The [yType] container, VALUE layer: what a cell list denotes as a sequence.
    Go values but no Iris.

    Definitions
    - [cell_models] / [cells_model]: a cell list read as the abstract sequence
      [list (YjsItem A * bool)], each document item paired with its tombstone
      bit.
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
      items. *)
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

    [items_string] is a bespoke [foldr], NOT [mjoin (content <$> ...)]: using
    [content] as [fmap]'s function argument together with [mjoin] entangles
    rocq-yjs's [YjsPtr.u0] universe with stdpp's monad-class universes, and in
    any file that also loads Perennial's [New.ghost] universal-[own] syntax
    codes that chain contradicts [syntax.cmra]'s universe bound (the [IsCmra]
    instances for [gset (YjsItem A)] then fail with "no instance found"). The
    fully-applied [content x] avoids the entanglement. *)
Definition visible_items (m : list (YjsItem A * bool)) : list (YjsItem A) :=
  (filter (λ p, p.2 = false) m).*1.

Definition items_string (l : list (YjsItem A)) : A :=
  foldr (λ x acc, content x ++ acc) [] l.

Definition visible_string (m : list (YjsItem A * bool)) : A :=
  items_string (visible_items m).

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

Lemma items_string_app (l1 l2 : list (YjsItem A)) :
  items_string (l1 ++ l2) = items_string l1 ++ items_string l2.
Proof.
  induction l1 as [|x l1 IH]; first done.
  rewrite /items_string /= -/(items_string (l1 ++ l2)) -/(items_string l1)
    IH app_assoc //.
Qed.

Lemma visible_string_app (m1 m2 : list (YjsItem A * bool)) :
  visible_string (m1 ++ m2) = visible_string m1 ++ visible_string m2.
Proof. rewrite /visible_string visible_items_app items_string_app //. Qed.

(** A run whose per-char contents explode a heap content string spells exactly
    that string (the [own_dll] node fact, consumed by the [yType.Text] walk). *)
Lemma items_string_explode (r : list (YjsItem A)) (s : go_string) :
  content <$> r = explode s -> items_string r = s.
Proof.
  revert s. induction r as [|x r IH] => s Hc.
  - destruct s; [done | discriminate].
  - destruct s as [|b s']; first discriminate.
    injection Hc as Hx Hr.
    rewrite /items_string /= -/(items_string r) (IH s' Hr) Hx //.
Qed.

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

End ytype_value.
