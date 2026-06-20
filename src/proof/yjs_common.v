(** Common definitions shared across the cert-yjs proof modules.

    Split out of the original single-file invariant development so the
    per-module proof files ([yjs_dll], [yjs_invariant], [yjs_proof],
    [yjs_store], [yjs_text]) can share one base layer:

    - scalar abstractions [toYjsId] / [toContent] (heap [w64] ids/content to
      the model);
    - the heap-node record [item_cell] and the cursor helper [node_loc];
    - the persistent origin-pointer predicate [is_origin_id];
    - the item-pointer helpers [oid_of] / [item_or_null];
    - small [gset YjsId] rewrite lemmas used by the conflict scan.

    None of these depend on the DLL spine or the heap<->model isomorphism, so
    every other module imports this one. The goose package-init instances live
    here too (declared once and inherited via [Require]). *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import yjs_core.

(** Small-context set rewrites for the scan accumulators. After a Go [append] of
    the conflict id, an id slice abstracts to [X ∪ ({[a]} ∪ ∅)] (the trailing [∅]
    is [list_to_set []] from the singleton tail); these relate that to the
    [setfii_loop] accumulator form [{[a]} ∪ X]. Proving them as standalone lemmas
    keeps [set_solver] on a tiny context — calling [set_solver] inside
    [wp_scanConflicts] instead does [set_unfold in *] over the whole proof state
    (including the [list_to_set] slice hypotheses) and is prohibitively slow.

    These live at top level (outside [Section common]): [set_solver] runs
    [set_unfold in *], which would otherwise pull the heap section variables into
    the proof term and force them into the lemma's [Proof using] footprint. *)
Lemma gset_union_singleton_swap (X : gset YjsId) (a : YjsId) :
  (X ∪ ({[a]} ∪ ∅) : gset YjsId) = {[a]} ∪ X.
Proof. set_solver. Qed.

Lemma gset_elem_union_singleton_swap (X : gset YjsId) (a b : YjsId) :
  b ∈ ({[a]} ∪ X) -> b ∈ (X ∪ ({[a]} ∪ ∅) : gset YjsId).
Proof. set_solver. Qed.

Lemma gset_not_elem_union_singleton_swap (X : gset YjsId) (a b : YjsId) :
  b ∉ ({[a]} ∪ X) -> b ∉ (X ∪ ({[a]} ∪ ∅) : gset YjsId).
Proof. set_solver. Qed.

Section common.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

#[global] Instance : IsPkgInit (iProp Σ) yjs := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) yjs := build_get_is_pkg_init_wf.

Set Default Proof Using "Type*".

(** Document content type. *)
Notation A := go_string.

(* ===== abstraction of scalar fields ====================================== *)

(** Heap id (two [w64]s) to model id (two [nat]s). *)
Definition toYjsId (i : yjs.id.t) : YjsId :=
  MkYjsId (uint.nat i.(yjs.id.clientId')) (uint.nat i.(yjs.id.clock')).

Definition toContent (c : yjs.content.t) : A := c.(yjs.content.content').

(** One node of the heap DLL: its location, struct value, and the optional
    origin ids it points at (resolved out of the [originLeftId]/[originRightId]
    pointers). *)
Record item_cell := MkItemCell {
  ic_loc : loc;
  ic_val : yjs.item.t;
  ic_oleft : option yjs.id.t;
  ic_oright : option yjs.id.t;
}.

(** The loc of the node at index [k] of [cells] ([null] outside [0, len)).
    Used to place the heap [conflict] / [left] pointers within the DLL. *)
Definition node_loc (cells : list item_cell) (k : Z) : loc :=
  if decide (0 <= k)%Z then default null (ic_loc <$> cells !! Z.to_nat k) else null.

(** An origin pointer is either null (no origin) or a read-only [Id] cell.
    Origins are immutable once integrated, hence persistent ([↦□]). *)
Definition is_origin_id (p : loc) (oid : option yjs.id.t) : iProp Σ :=
  match oid with
  | None => ⌜p = null⌝
  | Some idv => ⌜p ≠ null⌝ ∗ p ↦□ idv
  end.

(** Origins are read-only, hence the predicate is persistent. *)
Global Instance is_origin_id_persistent p oid : Persistent (is_origin_id p oid).
Proof. rewrite /is_origin_id. by destruct oid; apply _. Qed.

(* ----- item-pointer helpers --------------------------------------------- *)

(** A heap item pointer is null or owns a node; [oid_of] is its model id. *)
Definition oid_of (ov : option yjs.item.t) : option YjsId :=
  (λ v, toYjsId v.(yjs.item.id')) <$> ov.

Definition item_or_null (p : loc) (ov : option yjs.item.t) (dq : dfrac) : iProp Σ :=
  match ov with
  | None => ⌜p = null⌝
  | Some v => ⌜p ≠ null⌝ ∗ p ↦{dq} v
  end.

End common.
