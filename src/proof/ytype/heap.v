(** The [yType] container, Iris layer.

    In y-octo [YType] is the lock-guarded inner data structure while the [YText]
    handle lives outside the lock; this directory owns the [YType] side and is
    closed over implementation ([yjs/ytype.go]), spec, and proof.

    Definitions
    - [own_ytype parent dq ls tm]: THE representation predicate. [parent]
      is a heap [yType] whose [start] heads the DLL
      ([own_dll], from [item/heap.v]) at the node addresses [ls] and the
      runs of [tm], with [len] counting the visible chars. The type's
      document list is not a separate field of [tm] but its runs' flatten
      ([tm_arr]), so it cannot drift from the spine.
      [dfrac]-parameterized (idiom: plain owned heap data), and fractional
      through the spine
      ([own_ytype_fractional], in [store/heap.v] next to the pool's).

    [own_snapshot_chars sl dq model] is the slice [Text.Snapshot] returns
    for a snapshot (issue #239): the [SnapshotChar] values of its characters.

    The method proofs are [ytype/newYType.v], [ytype/findPos.v],
    [ytype/Text.v] and [ytype/Snapshot.v]. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core prelude.
(* The [findPos] word-arithmetic proof writes [Z] comparisons unannotated, so fix
   [Z_scope] as the default (matching the environment it was developed in). *)
Local Open Scope Z_scope.
From New.proof.ytype Require Import model value.
From New.proof.id Require Import value heap.
From New.proof.item Require Import run_theory model value heap.

Section ytype_heap.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

Notation A := (list w16).

(* ===== definitions ======================================================== *)

(** [own_ytype parent dq ls tm]: THE type predicate. [parent] is a heap [yType]
    whose [start] heads the DLL [own_dll] at the node
    addresses [ls] and the runs [tm_runs tm]; [len] counts the visible
    chars and the document list is the runs' flatten. The [(locs, p)]-keyed
    pool ([store/heap.v]'s [own_type_pool]) is a big-op of these. *)
Definition own_ytype (parent : loc) (dq : dfrac)
    (ls : list loc) (tm : type_model) : iProp Σ :=
  ∃ (yt : yjs.yType.t) (tl : loc),
    "Hparent" ∷ parent ↦{dq} yt ∗
    "Hdll" ∷ own_dll dq parent yt.(yjs.yType.start') tl null null ls (tm_runs tm) ∗
    "%Hlen" ∷ ⌜yt.(yjs.yType.len') = W64 (runs_visible (tm_runs tm))⌝.


(** [own_snapshot_chars sl dq model]: the slice [Text.Snapshot] returns for
    the snapshot [model] (issue #239): one [SnapshotChar] value per
    character ([snapshot_chars]), with the slice's capacity. Plain data,
    four scalars per character, no invariant of its own. *)
Definition own_snapshot_chars (sl : slice.t) (dq : dfrac)
    (model : list (YjsItem A * bool)) : iProp Σ :=
  sl ↦*{dq} snapshot_chars model ∗ own_slice_cap yjs.SnapshotChar.t sl dq.

(* ===== lemmas ============================================================= *)

End ytype_heap.
