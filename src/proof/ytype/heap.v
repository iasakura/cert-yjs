(** The [yType] container, Iris layer.

    In y-octo [YType] is the lock-guarded inner data structure while the [YText]
    handle lives outside the lock; this directory owns the [YType] side and is
    closed over implementation ([yjs/ytype.go]), spec, and proof.

    Definitions
    - [own_ytype_runs parent dq ls tm]: THE representation predicate. [parent]
      is a heap [yType] whose [start] heads the run-granular DLL
      ([own_dll_runs], from [item/heap.v]) at the node addresses [ls] and the
      runs of [tm], with [len] counting the visible chars and the document
      list the runs' flatten. [dfrac]-parameterized (idiom: plain owned heap
      data), and fractional through the spine
      ([own_ytype_runs_fractional], in [store/heap.v] next to the pool's).

    The method proofs are [ytype/newYType.v], [ytype/findPos.v] and
    [ytype/Text.v]. *)
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

Notation A := go_string.

(* ===== definitions ======================================================== *)

(** [own_ytype_runs parent dq ls tm]: the type at its run-granular model,
    PRIMITIVE (plan-item-run-split stage 3c): [parent] is a heap [yType]
    whose [start] heads the run-granular DLL [own_dll_runs] at the node
    addresses [ls] and the runs [tm_runs tm]; [len] counts the visible
    chars and the document list is the runs' flatten. The [(locs, p)]-keyed
    pool ([store/heap.v]'s [own_type_pool_runs]) is a big-op of these. *)
Definition own_ytype_runs (parent : loc) (dq : dfrac)
    (ls : list loc) (tm : type_model) : iProp Σ :=
  ∃ (yt : yjs.yType.t) (tl : loc),
    "Hparent" ∷ parent ↦{dq} yt ∗
    "Hdll" ∷ own_dll_runs dq parent yt.(yjs.yType.start') tl null null ls (tm_runs tm) ∗
    "%Hlen" ∷ ⌜yt.(yjs.yType.len') = W64 (runs_visible (tm_runs tm))⌝ ∗
    "%Harr" ∷ ⌜tm_arr tm = runs_flatten (tm_runs tm)⌝.

(* ===== lemmas ============================================================= *)

End ytype_heap.
