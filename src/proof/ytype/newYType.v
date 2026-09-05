(** [wp_newYType_runs]: allocating an empty root sequence (issue #54, the
    storage behind [getOrCreateYType]'s miss branch). The fresh [yType] has
    [start = nil] and [len = 0]: no node addresses and no runs. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core prelude.
From New.proof.item Require Import item.
From New.proof.ytype Require Import model value heap.

(* The [findPos] word-arithmetic proof writes [Z] comparisons unannotated, so fix
   [Z_scope] as the default (matching the environment it was developed in). *)
Local Open Scope Z_scope.

Section ytype_newYType.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.


(** [newYType] allocates an empty root sequence (issue #54: the storage
    backing [getOrCreateYType]'s miss branch). The fresh [yType] has
    [start = nil] and [len = 0]: no node addresses and no runs. *)
Lemma wp_newYType_runs :
  {{{ is_pkg_init yjs }}}
    @! yjs.newYType #()
  {{{ (p : loc), RET #p; own_ytype_runs p (DfracOwn 1) [] (MkTypeModel [] []) }}}.
Proof.
  wp_start as "_". wp_alloc p as "Hp". wp_auto.
  iApply "HΦ".
  iExists {| yjs.yType.start' := null; yjs.yType.len' := W64 0 |}, null.
  iFrame "Hp". iPureIntro. split_and!; reflexivity.
Qed.

End ytype_newYType.
