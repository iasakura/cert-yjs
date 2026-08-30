(** [wp_newYType]: allocating an empty root sequence (issue #54, the storage
    behind [getOrCreateYType]'s miss branch). The fresh [yType] has
    [start = nil] and [len = 0], the cells-level view of an empty type. *)
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


(** [newYType] allocates an empty root sequence (issue #54: the storage backing
    [getOrCreateYType]'s miss branch). The fresh [yType] has [start = nil] and
    [len = 0]: the cells-level view of an empty type, no cells and an empty
    model list. *)
Lemma wp_newYType :
  {{{ is_pkg_init yjs }}}
    @! yjs.newYType #()
  {{{ (p : loc), RET #p; own_ytype_cells p (DfracOwn 1) [] [] }}}.
Proof.
  wp_start as "_". wp_alloc p as "Hp". wp_auto.
  iApply "HΦ".
  iExists {| yjs.yType.start' := null; yjs.yType.len' := W64 0 |}, null.
  iFrame "Hp". iPureIntro. split_and!.
  - move=> c Hc. by apply elem_of_nil in Hc.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - by rewrite /cells_repr.
  - move=> c Hc. by apply elem_of_nil in Hc.
Qed.

End ytype_newYType.
