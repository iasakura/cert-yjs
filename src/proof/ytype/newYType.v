(** [wp_newYType]: allocating an empty root sequence (issue #54, the
    storage behind [getOrCreateYType]'s miss branch). The fresh [yType] has
    [start = nil], [len = 0] and the given [name]: no node addresses and no
    runs. *)
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

Notation A := (list w16).


(** [newYType] allocates an empty root sequence (issue #54: the storage
    backing [getOrCreateYType]'s miss branch). The fresh [yType] has
    [start = nil] and [len = 0]: no node addresses and no runs. The [name]
    field is set to the argument; [own_ytype] does not expose it yet. *)
Lemma wp_newYType (name : go_string) :
  {{{ is_pkg_init yjs }}}
    @! yjs.newYType #name
  {{{ (p : loc), RET #p; own_ytype p (DfracOwn 1) [] (MkTypeModel []) }}}.
Proof.
  wp_start as "_". wp_auto. wp_alloc p as "Hp". wp_auto.
  iApply "HΦ".
  iExists {| yjs.yType.start' := null; yjs.yType.len' := W64 0; yjs.yType.name' := name |}, null.
  iFrame "Hp". iPureIntro. split_and!; reflexivity.
Qed.

End ytype_newYType.
