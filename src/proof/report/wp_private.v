(** The report encoder's unexported helper ([yjs/report.go], issue #239):
    [appendUint64], a little-endian word appended byte by byte ([u64_le]),
    stated over the slice it grows. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core.
From New.proof Require Import prelude.
From Perennial.Helpers.Word Require Import LittleEndian.

Local Open Scope Z_scope.

Section report.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

(** [appendUint64]: one word, little-endian, appended to the caller's slice. *)
Lemma wp_appendUint64 (buf : slice.t) (bs : list u8) (x : w64) :
  {{{ is_pkg_init yjs ∗ buf ↦* bs ∗ own_slice_cap w8 buf (DfracOwn 1) }}}
    @! yjs.appendUint64 #buf #x
  {{{ (sl : slice.t), RET #sl; sl ↦* (bs ++ u64_le x) ∗ own_slice_cap w8 sl (DfracOwn 1) }}}.
Proof.
  wp_start as "[Hbuf Hcap]".
  wp_auto.
  wp_apply wp_slice_literal. iSplitR; first done. iIntros "%bsl [Hbsl _]". wp_auto.
  wp_apply (wp_slice_append with "[$Hbuf $Hcap $Hbsl]").
  iIntros (sl) "(Hsl & Hslcap & _)".
  wp_auto. iApply "HΦ". iFrame "Hslcap".
  iExactEq "Hsl". f_equal. f_equal.
  (* the eight literal bytes are the word's little-endian split *)
  replace (sint.nat (W64 0)) with 0%nat by word.
  replace (sint.nat (W64 (0 + 1))) with 1%nat by word.
  replace (sint.nat (W64 (0 + 1 + 1))) with 2%nat by word.
  replace (sint.nat (W64 (0 + 1 + 1 + 1))) with 3%nat by word.
  replace (sint.nat (W64 (0 + 1 + 1 + 1 + 1))) with 4%nat by word.
  replace (sint.nat (W64 (0 + 1 + 1 + 1 + 1 + 1))) with 5%nat by word.
  replace (sint.nat (W64 (0 + 1 + 1 + 1 + 1 + 1 + 1))) with 6%nat by word.
  replace (sint.nat (W64 (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1))) with 7%nat by word.
  simpl.
  rewrite u64_le_unseal /u64_le_def /=.
  rewrite !Z.shiftr_shiftr; try lia.
  repeat f_equal.
  all: rewrite word.unsigned_sru_nowrap; [ | word ]; f_equal; word.
Qed.

End report.
