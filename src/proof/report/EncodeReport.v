(** [wp_EncodeReport]: the report encoder ([yjs/report.go], issue #239).
    The slice it returns is fresh, the caller's own, and holds bytes the
    decoder reads back as the root's name and the snapshot's characters
    ([own_report], report/heap.v); inside, the bytes are the pure
    [encode_report] of report/value.v, and the roundtrip
    ([decode_encode_report]) is what the spec states, since only the encoder
    sees that the name's length fits a word. Its one helper, [appendUint64],
    is in [wp_private]. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core.
From New.proof Require Import algebra.
From New.proof Require Import prelude.
From Perennial.Helpers.Word Require Import LittleEndian.
From New.proof.github_com.mit_pdos.perennial.goose.model Require Import strings.
From New.proof.ytype Require Import model value heap.
From New.proof.report Require Import value heap wp_private.

Local Open Scope Z_scope.

Section report.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

Notation A := (list w16).

(** [EncodeReport]: the report of root [name] for a snapshot, given as the
    slice [Text.Snapshot] returns ([own_snapshot_chars], read at any fraction
    and handed back), as a fresh slice of bytes that decode back to the name
    and the snapshot's characters ([own_report]). *)
Lemma wp_EncodeReport (name : go_string) (chars_sl : slice.t) (dq : dfrac)
    (model : list (YjsItem A * bool)) :
  {{{ is_pkg_init yjs ∗ own_snapshot_chars chars_sl dq model }}}
    @! yjs.EncodeReport #name #chars_sl
  {{{ (sl : slice.t), RET #sl;
      own_snapshot_chars chars_sl dq model ∗
      own_report sl (DfracOwn 1) name (snapshot_chars model) }}}.
Proof.
  wp_start as "Hchars".
  iDestruct "Hchars" as "[Hchars Hcharscap]".
  iDestruct (own_slice_len with "Hchars") as %[Hlen Hlenz].
  wp_auto.
  (* the header: the name's length, the name, the character count *)
  wp_apply wp_string_len as "%Hnamelen".
  wp_apply (wp_appendUint64 slice.nil [] with "[]").
  { iSplitL; [iApply own_slice_nil | iApply own_slice_cap_nil]. }
  iIntros (sl1) "[Hsl1 Hcap1]".
  wp_auto.
  wp_apply wp_string_to_bytes. iIntros (nsl) "[Hnsl Hncap]".
  wp_auto.
  wp_apply (wp_slice_append with "[$Hsl1 $Hcap1 $Hnsl]"). iIntros (sl2) "(Hsl2 & Hcap2 & _)".
  wp_auto.
  wp_apply (wp_appendUint64 with "[$Hsl2 $Hcap2]"). iIntros (sl3) "[Hsl3 Hcap3]".
  wp_auto.
  (* the walk: [buf] holds the header and the characters before [i] *)
  iAssert (∃ (i : nat) (sl : slice.t),
    "Hbuf" ∷ buf_ptr ↦ sl ∗
    "Hsl" ∷ sl ↦* (u64_le (W64 (length name)) ++ name ++
                   u64_le (W64 (length (snapshot_chars model))) ++
                   mjoin (encode_char <$> take i (snapshot_chars model))) ∗
    "Hcap" ∷ own_slice_cap w8 sl (DfracOwn 1) ∗
    "Hi" ∷ i_ptr ↦ W64 (Z.of_nat i) ∗
    "%Hi" ∷ ⌜(i <= length (snapshot_chars model))%nat⌝)%I
    with "[buf Hsl3 Hcap3 i]" as "IH".
  { iExists 0%nat, sl3. rewrite take_0 /= app_nil_r. iFrame "buf Hcap3 i".
    iSplitL; last (iPureIntro; lia).
    iExactEq "Hsl3". f_equal.
    replace chars_sl.(slice.len) with (W64 (length (snapshot_chars model))) by word.
    rewrite -!app_assoc //. }
  wp_for "IH".
  case_bool_decide as Hilt.
  { (* one more character: its four words *)
    have Hipos : (i < length (snapshot_chars model))%nat by (move: Hilt Hlen Hlenz; word).
    destruct (lookup_lt_is_Some_2 (snapshot_chars model) i Hipos) as [c Hc].
    wp_auto.
    rewrite (decide_True (P := (0 ≤ sint.Z (W64 i) < sint.Z chars_sl.(slice.len))%Z)); last word.
    wp_apply (wp_load_slice_index with "[$Hchars]").
    { word. }
    { iPureIntro. replace (Z.to_nat (sint.Z (W64 i))) with i by word. exact Hc. }
    iIntros "Hchars".
    wp_auto.
    wp_apply (wp_appendUint64 with "[$Hsl $Hcap]"). iIntros (sl4) "[Hsl Hcap]".
    wp_auto.
    wp_apply (wp_appendUint64 with "[$Hsl $Hcap]"). iIntros (sl5) "[Hsl Hcap]".
    wp_auto.
    destruct c as [client clock deleted unit]; simpl.
    wp_if_join (λ v : val, ⌜v = execute_val⌝ ∗
        ∃ (sl6 : slice.t),
        "Hbuf" ∷ buf_ptr ↦ sl6 ∗
        "Hsl" ∷ sl6 ↦* ((((u64_le (W64 (length name)) ++ name ++
                           u64_le (W64 (length (snapshot_chars model))) ++
                           mjoin (encode_char <$> take i (snapshot_chars model))) ++
                          u64_le client) ++ u64_le clock) ++
                         u64_le (if deleted then W64 1 else W64 0)) ∗
        "Hcap" ∷ own_slice_cap w8 sl6 (DfracOwn 1))%I
        with "[Hbuf Hsl Hcap]".
    { wp_apply (wp_appendUint64 with "[$Hsl $Hcap]"). iIntros (sl6) "[Hsl Hcap]".
      wp_auto. iSplitR; first done. iExists sl6. iFrame. }
    { wp_apply (wp_appendUint64 with "[$Hsl $Hcap]"). iIntros (sl6) "[Hsl Hcap]".
      wp_auto. iSplitR; first done. iExists sl6. iFrame. }
    iIntros (v) "[-> H]". iNamed "H".
    wp_auto.
    wp_apply (wp_appendUint64 with "[$Hsl $Hcap]"). iIntros (sl7) "[Hsl Hcap]".
    wp_auto.
    wp_for_post.
    iFrame "Hchars Hcharscap HΦ chars Hncap".
    iExists (S i), sl7. iFrame "Hbuf Hcap".
    iSplitL "Hsl".
    { iExactEq "Hsl". f_equal.
      rewrite (take_S_r _ _ _ Hc) fmap_app join_app /= app_nil_r.
      rewrite /encode_char /= -!app_assoc //. }
    iSplitL "Hi".
    { replace (w64_word_instance.(word.add) (W64 i) (W64 1)) with (W64 (S i)) by word.
      iFrame "Hi". }
    iPureIntro; lia. }
  (* every character written: the slice is the report, and the decoder
     reads it back (the name's length fits a word by [wp_string_len], the
     character count by the slice's length) *)
  wp_auto.
  have -> : i = length (snapshot_chars model) by (move: Hilt Hlen Hlenz Hi; word).
  rewrite take_ge; last lia.
  iApply ("HΦ" $! sl).
  rewrite /own_snapshot_chars. iFrame "Hchars Hcharscap".
  iExists (encode_report name (snapshot_chars model)). iFrame "Hcap".
  iSplitL "Hsl"; first by rewrite /encode_report.
  iPureIntro. apply decode_encode_report; [lia | word].
Qed.

End report.
