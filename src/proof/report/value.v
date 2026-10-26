(** The report, VALUE layer (issue #239): what a replica writes to the
    trace about one root text, as bytes, and how those bytes read back. The
    report has no pure model of its own: its values are Go values (bytes,
    [SnapshotChar]) denoting the snapshot model of [ytype/value].

    A report is the root's name and the text as [Text.Snapshot] sees it:
    character by character, the id of the item carrying it, its tombstone
    bit and its code unit ([SnapshotChar], [ytype/value]'s
    [snapshot_chars]). Its layout is the simplest one a decoder reads back:
    every field a little-endian [u64] ([u64_le]), the name and the character
    list each preceded by their length.

    Definitions
    - [encode_report name chars]: the bytes [EncodeReport] produces.
    - [decode_report d]: the name and characters the bytes [d] denote, if
      they are a report; what the trace protocol and the closed theorem read
      a trace entry with.
    - [report_ids chars] / [report_text chars]: what the closed theorem
      compares two reports on, the set of ids and the (id, unit) sequence;
      [reports_converge T]: its conclusion over a trace, same root and
      same ids give the same text.

    Laws
    - [decode_encode_report]: the decoder reads the encoder back.
    - [decode_u64_app] / [decode_bytes_app] / [decode_char_app] /
      [decode_chars_app]: the decoding steps read an encoded prefix off an
      appended tail, which is what makes a report's bytes denote one thing.
    - [report_ids_snapshot_chars] / [report_text_snapshot_chars]: a
      snapshot's reported ids are its items' ids ([item_fits] makes the word
      pairs injective), and equal items report equal text. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From Perennial.Helpers.Word Require Import LittleEndian.
From New.proof Require Import core prelude network_convergence.
From New.proof.item Require Import model.
From New.proof.ytype Require Import model value.

Section report_value.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

Notation A := (list w16).

(* ===== definitions ======================================================== *)

(** One character, as the four words the report spells it in. *)
Definition encode_char (c : yjs.SnapshotChar.t) : list u8 :=
  u64_le c.(yjs.SnapshotChar.Client') ++
  u64_le c.(yjs.SnapshotChar.Clock') ++
  u64_le (if c.(yjs.SnapshotChar.Deleted') then W64 1 else W64 0) ++
  u64_le (W64 (uint.Z c.(yjs.SnapshotChar.Unit'))).

Definition encode_report (name : go_string) (chars : list yjs.SnapshotChar.t) : list u8 :=
  u64_le (W64 (length name)) ++ name ++
  u64_le (W64 (length chars)) ++ mjoin (encode_char <$> chars).

(** Reading one word, one byte string of a given length, one character and
    [n] characters off the front of a byte string. *)
Definition decode_u64 (d : list u8) : option (w64 * list u8) :=
  if decide (8 ≤ length d)%nat then Some (le_to_u64 (take 8 d), drop 8 d) else None.

Definition decode_bytes (n : nat) (d : list u8) : option (list u8 * list u8) :=
  if decide (n ≤ length d)%nat then Some (take n d, drop n d) else None.

Definition decode_char (d : list u8) : option (yjs.SnapshotChar.t * list u8) :=
  '(client, d1) ← decode_u64 d;
  '(clock, d2) ← decode_u64 d1;
  '(deleted, d3) ← decode_u64 d2;
  '(unit, d4) ← decode_u64 d3;
  Some (yjs.SnapshotChar.mk client clock (bool_decide (deleted ≠ W64 0)) (W16 (uint.Z unit)), d4).

Fixpoint decode_chars (n : nat) (d : list u8) : option (list yjs.SnapshotChar.t * list u8) :=
  match n with
  | O => Some ([], d)
  | S n' =>
      '(c, d1) ← decode_char d;
      '(cs, d2) ← decode_chars n' d1;
      Some (c :: cs, d2)
  end.

(** The report a byte string denotes: a name and its characters, with
    nothing left over. *)
Definition decode_report (d : list u8) : option (go_string * list yjs.SnapshotChar.t) :=
  '(nlen, d1) ← decode_u64 d;
  '(name, d2) ← decode_bytes (uint.nat nlen) d1;
  '(clen, d3) ← decode_u64 d2;
  '(chars, d4) ← decode_chars (uint.nat clen) d3;
  if decide (d4 = []) then Some (name, chars) else None.

(** What the closed theorem reads off a report: the ids of its characters,
    as a set ([report_ids]), and the text they spell, each character's id
    and code unit in document order with the tombstone bits dropped
    ([report_text]). *)
Definition snapshot_char_id (c : yjs.SnapshotChar.t) : w64 * w64 :=
  (c.(yjs.SnapshotChar.Client'), c.(yjs.SnapshotChar.Clock')).

Definition report_ids (chars : list yjs.SnapshotChar.t) : gset (w64 * w64) :=
  list_to_set (snapshot_char_id <$> chars).

Definition report_text (chars : list yjs.SnapshotChar.t) : list (w64 * w64 * w16) :=
  (λ c, (snapshot_char_id c, c.(yjs.SnapshotChar.Unit'))) <$> chars.

(** [reports_converge T]: any two reports among the byte strings [T] that
    are about the same root and hold the same ids spell the same text. The
    closed theorem's conclusion, over the run's trace. *)
Definition reports_converge (T : list (list u8)) : Prop :=
  ∀ (d1 d2 : list u8) (name : go_string) (chars1 chars2 : list yjs.SnapshotChar.t),
    d1 ∈ T -> d2 ∈ T ->
    decode_report d1 = Some (name, chars1) -> decode_report d2 = Some (name, chars2) ->
    report_ids chars1 = report_ids chars2 -> report_text chars1 = report_text chars2.

(* ===== lemmas ============================================================= *)

Lemma decode_u64_app (x : w64) (rest : list u8) :
  decode_u64 (u64_le x ++ rest) = Some (x, rest).
Proof.
  rewrite /decode_u64 length_app u64_le_length.
  case_decide as Hd; last lia.
  rewrite take_app_length' ?u64_le_length //.
  rewrite drop_app_length' ?u64_le_length //.
  rewrite u64_le_to_word //.
Qed.

Lemma decode_bytes_app (bs rest : list u8) :
  decode_bytes (length bs) (bs ++ rest) = Some (bs, rest).
Proof.
  rewrite /decode_bytes length_app.
  case_decide as Hd; last lia.
  rewrite take_app_length drop_app_length //.
Qed.

Lemma decode_char_app (c : yjs.SnapshotChar.t) (rest : list u8) :
  decode_char (encode_char c ++ rest) = Some (c, rest).
Proof.
  rewrite /decode_char /encode_char -!app_assoc.
  rewrite decode_u64_app /=.
  rewrite decode_u64_app /=.
  rewrite decode_u64_app /=.
  rewrite decode_u64_app /=.
  destruct c as [client clock deleted unit]. simpl. f_equal. f_equal.
  f_equal; [destruct deleted; [apply bool_decide_eq_true_2; word | apply bool_decide_eq_false_2; word] | word].
Qed.

Lemma decode_chars_app (chars : list yjs.SnapshotChar.t) (rest : list u8) :
  decode_chars (length chars) (mjoin (encode_char <$> chars) ++ rest) = Some (chars, rest).
Proof.
  induction chars as [| c chars IH]; first done.
  simpl. rewrite -app_assoc decode_char_app /= IH //.
Qed.

(** The decoder reads the encoder back, for a name and a character list the
    words can count. *)
Lemma decode_encode_report (name : go_string) (chars : list yjs.SnapshotChar.t) :
  (Z.of_nat (length name) < 2^64)%Z ->
  (Z.of_nat (length chars) < 2^64)%Z ->
  decode_report (encode_report name chars) = Some (name, chars).
Proof.
  move=> Hname Hchars.
  rewrite /decode_report /encode_report.
  rewrite decode_u64_app /=.
  have -> : uint.nat (W64 (length name)) = length name by word.
  rewrite decode_bytes_app /=.
  rewrite decode_u64_app /=.
  have -> : uint.nat (W64 (length chars)) = length chars by word.
  rewrite -(app_nil_r (mjoin (encode_char <$> chars))) decode_chars_app /=.
  done.
Qed.

(** A snapshot's reported ids are its items' ids, injectively, once those
    fit the words ([item_fits]): equal reported id sets are equal id sets. *)
Lemma report_ids_snapshot_chars (s1 s2 : list (YjsItem A * bool)) :
  Forall item_fits s1.*1 -> Forall item_fits s2.*1 ->
  report_ids (snapshot_chars s1) = report_ids (snapshot_chars s2) ->
  item_ids s1.*1 = item_ids s2.*1.
Proof.
  move=> Hfit1 Hfit2 Hids.
  have Hmem : ∀ (s : list (YjsItem A * bool)) (x : YjsItem A), x ∈ s.*1 ->
      (W64 (Z.of_nat (clientId (item_id x))), W64 (Z.of_nat (clock (item_id x))))
        ∈ report_ids (snapshot_chars s).
  { move=> s x Hx.
    rewrite /report_ids elem_of_list_to_set /snapshot_chars -list_fmap_compose list_elem_of_fmap.
    apply list_elem_of_fmap in Hx as (p & -> & Hp). by exists p. }
  have Hback : ∀ (s : list (YjsItem A * bool)) (d : YjsId), Forall item_fits s.*1 ->
      (Z.of_nat (clientId d) < 2^64)%Z -> (Z.of_nat (clock d) < 2^64)%Z ->
      (W64 (Z.of_nat (clientId d)), W64 (Z.of_nat (clock d))) ∈ report_ids (snapshot_chars s) ->
      ∃ x, d = item_id x ∧ x ∈ s.*1.
  { move=> s d Hfit Hc Hk Hd.
    rewrite /report_ids elem_of_list_to_set /snapshot_chars -list_fmap_compose list_elem_of_fmap in Hd.
    destruct Hd as (p & Hpair & Hp).
    have Hx : p.1 ∈ s.*1 by (apply list_elem_of_fmap; by exists p).
    have [Hc' Hk'] := proj1 (list.Forall_forall _ _) Hfit p.1 Hx.
    exists p.1. split; last exact Hx.
    rewrite /snapshot_char_id /snapshot_char /= in Hpair.
    have Hclient : W64 (Z.of_nat (clientId d)) = W64 (Z.of_nat (clientId (item_id p.1)))
      := f_equal fst Hpair.
    have Hclock : W64 (Z.of_nat (clock d)) = W64 (Z.of_nat (clock (item_id p.1)))
      := f_equal snd Hpair.
    apply (f_equal uint.Z) in Hclient. apply (f_equal uint.Z) in Hclock.
    destruct d as [dc dk]. destruct (item_id p.1) as [pc pk].
    f_equal; apply Nat2Z.inj; [move: Hclient Hc Hc' | move: Hclock Hk Hk'];
      cbn [clientId clock]; word. }
  rewrite /item_ids. apply set_eq => d.
  rewrite !elem_of_list_to_set !list_elem_of_fmap.
  split.
  - move=> [x [-> Hx]].
    have [Hc Hk] := proj1 (list.Forall_forall _ _) Hfit1 x Hx.
    apply (Hback s2 _ Hfit2 Hc Hk). rewrite -Hids. exact (Hmem s1 x Hx).
  - move=> [x [-> Hx]].
    have [Hc Hk] := proj1 (list.Forall_forall _ _) Hfit2 x Hx.
    apply (Hback s1 _ Hfit1 Hc Hk). rewrite Hids. exact (Hmem s2 x Hx).
Qed.

(** Two snapshots of the same items report the same text. *)
Lemma report_text_snapshot_chars (s1 s2 : list (YjsItem A * bool)) :
  s1.*1 = s2.*1 -> report_text (snapshot_chars s1) = report_text (snapshot_chars s2).
Proof.
  move=> Heq.
  have Hf : ∀ s : list (YjsItem A * bool), report_text (snapshot_chars s) =
      (λ x : YjsItem A,
         ((W64 (Z.of_nat (clientId (item_id x))), W64 (Z.of_nat (clock (item_id x)))),
          default (W16 0) (content x !! 0%nat))) <$> s.*1.
  { move=> s. rewrite /report_text /snapshot_chars -!list_fmap_compose.
    apply list_fmap_ext. by move=> i [x b] _. }
  rewrite !Hf Heq //.
Qed.

End report_value.
