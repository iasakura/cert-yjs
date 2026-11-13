(** The Yjs wire protocol (issue #107, W3b; issue #131): what every message
    on the wire satisfies, and the specifications the two halves of the codec
    are trusted against.

    API
    - [update_wf inputs] (from [store/model]): the pure honesty facts of a
      batch (the 2^64 no-wrap seam per struct, and [is_pending_rooted]: head
      structs target a named root); they ride the wire protocol rather than
      the server's hypotheses.
    - [yjs_prot decode γh d]: the deployment's [ws_prot]. The bytes decode
      (under the abstract [decode] the deployment is parameterized by) to a
      batch that is, struct by struct, the same wire struct
      ([same_wire_struct], [store/model]) as an honest batch whose per-char
      expansion is certified against the global history [γh]. The two
      batches differ only in the types of the structs that have an origin,
      which the bytes do not carry: [decode] reports some type for them, the
      certificates are under the type the sender integrated them into. A
      receiver applies the certified batch ([own_update_structs_same_wire_struct]
      turns the decoder's slice into it), so it can apply any message it is
      handed with no further hypotheses. Persistent.
    - [codec_spec decode f]: the Go decoder value [f] meets [decode]. The
      deployment's [yjs.WireCodec] is TRUSTED to meet it (the same boundary
      codec.go already is, now stated instead of implicit); a future
      goose-translated codec discharges it.
    - [encoder_spec encode g]: the Go encoder value [g] meets the abstract
      [encode], the mirror image of [codec_spec] (issue #131). The
      deployment's [yjs.WireEncoder] is trusted to meet it.
    - [structs_surrogate_free structs]: no code unit of the batch is a
      UTF-16 surrogate. The batches the two halves are required to agree on:
      the wire carries UTF-8, which has no encoding of a lone surrogate, and
      the real encoder replaces one by U+FFFD (issue #233).
    - [codec_roundtrip decode encode]: the pure contract between the two
      halves: what [decode] reads back from [encode structs] is made of
      wire structs of the per-char expansion of [structs], for every
      surrogate-free batch. An inclusion, not an equation: the real encoder
      reorders (clients descending, clocks ascending) and writes a struct
      whose ids it has already written only once, neither of which a
      receiver's safety depends on.

    Laws
    - [yjs_prot_encode]: a sender that holds the certificates of a batch's
      per-char expansion owns the protocol for the batch's encoding (what
      the client's [Insert] sends).

    No ws import here: the predicate is decode plus history certificates, so
    it sits between [store] and [doc]; the ws layer instantiates
    [ws_prot := yjs_prot decode γh] at the deployment seam (ws_relay.v,
    ws_env_smoke.v, the adequacy statement). *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core.
From New.proof Require Import prelude.
From New.proof Require Import history.
From New.proof.store Require Import store.

Section yjs_prot.

(* [allG] only (no [heapGS]): the protocol must be nameable inside an
   adequacy theorem's initial fancy update, before any node exists.
   [codec_spec], which contains a WP, lives in the second section below. *)
Context {Σ : gFunctors} `{!allG Σ}.

Set Default Proof Using "Type*".

Notation A := (list w16).

Notation P := go_string.

Local Notation TId := (TypeId P).

Local Notation Input := (TId * IntegrateInput (A := A))%type.

(** The abstract codec: which bytes stand for which batch is the
    application's business. The deployment's Go-level codec value is related
    to it by [codec_spec]; the environment peers (ws_env_smoke.v) construct
    messages with a matching encode. Nothing in the server depends on the
    choice beyond being able to read one back. *)
Context (decode : list u8 -> option (list Input)).

(* ===== definitions ======================================================== *)

(** The wire protocol: these bytes decode to a batch that is, struct by
    struct, the same wire struct as an honest batch every per-char operation
    of which is a point of the global history [γh]. Per character, via
    [expand_inputs], because that is what the ghost history holds and what
    [wp_Transaction__applyUpdate] consumes. Persistent, as [ws_prot] must be
    (one message is delivered to every member of a room). *)
Definition yjs_prot (γh : history_names) (d : list u8) : iProp Σ :=
  ∃ decoded inputs : list Input,
    ⌜decode d = Some decoded⌝ ∗ ⌜Forall2 same_wire_struct decoded inputs⌝ ∗
    ⌜update_wf inputs⌝ ∗
    is_pending_certified γh (expand_inputs inputs).

(** [structs_surrogate_free structs]: no code unit of the batch lies in the
    UTF-16 surrogate range D800-DFFF. *)
Definition structs_surrogate_free (structs : list Input) : Prop :=
  ∀ struct unit, struct ∈ structs -> unit ∈ in_content struct.2 ->
    ¬ (0xD800 ≤ uint.Z unit ≤ 0xDFFF)%Z.

(** The pure contract between the two halves of the codec, for the abstract
    [encode] the deployment's encoder is trusted against ([encoder_spec]). *)
Definition codec_roundtrip (encode : list Input -> list u8) : Prop :=
  ∀ structs, structs_surrogate_free structs ->
    ∃ decoded, decode (encode structs) = Some decoded ∧
      ∀ decoded_struct, decoded_struct ∈ decoded ->
        ∃ sent_struct, sent_struct ∈ expand_inputs structs ∧
          same_wire_struct decoded_struct sent_struct.

(* ===== lemmas ============================================================= *)

#[global] Instance yjs_prot_persistent γh d : Persistent (yjs_prot γh d).
Proof. apply _. Qed.

(** What a sender needs to put a batch on the wire: the batch is honest and
    the certificates of its per-char expansion are in the history. Then its
    encoding satisfies the protocol. *)
Lemma yjs_prot_encode (encode : list Input -> list u8) (γh : history_names)
    (structs : list Input) :
  codec_roundtrip encode ->
  structs_surrogate_free structs ->
  update_wf (expand_inputs structs) ->
  is_pending_certified γh (expand_inputs structs) -∗
  yjs_prot γh (encode structs).
Proof.
  move=> Hroundtrip Hfree Hwf.
  destruct (Hroundtrip structs Hfree) as (decoded & Hdecode & Hdecoded).
  have [inputs [Hsame Hinputs]] : ∃ inputs, Forall2 same_wire_struct decoded inputs ∧
      ∀ y, y ∈ inputs -> y ∈ expand_inputs structs.
  { clear Hdecode. induction decoded as [| x decoded IH].
    { exists []. split; [constructor | by move=> y /elem_of_nil]. }
    destruct (Hdecoded x ltac:(apply elem_of_cons; by left)) as (y & Hy & Hxy).
    destruct IH as (inputs & Hsame & Hinputs).
    { move=> x' Hx'. apply Hdecoded, elem_of_cons. by right. }
    exists (y :: inputs). split; first by constructor.
    move=> y' /elem_of_cons [-> | Hy']; [exact Hy | exact (Hinputs y' Hy')]. }
  have Hone : ∀ y, y ∈ inputs -> length (in_content y.2) = 1%nat.
  { move=> y Hy. exact (expand_inputs_unit_content structs y (Hinputs y Hy)). }
  iIntros "#Hcerts".
  iExists decoded, inputs. iSplit; first done. iSplit; first done.
  iSplit.
  { iPureIntro. destruct Hwf as [Hfits Hrooted]. split.
    - move=> y Hy. exact (Hfits y (Hinputs y Hy)).
    - move=> y Hy. exact (Hrooted y (Hinputs y Hy)). }
  rewrite (expand_inputs_all_singleton inputs Hone) /is_pending_certified.
  iApply big_sepL_forall. iIntros (i y Hy).
  have Hin := Hinputs y (list_elem_of_lookup_2 _ _ _ Hy).
  apply list_elem_of_lookup in Hin as [j Hj].
  iApply (big_sepL_lookup _ _ j y Hj with "Hcerts").
Qed.

End yjs_prot.

Section codec_spec.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

Notation A := (list w16).

Notation P := go_string.

Local Notation TId := (TypeId P).

Local Notation Input := (TId * IntegrateInput (A := A))%type.

Context (decode : list u8 -> option (list Input)).

(* ===== definitions ======================================================== *)

(** The Go codec value [f] meets the abstract [decode]: on any byte slice it
    reports exactly whether [decode] succeeds, and on success returns a
    struct slice denoting the decoded batch. *)
(** The decoded delete set is NOT constrained: deletes are state, not
    operations (docs/plan-delete-set.md), so they carry no history
    certificates and the protocol has nothing to say about them. It appears
    as the set of ids the batch denotes rather than as the wire records
    themselves, which are internal data a caller has no business reading.
    That is
    faithful rather than lax: a peer's spans can only tombstone ids that are
    already integrated, and tombstoning is idempotent and commutative, so a
    dishonest span costs content but cannot corrupt the CRDT. Yjs has no
    Byzantine tolerance at all, and peer conformance is an assumption of the
    whole stack ([yjs_prot] itself is that assumption for the struct half). *)
Definition codec_spec (f : func.t) : iProp Σ :=
  □ (∀ (s : slice.t) (dq : dfrac) (data : list u8),
      {{{ s ↦*{dq} data }}}
        #f #s
      {{{ (ok : bool) (sl sldel : slice.t), RET (#ok, #sl, #sldel);
          s ↦*{dq} data ∗
          if ok
          then ∃ (inputs : list Input) (deleted : gset YjsId),
               ⌜decode data = Some inputs⌝ ∗
               own_update_structs sl (DfracOwn 1) inputs ∗
               own_delete_ids sldel (DfracOwn 1) deleted
          else ⌜decode data = None⌝ }}}).

(** The Go encoder value [g] meets the abstract [encode]: on any struct
    slice it returns a fresh byte slice holding the encoding of the batch the
    slice denotes, and leaves the structs as they were. *)
Definition encoder_spec (encode : list Input -> list u8) (encoder : func.t) : iProp Σ :=
  □ (∀ (structs_slice : slice.t) (dq : dfrac) (structs : list Input),
      {{{ own_update_structs structs_slice dq structs }}}
        #encoder #structs_slice
      {{{ (bytes_slice : slice.t), RET #bytes_slice;
          own_update_structs structs_slice dq structs ∗
          bytes_slice ↦* encode structs ∗ own_slice_cap w8 bytes_slice (DfracOwn 1) }}}).

(* ===== lemmas ============================================================= *)

#[global] Instance codec_spec_persistent f : Persistent (codec_spec f).
Proof. apply _. Qed.

#[global] Instance encoder_spec_persistent encode encoder : Persistent (encoder_spec encode encoder).
Proof. apply _. Qed.

End codec_spec.
