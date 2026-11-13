(** The Yjs wire protocol (issue #107, W3b; issue #131): what every message
    on the wire satisfies, and the specifications the two halves of the codec
    are trusted against.

    API
    - [update_wf inputs] (from [store/model]): the pure honesty facts of a
      batch (the 2^64 no-wrap seam per struct, and [is_pending_rooted]: head
      structs target a named root); they ride the wire protocol rather than
      the server's hypotheses.
    - [decodes_to decode d inputs]: the bytes [d] decode to the batch
      [inputs], up to what the wire does not carry: [decode d] is a batch
      that is, struct by struct, the same wire struct ([same_wire_struct],
      [store/model]) as [inputs]. The two differ only in the types of the
      structs that have an origin: the bytes of such a struct do not say
      which type it belongs to, so [decode] reports some type for it, and
      [inputs] has the type the sender integrated it into.
    - [yjs_prot decode γh d]: the deployment's [ws_prot]. The bytes decode
      ([decodes_to]) to an honest batch whose per-char expansion is
      certified against the global history [γh]. A receiver applies that
      batch ([own_update_structs_same_wire_struct] turns the decoder's slice
      into it), so it can apply any message it is handed with no further
      hypotheses. Persistent.
    - [codec_spec decode f]: the Go decoder value [f] meets [decode]. The
      deployment's [yjs.WireCodec] is TRUSTED to meet it (the same boundary
      codec.go already is, now stated instead of implicit); a future
      goose-translated codec discharges it.
    - [encoder_spec encode g]: the Go encoder value [g] meets the abstract
      [encode], the mirror image of [codec_spec] (issue #131). The
      deployment's [yjs.WireEncoder] is trusted to meet it.
    - [units_surrogate_free units] / [structs_surrogate_free structs]: no
      code unit (of the list, of the batch) is a UTF-16 surrogate. The
      batches the two halves are required to agree on: the wire carries
      UTF-8, which has no encoding of a lone surrogate, and the real encoder
      replaces one by U+FFFD (issue #233).
    - [codec_roundtrip decode encode]: the pure contract between the two
      halves: the encoding of a surrogate-free batch whose characters are
      well formed ([update_wf]: their clocks fit a machine word, which is
      where the real decoder counts them) decodes ([decodes_to]) to
      characters of the batch (structs of its per-char expansion). An
      inclusion, not an equation: the real encoder reorders (clients
      descending, clocks ascending) and writes a struct whose ids it has
      already written only once, neither of which a receiver's safety
      depends on, and a trusted hypothesis assumes no more than the proofs
      use.

    Laws
    - [decodes_to_decoded]: what [decode] reports is what the bytes decode
      to.
    - [yjs_prot_encode]: a sender that holds the certificates of a batch's
      per-char expansion owns the protocol for the batch's encoding.

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

(** [decodes_to d inputs]: the bytes [d] decode to the batch [inputs], up to
    the types of the structs that have an origin, which the bytes do not
    carry ([same_wire_struct]). *)
Definition decodes_to (d : list u8) (inputs : list Input) : Prop :=
  ∃ decoded : list Input,
    decode d = Some decoded ∧ Forall2 same_wire_struct decoded inputs.

(** The wire protocol: these bytes decode to an honest batch every per-char
    operation of which is a point of the global history [γh]. Per character,
    via [expand_inputs], because that is what the ghost history holds and
    what [wp_Transaction__applyUpdate] consumes. Persistent, as [ws_prot]
    must be (one message is delivered to every member of a room). *)
Definition yjs_prot (γh : history_names) (d : list u8) : iProp Σ :=
  ∃ inputs : list Input,
    ⌜decodes_to d inputs⌝ ∗ ⌜update_wf inputs⌝ ∗
    is_pending_certified γh (expand_inputs inputs).

(** [units_surrogate_free units]: none of the code units lies in the UTF-16
    surrogate range D800-DFFF. *)
Definition units_surrogate_free (units : list w16) : Prop :=
  ∀ unit, unit ∈ units -> ¬ (0xD800 ≤ uint.Z unit ≤ 0xDFFF)%Z.

(** [structs_surrogate_free structs]: no code unit of the batch is a
    surrogate. *)
Definition structs_surrogate_free (structs : list Input) : Prop :=
  ∀ struct, struct ∈ structs -> units_surrogate_free (in_content struct.2).

(** The pure contract between the two halves of the codec, for the abstract
    [encode] the deployment's encoder is trusted against ([encoder_spec]):
    the encoding of a surrogate-free batch whose characters are well formed
    decodes to characters of the batch. Well-formedness is a premise because
    a struct whose clocks would pass 2^64 does not come back as its
    characters: the model counts clocks in [nat], the decoder in machine
    words. *)
Definition codec_roundtrip (encode : list Input -> list u8) : Prop :=
  ∀ structs, structs_surrogate_free structs -> update_wf (expand_inputs structs) ->
    ∃ inputs, decodes_to (encode structs) inputs ∧ inputs ⊆ expand_inputs structs.

(* ===== lemmas ============================================================= *)

#[global] Instance yjs_prot_persistent γh d : Persistent (yjs_prot γh d).
Proof. apply _. Qed.

(** What [decode] reports is what the bytes decode to. *)
Lemma decodes_to_decoded (d : list u8) (decoded : list Input) :
  decode d = Some decoded -> decodes_to d decoded.
Proof. move=> Hdecode. exists decoded. split; [exact Hdecode | exact (same_wire_struct_refl decoded)]. Qed.

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
  destruct (Hroundtrip structs Hfree Hwf) as (inputs & Hdecodes & Hinputs).
  have Hone : ∀ y, y ∈ inputs -> length (in_content y.2) = 1%nat.
  { move=> y Hy. exact (expand_inputs_unit_content structs y (Hinputs y Hy)). }
  iIntros "#Hcerts".
  iExists inputs. iSplit; first done.
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
