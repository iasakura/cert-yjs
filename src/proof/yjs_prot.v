(** The Yjs wire protocol (issue #107, W3b; issue #131): what every message
    sent over a connection satisfies, and the specification the decoder is
    trusted against.

    API
    - [update_wf inputs] (from [store/model]): the pure honesty facts of a
      batch (the 2^64 no-wrap seam per struct, and [is_pending_rooted]: head
      structs target a named root); they ride the wire protocol rather than
      the server's hypotheses.
    - [decodes_to decode d inputs]: the bytes [d] decode to the batch
      [inputs], up to what the wire does not carry: [decode d] is a batch
      that is, struct by struct, the same encoded struct ([same_encoded_struct],
      [store/model]) as [inputs]. The two differ only in the types of the
      structs that have an origin: the bytes of such a struct do not say
      which type it belongs to, so [decode] reports some type for it, and
      [inputs] has the type the sender integrated it into.
    - [yjs_prot decode γh d]: the deployment's [ws_prot]. The bytes decode
      ([decodes_to]) to an honest batch whose per-char expansion is
      certified against the global history [γh]. A receiver applies that
      batch ([own_update_structs_same_encoded_struct] turns the decoder's slice
      into it), so it can apply any message it is handed with no further
      hypotheses. Persistent.
    - [codec_spec decode f]: the Go decoder value [f] meets [decode]. The
      deployment's [yjs.WireCodec] is TRUSTED to meet it (the same boundary
      codec.go already is, now stated instead of implicit); a future
      goose-translated codec discharges it.

    Laws
    - [decodes_to_decoded]: what [decode] reports is what the bytes decode
      to.

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
    carry ([same_encoded_struct]). *)
Definition decodes_to (d : list u8) (inputs : list Input) : Prop :=
  ∃ decoded : list Input,
    decode d = Some decoded ∧ Forall2 same_encoded_struct decoded inputs.

(** The wire protocol: these bytes decode to an honest batch every per-char
    operation of which is a point of the global history [γh]. Per character,
    via [expand_inputs], because that is what the ghost history holds and
    what [wp_Transaction__applyUpdate] consumes. Persistent, as [ws_prot]
    must be (one message is delivered to every member of a room). *)
Definition yjs_prot (γh : history_names) (d : list u8) : iProp Σ :=
  ∃ inputs : list Input,
    ⌜decodes_to d inputs⌝ ∗ ⌜update_wf inputs⌝ ∗
    is_pending_certified γh (expand_inputs inputs).

(* ===== lemmas ============================================================= *)

#[global] Instance yjs_prot_persistent γh d : Persistent (yjs_prot γh d).
Proof. apply _. Qed.

(** What [decode] reports is what the bytes decode to. *)
Lemma decodes_to_decoded (d : list u8) (decoded : list Input) :
  decode d = Some decoded -> decodes_to d decoded.
Proof. move=> Hdecode. exists decoded. split; [exact Hdecode | exact (same_encoded_struct_refl decoded)]. Qed.

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

(* ===== lemmas ============================================================= *)

#[global] Instance codec_spec_persistent f : Persistent (codec_spec f).
Proof. apply _. Qed.

End codec_spec.
