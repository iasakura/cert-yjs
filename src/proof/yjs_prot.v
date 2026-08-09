(** The Yjs wire protocol (issue #107, W3b): what every message on the wire
    satisfies, and the codec specification the server is verified against.

    API
    - [update_wf inputs]: the pure honesty facts of a batch (the 2^64
      no-wrap seam per struct, and [is_pending_rooted]: head structs target
      a named root).
    - [yjs_prot decode γh d]: the deployment's [ws_prot]. The bytes decode
      (under the abstract [decode] the deployment is parameterized by) to an
      honest batch whose per-char expansion is certified against the global
      history [γh]; exactly the premises [wp_Doc__ApplySyncUpdate] consumes,
      so a receiver can apply any message it is handed with no further
      hypotheses. Persistent.
    - [codec_spec decode f]: the Go codec value [f] meets [decode]. The
      deployment's [yjs.WireCodec] is TRUSTED to meet it (the same boundary
      codec.go already is, now stated instead of implicit); a future
      goose-translated codec discharges it.

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

Notation A := go_string.

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

(** What an HONEST batch satisfies beyond certification: the 2^64 no-wrap
    seam (per struct, clock plus content length fits a word) and rootedness
    (a head struct names a root type). Facts about the peer's output, so they
    ride the wire protocol rather than the server's hypotheses. *)
Definition update_wf (inputs : list Input) : Prop :=
  (∀ x : Input, x ∈ inputs ->
     (Z.of_nat (clock (in_id x.2)) + Z.of_nat (length (in_content x.2)) < 2^64)%Z) /\
  is_pending_rooted inputs.

(** The wire protocol: these bytes decode to an honest batch every per-char
    operation of which is a point of the global history [γh]. Per character,
    via [expand_inputs], because that is what the ghost history holds and
    what [wp_store__applyUpdate_certs] consumes. Persistent, as [ws_prot]
    must be (one message is delivered to every member of a room). *)
Definition yjs_prot (γh : history_names) (d : list u8) : iProp Σ :=
  ∃ inputs : list Input,
    ⌜decode d = Some inputs⌝ ∗ ⌜update_wf inputs⌝ ∗
    is_pending_certified γh (expand_inputs inputs).

#[global] Instance yjs_prot_persistent γh d : Persistent (yjs_prot γh d).
Proof. apply _. Qed.

End yjs_prot.

Section codec_spec.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.

Notation P := go_string.

Local Notation TId := (TypeId P).

Local Notation Input := (TId * IntegrateInput (A := A))%type.

Context (decode : list u8 -> option (list Input)).

(** The Go codec value [f] meets the abstract [decode]: on any byte slice it
    reports exactly whether [decode] succeeds, and on success returns a
    struct slice denoting the decoded batch. *)
Definition codec_spec (f : func.t) : iProp Σ :=
  □ (∀ (s : slice.t) (dq : dfrac) (data : list u8),
      {{{ s ↦*{dq} data }}}
        #f #s
      {{{ (ok : bool) (sl : slice.t), RET (#ok, #sl);
          s ↦*{dq} data ∗
          if ok
          then ∃ inputs : list Input, ⌜decode data = Some inputs⌝ ∗
               own_update_structs sl (DfracOwn 1) inputs
          else ⌜decode data = None⌝ }}}).

#[global] Instance codec_spec_persistent f : Persistent (codec_spec f).
Proof. apply _. Qed.

End codec_spec.
