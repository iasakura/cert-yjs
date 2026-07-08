(** Trusted Grove FFI model of the [grovenet] Go package.

    [grovenet] is cert-yjs's Go realization of Perennial's Grove network FFI
    (grovenet/grovenet.go, adapted from gokv/grove_ffi); goose maps the package
    to the grove FFI (its declfilter config marks the API trusted), so the
    generated New.code....grovenet references the [ⁱᵐᵖˡ] definitions below.

    This file is modeled on Perennial's
    new/trusted_code/github_com/mit_pdos/gokv/grove_ffi.v, with the payload
    calling convention CORRECTED to match the grove operational semantics
    (Perennial.goose_lang.ffi.grove_ffi.impl): [SendOp] takes and [RecvOp]
    returns the payload as a [go_string] literal ([#data] with [data : list
    w8]), NOT a pointer/length pair, so the slice payload is marshalled with
    [Convert] (whose [StringSemantics] instances give it the byte-slice ↔
    go_string semantics; WP lemmas: [wp_bytes_to_string] /
    [wp_string_to_bytes] in New.golang.theory.string). *)
From New.golang Require Import defn.
From Perennial.goose_lang Require Import ffi.grove_ffi.impl.

#[global]
Existing Instances grove_op grove_model.

Module grovenet.
Section code.
  Context {go_gctx : GoGlobalContext}.

  (** These are pointers in Go ([type Listener *listener] etc.); the pointees
      are opaque to verified code (only the FFI model touches them, via raw
      load of the socket value stored at allocation). *)
  Definition listenerⁱᵐᵖˡ : go.type := unsafe.Pointer.
  Definition Listenerⁱᵐᵖˡ : go.type := unsafe.Pointer.
  Definition connectionⁱᵐᵖˡ : go.type := unsafe.Pointer.
  Definition Connectionⁱᵐᵖˡ : go.type := unsafe.Pointer.

  (** Type: func(uint64) Listener *)
  Definition Listenⁱᵐᵖˡ : val :=
    λ: "e", Alloc (ExternalOp ListenOp "e").

  (** Type: func(Listener) Connection *)
  Definition Acceptⁱᵐᵖˡ : val :=
    λ: "l", Alloc (ExternalOp AcceptOp (!"l")).

  (** Type: func(uint64) (bool, Connection) *)
  Definition Connectⁱᵐᵖˡ : val :=
    λ: "e",
      let: "c" := ExternalOp ConnectOp "e" in
      let: "err" := Fst "c" in
      let: "socket" := Alloc (Snd "c") in
      ("err", "socket").

  (** Type: func(Connection, []byte) bool *)
  Definition Sendⁱᵐᵖˡ : val :=
    λ: "c" "m",
      let: "data" := Convert (go.SliceType go.byte) go.string "m" in
      ExternalOp SendOp (!"c", "data").

  (** Type: func(Connection) (bool, []byte) *)
  Definition Receiveⁱᵐᵖˡ : val :=
    λ: "c",
      let: "r" := ExternalOp RecvOp (!"c") in
      let: "err" := Fst "r" in
      let: "data" := Convert go.string (go.SliceType go.byte) (Snd "r") in
      ("err", "data").
End code.

(** Value-model types for the trusted go.types above (referenced by the
    generated Assumptions classes' [go.TypeReprUnderlying] fields and by
    downstream generatedproof files). All four are pointers/opaque, so [loc]. *)
Module listener.
  Definition t := loc.
End listener.
Module Listener.
  Definition t := loc.
End Listener.
Module connection.
  Definition t := loc.
End connection.
Module Connection.
  Definition t := loc.
End Connection.
End grovenet.
