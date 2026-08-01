(** Trusted ws FFI model of the [wsnet] Go package.

    [wsnet] is cert-yjs's Go realization of the connection-oriented network FFI
    (wsnet/wsnet.go); goose maps the package to the ws FFI (its declfilter
    config marks the API trusted), so the generated New.code....wsnet
    references the [ⁱᵐᵖˡ] definitions below.

    Modeled on the [grovenet] trusted file, with the same payload calling
    convention: [WsSendOp] takes and [WsRecvOp] returns the payload as a
    [go_string] literal, so the slice payload is marshalled with [Convert] (WP
    lemmas: [wp_bytes_to_string] / [wp_string_to_bytes] in
    New.golang.theory.string). [WsAcceptOp] additionally returns the
    connection's request path, which the opening handshake carries. *)
From New.golang Require Import defn.
From New.goose_lang.ffi.ws_ffi Require Import impl.

#[global]
Existing Instances ws_op ws_model.

Module wsnet.
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
    λ: "e", Alloc (ExternalOp WsListenOp "e").

  (** Type: func(Listener) (Connection, string) *)
  Definition Acceptⁱᵐᵖˡ : val :=
    λ: "l",
      let: "r" := ExternalOp WsAcceptOp (!"l") in
      let: "socket" := Alloc (Fst "r") in
      ("socket", Snd "r").

  (** Type: func(uint64, string) (bool, Connection) *)
  Definition Connectⁱᵐᵖˡ : val :=
    λ: "e" "path",
      let: "c" := ExternalOp WsConnectOp ("e", "path") in
      let: "err" := Fst "c" in
      let: "socket" := Alloc (Snd "c") in
      ("err", "socket").

  (** Type: func(Connection, []byte) bool *)
  Definition Sendⁱᵐᵖˡ : val :=
    λ: "c" "m",
      let: "data" := Convert (go.SliceType go.byte) go.string "m" in
      ExternalOp WsSendOp (!"c", "data").

  (** Type: func(Connection) (bool, []byte) *)
  Definition Receiveⁱᵐᵖˡ : val :=
    λ: "c",
      let: "r" := ExternalOp WsRecvOp (!"c") in
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
End wsnet.
