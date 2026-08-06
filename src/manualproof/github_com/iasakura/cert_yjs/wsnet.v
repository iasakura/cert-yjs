(** Manual proof layer for the trusted [wsnet] package (the ws FFI
    realization): New-style WP wrappers for Listen/Accept/Connect/Send/Receive,
    delegating to the ws lifting lemmas
    (New.goose_lang.ffi.ws_ffi.ws_ffi: [wp_WsListenOp] / [wp_WsConnectOp] /
    [wp_WsAcceptOp] / [wp_WsSendOp] / [wp_WsRecvOp]), with the payload
    marshalled between New byte slices and go_string literals
    ([wp_bytes_to_string] / [wp_string_to_bytes], New.golang.theory.string).

    Listener / Connection handles are pointers to write-once cells holding the
    raw socket value; the cells are persisted at allocation
    ([heap_pointsto_persist]), so the handles ([is_Listener] /
    [is_Connection]) are persistent and freely shared. The cursors
    ([own_send_cursor] / [own_recv_cursor]) are the exclusive part and are
    threaded explicitly.

    The point of the layer, versus the grovenet one: [wp_Accept] returns a SEND
    cursor as well as a receive cursor, so a server can be proved to answer a
    connection it accepted without any resource coming from the peer. *)
Require Export New.proof.ws_prelude.
Require Export New.golang.theory.
Require Export New.trusted_code.github_com.iasakura.cert_yjs.wsnet.
From New.goose_lang.ffi.ws_ffi Require Import ws_ffi.

Section wrappers.
Context {Σ : gFunctors} {hG : heapGS Σ}.
Context {sem : go.Semantics}.

Set Default Proof Using "Type*".

(** Persistent handle for a [wsnet.Listener]: a pointer to the (write-once,
    persisted) cell holding the listen socket for endpoint [e]. *)
Definition is_Listener (l : loc) (e : ws_endpoint) : iProp Σ :=
  heap_pointsto l DfracDiscarded (listen_socket e).

(** Persistent handle for a [wsnet.Connection]: a pointer to the cell holding
    this side's channel pair, [sc] to send on and [rc] to receive from. *)
Definition is_Connection (c : loc) (sc rc : chan_id) : iProp Σ :=
  heap_pointsto c DfracDiscarded (connection sc rc).

#[global] Instance is_Listener_persistent l e : Persistent (is_Listener l e).
Proof. apply _. Qed.
#[global] Instance is_Connection_persistent c sc rc : Persistent (is_Connection c sc rc).
Proof. apply _. Qed.

Lemma wp_Listen (host : w64) :
  {{{ True }}}
    wsnet.Listenⁱᵐᵖˡ #host
  {{{ (l : loc), RET #l; is_Listener l host }}}.
Proof.
  wp_start as "_".
  iApply wp_fupd.
  wp_pures.
  wp_apply wp_WsListenOp.
  wp_apply wp_alloc_untyped.
  iIntros (l) "Hl".
  iMod (heap_pointsto_persist with "Hl") as "Hl".
  iModIntro. iApply "HΦ". iFrame.
Qed.

(** [Accept]: hands out BOTH cursors of the accepted connection, plus the path
    the peer connected to, out of the opening handshake. Nothing is required of
    the peer. *)
Lemma wp_Accept (l : loc) (e : ws_endpoint) :
  {{{ is_Listener l e }}}
    wsnet.Acceptⁱᵐᵖˡ #l
  {{{ (c : loc) (sc rc : chan_id) (path : go_string), RET (#c, #path);
      is_Connection c sc rc ∗ own_send_cursor sc 0 ∗ own_recv_cursor rc 0 }}}.
Proof.
  wp_start as "#Hl".
  iEval (rewrite /is_Listener) in "Hl".
  iApply wp_fupd.
  wp_pures.
  wp_apply (Perennial.goose_lang.lifting.wp_load _ _ _ DfracDiscarded (listen_socket e) with "[$Hl]").
  iIntros "_".
  wp_apply wp_WsAcceptOp.
  iIntros (sc rc path) "[Hsc Hrc]".
  wp_pures.
  wp_apply wp_alloc_untyped.
  iIntros (c) "Hc".
  iMod (heap_pointsto_persist with "Hc") as "Hc".
  wp_pures.
  iModIntro. iApply ("HΦ" $! c sc rc path). iFrame.
Qed.

(** [Connect]: allocates the connecting side's cursors and announces [path]. *)
Lemma wp_Connect (host : w64) (path : go_string) :
  {{{ True }}}
    wsnet.Connectⁱᵐᵖˡ #host #path
  {{{ (err : bool) (c : loc) (sc rc : chan_id), RET (#err, #c);
      if err then True
      else is_Connection c sc rc ∗ own_send_cursor sc 0 ∗ own_recv_cursor rc 0 }}}.
Proof.
  wp_start as "_".
  iApply wp_fupd.
  wp_pures.
  wp_apply wp_WsConnectOp.
  iIntros (err sc rc) "Hcur".
  destruct err.
  - wp_pures.
    wp_apply wp_alloc_untyped.
    iIntros (c) "Hc".
    wp_pures.
    iModIntro. by iApply ("HΦ" $! true c sc rc).
  - wp_pures.
    wp_apply wp_alloc_untyped.
    iIntros (c) "Hc".
    iMod (heap_pointsto_persist with "Hc") as "Hc".
    wp_pures.
    iModIntro. iApply ("HΦ" $! false c sc rc). iFrame.
Qed.

(** [Send]: the payload slice is read (via the byte-slice to go_string
    conversion) and appended at the send cursor. [err = false] guarantees the
    message went out as message [n]; [err = true] leaves it undetermined (the
    model's late failure), which the disjunction reflects. *)
Lemma wp_Send (c : loc) (sc rc : chan_id) (n : nat) (s : slice.t) (dq : dfrac)
    (data : list w8) :
  {{{ is_Connection c sc rc ∗ s ↦*{dq} data ∗ own_send_cursor sc n ∗
      ws_prot data }}}
    wsnet.Sendⁱᵐᵖˡ #c #s
  {{{ (err : bool), RET #err;
      s ↦*{dq} data ∗
      ((⌜err = true⌝ ∗ own_send_cursor sc n) ∨
       (own_send_cursor sc (S n) ∗ is_chan_msg sc n data)) }}}.
Proof.
  wp_start as "(#Hc & Hs & Hcur & #Hpd)".
  iEval (rewrite /is_Connection) in "Hc".
  wp_pures.
  wp_apply (wp_bytes_to_string with "[$Hs]").
  iIntros "Hs".
  wp_pures.
  wp_apply (Perennial.goose_lang.lifting.wp_load _ _ _ DfracDiscarded (connection sc rc) with "[$Hc]").
  iIntros "_".
  wp_pures.
  wp_apply (wp_WsSendOp with "[$Hcur $Hpd]").
  iIntros (err_early err_late) "Hcur".
  iApply "HΦ". iFrame "Hs".
  destruct err_early; simpl.
  - iLeft. by iFrame.
  - iRight. by iFrame.
Qed.

(** [Recv]: consumes at the receive cursor. On success the returned slice is
    fresh and holds message [n] of [rc]; the cursor advances, so the caller
    processes the peer's stream in order and exactly once. *)
Lemma wp_Receive (c : loc) (sc rc : chan_id) (n : nat) :
  {{{ is_Connection c sc rc ∗ own_recv_cursor rc n ∗ ws_env_preserves ⊤ }}}
    wsnet.Receiveⁱᵐᵖˡ #c
  {{{ (err : bool) (s : slice.t) (data : list w8), RET (#err, #s);
      s ↦* data ∗ own_slice_cap w8 s (DfracOwn 1) ∗
      (if err then own_recv_cursor rc n
       else own_recv_cursor rc (S n) ∗ is_chan_msg rc n data ∗ ws_prot data) }}}.
Proof.
  wp_start as "(#Hc & Hcur & #Henv)".
  iEval (rewrite /is_Connection) in "Hc".
  wp_pures.
  wp_apply (Perennial.goose_lang.lifting.wp_load _ _ _ DfracDiscarded (connection sc rc) with "[$Hc]").
  iIntros "_".
  wp_apply (wp_WsRecvOp with "[$Hcur $Henv]").
  iIntros (err data) "Hcur".
  wp_pures.
  wp_apply wp_string_to_bytes.
  iIntros (sl) "[Hsl Hcap]".
  wp_pures.
  iApply ("HΦ" $! err sl data). iFrame.
Qed.

End wrappers.
