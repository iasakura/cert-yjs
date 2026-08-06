(** W1 acceptance demo for the ws (connection-oriented) FFI: verify the
    [wsecho] package, the smallest program that ACCEPTS a connection and
    ANSWERS it, against the ws network model, via the trusted [wsnet] package
    and its WP wrappers
    (New.manualproof.github_com.iasakura.cert_yjs.wsnet).

    This is the point of the whole FFI. The grovenet ping-pong demo
    (src/proof/demo/pingpong.v) deliberately stops short of an echo server:
    under the grove model, sending to the peer needs the peer's mailbox
    points-to, which [wp_AcceptOp] does not give and which only a modeled,
    cooperating peer could escrow. Here [wp_Accept] returns the send cursor of
    the reply channel, so the echo is provable with NO hypothesis about who
    connected. *)
From New.proof Require Import proof_prelude.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import wsecho.
From New.goose_lang.ffi.ws_ffi Require Import ws_ffi.

Section proof.
Context {Σ : gFunctors} {hG : heapGS Σ}.
Context {sem : go.Semantics}.
Context {wsnet_pkg : wsnet.Assumptions} {wsecho_pkg : wsecho.Assumptions}.

#[global] Instance : IsPkgInit (iProp Σ) wsnet := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) wsnet := build_get_is_pkg_init_wf.
#[global] Instance : IsPkgInit (iProp Σ) wsecho := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) wsecho := build_get_is_pkg_init_wf.

Set Default Proof Using "Type*".

(** [ServeEcho] accepts a connection and echoes its first message back. On
    success ([err = false]) the two persistent message facts say precisely
    that: the bytes sent as message 0 of the reply channel are the bytes
    received as message 0 of the peer's channel.

    Echoing preserves the protocol for the same reason a relay does: what goes
    back out is what came in, so [Send]'s [ws_prot] obligation is discharged by
    the [ws_prot] the receive handed over. *)
Lemma wp_ServeEcho (l : loc) (e : ws_endpoint) :
  {{{ is_pkg_init wsecho ∗ is_Listener l e ∗ ws_env_preserves ⊤ }}}
    @! wsecho.ServeEcho #l
  {{{ (err : bool), RET #err;
      ⌜err = true⌝ ∨
      (∃ (sc rc : chan_id) (data : list w8),
         is_chan_msg rc 0 data ∗ is_chan_msg sc 0 data) }}}.
Proof.
  wp_start as "(#Hl & #Henv)".
  wp_auto.
  wp_func_call.
  wp_apply (wp_Accept with "[$Hl]").
  iIntros (c sc rc path) "(#Hc & Hsc & Hrc)".
  wp_auto.
  wp_func_call.
  wp_apply (wp_Receive with "[$Hc $Hrc $Henv]").
  iIntros (err s data) "(Hs & Hcap & Hcur)".
  destruct err.
  - (* nothing arrived: give up, no echo claimed *)
    wp_auto.
    iApply ("HΦ" $! true). by iLeft.
  - (* echo the received message back on the accepted connection *)
    iDestruct "Hcur" as "(Hrc & #Hmsgin & #Hpd)".
    wp_auto.
    wp_func_call.
    wp_apply (wp_Send with "[$Hc $Hs $Hsc $Hpd]").
    iIntros (errs) "(Hs & Hsend)".
    wp_auto.
    iApply ("HΦ" $! errs).
    iDestruct "Hsend" as "[[-> Hsc] | (Hsc & #Hmsgout)]".
    + by iLeft.
    + iRight. iExists sc, rc, data. iFrame "#".
Qed.

End proof.
