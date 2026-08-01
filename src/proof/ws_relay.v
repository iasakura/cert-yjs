(** The connection-management half of the verified Yjs WebSocket server
    (issue #107, W3a): rooms, the per-room connection table, and relay fan-out,
    over the ws FFI.

    The ownership split is the point, and it is what the ws FFI was built for:

    - [wp_Accept] hands out BOTH cursors of a connection. The RECEIVE cursor
      stays with that connection's own goroutine ([wp_Room__Serve] takes it and
      never shares it), which is why the receive loop needs no lock and reads
      the peer's stream in order and exactly once.
    - The SEND cursors of every connection in a room are collected under the
      room's lock ([room_inv]'s [Hsends]), which is what lets ONE connection's
      goroutine relay to ALL the others. [wp_Room__Join] is where a connection's
      send side is handed over; after it, the joining goroutine no longer owns
      the right to answer its own peer, the room does.

    Sending preserves the shape of [own_conn_send] (a cursor at some point stays
    a cursor at some point), so the fan-out's loop invariant is just [room_inv]'s
    big-op unchanged, and each iteration borrows one entry with
    [big_sepM_lookup_acc].

    Under the grove FFI none of this is expressible: accepting a connection
    grants no right to answer it, so there would be no send cursor to collect.
    See src/goose_lang/ffi/ws_ffi/impl.v's header. *)
From New.proof Require Import proof_prelude.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import wsrelay.
From New.proof.sync_proof Require Import base mutex.
From New.goose_lang.ffi.ws_ffi Require Import ws_ffi.
From New.proof Require Import ws_wire.

Section proof.
Context {Σ : gFunctors} {hG : heapGS Σ}.
Context {sem : go.Semantics}.
Context {sync_pkg : sync.Assumptions}.
Context {wsnet_pkg : wsnet.Assumptions} {wsrelay_pkg : wsrelay.Assumptions}.

(** The protocol every packet in the room satisfies. The room is generic in it;
    the Yjs server instantiates it with "decodes to a batch of ops registered in
    the history". *)
Context (Φw : list w8 -> iProp Σ).
Context `{!∀ data, Persistent (Φw data)}.
Context `{!∀ data, Timeless (Φw data)}.

#[global] Instance : IsPkgInit (iProp Σ) wsnet := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) wsnet := build_get_is_pkg_init_wf.
#[global] Instance : IsPkgInit (iProp Σ) wsrelay := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) wsrelay := build_get_is_pkg_init_wf.

Set Default Proof Using "Type*".

(** The right to answer one connection. The send cursor itself now lives in the
    channel's wire invariant, so what the room holds per connection is
    PERSISTENT: the handle and the fact that the channel carries the protocol.
    Sending is no longer a matter of owning a cursor, it is a matter of
    discharging [Φw data]. *)
Definition is_conn_send (c : loc) : iProp Σ :=
  ∃ (sc rc : chan_id), is_Connection c sc rc ∗ is_chan_wire Φw sc.

#[global] Instance is_conn_send_persistent c : Persistent (is_conn_send c).
Proof. apply _. Qed.

(** The room's lock body: the connection table, and the send side of every
    connection in it. A slice rather than a map: Perennial's [wp_map_for_range]
    consumes the map points-to without returning it, so it cannot iterate a
    table that has to stay fully owned. [slice.for_range] reduces to an
    ordinary indexed loop and has no such problem. *)
Definition room_inv (r : loc) : iProp Σ :=
  ∃ (sl : slice.t) (cs : list loc),
    "Hconnsf" ∷ (r .[(wsrelay.Room.t), "conns"]) ↦ sl ∗
    "Hconns"  ∷ sl ↦* cs ∗
    "Hcap"    ∷ own_slice_cap wsnet.Connection.t sl (DfracOwn 1) ∗
    "Hsends"  ∷ ([∗ list] c ∈ cs, is_conn_send c).

(** Room handle (persistent): the [sync.Mutex] embedded at [&Room.mu] guarding
    [room_inv]. Persistent, so every connection's goroutine holds a copy. *)
Definition is_Room (r : loc) : iProp Σ :=
  "#Hmu" ∷ is_Mutex (r .[(wsrelay.Room.t), "mu"]) (room_inv r).

#[global] Instance is_Room_persistent r : Persistent (is_Room r).
Proof. apply _. Qed.

Lemma wp_NewRoom :
  {{{ is_pkg_init wsrelay }}}
    @! wsrelay.NewRoom #()
  {{{ (r : loc), RET #r; is_Room r }}}.
Proof.
  wp_start.
  wp_alloc r as "Hr".
  iApply wp_fupd. wp_auto.
  iApply "HΦ". iStructNamed "Hr".
  simpl. iMod (init_Mutex with "[$] [-]") as "$"; last done.
  iExists slice.nil, []. iNext. iFrame "conns".
  iSplitR; [by iApply own_slice_nil|].
  iSplitR; [by iApply own_slice_cap_nil|].
  by iApply big_sepL_nil.
Qed.

(** [Join] hands the room the right to answer this connection, and in doing so
    puts the connection under the protocol: the send cursor is consumed into the
    channel's wire invariant, after which sending is no longer a matter of
    owning a cursor but of discharging [Φw]. *)
Lemma wp_Room__Join (r c : loc) (sc rc : chan_id) :
  {{{ is_pkg_init wsrelay ∗ is_Room r ∗
      is_Connection c sc rc ∗ own_send_cursor sc 0 }}}
    r @! (go.PointerType wsrelay.Room) @! "Join" #c
  {{{ RET #(); True }}}.
Proof.
  wp_start as "(#Hroom & #Hconn & Hsend)".
  iMod (chan_wire_alloc Φw sc ⊤ with "Hsend") as "#Hwire".
  wp_auto.
  wp_apply (wp_Mutex__Lock with "[$Hroom]").
  iIntros "[Hlocked Hinv]". iNamed "Hinv".
  wp_auto.
  wp_apply wp_slice_literal. iSplitR; first done. iIntros "%sl0 [Hsl0 _]".
  wp_auto.
  wp_apply (wp_slice_append with "[$Hconns $Hcap $Hsl0]").
  iIntros (sl') "(Hconns & Hcap & _)".
  wp_auto.
  wp_apply (wp_Mutex__Unlock with "[$Hroom $Hlocked Hconnsf Hconns Hcap Hsends]").
  { iNext. iExists sl', (cs ++ [c]).
    iFrame "Hconnsf Hconns Hcap".
    rewrite big_sepL_snoc. iFrame "Hsends".
    iExists sc, rc. iFrame "#". }
  by iApply "HΦ".
Qed.

(** [Broadcast] relays to every connection in the room but [self]. The caller
    must supply [Φw data]: sending is an obligation. It is discharged once and
    reused for the whole fan-out, since the protocol is persistent.

    What the room holds per connection is persistent too, so the loop only reads
    the table; nothing is borrowed and given back.

    The postcondition is only the payload slice. Nothing stronger is available,
    and deliberately so: [Send]'s error is ignored here, as in y-websocket, and
    an error says nothing about delivery either way. *)
Lemma wp_Room__Broadcast (r self : loc) (s : slice.t) (dq : dfrac) (data : list w8) :
  {{{ is_pkg_init wsrelay ∗ is_Room r ∗ s ↦*{dq} data ∗ Φw data }}}
    r @! (go.PointerType wsrelay.Room) @! "Broadcast" #self #s
  {{{ RET #(); s ↦*{dq} data }}}.
Proof.
  wp_start as "(#Hroom & Hs & #HΦw)".
  wp_auto.
  wp_apply (wp_Mutex__Lock with "[$Hroom]").
  iIntros "[Hlocked Hinv]". iNamed "Hinv".
  wp_auto.
  iAssert (∃ (i : w64) (cv : loc),
    "%Hi0" ∷ ⌜0 ≤ sint.Z i⌝ ∗
    "Hi" ∷ i_ptr ↦ i ∗
    "Hcv" ∷ c_ptr ↦ cv ∗
    "Hself" ∷ self_ptr ↦ self ∗
    "Hdata" ∷ data_ptr ↦ s ∗
    "Hconns" ∷ sl ↦* cs ∗
    "Hsends" ∷ ([∗ list] c ∈ cs, is_conn_send c) ∗
    "Hs" ∷ s ↦*{dq} data)%I
    with "[$i $c $self $data $Hconns $Hsends $Hs]" as "IH".
  { iPureIntro. word. }
  wp_for "IH".
  wp_if_destruct.
  - (* relay to connection number [i] *)
    iDestruct (own_slice_len with "Hconns") as %[Hlen Hlen0].
    destruct (cs !! uint.nat i) as [c|] eqn:Hc; last first.
    { exfalso. apply lookup_ge_None in Hc. word. }
    iDestruct (own_slice_elem_acc (sint.Z i) c sl (DfracOwn 1) cs with "Hconns")
      as "[Hel Hgive]".
    { word. }
    { replace (Z.to_nat (sint.Z i)) with (uint.nat i) by word. exact Hc. }
    rewrite decide_True; last word.
    wp_auto.
    iDestruct ("Hgive" with "Hel") as "Hconns".
    rewrite list_insert_id; last first.
    { replace (Z.to_nat (sint.Z i)) with (uint.nat i) by word. exact Hc. }
    wp_if_destruct.
    + (* the message came from this connection: skip it *)
      wp_for_post. iFrame. iPureIntro. word.
    + iDestruct (big_sepL_lookup with "Hsends") as "#Hone"; first exact Hc.
      iDestruct "Hone" as (sc' rc') "[#Hconn' #Hwire']".
      wp_func_call.
      wp_apply (wp_wire_Send with "[$Hconn' $Hwire' $Hs]").
      { iFrame "#". }
      iIntros (err) "Hs".
      wp_auto.
      wp_for_post. iFrame. iPureIntro. word.
  - (* every connection has been offered the message: release the lock *)
    wp_apply (wp_Mutex__Unlock with "[$Hroom $Hlocked Hconnsf Hconns Hcap Hsends]").
    { iNext. iExists sl, cs. iFrame. }
    by iApply "HΦ".
Qed.

(** [Serve] is one connection's receive loop. It owns that connection's RECEIVE
    cursor for the whole run and shares it with nobody, which is what makes the
    peer's stream arrive in order and exactly once with no lock on the read
    path. Its SEND side is not here: [Join] gave it to the room.

    [is_chan_wire Φw rc] is the peer's side of the protocol. For a verified peer
    it was established when that peer joined; for a peer we do not run it is the
    one assumption of the deployment, and this is where it appears. Everything
    the relay itself puts back on the wire is an obligation, discharged below
    from the very fact this hypothesis supplies. *)
Lemma wp_Room__Serve (r c : loc) (sc rc : chan_id) (n : nat) :
  {{{ is_pkg_init wsrelay ∗ is_Room r ∗ is_Connection c sc rc ∗
      is_chan_wire Φw rc ∗ own_recv_cursor rc n }}}
    r @! (go.PointerType wsrelay.Room) @! "Serve" #c
  {{{ RET #(); ∃ n', own_recv_cursor rc n' }}}.
Proof.
  wp_start as "(#Hroom & #Hconn & #Hwire & Hrecv)".
  wp_auto.
  iAssert (∃ (n' : nat), "Hrecv" ∷ own_recv_cursor rc n')%I with "[$Hrecv]" as "IH".
  wp_for "IH".
  wp_func_call.
  wp_apply (wp_wire_Receive with "[$Hconn $Hwire $Hrecv]").
  iIntros (err sl0 dta) "(Hsl & Hcap & Hcur)".
  wp_auto.
  destruct err.
  - (* the peer stopped delivering: hand the cursor back and stop *)
    wp_auto.
    wp_for_post.
    iApply "HΦ". iFrame.
  - iDestruct "Hcur" as "(Hrecv & #Hmsg & #HΦw)".
    wp_auto.
    wp_apply (wp_Room__Broadcast with "[$Hroom $Hsl]").
    { iFrame "#". }
    iIntros "Hsl".
    wp_auto.
    wp_for_post. iFrame.
Qed.

(** The peer's side of the protocol, for a connection we have just accepted.

    This is the one assumption of the deployment, and [Run] is where it belongs:
    the accept loop creates connections, so no per-connection precondition can
    reach them. For a peer running verified code it is discharged (that peer
    established the invariant when it took its own send cursor); for a peer we
    do not run it is assumed.

    Note what assuming it actually says. [is_chan_wire] parks a SEND CURSOR for
    the peer's channel in an invariant, and a channel someone owns the send
    cursor of never has bytes fabricated on it ([wp_WsRecvOp_bounded]). So
    "we trust this peer" is not a vague wish: it is exactly the claim that the
    peer's side of the wire is driven by something that follows the protocol
    rather than by the environment. *)
Definition peer_follows_protocol : iProp Σ :=
  □ (∀ rc : chan_id,
       own_recv_cursor rc 0 ={⊤}=∗ is_chan_wire Φw rc ∗ own_recv_cursor rc 0).

(** [Run] is the accept loop: the composition [Join] and [Serve] are meant to be
    used in. Keeping them separate calls is what leaves room for the sync
    handshake between joining and looping, but nothing should have to remember
    the order, so it is fixed here. *)
Lemma wp_Room__Run (r l : loc) (e : ws_endpoint) :
  {{{ is_pkg_init wsrelay ∗ is_Room r ∗ is_Listener l e ∗ peer_follows_protocol }}}
    r @! (go.PointerType wsrelay.Room) @! "Run" #l
  {{{ RET #(); True }}}.
Proof.
  wp_start as "(#Hroom & #Hl & #Hpeer)".
  wp_auto.
  iAssert (True)%I as "IH"; first done.
  wp_for "IH".
  wp_func_call.
  wp_apply (wp_Accept with "[$Hl]").
  iIntros (c sc rc path) "(#Hconn & Hsend & Hrecv)".
  wp_auto.
  wp_apply (wp_Room__Join with "[$Hroom $Hconn $Hsend]").
  (* the one assumption, taken for this connection *)
  iMod ("Hpeer" with "Hrecv") as "[#Hwire Hrecv]".
  wp_apply (wp_fork with "[Hrecv]").
  { wp_apply (wp_Room__Serve with "[$Hroom $Hconn $Hwire $Hrecv]"). auto. }
  wp_for_post. iFrame.
Qed.

End proof.
