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

Section proof.
Context {Σ : gFunctors} {hG : heapGS Σ}.
Context {sem : go.Semantics}.
Context {sync_pkg : sync.Assumptions}.
Context {wsnet_pkg : wsnet.Assumptions} {wsrelay_pkg : wsrelay.Assumptions}.

#[global] Instance : IsPkgInit (iProp Σ) wsnet := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) wsnet := build_get_is_pkg_init_wf.
#[global] Instance : IsPkgInit (iProp Σ) wsrelay := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) wsrelay := build_get_is_pkg_init_wf.

Set Default Proof Using "Type*".

(** The right to answer one connection: its handle plus its send cursor,
    wherever that cursor has reached. Sending advances the cursor but keeps this
    shape, which is what makes it a loop invariant for the fan-out. *)
Definition own_conn_send (c : loc) : iProp Σ :=
  ∃ (sc rc : chan_id) (n : nat),
    is_Connection c sc rc ∗ own_send_cursor sc n.

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
    "Hsends"  ∷ ([∗ list] c ∈ cs, own_conn_send c).

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

(** [Join] HANDS OVER the connection's send side to the room. After it the
    caller can no longer answer its own peer; any goroutine in the room can,
    which is the whole point of collecting the cursors under one lock. *)
Lemma wp_Room__Join (r c : loc) (sc rc : chan_id) (n : nat) :
  {{{ is_pkg_init wsrelay ∗ is_Room r ∗
      is_Connection c sc rc ∗ own_send_cursor sc n }}}
    r @! (go.PointerType wsrelay.Room) @! "Join" #c
  {{{ RET #(); True }}}.
Proof.
  wp_start as "(#Hroom & #Hconn & Hsend)".
  wp_auto.
  wp_apply (wp_Mutex__Lock with "[$Hroom]").
  iIntros "[Hlocked Hinv]". iNamed "Hinv".
  wp_auto.
  wp_apply wp_slice_literal. iSplitR; first done. iIntros "%sl0 [Hsl0 _]".
  wp_auto.
  wp_apply (wp_slice_append with "[$Hconns $Hcap $Hsl0]").
  iIntros (sl') "(Hconns & Hcap & _)".
  wp_auto.
  wp_apply (wp_Mutex__Unlock with "[$Hroom $Hlocked Hconnsf Hconns Hcap Hsends Hsend]").
  { iNext. iExists sl', (cs ++ [c]).
    iFrame "Hconnsf Hconns Hcap".
    rewrite big_sepL_snoc. iFrame "Hsends".
    iExists sc, rc, n. iFrame "#∗". }
  by iApply "HΦ".
Qed.

(** [Broadcast] relays to every connection in the room but [self]. The loop
    borrows one connection's send side per iteration and gives it straight
    back: sending advances that cursor, but [own_conn_send] existentially
    quantifies where the cursor is, so the room invariant is unchanged across
    the whole fan-out.

    The postcondition is only the payload slice. Nothing stronger is available,
    and deliberately so: [Send]'s error is ignored here, as in y-websocket, and
    an error says nothing about delivery either way. *)
Lemma wp_Room__Broadcast (r self : loc) (s : slice.t) (dq : dfrac) (data : list w8) :
  {{{ is_pkg_init wsrelay ∗ is_Room r ∗ s ↦*{dq} data }}}
    r @! (go.PointerType wsrelay.Room) @! "Broadcast" #self #s
  {{{ RET #(); s ↦*{dq} data }}}.
Proof.
  wp_start as "(#Hroom & Hs)".
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
    "Hsends" ∷ ([∗ list] c ∈ cs, own_conn_send c) ∗
    "Hs" ∷ s ↦*{dq} data)%I
    with "[$i $c $self $data $Hconns $Hsends $Hs]" as "IH".
  { iPureIntro. word. }
  wp_for "IH".
  wp_if_destruct.
  - (* relay to connection number [i], borrowing its send side and giving it
       straight back *)
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
    + (* relay to it, borrowing its send side and giving it straight back *)
      iDestruct (big_sepL_lookup_acc _ _ _ _ Hc with "Hsends") as "[Hone Hback]".
      iDestruct "Hone" as (sc' rc' n') "[#Hconn' Hsend']".
      wp_func_call.
      wp_apply (wp_Send with "[$Hconn' $Hs $Hsend']").
      iIntros (err) "(Hs & Hres)".
      iAssert (own_conn_send c) with "[Hres]" as "Hone".
      { iDestruct "Hres" as "[[_ H] | [H _]]"; iExists sc', rc', _; iFrame "#∗". }
      iDestruct ("Hback" with "Hone") as "Hsends".
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

    It returns when the peer stops delivering, handing the cursor back at
    whatever point it reached. *)
Lemma wp_Room__Serve (r c : loc) (sc rc : chan_id) (n : nat) :
  {{{ is_pkg_init wsrelay ∗ is_Room r ∗
      is_Connection c sc rc ∗ own_recv_cursor rc n }}}
    r @! (go.PointerType wsrelay.Room) @! "Serve" #c
  {{{ RET #(); ∃ n', own_recv_cursor rc n' }}}.
Proof.
  wp_start as "(#Hroom & #Hconn & Hrecv)".
  wp_auto.
  iAssert (∃ (n' : nat), "Hrecv" ∷ own_recv_cursor rc n')%I with "[$Hrecv]" as "IH".
  wp_for "IH".
  wp_func_call.
  wp_apply (wp_Receive with "[$Hconn $Hrecv]").
  iIntros (err sl0 dta) "(Hsl & Hcap & Hcur)".
  wp_auto.
  destruct err.
  - (* the peer stopped delivering: hand the cursor back and stop *)
    wp_auto.
    wp_for_post.
    iApply "HΦ". iFrame.
  - iDestruct "Hcur" as "(Hrecv & #Hmsg)".
    wp_auto.
    wp_apply (wp_Room__Broadcast with "[$Hroom $Hsl]").
    iIntros "Hsl".
    wp_auto.
    wp_for_post. iFrame.
Qed.

End proof.
