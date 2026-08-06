(** FFI module for a connection-oriented network: ordered, reliable,
    exactly-once message streams (what TCP, and hence WebSocket, actually
    provides). [Trusted definitions!]

    Staging note: this file is developed inside cert-yjs (so it lands under the
    [New] logical prefix) and belongs in the perennial fork at
    [src/goose_lang/ffi/ws_ffi/impl.v]; moving it only rewrites the intra-FFI
    [New.goose_lang.ffi.ws_ffi] requires to [Perennial.goose_lang.ffi.ws_ffi].

    Why not the grove FFI (Perennial.goose_lang.ffi.grove_ffi): grove models
    *endpoints with mailboxes*, not connections. [AcceptOp] there yields no
    resources about the peer and [SendOp] needs the RECEIVER's mailbox
    points-to, so a server cannot be proved to answer a connection it accepted
    unless the peer is itself modeled code that hands its mailbox invariant
    over. That blocks any server whose clients are outside the model. Here a
    connection is two one-way channels and [WsAcceptOp] hands the acceptor the
    reply channel's send end, which is what a real accept(2) gives you.

    The model in one line: a channel is an append-only sequence of messages
    with a sender-side write cursor and a receiver-side read cursor; sends
    append at the write cursor, receives consume at the read cursor. Ordering
    and exactly-once delivery therefore come from the model rather than from a
    sequence-number layer on the wire (which the Yjs sync protocol has no room
    for). Loss and connection death are modeled as receives that never
    progress: safety only, no liveness. *)
From stdpp Require Import gmap fin_maps.
From RecordUpdate Require Import RecordSet.

From Perennial.Helpers Require Import CountableTactics Transitions Integers ByteString.
From Perennial.goose_lang Require Import lang.

Set Default Proof Using "Type".
(* purely cosmetic, but it makes printing line up with how the code is written *)
Set Printing Projections.

(** * The connection-oriented network extension to GooseLang *)

Inductive WsOp : Set :=
  WsListenOp | WsConnectOp | WsAcceptOp | WsSendOp | WsRecvOp.
#[global]
Instance eq_WsOp : EqDecision WsOp.
Proof. solve_decision. Defined.
#[global]
Instance WsOp_fin : Countable WsOp.
Proof. solve_countable WsOp_rec 5%nat. Qed.

(** [ws_endpoint] corresponds to a host-IP pair, as in grove. *)
Definition ws_endpoint := u64.
(** A [chan_id] names ONE DIRECTION of one connection. A connection is a pair
    of them, and the two peers hold the pair in opposite orientations. *)
Definition chan_id := u64.

Inductive WsVal :=
(** A listening socket bound to [e]. *)
| ListenSocketV (e : ws_endpoint)
(** One endpoint of a connection: [send] is the channel this side appends to,
    [recv] the channel it consumes from. *)
| ConnectionV (send : chan_id) (recv : chan_id)
(** A failed connect. *)
| BadConnectionV.

#[global]
Instance WsVal_eq_decision : EqDecision WsVal.
Proof. solve_decision. Defined.
#[global]
Instance WsVal_countable : Countable WsVal.
Proof.
  refine (inj_countable'
    (λ x, match x with
          | ListenSocketV e => inl e
          | ConnectionV s r => inr $ inl (s, r)
          | BadConnectionV => inr $ inr ()
          end)
    (λ x, match x with
          | inl e => ListenSocketV e
          | inr (inl (s, r)) => ConnectionV s r
          | inr (inr ()) => BadConnectionV
          end)
    _);
  by intros [].
Qed.

Definition ws_op : ffi_syntax.
Proof.
  refine (mkExtOp WsOp _ _ WsVal _ _).
Defined.

(** The global network state.

    - [ws_msgs]: the message at index [n] of channel [c], for every message
      ever put on a channel. Append-only: entries are never removed or
      overwritten, which is what makes "message [n] of [c] was [data]"
      persistent knowledge at the Iris level.
    - [ws_sent]: the sender's write cursor, allocated when the sending side of
      the channel is handed to modeled code.
    - [ws_recvd]: the receiver's read cursor.
    - [ws_ext]: channels whose sending side is the environment, i.e. a peer we
      do not run. [WsRecvOp] produces bytes at receive time on exactly these,
      as permitted by [ws_env_may]. The
      set is explicit rather than derived from "[ws_sent] has no entry",
      because a channel that a connecting peer created is momentarily in that
      state too, between its [WsConnectOp] and the server's [WsAcceptOp], and
      the environment must not be able to forge messages on it.
    - [ws_env_may]: constant, never changed by a step. [ws_env_may M c data]
      reads "with [M] the messages on the wire, a peer we do not run may put
      [data] on channel [c]". [WsRecvOp]'s environment branch is guarded by it,
      so an unmodeled peer is not a source of arbitrary bytes: it is a
      transition system, and this is its send relation. [fun _ _ _ => False]
      closes the network to modeled code, and a Yjs instance lets a peer send
      exactly the encodings of the operations the protocol permits it next.

      It reads the whole of [ws_msgs] and not just the environment's own
      sends, because what a peer may say next depends on what was said TO it:
      a Yjs client's next operation is anchored at operations the server
      relayed to it. Those are on the wire, so they are in [M].
    - [ws_backlog]: per listening endpoint, the connections awaiting accept.
      Each entry is (the connecting side's send channel, its receive channel,
      the request target the connecting side asked for). That target is
      transport data, not application data: WebSocket carries it in the opening
      handshake, so it arrives before any message and there is no way for a
      peer to convey it in-band. It is handed to the acceptor once, at
      [WsAcceptOp], and the model keeps nothing about it afterwards. What an
      application reads into it is not this file's business. *)
Record ws_global_state : Type := {
  ws_msgs : gmap (chan_id * nat) (list u8);
  ws_sent : gmap chan_id nat;
  ws_recvd : gmap chan_id nat;
  ws_ext : gset chan_id;
  ws_backlog : gmap ws_endpoint (list (chan_id * chan_id * go_string));
  ws_env_may : gmap (chan_id * nat) (list u8) -> chan_id -> list u8 -> Prop;
}.

Global Instance ws_global_state_settable : Settable _ :=
  settable! Build_ws_global_state
    <ws_msgs; ws_sent; ws_recvd; ws_ext; ws_backlog; ws_env_may>.

Global Instance ws_global_state_inhabited : Inhabited ws_global_state :=
  populate {| ws_msgs := ∅; ws_sent := ∅; ws_recvd := ∅;
              ws_ext := ∅; ws_backlog := ∅;
              ws_env_may := fun _ _ _ => False |}.

(** There is no per-node state: this FFI is the network and nothing else. *)
Definition ws_node_state : Type := unit.

Definition ws_model : ffi_model.
Proof.
  refine (mkFfiModel ws_node_state ws_global_state _ _).
Defined.

Section ws.
  (* these are local instances on purpose, so that importing this file doesn't
  suddenly cause all FFI parameters to be inferred as the ws model *)
  Existing Instances ws_op ws_model.

  Existing Instances r_mbind r_fmap.
  Context {go_gctx : GoGlobalContext}.

  (** [c] names no channel yet: neither cursor is allocated and no message sits
      on it. Channel allocation steps carry this as a side condition, which is
      also how the WP lemmas get the freshness they need to allocate ghost
      state. *)
  Definition chan_fresh (g : ffi_global_state) (c : chan_id) : Prop :=
    g.(ws_sent) !! c = None ∧ g.(ws_recvd) !! c = None ∧
    c ∉ g.(ws_ext) ∧ (∀ n, g.(ws_msgs) !! (c, n) = None).

  Definition backlog_of (g : ffi_global_state) (e : ws_endpoint) :
      list (chan_id * chan_id * go_string) :=
    default [] (g.(ws_backlog) !! e).

  (** Everything the environment has put on the wire: the messages on channels
      whose sending side is a peer we do not run. This is the environment's
      whole observable state, so [ws_env_may] is a relation over it, and the
      Iris layer indexes its environment coherence predicate by it. *)
  Definition env_msgs (g : ffi_global_state) : gmap (chan_id * nat) (list u8) :=
    filter (fun kv => kv.1.1 ∈ g.(ws_ext)) g.(ws_msgs).


  Definition is_ws_ffi_step (op : WsOp) (v : val) (e' : expr)
    (σ σ' : ffi_state) (g g' : ffi_global_state) : Prop :=
    match op with
    (** [Listen(e)]: binding is pure bookkeeping; the backlog entry is created
        on demand by the first connect. *)
    | WsListenOp =>
        σ = σ' ∧ g = g' ∧ (∀ e, v = #e → e' = (ExtV (ListenSocketV e)))

    (** [Connect(e, path)]: either fail, or allocate the two channels of a
        fresh connection and queue it on [e]'s backlog. The connecting side
        keeps the send cursor of [s] and the receive cursor of [r]; the
        accepting side gets the opposite two at [WsAcceptOp]. *)
    | WsConnectOp =>
        σ = σ' ∧
        (∀ (e : ws_endpoint) (path : go_string), v = (#e, #path)%V →
           (g = g' ∧ e' = Val ((*err*) #true, ExtV BadConnectionV)%V) ∨
           (∃ (s r : chan_id),
              s ≠ r ∧ chan_fresh g s ∧ chan_fresh g r ∧
              g' = (set ws_backlog <[ e := backlog_of g e ++ [(s, r, path)] ]>
                   (set ws_recvd <[ r := 0%nat ]>
                   (set ws_sent <[ s := 0%nat ]> g))) ∧
              e' = Val ((*err*) #false, ExtV (ConnectionV s r))%V))

    (** [Accept(l)]: take the oldest queued connection, or invent one whose far
        side is NOT modeled code (an unverified peer: its send channel goes
        into [ws_ext], so [WsRecvOp] fabricates its bytes). Either way the
        acceptor is handed the send cursor of the reply channel and the receive
        cursor of the peer's channel: accepting a connection grants the right
        to answer it, with no cooperation from the peer.

        Blocking accept is modeled by this step simply not being enabled. *)
    | WsAcceptOp =>
        σ = σ' ∧
        (∀ (e : ws_endpoint), v = ExtV (ListenSocketV e) →
           ∃ (s r : chan_id) (path : go_string),
             g.(ws_sent) !! r = None ∧ g.(ws_recvd) !! s = None ∧
             r ∉ g.(ws_ext) ∧ s ∉ g.(ws_ext) ∧
             ((∃ rest, g.(ws_backlog) !! e = Some ((s, r, path) :: rest) ∧
                       g' = (set ws_backlog <[ e := rest ]>
                            (set ws_recvd <[ s := 0%nat ]>
                            (set ws_sent <[ r := 0%nat ]> g)))) ∨
              (s ≠ r ∧ chan_fresh g s ∧ chan_fresh g r ∧
               g' = (set ws_ext (λ S, {[ s ]} ∪ S)
                    (set ws_recvd <[ s := 0%nat ]>
                    (set ws_sent <[ r := 0%nat ]> g))))) ∧
             e' = Val (ExtV (ConnectionV r s), #path)%V)

    (** [Send(c, data)]: append [data] at the send cursor and advance it.
        Failure is either early (nothing appended) or late (appended, error
        still reported), exactly as in grove: a caller that sees an error
        learns nothing about delivery.

        Sending needs the send cursor, which only the owner of that side of the
        connection has; a program without it is stuck (Panic), which cannot
        happen for programs verified against the WP layer. *)
    | WsSendOp =>
        σ = σ' ∧
        (∀ (s r : chan_id) (data : list u8),
           v = (ExtV (ConnectionV s r), #data)%V →
           match g.(ws_sent) !! s with
           | Some n =>
               (g = g' ∧ e' = Val #true) ∨
               (g.(ws_msgs) !! (s, n) = None ∧
                g' = (set ws_sent <[ s := S n ]>
                     (set ws_msgs <[ (s, n) := data ]> g)) ∧
                ∃ (err_late : bool), e' = Val #err_late)
           | None => g = g' ∧ e' = Panic "invalid"
           end)

    (** [Recv(c)]: consume the message at the read cursor and advance it, or
        report that nothing arrived. The third branch is the environment: on a
        channel in [ws_ext], whatever [env_may_send] permits in the current
        state may show up. It is recorded in [ws_msgs] like any other message,
        so the receiver still gets the persistent "message [n] here was [data]"
        fact, and the peer we do not run is described by a send relation rather
        than by unrestricted nondeterminism.

        Loss, connection death and a slow peer are all the "nothing arrived"
        branch; nothing here ever makes a delivered message un-delivered. *)
    | WsRecvOp =>
        σ = σ' ∧
        (∀ (s r : chan_id),
           v = ExtV (ConnectionV s r) →
           match g.(ws_recvd) !! r with
           | Some n =>
               (g = g' ∧ e' = Val ((*err*) #true, #(@nil u8))%V) ∨
               (∃ data, g.(ws_msgs) !! (r, n) = Some data ∧
                        g' = set ws_recvd <[ r := S n ]> g ∧
                        e' = Val ((*err*) #false, #data)%V) ∨
               (r ∈ g.(ws_ext) ∧ g.(ws_msgs) !! (r, n) = None ∧
                ∃ data, g.(ws_env_may) g.(ws_msgs) r data ∧
                        g' = (set ws_recvd <[ r := S n ]>
                             (set ws_msgs <[ (r, n) := data ]> g)) ∧
                        e' = Val ((*err*) #false, #data)%V)
           | None => g = g' ∧ e' = Panic "invalid"
           end)
    end.

  (** ** The model can actually carry traffic

      Nothing in the WP layer needs what follows; it is the argument that those
      specs are not vacuous. [WsSendOp]'s appending branch is guarded by "the
      index at the send cursor is unused", so a state where that guard fails
      would leave only the failing branch enabled: a network that type-checks
      but cannot deliver anything. [ws_wf] rules that out, and is preserved by
      every step (the [ws_wf_step_*] lemmas), starting from the empty network.

      The content is that the message indices present on a channel always form
      an initial segment [0, k), with [k] the send cursor for a channel with a
      modeled sender and the receive cursor for an environment-fed one. *)
  Record ws_wf (g : ffi_global_state) : Prop := {
    (** an environment-fed channel has no modeled sender *)
    wswf_ext_nosend : ∀ c, c ∈ g.(ws_ext) → g.(ws_sent) !! c = None;
    (** a modeled sender has put exactly its cursor's worth of messages out *)
    wswf_sent_seg : ∀ c k, g.(ws_sent) !! c = Some k →
      ∀ n, is_Some (g.(ws_msgs) !! (c, n)) ↔ (n < k)%nat;
    (** an environment-fed channel's messages are fabricated at receive time,
        so they are exactly the ones already consumed *)
    wswf_ext_seg : ∀ c k, c ∈ g.(ws_ext) → g.(ws_recvd) !! c = Some k →
      ∀ n, is_Some (g.(ws_msgs) !! (c, n)) ↔ (n < k)%nat;
    (** a channel with neither carries nothing *)
    wswf_idle_empty : ∀ c, g.(ws_sent) !! c = None → c ∉ g.(ws_ext) →
      ∀ n, g.(ws_msgs) !! (c, n) = None;
  }.

  (** ** How a step moves the environment's view

      The four ways: not at all (most steps), or by one entry (an environment
      receive). Modeled code never moves it, which is what makes the Iris
      layer's [ws_env_coh] stable across everything but that one step. *)
  Lemma env_msgs_same g g' :
    g'.(ws_msgs) = g.(ws_msgs) -> g'.(ws_ext) = g.(ws_ext) ->
    env_msgs g' = env_msgs g.
  Proof. rewrite /env_msgs => -> ->. done. Qed.

  (** Accepting from an unmodeled peer puts a channel into [ws_ext]. It carries
      no message yet, so the environment's view does not move. *)
  Lemma env_msgs_add_ext g g' s :
    g'.(ws_msgs) = g.(ws_msgs) -> g'.(ws_ext) = {[ s ]} ∪ g.(ws_ext) ->
    (forall n, g.(ws_msgs) !! (s, n) = None) ->
    env_msgs g' = env_msgs g.
  Proof.
    rewrite /env_msgs => -> -> Hfresh.
    apply map_filter_ext => [[c n]] d Hd /=.
    split; last set_solver.
    move => /elem_of_union [/elem_of_singleton Hcs|//].
    by rewrite Hcs Hfresh in Hd.
  Qed.

  (** A modeled send lands on a channel the environment does not own. *)
  Lemma env_msgs_insert_nonext g g' c n data :
    c ∉ g.(ws_ext) ->
    g'.(ws_msgs) = <[ (c, n) := data ]> g.(ws_msgs) ->
    g'.(ws_ext) = g.(ws_ext) ->
    env_msgs g' = env_msgs g.
  Proof.
    rewrite /env_msgs => Hc -> ->.
    by rewrite map_filter_insert_not' //= => ?.
  Qed.

  (** An environment receive is the one step that grows it. *)
  Lemma env_msgs_insert_ext g g' c n data :
    c ∈ g.(ws_ext) ->
    g'.(ws_msgs) = <[ (c, n) := data ]> g.(ws_msgs) ->
    g'.(ws_ext) = g.(ws_ext) ->
    env_msgs g' = <[ (c, n) := data ]> (env_msgs g).
  Proof.
    rewrite /env_msgs => Hc -> ->.
    by rewrite map_filter_insert_True.
  Qed.

  Lemma ws_wf_empty envmay :
    ws_wf {| ws_msgs := ∅; ws_sent := ∅; ws_recvd := ∅;
             ws_ext := ∅; ws_backlog := ∅; ws_env_may := envmay |}.
  Proof.
    split; simpl.
    - set_solver.
    - move=> c k. rewrite lookup_empty //.
    - set_solver.
    - move=> c _ _ n. rewrite lookup_empty //.
  Qed.

  (** The payoff: in a well-formed network the send cursor always points at an
      unused index, which is exactly [WsSendOp]'s appending-branch guard. *)
  Lemma ws_send_enabled g s n :
    ws_wf g -> g.(ws_sent) !! s = Some n -> g.(ws_msgs) !! (s, n) = None.
  Proof.
    move=> Hwf Hs.
    destruct (g.(ws_msgs) !! (s, n)) as [d|] eqn:Hm; last done.
    have [Hlt _] := wswf_sent_seg g Hwf s n Hs n.
    have Hcontra : (n < n)%nat by apply Hlt; rewrite Hm; eauto.
    lia.
  Qed.

  (** ** The environment's send relation is a constant of the run

      No step touches [ws_env_may]. The Iris layer pins it in the state
      interpretation, because [ws_env_preserves] quantifies over states and
      would otherwise be asked to hold for a state whose field permits
      everything, which nothing can discharge. Carrying the equation across a
      step needs these. *)
  Lemma ws_env_may_step_listen (a : ws_endpoint) e' sigma sigma' g g' :
    is_ws_ffi_step WsListenOp #a e' sigma sigma' g g' ->
    g'.(ws_env_may) = g.(ws_env_may).
  Proof. intros [_ [<- _]]. done. Qed.

  Lemma ws_env_may_step_connect (a : ws_endpoint) (path : go_string) e' sigma sigma' g g' :
    is_ws_ffi_step WsConnectOp (#a, #path)%V e' sigma sigma' g g' ->
    g'.(ws_env_may) = g.(ws_env_may).
  Proof.
    intros [_ Hstep]. specialize (Hstep a path eq_refl).
    destruct Hstep as [[<- _] | (sc & rc & _ & _ & _ & -> & _)]; done.
  Qed.

  Lemma ws_env_may_step_accept (a : ws_endpoint) e' sigma sigma' g g' :
    is_ws_ffi_step WsAcceptOp (ExtV (ListenSocketV a)) e' sigma sigma' g g' ->
    g'.(ws_env_may) = g.(ws_env_may).
  Proof.
    intros [_ Hstep]. specialize (Hstep a eq_refl).
    destruct Hstep as (s' & r' & path' & _ & _ & _ & _ & Hbr & _).
    destruct Hbr as [(rest & _ & ->) | (_ & _ & _ & ->)]; done.
  Qed.

  Lemma ws_env_may_step_send (s r : chan_id) (data : list u8) e' sigma sigma' g g' :
    is_ws_ffi_step WsSendOp (ExtV (ConnectionV s r), #data)%V e' sigma sigma' g g' ->
    g'.(ws_env_may) = g.(ws_env_may).
  Proof.
    intros [_ Hstep]. specialize (Hstep s r data eq_refl).
    destruct (g.(ws_sent) !! s) as [n|]; last first.
    { destruct Hstep as [<- _]. done. }
    destruct Hstep as [[<- _] | (_ & -> & _)]; done.
  Qed.

  Lemma ws_env_may_step_recv (s r : chan_id) e' sigma sigma' g g' :
    is_ws_ffi_step WsRecvOp (ExtV (ConnectionV s r)) e' sigma sigma' g g' ->
    g'.(ws_env_may) = g.(ws_env_may).
  Proof.
    intros [_ Hstep]. specialize (Hstep s r eq_refl).
    destruct (g.(ws_recvd) !! r) as [n|]; last first.
    { destruct Hstep as [<- _]. done. }
    destruct Hstep
      as [[<- _] | [(d & _ & -> & _) | (_ & _ & (d & _ & -> & _))]]; done.
  Qed.

  Lemma ws_wf_step_listen (a : ws_endpoint) e' sigma sigma' g g' :
    is_ws_ffi_step WsListenOp #a e' sigma sigma' g g' -> ws_wf g -> ws_wf g'.
  Proof. intros (_ & <- & _) Hwf. exact Hwf. Qed.

  Lemma ws_wf_step_connect (a : ws_endpoint) (path : go_string) e' sigma sigma' g g' :
    is_ws_ffi_step WsConnectOp (#a, #path)%V e' sigma sigma' g g' -> ws_wf g -> ws_wf g'.
  Proof.
    intros (_ & Hstep) Hwf.
    destruct (Hstep a path eq_refl) as [(<- & _) | (s & r & Hne & Hs & Hr & -> & _)];
      first exact Hwf.
    destruct Hs as (Hs1 & Hs2 & Hs3 & Hs4).
    destruct Hr as (Hr1 & Hr2 & Hr3 & Hr4).
    split; simpl.
    - intros c Hc. rewrite lookup_insert_ne; last (intros ->; set_solver).
      by apply (wswf_ext_nosend _ Hwf).
    - intros c k. destruct (decide (s = c)) as [<-|Hcs].
      + rewrite lookup_insert_eq. intros [= <-] n. rewrite Hs4.
        split; [by intros [? ?] | lia].
      + rewrite lookup_insert_ne //. by apply (wswf_sent_seg _ Hwf).
    - intros c k Hc. rewrite lookup_insert_ne; last (intros ->; set_solver).
      by apply (wswf_ext_seg _ Hwf).
    - intros c Hc Hcext n. destruct (decide (r = c)) as [<-|Hcr].
      { by rewrite Hr4. }
      destruct (decide (s = c)) as [<-|Hcs].
      { rewrite lookup_insert_eq in Hc. done. }
      rewrite lookup_insert_ne // in Hc. by apply (wswf_idle_empty _ Hwf).
  Qed.

  Lemma ws_wf_step_accept (a : ws_endpoint) e' sigma sigma' g g' :
    is_ws_ffi_step WsAcceptOp (ExtV (ListenSocketV a)) e' sigma sigma' g g' ->
    ws_wf g -> ws_wf g'.
  Proof.
    intros (_ & Hstep) Hwf.
    destruct (Hstep a eq_refl)
      as (s & r & path & Hr1 & Hs1 & Hrext & Hsext & Hbranch & _).
    (* the reply channel carries nothing yet, in either branch *)
    assert (Hnomsg_r : forall n, g.(ws_msgs) !! (r, n) = None)
      by (by apply (wswf_idle_empty _ Hwf)).
    destruct Hbranch
      as [(rest & _ & ->) | (Hne & (Hs1' & Hs2' & Hs3' & Hs4') & _ & ->)];
      split; simpl.
    (* accepted from the backlog: the peer is modeled code *)
    - intros c Hc. rewrite lookup_insert_ne; last (intros ->; set_solver).
      by apply (wswf_ext_nosend _ Hwf).
    - intros c k. destruct (decide (r = c)) as [<-|Hcr].
      + rewrite lookup_insert_eq. intros [= <-] n. rewrite Hnomsg_r.
        split; [by intros [? ?] | lia].
      + rewrite lookup_insert_ne //. by apply (wswf_sent_seg _ Hwf).
    - intros c k Hc. rewrite lookup_insert_ne; last (intros ->; set_solver).
      by apply (wswf_ext_seg _ Hwf).
    - intros c Hc Hcext n. destruct (decide (r = c)) as [<-|Hcr].
      { rewrite lookup_insert_eq in Hc. done. }
      rewrite lookup_insert_ne // in Hc. by apply (wswf_idle_empty _ Hwf).
    (* invented for a peer we do not run: its send channel becomes external *)
    - intros c Hc. destruct (decide (s = c)) as [<-|Hcs].
      + rewrite lookup_insert_ne //.
      + rewrite lookup_insert_ne; last (intros ->; set_solver).
        apply (wswf_ext_nosend _ Hwf). set_solver.
    - intros c k. destruct (decide (r = c)) as [<-|Hcr].
      + rewrite lookup_insert_eq. intros [= <-] n. rewrite Hnomsg_r.
        split; [by intros [? ?] | lia].
      + rewrite lookup_insert_ne //. by apply (wswf_sent_seg _ Hwf).
    - intros c k Hc. destruct (decide (s = c)) as [<-|Hcs].
      + rewrite lookup_insert_eq. intros [= <-] n. rewrite Hs4'.
        split; [by intros [? ?] | lia].
      + rewrite lookup_insert_ne //. intros Hc2. apply (wswf_ext_seg _ Hwf) => //.
        set_solver.
    - intros c Hc Hcext n. destruct (decide (r = c)) as [<-|Hcr].
      { rewrite lookup_insert_eq in Hc. done. }
      rewrite lookup_insert_ne // in Hc.
      apply (wswf_idle_empty _ Hwf) => //. set_solver.
  Qed.

  Lemma ws_wf_step_send (s r : chan_id) (data : list u8) e' sigma sigma' g g' :
    is_ws_ffi_step WsSendOp (ExtV (ConnectionV s r), #data)%V e' sigma sigma' g g' ->
    ws_wf g -> ws_wf g'.
  Proof.
    intros (_ & Hstep) Hwf.
    specialize (Hstep s r data eq_refl).
    remember (g.(ws_sent) !! s) as os eqn:Hs. symmetry in Hs.
    destruct os as [k|]; last (destruct Hstep as (<- & _); exact Hwf).
    destruct Hstep as [(<- & _) | (Hfresh & -> & _)]; first exact Hwf.
    (* an external channel has no send cursor, so it is never [s] *)
    assert (Hsne : forall c, c ∈ g.(ws_ext) -> s ≠ c).
    { intros c Hc ->. by rewrite (wswf_ext_nosend _ Hwf c Hc) in Hs. }
    split; simpl.
    - intros c Hc. rewrite lookup_insert_ne; last by apply Hsne.
      by apply (wswf_ext_nosend _ Hwf).
    - intros c j. destruct (decide (s = c)) as [<-|Hcs].
      + rewrite lookup_insert_eq. intros [= <-] n.
        destruct (decide (n = k)) as [->|Hnk].
        * rewrite lookup_insert_eq. split; [lia | by eauto].
        * rewrite lookup_insert_ne; last (intros [= ?]; done).
          rewrite (wswf_sent_seg _ Hwf s k Hs n). lia.
      + rewrite lookup_insert_ne //. intros Hc n.
        rewrite lookup_insert_ne; last (intros [= ?]; done).
        by apply (wswf_sent_seg _ Hwf).
    - intros c j Hc Hrc n. rewrite lookup_insert_ne; last first.
      { intros [= ? ?]. by apply (Hsne c Hc). }
      by apply (wswf_ext_seg _ Hwf c j).
    - intros c Hc Hcext n.
      assert (Hne : s ≠ c).
      { intros ->. rewrite lookup_insert_eq in Hc. done. }
      rewrite lookup_insert_ne; last (intros [= ?]; done).
      rewrite lookup_insert_ne // in Hc. by apply (wswf_idle_empty _ Hwf).
  Qed.

  Lemma ws_wf_step_recv (s r : chan_id) e' sigma sigma' g g' :
    is_ws_ffi_step WsRecvOp (ExtV (ConnectionV s r)) e' sigma sigma' g g' ->
    ws_wf g -> ws_wf g'.
  Proof.
    intros (_ & Hstep) Hwf.
    specialize (Hstep s r eq_refl).
    remember (g.(ws_recvd) !! r) as orc eqn:Hr. symmetry in Hr.
    destruct orc as [k|]; last (destruct Hstep as (<- & _); exact Hwf).
    destruct Hstep
      as [(<- & _) | [(d & Hd & -> & _) | (Hrext & Hfresh & (d & _ & -> & _))]];
      first exact Hwf.
    - (* a queued message is consumed: only the read cursor moves *)
      split; simpl; try by apply Hwf.
      intros c j Hc. destruct (decide (r = c)) as [<-|Hcr].
      + (* vacuous: an environment-fed channel never has a pending message *)
        exfalso.
        destruct (wswf_ext_seg _ Hwf r k Hc Hr k) as [Hlt _].
        assert (k < k)%nat by (apply Hlt; rewrite Hd; eauto). lia.
      + rewrite lookup_insert_ne //. by apply (wswf_ext_seg _ Hwf).
    - (* the environment fabricates the next message and it is consumed *)
      assert (Hrs : g.(ws_sent) !! r = None) by (by apply (wswf_ext_nosend _ Hwf)).
      split; simpl.
      + by apply (wswf_ext_nosend _ Hwf).
      + intros c j Hc n. rewrite lookup_insert_ne; last first.
        { intros [= ? ?]. subst c. by rewrite Hrs in Hc. }
        by apply (wswf_sent_seg _ Hwf).
      + intros c j Hc. destruct (decide (r = c)) as [<-|Hcr].
        * rewrite lookup_insert_eq. intros [= <-] n.
          destruct (decide (n = k)) as [->|Hnk].
          { rewrite lookup_insert_eq. split; [lia | by eauto]. }
          rewrite lookup_insert_ne; last (intros [= ?]; done).
          rewrite (wswf_ext_seg _ Hwf r k Hrext Hr n). lia.
        * rewrite lookup_insert_ne //. intros Hc2 n.
          rewrite lookup_insert_ne; last (intros [= ?]; done).
          by apply (wswf_ext_seg _ Hwf).
      + intros c Hc Hcext n. rewrite lookup_insert_ne; last first.
        { intros [= ? ?]. subst c. done. }
        by apply (wswf_idle_empty _ Hwf).
  Qed.

  Definition ffi_step (op : WsOp) (v : val) : transition (state*global_state) expr :=
    '(e', s', w') ← suchThat
      (λ '(σ, g) '(e', σ', w'),
         let _ := σ.(go_state).(go_lctx) in
         let w := g.(global_world) in
         (σ' = σ.(world) ∧ w' = g.(global_world) ∧ e' = ExternalOp op v) ∨
         is_ws_ffi_step op v e' σ.(world) σ' g.(global_world) w')
      (gen:=fallback_genPred _);
  modify (λ '(σ, g), (set world (const s') σ, set global_world (const w') g));;
  ret e'.

  Local Instance ws_semantics : ffi_semantics ws_op ws_model :=
    { ffi_step := ffi_step;
      ffi_crash_step := eq; }. (* there is no per-node state to lose *)
End ws.
