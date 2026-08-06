(** Iris reasoning principles for the ws (connection-oriented network) FFI.

    Three ghost maps track the state of [impl.v]:
    - messages, [(chan, index) ↦□ data], allocated persistent and never
      changed, so "message [n] of channel [c] was [data]" is duplicable
      knowledge that both peers (and any third party told about it) can hold;
    - the send cursors, exclusive: owning [own_send_cursor c n] is the right to
      append to [c], and it is what [wp_WsAcceptOp] hands the acceptor;
    - the receive cursors, exclusive: owning [own_recv_cursor c n] is the right
      to consume from [c], and it pins how far this side has read.

    The reasoning principle that falls out is exactly the one a wire-level
    sequence-number layer would have to build by hand: a successful receive at
    cursor [n] yields [is_chan_msg c n data] and advances to [n+1], so message
    handling is in order and exactly once, with no sequence numbers on the
    wire. Composing the two peers' facts ([is_chan_msg] agreement) is how a
    receiver learns what the sender sent.

    On top of that sits the protocol, [ws_prot]: what every message on the wire
    satisfies. It is part of the state interpretation rather than a user-level
    invariant, because the authority over "these are all the messages there
    are" is the [ws_msgs] ghost map's auth, which lives in the state
    interpretation and nowhere else. A user-level invariant could only record
    what modeled code put on the wire, and a receiver would then need the
    sender's cursor to know its own message was among them, which is a fact
    about the physical state that no [fupd] can reach. Here a receiver reads
    [ws_prot] straight off the interpretation.

    A peer we do not run is described by two things, [ws_env_may] (impl.v),
    which says what it may send, and [ws_env_preserves], which says what
    sending costs in ghost state. Together they are a simulation: the peer is a
    transition system, [ws_env_coh] is the refinement relation to whatever
    ghost structure describes it, and [ws_env_preserves] is the one-step
    obligation. It is the only assumption here about a system we do not
    verify. *)
From stdpp Require Import gmap fin_maps.
From RecordUpdate Require Import RecordSet.
From iris.proofmode Require Import proofmode.
From Perennial.base_logic Require Import ghost_map.
From Perennial.program_logic Require Import ectx_lifting atomic.

From Perennial.Helpers Require Import CountableTactics Transitions Integers.
From Perennial.goose_lang Require Import lang lifting.
From Perennial.goose_lang Require Import crash_modality.
From New.goose_lang.ffi.ws_ffi Require Export impl.

Set Default Proof Using "Type".
Set Printing Projections.

(** * Semantic interpretation *)
Class wsGS Σ : Type := WsGS {
  #[global] wsG_msgG :: ghost_mapG Σ (chan_id * nat) (list u8);
  #[global] wsG_curG :: ghost_mapG Σ chan_id nat;
  ws_msgs_name : gname;
  ws_sent_name : gname;
  ws_recvd_name : gname;
  (** The protocol: what every message on the wire satisfies. Carried here
      rather than in a user-level invariant because the only authority over
      "these are all the messages there are" is the state interpretation, and
      that is what a receiver needs in order to conclude anything about the
      bytes it just consumed. Sending it is an obligation ([wp_WsSendOp]
      requires it), receiving it is a right ([wp_WsRecvOp] returns it). *)
  ws_prot : list u8 -> iProp Σ;
  (** Persistent: one message is delivered to every member of a room, and the
      state interpretation keeps its copy while a receiver takes one. *)
  #[global] ws_prot_persistent :: forall d, Persistent (ws_prot d);
  (** Environment coherence: what relates the peer we do not run to ghost
      state. Indexed by [env_msgs], the messages the environment has put on
      the wire, so that by construction nothing modeled code does can disturb
      it. See [ws_env_preserves]. *)
  ws_env_coh : gmap (chan_id * nat) (list u8) -> iProp Σ;
}.

Class wsGpreS Σ : Set := {
  #[global] ws_preG_msgG :: ghost_mapG Σ (chan_id * nat) (list u8);
  #[global] ws_preG_curG :: ghost_mapG Σ chan_id nat;
}.

Definition wsΣ : gFunctors :=
  #[ghost_mapΣ (chan_id * nat) (list u8); ghost_mapΣ chan_id nat].

#[global]
Instance subG_wsGpreS Σ : subG wsΣ Σ → wsGpreS Σ.
Proof. solve_inG. Qed.


Section ws.
  (* local instances on purpose, so that importing this file doesn't suddenly
  cause all FFI parameters to be inferred as the ws model *)
  Existing Instances ws_op ws_model.
  Context {go_gctx : GoGlobalContext}.

  Local Program Instance ws_interp : ffi_interp ws_model :=
    {| ffiGlobalGS := wsGS;
       ffiLocalGS _ := ()%type;
       ffi_local_ctx _ _ _ := True%I;
       ffi_global_ctx _ _ g :=
         (ghost_map_auth ws_msgs_name 1 g.(ws_msgs) ∗
          ghost_map_auth ws_sent_name 1 g.(ws_sent) ∗
          ghost_map_auth ws_recvd_name 1 g.(ws_recvd) ∗
          (* a copy of every message fact, so a receiver can extract one
             without holding anything of the sender's *)
          ([∗ map] k ↦ d ∈ g.(ws_msgs), k ↪[ws_msgs_name]□ d) ∗
          (* the protocol, over every message there is. This is the global
             invariant a relay needs: a receiver reads its message's [ws_prot]
             straight out of here, with no cursor of the sender's and no index
             arithmetic, because the authority over [ws_msgs] is right here. *)
          ([∗ map] k ↦ d ∈ g.(ws_msgs), ws_prot d) ∗
          (* the environment's side of the protocol: whatever ghost structure
             describes the peer we do not run, coherent with what that peer
             has put on the wire so far. [ws_env_preserves] is what moves it,
             and lives in the lifting section, since an obligation that opens
             an invariant needs a fancy update and this record has no [invGS]. *)
          ws_env_coh (env_msgs g) ∗
          (* physical well-formedness, needed here to know that a modeled send
             lands outside [ws_ext] and so leaves [env_msgs] alone *)
          ⌜ws_wf g⌝)%I;
       ffi_local_start _ _ _ := True%I;
       ffi_global_start _ _ g :=
         (([∗ map] c ↦ n ∈ g.(ws_sent), c ↪[ws_sent_name] n) ∗
          ([∗ map] c ↦ n ∈ g.(ws_recvd), c ↪[ws_recvd_name] n))%I;
       ffi_restart _ _ _ := True%I;
       ffi_crash_rel Σ hF1 σ1 hF2 σ2 := ⌜ hF1 = hF2 ∧ σ1 = σ2 ⌝%I;
    |}.
End ws.

Section resources.
  Existing Instances ws_op ws_model.
  Context `{!wsGS Σ}.

  (** The right to append to channel [c], whose next index is [n]. *)
  Definition own_send_cursor (c : chan_id) (n : nat) : iProp Σ :=
    c ↪[ws_sent_name] n.
  (** The right to consume from channel [c], which has read [n] messages. *)
  Definition own_recv_cursor (c : chan_id) (n : nat) : iProp Σ :=
    c ↪[ws_recvd_name] n.
  (** Message [n] of channel [c] was [data]. Persistent: messages are never
      removed or rewritten. *)
  Definition is_chan_msg (c : chan_id) (n : nat) (data : list u8) : iProp Σ :=
    (c, n) ↪[ws_msgs_name]□ data.

  #[global] Instance is_chan_msg_persistent c n data : Persistent (is_chan_msg c n data).
  Proof. apply _. Qed.
  #[global] Instance is_chan_msg_timeless c n data : Timeless (is_chan_msg c n data).
  Proof. apply _. Qed.
  #[global] Instance own_send_cursor_timeless c n : Timeless (own_send_cursor c n).
  Proof. apply _. Qed.
  #[global] Instance own_recv_cursor_timeless c n : Timeless (own_recv_cursor c n).
  Proof. apply _. Qed.

  (** Two views of the same wire message agree. This is how a receiver's
      [is_chan_msg] from [wp_WsRecvOp] is matched with the sender's from
      [wp_WsSendOp]. *)
  Lemma is_chan_msg_agree c n d1 d2 :
    is_chan_msg c n d1 -∗ is_chan_msg c n d2 -∗ ⌜d1 = d2⌝.
  Proof.
    iIntros "H1 H2".
    by iDestruct (ghost_map_elem_agree with "H1 H2") as %->.
  Qed.

  Lemma own_send_cursor_exclusive c n1 n2 :
    own_send_cursor c n1 -∗ own_send_cursor c n2 -∗ False.
  Proof.
    iIntros "H1 H2".
    by iDestruct (ghost_map_elem_ne with "H1 H2") as %?.
  Qed.

  Lemma own_recv_cursor_exclusive c n1 n2 :
    own_recv_cursor c n1 -∗ own_recv_cursor c n2 -∗ False.
  Proof.
    iIntros "H1 H2".
    by iDestruct (ghost_map_elem_ne with "H1 H2") as %?.
  Qed.
End resources.

(** * Lifting lemmas *)
Section lifting.
  Existing Instances ws_op ws_model ws_semantics ws_interp.
  Context `{!gooseGlobalGS Σ, !gooseLocalGS Σ} {go_gctx : GoGlobalContext}.
  Local Instance goose_wsGS : wsGS Σ := goose_ffiGlobalGS.

  (** The environment's step, at the Iris level.

      [env_may_send] (impl.v) says which bytes a peer we do not run may put on
      the wire. This says what that costs in ghost state: the coherence
      between that peer and whatever ghost structure describes it survives the
      step, and the bytes satisfy the protocol.

      This is the one assumption in the development about a system we do not
      verify, and discharging it is a simulation argument: [ws_env_coh] is the
      refinement relation, [env_may_send] is the abstract peer's send
      relation, and this is its one-step obligation. For a Yjs peer,
      [ws_env_coh] holds that peer's [own_client_history] and the proof is one
      [history_broadcast].

      It is an update and not an implication because the certificate it
      produces does not exist yet: the ghost history has to be extended to
      record what the environment did, and that extension is where the
      freshness and integration conditions get checked. An implication would
      instead claim the extension had already happened, which nothing did. The
      mask [E] it is stated at is the mask the receive that uses it runs at,
      and is where the instance's own invariant gets opened.

      The protocol facts about everything already on the wire come along as a
      hypothesis. They cost the state interpretation nothing, [ws_prot] being
      persistent, and they are what makes the obligation dischargeable at all:
      a Yjs peer's next operation is anchored at operations the server relayed
      to it, so proving it integrates means first delivering those into that
      peer's ghost history, which needs their certificates. Delivering them at
      that point rather than tracking each arrival is what
      [history_deliver_pending] is for.

      A network closed to modeled code takes [ws_env_may] to be empty, which
      makes this hold vacuously. *)
  Definition ws_env_preserves (E : coPset) : iProp Σ :=
    □ (∀ (g : ws_global_state) (r : chan_id) (n : nat) (data : list u8),
         ⌜g.(ws_env_may) g.(ws_msgs) r data⌝ -∗ ⌜r ∈ g.(ws_ext)⌝ -∗
         ([∗ map] k ↦ d ∈ g.(ws_msgs), ws_prot d) -∗
         ws_env_coh (env_msgs g) ={E}=∗
           ws_env_coh (<[ (r, n) := data ]> (env_msgs g)) ∗ ws_prot data).

  #[global] Instance ws_env_preserves_persistent E :
    Persistent (ws_env_preserves E).
  Proof. apply _. Qed.

  Definition connection (send recv : chan_id) : val :=
    ExtV (ConnectionV send recv).
  Definition listen_socket (e : ws_endpoint) : val :=
    ExtV (ListenSocketV e).
  Definition bad_connection : val :=
    ExtV BadConnectionV.

  (* Lifting automation, as in grove_ffi. *)
  Local Hint Extern 0 (base_reducible _ _ _) => eexists _, _, _, _, _; simpl : core.
  Local Hint Extern 0 (base_reducible_no_obs _ _ _) => eexists _, _, _, _; simpl : core.
  Ltac inv_base_step :=
    repeat match goal with
        | _ => progress simplify_map_eq/= (* simplify memory stuff *)
        | H : to_val _ = Some _ |- _ => apply of_to_val in H
        | H : base_step ?e _ _ _ _ _ _ _ |- _ =>
          rewrite /base_step /= in H;
          monad_inv; repeat (simpl in H; monad_inv)
        | H : ffi_step _ _ _ _ _ |- _ =>
          inversion H; subst; clear H
        | H : prod _ _ |- _ => destruct H
        | H : and _ _ |- _ => destruct H
        | H : ex _ |- _ => destruct H
        | H : ∀ _, (_ = _) → _ |- _ => specialize (H _ ltac:(done))
        | H : ∀ _ _, (_ = _) → _ |- _ => specialize (H _ _ ltac:(done))
        | H : ∀ _ _ _ , (_ = _) → _ |- _ => specialize (H _ _ _ ltac:(done))
        | _ => progress subst
        end.

  Local Lemma wp_WsOp op (v : val) s E Φ :
    ▷ (∀ σ1 g1 e2 σ2 g2 (Hstep : is_ws_ffi_step op v e2 σ1 σ2 g1 g2),
       ffi_local_ctx goose_ffiLocalGS σ1 -∗
       ffi_global_ctx goose_ffiGlobalGS g1 -∗ |NC={E}=>
       (ffi_local_ctx goose_ffiLocalGS σ2 ∗
        ffi_global_ctx goose_ffiGlobalGS g2 ∗
        WP e2 @ s; E {{ Φ }})) -∗
    WP ExternalOp op v @ s; E {{ v, Φ v }}.
  Proof.
    iLöb as "IH".
    iIntros "HΦ".
    iApply wp_lift_step_ncfupd; first by auto.
    iIntros (σ1 g1 ns mj D κ κs nt) "@ Hg".
    iApply ncfupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
    iSplit.
    { iPureIntro. destruct s; try done. apply base_prim_reducible.
      repeat econstructor; simpl.
      { instantiate (1:=(_, _, _)). repeat econstructor. }
      repeat econstructor. }
    iIntros "!>" (v2 σ2 g2 efs Hstep).
    iMod (global_state_interp_le with "Hg") as "Hg".
    { apply step_count_next_incr. }
    apply base_reducible_prim_step in Hstep.
    2:{ repeat econstructor; simpl.
        { instantiate (1:=(_, _, _)). repeat econstructor. }
        repeat econstructor. }
    inv Hstep. simpl in *.
    inv_base_step. monad_inv. simpl in *.
    inv_base_step. monad_inv. destruct H0; inv_base_step.
    { iFrame "∗#%". iMod "Hmask" as "_". iIntros "Hlc". iModIntro.
      by iApply "IH". }
    iMod "Hmask" as "_".
    iDestruct "Hg" as "[Hffi_global Hg]".
    iMod ("HΦ" with "[//] [$] [$]") as "H".
    iDestruct "H" as "(? & ? & ?)".
    iIntros "Hlc". iFrame "∗#%". done.
  Qed.

  Lemma wp_WsListenOp (e : ws_endpoint) s E :
    {{{ True }}}
      ExternalOp WsListenOp #e @ s; E
    {{{ RET listen_socket e; True }}}.
  Proof.
    iIntros (Φ) "_ HΦ". iApply (wp_WsOp with "[-]").
    iIntros "!> * Hl Hg".
    iDestruct "Hg" as "(Hmsgs & Hsent & Hrecvd & #Hmsgfacts & #Hprot & Hcoh & %Hwf)".
    assert (Hwf2 : ws_wf g2) by (eapply ws_wf_step_listen; [exact Hstep | exact Hwf]).
    iModIntro. inv_base_step.
    iFrame "∗#%". iApply wp_value. iFrame. by iApply "HΦ".
  Qed.

  (** [Connect] allocates the connecting side's two cursors. *)
  Lemma wp_WsConnectOp (e : ws_endpoint) (path : go_string) s E :
    {{{ True }}}
      ExternalOp WsConnectOp (#e, #path)%V @ s; E
    {{{ (err : bool) (sc rc : chan_id),
        RET (#err, if err then bad_connection else connection sc rc);
        if err then True else own_send_cursor sc 0 ∗ own_recv_cursor rc 0 }}}.
  Proof.
    iIntros (Φ) "_ HΦ". iApply (wp_WsOp with "[-]").
    iIntros "!> * Hl Hg".
    iDestruct "Hg" as "(Hmsgs & Hsent & Hrecvd & #Hmsgfacts & #Hprot & Hcoh & %Hwf)".
    assert (Hwf2 : ws_wf g2) by (eapply ws_wf_step_connect; [exact Hstep | exact Hwf]).
    inv_base_step.
    destruct H0 as [[-> ->] | (sc & rc & Hne & Hfs & Hfr & -> & ->)].
    - iModIntro. iFrame "∗#%". iApply wp_value.
      iApply ("HΦ" $! true (W64 0) (W64 0)). done.
    - destruct Hfs as (Hfs1 & _ & _). destruct Hfr as (_ & Hfr2 & _).
      iMod (@ghost_map_insert with "Hsent") as "[Hsent Hsc]"; first done.
      iMod (@ghost_map_insert with "Hrecvd") as "[Hrecvd Hrc]"; first done.
      (* only cursors and the backlog moved, so the environment's view of the
         wire is the one it was *)
      rewrite (env_msgs_same g1 _) //.
      iModIntro. iFrame "∗#%". iApply wp_value.
      iApply ("HΦ" $! false sc rc). iFrame.
  Qed.

  (** [Accept] hands the acceptor the send cursor of the reply channel: the
      right to answer a connection it did not initiate, with no cooperation
      from (and no assumption about) the peer. This is the reasoning principle
      grove cannot provide. *)
  Lemma wp_WsAcceptOp (e : ws_endpoint) s E :
    {{{ True }}}
      ExternalOp WsAcceptOp (listen_socket e) @ s; E
    {{{ (sc rc : chan_id) (path : go_string),
        RET (connection sc rc, #path);
        own_send_cursor sc 0 ∗ own_recv_cursor rc 0 }}}.
  Proof.
    iIntros (Φ) "_ HΦ". iApply (wp_WsOp with "[-]").
    iIntros "!> * Hl Hg".
    iDestruct "Hg" as "(Hmsgs & Hsent & Hrecvd & #Hmsgfacts & #Hprot & Hcoh & %Hwf)".
    assert (Hwf2 : ws_wf g2) by (eapply ws_wf_step_accept; [exact Hstep | exact Hwf]).
    inv_base_step.
    (* both branches allocate the same two cursors; they differ only in the
       accept backlog, which carries no ghost state, and in whether the peer's
       channel joins [ws_ext]. It joins empty, so either way the environment's
       view of the wire does not move. *)
    (* match on the shape rather than on an auto-generated name, so that adding
       a side condition to the accept step does not break this proof *)
    match goal with
    | H : _ ∨ _ |- _ => destruct H as [(rest & Hbl & ->) | (Hne & Hfs & Hfr & ->)]
    end; simpl;
      (iMod (@ghost_map_insert with "Hsent") as "[Hsent Hsc]"; first done);
      (iMod (@ghost_map_insert with "Hrecvd") as "[Hrecvd Hrc]"; first done);
      [ rewrite (env_msgs_same g1 _) //
      | destruct Hfs as (_ & _ & _ & Hfs4);
        rewrite (env_msgs_add_ext g1 _ x) // ];
      iModIntro; iFrame "∗#%"; iApply wp_value; iApply ("HΦ" $! x0 x x1); iFrame.
  Qed.

  (** [Send] appends at the cursor. As in grove, an error tells the caller
      nothing about delivery (the message may have gone out anyway); only
      [err = false] is informative.

      Sending is where the protocol is an obligation: the caller shows the
      bytes it puts on the wire satisfy [ws_prot], and the state interpretation
      records that for whoever receives them. *)
  Lemma wp_WsSendOp (sc rc : chan_id) (n : nat) (data : list u8) s E :
    {{{ own_send_cursor sc n ∗ ws_prot data }}}
      ExternalOp WsSendOp (connection sc rc, #data)%V @ s; E
    {{{ (err_early err_late : bool), RET #(err_early || err_late);
        if err_early then own_send_cursor sc n
        else own_send_cursor sc (S n) ∗ is_chan_msg sc n data }}}.
  Proof.
    iIntros (Φ) "[Hsc #Hpd] HΦ". iApply (wp_WsOp with "[-]").
    iIntros "!> * Hl Hg".
    iDestruct "Hg" as "(Hmsgs & Hsent & Hrecvd & #Hmsgfacts & #Hprot & Hcoh & %Hwf)".
    assert (Hwf2 : ws_wf g2) by (eapply ws_wf_step_send; [exact Hstep | exact Hwf]).
    inv_base_step.
    iDestruct (@ghost_map_lookup with "Hsent Hsc") as %Hn.
    rewrite Hn in H0.
    destruct H0 as [[-> ->] | (Hfresh & -> & (err_late & ->))].
    - iModIntro. iFrame "∗#%". iApply wp_value.
      iApply ("HΦ" $! true false). iFrame.
    - iMod (@ghost_map_insert_persist with "Hmsgs") as "[Hmsgs #Hmsg]".
      { done. }
      iMod (@ghost_map_update with "Hsent Hsc") as "[Hsent Hsc]".
      (* the channel has a modeled sender, so it is not one of the
         environment's and the environment's view of the wire does not move *)
      assert (Hnotext : sc ∉ g1.(ws_ext)).
      { intros Hin. by rewrite (wswf_ext_nosend _ Hwf _ Hin) in Hn. }
      rewrite (env_msgs_insert_nonext g1 _ sc n data) //.
      iAssert ([∗ map] k ↦ d ∈ <[ (sc, n) := data ]> g1.(ws_msgs),
                 k ↪[ws_msgs_name]□ d)%I as "#Hmsgfacts2".
      { iApply big_sepM_insert; [done|]. iFrame "#". }
      iAssert ([∗ map] k ↦ d ∈ <[ (sc, n) := data ]> g1.(ws_msgs), ws_prot d)%I
        as "#Hprot2".
      { iApply big_sepM_insert; [done|]. iFrame "#". }
      iModIntro. iFrame "∗#%".
      iApply wp_value. iApply ("HΦ" $! false err_late). iFrame "∗#".
  Qed.

  (** [Recv] consumes at the cursor. A successful receive pins WHICH message
      it was, so a receiver processes the stream in order and exactly once.

      Receiving is where the protocol is a right: [ws_prot] comes out with the
      bytes, and the caller does not have to know whether the sender was
      modeled code or the environment. The two cases reach it differently.
      A message a modeled [WsSendOp] put on the wire is already recorded in the
      state interpretation, and comes straight out of it, with no cursor of the
      sender's and no index arithmetic. A message the environment produces at
      receive time is not recorded yet, and [ws_env_preserves] is what records
      it, in the one update this development assumes about a system it does not
      verify. *)
  Lemma wp_WsRecvOp (sc rc : chan_id) (n : nat) s E :
    {{{ own_recv_cursor rc n ∗ ws_env_preserves E }}}
      ExternalOp WsRecvOp (connection sc rc) @ s; E
    {{{ (err : bool) (data : list u8), RET (#err, #data);
        if err then own_recv_cursor rc n
        else own_recv_cursor rc (S n) ∗ is_chan_msg rc n data ∗ ws_prot data }}}.
  Proof.
    iIntros (Φ) "[Hrc #Henv] HΦ". iApply (wp_WsOp with "[-]").
    iIntros "!> * Hl Hg".
    iDestruct "Hg" as "(Hmsgs & Hsent & Hrecvd & #Hmsgfacts & #Hprot & Hcoh & %Hwf)".
    assert (Hwf2 : ws_wf g2) by (eapply ws_wf_step_recv; [exact Hstep | exact Hwf]).
    inv_base_step.
    iDestruct (@ghost_map_lookup with "Hrecvd Hrc") as %Hn.
    rewrite Hn in H0.
    destruct H0 as [[-> ->] | [(data & Hlookup & -> & ->)
                              | (Hext & Hfresh & (data & Hmay & -> & ->))]].
    - iModIntro. iFrame "∗#%". iApply wp_value.
      iApply ("HΦ" $! true []). iFrame.
    - (* a modeled sender put it there: read the protocol off the interpretation *)
      iDestruct (big_sepM_lookup with "Hmsgfacts") as "#Hmsg"; first exact Hlookup.
      iDestruct (big_sepM_lookup with "Hprot") as "#Hpd"; first exact Hlookup.
      iMod (@ghost_map_update with "Hrecvd Hrc") as "[Hrecvd Hrc]".
      rewrite (env_msgs_same g1 _) //.
      iModIntro. iFrame "∗#%". iApply wp_value.
      iApply ("HΦ" $! false data). iFrame "∗#".
    - (* the environment produced it: record what it did, and get the protocol
         out of that record *)
      match goal with
      | |- context [ env_msgs ?gpost ] =>
          assert (Hem : env_msgs gpost = <[ (rc, n) := data ]> (env_msgs g1));
          [ apply (env_msgs_insert_ext g1 gpost rc n data); done | rewrite Hem ]
      end.
      iMod ("Henv" $! g1 rc n data with "[//] [//] Hprot Hcoh") as "[Hcoh #Hpd]".
      iMod (@ghost_map_insert_persist with "Hmsgs") as "[Hmsgs #Hmsg]".
      { done. }
      iMod (@ghost_map_update with "Hrecvd Hrc") as "[Hrecvd Hrc]".
      iAssert ([∗ map] k ↦ d ∈ <[ (rc, n) := data ]> g1.(ws_msgs),
                 k ↪[ws_msgs_name]□ d)%I as "#Hmsgfacts2".
      { iApply big_sepM_insert; [done|]. iFrame "#". }
      iAssert ([∗ map] k ↦ d ∈ <[ (rc, n) := data ]> g1.(ws_msgs), ws_prot d)%I
        as "#Hprot2".
      { iApply big_sepM_insert; [done|]. iFrame "#". }
      iModIntro. iFrame "∗#%".
      iApply wp_value. iApply ("HΦ" $! false data). iFrame "∗#".
  Qed.

End lifting.

(** * Adequacy: initializing the ghost state from an arbitrary initial network *)
From Perennial.goose_lang Require Import adequacy.

(** The generic initializer has no input beyond the initial network, so the
    [wsGS] it builds carries the trivial protocol: [ws_prot] holds of anything
    and [ws_env_coh] asks nothing of the environment. That is all this hook can
    do, since [ffi_initgP] is a [Prop] and cannot carry the Iris-level protocol
    a deployment means to run. A deployment that wants a real [ws_prot] (the
    Yjs one, say) has to build its [wsGS] in its own adequacy statement rather
    than go through [ffi_global_init]. *)
#[global]
Program Instance ws_interp_adequacy {go_gctx : GoGlobalContext} :
  @ffi_interp_adequacy ws_model ws_interp ws_op ws_semantics :=
  {| ffiGpreS := wsGpreS;
     ffiΣ := wsΣ;
     subG_ffiPreG := subG_wsGpreS;
     ffi_initgP := λ g, ws_wf g;
     ffi_initP := λ σ g, True;
  |}.
Next Obligation.
  rewrite //=. iIntros (? Σ hPre g Hwf).
  iMod (ghost_map_alloc g.(ws_msgs)) as (γm) "[Hm Hmelems]".
  iMod (ghost_map_alloc g.(ws_sent)) as (γs) "[Hs Hselems]".
  iMod (ghost_map_alloc g.(ws_recvd)) as (γr) "[Hr Hrelems]".
  (* messages start out persistent, as every later insert does *)
  iAssert (|==> [∗ map] k ↦ d ∈ g.(ws_msgs), k ↪[γm]□ d)%I
    with "[Hmelems]" as ">#Hmfacts".
  { iApply big_sepM_bupd. iApply (big_sepM_mono with "Hmelems").
    iIntros (k d Hk) "H". by iApply ghost_map_elem_persist. }
  iModIntro.
  iExists (WsGS _ _ _ γm γs γr (λ _, True)%I (λ _, _) (λ _, True)%I).
  iFrame "∗#%". by iApply big_sepM_intro.
Qed.
Next Obligation.
  rewrite //=. iIntros (? Σ hPre σ ??). iExists tt. eauto.
Qed.
Next Obligation.
  intros ?. iIntros (Σ σ σ' Hcrash Hold) "_".
  iExists Hold. iPureIntro. destruct Hcrash. destruct Hold, σ. done.
Qed.
