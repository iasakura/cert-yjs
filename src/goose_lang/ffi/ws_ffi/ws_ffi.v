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
    receiver learns what the sender sent. *)
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
Class wsGS Σ : Set := WsGS {
  #[global] wsG_msgG :: ghost_mapG Σ (chan_id * nat) (list u8);
  #[global] wsG_curG :: ghost_mapG Σ chan_id nat;
  ws_msgs_name : gname;
  ws_sent_name : gname;
  ws_recvd_name : gname;
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
          (* the physical well-formedness of impl.v, carried here so the Iris
             layer can read one fact off it: a message index on a channel with
             a modeled sender is below that sender's cursor. A receiver needs
             exactly that to tie the message it consumed to what the sender
             recorded about it. *)
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
    iDestruct "Hg" as "(Hmsgs & Hsent & Hrecvd & #Hmsgfacts & %Hwf)".
    assert (ws_wf g2) by (eapply ws_wf_step_listen; [exact Hstep | exact Hwf]).
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
    iDestruct "Hg" as "(Hmsgs & Hsent & Hrecvd & #Hmsgfacts & %Hwf)".
    assert (ws_wf g2) by (eapply ws_wf_step_connect; [exact Hstep | exact Hwf]).
    inv_base_step.
    destruct H1 as [[-> ->] | (sc & rc & Hne & Hfs & Hfr & -> & ->)].
    - iModIntro. iFrame "∗#%". iApply wp_value.
      iApply ("HΦ" $! true (W64 0) (W64 0)). done.
    - destruct Hfs as (Hfs1 & _ & _). destruct Hfr as (_ & Hfr2 & _).
      iMod (@ghost_map_insert with "Hsent") as "[Hsent Hsc]"; first done.
      iMod (@ghost_map_insert with "Hrecvd") as "[Hrecvd Hrc]"; first done.
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
    iDestruct "Hg" as "(Hmsgs & Hsent & Hrecvd & #Hmsgfacts & %Hwf)".
    assert (ws_wf g2) by (eapply ws_wf_step_accept; [exact Hstep | exact Hwf]).
    inv_base_step.
    (* both branches allocate the same two cursors; they differ only in the
       accept backlog, which carries no ghost state *)
    (* match on the shape rather than on an auto-generated name, so that adding
       a side condition to the accept step does not break this proof *)
    match goal with
    | H : _ ∨ _ |- _ => destruct H as [(rest & Hbl & ->) | (Hne & Hfs & Hfr & ->)]
    end; simpl;
      (iMod (@ghost_map_insert with "Hsent") as "[Hsent Hsc]"; first done);
      (iMod (@ghost_map_insert with "Hrecvd") as "[Hrecvd Hrc]"; first done);
      iModIntro; iFrame "∗#%"; iApply wp_value; iApply ("HΦ" $! x0 x x1); iFrame.
  Qed.

  (** [Send] appends at the cursor. As in grove, an error tells the caller
      nothing about delivery (the message may have gone out anyway); only
      [err = false] is informative. *)
  Lemma wp_WsSendOp (sc rc : chan_id) (n : nat) (data : list u8) s E :
    {{{ own_send_cursor sc n }}}
      ExternalOp WsSendOp (connection sc rc, #data)%V @ s; E
    {{{ (err_early err_late : bool), RET #(err_early || err_late);
        if err_early then own_send_cursor sc n
        else own_send_cursor sc (S n) ∗ is_chan_msg sc n data }}}.
  Proof.
    iIntros (Φ) "Hsc HΦ". iApply (wp_WsOp with "[-]").
    iIntros "!> * Hl Hg".
    iDestruct "Hg" as "(Hmsgs & Hsent & Hrecvd & #Hmsgfacts & %Hwf)".
    assert (ws_wf g2) by (eapply ws_wf_step_send; [exact Hstep | exact Hwf]).
    inv_base_step.
    iDestruct (@ghost_map_lookup with "Hsent Hsc") as %Hn.
    rewrite Hn in H1.
    destruct H1 as [[-> ->] | (Hfresh & -> & (err_late & ->))].
    - iModIntro. iFrame "∗#%". iApply wp_value.
      iApply ("HΦ" $! true false). iFrame.
    - iMod (@ghost_map_insert_persist with "Hmsgs") as "[Hmsgs #Hmsg]".
      { done. }
      iMod (@ghost_map_update with "Hsent Hsc") as "[Hsent Hsc]".
      iModIntro. iFrame "∗#%". iSplitR.
      { iApply big_sepM_insert; [done|]. iFrame "#". }
      iApply wp_value. iApply ("HΦ" $! false err_late). iFrame "∗#".
  Qed.

  (** [Recv] consumes at the cursor. A successful receive pins WHICH message
      it was, so a receiver processes the stream in order and exactly once. *)
  Lemma wp_WsRecvOp (sc rc : chan_id) (n : nat) s E :
    {{{ own_recv_cursor rc n }}}
      ExternalOp WsRecvOp (connection sc rc) @ s; E
    {{{ (err : bool) (data : list u8), RET (#err, #data);
        if err then own_recv_cursor rc n
        else own_recv_cursor rc (S n) ∗ is_chan_msg rc n data }}}.
  Proof.
    iIntros (Φ) "Hrc HΦ". iApply (wp_WsOp with "[-]").
    iIntros "!> * Hl Hg".
    iDestruct "Hg" as "(Hmsgs & Hsent & Hrecvd & #Hmsgfacts & %Hwf)".
    assert (ws_wf g2) by (eapply ws_wf_step_recv; [exact Hstep | exact Hwf]).
    inv_base_step.
    iDestruct (@ghost_map_lookup with "Hrecvd Hrc") as %Hn.
    rewrite Hn in H1.
    destruct H1 as [[-> ->] | [(data & Hlookup & -> & ->) | (Hext & Hfresh & (data & -> & ->))]].
    - iModIntro. iFrame "∗#%". iApply wp_value.
      iApply ("HΦ" $! true []). iFrame.
    - iDestruct (big_sepM_lookup with "Hmsgfacts") as "#Hmsg"; first exact Hlookup.
      iMod (@ghost_map_update with "Hrecvd Hrc") as "[Hrecvd Hrc]".
      iModIntro. iFrame "∗#%". iApply wp_value.
      iApply ("HΦ" $! false data). iFrame "∗#".
    - iMod (@ghost_map_insert_persist with "Hmsgs") as "[Hmsgs #Hmsg]".
      { done. }
      iMod (@ghost_map_update with "Hrecvd Hrc") as "[Hrecvd Hrc]".
      iModIntro. iFrame "∗#%". iSplitR.
      { iApply big_sepM_insert; [done|]. iFrame "#". }
      iApply wp_value. iApply ("HΦ" $! false data). iFrame "∗#".
  Qed.


  (** The fact a wire-protocol layer needs, and the reason [ws_wf] is carried in
      the state interpretation: a message the receiver consumed sits BELOW the
      sender's cursor, so it is one the sender has already recorded something
      about. It cannot be stated as a standalone entailment because it is read
      off the physical state, so it comes as a strengthened receive that also
      takes the sender's cursor.

      Holding that cursor additionally rules out the environment branch: an
      environment-fed channel has no modeled sender ([wswf_ext_nosend]), so a
      channel someone owns the send cursor of never has bytes fabricated on
      it. *)
  Lemma wp_WsRecvOp_bounded (sc rc : chan_id) (n m : nat) s E :
    {{{ own_recv_cursor rc n ∗ own_send_cursor rc m }}}
      ExternalOp WsRecvOp (connection sc rc) @ s; E
    {{{ (err : bool) (data : list u8), RET (#err, #data);
        own_send_cursor rc m ∗
        (if err then own_recv_cursor rc n
         else own_recv_cursor rc (S n) ∗ is_chan_msg rc n data ∗ ⌜(n < m)%nat⌝) }}}.
  Proof.
    iIntros (Φ) "[Hrc Hsc] HΦ". iApply (wp_WsOp with "[-]").
    iIntros "!> * Hl Hg".
    iDestruct "Hg" as "(Hmsgs & Hsent & Hrecvd & #Hmsgfacts & %Hwf)".
    assert (ws_wf g2) by (eapply ws_wf_step_recv; [exact Hstep | exact Hwf]).
    inv_base_step.
    iDestruct (@ghost_map_lookup with "Hrecvd Hrc") as %Hn.
    iDestruct (@ghost_map_lookup with "Hsent Hsc") as %Hm.
    rewrite Hn in H1.
    destruct H1 as [[-> ->] | [(data & Hlookup & -> & ->) | (Hext & Hfresh & (data & -> & ->))]].
    - iModIntro. iFrame "∗#%". iApply wp_value.
      iApply ("HΦ" $! true []). iFrame.
    - iDestruct (big_sepM_lookup with "Hmsgfacts") as "#Hmsg"; first exact Hlookup.
      assert (n < m)%nat as Hlt.
      { destruct (wswf_sent_seg _ Hwf rc m Hm n) as [Hto _].
        apply Hto. rewrite Hlookup. eauto. }
      iMod (@ghost_map_update with "Hrecvd Hrc") as "[Hrecvd Hrc]".
      iModIntro. iFrame "∗#%". iApply wp_value.
      iApply ("HΦ" $! false data). iFrame "∗#%".
    - (* impossible: an environment-fed channel has no send cursor *)
      exfalso. rewrite (wswf_ext_nosend _ Hwf rc Hext) in Hm. done.
  Qed.

  (** * Rules for a cursor that lives in an invariant

      [ExternalOp] is not [Atomic]: [ffi_step] carries a stuttering disjunct (a
      step to itself), which is what makes every operation unconditionally
      reducible but also means it does not reduce to a value in one step. So a
      caller cannot open an invariant AROUND the operation. These variants take
      the cursor through a mask-changing update instead and open it HERE,
      inside the one place that knows the stuttering branch changes nothing:
      [wp_WsOp] handles that branch itself and never runs the continuation.

      They stay FFI-generic: no protocol, no application predicate. *)

  Lemma wp_WsSendOp_inv (sc rc : chan_id) (data : list u8) s E1 E2 (Φ : val -> iProp Σ) :
    E2 ⊆ E1 ->
    (|={E1,E2}=> ∃ n : nat, own_send_cursor sc n ∗
       (∀ (err_early err_late : bool),
          (if err_early then own_send_cursor sc n
           else own_send_cursor sc (S n) ∗ is_chan_msg sc n data)
          ={E2,E1}=∗ Φ #(err_early || err_late)))
    -∗ WP ExternalOp WsSendOp (connection sc rc, #data)%V @ s; E1 {{ Φ }}.
  Proof.
    iIntros (HE) "Hau". iApply (wp_WsOp with "[-]").
    iIntros "!> * Hl Hg".
    iDestruct "Hg" as "(Hmsgs & Hsent & Hrecvd & #Hmsgfacts & %Hwf)".
    assert (ws_wf g2) by (eapply ws_wf_step_send; [exact Hstep | exact Hwf]).
    inv_base_step.
    iMod "Hau" as (n) "[Hsc Hclose]".
    iDestruct (@ghost_map_lookup with "Hsent Hsc") as %Hn.
    rewrite Hn in H1.
    destruct H1 as [[-> ->] | (Hfresh & -> & (err_late & ->))].
    - iMod ("Hclose" $! true false with "Hsc") as "HΦ".
      iModIntro. iFrame "∗#%". iApply wp_value. iFrame.
    - iMod (@ghost_map_insert_persist with "Hmsgs") as "[Hmsgs #Hmsg]".
      { done. }
      iMod (@ghost_map_update with "Hsent Hsc") as "[Hsent Hsc]".
      iMod ("Hclose" $! false err_late with "[$Hsc]") as "HΦ".
      { iFrame "#". }
      iModIntro. iFrame "∗#%". iSplitR.
      { iApply big_sepM_insert; [done|]. iFrame "#". }
      iApply wp_value. iFrame.
  Qed.

  Lemma wp_WsRecvOp_bounded_inv (sc rc : chan_id) (n : nat) s E1 E2 (Φ : val -> iProp Σ) :
    E2 ⊆ E1 ->
    own_recv_cursor rc n -∗
    (|={E1,E2}=> ∃ m : nat, own_send_cursor rc m ∗
       (∀ (err : bool) (data : list u8),
          own_send_cursor rc m ∗
          (if err then own_recv_cursor rc n
           else own_recv_cursor rc (S n) ∗ is_chan_msg rc n data ∗ ⌜(n < m)%nat⌝)
          ={E2,E1}=∗ Φ (#err, #data)%V))
    -∗ WP ExternalOp WsRecvOp (connection sc rc) @ s; E1 {{ Φ }}.
  Proof.
    iIntros (HE) "Hrc Hau". iApply (wp_WsOp with "[-]").
    iIntros "!> * Hl Hg".
    iDestruct "Hg" as "(Hmsgs & Hsent & Hrecvd & #Hmsgfacts & %Hwf)".
    assert (ws_wf g2) by (eapply ws_wf_step_recv; [exact Hstep | exact Hwf]).
    inv_base_step.
    iMod "Hau" as (m) "[Hsc Hclose]".
    iDestruct (@ghost_map_lookup with "Hrecvd Hrc") as %Hn.
    iDestruct (@ghost_map_lookup with "Hsent Hsc") as %Hm.
    rewrite Hn in H1.
    destruct H1 as [[-> ->] | [(data & Hlookup & -> & ->) | (Hext & Hfresh & (data & -> & ->))]].
    - iMod ("Hclose" $! true [] with "[$Hsc $Hrc]") as "HΦ".
      iModIntro. iFrame "∗#%". iApply wp_value. iFrame.
    - iDestruct (big_sepM_lookup with "Hmsgfacts") as "#Hmsg"; first exact Hlookup.
      assert (n < m)%nat as Hlt.
      { destruct (wswf_sent_seg _ Hwf rc m Hm n) as [Hto _].
        apply Hto. rewrite Hlookup. eauto. }
      iMod (@ghost_map_update with "Hrecvd Hrc") as "[Hrecvd Hrc]".
      iMod ("Hclose" $! false data with "[$Hsc $Hrc]") as "HΦ".
      { iFrame "#%". }
      iModIntro. iFrame "∗#%". iApply wp_value. iFrame.
    - (* impossible: an environment-fed channel has no send cursor *)
      exfalso. rewrite (wswf_ext_nosend _ Hwf rc Hext) in Hm. done.
  Qed.

End lifting.

(** * Adequacy: initializing the ghost state from an arbitrary initial network *)
From Perennial.goose_lang Require Import adequacy.

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
  rewrite //=. iIntros (_ Σ hPre g Hinit).
  iMod (ghost_map_alloc g.(ws_msgs)) as (γm) "[Hm Hmelems]".
  iMod (ghost_map_alloc g.(ws_sent)) as (γs) "[Hs Hselems]".
  iMod (ghost_map_alloc g.(ws_recvd)) as (γr) "[Hr Hrelems]".
  (* messages start out persistent, as every later insert does *)
  iAssert (|==> [∗ map] k ↦ d ∈ g.(ws_msgs), k ↪[γm]□ d)%I
    with "[Hmelems]" as ">#Hmfacts".
  { iApply big_sepM_bupd. iApply (big_sepM_mono with "Hmelems").
    iIntros (k d Hk) "H". by iApply ghost_map_elem_persist. }
  iModIntro. iExists (WsGS _ _ _ γm γs γr). iFrame "∗#%".
Qed.
Next Obligation.
  rewrite //=. iIntros (_ Σ hPre σ ??). iExists tt. eauto.
Qed.
Next Obligation.
  intros ?. iIntros (Σ σ σ' Hcrash Hold) "_".
  iExists Hold. iPureIntro. destruct Hcrash. destruct Hold, σ. done.
Qed.
