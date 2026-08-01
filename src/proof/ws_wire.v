(** The wire-protocol layer: "every packet on this channel satisfies [Φw]",
    as an invariant of the system rather than a hypothesis of each call.

    Why an invariant and not a parameter. A relay is a receiver AND a sender.
    If the protocol were a per-call hypothesis on the receive side, the packets
    the relay puts back on the wire would carry no obligation, and the property
    would not survive a hop: each connection would have its own unrelated
    assumption. As an invariant, sending is an OBLIGATION and receiving is a
    RIGHT, so a relay that forwards what it received discharges its obligation
    from the fact it just used, and the property is preserved end to end.

    What makes it expressible over the ws FFI, with no protocol machinery
    inside the FFI itself and in particular no saved predicates and no later:

    - [own_send_cursor c n] is EXCLUSIVE, so "exactly [n] packets have been put
      on [c]" is owned knowledge. Parking the cursor in the invariant is what
      lets the invariant quantify over a definite set of packets.
    - [is_chan_msg c n data] is PERSISTENT and indexed, so a receiver can name
      the packet it consumed and match it against what the invariant records.
    - [wp_WsRecvOp_bounded] says the index a receiver consumed is below the
      sender's cursor, which is the step that connects the two.

    [Φw] is a section parameter, not ghost state, so nothing here needs saved
    predicates. It must be persistent: the invariant hands a copy to every
    receiver and stays intact. For the Yjs use that is automatic, since the
    predicate is built from [is_pending_certified] and pure facts.

    Where the irreducible assumption sits: this invariant can only be
    established for a channel whose sender is modeled code. For an
    environment-fed channel (a browser, [ws_ext] in the model) nobody
    establishes it, and a deployment that wants to rely on the peer assumes it
    there. That is one place, at the edge, and every modeled hop discharges
    its own obligation. *)
From New.proof Require Import proof_prelude.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import wsnet.
From New.goose_lang.ffi.ws_ffi Require Import ws_ffi.

Section wire.
Context {Σ : gFunctors} {hG : heapGS Σ}.
Context {sem : go.Semantics}.
Context {wsnet_pkg : wsnet.Assumptions}.

(** The protocol: what every packet on a wired channel satisfies. *)
Context (Φw : list w8 -> iProp Σ).
Context `{!∀ data, Persistent (Φw data)}.
(* Timeless as well, so the invariant can be opened around the one atomic FFI
   step without a leftover later. The Yjs predicate is built from ghost_map
   elements and pure facts, so both hold automatically. *)
Context `{!∀ data, Timeless (Φw data)}.

Set Default Proof Using "Type*".

(** Everything put on [c] so far satisfies the protocol. The send cursor lives
    here because it is what pins down how many "so far" is; a sender therefore
    sends by opening this, which is exactly what makes [Φw data] an obligation. *)
Definition chan_body (c : chan_id) : iProp Σ :=
  ∃ (n : nat),
    "Hsend" ∷ own_send_cursor c n ∗
    "Hoks"  ∷ ([∗ list] k ∈ seq 0 n, ∃ data, is_chan_msg c k data ∗ Φw data).

Definition wireN : namespace := nroot .@ "cert_yjs" .@ "wire".

Definition is_chan_wire (c : chan_id) : iProp Σ := inv wireN (chan_body c).

#[global] Instance is_chan_wire_persistent c : Persistent (is_chan_wire c).
Proof. apply _. Qed.

(** Allocating the invariant is where a sender gives up its cursor and takes on
    the obligation. A freshly accepted or connected channel has sent nothing,
    so there is nothing to prove yet. *)
Lemma chan_wire_alloc (c : chan_id) E :
  own_send_cursor c 0 ={E}=∗ is_chan_wire c.
Proof.
  iIntros "Hsend".
  iApply (inv_alloc wireN E (chan_body c)).
  iNext. iExists 0%nat. iFrame.
  by rewrite big_sepL_nil.
Qed.

(** Sending is an obligation: the caller proves the packet satisfies the
    protocol, and the invariant records it for whoever receives it.

    The invariant is opened through [wp_WsSendOp_inv] rather than around the
    operation, because [ExternalOp] is not [Atomic] (see that lemma). *)
Lemma wp_wire_Send (cl : loc) (sc rc : chan_id) (s : slice.t) (dq : dfrac)
    (data : list w8) :
  {{{ is_Connection cl sc rc ∗ is_chan_wire sc ∗
      s ↦*{dq} data ∗ Φw data }}}
    wsnet.Sendⁱᵐᵖˡ #cl #s
  {{{ (err : bool), RET #err; s ↦*{dq} data }}}.
Proof.
  wp_start as "(#Hc & #Hwire & Hs & #HΦw)".
  iEval (rewrite /is_Connection) in "Hc".
  wp_pures.
  wp_apply (wp_bytes_to_string with "[$Hs]").
  iIntros "Hs".
  wp_pures.
  wp_apply (Perennial.goose_lang.lifting.wp_load _ _ _ DfracDiscarded (connection sc rc) with "[$Hc]").
  iIntros "_".
  wp_pures.
  iApply (wp_WsSendOp_inv sc rc data _ ⊤ (⊤ ∖ ↑wireN)); first solve_ndisj.
  iInv "Hwire" as (n) ">H" "Hclose". iNamed "H".
  iModIntro. iExists n. iFrame "Hsend".
  iIntros (err_early err_late) "Hsend".
  destruct err_early; simpl.
  - (* nothing went out: close unchanged *)
    iMod ("Hclose" with "[Hsend Hoks]") as "_".
    { iNext. iExists n. iFrame. }
    iModIntro. iApply "HΦ". iFrame.
  - iDestruct "Hsend" as "(Hsend & #Hmsg)".
    iMod ("Hclose" with "[Hsend Hoks]") as "_".
    { iNext. iExists (S n). iFrame "Hsend".
      rewrite seq_S big_sepL_snoc. iFrame "Hoks".
      iExists data. iFrame "#". }
    iModIntro. iApply "HΦ". iFrame.
Qed.

(** Receiving is a right: the protocol comes out with the packet. The sender's
    cursor is taken from the invariant, which is what lets the bounded receive
    place the consumed index inside the recorded range. *)
Lemma wp_wire_Receive (cl : loc) (sc rc : chan_id) (n : nat) :
  {{{ is_Connection cl sc rc ∗ is_chan_wire rc ∗
      own_recv_cursor rc n }}}
    wsnet.Receiveⁱᵐᵖˡ #cl
  {{{ (err : bool) (s : slice.t) (data : list w8), RET (#err, #s);
      s ↦* data ∗ own_slice_cap w8 s (DfracOwn 1) ∗
      (if err then own_recv_cursor rc n
       else own_recv_cursor rc (S n) ∗ is_chan_msg rc n data ∗ Φw data) }}}.
Proof.
  wp_start as "(#Hc & #Hwire & Hrecv)".
  iEval (rewrite /is_Connection) in "Hc".
  wp_pures.
  wp_apply (Perennial.goose_lang.lifting.wp_load _ _ _ DfracDiscarded (connection sc rc) with "[$Hc]").
  iIntros "_".
  wp_apply (wp_WsRecvOp_bounded_inv sc rc n _ ⊤ (⊤ ∖ ↑wireN) with "Hrecv");
    first solve_ndisj.
  iInv "Hwire" as (m) ">H" "Hclose". iNamed "H".
  iModIntro. iExists m. iFrame "Hsend".
  iIntros (err data) "[Hsend Hres]".
  destruct err.
  - iMod ("Hclose" with "[Hsend Hoks]") as "_".
    { iNext. iExists m. iFrame. }
    iModIntro. wp_pures.
    wp_apply wp_string_to_bytes.
    iIntros (sl) "[Hsl Hcap]".
    wp_pures.
    iApply ("HΦ" $! true sl data). iFrame.
  - iDestruct "Hres" as "(Hrecv & #Hmsg & %Hlt)".
    iDestruct (big_sepL_lookup _ _ n n with "Hoks") as (d) "[#Hmsg2 #HΦw]".
    { by apply lookup_seq_lt. }
    iDestruct (is_chan_msg_agree with "Hmsg Hmsg2") as %<-.
    iMod ("Hclose" with "[Hsend Hoks]") as "_".
    { iNext. iExists m. iFrame. }
    iModIntro. wp_pures.
    wp_apply wp_string_to_bytes.
    iIntros (sl) "[Hsl Hcap]".
    wp_pures.
    iApply ("HΦ" $! false sl data). iFrame "∗#".
Qed.

End wire.
