(** Manual proof layer for the trusted [grovenet] package (the Grove FFI
    realization): New-style WP wrappers for Listen/Accept/Connect/Send/Receive,
    delegating to the grove lifting lemmas
    (Perennial.goose_lang.ffi.grove_ffi.grove_ffi: [wp_ListenOp] /
    [wp_ConnectOp] / [wp_AcceptOp] / [wp_SendOp] / [wp_RecvOp]) via
    New.proof.grove_prelude's instances, with the payload marshalled between
    New byte slices and go_string literals ([wp_bytes_to_string] /
    [wp_string_to_bytes], New.golang.theory.string).

    Listener / Connection handles are pointers to write-once cells holding the
    raw socket value ([listen_socket] / [connection_socket]); the cells are
    persisted at allocation ([heap_pointsto_persist]), so the handles
    ([is_Listener] / [is_Connection]) are persistent and freely shared.

    The per-endpoint mailbox ownership [e c↦ ms] is taken and returned
    EXPLICITLY here; putting it in a shared invariant (and opening it around
    these wrappers) is the caller's design — see
    docs/plan-network-yjs-protocol.md §5. *)
Require Export New.proof.grove_prelude.
Require Export New.golang.theory.
Require Export New.trusted_code.github_com.iasakura.cert_yjs.grovenet.
From Perennial.goose_lang.ffi.grove_ffi Require Import grove_ffi.

Section wrappers.
Context {Σ : gFunctors} {hG : heapGS Σ}.
Context {sem : go.Semantics}.

Set Default Proof Using "Type*".

(** Persistent handle for a [grovenet.Listener]: a pointer to the (write-once,
    persisted) cell holding the listen socket for endpoint [host]. *)
Definition is_Listener (l : loc) (host : w64) : iProp Σ :=
  heap_pointsto l DfracDiscarded (listen_socket host).

(** Persistent handle for a [grovenet.Connection]: a pointer to the cell
    holding the connection socket [local] → [remote]. *)
Definition is_Connection (c : loc) (local remote : w64) : iProp Σ :=
  heap_pointsto c DfracDiscarded (connection_socket local remote).

#[global] Instance is_Listener_persistent l host : Persistent (is_Listener l host).
Proof. apply _. Qed.
#[global] Instance is_Connection_persistent c local remote : Persistent (is_Connection c local remote).
Proof. apply _. Qed.

Lemma wp_Listen (host : w64) :
  {{{ True }}}
    grovenet.Listenⁱᵐᵖˡ #host
  {{{ (l : loc), RET #l; is_Listener l host }}}.
Proof.
  wp_start as "_".
  iApply wp_fupd.
  wp_pures.
  wp_apply wp_ListenOp.
  wp_apply wp_alloc_untyped.
  iIntros (l) "Hl".
  iMod (heap_pointsto_persist with "Hl") as "Hl".
  iModIntro. iApply "HΦ". iFrame.
Qed.

Lemma wp_Accept (l : loc) (host : w64) :
  {{{ is_Listener l host }}}
    grovenet.Acceptⁱᵐᵖˡ #l
  {{{ (c : loc) (remote : w64), RET #c; is_Connection c host remote }}}.
Proof.
  wp_start as "#Hl".
  iEval (rewrite /is_Listener) in "Hl".
  iApply wp_fupd.
  wp_pures.
  wp_apply (Perennial.goose_lang.lifting.wp_load _ _ _ DfracDiscarded (listen_socket host) with "[$Hl]").
  iIntros "_".
  wp_apply wp_AcceptOp.
  iIntros (remote) "_".
  wp_apply wp_alloc_untyped.
  iIntros (c) "Hc".
  iMod (heap_pointsto_persist with "Hc") as "Hc".
  iModIntro. iApply "HΦ". iFrame.
Qed.

Lemma wp_Connect (host : w64) :
  {{{ True }}}
    grovenet.Connectⁱᵐᵖˡ #host
  {{{ (err : bool) (c : loc) (local : w64), RET (#err, #c);
      if err then True
      else is_Connection c local host ∗ local c↦ ∅ }}}.
Proof.
  wp_start as "_".
  iApply wp_fupd.
  wp_pures.
  wp_apply wp_ConnectOp.
  iIntros (err local) "Hlocal".
  destruct err.
  - wp_pures.
    wp_apply wp_alloc_untyped.
    iIntros (c) "Hc".
    wp_pures.
    iModIntro. by iApply ("HΦ" $! true c local).
  - wp_pures.
    wp_apply wp_alloc_untyped.
    iIntros (c) "Hc".
    iMod (heap_pointsto_persist with "Hc") as "Hc".
    wp_pures.
    iModIntro. iApply ("HΦ" $! false c local). iFrame.
Qed.

(** [Send]: the payload slice is read (via the byte-slice → go_string
    conversion) and the message [Message local data] is atomically added to
    [remote]'s mailbox — unless the early error case is taken. [err = false]
    guarantees the message is in the mailbox; [err = true] leaves it
    undetermined (grove's late failure: the message may still have been sent),
    which the disjunction reflects. *)
Lemma wp_Send (c : loc) (local remote : w64) (s : slice.t) (dq : dfrac)
    (data : list w8) (ms : gset message) :
  {{{ is_Connection c local remote ∗ s ↦*{dq} data ∗ remote c↦ ms }}}
    grovenet.Sendⁱᵐᵖˡ #c #s
  {{{ (err : bool), RET #err;
      s ↦*{dq} data ∗
      ((⌜err = true⌝ ∗ remote c↦ ms) ∨
       remote c↦ (ms ∪ {[Message local data]})) }}}.
Proof.
  wp_start as "(#Hc & Hs & Hms)".
  iEval (rewrite /is_Connection) in "Hc".
  wp_pures.
  wp_apply (wp_bytes_to_string with "[$Hs]").
  iIntros "Hs".
  wp_pures.
  wp_apply (Perennial.goose_lang.lifting.wp_load _ _ _ DfracDiscarded (connection_socket local remote) with "[$Hc]").
  iIntros "_".
  wp_pures.
  wp_apply (wp_SendOp _ _ _ null with "[$Hms]").
  iIntros (err_early err_late) "Hms".
  iApply "HΦ". iFrame "Hs".
  destruct err_early; simpl.
  - iLeft. by iFrame.
  - iRight. by iFrame.
Qed.

(** [Receive]: blocks for a message on [c]'s local endpoint; on success the
    returned slice is fresh and holds the payload of some message from
    [remote] in the mailbox (which is unchanged — grove mailboxes never shrink,
    so re-delivery of the same message is possible and the caller must
    deduplicate). *)
Lemma wp_Receive (c : loc) (local remote : w64) (ms : gset message) :
  {{{ is_Connection c local remote ∗ local c↦ ms }}}
    grovenet.Receiveⁱᵐᵖˡ #c
  {{{ (err : bool) (s : slice.t) (data : list w8), RET (#err, #s);
      local c↦ ms ∗ s ↦* data ∗ own_slice_cap w8 s (DfracOwn 1) ∗
      ⌜err = false → Message remote data ∈ ms⌝ }}}.
Proof.
  wp_start as "(#Hc & Hms)".
  iEval (rewrite /is_Connection) in "Hc".
  wp_pures.
  wp_apply (Perennial.goose_lang.lifting.wp_load _ _ _ DfracDiscarded (connection_socket local remote) with "[$Hc]").
  iIntros "_".
  wp_apply (wp_RecvOp with "[$Hms]").
  iIntros (err data) "[%Hin Hms]".
  wp_pures.
  wp_apply wp_string_to_bytes.
  iIntros (sl) "[Hsl Hcap]".
  wp_pures.
  iApply ("HΦ" $! err sl data). iFrame.
  iPureIntro. intros ->. exact Hin.
Qed.

End wrappers.
