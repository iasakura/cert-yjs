(** N0 feasibility demo (issue #45, docs/plan-network-yjs-protocol.md §8):
    verify the [pingpong] package — the smallest programs exercising the Grove
    network FFI through the goose New pipeline — against the Grove model, via
    the trusted [grovenet] package and its WP wrappers
    (New.manualproof.github_com.iasakura.cert_yjs.grovenet).

    Both specs own the relevant mailbox [e c↦ ms] explicitly (single-owner
    demo); the shared-invariant formulation is the network layer's design
    (docs/plan-network-yjs-protocol.md §5) and out of this demo's scope. *)
From New.proof Require Import proof_prelude.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import pingpong.
From Perennial.goose_lang.ffi.grove_ffi Require Import grove_ffi.

Section proof.
Context {Σ : gFunctors} {hG : heapGS Σ}.
Context {sem : go.Semantics}.
Context {grovenet_pkg : grovenet.Assumptions} {pingpong_pkg : pingpong.Assumptions}.

#[global] Instance : IsPkgInit (iProp Σ) grovenet := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) grovenet := build_get_is_pkg_init_wf.
#[global] Instance : IsPkgInit (iProp Σ) pingpong := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) pingpong := build_get_is_pkg_init_wf.

Set Default Proof Using "Type*".

(** [ServeOnce] accepts a connection on [l] and receives one message: on
    success the returned slice holds the payload of some message in [host]'s
    mailbox (whose ownership is returned unchanged — grove receives never
    remove messages). *)
Lemma wp_ServeOnce (l : loc) (host : w64) (ms : gset message) :
  {{{ is_pkg_init pingpong ∗ is_Listener l host ∗ host c↦ ms }}}
    @! pingpong.ServeOnce #l
  {{{ (err : bool) (s : slice.t) (data : list w8), RET (#err, #s);
      host c↦ ms ∗ s ↦* data ∗
      ⌜err = false → ∃ (remote : w64), Message remote data ∈ ms⌝ }}}.
Proof.
  wp_start as "(#Hl & Hms)".
  wp_auto.
  wp_func_call.
  wp_apply (wp_Accept with "[$Hl]").
  iIntros (c remote) "#Hc".
  wp_auto.
  wp_func_call.
  wp_apply (wp_Receive with "[$Hc $Hms]").
  iIntros (err s data) "(Hms & Hs & Hcap & %Hin)".
  wp_auto.
  iApply ("HΦ" $! err s data).
  iFrame. iPureIntro. intros He. exists remote. by apply Hin.
Qed.

(** [Ping] connects to [host] and sends [data] as one message. [err = false]
    guarantees the message is in [host]'s mailbox; on [err = true] the message
    may or may not have been delivered (grove's late send failure), so only
    the disjunction is guaranteed. *)
Lemma wp_Ping (host : w64) (s : slice.t) (dq : dfrac) (data : list w8)
    (ms : gset message) :
  {{{ is_pkg_init pingpong ∗ s ↦*{dq} data ∗ host c↦ ms }}}
    @! pingpong.Ping #host #s
  {{{ (err : bool), RET #err;
      s ↦*{dq} data ∗
      ((⌜err = true⌝ ∗ host c↦ ms) ∨
       (∃ (sender : w64), host c↦ (ms ∪ {[Message sender data]}))) }}}.
Proof.
  wp_start as "(Hs & Hms)".
  wp_auto.
  wp_func_call.
  wp_apply wp_Connect.
  iIntros (err c local) "Hconn".
  destruct err.
  - (* Connect failed: return true, mailbox untouched. *)
    wp_auto.
    iApply ("HΦ" $! true).
    iFrame. iLeft. by iFrame.
  - iDestruct "Hconn" as "[#Hc Hlocal]".
    wp_auto.
    wp_func_call.
    wp_apply (wp_Send with "[$Hc $Hs $Hms]").
    iIntros (errs) "[Hs Hms]".
    wp_auto.
    iApply ("HΦ" $! errs).
    iFrame.
    iDestruct "Hms" as "[[-> Hms] | Hms]".
    + iLeft. by iFrame.
    + iRight. iExists local. iFrame.
Qed.

End proof.
