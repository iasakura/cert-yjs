(** Distributed adequacy for the ws (connection-oriented network) FFI.

    The ws analogues of perennial's grove theorems
    ([Perennial.goose_lang.ffi.grove_ffi.adequacy]), in the same order and with
    the same proofs. Three differences come from the model:

    - what the caller starts from is [ffi_global_start], which for ws is the
      send and receive cursors of every channel already present in the initial
      network (grove hands out its mailboxes there instead);
    - [ffi_local_start] is [True], because a ws node has no per-node state, so
      grove's per-node file-resource premise has no counterpart here and simply
      disappears;
    - [ffi_initgP] is [ws_wf], so the initial network must be well formed,
      which the empty network is ([ws_wf_empty]).

    Staging note: as with the rest of this directory, the file is developed
    inside cert-yjs (so it lands under the [New] logical prefix) and belongs in
    the perennial fork at [src/goose_lang/ffi/ws_ffi/adequacy.v]; moving it only
    rewrites the [New.goose_lang.ffi.ws_ffi] require to
    [Perennial.goose_lang.ffi.ws_ffi]. *)
From Perennial.program_logic Require Import dist_lang.
From Perennial.goose_lang Require Import lang lifting.
From New.goose_lang.ffi.ws_ffi Require Import ws_ffi.

From Perennial.goose_lang Require Import adequacy recovery_adequacy dist_adequacy.

Set Default Proof Using "Type".

Existing Instances ws_op ws_model.
Existing Instances ws_semantics ws_interp.
Existing Instances goose_wsGS.

Theorem ws_ffi_dist_adequacy Σ {go_gctx : GoGlobalContext}
  {hGhost: all.allG Σ} `{hPre: !gooseGpreS Σ} ebσs g (φinv : _ → Prop) :
  ws_wf g.(global_world) →
  (∀ HG : gooseGlobalGS Σ,
      ⊢@{iPropI Σ}
        (([∗ map] c ↦ n ∈ g.(global_world).(ws_sent), own_send_cursor c n) ∗
         ([∗ map] c ↦ n ∈ g.(global_world).(ws_recvd), own_recv_cursor c n)) ={⊤}=∗
          (([∗ list] ρ ∈ ebσs,
                (* We reason about node running e with an arbitrary generation *)
                ∀ HL : gooseLocalGS Σ,
                  |={⊤}=> ∃ Φ Φc Φr, wpr NotStuck ⊤ ρ.(init_thread) ρ.(init_restart) Φ Φc Φr) ∗
          (∀ g', ffi_global_ctx goose_ffiGlobalGS g'.(global_world) ={⊤,∅}=∗ ⌜ φinv g' ⌝) )) →
  dist_adequacy.dist_adequate (CS := goose_crash_lang) ebσs g (λ g, φinv g).
Proof.
  intros Hwf H. eapply goose_dist_adequacy; try done.
  intros. iIntros "Hcursors". iMod (H HG with "Hcursors") as "(H1&H2)".
  iModIntro. iSplitL "H1".
  { iApply (big_sepL_mono with "H1").
    iIntros (? [e er σ] Hlookup) "H". iIntros. iSpecialize ("H" $! hG).
    iMod "H" as (???) "H". iModIntro. iExists _, _, _. iFrame "H".
  }
  { eauto. }
Qed.

Theorem ws_ffi_dist_adequacy_failstop Σ {go_gctx : GoGlobalContext}
  {hGhost: all.allG Σ} `{hPre: !gooseGpreS Σ}
  (ebσs : list (goose_lang.expr * state)) g (φinv : _ → Prop) :
  ws_wf g.(global_world) →
  (∀ HG : gooseGlobalGS Σ,
      ⊢@{iPropI Σ}
        (([∗ map] c ↦ n ∈ g.(global_world).(ws_sent), own_send_cursor c n) ∗
         ([∗ map] c ↦ n ∈ g.(global_world).(ws_recvd), own_recv_cursor c n)) ={⊤}=∗
          (([∗ list] '(e, σ) ∈ ebσs,
                (* We reason about node running e with an arbitrary generation *)
                ∀ HL : gooseLocalGS Σ,
                  own_go_state σ.(go_state).(package_state)
                  ={⊤}=∗ ∃ Φ, wp NotStuck ⊤ e Φ
            ) ∗
          (∀ g', ffi_global_ctx goose_ffiGlobalGS g'.(global_world) ={⊤,∅}=∗ ⌜ φinv g' ⌝) )) →
  dist_adequate_failstop (ffi_sem:=ws_semantics) ebσs g (λ g, φinv g).
Proof.
  intros Hwf H. eapply goose_dist_adequacy_failstop; try done.
  intros. iIntros "Hcursors". iMod (H HG with "Hcursors") as "(H1&H2)".
  iModIntro. iSplitL "H1".
  { iApply (big_sepL_mono with "H1").
    iIntros (? [e σ] Hlookup) "H". iIntros. iApply ("H" with "[$]"). }
  { eauto. }
Qed.

Theorem ws_ffi_single_node_adequacy_failstop Σ {go_gctx : GoGlobalContext}
  {hGhost: all.allG Σ} `{hPre: !gooseGpreS Σ} e σ g φ :
  ws_wf g.(global_world) →
  (∀ (Hl : gooseLocalGS Σ) (Hg : gooseGlobalGS Σ),
    ⊢ (([∗ map] c ↦ n ∈ g.(global_world).(ws_sent), own_send_cursor c n) ∗
       ([∗ map] c ↦ n ∈ g.(global_world).(ws_recvd), own_recv_cursor c n))
      ={⊤}=∗
      WP e @ ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate_failstop e σ g (λ v _ _, φ v).
Proof.
  intros Hwf H. eapply (goose_recv_adequacy_failstop Σ); try done.
  (* [ffi_local_start] is [True] for ws, so there is nothing to hand the node *)
  intros Hl Hg. iIntros "Hcursors _". iApply (H Hl Hg with "Hcursors").
Qed.
