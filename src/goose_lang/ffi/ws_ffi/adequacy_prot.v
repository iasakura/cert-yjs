(** Distributed adequacy with a protocol of the caller's choosing.

    [goose_dist_adequacy] builds the FFI's ghost state by calling
    [ffi_global_init], whose only inputs are the initial network and a [Prop].
    For ws that means the [wsGS] it builds can only carry the trivial
    [ws_prot], so no execution reachable through that theorem has a real
    protocol on the wire, and a proof that some peer discharges
    [ws_env_preserves] is a proof about ghost state no run can have.

    This is [goose_dist_adequacy] with that one step replaced by
    [ws_global_init_prot]. Everything else is its proof verbatim. What the
    caller gets in exchange is the three equations saying the run's protocol,
    environment coherence and send relation are the ones asked for.

    The initial network is required to be empty, which is what makes the two
    resources [ws_global_init_prot] asks for free: nothing is on the wire, so
    nothing has to satisfy the protocol yet, and the environment has said
    nothing. *)
From iris.proofmode Require Import proofmode.
From Perennial.program_logic Require Import recovery_weakestpre dist_weakestpre
     dist_adequacy.
From Perennial.goose_lang Require Export lifting recovery_lifting dist_lifting.
From Perennial.goose_lang Require Import adequacy lang crash_modality.
From New.goose_lang.ffi.ws_ffi Require Import ws_ffi.

Set Default Proof Using "Type".

Existing Instances ws_op ws_model ws_semantics ws_interp ws_interp_adequacy.

Theorem ws_dist_adequacy_prot {go_gctx : GoGlobalContext}
    Σ `{!all.allG Σ} `{hPre: !gooseGpreS Σ} (ebσs : list node_init_cfg)
    g φinv
    (prot : list u8 -> iProp Σ) (Hpers : forall d, Persistent (prot d))
    (coh : gmap (chan_id * nat) (list u8) -> iProp Σ) :
  ws_wf g.(global_world) ->
  g.(global_world).(ws_msgs) = ∅ ->
  (⊢ coh ∅) ->
  (∀ σ, σ ∈ init_local_state <$> ebσs -> ffi_initP σ.(world) g.(global_world)) ->
  (∀ HG : gooseGlobalGS Σ,
      goose_ffiGlobalGS.(ws_prot) = prot ->
      goose_ffiGlobalGS.(ws_env_coh) = coh ->
      goose_ffiGlobalGS.(ws_may) = g.(global_world).(ws_env_may) ->
      ⊢ ffi_global_start goose_ffiGlobalGS g.(global_world) ={⊤}=∗
        wpd ⊤ ebσs ∗
        (∀ g', ffi_global_ctx goose_ffiGlobalGS g'.(global_world) -∗
                 |={⊤, ∅}=> ⌜ φinv g' ⌝)) ->
  dist_adequate (CS := goose_crash_lang) ebσs g (λ g, φinv g).
Proof.
  intros Hwf Hempty Hcoh HINIT Hwp.
  eapply (wpd_dist_adequacy_inv Σ _ _ _ _ _ _ _ (λ n, 10 * (n + 1))%nat).
  iIntros (Hinv ?) "".
  (* the one line that differs from [goose_dist_adequacy] *)
  iMod (ws_global_init_prot Σ _ g.(global_world) prot Hpers coh Hwf
          with "[] []") as (ffi_namesg) "(%Hp & %Hc & %Hm & Hgw & Hgstart)".
  { rewrite Hempty. by iApply big_sepM_empty. }
  { rewrite /env_msgs Hempty map_filter_empty. iApply Hcoh. }
  iMod (credit_name_init (crash_borrow_ginv_number))
    as (name_credit) "(Hcred_auth&Hcred&Htok)".
  iMod (proph_map_init κs g.(used_proph_id)) as (proph_names) "Hproph".

  set (hG := GooseGlobalGS _ _ proph_names
               (creditGS_update_pre _ _ name_credit)
               (ffi_namesg : @ffiGlobalGS _ ws_interp Σ)).

  iExists global_state_interp, fork_post.
  iExists _, _.

  iMod (Hwp hG Hp Hc Hm with "[$]") as "(Hwp&Hφ)".

  iAssert (|={⊤}=> crash_borrow_ginv)%I with "[Hcred]" as ">Hinv".
  { rewrite /crash_borrow_ginv. iApply (inv_alloc _). iNext. eauto. }
  iModIntro.
  iFrame "Hgw Hinv Hcred_auth Htok Hproph".
  iSplitR; first by eauto.
  iSplitL "Hwp"; last first.
  { iIntros (???) "Hσ".
    iApply ("Hφ" with "[Hσ]").
    iDestruct "Hσ" as "($&_)".
  }
  rewrite /wpd/dist_weakestpre.wpd.
  iApply (big_sepL_mono with "Hwp").
  iIntros (k' σ Hin) "H %Hc'".

  iMod (na_heap_name_init tls σ.(init_local_state).(heap)) as (name_na_heap) "Hh".
  iMod (ffi_local_init _ _ σ.(init_local_state).(world)) as (ffi_names) "(Hw&Hstart)".
  { eapply HINIT. apply list_elem_of_fmap. eexists. split; first done.
    eapply list_elem_of_lookup_2. done. }
  iMod (go_state_init) as (globals_name) "(Hg & Hg_auth)".
  set (hL := GooseLocalGS Σ Hc' ffi_names
               σ.(init_local_state).(go_state).(go_lctx)
               (na_heapGS_update_pre _ name_na_heap)
               (go_stateGS_update_pre Σ _ globals_name)).

  iMod ("H" $! hL with "[$] [$]") as (Φ Φrx Φinv) "Hwpr".
  iModIntro. iExists state_interp, _, _, _.
  iSplitR "Hwpr"; first by iFrame.
  rewrite /wpr//=.
  (* the [wsGpreS] the initializer runs under: it is [gooseGpreS]'s FFI field,
     which typeclass search will not find on its own because reaching it means
     unfolding [ffiGpreS] through this FFI's [ffi_interp_adequacy] *)
  Unshelve. exact goose_preG_ffi.
Qed.

(** The same theorem with the protocol CHOSEN INSIDE the initial fancy
    update. A deployment whose [ws_prot] mentions ghost state has to allocate
    that ghost before it can even NAME its protocol: the Yjs protocol carries
    certificates against a history instance ([yjs_prot decode γh]), and [γh]
    comes out of [history_alloc]. [ws_dist_adequacy_prot] cannot express
    this, since it fixes [prot] before any allocation can run; here the
    caller's fupd runs first (under the run's [invGS], so invariant
    allocation is available), picks [prot] and [coh], and hands back the
    per-run continuation. Everything else is that theorem's proof verbatim. *)
(* The [coh] binder below sits inside an [iProp] context, where a different
   [EqDecision nat] instance is in scope than the one [wsGS]'s field was
   elaborated under; a top-level alias pins the intended type. *)
Local Definition ws_coh_ty Σ : Type :=
  gmap (chan_id * nat) (list u8) -> iProp Σ.

Theorem ws_dist_adequacy_prot_fupd {go_gctx : GoGlobalContext}
    Σ `{!all.allG Σ} `{hPre: !gooseGpreS Σ} (ebσs : list node_init_cfg)
    g φinv :
  ws_wf g.(global_world) ->
  g.(global_world).(ws_msgs) = ∅ ->
  (∀ σ, σ ∈ init_local_state <$> ebσs -> ffi_initP σ.(world) g.(global_world)) ->
  (∀ Hinv : invGS Σ,
     ⊢ |={⊤}=> ∃ (prot : list u8 -> iProp Σ)
                 (Hpers : forall d, Persistent (prot d))
                 (coh : ws_coh_ty Σ),
       coh ∅ ∗
       (∀ HG : gooseGlobalGS Σ,
          ⌜goose_ffiGlobalGS.(ws_prot) = prot⌝ -∗
          ⌜goose_ffiGlobalGS.(ws_env_coh) = coh⌝ -∗
          ⌜goose_ffiGlobalGS.(ws_may) = g.(global_world).(ws_env_may)⌝ -∗
          ffi_global_start goose_ffiGlobalGS g.(global_world) ={⊤}=∗
            wpd ⊤ ebσs ∗
            (∀ g', ffi_global_ctx goose_ffiGlobalGS g'.(global_world) -∗
                     |={⊤, ∅}=> ⌜ φinv g' ⌝))) ->
  dist_adequate (CS := goose_crash_lang) ebσs g (λ g, φinv g).
Proof.
  intros Hwf Hempty HINIT Hwp.
  eapply (wpd_dist_adequacy_inv Σ _ _ _ _ _ _ _ (λ n, 10 * (n + 1))%nat).
  iIntros (Hinv ?) "".
  (* the caller picks the protocol, allocating whatever ghost it needs *)
  iPoseProof (Hwp Hinv) as "Hchoice".
  iMod "Hchoice" as (prot Hpers coh) "[Hcoh Hcont]".
  iMod (ws_global_init_prot Σ _ g.(global_world) prot Hpers coh Hwf
          with "[] [Hcoh]") as (ffi_namesg) "(%Hp & %Hc & %Hm & Hgw & Hgstart)".
  { rewrite Hempty. by iApply big_sepM_empty. }
  { rewrite /env_msgs Hempty map_filter_empty. iFrame "Hcoh". }
  iMod (credit_name_init (crash_borrow_ginv_number))
    as (name_credit) "(Hcred_auth&Hcred&Htok)".
  iMod (proph_map_init κs g.(used_proph_id)) as (proph_names) "Hproph".

  set (hG := GooseGlobalGS _ _ proph_names
               (creditGS_update_pre _ _ name_credit)
               (ffi_namesg : @ffiGlobalGS _ ws_interp Σ)).

  iExists global_state_interp, fork_post.
  iExists _, _.

  iMod ("Hcont" $! hG with "[//] [//] [//] [$]") as "(Hwp&Hφ)".

  iAssert (|={⊤}=> crash_borrow_ginv)%I with "[Hcred]" as ">Hinv".
  { rewrite /crash_borrow_ginv. iApply (inv_alloc _). iNext. eauto. }
  iModIntro.
  iFrame "Hgw Hinv Hcred_auth Htok Hproph".
  iSplitR; first by eauto.
  iSplitL "Hwp"; last first.
  { iIntros (???) "Hσ".
    iApply ("Hφ" with "[Hσ]").
    iDestruct "Hσ" as "($&_)".
  }
  rewrite /wpd/dist_weakestpre.wpd.
  iApply (big_sepL_mono with "Hwp").
  iIntros (k' σ Hin) "H %Hc'".

  iMod (na_heap_name_init tls σ.(init_local_state).(heap)) as (name_na_heap) "Hh".
  iMod (ffi_local_init _ _ σ.(init_local_state).(world)) as (ffi_names) "(Hw&Hstart)".
  { eapply HINIT. apply list_elem_of_fmap. eexists. split; first done.
    eapply list_elem_of_lookup_2. done. }
  iMod (go_state_init) as (globals_name) "(Hg & Hg_auth)".
  set (hL := GooseLocalGS Σ Hc' ffi_names
               σ.(init_local_state).(go_state).(go_lctx)
               (na_heapGS_update_pre _ name_na_heap)
               (go_stateGS_update_pre Σ _ globals_name)).

  iMod ("H" $! hL with "[$] [$]") as (Φ Φrx Φinv) "Hwpr".
  iModIntro. iExists state_interp, _, _, _.
  iSplitR "Hwpr"; first by iFrame.
  rewrite /wpr//=.
  Unshelve. exact goose_preG_ffi.
Qed.
