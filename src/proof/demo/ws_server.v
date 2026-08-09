(** The closed-system theorem for the W3b update server (issue #107, M4).

    One node boots the whole verified server: initialize the packages,
    listen, create the document (the lock layer included, [wp_NewDoc]),
    create the room, and run the accept loop. The theorem pushes that
    through [ws_dist_adequacy_prot_fupd] with the REAL wire protocol
    [yjs_prot decode γh], whose history instance is allocated inside the
    initial fancy update, and exports protocol totality: in EVERY reachable
    state of EVERY execution, EVERY message on the wire decodes to an honest
    batch.

    Crash-restart halts immediately ([halt]) by design: the server's
    history element lives in the store lock invariant and dies with the
    heap, which is semantically right (a restarted y-websocket server has
    lost its document), so a crashed server is dead but safe.

    The environment is parametric: any peer population whose coherence
    [coh0 γh] and the initial world's send relation discharge
    [ws_env_preserves] for [yjs_prot decode γh] (the ws_env_smoke.v peers
    have exactly this shape). *)
From Perennial.program_logic Require Import recovery_weakestpre dist_weakestpre dist_adequacy.
From Perennial.goose_lang Require Import adequacy crash_modality recovery_lifting dist_lifting.
From New.proof Require Import proof_prelude.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import wsrelay.
From New.proof Require Import prelude.
From New.proof.sync_proof Require Import base mutex rwmutex.
From New.goose_lang.ffi.ws_ffi Require Import ws_ffi.
From New.goose_lang.ffi.ws_ffi Require Import adequacy_prot.
From New.proof Require Import core.
From New.proof Require Import history.
From New.proof Require Import yjs_prot.
From New.proof.store Require Import store.
From New.proof.doc Require Import doc.
From New.proof Require Import ws_relay.
From iris.algebra Require Import auth gmap gset.
From iris.algebra.lib Require Import dfrac_agree.

Local Open Scope Z_scope.

(** The node's restart program: halt immediately. A crashed server has lost
    its document with the heap ([own_client_history] lived in the store lock
    invariant), which is exactly a restarted y-websocket server's situation;
    a halted node is dead but safe, and the recovery obligation is the
    trivial one. *)
Definition halt {ext : ffi_syntax} {go_gctx : GoGlobalContext} : expr := #().

(** Initialize the packages, listen on [host], create the server document as
    client [client], wrap it in a room decoding with [f], and serve forever.
    Defined outside any [heapGS] section so a closed theorem can name it
    before any node exists. *)
Definition server_boot {go_gctx : GoGlobalContext}
    {go_lctx : GoLocalContext} {go_fns : GoSemanticsFunctions}
    (host client : w64) (f : func.t) : expr :=
  wsrelay.initialize' #();;
  (let: "l" := wsnet.Listenⁱᵐᵖˡ #host in
   let: "dv" := (@! yjs.NewDoc) #client in
   let: "r" := (@! wsrelay.NewRoom) "dv" #f in
   (@! wsrelay.Run) "l" "r").

Section boot.
Context {Σ : gFunctors} {hG : heapGS Σ}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.
Context {sync_pkg : sync.Assumptions}.
Context {wsnet_pkg : wsnet.Assumptions} {wsrelay_pkg : wsrelay.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.
Notation P := go_string.
Local Notation TId := (TypeId P).
Local Notation Input := (TId * IntegrateInput (A := A))%type.
Local Notation Ev := (@Event (TId * @YjsOperation A)).

Context {seq_inG : inG Σ (authR (gmapUR loc (gsetUR (YjsItem A))))}.
Context {acc_inG : inG Σ (authR (gsetUR YjsId))}.
Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO (gmap loc type_state)))}.

Context (decode : list u8 -> option (list Input)).

(* ===== package initialization ============================================ *)

Lemma wp_wsnet_initialize' get_is_pkg_init :
  get_is_pkg_init_prop wsnet get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init }}}
    wsnet.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init wsnet }}}.
Proof.
  intros Hinit. wp_start as "Hown".
  wp_apply (wp_package_init with "[$Hown] HΦ").
  { destruct Hinit as (-> & ?); done. }
  iIntros "Hown". wp_auto.
  iEval (rewrite is_pkg_init_unfold /=). iFrame "∗#". done.
Qed.

Lemma wp_yjs_initialize' get_is_pkg_init :
  get_is_pkg_init_prop yjs get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init }}}
    yjs.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init yjs }}}.
Proof.
  intros Hinit. wp_start as "Hown".
  wp_apply (wp_package_init with "[$Hown] HΦ").
  { destruct Hinit as (-> & ?); done. }
  iIntros "Hown". wp_auto.
  wp_apply (sync.wp_initialize' with "[$Hown]") as "(Hown & #?)".
  { naive_solver. }
  iEval (rewrite is_pkg_init_unfold /=). iFrame "∗#". done.
Qed.

Lemma wp_wsrelay_initialize' get_is_pkg_init :
  get_is_pkg_init_prop wsrelay get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init }}}
    wsrelay.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init wsrelay }}}.
Proof.
  intros Hinit. wp_start as "Hown".
  wp_apply (wp_package_init with "[$Hown] HΦ").
  { destruct Hinit as (-> & ?); done. }
  iIntros "Hown". wp_auto.
  wp_apply (wp_yjs_initialize' with "[$Hown]") as "(Hown & #?)".
  { naive_solver. }
  wp_apply (wp_wsnet_initialize' with "[$Hown]") as "(Hown & #?)".
  { naive_solver. }
  wp_apply (sync.wp_initialize' with "[$Hown]") as "(Hown & #?)".
  { naive_solver. }
  iEval (rewrite is_pkg_init_unfold /=). iFrame "∗#". done.
Qed.

(* ===== the boot expression =============================================== *)

Lemma wp_server_boot (host client : w64) (f : func.t) (γh : history_names)
    get_is_pkg_init :
  get_is_pkg_init_prop wsrelay get_is_pkg_init →
  (∀ d, ws_prot d = yjs_prot decode γh d) →
  ⊢ own_initializing get_is_pkg_init -∗
    is_history (A := A) (P := P) γh -∗
    own_client_history γh (uint.nat client) ([] : list Ev) -∗
    codec_spec decode f -∗
    ws_env_preserves ⊤ -∗
    WP server_boot host client f {{ _, True }}.
Proof.
  iIntros (Hget Hprot) "Hown #Hhist Hcl #Hcodec #Henv".
  rewrite /server_boot.
  wp_apply (wp_wsrelay_initialize' with "[$Hown]") as "(Hown & #Hinit)";
    first exact Hget.
  wp_apply wp_Listen.
  iIntros (l) "#Hl".
  wp_auto.
  wp_apply (wp_NewDoc γh client with "[$Hcl]").
  iIntros (dv s_loc γs) "[#Hdoc #Hpin]".
  wp_auto.
  wp_apply (wp_NewRoom decode dv s_loc γs γh (uint.nat client) f Hprot
             with "[$Hdoc $Hhist $Hpin $Hcodec]").
  iIntros (r γ) "#Hroom".
  wp_auto.
  wp_apply (wp_Run decode l host r γ γs γh (uint.nat client)
             with "[$Hl $Hroom $Henv]").
  iIntros "[]".
Qed.

(* ===== the package-init map ============================================== *)

(** The seven packages of the server's transitive import tree; anything else
    maps to [True] (nothing else is ever initialized by this boot). *)
Definition server_get_is_pkg_init : go_string → iProp Σ :=
  λ nm,
    if decide (nm = wsrelay) then is_pkg_init wsrelay
    else if decide (nm = yjs) then is_pkg_init yjs
    else if decide (nm = wsnet) then is_pkg_init wsnet
    else if decide (nm = sync) then is_pkg_init sync
    else if decide (nm = New.code.sync.atomic.pkg_id.atomic)
         then is_pkg_init New.code.sync.atomic.pkg_id.atomic
    else if decide (nm = New.code.internal.race.pkg_id.race)
         then is_pkg_init New.code.internal.race.pkg_id.race
    else if decide (nm = New.code.internal.synctest.pkg_id.synctest)
         then is_pkg_init New.code.internal.synctest.pkg_id.synctest
    else True%I.

Lemma server_get_is_pkg_init_wf :
  get_is_pkg_init_prop wsrelay server_get_is_pkg_init.
Proof.
  rewrite /get_is_pkg_init_prop /=.
  repeat split;
    rewrite /server_get_is_pkg_init;
    repeat first [ rewrite decide_True; [reflexivity | reflexivity]
                 | rewrite decide_False; last by discriminate ].
Qed.

(* ===== crash recovery: a dead server is a safe server ==================== *)

Lemma wpc_halt :
  ⊢ WPC halt @ NotStuck; ⊤ {{ _, True }} {{ True }}.
Proof. iApply wpc_value'. by iSplit. Qed.

(** The node's whole crash-aware obligation: turn the node's initial package
    state into the right to initialize, run the boot (whose crash condition
    is trivial), and after any crash come back up as [halt]. Stated over
    [own_go_state] directly so a closed theorem needs no in-context
    instances: everything is fixed by unifying with the [wpr] goal. *)
Lemma wpr_server_boot (host client : w64) (f : func.t) (γh : history_names)
    (σ : lang.state) :
  is_init σ →
  (∀ d, ws_prot d = yjs_prot decode γh d) →
  ⊢ own_go_state σ.(go_state).(package_state) -∗
    is_history (A := A) (P := P) γh -∗
    own_client_history γh (uint.nat client) ([] : list Ev) -∗
    codec_spec decode f -∗
    ws_env_preserves ⊤ -∗
    wpr NotStuck ⊤ (server_boot host client f) halt
        (λ _, True%I) (λ _, True%I) (λ _ _, True%I).
Proof.
  iIntros (Hinit Hprot) "Hgo #Hhist Hcl #Hcodec #Henv".
  iApply fupd_wpr.
  iMod (go_init server_get_is_pkg_init _ Hinit with "Hgo") as "Hown".
  iModIntro.
  iApply (idempotence_wpr NotStuck ⊤ _ _ _
            (λ _, True%I) (λ _ _, True%I) (λ _, True%I) with "[-] []").
  - iApply wp_wpc.
    iApply (wp_server_boot _ _ _ _ server_get_is_pkg_init
              server_get_is_pkg_init_wf Hprot
              with "Hown Hhist Hcl Hcodec Henv").
  - iModIntro.
    iIntros (hL' σ1 σ2 Hcrash) "_".
    iNext.
    iApply (post_crash_mono (λ _, emp)%I).
    { iIntros (hG'') "_ _".
      iSplit; first done.
      iApply wpc_value'. by iSplit. }
    iApply post_crash_intro. done.
Qed.

End boot.

(* ===== the closed-system theorem ========================================= *)

Existing Instances ws_op ws_model ws_semantics ws_interp ws_interp_adequacy.

Section closed.
Context {go_gctx : GoGlobalContext} {go_lctx : GoLocalContext}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.
Context {sync_pkg : sync.Assumptions}.
Context {wsnet_pkg : wsnet.Assumptions} {wsrelay_pkg : wsrelay.Assumptions}.

Local Notation Input :=
  (TypeId go_string * IntegrateInput (A := go_string))%type.

(** [heapGS] at the ws instances, resolved once here so the theorem's
    codec hypothesis does not have to re-infer the FFI parameters inside
    its binder telescope. *)
Definition ws_heapGS (Σ : gFunctors) := heapGS Σ.

(** The server, closed: one node boots [server_boot] against an empty
    well-formed wire and an arbitrary environment that discharges
    [ws_env_preserves] for the deployment protocol. In EVERY reachable state
    of EVERY execution (crash-restarts included), EVERY message on the wire
    decodes to an honest batch: protocol totality. *)
Theorem ws_server_dist_adequate Σ `{!all.allG Σ} `{hPre: !gooseGpreS Σ}
    (* the store-layer specs are generalized over these RAs (the item-set,
       the accepted-id set, the reader-count tie); mirror them to apply the
       boot lemma, exactly as every wp file above the store does *)
    `{seq_inG : !inG Σ (authR (gmapUR loc (gsetUR (YjsItem go_string))))}
    `{acc_inG : !inG Σ (authR (gsetUR YjsId))}
    `{ftypes_inG : !inG Σ (dfrac_agreeR (leibnizO (gmap loc type_state)))}
    (host client : w64) (f : func.t)
    (decode : list u8 -> option (list Input))
    (coh0 : history_names -> ws_coh_ty Σ)
    g σ0 :
  ws_wf g.(global_world) ->
  g.(global_world).(ws_msgs) = ∅ ->
  σ0.(go_state).(package_state) = ∅ ->
  σ0.(go_state).(lang.go_lctx) = go_lctx ->
  (∀ γh, ⊢ coh0 γh ∅) ->
  (∀ (hG : ws_heapGS Σ) (sem' : go.Semantics),
      ⊢ codec_spec (hG := hG) (sem := sem') decode f) ->
  (∀ (W : wsGS Σ) (Hinv : invGS Σ) (γh : history_names),
      W.(ws_prot) = yjs_prot decode γh ->
      W.(ws_env_coh) = coh0 γh ->
      W.(ws_may) = g.(global_world).(ws_env_may) ->
      ⊢ is_history (A := go_string) (P := go_string) γh -∗
        @ws_env_preserves Σ W Hinv ⊤) ->
  dist_adequate (CS := goose_crash_lang)
    [ {| init_thread := server_boot (go_fns := sem.(go.sem_fn)) host client f;
         init_restart := halt;
         init_local_state := σ0 |} ] g
    (λ g', ∀ ch n d,
        g'.(global_world).(ws_msgs) !! (ch, n) = Some d ->
        ∃ inputs, decode d = Some inputs ∧ update_wf inputs).
Proof.
  intros Hwf Hempty Hpkg Hlctx0 Hcoh0 Hcodec Henv.
  eapply (ws_dist_adequacy_prot_fupd Σ); [exact Hwf | exact Hempty | done |].
  intros Hinv.
  iStartProof.
  (* allocate the history, then name the protocol *)
  iMod (history_alloc (A := go_string) (P := go_string) {[ uint.nat client ]} ⊤)
    as (γh) "[#Hhist Hels]".
  iDestruct (big_sepS_elem_of _ _ (uint.nat client) with "Hels") as "Hcl";
    first set_solver.
  iModIntro.
  iExists (yjs_prot decode γh), _, (coh0 γh).
  iSplitR; first iApply Hcoh0.
  iIntros (HG) "%Hp %Hc %Hm %Hi Hstart".
  iEval (rewrite -Hi) in "Hhist".
  iModIntro.
  iSplitL.
  - (* the one node *)
    rewrite /ws_wpd big_sepL_singleton /=.
    iIntros (hL) "%Hlctx Hffistart Hgo".
    (* [ws_wpd] pins the node's Go local context to the initial state's;
       substituting it makes the boot lemma's [sem]/[Assumptions] contexts
       (stated over the section's [go_lctx]) line up definitionally *)
    destruct hL as [hLcrash hLffi hLlctx hLna hLgs].
    simpl in Hlctx. rewrite Hlctx0 in Hlctx. subst hLlctx.
    iModIntro.
    iExists _, _, _.
    iApply (wpr_server_boot (hG := HeapGS _ _ HG _ _) _ _ _ _ γh σ0 Hpkg
              with "Hgo Hhist Hcl [] []").
    + intros d. rewrite Hp //.
    + iApply (Hcodec _ _).
    + (* [iApply]'s unification will not unfold the instance aliases
         ([goose_wsGS], the [irisGS] projection chain); passing both
         instances explicitly lets definitional conversion do it *)
      iEval (simpl).
      iApply (Henv (@goose_wsGS Σ HG)
                   (@iris_invGS (@goose_lang ws_op ws_model go_gctx (@ws_semantics go_gctx)) Σ
                      (@goose_irisGS ws_op ws_model (@ws_semantics go_gctx) go_gctx ws_interp Σ HG))
                   γh Hp Hc Hm).
      iExact "Hhist".
  - (* the export: protocol totality off the state interpretation *)
    iIntros (g') "Hctx".
    iDestruct "Hctx" as "(_ & _ & _ & _ & #Hprot & _ & _ & _)".
    iApply fupd_mask_intro; [set_solver | iIntros "_"].
    iAssert ([∗ map] k↦d ∈ g'.(global_world).(ws_msgs),
               ⌜∃ inputs, decode d = Some inputs ∧ update_wf inputs⌝)%I as "#Hpure".
    { iApply (big_sepM_mono with "Hprot").
      iIntros (k d Hk) "Hd".
      rewrite Hp.
      iDestruct "Hd" as (inputs) "(%Hdec & %Hwfb & _)".
      iPureIntro. eauto. }
    iDestruct (big_sepM_pure_1 with "Hpure") as %Hall.
    iPureIntro.
    intros ch n d Hlk. exact (Hall (ch, n) d Hlk).
Qed.

End closed.
