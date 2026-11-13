(** The closed-system theorem for the verified server together with
    verified clients (issue #131; issue #132, part 2).

    One node boots the verified server ([server_boot], ws_server.v) and one
    node per client boots the scripted client ([client_boot]: initialize
    the packages, then [wsclient.Run], which connects, serves on a
    goroutine and types its script). The theorem pushes all of them through
    [ws_dist_adequacy_prot_fupd] with the real wire protocol
    [yjs_prot decode γh] and exports, about EVERY reachable state of EVERY
    execution, what the server's theorem exports: every message on the wire
    decodes to an honest batch, and the run's trace converges
    ([reports_converge]). The trace now holds the reports of every node, so
    the convergence compares replicas: any two reports, from any two nodes,
    about the same root that hold the same ids spell the same text.

    What is gone, against [ws_server_dist_adequate], is the assumption about
    the peers: there is no [ws_env_preserves] hypothesis. The environment
    of this theorem never sends (the initial world's send relation permits
    nothing), so the assumption is proved inside ([ws_env_preserves_silent]),
    and everything that does send is a verified node. What remains trusted
    is the codec: [codec_spec] for the decoder value, [encoder_spec] for the
    encoder value, and the contract between the two, [codec_roundtrip].

    Crash-restart halts, as for the server: a crashed client has lost its
    document with the heap. *)
From Perennial.program_logic Require Import recovery_weakestpre dist_weakestpre dist_adequacy.
From Perennial.goose_lang Require Import adequacy crash_modality recovery_lifting dist_lifting.
From New.proof Require Import proof_prelude.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import wsrelay.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import wsclient.
From New.proof Require Import prelude.
From New.proof.sync_proof Require Import base mutex rwmutex.
From New.goose_lang.ffi.ws_ffi Require Import ws_ffi.
From New.goose_lang.ffi.ws_ffi Require Import adequacy_prot.
From New.proof Require Import core.
From New.proof Require Import history.
From New.proof Require Import yjs_prot.
From New.proof.store Require Import store.
From New.proof.doc Require Import doc.
From New.proof.report Require Import report.
From New.proof Require Import deployment.
From New.proof Require Import ws_relay.
From New.proof Require Import ws_client.
From New.proof.demo Require Import ws_server.
From iris.algebra Require Import auth gmap gset.
From iris.algebra.lib Require Import dfrac_agree.

Local Open Scope Z_scope.

(** One client node of the system: the path it connects to, the client id
    of its document, and the script it types. *)
Record client_config := ClientConfig {
  client_path : go_string;
  client_id : w64;
  client_script : go_string;
}.

(** Initialize the packages, then run the translated scripted client
    [wsclient.Run] (connect to [host] at [path], create the document as
    client [client], serve on a goroutine, type [script] at the end of the
    root text [name]). A real deployment is
    [func main() { wsclient.Run(host, path, client, yjs.WireCodec(),
    yjs.WireEncoder(), "root", script) }]. Defined outside any [heapGS]
    section so a closed theorem can name it before any node exists. *)
Definition client_boot {go_gctx : GoGlobalContext}
    {go_lctx : GoLocalContext} {go_fns : GoSemanticsFunctions}
    (host : w64) (path : go_string) (client : w64) (decoder encoder : func.t)
    (name script : go_string) : expr :=
  wsclient.initialize' #();;
  (@! wsclient.Run) #host #path #client #decoder #encoder #name #script.

Section boot.
Context {Σ : gFunctors} {hG : heapGS Σ}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.
Context {sync_pkg : sync.Assumptions}.
Context {wsnet_pkg : wsnet.Assumptions} {wsclient_pkg : wsclient.Assumptions}.

Set Default Proof Using "Type*".

Notation A := (list w16).
Notation P := go_string.
Local Notation TId := (TypeId P).
Local Notation Input := (TId * IntegrateInput (A := A))%type.
Local Notation Ev := (@Event (TId * @YjsOperation A)).

Context {seq_inG : inG Σ (authR (gmapUR loc (gsetUR (YjsItem (list w16)))))}.
Context {acc_inG : inG Σ (authR (gsetUR YjsId))}.
Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO store_state))}.
Context {observed_inG : ghost_varG Σ (list (YjsItem (list w16) * bool))}.
Context {observers_inG : inG Σ (authR (gsetUR (gname * go_string)))}.
Context {observers_agree_inG : inG Σ (dfrac_agreeR (leibnizO registered_entries))}.

Context (decode : list u8 -> option (list Input)).
Context (encode : list Input -> list u8).

(* ===== package initialization ============================================ *)

Lemma wp_wsclient_initialize' get_is_pkg_init :
  get_is_pkg_init_prop wsclient get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init }}}
    wsclient.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init wsclient }}}.
Proof.
  intros Hinit. wp_start as "Hown".
  wp_apply (wp_package_init with "[$Hown] HΦ").
  { destruct Hinit as (-> & ?); done. }
  iIntros "Hown". wp_auto.
  wp_apply (wp_yjs_initialize' with "[$Hown]") as "(Hown & #?)".
  { naive_solver. }
  wp_apply (wp_wsnet_initialize' with "[$Hown]") as "(Hown & #?)".
  { naive_solver. }
  iEval (rewrite is_pkg_init_unfold /=). iFrame "∗#". done.
Qed.

(* ===== the boot expression =============================================== *)

Lemma wp_client_boot (host : w64) (path : go_string) (client : w64)
    (decoder encoder : func.t) (name script : go_string)
    (γh : history_names) get_is_pkg_init :
  get_is_pkg_init_prop wsclient get_is_pkg_init →
  deployment_protocols decode γh →
  ⊢ own_initializing get_is_pkg_init -∗
    is_history (A := A) (P := P) γh -∗
    own_client_history γh (uint.nat client) ([] : list Ev) -∗
    codec_pair_spec decode encode decoder encoder -∗
    ws_env_preserves ⊤ -∗
    WP client_boot host path client decoder encoder name script {{ _, True }}.
Proof.
  iIntros (Hget Hdeploy) "Hown #Hhist Hhistory #Hcodec_pair #Henv".
  rewrite /client_boot.
  wp_apply (wp_wsclient_initialize' with "[$Hown]") as "(Hown & #Hinit)";
    first exact Hget.
  wp_apply (wp_Run decode encode host path client decoder encoder name script γh Hdeploy
             with "[$Hhist $Hhistory $Hcodec_pair $Henv]").
  done.
Qed.

(* ===== the package-init map ============================================== *)

(** The packages of the client's transitive import tree; anything else maps
    to [True] (nothing else is ever initialized by this boot). *)
Definition client_get_is_pkg_init : go_string → iProp Σ :=
  λ nm,
    if decide (nm = wsclient) then is_pkg_init wsclient
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

Lemma client_get_is_pkg_init_wf :
  get_is_pkg_init_prop wsclient client_get_is_pkg_init.
Proof.
  rewrite /get_is_pkg_init_prop /=.
  repeat split;
    rewrite /client_get_is_pkg_init;
    repeat first [ rewrite decide_True; [reflexivity | reflexivity]
                 | rewrite decide_False; last by discriminate ].
Qed.

(* ===== crash recovery: a dead client is a safe client ==================== *)

(** The client node's whole crash-aware obligation, as [wpr_server_boot] is
    the server's: initialize, run the boot, and after any crash come back
    up as [halt]. *)
Lemma wpr_client_boot (host : w64) (path : go_string) (client : w64)
    (decoder encoder : func.t) (name script : go_string)
    (γh : history_names) (σ : lang.state) :
  is_init σ →
  deployment_protocols decode γh →
  ⊢ own_go_state σ.(go_state).(package_state) -∗
    is_history (A := A) (P := P) γh -∗
    own_client_history γh (uint.nat client) ([] : list Ev) -∗
    codec_pair_spec decode encode decoder encoder -∗
    ws_env_preserves ⊤ -∗
    wpr NotStuck ⊤ (client_boot host path client decoder encoder name script) halt
        (λ _, True%I) (λ _, True%I) (λ _ _, True%I).
Proof.
  iIntros (Hinit Hdeploy) "Hgo #Hhist Hhistory #Hcodec_pair #Henv".
  iApply fupd_wpr.
  iMod (go_init client_get_is_pkg_init _ Hinit with "Hgo") as "Hown".
  iModIntro.
  iApply (idempotence_wpr NotStuck ⊤ _ _ _
            (λ _, True%I) (λ _ _, True%I) (λ _, True%I) with "[-] []").
  - iApply wp_wpc.
    iApply (wp_client_boot _ _ _ _ _ _ _ _ client_get_is_pkg_init
              client_get_is_pkg_init_wf Hdeploy
              with "Hown Hhist Hhistory Hcodec_pair Henv").
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

(* ===== the environment of a closed system ================================ *)

(** An environment that never sends satisfies the one assumption the ws FFI
    makes about peers the theorem does not run, for any coherence: the
    assumption's first premise is that the send relation permits the
    message. *)
Lemma ws_env_preserves_silent Σ (W : wsGS Σ) (Hinv : invGS Σ) (E : coPset) :
  (∀ messages channel data, ¬ W.(ws_may) messages channel data) ->
  ⊢ @ws_env_preserves Σ W Hinv E.
Proof.
  intros Hsilent. rewrite /ws_env_preserves.
  iIntros "!>" (g r n data) "%Hmay". exfalso. exact (Hsilent _ _ _ Hmay).
Qed.

(* ===== the closed-system theorem ========================================= *)

Existing Instances ws_op ws_model ws_semantics ws_interp ws_interp_adequacy.

Section closed.
Context {go_gctx : GoGlobalContext} {go_lctx : GoLocalContext}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.
Context {sync_pkg : sync.Assumptions}.
Context {wsnet_pkg : wsnet.Assumptions} {wsrelay_pkg : wsrelay.Assumptions}.
Context {wsclient_pkg : wsclient.Assumptions}.

Local Notation Input :=
  (TypeId go_string * IntegrateInput (A := (list w16)))%type.

(** The node of one client: its boot expression, [halt] on restart, the
    shared initial local state. *)
Definition client_node (host : w64) (decoder encoder : func.t) (name : go_string)
    (σ0 : lang.state) (config : client_config) : node_init_cfg :=
  {| init_thread := client_boot (go_fns := sem.(go.sem_fn)) host config.(client_path)
                      config.(client_id) decoder encoder name config.(client_script);
     init_restart := halt;
     init_local_state := σ0 |}.

(** The system, closed: one node boots the verified server and one node per
    entry of [clients] boots the verified scripted client, against an empty
    well-formed wire and an environment that never sends. In EVERY reachable
    state of EVERY execution (crash-restarts included), EVERY message on the
    wire decodes to an honest batch (protocol totality), and the run's trace
    converges ([reports_converge]): any two reports, written by any two
    nodes, about the same root that hold the same ids spell the same text.

    Trusted, beyond the semantics: the two codec values meet their
    specifications ([codec_spec], [encoder_spec]) and the two abstract
    halves round-trip ([codec_roundtrip]). Nothing is assumed about peers:
    every sender is one of these nodes. The nodes' client ids are distinct,
    as Yjs requires of replicas. *)
Theorem ws_system_dist_adequate Σ `{!all.allG Σ} `{hPre: !gooseGpreS Σ}
    `{seq_inG : !inG Σ (authR (gmapUR loc (gsetUR (YjsItem (list w16)))))}
    `{acc_inG : !inG Σ (authR (gsetUR YjsId))}
    `{ftypes_inG : !inG Σ (dfrac_agreeR (leibnizO store_state))}
    `{observed_inG : !ghost_varG Σ (list (YjsItem (list w16) * bool))}
    `{observers_inG : !inG Σ (authR (gsetUR (gname * go_string)))}
    `{observers_agree_inG : !inG Σ (dfrac_agreeR (leibnizO registered_entries))}
    (host server_client : w64) (decoder encoder : func.t) (name : go_string)
    (decode : list u8 -> option (list Input)) (encode : list Input -> list u8)
    (clients : list client_config)
    g σ0 :
  ws_wf g.(global_world) ->
  g.(global_world).(ws_msgs) = ∅ ->
  g.(global_world).(ws_trace) = [] ->
  (∀ messages channel data, ¬ g.(global_world).(ws_env_may) messages channel data) ->
  σ0.(go_state).(package_state) = ∅ ->
  σ0.(go_state).(lang.go_lctx) = go_lctx ->
  NoDup (uint.nat server_client :: ((λ config, uint.nat config.(client_id)) <$> clients)) ->
  (∀ (hG : ws_heapGS Σ) (sem' : go.Semantics),
      ⊢ codec_spec (hG := hG) (sem := sem') decode decoder) ->
  (∀ (hG : ws_heapGS Σ) (sem' : go.Semantics),
      ⊢ encoder_spec (hG := hG) (sem := sem') encode encoder) ->
  codec_roundtrip decode encode ->
  dist_adequate (CS := goose_crash_lang)
    ({| init_thread := server_boot (go_fns := sem.(go.sem_fn)) host server_client decoder name;
        init_restart := halt;
        init_local_state := σ0 |}
     :: (client_node host decoder encoder name σ0 <$> clients)) g
    (λ g',
       (∀ ch n d,
          g'.(global_world).(ws_msgs) !! (ch, n) = Some d ->
          ∃ inputs, decode d = Some inputs ∧ update_wf inputs) ∧
       reports_converge g'.(global_world).(ws_trace)).
Proof.
  intros Hwf Hempty Htrace Hsilent Hpkg Hlctx0 Hdistinct Hcodec Hencoder Hroundtrip.
  eapply (ws_dist_adequacy_prot_fupd Σ); [exact Hwf | exact Hempty | exact Htrace | done |].
  intros Hinv.
  iStartProof.
  (* allocate the history for every node's client id, then name the protocol *)
  iMod (history_alloc (A := (list w16)) (P := go_string)
          (list_to_set (uint.nat server_client :: ((λ config, uint.nat config.(client_id)) <$> clients))) ⊤)
    as (γh) "[#Hhist Hels]".
  rewrite big_sepS_list_to_set; last exact Hdistinct.
  iDestruct "Hels" as "[Hserver_history Hclient_histories]".
  rewrite big_sepL_fmap.
  iModIntro.
  iExists (yjs_prot decode γh), _, (is_report γh), _, (λ _, True%I).
  iSplitR; first done.
  iIntros (HG) "%Hp %Ht %Hc %Hm %Hi Hstart".
  iEval (rewrite -Hi) in "Hhist".
  iModIntro.
  iSplitL.
  - rewrite /ws_wpd big_sepL_cons. iSplitL "Hserver_history".
    + (* the server node *)
      iIntros (hL) "%Hlctx Hffistart Hgo".
      destruct hL as [hLcrash hLffi hLlctx hLna hLgs].
      simpl in Hlctx. rewrite Hlctx0 in Hlctx. subst hLlctx.
      iModIntro.
      iExists _, _, _.
      iApply (wpr_server_boot (hG := HeapGS _ _ HG _ _) _ _ _ _ _ γh σ0 Hpkg
                with "Hgo Hhist Hserver_history [] []").
      * split; intros d; [rewrite Hp // | rewrite Ht //].
      * iApply (Hcodec _ _).
      * iEval (simpl).
        iApply (ws_env_preserves_silent Σ (@goose_wsGS Σ HG)
                  (@iris_invGS (@goose_lang ws_op ws_model go_gctx (@ws_semantics go_gctx)) Σ
                     (@goose_irisGS ws_op ws_model (@ws_semantics go_gctx) go_gctx ws_interp Σ HG))).
        intros messages channel data. rewrite Hm. apply Hsilent.
    + (* one client node per configuration *)
      rewrite big_sepL_fmap.
      iApply (big_sepL_impl with "Hclient_histories").
      iIntros "!>" (k config Hk) "Hclient_history".
      iIntros (hL) "%Hlctx Hffistart Hgo".
      destruct hL as [hLcrash hLffi hLlctx hLna hLgs].
      simpl in Hlctx. rewrite Hlctx0 in Hlctx. subst hLlctx.
      iModIntro.
      iExists _, _, _.
      iApply (wpr_client_boot (hG := HeapGS _ _ HG _ _) decode encode _ _ _ _ _ _ _ γh σ0 Hpkg
                with "Hgo Hhist Hclient_history [] []").
      * split; intros d; [rewrite Hp // | rewrite Ht //].
      * (* the codec values, as trusted *)
        iSplit; first iApply (Hcodec _ _).
        iSplit; first iApply (Hencoder _ _).
        done.
      * iEval (simpl).
        iApply (ws_env_preserves_silent Σ (@goose_wsGS Σ HG)
                  (@iris_invGS (@goose_lang ws_op ws_model go_gctx (@ws_semantics go_gctx)) Σ
                     (@goose_irisGS ws_op ws_model (@ws_semantics go_gctx) go_gctx ws_interp Σ HG))).
        intros messages channel data. rewrite Hm. apply Hsilent.
  - (* the export: protocol totality and report convergence off the state
       interpretation, as for the server alone *)
    iIntros (g') "Hctx".
    iDestruct "Hctx" as "(_ & _ & _ & _ & #Hprot & #Htrace & _ & _ & _)".
    iEval (rewrite Hi) in "Hhist".
    iMod (is_report_trace_converge (invGS0 := Hinv) γh g'.(global_world).(ws_trace) ⊤
            with "Hhist []") as %Hconv; first solve_ndisj.
    { iApply (big_sepL_mono with "Htrace").
      iIntros (k d Hk) "Hd". rewrite Ht. iExact "Hd". }
    iApply fupd_mask_intro; [set_solver | iIntros "_"].
    iAssert ([∗ map] k↦d ∈ g'.(global_world).(ws_msgs),
               ⌜∃ inputs, decode d = Some inputs ∧ update_wf inputs⌝)%I as "#Hpure".
    { iApply (big_sepM_mono with "Hprot").
      iIntros (k d Hk) "Hd".
      rewrite Hp.
      iDestruct "Hd" as (inputs) "(%Hdecodes & %Hwfb & _)".
      iPureIntro. destruct Hdecodes as (decoded & Hdec & Hsame). exists decoded.
      split; first exact Hdec.
      exact (update_wf_same_wire_struct decoded inputs Hsame Hwfb). }
    iDestruct (big_sepM_pure_1 with "Hpure") as %Hall.
    iPureIntro. split; last exact Hconv.
    intros ch n d Hlk. exact (Hall (ch, n) d Hlk).
Qed.

End closed.
