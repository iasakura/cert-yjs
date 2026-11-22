(** The verified Yjs WebSocket client (issue #131): one connection to a
    y-websocket server, one document, one root text, over the ws FFI. The
    client registers an update handler on its document ([Connect], over
    [wp_Doc__ObserveUpdate]) that sends the update of every transaction
    except the client's own applies; an application edits the document
    itself, with the document's own specifications ([Client.Doc] and
    [Client.Text] hand it [is_Doc] and [is_Text]); what the connection
    delivers is applied through the verified total apply path with the
    provider's origin ([Serve], over [wp_Doc__ApplyEncodedUpdate]); after
    every applied update, and when an application asks ([Client.Report]),
    the client writes the report of its root to the run's trace, under the
    trace protocol [is_report], as the server does (ws_relay.v).

    What the client proves about itself is the wire protocol: every message
    it sends satisfies [is_certified_update_message]. The store tells the update
    handler that the batch it is handed is certified and allowed by the
    document's insert rule ([is_update_callback]); the client's rule
    ([client_may_insert]) says that a batch of any origin but the provider's
    holds no surrogate code unit, which is what
    [is_certified_update_message_encode] asks. That is what makes the client a
    peer the server's theorem needs no assumption about.

    API
    - [provider_origin]: the origin the client applies received updates
      with; the update handler does not send their updates.
    - [client_may_insert origin unit]: the insert rule of a client's
      document: a transaction of the provider's origin may insert anything,
      any other only code units that are not surrogates.
    - [is_Client client_loc γs γh client_id send_channel receive_channel name]:
      the client at [client_loc]: its connection
      (send channel [send_channel], receive channel [receive_channel]), its document (store names
      [γs], client id [client_id]) in the deployment whose history is [γh], the
      root text [name] it reports on, and the lock that holds the
      connection's send cursor. Persistent: every field but the lock is
      written once, by [Connect].
    - [own_Client_receive_side γs receive_channel]: what the goroutine that runs [Serve]
      holds: the connection's receive cursor, and a read capability of the
      store for the report. The goroutine that runs the application holds a
      read capability alone ([own_read_cap]).
    - [client_app_spec app]: the contract of an application [Run] runs: with
      a client and a read capability of its store, it runs safely. An
      application has no contract of its own for its edits: it calls the
      document's operations, and their preconditions ask that what a
      transaction with no origin inserts satisfies [client_may_insert],
      that is, holds no surrogate code unit.
    - [wp_Connect] / [wp_Client__Doc] / [wp_Client__Text] /
      [wp_Client__Report] / [wp_Client__Serve] / [wp_Run] (a whole client
      around an application, what a closed-system theorem boots) /
      [wp_Typist] (an application: it types a script).

    The send cursor is under the client's send lock because the update
    handler runs in whichever goroutine ended a transaction, and its
    contract is proved once, at registration. *)
From New.proof Require Import proof_prelude.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import wsclient.
From New.proof Require Import prelude.
From New.proof.sync_proof Require Import base mutex rwmutex.
From New.goose_lang.ffi.ws_ffi Require Import ws_ffi.
From New.proof Require Import core.
From New.proof Require Import history.
From New.proof Require Import certified_update_message.
From New.proof.id Require Import id.
From New.proof.item Require Import item.
From New.proof.ytype Require Import ytype.
From New.proof.transaction Require Import transaction.
From New.proof.store Require Import store.
From New.proof.doc Require Import doc.
From New.proof.text Require Import text.
From New.proof.report Require Import report.
From New.proof Require Import deployment.
From iris.algebra Require Import auth gmap gset.
From iris.algebra.lib Require Import dfrac_agree.

(* iris.algebra pushes [nat_scope], retuning the default [<] / [≤]; the word
   arithmetic below writes [Z] comparisons unannotated, so restore [Z_scope]. *)
Local Open Scope Z_scope.

Section proof.
Context {Σ : gFunctors} {hG : heapGS Σ}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.
Context {sync_pkg : sync.Assumptions}.
Context {wsnet_pkg : wsnet.Assumptions} {wsclient_pkg : wsclient.Assumptions}.

#[global] Instance : IsPkgInit (iProp Σ) wsclient := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) wsclient := build_get_is_pkg_init_wf.

Set Default Proof Using "Type*".

Notation A := (list w16).
Notation P := go_string.
Local Notation TId := (TypeId P).
Local Notation Input := (TId * IntegrateInput (A := A))%type.
Local Notation Ev := (@Event (TId * @YjsOperation A)).
Local Notation DocModel := (gmap TId (list (YjsItem A))).

Context {seq_inG : inG Σ (authR (gmapUR loc (gsetUR (YjsItem A))))}.
Context {acc_inG : inG Σ (authR (gsetUR YjsId))}.
Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO store_state))}.
Context {observed_inG : ghost_varG Σ (list (YjsItem A * bool))}.
Context {observers_inG : inG Σ (authR (gsetUR (gname * go_string)))}.
Context {observers_agree_inG : inG Σ (dfrac_agreeR (leibnizO registered_entries))}.

(** The abstract codec the deployment runs under (see
    certified_update_message.v). *)
Context (decode : list u8 -> option (list Input)).
Context (encode : list Input -> list u8).

(* ===== definitions ======================================================== *)

(** The origin the client applies received updates with
    ([wsclient.providerOrigin]). *)
Definition provider_origin : go_string := "wsclient"%go.

(** [client_may_insert origin unit]: the insert rule of a client's document
    ([is_Doc]'s parameter). A transaction of the provider's origin may
    insert anything: it applies what the connection delivered, and its
    update is not sent. Any other transaction may insert only code units
    that are not UTF-16 surrogates ([unit_is_surrogate]): its update is
    sent, and the wire carries UTF-8, which has no encoding of a lone
    surrogate (issue #233). *)
Definition client_may_insert (origin : go_string) (unit : w16) : Prop :=
  origin = provider_origin ∨ ¬ unit_is_surrogate unit.

(** Client handle (persistent). The fields but the lock are written once,
    by [Connect]; the lock holds the connection's send cursor, at however
    many messages were sent. Beside its fields the handle carries the
    document's client pin with the empty history lower bound (what a read
    of the root for a report is certified against), the codec's
    specification ([codec_pair_spec], for the decoder
    in the struct and the encoder [Connect] registered the update handler
    with), and the deployment's protocols. *)
Definition is_Client (client_loc : loc) (γs : store_names) (γh : history_names)
    (client_id : ClientId) (send_channel receive_channel : chan_id) (name : go_string) : iProp Σ :=
  ∃ (connection : wsnet.Connection.t) (doc text s_loc : loc) (decoder : func.t),
    "#Hconnection_field" ∷ (client_loc .[(wsclient.Client.t), "conn"]) ↦□ connection ∗
    "#Hdoc_field"  ∷ (client_loc .[(wsclient.Client.t), "doc"]) ↦□ doc ∗
    "#Htext_field" ∷ (client_loc .[(wsclient.Client.t), "text"]) ↦□ text ∗
    "#Hname_field" ∷ (client_loc .[(wsclient.Client.t), "name"]) ↦□ name ∗
    "#Hdecode_field" ∷ (client_loc .[(wsclient.Client.t), "decode"]) ↦□ decoder ∗
    "#Hsend_lock" ∷ is_Mutex (client_loc .[(wsclient.Client.t), "sendMu"])
                      (∃ sent : nat, own_send_cursor send_channel sent) ∗
    "#Hconnection"    ∷ is_Connection connection send_channel receive_channel ∗
    "#Hdoc"     ∷ is_Doc doc s_loc γs γh client_may_insert ∗
    "#Htext"    ∷ is_Text text γs γh client_may_insert name [] ∅ ∗
    "#Hpin"     ∷ is_store_client γs client_id ∗
    "#Hhistory_lb"      ∷ is_history_lb γh client_id ([] : list Ev) ∗
    "#Hcodec_pair" ∷ (∃ encoder : func.t, codec_pair_spec decode encode decoder encoder) ∗
    "%Hdeploy"  ∷ ⌜deployment_protocols decode γh⌝.

(** The receive side of the client: the receive cursor of its connection
    and one read capability of its store ([Report] snapshots the root under
    the read lock). Held by the goroutine that runs [Serve]. *)
Definition own_Client_receive_side (γs : store_names) (receive_channel : chan_id) : iProp Σ :=
  ∃ received : nat, own_recv_cursor receive_channel received ∗ own_read_cap γs.

(** [client_app_spec app]: the application [app] runs safely with any
    client and a read capability of its store ([Run]'s argument).
    Persistent, as the codec specifications are: a property of the function
    value. *)
Definition client_app_spec (app : func.t) : iProp Σ :=
  □ (∀ (client_loc : loc) (γs : store_names) (γh : history_names) (client_id : ClientId)
       (send_channel receive_channel : chan_id) (name : go_string),
      {{{ is_pkg_init wsclient ∗
      is_Client client_loc γs γh client_id send_channel receive_channel name ∗ own_read_cap γs }}}
        #app #client_loc
      {{{ RET #(); True }}}).

#[global] Instance is_Client_persistent client_loc γs γh client_id send_channel receive_channel
    name :
  Persistent (is_Client client_loc γs γh client_id send_channel receive_channel name).
Proof. apply _. Qed.

(* ===== lemmas ============================================================= *)

(** [Doc]: the client's document, under the client's insert rule. An
    application edits it with the document's own specifications
    ([wp_Doc__Transact], [wp_Text__Insert]), and the update handler
    [Connect] registered sends what each transaction integrated. *)
Lemma wp_Client__Doc (client_loc : loc) (γs : store_names) (γh : history_names)
    (client_id : ClientId) (send_channel receive_channel : chan_id) (name : go_string) :
  {{{ is_pkg_init wsclient ∗
      is_Client client_loc γs γh client_id send_channel receive_channel name }}}
    client_loc @! (go.PointerType wsclient.Client) @! "Doc" #()
  {{{ (doc store_ref : loc), RET #doc; is_Doc doc store_ref γs γh client_may_insert }}}.
Proof.
  wp_start as "#Hclient".
  iNamed "Hclient".
  wp_auto.
  iApply "HΦ". iFrame "Hdoc".
Qed.

(** [Text]: the root text of the client's document, the one [Report]
    reports. *)
Lemma wp_Client__Text (client_loc : loc) (γs : store_names) (γh : history_names)
    (client_id : ClientId) (send_channel receive_channel : chan_id) (name : go_string) :
  {{{ is_pkg_init wsclient ∗
      is_Client client_loc γs γh client_id send_channel receive_channel name }}}
    client_loc @! (go.PointerType wsclient.Client) @! "Text" #()
  {{{ (text : loc), RET #text; is_Text text γs γh client_may_insert name [] ∅ }}}.
Proof.
  wp_start as "#Hclient".
  iNamed "Hclient".
  wp_auto.
  iApply "HΦ". iFrame "Htext".
Qed.

(** [Report]: the report of the root, as a read under the store's read lock
    sees it, goes to the run's trace under the deployment's trace protocol
    [is_report]; the certificate is the snapshot's exact read certificate. *)
Lemma wp_Client__Report (client_loc : loc) (γs : store_names) (γh : history_names)
    (client_id : ClientId) (send_channel receive_channel : chan_id) (name : go_string) :
  {{{ is_pkg_init wsclient ∗
      is_Client client_loc γs γh client_id send_channel receive_channel name ∗ own_read_cap γs }}}
    client_loc @! (go.PointerType wsclient.Client) @! "Report" #()
  {{{ RET #(); own_read_cap γs }}}.
Proof.
  wp_start as "(#Hclient & Hrcap)".
  iNamed "Hclient". destruct Hdeploy as [Hprot Htrace].
  wp_auto.
  wp_apply (wp_Text__Snapshot _ γs γh _ client_id _ [] ∅ [] with "[$Htext $Hpin $Hhistory_lb $Hrcap]").
  iIntros (chars_sl model) "(_ & Hrcap & Hchars & %Hsnap & Hstate & %Hexcl)".
  wp_auto.
  wp_apply (wp_EncodeReport _ chars_sl (DfracOwn 1) model with "[$Hchars]").
  iIntros (report_sl) "[Hchars Hreport]".
  iDestruct "Hreport" as (bytes) "(Hreport & Hreportcap & %Hreportdec)".
  wp_auto.
  wp_func_call.
  wp_apply (wp_Trace with "[$Hreport Hstate]").
  { rewrite Htrace. iDestruct "Hstate" as (h') "[_ #Hstate]".
    iExists client_id, h', _, model. iFrame "Hstate". iPureIntro.
    split; [exact (proj2 (proj2 Hsnap)) | exact Hreportdec]. }
  iIntros "Hreport".
  wp_auto.
  iApply "HΦ". iFrame "Hrcap".
Qed.

(** [sendUpdate], the client's update handler: it sends the update unless
    its origin is the provider's. The store tells it that the batch is
    certified and allowed by the document's rule for the origin
    ([own_emitted_update], the precondition of [is_update_callback]);
    for an origin that is not the provider's the rule says the batch holds
    no surrogate code unit, so the bytes satisfy the wire protocol
    ([is_certified_update_message_encode]). *)
Lemma wp_Client__sendUpdate (client_loc : loc) (γs : store_names) (γh : history_names)
    (client_id : ClientId) (send_channel receive_channel : chan_id) (name : go_string)
    (update_slice : slice.t) (structs : list Input) (origin : go_string) :
  {{{ is_pkg_init wsclient ∗
      is_Client client_loc γs γh client_id send_channel receive_channel name ∗
      own_emitted_update client_may_insert γh encode update_slice structs origin }}}
    client_loc @! (go.PointerType wsclient.Client) @! "sendUpdate" #update_slice #origin
  {{{ RET #(); True }}}.
Proof.
  wp_start as "(#Hclient & Hemitted)".
  iNamed "Hemitted". iRename "Hupdate_certified" into "Hcertified".
  rename Hupdate_units into Hunits.
  iNamed "Hclient". iDestruct "Hcodec_pair" as (encoder) "Hcodec_pair". iNamed "Hcodec_pair".
  destruct Hdeploy as [Hprot Htrace].
  wp_auto.
  destruct (decide (origin = "wsclient"%go)) as [Hprovider | Hlocal].
  { rewrite bool_decide_eq_true_2 //. wp_auto. by iApply "HΦ". }
  rewrite bool_decide_eq_false_2 //.
  (* the batch is not the provider's, so the rule says it holds no surrogate *)
  have Hfree : structs_surrogate_free structs.
  { move=> struct Hstruct unit Hunit.
    destruct (proj1 (Forall_forall _ _) (Hunits struct Hstruct) unit Hunit) as [Horigin | Hnot];
      [by destruct (Hlocal Horigin) | exact Hnot]. }
  iDestruct (is_certified_update_message_encode decode encode γh structs Hroundtrip Hfree with "Hcertified")
    as "#Hyprot".
  wp_auto.
  wp_apply (wp_Mutex__Lock with "[$Hsend_lock]"). iIntros "[Hlocked Hcursor]".
  iDestruct "Hcursor" as (sent) "Hcursor".
  wp_auto.
  wp_func_call.
  wp_apply (wp_Send with "[$Hconnection $Hupdate $Hcursor]").
  { rewrite Hprot. iFrame "Hyprot". }
  iIntros (err) "(Hupdate & Hsent)".
  wp_auto.
  wp_apply (wp_Mutex__Unlock with "[$Hsend_lock $Hlocked Hsent]").
  { iNext. iDestruct "Hsent" as "[[_ Hcursor] | [Hcursor _]]"; iExists _; iFrame "Hcursor". }
  by iApply "HΦ".
Qed.

(** [Serve]: the receive loop. It holds the client's receive side for the
    whole run and returns it when the connection stops delivering. Every
    message it receives satisfies the wire protocol, and the provider's
    origin may insert anything ([client_may_insert]), which is all
    [wp_Doc__ApplyEncodedUpdate] asks. *)
Lemma wp_Client__Serve (client_loc : loc) (γs : store_names) (γh : history_names)
    (client_id : ClientId) (send_channel receive_channel : chan_id) (name : go_string) :
  {{{ is_pkg_init wsclient ∗
      is_Client client_loc γs γh client_id send_channel receive_channel name ∗
      own_Client_receive_side γs receive_channel ∗ ws_env_preserves ⊤ }}}
    client_loc @! (go.PointerType wsclient.Client) @! "Serve" #()
  {{{ RET #(); own_Client_receive_side γs receive_channel }}}.
Proof.
  wp_start as "(#Hclient & Hside & #Henv)".
  iPoseProof "Hclient" as "Hopen". iNamed "Hopen".
  iDestruct "Hcodec_pair" as (encoder) "Hcodec_pair". iNamed "Hcodec_pair".
  destruct Hdeploy as [Hprot Htrace].
  iDestruct (is_Text_history with "Htext") as "#His_history".
  wp_auto.
  iAssert (∃ received : nat,
    "Hcursor" ∷ own_recv_cursor receive_channel received ∗
    "Hrcap" ∷ own_read_cap γs)%I with "[Hside]" as "IH".
  { iDestruct "Hside" as (received) "[Hcursor Hrcap]". iExists received. iFrame. }
  wp_for "IH".
  wp_func_call.
  wp_apply (wp_Receive with "[$Hconnection $Hcursor $Henv]").
  iIntros (err data_slice data) "(Hdata & Hdata_cap & Hreceived)".
  wp_auto.
  destruct err.
  - wp_auto. wp_for_post. iApply "HΦ". iExists received. iFrame.
  - iDestruct "Hreceived" as "(Hcursor & #Hmsg & #Hwire)".
    wp_auto.
    iAssert (is_certified_update_message decode γh data) as "#Hyprot".
    { rewrite -Hprot. iFrame "Hwire". }
    wp_apply (wp_Doc__ApplyEncodedUpdate decode _ s_loc γs γh client_may_insert client_id _ data_slice
                (DfracOwn 1) data provider_origin ltac:(move=> unit; by left)
               with "[$Hdoc $His_history $Hpin $Hcodec $Hdata $Hyprot]").
    iIntros (h inputs applied m') "(Hdata & %Hdecoded & #Hgrown & #Haccepts & #Happlied)".
    wp_auto.
    wp_apply (wp_Client__Report with "[$Hclient $Hrcap]").
    iIntros "Hrcap".
    wp_auto.
    wp_for_post. iFrame.
Qed.

(** [Connect]: dial, then create the document as [client], with the
    client's insert rule, and the root text, and register the update
    handler. On a failed dial there is no client and the history element
    is handed back untouched. Otherwise the caller gets the client, a read
    capability of its store for the goroutine that runs the application,
    and the receive side for the goroutine that runs [Serve]. *)
Lemma wp_Connect (host : w64) (path : go_string) (client : w64) (decoder encoder : func.t)
    (name : go_string) (γh : history_names) :
  deployment_protocols decode γh ->
  {{{ is_pkg_init wsclient ∗ is_history (A := A) (P := P) γh ∗
      own_client_history γh (uint.nat client) ([] : list Ev) ∗
      codec_pair_spec decode encode decoder encoder }}}
    @! wsclient.Connect #host #path #client #decoder #encoder #name
  {{{ (err : bool) (client_loc : loc), RET (#err, #client_loc);
      if err then own_client_history γh (uint.nat client) ([] : list Ev)
      else ∃ (γs : store_names) (send_channel receive_channel : chan_id),
             is_Client client_loc γs γh (uint.nat client) send_channel receive_channel name ∗
             own_read_cap γs ∗ own_Client_receive_side γs receive_channel }}}.
Proof.
  intros Hdeploy.
  wp_start as "(#His_history & Hhistory & #Hcodec_pair)".
  wp_auto.
  wp_func_call.
  wp_apply (wp_Connect host path).
  iIntros (err conn send_channel receive_channel) "Hconnected".
  wp_auto.
  destruct err.
  { wp_auto. iApply "HΦ". iFrame "Hhistory". }
  iDestruct "Hconnected" as "(#Hconnection & Hsend_cursor & Hrecv_cursor)".
  wp_auto.
  iDestruct (own_client_history_lb with "Hhistory") as "[Hhistory #Hhistory_lb]".
  wp_apply (wp_NewDoc γh client client_may_insert with "[$Hhistory]").
  (* the read capabilities come back with the document: one for each side
     of the client, the rest are kept unused here *)
  iIntros (dv s_loc γs) "(#Hdoc & #Hpin & Hrcaps)".
  destruct (Z.to_nat rwmutex.actualMaxReaders) as [|[|readers]] eqn:Hreaders.
  { exfalso. rewrite rwmutex.actualMaxReaders_unseal in Hreaders. lia. }
  { exfalso. rewrite rwmutex.actualMaxReaders_unseal in Hreaders. lia. }
  iEval (simpl) in "Hrcaps". iDestruct "Hrcaps" as "(Hrcap_send & Hrcap_receive & _)".
  wp_auto.
  wp_apply (wp_Doc__GetOrCreateText with "[$Hdoc $His_history]").
  iIntros (t) "#Htext".
  wp_auto.
  wp_alloc client_loc as "Hfields".
  iRename "doc" into "doc_local".
  iStructNamed "Hfields". simpl.
  (* the fields are written once; the lock takes the send cursor *)
  iPersist "conn doc text name decode".
  iMod (init_Mutex (∃ sent : nat, own_send_cursor send_channel sent) with "[$sendMu] [Hsend_cursor]")
    as "#Hsend_lock".
  { iNext. iExists 0%nat. iFrame "Hsend_cursor". }
  iAssert (is_Client client_loc γs γh (uint.nat client) send_channel receive_channel name) as "#Hclient".
  { iExists _, _, _, s_loc, _.
    iFrame "conn doc text name decode Hsend_lock Hconnection Hdoc Htext Hpin Hhistory_lb".
    iSplit; last done. iExists encoder. iFrame "Hcodec_pair". }
  iNamed "Hcodec_pair".
  wp_auto.
  (* the update handler reads the Go local [c], read-only from here on *)
  iPersist "c".
  wp_apply (wp_Doc__ObserveUpdate _ s_loc γs γh client_may_insert encode
              with "[$Hdoc $His_history $Hencoder]").
  { rewrite /is_update_callback.
    iIntros (update_slice structs origin Φ') "!> Hemitted HΦ'".
    wp_auto.
    wp_apply (wp_Client__sendUpdate with "[$Hclient $Hemitted]").
    by iApply "HΦ'". }
  iApply ("HΦ" $! false client_loc).
  iExists γs, send_channel, receive_channel. iFrame "Hclient Hrcap_send".
  iExists 0%nat. iFrame.
Qed.

(** [Run]: a whole client around an application: connect, serve on a
    goroutine with the receive side, and run the application with a read
    capability of the store. A closed-system theorem boots exactly this
    function, for any application that meets [client_app_spec]. *)
Lemma wp_Run (host : w64) (path : go_string) (client : w64) (decoder encoder : func.t)
    (name : go_string) (app : func.t) (γh : history_names) :
  deployment_protocols decode γh ->
  {{{ is_pkg_init wsclient ∗ is_history (A := A) (P := P) γh ∗
      own_client_history γh (uint.nat client) ([] : list Ev) ∗
      codec_pair_spec decode encode decoder encoder ∗
      ws_env_preserves ⊤ ∗ client_app_spec app }}}
    @! wsclient.Run #host #path #client #decoder #encoder #name #app
  {{{ RET #(); True }}}.
Proof.
  intros Hdeploy.
  wp_start as "(#Hhistory_inv & Hhistory & #Hcodec_values & #Henv & #Happ)".
  wp_auto.
  wp_apply (wp_Connect host path client decoder encoder name γh Hdeploy
              with "[$Hhistory_inv $Hhistory $Hcodec_values]").
  iIntros (err client_loc) "Hconnected".
  wp_auto.
  destruct err.
  { wp_auto. by iApply "HΦ". }
  iDestruct "Hconnected" as (γs send_channel receive_channel) "(#Hclient & Hsend & Hreceive)".
  wp_auto.
  wp_apply (wp_fork with "[Hreceive]").
  { wp_apply (wp_Client__Serve with "[$Hclient $Hreceive $Henv]"). iIntros "_". done. }
  wp_apply ("Happ" with "[$Hclient $Hsend]").
  by iApply "HΦ".
Qed.

(** [Typist]: an application for [Run]. It types its script one byte at a
    time at the end of the text, each byte as one code unit in its own
    transaction of the client's document ([wp_Doc__Transact]), and writes
    the report after each. A byte is below the surrogate range, so each
    transaction satisfies the document's rule, and the script needs no
    condition. *)
Lemma wp_Typist (script : go_string) :
  {{{ is_pkg_init wsclient }}}
    @! wsclient.Typist #script
  {{{ (app : func.t), RET #app; client_app_spec app }}}.
Proof.
  wp_start as "_".
  iApply wp_fupd.
  wp_auto.
  iPersist "script".
  iModIntro. iApply "HΦ".
  iIntros "!>" (client_loc γs γh client_id send_channel receive_channel name) "!>". iIntros (Ψ) "(#Hpkg' & #Hclient & Hsend) HΨ".
  wp_auto.
  wp_apply (wp_Client__Doc with "[$Hclient]"). iIntros (doc store_ref) "#Hdoc".
  wp_auto.
  wp_apply (wp_Client__Text with "[$Hclient]"). iIntros (text) "#Htext".
  wp_auto.
  iPersist "doc text".
  wp_apply wp_string_to_bytes. iIntros (units_slice) "[Hunits Hunits_cap]".
  wp_auto.
  iAssert (∃ (i : w64),
    "c" ∷ c_ptr ↦ client_loc ∗ "units" ∷ units_ptr ↦ units_slice ∗ "i" ∷ i_ptr ↦ i ∗
    "%Hi" ∷ ⌜0 ≤ sint.Z i⌝ ∗
    "Hsend" ∷ own_read_cap γs ∗
    "Hunits" ∷ units_slice ↦* script)%I with "[c units i Hsend Hunits]" as "IH".
  { iExists (W64 0). iFrame "c units i Hsend Hunits". done. }
  wp_for "IH".
  iDestruct (own_slice_len with "Hunits") as %[Hunits_length Hunits_nonneg].
  destruct (decide (sint.Z i < sint.Z units_slice.(slice.len))) as [Hinside | Hpast]; last first.
  { rewrite bool_decide_eq_false_2 //. wp_auto. by iApply "HΨ". }
  rewrite bool_decide_eq_true_2 //.
  wp_auto.
  rewrite decide_True; last (clear -Hinside Hi; word).
  have [unit Hunit] : is_Some (script !! sint.nat i).
  { apply lookup_lt_is_Some. clear -Hinside Hi Hunits_length. word. }
  iDestruct (own_slice_elem_acc (sint.Z i) unit units_slice (DfracOwn 1) script with "Hunits")
    as "[Helem Hgive]".
  { clear -Hinside Hi. word. }
  { exact Hunit. }
  wp_auto.
  iDestruct ("Hgive" $! unit with "Helem") as "Hunits".
  iEval (rewrite (list_insert_id _ _ _ Hunit)) in "Hunits".
  wp_apply wp_slice_literal. iSplitR; first done. iIntros "%literal [Hliteral _]". wp_auto.
  replace (sint.nat (W64 0)) with 0%nat by word. iEval (simpl) in "Hliteral".
  (* a byte is below the surrogate range *)
  have Hbyte : Forall (client_may_insert ""%go) [W16 (uint.Z unit)].
  { apply Forall_singleton. right. rewrite /unit_is_surrogate. word. }
  wp_apply (wp_Doc__Transact _ store_ref γs γh client_may_insert _ (λ _ _ _ _ _, True)%I
              with "[$Hdoc unit Hliteral]").
  { rewrite /closure_runs_transaction.
    iIntros (tr c' h m pend deleted Ψ') "Htx HΨ'".
    wp_auto.
    wp_apply (wp_Text__CodeUnitsIn with "[$Htext $Htx]").
    iIntros (visible_slice) "(_ & Htx & Hvisible & Hvisible_cap)".
    wp_auto.
    wp_apply (wp_Text__InsertIn with "[$Htext $Htx $Hliteral]").
    iIntros (L' ins h' m' k0 originLeft originRight)
      "(#Htext' & Htx & Hliteral & %Hrun & %Hreplaced & #Hcerts)".
    iDestruct (own_transaction_item_unique with "Htx") as %Hunique.
    wp_auto.
    iApply ("HΨ'" $! h' m' pend deleted (∅ ∪ char_ids ins) ∅
              (∅ ∪ (if decide (ins = []) then ∅ else {[name]}))).
    iFrame "Htx". iSplit; last done. iPureIntro.
    (* what the transaction inserted is the one byte *)
    exact (inserted_run_units_allowed _ m' name [] L' ins _ c' k0 originLeft originRight
             Hrun (proj1 Hreplaced) Hunique Hbyte). }
  iIntros "_".
  wp_auto.
  wp_apply (wp_Client__Report with "[$Hclient $Hsend]").
  iIntros "Hsend".
  wp_auto.
  wp_for_post. iFrame. iPureIntro. clear -Hinside Hi. word.
Qed.

End proof.
