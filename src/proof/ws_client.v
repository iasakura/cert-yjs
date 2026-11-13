(** The verified Yjs WebSocket client (issue #131): one connection to a
    y-websocket server, one document, one root text, over the ws FFI. A
    local edit is inserted, encoded and sent in one call ([Insert], over
    [wp_Text__InsertEncoded]); what the connection delivers is applied
    through the verified total apply path ([Serve], over
    [wp_Doc__ApplyEncodedUpdate]); after every local edit and every applied
    update the client writes the report of its root to the run's trace,
    under the trace protocol [is_report], as the server does (ws_relay.v).

    What the client proves about itself is the wire protocol: every message
    it sends satisfies [yjs_prot], with the certificates its own inserts
    minted ([yjs_prot_encode_inserted_run]). That is what makes it a peer
    the server's theorem needs no assumption about.

    API
    - [is_Client cl γs γh c sc rc name]: the client at [cl]: its connection
      (send channel [sc], receive channel [rc]), its document (store names
      [γs], client id [c]) in the deployment whose history is [γh], and the
      root text [name] it edits and reports on. Persistent: every field is
      written once, by [Connect].
    - [own_Client_send_side γs sc]: what the goroutine that calls [Insert]
      holds: the connection's send cursor, and a read capability of the
      store for the report.
    - [own_Client_receive_side γs rc]: the same for the goroutine that runs
      [Serve], with the receive cursor.
    - [wp_Connect] / [wp_Client__Insert] / [wp_Client__Serve] / [wp_Run]
      (the scripted client, which the closed-system theorem in
      src/proof/demo/ws_system.v boots).

    The client has no lock of its own: its send side stays with the
    goroutine that calls [Insert], its receive side with [Serve], and the
    document's lock orders an apply against a local edit. *)
From New.proof Require Import proof_prelude.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import wsclient.
From New.proof Require Import prelude.
From New.proof.sync_proof Require Import base mutex rwmutex.
From New.goose_lang.ffi.ws_ffi Require Import ws_ffi.
From New.proof Require Import core.
From New.proof Require Import history.
From New.proof Require Import yjs_prot.
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

(** The abstract codec the deployment runs under (see yjs_prot.v). *)
Context (decode : list u8 -> option (list Input)).
Context (encode : list Input -> list u8).

(* ===== definitions ======================================================== *)

(** Client handle (persistent). The struct is written once, by [Connect];
    beside its fields the handle carries the global-history handle, the
    document's client pin with the empty history lower bound (what a read
    of the root for a report is certified against), the specifications of
    the two codec values with the contract between them, and the
    deployment's protocols. *)
Definition is_Client (cl : loc) (γs : store_names) (γh : history_names)
    (c : ClientId) (sc rc : chan_id) (name : go_string) : iProp Σ :=
  ∃ (client_value : wsclient.Client.t) (s_loc : loc),
    "#Hfields"  ∷ cl ↦□ client_value ∗
    "%Hname"    ∷ ⌜client_value.(wsclient.Client.name') = name⌝ ∗
    "#Hconn"    ∷ is_Connection client_value.(wsclient.Client.conn') sc rc ∗
    "#Hdoc"     ∷ is_Doc client_value.(wsclient.Client.doc') s_loc γs γh ∗
    "#Htext"    ∷ is_Text client_value.(wsclient.Client.text') γs γh name [] ∅ ∗
    "#Hishist"  ∷ is_history (A := A) (P := P) γh ∗
    "#Hpin"     ∷ is_store_client γs c ∗
    "#Hlb"      ∷ is_history_lb γh c ([] : list Ev) ∗
    "#Hcodec"   ∷ codec_spec decode client_value.(wsclient.Client.decode') ∗
    "#Hencoder" ∷ encoder_spec encode client_value.(wsclient.Client.encode') ∗
    "%Hroundtrip" ∷ ⌜codec_roundtrip decode encode⌝ ∗
    "%Hdeploy"  ∷ ⌜deployment_protocols decode γh⌝.

(** The send side of the client: the send cursor of its connection, at
    however many messages it has sent, and one read capability of its
    store ([report] snapshots the root under the read lock). Held by the
    goroutine that calls [Insert]. *)
Definition own_Client_send_side (γs : store_names) (sc : chan_id) : iProp Σ :=
  ∃ n : nat, own_send_cursor sc n ∗ own_read_cap γs.

(** The receive side of the client: the receive cursor of its connection
    and one read capability of its store. Held by the goroutine that runs
    [Serve]. *)
Definition own_Client_receive_side (γs : store_names) (rc : chan_id) : iProp Σ :=
  ∃ n : nat, own_recv_cursor rc n ∗ own_read_cap γs.

#[global] Instance is_Client_persistent cl γs γh c sc rc name :
  Persistent (is_Client cl γs γh c sc rc name).
Proof. apply _. Qed.

(* ===== lemmas ============================================================= *)

(** [report]: the report of the root, as a read under the store's read lock
    sees it, goes to the run's trace under the deployment's trace protocol
    [is_report]; the certificate is the snapshot's exact read certificate. *)
Lemma wp_Client__report (cl : loc) (γs : store_names) (γh : history_names)
    (c : ClientId) (sc rc : chan_id) (name : go_string) :
  {{{ is_pkg_init wsclient ∗ is_Client cl γs γh c sc rc name ∗ own_read_cap γs }}}
    cl @! (go.PointerType wsclient.Client) @! "report" #()
  {{{ RET #(); own_read_cap γs }}}.
Proof.
  wp_start as "(#Hclient & Hrcap)".
  iNamed "Hclient". subst name. destruct Hdeploy as [Hprot Htrace].
  wp_auto.
  wp_apply (wp_Text__Snapshot _ γs γh c _ [] ∅ [] with "[$Htext $Hpin $Hlb $Hrcap]").
  iIntros (chars_sl model) "(_ & Hrcap & Hchars & %Hsnap & Hstate & %Hexcl)".
  wp_auto.
  wp_apply (wp_EncodeReport _ chars_sl (DfracOwn 1) model with "[$Hchars]").
  iIntros (report_sl) "[Hchars Hreport]".
  iDestruct "Hreport" as (bytes) "(Hreport & Hreportcap & %Hreportdec)".
  wp_auto.
  wp_func_call.
  wp_apply (wp_Trace with "[$Hreport Hstate]").
  { rewrite Htrace. iDestruct "Hstate" as (h') "[_ #Hstate]".
    iExists c, h', _, model. iFrame "Hstate". iPureIntro.
    split; [exact (proj2 (proj2 Hsnap)) | exact Hreportdec]. }
  iIntros "Hreport".
  wp_auto.
  iApply "HΦ". iFrame "Hrcap".
Qed.

(** [Insert]: one local edit, sent. The caller holds the client's send
    side and gets it back. The code units are free of surrogates: then the
    update [Text.InsertEncoded] returns satisfies the wire protocol
    ([yjs_prot_encode_inserted_run]), which is what [Send] asks of it. *)
Lemma wp_Client__Insert (cl : loc) (γs : store_names) (γh : history_names)
    (c : ClientId) (sc rc : chan_id) (name : go_string)
    (index : w64) (content_slice : slice.t) (dq : dfrac) (units : A) :
  units_surrogate_free units ->
  {{{ is_pkg_init wsclient ∗ is_Client cl γs γh c sc rc name ∗
      own_Client_send_side γs sc ∗ content_slice ↦*{dq} units }}}
    cl @! (go.PointerType wsclient.Client) @! "Insert" #index #content_slice
  {{{ (err : bool), RET #err;
      own_Client_send_side γs sc ∗ content_slice ↦*{dq} units }}}.
Proof.
  intros Hunits.
  wp_start as "(#Hclient & Hside & Hcontent)".
  iPoseProof "Hclient" as "Hopen". iNamed "Hopen".
  destruct Hdeploy as [Hprot Htrace].
  iDestruct "Hside" as (sent) "[Hcursor Hrcap]".
  wp_auto.
  wp_apply (wp_Text__InsertEncoded _ index content_slice dq units γs γh name [] ∅ encode
              with "[$Htext $Hcontent $Hencoder]").
  iIntros (bytes_slice L' ins client k0 originLeft originRight structs)
    "(_ & Hcontent & %Hrun & #Hcerts & Hbytes & Hbytes_cap & %Hstructs)".
  iDestruct (yjs_prot_encode_inserted_run decode encode γh name [] L' ins units client k0
               originLeft originRight structs Hroundtrip Hunits Hrun Hstructs with "Hcerts")
    as "#Hyprot".
  wp_auto.
  wp_func_call.
  wp_apply (wp_Send with "[$Hconn $Hbytes $Hcursor]").
  { rewrite Hprot. iFrame "Hyprot". }
  iIntros (err) "(Hbytes & Hsent)".
  wp_auto.
  wp_apply (wp_Client__report with "[$Hclient $Hrcap]").
  iIntros "Hrcap".
  wp_auto.
  iApply "HΦ". iFrame "Hcontent".
  iDestruct "Hsent" as "[[_ Hcursor] | [Hcursor _]]"; iExists _; iFrame "Hcursor Hrcap".
Qed.

(** [Serve]: the receive loop. It holds the client's receive side for the
    whole run and returns it when the connection stops delivering. Every
    message it receives satisfies the wire protocol, which is all
    [wp_Doc__ApplyEncodedUpdate] asks. *)
Lemma wp_Client__Serve (cl : loc) (γs : store_names) (γh : history_names)
    (c : ClientId) (sc rc : chan_id) (name : go_string) :
  {{{ is_pkg_init wsclient ∗ is_Client cl γs γh c sc rc name ∗
      own_Client_receive_side γs rc ∗ ws_env_preserves ⊤ }}}
    cl @! (go.PointerType wsclient.Client) @! "Serve" #()
  {{{ RET #(); own_Client_receive_side γs rc }}}.
Proof.
  wp_start as "(#Hclient & Hside & #Henv)".
  iPoseProof "Hclient" as "Hopen". iNamed "Hopen".
  destruct Hdeploy as [Hprot Htrace].
  wp_auto.
  iAssert (∃ received : nat,
    "Hcursor" ∷ own_recv_cursor rc received ∗
    "Hrcap" ∷ own_read_cap γs)%I with "[Hside]" as "IH".
  { iDestruct "Hside" as (received) "[Hcursor Hrcap]". iExists received. iFrame. }
  wp_for "IH".
  wp_func_call.
  wp_apply (wp_Receive with "[$Hconn $Hcursor $Henv]").
  iIntros (err data_slice data) "(Hdata & Hdata_cap & Hreceived)".
  wp_auto.
  destruct err.
  - wp_auto. wp_for_post. iApply "HΦ". iExists received. iFrame.
  - iDestruct "Hreceived" as "(Hcursor & #Hmsg & #Hwire)".
    wp_auto.
    iAssert (yjs_prot decode γh data) as "#Hyprot".
    { rewrite -Hprot. iFrame "Hwire". }
    wp_apply (wp_Doc__ApplyEncodedUpdate decode _ s_loc γs γh c _ data_slice (DfracOwn 1) data
               with "[$Hdoc $Hishist $Hpin $Hcodec $Hdata $Hyprot]").
    iIntros (h inputs applied m') "(Hdata & %Hdecoded & #Hgrown & #Haccepts & #Happlied)".
    wp_auto.
    wp_apply (wp_Client__report with "[$Hclient $Hrcap]").
    iIntros "Hrcap".
    wp_auto.
    wp_for_post. iFrame.
Qed.

(** [Connect]: dial, then create the document as [client] and the root
    text. On a failed dial there is no client and the history element is
    handed back untouched. Otherwise the caller gets the client with its
    two sides, to hand to the goroutines that call [Insert] and run
    [Serve]. *)
Lemma wp_Connect (host : w64) (path : go_string) (client : w64) (decoder encoder : func.t)
    (name : go_string) (γh : history_names) :
  codec_roundtrip decode encode ->
  deployment_protocols decode γh ->
  {{{ is_pkg_init wsclient ∗ is_history (A := A) (P := P) γh ∗
      own_client_history γh (uint.nat client) ([] : list Ev) ∗
      codec_spec decode decoder ∗ encoder_spec encode encoder }}}
    @! wsclient.Connect #host #path #client #decoder #encoder #name
  {{{ (err : bool) (cl : loc), RET (#err, #cl);
      if err then own_client_history γh (uint.nat client) ([] : list Ev)
      else ∃ (γs : store_names) (sc rc : chan_id),
             is_Client cl γs γh (uint.nat client) sc rc name ∗
             own_Client_send_side γs sc ∗ own_Client_receive_side γs rc }}}.
Proof.
  intros Hroundtrip Hdeploy.
  wp_start as "(#Hishist & Hhistory & #Hcodec & #Hencoder)".
  wp_auto.
  wp_func_call.
  wp_apply (wp_Connect host path).
  iIntros (err conn sc rc) "Hconnected".
  wp_auto.
  destruct err.
  { wp_auto. iApply "HΦ". iFrame "Hhistory". }
  iDestruct "Hconnected" as "(#Hconn & Hsend_cursor & Hrecv_cursor)".
  wp_auto.
  iDestruct (own_client_history_lb with "Hhistory") as "[Hhistory #Hlb]".
  wp_apply (wp_NewDoc γh client with "[$Hhistory]").
  (* the read capabilities come back with the document: one for each side
     of the client, the rest are kept unused here *)
  iIntros (dv s_loc γs) "(#Hdoc & #Hpin & Hrcaps)".
  destruct (Z.to_nat rwmutex.actualMaxReaders) as [|[|readers]] eqn:Hreaders.
  { exfalso. rewrite rwmutex.actualMaxReaders_unseal in Hreaders. lia. }
  { exfalso. rewrite rwmutex.actualMaxReaders_unseal in Hreaders. lia. }
  iEval (simpl) in "Hrcaps". iDestruct "Hrcaps" as "(Hrcap_send & Hrcap_receive & _)".
  wp_auto.
  wp_apply (wp_Doc__GetOrCreateText with "[$Hdoc $Hishist]").
  iIntros (t) "#Htext".
  wp_auto.
  wp_alloc cl as "Hfields".
  iPersist "Hfields".
  wp_auto.
  iApply ("HΦ" $! false cl).
  iExists γs, sc, rc. iSplitR.
  { iExists _, s_loc. iFrame "Hfields Hconn Hdoc Htext Hishist Hpin Hlb Hcodec Hencoder". done. }
  iSplitL "Hsend_cursor Hrcap_send"; iExists 0%nat; iFrame.
Qed.

(** [Run]: the scripted client, the client's top-level composition:
    connect, serve on a goroutine with the receive side, and type the
    script with the send side, one byte of the script as one code unit. A
    byte is below the surrogate range, so every insert meets [Insert]'s
    hypothesis and the script needs none. The closed-system theorem
    (src/proof/demo/ws_system.v) boots exactly this function. *)
Lemma wp_Run (host : w64) (path : go_string) (client : w64) (decoder encoder : func.t)
    (name script : go_string) (γh : history_names) :
  codec_roundtrip decode encode ->
  deployment_protocols decode γh ->
  {{{ is_pkg_init wsclient ∗ is_history (A := A) (P := P) γh ∗
      own_client_history γh (uint.nat client) ([] : list Ev) ∗
      codec_spec decode decoder ∗ encoder_spec encode encoder ∗
      ws_env_preserves ⊤ }}}
    @! wsclient.Run #host #path #client #decoder #encoder #name #script
  {{{ RET #(); True }}}.
Proof.
  intros Hroundtrip Hdeploy.
  wp_start as "(#Hhistory_inv & Hhistory & #Hdecoder_spec & #Hencoder_spec & #Henv)".
  wp_auto.
  wp_apply (wp_Connect host path client decoder encoder name γh Hroundtrip Hdeploy
              with "[$Hhistory_inv $Hhistory $Hdecoder_spec $Hencoder_spec]").
  iIntros (err cl) "Hconnected".
  wp_auto.
  destruct err.
  { wp_auto. by iApply "HΦ". }
  iDestruct "Hconnected" as (γs sc rc) "(#Hclient & Hsend & Hreceive)".
  wp_auto.
  wp_apply (wp_fork with "[Hreceive]").
  { wp_apply (wp_Client__Serve with "[$Hclient $Hreceive $Henv]"). iIntros "_". done. }
  wp_apply wp_string_to_bytes. iIntros (units_slice) "[Hunits Hunits_cap]".
  wp_auto.
  iPoseProof "Hclient" as "Hopen". iNamed "Hopen".
  iAssert (∃ (i : w64),
    "c" ∷ c_ptr ↦ cl ∗ "units" ∷ units_ptr ↦ units_slice ∗ "i" ∷ i_ptr ↦ i ∗
    "%Hi" ∷ ⌜0 ≤ sint.Z i⌝ ∗
    "Hsend" ∷ own_Client_send_side γs sc ∗
    "Hunits" ∷ units_slice ↦* script)%I with "[c units i Hsend Hunits]" as "IH".
  { iExists (W64 0). iFrame "c units i Hsend Hunits". done. }
  wp_for "IH".
  iDestruct (own_slice_len with "Hunits") as %[Hunits_length Hunits_nonneg].
  destruct (decide (sint.Z i < sint.Z units_slice.(slice.len))) as [Hinside | Hpast]; last first.
  { rewrite bool_decide_eq_false_2 //. wp_auto. by iApply "HΦ". }
  rewrite bool_decide_eq_true_2 //.
  wp_auto.
  iDestruct "Hsend" as (sent) "[Hcursor Hrcap]".
  wp_apply (wp_Text__Len _ γs γh (uint.nat client) name [] ∅ [] with "[$Htext $Hpin $Hlb $Hrcap]").
  iIntros (length_value model) "(_ & Hrcap & _)".
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
  have Hbyte : units_surrogate_free [W16 (uint.Z unit)].
  { move=> typed /list_elem_of_singleton ->. word. }
  wp_apply (wp_Client__Insert cl γs γh (uint.nat client) sc rc name length_value _ (DfracOwn 1) _ Hbyte
              with "[$Hclient Hcursor Hrcap $Hliteral]").
  { iExists sent. iFrame "Hcursor Hrcap". }
  iIntros (err) "[Hsend Hliteral]".
  wp_auto.
  wp_for_post. iFrame. iPureIntro. clear -Hinside Hi. word.
Qed.

End proof.
