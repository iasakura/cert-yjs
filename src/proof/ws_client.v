(** The verified Yjs WebSocket client (issue #131): one connection to a
    y-websocket server, one document, one root text, over the ws FFI. A
    local edit is one transaction whose update is sent ([Transact], over
    [wp_Doc__TransactEncoded]); what the connection delivers is applied
    through the verified total apply path ([Serve], over
    [wp_Doc__ApplyEncodedUpdate]); after every local edit and every applied
    update the client writes the report of its root to the run's trace,
    under the trace protocol [is_report], as the server does (ws_relay.v).

    What the client proves about itself is the wire protocol: every message
    it sends satisfies [yjs_prot], with the certificates the history holds
    for what its transactions inserted ([yjs_prot_encode]). That is what makes it a peer
    the server's theorem needs no assumption about.

    API
    - [is_Client cl γs γh c sc rc name]: the client at [cl]: its connection
      (send channel [sc], receive channel [rc]), its document (store names
      [γs], client id [c]) in the deployment whose history is [γh], and the
      root text [name] it edits and reports on. Persistent: every field is
      written once, by [Connect].
    - [own_Client_send_side γs sc]: what the goroutine that calls
      [Transact] holds: the connection's send cursor, and a read capability of the
      store for the report.
    - [own_Client_receive_side γs rc]: the same for the goroutine that runs
      [Serve], with the receive cursor.
    - [closure_edits_text γs γh name f Q]: the contract of the closure
      [Client.Transact] runs: handed the root text and a fresh transaction,
      it returns the transaction, changed as it may be, with [Q] and with
      what it inserted free of surrogate code units
      ([inserted_surrogate_free]). That is all an application proves to
      have its edit sent: the certificates of what it inserted are the
      history's, not its own.
    - [client_app_spec app]: the contract of an application [Run] runs: with
      a client and its send side, it runs safely.
      [client_app_expr_spec make_app] is the same for an expression that
      evaluates to the application, which is what a node's boot expression
      holds.
    - [wp_Connect] / [wp_Client__Transact] /
      [wp_Client__Serve] / [wp_Run] (a whole client around an application,
      which the closed-system theorem in src/proof/demo/ws_system.v boots)
      / [wp_Typist] (an application: it types a script).

    The client has no lock of its own: its send side stays with the
    goroutine that calls [Transact], its receive side with [Serve], and the
    document's lock orders an apply against a local edit. *)
From New.proof Require Import proof_prelude.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import wsclient.
From New.proof Require Import prelude.
From New.proof.sync_proof Require Import base mutex rwmutex.
From New.goose_lang.ffi.ws_ffi Require Import ws_ffi.
From New.proof Require Import core.
From New.proof Require Import history.
From New.proof Require Import yjs_prot.
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

(** The abstract codec the deployment runs under (see yjs_prot.v). *)
Context (decode : list u8 -> option (list Input)).
Context (encode : list Input -> list u8).

(* ===== definitions ======================================================== *)

(** Client handle (persistent). The struct is written once, by [Connect];
    beside its fields the handle carries the global-history handle, the
    document's client pin with the empty history lower bound (what a read
    of the root for a report is certified against), the specification of
    the two codec values ([codec_pair_spec]), and the deployment's
    protocols. *)
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
    "#Hcodec_pair" ∷ codec_pair_spec decode encode client_value.(wsclient.Client.decode')
                       client_value.(wsclient.Client.encode') ∗
    "%Hdeploy"  ∷ ⌜deployment_protocols decode γh⌝.

(** The send side of the client: the send cursor of its connection, at
    however many messages it has sent, and one read capability of its
    store ([report] snapshots the root under the read lock). Held by the
    goroutine that calls [Transact]. *)
Definition own_Client_send_side (γs : store_names) (sc : chan_id) : iProp Σ :=
  ∃ n : nat, own_send_cursor sc n ∗ own_read_cap γs.

(** The receive side of the client: the receive cursor of its connection
    and one read capability of its store. Held by the goroutine that runs
    [Serve]. *)
Definition own_Client_receive_side (γs : store_names) (rc : chan_id) : iProp Σ :=
  ∃ n : nat, own_recv_cursor rc n ∗ own_read_cap γs.

(** [inserted_surrogate_free m inserted]: the items of the document [m]
    whose ids are in [inserted] hold no surrogate code unit. *)
Definition inserted_surrogate_free (m : DocModel) (inserted : gset YjsId) : Prop :=
  ∀ (root : go_string) (item : YjsItem A),
    item ∈ doc_model_get m (RootId root) -> item_id item ∈ inserted ->
    units_surrogate_free (content item).

(** [closure_edits_text γs γh name f Q]: the closure [f] edits the root
    text [name] of the store [γs] inside one transaction
    ([Client.Transact]'s argument): handed the text's handle and the fresh
    transaction, it returns the transaction, changed as it may be, with [Q],
    and what the transaction recorded as inserted holds no surrogate code
    unit. A one-shot wand, as [closure_runs_transaction]: the closure runs
    once and may carry the caller's resources into the transaction. *)
Definition closure_edits_text (γs : store_names) (γh : history_names) (name : go_string)
    (f : func.t) (Q : iProp Σ) : iProp Σ :=
  ∀ (tr s_loc t : loc) (c : ClientId) (h : list Ev) (m : DocModel)
    (pend : list Input) (deleted : gset YjsId) (Ψ : val -> iProp Σ),
    is_Text t γs γh name [] ∅ -∗
    own_transaction tr s_loc γs γh c h m pend deleted ∅ ∅ ∅ -∗
    (∀ (h' : list Ev) (m' : DocModel) (pend' : list Input)
       (deleted' inserted tombstoned : gset YjsId) (changed : gset P),
       own_transaction tr s_loc γs γh c h' m' pend' deleted' inserted tombstoned changed ∗
       ⌜inserted_surrogate_free m' inserted⌝ ∗ Q -∗ Ψ #()) -∗
    WP #f #tr #t {{ Ψ }}.

(** [client_app_spec app]: the application [app] runs safely with any
    client and its send side ([Run]'s argument). Persistent, as the codec
    specifications are: a property of the function value. *)
Definition client_app_spec (app : func.t) : iProp Σ :=
  □ (∀ (cl : loc) (γs : store_names) (γh : history_names) (c : ClientId)
       (sc rc : chan_id) (name : go_string),
      {{{ is_pkg_init wsclient ∗ is_Client cl γs γh c sc rc name ∗ own_Client_send_side γs sc }}}
        #app #cl
      {{{ RET #(); True }}}).

(** [client_app_expr_spec make_app]: the expression [make_app] evaluates to
    an application that meets [client_app_spec]. What a boot expression
    takes: an application is either a function value or, like [Typist], the
    result of a call. *)
Definition client_app_expr_spec (make_app : expr) : iProp Σ :=
  (is_pkg_init wsclient -∗
   WP make_app {{ v, ∃ app : func.t, ⌜v = #app⌝ ∗ client_app_spec app }})%I.

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

(** [Transact]: one local edit, of any shape, sent. The closure edits inside
    one transaction ([closure_edits_text]); what the transaction inserted
    goes on the wire. [wp_Doc__TransactEncoded] hands back the bytes of a
    batch that is exactly what was inserted, well formed and certified, and
    the closure's contract says the batch holds no surrogate code unit, so
    the bytes satisfy the wire protocol ([yjs_prot_encode]). *)
Lemma wp_Client__Transact (cl : loc) (γs : store_names) (γh : history_names)
    (c : ClientId) (sc rc : chan_id) (name : go_string) (f : func.t) (Q : iProp Σ) :
  {{{ is_pkg_init wsclient ∗ is_Client cl γs γh c sc rc name ∗
      own_Client_send_side γs sc ∗ closure_edits_text γs γh name f Q }}}
    cl @! (go.PointerType wsclient.Client) @! "Transact" #f
  {{{ (err : bool), RET #err; own_Client_send_side γs sc ∗ Q }}}.
Proof.
  wp_start as "(#Hclient & Hside & Hf)".
  iPoseProof "Hclient" as "Hopen". iNamed "Hopen". iNamed "Hcodec_pair".
  destruct Hdeploy as [Hprot Htrace].
  iDestruct "Hside" as (sent) "[Hcursor Hrcap]".
  wp_auto.
  wp_apply (wp_Doc__TransactEncoded _ s_loc γs γh _ encode _
              (λ _ _ m' _ _ inserted, ⌜inserted_surrogate_free m' inserted⌝ ∗ Q)%I
              with "[$Hdoc $Hishist $Hencoder Hf f text]").
  { rewrite /closure_runs_recorded_transaction.
    iIntros (tr store_loc c' h m pend deleted Ψ) "Htx HΨ".
    wp_auto.
    wp_apply ("Hf" with "Htext Htx").
    iIntros (h' m' pend' deleted' inserted tombstoned changed) "(Htx & %Hfree & HQ)".
    wp_auto.
    iApply ("HΨ" $! h' m' pend' deleted' inserted tombstoned changed).
    iFrame "Htx HQ". done. }
  iIntros (bytes_slice c' h' m' pend' deleted' inserted structs)
    "([%Hfree HQ] & Hbytes & Hbytes_cap & %Hstructs & #Hcertified)".
  (* the batch is what was inserted, so it holds no surrogate code unit *)
  have Hstructs_free : structs_surrogate_free structs.
  { move=> struct Hstruct unit Hunit.
    destruct (expand_inputs_content_unit structs struct unit Hstruct Hunit) as (op & Hop & Hcontent).
    destruct (proj1 (Hstructs op) Hop) as (root & item & [Hitem Hid] & ->).
    apply (Hfree root item Hitem Hid).
    move: Hcontent. rewrite /=. move=> ->. by apply list_elem_of_singleton. }
  iDestruct (yjs_prot_encode decode encode γh structs Hroundtrip Hstructs_free with "Hcertified")
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
  iApply "HΦ". iFrame "HQ".
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
  iPoseProof "Hclient" as "Hopen". iNamed "Hopen". iNamed "Hcodec_pair".
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
    two sides, to hand to the goroutines that call [Transact] and run
    [Serve]. *)
Lemma wp_Connect (host : w64) (path : go_string) (client : w64) (decoder encoder : func.t)
    (name : go_string) (γh : history_names) :
  deployment_protocols decode γh ->
  {{{ is_pkg_init wsclient ∗ is_history (A := A) (P := P) γh ∗
      own_client_history γh (uint.nat client) ([] : list Ev) ∗
      codec_pair_spec decode encode decoder encoder }}}
    @! wsclient.Connect #host #path #client #decoder #encoder #name
  {{{ (err : bool) (cl : loc), RET (#err, #cl);
      if err then own_client_history γh (uint.nat client) ([] : list Ev)
      else ∃ (γs : store_names) (sc rc : chan_id),
             is_Client cl γs γh (uint.nat client) sc rc name ∗
             own_Client_send_side γs sc ∗ own_Client_receive_side γs rc }}}.
Proof.
  intros Hdeploy.
  wp_start as "(#Hishist & Hhistory & #Hcodec_pair)".
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
  { iExists _, s_loc. iFrame "Hfields Hconn Hdoc Htext Hishist Hpin Hlb Hcodec_pair". done. }
  iSplitL "Hsend_cursor Hrcap_send"; iExists 0%nat; iFrame.
Qed.

(** [Run]: a whole client around an application: connect, serve on a
    goroutine with the receive side, and run the application with the send
    side. The closed-system theorem (src/proof/demo/ws_system.v) boots
    exactly this function, for any application that meets
    [client_app_spec]. *)
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
  iIntros (err cl) "Hconnected".
  wp_auto.
  destruct err.
  { wp_auto. by iApply "HΦ". }
  iDestruct "Hconnected" as (γs sc rc) "(#Hclient & Hsend & Hreceive)".
  wp_auto.
  wp_apply (wp_fork with "[Hreceive]").
  { wp_apply (wp_Client__Serve with "[$Hclient $Hreceive $Henv]"). iIntros "_". done. }
  wp_apply ("Happ" with "[$Hclient $Hsend]").
  by iApply "HΦ".
Qed.

(** [Typist]: an application for [Run]. It types its script one byte at a
    time at the end of the text, each byte as one code unit in its own
    transaction. A byte is below the surrogate range, so each transaction
    meets [closure_edits_text], and the script needs no condition. *)
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
  iIntros "!>" (cl γs γh c sc rc name) "!>". iIntros (Ψ) "(#Hpkg' & #Hclient & Hsend) HΨ".
  wp_auto.
  wp_apply wp_string_to_bytes. iIntros (units_slice) "[Hunits Hunits_cap]".
  wp_auto.
  iAssert (∃ (i : w64),
    "c" ∷ c_ptr ↦ cl ∗ "units" ∷ units_ptr ↦ units_slice ∗ "i" ∷ i_ptr ↦ i ∗
    "%Hi" ∷ ⌜0 ≤ sint.Z i⌝ ∗
    "Hsend" ∷ own_Client_send_side γs sc ∗
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
  have Hbyte : units_surrogate_free [W16 (uint.Z unit)].
  { move=> typed /list_elem_of_singleton ->. word. }
  wp_apply (wp_Client__Transact cl γs γh c sc rc name _ True%I
              with "[$Hclient $Hsend unit Hliteral]").
  { rewrite /closure_edits_text.
    iIntros (tr s_loc t c' h m pend deleted Ψ') "#Htext Htx HΨ'".
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
    (* an inserted item is the one item of this insert, whose unit is the byte *)
    move=> root item Hitem Hid.
    rewrite left_id_L in Hid. apply elem_of_char_ids in Hid as (it & Hit & Hit_id).
    destruct Hrun as (_ & Hlength & Hitems & _).
    apply list_elem_of_lookup in Hit as [position Hposition].
    destruct Hlength as [-> | Hlength]; first by rewrite lookup_nil in Hposition.
    have [typed Htyped] : is_Some ([W16 (uint.Z unit)] !! position).
    { apply lookup_lt_is_Some. rewrite -Hlength. exact (lookup_lt_Some _ _ _ Hposition). }
    destruct (Hitems position it typed Hposition Htyped) as (Hit_model & _ & Hcontent & _).
    have Hit_root : it ∈ doc_model_get m' (RootId name).
    { rewrite (proj1 Hreplaced). exact Hit_model. }
    destruct (Hunique name root it item Hit_root Hitem Hit_id) as [_ <-].
    rewrite Hcontent. move=> x /list_elem_of_singleton ->.
    exact (Hbyte typed (list_elem_of_lookup_2 _ _ _ Htyped)). }
  iIntros (err) "[Hsend _]".
  wp_auto.
  wp_for_post. iFrame. iPureIntro. clear -Hinside Hi. word.
Qed.

(** The typist as a boot expression's application. *)
Lemma typist_app_expr_spec (script : go_string) :
  ⊢ client_app_expr_spec ((@! wsclient.Typist) #script).
Proof.
  iIntros "#Hpkg".
  wp_apply (wp_Typist script).
  iIntros (app) "#Happ". iExists app. by iFrame "Happ".
Qed.

End proof.
