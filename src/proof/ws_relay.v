(** The verified Yjs WebSocket server (issue #107, W3b): rooms, the per-room
    connection table, and the y-websocket message loop for the update case,
    over the ws FFI. [process] decodes one received message, applies it to the
    room's document through the verified total apply path
    ([wp_Doc__ApplyEncodedUpdate]), and relays the applied bytes to the room's
    other connections.

    API
    - [relay_entry] / [member]: one processed packet (who sent it, its stream
      index, its bytes) and one joined connection (its channels, its join
      point in the log, its processed cursor).
    - [is_room_member γ j mb]: persistent, member [j] of the room is [mb].
    - [room_inv] ties the ghost log to the wire: per entry the S1 receipts
      ([entry_receipts], internal: the packet decodes, every input is
      [is_accepted] by the server's store, and the server's history visibly
      grew by the applied portion); per member the log's entries are exactly
      the received prefix of that member's channel (S2, via [log_coh] + the
      per-entry [is_chan_msg] facts + the member's processed cursor), and
      everything the room has sent to a member embeds, in order, into the
      relay view of the log after its join point (S3, [own_member_send]).
    - [wp_NewRoom] / [wp_Room__Join] / [wp_Room__process] / [wp_Room__Serve] /
      [wp_Run] / [wp_ListenAndServe] (the whole server, which the
      closed-system theorem in src/proof/demo/ws_server.v boots).

    Concurrent reads (issue #125) need no lemma of this file: the [text]
    layer's [wp_Text__String] / [wp_Text__Len] guarantee that a
    read's snapshot contains every insert delivered by whatever
    [is_history_lb] certificate the reader holds, and code co-verified with
    the room (holding its [room_inv]) can extract exactly such certificates
    from the internal receipts.

    One [room.mu] critical section spans the apply and the fan-out
    ([process]), matching y-websocket's serialized handler; the store's write
    lock nests inside. That is what makes the log simultaneously the apply
    order and the relay order. Send errors lose that one relay for that one
    connection, as in y-websocket, which is why S3 is a sublist and not an
    equality. *)
From New.proof Require Import proof_prelude.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import wsrelay.
From New.proof Require Import prelude.
From New.proof.sync_proof Require Import base mutex.
From New.goose_lang.ffi.ws_ffi Require Import ws_ffi.
From New.proof Require Import core.
From New.proof Require Import history.
From New.proof Require Import yjs_prot.
From New.proof.store Require Import store.
From New.proof.doc Require Import doc.
From New.ghost Require Import mono_list ghost_var.
From iris.algebra Require Import auth gmap gset.
From iris.algebra.lib Require Import dfrac_agree.

(* iris.algebra pushes [nat_scope], retuning the default [<] / [≤]; the word
   arithmetic below writes [Z] comparisons unannotated, so restore [Z_scope]. *)
Local Open Scope Z_scope.

Section proof.
Context {Σ : gFunctors} {hG : heapGS Σ}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.
Context {sync_pkg : sync.Assumptions}.
Context {wsnet_pkg : wsnet.Assumptions} {wsrelay_pkg : wsrelay.Assumptions}.

#[global] Instance : IsPkgInit (iProp Σ) wsnet := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) wsnet := build_get_is_pkg_init_wf.
#[global] Instance : IsPkgInit (iProp Σ) wsrelay := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) wsrelay := build_get_is_pkg_init_wf.

Set Default Proof Using "Type*".

Notation A := go_string.
Notation P := go_string.
Local Notation TId := (TypeId P).
Local Notation Input := (TId * IntegrateInput (A := A))%type.
Local Notation Ev := (@Event (TId * @YjsOperation A)).
Local Notation DocModel := (gmap TId (list (YjsItem A))).

(* [is_Doc] / [wp_Doc__ApplyEncodedUpdate] are generalized over the store
   lock + item-set RAs; mirror their Context here to apply them. *)
Context {seq_inG : inG Σ (authR (gmapUR loc (gsetUR (YjsItem A))))}.
Context {acc_inG : inG Σ (authR (gsetUR YjsId))}.
Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO (gmap loc (list loc) * pool)))}.

(** The abstract codec the deployment runs under (see yjs_prot.v). *)
Context (decode : list u8 -> option (list Input)).

(* ===== definitions ======================================================== *)

(** One processed packet: member [re_mem] sent it as message [re_idx] of its
    receive channel [re_src], carrying [re_data]. *)
Record relay_entry := RelayEntry {
  re_mem  : nat;
  re_src  : chan_id;
  re_idx  : nat;
  re_data : list u8;
}.

(** One joined connection: its handle and channels, the log length at its
    join (relays reach it from there on; no backfill until the W3c
    handshake), and the name of its processed cursor. *)
Record member := Member {
  mb_conn : loc;
  mb_send : chan_id;
  mb_recv : chan_id;
  mb_join : nat;
  mb_processed : gname;
}.

(** The member's processed cursor: [n] of its messages have been processed
    into the room's log. Two halves of a [ghost_var]: one rides in
    [room_inv], pinned to the member's entry count in the log; the other is
    its [Serve] loop's, kept equal to the FFI receive cursor (received =
    processed). Their agreement at the log-append step is what makes the
    per-member entry indices dense (S2). *)
Definition own_processed (mb : member) (n : nat) : iProp Σ :=
  ghost_var mb.(mb_processed) (1/2) n.

#[global] Instance own_processed_timeless mb n : Timeless (own_processed mb n).
Proof. rewrite /own_processed. apply _. Qed.

Lemma own_processed_agree mb n m :
  own_processed mb n -∗ own_processed mb m -∗ ⌜n = m⌝.
Proof. iApply ghost_var_agree. Qed.

Lemma own_processed_update (k : nat) mb n m :
  own_processed mb n -∗ own_processed mb m ==∗
  own_processed mb k ∗ own_processed mb k.
Proof.
  iIntros "H1 H2". iMod (ghost_var_update_halves k with "H1 H2") as "[$ $]". done.
Qed.

(** The log entries member [j] contributed, in order. *)
Definition entries_of (j : nat) (L : list relay_entry) : list relay_entry :=
  filter (λ e, e.(re_mem) = j) L.

(** What the room may relay to member [j] out of log [L]: the payloads of the
    other members' entries. *)
Definition relay_view (j : nat) (L : list relay_entry) : list (list u8) :=
  re_data <$> filter (λ e, e.(re_mem) ≠ j) L.

(** The pure log/table coherence:
    - every entry is attributed to a real member, on that member's receive
      channel;
    - per member, the entry indices are exactly 0,1,2,... in order (with the
      per-entry [is_chan_msg] facts this makes the member's log entries THE
      received prefix of its channel: S2);
    - join points lie inside the log. *)
Definition log_coh (MS : list member) (L : list relay_entry) : Prop :=
  (∀ e, e ∈ L -> ∃ mb, MS !! e.(re_mem) = Some mb ∧ e.(re_src) = mb.(mb_recv)) ∧
  (∀ j, re_idx <$> entries_of j L = seq 0 (length (entries_of j L))) ∧
  (∀ mb, mb ∈ MS -> (mb.(mb_join) <= length L)%nat).

Record room_names := RoomNames {
  rn_log : gname;  (* mono_list of relay_entry: the processed-packet log *)
  rn_mem : gname;  (* mono_list of member: the join order *)
}.

(** Persistent: member [j] of the room is [mb], with its connection handle
    (so a member's [Serve] goroutine can receive without the room lock). *)
Definition is_room_member (γ : room_names) (j : nat) (mb : member) : iProp Σ :=
  mono_list_idx_own γ.(rn_mem) j mb ∗
  is_Connection mb.(mb_conn) mb.(mb_send) mb.(mb_recv).

(** Persistent: entry [i] of the room's log is [e]. *)
Definition is_room_log_entry (γ : room_names) (i : nat) (e : relay_entry) : iProp Σ :=
  mono_list_idx_own γ.(rn_log) i e.

(** The S1 safety receipts of one processed packet: it decodes, the server's
    store accepted every input (forever delivered-or-buffered,
    [own_store_accepted_sound]), and the server's history visibly grew by the
    applied portion, in processing order. The history certificate [Herlb] is
    also the CONTENT route (issue #125): fed to [wp_Text__Len] /
    [wp_Text__String] it guarantees a concurrent read's snapshot
    contains the applied portion's items, so no separate content certificate
    is carried here. Buffered inputs (dependencies not yet arrived) appear
    in no root's content until drained; [is_accepted] is their exact
    bound. *)
Definition entry_receipts (γs : store_names) (γh : history_names)
    (c : ClientId) (e : relay_entry) : iProp Σ :=
  ∃ (inputs : list Input) (h : list Ev) (applied : list Input),
    "%Herdec" ∷ ⌜decode e.(re_data) = Some inputs⌝ ∗
    "#Heracc" ∷ ([∗ list] x ∈ inputs, is_accepted γs (in_id x.2)) ∗
    "#Herlb"  ∷ is_history_lb γh c (h ++ (deliver_ev <$> expand_inputs applied)).

#[global] Instance entry_receipts_persistent γs γh c e :
  Persistent (entry_receipts γs γh c e).
Proof. apply _. Qed.

(* [room_inv] carries one [entry_receipts] per log entry, and every lock
   acquisition ([iNamed] on the invariant) moves that big-op into the
   persistent context; with the predicate transparent that Persistent /
   IntoPersistent search unfolds each element's body. Sealed for typeclass
   resolution so the move is a single [entry_receipts_persistent] lookup
   (the [tie_body] trick, store/heap.v): a development version carrying a
   [gmap]-typed existential here made the one [iNamed "Hinv"] in
   [wp_Room__Join] cost ~2 minutes (measured), and the seal is what keeps
   any future binder from reintroducing that. Nothing [iNamed]s into the
   predicate through the invariant; the producer ([wp_Room__process])
   builds it under [iAssert] where the unfolding is local. *)
#[global] Typeclasses Opaque entry_receipts.

(** The send side of one member (S3): the room has sent [sent] to it, that IS
    the wire content of its send channel (cursor + per-index message facts),
    and [sent] embeds, in order, into the relay view of the log after the
    member's join point. Sending extends [sent] by the entry just logged;
    everything else leaves it alone, so the shape is a loop invariant. *)
Definition own_member_send (L : list relay_entry) (j : nat) (mb : member) : iProp Σ :=
  ∃ sent : list (list u8),
    "Hsc"    ∷ own_send_cursor mb.(mb_send) (length sent) ∗
    "#Hsent" ∷ ([∗ list] i ↦ d ∈ sent, is_chan_msg mb.(mb_send) i d) ∗
    "%Hsub"  ∷ ⌜sent `sublist_of` relay_view j (drop mb.(mb_join) L)⌝.

(** The room's lock body. *)
Definition room_inv (r : loc) (γ : room_names) (γs : store_names)
    (γh : history_names) (c : ClientId) : iProp Σ :=
  ∃ (sl : slice.t) (dv s_loc : loc) (f : func.t)
    (MS : list member) (L : list relay_entry),
    "Hconnsf"   ∷ (r .[(wsrelay.Room.t), "conns"]) ↦ sl ∗
    "Hconns"    ∷ sl ↦* (mb_conn <$> MS) ∗
    "Hcap"      ∷ own_slice_cap wsnet.Connection.t sl (DfracOwn 1) ∗
    "Hdocf"     ∷ (r .[(wsrelay.Room.t), "doc"]) ↦ dv ∗
    "Hdecodef"  ∷ (r .[(wsrelay.Room.t), "decode"]) ↦ f ∗
    "#Hdoc"     ∷ is_Doc dv s_loc γs γh ∗
    "#Hcodec"   ∷ codec_spec decode f ∗
    "Hmem"      ∷ mono_list_auth_own γ.(rn_mem) 1 MS ∗
    "Hlog"      ∷ mono_list_auth_own γ.(rn_log) 1 L ∗
    "#Hconninfo" ∷ ([∗ list] mb ∈ MS,
                      is_Connection mb.(mb_conn) mb.(mb_send) mb.(mb_recv)) ∗
    "#Hlogmsgs" ∷ ([∗ list] e ∈ L, is_chan_msg e.(re_src) e.(re_idx) e.(re_data)) ∗
    "#Hrcpts"   ∷ ([∗ list] e ∈ L, entry_receipts γs γh c e) ∗
    "Hposvs"    ∷ ([∗ list] j ↦ mb ∈ MS,
                     own_processed mb (length (entries_of j L))) ∗
    "Hsends"    ∷ ([∗ list] j ↦ mb ∈ MS, own_member_send L j mb) ∗
    "%Hcoh"     ∷ ⌜log_coh MS L⌝.

(** Room handle (persistent). Carries the global-history handle, the server
    store's client pin, and the deployment equation identifying the ambient
    wire protocol with [yjs_prot]: receives convert their [ws_prot] payload
    into certificates, sends convert them back. *)
Definition is_Room (r : loc) (γ : room_names) (γs : store_names)
    (γh : history_names) (c : ClientId) : iProp Σ :=
  "#Hmu"     ∷ is_Mutex (r .[(wsrelay.Room.t), "mu"]) (room_inv r γ γs γh c) ∗
  "#Hishist" ∷ is_history (A := A) (P := P) γh ∗
  "#Hpin"    ∷ is_store_client γs c ∗
  "%Hprot"   ∷ ⌜∀ d, ws_prot d = yjs_prot decode γh d⌝.

#[global] Instance is_room_member_persistent γ j mb : Persistent (is_room_member γ j mb).
Proof. apply _. Qed.
#[global] Instance is_Room_persistent r γ γs γh c : Persistent (is_Room r γ γs γh c).
Proof. apply _. Qed.

(* ===== lemmas ============================================================= *)

(* ----- pure theory of the log ----- *)

Lemma entries_of_app j L1 L2 :
  entries_of j (L1 ++ L2) = entries_of j L1 ++ entries_of j L2.
Proof. rewrite /entries_of list.filter_app //. Qed.

Lemma entries_of_snoc_self j L e :
  e.(re_mem) = j ->
  entries_of j (L ++ [e]) = entries_of j L ++ [e].
Proof.
  move=> Hj. rewrite entries_of_app /entries_of filter_cons_True // filter_nil //.
Qed.

Lemma entries_of_snoc_other j L e :
  e.(re_mem) ≠ j ->
  entries_of j (L ++ [e]) = entries_of j L.
Proof.
  move=> Hj.
  rewrite entries_of_app /entries_of filter_cons_False // filter_nil app_nil_r //.
Qed.

Lemma relay_view_app j L1 L2 :
  relay_view j (L1 ++ L2) = relay_view j L1 ++ relay_view j L2.
Proof. rewrite /relay_view list.filter_app fmap_app //. Qed.

Lemma relay_view_snoc_other j L e :
  e.(re_mem) ≠ j ->
  relay_view j (L ++ [e]) = relay_view j L ++ [e.(re_data)].
Proof.
  move=> Hj.
  rewrite relay_view_app /relay_view filter_cons_True // filter_nil //.
Qed.

Lemma relay_view_snoc_self j L e :
  e.(re_mem) = j ->
  relay_view j (L ++ [e]) = relay_view j L.
Proof.
  move=> Hj.
  have Hne : ¬ (e.(re_mem) ≠ j) by move=> Hne; exact (Hne Hj).
  rewrite relay_view_app /relay_view filter_cons_False // filter_nil /= app_nil_r //.
Qed.

(** A member with no entries yet: anything at or beyond the table's length. *)
Lemma entries_of_oob MS L j :
  log_coh MS L -> (length MS <= j)%nat -> entries_of j L = [].
Proof.
  move=> [Hattr _] Hlen.
  apply length_zero_iff_nil, Nat.le_0_r, Nat.le_ngt => Hpos.
  have Hne : entries_of j L ≠ [] by move=> Heq; rewrite Heq /= in Hpos; lia.
  destruct (entries_of j L) as [|e es] eqn:Hes; first done.
  have He : e ∈ entries_of j L by rewrite Hes; left.
  move: He. rewrite /entries_of list_elem_of_filter. move=> [Hj He].
  destruct (Hattr e He) as (mb & Hmb & _).
  apply lookup_lt_Some in Hmb. lia.
Qed.

Lemma log_coh_nil : log_coh [] [].
Proof.
  split_and!.
  - move=> e /elem_of_nil [].
  - move=> j. rewrite /entries_of filter_nil //.
  - move=> mb /elem_of_nil [].
Qed.

(** Joining: a fresh member at the end of the table, join point = the current
    log length. *)
Lemma log_coh_member MS L mb :
  mb.(mb_join) = length L ->
  log_coh MS L -> log_coh (MS ++ [mb]) L.
Proof.
  move=> Hjoin [Hattr [Hidx Hjoins]]. split_and!.
  - move=> e He. destruct (Hattr e He) as (mb' & Hmb' & Hsrc).
    exists mb'. split; last exact Hsrc.
    apply lookup_app_l_Some. exact Hmb'.
  - exact Hidx.
  - move=> mb' /elem_of_app [Hin | Hin1].
    + exact (Hjoins mb' Hin).
    + apply list_elem_of_singleton in Hin1. subst mb'. lia.
Qed.

(** Processing: appending member [j]'s next message, at its dense index. *)
Lemma log_coh_snoc MS L j mb n data :
  log_coh MS L ->
  MS !! j = Some mb ->
  n = length (entries_of j L) ->
  log_coh MS (L ++ [RelayEntry j mb.(mb_recv) n data]).
Proof.
  move=> [Hattr [Hidx Hjoins]] Hj Hn.
  set (e := RelayEntry j mb.(mb_recv) n data).
  split_and!.
  - move=> e' /elem_of_app [He' | He'].
    + exact (Hattr e' He').
    + apply list_elem_of_singleton in He'. subst e'.
      exists mb. done.
  - move=> j'. destruct (decide (j' = j)) as [-> | Hne].
    + rewrite (entries_of_snoc_self j L e) //.
      rewrite fmap_app Hidx length_app /= -Hn Nat.add_1_r seq_S //.
    + rewrite (entries_of_snoc_other j' L e) //.
  - move=> mb' Hmb'. rewrite length_app /=.
    have := Hjoins mb' Hmb'. lia.
Qed.

(** The send bundle survives a log append: the view only grows at the end
    (or, for the sender itself, does not change), and a sublist of a prefix
    is a sublist of the whole. *)
Lemma own_member_send_snoc L j mb e :
  (mb.(mb_join) <= length L)%nat ->
  own_member_send L j mb -∗ own_member_send (L ++ [e]) j mb.
Proof.
  iIntros (Hjoin) "H". iNamed "H".
  iExists sent. iFrame "Hsc Hsent". iPureIntro.
  rewrite drop_app_le //.
  destruct (decide (e.(re_mem) = j)) as [Heq | Hne].
  - rewrite relay_view_snoc_self //.
  - rewrite relay_view_snoc_other //.
    apply sublist_inserts_r. exact Hsub.
Qed.

(* ----- the WP specs ----- *)

Lemma wp_NewRoom (dv s_loc : loc) (γs : store_names) (γh : history_names)
    (c : ClientId) (f : func.t) :
  (∀ d, ws_prot d = yjs_prot decode γh d) ->
  {{{ is_pkg_init wsrelay ∗ is_Doc dv s_loc γs γh ∗
      is_history (A := A) (P := P) γh ∗ is_store_client γs c ∗
      codec_spec decode f }}}
    @! wsrelay.NewRoom #dv #f
  {{{ (r : loc) (γ : room_names), RET #r; is_Room r γ γs γh c }}}.
Proof.
  intros Hprot.
  wp_start as "(#Hdoc & #Hishist & #Hpin & #Hcodec)".
  wp_auto.
  wp_alloc r as "Hr".
  iMod (mono_list_own_alloc ([] : list relay_entry)) as (γlog) "[Hlog _]".
  iMod (mono_list_own_alloc ([] : list member)) as (γmem) "[Hmem _]".
  set (γ := RoomNames γlog γmem).
  iApply wp_fupd. wp_auto.
  iApply ("HΦ" $! r γ). iStructNamed "Hr".
  simpl. rewrite /is_Room.
  iMod (init_Mutex (room_inv r γ γs γh c) with "[$] [-]") as "$"; last by iFrame "#%".
  iExists slice.nil, dv, s_loc, f, [], [].
  iNext. iFrame "conns doc decode Hmem Hlog Hdoc Hcodec".
  iSplitR; [by iApply own_slice_nil|].
  iSplitR; [by iApply own_slice_cap_nil|].
  iSplitR; [by iApply big_sepL_nil|].
  iSplitR; [by iApply big_sepL_nil|].
  iSplitR; [by iApply big_sepL_nil|].
  iSplitR; [by iApply big_sepL_nil|].
  iSplitR; [by iApply big_sepL_nil|].
  iPureIntro. exact log_coh_nil.
Qed.

(** [Join] hands over the connection's send side and mints the membership:
    the caller gets back the persistent member witness and its half of the
    processed cursor, at 0 (a fresh member has contributed nothing). The send
    cursor must be fresh: the room's S3 bookkeeping says everything on the
    send channel was relayed by the room. *)
Lemma wp_Room__Join (r cn : loc) (γ : room_names) (γs : store_names)
    (γh : history_names) (c : ClientId) (sc rc : chan_id) :
  {{{ is_pkg_init wsrelay ∗ is_Room r γ γs γh c ∗
      is_Connection cn sc rc ∗ own_send_cursor sc 0 }}}
    r @! (go.PointerType wsrelay.Room) @! "Join" #cn
  {{{ (j : nat) (mb : member), RET #();
      ⌜mb.(mb_conn) = cn ∧ mb.(mb_send) = sc ∧ mb.(mb_recv) = rc⌝ ∗
      is_room_member γ j mb ∗ own_processed mb 0%nat }}}.
Proof.
  wp_start as "(#Hroom & #Hconn & Hsend)".
  iNamed "Hroom".
  wp_auto.
  wp_apply (wp_Mutex__Lock with "[$Hmu]").
  iIntros "[Hlocked Hinv]". iNamed "Hinv".
  wp_auto.
  wp_apply wp_slice_literal. iSplitR; first done. iIntros "%sl0 [Hsl0 _]".
  wp_auto.
  wp_apply (wp_slice_append with "[$Hconns $Hcap $Hsl0]").
  iIntros (sl') "(Hconns & Hcap & _)".
  wp_auto.
  (* mint the member: fresh processed cursor, join point = current log length *)
  iMod (ghost_var_alloc 0%nat) as (γp) "[Hpos1 Hpos2]".
  set (mb := Member cn sc rc (length L) γp).
  iAssert (own_processed mb 0 ∗ own_processed mb 0)%I
    with "[Hpos1 Hpos2]" as "[Hpos1 Hpos2]".
  { rewrite /own_processed /mb /=. iFrame. }
  iMod (mono_list_auth_own_update_app [mb] with "Hmem") as "[Hmem #Hmemlb]".
  iDestruct (mono_list_idx_own_get (length MS) with "Hmemlb") as "#Hmidx".
  { rewrite lookup_app_r; last lia. rewrite Nat.sub_diag //. }
  iAssert (is_room_member γ (length MS) mb) as "#Hmember".
  { iFrame "Hmidx". iFrame "Hconn". }
  iAssert (▷ room_inv r γ γs γh c)%I
    with "[Hconnsf Hconns Hcap Hdocf Hdecodef Hmem Hlog Hposvs Hsends Hsend Hpos1]"
    as "Hinv2".
  { iNext. iExists sl', dv, s_loc, f, (MS ++ [mb]), L.
    iFrame "Hconnsf Hdocf Hdecodef Hmem Hlog Hdoc Hcodec".
    rewrite fmap_app /=. iFrame "Hconns Hcap".
    iSplitR.
    { rewrite big_sepL_snoc. iFrame "Hconninfo". iFrame "Hconn". }
    iFrame "Hlogmsgs Hrcpts".
    iSplitL "Hposvs Hpos1".
    { rewrite big_sepL_snoc. iFrame "Hposvs".
      rewrite (entries_of_oob MS L (length MS) Hcoh) //=. }
    iSplitL.
    { rewrite big_sepL_snoc. iFrame "Hsends".
      iExists [].
      iSplitL "Hsend"; first (simpl; by iFrame "Hsend").
      iSplitR; [by iApply big_sepL_nil|].
      iPureIntro. apply sublist_nil_l. }
    iPureIntro. apply log_coh_member; [done | exact Hcoh]. }

  wp_apply (wp_Mutex__Unlock with "[$Hmu $Hlocked $Hinv2]").
  iApply ("HΦ" $! (length MS) mb).
  iSplitR; first by iPureIntro.
  iFrame "Hmember".
  iExact "Hpos2".
Qed.

(** [process] handles ONE received message end to end: apply to the room's
    document, log it, fan out. The caller (the member's [Serve] goroutine)
    presents the wire fact for message [n] of its channel, the protocol that
    came with it, and its processed cursor at [n]; it gets the cursor back
    at [S n] and the log witness that THIS message is now entry-processed.
    The S1 receipts stay internal: they are minted here and recorded in
    [room_inv]'s per-entry [Hrcpts], not returned. *)
Lemma wp_Room__process (r : loc) (γ : room_names) (γs : store_names)
    (γh : history_names) (c : ClientId) (j : nat) (mb : member) (n : nat)
    (s : slice.t) (dq : dfrac) (data : list u8) :
  {{{ is_pkg_init wsrelay ∗ is_Room r γ γs γh c ∗
      is_room_member γ j mb ∗ own_processed mb n ∗
      is_chan_msg mb.(mb_recv) n data ∗ ws_prot data ∗ s ↦*{dq} data }}}
    r @! (go.PointerType wsrelay.Room) @! "process" #(mb.(mb_conn)) #s
  {{{ RET #(); s ↦*{dq} data ∗ own_processed mb (S n) ∗
      (∃ i : nat, is_room_log_entry γ i (RelayEntry j mb.(mb_recv) n data)) }}}.
Proof.
  wp_start as "(#Hroom & #Hmember & Hpos & #Hmsg & #Hprotd & Hs)".
  iNamed "Hroom".
  iDestruct "Hmember" as "[Hmidx Hmconn]".
  wp_auto.
  wp_apply (wp_Mutex__Lock with "[$Hmu]").
  iIntros "[Hlocked Hinv]". iNamed "Hinv".
  wp_auto.
  (* the member is in the table *)
  iDestruct (mono_list_auth_idx_lookup with "Hmem Hmidx") as %HMSj.
  (* the message's protocol, as certificates *)
  iAssert (yjs_prot decode γh data) as "#Hyprot".
  { rewrite -Hprot. iFrame "Hprotd". }
  (* apply the batch to the room's document (store lock nested inside) *)
  wp_apply (wp_Doc__ApplyEncodedUpdate _ dv s_loc γs γh c f s dq data
             with "[$Hdoc $Hishist $Hpin $Hcodec $Hs $Hyprot]").
  iIntros (h inputs applied m') "(Hs & %Hdec & #Hlb & #Haccepts & #Happlied)".
  wp_auto.
  (* the position halves agree: n is exactly member j's entry count *)
  iDestruct (big_sepL_delete _ _ j mb with "Hposvs") as "[Hposj Hposvs]";
    first exact HMSj.
  iDestruct (own_processed_agree with "Hposj Hpos") as %Hn.
  (* log the packet *)
  set (e := RelayEntry j mb.(mb_recv) n data).
  iMod (mono_list_auth_own_update_app [e] with "Hlog") as "[Hlog #Hloglb]".
  iDestruct (mono_list_idx_own_get (length L) with "Hloglb") as "#Hlogentry".
  { rewrite lookup_app_r; last lia. rewrite Nat.sub_diag //. }
  (* advance the position: both halves move to S n together *)
  iMod (own_processed_update (S n) with "Hposj Hpos") as "[Hposj Hpos]".
  iAssert ([∗ list] j' ↦ mb' ∈ MS,
             own_processed mb' (length (entries_of j' (L ++ [e]))))%I
    with "[Hposvs Hposj]" as "Hposvs".
  { iEval (rewrite (big_sepL_delete _ MS j mb HMSj)).
    iSplitL "Hposj".
    { rewrite (entries_of_snoc_self j L e) // length_app /= Hn Nat.add_1_r.
      iFrame. }
    iApply (big_sepL_impl with "Hposvs").
    iIntros "!>" (j' mb' Hj') "H".
    case_decide as Hjj; first by iExact "H".
    have Hne' : e.(re_mem) ≠ j' by simpl; congruence.
    rewrite (entries_of_snoc_other j' L e Hne'). iExact "H". }
  (* the receipts of the new entry *)
  iAssert (entry_receipts γs γh c e) as "#Hrcpt".
  { iExists inputs, h, applied. iFrame "Haccepts Hlb". done. }
  (* fan out under the same critical section, iterating the table. Members
     below the loop cursor have been offered the new entry (their bundle is
     at L ++ [e]); the rest are still at L, which is what lets a successful
     send extend their [sent] by exactly the new entry's payload. *)
  iDestruct (own_slice_len with "Hconns") as %[Hlen Hlen0].
  rewrite length_fmap in Hlen.
  iAssert (∃ (i : w64) (cv : loc),
    "%Hi0" ∷ ⌜0 ≤ sint.Z i⌝ ∗
    "Hi" ∷ i_ptr ↦ i ∗
    "Hcv" ∷ c_ptr ↦ cv ∗
    "Hself" ∷ self_ptr ↦ mb.(mb_conn) ∗
    "Hdata" ∷ data_ptr ↦ s ∗
    "Hconns" ∷ sl ↦* (mb_conn <$> MS) ∗
    "Hsends" ∷ ([∗ list] j' ↦ mb' ∈ MS,
                  own_member_send
                    (if decide (j' < uint.nat i)%nat then L ++ [e] else L) j' mb') ∗
    "Hs" ∷ s ↦*{dq} data)%I
    with "[$i $c $self $data $Hconns $Hs Hsends]" as "IH".
  { iSplitR; first (iPureIntro; word).
    iApply (big_sepL_impl with "Hsends").
    iIntros "!>" (j' mb' Hj') "H".
    case_decide as Hlt; [exfalso; word | by iExact "H"]. }
  wp_for "IH".
  wp_if_destruct.
  - (* offer the entry to connection number [i] *)
    destruct ((mb_conn <$> MS) !! uint.nat i) as [cv'|] eqn:Hcv'; last first.
    { exfalso. apply lookup_ge_None in Hcv'. rewrite length_fmap in Hcv'. word. }
    rewrite list_lookup_fmap in Hcv'.
    destruct (MS !! uint.nat i) as [mbi|] eqn:Hmbi; last discriminate.
    simpl in Hcv'. injection Hcv' as <-.
    iDestruct (own_slice_elem_acc (sint.Z i) mbi.(mb_conn) sl (DfracOwn 1) _
                with "Hconns") as "[Hel Hgive]".
    { word. }
    { replace (Z.to_nat (sint.Z i)) with (uint.nat i) by word.
      rewrite list_lookup_fmap Hmbi //. }
    rewrite decide_True; last word.
    wp_auto.
    iDestruct ("Hgive" with "Hel") as "Hconns".
    rewrite list_insert_id; last first.
    { replace (Z.to_nat (sint.Z i)) with (uint.nat i) by word.
      rewrite list_lookup_fmap Hmbi //. }
    (* borrow member [i]'s send bundle, still at [L] *)
    iDestruct (big_sepL_delete _ _ (uint.nat i) mbi with "Hsends")
      as "[Hsendi Hsends]"; first exact Hmbi.
    destruct (decide (uint.nat i < uint.nat i)%nat) as [Habs|_]; first lia.
    have Hjoini : (mbi.(mb_join) <= length L)%nat.
    { destruct Hcoh as (_ & _ & Hjoins).
      apply (Hjoins mbi). exact (list_elem_of_lookup_2 _ _ _ Hmbi). }
    wp_if_destruct.
    + (* the source connection: skip. Its bundle moves to L ++ [e] by
         monotonicity (its own entry never enters its view; for an aliased
         connection value the view grows, which a sublist survives). *)
      iDestruct (own_member_send_snoc L (uint.nat i) mbi e Hjoini with "Hsendi")
        as "Hsendi".
      wp_for_post. iFrame.
      iSplitR; first (iPureIntro; word).
      iEval (rewrite (big_sepL_delete _ MS (uint.nat i) mbi Hmbi)).
      iSplitL "Hsendi".
      { case_decide as Hci; [iFrame | exfalso; word]. }
      iApply (big_sepL_impl with "Hsends").
      iIntros "!>" (j' mb' Hj') "H".
      case_decide as Hji; first by iExact "H".
      case_decide as Hlt1; case_decide as Hlt2;
        [ by iExact "H" | exfalso; word | exfalso; word | by iExact "H" ].
    + (* relay: the entry is another member's, so its payload is the next
         element of this member's view *)
      iDestruct "Hsendi" as (sent) "Hsendi". iNamed "Hsendi".
      wp_func_call.
      iAssert (ws_prot data) as "#Hwsd"; first by rewrite Hprot.
      wp_apply (wp_Send with "[$Hs $Hsc $Hwsd]").
      { iDestruct (big_sepL_lookup _ _ (uint.nat i) mbi with "Hconninfo") as "$".
        exact Hmbi. }
      iIntros (errs) "(Hs & Hres)".
      (* either way the bundle is re-established at L ++ [e] *)
      iAssert (own_member_send (L ++ [e]) (uint.nat i) mbi)
        with "[Hres]" as "Hsendi".
      { have Hview : relay_view (uint.nat i) (drop mbi.(mb_join) (L ++ [e]))
                     = relay_view (uint.nat i) (drop mbi.(mb_join) L) ++ [data].
        { rewrite drop_app_le // relay_view_snoc_other //=.
          (* the source is member j, and this member is not it: their
             connection values differ *)
          move=> Hji. subst j. rewrite Hmbi in HMSj.
          injection HMSj as HMSj. subst mbi. done. }
        iDestruct "Hres" as "[[_ Hsc] | [Hsc #Hnew]]".
        - (* early failure: nothing went out, the sublist just extends *)
          iExists sent. iFrame "Hsc Hsent". iPureIntro.
          rewrite Hview. apply sublist_inserts_r. exact Hsub.
        - (* sent: message [length sent] of the channel is [data] *)
          iExists (sent ++ [data]).
          rewrite length_app /= Nat.add_1_r. iFrame "Hsc".
          iSplitR.
          { rewrite big_sepL_snoc. iFrame "Hsent". iFrame "Hnew". }
          iPureIntro. rewrite Hview.
          apply sublist_app; [exact Hsub | done]. }
      wp_auto.
      wp_for_post. iFrame.
      iSplitR; first (iPureIntro; word).
      iEval (rewrite (big_sepL_delete _ MS (uint.nat i) mbi Hmbi)).
      iSplitL "Hsendi".
      { case_decide as Hci; [iFrame | exfalso; word]. }
      iApply (big_sepL_impl with "Hsends").
      iIntros "!>" (j' mb' Hj') "H".
      case_decide as Hji; first by iExact "H".
      case_decide as Hlt1; case_decide as Hlt2;
        [ by iExact "H" | exfalso; word | exfalso; word | by iExact "H" ].
  - (* every member has been offered the entry: close the invariant at the
       extended log *)
    iAssert ([∗ list] j' ↦ mb' ∈ MS, own_member_send (L ++ [e]) j' mb')%I
      with "[Hsends]" as "Hsends".
    { iApply (big_sepL_impl with "Hsends").
      iIntros "!>" (j' mb' Hj') "H".
      case_decide as Hlt; first iFrame.
      exfalso. apply lookup_lt_Some in Hj'. word. }
    wp_apply (wp_Mutex__Unlock
      with "[$Hmu $Hlocked Hconnsf Hconns Hcap Hdocf Hdecodef Hmem Hlog
             Hposvs Hsends]").
    { iNext. iExists sl, dv, s_loc, f, MS, (L ++ [e]).
      iFrame "Hconnsf Hconns Hcap Hdocf Hdecodef Hmem Hlog Hdoc Hcodec Hconninfo".
      iSplitR.
      { rewrite big_sepL_snoc. iFrame "Hlogmsgs". iFrame "Hmsg". }
      iSplitR.
      { rewrite big_sepL_snoc. iFrame "Hrcpts". iFrame "Hrcpt". }
      iFrame "Hposvs Hsends".
      iPureIntro. apply (log_coh_snoc MS L j mb _ data Hcoh HMSj eq_refl). }
    iApply "HΦ". iFrame "Hs Hpos".
    iExists (length L). iFrame "Hlogentry".
Qed.

(** [Serve]: one member's receive loop. It owns the member's receive cursor
    and processed cursor for the whole run: the receive cursor makes the
    stream arrive in order and exactly once, the processed cursor ties every
    received message
    to its log entry (S2). It returns them, in step, when the peer stops
    delivering. *)
Lemma wp_Room__Serve (r : loc) (γ : room_names) (γs : store_names)
    (γh : history_names) (c : ClientId) (j : nat) (mb : member) :
  {{{ is_pkg_init wsrelay ∗ is_Room r γ γs γh c ∗ ws_env_preserves ⊤ ∗
      is_room_member γ j mb ∗
      own_recv_cursor mb.(mb_recv) 0 ∗ own_processed mb 0%nat }}}
    r @! (go.PointerType wsrelay.Room) @! "Serve" #(mb.(mb_conn))
  {{{ RET #(); ∃ n : nat,
      own_recv_cursor mb.(mb_recv) n ∗ own_processed mb n }}}.
Proof.
  wp_start as "(#Hroom & #Henv & #Hmember & Hrecv & Hpos)".
  iDestruct "Hmember" as "[Hmidx Hmconn]".
  wp_auto.
  iAssert (∃ n : nat,
    "Hrecv" ∷ own_recv_cursor mb.(mb_recv) n ∗
    "Hpos" ∷ own_processed mb n)%I with "[$Hrecv $Hpos]" as "IH".
  wp_for "IH".
  wp_func_call.
  wp_apply (wp_Receive with "[$Hmconn $Hrecv $Henv]").
  iIntros (err sl0 dta) "(Hsl & Hcap & Hcur)".
  wp_auto.
  destruct err.
  - wp_auto. wp_for_post. iApply "HΦ". iFrame.
  - iDestruct "Hcur" as "(Hrecv & #Hmsg & #Hpd)".
    wp_auto.
    wp_apply (wp_Room__process with "[$Hroom $Hmidx $Hmconn $Hpos $Hmsg $Hpd $Hsl]").
    iIntros "(Hsl & Hpos & _)".
    wp_auto.
    wp_for_post. iFrame.
Qed.

(** [Run]: the accept loop, the server's top-level composition. Every
    accepted connection is joined to the room and served on its own
    goroutine, so every message any peer ever sends flows through
    [wp_Room__process]: applied to the server document (S1), logged (S2), and
    relayed (S3). The loop never returns. Single room: the path Accept
    reports is ignored until the multi-room server (issue #117). *)
Lemma wp_Run (l : loc) (host : ws_endpoint) (r : loc) (γ : room_names)
    (γs : store_names) (γh : history_names) (c : ClientId) :
  {{{ is_pkg_init wsrelay ∗ is_Listener l host ∗ is_Room r γ γs γh c ∗
      ws_env_preserves ⊤ }}}
    @! wsrelay.Run #l #r
  {{{ RET #(); False }}}.
Proof.
  wp_start as "(#Hl & #Hroom & #Henv)".
  wp_auto.
  iAssert emp%I as "IH"; first done.
  wp_for "IH".
  wp_func_call.
  wp_apply (wp_Accept with "[$Hl]").
  iIntros (cn sc rc path) "(#Hconn & Hsend & Hrecv)".
  wp_auto.
  wp_apply (wp_Room__Join with "[$Hroom $Hconn $Hsend]").
  iIntros (j mb) "((%Hcn & %Hsc & %Hrc) & #Hmember & Hpos)".
  wp_auto.
  wp_apply (wp_fork with "[Hrecv Hpos]").
  { rewrite -Hcn.
    wp_apply (wp_Room__Serve _ _ _ _ _ j mb
                with "[$Hroom $Henv $Hmember Hrecv Hpos]").
    { rewrite Hrc. iFrame. }
    iIntros "_". done. }
  wp_for_post. by iFrame.
Qed.

(** The whole server: listen on [host], create the server document as client
    [client], wrap it in a room decoding with [f], and serve forever. The
    closed-system theorem (src/proof/demo/ws_server.v) boots exactly this
    function. *)
Lemma wp_ListenAndServe (host client : w64) (f : func.t) (γh : history_names) :
  (∀ d, ws_prot d = yjs_prot decode γh d) ->
  {{{ is_pkg_init wsrelay ∗
      is_history (A := A) (P := P) γh ∗
      own_client_history γh (uint.nat client) ([] : list Ev) ∗
      codec_spec decode f ∗
      ws_env_preserves ⊤ }}}
    @! wsrelay.ListenAndServe #host #client #f
  {{{ RET #(); False }}}.
Proof.
  intros Hprot.
  wp_start as "(#Hhist & Hcl & #Hcodec & #Henv)".
  wp_auto.
  wp_func_call.
  wp_apply wp_Listen.
  iIntros (l) "#Hl".
  wp_auto.
  wp_apply (wp_NewDoc γh client with "[$Hcl]").
  (* the read capabilities come back with the document (issue #125); the
     boot composition has no reader to hand them to yet, so they are simply
     kept unused here *)
  iIntros (dv s_loc γs) "(#Hdoc & #Hpin & Hrcaps)".
  wp_auto.
  wp_apply (wp_NewRoom dv s_loc γs γh (uint.nat client) f Hprot
             with "[$Hdoc $Hhist $Hpin $Hcodec]").
  iIntros (r γ) "#Hroom".
  wp_auto.
  wp_apply (wp_Run l host r γ γs γh (uint.nat client)
             with "[$Hl $Hroom $Henv]").
  iIntros "[]".
Qed.

End proof.
