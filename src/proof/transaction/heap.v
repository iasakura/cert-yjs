(** The [Transaction] type, Iris layer (issue #206 T1, issue #198 Part II):
    the record a transaction fills, the transaction as the writer holds it
    (the store with its observers at the start state, the record with its
    meaning, the start relation), and what a closure run by [transact] is
    asked to do.

    Definitions
    - [node_span v]: the span a node contributes to a record (head id, length).
    - [own_id_spans sl dq ids]: the [[]idSpan] at [sl] denotes the char-id
      set [ids] (the union of its spans' ids), every span fitting [w64]
      (what [containsId]'s range test needs): a record's slice as
      [textDelta] reads it.
    - [own_transaction_changes tr s inserted tombstoned changed]: the
      transaction struct at [tr]: the store [s] it belongs to and the three
      record fields, which have recorded exactly the char ids [inserted]
      (its [insertSet]), the char ids [tombstoned] (its [deleteSet]) and the
      type addresses [changed] (its [changed] map). The two span slices
      denote their sets as [own_delete_ids] reads a [[]idSpan]: the union of
      the spans' char ids; every recorded span fits [w64]. The receiver
      predicate of the transaction's cell-level methods ([integrate],
      [deleteNode] and the loops over them).
    - [changed_types_bound γs changed changed_locs]: the changed types by
      name and by address are the same types, through the type registry.
    - [own_transaction_record tr s γs m deleted inserted tombstoned changed]:
      the record with its meaning against the data's model [(m, deleted)].
    - [own_transaction tr s γs γh c h m pend deleted inserted tombstoned
      changed]: the transaction, over the issue #219 split: the public
      [own_store] at an existential cell state (its observers at the start
      state) tied to [(pend, deleted)] by [state_pending_tombstoned], the
      holder's [own_replica_history] at the public history and model, the
      record with its meaning, and [transaction_start].
    - [closure_runs_transaction s γs γh f Q]: what [transact] asks of its
      closure: run the fresh transaction to an end state where [Q] holds.

    Laws
    - [node_span_char_ids]: a node's span fits and denotes its run's chars.
    - [own_transaction_changes_store_acc]: borrow the store field (the
      methods read it first).
    - the changed types: [changed_types_bound_empty], [_mark] (one more
      type), [_grow] (a sweep's types, by [bound_names]), [_registered] /
      [_names] (the marked addresses are registered under the marked names,
      and the marked names bound to marked addresses).
    - [own_transaction_observed_agree]: inside a transaction that did not
      change a root, an observer's half of its token is at the root's
      current snapshot (what [Mirror.Check] reads off).
    - [own_transaction_accept_batch] / [own_transaction_client_pin] /
      [own_transaction_history_lb]: the data-level accept-batch update,
      client-pin read and history lower bound, lifted through the sealed
      transaction (what [Doc.ApplySyncUpdate] composes with).

    The WPs: [transaction/wp_private.v] (the record steps, [integrate],
    [deleteNode]), [transaction/deleteRange.v], [transaction/applyUpdate.v],
    [transaction/notify.v], [transaction/transact.v]. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core.
From New.proof Require Import algebra.
From New.proof Require Import prelude.
From New.proof Require Import history.
From iris.algebra Require Import auth gmap gset.
From iris.algebra.lib Require Import dfrac_agree.
From New.proof.id Require Import value heap.
From New.proof.item Require Import run_theory model value heap.
From New.proof.ytype Require Import model value heap.
From New.proof.delta Require Import model value heap.
From New.proof.store Require Import model value heap.
From New.proof.transaction Require Import model.

Section transaction_heap.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.

Notation P := go_string.

Local Notation TId := (TypeId P).

Local Notation Op := (TId * @YjsOperation A)%type.

Local Notation Ev := (@Event Op).

Local Notation DocModel := (gmap TId (list (YjsItem A))).

Local Notation snapshot := (list (YjsItem A * bool)).

(* the store's ghost state, as [store/heap] *)
Context {seq_inG : inG Σ (authR (gmapUR loc (gsetUR (YjsItem A))))}.
Context {acc_inG : inG Σ (authR (gsetUR YjsId))}.
Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO store_state))}.
Context {observed_inG : ghost_varG Σ (list (YjsItem go_string * bool))}.
Context {observers_inG : inG Σ (authR (gsetUR (gname * go_string)))}.
Context {observers_agree_inG : inG Σ (dfrac_agreeR (leibnizO registered_entries))}.

(* [own_slice_cap] is timeless but the New.golang slice library ships no such
   instance ([store/heap] provides its own; this file does not Require it, so
   repeat it here). *)
#[global] Instance own_slice_cap_timeless (V : Type) `{!ZeroVal V} `{!TypedPointsto V} (s : slice.t) (dq : dfrac) :
  Timeless (own_slice_cap V s dq).
Proof. rewrite own_slice_cap_unseal /own_slice_cap_def. apply _. Qed.

(* ===== definitions ======================================================== *)

(** [node_span v]: the span a node contributes to the record, its head id
    and its length as one [idSpan] (what [recordInsert] / [recordDelete]
    append). *)
Definition node_span (v : yjs.item.t) : yjs.idSpan.t :=
  yjs.idSpan.mk v.(yjs.item.id') (W64 (length v.(yjs.item.content').(yjs.content.content'))).

Definition own_id_spans (sl : slice.t) (dq : dfrac) (ids : gset YjsId) : iProp Σ :=
  ∃ (vs : list yjs.idSpan.t),
    "Hspans" ∷ sl ↦*{dq} vs ∗
    "%Hspans_wf" ∷ ⌜Forall span_no_overflow vs⌝ ∗
    "%Hspans_ids" ∷ ⌜ids = ⋃ (span_ids <$> vs)⌝.

(** The transaction struct: the store it belongs to and what it recorded so
    far, as the four fields of [Transaction]. The [changed] map holds [true]
    at every recorded type (a Go set). *)
Definition own_transaction_changes (tr s_loc : loc)
    (inserted tombstoned : gset YjsId) (changed : gset loc) : iProp Σ :=
  ∃ (insert_sl delete_sl : slice.t) (changed_mref : loc)
    (insert_vs delete_vs : list yjs.idSpan.t),
    "Htrstore" ∷ (tr .[(yjs.Transaction.t), "store"]) ↦ s_loc ∗
    "Hinsertf" ∷ (tr .[(yjs.Transaction.t), "insertSet"]) ↦ insert_sl ∗
    "Hinsert" ∷ insert_sl ↦* insert_vs ∗
    "Hinsertcap" ∷ own_slice_cap yjs.idSpan.t insert_sl (DfracOwn 1) ∗
    "%Hinsertwf" ∷ ⌜Forall span_no_overflow insert_vs⌝ ∗
    "%Hinserted" ∷ ⌜inserted = ⋃ (span_ids <$> insert_vs)⌝ ∗
    "Hdeletef" ∷ (tr .[(yjs.Transaction.t), "deleteSet"]) ↦ delete_sl ∗
    "Hdelete" ∷ delete_sl ↦* delete_vs ∗
    "Hdeletecap" ∷ own_slice_cap yjs.idSpan.t delete_sl (DfracOwn 1) ∗
    "%Hdeletewf" ∷ ⌜Forall span_no_overflow delete_vs⌝ ∗
    "%Htombstoned" ∷ ⌜tombstoned = ⋃ (span_ids <$> delete_vs)⌝ ∗
    "Hchangedf" ∷ (tr .[(yjs.Transaction.t), "changed"]) ↦ changed_mref ∗
    "Hchanged" ∷ changed_mref ↦$ (gset_to_gmap true changed : gmap loc bool).

#[global] Instance own_transaction_changes_timeless tr s_loc inserted tombstoned changed :
  Timeless (own_transaction_changes tr s_loc inserted tombstoned changed).
Proof. rewrite /own_transaction_changes. apply _. Qed.

(** [changed_types_bound γs changed changed_locs]: the transaction's changed
    root types by name and by address are the same types: every name in
    [changed] is bound by the type registry to an address in [changed_locs],
    and every address in [changed_locs] to a name in [changed]. *)
Definition changed_types_bound (γs : store_names) (changed : gset P) (changed_locs : gset loc) : iProp Σ :=
  ([∗ set] name ∈ changed, ∃ parent : loc,
     is_type_binding γs.(sn_types) name parent ∗ ⌜parent ∈ changed_locs⌝) ∗
  ([∗ set] parent ∈ changed_locs, ∃ name : P,
     is_type_binding γs.(sn_types) name parent ∗ ⌜name ∈ changed⌝).

#[global] Instance changed_types_bound_persistent γs changed changed_locs :
  Persistent (changed_types_bound γs changed changed_locs).
Proof. rewrite /changed_types_bound. apply _. Qed.

(** [own_transaction_record tr γs m deleted inserted tombstoned changed]:
    the transaction record at [tr] with its meaning against the data's
    public model [(m, deleted)] (issue #206 T1): [inserted] and
    [tombstoned] are the char ids the transaction integrated and tombstoned
    so far, [changed] the root types it wrote, by name (the Go map holds
    their addresses, bound to the names by the type registry). The clauses:
    every inserted id is in the model, every tombstoned id is tombstoned,
    and every recorded id is a char of a changed type's document; with the
    pool's uniqueness of ids that says a type outside [changed] has no id in
    either set, so its snapshot now is its snapshot at the start, which is
    what lets [notify] skip it. What the transaction's batch methods
    ([applyUpdate], [applyDeleteSpans]) take and give back, next to the
    store's data. *)
Definition own_transaction_record (tr s_loc : loc) (γs : store_names) (m : DocModel)
    (deleted inserted tombstoned : gset YjsId) (changed : gset P) : iProp Σ :=
  ∃ (changed_locs : gset loc),
    "Hchanges" ∷ own_transaction_changes tr s_loc inserted tombstoned changed_locs ∗
    "#Hchanged_bound" ∷ changed_types_bound γs changed changed_locs ∗
    "%Hinserted_dom" ∷ ⌜∀ i, i ∈ inserted -> doc_model_has m i = true⌝ ∗
    "%Htombstoned_sub" ∷ ⌜tombstoned ⊆ deleted⌝ ∗
    "%Hrecorded" ∷ ⌜∀ i, i ∈ inserted ∪ tombstoned ->
                     ∃ (name : P) (x : YjsItem A), name ∈ changed ∧
                       x ∈ doc_model_get m (RootId name) ∧ item_id x = i⌝.

(** [own_transaction tr s_loc γs γh c h m pend deleted inserted tombstoned changed]:
    the transaction at [tr] of the store at [s_loc] (issue #206 T1, issue
    #198 Part II): the store with its data at the current state
    [(m, deleted)] and its observers still at the state [(m0, deleted0)] the
    transaction started from, the record with its meaning, and the relation
    between the two states and the record ([transaction_start]: the start
    state is the current one without what the record says). Held by the
    writer, that is by the closure [Doc.Transact] runs, for the
    transaction's duration; [own_transaction_fresh] opens it at a store whose
    two states coincide and [wp_Transaction__notify] closes it back to one. *)
Definition own_transaction (tr s_loc : loc) (γs : store_names) (γh : history_names)
    (c : ClientId) (h : list Ev) (m : DocModel)
    (pend : list (TId * IntegrateInput (A := A)))
    (deleted inserted tombstoned : gset YjsId) (changed : gset P) : iProp Σ :=
  ∃ (state : store_state) (ds : gset YjsId) (m0 : DocModel) (deleted0 : gset YjsId),
    "%Hpend_tomb" ∷ ⌜state_pending_tombstoned state pend deleted⌝ ∗
    "Hstore" ∷ own_store s_loc γs γh 1 state ds m0 deleted0 ∗
    "Hreplica_history" ∷ own_replica_history γs γh c h m state ds ∗
    "Hrecord" ∷ own_transaction_record tr s_loc γs m deleted inserted tombstoned changed ∗
    "%Hstart" ∷ ⌜transaction_start m deleted inserted tombstoned m0 deleted0⌝.

(** [closure_runs_transaction s_loc γs γh f Q]: the closure [f] runs one
    transaction of the store at [s_loc] ([transact]'s argument, issue
    #206 T1): handed the fresh transaction, it returns it, changed as it
    may be, with [Q] holding of the end state (client, history, model,
    pending, tombstones). A one-shot wand, not a persistent triple: the
    closure runs once and may carry the caller's resources (the locals it
    captured) into the transaction. *)
Definition closure_runs_transaction (s_loc : loc) (γs : store_names) (γh : history_names)
    (f : func.t)
    (Q : ClientId -> list Ev -> DocModel -> list (TId * IntegrateInput (A := A)) -> gset YjsId -> iProp Σ) : iProp Σ :=
  ∀ (tr : loc) (c : ClientId) (h : list Ev) (m : DocModel)
    (pend : list (TId * IntegrateInput (A := A))) (deleted : gset YjsId) (Ψ : val -> iProp Σ),
    own_transaction tr s_loc γs γh c h m pend deleted ∅ ∅ ∅ -∗
    (∀ (h' : list Ev) (m' : DocModel) (pend' : list (TId * IntegrateInput (A := A)))
       (deleted' inserted tombstoned : gset YjsId) (changed : gset P),
       own_transaction tr s_loc γs γh c h' m' pend' deleted' inserted tombstoned changed ∗
       Q c h' m' pend' deleted' -∗ Ψ #()) -∗
    WP #f #tr {{ Ψ }}.

(* ===== lemmas ============================================================= *)

(** What a node's span records is its run: a node whose id, content length
    and run agree ([own_item_node]'s pins) contributes a span that fits a
    word and denotes exactly the run's char ids. *)
Lemma node_span_char_ids (v : yjs.item.t) (r : ItemRun) :
  run_wf (run_items r) ->
  toYjsId v.(yjs.item.id') = item_id (run_head_item r) ->
  length v.(yjs.item.content').(yjs.content.content') = length (run_items r) ->
  run_fits r ->
  span_no_overflow (node_span v) ∧ span_ids (node_span v) = char_ids (run_items r).
Proof.
  move=> Hwf Hid Hlen Hfits.
  have Hclk : uint.nat v.(yjs.item.id').(yjs.id.clock') = run_clock r.
  { rewrite /run_clock -Hid //. }
  have Hlen64 : (Z.of_nat (length (run_items r)) < 2^64)%Z.
  { move: Hfits. rewrite /run_fits. lia. }
  split.
  { rewrite /span_no_overflow /node_span /range_no_overflow /= Hlen.
    move: Hfits. rewrite /run_fits -Hclk. word. }
  have Hstep : run_step (run_items r) := run_wf_run_step _ Hwf.
  have Hhead : item_id (run_head_item r) = toYjsId v.(yjs.item.id') by rewrite Hid.
  have Hlenw : length (run_items r) = uint.nat (W64 (length v.(yjs.item.content').(yjs.content.content'))).
  { rewrite Hlen. word. }
  have Hcons : run_items r = run_head_item r :: List.tl (run_items r).
  { rewrite /run_head_item. destruct (run_items r); [by destruct Hwf | reflexivity]. }
  rewrite Hcons in Hstep Hlenw *.
  rewrite /node_span. exact (span_ids_char_ids _ _ _ _ Hhead Hstep Hlenw).
Qed.

Lemma own_transaction_changes_store_acc (tr s_loc : loc)
    (inserted tombstoned : gset YjsId) (changed : gset loc) :
  own_transaction_changes tr s_loc inserted tombstoned changed -∗
  (tr .[(yjs.Transaction.t), "store"]) ↦ s_loc ∗
  ((tr .[(yjs.Transaction.t), "store"]) ↦ s_loc -∗
   own_transaction_changes tr s_loc inserted tombstoned changed).
Proof.
  iIntros "H". iNamed "H". iFrame "Htrstore". iIntros "Htrstore".
  iExists insert_sl, delete_sl, changed_mref, insert_vs, delete_vs. iFrame "∗". done.
Qed.


Lemma changed_types_bound_empty (γs : store_names) :
  ⊢ changed_types_bound γs ∅ ∅.
Proof. rewrite /changed_types_bound !big_sepS_empty. auto. Qed.

(** Marking one more type: the name and its address join together. *)
Lemma changed_types_bound_mark (γs : store_names) (changed : gset P) (changed_locs : gset loc)
    (name : P) (parent : loc) :
  is_type_binding γs.(sn_types) name parent -∗
  changed_types_bound γs changed changed_locs -∗
  changed_types_bound γs (changed ∪ {[name]}) (changed_locs ∪ {[parent]}).
Proof.
  iIntros "#Hbind [#Hnames #Hlocs]". iSplit.
  - iApply big_sepS_intro. iIntros "!>" (nm Hnm).
    apply elem_of_union in Hnm as [Hnm | Hnm].
    + iDestruct (big_sepS_elem_of _ _ nm Hnm with "Hnames") as (q) "[#Hb %Hin]".
      iExists q. iFrame "Hb". iPureIntro. apply elem_of_union_l. exact Hin.
    + apply elem_of_singleton in Hnm as ->.
      iExists parent. iFrame "Hbind". iPureIntro. apply elem_of_union_r. by apply elem_of_singleton.
  - iApply big_sepS_intro. iIntros "!>" (q Hq).
    apply elem_of_union in Hq as [Hq | Hq].
    + iDestruct (big_sepS_elem_of _ _ q Hq with "Hlocs") as (nm) "[#Hb %Hin]".
      iExists nm. iFrame "Hb". iPureIntro. apply elem_of_union_l. exact Hin.
    + apply elem_of_singleton in Hq as ->.
      iExists name. iFrame "Hbind". iPureIntro. apply elem_of_union_r. by apply elem_of_singleton.
Qed.

(** The marked addresses are registered, under the marked names: what a
    transaction reads off the registry authority. *)
Lemma changed_types_bound_registered (γs : store_names) (changed : gset P) (changed_locs : gset loc)
    (bind : gmap P loc) :
  ghost_map_auth γs.(sn_types) 1 bind -∗
  changed_types_bound γs changed changed_locs -∗
  ⌜∀ q, q ∈ changed_locs -> ∃ nm, nm ∈ changed ∧ bind !! nm = Some q⌝.
Proof.
  iIntros "Hauth [_ #Hlocs]". iIntros (q Hq).
  iDestruct (big_sepS_elem_of _ _ q Hq with "Hlocs") as (nm) "[#Hb %Hin]".
  iDestruct (ghost_map_lookup with "Hauth Hb") as %Hlk.
  iPureIntro. by exists nm.
Qed.

(** The marked names are bound to marked addresses: what a transaction reads
    off the registry authority for the types it did not mark. *)
Lemma changed_types_bound_names (γs : store_names) (changed : gset P) (changed_locs : gset loc)
    (bind : gmap P loc) :
  ghost_map_auth γs.(sn_types) 1 bind -∗
  changed_types_bound γs changed changed_locs -∗
  ⌜∀ nm, nm ∈ changed -> ∃ q, bind !! nm = Some q ∧ q ∈ changed_locs⌝.
Proof.
  iIntros "Hauth [#Hnames _]". iIntros (nm Hnm).
  iDestruct (big_sepS_elem_of _ _ nm Hnm with "Hnames") as (q) "[#Hb %Hin]".
  iDestruct (ghost_map_lookup with "Hauth Hb") as %Hlk.
  iPureIntro. by exists q.
Qed.

(** Marking a sweep's types: the addresses grow to [changed_locs'], every
    new one registered under [bind], and the names grow by the names [bind]
    gives the new addresses ([bound_names]). *)
Lemma changed_types_bound_grow (γs : store_names) (changed : gset P)
    (changed_locs changed_locs' : gset loc) (bind : gmap P loc) :
  changed_locs ⊆ changed_locs' ->
  (∀ q, q ∈ changed_locs' -> q ∈ changed_locs ∨ ∃ nm, bind !! nm = Some q) ->
  ([∗ map] name ↦ q ∈ bind, is_type_binding γs.(sn_types) name q) -∗
  changed_types_bound γs changed changed_locs -∗
  changed_types_bound γs (changed ∪ bound_names bind changed_locs') changed_locs'.
Proof.
  move=> Hsub Hnew. iIntros "#Hbinds [#Hnames #Hlocs]". iSplit.
  - iApply big_sepS_intro. iIntros "!>" (nm Hnm).
    apply elem_of_union in Hnm as [Hnm | Hnm].
    + iDestruct (big_sepS_elem_of _ _ nm Hnm with "Hnames") as (q) "[#Hb %Hin]".
      iExists q. iFrame "Hb". iPureIntro. exact (Hsub q Hin).
    + apply elem_of_bound_names in Hnm as (q & Hbq & Hq).
      iDestruct (big_sepM_lookup _ _ nm q Hbq with "Hbinds") as "#Hb".
      iExists q. iFrame "Hb". iPureIntro. exact Hq.
  - iApply big_sepS_intro. iIntros "!>" (q Hq).
    destruct (Hnew q Hq) as [Hold | (nm & Hb)].
    + iDestruct (big_sepS_elem_of _ _ q Hold with "Hlocs") as (nm) "[#Hb %Hin]".
      iExists nm. iFrame "Hb". iPureIntro. apply elem_of_union_l. exact Hin.
    + iDestruct (big_sepM_lookup _ _ nm q Hb with "Hbinds") as "#Hbnd".
      iExists nm. iFrame "Hbnd". iPureIntro. apply elem_of_union_r.
      apply elem_of_bound_names. by exists q.
Qed.

(** The data-level laws lifted to the transaction (issue #219): the
    accept-batch update and the client pin, each opening the body,
    using the [own_store_data] form of the law through the split, and
    closing the body back unchanged. *)
Lemma own_transaction_accept_batch (tr s_loc : loc) (γs : store_names) (γh : history_names)
    (c : ClientId) (h : list Ev) (m : DocModel)
    (pend : list (TId * IntegrateInput (A := A)))
    (deleted inserted tombstoned : gset YjsId) (changed : gset P)
    (L : list (TId * IntegrateInput (A := A))) :
  (∀ x, x ∈ L -> in_id x.2 ∈ delivered_ids h ∪ pending_id_set pend) ->
  own_transaction tr s_loc γs γh c h m pend deleted inserted tombstoned changed ==∗
  own_transaction tr s_loc γs γh c h m pend deleted inserted tombstoned changed ∗
  [∗ list] x ∈ L, is_accepted γs (in_id x.2).
Proof.
  iIntros (HL) "Htx".
  iDestruct "Htx" as (state0 ds0 m0 deleted0) "Htx". iNamed "Htx".
  iDestruct "Hstore" as "[Hcore Hobservers]".
  iDestruct (own_store_data_build with "Hcore Hreplica_history") as "Hdata".
  destruct Hpend_tomb as [Hpend_state Hdeleted_state].
  iEval (rewrite Hpend_state) in "Hdata". iEval (rewrite -Hdeleted_state) in "Hdata".
  iMod (own_store_data_accept_batch _ _ _ _ _ _ _ _ L HL with "Hdata") as "[Hdata #Haccepts]".
  iDestruct (own_store_data_split with "Hdata") as (state' ds') "(%Hface' & Hcore' & Hreplica_history')". destruct Hface' as [Hpend' Hdel'].
  iModIntro. iFrame "Haccepts".
  iExists state', ds', m0, deleted0.
  iSplitR; first (iPureIntro; split; [exact Hpend' | exact Hdel']).
  iSplitL "Hcore' Hobservers"; first iFrame "Hcore' Hobservers".
  iFrame "Hreplica_history' Hrecord".
  iPureIntro. exact Hstart.
Qed.

Lemma own_transaction_client_pin (tr s_loc : loc) (γs : store_names) (γh : history_names)
    (c : ClientId) (h : list Ev) (m : DocModel)
    (pend : list (TId * IntegrateInput (A := A)))
    (deleted inserted tombstoned : gset YjsId) (changed : gset P) :
  own_transaction tr s_loc γs γh c h m pend deleted inserted tombstoned changed -∗
  own_transaction tr s_loc γs γh c h m pend deleted inserted tombstoned changed ∗
  is_store_client γs c.
Proof.
  iIntros "Htx".
  iDestruct "Htx" as (state0 ds0 m0 deleted0) "Htx". iNamed "Htx".
  iDestruct "Hstore" as "[Hcore Hobservers]".
  iDestruct (own_store_data_build with "Hcore Hreplica_history") as "Hdata".
  destruct Hpend_tomb as [Hpend_state Hdeleted_state].
  iEval (rewrite Hpend_state) in "Hdata". iEval (rewrite -Hdeleted_state) in "Hdata".
  iDestruct (own_store_data_client_pin with "Hdata") as "[Hdata #Hpin]".
  iDestruct (own_store_data_split with "Hdata") as (state' ds') "(%Hface' & Hcore' & Hreplica_history')". destruct Hface' as [Hpend' Hdel'].
  iFrame "Hpin".
  iExists state', ds', m0, deleted0.
  iSplitR; first (iPureIntro; split; [exact Hpend' | exact Hdel']).
  iSplitL "Hcore' Hobservers"; first iFrame "Hcore' Hobservers".
  iFrame "Hreplica_history' Hrecord".
  iPureIntro. exact Hstart.
Qed.

Lemma own_transaction_history_lb (tr s_loc : loc) (γs : store_names) (γh : history_names)
    (c : ClientId) (h : list Ev) (m : DocModel)
    (pend : list (TId * IntegrateInput (A := A)))
    (deleted inserted tombstoned : gset YjsId) (changed : gset P) :
  own_transaction tr s_loc γs γh c h m pend deleted inserted tombstoned changed -∗
  own_transaction tr s_loc γs γh c h m pend deleted inserted tombstoned changed ∗
  is_history_lb γh c h.
Proof.
  iIntros "Htx".
  iDestruct "Htx" as (state0 ds0 m0 deleted0) "Htx". iNamed "Htx".
  iDestruct "Hstore" as "[Hcore Hobservers]".
  iDestruct (own_store_data_build with "Hcore Hreplica_history") as "Hdata".
  destruct Hpend_tomb as [Hpend_state Hdeleted_state].
  iEval (rewrite Hpend_state) in "Hdata". iEval (rewrite -Hdeleted_state) in "Hdata".
  iDestruct (own_store_data_history_lb with "Hdata") as "[Hdata #Hlb]".
  iDestruct (own_store_data_split with "Hdata") as (state' ds') "(%Hface' & Hcore' & Hreplica_history')". destruct Hface' as [Hpend' Hdel'].
  iFrame "Hlb".
  iExists state', ds', m0, deleted0.
  iSplitR; first (iPureIntro; split; [exact Hpend' | exact Hdel']).
  iSplitL "Hcore' Hobservers"; first iFrame "Hcore' Hobservers".
  iFrame "Hreplica_history' Hrecord".
  iPureIntro. exact Hstart.
Qed.

(** An observer's own half agrees with the registry's inside a transaction
    that did not change its root: the snapshot it was last told is the
    root's current one, the record having no char of that root. What
    [Mirror.Check] reads off ([demo/observe_app]). *)
Lemma own_transaction_observed_agree (tr s_loc : loc) (γs : store_names) (γh : history_names)
    (c : ClientId) (h : list Ev) (m : DocModel) (pend : list (TId * IntegrateInput (A := A)))
    (deleted inserted tombstoned : gset YjsId) (changed : gset P)
    (name : P) (γo : gname) (s : snapshot) :
  name ∉ changed ->
  own_transaction tr s_loc γs γh c h m pend deleted inserted tombstoned changed -∗
  is_text_observed γs name γo -∗
  own_observed γo s -∗
  ⌜s = type_snapshot m deleted name⌝.
Proof.
  move=> Hnot. iIntros "Htx #Hobserved Hobs".
  iDestruct "Htx" as (state0 ds0 m0 deleted0) "Htx". iNamed "Htx".
  iDestruct "Hstore" as "[Hcore Hobservers]".
  iDestruct (own_store_data_build with "Hcore Hreplica_history") as "Hdata".
  destruct Hpend_tomb as [Hpend_state Hdeleted_state].
  iEval (rewrite Hpend_state) in "Hdata". iEval (rewrite -Hdeleted_state) in "Hdata".
  iDestruct "Hobservers" as (observers_mref) "(Hobserversf & Hregistry)".
  iDestruct "Hregistry" as (registry registered) "(Hobserversmap & Hobserversauth & Hregagree & #Hregistered_bind & Hobservers)".
  iDestruct "Hrecord" as (changed_locs) "Hrecord". iNamed "Hrecord".
  (* the token is registered under [name], at some address *)
  iDestruct (own_valid_2 with "Hobserversauth Hobserved") as %Hincl.
  apply auth_both_valid_discrete in Hincl as [Hincl _].
  apply gset_included in Hincl.
  have Htok : (γo, name) ∈ registered_tokens registered.
  { apply Hincl. apply elem_of_singleton. reflexivity. }
  apply elem_of_registered_tokens in Htok as (parent & γos & Hreglk & Hγo).
  (* its entry holds the registry's half at the start snapshot *)
  iDestruct (big_sepM2_dom with "Hobservers") as %Hdomeq.
  have [cbs_sl Hrlk] : is_Some (registry !! parent).
  { apply elem_of_dom. rewrite Hdomeq. apply elem_of_dom. by exists (name, γos). }
  iDestruct (big_sepM2_lookup _ _ _ parent cbs_sl (name, γos) Hrlk Hreglk with "Hobservers") as "Hentry".
  iDestruct "Hentry" as (cbs) "Hentry". iNamed "Hentry". simpl.
  apply list_elem_of_lookup in Hγo as [j Hj].
  iDestruct (big_sepL2_length with "Hentry_callbacks") as %Hlen.
  have Hjlt : (j < length cbs)%nat by (rewrite Hlen; exact (lookup_lt_Some _ _ _ Hj)).
  destruct (lookup_lt_is_Some_2 cbs j Hjlt) as [cb Hcb].
  iDestruct (big_sepL2_lookup _ _ _ j cb γo Hcb Hj with "Hentry_callbacks") as "[_ Hstore_half]".
  iDestruct (own_observed_agree with "Hstore_half Hobs") as %<-.
  (* the root is outside the record, so its snapshot did not move *)
  iDestruct "Hdata" as (client k pdel locs p bind acc) "Hown". iNamed "Hown".
  iDestruct (registered_bindings_lookup with "HtypesAuth Hregistered_bind") as %Hregbind.
  have Hbindlk : bind !! name = Some parent := Hregbind parent (name, γos) Hreglk.
  iDestruct (changed_types_bound_names with "HtypesAuth Hchanged_bound") as %Hbound.
  iDestruct (changed_types_bound_registered with "HtypesAuth Hchanged_bound") as %Hmarked.
  iDestruct (own_store_state_registry_coh with "Hstate") as %Hregcoh.
  iDestruct (own_store_state_run_pool_invs with "Hstate") as %Hpoolinv.
  simpl in Hregcoh, Hpoolinv.
  iPureIntro.
  apply (type_snapshot_untouched _ _ _ _ _ _ name Hstart).
  apply (type_untouched_by_record m bind p inserted tombstoned changed changed_locs name parent
           Hpoolinv Hregcoh Hregmodel Hrecorded Hbound Hbindlk).
  move=> Hin. apply Hnot.
  destruct (Hmarked parent Hin) as (nm & Hnm & Hnmlk).
  rewrite (proj1 (proj2 Hregcoh) nm name parent Hnmlk Hbindlk) in Hnm. exact Hnm.
Qed.

End transaction_heap.
