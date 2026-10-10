(** Specs of the [store]'s internal lock layer: [wlock] / [wunlock] trade
    the write lock for the issue #219 split of the lock body, the core
    ([own_store_core], what every store method preserves), the session
    ([own_replica_history], what the holder re-establishes before release)
    and the observers told up to the current model and tombstones;
    [rlock] / [runlock] trade a reader slot for an [rfrac] fraction of
    the public [own_store] (issue #219 M4), with a history certificate
    converted at the linearization point (issue #125). All four are
    [storeRef] methods, so these are their method specs; the methods are
    public for [storeRef] (Text / Doc / codec call them), so each takes
    and returns [own_store] whole at its fraction.
    Unexported, with no exported counterpart: every method proof of the
    store and of the [Text] handle enters through these, so they sit next
    to the invariant rather than inside any one method file. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core.
From New.proof Require Import prelude.
From New.proof.id Require Import id.
From New.proof.item Require Import item.
From New.proof.ytype Require Import ytype.
From New.proof.store Require Import model value heap.
From New.proof.item Require Import run_theory model value heap.
From New.proof Require Import history.
From New.proof.sync_proof Require Import base mutex rwmutex rwmutex_guard.
                                                      (* store lock: rwmutex.is_RWMutex + LP Lock/Unlock
                                                         (y-octo Arc<RwLock<DocStore>>); the
                                                         guard's rfrac + tok_set reader accounting *)
From New.proof Require Import tok_set.
From iris.algebra Require Import auth gmap gset.
From iris.algebra.lib Require Import dfrac_agree.
From iris.bi.lib Require Import fractional.
From stdpp Require Import sorting.

(* iris.algebra / stdpp.sorting push [nat_scope], retuning the default [<] / [≤].
   The verified WP proofs write [Z] comparisons (e.g. [sint.Z i < …]) unannotated
   and annotate [nat] ones with [%nat], so restore [Z_scope] as the default. *)
Local Open Scope Z_scope.

(* A generic [ghost_map] grow-and-persist step, in its own section so it depends
   only on a [ghost_mapG] instance (issue #54): the certificate proof in
   [store/applyUpdate], whose section lacks the store's [seq_inG] / [ftypes_inG],
   reconciles the registry map with the concrete one after [applyUpdate]'s drain
   creates fresh root types, minting one persistent binding per new name. *)

Section store_wp_private.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.

(* The ghost op-history types ([history] / [network_model]) at the
   document content type; type names are Go strings (issue #49). *)
Notation P := go_string.

Local Notation TId := (TypeId P).

Local Notation Op := (TId * @YjsOperation A)%type.

Local Notation Ev := (@Event Op).

Local Notation DocModel := (gmap TId (list (YjsItem A))).

(** Store lock = a [sync.Mutex]. The per-type item SET lives in a grow-only ghost
    (below), keyed by the type's [parent] loc. *)

Context {sync_pkg : sync.Assumptions}.

(** Item-SET RA: [auth (gmap loc (gset (YjsItem A)))] — the AUTH wraps the whole
    map (NOT [gmap (auth gset)], where a per-key frag would be valid even for an
    absent key and so would NOT witness registration). The authority [● m] (per
    type-loc item set) sits in the lock body; a persistent fragment
    [◯ {[parent := S]}] held by [is_Text] gives, when combined with [● m],
    gmap-inclusion [{[parent := S]} ≼ m] = [∃ S', m !! parent = Some S' ∧ S ⊆ S']
    — i.e. it BOTH witnesses [parent ∈ dom m] (= the type is registered) AND
    bounds [S ⊆ S'] (the lower bound). Insert only adds items (delete just flips a
    flag), so each item set grows monotonically under [⊆]; a recorded lower bound
    stays valid forever.

    We track full ITEMS, not just ids: a membership bound [x ∈ S ⊆ tm_arr tm]
    then pins [x] to a *genuine* document item (same structure, not merely the
    same id), which is what lets [Text.Insert] expose the post as a real
    [sublist L L'] rather than only an id-set inclusion. [gset (YjsItem A)] needs
    [Countable (YjsItem A)] (derived in [prelude] via [gen_tree]). Order is not
    tracked in the ghost (recoverable from origins / from [YjsArrInvariant]). *)

Notation seqUR := (authR (gmapUR loc (gsetUR (YjsItem A)))).

Context {seq_inG : inG Σ seqUR}.

(** Accepted-id RA (this branch): a GROW-ONLY set of ids the store has
    "accepted", i.e. promised not to lose. [authR (gsetUR YjsId)] — the
    authority [● acc] sits in the lock body, and a persistent lower-bound
    fragment [◯ {[i]}] (gset elements are core-id) is the [is_accepted]
    receipt every applyUpdate hands back per input. The store invariant ties
    [acc ⊆ delivered_ids h ∪ pending ids], so an accepted id is forever
    delivered-or-buffered: this is what makes "no input is lost" an
    ENFORCEABLE guarantee (a discarding implementation could not mint the
    receipt), unlike a bare existential over the pending list. *)

Notation accUR := (authR (gsetUR YjsId)).

Context {acc_inG : inG Σ accUR}.

Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO store_state))}.
Context {observers_agree_inG : inG Σ (dfrac_agreeR (leibnizO registered_entries))}.
(* the observers' tokens and registrations (issue #198 Part II), as [store/heap] *)
Context {observed_inG : ghost_varG Σ (list (YjsItem go_string * bool))}.
Context {observers_inG : inG Σ (authR (gsetUR (gname * go_string)))}.

(* The [∷] (named) wrapper blocks [Timeless] TC resolution; unfold it (as
   [New.proof.sync_proof.rwmutex] does) so the [Timeless] instances below go
   through the named conjuncts of [own_item_map] / the lock body. *)

#[local] Hint Extern 100 (Timeless (?n ∷ ?P)) =>
  (change (n ∷ P) with P) : typeclass_instances.

(* [rwmutex_inhabited] / [tie_store_timeless] are [#[local]] in [store/heap];
   opening the tie invariant here needs them again (the observers beside
   [tie_store] are not timeless: they stay under the later). *)
#[local] Instance rwmutex_inhabited : Inhabited rwmutex := populate Locked.

#[local] Instance tie_store_timeless s_loc γs γh n m deleted :
  Timeless (tie_store s_loc γs γh n m deleted).
Proof.
  rewrite /tie_store;
    repeat first [ apply sep_timeless | apply exist_timeless; intros ? ]; apply _.
Qed.


(** Write-lock acquire. The write [Lock] linearizes at [RLocked 0]
    (fraction 1), where the invariant holds the whole split: the public
    [own_store] at fraction 1 and the session ([own_replica_history], what
    the holder re-establishes before release); the invariant is left
    holding [Locked] (the bare reader-count authority). The store comes
    out under a later: the observers' callback contracts are not
    timeless (the next program step strips it). *)
Lemma wp_Store__wlock (ref : loc) (γs : store_names) (γh : history_names) :
  {{{ is_pkg_init yjs ∗ is_store_ref ref γs γh }}}
    ref @! (go.PointerType yjs.storeRef) @! "wlock" #()
  {{{ RET #(); own_wlock γs ∗
      ∃ (c : ClientId) (h : list Ev) (m : DocModel),
        ▷ ∃ (state : store_state) (ds : gset YjsId),
            own_store (store_of_ref ref) γs γh 1 state ds m (pool_tombstoned (ss_pool state)) ∗
            own_replica_history γs γh c h m state ds }}}.
Proof.
  wp_start_folded as "His". iNamed "His".
  wp_method_call. wp_call. wp_call. wp_auto.
  wp_apply (rwmutex.wp_RWMutex__Lock with "[$Hrw]").
  iInv "Htie" as "Hi" "Hclose".
  iDestruct "Hi" as (st) "[>Hown Hbody]".
  iFrame "Hown". iApply fupd_mask_intro; first solve_ndisj. iIntros "Hmask".
  iIntros "%Hst Hlocked". subst st.
  iEval (cbn [tie_body]) in "Hbody".
  iDestruct "Hbody" as "(>Hrauth & >Htoks0 & >Hwl & Hrest)".
  iDestruct "Hrest" as (m deleted) "[>Hstore Hobservers]".
  iEval (rewrite /tie_store) in "Hstore".
  iDestruct "Hstore" as (c h state ds) "(%Hdel & Hcore & Hsession)".
  iMod "Hmask" as "_".
  iMod ("Hclose" with "[Hlocked Hrauth]") as "_".
  { iExists Locked. iFrame "Hlocked". iEval (cbn [tie_body]). iFrame "Hrauth". }
  iModIntro. wp_auto. iApply "HΦ". iFrame "Hwl".
  iExists c, h, m. iNext.
  iExists state, ds.
  iEval (rewrite frac_of_0) in "Hcore".
  iEval (rewrite frac_of_0) in "Hobservers".
  subst deleted.
  rewrite /own_store. iFrame "Hcore Hsession Hobservers".
Qed.


(** Write-lock release. Consumes [own_wlock] and the split at whatever
    state the writer left the store: the public [own_store] whole, with
    the observers told up to the final model and the state's tombstones
    (a transaction ends with [store.notify]), and the session back in
    coherence at that model. The "invariant is in [RLocked]" case
    (unlock without the lock) is impossible: the [own_wlock] clash. *)
Lemma wp_Store__wunlock (ref : loc) (γs : store_names) (γh : history_names)
    (c : ClientId) (h : list Ev) (m : DocModel)
    (state : store_state) (ds : gset YjsId) :
  {{{ is_pkg_init yjs ∗ is_store_ref ref γs γh ∗ own_wlock γs ∗
      own_store (store_of_ref ref) γs γh 1 state ds m (pool_tombstoned (ss_pool state)) ∗
      own_replica_history γs γh c h m state ds }}}
    ref @! (go.PointerType yjs.storeRef) @! "wunlock" #()
  {{{ RET #(); True }}}.
Proof.
  wp_start_folded as "(His & Hwl & Hstore & Hsession)". iNamed "His".
  iDestruct "Hstore" as "[Hcore Hobservers]".
  wp_method_call. wp_call. wp_call. wp_auto.
  wp_apply (rwmutex.wp_RWMutex__Unlock with "[$Hrw]").
  iInv "Htie" as "Hi" "Hclose".
  iDestruct "Hi" as (st) "[>Hown Hbody]".
  destruct st.
  - iEval (cbn [tie_body]) in "Hbody".
    iDestruct "Hbody" as "(_ & _ & >Hwl2 & _)".
    iDestruct (ghost_var_valid_2 with "Hwl Hwl2") as %[Hbad _].
    exfalso. by apply (Qp.not_add_le_l 1 1).
  - iEval (cbn [tie_body]) in "Hbody".
    iDestruct "Hbody" as ">Hrauth".
    iFrame "Hown". iApply fupd_mask_intro; first solve_ndisj. iIntros "Hmask".
    iIntros "Hrl0".
    iMod "Hmask" as "_".
    iMod (own_toks_0 γs.(sn_rmax)) as "Htoks0".
    iMod ("Hclose" with "[Hrl0 Hrauth Htoks0 Hwl Hcore Hsession Hobservers]") as "_".
    { iExists (RLocked 0). iFrame "Hrl0". iEval (cbn [tie_body]).
      iFrame "Hrauth Htoks0 Hwl".
      iExists m, (pool_tombstoned (ss_pool state)).
      iSplitR "Hobservers"; last by (iEval (rewrite frac_of_0); iFrame "Hobservers").
      rewrite /tie_store frac_of_0.
      iExists c, h, state, ds. iFrame "Hcore Hsession". done. }
    iModIntro. wp_auto. by iApply "HΦ".
Qed.


(** Read-lock acquire: peels one [rfrac] share of the public [own_store]
    off the lock invariant (bumping the reader count), under one later
    (the observers' callback contracts are not timeless; the caller's
    next program step strips it).

    Two pure facts come with the share, both of them about the lock body's
    quiescent agreement between its halves, which a share of [own_store]
    cannot express on its own, and which the read lock's linearization point
    is the one moment to read:

    - the told model [m0] really is this state's document model
      ([pool_registry_models]). The predicate leaves it free, because a
      transaction moves the data ahead of what the observers were told.
    - every insert the reader's certificate says was delivered already has
      its item in [m0], under the type it targeted ([delivered_reflected]).
      The reader brings a prefix certificate of THIS replica's op history
      and the client pin identifying it (issue #125).

    Neither mentions a root: taking the lock is not a read of any one type,
    and a reader lands these on the root it cares about afterwards, with its
    own binding against the registry authority inside the share. *)
Lemma wp_Store__rlock (ref : loc) (γs : store_names) (γh : history_names)
    (c : ClientId) (h0 : list Ev) :
  {{{ is_pkg_init yjs ∗ is_store_ref ref γs γh ∗ own_read_cap γs ∗
      is_store_client γs c ∗ is_history_lb γh c h0 }}}
    ref @! (go.PointerType yjs.storeRef) @! "rlock" #()
  {{{ (state : store_state) (ds : gset YjsId) (m0 : DocModel), RET #();
      own_read_locked γs ∗
      ▷ own_store (store_of_ref ref) γs γh rwmutex_guard.rfrac state ds m0
          (pool_tombstoned (ss_pool state)) ∗
      ⌜pool_registry_models m0 (ss_bind state) (ss_pool state)⌝ ∗
      ⌜delivered_reflected h0 m0⌝ }}}.
Proof.
  wp_start_folded as "(His & Hcap & #Hpin & #Hlb)". iNamed "His".
  iDestruct "Hcap" as "[Htok Hmaxtok]".
  wp_method_call. wp_call. wp_call. wp_auto.
  wp_apply (rwmutex.wp_RWMutex__RLock with "[$Hrw $Htok]").
  iInv "Htie" as "Hi" "Hclose".
  iDestruct "Hi" as (st) "[>Hown Hbody]".
  iFrame "Hown". iApply fupd_mask_intro; first solve_ndisj. iIntros "Hmask".
  iIntros (n) "%Hst Hrl". subst st.
  iEval (cbn [tie_body]) in "Hbody".
  iDestruct "Hbody" as "(>Hrauth & >Hmaxn & >Hwl & Hrest)".
  iDestruct "Hrest" as (m deleted) "[>Hstore Hobservers]".
  iEval (rewrite /tie_store) in "Hstore".
  iDestruct "Hstore" as (c0 h state ds) "(%Hdel & Hcore & Hsession)".
  (* the two reads of the session, at the one moment it is visible *)
  iDestruct (own_replica_history_registry_models with "Hsession") as %Hregmodel.
  iDestruct (own_store_core_session_delivered_reflected with "Hcore Hsession Hpin Hlb")
    as %Hdeliv.
  iCombine "Hmaxn Hmaxtok" as "Hmaxn1".
  iCombine "Hmax Hmaxn1" gives %Hbound.
  iMod (own_tok_auth_S with "Hrauth") as "[Hrauth Hrtok]".
  assert (Z.of_nat n < rwmutex.actualMaxReaders)%Z as Hlt by (rewrite rwmutex.actualMaxReaders_unseal in Hbound |- *; lia).
  iEval (rewrite (frac_of_split n Hlt) own_store_core_split) in "Hcore".
  iDestruct "Hcore" as "[Hcore_r Hcore_i]".
  iEval (rewrite (frac_of_split n Hlt) own_observers_split later_sep) in "Hobservers".
  iDestruct "Hobservers" as "[Hobs_r Hobs_i]".
  iMod "Hmask" as "_".
  iMod ("Hclose" with "[Hrl Hrauth Hmaxn1 Hwl Hcore_i Hsession Hobs_i]") as "_".
  { iExists (RLocked (S n)). iFrame "Hrl". iEval (cbn [tie_body]).
    replace (S n) with (n + 1)%nat by lia.
    iFrame "Hrauth Hmaxn1 Hwl".
    iExists m, deleted. iFrame "Hobs_i". rewrite /tie_store.
    iExists c0, h, state, ds. iFrame "Hcore_i Hsession". done. }
  iModIntro. wp_auto. iApply ("HΦ" $! state ds m).
  iFrame "Hrtok".
  subst deleted.
  iSplitL "Hcore_r Hobs_r";
    last (iPureIntro; split; [exact Hregmodel | exact Hdeliv]).
  iNext. rewrite /own_store. iFrame "Hcore_r Hobs_r".
Qed.


(** Read-lock release: the reader's [rfrac] share recombines with the
    lock invariant's remainder. The core's agreement ghost proves the
    state (and the delete set) did not move since the [RLock] (a writer
    would have needed the whole fractions), so the cores recombine at
    the invariant's state; the observers recombine under the later
    ([own_observers_combine]: the registry's agreement ghost aligns the
    contents, each token's ghost_var the told snapshot). Returns
    [own_read_cap]. *)
Lemma wp_Store__runlock (ref : loc) (γs : store_names) (γh : history_names)
    (state_r : store_state) (ds_r : gset YjsId) (m_r : DocModel) (d_r : gset YjsId) :
  {{{ is_pkg_init yjs ∗ is_store_ref ref γs γh ∗ own_read_locked γs ∗
      own_store (store_of_ref ref) γs γh rwmutex_guard.rfrac state_r ds_r m_r d_r }}}
    ref @! (go.PointerType yjs.storeRef) @! "runlock" #()
  {{{ RET #(); own_read_cap γs }}}.
Proof.
  wp_start_folded as "(His & Hrtok & Hstore_r)". iNamed "His".
  iDestruct "Hstore_r" as "[Hcore_r Hobs_r]".
  wp_method_call. wp_call. wp_call. wp_auto.
  wp_apply (rwmutex.wp_RWMutex__RUnlock with "[$Hrw]").
  iInv "Htie" as "Hi" "Hclose".
  iDestruct "Hi" as (st) "[>Hown Hbody]".
  destruct st as [nr | ].
  2:{ iEval (cbn [tie_body]) in "Hbody". iDestruct "Hbody" as ">Hrauth".
      iCombine "Hrauth Hrtok" gives %Hbad. exfalso. lia. }
  destruct nr as [ | n ].
  { iEval (cbn [tie_body]) in "Hbody". iDestruct "Hbody" as "(>Hrauth & _)".
    iCombine "Hrauth Hrtok" gives %Hbad. exfalso. lia. }
  iEval (cbn [tie_body]) in "Hbody".
  iDestruct "Hbody" as "(>Hrauth & >Hmaxsn & >Hwl & Hrest)".
  iDestruct "Hrest" as (m deleted) "[>Hstore Hobservers]".
  iEval (rewrite /tie_store) in "Hstore".
  iDestruct "Hstore" as (c0 h state ds) "(%Hdel & Hcore_i & Hsession)".
  (* the state did not move since the RLock: the agreement ghost says so *)
  iDestruct (own_store_core_agree with "Hcore_r Hcore_i") as %[Heqst Heqds].
  subst state_r ds_r.
  iCombine "Hmax Hmaxsn" gives %Hbound.
  assert (Z.of_nat n < rwmutex.actualMaxReaders)%Z as Hlt by (rewrite rwmutex.actualMaxReaders_unseal in Hbound |- *; lia).
  iExists n. iFrame "Hown".
  iApply fupd_mask_intro; first solve_ndisj. iIntros "Hmask".
  iIntros "[Hrln Htok]".
  iMod "Hmask" as "_".
  iMod (own_tok_auth_delete_S with "Hrauth Hrtok") as "Hrauth".
  iEval (rewrite -Nat.add_1_r) in "Hmaxsn".
  iDestruct (own_toks_add_1 1 n γs.(sn_rmax) with "Hmaxsn") as "[Hmaxn Hmaxtok]".
  iCombine "Hcore_r Hcore_i" as "Hcore".
  iEval (rewrite -own_store_core_split -(frac_of_split n Hlt)) in "Hcore".
  iAssert (▷ own_observers (store_of_ref ref) γs γh (frac_of n) m deleted)%I
    with "[Hobs_r Hobservers]" as "Hobs".
  { iNext. iEval (rewrite (frac_of_split n Hlt)).
    iApply (own_observers_combine with "Hobs_r Hobservers"). }
  iMod ("Hclose" with "[Hrln Hrauth Hmaxn Hwl Hcore Hsession Hobs]") as "_".
  { iExists (RLocked n). iFrame "Hrln". iEval (cbn [tie_body]). iFrame "Hrauth Hmaxn Hwl".
    iExists m, deleted. iFrame "Hobs". rewrite /tie_store.
    iExists c0, h, state, ds. iFrame "Hcore Hsession". done. }
  iModIntro. wp_auto. iApply "HΦ". iFrame "Htok Hmaxtok".
Qed.

End store_wp_private.
