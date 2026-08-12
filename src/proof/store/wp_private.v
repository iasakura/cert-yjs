(** Specs of the [store]'s internal lock layer: [wlock] / [wunlock] trade the
    write lock for the lock body [store_inv_excl], [rlock] / [runlock] trade a
    reader slot for a fractional [store_inv_ro] share (issue #22), and
    [rlock_hist] is [rlock] with a history certificate converted at the
    linearization point (issue #125). Not part of the store's Go API: every
    method proof of the store and of the [Text] handle enters through these,
    so they sit next to the invariant rather than inside any one method
    file. *)
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
    type-loc item set) sits in [store_inv]; a persistent fragment
    [◯ {[parent := S]}] held by [is_Text] gives, when combined with [● m],
    gmap-inclusion [{[parent := S]} ≼ m] = [∃ S', m !! parent = Some S' ∧ S ⊆ S']
    — i.e. it BOTH witnesses [parent ∈ dom m] (= the type is registered) AND
    bounds [S ⊆ S'] (the lower bound). Insert only adds items (delete just flips a
    flag), so each item set grows monotonically under [⊆]; a recorded lower bound
    stays valid forever.

    We track full ITEMS, not just ids: a membership bound [x ∈ S ⊆ ty_arr ts]
    then pins [x] to a *genuine* document item (same structure, not merely the
    same id), which is what lets [Text.Insert] expose the post as a real
    [sublist L L'] rather than only an id-set inclusion. [gset (YjsItem A)] needs
    [Countable (YjsItem A)] (derived in [prelude] via [gen_tree]). Order is not
    tracked in the ghost (recoverable from origins / from [YjsArrInvariant]). *)

Notation seqUR := (authR (gmapUR loc (gsetUR (YjsItem A)))).

Context {seq_inG : inG Σ seqUR}.

(** Accepted-id RA (this branch): a GROW-ONLY set of ids the store has
    "accepted", i.e. promised not to lose. [authR (gsetUR YjsId)] — the
    authority [● acc] sits in [store_inv], and a persistent lower-bound
    fragment [◯ {[i]}] (gset elements are core-id) is the [is_accepted]
    receipt every applyUpdate hands back per input. The store invariant ties
    [acc ⊆ delivered_ids h ∪ pending ids], so an accepted id is forever
    delivered-or-buffered: this is what makes "no input is lost" an
    ENFORCEABLE guarantee (a discarding implementation could not mint the
    receipt), unlike a bare existential over the pending list. *)

Notation accUR := (authR (gsetUR YjsId)).

Context {acc_inG : inG Σ accUR}.

Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO (gmap loc type_state)))}.

(* The [∷] (named) wrapper blocks [Timeless] TC resolution; unfold it (as
   [New.proof.sync_proof.rwmutex] does) so the [Timeless] instances below go
   through the named conjuncts of [own_item_map] / [store_inv]. *)

#[local] Hint Extern 100 (Timeless (?n ∷ ?P)) =>
  (change (n ∷ P) with P) : typeclass_instances.

(* [rwmutex_inhabited] / [tie_body_timeless] are [#[local]] in [store/heap];
   opening the tie invariant here needs them again. *)
#[local] Instance rwmutex_inhabited : Inhabited rwmutex := populate Locked.

#[local] Instance tie_body_timeless s_loc γs γh st : Timeless (tie_body s_loc γs γh st).
Proof.
  destruct st; rewrite /tie_body;
    repeat first [ apply sep_timeless | apply exist_timeless; intros ? ]; apply _.
Qed.


(** Write-lock acquire. The write [Lock] linearizes at [RLocked 0] (fraction 1),
    where [store_inv_bridge] reassembles the whole [store_inv]; the invariant is
    left holding [Locked] (which keeps the [types_frag] for the next transition).
    Signature unchanged from the Phase-1 wrapper, so Insert/Delete are untouched. *)
Lemma wp_Store__wlock (s_loc : loc) (γs : store_names) (γh : history_names) :
  {{{ is_pkg_init sync ∗ is_Store s_loc γs γh }}}
    (s_loc .[(yjs.store.t), "mu"]) @! (go.PointerType sync.RWMutex) @! "Lock" #()
  {{{ RET #(); own_wlock γs ∗ store_inv s_loc γs γh }}}.
Proof.
  wp_start_folded as "His". iNamed "His".
  wp_apply (rwmutex.wp_RWMutex__Lock with "[$Hrw]").
  iInv "Htie" as "Hi" "Hclose".
  iDestruct "Hi" as (st) "[>Hown Hbody]".
  iFrame "Hown". iApply fupd_mask_intro; first solve_ndisj. iIntros "Hmask".
  iIntros "%Hst Hlocked". subst st.
  iDestruct "Hbody" as ">Hbody". iEval (cbn [tie_body]) in "Hbody".
  iDestruct "Hbody" as "(Hrauth & Htoks0 & Hwl & Hrest)".
  iDestruct "Hrest" as (client k items_mref types_mref deletedSetVal pend_sl pdel_sl types bind h m pend pdel) "(Hfrag & Hexcl & Hro)".
  rewrite frac_of_0.
  iMod "Hmask" as "_".
  iMod ("Hclose" with "[Hlocked Hrauth Hfrag]") as "_".
  { iExists Locked. iFrame "Hlocked". iExists types. iFrame "Hrauth Hfrag". }
  iModIntro. iApply "HΦ". iFrame "Hwl".
  iApply store_inv_bridge. iExists client, k, items_mref, types_mref, deletedSetVal, pend_sl, pdel_sl, types, bind, h, m, pend, pdel. iFrame "Hexcl Hro".
Qed.


(** Write-lock release. Consumes [own_wlock] and returns [store_inv]; updates the
    lock invariant's [types_frag] to the (possibly changed) current [types] read
    off the returned [store_inv] via the bridge; this is what lets the write
    proofs stay ignorant of the reader accounting. The "invariant is in [RLocked]"
    case (unlock without the lock) is impossible: the [own_wlock] clash. *)
Lemma wp_Store__wunlock (s_loc : loc) (γs : store_names) (γh : history_names) :
  {{{ is_pkg_init sync ∗ is_Store s_loc γs γh ∗ own_wlock γs ∗ ▷ store_inv s_loc γs γh }}}
    (s_loc .[(yjs.store.t), "mu"]) @! (go.PointerType sync.RWMutex) @! "Unlock" #()
  {{{ RET #(); True }}}.
Proof.
  wp_start_folded as "(His & Hwl & HR)". iNamed "His".
  wp_apply (rwmutex.wp_RWMutex__Unlock with "[$Hrw]").
  iInv "Htie" as "Hi" "Hclose".
  iDestruct "Hi" as (st) "[>Hown Hbody]".
  destruct st.
  - iEval (cbn [tie_body]) in "Hbody".
    iDestruct "Hbody" as "(_ & _ & >Hwl2 & _)".
    iDestruct (ghost_var_valid_2 with "Hwl Hwl2") as %[Hbad _].
    exfalso. by apply (Qp.not_add_le_l 1 1).
  - iEval (cbn [tie_body]) in "Hbody".
    iDestruct "Hbody" as (types_old) "(>Hrauth & >Hfrag)".
    iFrame "Hown". iApply fupd_mask_intro; first solve_ndisj. iIntros "Hmask".
    iIntros "Hrl0".
    iMod "Hmask" as "_".
    iMod (own_toks_0 γs.(sn_rmax)) as "Htoks0".
    iEval (rewrite store_inv_bridge) in "HR".
    iDestruct "HR" as (client k items_mref types_mref deletedSetVal pend_sl pdel_sl types' bind h m pend pdel) "[Hexcl Hro]".
    iMod (own_update _ _ (to_frac_agree 1 (types' : leibnizO _)) with "Hfrag") as "Hfrag".
    { apply cmra_update_exclusive. done. }
    iMod ("Hclose" with "[Hrl0 Hrauth Htoks0 Hwl Hfrag Hexcl Hro]") as "_".
    { iExists (RLocked 0). iFrame "Hrl0". iEval (cbn [tie_body]). iFrame "Hrauth Htoks0 Hwl".
      iExists client, k, items_mref, types_mref, deletedSetVal, pend_sl, pdel_sl, types', bind, h, m, pend, pdel.
      rewrite frac_of_0. iFrame "Hfrag Hexcl Hro". }
    iModIntro. by iApply "HΦ".
Qed.


(** Read-lock acquire: peels one [rfrac] share of [store_inv_ro] off the lock
    invariant (bumping the reader count), returning the reader's slot witness
    [own_read_locked] and that share for the specific current [types]. *)
Lemma wp_Store__rlock (s_loc : loc) (γs : store_names) (γh : history_names) :
  {{{ is_pkg_init sync ∗ is_Store s_loc γs γh ∗ own_read_cap γs }}}
    (s_loc .[(yjs.store.t), "mu"]) @! (go.PointerType sync.RWMutex) @! "RLock" #()
  {{{ types, RET #(); own_read_locked γs types ∗ store_inv_ro γs types rwmutex_guard.rfrac }}}.
Proof.
  wp_start_folded as "(His & Hcap)". iNamed "His".
  iDestruct "Hcap" as "[Htok Hmaxtok]".
  wp_apply (rwmutex.wp_RWMutex__RLock with "[$Hrw $Htok]").
  iInv "Htie" as "Hi" "Hclose".
  iDestruct "Hi" as (st) "[>Hown Hbody]".
  iFrame "Hown". iApply fupd_mask_intro; first solve_ndisj. iIntros "Hmask".
  iIntros (n) "%Hst Hrl". subst st.
  iDestruct "Hbody" as ">Hbody". iEval (cbn [tie_body]) in "Hbody".
  iDestruct "Hbody" as "(Hrauth & Hmaxn & Hwl & Hrest)".
  iDestruct "Hrest" as (client k items_mref types_mref deletedSetVal pend_sl pdel_sl types bind h m pend pdel) "(Hfrag & Hexcl & Hro)".
  iCombine "Hmaxn Hmaxtok" as "Hmaxn1".
  iCombine "Hmax Hmaxn1" gives %Hbound.
  iMod (own_tok_auth_S with "Hrauth") as "[Hrauth Hrtok]".
  assert (Z.of_nat n < rwmutex.actualMaxReaders)%Z as Hlt by (rewrite rwmutex.actualMaxReaders_unseal in Hbound |- *; lia).
  rewrite (frac_of_split n Hlt).
  iDestruct (tf_split with "Hfrag") as "[Hfrag_r Hfrag_i]".
  iDestruct (store_inv_ro_fractional γs types with "Hro") as "[Hro_r Hro_i]".
  iMod "Hmask" as "_".
  iMod ("Hclose" with "[Hrl Hrauth Hmaxn1 Hwl Hfrag_i Hexcl Hro_i]") as "_".
  { iExists (RLocked (S n)). iFrame "Hrl". iEval (cbn [tie_body]).
    replace (S n) with (n + 1)%nat by lia.
    iFrame "Hrauth Hmaxn1 Hwl".
    iExists client, k, items_mref, types_mref, deletedSetVal, pend_sl, pdel_sl, types, bind, h, m, pend, pdel.
    iFrame "Hfrag_i Hexcl Hro_i". }
  iModIntro. iApply ("HΦ" $! types). iFrame "Hrtok Hfrag_r Hro_r".
Qed.


(** [wp_Store__rlock], history-certificate form (issue #125): the reader
    brings a prefix certificate of THIS replica's op history (plus the client
    pin identifying it) and a root binding; the read lock's linearization
    point is the one moment the reader sees the exclusive slice, and
    [store_inv_excl_hist_root] converts there: the [types] snapshot handed
    out already contains, at the bound root, one item per delivered insert
    of the certified prefix. *)
Lemma wp_Store__rlock_hist (s_loc : loc) (γs : store_names) (γh : history_names)
    (c : ClientId) (h0 : list Ev) (name : P) (parent : loc) :
  {{{ is_pkg_init sync ∗ is_Store s_loc γs γh ∗ own_read_cap γs ∗
      is_store_client γs c ∗ is_history_lb γh c h0 ∗
      is_type_binding γs.(sn_types) name parent }}}
    (s_loc .[(yjs.store.t), "mu"]) @! (go.PointerType sync.RWMutex) @! "RLock" #()
  {{{ types, RET #();
      own_read_locked γs types ∗ store_inv_ro γs types rwmutex_guard.rfrac ∗
      ⌜∀ input : IntegrateInput (A := A),
         (RootId name, OpInsert input) ∈ delivered_ops h0 ->
         ∃ ts it, types !! parent = Some ts ∧ item_id it = in_id input ∧ it ∈ ty_arr ts⌝ }}}.
Proof.
  wp_start_folded as "(His & Hcap & #Hpin & #Hlb & #Hbind)". iNamed "His".
  iDestruct "Hcap" as "[Htok Hmaxtok]".
  wp_apply (rwmutex.wp_RWMutex__RLock with "[$Hrw $Htok]").
  iInv "Htie" as "Hi" "Hclose".
  iDestruct "Hi" as (st) "[>Hown Hbody]".
  iFrame "Hown". iApply fupd_mask_intro; first solve_ndisj. iIntros "Hmask".
  iIntros (n) "%Hst Hrl". subst st.
  iDestruct "Hbody" as ">Hbody". iEval (cbn [tie_body]) in "Hbody".
  iDestruct "Hbody" as "(Hrauth & Hmaxn & Hwl & Hrest)".
  iDestruct "Hrest" as (client k items_mref types_mref deletedSetVal pend_sl pdel_sl types bind h m pend pdel) "(Hfrag & Hexcl & Hro)".
  (* the conversion, at the one moment the exclusive slice is visible *)
  iDestruct (store_inv_excl_hist_root with "Hexcl Hpin Hlb Hbind") as "[Hexcl %Hfact]".
  iCombine "Hmaxn Hmaxtok" as "Hmaxn1".
  iCombine "Hmax Hmaxn1" gives %Hbound.
  iMod (own_tok_auth_S with "Hrauth") as "[Hrauth Hrtok]".
  assert (Z.of_nat n < rwmutex.actualMaxReaders)%Z as Hlt by (rewrite rwmutex.actualMaxReaders_unseal in Hbound |- *; lia).
  rewrite (frac_of_split n Hlt).
  iDestruct (tf_split with "Hfrag") as "[Hfrag_r Hfrag_i]".
  iDestruct (store_inv_ro_fractional γs types with "Hro") as "[Hro_r Hro_i]".
  iMod "Hmask" as "_".
  iMod ("Hclose" with "[Hrl Hrauth Hmaxn1 Hwl Hfrag_i Hexcl Hro_i]") as "_".
  { iExists (RLocked (S n)). iFrame "Hrl". iEval (cbn [tie_body]).
    replace (S n) with (n + 1)%nat by lia.
    iFrame "Hrauth Hmaxn1 Hwl".
    iExists client, k, items_mref, types_mref, deletedSetVal, pend_sl, pdel_sl, types, bind, h, m, pend, pdel.
    iFrame "Hfrag_i Hexcl Hro_i". }
  iModIntro. iApply ("HΦ" $! types). iFrame "Hrtok Hfrag_r Hro_r".
  iPureIntro. exact Hfact.
Qed.


(** Read-lock release: returns the reader's [rfrac] share (proving via [tf_agree]
    that the store's [types] is unchanged since the [RLock], so the share
    recombines) and the reader slot; returns [own_read_cap]. *)
Lemma wp_Store__runlock (s_loc : loc) (γs : store_names) (γh : history_names) types_r :
  {{{ is_pkg_init sync ∗ is_Store s_loc γs γh ∗ own_read_locked γs types_r ∗
        store_inv_ro γs types_r rwmutex_guard.rfrac }}}
    (s_loc .[(yjs.store.t), "mu"]) @! (go.PointerType sync.RWMutex) @! "RUnlock" #()
  {{{ RET #(); own_read_cap γs }}}.
Proof.
  wp_start_folded as "(His & Hrlo & Hro_r)". iNamed "His".
  iDestruct "Hrlo" as "[Hrtok Hfrag_r]".
  wp_apply (rwmutex.wp_RWMutex__RUnlock with "[$Hrw]").
  iInv "Htie" as "Hi" "Hclose".
  iDestruct "Hi" as (st) "[>Hown Hbody]".
  destruct st as [nr | ].
  2:{ iEval (cbn [tie_body]) in "Hbody". iDestruct "Hbody" as (types0) "(>Hrauth & _)".
      iCombine "Hrauth Hrtok" gives %Hbad. exfalso. lia. }
  destruct nr as [ | n ].
  { iEval (cbn [tie_body]) in "Hbody". iDestruct "Hbody" as "(>Hrauth & _)".
    iCombine "Hrauth Hrtok" gives %Hbad. exfalso. lia. }
  iDestruct "Hbody" as ">Hbody". iEval (cbn [tie_body]) in "Hbody".
  iDestruct "Hbody" as "(Hrauth & Hmaxsn & Hwl & Hrest)".
  iDestruct "Hrest" as (client k items_mref types_mref deletedSetVal pend_sl pdel_sl types_i bind h m pend pdel) "(Hfrag_i & Hexcl & Hro_i)".
  iDestruct (tf_agree with "Hfrag_r Hfrag_i") as %->.
  iCombine "Hmax Hmaxsn" gives %Hbound.
  assert (Z.of_nat n < rwmutex.actualMaxReaders)%Z as Hlt by (rewrite rwmutex.actualMaxReaders_unseal in Hbound |- *; lia).
  iExists n. iFrame "Hown".
  iApply fupd_mask_intro; first solve_ndisj. iIntros "Hmask".
  iIntros "[Hrln Htok]".
  iMod "Hmask" as "_".
  iMod (own_tok_auth_delete_S with "Hrauth Hrtok") as "Hrauth".
  iEval (rewrite -Nat.add_1_r) in "Hmaxsn".
  iDestruct (own_toks_add_1 1 n γs.(sn_rmax) with "Hmaxsn") as "[Hmaxn Hmaxtok]".
  iDestruct (tf_split γs rwmutex_guard.rfrac (frac_of (S n)) types_i with "[$Hfrag_r $Hfrag_i]") as "Hfrag".
  iDestruct (store_inv_ro_fractional γs types_i rwmutex_guard.rfrac (frac_of (S n)) with "[$Hro_r $Hro_i]") as "Hro".
  rewrite -(frac_of_split n Hlt).
  iMod ("Hclose" with "[Hrln Hrauth Hmaxn Hwl Hfrag Hexcl Hro]") as "_".
  { iExists (RLocked n). iFrame "Hrln". iEval (cbn [tie_body]). iFrame "Hrauth Hmaxn Hwl".
    iExists client, k, items_mref, types_mref, deletedSetVal, pend_sl, pdel_sl, types_i, bind, h, m, pend, pdel.
    iFrame "Hfrag Hexcl Hro". }
  iModIntro. iApply "HΦ". iFrame "Htok Hmaxtok".
Qed.

End store_wp_private.
