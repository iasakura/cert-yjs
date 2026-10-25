(** [wp_Text__CodeUnits]: the [Text] handle's visible-text read, as UTF-16
    code units, a concurrent read under the store's RWMutex read lock
    (issues #22 / #125). Shares [is_Text] etc. via [text/heap.v].

    The postcondition is a SNAPSHOT: the returned slice, fresh and the
    caller's own, holds exactly the
    visible code units of some tombstone-tagged array [model] that satisfies
    the document invariant and contains everything the handle already knows
    ([L], the handle's grow-only lower bound), and that is EXACTLY the root's
    document in the replay of a certified history prefix [h] extending the
    caller's certificate [h0] ([is_text_state], issue #239; that [model]
    holds one item per delivered insert of [h0] targeting this root follows,
    [text_state_history_reflected]). The bound is at the ITEM-SET
    level: a tombstoned item is in [model] but not in the string, so "the
    characters are visible" needs a no-delete side condition on top; the
    set-level statement is unconditional. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core.
From New.proof Require Import algebra.
From New.proof Require Import prelude.
From New.proof Require Import history.
From New.proof.id Require Import id.
From New.proof.item Require Import item.
From New.proof.ytype Require Import ytype.
From New.proof.delta Require Import delta.
From New.proof.store Require Import store.
From New.proof.sync_proof Require Import mutex.
From iris.algebra Require Import auth gmap gset.
From iris.algebra.lib Require Import dfrac_agree.
From stdpp Require Import sorting.
From New.proof.text Require Import model heap.

(* iris.algebra / stdpp.sorting push [nat_scope], retuning the default [<] / [≤];
   the verified word-arithmetic proofs write [Z] comparisons unannotated, so
   restore [Z_scope] as the default. *)
Local Open Scope Z_scope.

Section text.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.
Context {sync_pkg : sync.Assumptions}.

Set Default Proof Using "Type*".

Notation A := (list w16).
Context {seq_inG : inG Σ (authR (gmapUR loc (gsetUR (YjsItem A))))}.
Context {acc_inG : inG Σ (authR (gsetUR YjsId))}.
Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO store_state))}.
(* the observers' tokens and registrations (issue #198 Part II), as [store/heap] *)
Context {observed_inG : ghost_varG Σ (list (YjsItem A * bool))}.
Context {observers_inG : inG Σ (authR (gsetUR (gname * go_string)))}.
Context {observers_agree_inG : inG Σ (dfrac_agreeR (leibnizO registered_entries))}.

Local Notation P := go_string.
Local Notation TId := (TypeId P).
Local Notation Op := (TId * @YjsOperation A)%type.
Local Notation Ev := (@Event Op).
Local Notation DocModel := (gmap TId (list (YjsItem A))).


(** [Text.CodeUnits]: a CONCURRENT functional read (issue #125). Takes the
    RWMutex read lock, walks the type's DLL through a fractional
    share of [own_store] ([wp_yType__Text]), then releases. The caller brings
    a prefix certificate [is_history_lb γh c h0] of THIS replica's op history
    (with the client pin identifying it), and gets back an exact certificate
    of the snapshot at a history prefix extending [h0] (a caller with no such
    knowledge passes [h0 = []]). This is the read
    guarantee in the network stack's own currency: whoever observed the
    history grow (an applyUpdate postcondition, a server receipt, a
    sync-protocol certificate) can replay that knowledge against a concurrent
    read. *)
Lemma wp_Text__CodeUnits (t : loc) (γs : store_names) (γh : history_names)
    (c : ClientId) (name : P) (L : list (YjsItem A)) (deleted_ids : gset YjsId)
    (h0 : list Ev) :
  {{{ is_pkg_init yjs ∗ is_Text t γs γh name L deleted_ids ∗
      is_store_client γs c ∗ is_history_lb γh c h0 ∗ own_read_cap γs }}}
    t @! (go.PointerType yjs.Text) @! "CodeUnits" #()
  {{{ (sl : slice.t) (model : list (YjsItem A * bool)), RET #sl;
      is_Text t γs γh name L deleted_ids ∗ own_read_cap γs ∗
      sl ↦* visible_string model ∗ own_slice_cap w16 sl (DfracOwn 1) ∗
      ⌜text_snapshot L model⌝ ∗
      (∃ h : list Ev, ⌜h0 `prefix_of` h⌝ ∗ is_text_state γh c h name model) ∗
      ⌜visible_excludes deleted_ids model⌝ }}}.
Proof.
  wp_start as "(Hpre & #Hpin & #Hlb & Hcap)". iNamed "Hpre".
  iDestruct "His_store" as "#His_store".
  wp_auto. subst s_loc. subst parent.
  wp_apply (wp_Store__rlock _ _ _ c h0 with "[$His_store $Hcap $Hpin $Hlb]").
  iIntros (state ds m0) "(Hrlo & Hstore & %Hregmodel & (%h & %Hpref & #Hreplay))".
  wp_auto.
  iNamed "Hstore". iNamed "Hcore".
  (* this handle's root, in the state the lock handed out: the registry
     authority inside the share answers the handle's binding *)
  iDestruct (ghost_map_lookup with "HtypesAuth Hbind") as %Hbindlk.
  (* the handle's certificate against the shared authority: the ids it knows
     deleted are in the store's delete set, hence tombstoned in this pool *)
  iDestruct (auth_gset_frag_sub_dq with "Hdelete_set_auth Hdeleted_lb") as %Hdelsub.
  iDestruct (auth_gmap_gset_lookup_dq with "Hseq His_lb") as %(S' & HmS & HLsub).
  rewrite lookup_fmap in HmS. apply fmap_Some in HmS as (tm & Htmp & ->).
  iDestruct (own_store_state_aligned with "Hstate") as %Haligned.
  iDestruct (own_store_state_arr_inv with "Hstate") as %Harrinv.
  have [ls Hls] : ∃ ls, ss_locs state !! tv.(yjs.Text.inner') = Some ls.
  { apply elem_of_dom. rewrite (proj1 Haligned). apply elem_of_dom. by exists tm. }
  have Harr : tm_arr tm = runs_flatten (tm_runs tm) := eq_refl.
  (* borrow the type's run view at the reader's fraction and run the walk *)
  iDestruct (own_store_state_ytype_acc _ rwmutex_guard.rfrac state
               tv.(yjs.Text.inner') ls tm Hls Htmp with "Hstate") as "[Hyt Hytback]".
  wp_apply (wp_yType__Text (tv.(yjs.Text.inner')) (DfracOwn rwmutex_guard.rfrac) ls tm with "[$Hyt]").
  iIntros (sl) "(Hyt & Hsl & Hslcap)".
  iDestruct ("Hytback" with "Hyt") as "Hstate".
  wp_auto.
  (* the reader's share goes back whole *)
  iAssert (own_store (store_of_ref tv.(yjs.Text.store')) γs γh rwmutex_guard.rfrac
             state ds m0 (pool_tombstoned (ss_pool state)))
    with "[Hstate Hseq HtypesAuth Hdelete_set_auth Hstate_agree Hobservers]" as "Hstore".
  { rewrite /own_store /own_store_core.
    iFrame "Hstate Hclientpin Hseq HtypesAuth Hbinds Hdelete_set_auth Hstate_agree Hobservers".
    iPureIntro. exact Hds_tomb. }
  wp_apply (wp_Store__runlock with "[$His_store $Hrlo $Hstore]").
  iIntros "Hcap".
  wp_auto.
  have Hfst : (runs_model (tm_runs tm)).*1 = tm_arr tm.
  { rewrite runs_model_fst -Harr //. }
  (* what the read now says about the handle's deleted ids: each such char of
     the snapshot carries the tombstone bit, so the visible chars exclude it *)
  have Hexcl : visible_excludes deleted_ids (runs_model (tm_runs tm)).
  { apply visible_excludes_of_bits => x b Hin Hid.
    destruct (runs_model_elem_of _ _ _ Hin) as (r & Hr & Hx & ->).
    have Hrall : r ∈ all_runs (ss_pool state).
    { apply elem_of_all_runs. exists tv.(yjs.Text.inner'), tm.
      split; [exact Htmp | exact Hr]. }
    exact (Hds_tomb r Hrall x Hx (Hdelsub (item_id x) Hid)). }
  (* the walked list is the root's document in [m0], which is the replay of
     the history [h] the read lock certified *)
  have Hroot : (runs_model (tm_runs tm)).*1 = doc_model_get m0 (RootId name).
  { rewrite Hfst. symmetry.
    exact (proj1 Hregmodel name tv.(yjs.Text.inner') tm Hbindlk Htmp). }
  iApply ("HΦ" $! sl (runs_model (tm_runs tm))).
  iSplitR "Hcap Hsl Hslcap"; last first.
  { iFrame "Hcap Hsl Hslcap".
    iSplitR.
    { iPureIntro. split; rewrite Hfst; [exact HLsub | exact (Harrinv _ _ Htmp)]. }
    iSplitR; last (iPureIntro; exact Hexcl).
    iExists h. iSplitR; first (iPureIntro; exact Hpref).
    rewrite /is_text_state. iExists m0. iFrame "Hreplay". iPureIntro. exact Hroot. }
  iExists tv, tv.(yjs.Text.store'), tv.(yjs.Text.inner'), deleted_items.
  iFrame "Ht His_store His_hist Hbind His_lb Hdeleted_lb Hdeleted_items".
  iPureIntro. split_and!; [reflexivity | reflexivity | exact Hdeleted_known | exact Hsorted].
Qed.

End text.
