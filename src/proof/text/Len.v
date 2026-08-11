(** [wp_Text__Len]: the [Text] handle's visible-length read, a concurrent read
    under the store's RWMutex read lock (issues #22 / #125). Shares [is_Text]
    etc. via [text/heap.v].

    The postcondition is a SNAPSHOT (issue #125): the returned counter is the
    visible length of some tombstone-tagged array [marr] that satisfies the
    document invariant and contains everything the handle already knows
    ([L], the handle's grow-only lower bound). A caller whose knowledge came
    from elsewhere (an applyUpdate certificate) uses the history form
    [wp_Text__Len_hist] below instead. The bound is at the ITEM-SET level: a
    tombstoned item is in [marr] but not counted. The length comes back as
    the [W64] image of the model count: the heap counter is a [w64] and
    nothing bounds a document's size, so the spec does not invent a no-wrap
    fact. *)
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
From New.proof.store Require Import store.
From New.proof.sync_proof Require Import mutex.
From iris.algebra Require Import auth gmap gset.
From iris.algebra.lib Require Import dfrac_agree.
From stdpp Require Import sorting.
From New.proof.text Require Import heap.

(* iris.algebra / stdpp.sorting push [nat_scope], retuning the default [<] / [≤];
   the verified word-arithmetic proofs write [Z] comparisons unannotated, so
   restore [Z_scope] as the default. *)
Local Open Scope Z_scope.

Section text.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.
(** Store lock = a [sync.RWMutex] (write path here, via [wp_Store__wlock] /
    [wp_Store__wunlock]); the per-text item set lives in a grow-only auth
    (the same RA as [store/store], used by [is_type_lb]). *)
Context {sync_pkg : sync.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.
Context {seq_inG : inG Σ (authR (gmapUR loc (gsetUR (YjsItem A))))}.
Context {acc_inG : inG Σ (authR (gsetUR YjsId))}.
(* [is_Store]'s reader-count accounting ties the readers' share to the store's
   [types] map via a [dfrac_agree]; threaded here so [is_Text]/[is_Store] uses
   in this file (Insert/Delete/Len) can discharge the instance. *)
Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO (gmap loc type_state)))}.

(* The ghost op-history types at the document content type; type names are Go
   strings (issue #49). *)
Local Notation P := go_string.
Local Notation TId := (TypeId P).
Local Notation Op := (TId * @YjsOperation A)%type.
Local Notation Ev := (@Event Op).
Local Notation DocModel := (gmap TId (list (YjsItem A))).

(** [Text.Len]: a CONCURRENT read (issue #22). Takes the RWMutex read lock,
    reads the type's visible length off its DLL through a fractional
    [store_inv_ro] share (so it runs alongside other readers), then releases.
    The read capability [own_read_cap] (one reader slot) is threaded and
    returned; [is_Text] is preserved. Functional since issue #125: the length
    counts the visible items of a snapshot [marr] bounded below by [L]. *)
Lemma wp_Text__Len (t : loc) (γs : store_names) (γh : history_names) (name : P)
    (L : list (YjsItem A)) :
  {{{ is_pkg_init yjs ∗ is_Text t γs γh name L ∗ own_read_cap γs }}}
    t @! (go.PointerType yjs.Text) @! "Len" #()
  {{{ (n : w64) (marr : list (YjsItem A * bool)), RET #n;
      is_Text t γs γh name L ∗ own_read_cap γs ∗
      ⌜n = W64 (length (visible_items marr))⌝ ∗
      ⌜list_to_set L ⊆ (list_to_set marr.*1 : gset (YjsItem A))⌝ ∗
      ⌜YjsArrInvariant marr.*1⌝ }}}.
Proof.
  wp_start as "(Hpre & Hcap)". iNamed "Hpre".
  iDestruct "His_store" as "#His_store".
  wp_auto. subst s_loc.
  wp_apply (wp_Store__rlock with "[$His_store $Hcap]"). iIntros (types) "[Hrlo Hro]".
  iNamed "Hro".
  iDestruct (auth_gmap_gset_lookup_dq with "Hseq His_lb") as %(S' & HmS & HLsub).
  rewrite lookup_fmap in HmS. apply fmap_Some in HmS as (ts & Htsp & ->).
  iDestruct (big_sepM_lookup_acc _ _ _ _ Htsp with "Htypes") as "[Hbody Hclose]".
  iDestruct "Hbody" as "(Htext & %Hinvarr)".
  iDestruct "Htext" as (yt0 tl0) "(Hparent & Hdll & %Hlen & %Hrepr & %Hcpar)".
  subst parent.
  wp_auto.
  iDestruct ("Hclose" with "[Hparent Hdll]") as "Htypes".
  { iSplitL "Hparent Hdll"; [ iExists yt0, tl0; iFrame "Hparent Hdll"; iPureIntro; done | iPureIntro; exact Hinvarr ]. }
  wp_apply (wp_Store__runlock with "[$His_store $Hrlo Hseq Htypes]").
  { iFrame "Hseq Htypes". }
  iIntros "Hcap".
  wp_auto.
  have Hfst : (cells_model (ty_cells ts)).*1 = ty_arr ts.
  { rewrite cells_model_fst. rewrite /cells_repr in Hrepr. rewrite -Hrepr //. }
  iApply ("HΦ" $! _ (cells_model (ty_cells ts))).
  iSplitR "Hcap"; last first.
  { iFrame "Hcap". iPureIntro. split_and!.
    - rewrite Hlen num_visible_model //.
    - rewrite Hfst. exact HLsub.
    - rewrite Hfst. exact Hinvarr. }
  iExists tv, tv.(yjs.Text.store'), tv.(yjs.Text.inner').
  iFrame "Ht His_store His_hist Hbind His_lb".
  iPureIntro. split_and!; [reflexivity | reflexivity | exact Hsorted].
Qed.

(** [Text.Len], history-certificate form (issue #125): like
    [wp_Text__String_hist], the caller brings a prefix certificate of this
    replica's op history and the counted snapshot contains one item per
    delivered insert of the prefix targeting this root. *)
Lemma wp_Text__Len_hist (t : loc) (γs : store_names) (γh : history_names)
    (c : ClientId) (name : P) (L : list (YjsItem A)) (h0 : list Ev) :
  {{{ is_pkg_init yjs ∗ is_Text t γs γh name L ∗
      is_store_client γs c ∗ is_history_lb γh c h0 ∗ own_read_cap γs }}}
    t @! (go.PointerType yjs.Text) @! "Len" #()
  {{{ (n : w64) (marr : list (YjsItem A * bool)), RET #n;
      is_Text t γs γh name L ∗ own_read_cap γs ∗
      ⌜n = W64 (length (visible_items marr))⌝ ∗
      ⌜list_to_set L ⊆ (list_to_set marr.*1 : gset (YjsItem A))⌝ ∗
      ⌜YjsArrInvariant marr.*1⌝ ∗
      ⌜∀ input : IntegrateInput (A := A),
         (RootId name, OpInsert input) ∈ delivered_ops h0 ->
         ∃ it, item_id it = in_id input ∧ it ∈ marr.*1⌝ }}}.
Proof.
  wp_start as "(Hpre & #Hpin & #Hlb & Hcap)". iNamed "Hpre".
  iDestruct "His_store" as "#His_store".
  wp_auto. subst s_loc.
  wp_apply (wp_Store__rlock_hist _ _ _ c h0 name _ with "[$His_store $Hcap $Hpin $Hlb $Hbind]").
  iIntros (types) "(Hrlo & Hro & %Hfact)".
  iNamed "Hro".
  iDestruct (auth_gmap_gset_lookup_dq with "Hseq His_lb") as %(S' & HmS & HLsub).
  rewrite lookup_fmap in HmS. apply fmap_Some in HmS as (ts & Htsp & ->).
  iDestruct (big_sepM_lookup_acc _ _ _ _ Htsp with "Htypes") as "[Hbody Hclose]".
  iDestruct "Hbody" as "(Htext & %Hinvarr)".
  iDestruct "Htext" as (yt0 tl0) "(Hparent & Hdll & %Hlen & %Hrepr & %Hcpar)".
  subst parent.
  wp_auto.
  iDestruct ("Hclose" with "[Hparent Hdll]") as "Htypes".
  { iSplitL "Hparent Hdll"; [ iExists yt0, tl0; iFrame "Hparent Hdll"; iPureIntro; done | iPureIntro; exact Hinvarr ]. }
  wp_apply (wp_Store__runlock with "[$His_store $Hrlo Hseq Htypes]").
  { iFrame "Hseq Htypes". }
  iIntros "Hcap".
  wp_auto.
  have Hfst : (cells_model (ty_cells ts)).*1 = ty_arr ts.
  { rewrite cells_model_fst. rewrite /cells_repr in Hrepr. rewrite -Hrepr //. }
  iApply ("HΦ" $! _ (cells_model (ty_cells ts))).
  iSplitR "Hcap"; last first.
  { iFrame "Hcap". iPureIntro. split_and!.
    - rewrite Hlen num_visible_model //.
    - rewrite Hfst. exact HLsub.
    - rewrite Hfst. exact Hinvarr.
    - move=> input Hin.
      destruct (Hfact input Hin) as (ts' & it & Hts' & Hitid & Hitmem).
      rewrite Htsp in Hts'. injection Hts' as <-.
      exists it. split; [exact Hitid | rewrite Hfst //]. }
  iExists tv, tv.(yjs.Text.store'), tv.(yjs.Text.inner').
  iFrame "Ht His_store His_hist Hbind His_lb".
  iPureIntro. split_and!; [reflexivity | reflexivity | exact Hsorted].
Qed.

End text.
