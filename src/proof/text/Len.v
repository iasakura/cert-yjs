(** [wp_Text__Len]: the [Text] handle's visible-length read, a concurrent read
    under the store's RWMutex read lock (issues #22 / #125). Shares [is_Text]
    etc. via [text/heap.v].

    The postcondition is a SNAPSHOT (issue #125): the returned counter is the
    visible length of some tombstone-tagged array [model] that satisfies the
    document invariant and contains everything the handle already knows
    ([L], the handle's grow-only lower bound), and that contains one item per
    delivered insert of the caller's history certificate [is_history_lb]
    targeting this root. The bound is at the ITEM-SET level: a
    tombstoned item is in [model] but not counted. The length comes back as
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
From New.proof.text Require Import model heap.

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
Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO addressed_pool))}.

(* The ghost op-history types at the document content type; type names are Go
   strings (issue #49). *)
Local Notation P := go_string.
Local Notation TId := (TypeId P).
Local Notation Op := (TId * @YjsOperation A)%type.
Local Notation Ev := (@Event Op).
Local Notation DocModel := (gmap TId (list (YjsItem A))).


(** [Text.Len]: a CONCURRENT read (issues #22 / #125). Takes the RWMutex
    read lock, reads the type's visible length off its DLL through a
    fractional [store_inv_ro] share (so it runs alongside other readers),
    then releases. The read capability [own_read_cap] (one reader slot) is
    threaded and returned; [is_Text] is preserved. Like [wp_Text__String],
    the caller brings a prefix certificate of this replica's op history and
    the counted snapshot contains one item per delivered insert of the prefix
    targeting this root (a caller with no such knowledge passes [h0 = []]). *)
Lemma wp_Text__Len (t : loc) (γs : store_names) (γh : history_names)
    (c : ClientId) (name : P) (L : list (YjsItem A)) (h0 : list Ev) :
  {{{ is_pkg_init yjs ∗ is_Text t γs γh name L ∗
      is_store_client γs c ∗ is_history_lb γh c h0 ∗ own_read_cap γs }}}
    t @! (go.PointerType yjs.Text) @! "Len" #()
  {{{ (n : w64) (model : list (YjsItem A * bool)), RET #n;
      is_Text t γs γh name L ∗ own_read_cap γs ∗
      ⌜n = W64 (length (visible_items model))⌝ ∗
      ⌜text_snapshot L model⌝ ∗ ⌜history_reflected h0 name model⌝ }}}.
Proof.
  wp_start as "(Hpre & #Hpin & #Hlb & Hcap)". iNamed "Hpre".
  iDestruct "His_store" as "#His_store".
  wp_auto. subst s_loc.
  wp_apply (wp_Store__rlock _ _ _ c h0 name _ with "[$His_store $Hcap $Hpin $Hlb $Hbind]").
  iIntros (locs p) "(Hrlo & Hro & %Hfact)".
  iNamed "Hro".
  iDestruct (auth_gmap_gset_lookup_dq with "Hseq His_lb") as %(S' & HmS & HLsub).
  rewrite lookup_fmap in HmS. apply fmap_Some in HmS as (tm & Htmp & ->).
  iDestruct "Htypes" as "(%Hlocswf & Hpool)".
  iDestruct (big_sepM_lookup_acc _ _ _ _ Htmp with "Hpool") as "[Hbody Hclose]".
  iDestruct "Hbody" as (ls) "(%Hls & Htext & %Hinvarr)".
  iDestruct "Htext" as (yt0 tl0) "(Hparent & Hdll & %Hlen & %Harr)".
  subst parent.
  wp_auto.
  iDestruct ("Hclose" with "[Hparent Hdll]") as "Hpool".
  { iExists ls. iSplitR; first by iPureIntro. iSplitL; last by iPureIntro.
    iExists yt0, tl0. iFrame "Hparent Hdll". iPureIntro. split; [exact Hlen | exact Harr]. }
  wp_apply (wp_Store__runlock with "[$His_store $Hrlo Hseq Hpool]").
  { iFrame "Hseq". rewrite /own_type_pool_runs. iSplitR; [by iPureIntro | iFrame "Hpool"]. }
  iIntros "Hcap".
  wp_auto.
  have Hfst : (runs_model (tm_runs tm)).*1 = tm_arr tm.
  { rewrite runs_model_fst -Harr //. }
  iApply ("HΦ" $! _ (runs_model (tm_runs tm))).
  iSplitR "Hcap"; last first.
  { iFrame "Hcap". iPureIntro. split_and!.
    - rewrite Hlen runs_visible_model //.
    - split; rewrite Hfst; [exact HLsub | exact Hinvarr].
    - move=> input Hin.
      destruct (Hfact input Hin) as (tm' & it & Htm' & Hitid & Hitmem).
      rewrite Htmp in Htm'. injection Htm' as <-.
      exists it. split; [exact Hitid | rewrite Hfst //]. }
  iExists tv, tv.(yjs.Text.store'), tv.(yjs.Text.inner').
  iFrame "Ht His_store His_hist Hbind His_lb".
  iPureIntro. split_and!; [reflexivity | reflexivity | exact Hsorted].
Qed.

End text.
