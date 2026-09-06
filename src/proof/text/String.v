(** [wp_Text__String]: the [Text] handle's visible-string read, a concurrent
    read under the store's RWMutex read lock (issues #22 / #125). Shares
    [is_Text] etc. via [text/heap.v].

    The postcondition is a SNAPSHOT: the returned string spells exactly the
    visible characters of some tombstone-tagged array [model] that satisfies
    the document invariant and contains everything the handle already knows
    ([L], the handle's grow-only lower bound), and that contains one item per
    delivered insert of the caller's history certificate [is_history_lb]
    targeting this root. The bound is at the ITEM-SET
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

Notation A := go_string.
Context {seq_inG : inG Σ (authR (gmapUR loc (gsetUR (YjsItem A))))}.
Context {acc_inG : inG Σ (authR (gsetUR YjsId))}.
Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO addressed_pool))}.

Local Notation P := go_string.
Local Notation TId := (TypeId P).
Local Notation Op := (TId * @YjsOperation A)%type.
Local Notation Ev := (@Event Op).
Local Notation DocModel := (gmap TId (list (YjsItem A))).


(** [Text.String]: a CONCURRENT functional read (issue #125). Takes the
    RWMutex read lock, walks the type's DLL through a fractional
    [store_inv_ro] share ([wp_yType__Text]), then releases. The caller brings
    a prefix certificate [is_history_lb γh c h0] of THIS replica's op history
    (with the client pin identifying it), and the model is guaranteed to
    contain one item per delivered insert of [h0] targeting this root (a
    caller with no such knowledge passes [h0 = []]). This is the read
    guarantee in the network stack's own currency: whoever observed the
    history grow (an applyUpdate postcondition, a server receipt, a
    sync-protocol certificate) can replay that knowledge against a concurrent
    read. *)
Lemma wp_Text__String (t : loc) (γs : store_names) (γh : history_names)
    (c : ClientId) (name : P) (L : list (YjsItem A)) (h0 : list Ev) :
  {{{ is_pkg_init yjs ∗ is_Text t γs γh name L ∗
      is_store_client γs c ∗ is_history_lb γh c h0 ∗ own_read_cap γs }}}
    t @! (go.PointerType yjs.Text) @! "String" #()
  {{{ (visible_text : go_string) (model : list (YjsItem A * bool)), RET #visible_text;
      is_Text t γs γh name L ∗ own_read_cap γs ∗
      ⌜visible_text = visible_string model⌝ ∗
      ⌜text_snapshot L model⌝ ∗ ⌜history_reflected h0 name model⌝ }}}.
Proof.
  wp_start as "(Hpre & #Hpin & #Hlb & Hcap)". iNamed "Hpre".
  iDestruct "His_store" as "#His_store".
  wp_auto. subst s_loc. subst parent.
  wp_apply (wp_Store__rlock _ _ _ c h0 name _ with "[$His_store $Hcap $Hpin $Hlb $Hbind]").
  iIntros (locs p) "(Hrlo & Hro & %Hfact)".
  iNamed "Hro".
  iDestruct (auth_gmap_gset_lookup_dq with "Hseq His_lb") as %(S' & HmS & HLsub).
  rewrite lookup_fmap in HmS. apply fmap_Some in HmS as (tm & Htmp & ->).
  iDestruct "Htypes" as "(%Hlocswf & Hpool)".
  (* borrow the type's run view and run the verified walk *)
  iDestruct (big_sepM_lookup_acc _ _ _ _ Htmp with "Hpool") as "[Hbody Hclose]".
  iDestruct "Hbody" as (ls) "(%Hls & Htextr & %Hinvarr)".
  iAssert (⌜tm_arr tm = runs_flatten (tm_runs tm)⌝)%I as %Harr;
    first by iDestruct "Htextr" as (yt tl) "(_ & _ & _ & %Harr)".
  wp_auto.
  wp_apply (wp_yType__Text (tv.(yjs.Text.inner')) (DfracOwn rwmutex_guard.rfrac) ls tm with "[$Htextr]").
  iIntros "Htextr".
  iDestruct ("Hclose" with "[Htextr]") as "Hpool".
  { iExists ls. iSplitR; first by iPureIntro. iFrame "Htextr". by iPureIntro. }
  wp_auto.
  wp_apply (wp_Store__runlock with "[$His_store $Hrlo Hseq Hpool]").
  { iFrame "Hseq". rewrite /own_type_pool_runs. iSplitR; [by iPureIntro | iFrame "Hpool"]. }
  iIntros "Hcap".
  wp_auto.
  have Hfst : (runs_model (tm_runs tm)).*1 = tm_arr tm.
  { rewrite runs_model_fst -Harr //. }
  iApply ("HΦ" $! _ (runs_model (tm_runs tm))).
  iSplitR "Hcap"; last first.
  { iFrame "Hcap". iPureIntro. split_and!.
    - reflexivity.
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
