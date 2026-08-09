(** [wp_Text__String]: the [Text] handle's visible-string read, a concurrent
    read under the store's RWMutex read lock (issues #22 / #125). Shares
    [is_Text] etc. via [text/heap.v].

    The postcondition is a SNAPSHOT: the returned string spells exactly the
    visible characters of some tombstone-tagged array [marr] that (a)
    satisfies the document invariant, (b) contains everything the handle
    already knew ([L]), and (c) contains any content lower bound [S] the
    caller brings as an [is_root_lb] certificate (e.g. the applyUpdate
    receipts threaded through the ws server's [entry_receipts], issue #125).
    The bound is at the ITEM-SET level: a tombstoned item is in [marr] but
    not in the string, so "the characters are visible" needs a no-delete
    side condition on top; the set-level statement is unconditional. *)
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
Context {sync_pkg : sync.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.
Context {seq_inG : inG Σ (authR (gmapUR loc (gsetUR (YjsItem A))))}.
Context {acc_inG : inG Σ (authR (gsetUR YjsId))}.
Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO (gmap loc type_state)))}.

Local Notation P := go_string.
Local Notation TId := (TypeId P).
Local Notation Op := (TId * @YjsOperation A)%type.
Local Notation Ev := (@Event Op).
Local Notation DocModel := (gmap TId (list (YjsItem A))).

(** [Text.String]: a CONCURRENT functional read (issue #125). Takes the
    RWMutex read lock, walks the type's DLL through a fractional
    [store_inv_ro] share ([wp_yType__Text]), then releases. *)
Lemma wp_Text__String (t : loc) (γs : store_names) (γh : history_names) (name : P)
    (L : list (YjsItem A)) (S : gset (YjsItem A)) :
  {{{ is_pkg_init yjs ∗ is_Text t γs γh name L ∗ is_root_lb γs name S ∗ own_read_cap γs }}}
    t @! (go.PointerType yjs.Text) @! "String" #()
  {{{ (str : go_string) (marr : list (YjsItem A * bool)), RET #str;
      is_Text t γs γh name L ∗ own_read_cap γs ∗
      ⌜str = visible_string marr⌝ ∗
      ⌜list_to_set L ∪ S ⊆ (list_to_set marr.*1 : gset (YjsItem A))⌝ ∗
      ⌜YjsArrInvariant marr.*1⌝ }}}.
Proof.
  wp_start as "(Hpre & #Hrootlb & Hcap)". iNamed "Hpre".
  iDestruct "His_store" as "#His_store".
  wp_auto. subst s_loc. subst parent.
  wp_apply (wp_Store__rlock with "[$His_store $Hcap]"). iIntros (types) "[Hrlo Hro]".
  iNamed "Hro".
  iDestruct (auth_gmap_gset_lookup_dq with "Hseq His_lb") as %(S' & HmS & HLsub).
  rewrite lookup_fmap in HmS. apply fmap_Some in HmS as (ts & Htsp & ->).
  (* the caller's certificate names the same root: its hidden binding agrees
     with the handle's, so its bound lands in the same item set *)
  iDestruct "Hrootlb" as (p') "[Hbind' Hlb']".
  iDestruct (is_type_binding_agree with "Hbind Hbind'") as %<-.
  iDestruct (auth_gmap_gset_lookup_dq with "Hseq Hlb'") as %(S'' & HmS' & HSsub).
  rewrite lookup_fmap Htsp /= in HmS'. injection HmS' as <-.
  (* borrow the type's DLL and run the verified walk *)
  iDestruct (big_sepM_lookup_acc _ _ _ _ Htsp with "Htypes") as "[Hbody Hclose]".
  iDestruct "Hbody" as "(Htext & %Hinvarr)".
  iDestruct (own_ytype_cells_flatten with "Htext") as "[Htext %Hflat]".
  wp_auto.
  wp_apply (wp_yType__Text (tv.(yjs.Text.inner')) (DfracOwn rwmutex_guard.rfrac)
              (ty_cells ts) (ty_arr ts) with "[$Htext]").
  iIntros "Htext".
  iDestruct ("Hclose" with "[Htext]") as "Htypes".
  { iFrame "Htext". iPureIntro. exact Hinvarr. }
  wp_auto.
  wp_apply (wp_Store__runlock with "[$His_store $Hrlo Hseq Htypes]").
  { iFrame "Hseq Htypes". }
  iIntros "Hcap".
  wp_auto.
  have Hfst : (cells_model (ty_cells ts)).*1 = ty_arr ts.
  { rewrite cells_model_fst -Hflat //. }
  iApply ("HΦ" $! _ (cells_model (ty_cells ts))).
  iSplitR "Hcap"; last first.
  { iFrame "Hcap". iPureIntro. split_and!.
    - reflexivity.
    - rewrite Hfst. apply union_least; [exact HLsub | exact HSsub].
    - rewrite Hfst. exact Hinvarr. }
  iExists tv, tv.(yjs.Text.store'), tv.(yjs.Text.inner').
  iFrame "Ht His_store His_hist Hbind His_lb".
  iPureIntro. split_and!; [reflexivity | reflexivity | exact Hsorted].
Qed.

End text.
