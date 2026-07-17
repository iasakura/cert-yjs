(** Doc-layer invariant / WP proofs — mirrors yjs/doc.go. Currently just the
    [Doc] representation predicate [is_Doc]; it is the home for the eventual
    [wp_NewDoc] / [wp_Doc__GetText] proofs (GetText consumes [is_Doc] and returns
    [is_Text t []], which is why this module sits after [yjs_text] in the
    dependency order: core → common → id → item → ytype → store → text → doc). *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import yjs_core.
From New.proof Require Import yjs_common yjs_id yjs_item yjs_ytype yjs_history yjs_store yjs_text.
From New.proof.sync_proof Require Import mutex.
From iris.algebra Require Import auth gmap gset.
From iris.algebra.lib Require Import dfrac_agree.       (* [is_Store]'s reader-count [types] agreement *)

Section doc.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.
(* [is_Store] (from yjs_store) is generalized over the store lock + item-set RA,
   so mirror its Context here to apply it. *)
Context {sync_pkg : sync.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.
Notation P := go_string.
Local Notation TId := (TypeId P).
Local Notation Op := (TId * @YjsOperation A)%type.
Local Notation Ev := (@Event Op).
Local Notation DocM := (gmap TId (list (YjsItem A))).
Context {seq_inG : inG Σ (authR (gmapUR loc (gsetUR (YjsItem A))))}.
(* [is_Store]'s reader-count accounting ties the readers' share to the store's
   [types] map via a [dfrac_agree]; mirror the instance here to apply [is_Store]. *)
Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO (gmap loc type_state)))}.

(** Doc handle (persistent): reads ONLY [Doc.store] (immutable ⇒ [↦□]) and
    delegates to [is_Store]. Since [Text] holds the store directly (y-octo: the
    YTypeRef carries the store ref), [is_Text] does NOT go through [is_Doc]; this
    predicate is the Doc-level handle used by the eventual [wp_NewDoc] /
    [wp_Doc__GetText] specs (GetText: consume [is_Doc dv s_loc γ], create a YType
    under the lock, return [is_Text t []]). *)
Definition is_Doc (dv s_loc : loc) (γs : store_names) (γh : history_names) : iProp Σ :=
  ∃ (dvv : yjs.Doc.t),
    "Hdoc" ∷ dv ↦□ dvv ∗
    "%Hstore" ∷ ⌜dvv.(yjs.Doc.store') = s_loc⌝ ∗
    "His_store" ∷ is_Store s_loc γs γh.

#[global] Instance is_Doc_persistent dv s_loc γs γh : Persistent (is_Doc dv s_loc γs γh).
Proof. apply _. Qed.

(** Peek [own_store]'s coherence fact while keeping the resource: the replayed
    doc model [m] is coherent with the store's current history [h]. Used to
    instantiate the receiver-side obligation of [wp_Doc__ApplySyncUpdate] at
    the history the lock reveals. *)
Lemma own_store_hist_coh (s_loc : loc) (γs : store_names) (γh : history_names)
    (c : ClientId) (h : list Ev) (m : DocM) :
  own_store s_loc γs γh c h m -∗ own_store s_loc γs γh c h m ∗ ⌜history_state_coh h m⌝.
Proof.
  iIntros "H". iNamed "H".
  iSplitL "Hclient Hclock Hitemsf Hitemmap Htypesf Htypesmap Hdset Hseq Htypes HtypesAuth Hhist".
  - iExists client, k, items_mref, types_mref, dset, types, bind.
    iFrame "Hclient Hclock Hitemsf Hitemmap Htypesf Htypesmap Hdset Hseq Htypes HtypesAuth Hbinds Hhist".
    iPureIntro. split_and!;
      [exact Hclientc | exact Hregcoh | exact Hhcoh | exact Hctr
      | exact Hlocdup | exact Hrangedisj].
  - iPureIntro. exact Hhcoh.
Qed.

(** [Doc.ApplySyncUpdate]: the receiving half of the Yjs sync protocol
    (Step2/Update) over the REAL document. It takes the write lock and runs the
    proven conflict-resolving integrate loop ([store.applyUpdate]) on the
    actual store, so the replica's history genuinely advances by the batch. The
    change is reported as the persistent history-prefix certificate
    [is_history_lb γh c (h ++ deliver_ev <$> inputs)]: the document's delivered
    fragment now contains exactly this update.

    The two side conditions are the honest receiver obligations, not faked. The
    first is the [2^64] no-wrap seam on the inputs. The second is the
    protocol's freshness/coverage guarantee: for WHATEVER coherent history and
    model the replica is actually in (revealed only under the lock), the batch
    is a certified, deliverable update ([batch_ok]) with no clock at [2^64-1].
    A real sender establishes it by diffing against the receiver's advertised
    state vector (Step1), so exactly the missing, causally ready structs are
    sent; here it is a pure precondition, discharged by that protocol argument
    (which, end to end, needs the state-vector <-> delivered-set faithfulness,
    the remaining #51/#63 work). Everything h-independent (the op certificates
    and the root witnesses) is supplied up front. *)
Lemma wp_Doc__ApplySyncUpdate (dv s_loc : loc) (γs : store_names) (γh : history_names)
    (sl : slice.t) (dq : dfrac)
    (inputs : list (TId * IntegrateInput (A := A))) (Ds : list (gset YjsId)) :
  (∀ (i : nat) (ti : TId * IntegrateInput (A := A)),
     inputs !! i = Some ti -> (Z.of_nat (clock (in_id ti.2)) + 1 < 2^64)%Z) ->
  (∀ (h : list Ev) (m : DocM), history_state_coh h m ->
     batch_ok h inputs Ds /\
     (∀ (t : TId) x, x ∈ docm_get m t -> (Z.of_nat (clock (item_id x)) + 1 < 2^64)%Z)) ->
  {{{ is_pkg_init yjs ∗ is_Doc dv s_loc γs γh ∗ is_history (A := A) (P := P) γh ∗
      own_update sl dq inputs ∗
      ([∗ list] ti;D ∈ inputs;Ds, is_op_cert γh (ti.1, OpInsert ti.2) D) ∗
      ([∗ list] ti ∈ inputs, ∃ nm : P, ⌜ti.1 = RootId nm⌝ ∗ is_root γs nm) }}}
    dv @! (go.PointerType yjs.Doc) @! "ApplySyncUpdate" #sl
  {{{ (c : ClientId) (h : list Ev) (m' : DocM), RET #();
      own_update sl dq inputs ∗
      is_history_lb γh c (h ++ (deliver_ev <$> inputs)) }}}.
Proof.
  move=> Hnowrapb Hrecv.
  wp_start as "(#His_doc & #Hishist & Hupd & #Hcerts & #Hroots)".
  iNamed "His_doc". subst s_loc. wp_auto.
  (* take the write lock, reveal the store's current (c, h, m) *)
  wp_apply (wp_Store__wlock with "[$His_store]"). iIntros "[Hwl Hinv]".
  iEval (rewrite store_inv_own_store) in "Hinv".
  iDestruct "Hinv" as (c h m) "Hstore".
  iDestruct (own_store_hist_coh with "Hstore") as "[Hstore %Hhcoh]".
  destruct (Hrecv h m Hhcoh) as [Hbatch Hnowrapm].
  wp_auto.
  (* run the proven certificate-based applyUpdate on the real store *)
  wp_apply (wp_store__applyUpdate_certs _ sl dq γs γh c h m inputs
              Hnowrapm Hnowrapb
              with "[$Hishist $Hstore $Hupd $Hroots Hcerts]").
  { iExists Ds. iFrame "Hcerts". iPureIntro. exact Hbatch. }
  iIntros (m') "(Hstore & Hupd & %Hvr & #Hlb & #Hrootlbs)".
  wp_auto.
  (* rebuild store_inv at the advanced history and release the lock *)
  iAssert (▷ store_inv dvv.(yjs.Doc.store') γs γh)%I with "[Hstore]" as "Hinv".
  { iNext. iApply store_inv_own_store.
    iExists c, (h ++ (deliver_ev <$> inputs)), m'. iFrame "Hstore". }
  wp_apply (wp_Store__wunlock with "[$His_store $Hwl $Hinv]").
  iApply ("HΦ" $! c h m'). iFrame "Hupd Hlb".
Qed.

End doc.
