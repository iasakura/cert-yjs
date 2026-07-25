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
Local Notation DocModel := (gmap TId (list (YjsItem A))).
Context {seq_inG : inG Σ (authR (gmapUR loc (gsetUR (YjsItem A))))}.
Context {acc_inG : inG Σ (authR (gsetUR YjsId))}.
(* [is_Store]'s reader-count accounting ties the readers' share to the store's
   [types] map via a [dfrac_agree]; mirror the instance here to apply [is_Store]. *)
Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO (gmap loc type_state)))}.

(* [is_pending_rooted]'s instances are [#[local]] in [yjs_store_base] (closed over
   a wider section context); re-declare here so [iNamed] can unpack the
   persistent [#Hpendroot] conjunct of [own_store]. *)
#[local] Instance pending_item_rooted_persistent'' γs typedInput :
  Persistent (pending_item_rooted γs typedInput).
Proof. rewrite /pending_item_rooted. destruct (decide _); apply _. Qed.
#[local] Instance is_pending_rooted_persistent'' γs pending :
  Persistent (is_pending_rooted γs pending).
Proof. apply _. Qed.

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
    (c : ClientId) (h : list Ev) (m : DocModel)
    (pend : list (TId * IntegrateInput (A := A))) :
  own_store s_loc γs γh c h m pend -∗
  own_store s_loc γs γh c h m pend ∗ ⌜history_state_coh h m⌝.
Proof.
  iIntros "H". iNamed "H".
  iSplitL "Hclient Hclock Hitemsf Hitemmap Htypesf Htypesmap Hdset Hpendf Hpend Hseq Htypes HtypesAuth Hhist Hacc".
  - iExists client, k, items_mref, types_mref, dset, pend_sl, types, bind, acc.
    iFrame "∗#".
    iPureIntro. split_and!;
      [exact Hclientc | exact Hpendbnd | exact Hregcoh | exact Hhcoh | exact Hctr
      | exact Hlocdup | exact Hrangedisj | exact Hrunfits | exact Horiginclk | exact Hacccoh].
  - iPureIntro. exact Hhcoh.
Qed.

(** [Doc.ApplySyncUpdate]: the receiving half of the Yjs sync protocol
    (Step2/Update) over the REAL document. It takes the write lock and runs the
    proven conflict-resolving integrate loop ([store.applyUpdate]) on the
    actual store, so the replica's history genuinely advances by the batch. The
    change is reported as the persistent history-prefix certificate
    [is_history_lb γh c (h ++ deliver_ev <$> expand_inputs applied)]: the
    document's delivered fragment now contains exactly the applied (drained)
    per-char ops. Crucially, every input is handed a persistent receipt
    [is_accepted γs (in_id x.2)]: the store invariant ties the grow-only
    accepted-id set to [delivered_ids h ∪ pending ids] and every store op
    preserves that tie, so an accepted id is FOREVER delivered-or-buffered,
    never silently dropped. This makes no-loss an ENFORCEABLE guarantee: a
    discarding implementation, which delivers and buffers nothing, could not
    mint these fragments (unlike a bare existential over the internal [rest],
    which any implementation can satisfy vacuously). Interference means we
    still cannot pin down WHICH of delivered/buffered a given input takes (the
    receipt is at the id level); [own_store_accepted_sound] recovers, under the
    lock, that an accepted id is currently one or the other.

    Because the drain is TOTAL (issue #40: the pending buffer plus the batch
    drain to the structural-dependency fixpoint, in ANY order), there is NO
    causal-closure / [batch_ok] / freshness receiver obligation: whatever
    coherent history and model the replica is in (revealed only under the lock),
    the certified structs that are ready get delivered and the rest stay
    buffered. The only side condition is the honest [2^64] no-wrap seam on the
    inputs (per char: [clock + length(content) < 2^64]). Everything else (the
    per-char op certificates over [expand_inputs inputs] and the root witnesses)
    is supplied up front and is [h]-independent. *)
Lemma wp_Doc__ApplySyncUpdate (dv s_loc : loc) (γs : store_names) (γh : history_names)
    (sl : slice.t) (dq : dfrac)
    (inputs : list (TId * IntegrateInput (A := A))) :
  (∀ typedInput : TId * IntegrateInput (A := A), typedInput ∈ inputs ->
     (Z.of_nat (clock (in_id typedInput.2)) + Z.of_nat (length (in_content typedInput.2)) < 2^64)%Z) ->
  {{{ is_pkg_init yjs ∗ is_Doc dv s_loc γs γh ∗ is_history (A := A) (P := P) γh ∗
      own_update_structs sl dq inputs ∗
      is_pending_certified γh (expand_inputs inputs) ∗
      is_pending_rooted γs inputs }}}
    dv @! (go.PointerType yjs.Doc) @! "ApplySyncUpdate" #sl
  {{{ (c : ClientId) (h : list Ev)
      (applied rest : list (TId * IntegrateInput (A := A))), RET #();
      own_update_structs sl dq inputs ∗
      is_history_lb γh c (h ++ (deliver_ev <$> expand_inputs applied)) ∗
      ([∗ list] x ∈ inputs, is_accepted γs (in_id x.2)) }}}.
Proof.
  move=> Hnowrapb.
  wp_start as "(#His_doc & #Hishist & Hupd & #Hcerts & #Hroots)".
  iNamed "His_doc". subst s_loc. wp_auto.
  (* take the write lock, reveal the store's current (c, h, m, pend) *)
  wp_apply (wp_Store__wlock with "[$His_store]"). iIntros "[Hwl Hinv]".
  iEval (rewrite store_inv_own_store) in "Hinv".
  iDestruct "Hinv" as (c h m pend) "Hstore".
  iDestruct (own_store_hist_coh with "Hstore") as "[Hstore %Hhcoh]".
  wp_auto.
  (* run the total certificate-based applyUpdate on the real store: no
     causal-closure obligation; the pending plus the batch drain to the
     structural fixpoint, delivering only the applied structs (per char) *)
  wp_apply (wp_store__applyUpdate_certs _ sl dq γs γh c h m pend inputs
              Hnowrapb
              with "[$Hishist $Hstore $Hupd $Hcerts $Hroots]").
  iIntros (applied rest m') "(Hupd & Hstore & #Hlb & %Hdrain & %Hvr & %Hnoc & %Hnoloss & #Hrootlbs)".
  wp_auto.
  (* mint the ENFORCEABLE no-loss receipts: every input's id is accepted, hence
     (by the store invariant) forever delivered-or-buffered; a discarding
     implementation could not produce these fragments *)
  iMod (own_store_accept_batch _ _ _ _ _ _ _ inputs
          ltac:(move=> x Hx; exact (input_accounted_id _ _ _ (Hnoloss x Hx)))
          with "Hstore") as "[Hstore #Haccepts]".
  (* rebuild store_inv at the advanced history (delivered = expand_inputs applied)
     with the leftover as the new pending, and release the lock *)
  iAssert (▷ store_inv dvv.(yjs.Doc.store') γs γh)%I with "[Hstore]" as "Hinv".
  { iNext. iApply store_inv_own_store.
    iExists c, (h ++ (deliver_ev <$> expand_inputs applied)), m', rest. iFrame "Hstore". }
  wp_apply (wp_Store__wunlock with "[$His_store $Hwl $Hinv]").
  iApply ("HΦ" $! c h applied rest). iFrame "Hupd Hlb Haccepts".
Qed.

End doc.
