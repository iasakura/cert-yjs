(** [wp_Doc__ApplySyncUpdate]: the Doc-level entry point of the sync protocol,
    applying a peer's update batch under the store's write lock and reporting
    the resulting growth of the ghost history. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core.
From New.proof Require Import prelude.
From New.proof Require Import history.
From New.proof.id Require Import id.
From New.proof.item Require Import item.
From New.proof.ytype Require Import ytype.
From New.proof.store Require Import store.
From New.proof.text Require Import text.
From New.proof.sync_proof Require Import mutex.
From iris.algebra Require Import auth gmap gset.
From iris.algebra.lib Require Import dfrac_agree.
From New.proof.doc Require Import model heap.

Section doc_ApplySyncUpdate.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

(* [is_Store] (from store/store) is generalized over the store lock + item-set RA,
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
Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO addressed_pool))}.


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
    is supplied up front and is [h]-independent.

    The CONTENT receipts (issue #125): [is_applied_root_lb] bounds each
    applied root's grow-only item set from below by its post-apply model
    list [doc_model_get m' _], and the pure companion names which items sit
    in that bound, one item per applied per-char op, carrying the op's id
    ([ValidReplay_input_mem]). A concurrent reader intersects the bound with
    its snapshot ([wp_Text__Len] / [wp_Text__String], via the history
    certificate below), so the applied portion
    of the batch is guaranteed VISIBLE-as-items to every later read. The
    buffered portion is covered only by [is_accepted] (delivered-or-buffered):
    it reaches no root's content until its dependencies arrive. *)
Lemma wp_Doc__ApplySyncUpdate (dv s_loc : loc) (γs : store_names) (γh : history_names)
    (c : ClientId) (sl sldel : slice.t) (dq dqd : dfrac)
    (inputs : list (TId * IntegrateInput (A := A)))
    (deleted : gset YjsId) :
  update_wf inputs ->
  {{{ is_pkg_init yjs ∗ is_Doc dv s_loc γs γh ∗ is_history (A := A) (P := P) γh ∗
      is_store_client γs c ∗
      own_update_structs sl dq inputs ∗
      own_delete_ids sldel dqd deleted ∗
      is_pending_certified γh (expand_inputs inputs) }}}
    dv @! (go.PointerType yjs.Doc) @! "ApplySyncUpdate" #sl #sldel
  {{{ (h : list Ev) (applied : list (TId * IntegrateInput (A := A))) (m' : DocModel), RET #();
      own_update_structs sl dq inputs ∗
      own_delete_ids sldel dqd deleted ∗
      is_history_lb γh c (h ++ (deliver_ev <$> expand_inputs applied)) ∗
      ([∗ list] x ∈ inputs, is_accepted γs (in_id x.2)) ∗
      is_applied_certs γs applied m' }}}.
Proof.
  move=> Hwf.
  wp_start as "(#His_doc & #Hishist & #Hpin & Hupd & Hdel & #Hcerts)".
  (* open the pure model: the wire records live only inside this proof *)
  iDestruct "Hdel" as (spans) "[Hspans %Hdeleted]".
  iNamed "His_doc". subst s_loc. wp_auto.
  (* take the write lock, reveal the store's current (c0, h, m, pend); the
     client pin identifies c0 with the caller's c *)
  wp_apply (wp_Store__wlock with "[$His_store]"). iIntros "[Hwl Hinv]".
  iDestruct "Hinv" as (c0 h m pend) "Hstore".
  iDestruct (own_store_client_pin with "Hstore") as "[Hstore #Hpin0]".
  iDestruct (is_store_client_agree with "Hpin0 Hpin") as %->.
  iDestruct (own_store_hist_coh with "Hstore") as "[Hstore %Hhcoh]".
  wp_auto.
  (* run the total certificate-based applyUpdate on the real store: no
     causal-closure obligation; the pending plus the batch drain to the
     structural fixpoint, delivering only the applied structs (per char) *)
  wp_apply (wp_store__applyUpdate _ sl dq γs γh c h m pend inputs Hwf
              with "[$Hishist $Hstore $Hupd $Hcerts]").
  iIntros (applied rest m') "(Hupd & Hstore & #Hlb & %Hdrain & %Hvr & %Hnoloss & #Happlied)".
  wp_auto.
  (* the delete spans, second: a span may target a struct that just arrived
     in this very batch. Deletes are model no-ops, so the store's model,
     history and pending buffer come back unchanged (the tombstones and the
     splits live under the [types] existential). *)
  wp_apply (wp_store__applyDeleteSpans_store (dvv.(yjs.Doc.store')) γs γh c
              (h ++ (deliver_ev <$> expand_inputs applied)) m' rest sldel dqd spans
              with "[$Hstore $Hspans]").
  iIntros "[Hstore Hspans]".
  wp_auto.
  (* mint the ENFORCEABLE no-loss receipts: every input's id is accepted, hence
     (by the store invariant) forever delivered-or-buffered; a discarding
     implementation could not produce these fragments *)
  iMod (own_store_accept_batch _ _ _ _ _ _ _ inputs
          ltac:(move=> x Hx; exact (input_accounted_id _ _ _ (Hnoloss x Hx)))
          with "Hstore") as "[Hstore #Haccepts]".
  (* release the lock at the advanced history (delivered = expand_inputs applied)
     with the leftover as the new pending *)
  wp_apply (wp_Store__wunlock with "[$His_store $Hwl $Hstore]").
  iApply ("HΦ" $! h applied m'). iFrame "Hupd Hlb Haccepts Happlied".
  iExists spans. by iFrame "Hspans".
Qed.

End doc_ApplySyncUpdate.
