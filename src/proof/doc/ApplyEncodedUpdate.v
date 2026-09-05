(** [wp_Doc__ApplyEncodedUpdate]: the byte-level entry point of the update
    path (issue #107, W3b). Decode one wire message with the deployment's
    codec value and apply the batch through [wp_Doc__ApplySyncUpdate].

    Everything the apply needs comes off the wire protocol [yjs_prot]: the
    decode fact closes the codec's failure branch (dead under the protocol),
    [update_wf] discharges the no-wrap and rootedness premises, and the
    per-char certificates feed the total drain. The caller learns the S1
    receipts: every decoded input is [is_accepted] by the store (forever
    delivered-or-buffered), and the client's history visibly grew by the
    applied portion. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core.
From New.proof Require Import prelude.
From New.proof Require Import history.
From New.proof Require Import yjs_prot.
From New.proof.id Require Import id.
From New.proof.item Require Import item.
From New.proof.ytype Require Import ytype.
From New.proof.store Require Import store.
From New.proof.text Require Import text.
From New.proof.sync_proof Require Import mutex.
From iris.algebra Require Import auth gmap gset.
From iris.algebra.lib Require Import dfrac_agree.
From New.proof.doc Require Import model heap ApplySyncUpdate.

Section doc_ApplyEncodedUpdate.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Context {sync_pkg : sync.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.

Notation P := go_string.

Local Notation TId := (TypeId P).

Local Notation Input := (TId * IntegrateInput (A := A))%type.

Local Notation Ev := (@Event (TId * @YjsOperation A)).

Context {seq_inG : inG Σ (authR (gmapUR loc (gsetUR (YjsItem A))))}.

Context {acc_inG : inG Σ (authR (gsetUR YjsId))}.

Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO addressed_pool))}.

Context (decode : list u8 -> option (list Input)).

Lemma wp_Doc__ApplyEncodedUpdate (dv s_loc : loc) (γs : store_names)
    (γh : history_names) (c : ClientId) (f : func.t) (s : slice.t) (dq : dfrac)
    (data : list u8) :
  {{{ is_pkg_init yjs ∗ is_Doc dv s_loc γs γh ∗ is_history (A := A) (P := P) γh ∗
      is_store_client γs c ∗ codec_spec decode f ∗
      s ↦*{dq} data ∗ yjs_prot decode γh data }}}
    dv @! (go.PointerType yjs.Doc) @! "ApplyEncodedUpdate" #f #s
  {{{ (h : list Ev) (inputs applied : list Input) (m' : gmap TId (list (YjsItem A))), RET #true;
      s ↦*{dq} data ∗
      ⌜decode data = Some inputs⌝ ∗
      is_history_lb γh c (h ++ (deliver_ev <$> expand_inputs applied)) ∗
      ([∗ list] x ∈ inputs, is_accepted γs (in_id x.2)) ∗
      is_applied_certs γs applied m' }}}.
Proof.
  wp_start as "(#His_doc & #Hishist & #Hpin & #Hcodec & Hs & #Hprot)".
  iDestruct "Hprot" as (inputs) "(%Hdec & %Hwf & #Hcerts)".
  wp_auto.
  wp_apply ("Hcodec" with "[$Hs]").
  iIntros (ok sl sldel) "[Hs Hres]".
  destruct ok; last first.
  { (* dead under the protocol: the message decodes *)
    iDestruct "Hres" as %Hnone. rewrite Hdec in Hnone. discriminate. }
  iDestruct "Hres" as (inputs' deleted) "(%Hdec' & Hupd & Hdel)".
  rewrite Hdec in Hdec'. injection Hdec' as <-.
  wp_auto.
  wp_apply (wp_Doc__ApplySyncUpdate _ _ _ _ c _ _ _ _ inputs deleted Hwf
              with "[$His_doc $Hishist $Hpin $Hupd $Hdel $Hcerts]").
  iIntros (h applied m') "(Hupd & Hdel & #Hlb & #Haccepts & #Happlied)".
  wp_auto.
  iApply ("HΦ" $! h inputs applied m').
  iFrame "Hs Hlb Haccepts Happlied". done.
Qed.

End doc_ApplyEncodedUpdate.
