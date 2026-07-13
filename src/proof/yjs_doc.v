(** Doc-layer invariant / WP proofs, mirroring yjs/doc.go: the [Doc]
    representation predicate [is_Doc] and the PUBLIC locking apply_update
    entry [wp_Doc__applyUpdate] (issue #40). Still the home for the eventual
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
Context {seq_inG : inG Σ (authR (gmapUR loc (gsetUR (YjsItem A))))}.
(* [is_Store]'s reader-count accounting ties the readers' share to the store's
   [types] map via a [dfrac_agree]; mirror the instance here to apply [is_Store]. *)
Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO (gmap loc type_state)))}.

(* The ghost op-history types at the document content type (as in yjs_store). *)
Local Notation P := go_string.
Local Notation TId := (TypeId P).
Local Notation Op := (TId * @YjsOperation A)%type.
Local Notation Ev := (@Event Op).
Local Notation DocM := (gmap TId (list (YjsItem A))).

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

(** [Doc.applyUpdate], the PUBLIC locking apply_update entry (issue #40):
    take the store's write lock, run the certificate-based
    [store.applyUpdate], release. Stated over the persistent [is_Doc] only;
    the lock-hidden store state enters through the caller's
    LINEARIZATION-POINT VIEW SHIFT ("the certifier"): for whatever model
    [(c, h, m)] the store holds when the lock is acquired, the caller must
    produce the batch's sender-side certificates ([is_certified_batch]: one
    persistent [is_op_cert] per input + the pure id-level coverage/freshness
    [batch_ok]) and the [2^64-1] no-wrap seam for [m], and may extract any
    [Ψ c h m] it wants to remember the pre-state by. Validity is thereby a
    sender-side property (history membership + causal closure); no
    receiver-side [ValidReplay] precondition anywhere. [ValidReplay] appears
    only in the POST, as the pure witness determining [m'] from [m], next to
    one persistent [is_root_lb] content certificate per delivered root.

    A single-owner caller (e.g. the network layer's receive loop, which is
    the only writer besides its own [Text] handles) discharges the certifier
    by tracking [(c, h, m)] through its own protocol invariant; y-octo's
    state-vector dedup / pending buffer, which would make the entry total,
    is the staged follow-up (plan-issue-42 §6.5.1 / §8.5). *)
Lemma wp_Doc__applyUpdate (dv s_loc : loc) (γs : store_names) (γh : history_names)
    (sl : slice.t) (dq : dfrac)
    (inputs : list (TId * IntegrateInput (A := A)))
    (Ψ : ClientId -> list Ev -> DocM -> iProp Σ) :
  (∀ (i : nat) (ti : TId * IntegrateInput (A := A)),
     inputs !! i = Some ti -> (Z.of_nat (clock (in_id ti.2)) + 1 < 2^64)%Z) ->
  {{{ is_pkg_init yjs ∗ is_Doc dv s_loc γs γh ∗
      is_history (A := A) (P := P) γh ∗
      own_update sl dq inputs ∗
      ([∗ list] ti ∈ inputs, ∃ nm : P, ⌜ti.1 = RootId nm⌝ ∗ is_root γs nm) ∗
      (∀ (c : ClientId) (h : list Ev) (m : DocM),
         own_store s_loc γs γh c h m ={⊤}=∗
         own_store s_loc γs γh c h m ∗
         is_certified_batch γh h inputs ∗
         ⌜∀ (t : TId) (x : YjsItem A), x ∈ docm_get m t ->
            (Z.of_nat (clock (item_id x)) + 1 < 2^64)%Z⌝ ∗
         Ψ c h m) }}}
    dv @! (go.PointerType yjs.Doc) @! "applyUpdate" #sl
  {{{ RET #();
      own_update sl dq inputs ∗
      ∃ (c : ClientId) (h : list Ev) (m m' : DocM),
        Ψ c h m ∗ ⌜ValidReplay inputs m m'⌝ ∗
        ([∗ list] ti ∈ inputs, ∃ nm : P, ⌜ti.1 = RootId nm⌝ ∗
           is_root_lb γs nm (list_to_set (docm_get m' ti.1))) }}}.
Proof.
  move=> Hnowrapb.
  wp_start as "Hpre".
  iDestruct "Hpre" as "(#Hdoc & #Hishist & Hupd & #Hroots & Hcert)".
  iNamed "Hdoc".
  wp_auto.
  subst s_loc.
  wp_apply (wp_Store__wlock with "[$His_store]"). iIntros "[Hlk Hinv]".
  iEval (rewrite store_inv_own_store) in "Hinv".
  iDestruct "Hinv" as (c h m) "Hstore".
  iMod ("Hcert" with "Hstore") as "(Hstore & #Hcertb & %Hnowrapm & HΨ)".
  wp_auto.
  wp_apply (wp_store__applyUpdate_certs _ sl dq γs γh c h m inputs Hnowrapm Hnowrapb
              with "[$Hishist $Hstore $Hupd $Hcertb $Hroots]").
  iIntros (m') "(Hstore & Hupd & %Hvr & #Hlbs)".
  wp_auto.
  wp_apply (wp_Store__wunlock with "[$His_store $Hlk Hstore]").
  { iNext. rewrite store_inv_own_store.
    iExists c, (h ++ (deliver_ev <$> inputs)), m'. iFrame "Hstore". }
  iApply "HΦ". iFrame "Hupd".
  iExists c, h, m, m'. iFrame "HΨ Hlbs". by iPureIntro.
Qed.

End doc.
