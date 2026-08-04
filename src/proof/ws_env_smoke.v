(** The environment obligation is not vacuous.

    [ws_env_preserves] (src/goose_lang/ffi/ws_ffi/ws_ffi.v) is the one thing
    this development assumes about a peer it does not run. An assumption nobody
    can discharge is worth nothing, so here is a peer that discharges it, with a
    [ws_prot] that carries real certificates rather than [True].

    The peer is deliberately tiny: it may put exactly one message on the wire,
    the encoding of one insert into the empty document, and only as the first
    thing the network carries. That is enough for what is being checked, which
    is that the three pieces fit together at all:

    - [ws_may] is inhabited: there is data the environment is permitted to send;
    - [ws_prot] of that data is a real [is_op_cert], so a receiver learns the
      operation is registered in the ghost history;
    - [ws_env_preserves] holds, by the same [history_broadcast] a modeled sender
      would use at [wp_WsSendOp].

    Ghost only: no goose, no program, no WP. This is the ws analogue of
    [history_smoke] in history.v, and it reuses that lemma's side conditions
    verbatim.

    What it does NOT show is that a full Yjs client discharges the obligation.
    That peer's operations are anchored at operations the server relayed to it,
    so the argument goes through [history_deliver_pending] first, and its pure
    side conditions are about the model reached by draining the wire. Those are
    the next step; see the PR discussion. *)
From New.proof Require Import proof_prelude.
From New.golang Require Import theory.
From New.proof Require Export core.
From New.proof Require Export network_model.
From New.proof Require Export history.
From New.goose_lang.ffi.ws_ffi Require Import ws_ffi.

Section smoke.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {A : Type} `{EqDA : EqDecision A}.
Context {P : Type} `{EqDP : !EqDecision P} `{CntP : !Countable P}.
Context `{!wsGS Σ}.

Set Default Proof Using "Type*".

Local Notation TId := (TypeId P).
Local Notation Input := (TId * IntegrateInput (A := A))%type.
Local Notation Ev := (@Event (TId * @YjsOperation A)).
Local Notation DocM := (gmap TId (list (YjsItem A))).

(** The codec is a parameter: which bytes stand for which operation is the
    application's business, and nothing here depends on the choice beyond
    being able to read one back. *)
Context (encode : Input -> list u8).
Context (decode : list u8 -> option Input).
Hypothesis decode_encode : forall x, decode (encode x) = Some x.

(** The protocol: these bytes decode to an operation that is registered in the
    ghost history. Persistent, as [ws_prot] must be. *)
Definition smoke_prot (γh : history_names) (d : list u8) : iProp Σ :=
  ∃ ti : Input, ⌜decode d = Some ti⌝ ∗ is_op_cert γh (ti.1, OpInsert ti.2).

#[local] Instance smoke_prot_persistent γh d : Persistent (smoke_prot γh d).
Proof. apply _. Qed.

(** The one operation this peer ever performs: insert [a] into the empty
    document of type [t], as client [cl]'s clock-zero operation. *)
Definition smoke_input (cl : ClientId) (a : A) : IntegrateInput (A := A) :=
  MkIntegrateInput (A := A) None None a (MkYjsId cl 0).

Definition smoke_item (cl : ClientId) (a : A) : YjsItem A :=
  Item (A := A) First Last (MkYjsId cl 0) a.

(** The send relation: that one message, and only onto an empty network. The
    emptiness condition is what makes the peer's operation anchor-free, so no
    delivery has to happen before it can be minted. *)
Definition smoke_may (cl : ClientId) (t : TId) (a : A)
    (M : gmap (chan_id * nat) (list u8)) (c : chan_id) (d : list u8) : Prop :=
  M = ∅ /\ d = encode (t, smoke_input cl a).

(** Coherence: before the peer has said anything its history is empty, which is
    what lets [history_broadcast] apply against the empty document. Afterwards
    nothing more is claimed, since the peer has nothing left it may send. *)
Definition smoke_coh (γh : history_names) (cl : ClientId)
    (M : gmap (chan_id * nat) (list u8)) : iProp Σ :=
  (if bool_decide (M = ∅)
   then own_client_history γh cl ([] : list Ev)
   else ∃ h : list Ev, own_client_history γh cl h)%I.

(** The ghost state a run of this peer is carried out under. The three ws ghost
    names are whatever the network layer allocated; only the last four fields
    are this file's business. *)
Definition smoke_wsGS (γm γs γr : gname) (γh : history_names)
    (cl : ClientId) (t : TId) (a : A) : wsGS Σ :=
  WsGS Σ _ _ γm γs γr (smoke_prot γh) (smoke_prot_persistent γh)
       (smoke_coh γh cl) (smoke_may cl t a).

(** The pure premises of [history_broadcast] at the empty document. Lifted
    verbatim from [history_smoke]: an insert with no origins into an empty
    array is valid, maximal, and integrates. *)
Lemma smoke_broadcast_premises (cl : ClientId) (t : TId) (a : A) :
  toItem (smoke_input cl a) (doc_model_get (∅ : DocM) t)
    = Some (smoke_item cl a) /\
  IsItemValid (smoke_item cl a) /\
  maximalId (smoke_item cl a) (doc_model_get (∅ : DocM) t) /\
  integrate (smoke_input cl a) (doc_model_get (∅ : DocM) t)
    = Some [smoke_item cl a] /\
  (forall (t' : TId) (x : YjsItem A),
     x ∈ doc_model_get (∅ : DocM) t' ->
     clientId (item_id x) = cl -> (clock (item_id x) < 0)%nat).
Proof.
  have Hnilget : forall t' : TId,
      doc_model_get (∅ : DocM) t' = []
    by move=> t'; rewrite /doc_model_get lookup_empty.
  split_and!.
  - rewrite Hnilget //.
  - split.
    + apply YjsLt'_ltOriginOrder. exact lt_first_last.
    + move=> x Hx.
      inversion Hx as [x0 y0 Hstep | x0 y0 z0 Hstep Hreach]; subst.
      * inversion Hstep; subst; [left | right]; exists 0%nat; exact (leqSame _ _).
      * inversion Hstep; subst;
          inversion Hreach as [x1 y1 Hstep2 | x1 y1 z1 Hstep2 ?]; subst;
          inversion Hstep2.
  - rewrite Hnilget. move=> x Hx. exfalso.
    move: Hx. rewrite /ArrSet /= elem_of_nil //.
  - rewrite Hnilget. vm_compute. done.
  - move=> t' x Hx. exfalso. move: Hx. rewrite Hnilget elem_of_nil //.
Qed.

(** The obligation holds for this peer. *)
Lemma smoke_ws_env_preserves (γm γs γr : gname) (γh : history_names)
    (cl : ClientId) (t : TId) (a : A) (E : coPset) :
  ↑histN ⊆ E ->
  is_history (A := A) (P := P) γh -∗
    @ws_env_preserves Σ (smoke_wsGS γm γs γr γh cl t a) _ E.
Proof.
  iIntros (HE) "#Hinv".
  iModIntro. iIntros (g r n data) "%Hmay %Hext _ Hcoh".
  destruct Hmay as [Hempty ->].
  (* nothing on the wire at all, so nothing from the environment either *)
  have Henv : env_msgs g = ∅.
  { rewrite /env_msgs Hempty map_filter_empty //. }
  rewrite /smoke_wsGS /= Henv.
  iEval (rewrite /smoke_coh bool_decide_eq_true_2 //) in "Hcoh".
  have [Htoitem [Hvalid [Hmax [Hint Hbound]]]] := smoke_broadcast_premises cl t a.
  iMod (history_broadcast γh cl 0%nat [] ∅ t [smoke_item cl a]
          (smoke_input cl a) (smoke_item cl a) E HE
          Htoitem Hvalid Hmax eq_refl Hbound Hint history_state_coh_nil
          with "Hinv Hcoh") as "(Hown & _ & #Hcert & _)".
  iModIntro. iSplitL "Hown".
  - (* the wire is no longer empty, so the weaker branch is what is owed *)
    rewrite /smoke_coh bool_decide_eq_false_2; last by apply insert_non_empty.
    by iExists _.
  - rewrite /smoke_prot. iExists (t, smoke_input cl a).
    rewrite decode_encode. by iFrame "Hcert".
Qed.

(** Non-vacuity, in one statement: a history exists, the obligation holds over
    it, and the send relation permits something. *)
Lemma smoke_env_nonvacuous (γm γs γr : gname)
    (cl : ClientId) (t : TId) (a : A) (c : chan_id) (E : coPset) :
  ↑histN ⊆ E ->
  ⊢ |={E}=> ∃ γh : history_names,
      is_history (A := A) (P := P) γh ∗
      @ws_env_preserves Σ (smoke_wsGS γm γs γr γh cl t a) _ E ∗
      ⌜smoke_may cl t a ∅ c (encode (t, smoke_input cl a))⌝.
Proof.
  iIntros (HE).
  iMod (history_alloc (A := A) (P := P) {[ cl ]} E) as (γh) "[#Hinv _]".
  iModIntro. iExists γh. iFrame "Hinv".
  iSplitL; last done.
  by iApply smoke_ws_env_preserves.
Qed.

End smoke.
