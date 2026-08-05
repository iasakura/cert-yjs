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
    - [ws_prot] of that data is the real thing a receiver needs, one point of
      the global history per character ([is_pending_certified] over
      [expand_inputs]), which is exactly what
      [wp_store__applyUpdate_certs] consumes;
    - [ws_env_preserves] holds, by the same [history_broadcast] a modeled sender
      would use at [wp_WsSendOp].

    Ghost only: no goose, no program, no WP. This is the ws analogue of
    [history_smoke] in history.v, and it reuses that lemma's side conditions
    verbatim.

    Three peers, each doing one more of what a real one does.

    - [smoke_ws_env_preserves] speaks into an empty network and never looks at
      what is on the wire, so it exercises [history_broadcast] alone.
    - [relay_ws_env_preserves] takes in an operation another client put on the
      wire, reading its certificate out of the obligation's hypothesis, and
      runs [history_deliver_pending] before minting its own. That is the
      two-step argument. Its own operation is still anchor-free, and it inserts
      into another type, so it still broadcasts against an empty array.
    - [anchor_ws_env_preserves] anchors its operation at the one it took in,
      and so integrates against a document that holds it. This is the shape a
      Yjs client actually has: what it says next points at what was said to
      it.

    What is still small about all three is the size of [ws_may]: each peer may
    send one message, once. A realistic client is the same construction with a
    send relation that admits a stream, and [ws_env_coh] carrying its whole
    document rather than a token. *)
From New.proof Require Import proof_prelude.
From New.golang Require Import theory.
From New.proof Require Export core.
From New.proof Require Export network_model.
From New.proof Require Export history.
From New.proof.item Require Import run_theory model.
From New.proof.store Require Import model.
From New.goose_lang.ffi.ws_ffi Require Import ws_ffi.

Section smoke.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!wsGS Σ}.

Set Default Proof Using "Type*".

(** The content type is the store's, since the protocol has to be the one
    [wp_store__applyUpdate_certs] consumes. *)
Notation A := go_string.
Notation P := go_string.

Local Notation TId := (TypeId P).
Local Notation Input := (TId * IntegrateInput (A := A))%type.
Local Notation Ev := (@Event (TId * @YjsOperation A)).
Local Notation DocM := (gmap TId (list (YjsItem A))).

(** The codec is a parameter: which bytes stand for which operation is the
    application's business, and nothing here depends on the choice beyond
    being able to read one back. *)
Context (encode : list Input -> list u8).
Context (decode : list u8 -> option (list Input)).
Hypothesis decode_encode : forall x, decode (encode x) = Some x.

(** The protocol: these bytes decode to operations every one of which is a
    point of the global history [γh]. Per character, via [expand_inputs],
    because that is what the ghost history holds and what
    [wp_store__applyUpdate_certs] consumes: a multi-character wire item's
    head-id operation is not itself in the log, only its per-character ones
    are. Persistent, as [ws_prot] must be. *)
Definition smoke_prot (γh : history_names) (d : list u8) : iProp Σ :=
  ∃ inputs : list Input, ⌜decode d = Some inputs⌝ ∗
    is_pending_certified γh (expand_inputs inputs).

#[local] Instance smoke_prot_persistent γh d : Persistent (smoke_prot γh d).
Proof. apply _. Qed.

(** The one operation this peer ever performs: insert [a] into the empty
    document of type [t], as client [cl]'s clock-zero operation. *)
Definition smoke_input (cl : ClientId) (b : w8) : IntegrateInput (A := A) :=
  MkIntegrateInput (A := A) None None [b] (MkYjsId cl 0).

Definition smoke_item (cl : ClientId) (b : w8) : YjsItem A :=
  Item (A := A) First Last (MkYjsId cl 0) [b].

(** One character, so the per-character expansion is the operation itself.
    This is what lets a one-operation message's protocol be one certificate. *)
Lemma expand_inputs_smoke (t : TId) (cl : ClientId) (b : w8) :
  expand_inputs [(t, smoke_input cl b)] = [(t, smoke_input cl b)].
Proof. rewrite /expand_inputs /expand_input /ops_of_input /explode //=. Qed.

(** The send relation: that one message, and only onto an empty network. The
    emptiness condition is what makes the peer's operation anchor-free, so no
    delivery has to happen before it can be minted. *)
Definition smoke_may (cl : ClientId) (t : TId) (a : w8)
    (M : gmap (chan_id * nat) (list u8)) (c : chan_id) (d : list u8) : Prop :=
  M = ∅ /\ d = encode [(t, smoke_input cl a)].

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
    (cl : ClientId) (t : TId) (a : w8) : wsGS Σ :=
  WsGS Σ _ _ γm γs γr (smoke_prot γh) (smoke_prot_persistent γh)
       (smoke_coh γh cl) (smoke_may cl t a).

(** The pure premises of [history_broadcast] against an empty array. Lifted
    verbatim from [history_smoke]: an insert with no origins into an empty
    array is valid, maximal, and integrates. Stated over the array rather than
    over the empty document, because the peer below broadcasts into a document
    that is not empty, only empty at the type it is inserting into. *)
Lemma smoke_premises_nil (cl : ClientId) (a : w8) :
  toItem (smoke_input cl a) [] = Some (smoke_item cl a) /\
  IsItemValid (smoke_item cl a) /\
  maximalId (smoke_item cl a) [] /\
  integrate (smoke_input cl a) [] = Some [smoke_item cl a].
Proof.
  split_and!.
  - done.
  - split.
    + apply YjsLt'_ltOriginOrder. exact lt_first_last.
    + move=> x Hx.
      inversion Hx as [x0 y0 Hstep | x0 y0 z0 Hstep Hreach]; subst.
      * inversion Hstep; subst; [left | right]; exists 0%nat; exact (leqSame _ _).
      * inversion Hstep; subst;
          inversion Hreach as [x1 y1 Hstep2 | x1 y1 z1 Hstep2 ?]; subst;
          inversion Hstep2.
  - move=> x Hx. exfalso. move: Hx. rewrite /ArrSet /= elem_of_nil //.
  - vm_compute. done.
Qed.

Lemma smoke_nilget (t' : TId) : doc_model_get (∅ : DocM) t' = [].
Proof. rewrite /doc_model_get lookup_empty //. Qed.

Lemma smoke_broadcast_premises (cl : ClientId) (t : TId) (a : w8) :
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
  have [H1 [H2 [H3 H4]]] := smoke_premises_nil cl a.
  rewrite !smoke_nilget. split_and!; try done.
Qed.

(** The obligation holds for this peer. *)
Lemma smoke_ws_env_preserves (γm γs γr : gname) (γh : history_names)
    (cl : ClientId) (t : TId) (a : w8) (E : coPset) :
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
  - rewrite /smoke_prot. iExists [(t, smoke_input cl a)].
    iSplitR; first by rewrite decode_encode.
    rewrite expand_inputs_smoke /is_pending_certified big_sepL_singleton.
    by iFrame "Hcert".
Qed.

(** Non-vacuity, in one statement: a history exists, the obligation holds over
    it, and the send relation permits something. *)
Lemma smoke_env_nonvacuous (γm γs γr : gname)
    (cl : ClientId) (t : TId) (a : w8) (c : chan_id) (E : coPset) :
  ↑histN ⊆ E ->
  ⊢ |={E}=> ∃ γh : history_names,
      is_history (A := A) (P := P) γh ∗
      @ws_env_preserves Σ (smoke_wsGS γm γs γr γh cl t a) _ E ∗
      ⌜smoke_may cl t a ∅ c (encode [(t, smoke_input cl a)])⌝.
Proof.
  iIntros (HE).
  iMod (history_alloc (A := A) (P := P) {[ cl ]} E) as (γh) "[#Hinv _]".
  iModIntro. iExists γh. iFrame "Hinv".
  iSplitL; last done.
  by iApply smoke_ws_env_preserves.
Qed.

(** ** A peer that takes something in before it speaks

    The peer above never looks at what is already on the wire, so it never runs
    [history_deliver_pending] and never touches the protocol facts
    [ws_env_preserves] hands it. This one does. The wire carries one operation
    of another client; the peer delivers that into its own ghost history, using
    the certificate the hypothesis carries, and only then mints its own.

    Two choices keep the pure side conditions the same as above. The operation
    the peer takes in belongs to a different client, which makes [maximalId]
    and the freshness bound vacuous. And the peer inserts into a different
    type, so it still broadcasts against an empty array. Anchoring at an
    operation it received is the next step, and that one needs the theory of
    [toItem] and [integrate] at a non-empty array. *)

Definition relay_may (cl clX : ClientId) (t t2 : TId) (aX aY : w8)
    (k : chan_id * nat)
    (M : gmap (chan_id * nat) (list u8)) (c : chan_id) (d : list u8) : Prop :=
  M = {[ k := encode [(t, smoke_input clX aX)] ]} /\
  d = encode [(t2, smoke_input cl aY)].

Definition relay_coh (γh : history_names) (cl : ClientId)
    (k : chan_id * nat) (msg : list u8)
    (M : gmap (chan_id * nat) (list u8)) : iProp Σ :=
  (if bool_decide (M = ∅ \/ M = {[ k := msg ]})
   then own_client_history γh cl ([] : list Ev)
   else ∃ h : list Ev, own_client_history γh cl h)%I.

Lemma relay_coh_open γh cl k msg M :
  M = ∅ \/ M = {[ k := msg ]} ->
  relay_coh γh cl k msg M -∗ own_client_history γh cl ([] : list Ev).
Proof. intros HM. rewrite /relay_coh bool_decide_eq_true_2 //. by iIntros "$". Qed.

Lemma relay_coh_close γh cl k msg M (h : list Ev) :
  ¬ (M = ∅ \/ M = {[ k := msg ]}) ->
  own_client_history γh cl h -∗ relay_coh γh cl k msg M.
Proof.
  intros HM. rewrite /relay_coh bool_decide_eq_false_2 //.
  iIntros "H". by iExists h.
Qed.

Definition relay_wsGS (γm γs γr : gname) (γh : history_names)
    (cl clX : ClientId) (t t2 : TId) (aX aY : w8) (k : chan_id * nat) : wsGS Σ :=
  WsGS Σ _ _ γm γs γr (smoke_prot γh) (smoke_prot_persistent γh)
       (relay_coh γh cl k (encode [(t, smoke_input clX aX)]))
       (relay_may cl clX t t2 aX aY k).

(** Draining the one operation the wire carries into an empty document. Same
    computation as [history_smoke]'s. *)
Lemma relay_deliver_drain (clX : ClientId) (t : TId) (aX : w8) :
  pending_drain (∅ : DocM) [(t, smoke_input clX aX)]
    = ([(t, smoke_input clX aX)], [],
       <[t := [smoke_item clX aX]]> (∅ : DocM)).
Proof.
  have [_ [_ [_ Hint]]] := smoke_premises_nil clX aX.
  have Hdmh : doc_model_has (∅ : DocM) (in_id (smoke_input clX aX)) = false.
  { rewrite /doc_model_has map_to_list_empty //. }
  rewrite /pending_drain /= Hdmh /= smoke_nilget Hint //=.
Qed.

Lemma relay_ws_env_preserves (γm γs γr : gname) (γh : history_names)
    (cl clX : ClientId) (t t2 : TId) (aX aY : w8) (k : chan_id * nat)
    (E : coPset) :
  ↑histN ⊆ E ->
  cl ≠ clX ->
  t2 ≠ t ->
  is_history (A := A) (P := P) γh -∗
    @ws_env_preserves Σ (relay_wsGS γm γs γr γh cl clX t t2 aX aY k) _ E.
Proof.
  iIntros (HE Hne Hnt) "#Hinv".
  iModIntro. iIntros (g r n data) "%Hmay %Hext #Hwire Hcoh".
  destruct Hmay as [Hw ->].
  rewrite /relay_wsGS /=.
  (* the environment's view is a sub-map of the one message on the wire *)
  have Henv : env_msgs g = ∅ \/
              env_msgs g = {[ k := encode [(t, smoke_input clX aX)] ]}.
  { rewrite /env_msgs Hw map_filter_singleton.
    case_decide; [by right | by left]. }
  iDestruct (relay_coh_open with "Hcoh") as "Hcoh"; first exact Henv.
  (* the certificate for what is on the wire comes from the hypothesis *)
  iAssert (is_op_cert γh (t, OpInsert (smoke_input clX aX))) as "#HcertX".
  { rewrite Hw big_sepM_singleton.
    iDestruct "Hwire" as (inputs) "[%Hd Hc]".
    rewrite decode_encode in Hd. injection Hd as <-.
    rewrite expand_inputs_smoke /is_pending_certified big_sepL_singleton.
    iApply "Hc". }
  (* deliver it, then mint *)
  iMod (history_deliver_pending γh cl [] ∅ [(t, smoke_input clX aX)]
          [(t, smoke_input clX aX)] [] (<[t := [smoke_item clX aX]]> (∅ : DocM))
          E HE (relay_deliver_drain clX t aX) history_state_coh_nil
          with "Hinv Hcoh []") as "(Hcoh & _ & _ & %Hcoh2 & _)".
  { rewrite /is_pending_certified big_sepL_singleton. iApply "HcertX". }
  have Hget2 : doc_model_get (<[t := [smoke_item clX aX]]> (∅ : DocM)) t2 = [].
  { rewrite docm_get_insert_ne // smoke_nilget //. }
  have [Htoitem [Hvalid [Hmax Hint]]] := smoke_premises_nil cl aY.
  rewrite -Hget2 in Htoitem Hmax Hint.
  have Hbound : forall (t' : TId) (x : YjsItem A),
      x ∈ doc_model_get (<[t := [smoke_item clX aX]]> (∅ : DocM)) t' ->
      clientId (item_id x) = cl -> (clock (item_id x) < 0)%nat.
  { move=> t' x Hx Hcid. exfalso.
    destruct (decide (t' = t)) as [->|Hne'].
    - move: Hx. rewrite docm_get_insert_eq list_elem_of_singleton => Hxeq.
      subst x. rewrite /smoke_item /= in Hcid. by apply Hne.
    - move: Hx. rewrite docm_get_insert_ne // smoke_nilget elem_of_nil //. }
  iMod (history_broadcast γh cl 0%nat _ _ t2 _
          (smoke_input cl aY) (smoke_item cl aY) E HE
          Htoitem Hvalid Hmax eq_refl Hbound Hint Hcoh2
          with "Hinv Hcoh") as "(Hown & _ & #Hcert & _)".
  iModIntro. iSplitL "Hown".
  - iApply (relay_coh_close with "Hown").
    (* the peer's own message is now on the wire, and it is not the other
       client's, so neither branch of the strong case applies *)
    move=> [Hc | Hc].
    + apply (f_equal (lookup (r, n))) in Hc.
      rewrite lookup_insert_eq lookup_empty in Hc. discriminate.
    + have Hd : encode [(t2, smoke_input cl aY)]
                  = encode [(t, smoke_input clX aX)].
      { apply (f_equal (lookup (r, n))) in Hc.
        rewrite lookup_insert_eq in Hc.
        destruct (decide ((r, n) = k)) as [Heq|Hk].
        - rewrite Heq lookup_singleton_eq in Hc. by injection Hc.
        - rewrite lookup_singleton_ne in Hc; [ discriminate | done ]. }
      (* the peer inserts into a different type than the message it took in *)
      have := f_equal decode Hd. rewrite !decode_encode.
      move=> [=] Ht *. exact (Hnt Ht).
  - rewrite /smoke_prot. iExists [(t2, smoke_input cl aY)].
    iSplitR; first by rewrite decode_encode.
    rewrite expand_inputs_smoke /is_pending_certified big_sepL_singleton.
    by iFrame "Hcert".
Qed.

(** ** A peer whose operation is anchored at one it took in

    The last thing the two peers above avoid: their own operation has no
    origins, so it integrates against an empty array whatever the document
    holds. A real Yjs client's next operation points at one the server relayed
    to it. Here it does. *)

Definition anchor_input (cl clX : ClientId) (b : w8) : IntegrateInput (A := A) :=
  MkIntegrateInput (A := A) (Some (MkYjsId clX 0)) None [b] (MkYjsId cl 0).

Definition anchor_item (cl clX : ClientId) (bX b : w8) : YjsItem A :=
  Item (A := A) (itemPtr (smoke_item clX bX)) Last (MkYjsId cl 0) [b].

Lemma expand_inputs_anchor (t : TId) (cl clX : ClientId) (b : w8) :
  expand_inputs [(t, anchor_input cl clX b)] = [(t, anchor_input cl clX b)].
Proof. rewrite /expand_inputs /expand_input /ops_of_input /explode //=. Qed.

Lemma anchor_toItem (cl clX : ClientId) (bX b : w8) :
  toItem (anchor_input cl clX b) [smoke_item clX bX]
    = Some (anchor_item cl clX bX b).
Proof.
  rewrite /toItem /anchor_input /anchor_item /find_by_id /smoke_item /=.
  rewrite decide_True //.
Qed.

Lemma anchor_integrate (cl clX : ClientId) (bX b : w8) :
  integrate (anchor_input cl clX b) [smoke_item clX bX]
    = Some [smoke_item clX bX; anchor_item cl clX bX b].
Proof.
  rewrite /integrate /anchor_input /anchor_item /smoke_item /=.
  rewrite decide_True //.
Qed.

Lemma anchor_valid (cl clX : ClientId) (bX b : w8) :
  IsItemValid (anchor_item cl clX bX b).
Proof.
  split.
  - apply YjsLt'_ltOriginOrder. apply lt_last.
  - move=> x Hx.
    inversion Hx as [x0 y0 Hstep | x0 y0 z0 Hstep Hreach]; subst.
    + (* one step out of the new item: its own two origins *)
      inversion Hstep; subst; [left | right]; exists 0%nat; exact (leqSame _ _).
    + inversion Hstep; subst.
      * (* through the item it is anchored at, whose origins are First and Last *)
        inversion Hreach as [x1 y1 Hstep2 | x1 y1 z1 Hstep2 Hreach2]; subst.
        -- inversion Hstep2; subst.
           ++ left. apply YjsLeq'_leqLt, YjsLt'_ltOriginOrder, lt_first.
           ++ right. exists 0%nat. exact (leqSame _ _).
        -- inversion Hstep2; subst;
             inversion Hreach2 as [? ? Hs3 | ? ? ? Hs3 ?]; subst; inversion Hs3.
      * (* nothing is reachable out of [Last] *)
        inversion Hreach as [? ? Hs2 | ? ? ? Hs2 ?]; subst; inversion Hs2.
Qed.

Lemma anchor_maximal (cl clX : ClientId) (bX b : w8) :
  cl ≠ clX ->
  maximalId (anchor_item cl clX bX b) [smoke_item clX bX].
Proof.
  move=> Hne x Hx Hcid. exfalso.
  move: Hx. rewrite /ArrSet /= list_elem_of_singleton => Hxeq.
  subst x. rewrite /smoke_item /anchor_item /= in Hcid. by apply Hne.
Qed.

Definition anchor_may (cl clX : ClientId) (t : TId) (bX bY : w8)
    (k : chan_id * nat)
    (M : gmap (chan_id * nat) (list u8)) (c : chan_id) (d : list u8) : Prop :=
  M = {[ k := encode [(t, smoke_input clX bX)] ]} /\
  d = encode [(t, anchor_input cl clX bY)].

Definition anchor_wsGS (γm γs γr : gname) (γh : history_names)
    (cl clX : ClientId) (t : TId) (bX bY : w8) (k : chan_id * nat) : wsGS Σ :=
  WsGS Σ _ _ γm γs γr (smoke_prot γh) (smoke_prot_persistent γh)
       (relay_coh γh cl k (encode [(t, smoke_input clX bX)]))
       (anchor_may cl clX t bX bY k).

Lemma anchor_ws_env_preserves (γm γs γr : gname) (γh : history_names)
    (cl clX : ClientId) (t : TId) (bX bY : w8) (k : chan_id * nat)
    (E : coPset) :
  ↑histN ⊆ E ->
  cl ≠ clX ->
  is_history (A := A) (P := P) γh -∗
    @ws_env_preserves Σ (anchor_wsGS γm γs γr γh cl clX t bX bY k) _ E.
Proof.
  iIntros (HE Hne) "#Hinv".
  iModIntro. iIntros (g r n data) "%Hmay %Hext #Hwire Hcoh".
  destruct Hmay as [Hw ->].
  rewrite /anchor_wsGS /=.
  have Henv : env_msgs g = ∅ \/
              env_msgs g = {[ k := encode [(t, smoke_input clX bX)] ]}.
  { rewrite /env_msgs Hw map_filter_singleton.
    case_decide; [by right | by left]. }
  iDestruct (relay_coh_open with "Hcoh") as "Hcoh"; first exact Henv.
  iAssert (is_op_cert γh (t, OpInsert (smoke_input clX bX))) as "#HcertX".
  { rewrite Hw big_sepM_singleton.
    iDestruct "Hwire" as (inputs) "[%Hd Hc]".
    rewrite decode_encode in Hd. injection Hd as <-.
    rewrite expand_inputs_smoke /is_pending_certified big_sepL_singleton.
    iApply "Hc". }
  iMod (history_deliver_pending γh cl [] ∅ [(t, smoke_input clX bX)]
          [(t, smoke_input clX bX)] [] (<[t := [smoke_item clX bX]]> (∅ : DocM))
          E HE (relay_deliver_drain clX t bX) history_state_coh_nil
          with "Hinv Hcoh []") as "(Hcoh & _ & _ & %Hcoh2 & _)".
  { rewrite /is_pending_certified big_sepL_singleton. iApply "HcertX". }
  (* now the peer's document at [t] holds the operation it took in, and its own
     operation points at it *)
  have Hgett : doc_model_get (<[t := [smoke_item clX bX]]> (∅ : DocM)) t
                 = [smoke_item clX bX] by rewrite docm_get_insert_eq.
  have Htoitem := anchor_toItem cl clX bX bY.
  have Hvalid := anchor_valid cl clX bX bY.
  have Hmax := anchor_maximal cl clX bX bY Hne.
  have Hint := anchor_integrate cl clX bX bY.
  rewrite -Hgett in Htoitem Hmax Hint.
  have Hbound : forall (t' : TId) (x : YjsItem A),
      x ∈ doc_model_get (<[t := [smoke_item clX bX]]> (∅ : DocM)) t' ->
      clientId (item_id x) = cl -> (clock (item_id x) < 0)%nat.
  { move=> t' x Hx Hcid. exfalso.
    destruct (decide (t' = t)) as [->|Hne'].
    - move: Hx. rewrite Hgett list_elem_of_singleton => Hxeq.
      subst x. rewrite /smoke_item /= in Hcid. by apply Hne.
    - move: Hx. rewrite docm_get_insert_ne // smoke_nilget elem_of_nil //. }
  iMod (history_broadcast γh cl 0%nat _ _ t _
          (anchor_input cl clX bY) (anchor_item cl clX bX bY) E HE
          Htoitem Hvalid Hmax eq_refl Hbound Hint Hcoh2
          with "Hinv Hcoh") as "(Hown & _ & #Hcert & _)".
  iModIntro. iSplitL "Hown".
  - iApply (relay_coh_close with "Hown").
    move=> [Hc | Hc].
    + apply (f_equal (lookup (r, n))) in Hc.
      rewrite lookup_insert_eq lookup_empty in Hc. discriminate.
    + have Hd : encode [(t, anchor_input cl clX bY)]
                  = encode [(t, smoke_input clX bX)].
      { apply (f_equal (lookup (r, n))) in Hc.
        rewrite lookup_insert_eq in Hc.
        destruct (decide ((r, n) = k)) as [Heq|Hk].
        - rewrite Heq lookup_singleton_eq in Hc. by injection Hc.
        - rewrite lookup_singleton_ne in Hc; [ discriminate | done ]. }
      (* the two differ in whether the operation has an origin at all *)
      have := f_equal decode Hd. rewrite !decode_encode.
      rewrite /anchor_input /smoke_input. move=> [=] *. by [].
  - rewrite /smoke_prot. iExists [(t, anchor_input cl clX bY)].
    iSplitR; first by rewrite decode_encode.
    rewrite expand_inputs_anchor /is_pending_certified big_sepL_singleton.
    by iFrame "Hcert".
Qed.

End smoke.
