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

    Five peers, each doing one more of what a real one does.

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
    - [stream_ws_env_preserves] says an unbounded number of things rather than
      one: character [k] of what someone typed into it, anchored at character
      [k-1]. Its [ws_env_coh] is no longer a token recording whether the peer
      has spoken but the whole document it has built, related to its ghost
      history by [history_state_coh].
    - [full_ws_env_preserves] does both: it delivers what another client put
      on the wire into its own history, and then types without end. That is
      the shape a Yjs client on a relayed connection has.

    What is still small about the last one is where its characters go: into a
    different type than the operation it took in, which is what keeps the
    array it types into the empty-based one [stream_step] describes. A peer
    typing into the same list it received into is
    [anchor_ws_env_preserves]'s document with a stream on top of it, and that
    wants [stream_ok] over a base array rather than over the empty one. *)
From New.proof Require Import proof_prelude.
From New.golang Require Import theory.
From New.proof Require Export core.
From New.proof Require Export network_model.
From New.proof Require Export history.
From New.proof.item Require Import run_theory model.
From New.proof.store Require Import model.
From New.proof.store Require Import store.
From New.proof Require Import yjs_prot.
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

(** The protocol: the deployment's [yjs_prot] at this file's codec (issue
    #107, W3b): the bytes decode to an HONEST batch ([update_wf]: the 2^64
    no-wrap seam and rootedness of head structs) every per-char operation of
    which is a point of the global history [γh]. The peers below discharge
    [ws_env_preserves] for THE protocol the verified server runs under,
    which is what makes the server's one assumption non-vacuous. *)
Definition smoke_prot (γh : history_names) (d : list u8) : iProp Σ :=
  yjs_prot decode γh d.

#[local] Instance smoke_prot_persistent (γh : history_names) (d : list u8) :
  Persistent (smoke_prot γh d).
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

(** Honesty of the peers' single-struct batches: tiny clocks make the no-wrap
    seam trivial, and an origin-less struct targets a named root (which is why
    the peers below insert at [RootId nm] rather than an arbitrary type). *)
Lemma smoke_input_wf (nm : P) (cl : ClientId) (b : w8) :
  update_wf [(RootId nm, smoke_input cl b)].
Proof.
  split; move=> x Hx; apply list_elem_of_singleton in Hx; subst x; simpl.
  - word.
  - rewrite /pending_item_rooted /=. by exists nm.
Qed.

(** The send relation: that one message, and only onto an empty network. The
    emptiness condition is what makes the peer's operation anchor-free, so no
    delivery has to happen before it can be minted. *)
Definition smoke_may (cl : ClientId) (nm : P) (a : w8)
    (M : gmap (chan_id * nat) (list u8)) (c : chan_id) (d : list u8) : Prop :=
  M = ∅ /\ d = encode [(RootId nm, smoke_input cl a)].

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
    (cl : ClientId) (nm : P) (a : w8) : wsGS Σ :=
  WsGS Σ _ _ γm γs γr (smoke_prot γh) (smoke_prot_persistent γh)
       (smoke_coh γh cl) (smoke_may cl nm a).

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
    (cl : ClientId) (nm : P) (a : w8) (E : coPset) :
  ↑histN ⊆ E ->
  is_history (A := A) (P := P) γh -∗
    @ws_env_preserves Σ (smoke_wsGS γm γs γr γh cl nm a) _ E.
Proof.
  iIntros (HE) "#Hinv".
  iModIntro. iIntros (g r n data) "%Hmay %Hext %Hwf %Hfresh _ Hcoh".
  destruct Hmay as [Hempty ->].
  (* nothing on the wire at all, so nothing from the environment either *)
  have Henv : env_msgs g = ∅.
  { rewrite /env_msgs Hempty map_filter_empty //. }
  rewrite /smoke_wsGS /= Henv.
  iEval (rewrite /smoke_coh bool_decide_eq_true_2 //) in "Hcoh".
  have [Htoitem [Hvalid [Hmax [Hint Hbound]]]] := smoke_broadcast_premises cl (RootId nm) a.
  iMod (history_broadcast γh cl 0%nat [] ∅ (RootId nm) [smoke_item cl a]
          (smoke_input cl a) (smoke_item cl a) E HE
          Htoitem Hvalid Hmax eq_refl Hbound Hint history_state_coh_nil
          with "Hinv Hcoh") as "(Hown & _ & #Hcert & _)".
  iModIntro. iSplitL "Hown".
  - (* the wire is no longer empty, so the weaker branch is what is owed *)
    rewrite /smoke_coh bool_decide_eq_false_2; last by apply insert_non_empty.
    by iExists _.
  - rewrite /smoke_prot /yjs_prot. iExists [(RootId nm, smoke_input cl a)].
    iSplitR; first by rewrite decode_encode.
    iSplitR; first by iPureIntro; apply smoke_input_wf.
    rewrite expand_inputs_smoke /is_pending_certified big_sepL_singleton.
    by iFrame "Hcert".
Qed.

(** Non-vacuity, in one statement: a history exists, the obligation holds over
    it, and the send relation permits something. *)
Lemma smoke_env_nonvacuous (γm γs γr : gname)
    (cl : ClientId) (nm : P) (a : w8) (c : chan_id) (E : coPset) :
  ↑histN ⊆ E ->
  ⊢ |={E}=> ∃ γh : history_names,
      is_history (A := A) (P := P) γh ∗
      @ws_env_preserves Σ (smoke_wsGS γm γs γr γh cl nm a) _ E ∗
      ⌜smoke_may cl nm a ∅ c (encode [(RootId nm, smoke_input cl a)])⌝.
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

Definition relay_may (cl clX : ClientId) (t : TId) (nm2 : P) (aX aY : w8)
    (k : chan_id * nat)
    (M : gmap (chan_id * nat) (list u8)) (c : chan_id) (d : list u8) : Prop :=
  M = {[ k := encode [(t, smoke_input clX aX)] ]} /\
  d = encode [(RootId nm2, smoke_input cl aY)].

Definition relay_coh (γh : history_names) (cl : ClientId)
    (k : chan_id * nat) (msg : list u8)
    (M : gmap (chan_id * nat) (list u8)) : iProp Σ :=
  (if bool_decide (M = ∅ \/ M = {[ k := msg ]})
   then own_client_history γh cl ([] : list Ev)
   else ∃ h : list Ev, own_client_history γh cl h)%I.

Lemma relay_coh_open (γh : history_names) (cl : ClientId) (k : chan_id * nat)
    (msg : list u8) (M : gmap (chan_id * nat) (list u8)) :
  M = ∅ \/ M = {[ k := msg ]} ->
  relay_coh γh cl k msg M -∗ own_client_history γh cl ([] : list Ev).
Proof. intros HM. rewrite /relay_coh bool_decide_eq_true_2 //. by iIntros "$". Qed.

Lemma relay_coh_close (γh : history_names) (cl : ClientId) (k : chan_id * nat)
    (msg : list u8) (M : gmap (chan_id * nat) (list u8)) (h : list Ev) :
  ¬ (M = ∅ \/ M = {[ k := msg ]}) ->
  own_client_history γh cl h -∗ relay_coh γh cl k msg M.
Proof.
  intros HM. rewrite /relay_coh bool_decide_eq_false_2 //.
  iIntros "H". by iExists h.
Qed.

Definition relay_wsGS (γm γs γr : gname) (γh : history_names)
    (cl clX : ClientId) (t : TId) (nm2 : P) (aX aY : w8) (k : chan_id * nat) : wsGS Σ :=
  WsGS Σ _ _ γm γs γr (smoke_prot γh) (smoke_prot_persistent γh)
       (relay_coh γh cl k (encode [(t, smoke_input clX aX)]))
       (relay_may cl clX t nm2 aX aY k).

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
    (cl clX : ClientId) (t : TId) (nm2 : P) (aX aY : w8) (k : chan_id * nat)
    (E : coPset) :
  ↑histN ⊆ E ->
  cl ≠ clX ->
  RootId nm2 ≠ t ->
  is_history (A := A) (P := P) γh -∗
    @ws_env_preserves Σ (relay_wsGS γm γs γr γh cl clX t nm2 aX aY k) _ E.
Proof.
  iIntros (HE Hne Hnt) "#Hinv".
  iModIntro. iIntros (g r n data) "%Hmay %Hext %Hwf %Hfresh #Hwire Hcoh".
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
    iDestruct "Hwire" as (inputs) "(%Hd & %Hwfw & Hc)".
    rewrite decode_encode in Hd. injection Hd as <-.
    rewrite expand_inputs_smoke /is_pending_certified big_sepL_singleton.
    iApply "Hc". }
  (* deliver it, then mint *)
  iMod (history_deliver_pending γh cl [] ∅ [(t, smoke_input clX aX)]
          [(t, smoke_input clX aX)] [] (<[t := [smoke_item clX aX]]> (∅ : DocM))
          E HE (relay_deliver_drain clX t aX) history_state_coh_nil
          with "Hinv Hcoh []") as "(Hcoh & _ & _ & %Hcoh2 & _)".
  { rewrite /is_pending_certified big_sepL_singleton. iApply "HcertX". }
  have Hget2 : doc_model_get (<[t := [smoke_item clX aX]]> (∅ : DocM)) (RootId nm2) = [].
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
  iMod (history_broadcast γh cl 0%nat _ _ (RootId nm2) _
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
    + have Hd : encode [(RootId nm2, smoke_input cl aY)]
                  = encode [(t, smoke_input clX aX)].
      { apply (f_equal (lookup (r, n))) in Hc.
        rewrite lookup_insert_eq in Hc.
        destruct (decide ((r, n) = k)) as [Heq|Hk].
        - rewrite Heq lookup_singleton_eq in Hc. by injection Hc.
        - rewrite lookup_singleton_ne in Hc; [ discriminate | done ]. }
      (* the peer inserts into a different type than the message it took in *)
      have := f_equal decode Hd. rewrite !decode_encode.
      move=> [=] Ht *. exact (Hnt Ht).
  - rewrite /smoke_prot /yjs_prot. iExists [(RootId nm2, smoke_input cl aY)].
    iSplitR; first by rewrite decode_encode.
    iSplitR; first by iPureIntro; apply smoke_input_wf.
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

Lemma anchor_input_wf (t : TId) (cl clX : ClientId) (b : w8) :
  update_wf [(t, anchor_input cl clX b)].
Proof.
  split; move=> x Hx; apply list_elem_of_singleton in Hx; subst x; simpl.
  - word.
  - rewrite /pending_item_rooted /=. done.
Qed.


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
  iModIntro. iIntros (g r n data) "%Hmay %Hext %Hwf %Hfresh #Hwire Hcoh".
  destruct Hmay as [Hw ->].
  rewrite /anchor_wsGS /=.
  have Henv : env_msgs g = ∅ \/
              env_msgs g = {[ k := encode [(t, smoke_input clX bX)] ]}.
  { rewrite /env_msgs Hw map_filter_singleton.
    case_decide; [by right | by left]. }
  iDestruct (relay_coh_open with "Hcoh") as "Hcoh"; first exact Henv.
  iAssert (is_op_cert γh (t, OpInsert (smoke_input clX bX))) as "#HcertX".
  { rewrite Hw big_sepM_singleton.
    iDestruct "Hwire" as (inputs) "(%Hd & %Hwfw & Hc)".
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
  - rewrite /smoke_prot /yjs_prot. iExists [(t, anchor_input cl clX bY)].
    iSplitR; first by rewrite decode_encode.
    iSplitR; first by iPureIntro; apply anchor_input_wf.
    rewrite expand_inputs_anchor /is_pending_certified big_sepL_singleton.
    by iFrame "Hcert".
Qed.

(** ** A peer that keeps typing

    The three above each send once. This one sends a stream: character [k] is
    anchored at character [k-1], which is what a Yjs client does when someone
    types into it. Its state is no longer a token but its whole document, and
    [ws_env_coh] is the refinement relation between that document and its
    ghost history.

    The peer's state has to be a function of what it has put on the wire, since
    the wire is the only thing [ws_may] and [ws_env_coh] both see. Here that
    function is [stream_pos]: how many messages stand on the channel the peer
    owns. The obligation's emptiness hypothesis is what makes that count grow
    by one across the step; a peer that instead read its position off the index
    of the slot being filled would want the network's well-formedness too,
    which the obligation also carries. *)

Fixpoint stream_items (cl : ClientId) (prev : YjsPtr A) (k : nat) (bs : list w8)
    : list (YjsItem A) :=
  match bs with
  | [] => []
  | b :: rest =>
      let it := Item (A := A) prev Last (MkYjsId cl k) [b] in
      it :: stream_items cl (itemPtr it) (S k) rest
  end.

Definition stream_input (cl : ClientId) (k : nat) (b : w8)
    : IntegrateInput (A := A) :=
  MkIntegrateInput (A := A)
    (match k with O => None | S k' => Some (MkYjsId cl k') end)
    None [b] (MkYjsId cl k).

Lemma stream_items_length (cl : ClientId) (prev : YjsPtr A) (k : nat)
    (bs : list w8) :
  length (stream_items cl prev k bs) = length bs.
Proof. elim: bs prev k => [| b bs IH] prev k //=. by rewrite IH. Qed.

Lemma stream_input_wf (nm : P) (cl : ClientId) (k : nat) (b : w8) :
  (Z.of_nat k + 1 < 2^64)%Z ->
  update_wf [(RootId nm, stream_input cl k b)].
Proof.
  move=> Hk.
  split; move=> x Hx; apply list_elem_of_singleton in Hx; subst x; simpl.
  - word.
  - rewrite /pending_item_rooted.
    destruct k; simpl; [by exists nm | done].
Qed.


(** Growing at the end: the new character hangs off the last one, or off
    [prev] when there is none yet. *)
Fixpoint stream_last (cl : ClientId) (prev : YjsPtr A) (k : nat) (bs : list w8)
    : YjsPtr A :=
  match bs with
  | [] => prev
  | b :: rest =>
      stream_last cl (itemPtr (Item (A := A) prev Last (MkYjsId cl k) [b]))
        (S k) rest
  end.

Lemma stream_items_snoc (cl : ClientId) (prev : YjsPtr A) (k : nat)
    (bs : list w8) (b : w8) :
  stream_items cl prev k (bs ++ [b])
    = stream_items cl prev k bs
      ++ [Item (A := A) (stream_last cl prev k bs) Last
            (MkYjsId cl (k + length bs)) [b]].
Proof.
  elim: bs prev k => [| b0 bs IH] prev k /=.
  - rewrite Nat.add_0_r //.
  - rewrite IH Nat.add_succ_r //.
Qed.

Notation stream_doc cl bs := (stream_items cl First 0 bs).
Notation stream_tail cl bs := (stream_last cl First 0 bs).

Lemma stream_last_snoc (cl : ClientId) (prev : YjsPtr A) (k : nat)
    (bs : list w8) (b : w8) :
  stream_last cl prev k (bs ++ [b])
    = itemPtr (Item (A := A) (stream_last cl prev k bs) Last
                 (MkYjsId cl (k + length bs)) [b]).
Proof.
  elim: bs prev k => [| b0 bs IH] prev k /=.
  - rewrite Nat.add_0_r //.
  - rewrite IH Nat.add_succ_r //.
Qed.

(** What the peer's document satisfies at every point of the stream. Enough to
    take the next step and re-establish itself. *)
Record stream_ok (cl : ClientId) (bs : list w8) : Prop := {
  so_inv : YjsArrInvariant (stream_doc cl bs);
  so_ids : forall i it, stream_doc cl bs !! i = Some it ->
             item_id it = MkYjsId cl i;
  so_valid : forall z, z ∈ stream_doc cl bs -> IsItemValid z;
  so_nosucc : forall z, z ∈ stream_doc cl bs -> origin z ≠ stream_tail cl bs;
}.

Lemma YjsArrInvariant_nil : YjsArrInvariant ([] : list (YjsItem A)).
Proof.
  split.
  - split => //=; move=> o r id c; rewrite /ArrSet /= => /elem_of_nil [].
  - split; move=> *;
      match goal with
      | H : ArrSet [] _ |- _ => move: H; rewrite /ArrSet /= => /elem_of_nil []
      end.
  - by constructor.
  - by constructor.
Qed.

Lemma stream_ok_nil (cl : ClientId) : stream_ok cl [].
Proof.
  split; simpl.
  - exact YjsArrInvariant_nil.
  - by move=> [|i] it.
  - by move=> z /elem_of_nil.
  - by move=> z /elem_of_nil.
Qed.

(** The character typed after [bs]: it hangs off the last one, and nothing
    stands to its right. *)
Definition stream_item (cl : ClientId) (bs : list w8) (b : w8) : YjsItem A :=
  Item (A := A) (stream_tail cl bs) Last (MkYjsId cl (length bs)) [b].

Lemma stream_doc_snoc (cl : ClientId) (bs : list w8) (b : w8) :
  stream_doc cl (bs ++ [b]) = stream_doc cl bs ++ [stream_item cl bs b].
Proof. rewrite stream_items_snoc //. Qed.

Lemma stream_tail_snoc (cl : ClientId) (bs : list w8) (b : w8) :
  stream_tail cl (bs ++ [b]) = itemPtr (stream_item cl bs b).
Proof. rewrite stream_last_snoc //. Qed.

(** Where the tail points: at nothing, or at an item of the document. *)
Lemma stream_tail_elem (cl : ClientId) (bs : list w8) :
  stream_tail cl bs = First \/
  ∃ y, y ∈ stream_doc cl bs /\ stream_tail cl bs = itemPtr y.
Proof.
  elim/rev_ind: bs => [| b bs _]; first by left.
  right. exists (stream_item cl bs b). split; last exact (stream_tail_snoc cl bs b).
  rewrite stream_doc_snoc. apply elem_of_app. right. by apply list_elem_of_singleton.
Qed.

(** Ids read off membership rather than off a position. *)
Lemma stream_ok_id_elem (cl : ClientId) (bs : list w8) (y : YjsItem A) :
  stream_ok cl bs -> y ∈ stream_doc cl bs ->
  ∃ i, (i < length bs)%nat /\ item_id y = MkYjsId cl i.
Proof.
  move=> Hok Hy.
  destruct (list_elem_of_lookup_1 _ _ Hy) as [i Hi].
  exists i. split; last exact (so_ids _ _ Hok i y Hi).
  have := lookup_lt_Some _ _ _ Hi. by rewrite stream_items_length.
Qed.

(** The step, at the array level: the next character resolves to
    [stream_item], that item is valid and carries this client's largest clock,
    and integrating it appends it. *)
Lemma stream_step (cl : ClientId) (bs : list w8) (b : w8) :
  stream_ok cl bs ->
  toItem (stream_input cl (length bs) b) (stream_doc cl bs)
    = Some (stream_item cl bs b) /\
  IsItemValid (stream_item cl bs b) /\
  maximalId (stream_item cl bs b) (stream_doc cl bs) /\
  integrate (stream_input cl (length bs) b) (stream_doc cl bs)
    = Some (stream_doc cl (bs ++ [b])).
Proof.
  move: bs. elim/rev_ind => [| b0 bs _] Hok.
  - (* nothing typed yet, so the character is anchor-free *)
    have [H1 [H2 [H3 H4]]] := smoke_premises_nil cl b.
    rewrite /stream_item /stream_input /=.
    rewrite /smoke_input /smoke_item in H1 H2 H3 H4.
    split_and!; [exact H1 | exact H2 | exact H3 | exact H4].
  - (* anchored at the character before it *)
    set (x := stream_item cl bs b0).
    set (arr := stream_doc cl (bs ++ [b0])).
    have Harr : arr = stream_doc cl bs ++ [x] := stream_doc_snoc cl bs b0.
    have Hlenbs : length (stream_doc cl bs) = length bs := stream_items_length _ _ _ _.
    have Hlenarr : length arr = S (length bs).
    { rewrite Harr length_app Hlenbs /=. lia. }
    have Hj : arr !! length bs = Some x.
    { rewrite Harr lookup_app_r Hlenbs; last lia.
      by rewrite Nat.sub_diag. }
    have Hxin : x ∈ arr by apply (list_elem_of_lookup_2 _ _ _ Hj).
    have Hinv : YjsArrInvariant arr := so_inv _ _ Hok.
    have Hlenapp : length (bs ++ [b0]) = S (length bs)
      by rewrite length_app /=; lia.
    (* the input's origin is the id of the item at the end *)
    have Hoin : in_originId (stream_input cl (length (bs ++ [b0])) b)
                  = Some (item_id x).
    { rewrite Hlenapp /stream_input /stream_item //. }
    have Hri : findRightIdx (in_rightOriginId (stream_input cl (length (bs ++ [b0])) b))
                 arr = Some (Z.of_nat (length arr)) by [].
    have Hjr : (Z.of_nat (length bs) < Z.of_nat (length arr))%Z by lia.
    have Hnosucc : forall z, z ∈ arr -> origin z ≠ itemPtr x.
    { move=> z Hz. rewrite -(stream_tail_snoc cl bs b0).
      exact (so_nosucc _ _ Hok z Hz). }
    destruct (integrate_after_no_successor arr (length bs) x
                (stream_input cl (length (bs ++ [b0])) b) (Z.of_nat (length arr))
                Hinv Hj Hoin Hri Hjr Hnosucc) as (rptr & Hrptr & Hint).
    (* nothing stands to the right of the end, so the right origin is [Last] *)
    have Hlast : rptr = Last.
    { move: Hrptr. rewrite /getPtrExcept.
      destruct (decide (Z.of_nat (length arr) = -1)%Z); first lia.
      rewrite decide_True //. by move=> [=] <-. }
    subst rptr.
    have Hgoal : stream_item cl (bs ++ [b0]) b
                   = Item (A := A) (itemPtr x) Last
                       (in_id (stream_input cl (length (bs ++ [b0])) b))
                       (in_content (stream_input cl (length (bs ++ [b0])) b)).
    { rewrite /stream_item stream_tail_snoc //. }
    split_and!.
    + rewrite Hgoal.
      exact (toItem_resolved arr (length bs) x (Z.of_nat (length arr)) Last
               (stream_input cl (length (bs ++ [b0])) b) Hinv Hj Hoin Hri Hrptr).
    + (* the next link of a chain whose last item is valid *)
      rewrite Hgoal -/x.
      apply (chain_link_valid (ArrSet arr) x Last
               (in_id (stream_input cl (length (bs ++ [b0])) b))
               (in_content (stream_input cl (length (bs ++ [b0])) b))
               (yai_closed _ Hinv) (yai_item_set_inv _ Hinv)); [done | done |].
      exact (so_valid _ _ Hok x Hxin).
    + (* every id in the document is this client's, with a smaller clock *)
      move=> z Hz Hcid.
      have [i [Hi Hid]] := stream_ok_id_elem cl (bs ++ [b0]) z Hok Hz.
      rewrite Hid /stream_item /= Hlenapp. move: Hi. rewrite Hlenapp. lia.
    + rewrite Hint (stream_doc_snoc cl (bs ++ [b0]) b) Hgoal.
      rewrite take_ge; last lia.
      rewrite drop_ge; last lia.
      done.
Qed.

Lemma stream_ok_snoc (cl : ClientId) (bs : list w8) (b : w8) :
  stream_ok cl bs -> stream_ok cl (bs ++ [b]).
Proof.
  move=> Hok.
  have [Htoitem [Hvalid [Hmax Hint]]] := stream_step cl bs b Hok.
  have Hlenbs : length (stream_doc cl bs) = length bs := stream_items_length _ _ _ _.
  have Hinv : YjsArrInvariant (stream_doc cl (bs ++ [b])).
  { destruct (YjsArrInvariant_integrate (stream_input cl (length bs) b)
                (stream_doc cl bs) (stream_doc cl (bs ++ [b])) (stream_item cl bs b)
                (so_inv _ _ Hok) Htoitem Hvalid Hmax Hint) as (_ & _ & _ & H).
    exact H. }
  split; first exact Hinv.
  - (* the old ids, plus the new one at the end *)
    move=> i it. rewrite stream_doc_snoc.
    destruct (decide (i < length bs)%nat) as [Hlt | Hge].
    + rewrite lookup_app_l; last lia. exact (so_ids _ _ Hok i it).
    + rewrite lookup_app_r; last lia.
      destruct (i - length (stream_doc cl bs))%nat as [| k] eqn:Hk; last done.
      move=> [= <-]. rewrite /stream_item /=. f_equal. lia.
  - move=> z. rewrite stream_doc_snoc elem_of_app list_elem_of_singleton.
    move=> [Hz | ->]; [exact (so_valid _ _ Hok z Hz) | exact Hvalid].
  - (* nothing points at the new item: the old ones point inside the old
       document, and the new one points at the item before it *)
    have Hfresh : forall y, y ∈ stream_doc cl bs -> y ≠ stream_item cl bs b.
    { move=> y Hy Heq.
      have [i [Hi Hid]] := stream_ok_id_elem cl bs y Hok Hy.
      move: Hid. rewrite Heq /stream_item /= => [= Hclk]. lia. }
    move=> z. rewrite stream_tail_snoc stream_doc_snoc.
    rewrite elem_of_app list_elem_of_singleton => [[Hz | ->]].
    + move=> Horig. destruct z as [oz rz idz cz]. simpl in Horig. subst oz.
      have Hin : ArrSet (stream_doc cl bs) (itemPtr (stream_item cl bs b))
        := closedLeft _ (yai_closed _ (so_inv _ _ Hok)) _ _ _ _ Hz.
      simpl in Hin. exact (Hfresh _ Hin eq_refl).
    + (* the new item's own origin is the character before it *)
      rewrite /stream_item /=.
      case: (stream_tail_elem cl bs) => [Hnil | [y [Hy Hty]]]; first by rewrite Hnil.
      rewrite Hty. move=> [= Heq].
      have [i [Hi Hid]] := stream_ok_id_elem cl bs y Hok Hy.
      have Hidy := f_equal item_id Heq.
      move: Hidy. rewrite Hid /= => [= Hclk]. lia.
Qed.

(** So the peer's document is a well-formed Yjs array at every point of its
    stream, whatever it types. *)
Lemma stream_ok_all (cl : ClientId) (bs : list w8) : stream_ok cl bs.
Proof.
  elim/rev_ind: bs => [| b bs IH]; [exact (stream_ok_nil cl) | exact (stream_ok_snoc cl bs b IH)].
Qed.

(** One character per message, so again the per-character expansion is the
    operation itself. *)
Lemma expand_inputs_stream (t : TId) (cl : ClientId) (k : nat) (b : w8) :
  expand_inputs [(t, stream_input cl k b)] = [(t, stream_input cl k b)].
Proof. rewrite /expand_inputs /expand_input /ops_of_input /explode //=. Qed.

(** How far along the peer is: the messages it has put on the channel it owns.
    The wire is the only thing [ws_may] and [ws_env_coh] both see, so this is
    what the peer's position has to be read off. *)
Definition chan_msgs (c0 : chan_id) (M : gmap (chan_id * nat) (list u8))
    : gmap (chan_id * nat) (list u8) := filter (fun kv => kv.1.1 = c0) M.

Definition stream_pos (c0 : chan_id) (M : gmap (chan_id * nat) (list u8)) : nat :=
  size (chan_msgs c0 M).

Lemma stream_pos_empty (c0 : chan_id) : stream_pos c0 ∅ = 0%nat.
Proof. rewrite /stream_pos /chan_msgs map_filter_empty map_size_empty //. Qed.

Lemma stream_pos_insert (c0 : chan_id) (M : gmap (chan_id * nat) (list u8))
    (n : nat) (d : list u8) :
  M !! (c0, n) = None ->
  stream_pos c0 (<[(c0, n) := d]> M) = S (stream_pos c0 M).
Proof.
  move=> Hnone. rewrite /stream_pos /chan_msgs map_filter_insert_True //.
  apply map_size_insert_None. apply map_lookup_filter_None. by left.
Qed.

(** The channel the peer owns is one the environment feeds, so restricting to
    it does not care whether the whole wire or only the environment's part of
    it is in view. This is what lets [ws_may], which reads [ws_msgs], and
    [ws_env_coh], which is indexed by [env_msgs], agree on the position. *)
Lemma chan_msgs_env (g : ws_global_state) (c0 : chan_id) :
  c0 ∈ g.(ws_ext) -> chan_msgs c0 (env_msgs g) = chan_msgs c0 g.(ws_msgs).
Proof.
  move=> Hext. rewrite /chan_msgs /env_msgs.
  apply map_filter_filter_l. by move=> [c k] d _ /= ->.
Qed.

(** The peer's document, as a doc model: one type, holding what it typed. *)
Definition stream_docm (cl : ClientId) (t : TId) (bs : list w8) : DocM :=
  <[t := stream_doc cl bs]> (∅ : DocM).

Lemma stream_docm_get (cl : ClientId) (t t' : TId) (bs : list w8) :
  doc_model_get (stream_docm cl t bs) t'
    = if decide (t' = t) then stream_doc cl bs else [].
Proof.
  rewrite /stream_docm. case_decide as Ht.
  - rewrite Ht docm_get_insert_eq //.
  - rewrite docm_get_insert_ne // smoke_nilget //.
Qed.

(** The send relation: on the channel it owns, the peer may put the next
    character of its stream, for as long as its clock fits a word (the honest
    2^64 seam [update_wf] puts on the wire; a peer that has typed that much
    stops). Which character is its own business; where that character sits in
    the stream is not, and that is a function of the wire. *)
Definition stream_may (cl : ClientId) (nm : P) (c0 : chan_id)
    (M : gmap (chan_id * nat) (list u8)) (c : chan_id) (d : list u8) : Prop :=
  c = c0 /\ (Z.of_nat (stream_pos c0 M) + 1 < 2^64)%Z /\
  ∃ b : w8, d = encode [(RootId nm, stream_input cl (stream_pos c0 M) b)].

(** Coherence: the peer has typed some byte string, it is as far along as the
    wire says, and its ghost history replays to the document that byte string
    denotes. This is the refinement relation the peers above carried a token
    for. *)
Definition stream_coh (γh : history_names) (cl : ClientId) (t : TId)
    (c0 : chan_id) (M : gmap (chan_id * nat) (list u8)) : iProp Σ :=
  ∃ (bs : list w8) (h : list Ev),
    ⌜length bs = stream_pos c0 M⌝ ∗
    ⌜history_state_coh h (stream_docm cl t bs)⌝ ∗
    own_client_history γh cl h.

Definition stream_wsGS (γm γs γr : gname) (γh : history_names)
    (cl : ClientId) (nm : P) (c0 : chan_id) : wsGS Σ :=
  WsGS Σ _ _ γm γs γr (smoke_prot γh) (smoke_prot_persistent γh)
       (stream_coh γh cl (RootId nm) c0) (stream_may cl nm c0).

(** A peer that has not typed anything yet is coherent with the empty history,
    so the relation can be entered. *)
Lemma stream_coh_init (γh : history_names) (cl : ClientId) (t : TId)
    (c0 : chan_id) :
  own_client_history γh cl ([] : list Ev) -∗ stream_coh γh cl t c0 ∅.
Proof.
  iIntros "Hown". iExists [], []. iFrame "Hown". iPureIntro.
  split; first by rewrite stream_pos_empty.
  destruct (history_state_coh_nil (A := A) (P := P)) as (s & Hs & Hm).
  exists s. split; first exact Hs.
  move=> t'. rewrite (Hm t') smoke_nilget stream_docm_get. by case_decide.
Qed.

(** The obligation holds for a peer that types without end. *)
Lemma stream_ws_env_preserves (γm γs γr : gname) (γh : history_names)
    (cl : ClientId) (nm : P) (c0 : chan_id) (E : coPset) :
  ↑histN ⊆ E ->
  is_history (A := A) (P := P) γh -∗
    @ws_env_preserves Σ (stream_wsGS γm γs γr γh cl nm c0) _ E.
Proof.
  iIntros (HE) "#Hinv".
  iModIntro. iIntros (g r n data) "%Hmay %Hext %Hwf %Hfresh _ Hcoh".
  destruct Hmay as (-> & Hclkbnd & [b ->]).
  rewrite /stream_wsGS /=.
  iDestruct "Hcoh" as (bs h) "(%Hlen & %Hcohst & Hown)".
  (* the peer's own channel is the environment's, so the position the send
     relation read off the whole wire is the one the coherence carries *)
  have Hpos : stream_pos c0 g.(ws_msgs) = length bs.
  { rewrite Hlen /stream_pos (chan_msgs_env g c0 Hext) //. }
  rewrite Hpos.
  have Hnone : env_msgs g !! (c0, n) = None.
  { apply map_lookup_filter_None. by left. }
  (* the pure step, at the peer's own document *)
  have Hok := stream_ok_all cl bs.
  have [Htoitem [Hvalid [Hmax Hint]]] := stream_step cl bs b Hok.
  have Hget : doc_model_get (stream_docm cl (RootId nm) bs) (RootId nm) = stream_doc cl bs.
  { rewrite stream_docm_get decide_True //. }
  rewrite -Hget in Htoitem Hmax Hint.
  have Hbound : forall (t' : TId) (x : YjsItem A),
      x ∈ doc_model_get (stream_docm cl (RootId nm) bs) t' ->
      clientId (item_id x) = cl -> (clock (item_id x) < length bs)%nat.
  { move=> t' x. rewrite stream_docm_get. case_decide as Ht'.
    - move=> Hx _. have [i [Hi Hid]] := stream_ok_id_elem cl bs x Hok Hx.
      rewrite Hid /=. lia.
    - by move=> /elem_of_nil. }
  iMod (history_broadcast γh cl (length bs) h (stream_docm cl (RootId nm) bs) (RootId nm)
          (stream_doc cl (bs ++ [b])) (stream_input cl (length bs) b)
          (stream_item cl bs b) E HE
          Htoitem Hvalid Hmax eq_refl Hbound Hint Hcohst
          with "Hinv Hown") as "(Hown & _ & #Hcert & %Hcoh2)".
  iModIntro. iSplitL "Hown".
  - (* one character further along, in both the wire and the document *)
    iExists (bs ++ [b]),
      (h ++ [EvBroadcast (RootId nm, OpInsert (stream_input cl (length bs) b));
             EvDeliver (RootId nm, OpInsert (stream_input cl (length bs) b))]).
    iFrame "Hown". iPureIntro. split.
    + rewrite length_app /= (stream_pos_insert c0 (env_msgs g) n) // -Hlen. lia.
    + move: Hcoh2. rewrite /stream_docm insert_insert_eq //.
  - rewrite /smoke_prot /yjs_prot. iExists [(RootId nm, stream_input cl (length bs) b)].
    iSplitR; first by rewrite decode_encode.
    iSplitR.
    { iPureIntro. apply stream_input_wf. word. }
    rewrite expand_inputs_stream /is_pending_certified big_sepL_singleton.
    by iFrame "Hcert".
Qed.

(** Non-vacuity for this peer, as for the first one: a history exists, the
    obligation holds over it, the coherence can be entered, and the relation
    permits a message at every point of the stream, not just the first. *)
Lemma stream_env_nonvacuous (γm γs γr : gname)
    (cl : ClientId) (nm : P) (c0 : chan_id) (E : coPset) :
  ↑histN ⊆ E ->
  ⊢ |={E}=> ∃ γh : history_names,
      is_history (A := A) (P := P) γh ∗
      @ws_env_preserves Σ (stream_wsGS γm γs γr γh cl nm c0) _ E ∗
      stream_coh γh cl (RootId nm) c0 ∅ ∗
      ⌜forall (M : gmap (chan_id * nat) (list u8)) (b : w8),
         (Z.of_nat (stream_pos c0 M) + 1 < 2^64)%Z ->
         stream_may cl nm c0 M c0
           (encode [(RootId nm, stream_input cl (stream_pos c0 M) b)])⌝.
Proof.
  iIntros (HE).
  iMod (history_alloc (A := A) (P := P) {[ cl ]} E) as (γh) "[#Hinv Hown]".
  iModIntro. iExists γh. iFrame "Hinv".
  iSplitR; first by iApply stream_ws_env_preserves.
  iSplitL; last by iPureIntro; move=> M b Hbnd; split_and!; [done | done | by exists b].
  iApply stream_coh_init.
  by iDestruct (big_sepS_elem_of _ _ cl with "Hown") as "$"; first apply elem_of_singleton.
Qed.

(** ** A peer that takes something in and keeps typing

    The three before it read the wire but speak once; the one above speaks
    without end but never reads the wire. This one does both: it delivers the
    operation another client put on the wire into its own ghost history, and
    then types for as long as someone types into it. The delivery happens
    inside the same step as the peer's first character, since a send is the
    only step the obligation gives, and after that there is nothing left to
    deliver.

    Which of the two the peer is at is a function of the wire, like everything
    else its state depends on: it has delivered exactly when it has said
    something, that is when [stream_pos] is not zero.

    What it still shares with [relay_ws_env_preserves] is where its own
    characters go: into a different type than the operation it took in, which
    is what keeps the array it types into the one [stream_step] describes. A
    peer typing into the same list as the operation it received is
    [anchor_ws_env_preserves]'s document with a stream on top, and that wants
    [stream_ok] over a base array rather than over the empty one. *)

(** What the peer holds once it has done both: the operation it took in, at
    [t], and the characters it typed, at [t2]. *)
Definition full_model (cl clX : ClientId) (t t2 : TId) (aX : w8)
    (bs : list w8) : DocM :=
  <[t := [smoke_item clX aX]]> (<[t2 := stream_doc cl bs]> (∅ : DocM)).

Lemma full_model_typed (cl clX : ClientId) (t t2 : TId) (aX : w8) (bs : list w8) :
  t2 ≠ t ->
  doc_model_get (full_model cl clX t t2 aX bs) t2 = stream_doc cl bs.
Proof. move=> Hnt. rewrite /full_model docm_get_insert_ne // docm_get_insert_eq //. Qed.

(** Delivering the relayed operation lands on a model with no entry at [t2] at
    all; the peer's, before it has typed, has an empty one. As documents those
    are the same, which is all [history_state_coh] looks at. *)
Lemma full_model_nil_get (cl clX : ClientId) (t t2 : TId) (aX : w8) (t'' : TId) :
  doc_model_get (<[t := [smoke_item clX aX]]> (∅ : DocM)) t''
    = doc_model_get (full_model cl clX t t2 aX []) t''.
Proof.
  rewrite /full_model.
  destruct (decide (t'' = t)) as [-> | H1]; first by rewrite !docm_get_insert_eq.
  rewrite (docm_get_insert_ne (∅ : DocM) t t'' _ H1).
  rewrite (docm_get_insert_ne _ t t'' _ H1).
  destruct (decide (t'' = t2)) as [-> | H2].
  - rewrite docm_get_insert_eq smoke_nilget //.
  - rewrite (docm_get_insert_ne (∅ : DocM) t2 t'' _ H2) //.
Qed.

Lemma full_model_bound (cl clX : ClientId) (t t2 : TId) (aX : w8) (bs : list w8) :
  cl ≠ clX -> t2 ≠ t ->
  forall (t' : TId) (x : YjsItem A),
    x ∈ doc_model_get (full_model cl clX t t2 aX bs) t' ->
    clientId (item_id x) = cl -> (clock (item_id x) < length bs)%nat.
Proof.
  move=> Hne Hnt t' x. rewrite /full_model.
  destruct (decide (t' = t)) as [-> | H1].
  - (* the operation the peer took in is another client's *)
    rewrite docm_get_insert_eq list_elem_of_singleton => -> /=.
    move=> Hcid. exfalso. by apply Hne.
  - rewrite docm_get_insert_ne //.
    destruct (decide (t' = t2)) as [-> | H2].
    + rewrite docm_get_insert_eq => Hx _.
      have [i [Hi Hid]] := stream_ok_id_elem cl bs x (stream_ok_all cl bs) Hx.
      rewrite Hid /=. lia.
    + rewrite docm_get_insert_ne // smoke_nilget. by move=> /elem_of_nil.
Qed.

(** The send relation: the wire carries the other client's operation at [kX],
    and the peer may put the next character of its stream on the channel it
    owns. *)
Definition full_may (cl clX : ClientId) (t : TId) (nm2 : P) (aX : w8)
    (kX : chan_id * nat) (c0 : chan_id)
    (M : gmap (chan_id * nat) (list u8)) (c : chan_id) (d : list u8) : Prop :=
  M !! kX = Some (encode [(t, smoke_input clX aX)]) /\
  c = c0 /\ (Z.of_nat (stream_pos c0 M) + 1 < 2^64)%Z /\
  ∃ b : w8, d = encode [(RootId nm2, stream_input cl (stream_pos c0 M) b)].

(** Coherence: as for the typing peer, with the delivery folded in. Before the
    first character the peer's history is empty of everything, including what
    was relayed to it; afterwards it replays to both halves of its document. *)
Definition full_coh (γh : history_names) (cl clX : ClientId) (t t2 : TId)
    (aX : w8) (c0 : chan_id) (M : gmap (chan_id * nat) (list u8)) : iProp Σ :=
  ∃ (bs : list w8) (h : list Ev),
    ⌜length bs = stream_pos c0 M⌝ ∗
    ⌜history_state_coh h
       (if decide (bs = []) then (∅ : DocM) else full_model cl clX t t2 aX bs)⌝ ∗
    own_client_history γh cl h.

Definition full_wsGS (γm γs γr : gname) (γh : history_names)
    (cl clX : ClientId) (t : TId) (nm2 : P) (aX : w8) (kX : chan_id * nat)
    (c0 : chan_id) : wsGS Σ :=
  WsGS Σ _ _ γm γs γr (smoke_prot γh) (smoke_prot_persistent γh)
       (full_coh γh cl clX t (RootId nm2) aX c0) (full_may cl clX t nm2 aX kX c0).

Lemma full_coh_init (γh : history_names) (cl clX : ClientId) (t t2 : TId)
    (aX : w8) (c0 : chan_id) :
  own_client_history γh cl ([] : list Ev) -∗ full_coh γh cl clX t t2 aX c0 ∅.
Proof.
  iIntros "Hown". iExists [], []. iFrame "Hown". iPureIntro.
  split; first by rewrite stream_pos_empty.
  exact (history_state_coh_nil (A := A) (P := P)).
Qed.

Lemma full_ws_env_preserves (γm γs γr : gname) (γh : history_names)
    (cl clX : ClientId) (t : TId) (nm2 : P) (aX : w8) (kX : chan_id * nat)
    (c0 : chan_id) (E : coPset) :
  ↑histN ⊆ E ->
  cl ≠ clX ->
  RootId nm2 ≠ t ->
  is_history (A := A) (P := P) γh -∗
    @ws_env_preserves Σ (full_wsGS γm γs γr γh cl clX t nm2 aX kX c0) _ E.
Proof.
  iIntros (HE Hne Hnt) "#Hinv".
  iModIntro. iIntros (g r n data) "%Hmay %Hext %Hwf %Hfresh #Hwire Hcoh".
  destruct Hmay as (HkX & -> & Hclkbnd & [b ->]).
  rewrite /full_wsGS /=.
  iDestruct "Hcoh" as (bs h) "(%Hlen & %Hcohst & Hown)".
  (* the certificate for what the peer took in comes off the wire *)
  iAssert (is_op_cert γh (t, OpInsert (smoke_input clX aX))) as "#HcertX".
  { iDestruct (big_sepM_lookup _ _ kX with "Hwire") as (inputs) "(%Hd & %Hwfw & Hc)";
      first exact HkX.
    rewrite decode_encode in Hd. injection Hd as <-.
    rewrite expand_inputs_smoke /is_pending_certified big_sepL_singleton.
    iApply "Hc". }
  have Hpos : stream_pos c0 g.(ws_msgs) = length bs.
  { rewrite Hlen /stream_pos (chan_msgs_env g c0 Hext) //. }
  rewrite Hpos.
  have Hnone : env_msgs g !! (c0, n) = None.
  { apply map_lookup_filter_None. by left. }
  (* deliver what the peer took in, unless it already has *)
  iAssert (|={E}=> ∃ h' : list Ev, own_client_history γh cl h' ∗
             ⌜history_state_coh h' (full_model cl clX t (RootId nm2) aX bs)⌝)%I
    with "[Hown]" as ">(%h' & Hown & %Hcoh1)".
  { move: Hcohst. case_decide as Hbs; last first.
    - move=> Hcohst. iModIntro. iExists h. by iFrame "Hown".
    - subst bs => Hcohst.
      iMod (history_deliver_pending γh cl h ∅ [(t, smoke_input clX aX)]
              [(t, smoke_input clX aX)] [] (<[t := [smoke_item clX aX]]> (∅ : DocM))
              E HE (relay_deliver_drain clX t aX) Hcohst
              with "Hinv Hown []") as "(Hown & _ & _ & %Hcoh2 & _)".
      { rewrite /is_pending_certified big_sepL_singleton. iApply "HcertX". }
      iModIntro. iExists _. iFrame "Hown". iPureIntro.
      apply (history_state_coh_get_eq _ (<[t := [smoke_item clX aX]]> (∅ : DocM)));
        [exact (full_model_nil_get cl clX t (RootId nm2) aX) | exact Hcoh2]. }
  (* from here the typing peer's step, at the type the peer types into *)
  have Hok := stream_ok_all cl bs.
  have [Htoitem [Hvalid [Hmax Hint]]] := stream_step cl bs b Hok.
  have Hgt2 := full_model_typed cl clX t (RootId nm2) aX bs Hnt.
  rewrite -Hgt2 in Htoitem Hmax Hint.
  iMod (history_broadcast γh cl (length bs) h' (full_model cl clX t (RootId nm2) aX bs) (RootId nm2)
          (stream_doc cl (bs ++ [b])) (stream_input cl (length bs) b)
          (stream_item cl bs b) E HE
          Htoitem Hvalid Hmax eq_refl (full_model_bound cl clX t (RootId nm2) aX bs Hne Hnt)
          Hint Hcoh1 with "Hinv Hown") as "(Hown & _ & #Hcert & %Hcoh3)".
  iModIntro. iSplitL "Hown".
  - iExists (bs ++ [b]), _. iFrame "Hown". iPureIntro. split.
    + rewrite length_app /= (stream_pos_insert c0 (env_msgs g) n) // -Hlen. lia.
    + rewrite decide_False; last by destruct bs.
      move: Hcoh3. rewrite /full_model insert_insert_ne // insert_insert_eq //.
  - rewrite /smoke_prot /yjs_prot. iExists [(RootId nm2, stream_input cl (length bs) b)].
    iSplitR; first by rewrite decode_encode.
    iSplitR.
    { iPureIntro. apply stream_input_wf. word. }
    rewrite expand_inputs_stream /is_pending_certified big_sepL_singleton.
    by iFrame "Hcert".
Qed.

End smoke.
