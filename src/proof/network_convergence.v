(** Convergence of coherent history prefixes (issue #239, layer 0): two
    replicas that have delivered the same set of operations into a root hold
    the same document for that root, in the relaxed network model of issue
    #40 (no causal delivery: an operation is applied as soon as its
    structural dependencies have).

    The Rocq-Yjs convergence theorem ([doc_strong_convergence], the Gomes et
    al. framework at the doc level) takes an abstract causal order over which
    both replicas' delivery orders are consistent and closed, with concurrent
    ops of distinct clients. Since issue #40 the histories are not causally
    delivered, so the model's happens-before is not such an order for them.
    The order used here is the STRUCTURAL one, built from the delivered set
    itself: [x] precedes [y] when [x] is one of [y]'s origins or an earlier op
    of [y]'s author, transitively ([dep_le]). Every edge points forward in
    EITHER replica's delivery order, for the two reasons a coherent replay
    guarantees:
    - a replay resolves every insert's origins against the state it has
      built, so an origin was delivered earlier ([replay_origin_before]);
    - per-author FIFO delivery ([hwf_fifo]) against the author's clock-sorted
      log ([broadcast_log_clock_lt]) delivers an author's ops in clock order
      ([fifo_same_client_before]).
    That makes [dep_le] a partial order (ranked by one replica's delivery
    order, [dep_order]) under which both delivery orders are consistent and
    closed ([dep_hb_consistent], [dep_hbClosed]), with concurrent ops of
    distinct clients ([dep_concurrent_distinct]); validity transports along
    the origins alone ([valid_in_broadcast_replay], via
    [dep_replay_validity_at]).

    Everything is stated per type ([ops_at t], the delivered ops into type
    [t]): a doc-level op touches only its own type, so a type's document is
    the replay of the ops into that type ([effect_list_ops_at]), and a read
    of one root knows only that root's ops. The whole-document statement is
    the corollary over every type.

    API
    - [ops_at t l]: the ops of [l] into type [t]; [dep_step L] / [dep_le L]:
      the structural dependency order within the delivered set [L].
    - [history_prefix_convergence_at]: THE theorem. Under [history_wf N],
      two prefixes [h1] of [N c1] and [h2] of [N c2], each coherent with a
      document model: equal delivered op sets into [t] give equal documents
      at [t]. Prefixes, because a read certifies a prefix.
    - [history_prefix_convergence_ids_at]: the same with the hypothesis as a
      read sees it, equal id sets ([item_ids]) of the two documents at [t]
      ([docm_ids_at]: a coherent document's ids at [t] are the ids delivered
      into [t]).
    - [history_prefix_convergence]: the whole-document corollary, from equal
      delivered id sets.

    Pure, like [network_model]; iterate on this file alone. *)
From stdpp Require Import base list gmap relations.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.
From New.proof Require Import core.
From New.proof Require Import algebra.
From New.proof Require Import network_model.

Section network_convergence.
Context {A : Type} `{EqDA : EqDecision A}.
Context {P : Type} `{EqDP : !EqDecision P} `{CntP : !Countable P}.

Local Notation TId := (TypeId P).
Local Notation Oy := (@YjsOp A EqDA).
Local Notation Op := (TId * @YjsOperation A)%type.
Local Notation opid := (DocOp_id (A := A) (P := P)).
Local Notation O := (DocO (A := A) (P := P)).
Local Notation Ev := (@Event Op).
Local Notation RawHistories := (gmap ClientId (list Ev)).
Local Notation DocModel := (gmap TId (list (YjsItem A))).

Implicit Types (N : RawHistories) (h : list Ev) (op : Op) (c i j : ClientId).

Set Default Proof Using "Type*".

(* ===== definitions ======================================================== *)

(** The ops of a list into type [t]. *)
Definition ops_at (t : TId) (l : list Op) : list Op := filter (λ op, op.1 = t) l.

(** The ids of a document's items (what a read of it can compare). *)
Definition item_ids (l : list (YjsItem A)) : gset YjsId := list_to_set (item_id <$> l).

(** The ids an op resolves against when integrated: an insert's two origins. *)
Definition op_origin_ids op : list YjsId :=
  match op.2 with
  | OpInsert input => option_list (in_originId input) ++ option_list (in_rightOriginId input)
  | OpDelete _ _ => []
  end.

(** One structural-dependency edge within the delivered set [L]: [x] is an
    origin of [y], or an earlier op of [y]'s author. *)
Definition dep_step (L : list Op) (x y : Op) : Prop :=
  x ∈ L ∧ y ∈ L ∧
  (opid x ∈ op_origin_ids y ∨
   (clientId (opid x) = clientId (opid y) ∧ (clock (opid x) < clock (opid y))%nat)).

(** The structural dependency order: the reflexive-transitive closure. *)
Definition dep_le (L : list Op) : relation Op := rtc (dep_step L).

(** [L'] ranks [L]: every edge of [L] points forward in [L']. *)
Definition dep_ranked (L L' : list Op) : Prop :=
  ∀ x y, dep_step L x y -> list_before L' x y.

(** The causal order of the Rocq-Yjs framework over a self-ranked delivered
    set. *)
Program Definition dep_order (L : list Op) (Hnd : NoDup L) (Hrank : dep_ranked L L)
    : @CausalOrder Op :=
  MkCausalOrder (dep_le L) _.
Next Obligation.
  move=> L Hnd Hrank. split; first apply _.
  move=> x y Hxy Hyx.
  destruct (rtc_list_before (dep_step L) L x y Hnd Hrank Hxy) as [-> | Hb]; first done.
  destruct (rtc_list_before (dep_step L) L y x Hnd Hrank Hyx) as [-> | Hb']; first done.
  exfalso. exact (list_before_asymm L x y Hnd Hb Hb').
Qed.

(* ===== lemmas ============================================================= *)

(* ----- the ops into one type ----- *)

Lemma elem_of_ops_at (t : TId) (l : list Op) op :
  op ∈ ops_at t l <-> op ∈ l ∧ op.1 = t.
Proof. rewrite /ops_at list_elem_of_filter. tauto. Qed.

Lemma ops_at_NoDup (t : TId) (l : list Op) : NoDup l -> NoDup (ops_at t l).
Proof. apply NoDup_filter. Qed.

Lemma elem_of_item_ids (l : list (YjsItem A)) (i : YjsId) :
  i ∈ item_ids l <-> ∃ x, x ∈ l ∧ item_id x = i.
Proof.
  rewrite /item_ids elem_of_list_to_set list_elem_of_fmap. split.
  - move=> [x [-> Hx]]. by exists x.
  - move=> [x [Hx <-]]. by exists x.
Qed.

Lemma ops_at_IdNoDup (t : TId) (l : list Op) :
  IdNoDup DocWithId l -> IdNoDup DocWithId (ops_at t l).
Proof.
  rewrite /IdNoDup => Hnd.
  apply NoDup_fmap_inj_on; last exact (ops_at_NoDup t l (NoDup_fmap_1 _ _ Hnd)).
  move=> x y Hx Hy Hid.
  apply elem_of_ops_at in Hx as [Hx _]. apply elem_of_ops_at in Hy as [Hy _].
  exact (NoDup_fmap_elem_of_eq _ l x y Hnd Hx Hy Hid).
Qed.

(** The replay of a list restricted to type [t] builds [t]'s document as the
    whole replay does: a doc-level op touches only its own type. *)
Lemma effect_list_ops_at (t : TId) (l : list Op) (s0 s0' s : op_State O) :
  doc_get s0 t = doc_get s0' t ->
  effect_list O l s0 s ->
  ∃ s', effect_list O (ops_at t l) s0' s' ∧ doc_get s' t = doc_get s t.
Proof.
  move: s0 s0'. elim: l => [| op l IH] s0 s0' Heq.
  - move=> /(effect_list_nil O) <-. exists s0'.
    split; [by apply (effect_list_nil O) | exact (eq_sym Heq)].
  - move=> /(effect_list_cons O) [m [Hstep Hrest]].
    destruct Hstep as (st' & Heff & ->).
    rewrite /ops_at filter_cons. case_decide as Ht.
    + (* the op is of type [t]: step the restricted replay the same way *)
      have Heq' : doc_get (<[op.1 := st']> s0) t = doc_get (<[op.1 := st']> s0') t
        by rewrite Ht !doc_get_insert_eq.
      destruct (IH (<[op.1 := st']> s0) (<[op.1 := st']> s0') Heq' Hrest) as (s' & Heffl & Hs').
      exists s'. split; [| exact Hs'].
      apply (effect_list_cons O). exists (<[op.1 := st']> s0'). split; [| exact Heffl].
      exists st'. split; [| done].
      rewrite Ht in Heff |- *. rewrite -Heq. exact Heff.
    + (* another type: the [t] component is untouched *)
      have Heq' : doc_get (<[op.1 := st']> s0) t = doc_get s0' t.
      { rewrite doc_get_insert_ne; [exact Heq | congruence]. }
      exact (IH (<[op.1 := st']> s0) s0' Heq' Hrest).
Qed.

(* ----- prefixes of well-formed histories ----- *)

Lemma prefix_history_NoDup N c h :
  history_wf N -> h `prefix_of` to_histories N c -> NoDup h.
Proof.
  move=> Hwf [rest Hh].
  have Hnd := hwf_nodup N Hwf c. rewrite Hh in Hnd.
  apply NoDup_app in Hnd as (Hnd & _ & _). exact Hnd.
Qed.

Lemma prefix_delivered_ops N c h op :
  h `prefix_of` to_histories N c -> op ∈ delivered_ops h -> op ∈ delivered_ops (to_histories N c).
Proof.
  move=> Hpre Hin.
  destruct (delivered_ops_prefix h _ Hpre) as [rest ->].
  rewrite elem_of_app. by left.
Qed.

Lemma prefix_delivered_broadcast N c h op :
  history_wf N -> h `prefix_of` to_histories N c -> op ∈ delivered_ops h -> op_broadcast N op.
Proof.
  move=> Hwf Hpre Hin.
  have Hin' := prefix_delivered_ops N c h op Hpre Hin.
  apply elem_of_delivered_ops_ev in Hin'.
  exact (hwf_deliver_has_a_cause N Hwf c op Hin').
Qed.

Lemma prefix_delivered_insert N c h op :
  history_wf N -> h `prefix_of` to_histories N c -> op ∈ delivered_ops h ->
  ∃ input, op.2 = OpInsert input.
Proof.
  move=> Hwf Hpre Hin.
  have Hin' := prefix_delivered_ops N c h op Hpre Hin.
  apply elem_of_delivered_ops_ev in Hin'.
  exact (hwf_insert_only N Hwf c op (or_intror Hin')).
Qed.

Lemma delivered_ops_NoDup h : NoDup h -> NoDup (delivered_ops h).
Proof.
  apply NoDup_omap_inj.
  move=> e1 e2 op. destruct e1 as [a | a]; destruct e2 as [b | b]; simpl; try done.
  move=> [= <-] [= <-] //.
Qed.

(** Delivered ops of one replica have pairwise distinct ids: two with one id
    were both broadcast, and broadcast ops are determined by their id. *)
Lemma delivered_IdNoDup N c h :
  history_wf N -> h `prefix_of` to_histories N c -> IdNoDup DocWithId (delivered_ops h).
Proof.
  move=> Hwf Hpre. rewrite /IdNoDup.
  apply NoDup_fmap_inj_on;
    last exact (delivered_ops_NoDup h (prefix_history_NoDup N c h Hwf Hpre)).
  move=> x y Hx Hy Hid.
  destruct (prefix_delivered_broadcast N c h x Hwf Hpre Hx) as (ix & Hix).
  destruct (prefix_delivered_broadcast N c h y Hwf Hpre Hy) as (iy & Hiy).
  exact (proj2 (hwf_msg_id_unique N Hwf x y ix iy Hix Hiy Hid)).
Qed.

(** Two delivered ops with one id, at any two replicas, are one op. *)
Lemma delivered_id_eq N c1 c2 h1 h2 (x y : Op) :
  history_wf N ->
  h1 `prefix_of` to_histories N c1 -> h2 `prefix_of` to_histories N c2 ->
  x ∈ delivered_ops h1 -> y ∈ delivered_ops h2 -> opid x = opid y -> x = y.
Proof.
  move=> Hwf Hpre1 Hpre2 Hx Hy Hid.
  destruct (prefix_delivered_broadcast N c1 h1 x Hwf Hpre1 Hx) as (ix & Hix).
  destruct (prefix_delivered_broadcast N c2 h2 y Hwf Hpre2 Hy) as (iy & Hiy).
  exact (proj2 (hwf_msg_id_unique N Hwf x y ix iy Hix Hiy Hid)).
Qed.

(** Equal delivered id sets are equal delivered op sets. *)
Lemma delivered_ids_eq_ops N c1 c2 h1 h2 :
  history_wf N ->
  h1 `prefix_of` to_histories N c1 -> h2 `prefix_of` to_histories N c2 ->
  delivered_ids h1 = delivered_ids h2 ->
  ∀ op, op ∈ delivered_ops h1 <-> op ∈ delivered_ops h2.
Proof.
  move=> Hwf Hpre1 Hpre2 Hids.
  have Hdir : ∀ c1' c2' h1' h2',
      h1' `prefix_of` to_histories N c1' -> h2' `prefix_of` to_histories N c2' ->
      delivered_ids h1' ⊆ delivered_ids h2' ->
      ∀ op, op ∈ delivered_ops h1' -> op ∈ delivered_ops h2'.
  { move=> c1' c2' h1' h2' Hp1 Hp2 Hsub op Hin.
    have Hid : opid op ∈ delivered_ids h2'.
    { apply Hsub. apply elem_of_delivered_ids. exists op.
      split; [by apply elem_of_delivered_ops_ev | done]. }
    apply elem_of_delivered_ids in Hid as (op' & Hop' & Hideq).
    have Hin' : op' ∈ delivered_ops h2' by apply elem_of_delivered_ops_ev.
    rewrite -(delivered_id_eq N c2' c1' h2' h1' op' op Hwf Hp2 Hp1 Hin' Hin Hideq).
    exact Hin'. }
  move=> op. split.
  - apply (Hdir c1 c2 h1 h2 Hpre1 Hpre2). rewrite Hids. done.
  - apply (Hdir c2 c1 h2 h1 Hpre2 Hpre1). rewrite Hids. done.
Qed.

(** The ids of a coherent document at [t] are the ids delivered into [t]. *)
Lemma docm_ids_at N c h (m : DocModel) (t : TId) (i : YjsId) :
  history_wf N -> h `prefix_of` to_histories N c ->
  history_state_coh h m ->
  (∃ x, x ∈ doc_model_get m t ∧ item_id x = i) <->
  (∃ op, op ∈ ops_at t (delivered_ops h) ∧ opid op = i).
Proof.
  move=> Hwf Hpre Hcoh. split.
  - move=> [x [Hx Hid]].
    destruct (docm_mem_delivered h m t x Hcoh Hx) as (input & Hin & Hinid).
    exists (t, OpInsert input). split.
    + apply elem_of_ops_at. by split.
    + rewrite /DocOp_id /= Hinid Hid //.
  - move=> [op [Hop Hid]].
    apply elem_of_ops_at in Hop as [Hop Ht].
    destruct (prefix_delivered_insert N c h op Hwf Hpre Hop) as (input & Hinput).
    destruct op as [t' oop]. simpl in Ht, Hinput. subst t' oop.
    destruct (delivered_docm_mem h m t input Hcoh Hop) as (it & Hitid & Hit).
    exists it. split; [exact Hit | rewrite Hitid; exact Hid].
Qed.

(* ----- origins are delivered first ----- *)

(** [toItem] resolves every origin id of its input by a lookup. *)
Lemma toItem_origin_find (input : IntegrateInput (A := A)) (arr : list (YjsItem A))
    (it : YjsItem A) (originId : YjsId) :
  toItem input arr = Some it ->
  originId ∈ option_list (in_originId input) ++ option_list (in_rightOriginId input) ->
  ∃ oit, find_by_id originId arr = Some oit.
Proof.
  move=> Htoit Hor.
  destruct (proj1 (toItem_ok_iff input arr it) Htoit)
    as (o & r & id & ct & _ & HoL & HoR & _ & _).
  move: Hor HoL HoR. rewrite /isLeftIdPtr /isRightIdPtr elem_of_app.
  destruct (in_originId input) as [oid |]; destruct (in_rightOriginId input) as [rid |];
    simpl.
  - move=> [Hor | Hor] [oit [_ Hfo]] [rit [_ Hfr]];
      apply list_elem_of_singleton in Hor; subst originId; eauto.
  - move=> [Hor | Hor] [oit [_ Hfo]] _; [| by apply elem_of_nil in Hor].
    apply list_elem_of_singleton in Hor. subst originId. eauto.
  - move=> [Hor | Hor] _ [rit [_ Hfr]]; [by apply elem_of_nil in Hor |].
    apply list_elem_of_singleton in Hor. subst originId. eauto.
  - move=> [Hor | Hor]; by apply elem_of_nil in Hor.
Qed.

(** In a replay from the empty document, an insert's origin was delivered
    earlier, by an op of the same type carrying the origin's id. *)
Lemma replay_origin_src (L : list Op) (s : op_State O) (y : Op) (originId : YjsId) :
  effect_list O L (op_init O) s ->
  y ∈ L -> originId ∈ op_origin_ids y ->
  ∃ x, x.1 = y.1 ∧ opid x = originId ∧ list_before L x y.
Proof.
  move=> Heff Hy Hor.
  destruct (list_elem_of_split _ _ Hy) as (l1 & l2 & Hsplit).
  rewrite Hsplit in Heff.
  apply (effect_list_app O) in Heff as (sMid & Hpre & Hrest).
  apply (effect_list_cons O) in Hrest as (sNext & Hstep & _).
  destruct y as [t yop]. destruct yop as [input | id did];
    last by (simpl in Hor; apply elem_of_nil in Hor).
  destruct Hstep as (st' & Hins & _). simpl in Hins.
  destruct (YjsState_insert_toItem _ _ _ Hins) as (it & _ & Htoit & _ & _ & _).
  destruct (toItem_origin_find input _ it originId Htoit Hor) as (oit & Hfind).
  have Hmem : oit ∈ st_items (doc_get sMid t) := @find_by_id_mem _ EqDA _ _ _ Hfind.
  have Hoid : item_id oit = originId := @find_by_id_id _ EqDA _ _ _ Hfind.
  have HeffP : effect_list Oy (proj_ops t l1) (op_init Oy) (doc_get sMid t).
  { have -> : op_init Oy = doc_get (op_init O) t by rewrite /= doc_get_empty.
    exact (doc_effect_list_proj l1 _ sMid t Hpre). }
  destruct (effect_list_mem_src (proj_ops t l1) (op_init Oy) (doc_get sMid t) oit HeffP Hmem)
    as [Hnil | (xin & Hxin & Hxid)].
  { move: Hnil. rewrite /= elem_of_nil //. }
  apply elem_of_proj_ops in Hxin.
  exists (t, OpInsert xin). split_and!; first done.
  - rewrite /DocOp_id /= Hxid Hoid //.
  - rewrite Hsplit. destruct (list_elem_of_lookup_1 _ _ Hxin) as (i & Hi).
    exists i, (length l1). split_and!.
    + rewrite lookup_app_l //. exact (lookup_lt_Some _ _ _ Hi).
    + rewrite list_lookup_middle //.
    + exact (lookup_lt_Some _ _ _ Hi).
Qed.

(** With distinct ids, the origin's op is the one with that id. *)
Lemma replay_origin_before (L : list Op) (s : op_State O) (x y : Op) :
  effect_list O L (op_init O) s -> IdNoDup DocWithId L ->
  x ∈ L -> y ∈ L -> opid x ∈ op_origin_ids y ->
  list_before L x y.
Proof.
  move=> Heff Hnd Hx Hy Hor.
  destruct (replay_origin_src L s y (opid x) Heff Hy Hor) as (x' & _ & Hid & Hb).
  have Hx' : x' ∈ L := list_before_elem_of_l _ _ _ Hb.
  have -> : x = x' := NoDup_fmap_elem_of_eq _ L x x' Hnd Hx Hx' (eq_sym Hid).
  exact Hb.
Qed.

(* ----- an author's ops are delivered in clock order ----- *)

(** Per-author FIFO delivery against the author's clock-sorted log. *)
Lemma fifo_same_client_before N c h (x y : Op) :
  history_wf N -> h `prefix_of` to_histories N c ->
  x ∈ delivered_ops h -> y ∈ delivered_ops h ->
  clientId (opid x) = clientId (opid y) -> (clock (opid x) < clock (opid y))%nat ->
  list_before (delivered_ops h) x y.
Proof.
  move=> Hwf Hpre Hx Hy Hcc Hclk.
  set j := clientId (opid y).
  set log := broadcast_ops (to_histories N j).
  have Hxf : x ∈ delivered_from h j.
  { apply elem_of_delivered_from. split; [by apply elem_of_delivered_ops_ev | exact Hcc]. }
  have Hyf : y ∈ delivered_from h j.
  { apply elem_of_delivered_from. split; [by apply elem_of_delivered_ops_ev | done]. }
  have Hprelog : delivered_from h j `prefix_of` log.
  { transitivity (delivered_from (to_histories N c) j).
    - exact (delivered_from_prefix_mono h _ j Hpre).
    - exact (hwf_fifo N Hwf c j). }
  pose proof (NoDup_broadcast_ops _ (hwf_nodup N Hwf j)) as Hndlog.
  have Hxlog : x ∈ log.
  { destruct Hprelog as [rest ->]. rewrite elem_of_app. by left. }
  have Hylog : y ∈ log.
  { destruct Hprelog as [rest ->]. rewrite elem_of_app. by left. }
  have Hblog : list_before log x y.
  { apply (list_before_of_measure (λ op, clock (opid op)) log x y);
      [| exact Hxlog | exact Hylog | exact Hclk].
    move=> q1 q2 o1 o2 Hlt H1 H2.
    exact (broadcast_log_clock_lt N j q1 q2 o1 o2 Hwf Hlt H1 H2). }
  pose proof (list_before_prefix_inv _ log x y Hndlog Hprelog Hxf Hyf Hblog) as Hbf.
  exact (list_before_filter _ (delivered_ops h) x y Hbf).
Qed.

(** The same, within the ops into one type. *)
Lemma fifo_same_client_before_at N c h (t : TId) (x y : Op) :
  history_wf N -> h `prefix_of` to_histories N c ->
  x ∈ ops_at t (delivered_ops h) -> y ∈ ops_at t (delivered_ops h) ->
  clientId (opid x) = clientId (opid y) -> (clock (opid x) < clock (opid y))%nat ->
  list_before (ops_at t (delivered_ops h)) x y.
Proof.
  move=> Hwf Hpre Hx Hy Hcc Hclk.
  have Hnd : NoDup (delivered_ops h)
    := delivered_ops_NoDup h (prefix_history_NoDup N c h Hwf Hpre).
  apply (list_before_filter_inv _ (delivered_ops h) x y Hnd Hx Hy).
  apply elem_of_ops_at in Hx as [Hx _]. apply elem_of_ops_at in Hy as [Hy _].
  exact (fifo_same_client_before N c h x y Hwf Hpre Hx Hy Hcc Hclk).
Qed.

(* ----- the delivered set ranks itself, at every replica that delivered it ----- *)

(** Every structural edge of the ops delivered into [t] points forward in
    the delivery order of any replica that delivered exactly those ops. *)
Lemma dep_ranked_delivered_at N c h (m : DocModel) (t : TId) (L : list Op) :
  history_wf N -> h `prefix_of` to_histories N c -> history_state_coh h m ->
  (∀ op, op ∈ L <-> op ∈ ops_at t (delivered_ops h)) ->
  dep_ranked L (ops_at t (delivered_ops h)).
Proof.
  move=> Hwf Hpre Hcoh HL x y [Hx [Hy Hedge]].
  apply HL in Hx. apply HL in Hy.
  destruct Hedge as [Hor | [Hcc Hclk]].
  - destruct Hcoh as (s & Hinterp & _).
    destruct (effect_list_ops_at t (delivered_ops h) (op_init O) (op_init O) s eq_refl Hinterp)
      as (s' & Heff' & _).
    exact (replay_origin_before (ops_at t (delivered_ops h)) s' x y Heff'
             (ops_at_IdNoDup t _ (delivered_IdNoDup N c h Hwf Hpre)) Hx Hy Hor).
  - exact (fifo_same_client_before_at N c h t x y Hwf Hpre Hx Hy Hcc Hclk).
Qed.

(* ----- the framework's hypotheses ----- *)

(** A ranked list is consistent with the order: no later op precedes an
    earlier one. *)
Lemma dep_hb_consistent (L L' : list Op) (Hnd : NoDup L) (Hrank : dep_ranked L L) :
  NoDup L' -> dep_ranked L L' -> hb_consistent (dep_order L Hnd Hrank) L'.
Proof.
  move=> Hnd' Hrank'.
  have Hgen : ∀ pre L'', L' = pre ++ L'' -> hb_consistent (dep_order L Hnd Hrank) L''.
  { move=> pre L''. move: pre. induction L'' as [| a L'' IH] => pre Hsplit;
      first constructor.
    apply hb_consistent_cons.
    - apply (IH (pre ++ [a])). rewrite Hsplit -app_assoc //.
    - move=> b Hb Hle.
      destruct (rtc_list_before (dep_step L) L' b a Hnd' Hrank' Hle) as [Heq | Hbefore].
      + subst b.
        have Hnd2 : NoDup (a :: L'').
        { rewrite Hsplit in Hnd'. apply NoDup_app in Hnd' as (_ & _ & Hnd2). exact Hnd2. }
        apply NoDup_cons in Hnd2 as [Hnotin _]. exact (Hnotin Hb).
      + exact (list_before_asymm L' a b Hnd' (list_before_split_r L' pre L'' a b Hsplit Hb)
                 Hbefore). }
  exact (Hgen [] L' eq_refl).
Qed.

(** A ranked list is closed under the order: every strict predecessor of a
    member comes earlier in the list. *)
Lemma dep_hbClosed (L L' : list Op) (Hnd : NoDup L) (Hrank : dep_ranked L L) :
  NoDup L' -> dep_ranked L L' -> hbClosed (dep_order L Hnd Hrank) L'.
Proof.
  move=> Hnd' Hrank' a b l1 l2 Hsplit [Hle Hne].
  destruct (rtc_list_before (dep_step L) L' b a Hnd' Hrank' Hle) as [Heq | Hbefore];
    first by (exfalso; apply Hne).
  exact (list_before_split L' l1 l2 a b Hnd' Hsplit Hbefore).
Qed.

(** Concurrent ops are by distinct clients: one author's ops are ordered by
    clock, and equal ids are equal ops. *)
Lemma dep_concurrent_distinct N c h (L : list Op) (Hnd : NoDup L) (Hrank : dep_ranked L L) :
  history_wf N -> h `prefix_of` to_histories N c ->
  (∀ op, op ∈ L -> op ∈ delivered_ops h) ->
  ∀ a b, a ∈ L -> b ∈ L -> hb_concurrent (dep_order L Hnd Hrank) a b ->
  clientId (opid a) ≠ clientId (opid b).
Proof.
  move=> Hwf Hpre HL a b Ha Hb [Hnab Hnba] Hcc.
  destruct (Nat.lt_trichotomy (clock (opid a)) (clock (opid b))) as [Hlt | [Heq | Hgt]].
  - apply Hnab. apply rtc_once. split_and!; [exact Ha | exact Hb | right; by split].
  - have Hid : opid a = opid b.
    { destruct (opid a) as [ca ka]; destruct (opid b) as [cb kb]. simpl in Hcc, Heq. by subst. }
    have Hab : a = b
      := delivered_id_eq N c c h h a b Hwf Hpre Hpre (HL a Ha) (HL b Hb) Hid.
    subst b. apply Hnab. apply rtc_refl.
  - apply Hnba. apply rtc_once. split_and!; [exact Hb | exact Ha | right; by split].
Qed.

(** Replay validity: an op delivered into [t] is valid in the replay of any
    order-closed list of its predecessors, because such a list holds the ops
    carrying its origins (which are ops into [t] too). *)
Lemma dep_replay_validity_at N c h (m : DocModel) (t : TId) (L : list Op) (Hnd : NoDup L)
    (Hrank : dep_ranked L L) :
  history_wf N -> h `prefix_of` to_histories N c -> history_state_coh h m ->
  (∀ op, op ∈ L <-> op ∈ ops_at t (delivered_ops h)) ->
  OperationReplayValidity O DocOV DocWithId (dep_order L Hnd Hrank) (λ op, op ∈ L).
Proof.
  move=> Hwf Hpre Hcoh HL.
  have HLd : ∀ op, op ∈ L -> op ∈ delivered_ops h.
  { move=> op Hop. apply HL in Hop. apply elem_of_ops_at in Hop. exact (proj1 Hop). }
  constructor => a s l Ha Hl Hpast Hcons Hclosed Heff Hndl.
  destruct a as [t0 aop]. destruct aop as [input | id did]; last exact I.
  rewrite /isValidState /= /isValidStateDoc /DocIsValidMessage /=.
  apply (valid_in_broadcast_replay N l s t0 input Hwf).
  - apply (prefix_delivered_broadcast N c h _ Hwf Hpre). by apply HLd.
  - move=> op Hop. apply (prefix_delivered_broadcast N c h op Hwf Hpre). by apply HLd, Hl.
  - exact Heff.
  - move=> originId Hor.
    have Hor' : originId ∈ op_origin_ids (t0, OpInsert input).
    { rewrite /op_origin_ids /= elem_of_app.
      destruct Hor as [-> | ->]; [left | right]; by apply list_elem_of_singleton. }
    have HaD : (t0, OpInsert input) ∈ delivered_ops h by apply HLd.
    have Ht0 : t0 = t.
    { apply HL in Ha. apply elem_of_ops_at in Ha. exact (proj2 Ha). }
    destruct Hcoh as (sh & Hinterp & _).
    destruct (replay_origin_src (delivered_ops h) sh (t0, OpInsert input) originId
                Hinterp HaD Hor') as (x & Hxt & Hxid & Hxb).
    have HxD : x ∈ delivered_ops h := list_before_elem_of_l _ _ _ Hxb.
    have HxL : x ∈ L.
    { apply HL. apply elem_of_ops_at. split; [exact HxD | rewrite Hxt /= Ht0 //]. }
    have Hstep : dep_step L x (t0, OpInsert input).
    { split_and!; [exact HxL | exact Ha | left; rewrite Hxid; exact Hor']. }
    have Hne : x ≠ (t0, OpInsert input).
    { move=> Heq. rewrite Heq in Hxb.
      exact (list_before_irrefl _ _
               (delivered_ops_NoDup h (prefix_history_NoDup N c h Hwf Hpre)) Hxb). }
    have Hxl : x ∈ l := Hpast x (conj (rtc_once _ _ Hstep) Hne).
    destruct (prefix_delivered_insert N c h x Hwf Hpre HxD) as (xin & Hxin).
    destruct x as [t' xop]. simpl in Hxin. subst xop.
    exists t', xin. split; [exact Hxl |].
    rewrite /DocOp_id /= in Hxid. exact Hxid.
Qed.

(* ----- THE theorems ----- *)

(** Two coherent history prefixes with the same delivered ops into [t]
    replay to the same document at [t]. *)
Theorem history_prefix_convergence_at N c1 c2 h1 h2 (m1 m2 : DocModel) (t : TId) :
  history_wf N ->
  h1 `prefix_of` to_histories N c1 -> h2 `prefix_of` to_histories N c2 ->
  history_state_coh h1 m1 -> history_state_coh h2 m2 ->
  (∀ op, op ∈ ops_at t (delivered_ops h1) <-> op ∈ ops_at t (delivered_ops h2)) ->
  doc_model_get m1 t = doc_model_get m2 t.
Proof.
  move=> Hwf Hpre1 Hpre2 Hcoh1 Hcoh2 Hops.
  set L := ops_at t (delivered_ops h1).
  have HL1 : ∀ op, op ∈ L <-> op ∈ ops_at t (delivered_ops h1) by done.
  have HL2 : ∀ op, op ∈ L <-> op ∈ ops_at t (delivered_ops h2) := Hops.
  have HLd1 : ∀ op, op ∈ L -> op ∈ delivered_ops h1.
  { move=> op Hop. apply elem_of_ops_at in Hop. exact (proj1 Hop). }
  have Hnd1 : NoDup (ops_at t (delivered_ops h1))
    := ops_at_NoDup t _ (delivered_ops_NoDup h1 (prefix_history_NoDup N c1 h1 Hwf Hpre1)).
  have Hnd2 : NoDup (ops_at t (delivered_ops h2))
    := ops_at_NoDup t _ (delivered_ops_NoDup h2 (prefix_history_NoDup N c2 h2 Hwf Hpre2)).
  have Hrank1 : dep_ranked L (ops_at t (delivered_ops h1))
    := dep_ranked_delivered_at N c1 h1 m1 t L Hwf Hpre1 Hcoh1 HL1.
  have Hrank2 : dep_ranked L (ops_at t (delivered_ops h2))
    := dep_ranked_delivered_at N c2 h2 m2 t L Hwf Hpre2 Hcoh2 HL2.
  have HRV := dep_replay_validity_at N c1 h1 m1 t L Hnd1 Hrank1 Hwf Hpre1 Hcoh1 HL1.
  destruct Hcoh1 as (s1 & Hinterp1 & Hm1).
  destruct Hcoh2 as (s2 & Hinterp2 & Hm2).
  destruct (effect_list_ops_at t (delivered_ops h1) (op_init O) (op_init O) s1 eq_refl Hinterp1)
    as (s1' & Heff1 & Hs1).
  destruct (effect_list_ops_at t (delivered_ops h2) (op_init O) (op_init O) s2 eq_refl Hinterp2)
    as (s2' & Heff2 & Hs2).
  have Heff2' : effect_list O (ops_at t (delivered_ops h2)) (op_init O) s1'.
  { apply (doc_strong_convergence (dep_order L Hnd1 Hrank1) (λ op, op ∈ L) HRV
             (ops_at t (delivered_ops h1)) (ops_at t (delivered_ops h2)) s1').
    - move=> x Hx. exact Hx.
    - move=> x Hx. by apply HL2.
    - exact (dep_hb_consistent L _ Hnd1 Hrank1 Hnd1 Hrank1).
    - exact (dep_hb_consistent L _ Hnd1 Hrank1 Hnd2 Hrank2).
    - exact (dep_hbClosed L _ Hnd1 Hrank1 Hnd1 Hrank1).
    - exact (dep_hbClosed L _ Hnd1 Hrank1 Hnd2 Hrank2).
    - exact (dep_concurrent_distinct N c1 h1 L Hnd1 Hrank1 Hwf Hpre1 HLd1).
    - exact (ops_at_IdNoDup t _ (delivered_IdNoDup N c1 h1 Hwf Hpre1)).
    - exact (ops_at_IdNoDup t _ (delivered_IdNoDup N c2 h2 Hwf Hpre2)).
    - exact HL2.
    - exact Heff1. }
  have Hs : s1' = s2'
    := doc_effect_list_det (ops_at t (delivered_ops h2)) (op_init O) s1' s2' Heff2' Heff2.
  rewrite -(Hm1 t) -(Hm2 t) -Hs1 -Hs2 Hs //.
Qed.

(** The same, from what a read of each document at [t] sees: equal sets of
    item ids. *)
Theorem history_prefix_convergence_ids_at N c1 c2 h1 h2 (m1 m2 : DocModel) (t : TId) :
  history_wf N ->
  h1 `prefix_of` to_histories N c1 -> h2 `prefix_of` to_histories N c2 ->
  history_state_coh h1 m1 -> history_state_coh h2 m2 ->
  item_ids (doc_model_get m1 t) = item_ids (doc_model_get m2 t) ->
  doc_model_get m1 t = doc_model_get m2 t.
Proof.
  move=> Hwf Hpre1 Hpre2 Hcoh1 Hcoh2 Hidset.
  have Hids : ∀ i : YjsId, (∃ x, x ∈ doc_model_get m1 t ∧ item_id x = i) <->
                           (∃ x, x ∈ doc_model_get m2 t ∧ item_id x = i).
  { move=> i. rewrite -!elem_of_item_ids Hidset. done. }
  apply (history_prefix_convergence_at N c1 c2 h1 h2 m1 m2 t Hwf Hpre1 Hpre2 Hcoh1 Hcoh2).
  have Hdir : ∀ c1' c2' h1' h2' (m1' m2' : DocModel),
      h1' `prefix_of` to_histories N c1' -> h2' `prefix_of` to_histories N c2' ->
      history_state_coh h1' m1' -> history_state_coh h2' m2' ->
      (∀ i : YjsId, (∃ x, x ∈ doc_model_get m1' t ∧ item_id x = i) ->
                    (∃ x, x ∈ doc_model_get m2' t ∧ item_id x = i)) ->
      ∀ op, op ∈ ops_at t (delivered_ops h1') -> op ∈ ops_at t (delivered_ops h2').
  { move=> c1' c2' h1' h2' m1' m2' Hp1 Hp2 Hc1 Hc2 Hsub op Hop.
    have Hx1 : ∃ x, x ∈ doc_model_get m1' t ∧ item_id x = opid op.
    { apply (docm_ids_at N c1' h1' m1' t (opid op) Hwf Hp1 Hc1). by exists op. }
    have Hx2 := Hsub _ Hx1.
    apply (docm_ids_at N c2' h2' m2' t (opid op) Hwf Hp2 Hc2) in Hx2 as (op' & Hop' & Hid).
    have Hop'' := proj1 (proj1 (elem_of_ops_at t _ op') Hop').
    have Hopd := proj1 (proj1 (elem_of_ops_at t _ op) Hop).
    rewrite -(delivered_id_eq N c2' c1' h2' h1' op' op Hwf Hp2 Hp1 Hop'' Hopd Hid).
    exact Hop'. }
  move=> op. split.
  - apply (Hdir c1 c2 h1 h2 m1 m2 Hpre1 Hpre2 Hcoh1 Hcoh2). move=> i0. apply Hids.
  - apply (Hdir c2 c1 h2 h1 m2 m1 Hpre2 Hpre1 Hcoh2 Hcoh1). move=> i0. apply Hids.
Qed.

(** The whole document: equal delivered id sets give pointwise equal
    documents. *)
Theorem history_prefix_convergence N c1 c2 h1 h2 (m1 m2 : DocModel) :
  history_wf N ->
  h1 `prefix_of` to_histories N c1 -> h2 `prefix_of` to_histories N c2 ->
  history_state_coh h1 m1 -> history_state_coh h2 m2 ->
  delivered_ids h1 = delivered_ids h2 ->
  ∀ t, doc_model_get m1 t = doc_model_get m2 t.
Proof.
  move=> Hwf Hpre1 Hpre2 Hcoh1 Hcoh2 Hids t.
  apply (history_prefix_convergence_at N c1 c2 h1 h2 m1 m2 t Hwf Hpre1 Hpre2 Hcoh1 Hcoh2).
  move=> op. rewrite !elem_of_ops_at.
  have Hop := delivered_ids_eq_ops N c1 c2 h1 h2 Hwf Hpre1 Hpre2 Hids op.
  tauto.
Qed.

End network_convergence.
