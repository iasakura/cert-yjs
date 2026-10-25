(** Convergence of coherent history prefixes (issue #239, layer 0): two
    replicas that have delivered the same set of operations hold the same
    document, in the relaxed network model of issue #40 (no causal delivery:
    an operation is applied as soon as its structural dependencies have).

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
    [dep_replay_validity]).

    API
    - [dep_step L] / [dep_le L]: the structural dependency order within the
      delivered set [L].
    - [history_prefix_convergence]: THE theorem. Under [history_wf N], two
      prefixes [h1] of [N c1] and [h2] of [N c2], each coherent with a
      document model: equal delivered id sets give pointwise equal
      documents. Prefixes, because a read certifies a prefix.

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
    destruct (prefix_delivered_broadcast N c1' h1' op Hwf Hp1 Hin) as (i1 & Hi1).
    destruct (prefix_delivered_broadcast N c2' h2' op' Hwf Hp2 Hin') as (i2 & Hi2).
    have Heq := proj2 (hwf_msg_id_unique N Hwf op' op i2 i1 Hi2 Hi1 Hideq).
    rewrite -Heq. exact Hin'. }
  move=> op. split.
  - apply (Hdir c1 c2 h1 h2 Hpre1 Hpre2). rewrite Hids. done.
  - apply (Hdir c2 c1 h2 h1 Hpre2 Hpre1). rewrite Hids. done.
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
    earlier, by an op carrying the origin's id. *)
Lemma replay_origin_src (L : list Op) (s : op_State O) (y : Op) (originId : YjsId) :
  effect_list O L (op_init O) s ->
  y ∈ L -> originId ∈ op_origin_ids y ->
  ∃ x, opid x = originId ∧ list_before L x y.
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
  exists (t, OpInsert xin). split.
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
  destruct (replay_origin_src L s y (opid x) Heff Hy Hor) as (x' & Hid & Hb).
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

(* ----- the delivered set ranks itself, at every replica that delivered it ----- *)

(** Every structural edge of a delivered set points forward in the delivery
    order of any replica that delivered exactly that set. *)
Lemma dep_ranked_delivered N c h (m : DocModel) (L : list Op) :
  history_wf N -> h `prefix_of` to_histories N c -> history_state_coh h m ->
  (∀ op, op ∈ L <-> op ∈ delivered_ops h) ->
  dep_ranked L (delivered_ops h).
Proof.
  move=> Hwf Hpre Hcoh HL x y [Hx [Hy Hedge]].
  apply HL in Hx. apply HL in Hy.
  destruct Hedge as [Hor | [Hcc Hclk]].
  - destruct Hcoh as (s & Hinterp & _).
    exact (replay_origin_before (delivered_ops h) s x y Hinterp
             (delivered_IdNoDup N c h Hwf Hpre) Hx Hy Hor).
  - exact (fifo_same_client_before N c h x y Hwf Hpre Hx Hy Hcc Hclk).
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
  (∀ op, op ∈ L <-> op ∈ delivered_ops h) ->
  ∀ a b, a ∈ L -> b ∈ L -> hb_concurrent (dep_order L Hnd Hrank) a b ->
  clientId (opid a) ≠ clientId (opid b).
Proof.
  move=> Hwf Hpre HL a b Ha Hb [Hnab Hnba] Hcc.
  destruct (Nat.lt_trichotomy (clock (opid a)) (clock (opid b))) as [Hlt | [Heq | Hgt]].
  - apply Hnab. apply rtc_once. split_and!; [exact Ha | exact Hb | right; by split].
  - have Hid : opid a = opid b.
    { destruct (opid a) as [ca ka]; destruct (opid b) as [cb kb]. simpl in Hcc, Heq. by subst. }
    have Hab : a = b.
    { apply HL in Ha. apply HL in Hb.
      destruct (prefix_delivered_broadcast N c h a Hwf Hpre Ha) as (ia & Hia).
      destruct (prefix_delivered_broadcast N c h b Hwf Hpre Hb) as (ib & Hib).
      exact (proj2 (hwf_msg_id_unique N Hwf a b ia ib Hia Hib Hid)). }
    subst b. apply Hnab. apply rtc_refl.
  - apply Hnba. apply rtc_once. split_and!; [exact Hb | exact Ha | right; by split].
Qed.

(** Replay validity: an op of the delivered set is valid in the replay of
    any order-closed list of its predecessors, because such a list holds the
    ops carrying its origins. *)
Lemma dep_replay_validity N c h (m : DocModel) (L : list Op) (Hnd : NoDup L)
    (Hrank : dep_ranked L L) :
  history_wf N -> h `prefix_of` to_histories N c -> history_state_coh h m ->
  (∀ op, op ∈ L <-> op ∈ delivered_ops h) ->
  OperationReplayValidity O DocOV DocWithId (dep_order L Hnd Hrank) (λ op, op ∈ L).
Proof.
  move=> Hwf Hpre Hcoh HL.
  constructor => a s l Ha Hl Hpast Hcons Hclosed Heff Hndl.
  destruct a as [t0 aop]. destruct aop as [input | id did]; last exact I.
  rewrite /isValidState /= /isValidStateDoc /DocIsValidMessage /=.
  apply (valid_in_broadcast_replay N l s t0 input Hwf).
  - apply (prefix_delivered_broadcast N c h _ Hwf Hpre). by apply HL.
  - move=> op Hop. apply (prefix_delivered_broadcast N c h op Hwf Hpre). by apply HL, Hl.
  - exact Heff.
  - move=> originId Hor.
    have Hor' : originId ∈ op_origin_ids (t0, OpInsert input).
    { rewrite /op_origin_ids /= elem_of_app.
      destruct Hor as [-> | ->]; [left | right]; by apply list_elem_of_singleton. }
    have HaD : (t0, OpInsert input) ∈ delivered_ops h by apply HL.
    destruct Hcoh as (sh & Hinterp & _).
    destruct (replay_origin_src (delivered_ops h) sh (t0, OpInsert input) originId
                Hinterp HaD Hor') as (x & Hxid & Hxb).
    have HxD : x ∈ delivered_ops h := list_before_elem_of_l _ _ _ Hxb.
    have HxL : x ∈ L by apply HL.
    have Hstep : dep_step L x (t0, OpInsert input).
    { split_and!; [exact HxL | by apply HL | left; rewrite Hxid; exact Hor']. }
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

(* ----- THE theorem ----- *)

(** Two coherent history prefixes with the same delivered ids replay to the
    same document, type by type. *)
Theorem history_prefix_convergence N c1 c2 h1 h2 (m1 m2 : DocModel) :
  history_wf N ->
  h1 `prefix_of` to_histories N c1 -> h2 `prefix_of` to_histories N c2 ->
  history_state_coh h1 m1 -> history_state_coh h2 m2 ->
  delivered_ids h1 = delivered_ids h2 ->
  ∀ t, doc_model_get m1 t = doc_model_get m2 t.
Proof.
  move=> Hwf Hpre1 Hpre2 Hcoh1 Hcoh2 Hids.
  set L := delivered_ops h1.
  have HL1 : ∀ op, op ∈ L <-> op ∈ delivered_ops h1 by done.
  have HL2 : ∀ op, op ∈ L <-> op ∈ delivered_ops h2
    := delivered_ids_eq_ops N c1 c2 h1 h2 Hwf Hpre1 Hpre2 Hids.
  have Hnd1 : NoDup (delivered_ops h1)
    := delivered_ops_NoDup h1 (prefix_history_NoDup N c1 h1 Hwf Hpre1).
  have Hnd2 : NoDup (delivered_ops h2)
    := delivered_ops_NoDup h2 (prefix_history_NoDup N c2 h2 Hwf Hpre2).
  have Hrank1 : dep_ranked L (delivered_ops h1)
    := dep_ranked_delivered N c1 h1 m1 L Hwf Hpre1 Hcoh1 HL1.
  have Hrank2 : dep_ranked L (delivered_ops h2)
    := dep_ranked_delivered N c2 h2 m2 L Hwf Hpre2 Hcoh2 HL2.
  have HRV := dep_replay_validity N c1 h1 m1 L Hnd1 Hrank1 Hwf Hpre1 Hcoh1 HL1.
  destruct Hcoh1 as (s1 & Hinterp1 & Hm1).
  destruct Hcoh2 as (s2 & Hinterp2 & Hm2).
  have Heff2 : effect_list O (delivered_ops h2) (op_init O) s1.
  { apply (doc_strong_convergence (dep_order L Hnd1 Hrank1) (λ op, op ∈ L) HRV
             (delivered_ops h1) (delivered_ops h2) s1).
    - move=> x Hx. exact Hx.
    - move=> x Hx. by apply HL2.
    - exact (dep_hb_consistent L _ Hnd1 Hrank1 Hnd1 Hrank1).
    - exact (dep_hb_consistent L _ Hnd1 Hrank1 Hnd2 Hrank2).
    - exact (dep_hbClosed L _ Hnd1 Hrank1 Hnd1 Hrank1).
    - exact (dep_hbClosed L _ Hnd1 Hrank1 Hnd2 Hrank2).
    - exact (dep_concurrent_distinct N c1 h1 L Hnd1 Hrank1 Hwf Hpre1 HL1).
    - exact (delivered_IdNoDup N c1 h1 Hwf Hpre1).
    - exact (delivered_IdNoDup N c2 h2 Hwf Hpre2).
    - exact HL2.
    - exact Hinterp1. }
  have Hs : s1 = s2 := doc_effect_list_det (delivered_ops h2) (op_init O) s1 s2 Heff2 Hinterp2.
  move=> t. rewrite -(Hm1 t) -(Hm2 t) Hs //.
Qed.

End network_convergence.
