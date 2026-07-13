(** The pure bridge to the rocq-yjs network model (issues #42, #49).

    Everything here is Iris-free: it re-states the network-model records
    ([NodeHistories] / [NetworkBase] / [CausalNetwork] / [OperationNetwork] /
    [DocOperationNetwork]) over a raw [gmap ClientId (list Event)] — the shape a
    Perennial [ghost_map] carries — and proves the append-preservation and
    certificate lemmas the ghost layer ([yjs_history]) consumes.

    Since #49 the operations are *doc-level*: [TypeId * YjsOperation]
    ([yjs_doc_model]), one network/history per document with doc-global
    clocks/causality, integration per type. Per-type facts (validity of a
    delivered insert, item membership) are obtained by projecting the packaged
    doc network to a [YjsOperationNetwork] ([to_proj_network] =
    [proj_network ∘ to_doc_network]) and applying the upstream theorems.

    - [history_wf N]: the conjunction of the model's network axioms over the raw
      map, plus the two disciplines of our instantiation (immediate
      self-delivery, insert-only history). Re-establishing it at each ghost
      append IS the proof that the WP state refines the network model.
    - [to_doc_network N wf : DocOperationNetwork]: packaging, so the model's
      endgame theorems ([doc_strong_convergence],
      [DocOperationNetwork_converge_final]) apply to the ghost state directly
      (consumed at the ghost boundary by #40).
    - [history_state_coh h m]: the lock-side tie — the events of [h] replay to
      a document whose per-type item lists are [m : gmap TypeId (list item)].
    - the lemma stack: happens-before append-stability, freshness, receiver
      clock safety, the broadcast / deliver steps, and [certs_ValidReplay] (the
      certificate-based justification of [applyUpdate]'s [ValidReplay]).

    [ValidReplay] itself lives here (moved from [yjs_store], where it was born):
    it is a pure inductive over model types, and [certs_ValidReplay] produces it.

    Iterate on this file alone with rocq-mcp; it compiles without goose
    output. *)
From stdpp Require Import base list gmap sorting.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.
From New.proof Require Import yjs_core.
From New.proof Require Export yjs_doc_model.
From yjs.algorithm Require Export toitem_lemmas.
From yjs.algorithm Require Import findptridx_insert.
From yjs.crdt.operation Require Export causal_order hb_closed strong_causal_order.
From yjs.crdt.network Require Export causal_network operation_network.
From yjs.network Require Export yjs_network yjs_operation_network yjs_replay_validity.

Section network_model.
Context {A : Type} `{EqDA : EqDecision A}.
Context {P : Type} `{EqDP : !EqDecision P} `{CntP : !Countable P}.

Local Notation TId := (TypeId P).
(** The per-type (upstream) operation instance and its id. *)
Local Notation Oy := (@YjsOp A EqDA).
Local Notation yopid := (@YjsOperation_id A).
(** The doc-level operations of the raw histories (issue #49). *)
Local Notation Op := (TId * @YjsOperation A)%type.
Local Notation opid := (DocOp_id (A := A) (P := P)).
Local Notation O := (DocO (A := A) (P := P)).
Local Notation Ev := (@Event Op).
Local Notation RawHistories := (gmap ClientId (list Ev)).
(** The per-type item-list view of a doc state. *)
Local Notation DocM := (gmap TId (list (YjsItem A))).

Implicit Types (N : RawHistories) (h : list Ev) (op : Op) (c i j : ClientId).

Set Default Proof Using "Type*".

(* ===== raw-history views ================================================== *)

(** The per-client history function a raw map denotes (absent = empty). *)
Definition to_histories N : ClientId -> list Ev :=
  fun i => default [] (N !! i).

(** Ops delivered in one raw history, in order (= the model's
    [toDeliverMessages] on the packaged network). *)
Definition delivered_ops h : list Op := omap deliverP h.

Definition delivered_ids h : gset YjsId := list_to_set (opid <$> delivered_ops h).

(** [op] was broadcast somewhere in the network / some broadcast carries [id]. *)
Definition op_broadcast N op : Prop := ∃ i, EvBroadcast op ∈ to_histories N i.
Definition id_broadcast N (id : YjsId) : Prop := ∃ op, op_broadcast N op ∧ opid op = id.

(* ----- small rewrites ----- *)

Lemma to_histories_lookup N c h : N !! c = Some h -> to_histories N c = h.
Proof. rewrite /to_histories => -> //. Qed.

Lemma to_histories_insert N c l : to_histories (<[c := l]> N) c = l.
Proof. rewrite /to_histories lookup_insert_eq //. Qed.

Lemma to_histories_insert_ne N c l i : i ≠ c -> to_histories (<[c := l]> N) i = to_histories N i.
Proof. move=> Hne. rewrite /to_histories lookup_insert_ne //. Qed.

Lemma delivered_ops_app h1 h2 : delivered_ops (h1 ++ h2) = delivered_ops h1 ++ delivered_ops h2.
Proof. rewrite /delivered_ops omap_app //. Qed.

Lemma delivered_ops_broadcast op : delivered_ops [EvBroadcast op] = [].
Proof. reflexivity. Qed.

Lemma delivered_ops_deliver op : delivered_ops [EvDeliver op] = [op].
Proof. reflexivity. Qed.

Lemma delivered_ids_app h1 h2 :
  delivered_ids (h1 ++ h2) = delivered_ids h1 ∪ delivered_ids h2.
Proof. rewrite /delivered_ids delivered_ops_app fmap_app list_to_set_app_L //. Qed.

Lemma elem_of_delivered_ids h (id : YjsId) :
  id ∈ delivered_ids h ↔ ∃ op, EvDeliver op ∈ h ∧ opid op = id.
Proof.
  rewrite /delivered_ids elem_of_list_to_set list_elem_of_fmap.
  split.
  - move=> [op [-> Hin]]. exists op. split; [| done].
    move: Hin. rewrite /delivered_ops list_elem_of_omap => -[ev [Hev Hdel]].
    destruct ev as [a | a]; simpl in Hdel; [done | by injection Hdel as ->].
  - move=> [op [Hin <-]]. exists op. split; [done |].
    rewrite /delivered_ops list_elem_of_omap. by exists (EvDeliver op).
Qed.

(** Membership of a broadcast under a one-client append. *)
Lemma op_broadcast_append N c h tail op :
  N !! c = Some h ->
  op_broadcast (<[c := h ++ tail]> N) op ↔ op_broadcast N op ∨ EvBroadcast op ∈ tail.
Proof.
  move=> Hc. rewrite /op_broadcast. split.
  - move=> [i Hin].
    destruct (decide (i = c)) as [-> | Hne].
    + rewrite to_histories_insert elem_of_app in Hin.
      destruct Hin as [Hin | Hin]; [left; exists c; by rewrite (to_histories_lookup _ _ _ Hc) | by right].
    + rewrite (to_histories_insert_ne _ _ _ _ Hne) in Hin. left; by exists i.
  - move=> [[i Hin] | Hin].
    + destruct (decide (i = c)) as [-> | Hne].
      * exists c. rewrite to_histories_insert elem_of_app. left.
        by rewrite (to_histories_lookup _ _ _ Hc) in Hin.
      * exists i. by rewrite (to_histories_insert_ne _ _ _ _ Hne).
    + exists c. rewrite to_histories_insert elem_of_app. by right.
Qed.

(* ===== raw happens-before ================================================= *)

(** Local order / happens-before over a plain histories function — no record,
    no wf proof term. Definitionally equal to the model's [locallyOrdered] /
    [HappensBefore] once packaged ([raw_hb_HappensBefore]). *)
Definition raw_lo (hs : ClientId -> list Ev) i (e1 e2 : Ev) : Prop :=
  ∃ l1 l2 l3, hs i = l1 ++ [e1] ++ l2 ++ [e2] ++ l3.

Inductive raw_hb (hs : ClientId -> list Ev) : Op -> Op -> Prop :=
  | raw_hb_bb i x y : raw_lo hs i (EvBroadcast x) (EvBroadcast y) -> raw_hb hs x y
  | raw_hb_db i x y : raw_lo hs i (EvDeliver x) (EvBroadcast y) -> raw_hb hs x y
  | raw_hb_trans x y z : raw_hb hs x y -> raw_hb hs y z -> raw_hb hs x z.

(** [raw_lo]/[raw_hb] over [histories nb] are the model's [locallyOrdered] /
    [HappensBefore] (they unfold to the same splits). *)
Lemma raw_lo_locallyOrdered (nb : @NodeHistories Op) i (e1 e2 : Ev) :
  raw_lo (histories nb) i e1 e2 ↔ locallyOrdered nb i e1 e2.
Proof. done. Qed.

Lemma raw_hb_HappensBefore (nb : @NetworkBase Op YjsId opid) (x y : Op) :
  raw_hb (histories nb) x y ↔ HappensBefore opid nb x y.
Proof.
  split.
  - elim => [i' x' y' Hlo | i' x' y' Hlo | x' y' z' _ IH1 _ IH2].
    + exact: hb_bb Hlo.
    + exact: hb_db Hlo.
    + exact: hb_trans IH1 IH2.
  - elim => [i' x' y' Hlo | i' x' y' Hlo | x' y' z' _ IH1 _ IH2].
    + exact: raw_hb_bb Hlo.
    + exact: raw_hb_db Hlo.
    + exact: raw_hb_trans IH1 IH2.
Qed.

(** A membership split: an element of a history gives a [raw_lo]-style split. *)
Lemma elem_of_split_lo (hs : ClientId -> list Ev) i (e1 e2 : Ev) l1 l2 :
  hs i = l1 ++ [e1] ++ l2 -> e2 ∈ l2 -> raw_lo hs i e1 e2.
Proof.
  move=> Hh Hin.
  have [l2a [l2b Hl2]] := list_elem_of_split _ _ Hin.
  exists l1, l2a, l2b. rewrite Hh Hl2 //.
Qed.

(* ===== history_wf ========================================================= *)

(** The model's network axioms over the raw map, plus our two disciplines.
    The [interpHistory]-mentioning fields use the Yjs operation instance [O]
    with [YjsIsValidMessage] (the [OperationNetwork] instantiation). *)
Record history_wf N : Prop := {
  (* NodeHistories *)
  hwf_nodup : ∀ i, NoDup (to_histories N i);
  (* NetworkBase *)
  hwf_deliver_has_a_cause : ∀ i e,
    EvDeliver e ∈ to_histories N i -> ∃ j, EvBroadcast e ∈ to_histories N j;
  hwf_msg_id_unique : ∀ mi mj i j,
    EvBroadcast mi ∈ to_histories N i -> EvBroadcast mj ∈ to_histories N j ->
    opid mi = opid mj -> i = j ∧ mi = mj;
  (* CausalNetwork *)
  hwf_causal_delivery : ∀ i e1 e2,
    EvDeliver e2 ∈ to_histories N i -> raw_hb (to_histories N) e1 e2 ->
    raw_lo (to_histories N) i (EvDeliver e1) (EvDeliver e2);
  (* OperationNetwork, isValidMessage := DocIsValidMessage *)
  hwf_broadcast_valid : ∀ i e pre post,
    to_histories N i = pre ++ [EvBroadcast e] ++ post ->
    ∃ s, interpHistory O pre (op_init O) s ∧ DocIsValidMessage s e;
  (* DocOperationNetwork: doc-global clock discipline *)
  hwf_client_id : ∀ e i,
    EvBroadcast e ∈ to_histories N i -> clientId (opid e) = i;
  hwf_unique_id : ∀ e i hist1 hist2 array,
    to_histories N i = hist1 ++ [EvBroadcast e] ++ hist2 ->
    interpHistory O hist1 (op_init O) array ->
    DocOperation_UniqueId e array;
  (* ours: a broadcast is immediately followed by its own delivery. *)
  hwf_self_deliver : ∀ i e pre post,
    to_histories N i = pre ++ [EvBroadcast e] ++ post ->
    ∃ post', post = EvDeliver e :: post';
  (* ours: insert-only history (plan §8.1). *)
  hwf_insert_only : ∀ i e,
    (EvBroadcast e ∈ to_histories N i ∨ EvDeliver e ∈ to_histories N i) ->
    ∃ input, e.2 = OpInsert input;
}.

(** Gomes-form [deliver_locally], derived from [hwf_self_deliver]. *)
Lemma hwf_deliver_locally N (wf : history_wf N) : ∀ i e,
  EvBroadcast e ∈ to_histories N i ->
  raw_lo (to_histories N) i (EvBroadcast e) (EvDeliver e).
Proof.
  move=> i e Hin.
  have [pre [post Hsplit]] := list_elem_of_split _ _ Hin.
  have Hsplit' : to_histories N i = pre ++ [EvBroadcast e] ++ post by rewrite Hsplit.
  have [post' Hpost] := hwf_self_deliver N wf i e pre post Hsplit'.
  exists pre, [], post'. rewrite Hsplit' Hpost //.
Qed.

(** The left end of a happens-before edge is a broadcast op (via
    [hwf_deliver_has_a_cause] for delivery-anchored edges); so is the right. *)
Lemma raw_hb_left_broadcast N (wf : history_wf N) (x y : Op) :
  raw_hb (to_histories N) x y -> op_broadcast N x.
Proof.
  elim => [i' x' y' Hlo | i' x' y' Hlo | x' y' z' Hxy IH1 _ _].
  - move: Hlo => [l1 [l2 [l3 Hh]]]. exists i'. rewrite Hh. set_solver.
  - move: Hlo => [l1 [l2 [l3 Hh]]].
    apply (hwf_deliver_has_a_cause N wf i'). rewrite Hh. set_solver.
  - exact IH1.
Qed.

Lemma raw_hb_right_broadcast N (x y : Op) :
  raw_hb (to_histories N) x y -> op_broadcast N y.
Proof.
  elim => [i' x' y' Hlo | i' x' y' Hlo | x' y' z' _ _ _ IH2].
  - move: Hlo => [l1 [l2 [l3 Hh]]]. exists i'. rewrite Hh. set_solver.
  - move: Hlo => [l1 [l2 [l3 Hh]]]. exists i'. rewrite Hh. set_solver.
  - exact IH2.
Qed.

(* ===== packaging: to_network ============================================== *)

Definition to_nodehistories N (wf : history_wf N) : @NodeHistories Op :=
  {| histories := to_histories N; event_distinct := hwf_nodup N wf |}.

Program Definition to_network_base N (wf : history_wf N) : @NetworkBase Op YjsId opid :=
  {| nb_nodes := to_nodehistories N wf;
     deliver_has_a_cause := hwf_deliver_has_a_cause N wf;
     deliver_locally := _;
     msg_id_unique := hwf_msg_id_unique N wf |}.
Next Obligation.
  move=> N wf i e Hin. exact (hwf_deliver_locally N wf i e Hin).
Qed.

Program Definition to_causal_network N (wf : history_wf N) : @CausalNetwork Op YjsId opid :=
  {| cn_base := to_network_base N wf; causal_delivery := _ |}.
Next Obligation.
  move=> N wf i e1 e2 Hdel Hhb.
  apply (hwf_causal_delivery N wf i e1 e2 Hdel).
  apply (raw_hb_HappensBefore (to_network_base N wf)). exact Hhb.
Qed.

Program Definition to_operation_network N (wf : history_wf N) :
    @OperationNetwork Op YjsId opid O (DocIsValidMessage (A := A) (P := P)) :=
  {| on_net := to_causal_network N wf;
     broadcast_only_valid_messages := hwf_broadcast_valid N wf |}.

Program Definition to_doc_network N (wf : history_wf N) :
    DocOperationNetwork (A := A) (P := P) :=
  {| don_net := to_operation_network N wf;
     don_client_id := hwf_client_id N wf;
     don_UniqueId := hwf_unique_id N wf |}.

(** The packaged network's histories are the raw ones, definitionally. *)
Lemma to_doc_network_histories N (wf : history_wf N) :
  histories (to_doc_network N wf) = to_histories N.
Proof. reflexivity. Qed.

(** The per-type view: project the packaged doc network down to a
    [YjsOperationNetwork], through which the upstream replay-validity
    theorems apply. *)
Definition to_proj_network (t : TId) N (wf : history_wf N) : YjsOperationNetwork (A := A) :=
  proj_network t (to_doc_network N wf).

Lemma to_proj_network_histories (t : TId) N (wf : history_wf N) (i : ClientId) :
  histories (to_proj_network t N wf) i = proj_hist t (to_histories N i).
Proof. reflexivity. Qed.

(** Membership of a per-type op list in the doc list. *)
Lemma elem_of_proj_ops (t : TId) (l : list Op) (x : @YjsOperation A) :
  x ∈ proj_ops t l <-> (t, x) ∈ l.
Proof.
  rewrite /proj_ops list_elem_of_omap. split.
  - move=> [dop [Hdop Hp]]. apply proj_op_Some in Hp. by subst dop.
  - move=> Hin. exists (t, x). split; [done | exact (proj_op_pair t x)].
Qed.

(** Projection of the delivered ops. *)
Lemma delivered_ops_proj (t : TId) h :
  proj_ops t (delivered_ops h) = omap deliverP (proj_hist t h).
Proof. rewrite /delivered_ops proj_deliver_comm //. Qed.

(* ===== local coherence (lock-side tie) ==================================== *)

(** The per-type item list a [DocM] denotes (absent = empty; a [DocM] with an
    explicit empty entry and one without are the same document). *)
Definition docm_get (m : DocM) (t : TId) : list (YjsItem A) := default [] (m !! t).

Lemma docm_get_insert_eq (m : DocM) t arr : docm_get (<[t := arr]> m) t = arr.
Proof. rewrite /docm_get lookup_insert_eq //. Qed.

Lemma docm_get_insert_ne (m : DocM) t t' arr :
  t' ≠ t -> docm_get (<[t := arr]> m) t' = docm_get m t'.
Proof. move=> Hne. rewrite /docm_get lookup_insert_ne //. Qed.

(** The events of [h] replay (delivers only) to a doc state whose per-type item
    lists are [m]. Tombstone flags are NOT tracked by the history (plan §8.4),
    so the per-type deleted sets stay existential inside the doc state. *)
Definition history_state_coh h (m : DocM) : Prop :=
  ∃ s, interpHistory O h (op_init O) s ∧ ∀ t, st_items (doc_get s t) = docm_get m t.

Lemma history_state_coh_nil : history_state_coh [] ∅.
Proof.
  exists (op_init O). split.
  - rewrite /interpHistory /=. by apply (effect_list_nil O).
  - move=> t. rewrite doc_get_empty /docm_get lookup_empty //.
Qed.

(** Replay determinism, at the coherence level (as documents: pointwise). *)
Lemma history_state_coh_det h m m' :
  history_state_coh h m -> history_state_coh h m' ->
  ∀ t, docm_get m t = docm_get m' t.
Proof.
  move=> [s [Hs Hm]] [s' [Hs' Hm']] t.
  have Heq : s = s' := doc_effect_list_det (omap deliverP h) (op_init O) s s' Hs Hs'.
  rewrite -(Hm t) -(Hm' t) Heq //.
Qed.

(** Coherence projects to a per-type replay of the projected history. *)
Lemma history_state_coh_proj h (m : DocM) (t : TId) :
  history_state_coh h m ->
  ∃ st, interpHistory Oy (proj_hist t h) (op_init Oy) st ∧ st_items st = docm_get m t.
Proof.
  move=> [s [Hs Hm]]. exists (doc_get s t).
  split; [| exact (Hm t)].
  exact (doc_interp_proj h s t Hs).
Qed.

(** Appending a broadcast event does not change the replayed state. *)
Lemma interpHistory_snoc_broadcast h op (init s : op_State O) :
  interpHistory O h init s -> interpHistory O (h ++ [EvBroadcast op]) init s.
Proof.
  rewrite /interpHistory omap_app /= app_nil_r //.
Qed.

(** Appending a delivery steps the replayed state by the op's effect. *)
Lemma interpHistory_snoc_deliver h op (init s s' : op_State O) :
  interpHistory O h init s -> op_effect O op s s' ->
  interpHistory O (h ++ [EvDeliver op]) init s'.
Proof.
  rewrite /interpHistory omap_app /= => Hh Heff.
  apply (effect_list_snoc O). by exists s.
Qed.

(* ===== toItem / clock-safety glue ========================================= *)

(** Clock-safety of the input is exactly clock-maximality of the resolved item
    (converse direction of the upstream [isClockSafe_maximalId]). *)
Lemma maximalId_isClockSafe (input : IntegrateInput (A := A)) (arr : list (YjsItem A))
    (item : YjsItem A) :
  toItem input arr = Some item ->
  maximalId item arr ->
  isClockSafe (in_id input) arr = true.
Proof.
  move=> Htoitem Hmax.
  pose proof (toItem_id input arr item Htoitem) as Hid.
  rewrite /isClockSafe. apply Is_true_eq_true, forallb_True, Forall_forall => x Hx.
  destruct (decide (clientId (item_id x) = clientId (in_id input))) as [Hc | Hc].
  - rewrite (bool_decide_eq_true_2 _ Hc) /=.
    apply Is_true_eq_left, bool_decide_eq_true_2.
    rewrite -Hid. apply (Hmax x Hx). rewrite Hid. exact Hc.
  - rewrite (bool_decide_eq_false_2 _ Hc) //.
Qed.

(** A successful [toItem] resolution determines the input from the item: the
    input is exactly the item's origin-id / right-origin-id / content / id.
    ([origin_id] is the id of an item pointer, [None] at the sentinels —
    from [insert_set].) *)
Definition input_of_item (it : YjsItem A) : IntegrateInput (A := A) :=
  MkIntegrateInput (origin_id (origin it)) (origin_id (rightOrigin it)) (content it) (item_id it).

Lemma toItem_input_of_item (input : IntegrateInput (A := A)) (arr : list (YjsItem A))
    (it : YjsItem A) :
  toItem input arr = Some it -> input = input_of_item it.
Proof.
  move=> Htoitem.
  pose proof (proj1 (toItem_ok_iff input arr it) Htoitem)
    as (o & r & id & ct & Hdef & HoL & HoR & Hid & Hct).
  rewrite /input_of_item Hdef /origin /rightOrigin /item_id /content.
  move: HoL HoR. rewrite /isLeftIdPtr /isRightIdPtr.
  destruct (in_originId input) as [oid |] eqn:HoidL;
    destruct (in_rightOriginId input) as [rid |] eqn:HoidR.
  - move=> [oit [Hoeq Hfo]] [rit [Hreq Hfr]]. subst o r.
    pose proof (find_by_id_id oid arr oit Hfo) as Hoid.
    pose proof (find_by_id_id rid arr rit Hfr) as Hrid.
    destruct input; simpl in *; congruence.
  - move=> [oit [Hoeq Hfo]] Hr. subst o r.
    pose proof (find_by_id_id oid arr oit Hfo) as Hoid.
    destruct input; simpl in *; congruence.
  - move=> Ho [rit [Hreq Hfr]]. subst o r.
    pose proof (find_by_id_id rid arr rit Hfr) as Hrid.
    destruct input; simpl in *; congruence.
  - move=> Ho Hr. subst o r. destruct input; simpl in *; congruence.
Qed.

(** The concrete FIRST insert (both origins sentinels, clock 0) into an empty
    document: resolution, validity, maximality, the resulting singleton
    splice, and its invariant. The ghost layer's smoke tests ([history_smoke],
    [history_converge_smoke]) broadcast and deliver exactly this op. *)
Lemma first_insert_facts (c : nat) (a : A) :
  toItem (MkIntegrateInput (A := A) None None a (MkYjsId c 0)) ([] : list (YjsItem A))
    = Some (Item (A := A) First Last (MkYjsId c 0) a) ∧
  IsItemValid (Item (A := A) First Last (MkYjsId c 0) a) ∧
  maximalId (Item (A := A) First Last (MkYjsId c 0) a) ([] : list (YjsItem A)) ∧
  integrate (MkIntegrateInput (A := A) None None a (MkYjsId c 0)) ([] : list (YjsItem A))
    = Some [Item (A := A) First Last (MkYjsId c 0) a] ∧
  YjsArrInvariant [Item (A := A) First Last (MkYjsId c 0) a].
Proof.
  set (input := MkIntegrateInput (A := A) None None a (MkYjsId c 0)).
  set (item := Item (A := A) First Last (MkYjsId c 0) a).
  have Htoitem : toItem input ([] : list (YjsItem A)) = Some item by done.
  have Hvalid : IsItemValid item.
  { split.
    - apply YjsLt'_ltOriginOrder. exact lt_first_last.
    - move=> x Hx.
      inversion Hx as [x0 y0 Hstep | x0 y0 z0 Hstep Hreach]; subst.
      + inversion Hstep; subst; [left | right]; exists 0%nat; exact (leqSame _ _).
      + inversion Hstep; subst;
          inversion Hreach as [x1 y1 Hstep2 | x1 y1 z1 Hstep2 ?]; subst;
          inversion Hstep2. }
  have Hmax : maximalId item ([] : list (YjsItem A)).
  { move=> x Hx. exfalso. move: Hx. rewrite /ArrSet /= elem_of_nil //. }
  have Hint : integrate input ([] : list (YjsItem A)) = Some [item] by vm_compute.
  destruct (YjsArrInvariant_integrate input [] [item] item YjsArrInvariant_empty
              Htoitem Hvalid Hmax Hint) as (didx & _ & _ & Hinv).
  split_and!; [exact Htoitem | exact Hvalid | exact Hmax | exact Hint | exact Hinv].
Qed.

Lemma YjsArrInvariant_first_item (c : nat) (a : A) :
  YjsArrInvariant [Item (A := A) First Last (MkYjsId c 0) a].
Proof. destruct (first_insert_facts c a) as (_ & _ & _ & _ & Hinv). exact Hinv. Qed.

(* ===== happens-before append stability ==================================== *)

(** (a) Monotonicity: appending a tail to one client's history preserves every
    happens-before edge (splits survive appends). *)
Lemma raw_hb_append_mono N c h (tail : list Ev) (x y : Op) :
  N !! c = Some h ->
  raw_hb (to_histories N) x y ->
  raw_hb (to_histories (<[c := h ++ tail]> N)) x y.
Proof.
  move=> Hc Hhb.
  have Hlo : ∀ i e1 e2, raw_lo (to_histories N) i e1 e2 ->
             raw_lo (to_histories (<[c := h ++ tail]> N)) i e1 e2.
  { move=> i e1 e2 [l1 [l2 [l3 Hh]]].
    destruct (decide (i = c)) as [-> | Hne].
    - exists l1, l2, (l3 ++ tail).
      rewrite to_histories_insert (to_histories_lookup _ _ _ Hc) in Hh |- *.
      rewrite Hh -!app_assoc //.
    - exists l1, l2, l3. rewrite (to_histories_insert_ne _ _ _ _ Hne) //. }
  elim: Hhb => [i' x' y' H | i' x' y' H | x' y' z' _ IH1 _ IH2].
  - apply (raw_hb_bb _ i'). exact: Hlo.
  - apply (raw_hb_db _ i'). exact: Hlo.
  - exact: raw_hb_trans IH1 IH2.
Qed.

(** A split whose second pivot avoids the appended tail confines to the
    original list (no duplicate-freeness needed — pure position counting). *)
Lemma lo_app_confine (l t : list Ev) (e1 e2 : Ev) (l1 l2 l3 : list Ev) :
  l ++ t = l1 ++ [e1] ++ l2 ++ [e2] ++ l3 ->
  e2 ∉ t ->
  ∃ l3', l = l1 ++ [e1] ++ l2 ++ [e2] ++ l3'.
Proof.
  move=> Heq Hnot.
  set n := (length l1 + S (length l2))%nat.
  have Hlk : (l ++ t) !! n = Some e2.
  { rewrite Heq /n /=.
    rewrite lookup_app_r; [| lia].
    have -> : (length l1 + S (length l2) - length l1)%nat = S (length l2) by lia.
    rewrite /= lookup_app_r; [| lia].
    have -> : (length l2 - length l2)%nat = 0%nat by lia.
    done. }
  have Hlt : (n < length l)%nat.
  { destruct (decide (n < length l)%nat) as [| Hge]; [done | exfalso].
    move: Hlk. rewrite lookup_app_r; [| lia]. move=> Hlk.
    apply Hnot. exact (list_elem_of_lookup_2 _ _ _ Hlk). }
  have Htake : take (S n) l = l1 ++ [e1] ++ l2 ++ [e2].
  { have H1 : take (S n) (l ++ t) = take (S n) l by (rewrite take_app_le; [done | lia]).
    rewrite Heq in H1. rewrite -H1.
    have -> : l1 ++ [e1] ++ l2 ++ [e2] ++ l3 = (l1 ++ [e1] ++ l2 ++ [e2]) ++ l3
      by rewrite -!app_assoc.
    have -> : S n = length (l1 ++ [e1] ++ l2 ++ [e2]) by (rewrite !length_app /n /=; lia).
    rewrite take_app_length //. }
  exists (drop (S n) l).
  rewrite -{1}(take_drop (S n) l) Htake -!app_assoc //.
Qed.

(** The fresh tail [B op; D op] is duplicate-free on top of [h], and neither
    of the new op's events occurs in [h]. *)
Lemma fresh_tail_nodup N c h op :
  history_wf N -> N !! c = Some h ->
  ¬ id_broadcast N (opid op) ->
  NoDup (h ++ [EvBroadcast op; EvDeliver op]) ∧
  EvBroadcast op ∉ h ∧ EvDeliver op ∉ h.
Proof.
  move=> Hwf Hc Hfresh.
  have Hbh : EvBroadcast op ∉ h.
  { move=> Hin. apply Hfresh. exists op. split; [| done].
    exists c. rewrite (to_histories_lookup N c h Hc) //. }
  have Hdh : EvDeliver op ∉ h.
  { move=> Hin. apply Hfresh.
    have Hin' : EvDeliver op ∈ to_histories N c by rewrite (to_histories_lookup N c h Hc).
    pose proof (hwf_deliver_has_a_cause N Hwf c op Hin') as (j & Hj).
    exists op. split; [by exists j | done]. }
  split_and!; [| exact Hbh | exact Hdh].
  apply NoDup_app. split_and!.
  - rewrite -(to_histories_lookup N c h Hc). exact (hwf_nodup N Hwf c).
  - move=> e He. rewrite !elem_of_cons elem_of_nil. move=> [Heq | [Heq | []]]; subst e.
    + exact (Hbh He).
    + exact (Hdh He).
  - apply NoDup_cons_2.
    + rewrite elem_of_cons elem_of_nil. move=> [Heq | []]. discriminate.
    + apply NoDup_cons_2; [rewrite elem_of_nil; move=> [] | constructor].
Qed.

(** A broadcast is self-delivered within the same (raw) history. *)
Lemma self_deliver_mem N c h (u : Op) :
  history_wf N -> N !! c = Some h ->
  EvBroadcast u ∈ h -> EvDeliver u ∈ h.
Proof.
  move=> Hwf Hc Hin.
  have Hin' : EvBroadcast u ∈ to_histories N c by rewrite (to_histories_lookup N c h Hc).
  pose proof (hwf_deliver_locally N Hwf c u Hin') as (l1 & l2 & l3 & Hsplit).
  rewrite (to_histories_lookup N c h Hc) in Hsplit.
  rewrite Hsplit. set_solver.
Qed.

(** (b) Reflection: for [y] broadcast in [N] (and the appended tail containing
    no broadcast of an old op), a happens-before edge of the extended network
    between old ops already held in [N]. *)
Lemma raw_hb_append_old N c h (tail : list Ev) (x y : Op) :
  history_wf N -> N !! c = Some h ->
  (∀ e, EvBroadcast e ∈ tail -> ¬ op_broadcast N e) ->
  op_broadcast N y ->
  raw_hb (to_histories (<[c := h ++ tail]> N)) x y ->
  raw_hb (to_histories N) x y.
Proof.
  move=> Hwf Hc Htail Hy Hhb.
  (* generalize over the (old-broadcast) right end for the transitivity case *)
  move: Hy.
  elim: Hhb => [i' x' y' Hlo | i' x' y' Hlo | x' y' z' Hxy IH1 Hyz IH2] Hold.
  - (* B x' <_i B y' *)
    destruct (decide (i' = c)) as [-> | Hne];
      last by (apply (raw_hb_bb _ i'); move: Hlo;
               rewrite /raw_lo (to_histories_insert_ne _ _ _ _ Hne)).
    move: Hlo => [l1 [l2 [l3 Hsplit]]].
    rewrite to_histories_insert in Hsplit.
    have Hnotin : EvBroadcast y' ∉ tail.
    { move=> Hin. exact (Htail y' Hin Hold). }
    pose proof (lo_app_confine h tail _ _ l1 l2 l3 Hsplit Hnotin) as (l3' & Hh).
    apply (raw_hb_bb _ c). exists l1, l2, l3'.
    rewrite (to_histories_lookup N c h Hc) //.
  - (* D x' <_i B y' *)
    destruct (decide (i' = c)) as [-> | Hne];
      last by (apply (raw_hb_db _ i'); move: Hlo;
               rewrite /raw_lo (to_histories_insert_ne _ _ _ _ Hne)).
    move: Hlo => [l1 [l2 [l3 Hsplit]]].
    rewrite to_histories_insert in Hsplit.
    have Hnotin : EvBroadcast y' ∉ tail.
    { move=> Hin. exact (Htail y' Hin Hold). }
    pose proof (lo_app_confine h tail _ _ l1 l2 l3 Hsplit Hnotin) as (l3' & Hh).
    apply (raw_hb_db _ c). exists l1, l2, l3'.
    rewrite (to_histories_lookup N c h Hc) //.
  - (* transitivity: reflect the right leg first, learn [y'] is old, recurse *)
    have Hyz' : raw_hb (to_histories N) y' z' := IH2 Hold.
    have Hy' : op_broadcast N y' := raw_hb_left_broadcast N Hwf y' z' Hyz'.
    exact (raw_hb_trans _ _ _ _ (IH1 Hy') Hyz').
Qed.

(** A freshly appended op (its only events are the tail of [c]'s history, and
    its id is not broadcast elsewhere) has no happens-before successors. *)
Lemma fresh_op_no_succ N c h op (z : Op) :
  history_wf N -> N !! c = Some h ->
  ¬ id_broadcast N (opid op) ->
  ¬ raw_hb (to_histories (<[c := h ++ [EvBroadcast op; EvDeliver op]]> N)) op z.
Proof.
  move=> Hwf Hc Hfresh.
  pose proof (fresh_tail_nodup N c h op Hwf Hc Hfresh) as (Hnd & Hbh & Hdh).
  set tail := [EvBroadcast op; EvDeliver op].
  assert (Haux : ∀ u v : Op,
    raw_hb (to_histories (<[c := h ++ tail]> N)) u v -> u = op -> False).
  2:{ move=> Hhb. exact (Haux op z Hhb eq_refl). }
  move=> u v Hhb. elim: Hhb => [i' x' y' Hlo | i' x' y' Hlo | x' y' z' Hxy IH1 Hyz IH2] Hequ;
    last exact (IH1 Hequ).
  - (* B op <_i B y': nothing follows the fresh broadcast but its delivery *)
    subst x'.
    destruct (decide (i' = c)) as [-> | Hne].
    2:{ move: Hlo => [l1 [l2 [l3 Hsplit]]].
        rewrite (to_histories_insert_ne _ _ _ _ Hne) in Hsplit.
        apply Hfresh. exists op. split; [| done].
        exists i'. rewrite Hsplit. set_solver. }
    move: Hlo => [l1 [l2 [l3 Hsplit]]].
    rewrite to_histories_insert in Hsplit.
    have Hx1 : EvBroadcast op ∉ l1.
    { apply (elem_not_in_of_nodup_mid l1 (l2 ++ [EvBroadcast y'] ++ l3)).
      rewrite -Hsplit //. }
    have Heq2 : l1 ++ EvBroadcast op :: (l2 ++ [EvBroadcast y'] ++ l3)
              = h ++ EvBroadcast op :: [EvDeliver op] by rewrite -Hsplit //.
    pose proof (nodup_app_mid_uniq (EvBroadcast op) l1 _ h _ Hx1 Hbh Heq2) as [_ Hsuf].
    destruct l2 as [| e l2]; simpl in Hsuf.
    + injection Hsuf as Hbv _. discriminate.
    + injection Hsuf as _ Hnil. by destruct l2.
  - (* D op <_i B y': nothing at all follows the fresh delivery *)
    subst x'.
    destruct (decide (i' = c)) as [-> | Hne].
    2:{ move: Hlo => [l1 [l2 [l3 Hsplit]]].
        rewrite (to_histories_insert_ne _ _ _ _ Hne) in Hsplit.
        apply Hfresh.
        have Hdel : EvDeliver op ∈ to_histories N i' by (rewrite Hsplit; set_solver).
        pose proof (hwf_deliver_has_a_cause N Hwf i' op Hdel) as (j & Hj).
        exists op. split; [by exists j | done]. }
    move: Hlo => [l1 [l2 [l3 Hsplit]]].
    rewrite to_histories_insert in Hsplit.
    have Hx1 : EvDeliver op ∉ l1.
    { apply (elem_not_in_of_nodup_mid l1 (l2 ++ [EvBroadcast y'] ++ l3)).
      rewrite -Hsplit //. }
    have Hnotmid : EvDeliver op ∉ h ++ [EvBroadcast op].
    { rewrite elem_of_app elem_of_cons elem_of_nil.
      move=> [Hin | [Heq | []]]; [exact (Hdh Hin) | discriminate]. }
    have Heq2 : l1 ++ EvDeliver op :: (l2 ++ [EvBroadcast y'] ++ l3)
              = (h ++ [EvBroadcast op]) ++ EvDeliver op :: [].
    { rewrite -Hsplit -!app_assoc //. }
    pose proof (nodup_app_mid_uniq (EvDeliver op) l1 _ (h ++ [EvBroadcast op]) _ Hx1 Hnotmid Heq2)
      as [_ Hsuf].
    by destruct l2.
Qed.

(** The causal past of a freshly broadcast op was already delivered at its
    author: everything below the new op is a delivery of [h]. *)
Lemma fresh_broadcast_past N c h op (x : Op) :
  history_wf N -> N !! c = Some h ->
  ¬ id_broadcast N (opid op) ->
  raw_hb (to_histories (<[c := h ++ [EvBroadcast op; EvDeliver op]]> N)) x op ->
  EvDeliver x ∈ h.
Proof.
  move=> Hwf Hc Hfresh.
  pose proof (fresh_tail_nodup N c h op Hwf Hc Hfresh) as (Hnd & Hbh & Hdh).
  set tail := [EvBroadcast op; EvDeliver op].
  have Htail : ∀ e : Op, EvBroadcast e ∈ tail -> ¬ op_broadcast N e.
  { move=> e He. rewrite /tail !elem_of_cons elem_of_nil in He.
    destruct He as [Heq | [Heq | []]]; [| discriminate].
    injection Heq as ->. move=> Hbc. apply Hfresh. by exists op. }
  assert (Haux : ∀ u v : Op,
    raw_hb (to_histories (<[c := h ++ tail]> N)) u v -> v = op -> EvDeliver u ∈ h).
  2:{ move=> Hhb. exact (Haux x op Hhb eq_refl). }
  move=> u v Hhb. elim: Hhb => [i' x' y' Hlo | i' x' y' Hlo | x' y' z' Hxy IH1 Hyz IH2] Heqv.
  - (* B x' <_i B op: at [c] (fresh elsewhere), so B x' ∈ h; self-deliver *)
    subst y'.
    destruct (decide (i' = c)) as [-> | Hne].
    2:{ exfalso. move: Hlo => [l1 [l2 [l3 Hsplit]]].
        rewrite (to_histories_insert_ne _ _ _ _ Hne) in Hsplit.
        apply Hfresh. exists op. split; [| done].
        exists i'. rewrite Hsplit. set_solver. }
    move: Hlo => [l1 [l2 [l3 Hsplit]]].
    rewrite to_histories_insert in Hsplit.
    have Hprem : EvBroadcast op ∉ l1 ++ [EvBroadcast x'] ++ l2.
    { apply (elem_not_in_of_nodup_mid _ l3).
      rewrite -!app_assoc /= -Hsplit //. }
    have Heq2 : (l1 ++ [EvBroadcast x'] ++ l2) ++ EvBroadcast op :: l3
              = h ++ EvBroadcast op :: [EvDeliver op].
    { rewrite -!app_assoc /= -Hsplit //. }
    pose proof (nodup_app_mid_uniq (EvBroadcast op) _ l3 h _ Hprem Hbh Heq2) as [Hpre _].
    have Hbx : EvBroadcast x' ∈ h by (rewrite -Hpre; set_solver).
    exact (self_deliver_mem N c h x' Hwf Hc Hbx).
  - (* D x' <_i B op: at [c], so D x' ∈ h directly *)
    subst y'.
    destruct (decide (i' = c)) as [-> | Hne].
    2:{ exfalso. move: Hlo => [l1 [l2 [l3 Hsplit]]].
        rewrite (to_histories_insert_ne _ _ _ _ Hne) in Hsplit.
        apply Hfresh. exists op. split; [| done].
        exists i'. rewrite Hsplit. set_solver. }
    move: Hlo => [l1 [l2 [l3 Hsplit]]].
    rewrite to_histories_insert in Hsplit.
    have Hprem : EvBroadcast op ∉ l1 ++ [EvDeliver x'] ++ l2.
    { apply (elem_not_in_of_nodup_mid _ l3).
      rewrite -!app_assoc /= -Hsplit //. }
    have Heq2 : (l1 ++ [EvDeliver x'] ++ l2) ++ EvBroadcast op :: l3
              = h ++ EvBroadcast op :: [EvDeliver op].
    { rewrite -!app_assoc /= -Hsplit //. }
    pose proof (nodup_app_mid_uniq (EvBroadcast op) _ l3 h _ Hprem Hbh Heq2) as [Hpre _].
    have Hdx : EvDeliver x' ∈ h by (rewrite -Hpre; set_solver).
    exact Hdx.
  - (* transitivity: the middle op is old and delivered in [h]; causal
       delivery of [N] pulls [u]'s delivery before it *)
    have Hdy : EvDeliver y' ∈ h := IH2 Heqv.
    have Hyold : op_broadcast N y'.
    { have Hdy' : EvDeliver y' ∈ to_histories N c by rewrite (to_histories_lookup N c h Hc).
      pose proof (hwf_deliver_has_a_cause N Hwf c y' Hdy') as (j & Hj). by exists j. }
    have Hxy' : raw_hb (to_histories N) x' y' :=
      raw_hb_append_old N c h tail x' y' Hwf Hc Htail Hyold Hxy.
    have Hdy' : EvDeliver y' ∈ to_histories N c by rewrite (to_histories_lookup N c h Hc).
    pose proof (hwf_causal_delivery N Hwf c x' y' Hdy' Hxy') as (l1 & l2 & l3 & Hsplit).
    rewrite (to_histories_lookup N c h Hc) in Hsplit.
    rewrite Hsplit. set_solver.
Qed.

(** Membership in an extended network: up (splits/members survive appends) and
    down (a member is old, or sits in the appended tail at [c]). *)
Lemma hist_mem_append_mono N c h (tail : list Ev) i (e : Ev) :
  N !! c = Some h ->
  e ∈ to_histories N i -> e ∈ to_histories (<[c := h ++ tail]> N) i.
Proof.
  move=> Hc Hin.
  destruct (decide (i = c)) as [-> | Hne].
  - rewrite to_histories_insert elem_of_app. left.
    rewrite -(to_histories_lookup N c h Hc) //.
  - rewrite (to_histories_insert_ne _ _ _ _ Hne) //.
Qed.

Lemma hist_mem_insert_case N c h (tail : list Ev) i (e : Ev) :
  N !! c = Some h ->
  e ∈ to_histories (<[c := h ++ tail]> N) i ->
  e ∈ to_histories N i ∨ (i = c ∧ e ∈ tail).
Proof.
  move=> Hc Hin.
  destruct (decide (i = c)) as [-> | Hne].
  - rewrite to_histories_insert elem_of_app in Hin.
    destruct Hin as [Hin | Hin];
      [left; rewrite (to_histories_lookup N c h Hc) // | by right].
  - rewrite (to_histories_insert_ne _ _ _ _ Hne) in Hin. by left.
Qed.

(** Local order survives a one-client append. *)
Lemma raw_lo_append_mono N c h (tail : list Ev) i (e1 e2 : Ev) :
  N !! c = Some h ->
  raw_lo (to_histories N) i e1 e2 ->
  raw_lo (to_histories (<[c := h ++ tail]> N)) i e1 e2.
Proof.
  move=> Hc [l1 [l2 [l3 Hh]]].
  destruct (decide (i = c)) as [-> | Hne].
  - exists l1, l2, (l3 ++ tail).
    rewrite to_histories_insert.
    rewrite (to_histories_lookup _ _ _ Hc) in Hh.
    rewrite Hh -!app_assoc //.
  - exists l1, l2, l3. rewrite (to_histories_insert_ne _ _ _ _ Hne) //.
Qed.

(** A split whose pivot avoids the appended tail confines to the original
    list, with the tail hanging off the suffix. *)
Lemma split_app_confine (l t : list Ev) (e : Ev) (pre post : list Ev) :
  l ++ t = pre ++ [e] ++ post ->
  e ∉ t ->
  ∃ post', l = pre ++ [e] ++ post' ∧ post = post' ++ t.
Proof.
  move=> Heq Hnot.
  set n := length pre.
  have Hlk : (l ++ t) !! n = Some e.
  { rewrite Heq /n list_lookup_middle //. }
  have Hlt : (n < length l)%nat.
  { destruct (decide (n < length l)%nat) as [| Hge]; [done | exfalso].
    move: Hlk. rewrite lookup_app_r; [| lia]. move=> Hlk.
    apply Hnot. exact (list_elem_of_lookup_2 _ _ _ Hlk). }
  have Htake : take (S n) l = pre ++ [e].
  { have H1 : take (S n) (l ++ t) = take (S n) l by (rewrite take_app_le; [done | lia]).
    rewrite Heq in H1. rewrite -H1.
    have -> : pre ++ [e] ++ post = (pre ++ [e]) ++ post by rewrite -!app_assoc.
    have -> : S n = length (pre ++ [e]) by (rewrite !length_app /n /=; lia).
    rewrite take_app_length //. }
  exists (drop (S n) l). split.
  - rewrite -{1}(take_drop (S n) l) Htake -!app_assoc //.
  - have Hdrop : drop (S n) (l ++ t) = drop (S n) l ++ t by (rewrite drop_app_le; [done | lia]).
    have Hdrop2 : drop (S n) (pre ++ [e] ++ post) = post.
    { have -> : pre ++ [e] ++ post = (pre ++ [e]) ++ post by rewrite -!app_assoc.
      have -> : S n = length (pre ++ [e]) by (rewrite !length_app /n /=; lia).
      rewrite drop_app_length //. }
    rewrite Heq Hdrop2 in Hdrop. rewrite Hdrop //.
Qed.

(* ===== freshness ========================================================== *)

(** A local clock bound makes the id globally fresh: any broadcast with client
    [c] happened at [c] (client-id discipline), was self-delivered into [h],
    so its item is in the replayed document (at its own type) with a smaller
    clock. The bound is doc-global — over every type's items. *)
Lemma history_fresh_id N c h (m : DocM) (k : nat) :
  history_wf N -> N !! c = Some h ->
  history_state_coh h m ->
  (∀ (t : TId) x, x ∈ docm_get m t -> clientId (item_id x) = c ->
     (clock (item_id x) < k)%nat) ->
  ¬ id_broadcast N (MkYjsId c k).
Proof.
  move=> Hwf Hc Hcoh Hbound [op [[i Hbc] Hopid]].
  (* a broadcast with client [c] happened at [c] itself *)
  have Hcid : clientId (opid op) = i := hwf_client_id N Hwf op i Hbc.
  have Hic : i = c by rewrite -Hcid Hopid.
  subst i. rewrite Hic in Hbc.
  (* ... and was immediately self-delivered into [h] *)
  pose proof (hwf_deliver_locally N Hwf c op Hbc) as (l1 & l2 & l3 & Hsplit).
  have Hdel : EvDeliver op ∈ h.
  { rewrite -(to_histories_lookup N c h Hc) Hsplit. set_solver. }
  pose proof (hwf_insert_only N Hwf c op (or_introl Hbc)) as (input & Hop2).
  destruct op as [tid inner]. simpl in Hop2. subst inner.
  (* so its item is in the replayed document at its type, with clock [k] *)
  pose proof (history_state_coh_proj h m tid Hcoh) as (st & Hinterp & Hitems).
  have Hmemev : EvDeliver (OpInsert input) ∈ proj_hist tid h.
  { rewrite /proj_hist list_elem_of_omap. exists (EvDeliver (tid, OpInsert input)).
    split; [exact Hdel | exact (proj_ev_deliver tid (OpInsert input))]. }
  have Hmem : OpInsert input ∈ omap deliverP (proj_hist tid h).
  { rewrite list_elem_of_omap. by exists (EvDeliver (OpInsert input)). }
  pose proof (effect_list_uniqueId_init (omap deliverP (proj_hist tid h)) st Hinterp) as Huniq.
  pose proof (effect_list_insert_mem (omap deliverP (proj_hist tid h)) (op_init Oy) st input
                Hinterp Huniq Hmem) as (it & Hitid & Hfind).
  pose proof (find_by_id_mem (in_id input) (st_items st) it Hfind) as Hitmem.
  rewrite Hitems in Hitmem.
  have Hopid' : in_id input = MkYjsId c k := Hopid.
  have Hcx : clientId (item_id it) = c by rewrite Hitid Hopid' //.
  have := Hbound tid it Hitmem Hcx.
  rewrite Hitid Hopid' /=. lia.
Qed.

(* ===== op certificates (pure side) ======================================== *)

(** What the ops registry records per op: broadcast at its author, with [D]
    covering its strict causal past (id-level). *)
Definition op_registered N op (D : gset YjsId) : Prop :=
  EvBroadcast op ∈ to_histories N (clientId (opid op)) ∧
  (∀ x, raw_hb (to_histories N) x op -> opid x ∈ D).

(** Registry coherence: every registered op is broadcast with a covering [D];
    every broadcast op is registered. *)
Definition ops_coh N (ops : gmap YjsId (Op * gset YjsId)) : Prop :=
  (∀ id op D, ops !! id = Some (op, D) -> opid op = id ∧ op_registered N op D) ∧
  (∀ op, op_broadcast N op -> is_Some (ops !! opid op)).

(** Certificate stability: a certificate survives any append whose tail
    broadcasts nothing old (deliver-only tails, or a fresh broadcast). *)
Lemma op_registered_append N c h (tail : list Ev) op (D : gset YjsId) :
  history_wf N -> N !! c = Some h ->
  (∀ e, EvBroadcast e ∈ tail -> ¬ op_broadcast N e) ->
  op_registered N op D ->
  op_registered (<[c := h ++ tail]> N) op D.
Proof.
  move=> Hwf Hc Htail [Hbc Hcov]. split.
  - destruct (decide (clientId (opid op) = c)) as [Hcc | Hcc].
    + rewrite Hcc to_histories_insert elem_of_app. left.
      rewrite Hcc (to_histories_lookup _ _ _ Hc) in Hbc. exact Hbc.
    + rewrite (to_histories_insert_ne _ _ _ _ Hcc) //.
  - move=> x Hhb. apply Hcov.
    apply (raw_hb_append_old N c h tail x op Hwf Hc Htail); [| exact Hhb].
    by exists (clientId (opid op)).
Qed.

(** A fresh id is unregistered (the [ghost_map_insert] side condition). *)
Lemma ops_coh_lookup_fresh N (ops : gmap YjsId (Op * gset YjsId)) (id : YjsId) :
  ops_coh N ops -> ¬ id_broadcast N id -> ops !! id = None.
Proof.
  move=> [Hc1 _] Hfresh.
  destruct (ops !! id) as [[op' D'] |] eqn:Hlk; [| done]. exfalso.
  destruct (Hc1 _ _ _ Hlk) as [Hopid [Hbc _]].
  apply Hfresh. exists op'. split; [by eexists | exact Hopid].
Qed.

(** Registry coherence survives a fresh broadcast (+ its registration). *)
Lemma ops_coh_broadcast N c h (ops : gmap YjsId (Op * gset YjsId))
    (op0 : Op) (D : gset YjsId) :
  history_wf N -> N !! c = Some h ->
  ¬ id_broadcast N (opid op0) ->
  ops_coh N ops ->
  op_registered (<[c := h ++ [EvBroadcast op0; EvDeliver op0]]> N) op0 D ->
  ops_coh (<[c := h ++ [EvBroadcast op0; EvDeliver op0]]> N)
    (<[opid op0 := (op0, D)]> ops).
Proof.
  move=> Hwf Hc Hfresh [Hc1 Hc2] Hreg.
  have Htail : ∀ e : Op, EvBroadcast e ∈ [EvBroadcast op0; EvDeliver op0]
               -> ¬ op_broadcast N e.
  { move=> e He. move: He. rewrite !elem_of_cons elem_of_nil.
    move=> [[= ->] | [He | He]] // Hbc. apply Hfresh. by exists op0. }
  split.
  - move=> id op D' Hlk.
    destruct (decide (id = opid op0)) as [-> | Hne].
    + rewrite lookup_insert_eq in Hlk. injection Hlk as <- <-.
      split; [reflexivity | exact Hreg].
    + rewrite lookup_insert_ne in Hlk; [| congruence].
      destruct (Hc1 _ _ _ Hlk) as [Hopid Hregd].
      split; [exact Hopid | exact (op_registered_append N c h _ op D' Hwf Hc Htail Hregd)].
  - move=> op Hbc.
    apply (op_broadcast_append N c h _ op Hc) in Hbc.
    destruct Hbc as [Hold | Hnew].
    + destruct (decide (opid op = opid op0)) as [Heq | Hne].
      * rewrite Heq lookup_insert_eq. by eexists.
      * rewrite lookup_insert_ne; [exact (Hc2 op Hold) | congruence].
    + have -> : op = op0.
      { move: Hnew. rewrite !elem_of_cons elem_of_nil. by move=> [[= ->] | [He | He]]. }
      rewrite lookup_insert_eq. by eexists.
Qed.

(** Registry coherence survives a deliver-only append. *)
Lemma ops_coh_deliver_tail N c h (ops : gmap YjsId (Op * gset YjsId)) (tail : list Ev) :
  history_wf N -> N !! c = Some h ->
  (∀ e : Op, EvBroadcast e ∉ tail) ->
  ops_coh N ops ->
  ops_coh (<[c := h ++ tail]> N) ops.
Proof.
  move=> Hwf Hc Htail [Hc1 Hc2].
  have Htail' : ∀ e : Op, EvBroadcast e ∈ tail -> ¬ op_broadcast N e.
  { move=> e He. by destruct (Htail e). }
  split.
  - move=> id op D Hlk.
    destruct (Hc1 _ _ _ Hlk) as [Hopid Hreg].
    split; [exact Hopid | exact (op_registered_append N c h _ op D Hwf Hc Htail' Hreg)].
  - move=> op Hbc.
    apply (op_broadcast_append N c h _ op Hc) in Hbc.
    destruct Hbc as [Hold | Hnew]; [exact (Hc2 op Hold) | by destruct (Htail op)].
Qed.

(* ===== receiver clock safety ============================================== *)

(** THE hard theorem: replaying a broadcast-closed, hb-past-covering list [l]
    that does not contain [op] itself yields a state where [op]'s id is
    clock-maximal among same-client items. Same-client items come from
    same-client ops; those are locally ordered with [op] at their common
    author: an earlier one was self-delivered before [op]'s broadcast, so the
    author's replayed state contains it with a smaller clock
    ([hwf_unique_id]); a later one would place [op] in its causal past, hence
    (causal delivery) already delivered in [l] — contradiction. *)
Lemma receiver_clock_safety N (t0 : TId) (input : IntegrateInput (A := A))
    (l : list Op) (s : op_State O) :
  history_wf N ->
  op_broadcast N (t0, OpInsert input) ->
  (∀ x, raw_hb (to_histories N) x (t0, OpInsert input) -> x ∈ l) ->
  (∀ x, x ∈ l -> op_broadcast N x) ->
  (∀ y, y ∈ l -> opid y ≠ in_id input) ->
  (* [l] is a causally-delivered set: the new op precedes nothing in it (at a
     real receiver this is causal delivery + the op's freshness) *)
  (∀ y, y ∈ l -> ¬ raw_hb (to_histories N) (t0, OpInsert input) y) ->
  effect_list O l (op_init O) s ->
  ∀ (t : TId) x, x ∈ st_items (doc_get s t) ->
       clientId (item_id x) = clientId (in_id input) ->
       (clock (item_id x) < clock (in_id input))%nat.
Proof.
  move=> Hwf Hbc Hcov Hsrc Hnid Hnosucc Heff t x Hx Hcx.
  set op0 : Op := (t0, OpInsert input).
  set c' := clientId (in_id input).
  (* trace [x] to the op that inserted it, within its own type [t] *)
  have Hefft : effect_list Oy (proj_ops t l) (op_init Oy) (doc_get s t).
  { have -> : op_init Oy = doc_get (op_init O) t by rewrite /= doc_get_empty.
    exact (doc_effect_list_proj l _ s t Heff). }
  pose proof (effect_list_mem_src (proj_ops t l) (op_init Oy) (doc_get s t) x Hefft Hx)
    as [Hnil | (xin & Hxin & Hxid)].
  { move: Hnil. rewrite /= elem_of_nil //. }
  apply elem_of_proj_ops in Hxin.
  (* both its op and the new op are authored at [c'] *)
  pose proof (Hsrc (t, OpInsert xin) Hxin) as (jx & Hjx).
  have Hjx' : jx = c'
    by rewrite -(hwf_client_id N Hwf (t, OpInsert xin) jx Hjx) /DocOp_id /= Hxid Hcx.
  subst jx.
  destruct Hbc as (j0 & Hj0).
  have Hj0' : j0 = c' by rewrite -(hwf_client_id N Hwf op0 j0 Hj0).
  subst j0.
  (* the two broadcasts are locally ordered at their common author *)
  pose proof (elem_of_two_split (to_histories N c') _ _ Hjx Hj0) as
    [(l1 & l2 & l3 & Hsplit) | [(l1 & l2 & l3 & Hsplit) | Heq]].
  - (* [xin] earlier: the author's doc-global clock discipline bounds it *)
    have Hsplit' : to_histories N c'
        = l1 ++ [EvBroadcast (t, OpInsert xin)] ++ (l2 ++ [EvBroadcast op0] ++ l3)
      by rewrite Hsplit.
    pose proof (hwf_self_deliver N Hwf c' (t, OpInsert xin) l1 _ Hsplit') as (post' & Hpost).
    destruct l2 as [| e2 l2'].
    { simpl in Hpost. injection Hpost as Hpost _. discriminate. }
    have He2 : e2 = EvDeliver (t, OpInsert xin).
    { move: Hpost. simpl. move=> Hpost. by injection Hpost. }
    subst e2.
    have Hsplit0 : to_histories N c'
        = (l1 ++ [EvBroadcast (t, OpInsert xin)] ++ (EvDeliver (t, OpInsert xin) :: l2'))
          ++ [EvBroadcast op0] ++ l3.
    { rewrite Hsplit -!app_assoc //. }
    set hist1 := l1 ++ [EvBroadcast (t, OpInsert xin)] ++ (EvDeliver (t, OpInsert xin) :: l2').
    pose proof (hwf_broadcast_valid N Hwf c' op0 hist1 l3 Hsplit0) as (s0 & Hinterp0 & _).
    pose proof (hwf_unique_id N Hwf op0 c' hist1 l3 s0 Hsplit0 Hinterp0) as Huid.
    (* the earlier op's item is in the author's replayed state, at type [t] *)
    have Hinterp0t : interpHistory Oy (proj_hist t hist1) (op_init Oy) (doc_get s0 t)
      := doc_interp_proj hist1 s0 t Hinterp0.
    have Hmemev : EvDeliver (OpInsert xin) ∈ proj_hist t hist1.
    { rewrite /proj_hist list_elem_of_omap. exists (EvDeliver (t, OpInsert xin)).
      split; [| exact (proj_ev_deliver t (OpInsert xin))].
      rewrite /hist1. set_solver. }
    have Hmem0 : OpInsert xin ∈ omap deliverP (proj_hist t hist1).
    { rewrite list_elem_of_omap. by exists (EvDeliver (OpInsert xin)). }
    pose proof (effect_list_uniqueId_init (omap deliverP (proj_hist t hist1))
                  (doc_get s0 t) Hinterp0t) as Huniq0.
    pose proof (effect_list_insert_mem (omap deliverP (proj_hist t hist1)) (op_init Oy)
                  (doc_get s0 t) xin Hinterp0t Huniq0 Hmem0) as (it & Hitid & Hfind).
    pose proof (find_by_id_mem (in_id xin) (st_items (doc_get s0 t)) it Hfind) as Hitmem.
    have Hccit : clientId (item_id it) = clientId (opid op0) by rewrite Hitid Hxid Hcx.
    pose proof (Huid t it Hitmem Hccit) as Hclk.
    rewrite Hitid Hxid in Hclk. exact Hclk.
  - (* the new op earlier: it would causally precede a delivered op *)
    exfalso.
    have Hhb : raw_hb (to_histories N) op0 (t, OpInsert xin).
    { apply (raw_hb_bb _ c'). exists l1, l2, l3. exact Hsplit. }
    exact (Hnosucc (t, OpInsert xin) Hxin Hhb).
  - (* the same op: a re-delivery, excluded *)
    exfalso.
    injection Heq as Heq1 Heq2. subst xin.
    exact (Hnid (t, OpInsert input) Hxin eq_refl).
Qed.

(* ===== the broadcast step ================================================= *)

(** Appending [EvBroadcast op; EvDeliver op] for a valid, clock-maximal, fresh
    insert into type [t0] preserves [history_wf], advances the coherent state
    by the insert's splice at [t0], and confines the new op's causal past to
    [delivered_ids h]. The clock bound is doc-global (all types). *)
Lemma history_wf_broadcast N c h (m : DocM) (t0 : TId) (arr' : list (YjsItem A))
    (input : IntegrateInput (A := A)) (item : YjsItem A) (k : nat) :
  history_wf N -> N !! c = Some h ->
  history_state_coh h m ->
  toItem input (docm_get m t0) = Some item ->
  IsItemValid item ->
  maximalId item (docm_get m t0) ->
  in_id input = MkYjsId c k ->
  (∀ (t : TId) x, x ∈ docm_get m t -> clientId (item_id x) = c ->
     (clock (item_id x) < k)%nat) ->
  integrate input (docm_get m t0) = Some arr' ->
  let tail := [EvBroadcast (t0, OpInsert input); EvDeliver (t0, OpInsert input)] in
  history_wf (<[c := h ++ tail]> N) ∧
  history_state_coh (h ++ tail) (<[t0 := arr']> m) ∧
  op_registered (<[c := h ++ tail]> N) (t0, OpInsert input) (delivered_ids h).
Proof.
  move=> Hwf Hc Hcoh Htoitem Hvalid Hmax Hinid Hbound Hint tail.
  set op' : Op := (t0, OpInsert input).
  have Hopid' : opid op' = in_id input by done.
  have Hfresh : ¬ id_broadcast N (opid op').
  { rewrite Hopid' Hinid. exact (history_fresh_id N c h m k Hwf Hc Hcoh Hbound). }
  pose proof (fresh_tail_nodup N c h op' Hwf Hc Hfresh) as (Hnd & Hbh & Hdh).
  have Htail_nobc : ∀ e : Op, EvBroadcast e ∈ tail -> ¬ op_broadcast N e.
  { move=> e He. rewrite /tail !elem_of_cons elem_of_nil in He.
    destruct He as [Heq | [Heq | []]]; [| discriminate].
    injection Heq as ->. move=> Hbc. apply Hfresh. by exists op'. }
  have Hcid' : clientId (opid op') = c by rewrite Hopid' Hinid.
  have Hbcase : ∀ i e, EvBroadcast e ∈ to_histories (<[c := h ++ tail]> N) i ->
                EvBroadcast e ∈ to_histories N i ∨ (i = c ∧ e = op').
  { move=> i e Hin.
    pose proof (hist_mem_insert_case N c h tail i _ Hc Hin) as [Hold | [-> Hnew]];
      [by left |].
    right. split; [done |].
    rewrite /tail !elem_of_cons elem_of_nil in Hnew.
    destruct Hnew as [Heq | [Heq | []]]; [by injection Heq | discriminate]. }
  have Hsplit_new : ∀ pre post, h ++ tail = pre ++ [EvBroadcast op'] ++ post ->
                    pre = h ∧ post = [EvDeliver op'].
  { move=> pre post Heq.
    have Hnd2 : NoDup (pre ++ [EvBroadcast op'] ++ post) by rewrite -Heq.
    have Hx1 : EvBroadcast op' ∉ pre := elem_not_in_of_nodup_mid pre _ _ Hnd2.
    have Heq2 : pre ++ EvBroadcast op' :: post = h ++ EvBroadcast op' :: [EvDeliver op']
      := eq_sym Heq.
    exact (nodup_app_mid_uniq (EvBroadcast op') pre post h _ Hx1 Hbh Heq2). }
  destruct Hcoh as (s & Hinterp & Hitems).
  have Hcs : isClockSafe (in_id input) (docm_get m t0) = true
    := maximalId_isClockSafe input (docm_get m t0) item Htoitem Hmax.
  split_and!.
  - (* ---- history_wf ---- *)
    constructor.
    + (* nodup *)
      move=> i. destruct (decide (i = c)) as [-> | Hne];
        last by (rewrite (to_histories_insert_ne _ _ _ _ Hne); exact (hwf_nodup N Hwf i)).
      rewrite to_histories_insert. exact Hnd.
    + (* deliver_has_a_cause *)
      move=> i e Hin.
      pose proof (hist_mem_insert_case N c h tail i _ Hc Hin) as [Hold | [-> Hnew]].
      * pose proof (hwf_deliver_has_a_cause N Hwf i e Hold) as (j & Hj).
        exists j. exact (hist_mem_append_mono N c h tail j _ Hc Hj).
      * rewrite /tail !elem_of_cons elem_of_nil in Hnew.
        destruct Hnew as [Heq | [Heq | []]]; [discriminate |].
        injection Heq as ->.
        exists c. rewrite to_histories_insert elem_of_app !elem_of_cons.
        right. by left.
    + (* msg_id_unique *)
      move=> mi mj i j Hmi Hmj Hid.
      pose proof (Hbcase i mi Hmi) as [Hoi | [-> ->]];
        pose proof (Hbcase j mj Hmj) as [Hoj | [-> ->]].
      * exact (hwf_msg_id_unique N Hwf mi mj i j Hoi Hoj Hid).
      * exfalso. apply Hfresh. exists mi. split; [by exists i | exact Hid].
      * exfalso. apply Hfresh. exists mj. split; [by exists j | exact (eq_sym Hid)].
      * done.
    + (* causal_delivery *)
      move=> i e1 e2 Hdel Hhb.
      pose proof (hist_mem_insert_case N c h tail i _ Hc Hdel) as [Hold | [-> Hnew]].
      * have He2bc : op_broadcast N e2.
        { pose proof (hwf_deliver_has_a_cause N Hwf i e2 Hold) as (j & Hj). by exists j. }
        have Hhb' : raw_hb (to_histories N) e1 e2
          := raw_hb_append_old N c h tail e1 e2 Hwf Hc Htail_nobc He2bc Hhb.
        exact (raw_lo_append_mono N c h tail i _ _ Hc
                 (hwf_causal_delivery N Hwf i e1 e2 Hold Hhb')).
      * rewrite /tail !elem_of_cons elem_of_nil in Hnew.
        destruct Hnew as [Heq | [Heq | []]]; [discriminate |].
        injection Heq as ->.
        have Hd1 : EvDeliver e1 ∈ h
          := fresh_broadcast_past N c h op' e1 Hwf Hc Hfresh Hhb.
        pose proof (list_elem_of_split _ _ Hd1) as (p & q & Hh).
        exists p, (q ++ [EvBroadcast op']), [].
        rewrite to_histories_insert Hh /tail -!app_assoc //=.
    + (* broadcast_valid *)
      move=> i e pre post Hsplit.
      destruct (decide (i = c)) as [-> | Hne];
        last by (rewrite (to_histories_insert_ne _ _ _ _ Hne) in Hsplit;
                 exact (hwf_broadcast_valid N Hwf i e pre post Hsplit)).
      rewrite to_histories_insert in Hsplit.
      destruct (decide (e = op')) as [-> | Hne2].
      * pose proof (Hsplit_new pre post Hsplit) as [-> _].
        exists s. split; [exact Hinterp |].
        rewrite /DocIsValidMessage /= (Hitems t0). by exists item.
      * have Hnotin : EvBroadcast e ∉ tail.
        { rewrite /tail !elem_of_cons elem_of_nil.
          move=> [Heq | [Heq | []]]; [| discriminate].
          injection Heq as Heq. exact (Hne2 Heq). }
        pose proof (split_app_confine h tail _ pre post Hsplit Hnotin) as (post' & Hh & _).
        rewrite -(to_histories_lookup N c h Hc) in Hh.
        exact (hwf_broadcast_valid N Hwf c e pre post' Hh).
    + (* client_id *)
      move=> e i Hin.
      pose proof (Hbcase i e Hin) as [Hold | [-> ->]].
      * exact (hwf_client_id N Hwf e i Hold).
      * exact Hcid'.
    + (* unique_id *)
      move=> e i hist1 hist2 array Hsplit Hinterp2.
      destruct (decide (i = c)) as [-> | Hne];
        last by (rewrite (to_histories_insert_ne _ _ _ _ Hne) in Hsplit;
                 exact (hwf_unique_id N Hwf e i hist1 hist2 array Hsplit Hinterp2)).
      rewrite to_histories_insert in Hsplit.
      destruct (decide (e = op')) as [-> | Hne2].
      * pose proof (Hsplit_new hist1 hist2 Hsplit) as [-> _].
        have Heqs : s = array
          := doc_effect_list_det (omap deliverP h) (op_init O) s array Hinterp Hinterp2.
        move=> t x Hx Hcx.
        rewrite -Heqs (Hitems t) in Hx.
        rewrite Hopid' Hinid /= in Hcx *.
        exact (Hbound t x Hx Hcx).
      * have Hnotin : EvBroadcast e ∉ tail.
        { rewrite /tail !elem_of_cons elem_of_nil.
          move=> [Heq | [Heq | []]]; [| discriminate].
          injection Heq as Heq. exact (Hne2 Heq). }
        pose proof (split_app_confine h tail _ hist1 hist2 Hsplit Hnotin)
          as (post' & Hh & _).
        rewrite -(to_histories_lookup N c h Hc) in Hh.
        exact (hwf_unique_id N Hwf e c hist1 post' array Hh Hinterp2).
    + (* self_deliver *)
      move=> i e pre post Hsplit.
      destruct (decide (i = c)) as [-> | Hne];
        last by (rewrite (to_histories_insert_ne _ _ _ _ Hne) in Hsplit;
                 exact (hwf_self_deliver N Hwf i e pre post Hsplit)).
      rewrite to_histories_insert in Hsplit.
      destruct (decide (e = op')) as [-> | Hne2].
      * pose proof (Hsplit_new pre post Hsplit) as [_ ->]. by exists [].
      * have Hnotin : EvBroadcast e ∉ tail.
        { rewrite /tail !elem_of_cons elem_of_nil.
          move=> [Heq | [Heq | []]]; [| discriminate].
          injection Heq as Heq. exact (Hne2 Heq). }
        pose proof (split_app_confine h tail _ pre post Hsplit Hnotin)
          as (post' & Hh & Hpost).
        rewrite -(to_histories_lookup N c h Hc) in Hh.
        pose proof (hwf_self_deliver N Hwf c e pre post' Hh) as (post'' & Hpost').
        exists (post'' ++ tail). rewrite Hpost Hpost' //.
    + (* insert_only *)
      move=> i e Hin.
      destruct Hin as [Hin | Hin].
      * pose proof (Hbcase i e Hin) as [Hold | [-> ->]].
        -- exact (hwf_insert_only N Hwf i e (or_introl Hold)).
        -- by exists input.
      * pose proof (hist_mem_insert_case N c h tail i _ Hc Hin) as [Hold | [-> Hnew]].
        -- exact (hwf_insert_only N Hwf i e (or_intror Hold)).
        -- rewrite /tail !elem_of_cons elem_of_nil in Hnew.
           destruct Hnew as [Heq | [Heq | []]]; [discriminate |].
           injection Heq as ->. by exists input.
  - (* ---- coherence with the document spliced at [t0] ---- *)
    set st0 := doc_get s t0.
    set s' := <[t0 := MkYjsState arr' (st_deleted st0)]> s.
    exists s'. split.
    + have Hstep : op_effect O op' s s'.
      { exists (MkYjsState arr' (st_deleted st0)). split; [| done].
        rewrite /op' /= /YjsState_insert /integrateSafe -/st0 (Hitems t0) Hcs Hint //=. }
      have H1 : interpHistory O (h ++ [EvBroadcast op']) (op_init O) s
        := interpHistory_snoc_broadcast h op' _ s Hinterp.
      have H2 := interpHistory_snoc_deliver (h ++ [EvBroadcast op']) op' _ s _ H1 Hstep.
      have -> : h ++ tail = (h ++ [EvBroadcast op']) ++ [EvDeliver op']
        by rewrite /tail -app_assoc //.
      exact H2.
    + move=> t. destruct (decide (t = t0)) as [-> | Hne].
      * rewrite /s' doc_get_insert_eq docm_get_insert_eq //.
      * rewrite /s' doc_get_insert_ne // docm_get_insert_ne //.
  - (* ---- the new op's registration ---- *)
    split.
    + rewrite Hcid' to_histories_insert elem_of_app /tail !elem_of_cons.
      right. by left.
    + move=> x Hhb.
      have Hd : EvDeliver x ∈ h
        := fresh_broadcast_past N c h op' x Hwf Hc Hfresh Hhb.
      apply elem_of_delivered_ids. by exists x.
Qed.

(* ===== the deliver step =================================================== *)

(** Delivering one certified, causally covered, fresh op preserves
    [history_wf]. *)
Lemma history_wf_deliver N c h op (D : gset YjsId) :
  history_wf N -> N !! c = Some h ->
  op_registered N op D ->
  D ⊆ delivered_ids h ->
  opid op ∉ delivered_ids h ->
  history_wf (<[c := h ++ [EvDeliver op]]> N).
Proof.
  move=> Hwf Hc [Hbcreg Hcov] HDsub Hnotdel.
  set tail := [EvDeliver op].
  have Hdop_h : EvDeliver op ∉ h.
  { move=> Hin. apply Hnotdel. apply elem_of_delivered_ids. by exists op. }
  have Htail_nobc : ∀ e : Op, EvBroadcast e ∈ tail -> ¬ op_broadcast N e.
  { move=> e He. rewrite /tail elem_of_cons elem_of_nil in He.
    destruct He as [He | []]. discriminate. }
  have Hbcase : ∀ i e, EvBroadcast e ∈ to_histories (<[c := h ++ tail]> N) i ->
                EvBroadcast e ∈ to_histories N i.
  { move=> i e Hin.
    pose proof (hist_mem_insert_case N c h tail i _ Hc Hin) as [Hold | [_ Hnew]]; [done |].
    rewrite /tail elem_of_cons elem_of_nil in Hnew.
    destruct Hnew as [Hnew | []]. discriminate. }
  constructor.
  - (* nodup *)
    move=> i. destruct (decide (i = c)) as [-> | Hne];
      last by (rewrite (to_histories_insert_ne _ _ _ _ Hne); exact (hwf_nodup N Hwf i)).
    rewrite to_histories_insert. apply NoDup_app. split_and!.
    + rewrite -(to_histories_lookup N c h Hc). exact (hwf_nodup N Hwf c).
    + move=> e He. rewrite /tail elem_of_cons elem_of_nil.
      move=> [Heq | []]. subst e. exact (Hdop_h He).
    + apply NoDup_cons_2; [rewrite elem_of_nil; move=> [] | constructor].
  - (* deliver_has_a_cause *)
    move=> i e Hin.
    pose proof (hist_mem_insert_case N c h tail i _ Hc Hin) as [Hold | [-> Hnew]].
    + pose proof (hwf_deliver_has_a_cause N Hwf i e Hold) as (j & Hj).
      exists j. exact (hist_mem_append_mono N c h tail j _ Hc Hj).
    + rewrite /tail elem_of_cons elem_of_nil in Hnew.
      destruct Hnew as [Heq | []]. injection Heq as ->.
      exists (clientId (opid op)).
      exact (hist_mem_append_mono N c h tail _ _ Hc Hbcreg).
  - (* msg_id_unique *)
    move=> mi mj i j Hmi Hmj Hid.
    exact (hwf_msg_id_unique N Hwf mi mj i j (Hbcase i mi Hmi) (Hbcase j mj Hmj) Hid).
  - (* causal_delivery *)
    move=> i e1 e2 Hdel Hhb.
    have He2bc : op_broadcast N e2.
    { pose proof (raw_hb_right_broadcast _ e1 e2 Hhb) as (j & Hj).
      exists j. exact (Hbcase j e2 Hj). }
    have Hhb' : raw_hb (to_histories N) e1 e2 :=
      raw_hb_append_old N c h tail e1 e2 Hwf Hc Htail_nobc He2bc Hhb.
    pose proof (hist_mem_insert_case N c h tail i _ Hc Hdel) as [Hold | [-> Hnew]].
    + exact (raw_lo_append_mono N c h tail i _ _ Hc
               (hwf_causal_delivery N Hwf i e1 e2 Hold Hhb')).
    + rewrite /tail elem_of_cons elem_of_nil in Hnew.
      destruct Hnew as [Heq | []]. injection Heq as ->.
      (* e2 = op: e1's delivery is already in [h], by the certificate *)
      have Hin1 : opid e1 ∈ D := Hcov e1 Hhb'.
      have Hin2 : opid e1 ∈ delivered_ids h := HDsub _ Hin1.
      apply elem_of_delivered_ids in Hin2. destruct Hin2 as (y & Hyh & Hyid).
      have He1y : e1 = y.
      { pose proof (raw_hb_left_broadcast N Hwf e1 op Hhb') as (j1 & Hj1).
        have Hyc : EvDeliver y ∈ to_histories N c
          by rewrite (to_histories_lookup N c h Hc).
        pose proof (hwf_deliver_has_a_cause N Hwf c y Hyc) as (j2 & Hj2).
        pose proof (hwf_msg_id_unique N Hwf e1 y j1 j2 Hj1 Hj2 (eq_sym Hyid)) as [_ Heq].
        exact Heq. }
      subst y.
      pose proof (list_elem_of_split _ _ Hyh) as (p & s & Hh).
      exists p, s, []. rewrite to_histories_insert Hh /tail -!app_assoc //=.
  - (* broadcast_valid *)
    move=> i e pre post Hsplit.
    destruct (decide (i = c)) as [-> | Hne];
      last by (rewrite (to_histories_insert_ne _ _ _ _ Hne) in Hsplit;
               exact (hwf_broadcast_valid N Hwf i e pre post Hsplit)).
    rewrite to_histories_insert in Hsplit.
    have Hnotin : EvBroadcast e ∉ tail.
    { rewrite /tail elem_of_cons elem_of_nil. move=> [Heq | []]. discriminate. }
    pose proof (split_app_confine h tail _ pre post Hsplit Hnotin) as (post' & Hh & _).
    rewrite -(to_histories_lookup N c h Hc) in Hh.
    exact (hwf_broadcast_valid N Hwf c e pre post' Hh).
  - (* client_id *)
    move=> e i Hin. exact (hwf_client_id N Hwf e i (Hbcase i e Hin)).
  - (* unique_id *)
    move=> e i hist1 hist2 array Hsplit Hinterp.
    destruct (decide (i = c)) as [-> | Hne];
      last by (rewrite (to_histories_insert_ne _ _ _ _ Hne) in Hsplit;
               exact (hwf_unique_id N Hwf e i hist1 hist2 array Hsplit Hinterp)).
    rewrite to_histories_insert in Hsplit.
    have Hnotin : EvBroadcast e ∉ tail.
    { rewrite /tail elem_of_cons elem_of_nil. move=> [Heq | []]. discriminate. }
    pose proof (split_app_confine h tail _ hist1 hist2 Hsplit Hnotin) as (post' & Hh & _).
    rewrite -(to_histories_lookup N c h Hc) in Hh.
    exact (hwf_unique_id N Hwf e c hist1 post' array Hh Hinterp).
  - (* self_deliver *)
    move=> i e pre post Hsplit.
    destruct (decide (i = c)) as [-> | Hne];
      last by (rewrite (to_histories_insert_ne _ _ _ _ Hne) in Hsplit;
               exact (hwf_self_deliver N Hwf i e pre post Hsplit)).
    rewrite to_histories_insert in Hsplit.
    have Hnotin : EvBroadcast e ∉ tail.
    { rewrite /tail elem_of_cons elem_of_nil. move=> [Heq | []]. discriminate. }
    pose proof (split_app_confine h tail _ pre post Hsplit Hnotin) as (post' & Hh & Hpost).
    rewrite -(to_histories_lookup N c h Hc) in Hh.
    pose proof (hwf_self_deliver N Hwf c e pre post' Hh) as (post'' & Hpost').
    exists (post'' ++ tail). rewrite Hpost Hpost' //.
  - (* insert_only *)
    move=> i e Hin.
    destruct Hin as [Hin | Hin].
    + exact (hwf_insert_only N Hwf i e (or_introl (Hbcase i e Hin))).
    + pose proof (hist_mem_insert_case N c h tail i _ Hc Hin) as [Hold | [-> Hnew]].
      * exact (hwf_insert_only N Hwf i e (or_intror Hold)).
      * rewrite /tail elem_of_cons elem_of_nil in Hnew.
        destruct Hnew as [Heq | []]. injection Heq as ->.
        exact (hwf_insert_only N Hwf (clientId (opid op)) op (or_introl Hbcreg)).
Qed.

(* ===== ValidReplay ======================================================== *)

(** [ValidReplay inputs m m']: applying the decoded, type-tagged [inputs] to
    the per-type documents [m] in list order is a *valid causal replay*
    yielding [m'] — at each step the input resolves to a model item in its own
    type's list ([toItem]), that item is valid ([IsItemValid]) and per-client
    clock-maximal — both within its type ([maximalId], the causal-delivery
    condition [Store.Integrate] consumes) and doc-globally over every type's
    items (the receiver-side freshness that used to be a leftover hypothesis
    of [applyUpdate]'s certificate spec; with doc-global clocks it is a fact
    of the replay) — and the pure [integrate] advances that type's list. This
    is exactly the chain of preconditions [wp_Store__Integrate] needs at each
    loop step; it coincides with a valid replay of doc-level [OpInsert]s in
    the network model, so a proof against it inherits the model's invariant
    preservation and strong convergence.

    (Moved here from [yjs_store]: it is pure, and [certs_ValidReplay] below
    produces it from op certificates.) *)
Inductive ValidReplay :
    list (TId * IntegrateInput (A := A)) -> DocM -> DocM -> Prop :=
  | VR_nil m : ValidReplay [] m m
  | VR_cons t input rest m arr2 m' nit :
      toItem input (docm_get m t) = Some nit ->
      IsItemValid nit ->
      maximalId nit (docm_get m t) ->
      (∀ (t' : TId) x, x ∈ docm_get m t' ->
         clientId (item_id x) = clientId (in_id input) ->
         (clock (item_id x) < clock (in_id input))%nat) ->
      integrate input (docm_get m t) = Some arr2 ->
      ValidReplay rest (<[t := arr2]> m) m' ->
      ValidReplay ((t, input) :: rest) m m'.

(** A splice only adds: [integrate] preserves membership. *)
Lemma integrate_preserves_mem (input : IntegrateInput (A := A))
    (arr arr2 : list (YjsItem A)) :
  integrate input arr = Some arr2 -> ∀ x, x ∈ arr -> x ∈ arr2.
Proof.
  move=> Hint x Hx.
  pose proof (integrate_insertIdx_form input arr arr2 Hint) as (didx & it & _ & Hres).
  rewrite Hres /insertIdxIfInBounds.
  case: (decide (didx <= length arr)%nat) => Hd; last exact Hx.
  rewrite -{1}(take_drop didx arr) in Hx.
  move: Hx. rewrite !elem_of_app elem_of_cons. tauto.
Qed.

(** [integrate] actually places an item of the input's id (the splice is
    in-bounds — only index-bound reasoning, no validity needed; the
    [integrate]-level analogue of the upstream [YjsState_insert_mem]). *)
Lemma integrate_new_mem (input : IntegrateInput (A := A))
    (arr arr2 : list (YjsItem A)) :
  integrate input arr = Some arr2 ->
  ∃ it, item_id it = in_id input ∧ it ∈ arr2.
Proof.
  rewrite /integrate.
  move=> /bind_Some [leftIdx [HfindLeft Hr1]].
  move: Hr1 => /bind_Some [rightIdx [HfindRight Hr2]].
  move: Hr2 => /bind_Some [destIdx [HfindIdx Hr3]].
  move: Hr3 => /bind_Some [item [Hmk Hlast]].
  move: Hlast => [= <-].
  pose proof (findLeftIdx_getElemExcept arr input leftIdx HfindLeft) as (lptr & Hgl & _).
  pose proof (findRightIdx_getElemExcept arr input rightIdx HfindRight) as (rptr & Hgr & _).
  have Hitem : item = Item lptr rptr (in_id input) (in_content input)
    by move: Hmk; rewrite /mkItemByIndex Hgl Hgr /= => [= H]; rewrite H.
  have Hbound : (destIdx <= length arr)%nat
    by apply: (findIntegratedIndex_le_size leftIdx rightIdx input arr destIdx
      (findLeftIdx_ge _ _ _ HfindLeft) (findLeftIdx_lt_size _ _ _ HfindLeft)
      (findRightIdx_le_size _ _ _ HfindRight) HfindIdx).
  exists item. split; [by rewrite Hitem |].
  apply (proj2 (mem_insertIdxIfInBounds arr item item destIdx Hbound)). by left.
Qed.

(** A valid replay only splices items in: membership is preserved, per type. *)
Lemma ValidReplay_mem (inputs : list (TId * IntegrateInput (A := A))) (m m' : DocM) :
  ValidReplay inputs m m' -> ∀ (t : TId) x, x ∈ docm_get m t -> x ∈ docm_get m' t.
Proof.
  elim => [m0 | t0 input rest m0 arr2 m1 nit Htoit _ _ _ Hint _ IH] t x Hx; first exact Hx.
  apply IH.
  destruct (decide (t = t0)) as [-> | Hne].
  - rewrite docm_get_insert_eq.
    exact (integrate_preserves_mem input (docm_get m0 t0) arr2 Hint x Hx).
  - rewrite docm_get_insert_ne //.
Qed.

(** Converse provenance: a replayed item is an original item or carries the
    id of some batch input (the model-level analogue of the heap-level
    [all_cells] provenance clause of [wp_store__applyUpdate]). *)
Lemma ValidReplay_prov (inputs : list (TId * IntegrateInput (A := A))) (m m' : DocM) :
  ValidReplay inputs m m' ->
  ∀ (t : TId) x, x ∈ docm_get m' t ->
    x ∈ docm_get m t ∨
    ∃ (i : nat) (ti : TId * IntegrateInput (A := A)),
      inputs !! i = Some ti ∧ item_id x = in_id ti.2.
Proof.
  elim => [m0 | t0 input0 rest m0 arr2 m1 nit Htoit _ _ _ Hint Hvr IH] t x Hx.
  - by left.
  - destruct (IH t x Hx) as [Hmid | (i & ti & Hi & Hid)]; last first.
    { right. by exists (S i), ti. }
    destruct (decide (t = t0)) as [-> | Hne]; last first.
    { left. rewrite docm_get_insert_ne // in Hmid. }
    rewrite docm_get_insert_eq in Hmid.
    pose proof (integrate_insertIdx_form input0 (docm_get m0 t0) arr2 Hint)
      as (didx & item & Hitid & Hres).
    rewrite Hres in Hmid.
    case: (decide (didx <= length (docm_get m0 t0))%nat) => Hd.
    + apply (proj1 (mem_insertIdxIfInBounds (docm_get m0 t0) item x didx Hd)) in Hmid.
      destruct Hmid as [-> | Hin]; [right | by left].
      exists 0%nat, (t0, input0). split; [done | exact Hitid].
    + rewrite /insertIdxIfInBounds decide_False // in Hmid. by left.
Qed.

(** Every batch item's clock strictly exceeds all same-client items already in
    the initial documents — any type (the heap-level freshness side condition
    of [wp_store__applyUpdate], at the model level). *)
Lemma ValidReplay_arr_fresh (inputs : list (TId * IntegrateInput (A := A))) (m m' : DocM) :
  ValidReplay inputs m m' ->
  ∀ (i : nat) (ti : TId * IntegrateInput (A := A)), inputs !! i = Some ti ->
  ∀ (t : TId) x, x ∈ docm_get m t -> clientId (item_id x) = clientId (in_id ti.2) ->
       (clock (item_id x) < clock (in_id ti.2))%nat.
Proof.
  elim => [m0 | t0 input0 rest m0 arr2 m1 nit Htoit _ _ Hglob Hint Hvr IH] i ti Hi t x Hx Hcc.
  - rewrite lookup_nil in Hi. done.
  - destruct i as [| i'].
    + injection Hi as <-. exact (Hglob t x Hx Hcc).
    + simpl in Hi.
      have Hx2 : x ∈ docm_get (<[t0 := arr2]> m0) t.
      { destruct (decide (t = t0)) as [-> | Hne].
        - rewrite docm_get_insert_eq.
          exact (integrate_preserves_mem input0 (docm_get m0 t0) arr2 Hint x Hx).
        - rewrite docm_get_insert_ne //. }
      exact (IH i' ti Hi t x Hx2 Hcc).
Qed.

(** Earlier same-client batch items have strictly smaller clocks (the
    intra-batch causal-order side condition of [wp_store__applyUpdate]). *)
Lemma ValidReplay_batch_causal (inputs : list (TId * IntegrateInput (A := A))) (m m' : DocM) :
  ValidReplay inputs m m' ->
  ∀ (i j : nat) (ti tj : TId * IntegrateInput (A := A)),
    inputs !! i = Some ti -> inputs !! j = Some tj ->
    (j < i)%nat -> clientId (in_id tj.2) = clientId (in_id ti.2) ->
    (clock (in_id tj.2) < clock (in_id ti.2))%nat.
Proof.
  elim => [m0 | t0 input0 rest m0 arr2 m1 nit Htoit _ _ Hglob Hint Hvr IH]
    i j ti tj Hi Hj Hji Hcc.
  - rewrite lookup_nil in Hi. done.
  - destruct j as [| j'].
    + (* the head op's item is in its type's new list; the tail's freshness
         bounds it *)
      injection Hj as <-. destruct i as [| i']; [lia |]. simpl in Hi.
      pose proof (integrate_new_mem input0 (docm_get m0 t0) arr2 Hint) as (it & Hitid & Hitmem).
      have Hitmem2 : it ∈ docm_get (<[t0 := arr2]> m0) t0 by rewrite docm_get_insert_eq.
      have Hccit : clientId (item_id it) = clientId (in_id ti.2) by rewrite Hitid /=.
      have := ValidReplay_arr_fresh rest (<[t0 := arr2]> m0) m1 Hvr i' ti Hi t0 it Hitmem2 Hccit.
      rewrite Hitid //.
    + destruct i as [| i']; [lia |]. simpl in Hi, Hj.
      exact (IH i' j' ti tj Hi Hj ltac:(lia) Hcc).
Qed.

(* ===== certificates ⇒ ValidReplay ========================================= *)

(** Batch delivery precondition, receiver-side but *pure and id-level*: every
    input's certified causal past is covered by what this replica already
    delivered plus the earlier part of the batch, and no input is a
    re-delivery. This is what y-octo's UpdateIterator establishes with the
    state vector; the verified subset takes it as a hypothesis (see plan
    §6.5.1 / §8.5 for the staged path to the total pending-buffer spec). *)
Definition batch_ok h (inputs : list (TId * IntegrateInput (A := A)))
    (Ds : list (gset YjsId)) : Prop :=
  ∀ (i : nat) (ti : TId * IntegrateInput (A := A)) (D : gset YjsId),
    inputs !! i = Some ti -> Ds !! i = Some D ->
    D ⊆ delivered_ids h ∪ list_to_set ((λ tj, in_id tj.2) <$> take i inputs) ∧
    in_id ti.2 ∉ delivered_ids h
                 ∪ (list_to_set ((λ tj, in_id tj.2) <$> take i inputs) : gset YjsId).

(** The deliver event a decoded, type-tagged input denotes. *)
Definition deliver_ev (ti : TId * IntegrateInput (A := A)) : Ev :=
  EvDeliver (ti.1, OpInsert ti.2).

(** A certified [batch_ok] batch contains no op authored by the receiving
    client: a certificate pins its op as broadcast at the author
    ([op_registered]), own broadcasts are immediately self-delivered
    ([hwf_self_deliver]), and [batch_ok]'s freshness excludes anything
    already delivered here. This is what lets the receiver's per-client
    clock invariant survive [applyUpdate] (no delivered item carries the
    local client id). *)
Lemma batch_not_own_client N c h
    (inputs : list (TId * IntegrateInput (A := A))) (Ds : list (gset YjsId)) :
  history_wf N -> N !! c = Some h ->
  length Ds = length inputs ->
  (∀ (i : nat) (ti : TId * IntegrateInput (A := A)) (D : gset YjsId),
     inputs !! i = Some ti -> Ds !! i = Some D ->
     op_registered N (ti.1, OpInsert ti.2) D) ->
  batch_ok h inputs Ds ->
  ∀ (i : nat) (ti : TId * IntegrateInput (A := A)),
    inputs !! i = Some ti -> clientId (in_id ti.2) ≠ c.
Proof.
  move=> Hwf Hc Hlen Hreg Hbatch i ti Hi Hcc.
  have [D HD] : is_Some (Ds !! i)
    by apply lookup_lt_is_Some; rewrite Hlen; exact (lookup_lt_Some _ _ _ Hi).
  have [Hbc _] := Hreg i ti D Hi HD.
  have Hopid : opid (ti.1, OpInsert ti.2) = in_id ti.2 by [].
  rewrite Hopid Hcc in Hbc.
  (* self-delivery: the op is already delivered in [h] *)
  rewrite (to_histories_lookup N c h Hc) in Hbc.
  have [pre [post Hsplit]] := list_elem_of_split _ _ Hbc.
  have Hsplit' : to_histories N c = pre ++ [EvBroadcast (ti.1, OpInsert ti.2)] ++ post
    by rewrite (to_histories_lookup N c h Hc) Hsplit.
  have [post' Hpost] := hwf_self_deliver N Hwf c _ pre post Hsplit'.
  have Hidin : in_id ti.2 ∈ delivered_ids h.
  { apply elem_of_delivered_ids. exists (ti.1, OpInsert ti.2).
    split; [| exact Hopid]. rewrite Hsplit Hpost. set_solver. }
  have [_ Hfresh] := Hbatch i ti D Hi HD.
  apply Hfresh. apply elem_of_union_l. exact Hidin.
Qed.

(** The applyUpdate bridge: certificates + coverage turn into a [ValidReplay]
    of the batch, the coherent state advances by the batch's delivers, and the
    extended history is well-formed. Produces the existential [m'], so the
    WP spec need not ask the caller for it. *)
Lemma certs_ValidReplay N c h (m : DocM)
    (inputs : list (TId * IntegrateInput (A := A))) (Ds : list (gset YjsId)) :
  history_wf N -> N !! c = Some h ->
  history_state_coh h m ->
  (∀ t : TId, YjsArrInvariant (docm_get m t)) ->
  (∀ (i : nat) (ti : TId * IntegrateInput (A := A)) (D : gset YjsId),
     inputs !! i = Some ti -> Ds !! i = Some D ->
     op_registered N (ti.1, OpInsert ti.2) D) ->
  length Ds = length inputs ->
  batch_ok h inputs Ds ->
  ∃ m',
    ValidReplay inputs m m' ∧
    history_state_coh (h ++ (deliver_ev <$> inputs)) m' ∧
    history_wf (<[c := h ++ (deliver_ev <$> inputs)]> N).
Proof.
  move: N h m Ds.
  elim: inputs => [| ti0 inputs' IH] N h m Ds Hwf Hc Hcoh Hinv Hreg Hlen Hbatch.
  - (* empty batch *)
    exists m. split_and!.
    + exact (VR_nil m).
    + rewrite /= app_nil_r //.
    + rewrite /= app_nil_r (insert_id N c h Hc) //.
  - (* one delivery, then recurse on the extended network *)
    destruct Ds as [| D Ds']; [simpl in Hlen; lia |].
    destruct ti0 as [t0 input].
    set op0 : Op := (t0, OpInsert input).
    have Hreg0 : op_registered N op0 D := Hreg 0%nat (t0, input) D eq_refl eq_refl.
    pose proof Hreg0 as [Hbc0 Hcov0].
    pose proof (Hbatch 0%nat (t0, input) D eq_refl eq_refl) as [HD0 Hfresh0].
    rewrite take_0 /= in HD0 Hfresh0.
    have Hop0id : opid op0 = in_id input by done.
    have HDsub : D ⊆ delivered_ids h by set_solver.
    have Hnotdel : opid op0 ∉ delivered_ids h.
    { rewrite Hop0id. set_solver. }
    destruct Hcoh as (s & Hinterp & Hitems).
    (* every op delivered in [h] was broadcast somewhere *)
    have HsrcL : ∀ x : Op, x ∈ delivered_ops h -> op_broadcast N x.
    { move=> x Hx. move: Hx. rewrite /delivered_ops list_elem_of_omap => -[ev [Hev Hdev]].
      destruct ev as [a | a]; simpl in Hdev; [done | injection Hdev as ->].
      have Hd : EvDeliver x ∈ to_histories N c by rewrite (to_histories_lookup N c h Hc).
      exact (hwf_deliver_has_a_cause N Hwf c x Hd). }
    (* the certified causal past is already delivered here *)
    have Hpast : ∀ x : Op, raw_hb (to_histories N) x op0 -> x ∈ delivered_ops h.
    { move=> x Hhb.
      have Hxid : opid x ∈ delivered_ids h := HDsub _ (Hcov0 x Hhb).
      apply elem_of_delivered_ids in Hxid. destruct Hxid as (y & Hyh & Hyid).
      have Hxy : x = y.
      { pose proof (raw_hb_left_broadcast N Hwf x op0 Hhb) as (j1 & Hj1).
        have Hyc : EvDeliver y ∈ to_histories N c
          by rewrite (to_histories_lookup N c h Hc).
        pose proof (hwf_deliver_has_a_cause N Hwf c y Hyc) as (j2 & Hj2).
        exact (proj2 (hwf_msg_id_unique N Hwf x y j1 j2 Hj1 Hj2 (eq_sym Hyid))). }
      subst y. rewrite /delivered_ops list_elem_of_omap. by exists (EvDeliver x). }
    (* validity at the replayed state, via the type-[t0] projection of the
       packaged doc network (the upstream replay-validity theorem) *)
    have Hval : ∃ item0, toItem input (docm_get m t0) = Some item0 ∧ IsItemValid item0.
    { have Hit : st_items (doc_get s t0) = docm_get m t0 := Hitems t0.
      rewrite -Hit.
      apply (isValidState_insert_from_source (to_proj_network t0 N Hwf) input
               (doc_get s t0) (omap deliverP (proj_hist t0 h))).
      - exists (clientId (opid op0)).
        rewrite to_proj_network_histories /proj_hist list_elem_of_omap.
        exists (EvBroadcast op0).
        split; [exact Hbc0 | exact (proj_ev_broadcast t0 (OpInsert input))].
      - move=> x Hlt.
        destruct Hlt as [Hle Hne].
        destruct Hle as [Heq | Hhb]; [by destruct Hne |].
        have Hhbdoc : HappensBefore opid (to_doc_network N Hwf) (t0, x) (t0, OpInsert input).
        { apply (proj_hb_lift t0 (to_doc_network N Hwf)
                   (proj_network_base t0 (to_doc_network N Hwf))); [done | exact Hhb]. }
        have Hraw : raw_hb (to_histories N) (t0, x) op0.
        { apply (raw_hb_HappensBefore (to_network_base N Hwf)). exact Hhbdoc. }
        have Hin : (t0, x) ∈ delivered_ops h := Hpast (t0, x) Hraw.
        rewrite -delivered_ops_proj elem_of_proj_ops //.
      - move=> x Hx.
        rewrite -delivered_ops_proj elem_of_proj_ops in Hx.
        destruct (HsrcL (t0, x) Hx) as (j & Hj).
        exists j.
        rewrite to_proj_network_histories /proj_hist list_elem_of_omap.
        exists (EvBroadcast (t0, x)).
        split; [exact Hj | exact (proj_ev_broadcast t0 x)].
      - exact (doc_interp_proj h s t0 Hinterp). }
    destruct Hval as (item0 & Htoit0 & Hvalid0).
    (* doc-global clock-maximality at the replayed state (receiver clock
       safety) *)
    have Hbcast : op_broadcast N op0 by exists (clientId (opid op0)).
    have Hnid' : ∀ y, y ∈ delivered_ops h -> opid y ≠ in_id input.
    { move=> y Hy Heq. apply Hnotdel.
      have HDy : EvDeliver y ∈ h.
      { move: Hy. rewrite /delivered_ops list_elem_of_omap => -[ev [Hev Hdev]].
        destruct ev as [a | a]; simpl in Hdev; [done | by injection Hdev as ->]. }
      rewrite Hop0id -Heq. apply elem_of_delivered_ids. by exists y. }
    have Hnosucc' : ∀ y, y ∈ delivered_ops h -> ¬ raw_hb (to_histories N) op0 y.
    { (* causal delivery: were the new op below a delivered one, it would
         already be delivered here — contradicting its freshness *)
      move=> y Hy Hhb. apply Hnotdel.
      have HDy : EvDeliver y ∈ to_histories N c.
      { rewrite (to_histories_lookup N c h Hc).
        move: Hy. rewrite /delivered_ops list_elem_of_omap => -[ev [Hev Hdev]].
        destruct ev as [a | a]; simpl in Hdev; [done | by injection Hdev as ->]. }
      pose proof (hwf_causal_delivery N Hwf c op0 y HDy Hhb)
        as (l1 & l2 & l3 & Hsplit).
      rewrite (to_histories_lookup N c h Hc) in Hsplit.
      have Hd0 : EvDeliver op0 ∈ h by (rewrite Hsplit; set_solver).
      apply elem_of_delivered_ids. by exists op0. }
    have Hbnd : ∀ (t : TId) x, x ∈ docm_get m t ->
                clientId (item_id x) = clientId (in_id input) ->
                (clock (item_id x) < clock (in_id input))%nat.
    { move=> t x Hx Hcx.
      have Hx' : x ∈ st_items (doc_get s t) by rewrite (Hitems t).
      exact (receiver_clock_safety N t0 input (delivered_ops h) s Hwf Hbcast Hpast
               HsrcL Hnid' Hnosucc' Hinterp t x Hx' Hcx). }
    have Hmax0 : maximalId item0 (docm_get m t0).
    { move=> x Hx Hcx.
      pose proof (toItem_id input (docm_get m t0) item0 Htoit0) as Hid0.
      rewrite Hid0 in Hcx *. exact (Hbnd t0 x Hx Hcx). }
    (* progress + invariant *)
    pose proof (integrate_some input (docm_get m t0) item0 (Hinv t0) Htoit0) as (arr2 & Hint2).
    pose proof (YjsArrInvariant_integrate input (docm_get m t0) arr2 item0 (Hinv t0)
                  Htoit0 Hvalid0 Hmax0 Hint2) as (didx & _ & _ & Hinv2).
    (* the network deliver step *)
    have Hwf1 : history_wf (<[c := h ++ [EvDeliver op0]]> N)
      := history_wf_deliver N c h op0 D Hwf Hc Hreg0 HDsub Hnotdel.
    have Hcs0 : isClockSafe (in_id input) (docm_get m t0) = true
      := maximalId_isClockSafe input (docm_get m t0) item0 Htoit0 Hmax0.
    set st0 := doc_get s t0.
    have Hstep : op_effect O op0 s (<[t0 := MkYjsState arr2 (st_deleted st0)]> s).
    { exists (MkYjsState arr2 (st_deleted st0)). split; [| done].
      rewrite /op0 /= /YjsState_insert /integrateSafe -/st0 (Hitems t0) Hcs0 Hint2 //=. }
    have Hcoh1 : history_state_coh (h ++ [EvDeliver op0]) (<[t0 := arr2]> m).
    { exists (<[t0 := MkYjsState arr2 (st_deleted st0)]> s). split.
      - exact (interpHistory_snoc_deliver h op0 _ _ _ Hinterp Hstep).
      - move=> t. destruct (decide (t = t0)) as [-> | Hne].
        + rewrite doc_get_insert_eq docm_get_insert_eq //.
        + rewrite doc_get_insert_ne // docm_get_insert_ne //. }
    (* recurse *)
    have Hc1 : (<[c := h ++ [EvDeliver op0]]> N) !! c = Some (h ++ [EvDeliver op0])
      by rewrite lookup_insert_eq.
    have Hinv1 : ∀ t : TId, YjsArrInvariant (docm_get (<[t0 := arr2]> m) t).
    { move=> t. destruct (decide (t = t0)) as [-> | Hne].
      - rewrite docm_get_insert_eq. exact Hinv2.
      - rewrite docm_get_insert_ne //. }
    have Hreg1 : ∀ (i : nat) (ti' : TId * IntegrateInput (A := A)) (D' : gset YjsId),
        inputs' !! i = Some ti' -> Ds' !! i = Some D' ->
        op_registered (<[c := h ++ [EvDeliver op0]]> N) (ti'.1, OpInsert ti'.2) D'.
    { move=> i ti' D' Hi HD'.
      apply (op_registered_append N c h _ _ _ Hwf Hc).
      - move=> e He. rewrite elem_of_cons elem_of_nil in He.
        destruct He as [He | []]. discriminate.
      - exact (Hreg (S i) ti' D' Hi HD'). }
    have Hlen1 : length Ds' = length inputs' by (simpl in Hlen; lia).
    have Hbatch1 : batch_ok (h ++ [EvDeliver op0]) inputs' Ds'.
    { move=> i ti' D' Hi HD'.
      pose proof (Hbatch (S i) ti' D' Hi HD') as [Hsub' Hnin'].
      rewrite delivered_ids_app.
      have Hdel1 : delivered_ids [EvDeliver op0] = ({[in_id input]} : gset YjsId).
      { rewrite /delivered_ids /=. set_solver. }
      rewrite Hdel1.
      simpl in Hsub', Hnin'.
      split; set_solver. }
    pose proof (IH (<[c := h ++ [EvDeliver op0]]> N) (h ++ [EvDeliver op0])
                  (<[t0 := arr2]> m) Ds'
                  Hwf1 Hc1 Hcoh1 Hinv1 Hreg1 Hlen1 Hbatch1) as (m' & Hvr' & Hcoh' & Hwf').
    exists m'.
    have Heqh : h ++ (deliver_ev <$> ((t0, input) :: inputs'))
              = (h ++ [EvDeliver op0]) ++ (deliver_ev <$> inputs')
      by rewrite fmap_cons -app_assoc //.
    split_and!.
    + exact (VR_cons t0 input inputs' m arr2 m' item0 Htoit0 Hvalid0 Hmax0 Hbnd Hint2 Hvr').
    + rewrite Heqh. exact Hcoh'.
    + rewrite Heqh.
      have Hcollapse :
        <[c := (h ++ [EvDeliver op0]) ++ (deliver_ev <$> inputs')]>
          (<[c := h ++ [EvDeliver op0]]> N)
        = <[c := (h ++ [EvDeliver op0]) ++ (deliver_ev <$> inputs')]> N.
      { rewrite insert_insert. case_decide; [reflexivity | congruence]. }
      rewrite Hcollapse in Hwf'. exact Hwf'.
Qed.

(* ===== convergence: document = f(delivered op-set) (issue #40) =========== *)

(** Membership in the delivered-op list, event-level. *)
Lemma elem_of_delivered_ops h (op : Op) :
  op ∈ delivered_ops h ↔ EvDeliver op ∈ h.
Proof.
  rewrite /delivered_ops list_elem_of_omap. split.
  - move=> [ev [Hev Hdel]]. destruct ev as [a | a]; simpl in Hdel;
      [done | by injection Hdel as ->].
  - move=> Hin. by exists (EvDeliver op).
Qed.

(** Delivered ops are membership-determined by their delivered IDS: every
    delivered op has a broadcast cause, and broadcast ids are unique
    network-wide ([hwf_msg_id_unique]), so two replicas of one well-formed
    network that delivered the same id sets delivered the same op sets. This
    is what lets the convergence statement (and the sync protocol's state
    vectors) speak in ids. *)
Lemma delivered_ops_same_ids N c1 c2 h1 h2 :
  history_wf N -> N !! c1 = Some h1 -> N !! c2 = Some h2 ->
  (∀ id : YjsId, id ∈ delivered_ids h1 ↔ id ∈ delivered_ids h2) ->
  ∀ x : Op, x ∈ delivered_ops h1 ↔ x ∈ delivered_ops h2.
Proof.
  move=> Hwf Hc1 Hc2 Hids.
  have Haux : ∀ ca cb ha hb, N !! ca = Some ha -> N !! cb = Some hb ->
      (∀ id : YjsId, id ∈ delivered_ids ha -> id ∈ delivered_ids hb) ->
      ∀ x : Op, x ∈ delivered_ops ha -> x ∈ delivered_ops hb.
  { move=> ca cb ha hb Hca Hcb Hsub x Hx.
    have Hidx : opid x ∈ delivered_ids ha.
    { apply elem_of_delivered_ids. exists x. split; [| done].
      by apply elem_of_delivered_ops. }
    have Hidb := Hsub _ Hidx.
    apply elem_of_delivered_ids in Hidb. destruct Hidb as (y & Hyb & Hyid).
    have Hxa : EvDeliver x ∈ to_histories N ca.
    { rewrite (to_histories_lookup N ca ha Hca). by apply elem_of_delivered_ops. }
    pose proof (hwf_deliver_has_a_cause N Hwf ca x Hxa) as (ja & Hja).
    have Hyc : EvDeliver y ∈ to_histories N cb
      by rewrite (to_histories_lookup N cb hb Hcb).
    pose proof (hwf_deliver_has_a_cause N Hwf cb y Hyc) as (jb & Hjb).
    have Hxy : x = y
      := proj2 (hwf_msg_id_unique N Hwf x y ja jb Hja Hjb (eq_sym Hyid)).
    subst y. by apply elem_of_delivered_ops. }
  move=> x. split.
  - apply (Haux c1 c2 h1 h2 Hc1 Hc2). move=> id Hid. by apply Hids.
  - apply (Haux c2 c1 h2 h1 Hc2 Hc1). move=> id Hid. by apply Hids.
Qed.

(** THE issue #40 statement, raw-history level: the document is a function of
    the delivered op-set. Two replicas of one well-formed network whose
    delivered id sets agree replay to pointwise-equal documents; delivery
    order and batching appear nowhere, so any two causally consistent orders
    of one op set land in the same document. The proof packages the raw map
    into the doc operation network and CONSUMES the model's strong eventual
    consistency ([DocOperationNetwork_converge_final]) at this boundary; no
    convergence argument is re-proved here. Per §8.4 of the #42 plan the
    statement is about the item sequence ([docm_get]); tombstone flags are
    not tracked by the history. *)
Lemma history_state_converge N c1 c2 h1 h2 (m1 m2 : DocM) :
  history_wf N ->
  N !! c1 = Some h1 -> N !! c2 = Some h2 ->
  history_state_coh h1 m1 -> history_state_coh h2 m2 ->
  (∀ id : YjsId, id ∈ delivered_ids h1 ↔ id ∈ delivered_ids h2) ->
  ∀ t : TId, docm_get m1 t = docm_get m2 t.
Proof.
  move=> Hwf Hc1 Hc2 [s1 [Hint1 Hm1]] [s2 [Hint2 Hm2]] Hids t.
  have Hops := delivered_ops_same_ids N c1 c2 h1 h2 Hwf Hc1 Hc2 Hids.
  set dn := to_doc_network N Hwf.
  have Heff1 : effect_list O (toDeliverMessages dn c1) (op_init O) s1.
  { rewrite /toDeliverMessages to_doc_network_histories (to_histories_lookup N c1 h1 Hc1).
    exact Hint1. }
  have Heff2 : effect_list O (toDeliverMessages dn c2) (op_init O) s2.
  { rewrite /toDeliverMessages to_doc_network_histories (to_histories_lookup N c2 h2 Hc2).
    exact Hint2. }
  have Hmem : ∀ x, x ∈ toDeliverMessages dn c1 ↔ x ∈ toDeliverMessages dn c2.
  { move=> x.
    rewrite /toDeliverMessages to_doc_network_histories
      (to_histories_lookup N c1 h1 Hc1) (to_histories_lookup N c2 h2 Hc2).
    exact (Hops x). }
  have Heq : s1 = s2
    := DocOperationNetwork_converge_final dn c1 c2 s1 s2 Heff1 Heff2 Hmem.
  rewrite -(Hm1 t) -(Hm2 t) Heq //.
Qed.

(** Delivered ids of an [applyUpdate] extension: the receiver's delivered set
    grows by exactly the batch's input ids. This is the rewriting that plugs
    [wp_store__applyUpdate_certs]' post-state history into the convergence
    statement. *)
Lemma delivered_ids_deliver_evs h (inputs : list (TId * IntegrateInput (A := A))) :
  delivered_ids (h ++ (deliver_ev <$> inputs)) =
  delivered_ids h ∪ list_to_set ((λ ti : TId * IntegrateInput (A := A), in_id ti.2) <$> inputs).
Proof.
  rewrite delivered_ids_app. f_equal.
  elim: inputs => [| ti inputs' IH].
  - rewrite /delivered_ids /=. done.
  - rewrite !fmap_cons.
    have -> : delivered_ids (deliver_ev ti :: (deliver_ev <$> inputs'))
            = {[in_id ti.2]} ∪ delivered_ids (deliver_ev <$> inputs').
    { rewrite /delivered_ids /delivered_ops omap_cons /=. done. }
    rewrite IH /=. done.
Qed.

(** Order independence of batch delivery, id-level: applying PERMUTED batches
    on top of histories with equal delivered sets leaves the delivered sets
    equal, so (via [history_state_converge]) the documents agree. *)
Lemma delivered_ids_deliver_evs_perm h1 h2
    (inputs1 inputs2 : list (TId * IntegrateInput (A := A))) :
  inputs1 ≡ₚ inputs2 ->
  (∀ id : YjsId, id ∈ delivered_ids h1 ↔ id ∈ delivered_ids h2) ->
  ∀ id : YjsId,
    id ∈ delivered_ids (h1 ++ (deliver_ev <$> inputs1)) ↔
    id ∈ delivered_ids (h2 ++ (deliver_ev <$> inputs2)).
Proof.
  move=> Hperm Hids id.
  rewrite !delivered_ids_deliver_evs.
  have -> : (list_to_set ((λ ti : TId * IntegrateInput (A := A), in_id ti.2) <$> inputs1) : gset YjsId)
          = list_to_set ((λ ti : TId * IntegrateInput (A := A), in_id ti.2) <$> inputs2).
  { apply list_to_set_perm_L. by apply fmap_Permutation. }
  rewrite !elem_of_union. by rewrite Hids.
Qed.

(* ===== allocation ========================================================= *)

(** The all-empty network is well-formed (the ghost allocation's initial
    invariant). *)
Lemma history_wf_init (C : gset ClientId) :
  history_wf (gset_to_gmap [] C).
Proof.
  have Hemp : ∀ i, to_histories (gset_to_gmap ([] : list Ev) C) i = [].
  { move=> i. rewrite /to_histories lookup_gset_to_gmap.
    destruct (decide (i ∈ C)) as [Hin | Hin].
    - rewrite option_guard_True //.
    - rewrite option_guard_False //. }
  split => i; rewrite ?Hemp.
  - constructor.
  - move=> e. rewrite elem_of_nil //.
  - move=> mi i' j Hmi. rewrite Hemp elem_of_nil // in Hmi.
  - move=> e1 e2 He2. rewrite elem_of_nil // in He2.
  - move=> e pre post Hsplit. exfalso.
    have : EvBroadcast e ∈ ([] : list Ev) by rewrite Hsplit; set_solver.
    rewrite elem_of_nil //.
  - move=> i' He. rewrite Hemp elem_of_nil // in He.
  - move=> i' hist1 hist2 array Hsplit. exfalso.
    have : EvBroadcast i ∈ ([] : list Ev) by rewrite Hemp in Hsplit; rewrite Hsplit; set_solver.
    rewrite elem_of_nil //.
  - move=> e pre post Hsplit. exfalso.
    have : EvBroadcast e ∈ ([] : list Ev) by rewrite Hsplit; set_solver.
    rewrite elem_of_nil //.
  - move=> e He. rewrite !elem_of_nil in He. tauto.
Qed.

Lemma ops_coh_init (C : gset ClientId) :
  ops_coh (gset_to_gmap [] C) ∅.
Proof.
  split.
  - move=> id op D. rewrite lookup_empty //.
  - move=> op [i Hin]. exfalso. move: Hin.
    rewrite /to_histories lookup_gset_to_gmap.
    destruct (decide (i ∈ C)) as [HC | HC].
    + rewrite option_guard_True //= elem_of_nil //.
    + rewrite option_guard_False //= elem_of_nil //.
Qed.

End network_model.
