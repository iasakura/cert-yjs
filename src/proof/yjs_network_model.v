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
From yjs Require Import util.
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

(* ----- the per-author views (used by [history_wf]'s FIFO field) ----- *)

(** The broadcast projection of one history (the author's op log), the dual
    of [delivered_ops]. *)
Definition broadcast_ops (h : list Ev) : list Op :=
  omap (λ e, match e with EvBroadcast op => Some op | _ => None end) h.

(** The ops of author [j] delivered in [h], in delivery order. *)
Definition delivered_from (h : list Ev) (j : ClientId) : list Op :=
  filter (λ op, clientId (opid op) = j) (delivered_ops h).

Lemma elem_of_broadcast_ops (h : list Ev) (op : Op) :
  op ∈ broadcast_ops h ↔ EvBroadcast op ∈ h.
Proof.
  rewrite /broadcast_ops list_elem_of_omap. split.
  - move=> [e [He Hfe]]. destruct e; [| done]. simpl in Hfe.
    injection Hfe as ->. exact He.
  - move=> He. exists (EvBroadcast op). by split.
Qed.

Lemma elem_of_delivered_ops_ev (h : list Ev) (op : Op) :
  op ∈ delivered_ops h ↔ EvDeliver op ∈ h.
Proof.
  rewrite /delivered_ops list_elem_of_omap. split.
  - move=> [e [He Hfe]]. destruct e; [done |]. simpl in Hfe.
    injection Hfe as ->. exact He.
  - move=> He. exists (EvDeliver op). by split.
Qed.

Lemma elem_of_delivered_from (h : list Ev) (j : ClientId) (op : Op) :
  op ∈ delivered_from h j ↔ EvDeliver op ∈ h ∧ clientId (opid op) = j.
Proof.
  rewrite /delivered_from list_elem_of_filter elem_of_delivered_ops_ev.
  split; move=> [? ?]; by split.
Qed.

Lemma NoDup_broadcast_ops (h : list Ev) :
  NoDup h -> NoDup (broadcast_ops h).
Proof.
  induction 1 as [| e h He Hnd IH]; simpl; [constructor |].
  destruct e as [op | op]; simpl; [| exact IH].
  constructor; [| exact IH].
  rewrite elem_of_broadcast_ops. move=> Hin. exact (He Hin).
Qed.

(* ----- snoc laws for the per-author views ----- *)

Lemma delivered_from_snoc_deliver (p : list Ev) (op : Op) (j : ClientId) :
  clientId (opid op) = j ->
  delivered_from (p ++ [EvDeliver op]) j = delivered_from p j ++ [op].
Proof.
  move=> Hj.
  rewrite /delivered_from delivered_ops_app delivered_ops_deliver filter_app
          filter_cons_True // filter_nil //.
Qed.

Lemma delivered_from_snoc_deliver_ne (p : list Ev) (op : Op) (j : ClientId) :
  clientId (opid op) ≠ j ->
  delivered_from (p ++ [EvDeliver op]) j = delivered_from p j.
Proof.
  move=> Hj.
  rewrite /delivered_from delivered_ops_app delivered_ops_deliver filter_app
          filter_cons_False // filter_nil app_nil_r //.
Qed.

Lemma delivered_from_snoc_broadcast (p : list Ev) (op : Op) (j : ClientId) :
  delivered_from (p ++ [EvBroadcast op]) j = delivered_from p j.
Proof.
  rewrite /delivered_from delivered_ops_app delivered_ops_broadcast app_nil_r //.
Qed.

Lemma broadcast_ops_app (h1 h2 : list Ev) :
  broadcast_ops (h1 ++ h2) = broadcast_ops h1 ++ broadcast_ops h2.
Proof. rewrite /broadcast_ops omap_app //. Qed.

Lemma broadcast_ops_snoc_deliver (p : list Ev) (op : Op) :
  broadcast_ops (p ++ [EvDeliver op]) = broadcast_ops p.
Proof. rewrite broadcast_ops_app /= app_nil_r //. Qed.

Lemma broadcast_ops_snoc_broadcast (p : list Ev) (op : Op) :
  broadcast_ops (p ++ [EvBroadcast op]) = broadcast_ops p ++ [op].
Proof. rewrite broadcast_ops_app //. Qed.

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

(** The model's network axioms over the raw map, plus our disciplines.
    The [interpHistory]-mentioning fields use the doc operation instance [O]
    with [DocIsValidMessage].

    Since issue #40 there is NO causal-delivery field: [applyUpdate] delivers
    an op as soon as its structural dependencies (origins and same-author
    predecessor) have arrived, which is strictly weaker than happens-before.
    Its load-bearing consequence is kept as a field, maintainable by the
    structural gate:
    - [hwf_fifo]: per author the delivered ops form a PREFIX of that author's
      broadcast log (the lossless state-vector reading; the same-author
      predecessor gate maintains it). *)
Record history_wf N : Prop := {
  (* NodeHistories *)
  hwf_nodup : ∀ i, NoDup (to_histories N i);
  (* NetworkBase *)
  hwf_deliver_has_a_cause : ∀ i e,
    EvDeliver e ∈ to_histories N i -> ∃ j, EvBroadcast e ∈ to_histories N j;
  hwf_msg_id_unique : ∀ mi mj i j,
    EvBroadcast mi ∈ to_histories N i -> EvBroadcast mj ∈ to_histories N j ->
    opid mi = opid mj -> i = j ∧ mi = mj;
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
  (* ours (issue #40): per-author FIFO delivery. *)
  hwf_fifo : ∀ i j,
    delivered_from (to_histories N i) j `prefix_of` broadcast_ops (to_histories N j);
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

(* Since issue #40 the raw histories are NOT causally delivered, so they do
   not package into the model's [CausalNetwork] / [OperationNetwork] /
   [DocOperationNetwork] records anymore; the validity-transport and
   convergence arguments run over the raw fields directly (raw ports of the
   upstream lemmas, below). Only the causal-delivery-free [NetworkBase]
   packaging survives. *)

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

(* ===== history-size bound (issue #28 U5): the replayed document holds at
   most one item per history event ========================================= *)

Lemma insertIdxIfInBounds_length (n : nat) (x : YjsItem A) (l : list (YjsItem A)) :
  (length (insertIdxIfInBounds n x l) <= S (length l))%nat.
Proof.
  rewrite /insertIdxIfInBounds. case_decide; last lia.
  rewrite length_app /= length_take length_drop. lia.
Qed.

Lemma yjs_op_effect_size (op : @YjsOperation A) (st st' : YjsState A) :
  yjs_op_effect op st st' -> (length (st_items st') <= S (length (st_items st)))%nat.
Proof.
  destruct op as [input | id did]; rewrite /yjs_op_effect.
  - rewrite /YjsState_insert /integrateSafe.
    destruct (isClockSafe (in_id input) (st_items st)); last done.
    rewrite /integrate.
    destruct (findLeftIdx (in_originId input) (st_items st)) as [li|]; simpl; try done.
    destruct (findRightIdx (in_rightOriginId input) (st_items st)) as [ri|]; simpl; try done.
    destruct (findIntegratedIndex li ri input (st_items st)) as [di|]; simpl; try done.
    destruct (mkItemByIndex li ri input (st_items st)) as [it|]; simpl; try done.
    move=> [= <-]. simpl. apply insertIdxIfInBounds_length.
  - move=> ->. simpl. lia.
Qed.

(** Total number of items across a doc state. *)
Definition doc_total_size (s : gmap TId (YjsState A)) : nat :=
  map_fold (λ _ st acc, (length (st_items st) + acc)%nat) 0%nat s.

Lemma doc_total_size_insert (s : gmap TId (YjsState A)) (t : TId) (st' : YjsState A) :
  doc_total_size (<[t := st']> s)
  = (length (st_items st') + doc_total_size (delete t s))%nat.
Proof.
  rewrite /doc_total_size -insert_delete_eq map_fold_insert_L.
  - done.
  - move=> j1 j2 z1 z2 y Hne. lia.
  - apply lookup_delete_eq.
Qed.

Lemma doc_total_size_get (s : gmap TId (YjsState A)) (t : TId) :
  doc_total_size s
  = (length (st_items (doc_get s t)) + doc_total_size (delete t s))%nat.
Proof.
  destruct (s !! t) as [st|] eqn:Ht.
  - rewrite -{1}(insert_id s t st Ht) doc_total_size_insert /doc_get Ht //.
  - rewrite delete_id // /doc_get Ht /=. lia.
Qed.

Lemma doc_op_effect_total_size (op : Op) (s s' : gmap TId (YjsState A)) :
  op_effect O op s s' -> (doc_total_size s' <= S (doc_total_size s))%nat.
Proof.
  move=> [st' [Heff ->]].
  have Hstep := yjs_op_effect_size op.2 (doc_get s op.1) st' Heff.
  rewrite doc_total_size_insert (doc_total_size_get s op.1). lia.
Qed.

Lemma effect_list_total_size (l : list Op) (init s : gmap TId (YjsState A)) :
  effect_list O l init s -> (doc_total_size s <= doc_total_size init + length l)%nat.
Proof.
  move: init. induction l as [|op l IH] => init Heff.
  - move: Heff => /(effect_list_nil O) ->. lia.
  - move: Heff => /(effect_list_cons O) [mmid [Hop Hrest]].
    have H1 := doc_op_effect_total_size op init mmid Hop.
    have H2 := IH mmid Hrest. simpl. lia.
Qed.

(** The state replayed from a history holds at most [length h] items. *)
Lemma history_interp_total_size h (s : gmap TId (YjsState A)) :
  interpHistory O h (op_init O) s -> (doc_total_size s <= length h)%nat.
Proof.
  rewrite /interpHistory => Heff.
  have H1 := effect_list_total_size (omap deliverP h) (op_init O) s Heff.
  have H2 : ∀ h0, (length (omap deliverP h0) <= length h0)%nat.
  { clear. elim=> [| e h0 IHh]; cbn; [lia |].
    destruct (deliverP e); cbn; lia. }
  have H0 : doc_total_size (op_init O) = 0%nat
    by rewrite /doc_total_size map_fold_empty.
  have := H2 h. lia.
Qed.

(** Per-type-list version for the store-side consumers: a duplicate-free
    family of types holds at most [length h] items in total. *)
Lemma history_state_coh_size_list h (m : DocM) (ts : list TId) :
  history_state_coh h m -> NoDup ts ->
  (foldr (λ t acc, (length (docm_get m t) + acc)%nat) 0%nat ts <= length h)%nat.
Proof.
  move=> [s [Hs Hm]] Hnd.
  have Hbound := history_interp_total_size h s Hs.
  have Hsuff : ∀ (ts0 : list TId) (s0 : gmap TId (YjsState A)), NoDup ts0 ->
      (foldr (λ t acc, (length (st_items (doc_get s0 t)) + acc)%nat) 0%nat ts0
       <= doc_total_size s0)%nat.
  { induction ts0 as [|t ts0 IH] => s0 Hnd0.
    - simpl. lia.
    - apply NoDup_cons in Hnd0. destruct Hnd0 as [Hnotin Hnd'].
      simpl.
      have Hrest : ∀ (ts1 : list TId), t ∉ ts1 ->
          foldr (λ t' acc, (length (st_items (doc_get s0 t')) + acc)%nat) 0%nat ts1
        = foldr (λ t' acc, (length (st_items (doc_get (delete t s0) t')) + acc)%nat) 0%nat ts1.
      { induction ts1 as [|t' ts1 IHts] => Hnotin1; simpl; [done |].
        f_equal.
        - have Hne : t' ≠ t.
          { move=> Heq. apply Hnotin1. apply elem_of_cons. left. by rewrite Heq. }
          rewrite /doc_get lookup_delete_ne //.
        - apply IHts. move=> Hin. apply Hnotin1. apply elem_of_cons. by right. }
      rewrite (Hrest ts0 Hnotin).
      have Hihd : (foldr (λ t' acc, (length (st_items (doc_get (delete t s0) t')) + acc)%nat) 0%nat ts0
                   <= doc_total_size (delete t s0))%nat.
      { apply IH. exact Hnd'. }
      rewrite (doc_total_size_get s0 t). lia. }
  have Heq : ∀ ts1 : list TId,
      foldr (λ t acc, (length (docm_get m t) + acc)%nat) 0%nat ts1
    = foldr (λ t acc, (length (st_items (doc_get s t)) + acc)%nat) 0%nat ts1.
  { induction ts1 as [|t1 ts1 IHts]; simpl; [done | rewrite -(Hm t1) IHts //]. }
  rewrite (Heq ts).
  have := Hsuff ts s Hnd. lia.
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

(** What the ops registry records per op: broadcast at its author. Since
    issue #40 the certificate carries NO causal-cover set: the structural
    gate replaces causal-closure obligations entirely, so "this op was
    broadcast (with this id, at its author)" is the whole certificate. *)
Definition op_registered N op : Prop :=
  EvBroadcast op ∈ to_histories N (clientId (opid op)).

(** Registry coherence: every registered op is broadcast; every broadcast op
    is registered. *)
Definition ops_coh N (ops : gmap YjsId Op) : Prop :=
  (∀ id op, ops !! id = Some op -> opid op = id ∧ op_registered N op) ∧
  (∀ op, op_broadcast N op -> is_Some (ops !! opid op)).

(** Certificate stability: a registration survives any one-client append. *)
Lemma op_registered_append N c h (tail : list Ev) op :
  N !! c = Some h ->
  op_registered N op ->
  op_registered (<[c := h ++ tail]> N) op.
Proof.
  move=> Hc Hbc.
  rewrite /op_registered in Hbc *.
  destruct (decide (clientId (opid op) = c)) as [Hcc | Hcc].
  - rewrite Hcc to_histories_insert elem_of_app. left.
    rewrite Hcc (to_histories_lookup _ _ _ Hc) in Hbc. exact Hbc.
  - rewrite (to_histories_insert_ne _ _ _ _ Hcc) //.
Qed.

(** A fresh id is unregistered (the [ghost_map_insert] side condition). *)
Lemma ops_coh_lookup_fresh N (ops : gmap YjsId Op) (id : YjsId) :
  ops_coh N ops -> ¬ id_broadcast N id -> ops !! id = None.
Proof.
  move=> [Hc1 _] Hfresh.
  destruct (ops !! id) as [op' |] eqn:Hlk; [| done]. exfalso.
  destruct (Hc1 _ _ Hlk) as [Hopid Hbc].
  apply Hfresh. exists op'. split; [by eexists | exact Hopid].
Qed.

(** Registry coherence survives a fresh broadcast (+ its registration). *)
Lemma ops_coh_broadcast N c h (ops : gmap YjsId Op) (op0 : Op) :
  history_wf N -> N !! c = Some h ->
  ¬ id_broadcast N (opid op0) ->
  ops_coh N ops ->
  op_registered (<[c := h ++ [EvBroadcast op0; EvDeliver op0]]> N) op0 ->
  ops_coh (<[c := h ++ [EvBroadcast op0; EvDeliver op0]]> N)
    (<[opid op0 := op0]> ops).
Proof.
  move=> Hwf Hc Hfresh [Hc1 Hc2] Hreg.
  split.
  - move=> id op Hlk.
    destruct (decide (id = opid op0)) as [-> | Hne].
    + rewrite lookup_insert_eq in Hlk. injection Hlk as <-.
      split; [reflexivity | exact Hreg].
    + rewrite lookup_insert_ne in Hlk; [| congruence].
      destruct (Hc1 _ _ Hlk) as [Hopid Hregd].
      split; [exact Hopid | exact (op_registered_append N c h _ op Hc Hregd)].
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
Lemma ops_coh_deliver_tail N c h (ops : gmap YjsId Op) (tail : list Ev) :
  history_wf N -> N !! c = Some h ->
  (∀ e : Op, EvBroadcast e ∉ tail) ->
  ops_coh N ops ->
  ops_coh (<[c := h ++ tail]> N) ops.
Proof.
  move=> Hwf Hc Htail [Hc1 Hc2].
  split.
  - move=> id op Hlk.
    destruct (Hc1 _ _ Hlk) as [Hopid Hreg].
    split; [exact Hopid | exact (op_registered_append N c h _ op Hc Hreg)].
  - move=> op Hbc.
    apply (op_broadcast_append N c h _ op Hc) in Hbc.
    destruct Hbc as [Hold | Hnew]; [exact (Hc2 op Hold) | by destruct (Htail op)].
Qed.

(* ===== self-delivery saturation =========================================== *)

(** A client has delivered ALL of its own broadcasts, in order: its per-author
    view of itself IS its broadcast log (immediate self-delivery + duplicate
    freedom). Feeds the FIFO field through the broadcast step. *)
Lemma self_delivered_all N (j : ClientId) :
  history_wf N ->
  delivered_from (to_histories N j) j = broadcast_ops (to_histories N j).
Proof.
  move=> Hwf.
  set hj := to_histories N j.
  have Hnd : NoDup hj := hwf_nodup N Hwf j.
  suff Hgen : ∀ p rest, hj = p ++ rest ->
      delivered_from p j = broadcast_ops p ∨
      (∃ p' y, p = p' ++ [EvBroadcast y] ∧ delivered_from p j = broadcast_ops p').
  { destruct (Hgen hj [] (eq_sym (app_nil_r hj))) as [Hd | (p' & y & Hp & _)];
      first exact Hd.
    exfalso.
    have Hsplit : hj = p' ++ [EvBroadcast y] ++ [] by rewrite Hp app_nil_r.
    destruct (hwf_self_deliver N Hwf j y p' [] Hsplit) as (post' & Hpost).
    discriminate. }
  elim/rev_ind => [| e p IH] rest Hsplit.
  { left. rewrite /delivered_from /delivered_ops //=. }
  have Hsplit' : hj = p ++ (e :: rest) by rewrite Hsplit -app_assoc //.
  have Hpre := IH (e :: rest) Hsplit'.
  destruct e as [op | op].
  - (* a broadcast: it must be pending its own delivery; the previous prefix
       cannot itself end in a pending broadcast (self-delivery forces the next
       event) *)
    right. exists p, op. split; [done |].
    destruct Hpre as [Hd | (p' & y & Hp & Hd)].
    + rewrite delivered_from_snoc_broadcast //.
    + exfalso.
      have Hsp : hj = p' ++ [EvBroadcast y] ++ (EvBroadcast op :: rest)
        by rewrite Hsplit' Hp -app_assoc //.
      destruct (hwf_self_deliver N Hwf j y p' _ Hsp) as (post' & Hpost).
      discriminate.
  - (* a delivery *)
    destruct Hpre as [Hd | (p' & y & Hp & Hd)].
    + (* no pending broadcast: an own-authored delivery here is impossible *)
      destruct (decide (clientId (opid op) = j)) as [Hj | Hj]; last first.
      { left. rewrite delivered_from_snoc_deliver_ne // broadcast_ops_snoc_deliver //. }
      exfalso.
      (* op was broadcast at j (cause + client id), so B op ∈ hj; its delivery
         follows it immediately, and both are in [p ++ [D op] ++ rest]. *)
      have Hdel : EvDeliver op ∈ hj by rewrite Hsplit'; set_solver.
      destruct (hwf_deliver_has_a_cause N Hwf j op Hdel) as (j0 & Hj0).
      have Hj0j : j0 = clientId (opid op) := eq_sym (hwf_client_id N Hwf op j0 Hj0).
      rewrite Hj0j Hj in Hj0.
      (* B op ∈ p: it cannot be in [D op :: rest] later than its delivery...
         it CAN be in rest; but then self-delivery of B op gives a SECOND
         D op, clashing with NoDup. Split on where B op sits. *)
      have Hbmem : EvBroadcast op ∈ p ∨ EvBroadcast op ∈ (EvDeliver op :: rest).
      { move: Hj0. rewrite -/hj Hsplit' elem_of_app. move=> [Hl | Hr]; [by left | by right]. }
      destruct Hbmem as [Hbp | Hbrest].
      * (* B op ∈ p, no pending broadcast at p means D op ∈ p already; but
           D op also sits right after p: duplicate *)
        have Hop_in : op ∈ broadcast_ops p by apply elem_of_broadcast_ops.
        rewrite -Hd in Hop_in.
        apply elem_of_delivered_from in Hop_in. destruct Hop_in as [Hdp _].
        move: Hnd. rewrite Hsplit' NoDup_app. move=> [_ [Hdisj _]].
        exact (Hdisj (EvDeliver op) Hdp ltac:(by left)).
      * (* B op after its own delivery: self-delivery would append a second
           D op after it, again a duplicate *)
        move: Hbrest. rewrite elem_of_cons. move=> [Heq | Hbrest]; first discriminate.
        destruct (list_elem_of_split _ _ Hbrest) as (r1 & r2 & Hrest).
        have Hsp2 : hj = (p ++ [EvDeliver op] ++ r1) ++ [EvBroadcast op] ++ r2
          by rewrite Hsplit' Hrest -!app_assoc //.
        destruct (hwf_self_deliver N Hwf j op _ _ Hsp2) as (post' & Hpost).
        move: Hnd. rewrite Hsp2 Hpost NoDup_app. move=> [_ [Hdisj _]].
        apply (Hdisj (EvDeliver op)); [set_solver | set_solver].
    + (* pending broadcast y: self-delivery forces e = D y *)
      have Hsp : hj = p' ++ [EvBroadcast y] ++ (EvDeliver op :: rest)
        by rewrite Hsplit' Hp -app_assoc //.
      destruct (hwf_self_deliver N Hwf j y p' _ Hsp) as (post' & Hpost).
      injection Hpost as Heq Hrest'. subst op post'.
      left.
      have Hyj : clientId (opid y) = j.
      { apply (hwf_client_id N Hwf y j). rewrite -/hj Hsp. set_solver. }
      rewrite (delivered_from_snoc_deliver _ _ _ Hyj) broadcast_ops_snoc_deliver
              Hd Hp broadcast_ops_snoc_broadcast //.
Qed.

(* ===== author-side clock monotonicity ===================================== *)

(** Of two broadcasts in one author's history, the earlier has the strictly
    smaller clock: the earlier op is self-delivered before the later one is
    broadcast, so its item is in the author's replayed state at that point,
    and [hwf_unique_id] bounds it. This makes the per-author broadcast log
    clock-sorted, the backbone of the FIFO / pending arguments (issue #40;
    extracted from the retired [receiver_clock_safety], whose remaining
    causal-delivery reasoning the structural gate replaces). *)
Lemma author_earlier_clock N (j : ClientId) (x_op op0 : Op) (l1 l2 l3 : list Ev) :
  history_wf N ->
  to_histories N j = l1 ++ [EvBroadcast x_op] ++ l2 ++ [EvBroadcast op0] ++ l3 ->
  (clock (opid x_op) < clock (opid op0))%nat.
Proof.
  move=> Hwf Hsplit.
  have Hxbc : EvBroadcast x_op ∈ to_histories N j by rewrite Hsplit; set_solver.
  have H0bc : EvBroadcast op0 ∈ to_histories N j by rewrite Hsplit; set_solver.
  have Hxj : clientId (opid x_op) = j := hwf_client_id N Hwf x_op j Hxbc.
  have H0j : clientId (opid op0) = j := hwf_client_id N Hwf op0 j H0bc.
  pose proof (hwf_insert_only N Hwf j x_op (or_introl Hxbc)) as (xin & Hxop).
  destruct x_op as [t xop2]. simpl in Hxop. subst xop2.
  have Hsplit' : to_histories N j
      = l1 ++ [EvBroadcast (t, OpInsert xin)] ++ (l2 ++ [EvBroadcast op0] ++ l3)
    by rewrite Hsplit.
  pose proof (hwf_self_deliver N Hwf j (t, OpInsert xin) l1 _ Hsplit') as (post' & Hpost).
  destruct l2 as [| e2 l2'].
  { simpl in Hpost. injection Hpost as Hpost _. discriminate. }
  have He2 : e2 = EvDeliver (t, OpInsert xin).
  { move: Hpost. simpl. move=> Hpost. by injection Hpost. }
  subst e2.
  have Hsplit0 : to_histories N j
      = (l1 ++ [EvBroadcast (t, OpInsert xin)] ++ (EvDeliver (t, OpInsert xin) :: l2'))
        ++ [EvBroadcast op0] ++ l3.
  { rewrite Hsplit -!app_assoc //. }
  set hist1 := l1 ++ [EvBroadcast (t, OpInsert xin)] ++ (EvDeliver (t, OpInsert xin) :: l2').
  pose proof (hwf_broadcast_valid N Hwf j op0 hist1 l3 Hsplit0) as (s0 & Hinterp0 & _).
  pose proof (hwf_unique_id N Hwf op0 j hist1 l3 s0 Hsplit0 Hinterp0) as Huid.
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
  have Hccit : clientId (item_id it) = clientId (opid op0).
  { rewrite Hitid /= H0j. exact Hxj. }
  pose proof (Huid t it Hitmem Hccit) as Hclk.
  rewrite Hitid in Hclk. exact Hclk.
Qed.

(* ----- positions: omap splits, unique occurrences, local order ----- *)

(** Split a list at the event backing position [n] of its [omap] image. *)
Lemma omap_lookup_split {X Y : Type} (f : X -> option Y) (l : list X) (n : nat) (y : Y) :
  omap f l !! n = Some y ->
  ∃ p e s, l = p ++ e :: s ∧ f e = Some y ∧ length (omap f p) = n.
Proof.
  move: n. induction l as [| x l IH] => n; simpl.
  - rewrite lookup_nil //.
  - destruct (f x) as [y'|] eqn:Hfx; simpl.
    + destruct n as [| n']; simpl.
      * move=> [= <-]. exists [], x, l. split_and!; [done | exact Hfx | done].
      * move=> Hn. destruct (IH n' Hn) as (p & e & s & -> & Hfe & Hlen).
        exists (x :: p), e, s. split_and!; [done | exact Hfe |].
        simpl. rewrite Hfx /= Hlen //.
    + move=> Hn. destruct (IH n Hn) as (p & e & s & -> & Hfe & Hlen).
      exists (x :: p), e, s. split_and!; [done | exact Hfe |].
      simpl. rewrite Hfx Hlen //.
Qed.

(** With duplicate-free events, anything locally ordered before the event at
    the split point lands in the prefix. *)
Lemma raw_lo_in_prefix (hc p rest : list Ev) (e1 e2 : Ev) :
  NoDup hc -> hc = p ++ e2 :: rest ->
  (∃ l1 l2 l3, hc = l1 ++ [e1] ++ l2 ++ [e2] ++ l3) ->
  e1 ∈ p.
Proof.
  move=> Hnd Hsplit [l1 [l2 [l3 Hsplit2]]].
  have He2a : hc !! length p = Some e2 by rewrite Hsplit list_lookup_middle //.
  have He2b : hc !! length (l1 ++ e1 :: l2) = Some e2.
  { rewrite Hsplit2 /=.
    replace (l1 ++ e1 :: l2 ++ e2 :: l3) with ((l1 ++ e1 :: l2) ++ e2 :: l3)
      by (rewrite -app_assoc //).
    rewrite list_lookup_middle //. }
  have Hpos := NoDup_lookup hc _ _ e2 Hnd He2a He2b.
  have He1 : hc !! length l1 = Some e1 by rewrite Hsplit2 list_lookup_middle //.
  have Hlt : (length l1 < length p)%nat.
  { rewrite Hpos length_app /=. lia. }
  rewrite Hsplit lookup_app_l // in He1.
  exact (list_elem_of_lookup_2 _ _ _ He1).
Qed.

(** Two positions of an author's broadcast log are locally ordered at the
    author. *)
Lemma broadcast_ops_lo (h : list Ev) (q1 q2 : nat) (o1 o2 : Op) :
  (q1 < q2)%nat ->
  broadcast_ops h !! q1 = Some o1 ->
  broadcast_ops h !! q2 = Some o2 ->
  ∃ l1 l2 l3, h = l1 ++ [EvBroadcast o1] ++ l2 ++ [EvBroadcast o2] ++ l3.
Proof.
  move=> Hlt H1 H2.
  destruct (omap_lookup_split _ _ _ _ H2) as (p & e2 & s & Hsp & Hfe2 & Hlen2).
  have He2 : e2 = EvBroadcast o2.
  { destruct e2; [| done]. simpl in Hfe2. by injection Hfe2 as ->. }
  have H1p : broadcast_ops p !! q1 = Some o1.
  { move: H1. rewrite Hsp /broadcast_ops omap_app lookup_app_l //.
    rewrite -/(broadcast_ops p) Hlen2 //. }
  destruct (omap_lookup_split _ _ _ _ H1p) as (p' & e1 & s' & Hsp' & Hfe1 & _).
  have He1 : e1 = EvBroadcast o1.
  { destruct e1; [| done]. simpl in Hfe1. by injection Hfe1 as ->. }
  exists p', s', s. rewrite Hsp Hsp' He1 He2 -app_assoc //.
Qed.


(** Clocks strictly increase along an author's broadcast log
    ([author_earlier_clock] at the positions of [broadcast_ops_lo]). *)
Lemma broadcast_log_clock_lt N (j : ClientId) (q1 q2 : nat) (o1 o2 : Op) :
  history_wf N ->
  (q1 < q2)%nat ->
  broadcast_ops (to_histories N j) !! q1 = Some o1 ->
  broadcast_ops (to_histories N j) !! q2 = Some o2 ->
  (clock (opid o1) < clock (opid o2))%nat.
Proof.
  move=> Hwf Hlt H1 H2.
  destruct (broadcast_ops_lo (to_histories N j) q1 q2 o1 o2 Hlt H1 H2)
    as (l1 & l2 & l3 & Hsp).
  exact (author_earlier_clock N j o1 o2 l1 l2 l3 Hwf Hsp).
Qed.

(* ===== the broadcast step ================================================= *)

(** Appending [EvBroadcast op; EvDeliver op] for a valid, clock-maximal, fresh
    insert into type [t0] preserves [history_wf], advances the coherent state
    by the insert's splice at [t0], and registers the new op. The clock bound
    is doc-global (all types). *)
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
  op_registered (<[c := h ++ tail]> N) (t0, OpInsert input).
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
    + (* fifo (issue #40) *)
      move=> i j.
      have Htl : h ++ tail = (h ++ [EvBroadcast op']) ++ [EvDeliver op']
        by rewrite /tail -app_assoc //.
      have Hboc : broadcast_ops (h ++ tail) = broadcast_ops h ++ [op'].
      { rewrite Htl broadcast_ops_snoc_deliver broadcast_ops_snoc_broadcast //. }
      destruct (decide (i = c)) as [-> | Hnei]; destruct (decide (j = c)) as [-> | Hnej].
      * (* own view of self: saturated on both sides *)
        rewrite to_histories_insert Hboc Htl.
        rewrite (delivered_from_snoc_deliver _ _ _ Hcid') delivered_from_snoc_broadcast.
        have Hsat : delivered_from h c = broadcast_ops h.
        { have := self_delivered_all N c Hwf.
          rewrite (to_histories_lookup N c h Hc) //. }
        rewrite Hsat //.
      * (* i = c, j ≠ c: the appended pair is authored at c *)
        rewrite to_histories_insert (to_histories_insert_ne _ _ _ _ Hnej) Htl.
        rewrite delivered_from_snoc_deliver_ne; last by rewrite Hcid'; congruence.
        rewrite delivered_from_snoc_broadcast.
        have := hwf_fifo N Hwf c j.
        rewrite (to_histories_lookup N c h Hc) //.
      * (* i ≠ c, j = c: the log grows at its end *)
        rewrite (to_histories_insert_ne _ _ _ _ Hnei) to_histories_insert Hboc.
        etrans; last by eexists.
        have := hwf_fifo N Hwf i c.
        rewrite (to_histories_lookup N c h Hc) //.
      * rewrite (to_histories_insert_ne _ _ _ _ Hnei)
                (to_histories_insert_ne _ _ _ _ Hnej).
        exact (hwf_fifo N Hwf i j).
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
    rewrite /op_registered Hcid' to_histories_insert elem_of_app /tail !elem_of_cons.
    right. by left.
Qed.

(* ===== the deliver step =================================================== *)

(** Delivering one broadcast, fresh op whose same-author predecessor (if any)
    is already delivered here preserves [history_wf]. Since issue #40 there is
    NO causal-closure hypothesis: the structural gate's own-predecessor clause
    is exactly what keeps per-author delivery FIFO. *)
Lemma history_wf_deliver N c h op :
  history_wf N -> N !! c = Some h ->
  op_broadcast N op ->
  opid op ∉ delivered_ids h ->
  (∀ k, clock (opid op) = S k ->
     MkYjsId (clientId (opid op)) k ∈ delivered_ids h) ->
  history_wf (<[c := h ++ [EvDeliver op]]> N).
Proof.
  move=> Hwf Hc Hbc0 Hnotdel Hpred.
  have Hbcreg : EvBroadcast op ∈ to_histories N (clientId (opid op)).
  { destruct Hbc0 as (i & Hi).
    rewrite (hwf_client_id N Hwf op i Hi) //. }
  set tail := [EvDeliver op].
  have Hdop_h : EvDeliver op ∉ h.
  { move=> Hin. apply Hnotdel. apply elem_of_delivered_ids. by exists op. }
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
  - (* fifo (issue #40): the gate's own-predecessor clause pins the delivered
       op to the next position of its author's log *)
    move=> i j.
    set j0 := clientId (opid op).
    have Hboc : ∀ j', broadcast_ops (to_histories (<[c := h ++ tail]> N) j')
              = broadcast_ops (to_histories N j').
    { move=> j'. destruct (decide (j' = c)) as [-> | Hne].
      - rewrite to_histories_insert /tail broadcast_ops_snoc_deliver
                (to_histories_lookup N c h Hc) //.
      - rewrite (to_histories_insert_ne _ _ _ _ Hne) //. }
    rewrite Hboc.
    destruct (decide (i = c)) as [-> | Hnei]; last first.
    { rewrite (to_histories_insert_ne _ _ _ _ Hnei). exact (hwf_fifo N Hwf i j). }
    rewrite to_histories_insert /tail.
    destruct (decide (j = j0)) as [-> | Hnej]; last first.
    { rewrite delivered_from_snoc_deliver_ne; last by rewrite -/j0; congruence.
      rewrite -(to_histories_lookup N c h Hc). exact (hwf_fifo N Hwf c j). }
    rewrite (delivered_from_snoc_deliver h op j0) //.
    set log := broadcast_ops (to_histories N j0).
    have Hpre0 : delivered_from h j0 `prefix_of` log.
    { rewrite -(to_histories_lookup N c h Hc). exact (hwf_fifo N Hwf c j0). }
    set L := length (delivered_from h j0).
    have HtakeL : delivered_from h j0 = take L log.
    { destruct Hpre0 as [tl Htl]. rewrite /L Htl take_app_length //. }
    have Hoplog : op ∈ log by apply elem_of_broadcast_ops.
    destruct (list_elem_of_lookup_1 _ _ Hoplog) as (q & Hq).
    have Hnotp : op ∉ delivered_from h j0.
    { move=> Hin. apply Hnotdel. apply elem_of_delivered_ids.
      exists op. split; [| done].
      apply elem_of_delivered_from in Hin. by destruct Hin. }
    have HqgeL : (L <= q)%nat.
    { destruct (decide (L <= q)%nat) as [| Hgt]; [done | exfalso].
      apply Hnotp. rewrite HtakeL. apply elem_of_take. exists q.
      split; [done | lia]. }
    have HqL : q = L.
    { destruct (decide (q = L)) as [| Hne]; [done | exfalso].
      have HL : (L < q)%nat by lia.
      have HlogL : ∃ oL, log !! L = Some oL.
      { apply lookup_lt_is_Some. have := lookup_lt_Some _ _ _ Hq. lia. }
      destruct HlogL as (oL & HoL).
      have Hc2 : (clock (opid oL) < clock (opid op))%nat
        := broadcast_log_clock_lt N j0 L q oL op Hwf HL HoL Hq.
      destruct (clock (opid op)) as [| k] eqn:Hck; first lia.
      have Hpredin : MkYjsId j0 k ∈ delivered_ids h
        by apply (Hpred k); rewrite ?Hck //.
      apply elem_of_delivered_ids in Hpredin.
      destruct Hpredin as (y & Hyh & Hyid).
      have Hyj : clientId (opid y) = j0 by rewrite Hyid //.
      have Hyin : y ∈ delivered_from h j0.
      { apply elem_of_delivered_from. by split. }
      rewrite HtakeL in Hyin. apply elem_of_take in Hyin.
      destruct Hyin as (qy & Hqy & HqyL).
      have Hc1 : (clock (opid y) < clock (opid oL))%nat
        := broadcast_log_clock_lt N j0 qy L y oL Hwf HqyL Hqy HoL.
      rewrite Hyid /= in Hc1. lia. }
    rewrite HtakeL.
    exists (drop (S L) log).
    rewrite -(take_S_r log L op); last by rewrite -HqL.
    rewrite take_drop //.
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

    (Moved here from [yjs_store]: it is pure; the pending machinery below
    produces it for the drained applied list, issue #40.) *)
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

(** The deliver event a decoded, type-tagged input denotes. *)
Definition deliver_ev (ti : TId * IntegrateInput (A := A)) : Ev :=
  EvDeliver (ti.1, OpInsert ti.2).

(* ===== the pending drain (issue #40) ======================================= *)

(** The pure mirror of the total [store.applyUpdate] loop (store.go): the drained set
    is the store's pending buffer plus the incoming batch, each struct tagged
    with its target type. One [pending_pass] is one scan of the pending -- drop the
    structs already integrated (re-deliveries), integrate the structs whose
    structural dependencies have arrived, keep the rest deduplicated by id --
    and [pending_drain] repeats passes until one integrates nothing. The WP proof
    refines the Go loop against these functions step by step; the certificate
    layer characterizes their output ([ValidReplay] on the applied list, the
    fixpoint property on the rest). *)

(** Store-wide id presence in a doc model (the pure mirror of [store.hasNode]:
    the per-client run lists hold every integrated item of every type). *)
Definition docm_has (m : DocM) (i : YjsId) : bool :=
  existsb (λ ta, existsb (λ x, bool_decide (item_id x = i)) ta.2) (map_to_list m).

Lemma docm_has_spec (m : DocM) (i : YjsId) :
  docm_has m i = true <-> ∃ (t : TId) x, x ∈ docm_get m t ∧ item_id x = i.
Proof.
  rewrite /docm_has existsb_exists. split.
  - move=> [[t arr] [Hin Hex]].
    apply existsb_exists in Hex. destruct Hex as (x & Hx & Hid).
    apply bool_decide_eq_true in Hid.
    exists t, x. split; [| exact Hid].
    apply list_elem_of_In in Hin. apply elem_of_map_to_list in Hin.
    rewrite /docm_get Hin //. by apply list_elem_of_In.
  - move=> [t [x [Hx Hid]]].
    rewrite /docm_get in Hx.
    destruct (m !! t) as [arr |] eqn:Hlk; simpl in Hx; last by apply elem_of_nil in Hx.
    exists (t, arr). split.
    + apply list_elem_of_In. by apply elem_of_map_to_list.
    + apply existsb_exists. exists x.
      split; [by apply list_elem_of_In | by apply bool_decide_eq_true].
Qed.

(** The structural dependencies of one decoded struct: both origins plus, for
    clock > 0, the author's preceding id. The predecessor clause is the
    per-client contiguity gate (y-octo: [state.contains]); [store.depsArrived]
    checks exactly these ids by arrival. *)
Definition input_deps (input : IntegrateInput (A := A)) : list YjsId :=
  option_list (in_originId input) ++ option_list (in_rightOriginId input) ++
  match clock (in_id input) with
  | 0%nat => []
  | S k => [MkYjsId (clientId (in_id input)) k]
  end.

Definition input_ready (m : DocM) (input : IntegrateInput (A := A)) : bool :=
  forallb (docm_has m) (input_deps input).

Lemma input_ready_spec (m : DocM) (input : IntegrateInput (A := A)) :
  input_ready m input = true <-> ∀ d : YjsId, d ∈ input_deps input -> docm_has m d = true.
Proof.
  rewrite /input_ready forallb_forall. split.
  - move=> H d Hin. apply H. by apply list_elem_of_In.
  - move=> H d Hin. apply H. by apply list_elem_of_In.
Qed.

(** Keep a struct for the next pass unless an equal id is already kept
    (store.go: [containsUpdateItemId] -- pending re-deliveries drop by id). *)
Definition pending_keep (kept : list (TId * IntegrateInput (A := A)))
    (ti : TId * IntegrateInput (A := A)) : list (TId * IntegrateInput (A := A)) :=
  if existsb (λ tj, bool_decide (in_id tj.2 = in_id ti.2)) kept
  then kept
  else kept ++ [ti].

(** One pass over the pending, mirroring one iteration of the Go outer loop:
    [pending_pass m pending kept = (applied, kept', m')] where [applied] lists the
    structs integrated this pass in application order, [m'] is the doc model
    after them, and [kept'] extends [kept] with the structs queued for the
    next pass. A ready struct whose pure [integrate] fails is kept; the
    certificate layer proves this branch dead (a ready certified struct
    always integrates), and the heap-level loop is only ever related to
    passes where it is dead. *)
Fixpoint pending_pass (m : DocM) (pending kept : list (TId * IntegrateInput (A := A)))
    : list (TId * IntegrateInput (A := A)) * list (TId * IntegrateInput (A := A)) * DocM :=
  match pending with
  | [] => ([], kept, m)
  | ti :: tl =>
      if docm_has m (in_id ti.2) then pending_pass m tl kept
      else if input_ready m ti.2 then
        match integrate ti.2 (docm_get m ti.1) with
        | Some arr' =>
            let '(app, kept', m') := pending_pass (<[ti.1 := arr']> m) tl kept in
            (ti :: app, kept', m')
        | None => pending_pass m tl (pending_keep kept ti)
        end
      else pending_pass m tl (pending_keep kept ti)
  end.

Fixpoint pending_drain_aux (fuel : nat) (m : DocM)
    (pending : list (TId * IntegrateInput (A := A)))
    : list (TId * IntegrateInput (A := A)) * list (TId * IntegrateInput (A := A)) * DocM :=
  match fuel with
  | 0%nat => ([], pending, m)
  | S f =>
      let '(app, kept, m') := pending_pass m pending [] in
      match app with
      | [] => ([], kept, m')
      | _ :: _ =>
          let '(app2, rest, m'') := pending_drain_aux f m' kept in
          (app ++ app2, rest, m'')
      end
  end.

(** Drain to the fixpoint (store.go applyUpdate: passes repeat until one
    integrates nothing). A progressing pass strictly shrinks the pending
    ([pending_pass_kept_lt]), so [length pending] passes always suffice and the
    fuel is irrelevant beyond that ([pending_drain_aux_fuel_ge]). *)
Definition pending_drain (m : DocM) (pending : list (TId * IntegrateInput (A := A)))
    : list (TId * IntegrateInput (A := A)) * list (TId * IntegrateInput (A := A)) * DocM :=
  pending_drain_aux (S (length pending)) m pending.

(* ----- pass structure ----- *)

Lemma pending_keep_length kept ti :
  (length (pending_keep kept ti) <= S (length kept))%nat.
Proof.
  rewrite /pending_keep. destruct (existsb _ kept); [lia | rewrite length_app /=; lia].
Qed.

Lemma pending_keep_prefix kept ti : kept `prefix_of` pending_keep kept ti.
Proof.
  rewrite /pending_keep. destruct (existsb _ kept); [done | by eexists].
Qed.

(** The kept list grows from [kept] by at most the non-applied pending
    elements. *)
Lemma pending_pass_kept_le (pending : list (TId * IntegrateInput (A := A))) :
  ∀ m kept app kept' m',
    pending_pass m pending kept = (app, kept', m') ->
    (length kept' + length app <= length kept + length pending)%nat.
Proof.
  elim: pending => [| ti tl IH] m kept app kept' m' /=.
  - move=> [= <- <- _] /=. lia.
  - destruct (docm_has m (in_id ti.2)).
    { move=> /IH. lia. }
    destruct (input_ready m ti.2); last first.
    { move=> /IH. move: (pending_keep_length kept ti). lia. }
    destruct (integrate ti.2 (docm_get m ti.1)) as [arr' |]; last first.
    { move=> /IH. move: (pending_keep_length kept ti). lia. }
    destruct (pending_pass (<[ti.1 := arr']> m) tl kept) as [[app0 kept0] m0] eqn:Hrec.
    move=> [= <- <- _] /=.
    move: (IH _ _ _ _ _ Hrec). lia.
Qed.

(** A progressing pass (from an empty kept accumulator) strictly shrinks. *)
Lemma pending_pass_kept_lt (pending app kept' : list (TId * IntegrateInput (A := A)))
    (m m' : DocM) :
  pending_pass m pending [] = (app, kept', m') ->
  app ≠ [] ->
  (length kept' < length pending)%nat.
Proof.
  move=> Hpass Hne.
  move: (pending_pass_kept_le pending m [] app kept' m' Hpass) => /=.
  destruct app; [done | simpl; lia].
Qed.

Lemma pending_pass_kept_prefix (pending : list (TId * IntegrateInput (A := A))) :
  ∀ m kept app kept' m',
    pending_pass m pending kept = (app, kept', m') ->
    kept `prefix_of` kept'.
Proof.
  elim: pending => [| ti tl IH] m kept app kept' m' /=.
  - move=> [= _ <- _] //.
  - destruct (docm_has m (in_id ti.2)).
    { move=> /IH //. }
    destruct (input_ready m ti.2); last first.
    { move=> /IH Hpre. etrans; [apply pending_keep_prefix | exact Hpre]. }
    destruct (integrate ti.2 (docm_get m ti.1)) as [arr' |]; last first.
    { move=> /IH Hpre. etrans; [apply pending_keep_prefix | exact Hpre]. }
    destruct (pending_pass (<[ti.1 := arr']> m) tl kept) as [[app0 kept0] m0] eqn:Hrec.
    move=> [= _ <- _]. exact (IH _ _ _ _ _ Hrec).
Qed.

(* ----- fuel irrelevance ----- *)

Lemma pending_drain_aux_fuel_agree (f1 : nat) :
  ∀ (f2 : nat) (m : DocM) (pending : list (TId * IntegrateInput (A := A))),
    (length pending < f1)%nat -> (length pending < f2)%nat ->
    pending_drain_aux f1 m pending = pending_drain_aux f2 m pending.
Proof.
  elim: f1 => [| f1 IH] f2 m pending Hlt1 Hlt2; first lia.
  destruct f2 as [| f2]; first lia.
  simpl.
  destruct (pending_pass m pending []) as [[app kept] m'] eqn:Hpass.
  destruct app as [| a app0]; first done.
  have Hklt : (length kept < length pending)%nat
    by exact (pending_pass_kept_lt pending (a :: app0) kept m m' Hpass ltac:(done)).
  rewrite (IH f2 m' kept ltac:(lia) ltac:(lia)) //.
Qed.

Lemma pending_drain_aux_fuel_ge (fuel : nat) (m : DocM)
    (pending : list (TId * IntegrateInput (A := A))) :
  (length pending < fuel)%nat ->
  pending_drain_aux fuel m pending = pending_drain_aux (S (length pending)) m pending.
Proof.
  move=> Hlt. exact (pending_drain_aux_fuel_agree fuel (S (length pending)) m pending Hlt ltac:(lia)).
Qed.

(** The one-pass unfolding of [pending_drain] (the Go outer loop consumes exactly
    one pass per iteration; the WP loop invariant steps with this equation). *)
Lemma pending_drain_unfold (m : DocM) (pending : list (TId * IntegrateInput (A := A))) :
  pending_drain m pending =
    let '(app, kept, m') := pending_pass m pending [] in
    match app with
    | [] => ([], kept, m')
    | _ :: _ =>
        let '(app2, rest, m'') := pending_drain m' kept in (app ++ app2, rest, m'')
    end.
Proof.
  rewrite {1}/pending_drain /=.
  destruct (pending_pass m pending []) as [[app kept] m'] eqn:Hpass.
  destruct app as [| a app0]; first done.
  have Hklt : (length kept < length pending)%nat
    by exact (pending_pass_kept_lt pending (a :: app0) kept m m' Hpass ltac:(done)).
  rewrite (pending_drain_aux_fuel_ge (length pending) m' kept Hklt) //.
Qed.

(* ----- the replay view of a pass / drain ----- *)

(** The applied list of a pass, as a step-indexed replay: each applied struct
    was fresh (not yet integrated) and ready at its application point, and the
    pure [integrate] advanced its type's list. This is [ValidReplay] minus the
    validity facts ([toItem] / [IsItemValid] / clock maximality), which the
    certificate layer supplies on top. *)
Inductive PendingReplay : DocM -> list (TId * IntegrateInput (A := A)) -> DocM -> Prop :=
  | PendingReplay_nil m : PendingReplay m [] m
  | PendingReplay_cons m ti arr' rest m' :
      docm_has m (in_id ti.2) = false ->
      input_ready m ti.2 = true ->
      integrate ti.2 (docm_get m ti.1) = Some arr' ->
      PendingReplay (<[ti.1 := arr']> m) rest m' ->
      PendingReplay m (ti :: rest) m'.

Lemma PendingReplay_app (m m1 m2 : DocM)
    (a1 a2 : list (TId * IntegrateInput (A := A))) :
  PendingReplay m a1 m1 -> PendingReplay m1 a2 m2 -> PendingReplay m (a1 ++ a2) m2.
Proof.
  move=> H1. elim: H1 a2 m2 => [m0 | m0 ti arr' rest m0' Hdup Hready Hint Hrest IH] a2 m2 H2 /=.
  - exact H2.
  - apply (PendingReplay_cons m0 ti arr' (rest ++ a2) m2 Hdup Hready Hint).
    exact (IH a2 m2 H2).
Qed.

Lemma pending_pass_replay (pending : list (TId * IntegrateInput (A := A))) :
  ∀ m kept app kept' m',
    pending_pass m pending kept = (app, kept', m') ->
    PendingReplay m app m'.
Proof.
  elim: pending => [| ti tl IH] m kept app kept' m' /=.
  - move=> [= <- _ <-]. constructor.
  - destruct (docm_has m (in_id ti.2)) eqn:Hdup.
    { move=> /IH //. }
    destruct (input_ready m ti.2) eqn:Hready; last first.
    { move=> /IH //. }
    destruct (integrate ti.2 (docm_get m ti.1)) as [arr' |] eqn:Hint; last first.
    { move=> /IH //. }
    destruct (pending_pass (<[ti.1 := arr']> m) tl kept) as [[app0 kept0] m0] eqn:Hrec.
    move=> [= <- _ <-].
    exact (PendingReplay_cons m ti arr' app0 m0 Hdup Hready Hint (IH _ _ _ _ _ Hrec)).
Qed.

(** A pass that applies nothing leaves the model unchanged. *)
Lemma pending_pass_no_progress (pending : list (TId * IntegrateInput (A := A))) :
  ∀ m kept kept' m',
    pending_pass m pending kept = ([], kept', m') ->
    m' = m.
Proof.
  elim: pending => [| ti tl IH] m kept kept' m' /=.
  - move=> [= _ <-] //.
  - destruct (docm_has m (in_id ti.2)).
    { move=> /IH //. }
    destruct (input_ready m ti.2); last first.
    { move=> /IH //. }
    destruct (integrate ti.2 (docm_get m ti.1)) as [arr' |]; last first.
    { move=> /IH //. }
    destruct (pending_pass (<[ti.1 := arr']> m) tl kept) as [[app0 kept0] m0] eqn:Hrec.
    move=> [= Happ _ _]. discriminate.
Qed.

Lemma pending_drain_aux_replay (fuel : nat) :
  ∀ (m : DocM) (pending app rest : list (TId * IntegrateInput (A := A))) (m' : DocM),
    pending_drain_aux fuel m pending = (app, rest, m') ->
    PendingReplay m app m'.
Proof.
  elim: fuel => [| f IH] m pending app rest m' /=.
  - move=> [= <- _ <-]. constructor.
  - destruct (pending_pass m pending []) as [[app0 kept] m0] eqn:Hpass.
    destruct app0 as [| a app0'].
    { move=> [= <- _ <-].
      rewrite (pending_pass_no_progress pending m [] kept m0 Hpass). constructor. }
    destruct (pending_drain_aux f m0 kept) as [[app2 rest2] m2] eqn:Hrec.
    move=> [= <- _ <-].
    exact (PendingReplay_app _ _ _ _ _ (pending_pass_replay pending m [] _ _ _ Hpass)
             (IH _ _ _ _ _ Hrec)).
Qed.

Lemma pending_drain_replay (m : DocM)
    (pending app rest : list (TId * IntegrateInput (A := A))) (m' : DocM) :
  pending_drain m pending = (app, rest, m') ->
  PendingReplay m app m'.
Proof. apply pending_drain_aux_replay. Qed.

(* ----- monotonicity: integrated structs stay integrated ----- *)

Lemma docm_has_integrate_mono (m : DocM) (t : TId) (input : IntegrateInput (A := A))
    (arr' : list (YjsItem A)) (d : YjsId) :
  integrate input (docm_get m t) = Some arr' ->
  docm_has m d = true ->
  docm_has (<[t := arr']> m) d = true.
Proof.
  move=> Hint /docm_has_spec [t0 [x [Hx Hid]]].
  apply docm_has_spec.
  destruct (decide (t0 = t)) as [-> | Hne].
  - exists t, (x). rewrite docm_get_insert_eq.
    split; [| exact Hid].
    exact (integrate_preserves_mem input (docm_get m t) arr' Hint x Hx).
  - exists t0, x. rewrite docm_get_insert_ne //.
Qed.

Lemma PendingReplay_docm_has_mono (m m' : DocM)
    (app : list (TId * IntegrateInput (A := A))) (d : YjsId) :
  PendingReplay m app m' ->
  docm_has m d = true ->
  docm_has m' d = true.
Proof.
  move=> H. elim: H => [m0 | m0 ti arr' rest m0' Hdup Hready Hint Hrest IH] Hd; first exact Hd.
  apply IH. exact (docm_has_integrate_mono m0 ti.1 ti.2 arr' d Hint Hd).
Qed.

(** An applied struct is integrated from its application point on. *)
Lemma PendingReplay_applied_present (m m' : DocM)
    (app : list (TId * IntegrateInput (A := A))) :
  PendingReplay m app m' ->
  ∀ ti, ti ∈ app -> docm_has m' (in_id ti.2) = true.
Proof.
  move=> H. elim: H => [m0 | m0 ti0 arr' rest m0' Hdup Hready Hint Hrest IH] ti Hin.
  - by apply elem_of_nil in Hin.
  - apply elem_of_cons in Hin. destruct Hin as [-> | Hin]; last exact (IH ti Hin).
    apply (PendingReplay_docm_has_mono _ _ _ _ Hrest).
    apply docm_has_spec.
    destruct (integrate_new_mem ti0.2 (docm_get m0 ti0.1) arr' Hint) as (it & Hitid & Hitmem).
    exists ti0.1, it. rewrite docm_get_insert_eq. by split.
Qed.

(** Applied ids are pairwise distinct (freshness at each step plus
    monotonicity), the pure dedup fact behind [IdNoDup] downstream. *)
Lemma PendingReplay_ids_nodup (m m' : DocM)
    (app : list (TId * IntegrateInput (A := A))) :
  PendingReplay m app m' ->
  NoDup ((λ ti, in_id ti.2) <$> app).
Proof.
  move=> H. elim: H => [m0 | m0 ti arr' rest m0' Hdup Hready Hint Hrest IH] /=; first constructor.
  apply NoDup_cons_2; last exact IH.
  rewrite list_elem_of_fmap. move=> [tj [Hideq Hj]].
  have Hpres : docm_has (<[ti.1 := arr']> m0) (in_id ti.2) = true.
  { apply docm_has_spec.
    destruct (integrate_new_mem ti.2 (docm_get m0 ti.1) arr' Hint) as (it & Hitid & Hitmem).
    exists ti.1, it. rewrite docm_get_insert_eq. by split. }
  (* the later application point still has [in_id ti.2] integrated, yet [tj]
     was fresh there: walk the tail replay to [tj]'s point *)
  clear IH. move: Hpres. rewrite Hideq. clear Hideq.
  elim: Hrest Hj => [m1 | m1 tk arr1 rest1 m1' Hdup1 Hready1 Hint1 Hrest1 IH1] Hj Hpres.
  - by apply elem_of_nil in Hj.
  - apply elem_of_cons in Hj. destruct Hj as [-> | Hj].
    + rewrite Hpres in Hdup1. discriminate.
    + apply (IH1 Hj).
      exact (docm_has_integrate_mono m1 tk.1 tk.2 arr1 _ Hint1 Hpres).
Qed.

(* ----- the fixpoint property of the drained rest ----- *)

(** A struct the drain leaves pending is genuinely blocked in the final model:
    not integrated, and either a dependency is still missing or (for
    uncertified pendings) its [integrate] fails. *)
Definition pending_blocked (m : DocM) (ti : TId * IntegrateInput (A := A)) : Prop :=
  docm_has m (in_id ti.2) = false ∧
  (input_ready m ti.2 = false ∨ integrate ti.2 (docm_get m ti.1) = None).

Lemma pending_pass_kept_blocked (pending : list (TId * IntegrateInput (A := A))) :
  ∀ m kept kept' m',
    pending_pass m pending kept = ([], kept', m') ->
    ∀ ti, ti ∈ kept' -> ti ∈ kept ∨ pending_blocked m ti.
Proof.
  elim: pending => [| ti0 tl IH] m kept kept' m' /=.
  - move=> [= <- _] ti Hin. by left.
  - destruct (docm_has m (in_id ti0.2)) eqn:Hdup.
    { move=> /IH //. }
    destruct (input_ready m ti0.2) eqn:Hready; last first.
    { move=> Hpass ti Hin.
      destruct (IH _ _ _ _ Hpass ti Hin) as [Hkept | Hblocked]; last by right.
      move: Hkept. rewrite /pending_keep.
      destruct (existsb _ kept); first by left.
      rewrite elem_of_app list_elem_of_singleton. move=> [Hk | ->]; first by left.
      right. split; [exact Hdup | by left]. }
    destruct (integrate ti0.2 (docm_get m ti0.1)) as [arr' |] eqn:Hint; last first.
    { move=> Hpass ti Hin.
      destruct (IH _ _ _ _ Hpass ti Hin) as [Hkept | Hblocked]; last by right.
      move: Hkept. rewrite /pending_keep.
      destruct (existsb _ kept); first by left.
      rewrite elem_of_app list_elem_of_singleton. move=> [Hk | ->]; first by left.
      right. split; [exact Hdup | by right]. }
    destruct (pending_pass (<[ti0.1 := arr']> m) tl kept) as [[app0 kept0] m0] eqn:Hrec.
    move=> [= Happ _ _]. discriminate.
Qed.

Lemma pending_drain_aux_rest_blocked (fuel : nat) :
  ∀ (m : DocM) (pending app rest : list (TId * IntegrateInput (A := A))) (m' : DocM),
    (length pending < fuel)%nat ->
    pending_drain_aux fuel m pending = (app, rest, m') ->
    ∀ ti, ti ∈ rest -> pending_blocked m' ti.
Proof.
  elim: fuel => [| f IH] m pending app rest m' Hfuel /=; first lia.
  destruct (pending_pass m pending []) as [[app0 kept] m0] eqn:Hpass.
  destruct app0 as [| a app0'].
  - move=> [= _ <- <-] ti Hin.
    have Hm : m0 = m := pending_pass_no_progress pending m [] kept m0 Hpass.
    destruct (pending_pass_kept_blocked pending m [] kept m0 Hpass ti Hin) as [Hk | Hb].
    + by apply elem_of_nil in Hk.
    + rewrite Hm //.
  - destruct (pending_drain_aux f m0 kept) as [[app2 rest2] m2] eqn:Hrec.
    move=> [= _ <- <-].
    have Hklt : (length kept < length pending)%nat
      by exact (pending_pass_kept_lt pending (a :: app0') kept m m0 Hpass ltac:(done)).
    exact (IH m0 kept app2 rest2 m2 ltac:(lia) Hrec).
Qed.

Lemma pending_drain_rest_blocked (m : DocM)
    (pending app rest : list (TId * IntegrateInput (A := A))) (m' : DocM) :
  pending_drain m pending = (app, rest, m') ->
  ∀ ti, ti ∈ rest -> pending_blocked m' ti.
Proof.
  apply pending_drain_aux_rest_blocked. lia.
Qed.

(* ----- provenance: everything applied/kept comes from the pending ----- *)

Lemma pending_keep_subset kept ti tj :
  tj ∈ pending_keep kept ti -> tj ∈ kept ∨ tj = ti.
Proof.
  rewrite /pending_keep. destruct (existsb _ kept); first by left.
  rewrite elem_of_app list_elem_of_singleton. move=> [Hk | ->]; [by left | by right].
Qed.

Lemma pending_pass_subset (pending : list (TId * IntegrateInput (A := A))) :
  ∀ m kept app kept' m',
    pending_pass m pending kept = (app, kept', m') ->
    (∀ ti, ti ∈ app -> ti ∈ pending) ∧
    (∀ ti, ti ∈ kept' -> ti ∈ kept ∨ ti ∈ pending).
Proof.
  elim: pending => [| ti0 tl IH] m kept app kept' m' /=.
  - move=> [= <- <- _]. split; [move=> ti Hin; by apply elem_of_nil in Hin |].
    move=> ti Hin. by left.
  - destruct (docm_has m (in_id ti0.2)).
    { move=> /IH [Happ Hkept]. split.
      - move=> ti Hin. apply elem_of_cons. right. exact (Happ ti Hin).
      - move=> ti Hin. destruct (Hkept ti Hin) as [Hk | Hp]; [by left |].
        right. apply elem_of_cons. by right. }
    destruct (input_ready m ti0.2); last first.
    { move=> /IH [Happ Hkept]. split.
      - move=> ti Hin. apply elem_of_cons. right. exact (Happ ti Hin).
      - move=> ti Hin. destruct (Hkept ti Hin) as [Hk | Hp].
        + destruct (pending_keep_subset kept ti0 ti Hk) as [Hk' | ->]; [by left |].
          right. apply elem_of_cons. by left.
        + right. apply elem_of_cons. by right. }
    destruct (integrate ti0.2 (docm_get m ti0.1)) as [arr' |]; last first.
    { move=> /IH [Happ Hkept]. split.
      - move=> ti Hin. apply elem_of_cons. right. exact (Happ ti Hin).
      - move=> ti Hin. destruct (Hkept ti Hin) as [Hk | Hp].
        + destruct (pending_keep_subset kept ti0 ti Hk) as [Hk' | ->]; [by left |].
          right. apply elem_of_cons. by left.
        + right. apply elem_of_cons. by right. }
    destruct (pending_pass (<[ti0.1 := arr']> m) tl kept) as [[app0 kept0] m0] eqn:Hrec.
    move=> [= <- <- _].
    destruct (IH _ _ _ _ _ Hrec) as [Happ Hkept]. split.
    + move=> ti Hin. apply elem_of_cons in Hin.
      destruct Hin as [-> | Hin]; [by left | right; exact (Happ ti Hin)].
    + move=> ti Hin. destruct (Hkept ti Hin) as [Hk | Hp]; [by left |].
      right. apply elem_of_cons. by right.
Qed.

Lemma pending_drain_aux_subset (fuel : nat) :
  ∀ (m : DocM) (pending app rest : list (TId * IntegrateInput (A := A))) (m' : DocM),
    pending_drain_aux fuel m pending = (app, rest, m') ->
    (∀ ti, ti ∈ app -> ti ∈ pending) ∧ (∀ ti, ti ∈ rest -> ti ∈ pending).
Proof.
  elim: fuel => [| f IH] m pending app rest m' /=.
  - move=> [= <- <- _]. split; [move=> ti Hin; by apply elem_of_nil in Hin | done].
  - destruct (pending_pass m pending []) as [[app0 kept] m0] eqn:Hpass.
    destruct (pending_pass_subset pending m [] app0 kept m0 Hpass) as [Happ0 Hkept0].
    have Hkept0' : ∀ ti, ti ∈ kept -> ti ∈ pending.
    { move=> ti Hin. destruct (Hkept0 ti Hin) as [Hk | Hp]; [by apply elem_of_nil in Hk | done]. }
    destruct app0 as [| a app0'].
    { move=> [= <- <- _]. split; [move=> ti Hin; by apply elem_of_nil in Hin | done]. }
    destruct (pending_drain_aux f m0 kept) as [[app2 rest2] m2] eqn:Hrec.
    move=> [= <- <- _].
    destruct (IH _ _ _ _ _ Hrec) as [Happ2 Hrest2]. split.
    + move=> ti Hin.
      apply elem_of_cons in Hin. destruct Hin as [-> | Hin].
      * apply (Happ0 a). apply elem_of_cons. by left.
      * apply elem_of_app in Hin. destruct Hin as [Hin | Hin].
        -- apply (Happ0 ti). apply elem_of_cons. by right.
        -- exact (Hkept0' ti (Happ2 ti Hin)).
    + move=> ti Hin. exact (Hkept0' ti (Hrest2 ti Hin)).
Qed.

Lemma pending_drain_subset (m : DocM)
    (pending app rest : list (TId * IntegrateInput (A := A))) (m' : DocM) :
  pending_drain m pending = (app, rest, m') ->
  (∀ ti, ti ∈ app -> ti ∈ pending) ∧ (∀ ti, ti ∈ rest -> ti ∈ pending).
Proof. apply pending_drain_aux_subset. Qed.
(* ===== gate arithmetic and integrate totality (issue #40) ================= *)

(** Pure: one failing dependency falsifies the gate. *)
Lemma input_ready_false_of_dep (m : DocM) (input : IntegrateInput (A := A)) (d : YjsId) :
  d ∈ input_deps input -> docm_has m d = false -> input_ready m input = false.
Proof.
  move=> Hd Hf.
  destruct (input_ready m input) eqn:Hr; [| done].
  have Habs := proj1 (input_ready_spec m input) Hr d Hd.
  by rewrite Habs in Hf.
Qed.

(** Pure: the three arrival checks exhaust the dependency list. *)
Lemma input_ready_true_of (m : DocM) (input : IntegrateInput (A := A)) :
  (∀ oid, in_originId input = Some oid -> docm_has m oid = true) ->
  (∀ oid, in_rightOriginId input = Some oid -> docm_has m oid = true) ->
  (∀ k, clock (in_id input) = S k ->
     docm_has m (MkYjsId (clientId (in_id input)) k) = true) ->
  input_ready m input = true.
Proof.
  move=> HL HR HP.
  apply input_ready_spec. move=> d.
  rewrite /input_deps !elem_of_app. move=> [Hd | [Hd | Hd]].
  - destruct (in_originId input) as [oid |] eqn:HoL; simpl in Hd;
      [| by apply elem_of_nil in Hd].
    apply list_elem_of_singleton in Hd. subst d. exact (HL oid eq_refl).
  - destruct (in_rightOriginId input) as [oid |] eqn:HoR; simpl in Hd;
      [| by apply elem_of_nil in Hd].
    apply list_elem_of_singleton in Hd. subst d. exact (HR oid eq_refl).
  - destruct (clock (in_id input)) as [| k] eqn:Hck; simpl in Hd;
      [by apply elem_of_nil in Hd |].
    apply list_elem_of_singleton in Hd. subst d. exact (HP k eq_refl).
Qed.

(** Membership shortcuts into [input_deps]. *)
Lemma input_deps_originL (input : IntegrateInput (A := A)) (oid : YjsId) :
  in_originId input = Some oid -> oid ∈ input_deps input.
Proof.
  move=> H. rewrite /input_deps !elem_of_app H. left.
  apply list_elem_of_singleton. done.
Qed.
Lemma input_deps_originR (input : IntegrateInput (A := A)) (oid : YjsId) :
  in_rightOriginId input = Some oid -> oid ∈ input_deps input.
Proof.
  move=> H. rewrite /input_deps !elem_of_app H. right. left.
  apply list_elem_of_singleton. done.
Qed.
Lemma input_deps_pred (input : IntegrateInput (A := A)) (k : nat) :
  clock (in_id input) = S k ->
  MkYjsId (clientId (in_id input)) k ∈ input_deps input.
Proof.
  move=> H. rewrite /input_deps !elem_of_app H. right. right.
  apply list_elem_of_singleton. done.
Qed.


(** The set-based scan is total on an in-bounds window: its only bind is the
    array lookup. *)
Lemma setfii_loop_some (count : nat) :
  ∀ (offset : nat) (leftIdx rightIdx : Z) (oLeftId oRightId : option YjsId)
    (newId : YjsId) (arr : list (YjsItem A)) (ibo ci : gset YjsId) (destIdx : Z),
  (1 <= offset)%nat ->
  (Z.of_nat offset + Z.of_nat count <= rightIdx - leftIdx)%Z ->
  (-1 <= leftIdx)%Z ->
  (rightIdx <= Z.of_nat (length arr))%Z ->
  is_Some (setfii_loop count offset leftIdx rightIdx oLeftId oRightId newId arr ibo ci destIdx).
Proof.
  elim: count => [| count IH] offset leftIdx rightIdx oLeftId oRightId newId arr ibo ci destIdx
    Hoff Hwin HleftIdx Hright; first by eexists.
  simpl.
  have Hi : (Z.to_nat (leftIdx + Z.of_nat offset) < length arr)%nat by lia.
  destruct (arr !! Z.to_nat (leftIdx + Z.of_nat offset)) as [other |] eqn:Hother;
    last by (apply lookup_ge_None in Hother; lia).
  simpl.
  destruct (decide (origin_id (origin other) = oLeftId)).
  - destruct (decide (clientId (item_id other) < clientId newId)%nat).
    + apply IH; lia.
    + destruct (decide (origin_id (rightOrigin other) = oRightId)); first by eexists.
      apply IH; lia.
  - destruct (origin_id (origin other)) as [col |]; last by eexists.
    destruct (decide (col ∈ ({[item_id other]} ∪ ibo))); last by eexists.
    destruct (decide (col ∉ ({[item_id other]} ∪ ci))); apply IH; lia.
Qed.

(** [setintegrate] is total once [toItem] resolves: both finds succeed at
    in-range indices, the scan window is in bounds, and the boundary pointers
    exist. *)
Lemma setintegrate_some_of_toItem (input : IntegrateInput (A := A))
    (arr : list (YjsItem A)) (it : YjsItem A) :
  toItem input arr = Some it ->
  is_Some (setintegrate input arr).
Proof.
  move=> Htoit.
  pose proof (proj1 (toItem_ok_iff input arr it) Htoit)
    as (o & r & id & c & Hdef & HoL & HoR & Hid & Hct).
  (* the left find *)
  have HfindL : ∃ leftIdx, findLeftIdx (in_originId input) arr = Some leftIdx ∧
      (-1 <= leftIdx)%Z ∧ (leftIdx < Z.of_nat (length arr))%Z.
  { move: HoL. rewrite /isLeftIdPtr /findLeftIdx.
    destruct (in_originId input) as [oid |].
    - move=> [oit [Hoeq Hfo]].
      move: Hfo. rewrite /find_by_id.
      destruct (list_find (λ item, item_id item = oid) arr) as [[i y] |] eqn:Hlf;
        simpl; last done.
      move=> _.
      apply list_find_Some in Hlf. destruct Hlf as (Hlk & _ & _).
      eexists. split; [done |].
      have := lookup_lt_Some _ _ _ Hlk. lia.
    - move=> _. eexists. split; [done | lia]. }
  (* the right find *)
  have HfindR : ∃ rightIdx, findRightIdx (in_rightOriginId input) arr = Some rightIdx ∧
      (-1 <= rightIdx)%Z ∧ (rightIdx <= Z.of_nat (length arr))%Z.
  { move: HoR. rewrite /isRightIdPtr /findRightIdx.
    destruct (in_rightOriginId input) as [rid |].
    - move=> [rit [Hreq Hfr]].
      move: Hfr. rewrite /find_by_id.
      destruct (list_find (λ item, item_id item = rid) arr) as [[i y] |] eqn:Hlf;
        simpl; last done.
      move=> _.
      apply list_find_Some in Hlf. destruct Hlf as (Hlk & _ & _).
      eexists. split; [done |].
      have := lookup_lt_Some _ _ _ Hlk. lia.
    - move=> _. eexists. split; [done | lia]. }
  destruct HfindL as (leftIdx & HL & HLlo & HLhi).
  destruct HfindR as (rightIdx & HR & HRlo & HRhi).
  rewrite /setintegrate HL /= HR /=.
  (* the scan *)
  have Hscan : is_Some (setfindIntegratedIndex leftIdx rightIdx input arr).
  { rewrite /setfindIntegratedIndex.
    destruct (decide (Z.to_nat (rightIdx - leftIdx) - 1 = 0)%nat) as [-> |].
    { by eexists. }
    have Hs := setfii_loop_some (Z.to_nat (rightIdx - leftIdx) - 1) 1 leftIdx rightIdx
                 (in_originId input) (in_rightOriginId input) (in_id input) arr ∅ ∅
                 (leftIdx + 1) ltac:(lia) ltac:(lia) HLlo HRhi.
    destruct Hs as [d Hd]. rewrite Hd. by eexists. }
  destruct Hscan as [d Hd]. rewrite Hd /=.
  (* the boundary pointers *)
  have Hgpe : ∀ idx : Z, (-1 <= idx)%Z -> (idx <= Z.of_nat (length arr))%Z ->
      is_Some (getPtrExcept arr idx).
  { move=> idx H1 H2. rewrite /getPtrExcept.
    destruct (decide (idx = -1)%Z); first by eexists.
    destruct (decide (idx = Z.of_nat (length arr))%Z); first by eexists.
    have Hlk : (Z.to_nat idx < length arr)%nat by lia.
    destruct (arr !! Z.to_nat idx) eqn:Hl2;
      last by (apply lookup_ge_None in Hl2; lia).
    simpl. by eexists. }
  have Hmk : is_Some (mkItemByIndex leftIdx rightIdx input arr).
  { rewrite /mkItemByIndex.
    destruct (Hgpe leftIdx HLlo ltac:(lia)) as [pl Hpl]. rewrite Hpl /=.
    destruct (Hgpe rightIdx HRlo HRhi) as [pr Hpr]. rewrite Hpr /=. by eexists. }
  destruct Hmk as [itm Hitm]. rewrite Hitm /=. by eexists.
Qed.

(** [integrate] is total on valid, clock-maximal resolutions ([setintegrate]'s
    totality through the loop-equivalence theorem). *)
Lemma integrate_some_of_toItem (input : IntegrateInput (A := A))
    (arr : list (YjsItem A)) (it : YjsItem A) :
  YjsArrInvariant arr ->
  toItem input arr = Some it ->
  IsItemValid it ->
  maximalId it arr ->
  is_Some (integrate input arr).
Proof.
  move=> Hinv Htoit Hvld Hmax.
  have := setintegrate_some_of_toItem input arr it Htoit.
  rewrite (setintegrate_eq_integrate input arr it Hinv Htoit Hvld Hmax) //.
Qed.

(** The document invariants survive a valid replay. *)
Lemma ValidReplay_arrinv (pre : list (TId * IntegrateInput (A := A))) (m mx : DocM) :
  ValidReplay pre m mx ->
  (∀ t : TId, YjsArrInvariant (docm_get m t)) ->
  (∀ t : TId, YjsArrInvariant (docm_get mx t)).
Proof.
  elim => [m0 | t0 input rest m0 arr2 m0' nit Htoit Hvld Hmax Hglob Hint Hvr IH] Hinvs t;
    first exact (Hinvs t).
  apply IH. move=> t'.
  destruct (decide (t' = t0)) as [-> | Hne].
  - rewrite docm_get_insert_eq.
    destruct (YjsArrInvariant_integrate input (docm_get m0 t0) arr2 nit
                (Hinvs t0) Htoit Hvld Hmax Hint) as (i & _ & _ & Hinv2).
    exact Hinv2.
  - rewrite docm_get_insert_ne //.
Qed.

(** [pending_ready_total]: along the drain, a fresh, ready pending struct always
    integrates (the pure exclusion of the ready-but-stuck branch, which the
    heap loop's refinement needs: Go integrates whenever the gate passes). *)
Definition pending_ready_total (m : DocM)
    (pending applied : list (TId * IntegrateInput (A := A))) : Prop :=
  ∀ pre suf mx (ti : TId * IntegrateInput (A := A)),
    applied = pre ++ suf -> PendingReplay m pre mx ->
    ti ∈ pending ->
    docm_has mx (in_id ti.2) = false ->
    input_ready mx ti.2 = true ->
    is_Some (integrate ti.2 (docm_get mx ti.1)).

(* ===== validity transport along structural dependencies (issue #40) ======= *)

(** The raw port of the upstream [item_determinism]: across any two replays of
    operations from one id-unique universe [B], the item carrying a given id is
    the same. Identical to the upstream proof, with the network's
    [msg_id_unique] abstracted into [Huniq] so it applies to the relaxed
    (causal-delivery-free) histories. *)
Lemma item_determinism_raw (B : @YjsOperation A -> Prop)
    (Huniq : ∀ x y, B x -> B y -> yopid x = yopid y -> x = y)
    (it1 it2 : YjsItem A) (ops1 ops2 : list (@YjsOperation A))
    (s1 s2 : YjsState A) (oid : YjsId) :
  (∀ x, x ∈ ops1 -> B x) ->
  (∀ x, x ∈ ops2 -> B x) ->
  effect_list Oy ops1 (op_init Oy) s1 ->
  effect_list Oy ops2 (op_init Oy) s2 ->
  find_by_id oid (st_items s1) = Some it1 ->
  find_by_id oid (st_items s2) = Some it2 ->
  it1 = it2.
Proof.
  remember (YjsItem_size it1) as n eqn:Hn.
  move: it1 it2 ops1 ops2 s1 s2 oid Hn.
  elim/nat_strong_ind: n => n IH it1 it2 ops1 ops2 s1 s2 oid
    Hsize Hsrc1 Hsrc2 Heff1 Heff2 Hf1 Hf2.
  have Hmem1 := @find_by_id_mem _ EqDA oid (st_items s1) it1 Hf1.
  have Hmem2 := @find_by_id_mem _ EqDA oid (st_items s2) it2 Hf2.
  case: (effect_list_mem_toItem ops1 (op_init Oy) s1 it1 Heff1 Hmem1)
    => [Hnil1 | [inO1 [l1a [l1b [sMid1 [Hsplit1 [Hpre1 Htoit1]]]]]]];
    first by move: Hnil1; rewrite /= elem_of_nil.
  case: (effect_list_mem_toItem ops2 (op_init Oy) s2 it2 Heff2 Hmem2)
    => [Hnil2 | [inO2 [l2a [l2b [sMid2 [Hsplit2 [Hpre2 Htoit2]]]]]]];
    first by move: Hnil2; rewrite /= elem_of_nil.
  have HinA : in_id inO1 = oid.
  { rewrite -(@toItem_id _ EqDA inO1 (st_items sMid1) it1 Htoit1).
    exact (@find_by_id_id _ EqDA oid (st_items s1) it1 Hf1). }
  have HinB : in_id inO2 = oid.
  { rewrite -(@toItem_id _ EqDA inO2 (st_items sMid2) it2 Htoit2).
    exact (@find_by_id_id _ EqDA oid (st_items s2) it2 Hf2). }
  have HB1 : B (OpInsert inO1)
    by apply: Hsrc1; rewrite Hsplit1 elem_of_app elem_of_cons; right; left.
  have HB2 : B (OpInsert inO2)
    by apply: Hsrc2; rewrite Hsplit2 elem_of_app elem_of_cons; right; left.
  have HopEq : OpInsert inO1 = OpInsert inO2.
  { apply (Huniq _ _ HB1 HB2). by rewrite /= HinA HinB. }
  move: HopEq => [= HinOeq]. subst inO2.
  have HsrcL1 : ∀ x, x ∈ l1a -> B x
    by move=> x Hx; apply: Hsrc1; rewrite Hsplit1 elem_of_app; left.
  have HsrcL2 : ∀ x, x ∈ l2a -> B x
    by move=> x Hx; apply: Hsrc2; rewrite Hsplit2 elem_of_app; left.
  have [o1 [r1 [id1 [c1 [Hdef1 [HoL1 [HoR1 [Hidd1 Hcc1]]]]]]]] :=
    proj1 (toItem_ok_iff inO1 (st_items sMid1) it1) Htoit1.
  have [o2 [r2 [id2 [c2 [Hdef2 [HoL2 [HoR2 [Hidd2 Hcc2]]]]]]]] :=
    proj1 (toItem_ok_iff inO1 (st_items sMid2) it2) Htoit2.
  have Ho : o1 = o2.
  { move: HoL1 HoL2; rewrite /isLeftIdPtr; destruct (in_originId inO1) as [oid'|].
    - move=> [ot1 [Ho1eq Hfot1]] [ot2 [Ho2eq Hfot2]].
      have HszOt : (YjsItem_size ot1 < n)%nat by rewrite Hsize Hdef1 Ho1eq /=; lia.
      have Hoteq := IH (YjsItem_size ot1) HszOt ot1 ot2 l1a l2a sMid1 sMid2 oid'
        eq_refl HsrcL1 HsrcL2 Hpre1 Hpre2 Hfot1 Hfot2.
      by rewrite Ho1eq Ho2eq Hoteq.
    - by move=> -> ->. }
  have Hr : r1 = r2.
  { move: HoR1 HoR2; rewrite /isRightIdPtr; destruct (in_rightOriginId inO1) as [rid'|].
    - move=> [rt1 [Hr1eq Hfrt1]] [rt2 [Hr2eq Hfrt2]].
      have HszRt : (YjsItem_size rt1 < n)%nat by rewrite Hsize Hdef1 Hr1eq /=; lia.
      have Hrteq := IH (YjsItem_size rt1) HszRt rt1 rt2 l1a l2a sMid1 sMid2 rid'
        eq_refl HsrcL1 HsrcL2 Hpre1 Hpre2 Hfrt1 Hfrt2.
      by rewrite Hr1eq Hr2eq Hrteq.
    - by move=> -> ->. }
  by rewrite Hdef1 Hdef2 Ho Hr Hidd1 Hidd2 Hcc1 Hcc2.
Qed.

(** [toItem_isValid_transport], restricted to the lookups [toItem] performs:
    the origin / right-origin finds. (The upstream lemma quantifies over all
    ids; only these two matter, and the relaxed setting can only supply
    these two.) *)
Lemma toItem_isValid_transport_origins (input : IntegrateInput (A := A))
    (state0 s : list (YjsItem A)) (item0 : YjsItem A) :
  toItem input state0 = Some item0 ->
  IsItemValid item0 ->
  (∀ oid oit, (in_originId input = Some oid ∨ in_rightOriginId input = Some oid) ->
     find_by_id oid state0 = Some oit -> find_by_id oid s = Some oit) ->
  ∃ item, toItem input s = Some item ∧ IsItemValid item.
Proof.
  move=> Ht0 Hvalid Hpres. exists item0. split; last exact Hvalid.
  move: Ht0. rewrite /toItem.
  destruct (in_originId input) as [oid|] eqn:HoO;
    destruct (in_rightOriginId input) as [rid|] eqn:HrO; rewrite /=.
  - move=> /bind_Some [op [Hop Hrest]].
    move: Hop => /fmap_Some [oit [Hfo Hopeq]].
    move: Hrest => /bind_Some [rp [Hrp Hlast]].
    move: Hrp => /fmap_Some [rit [Hfr Hrpeq]]. subst op rp.
    by rewrite (Hpres oid oit (or_introl eq_refl) Hfo) /=
               (Hpres rid rit (or_intror eq_refl) Hfr) /=.
  - move=> /bind_Some [op [Hop Hlast]].
    move: Hop => /fmap_Some [oit [Hfo Hopeq]]. subst op.
    by rewrite (Hpres oid oit (or_introl eq_refl) Hfo) /=.
  - move=> /bind_Some [rp [Hrp Hlast]].
    move: Hrp => /fmap_Some [rit [Hfr Hrpeq]]. subst rp.
    by rewrite (Hpres rid rit (or_intror eq_refl) Hfr) /=.
  - by [].
Qed.

(* ----- coherence-level provenance ----- *)

(** An item of the coherent document was inserted by a delivered op of its
    type, carrying its id. *)
Lemma docm_mem_delivered h (m : DocM) (t : TId) (x : YjsItem A) :
  history_state_coh h m ->
  x ∈ docm_get m t ->
  ∃ input : IntegrateInput (A := A),
    (t, OpInsert input) ∈ delivered_ops h ∧ in_id input = item_id x.
Proof.
  move=> Hcoh Hx.
  destruct (history_state_coh_proj h m t Hcoh) as (st & Hinterp & Hitems).
  rewrite -Hitems in Hx.
  case: (effect_list_mem_src (omap deliverP (proj_hist t h)) (op_init Oy) st x Hinterp Hx)
    => [Hnil | [xin [Hxin Hxid]]].
  { move: Hnil. rewrite /= elem_of_nil //. }
  exists xin. split; [| exact Hxid].
  rewrite -(delivered_ops_proj t h) elem_of_proj_ops // in Hxin.
Qed.

(** Conversely, a delivered insert's item is in the coherent document (at its
    type), so its id is integrated store-wide. *)
Lemma delivered_docm_has h (m : DocM) (t : TId) (input : IntegrateInput (A := A)) :
  history_state_coh h m ->
  (t, OpInsert input) ∈ delivered_ops h ->
  docm_has m (in_id input) = true.
Proof.
  move=> Hcoh Hin.
  destruct (history_state_coh_proj h m t Hcoh) as (st & Hinterp & Hitems).
  have Hmem : OpInsert input ∈ omap deliverP (proj_hist t h).
  { rewrite -(delivered_ops_proj t h) elem_of_proj_ops //. }
  pose proof (effect_list_uniqueId_init (omap deliverP (proj_hist t h)) st Hinterp) as Huniq.
  pose proof (effect_list_insert_mem (omap deliverP (proj_hist t h)) (op_init Oy) st input
                Hinterp Huniq Hmem) as (it & Hitid & Hfind).
  apply docm_has_spec. exists t, it.
  rewrite -Hitems. split; [| exact Hitid].
  exact (@find_by_id_mem _ EqDA (in_id input) (st_items st) it Hfind).
Qed.

(** The uniqueness backbone for [item_determinism_raw] at type [t0]: two
    broadcast ops of type [t0] with equal ids are equal. *)
Lemma broadcast_type_uniq N (t0 : TId) :
  history_wf N ->
  ∀ x y : @YjsOperation A,
    op_broadcast N (t0, x) -> op_broadcast N (t0, y) -> yopid x = yopid y -> x = y.
Proof.
  move=> Hwf x y [i Hi] [j Hj] Hid.
  have [_ Heq] := hwf_msg_id_unique N Hwf (t0, x) (t0, y) i j Hi Hj Hid.
  by injection Heq.
Qed.

(** Everything delivered was broadcast (as its own doc-level op). *)
Lemma delivered_ops_broadcast_src N c h :
  history_wf N -> N !! c = Some h ->
  ∀ op : Op, op ∈ delivered_ops h -> op_broadcast N op.
Proof.
  move=> Hwf Hc op Hin.
  apply elem_of_delivered_ops_ev in Hin.
  have Hd : EvDeliver op ∈ to_histories N c by rewrite (to_histories_lookup N c h Hc).
  exact (hwf_deliver_has_a_cause N Hwf c op Hd).
Qed.

(** THE relaxed validity transport: a broadcast insert is valid in any
    coherent state that has integrated its ORIGINS (same type). No causal
    coverage: broadcast-time validity moves along [item_determinism_raw],
    which only needs the shared broadcast universe. *)
Lemma docm_valid_from_deps N c h (m : DocM) (t0 : TId)
    (input : IntegrateInput (A := A)) :
  history_wf N -> N !! c = Some h ->
  history_state_coh h m ->
  op_broadcast N (t0, OpInsert input) ->
  (∀ oid : YjsId, (in_originId input = Some oid ∨ in_rightOriginId input = Some oid) ->
     ∃ (t' : TId) (x : IntegrateInput (A := A)),
       (t', OpInsert x) ∈ delivered_ops h ∧ in_id x = oid) ->
  ∃ item0, toItem input (docm_get m t0) = Some item0 ∧ IsItemValid item0.
Proof.
  move=> Hwf Hc Hcoh Hbc Horigins.
  (* the author's pre-broadcast state, projected at [t0] *)
  destruct Hbc as (j & Hj).
  destruct (list_elem_of_split _ _ Hj) as (preA & postA & HhjA).
  have HhjA' : to_histories N j = preA ++ [EvBroadcast (t0, OpInsert input)] ++ postA
    by rewrite HhjA.
  destruct (hwf_broadcast_valid N Hwf j _ preA postA HhjA') as (sA & HinterpA & HvalidA).
  destruct HvalidA as (itemA & HtoitA & HvalidA).
  have HinterpAt : interpHistory Oy (proj_hist t0 preA) (op_init Oy) (doc_get sA t0)
    := doc_interp_proj preA sA t0 HinterpA.
  (* the receiver's state, projected at [t0] *)
  destruct (history_state_coh_proj h m t0 Hcoh) as (stR & HinterpR & HitemsR).
  rewrite -HitemsR.
  (* sourcing of both projected replays in the broadcast universe at [t0] *)
  set B := λ y : @YjsOperation A, op_broadcast N (t0, y).
  have HsrcA : ∀ y, y ∈ omap deliverP (proj_hist t0 preA) -> B y.
  { move=> y Hy.
    have Hy' : (t0, y) ∈ delivered_ops preA.
    { rewrite -(delivered_ops_proj t0 preA) elem_of_proj_ops // in Hy. }
    apply elem_of_delivered_ops_ev in Hy'.
    have Hd : EvDeliver (t0, y) ∈ to_histories N j by rewrite HhjA'; set_solver.
    exact (hwf_deliver_has_a_cause N Hwf j (t0, y) Hd). }
  have HsrcR : ∀ y, y ∈ omap deliverP (proj_hist t0 h) -> B y.
  { move=> y Hy.
    have Hy' : (t0, y) ∈ delivered_ops h.
    { rewrite -(delivered_ops_proj t0 h) elem_of_proj_ops // in Hy. }
    exact (delivered_ops_broadcast_src N c h Hwf Hc (t0, y) Hy'). }
  have Huniq : ∀ x y, B x -> B y -> yopid x = yopid y -> x = y
    := broadcast_type_uniq N t0 Hwf.
  (* transport along the origins *)
  apply (toItem_isValid_transport_origins input (st_items (doc_get sA t0))
           (st_items stR) itemA HtoitA HvalidA).
  move=> oid oitA Hor HfindA.
  (* the origin op, as delivered at the receiver: same type by id uniqueness *)
  destruct (Horigins oid Hor) as (t' & xR & HdelR & HidR).
  (* the origin op at the author's prefix: type [t0] *)
  have HmemA : oitA ∈ st_items (doc_get sA t0)
    := @find_by_id_mem _ EqDA oid (st_items (doc_get sA t0)) oitA HfindA.
  destruct (effect_list_mem_src (omap deliverP (proj_hist t0 preA)) (op_init Oy)
              (doc_get sA t0) oitA HinterpAt HmemA)
    as [Hnil | (xA & HxA & HxAid)].
  { move: Hnil. rewrite /= elem_of_nil //. }
  have HidA : in_id xA = oid.
  { rewrite HxAid. exact (@find_by_id_id _ EqDA oid _ _ HfindA). }
  (* the two origin ops agree, so the receiver delivered it into [t0] *)
  have HbcA : op_broadcast N (t0, OpInsert xA) := HsrcA _ HxA.
  have HbcR : op_broadcast N (t', OpInsert xR).
  { exact (delivered_ops_broadcast_src N c h Hwf Hc _ HdelR). }
  have Heqop : (t0, OpInsert xA) = ((t', OpInsert xR) : Op).
  { destruct HbcA as (jA & HjA). destruct HbcR as (jR & HjR).
    exact (proj2 (hwf_msg_id_unique N Hwf _ _ jA jR HjA HjR
                    ltac:(by rewrite /DocOp_id /= HidA HidR))). }
  injection Heqop as Heqt HeqxA. subst t' xR.
  (* the receiver's item with this id *)
  have HmemRop : OpInsert xA ∈ omap deliverP (proj_hist t0 h).
  { rewrite -(delivered_ops_proj t0 h) elem_of_proj_ops //. }
  pose proof (effect_list_uniqueId_init (omap deliverP (proj_hist t0 h)) stR HinterpR)
    as HuniqR.
  pose proof (effect_list_insert_mem (omap deliverP (proj_hist t0 h)) (op_init Oy) stR xA
                HinterpR HuniqR HmemRop) as (oitR & HoitRid & HfindR).
  rewrite HidA in HfindR.
  (* determinism: the author's and the receiver's items with id [oid] agree *)
  have Heqit : oitA = oitR.
  { exact (item_determinism_raw B Huniq oitA oitR
             (omap deliverP (proj_hist t0 preA)) (omap deliverP (proj_hist t0 h))
             (doc_get sA t0) stR oid HsrcA HsrcR HinterpAt HinterpR HfindA HfindR). }
  rewrite Heqit //.
Qed.

(* ----- the FIFO clock bound ----- *)

(** Every integrated same-author item's clock lies strictly below an
    undelivered broadcast op's clock: delivered ops of one author form a log
    prefix (FIFO), the op sits at-or-past the prefix boundary, and the log is
    clock-sorted. This is [ValidReplay]'s doc-global clock condition, with no
    causal reasoning. *)
Lemma delivered_clock_bound N c h (m : DocM) (op0 : Op) :
  history_wf N -> N !! c = Some h ->
  history_state_coh h m ->
  op_broadcast N op0 ->
  opid op0 ∉ delivered_ids h ->
  ∀ (t : TId) x, x ∈ docm_get m t ->
    clientId (item_id x) = clientId (opid op0) ->
    (clock (item_id x) < clock (opid op0))%nat.
Proof.
  move=> Hwf Hc Hcoh Hbc Hnotdel t x Hx Hcc.
  set j0 := clientId (opid op0).
  set log := broadcast_ops (to_histories N j0).
  (* the item's op, delivered here, authored at [j0] *)
  destruct (docm_mem_delivered h m t x Hcoh Hx) as (xin & Hxdel & Hxid).
  have HbcX : op_broadcast N (t, OpInsert xin)
    := delivered_ops_broadcast_src N c h Hwf Hc _ Hxdel.
  have HcidX : clientId (opid ((t, OpInsert xin) : Op)) = j0.
  { rewrite /DocOp_id /= Hxid. exact Hcc. }
  have HyF : (t, OpInsert xin) ∈ delivered_from h j0.
  { apply elem_of_delivered_from.
    split; [by apply elem_of_delivered_ops_ev | exact HcidX]. }
  (* positions *)
  have Hpre : delivered_from h j0 `prefix_of` log.
  { rewrite -(to_histories_lookup N c h Hc). exact (hwf_fifo N Hwf c j0). }
  set L := length (delivered_from h j0).
  have HtakeL : delivered_from h j0 = take L log.
  { destruct Hpre as [tl Htl]. rewrite /L Htl take_app_length //. }
  rewrite HtakeL in HyF. apply elem_of_take in HyF.
  destruct HyF as (qy & Hqy & HqyL).
  have Hoplog : op0 ∈ log.
  { apply elem_of_broadcast_ops.
    destruct Hbc as (i & Hi). rewrite /log /j0 (hwf_client_id N Hwf op0 i Hi) //. }
  destruct (list_elem_of_lookup_1 _ _ Hoplog) as (q0 & Hq0).
  have Hq0ge : (L <= q0)%nat.
  { destruct (decide (L <= q0)%nat) as [| Hgt]; [done | exfalso].
    apply Hnotdel.
    have Hin : op0 ∈ delivered_from h j0.
    { rewrite HtakeL. apply elem_of_take. exists q0. split; [done | lia]. }
    apply elem_of_delivered_from in Hin. destruct Hin as [Hin _].
    apply elem_of_delivered_ids. by exists op0. }
  have Hlt : (clock (opid ((t, OpInsert xin) : Op)) < clock (opid op0))%nat.
  { apply (broadcast_log_clock_lt N j0 qy q0 _ _ Hwf ltac:(lia) Hqy Hq0). }
  move: Hlt. rewrite /DocOp_id /= Hxid //.
Qed.

(* ----- the drained pending is a valid replay ----- *)

(** THE certificate lemma (issue #40): draining a pending of broadcast ops
    against a coherent store yields a [ValidReplay] of the applied list, the
    coherent state and well-formed history advance by exactly those
    deliveries, and no applied op is authored by the receiver. This replaces
    the retired [certs_ValidReplay]: there is NO ordering, causal-closure, or
    freshness obligation on the pending. *)
Lemma pending_ValidReplay N c h (m : DocM)
    (applied : list (TId * IntegrateInput (A := A))) (m' : DocM) :
  history_wf N -> N !! c = Some h ->
  history_state_coh h m ->
  (∀ ti : TId * IntegrateInput (A := A), ti ∈ applied ->
     op_broadcast N (ti.1, OpInsert ti.2)) ->
  PendingReplay m applied m' ->
  ValidReplay applied m m' ∧
  history_state_coh (h ++ (deliver_ev <$> applied)) m' ∧
  history_wf (<[c := h ++ (deliver_ev <$> applied)]> N) ∧
  (∀ ti : TId * IntegrateInput (A := A), ti ∈ applied ->
     clientId (in_id ti.2) ≠ c).
Proof.
  move=> Hwf HNc Hcoh Hcerts Hreplay.
  move: N h Hwf HNc Hcoh Hcerts.
  elim: Hreplay => [m0 | m0 ti arr' rest m0' Hfresh Hready Hint Hrest IH]
    N h Hwf HNc Hcoh Hcerts.
  - split_and!.
    + exact (VR_nil m0).
    + rewrite /= app_nil_r //.
    + rewrite /= app_nil_r (insert_id N c h HNc) //.
    + move=> ti Hin. by apply elem_of_nil in Hin.
  - destruct ti as [t0 input]. simpl in *.
    set op0 : Op := (t0, OpInsert input).
    have Hbc0 : op_broadcast N op0.
    { exact (Hcerts (t0, input) ltac:(apply elem_of_cons; by left)). }
    have Hop0id : opid op0 = in_id input by done.
    (* fresh here: not delivered *)
    have Hnotdel : opid op0 ∉ delivered_ids h.
    { rewrite Hop0id. move=> Hin.
      apply elem_of_delivered_ids in Hin. destruct Hin as (y & Hyh & Hyid).
      have Hins : ∃ inputy, y.2 = OpInsert inputy.
      { apply (hwf_insert_only N Hwf c y). right.
        rewrite (to_histories_lookup N c h HNc) //. }
      destruct Hins as (inputy & Hy2). destruct y as [ty y2]. simpl in Hy2. subst y2.
      have Hdel : (ty, OpInsert inputy) ∈ delivered_ops h
        by apply elem_of_delivered_ops_ev.
      have := delivered_docm_has h m0 ty inputy Hcoh Hdel.
      have -> : in_id inputy = in_id input by exact Hyid.
      rewrite Hfresh //. }
    (* the gate's arrival facts, translated to delivered ops *)
    have Hready' := proj1 (input_ready_spec m0 input) Hready.
    have Harrive : ∀ d : YjsId, d ∈ input_deps input ->
        ∃ (t' : TId) (x : IntegrateInput (A := A)),
          (t', OpInsert x) ∈ delivered_ops h ∧ in_id x = d.
    { move=> d Hd.
      have Hhas := Hready' d Hd.
      apply docm_has_spec in Hhas. destruct Hhas as (t' & x & Hx & Hxid).
      destruct (docm_mem_delivered h m0 t' x Hcoh Hx) as (xin & Hxdel & Hxinid).
      exists t', xin. split; [exact Hxdel | by rewrite Hxinid Hxid]. }
    (* validity at the current state *)
    have Hval : ∃ item0, toItem input (docm_get m0 t0) = Some item0 ∧ IsItemValid item0.
    { apply (docm_valid_from_deps N c h m0 t0 input Hwf HNc Hcoh Hbc0).
      move=> oid Hor. apply Harrive.
      rewrite /input_deps !elem_of_app.
      destruct Hor as [Ho | Ho]; rewrite Ho.
      - left. apply list_elem_of_singleton. done.
      - right. left. apply list_elem_of_singleton. done. }
    destruct Hval as (item0 & Htoit0 & Hvalid0).
    (* the doc-global clock bound *)
    have Hbnd : ∀ (t : TId) x, x ∈ docm_get m0 t ->
        clientId (item_id x) = clientId (in_id input) ->
        (clock (item_id x) < clock (in_id input))%nat.
    { have := delivered_clock_bound N c h m0 op0 Hwf HNc Hcoh Hbc0 Hnotdel.
      rewrite Hop0id //. }
    have Hmax : maximalId item0 (docm_get m0 t0).
    { move=> x Hx Hcx.
      rewrite (toItem_id input (docm_get m0 t0) item0 Htoit0).
      apply (Hbnd t0 x Hx).
      rewrite -(toItem_id input (docm_get m0 t0) item0 Htoit0) //. }
    (* not the receiver's own op *)
    have Hnoc : clientId (in_id input) ≠ c.
    { move=> Hcc.
      have Hbcc : EvBroadcast op0 ∈ to_histories N c.
      { destruct Hbc0 as (i & Hi).
        have Hic : i = c.
        { rewrite -(hwf_client_id N Hwf op0 i Hi) Hop0id Hcc //. }
        rewrite -Hic //. }
      have Hd : EvDeliver op0 ∈ h.
      { rewrite -(to_histories_lookup N c h HNc).
        pose proof (hwf_deliver_locally N Hwf c op0 Hbcc) as (l1 & l2 & l3 & Hsp).
        rewrite Hsp. set_solver. }
      apply Hnotdel. apply elem_of_delivered_ids. by exists op0. }
    (* one ghost delivery: wf + coherence step *)
    have Hpred : ∀ k, clock (opid op0) = S k ->
        MkYjsId (clientId (opid op0)) k ∈ delivered_ids h.
    { move=> k Hck.
      have Hd : MkYjsId (clientId (in_id input)) k ∈ input_deps input.
      { rewrite /input_deps !elem_of_app.
        right. right. rewrite Hop0id in Hck. rewrite Hck.
        apply list_elem_of_singleton. done. }
      destruct (Harrive _ Hd) as (t' & x & Hxdel & Hxid).
      apply elem_of_delivered_ids.
      exists (t', OpInsert x). split; [by apply elem_of_delivered_ops_ev |].
      have -> : opid ((t', OpInsert x) : Op) = in_id x by done.
      rewrite Hxid Hop0id //. }
    have Hwf' : history_wf (<[c := h ++ [EvDeliver op0]]> N)
      := history_wf_deliver N c h op0 Hwf HNc Hbc0 Hnotdel Hpred.
    (* coherence step *)
    destruct Hcoh as (s & Hinterp & Hitems).
    have Hcs : isClockSafe (in_id input) (docm_get m0 t0) = true
      := maximalId_isClockSafe input (docm_get m0 t0) item0 Htoit0 Hmax.
    set st0 := doc_get s t0.
    set s' := <[t0 := MkYjsState arr' (st_deleted st0)]> s.
    have Hcoh' : history_state_coh (h ++ [EvDeliver op0]) (<[t0 := arr']> m0).
    { exists s'. split.
      - apply (interpHistory_snoc_deliver h op0 (op_init O) s s' Hinterp).
        exists (MkYjsState arr' (st_deleted st0)). split; [| done].
        rewrite /op0 /= /YjsState_insert /integrateSafe -/st0 (Hitems t0) Hcs Hint //=.
      - move=> t. destruct (decide (t = t0)) as [-> | Hne].
        + rewrite /s' doc_get_insert_eq docm_get_insert_eq //.
        + rewrite /s' doc_get_insert_ne // docm_get_insert_ne //. }
    (* recurse on the extended history *)
    have HNc' : (<[c := h ++ [EvDeliver op0]]> N) !! c = Some (h ++ [EvDeliver op0])
      by rewrite lookup_insert_eq.
    have Hcerts' : ∀ ti : TId * IntegrateInput (A := A), ti ∈ rest ->
        op_broadcast (<[c := h ++ [EvDeliver op0]]> N) (ti.1, OpInsert ti.2).
    { move=> ti Hin.
      have Hb := Hcerts ti (ltac:(apply elem_of_cons; by right)).
      apply (op_broadcast_append N c h [EvDeliver op0] _ HNc). by left. }
    destruct (IH _ _ Hwf' HNc' Hcoh' Hcerts') as (Hvr & Hcoh'' & Hwf'' & Hnoc').
    split_and!.
    + exact (VR_cons t0 input rest m0 arr' m0' item0 Htoit0 Hvalid0 Hmax Hbnd Hint Hvr).
    + move: Hcoh''.
      have -> : (h ++ [EvDeliver op0]) ++ (deliver_ev <$> rest)
              = h ++ (deliver_ev <$> ((t0, input) :: rest))
        by rewrite fmap_cons -app_assoc //.
      done.
    + move: Hwf''.
      rewrite insert_insert_eq.
      have -> : (h ++ [EvDeliver op0]) ++ (deliver_ev <$> rest)
              = h ++ (deliver_ev <$> ((t0, input) :: rest))
        by rewrite fmap_cons -app_assoc //.
      done.
    + move=> ti Hin. apply elem_of_cons in Hin.
      destruct Hin as [-> | Hin]; [exact Hnoc | exact (Hnoc' ti Hin)].
Qed.

(** Certified pendings are ready-total: broadcast-time validity transports to any
    drain intermediate along the structural dependencies alone. *)
Lemma pending_ready_total_of_certs N c h (m : DocM)
    (pending applied : list (TId * IntegrateInput (A := A))) :
  history_wf N -> N !! c = Some h ->
  history_state_coh h m ->
  (∀ t : TId, YjsArrInvariant (docm_get m t)) ->
  (∀ ti : TId * IntegrateInput (A := A), ti ∈ pending ->
     op_broadcast N (ti.1, OpInsert ti.2)) ->
  (∀ ti : TId * IntegrateInput (A := A), ti ∈ applied -> ti ∈ pending) ->
  pending_ready_total m pending applied.
Proof.
  move=> Hwf HNc Hcoh Hinvs Hcerts Happsub pre suf mx ti Heq Hpr Hin Hfresh Hready.
  have Hcpre : ∀ tj : TId * IntegrateInput (A := A), tj ∈ pre ->
      op_broadcast N (tj.1, OpInsert tj.2).
  { move=> tj Htj. apply Hcerts, Happsub. rewrite Heq elem_of_app. by left. }
  pose proof (pending_ValidReplay N c h m pre mx Hwf HNc Hcoh Hcpre Hpr)
    as (Hvr & Hcoh' & Hwf' & _).
  set N' := <[c := h ++ (deliver_ev <$> pre)]> N.
  set h' := h ++ (deliver_ev <$> pre).
  have HN'c : N' !! c = Some h' by rewrite /N' lookup_insert_eq.
  have Hbc' : op_broadcast N' (ti.1, OpInsert ti.2).
  { apply (op_broadcast_append N c h _ _ HNc). left. exact (Hcerts ti Hin). }
  (* the gate's arrivals, as delivered ops of [h'] *)
  have Hready' := proj1 (input_ready_spec mx ti.2) Hready.
  have Harrive : ∀ d : YjsId, d ∈ input_deps ti.2 ->
      ∃ (t' : TId) (x : IntegrateInput (A := A)),
        (t', OpInsert x) ∈ delivered_ops h' ∧ in_id x = d.
  { move=> d Hd.
    have Hhas := Hready' d Hd.
    apply docm_has_spec in Hhas. destruct Hhas as (t' & x & Hx & Hxid).
    destruct (docm_mem_delivered h' mx t' x Hcoh' Hx) as (xin & Hxdel & Hxinid).
    exists t', xin. split; [exact Hxdel | by rewrite Hxinid Hxid]. }
  (* validity at the intermediate *)
  have Hval : ∃ item0, toItem ti.2 (docm_get mx ti.1) = Some item0 ∧ IsItemValid item0.
  { apply (docm_valid_from_deps N' c h' mx ti.1 ti.2 Hwf' HN'c Hcoh' Hbc').
    move=> oid Hor. apply Harrive.
    destruct Hor as [Ho | Ho]; [exact (input_deps_originL _ _ Ho) | exact (input_deps_originR _ _ Ho)]. }
  destruct Hval as (item0 & Htoit & Hvld).
  (* freshness at the intermediate *)
  have Hnotdel : opid ((ti.1, OpInsert ti.2) : Op) ∉ delivered_ids h'.
  { move=> Hdel.
    apply elem_of_delivered_ids in Hdel. destruct Hdel as (y & Hyh & Hyid).
    have Hins : ∃ inputy, y.2 = OpInsert inputy.
    { apply (hwf_insert_only N' Hwf' c y). right.
      rewrite (to_histories_lookup N' c h' HN'c) //. }
    destruct Hins as (inputy & Hy2). destruct y as [ty y2]. simpl in Hy2. subst y2.
    have Hdel2 : (ty, OpInsert inputy) ∈ delivered_ops h'
      by apply elem_of_delivered_ops_ev.
    have := delivered_docm_has h' mx ty inputy Hcoh' Hdel2.
    have -> : in_id inputy = in_id ti.2 by exact Hyid.
    rewrite Hfresh //. }
  (* clock maximality at the intermediate *)
  have Hbnd := delivered_clock_bound N' c h' mx ((ti.1, OpInsert ti.2) : Op)
                 Hwf' HN'c Hcoh' Hbc' Hnotdel.
  have Hmax : maximalId item0 (docm_get mx ti.1).
  { move=> x Hx Hcx.
    rewrite (toItem_id ti.2 (docm_get mx ti.1) item0 Htoit).
    have -> : clock (in_id ti.2) = clock (opid ((ti.1, OpInsert ti.2) : Op)) by done.
    apply (Hbnd ti.1 x Hx).
    have -> : clientId (opid ((ti.1, OpInsert ti.2) : Op)) = clientId (in_id ti.2) by done.
    rewrite -(toItem_id ti.2 (docm_get mx ti.1) item0 Htoit) //. }
  (* invariant at the intermediate *)
  have Hinv' : YjsArrInvariant (docm_get mx ti.1)
    := ValidReplay_arrinv pre m mx Hvr Hinvs ti.1.
  exact (integrate_some_of_toItem ti.2 (docm_get mx ti.1) item0 Hinv' Htoit Hvld Hmax).
Qed.

(* ===== state vectors (max semantics) ====================================== *)

(** The vector-clock view of delivered state ([docs/plan-predicate-refactor.md]
    section 6, step 1). [sv_of h] summarizes [delivered_ids h] per client as
    "max delivered clock + 1" (absent = 0); [sv_join] is the pointwise-max
    least upper bound; delivering a batch is exactly a join
    ([sv_of_deliver_batch]), and each [Text.Insert] event pair is a one-op
    join ([sv_of_broadcast]).

    These are the MAX-semantics laws only: [sv_of] soundly bounds every
    delivered id ([delivered_ids_lt_sv]) and is attained ([sv_of_attained]),
    but it determines the delivered SET only under per-client gaplessness,
    which the current broadcast step does not yet enforce (an author's clocks
    are only required to grow, not to be successors). The faithful reading
    (ids strictly below [sv_of h] = [delivered_ids h]) and the persistent
    [is_sv_lb] certificates are staged as steps 2 and 3 of the plan. *)

(** [sv_get sv c]: the per-client "next clock" (absent = 0). *)
Definition sv_get (sv : gmap ClientId nat) (c : ClientId) : nat :=
  default 0%nat (sv !! c).

(** Pointwise-max join: the least upper bound of two state vectors. *)
Definition sv_join (sv1 sv2 : gmap ClientId nat) : gmap ClientId nat :=
  union_with (λ a b, Some (a `max` b)%nat) sv1 sv2.

(** The one-op state vector: its author's clock, plus one. *)
Definition op_sv (op : Op) : gmap ClientId nat :=
  {[ clientId (opid op) := S (clock (opid op)) ]}.

(** The state vector of a list of (delivered) ops / of a history's delivers. *)
Definition svs_of (l : list Op) : gmap ClientId nat :=
  foldr (λ op acc, sv_join (op_sv op) acc) ∅ l.

Definition sv_of (h : list Ev) : gmap ClientId nat := svs_of (delivered_ops h).

(** The state vector a decoded batch contributes. *)
Definition batch_sv (inputs : list (TId * IntegrateInput (A := A))) : gmap ClientId nat :=
  svs_of ((λ ti, (ti.1, OpInsert ti.2)) <$> inputs).

(* ----- the join semilattice ----- *)

Lemma sv_join_lookup sv1 sv2 c :
  sv_join sv1 sv2 !! c =
  match sv1 !! c, sv2 !! c with
  | Some a, Some b => Some (a `max` b)%nat
  | Some a, None => Some a
  | None, mb => mb
  end.
Proof. rewrite /sv_join lookup_union_with. by destruct (sv1 !! c), (sv2 !! c). Qed.

Lemma sv_get_join sv1 sv2 c :
  sv_get (sv_join sv1 sv2) c = (sv_get sv1 c `max` sv_get sv2 c)%nat.
Proof. rewrite /sv_get sv_join_lookup. destruct (sv1 !! c), (sv2 !! c); simpl; lia. Qed.

Lemma sv_join_comm sv1 sv2 : sv_join sv1 sv2 = sv_join sv2 sv1.
Proof.
  apply map_eq => c. rewrite !sv_join_lookup.
  destruct (sv1 !! c), (sv2 !! c) => //. f_equal. lia.
Qed.

Lemma sv_join_assoc sv1 sv2 sv3 :
  sv_join sv1 (sv_join sv2 sv3) = sv_join (sv_join sv1 sv2) sv3.
Proof.
  apply map_eq => c. rewrite !sv_join_lookup.
  destruct (sv1 !! c), (sv2 !! c), (sv3 !! c) => //=; f_equal; lia.
Qed.

Lemma sv_join_empty_l sv : sv_join ∅ sv = sv.
Proof. apply map_eq => c. rewrite sv_join_lookup lookup_empty //. Qed.

Lemma sv_join_empty_r sv : sv_join sv ∅ = sv.
Proof. apply map_eq => c. rewrite sv_join_lookup lookup_empty. by destruct (sv !! c). Qed.

Lemma sv_join_idemp sv : sv_join sv sv = sv.
Proof.
  apply map_eq => c. rewrite sv_join_lookup.
  destruct (sv !! c) => //. f_equal. lia.
Qed.

(* ----- homomorphism over histories ----- *)

Lemma svs_of_app (l1 l2 : list Op) :
  svs_of (l1 ++ l2) = sv_join (svs_of l1) (svs_of l2).
Proof.
  induction l1 as [| op l1 IH]; simpl.
  - rewrite sv_join_empty_l //.
  - rewrite IH sv_join_assoc //.
Qed.

Lemma sv_of_app (h1 h2 : list Ev) :
  sv_of (h1 ++ h2) = sv_join (sv_of h1) (sv_of h2).
Proof. rewrite /sv_of delivered_ops_app svs_of_app //. Qed.

Lemma delivered_ops_deliver_batch (inputs : list (TId * IntegrateInput (A := A))) :
  delivered_ops (deliver_ev <$> inputs) = (λ ti, (ti.1, OpInsert ti.2)) <$> inputs.
Proof.
  induction inputs as [| ti inputs IH]; [done |].
  rewrite /delivered_ops /deliver_ev !fmap_cons /=. f_equal. exact IH.
Qed.

(** THE join law: delivering a batch advances the state vector to the least
    upper bound of the receiver's and the batch's. *)
Lemma sv_of_deliver_batch (h : list Ev) (inputs : list (TId * IntegrateInput (A := A))) :
  sv_of (h ++ (deliver_ev <$> inputs)) = sv_join (sv_of h) (batch_sv inputs).
Proof. rewrite sv_of_app /sv_of /batch_sv delivered_ops_deliver_batch //. Qed.

(** The broadcast-side law (the two events [Text.Insert] appends per item). *)
Lemma sv_of_broadcast (h : list Ev) (op : Op) :
  sv_of (h ++ [EvBroadcast op; EvDeliver op]) = sv_join (sv_of h) (op_sv op).
Proof.
  rewrite sv_of_app. f_equal.
  rewrite /sv_of /delivered_ops /= sv_join_empty_r //.
Qed.

(* ----- semantics: upper bound + attainment (max reading) ----- *)

Lemma sv_get_op_sv_same (op : Op) :
  sv_get (op_sv op) (clientId (opid op)) = S (clock (opid op)).
Proof. rewrite /op_sv /sv_get lookup_singleton_eq. reflexivity. Qed.

Lemma svs_of_sound (l : list Op) (op : Op) :
  op ∈ l -> (clock (opid op) < sv_get (svs_of l) (clientId (opid op)))%nat.
Proof.
  induction l as [| op' l IH]; [by intros ?%elem_of_nil |].
  intros [-> | Hin]%elem_of_cons; simpl.
  - rewrite sv_get_join sv_get_op_sv_same. lia.
  - rewrite sv_get_join. have := IH Hin. lia.
Qed.

Lemma svs_of_attained (l : list Op) (c : ClientId) (n : nat) :
  sv_get (svs_of l) c = S n ->
  ∃ op, op ∈ l ∧ clientId (opid op) = c ∧ clock (opid op) = n.
Proof.
  induction l as [| op' l IH]; simpl.
  - rewrite /sv_get lookup_empty //.
  - rewrite sv_get_join => Hmax.
    destruct (Nat.max_dec (sv_get (op_sv op') c) (sv_get (svs_of l) c)) as [He | He];
      rewrite He in Hmax.
    + move: Hmax. rewrite /op_sv /sv_get.
      destruct (decide (clientId (opid op') = c)) as [Heq | Hne].
      * rewrite Heq lookup_singleton_eq. move=> /= [= <-].
        exists op'. split_and!; [by left | exact Heq | done].
      * rewrite lookup_singleton_ne; [| exact Hne]. move=> /= H. discriminate H.
    + destruct (IH Hmax) as (op & Hin & Hc & Hk).
      exists op. split_and!; [by right | done | done].
Qed.

(** Every delivered id sits strictly below the history's state vector at its
    client (the sound, gaplessness-free reading of [sv_of]). *)
Lemma delivered_ids_lt_sv (h : list Ev) (id : YjsId) :
  id ∈ delivered_ids h -> (clock id < sv_get (sv_of h) (clientId id))%nat.
Proof.
  rewrite /delivered_ids elem_of_list_to_set list_elem_of_fmap.
  move=> [op [-> Hin]]. exact (svs_of_sound (delivered_ops h) op Hin).
Qed.

(** A positive state-vector entry is attained by a delivered id. *)
Lemma sv_of_attained (h : list Ev) (c : ClientId) (n : nat) :
  sv_get (sv_of h) c = S n ->
  ∃ id, id ∈ delivered_ids h ∧ clientId id = c ∧ clock id = n.
Proof.
  move=> /svs_of_attained [op [Hin [Hc Hk]]].
  exists (opid op). split_and!; [| exact Hc | exact Hk].
  rewrite /delivered_ids elem_of_list_to_set. apply list_elem_of_fmap_2. exact Hin.
Qed.

(* ===== the per-author prefix order (lossless "state vector") ============== *)

(* [broadcast_ops] / [delivered_from] and their membership / snoc laws now
   live near the top of the file: [history_wf]'s per-author FIFO field
   ([hwf_fifo], issue #40) is stated over them. *)

(* ----- prefix monotonicity of the delivered views ----- *)

Lemma delivered_ops_prefix (h0 h : list Ev) :
  h0 `prefix_of` h -> delivered_ops h0 `prefix_of` delivered_ops h.
Proof.
  move=> [t ->]. rewrite delivered_ops_app. by eexists.
Qed.

Lemma delivered_from_prefix_mono (h0 h : list Ev) (j : ClientId) :
  h0 `prefix_of` h -> delivered_from h0 j `prefix_of` delivered_from h j.
Proof.
  move=> [t ->]. rewrite /delivered_from delivered_ops_app filter_app. by eexists.
Qed.

Lemma delivered_ids_prefix (h0 h : list Ev) :
  h0 `prefix_of` h -> delivered_ids h0 ⊆ delivered_ids h.
Proof.
  move=> [t ->]. rewrite delivered_ids_app. set_solver.
Qed.

Lemma sv_of_prefix (h0 h : list Ev) (c : ClientId) :
  h0 `prefix_of` h -> (sv_get (sv_of h0) c <= sv_get (sv_of h) c)%nat.
Proof.
  move=> [t ->]. rewrite sv_of_app sv_get_join. lia.
Qed.


(* ----- THE per-author prefix theorem ----- *)

(** At any replica, the delivered ops of author [j] are a PREFIX of [j]'s
    broadcast log. Since issue #40 this is a [history_wf] FIELD (maintained by
    the structural gate at each deliver step) rather than a consequence of
    causal delivery; the lemma keeps its name for the sync-protocol layer. *)
Lemma delivered_from_prefix (N : RawHistories) (c j : ClientId) :
  history_wf N ->
  delivered_from (to_histories N c) j `prefix_of` broadcast_ops (to_histories N j).
Proof. move=> Hwf. exact (hwf_fifo N Hwf c j). Qed.

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
  split.
  - move=> i. rewrite Hemp. constructor.
  - move=> i e He. rewrite Hemp in He. by apply elem_of_nil in He.
  - move=> mi mj i j Hmi Hmj Hid. rewrite Hemp in Hmi. by apply elem_of_nil in Hmi.
  - move=> i e pre post Hsplit. rewrite Hemp in Hsplit. by destruct pre.
  - move=> e i He. rewrite Hemp in He. by apply elem_of_nil in He.
  - move=> e i hist1 hist2 array Hsplit Hinterp. rewrite Hemp in Hsplit.
    by destruct hist1.
  - move=> i e pre post Hsplit. rewrite Hemp in Hsplit. by destruct pre.
  - move=> i e He. rewrite !Hemp in He.
    destruct He as [He | He]; by apply elem_of_nil in He.
  - move=> i j. rewrite !Hemp /delivered_from /delivered_ops /=. apply prefix_nil.
Qed.

Lemma ops_coh_init (C : gset ClientId) :
  ops_coh (gset_to_gmap [] C) ∅.
Proof.
  split.
  - move=> id op. rewrite lookup_empty //.
  - move=> op [i Hin]. exfalso. move: Hin.
    rewrite /to_histories lookup_gset_to_gmap.
    destruct (decide (i ∈ C)) as [HC | HC].
    + rewrite option_guard_True //= elem_of_nil //.
    + rewrite option_guard_False //= elem_of_nil //.
Qed.

End network_model.
