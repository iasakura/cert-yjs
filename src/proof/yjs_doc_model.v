(** Doc-level operations over multiple root types (issue #49, flat multi-root
    slice).

    y-octo's clock / causality is *doc-global* (one state vector per document),
    while integration is *per-type* (each struct carries its parent). This file
    is the pure model of that split, Iris-free and goose-free:

    - [TypeId]: the model name of a type — a named root ([RootId], the only
      constructor this slice uses) or a type-as-item anchor ([AnchorId], #43).
    - the doc-level operation instance: ops are [TypeId * YjsOperation], the
      doc state is a [gmap TypeId (YjsState A)], and an op's effect touches
      exactly its type's component ([doc_op_effect] / [DocO] / [DocOV] /
      [DocWithId]).
    - commutativity and strong convergence at the doc level: same-type
      concurrent ops commute by the upstream [yjs_concurrent_commute],
      different-type ops commute because they touch disjoint keys.
    - the *projection* reduction: a doc-level operation network restricted to
      one type is a [YjsOperationNetwork] ([proj_network]), so the upstream
      replay-validity theorems ([isValidState_insert_from_source], ...) apply
      per type with no upstream change. [DocOperationReplayValidity] and
      [DocOperationNetwork_converge_final] are assembled from it.

    The raw-history bridge (ghost-map shaped) consuming this file lives in
    [yjs_network_model]. *)
From stdpp Require Import base list gmap sorting.
From stdpp Require Import ssreflect.
From iris.prelude Require Import options.
From New.proof Require Import yjs_core.
From yjs.algorithm Require Export toitem_lemmas.
From yjs.crdt.operation Require Export causal_order hb_closed strong_causal_order.
From yjs.crdt.network Require Export causal_network operation_network.
From yjs.network Require Export yjs_network yjs_operation_network yjs_replay_validity.

(* ===== TypeId ============================================================= *)

Section type_id.
Context (P : Type).

(** The model name of a type: a root type by name, or (out of this slice,
    issue #43) a type stored as an item, anchored at that item's id. *)
Inductive TypeId : Type :=
  | RootId (name : P)
  | AnchorId (id : YjsId).

End type_id.

Arguments RootId {P} _.
Arguments AnchorId {P} _.

Global Instance TypeId_eq_dec {P} `{EqDecision P} : EqDecision (TypeId P).
Proof. solve_decision. Defined.

Global Instance TypeId_countable {P} `{Countable P} : Countable (TypeId P).
Proof.
  apply (inj_countable'
           (λ t, match t with RootId n => inl n | AnchorId i => inr i end)
           (λ s, match s with inl n => RootId n | inr i => AnchorId i end)).
  by intros [].
Qed.

(* ===== the doc-level operation instance =================================== *)

Section doc_model.
Context {A : Type} `{EqDA : EqDecision A}.
Context {P : Type} `{EqDP : !EqDecision P} `{CntP : !Countable P}.

Local Notation Op := (@YjsOperation A).
Local Notation opid := (@YjsOperation_id A).
Local Notation O := (@YjsOp A EqDA).
Local Notation TId := (TypeId P).
Local Notation DocOp := (TId * Op)%type.
Local Notation DocSt := (gmap TId (YjsState A)).

Set Default Proof Using "Type*".

(** The id of a doc-level op is its inner op's id (clocks are doc-global). *)
Definition DocOp_id (dop : DocOp) : YjsId := opid dop.2.

(** The state of one type in a doc state (absent = empty). *)
Definition doc_get (s : DocSt) (t : TId) : YjsState A :=
  default YjsState_empty (s !! t).

Lemma doc_get_empty t : doc_get (∅ : DocSt) t = YjsState_empty.
Proof. rewrite /doc_get lookup_empty //. Qed.

Lemma doc_get_insert_eq s t st : doc_get (<[t := st]> s) t = st.
Proof. rewrite /doc_get lookup_insert_eq //. Qed.

Lemma doc_get_insert_ne s t t' st : t' ≠ t -> doc_get (<[t := st]> s) t' = doc_get s t'.
Proof. move=> Hne. rewrite /doc_get lookup_insert_ne //. Qed.

(** A doc op's effect: step its own type's component, leave the rest. *)
Definition doc_op_effect (dop : DocOp) (s s' : DocSt) : Prop :=
  ∃ st', yjs_op_effect dop.2 (doc_get s dop.1) st' ∧ s' = <[dop.1 := st']> s.

Definition DocO : @Operation DocOp := @MkOperation DocOp DocSt ∅ doc_op_effect.

(** Validity / invariant, componentwise. *)
Definition DocIsValidMessage (s : DocSt) (dop : DocOp) : Prop :=
  IsValidMessage (st_items (doc_get s dop.1)) dop.2.

Definition isValidStateDoc (dop : DocOp) (s : DocSt) : Prop := DocIsValidMessage s dop.

Definition DocStateInvariant (s : DocSt) : Prop :=
  ∀ t st, s !! t = Some st -> YjsStateInvariant st.

Lemma DocStateInvariant_get (s : DocSt) (t : TId) :
  DocStateInvariant s -> YjsStateInvariant (doc_get s t).
Proof.
  move=> Hinv. rewrite /doc_get.
  destruct (s !! t) as [st |] eqn:Hlk.
  - exact (Hinv t st Hlk).
  - exact (stateInv_init O (@YjsOV A EqDA)).
Qed.

Definition DocOV : OperationValidity DocO.
Proof using A EqDA P EqDP CntP.
  refine (@Build_OperationValidity DocOp DocO isValidStateDoc DocStateInvariant _ _).
  - move=> t st. rewrite lookup_empty //.
  - move=> dop s s' Hinv Hvalid Heff.
    destruct dop as [t op]. destruct Heff as (st' & Heff & ->). simpl in *.
    move=> t' st0.
    destruct (decide (t' = t)) as [-> | Hne].
    + rewrite lookup_insert_eq. move=> [= <-].
      exact (stateInv_effect O (@YjsOV A EqDA) op (doc_get s t) st'
               (DocStateInvariant_get s t Hinv) Hvalid Heff).
    + rewrite lookup_insert_ne; last by move=> Heq; apply Hne; rewrite Heq.
      move=> Hlk. exact (Hinv t' st0 Hlk).
Defined.

Definition DocWithId : @WithId DocOp YjsId := {| wid := DocOp_id |}.

(* ===== commutativity ====================================================== *)

(** Concurrent doc ops of distinct clients commute: same type by the upstream
    [yjs_concurrent_commute], distinct types by key disjointness. *)
Lemma doc_concurrent_commute (a b : DocOp) (s s' : DocSt) :
  clientId (DocOp_id a) ≠ clientId (DocOp_id b) ->
  DocStateInvariant s -> isValidStateDoc a s -> isValidStateDoc b s ->
  eff_comp DocO (effect DocO a) (effect DocO b) s s' ->
  eff_comp DocO (effect DocO b) (effect DocO a) s s'.
Proof.
  destruct a as [ta a2]. destruct b as [tb b2].
  move=> Hcid Hinv Hva Hvb [m [Ha Hb]].
  destruct Ha as (sta & Hea & ->).
  destruct Hb as (stb & Heb & ->).
  simpl in *.
  destruct (decide (ta = tb)) as [-> | Hne].
  - (* same type: reduce to the per-type commutativity *)
    rewrite doc_get_insert_eq in Heb.
    have Hcomp : eff_comp O (effect O a2) (effect O b2) (doc_get s tb) stb
      by exists sta.
    have Hcomp' := yjs_concurrent_commute a2 b2 (doc_get s tb) stb Hcid
                     (DocStateInvariant_get s tb Hinv) Hva Hvb Hcomp.
    destruct Hcomp' as (m' & Hb' & Ha').
    exists (<[tb := m']> s). split.
    + exists m'. by split.
    + exists stb. rewrite doc_get_insert_eq. split; [exact Ha' |].
      (* NB: this stdpp's [insert_insert] is the general decide-form; [!] on it
         diverges. Use the same-key [insert_insert_eq]. *)
      rewrite /= !insert_insert_eq //.
  - (* distinct types: disjoint keys *)
    rewrite (doc_get_insert_ne s ta tb sta) in Heb;
      last by move=> Heq; apply Hne; rewrite Heq.
    exists (<[tb := stb]> s). split.
    + exists stb. by split.
    + exists sta. rewrite (doc_get_insert_ne s tb ta stb); last done.
      split; [exact Hea |].
      rewrite /= (insert_insert_ne _ ta tb) //.
Qed.

Lemma doc_concurrent_commutative (hb : @CausalOrder DocOp) (ops : list DocOp) :
  (∀ a b, a ∈ ops -> b ∈ ops -> hb_concurrent hb a b ->
     clientId (DocOp_id a) ≠ clientId (DocOp_id b)) ->
  concurrent_commutative DocO DocOV hb ops.
Proof.
  move=> Hdisc a b s s' Ha Hb Hconc Hsinv Hva Hvb.
  exact (doc_concurrent_commute a b s s' (Hdisc a b Ha Hb Hconc) Hsinv Hva Hvb).
Qed.

(** Doc-level strong convergence over an abstract causal order. *)
Theorem doc_strong_convergence
    (hb : @CausalOrder DocOp) (StateSource : DocOp -> Prop)
    (RV : OperationReplayValidity DocO DocOV DocWithId hb StateSource)
    (ops0 ops1 : list DocOp) (s : DocSt) :
  (∀ x, x ∈ ops0 -> StateSource x) -> (∀ x, x ∈ ops1 -> StateSource x) ->
  hb_consistent hb ops0 -> hb_consistent hb ops1 -> hbClosed hb ops0 -> hbClosed hb ops1 ->
  (∀ a b, a ∈ ops0 -> b ∈ ops0 -> hb_concurrent hb a b ->
     clientId (DocOp_id a) ≠ clientId (DocOp_id b)) ->
  IdNoDup DocWithId ops0 -> IdNoDup DocWithId ops1 ->
  (∀ x, x ∈ ops0 <-> x ∈ ops1) ->
  effect_list DocO ops0 (op_init DocO) s -> effect_list DocO ops1 (op_init DocO) s.
Proof.
  move=> Hsrc0 Hsrc1 Hc0 Hc1 Hcl0 Hcl1 Hdisc Hnd0 Hnd1 Hmem Heff.
  apply: (hb_consistent_effect_convergent DocO DocOV DocWithId hb StateSource RV
    ops0 ops1 s Hsrc0 Hsrc1 Hc0 Hc1 Hcl0 Hcl1 _ Hnd0 Hnd1 Hmem Heff).
  exact (doc_concurrent_commutative hb ops0 Hdisc).
Qed.

(* ===== effect determinism ================================================= *)

Lemma doc_op_effect_det (dop : DocOp) (s s1 s2 : DocSt) :
  doc_op_effect dop s s1 -> doc_op_effect dop s s2 -> s1 = s2.
Proof.
  move=> [st1 [He1 ->]] [st2 [He2 ->]].
  by rewrite (yjs_op_effect_det dop.2 (doc_get s dop.1) st1 st2 He1 He2).
Qed.

Lemma doc_effect_list_det (ops : list DocOp) (s s1 s2 : DocSt) :
  effect_list DocO ops s s1 -> effect_list DocO ops s s2 -> s1 = s2.
Proof.
  elim: ops s s1 s2 => [| op ops IH] s s1 s2.
  - by move=> /(effect_list_nil DocO) <- /(effect_list_nil DocO) <-.
  - move=> /(effect_list_cons DocO) [m1 [H1 Hr1]] /(effect_list_cons DocO) [m2 [H2 Hr2]].
    have Hm : m1 = m2 := doc_op_effect_det op s m1 m2 H1 H2.
    subst m2. exact (IH m1 s1 s2 Hr1 Hr2).
Qed.

(* ===== projections ======================================================== *)

(** Restrict a doc op / event / list to one type. *)
Definition proj_op (t : TId) (dop : DocOp) : option Op :=
  if decide (dop.1 = t) then Some dop.2 else None.

Definition proj_ev (t : TId) (e : @Event DocOp) : option (@Event Op) :=
  match e with
  | EvBroadcast dop => EvBroadcast <$> proj_op t dop
  | EvDeliver dop => EvDeliver <$> proj_op t dop
  end.

Definition proj_ops (t : TId) (l : list DocOp) : list Op := omap (proj_op t) l.
Definition proj_hist (t : TId) (h : list (@Event DocOp)) : list (@Event Op) :=
  omap (proj_ev t) h.

Lemma proj_op_Some (t : TId) (dop : DocOp) (o : Op) :
  proj_op t dop = Some o <-> dop = (t, o).
Proof.
  rewrite /proj_op. destruct (decide (dop.1 = t)) as [Heq | Hne].
  - split.
    + move=> [= <-]. destruct dop; simpl in *; by subst.
    + move=> ->. done.
  - split; [done | move=> Heq; subst dop; case: (Hne eq_refl)].
Qed.

Lemma proj_op_pair (t : TId) (o : Op) : proj_op t (t, o) = Some o.
Proof. apply proj_op_Some. done. Qed.

Lemma proj_ev_Some (t : TId) (e : @Event DocOp) (e' : @Event Op) :
  proj_ev t e = Some e' <->
  (∃ o : Op, e = EvBroadcast (t, o) ∧ e' = EvBroadcast o) ∨
  (∃ o : Op, e = EvDeliver (t, o) ∧ e' = EvDeliver o).
Proof.
  destruct e as [dop | dop]; simpl; split.
  - move=> /fmap_Some [o [Hp ->]]. left. exists o.
    by rewrite (proj1 (proj_op_Some t dop o) Hp).
  - move=> [[o [[= ->] ->]] | [o [Ho _]]]; [| done].
    rewrite proj_op_pair //.
  - move=> /fmap_Some [o [Hp ->]]. right. exists o.
    by rewrite (proj1 (proj_op_Some t dop o) Hp).
  - move=> [[o [Ho _]] | [o [[= ->] ->]]]; [done |].
    rewrite proj_op_pair //.
Qed.

Lemma proj_ev_broadcast (t : TId) (o : Op) :
  proj_ev t (EvBroadcast (t, o)) = Some (EvBroadcast o).
Proof. simpl. rewrite proj_op_pair //. Qed.

Lemma proj_ev_deliver (t : TId) (o : Op) :
  proj_ev t (EvDeliver (t, o)) = Some (EvDeliver o).
Proof. simpl. rewrite proj_op_pair //. Qed.

(** [proj_ev t] is injective on its domain. *)
Lemma proj_ev_inj (t : TId) (e1 e2 : @Event DocOp) (e' : @Event Op) :
  proj_ev t e1 = Some e' -> proj_ev t e2 = Some e' -> e1 = e2.
Proof.
  move=> /proj_ev_Some H1 /proj_ev_Some H2.
  destruct H1 as [(o1 & -> & ->) | (o1 & -> & ->)];
    destruct H2 as [(o2 & -> & Heq) | (o2 & -> & Heq)]; try discriminate;
    by injection Heq as ->.
Qed.

(* ----- generic omap lemmas ----- *)

Lemma NoDup_omap_inj {X Y} (f : X -> option Y) (l : list X) :
  (∀ x1 x2 y, f x1 = Some y -> f x2 = Some y -> x1 = x2) ->
  NoDup l -> NoDup (omap f l).
Proof.
  move=> Hinj. elim: l => [| x l IH] Hnd /=; first constructor.
  move: Hnd. rewrite NoDup_cons. move=> [Hx Hnd].
  destruct (f x) as [y |] eqn:Hfx; last exact (IH Hnd).
  apply NoDup_cons_2; last exact (IH Hnd).
  rewrite list_elem_of_omap. move=> [x' [Hx' Hfx']].
  have Heq : x = x' := Hinj x x' y Hfx Hfx'.
  subst x'. exact (Hx Hx').
Qed.

(** [omap] on a cons, as an equation ([omap] is simpl-resistant here). *)
Lemma omap_cons {X Y : Type} (f : X -> option Y) (x : X) (l : list X) :
  omap f (x :: l) = match f x with Some y => y :: omap f l | None => omap f l end.
Proof. done. Qed.

(** Splitting an [omap] at one element reflects back to a split of the source
    (the generic form of the upstream [omap_deliver_cons_inv]). *)
Lemma omap_split {X Y} (f : X -> option Y) (l : list X) (l1 l2 : list Y) (y : Y) :
  omap f l = l1 ++ y :: l2 ->
  ∃ k1 x k2, l = k1 ++ x :: k2 ∧ f x = Some y ∧ omap f k1 = l1 ∧ omap f k2 = l2.
Proof.
  elim: l l1 => [| x l IH] l1 /= Heq.
  - by destruct l1.
  - destruct (f x) as [y' |] eqn:Hfx.
    + destruct l1 as [| z l1]; simpl in Heq.
      * injection Heq as -> Hsuf. exists [], x, l. by rewrite /= Hfx.
      * injection Heq as -> Heq.
        destruct (IH l1 Heq) as (k1 & x' & k2 & Hl & Hfx' & Hk1 & Hk2).
        exists (x :: k1), x', k2.
        split_and!; [by rewrite Hl | done | | done].
        rewrite omap_cons Hfx /= Hk1 //.
    + destruct (IH l1 Heq) as (k1 & x' & k2 & Hl & Hfx' & Hk1 & Hk2).
      exists (x :: k1), x', k2.
      split_and!; [by rewrite Hl | done | | done].
      rewrite omap_cons Hfx /= Hk1 //.
Qed.

(** Two-pivot version. *)
Lemma omap_split2 {X Y} (f : X -> option Y) (l : list X) (l1 l2 l3 : list Y) (y1 y2 : Y) :
  omap f l = l1 ++ [y1] ++ l2 ++ [y2] ++ l3 ->
  ∃ k1 x1 k2 x2 k3,
    l = k1 ++ [x1] ++ k2 ++ [x2] ++ k3 ∧ f x1 = Some y1 ∧ f x2 = Some y2 ∧
    omap f k1 = l1 ∧ omap f k2 = l2 ∧ omap f k3 = l3.
Proof.
  move=> Heq.
  destruct (omap_split f l l1 (l2 ++ y2 :: l3) y1 Heq)
    as (k1 & x1 & krest & Hl & Hfx1 & Hk1 & Hkrest).
  destruct (omap_split f krest l2 l3 y2 Hkrest)
    as (k2 & x2 & k3 & Hkr & Hfx2 & Hk2 & Hk3).
  exists k1, x1, k2, x2, k3.
  rewrite Hl Hkr. done.
Qed.

(* ----- deliver / projection commutation ----- *)

Lemma proj_deliver_comm (t : TId) (h : list (@Event DocOp)) :
  omap deliverP (proj_hist t h) = proj_ops t (omap deliverP h).
Proof.
  rewrite /proj_hist /proj_ops.
  elim: h => [| e h IH]; first done.
  rewrite !omap_cons.
  destruct e as [dop | dop] => /=.
  - destruct (proj_op t dop) as [o |] => /=; exact IH.
  - destruct (proj_op t dop) as [o |] => /=; [f_equal; exact IH | exact IH].
Qed.

(* ----- effect projection ----- *)

Lemma doc_effect_list_proj (l : list DocOp) (s s' : DocSt) (t : TId) :
  effect_list DocO l s s' ->
  effect_list O (proj_ops t l) (doc_get s t) (doc_get s' t).
Proof.
  elim: l s => [| dop l IH] s.
  - move=> /(effect_list_nil DocO) ->. by apply (effect_list_nil O).
  - move=> /(effect_list_cons DocO) [m [Hstep Hrest]].
    destruct Hstep as (st' & Heff & ->).
    rewrite /proj_ops omap_cons /proj_op.
    destruct (decide (dop.1 = t)) as [Heq | Hne].
    + subst t. apply (effect_list_cons O). exists st'.
      split; [exact Heff |].
      have -> : st' = doc_get (<[dop.1 := st']> s) dop.1 by rewrite doc_get_insert_eq.
      exact (IH _ Hrest).
    + have Hget : doc_get (<[dop.1 := st']> s) t = doc_get s t
        by rewrite doc_get_insert_ne //; congruence.
      rewrite -Hget. exact (IH _ Hrest).
Qed.

Lemma doc_interp_proj (h : list (@Event DocOp)) (s : DocSt) (t : TId) :
  interpHistory DocO h (op_init DocO) s ->
  interpHistory O (proj_hist t h) (op_init O) (doc_get s t).
Proof.
  rewrite /interpHistory proj_deliver_comm => Heff.
  have -> : op_init O = doc_get (op_init DocO) t by rewrite /= doc_get_empty.
  exact (doc_effect_list_proj _ _ _ _ Heff).
Qed.

(* ===== the doc operation network ========================================== *)

(** Doc-global per-client clock discipline: an op's clock strictly exceeds the
    clocks of all same-client items in *every* type of the replayed state. *)
Definition DocOperation_UniqueId (dop : DocOp) (s : DocSt) : Prop :=
  ∀ (t : TId) (x : YjsItem A), x ∈ st_items (doc_get s t) ->
    clientId (item_id x) = clientId (DocOp_id dop) ->
    (clock (item_id x) < clock (DocOp_id dop))%nat.

Local Notation DocOpNet := (@OperationNetwork DocOp YjsId DocOp_id DocO DocIsValidMessage).

(** The doc operation network: one network per document, ids doc-global. *)
Record DocOperationNetwork := {
  don_net :> DocOpNet;
  don_client_id : ∀ (e : DocOp) (i : ClientId),
    EvBroadcast e ∈ histories don_net i -> clientId (DocOp_id e) = i;
  don_UniqueId : ∀ (e : DocOp) (i : ClientId)
      (hist1 hist2 : list Event) (array : DocSt),
    histories don_net i = hist1 ++ [EvBroadcast e] ++ hist2 ->
    interpHistory DocO hist1 (op_init DocO) array ->
    DocOperation_UniqueId e array;
}.

(* ----- the per-type projection of a doc network ----- *)

Section proj_network.
Context (t : TId) (dn : DocOperationNetwork).

Lemma proj_hist_mem (e : @Event DocOp) (e' : @Event Op) (i : ClientId) :
  proj_ev t e = Some e' -> e ∈ histories dn i -> e' ∈ proj_hist t (histories dn i).
Proof.
  move=> Hp Hin. rewrite /proj_hist list_elem_of_omap. by exists e.
Qed.

Lemma proj_hist_mem_inv (e' : @Event Op) (i : ClientId) :
  e' ∈ proj_hist t (histories dn i) ->
  ∃ e : @Event DocOp, e ∈ histories dn i ∧ proj_ev t e = Some e'.
Proof.
  rewrite /proj_hist list_elem_of_omap. move=> [e [He Hp]]. by exists e.
Qed.

(** A local-order split of the projection lifts to a doc-level split. *)
Lemma proj_lo_lift (i : ClientId) (e1' e2' : @Event Op) :
  (∃ l1 l2 l3, proj_hist t (histories dn i) = l1 ++ [e1'] ++ l2 ++ [e2'] ++ l3) ->
  ∃ (e1 e2 : @Event DocOp),
    proj_ev t e1 = Some e1' ∧ proj_ev t e2 = Some e2' ∧
    locallyOrdered dn i e1 e2.
Proof.
  move=> [l1 [l2 [l3 Hsplit]]].
  destruct (omap_split2 (proj_ev t) _ l1 l2 l3 e1' e2' Hsplit)
    as (k1 & x1 & k2 & x2 & k3 & Hl & Hf1 & Hf2 & _ & _ & _).
  exists x1, x2. split_and!; [done | done |]. by exists k1, k2, k3.
Qed.

(** A doc-level split whose pivots survive the projection projects down. *)
Lemma proj_lo_down (i : ClientId) (e1 e2 : @Event DocOp) (e1' e2' : @Event Op) :
  proj_ev t e1 = Some e1' -> proj_ev t e2 = Some e2' ->
  locallyOrdered dn i e1 e2 ->
  ∃ l1 l2 l3, proj_hist t (histories dn i) = l1 ++ [e1'] ++ l2 ++ [e2'] ++ l3.
Proof.
  move=> Hp1 Hp2 [l1 [l2 [l3 Hsplit]]].
  exists (proj_hist t l1), (proj_hist t l2), (proj_hist t l3).
  rewrite Hsplit /proj_hist !omap_app !omap_cons Hp1 Hp2 /=. done.
Qed.

(** Happens-before of the projection lifts to the doc network, tagging with
    [t]. *)
Lemma proj_hb_lift (nb' : @NetworkBase Op YjsId opid) (x y : Op) :
  (∀ i, histories nb' i = proj_hist t (histories dn i)) ->
  HappensBefore opid nb' x y ->
  HappensBefore DocOp_id dn (t, x) (t, y).
Proof.
  move=> Hh Hhb.
  elim: Hhb => [i x' y' Hlo | i x' y' Hlo | x' y' z' _ IH1 _ IH2].
  - rewrite /locallyOrdered Hh in Hlo.
    destruct (proj_lo_lift i (EvBroadcast x') (EvBroadcast y') Hlo)
      as (e1 & e2 & Hp1 & Hp2 & Hlo').
    apply proj_ev_Some in Hp1. apply proj_ev_Some in Hp2.
    destruct Hp1 as [(o1 & -> & Heq1) | (o1 & _ & Heq1)]; [| discriminate].
    destruct Hp2 as [(o2 & -> & Heq2) | (o2 & _ & Heq2)]; [| discriminate].
    injection Heq1 as <-. injection Heq2 as <-.
    exact (hb_bb DocOp_id dn i (t, x') (t, y') Hlo').
  - rewrite /locallyOrdered Hh in Hlo.
    destruct (proj_lo_lift i (EvDeliver x') (EvBroadcast y') Hlo)
      as (e1 & e2 & Hp1 & Hp2 & Hlo').
    apply proj_ev_Some in Hp1. apply proj_ev_Some in Hp2.
    destruct Hp1 as [(o1 & _ & Heq1) | (o1 & -> & Heq1)]; [discriminate |].
    destruct Hp2 as [(o2 & -> & Heq2) | (o2 & _ & Heq2)]; [| discriminate].
    injection Heq1 as <-. injection Heq2 as <-.
    exact (hb_db DocOp_id dn i (t, x') (t, y') Hlo').
  - exact (hb_trans DocOp_id dn _ _ _ IH1 IH2).
Qed.

Program Definition proj_nodehistories : @NodeHistories Op :=
  {| histories := fun i => proj_hist t (histories dn i) |}.
Next Obligation.
  move=> i. apply NoDup_omap_inj; [| exact (event_distinct dn i)].
  move=> e1 e2 e' Hp1 Hp2. exact (proj_ev_inj t e1 e2 e' Hp1 Hp2).
Qed.

Program Definition proj_network_base : @NetworkBase Op YjsId opid :=
  {| nb_nodes := proj_nodehistories |}.
Next Obligation.
  (* deliver_has_a_cause *)
  move=> i e He.
  destruct (proj_hist_mem_inv (EvDeliver e) i He) as (ed & Hed & Hp).
  apply proj_ev_Some in Hp.
  destruct Hp as [(o & _ & Heq) | (o & -> & Heq)]; [discriminate |].
  injection Heq as <-.
  destruct (deliver_has_a_cause DocOp_id dn i (t, e) Hed) as (j & Hj).
  exists j. exact (proj_hist_mem _ _ j (proj_ev_broadcast t e) Hj).
Qed.
Next Obligation.
  (* deliver_locally (Gomes form: a broadcast is locally followed by its
     delivery) *)
  move=> i e He.
  destruct (proj_hist_mem_inv (EvBroadcast e) i He) as (ed & Hed & Hp).
  apply proj_ev_Some in Hp.
  destruct Hp as [(o & -> & Heq) | (o & _ & Heq)]; [| discriminate].
  injection Heq as <-.
  have Hlo := deliver_locally DocOp_id dn i (t, e) Hed.
  exact (proj_lo_down i _ _ _ _ (proj_ev_broadcast t e) (proj_ev_deliver t e) Hlo).
Qed.
Next Obligation.
  (* msg_id_unique *)
  move=> mi mj i j Hmi Hmj Hid.
  destruct (proj_hist_mem_inv (EvBroadcast mi) i Hmi) as (ei & Hei & Hpi).
  destruct (proj_hist_mem_inv (EvBroadcast mj) j Hmj) as (ej & Hej & Hpj).
  apply proj_ev_Some in Hpi. apply proj_ev_Some in Hpj.
  destruct Hpi as [(oi & -> & Heqi) | (oi & _ & Heqi)]; [| discriminate].
  destruct Hpj as [(oj & -> & Heqj) | (oj & _ & Heqj)]; [| discriminate].
  injection Heqi as <-. injection Heqj as <-.
  have Hid' : DocOp_id (t, mi) = DocOp_id (t, mj) by exact Hid.
  destruct (msg_id_unique DocOp_id dn (t, mi) (t, mj) i j Hei Hej Hid') as [Hij Heq].
  split; [exact Hij | by injection Heq].
Qed.

Program Definition proj_causal_network : @CausalNetwork Op YjsId opid :=
  {| cn_base := proj_network_base |}.
Next Obligation.
  (* causal_delivery *)
  move=> i e1 e2 Hdel Hhb.
  have Hhb' : HappensBefore DocOp_id dn (t, e1) (t, e2).
  { apply (proj_hb_lift proj_network_base); [done | exact Hhb]. }
  destruct (proj_hist_mem_inv (EvDeliver e2) i Hdel) as (ed & Hed & Hp).
  apply proj_ev_Some in Hp.
  destruct Hp as [(o & _ & Heq) | (o & -> & Heq)]; [discriminate |].
  injection Heq as <-.
  have Hlo := causal_delivery DocOp_id dn i (t, e1) (t, e2) Hed Hhb'.
  exact (proj_lo_down i _ _ _ _ (proj_ev_deliver t e1) (proj_ev_deliver t e2) Hlo).
Qed.

Program Definition proj_operation_network :
    @OperationNetwork Op YjsId opid O (@YjsIsValidMessage A) :=
  {| on_net := proj_causal_network |}.
Next Obligation.
  (* broadcast_only_valid_messages *)
  move=> i e pre post Hsplit.
  simpl in Hsplit.
  destruct (omap_split (proj_ev t) (histories dn i) pre post (EvBroadcast e) Hsplit)
    as (k1 & x & k2 & Hl & Hfx & Hk1 & Hk2).
  apply proj_ev_Some in Hfx.
  destruct Hfx as [(o & -> & Heq) | (o & -> & Heq)]; [| discriminate].
  injection Heq as <-.
  have Hl' : histories dn i = k1 ++ [EvBroadcast (t, e)] ++ k2 by rewrite Hl.
  destruct (broadcast_only_valid_messages DocOp_id DocO DocIsValidMessage dn i (t, e)
              k1 k2 Hl') as (s & Hinterp & Hvalid).
  exists (doc_get s t). split.
  - rewrite -Hk1. exact (doc_interp_proj k1 s t Hinterp).
  - exact Hvalid.
Qed.

Program Definition proj_network : YjsOperationNetwork (A := A) :=
  {| yon_net := proj_operation_network |}.
Next Obligation.
  (* histories_client_id *)
  move=> e i Hin.
  destruct (proj_hist_mem_inv (EvBroadcast e) i Hin) as (ed & Hed & Hp).
  apply proj_ev_Some in Hp.
  destruct Hp as [(o & -> & Heq) | (o & _ & Heq)]; [| discriminate].
  injection Heq as <-.
  exact (don_client_id dn (t, e) i Hed).
Qed.
Next Obligation.
  (* histories_UniqueId *)
  move=> e i hist1 hist2 array Hsplit Hinterp.
  simpl in Hsplit.
  destruct (omap_split (proj_ev t) (histories dn i) hist1 hist2 (EvBroadcast e) Hsplit)
    as (k1 & x & k2 & Hl & Hfx & Hk1 & Hk2).
  apply proj_ev_Some in Hfx.
  destruct Hfx as [(o & -> & Heq) | (o & -> & Heq)]; [| discriminate].
  injection Heq as <-.
  have Hl' : histories dn i = k1 ++ [EvBroadcast (t, e)] ++ k2 by rewrite Hl.
  (* replay the doc history over k1; its projection replays to [array] *)
  have Hex : ∃ sdoc, interpHistory DocO k1 (op_init DocO) sdoc.
  { destruct (broadcast_only_valid_messages DocOp_id DocO DocIsValidMessage dn i (t, e)
                k1 k2 Hl') as (sdoc & Hinterp' & _). by exists sdoc. }
  destruct Hex as (sdoc & Hinterpd).
  have Hproj := doc_interp_proj k1 sdoc t Hinterpd.
  rewrite /proj_hist Hk1 in Hproj.
  have Harr : array = doc_get sdoc t.
  { exact (effect_list_det (omap deliverP hist1) (op_init O) array (doc_get sdoc t)
             Hinterp Hproj). }
  have Huniq := don_UniqueId dn (t, e) i k1 k2 sdoc Hl' Hinterpd.
  move=> x' Hx' Hcx'.
  rewrite Harr in Hx'.
  exact (Huniq t x' Hx' Hcx').
Qed.

End proj_network.

(* ===== doc replay validity + convergence ================================== *)

Definition DocNetStateSource (dn : DocOperationNetwork) (a : DocOp) : Prop :=
  ∃ k, EvBroadcast a ∈ histories dn k.

(** Doc-level operation replay validity: for an insert into type [t], project
    the network and the replay to [t] and apply the upstream
    [isValidState_insert_from_source]. *)
Definition DocOperationReplayValidity (dn : DocOperationNetwork) :
  OperationReplayValidity DocO DocOV DocWithId
    (network_causal_order DocOp_id dn) (DocNetStateSource dn).
Proof.
  constructor => a s l Hsrc HsrcL Hlt Hcons Hclosed Heff Hnd.
  destruct a as [t op]. destruct op as [input | id did]; last exact I.
  apply (isValidState_insert_from_source (proj_network t dn) input (doc_get s t)
           (proj_ops t l)).
  - (* broadcast in the projected network *)
    destruct Hsrc as (k & Hk). exists k.
    exact (proj_hist_mem t dn _ _ k (proj_ev_broadcast t (OpInsert input)) Hk).
  - (* causal past covered by the projected list *)
    move=> x [Hle Hne].
    destruct Hle as [Heq | Hhb]; [by destruct Hne |].
    have Hhb' : HappensBefore DocOp_id dn (t, x) (t, OpInsert input).
    { apply (proj_hb_lift t dn (proj_network_base t dn)); [done | exact Hhb]. }
    have Hin : (t, x) ∈ l.
    { apply Hlt. split; [right; exact Hhb' | congruence]. }
    rewrite /proj_ops list_elem_of_omap. exists (t, x).
    split; [exact Hin | exact (proj_op_pair t x)].
  - (* sources *)
    move=> x. rewrite /proj_ops list_elem_of_omap. move=> [dop [Hdop Hp]].
    apply proj_op_Some in Hp. subst dop.
    destruct (HsrcL (t, x) Hdop) as (k & Hk). exists k.
    exact (proj_hist_mem t dn _ _ k (proj_ev_broadcast t x) Hk).
  - (* the projected replay *)
    have -> : op_init O = doc_get (op_init DocO) t by rewrite /= doc_get_empty.
    exact (doc_effect_list_proj l _ s t Heff).
Qed.

(* ----- doc-level structural facts, mirroring yjs_operation_network ----- *)

Lemma doc_same_history_not_hb_concurrent
    (cn : @CausalNetwork DocOp YjsId DocOp_id)
    (i : ClientId) (a b : DocOp) :
  EvBroadcast a ∈ histories cn i ->
  EvBroadcast b ∈ histories cn i ->
  ¬ hb_concurrent (network_causal_order DocOp_id cn) a b.
Proof.
  move=> Ha Hb [Hnab Hnba].
  case: (elem_of_two_split (histories cn i) (EvBroadcast a) (EvBroadcast b) Ha Hb)
    => [Hlo | [Hlo | Heq]].
  - apply: Hnab. right. exact (hb_bb DocOp_id cn i a b Hlo).
  - apply: Hnba. right. exact (hb_bb DocOp_id cn i b a Hlo).
  - apply: Hnab. left. congruence.
Qed.

Lemma doc_deliver_mem_of_toDeliver_mem (nh : @NodeHistories DocOp)
    (k : ClientId) (m : DocOp) :
  m ∈ toDeliverMessages nh k -> EvDeliver m ∈ histories nh k.
Proof.
  rewrite /toDeliverMessages list_elem_of_omap => -[ev [Hev Hdel]].
  destruct ev as [x | x]; simpl in Hdel; [done | injection Hdel as ->; exact Hev].
Qed.

Lemma doc_hb_concurrent_diff_id (dn : DocOperationNetwork) (i : ClientId)
    (a b : DocOp) :
  a ∈ toDeliverMessages dn i ->
  b ∈ toDeliverMessages dn i ->
  hb_concurrent (network_causal_order DocOp_id dn) a b ->
  clientId (DocOp_id a) ≠ clientId (DocOp_id b).
Proof.
  move=> Ha Hb Hconc Hcid.
  have HdA := doc_deliver_mem_of_toDeliver_mem dn i a Ha.
  have HdB := doc_deliver_mem_of_toDeliver_mem dn i b Hb.
  have [ia HbA] := deliver_has_a_cause DocOp_id dn i a HdA.
  have [ib HbB] := deliver_has_a_cause DocOp_id dn i b HdB.
  have HiA := don_client_id dn a ia HbA.
  have HiB := don_client_id dn b ib HbB.
  have Hii : ia = ib by rewrite -HiA -HiB Hcid.
  rewrite Hii in HbA.
  exact (doc_same_history_not_hb_concurrent dn ib a b HbA HbB Hconc).
Qed.

Lemma doc_toDeliver_mem_of_deliver_mem (nh : @NodeHistories DocOp)
    (k : ClientId) (m : DocOp) :
  EvDeliver m ∈ histories nh k -> m ∈ toDeliverMessages nh k.
Proof.
  move=> Hm. rewrite /toDeliverMessages list_elem_of_omap. by exists (EvDeliver m).
Qed.

(** The delivered list is happens-before-closed (doc-level copy of the
    upstream [toDeliverMessages_hbClosed], which is stated for Yjs ops). *)
Lemma doc_toDeliverMessages_hbClosed (cn : @CausalNetwork DocOp YjsId DocOp_id)
    (i : ClientId) :
  hbClosed (network_causal_order DocOp_id cn) (toDeliverMessages cn i).
Proof.
  have Hcons := hb_consistent_local_history DocOp_id cn i.
  move=> a b l1 l2 Heq Hlt.
  have Ha : a ∈ toDeliverMessages cn i by rewrite Heq; set_solver.
  have HdA := doc_deliver_mem_of_toDeliver_mem cn i a Ha.
  have Hhb : HappensBefore DocOp_id cn b a.
  { move: (proj1 Hlt) (proj2 Hlt) => [Heqab | Hhb'] Hne;
      [by case: Hne | exact Hhb']. }
  have Hlocal := causal_delivery DocOp_id cn i b a HdA Hhb.
  have HdB : EvDeliver b ∈ histories cn i
    by move: Hlocal => [p1 [p2 [p3 Hh]]]; rewrite Hh; set_solver.
  have Hb := doc_toDeliver_mem_of_deliver_mem cn i b HdB.
  have Hnotin : b ∉ l2.
  { move=> Hbin.
    apply: (hb_consistent_concurrent_r (network_causal_order DocOp_id cn) a l1 l2 _ b Hbin
              (proj1 Hlt)).
    by rewrite -Heq. }
  move: Hb. rewrite Heq elem_of_app elem_of_cons => -[Hb1 | [Hba | Hb2]].
  - exact Hb1.
  - by case: (proj2 Hlt).
  - by case: Hnotin.
Qed.

Lemma doc_toDeliverMessages_IdNoDup (cn : @CausalNetwork DocOp YjsId DocOp_id)
    (i : ClientId) :
  IdNoDup DocWithId (toDeliverMessages cn i).
Proof.
  rewrite /IdNoDup.
  apply: NoDup_fmap_inj_on; last exact (toDeliverMessages_Nodup DocOp_id cn i).
  move=> x y Hx Hy Hid.
  have Hdx := doc_deliver_mem_of_toDeliver_mem cn i x Hx.
  have Hdy := doc_deliver_mem_of_toDeliver_mem cn i y Hy.
  have [c1 Hbx] := deliver_has_a_cause DocOp_id cn i x Hdx.
  have [c2 Hby] := deliver_has_a_cause DocOp_id cn i y Hdy.
  have [_ Heq] := msg_id_unique DocOp_id cn x y c1 c2 Hbx Hby Hid.
  exact Heq.
Qed.

(** Doc-level network strong eventual consistency: two nodes of one doc
    network with the same delivered op set reach the same doc state — every
    root type's document agrees. *)
Theorem DocOperationNetwork_converge_final (dn : DocOperationNetwork)
    (i j : ClientId) (res0 res1 : DocSt) :
  effect_list DocO (toDeliverMessages dn i) (op_init DocO) res0 ->
  effect_list DocO (toDeliverMessages dn j) (op_init DocO) res1 ->
  (∀ m, m ∈ toDeliverMessages dn i <-> m ∈ toDeliverMessages dn j) ->
  res0 = res1.
Proof.
  move=> Heff0 Heff1 Hmem.
  have Heff1' : effect_list DocO (toDeliverMessages dn j) (op_init DocO) res0.
  { apply: (doc_strong_convergence (network_causal_order DocOp_id dn)
              (DocNetStateSource dn) (DocOperationReplayValidity dn)
              (toDeliverMessages dn i) (toDeliverMessages dn j) res0).
    - move=> x Hx. have Hd := doc_deliver_mem_of_toDeliver_mem dn i x Hx.
      have [c Hc] := deliver_has_a_cause DocOp_id dn i x Hd. by exists c.
    - move=> x Hx. have Hd := doc_deliver_mem_of_toDeliver_mem dn j x Hx.
      have [c Hc] := deliver_has_a_cause DocOp_id dn j x Hd. by exists c.
    - exact (hb_consistent_local_history DocOp_id dn i).
    - exact (hb_consistent_local_history DocOp_id dn j).
    - exact (doc_toDeliverMessages_hbClosed dn i).
    - exact (doc_toDeliverMessages_hbClosed dn j).
    - move=> a b Ha Hb Hconc. exact (doc_hb_concurrent_diff_id dn i a b Ha Hb Hconc).
    - exact (doc_toDeliverMessages_IdNoDup dn i).
    - exact (doc_toDeliverMessages_IdNoDup dn j).
    - exact Hmem.
    - exact Heff0. }
  exact (doc_effect_list_det (toDeliverMessages dn j) (op_init DocO) res0 res1 Heff1' Heff1).
Qed.

End doc_model.
