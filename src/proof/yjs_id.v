(** WP specs for the [id] type (yjs/id.go) and the model-id equality bridge.

    The smallest leaf proofs the integrate / insert development builds on:
    [newId] / [Id.Add] / [Id.Sub] and the [Sub]-undoes-[Add] round-trip, the
    injectivity of [toYjsId] and its [bool_decide] bridge ([toYjsId_inj] /
    [Id_eqb_toYjsId]), and the equality specs [Id.Equal] / [idOptEqual] that the
    conflict scan tests ids with. The shared scalar abstractions
    ([toYjsId] / [is_origin_id]) come from [yjs_common]. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import yjs_core.
From New.proof Require Import yjs_common.

Section id.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

(* ----- Id ----------------------------------------------------------------- *)

(* NewId builds the expected struct value. *)
Lemma wp_NewId (client clock : w64) :
  {{{ is_pkg_init yjs }}}
    @! yjs.newId #client #clock
  {{{ RET #(yjs.id.mk client clock); True }}}.
Proof.
  wp_start. wp_auto. iApply "HΦ". done.
Qed.

(* Add advances the clock; the client is untouched. *)
Lemma wp_Id__Add (id : yjs.id.t) (n : w64) :
  {{{ is_pkg_init yjs }}}
    id @! yjs.id @! "Add" #n
  {{{ RET #(yjs.id.mk id.(yjs.id.clientId') (word.add id.(yjs.id.clock') n)); True }}}.
Proof.
  wp_start. wp_auto. iApply "HΦ". done.
Qed.

(* Sub rewinds the clock; the client is untouched. *)
Lemma wp_Id__Sub (id : yjs.id.t) (n : w64) :
  {{{ is_pkg_init yjs }}}
    id @! yjs.id @! "Sub" #n
  {{{ RET #(yjs.id.mk id.(yjs.id.clientId') (word.sub id.(yjs.id.clock') n)); True }}}.
Proof.
  wp_start. wp_auto. iApply "HΦ". done.
Qed.

(* Functional-correctness round-trip: Sub undoes Add (machine-word level,
   holds unconditionally because subtraction is the inverse of addition mod
   2^64). This is the kind of property the foundation lets us state. *)
Lemma id_add_sub_roundtrip (id : yjs.id.t) (n : w64) :
  yjs.id.mk
    (yjs.id.mk id.(yjs.id.clientId') (word.add id.(yjs.id.clock') n)).(yjs.id.clientId')
    (word.sub (yjs.id.mk id.(yjs.id.clientId') (word.add id.(yjs.id.clock') n)).(yjs.id.clock') n)
  = id.
Proof.
  destruct id as [c k]. simpl. f_equal. word.
Qed.

(* ----- Id / set helper specs (model-id equality bridge) ------------------ *)

(** [toYjsId] is injective (it is [uint.nat] on both [w64] fields), so heap id
    equality matches model id equality — the bridge between the Go id ops and
    the pure [gset] tests. *)
Lemma toYjsId_inj (a b : yjs.id.t) : toYjsId a = toYjsId b -> a = b.
Proof.
  destruct a as [ca ka], b as [cb kb]. rewrite /toYjsId /=.
  injection 1 as Hc Hk. f_equal; word.
Qed.

(** [Id.Equal] computes the conjunction of the two field equalities; this is
    exactly [bool_decide] of the model id equality. *)
Lemma Id_eqb_toYjsId (a b : yjs.id.t) :
  (bool_decide (a.(yjs.id.clientId') = b.(yjs.id.clientId'))
   && bool_decide (a.(yjs.id.clock') = b.(yjs.id.clock')))%bool
  = bool_decide (toYjsId a = toYjsId b).
Proof.
  rewrite -bool_decide_and. apply bool_decide_ext. rewrite /toYjsId. split.
  - move=> [Hc Hk]. by rewrite Hc Hk.
  - move=> H. injection H => Hk Hc. split; word.
Qed.

(* ----- WP specs for the id / set helper functions ------------------------ *)

Lemma wp_Id__Equal (a b : yjs.id.t) :
  {{{ is_pkg_init yjs }}}
    a @! yjs.id @! "Equal" #b
  {{{ RET #(bool_decide (toYjsId a = toYjsId b)); True }}}.
Proof.
  wp_start as "_". wp_auto. wp_if_destruct.
  - have -> : bool_decide (a.(yjs.id.clock') = b.(yjs.id.clock'))
             = bool_decide (toYjsId a = toYjsId b).
    { rewrite -Id_eqb_toYjsId. by rewrite (bool_decide_eq_true_2 _ e). }
    iApply "HΦ". done.
  - have Hf : bool_decide (toYjsId a = toYjsId b) = false.
    { apply bool_decide_eq_false_2 => H. apply n. by rewrite (toYjsId_inj _ _ H). }
    iEval (rewrite Hf) in "HΦ". iApply "HΦ". done.
Qed.

(** [idOptEqual] on two optional-id pointers ([is_origin_id]) decides equality of
    the abstract model ids. (Both origin facts are persistent, so kept.) *)
Lemma wp_idOptEqual (pa pb : loc) (oa ob : option yjs.id.t) :
  {{{ is_pkg_init yjs ∗ is_origin_id pa oa ∗ is_origin_id pb ob }}}
    @! yjs.idOptEqual #pa #pb
  {{{ RET #(bool_decide ((toYjsId <$> oa) = (toYjsId <$> ob))); True }}}.
Proof.
  wp_start as "[Ha Hb]". wp_auto.
  destruct oa as [ida|]; destruct ob as [idb|].
  - iDestruct "Ha" as "[%Hpa Hpa]". iDestruct "Hb" as "[%Hpb Hpb]".
    rewrite (bool_decide_eq_false_2 (pa = null) Hpa). wp_auto.
    rewrite (bool_decide_eq_false_2 (pa = null) Hpa). wp_auto.
    rewrite (bool_decide_eq_false_2 (pb = null) Hpb). wp_auto.
    wp_method_call; wp_call; wp_auto. wp_apply (wp_Id__Equal ida idb).
    have Heq : bool_decide (toYjsId <$> Some ida = toYjsId <$> Some idb)
             = bool_decide (toYjsId ida = toYjsId idb).
    { apply bool_decide_ext. simpl. by split; congruence. }
    iEval (rewrite Heq) in "HΦ". iApply "HΦ". done.
  - iDestruct "Ha" as "[%Hpa Hpa]". iDestruct "Hb" as "%Hpb". subst pb.
    rewrite (bool_decide_eq_false_2 (pa = null) Hpa). wp_auto.
    rewrite (bool_decide_eq_false_2 (pa = null) Hpa). wp_auto.
    iApply "HΦ". done.
  - iDestruct "Ha" as "%Hpa". iDestruct "Hb" as "[%Hpb Hpb]". subst pa.
    wp_auto. rewrite (bool_decide_eq_false_2 (pb = null) Hpb). wp_auto.
    iApply "HΦ". done.
  - iDestruct "Ha" as "%Hpa". iDestruct "Hb" as "%Hpb". subst pa pb.
    wp_auto. iApply "HΦ". done.
Qed.

End id.
