(* Basic per-method WP specs for the leaf [id] / [item] operations of yjs/yjs.go.

   The goose-translated model of the core data structures (Id, Content, Item,
   Store, ...) is in New.code.github_com.iasakura.cert_yjs.yjs; this module
   proves the small, structure-free method specs the integrate / insert proofs
   build on: Id arithmetic ([Add]/[Sub]) and equality ([Equal]/[idOptEqual]),
   item-pointer comparison ([itemPtrEqual]), and the per-node accessors
   ([gcNode] projections, item [Indexable]/[Len]/[Deleted]). The shared scalar
   abstractions ([toYjsId]/[oid_of]/[item_or_null]) come from [yjs_common]. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import yjs_core.
From New.proof Require Import yjs_common.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.

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

(* ----- Node interface impls ----------------------------------------------- *)

(* The Node accessors read out of the embedded NodeLen / Item; here we pin down
   the GC-node projections, which the store's binary search relies on. *)
Lemma wp_GCNode__clock (n : yjs.gcNode.t) :
  {{{ is_pkg_init yjs }}}
    n @! yjs.gcNode @! "clock" #()
  {{{ RET #(n.(yjs.gcNode.nodeLen').(yjs.nodeLen.id').(yjs.id.clock')); True }}}.
Proof.
  wp_start. wp_auto. iApply "HΦ". done.
Qed.

Lemma wp_GCNode__length (n : yjs.gcNode.t) :
  {{{ is_pkg_init yjs }}}
    n @! yjs.gcNode @! "length" #()
  {{{ RET #(n.(yjs.gcNode.nodeLen').(yjs.nodeLen.len')); True }}}.
Proof.
  wp_start. wp_auto. iApply "HΦ". done.
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

(** [itemPtrEqual] compares two item pointers by identity (= model id, ids being
    unique), with the null cases of y-octo's [Somr] comparison. *)
Lemma wp_itemPtrEqual (pa pb : loc) (ova ovb : option yjs.item.t) (dqa dqb : dfrac) :
  {{{ is_pkg_init yjs ∗ item_or_null pa ova dqa ∗ item_or_null pb ovb dqb }}}
    @! yjs.itemPtrEqual #pa #pb
  {{{ RET #(bool_decide (oid_of ova = oid_of ovb));
      item_or_null pa ova dqa ∗ item_or_null pb ovb dqb }}}.
Proof.
  wp_start as "[Ha Hb]". wp_auto.
  destruct ova as [va|]; destruct ovb as [vb|].
  - iDestruct "Ha" as "[%Hpa Hpa]". iDestruct "Hb" as "[%Hpb Hpb]".
    rewrite (bool_decide_eq_false_2 (pa = null) Hpa). wp_auto.
    rewrite (bool_decide_eq_false_2 (pa = null) Hpa). wp_auto.
    rewrite (bool_decide_eq_false_2 (pb = null) Hpb). wp_auto.
    wp_method_call; wp_call; wp_auto.
    wp_apply (wp_Id__Equal va.(yjs.item.id') vb.(yjs.item.id')).
    have Heq : bool_decide (oid_of (Some va) = oid_of (Some vb))
             = bool_decide (toYjsId va.(yjs.item.id') = toYjsId vb.(yjs.item.id')).
    { apply bool_decide_ext. rewrite /oid_of /=. by split; congruence. }
    iEval (rewrite Heq) in "HΦ". iApply "HΦ". rewrite /item_or_null. iFrame.
    iSplit; iPureIntro; assumption.
  - iDestruct "Ha" as "[%Hpa Hpa]". iDestruct "Hb" as "%Hpb". subst pb.
    rewrite (bool_decide_eq_false_2 (pa = null) Hpa). wp_auto.
    rewrite (bool_decide_eq_false_2 (pa = null) Hpa). wp_auto.
    iApply "HΦ". rewrite /item_or_null. iFrame.
    iSplit; iPureIntro; [assumption | reflexivity].
  - iDestruct "Ha" as "%Hpa". iDestruct "Hb" as "[%Hpb Hpb]". subst pa.
    wp_auto. rewrite (bool_decide_eq_false_2 (pb = null) Hpb). wp_auto.
    iApply "HΦ". rewrite /item_or_null. iFrame.
    iSplit; iPureIntro; [reflexivity | assumption].
  - iDestruct "Ha" as "%Hpa". iDestruct "Hb" as "%Hpb". subst pa pb.
    wp_auto. iApply "HΦ". rewrite /item_or_null. iSplit; iPureIntro; reflexivity.
Qed.

(* ----- per-node accessors read by yText.findPos -------------------------- *)

(** Per-node method specs [findPos] reads off each cursor node. Every cell is
    [flags' = W8 2] (Countable, not Deleted) with single-byte content, so
    [Indexable] is [true] and [Len] is the content byte length (1 for our
    cells). Proving these once keeps the [findPos] loop free of nested
    method-call stepping. *)
Lemma wp_item__Indexable (l : loc) (v : yjs.item.t) :
  v.(yjs.item.flags') = W8 2 ->
  {{{ is_pkg_init yjs ∗ l ↦ v }}}
    l @! (go.PointerType yjs.item) @! "Indexable" #()
  {{{ RET #true; l ↦ v }}}.
Proof.
  intros Hflags.
  wp_start as "Hl".
  wp_auto.
  wp_method_call. wp_call. rewrite /yjs.item__Indexableⁱᵐᵖˡ. wp_auto.
  wp_method_call. wp_call. wp_auto.
  wp_method_call. wp_call. rewrite /yjs.item__Countableⁱᵐᵖˡ. wp_auto.
  wp_alloc i2 as "Hi2". wp_auto. rewrite Hflags.
  have Hand2 : w8_word_instance.(word.and) (W8 2) (W8 2) = W8 2 by reflexivity.
  rewrite Hand2. rewrite bool_decide_eq_false_2; [| done]. simpl negb. wp_auto.
  have Hand : w8_word_instance.(word.and) (W8 2) (W8 4) = W8 0 by reflexivity.
  wp_method_call. wp_call. wp_auto.
  wp_method_call. wp_call. rewrite /yjs.item__Deletedⁱᵐᵖˡ. wp_auto.
  rewrite Hflags Hand (bool_decide_eq_true_2 (W8 0 = W8 0) eq_refl) /=.
  iApply "HΦ". iFrame "Hl".
Qed.

Lemma wp_item__Len (l : loc) (v : yjs.item.t) :
  {{{ is_pkg_init yjs ∗ l ↦ v }}}
    l @! (go.PointerType yjs.item) @! "Len" #()
  {{{ RET #(W64 (length (v.(yjs.item.content').(yjs.content.content')))); l ↦ v }}}.
Proof.
  wp_start as "Hl". wp_auto.
  wp_method_call. wp_call. rewrite /yjs.item__Lenⁱᵐᵖˡ. wp_auto.
  wp_method_call. wp_call. rewrite /yjs.content__Lenⁱᵐᵖˡ. wp_auto.
  wp_method_call. wp_call. rewrite /yjs.content__Lenⁱᵐᵖˡ. wp_auto.
  wp_apply strings.wp_string_len. iIntros "_". wp_auto.
  iApply "HΦ". iFrame "Hl".
Qed.

Lemma wp_item__Deleted (l : loc) (v : yjs.item.t) :
  v.(yjs.item.flags') = W8 2 ->
  {{{ is_pkg_init yjs ∗ l ↦ v }}}
    l @! (go.PointerType yjs.item) @! "Deleted" #()
  {{{ RET #false; l ↦ v }}}.
Proof.
  intros Hflags. wp_start as "Hl". wp_auto.
  wp_method_call. wp_call. rewrite /yjs.item__Deletedⁱᵐᵖˡ. wp_auto. rewrite Hflags.
  have Hand : w8_word_instance.(word.and) (W8 2) (W8 4) = W8 0 by reflexivity.
  rewrite Hand (bool_decide_eq_true_2 (W8 0 = W8 0) eq_refl) /=.
  iApply "HΦ". iFrame "Hl".
Qed.

End proof.
