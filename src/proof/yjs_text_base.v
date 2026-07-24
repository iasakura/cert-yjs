(** Text handle, shared base: [insert_item_valid] / [insert_maximalId] /
    [sorted_subseteq_*] helpers and the [is_Text] invariant with its
    [is_Text_root] / [is_Text_root_lb] projections. Split out of [yjs_text]
    so [wp_Text__Insert] and [wp_Text__Delete] proof-check in parallel;
    consumed through the [yjs_text] facade. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import yjs_core.
From New.proof Require Import yjs_common yjs_id yjs_item yjs_ytype yjs_history yjs_store.
From New.proof.sync_proof Require Import mutex.        (* transitive; the store's
                                                          RWMutex write lock is taken
                                                          via [wp_Store__wlock] /
                                                          [wp_Store__wunlock] (yjs_store) *)
From iris.algebra Require Import auth gmap gset.        (* is_type_lb grow-only item-set RA *)
From iris.algebra.lib Require Import dfrac_agree.       (* [is_Store]'s reader-count [types] agreement *)
From stdpp Require Import sorting.                      (* StronglySorted / sublist *)

(* iris.algebra / stdpp.sorting push [nat_scope], retuning the default [<] / [≤];
   the verified word-arithmetic proofs write [Z] comparisons unannotated, so
   restore [Z_scope] as the default. *)
Local Open Scope Z_scope.

Section text.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.
(** Store lock = a [sync.RWMutex] (write path here, via [wp_Store__wlock] /
    [wp_Store__wunlock]); the per-text item set lives in a grow-only auth
    (the same RA as [yjs_store], used by [is_type_lb]). *)
Context {sync_pkg : sync.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.
Context {seq_inG : inG Σ (authR (gmapUR loc (gsetUR (YjsItem A))))}.
(* [is_Store]'s reader-count accounting ties the readers' share to the store's
   [types] map via a [dfrac_agree]; threaded here so [is_Text]/[is_Store] uses
   in this file (Insert/Delete/Len) can discharge the instance. *)
Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO (gmap loc type_state)))}.

(* The ghost op-history types at the document content type; type names are Go
   strings (issue #49). *)
Local Notation P := go_string.
Local Notation TId := (TypeId P).
Local Notation Op := (TId * @YjsOperation A)%type.
Local Notation Ev := (@Event Op).
Local Notation DocModel := (gmap TId (list (YjsItem A))).

(** The item [Text.Insert] builds at the straddle point is valid. Repackages
    [item_valid_at] over the exact origin facts [findPos] yields (a left/right
    neighbour by id, or the [First]/[Last] boundary), so the WP proof discharges
    [IsItemValid] in one application. *)
Lemma insert_item_valid (arr : list (YjsItem A)) (p : nat) (newid : YjsId) (c : A)
    (o r : YjsPtr A) (originIdLeft originIdRight : option YjsId) :
  YjsArrInvariant arr ->
  (originIdLeft = None /\ o = First /\ p = 0%nat
     \/ ∃ li, (1 <= p)%nat /\ arr !! (p - 1)%nat = Some li /\ originIdLeft = Some (item_id li) /\ o = itemPtr li) ->
  (originIdRight = None /\ r = Last /\ p = length arr
     \/ ∃ ri, arr !! p = Some ri /\ originIdRight = Some (item_id ri) /\ r = itemPtr ri) ->
  IsItemValid (Item o r newid c).
Proof.
  intros Hinv Hleft Hright.
  apply (item_valid_at arr p newid c o r Hinv).
  - destruct Hleft as [(_ & Ho & Hp0) | (li & Hge & Hla & _ & Ho)];
      [left; split; [exact Hp0 | exact Ho]
      | right; split; [exact Hge | exists li; split; [exact Hla | exact Ho]]].
  - destruct Hright as [(_ & Hr & Hpl) | (ri & Hria & _ & Hr)];
      [left; split; [exact Hpl | exact Hr]
      | right; exists ri; split; [exact Hria | exact Hr]].
Qed.

(** The fresh item is maximal among same-client items of [arr]: its clock [clk]
    exceeds every same-client clock already present. This is the [maximalId] side
    condition of [wp_Store__Integrate], read off the Doc clock-counter invariant. *)
Lemma insert_maximalId (arr : list (YjsItem A)) (o r : YjsPtr A) (client clk : nat) (c : A) :
  (∀ x, ArrSet arr (itemPtr x) -> clientId (item_id x) = client -> (clock (item_id x) < clk)%nat) ->
  maximalId (Item o r (MkYjsId client clk) c) arr.
Proof. intros Hctr x Hx Hc. exact (Hctr x Hx Hc). Qed.


(** Two lists [StronglySorted] by the document order [YjsLt'], with [l1]'s
    elements ⊆ [l2]'s (as actual items) and [l2] a valid [YjsArrInvariant] list,
    force [l1] to be a [sublist] of [l2]. The order is a strict order on [l2]'s
    items ([yjs_lt_asymm], hence irreflexive + asymmetric), so the relative
    position of any shared item is forced; the [aux] form keeps the asymmetry
    fact about the FIXED valid set [S = (∈ l2)] as the induction peels [l2]. This
    is what upgrades the item-set lower bound ([list_to_set L ⊆ list_to_set L'])
    into the [sublist L L'] the [Text.Insert] post advertises. *)
Lemma sorted_subseteq_sublist_aux {B : Type} `{EqDecision B} (S : YjsItem B -> Prop)
    (Hasym : ∀ x y, S x -> S y -> YjsLt' (itemPtr x) (itemPtr y) -> YjsLt' (itemPtr y) (itemPtr x) -> False) :
  ∀ (l2 l1 : list (YjsItem B)),
  (∀ x, x ∈ l2 -> S x) ->
  StronglySorted (λ x y : YjsItem B, YjsLt' (itemPtr x) (itemPtr y)) l1 ->
  StronglySorted (λ x y : YjsItem B, YjsLt' (itemPtr x) (itemPtr y)) l2 ->
  (∀ x, x ∈ l1 -> x ∈ l2) ->
  sublist l1 l2.
Proof.
  intros l2. induction l2 as [|y l2' IH]; intros l1 HS Hss1 Hss2 Hsub.
  - destruct l1 as [|x l1']; [apply sublist_nil|].
    exfalso. have Hx : x ∈ ([] : list (YjsItem B)) by (apply Hsub; left). inversion Hx.
  - apply StronglySorted_inv in Hss2 as [Hss2' Hy].
    destruct l1 as [|x l1']; [apply sublist_nil_l|].
    apply StronglySorted_inv in Hss1 as [Hss1' Hx].
    destruct (decide (x = y)) as [->|Hne].
    + apply sublist_skip. apply (IH l1').
      * intros z Hz. apply HS. right. exact Hz.
      * exact Hss1'.
      * exact Hss2'.
      * intros z Hz.
        have Hzl2 : z ∈ (y :: l2') by (apply Hsub; right; exact Hz).
        apply elem_of_cons in Hzl2 as [-> | Hz']; [|exact Hz'].
        exfalso. rewrite Forall_forall in Hx.
        have Ryy : YjsLt' (itemPtr y) (itemPtr y) by (apply Hx; exact Hz).
        apply (Hasym y y); [apply HS; left; reflexivity | apply HS; left; reflexivity | exact Ryy | exact Ryy].
    + apply sublist_cons. apply (IH (x :: l1')).
      * intros z Hz. apply HS. right. exact Hz.
      * constructor; [exact Hss1' | exact Hx].
      * exact Hss2'.
      * intros z Hz.
        have Hzl2 : z ∈ (y :: l2') by (apply Hsub; exact Hz).
        apply elem_of_cons in Hzl2 as [-> | Hz']; [|exact Hz'].
        exfalso.
        apply elem_of_cons in Hz as [Hzx | Hzl1'].
        { apply Hne. symmetry. exact Hzx. }
        have Hxl2 : x ∈ (y :: l2') by (apply Hsub; left).
        apply elem_of_cons in Hxl2 as [Hxy | Hxl2'].
        { apply Hne. exact Hxy. }
        rewrite Forall_forall in Hx. rewrite Forall_forall in Hy.
        have Rxy : YjsLt' (itemPtr x) (itemPtr y) by (apply Hx; exact Hzl1').
        have Ryx : YjsLt' (itemPtr y) (itemPtr x) by (apply Hy; exact Hxl2').
        apply (Hasym x y); [apply HS; right; exact Hxl2' | apply HS; left; reflexivity | exact Rxy | exact Ryx].
Qed.

Lemma sorted_subseteq_sublist {B : Type} `{EqDecision B} (l1 l2 : list (YjsItem B)) :
  YjsArrInvariant l2 ->
  StronglySorted (λ x y : YjsItem B, YjsLt' (itemPtr x) (itemPtr y)) l1 ->
  StronglySorted (λ x y : YjsItem B, YjsLt' (itemPtr x) (itemPtr y)) l2 ->
  (∀ x, x ∈ l1 -> x ∈ l2) ->
  sublist l1 l2.
Proof.
  intros Hinv Hss1 Hss2 Hsub.
  apply (sorted_subseteq_sublist_aux (λ x, x ∈ l2)); [| intros x Hx; exact Hx | exact Hss1 | exact Hss2 | exact Hsub].
  intros x y Hx Hy Rxy Ryx.
  exact (asymmetry.yjs_lt_asymm (yai_closed _ Hinv) (yai_item_set_inv _ Hinv) (itemPtr x) (itemPtr y) Hx Hy Rxy Ryx).
Qed.

(* ----- Text invariant predicate + Text.Insert spec ----------------------
   [is_Text] lives here; the Doc-layer predicate [is_Doc] lives in yjs_doc.v
   (mirrors doc.go). [is_Text] delegates straight to the store invariants
   ([is_Store] / [is_type_lb]) in yjs_store, referencing only Text's own fields.
   [wp_Text__Insert] is proved (Lock → store_inv → findPos/Integrate loop → grow
   the item-set auth → Unlock). *)

(** Text handle (persistent), parameterized by a SORTED list [L] of known items:
    reads ONLY its OWN fields ([store]/[inner], immutable ⇒ [↦□]) and delegates
    straight to [is_Store] (no Doc hop — Text holds [store] directly). The ghost
    is fed the item-SET of [L] ([is_type_lb] over [gset (YjsItem A)], a subset
    lower bound — grow-only, no [mra] needed), while [L] is required
    [StronglySorted] by the document order [YjsLt'] (the order
    [YjsArrInvariant.yai_sorted] uses). Tracking full items (not just ids) pins
    each [x ∈ L] to a genuine document item, so [L] is a real CRDT-ordered
    sub-sequence of the current content (a directly-readable [sublist]/string
    lower bound). Says NOTHING about store fields. Persistent ⇒ the [Insert] spec
    is pre/post in the same predicate (with [L] growing).

    Network layer (issues #42/#49): the handle also carries the (persistent)
    ghost op-history handle [is_history γh] and its root-type binding
    [is_type_binding] — the handle's text is the one the store's registry
    binds to [name], which is what ties the store's per-type history view to
    THIS text under the lock. *)
Definition is_Text (t : loc) (γs : store_names) (γh : history_names) (name : P) (L : list (YjsItem A)) : iProp Σ :=
  ∃ (tv : yjs.Text.t) (s_loc parent : loc),
    "Ht" ∷ t ↦□ tv ∗
    "%Hstore" ∷ ⌜tv.(yjs.Text.store') = s_loc⌝ ∗
    "%Hinner" ∷ ⌜tv.(yjs.Text.inner') = parent⌝ ∗
    "His_store" ∷ is_Store s_loc γs γh ∗
    "#His_hist" ∷ is_history (A := A) (P := P) γh ∗
    "#Hbind" ∷ is_type_binding γs.(sn_types) name parent ∗
    "His_lb" ∷ is_type_lb γs.(sn_seq) parent (list_to_set L) ∗
    "%Hsorted" ∷ ⌜StronglySorted (λ x y : YjsItem A, YjsLt' (itemPtr x) (itemPtr y)) L⌝.

#[global] Instance is_Text_persistent t γs γh name L : Persistent (is_Text t γs γh name L).
Proof. apply _. Qed.

(** A Text handle certifies its root at the store level: the name is
    registered ([is_root]) and the handle's known content is a lower bound
    of the root's item set ([is_root_lb]), with the handle's inner pointer
    as the hidden binding witness. These are the projections that let a
    Text-handle holder feed the [applyUpdate] certificate spec (its
    [is_root] precondition) and compare its content bound against the
    [is_root_lb] certificates the spec returns. [is_Text] itself keeps the
    binding and the lower bound as separate conjuncts because it must also
    pin the binding's loc to the handle's [inner] field. *)
Lemma is_Text_root (t : loc) (γs : store_names) (γh : history_names)
    (name : P) (L : list (YjsItem A)) :
  is_Text t γs γh name L -∗ is_root γs name.
Proof. iIntros "H". iNamed "H". iExists _. iFrame "Hbind". Qed.

Lemma is_Text_root_lb (t : loc) (γs : store_names) (γh : history_names)
    (name : P) (L : list (YjsItem A)) :
  is_Text t γs γh name L -∗ is_root_lb γs name (list_to_set L).
Proof. iIntros "H". iNamed "H". iExists _. iFrame "Hbind His_lb". Qed.

(** [Text.Insert] preserves the (persistent) document handle, grows the known
    content ([L ⊑ L']), AND exposes the inserted run [ins]: one fresh item per
    byte of [content], each now known ([∈ L'], and [∉ L] since its id is fresh),
    carrying that byte as content, with a fresh id [(client, k0+i)] (one local
    [client], consecutive clocks from some [k0]), the run's shared right origin
    [originRight], and its left origin chained (item 0 from [originLeft], item i+1 from item i).
    This says exactly "the characters you inserted are in [L'−L], with these
    content / id / left / right".

    Proof shape: peel [is_Text → is_Store] and take the RWMutex write lock
    ([wp_Store__wlock]), which yields [store_inv]; combine [is_type_lb] with
    [Hseq] (auth) via
    [auth_gmap_gset_lookup] to learn [parent ∈ dom types] and extract THIS text's
    [type_state] / DLL from [Htypes]; run the findPos/Integrate loop, whose
    invariant accumulates [ins] with the per-byte facts (content/id/origins) plus
    [ty_arr ts ⊆ arr]; at exit grow the auth item-set ([ty_arr ts → arr]) with
    [auth_gmap_gset_grow] and mint the new [is_type_lb]; reinsert the grown text
    into [Htypes] ([big_sepM_insert_acc]); rebuild [store_inv] (clock bumped,
    counter [Hctr] preserved); [Unlock]; return with [L' = arr]. The post's
    [sublist L L'] follows from [sorted_subseteq_sublist] (both sorted, [L ⊆ L']
    as items via the item-set ghost), and [it ∉ L] from the fresh clocks vs the
    initial [Hctr]. Overflow is ruled out by a Go-side guard in [Text.Insert]
    (its early return takes the [ins = []] disjunct); [k] stays hidden in the
    lock. Axiom-clean ([Print Assumptions] shows only goose/Perennial axioms). *)
End text.
