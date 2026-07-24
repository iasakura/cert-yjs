(** WP proofs for the [Text] handle: the top-level [Text.Insert] (the lock-based
    per-byte Integrate loop) and [Text.Delete] (tombstoning a visible run). The
    visible-index navigation [yType.findPos] they call lives in [yjs_ytype].

    [is_Text] is the Text-handle invariant, delegating to the store lock
    ([is_Store] / [is_type_lb] in [yjs_store]); [wp_yType__findPos] and the
    [insert_item_valid] / [insert_maximalId] helpers feed [wp_Text__Insert]. *)
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
Local Notation DocM := (gmap TId (list (YjsItem A))).

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
    [oR], and its left origin chained (item 0 from [oL], item i+1 from item i).
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
Lemma wp_Text__Insert (t : loc) (idx : w64) (cs : go_string) (γs : store_names) (γh : history_names)
    (name : P) (L : list (YjsItem A)) :
  {{{ is_pkg_init yjs ∗ is_Text t γs γh name L }}}
    t @! (go.PointerType yjs.Text) @! "Insert" #idx #cs
  {{{ (L' ins : list (YjsItem A)) (client k0 : nat) (oL oR : YjsPtr A), RET #();
      is_Text t γs γh name L' ∗ ⌜sublist L L'⌝ ∗
      ⌜ins = [] ∨ length ins = length cs⌝ ∗
      ⌜∀ (i : nat) (it : YjsItem A) (b : w8),
         ins !! i = Some it → cs !! i = Some b →
           it ∈ L' ∧ it ∉ L ∧
           content it = [b] ∧
           item_id it = MkYjsId client (k0 + i)%nat ∧
           rightOrigin it = oR ∧
           (i = 0%nat → origin it = oL) ∧
           (∀ (j : nat) (itj : YjsItem A),
              i = S j → ins !! j = Some itj → origin it = itemPtr itj)⌝ ∗
      (* the op certificates: one broadcast fragment per inserted item
         (issues #42/#49; the doc-level op an item denotes is
         [(RootId name, OpInsert (input_of_item it))]) *)
      ([∗ list] it ∈ ins,
         is_op_cert γh (RootId name, OpInsert (input_of_item it))) }}}.
Proof.
  (* ---- Prologue: take the store lock, extract THIS text. ---- *)
  wp_start as "Hpre". iNamed "Hpre".
  iDestruct "His_store" as "#His_store".   (* keep is_Store (persistent) for the later Unlock *)
  wp_auto.
  subst s_loc.
  wp_apply (wp_Store__wlock with "[$His_store]"). iIntros "[Hlk Hinv]".
  iNamed "Hinv". iNamed "Hexcl". iNamed "Hro".
  iDestruct (auth_gmap_gset_lookup with "Hseq His_lb") as %(S' & HmS & HLsub).
  rewrite lookup_fmap in HmS.
  apply fmap_Some in HmS as (ts & Htsp & ->).
  (* the registry binds [name] to this text, so the history's [RootId name]
     component is exactly this text's document (issue #49) *)
  iDestruct (ghost_map_lookup with "HtypesAuth Hbind") as %Hbindlk.
  have Hmt : doc_model_get m (RootId name) = ty_arr ts := Hmtypes name parent ts Hbindlk Htsp.
  iDestruct (big_sepM_delete _ _ _ _ Htsp with "Htypes") as "[Hbody Hrest]".
  iDestruct "Hbody" as "(Htext & %Hinvarr)".
  iDestruct "Htext" as (yt0 tl0) "(Hparent & Hdll & %Hlen & %Hrepr & %Hcpar)".
  subst parent. wp_auto.
  case_bool_decide as Hbound.
  { (* ---- out-of-range: index past the visible length, nothing inserted. ---- *)
    wp_auto.
    iAssert ([∗ map] kk↦y ∈ types,
        own_ytype_cells kk (DfracOwn 1) (ty_cells y) (ty_arr y) ∗
        ⌜YjsArrInvariant (ty_arr y)⌝)%I
      with "[Hparent Hdll Hrest]" as "Htypes".
    { rewrite -{2}(insert_id types (tv.(yjs.Text.inner')) ts Htsp) -insert_delete_eq.
      rewrite big_sepM_insert; last apply lookup_delete_eq.
      iFrame "Hrest". iSplitL "Hparent Hdll".
      - iExists yt0, tl0. iFrame "Hparent Hdll". iPureIntro. split_and!; [exact Hlen | exact Hrepr | exact Hcpar].
      - iPureIntro. exact Hinvarr. }
    wp_apply (wp_Store__wunlock with "[$His_store $Hlk Hclient Hclock Hitemsf Hitemmap Htypesf Htypesmap Hdset Hpendf Hpend Hseq HtypesAuth Htypes Hhist]").
    { iNext. iExists client, k, items_mref, types_mref, dset, pend_sl, types, bind, h, m, pend.
      iSplitR "Hseq Htypes"; last by iFrame "Hseq Htypes".
      iFrame "∗#". iPureIntro.
      split_and!;
        [exact Hpendbnd | exact Hctr | exact Hcellctr | exact Hlocdup | exact Hrangedisj
        | exact Hrunfits | exact Horiginclk | exact Hbindtypes | exact Hbindinj
        | exact Htypesbound | exact Hhcoh | exact Hmtypes | exact Hmdom]. }
    iApply ("HΦ" $! L [] 0%nat 0%nat First Last).
    iSplit.
    { iExists tv, tv.(yjs.Text.store'), tv.(yjs.Text.inner').
      iFrame "Ht His_store His_hist Hbind His_lb". iPureIntro. split_and!; [reflexivity | reflexivity | exact Hsorted]. }
    iSplit; [iPureIntro; reflexivity |].
    iSplit; [iPureIntro; left; reflexivity |].
    iSplit; [iPureIntro; intros i it b Hii; rewrite lookup_nil in Hii; inversion Hii |].
    rewrite big_sepL_nil. done. }
  (* ---- in-range: insert one 1-char item per byte. ---- *)
  rewrite Hlen in Hbound.
  wp_auto.
  wp_apply strings.wp_string_len. iIntros "%Hlcb".
  wp_auto.
  case_bool_decide as Hovf.
  { (* clock-overflow guard fired: nothing inserted (like OOB). *)
    wp_auto.
    iAssert ([∗ map] kk↦y ∈ types,
        own_ytype_cells kk (DfracOwn 1) (ty_cells y) (ty_arr y) ∗
        ⌜YjsArrInvariant (ty_arr y)⌝)%I
      with "[Hparent Hdll Hrest]" as "Htypes".
    { rewrite -{2}(insert_id types (tv.(yjs.Text.inner')) ts Htsp) -insert_delete_eq.
      rewrite big_sepM_insert; last apply lookup_delete_eq.
      iFrame "Hrest". iSplitL "Hparent Hdll".
      - iExists yt0, tl0. iFrame "Hparent Hdll". iPureIntro. split_and!; [exact Hlen | exact Hrepr | exact Hcpar].
      - iPureIntro. exact Hinvarr. }
    wp_apply (wp_Store__wunlock with "[$His_store $Hlk Hclient Hclock Hitemsf Hitemmap Htypesf Htypesmap Hdset Hpendf Hpend Hseq HtypesAuth Htypes Hhist]").
    { iNext. iExists client, k, items_mref, types_mref, dset, pend_sl, types, bind, h, m, pend.
      iSplitR "Hseq Htypes"; last by iFrame "Hseq Htypes".
      iFrame "∗#". iPureIntro.
      split_and!;
        [exact Hpendbnd | exact Hctr | exact Hcellctr | exact Hlocdup | exact Hrangedisj
        | exact Hrunfits | exact Horiginclk | exact Hbindtypes | exact Hbindinj
        | exact Htypesbound | exact Hhcoh | exact Hmtypes | exact Hmdom]. }
    iApply ("HΦ" $! L [] 0%nat 0%nat First Last).
    iSplit.
    { iExists tv, tv.(yjs.Text.store'), tv.(yjs.Text.inner').
      iFrame "Ht His_store His_hist Hbind His_lb". iPureIntro. split_and!; [reflexivity | reflexivity | exact Hsorted]. }
    iSplit; [iPureIntro; reflexivity |].
    iSplit; [iPureIntro; left; reflexivity |].
    iSplit; [iPureIntro; intros i it b Hii; rewrite lookup_nil in Hii; inversion Hii |].
    rewrite big_sepL_nil. done. }
  (* no overflow: the run fits. *)
  have Hnoof : (uint.Z k + Z.of_nat (length cs) < 2^64)%Z by word.
  wp_auto.
  iAssert (own_ytype_cells (tv.(yjs.Text.inner')) (DfracOwn 1) ts.(ty_cells) ts.(ty_arr)) with "[Hparent Hdll]" as "Htext".
  { iExists yt0, tl0. iFrame "Hparent Hdll". iPureIntro. split_and!; [exact Hlen | exact Hrepr | exact Hcpar]. }
  wp_apply (wp_yType__findPos (tv.(yjs.Text.inner')) (DfracOwn 1) ts.(ty_cells) ts.(ty_arr) idx with "[$Htext]").
  iIntros (lft rgt p off) "(Htext & %Hpbound & %Hlftloc & %Hrgtloc & %Hoff)".
  wp_auto.
  (* normalize the position (issue #28 M3): when the index lands inside a
     multi-char run, split the straddled node at the offset so the insertion
     point sits on a cell boundary. The flatten is unchanged, so only the
     cell layer and the cursor move; both branches rebind the state under
     the shared boundary-form names. *)
  wp_if_join (λ v : val, ⌜v = execute_val⌝ ∗
      ∃ (types1 : gmap loc type_state) (ts1 : type_state) (p1 : nat),
      "s" ∷ s_ptr ↦ tv.(yjs.Text.store') ∗
      "Hitemsf" ∷ (tv.(yjs.Text.store')).[yjs.store.t, "items"] ↦ items_mref ∗
      "Hitemmap" ∷ own_item_map items_mref (DfracOwn 1) types1 ∗
      "Hrest" ∷ ([∗ map] kk↦y ∈ delete (tv.(yjs.Text.inner')) types1,
          own_ytype_cells kk (DfracOwn 1) y.(ty_cells) y.(ty_arr) ∗
          ⌜YjsArrInvariant y.(ty_arr)⌝) ∗
      "Htext" ∷ own_ytype_cells (tv.(yjs.Text.inner')) (DfracOwn 1) ts1.(ty_cells) ts1.(ty_arr) ∗
      "left" ∷ left_ptr ↦ node_loc ts1.(ty_cells) (Z.of_nat p1 - 1) ∗
      "right" ∷ right_ptr ↦ node_loc ts1.(ty_cells) (Z.of_nat p1) ∗
      "%Htsp1" ∷ ⌜types1 !! tv.(yjs.Text.inner') = Some ts1⌝ ∗
      "%Harr1" ∷ ⌜ty_arr ts1 = ty_arr ts⌝ ∗
      "%Hdomeq1" ∷ ⌜∀ p', p' ≠ tv.(yjs.Text.inner') → types1 !! p' = types !! p'⌝ ∗
      "%Hpb1" ∷ ⌜(p1 <= length ts1.(ty_cells))%nat⌝ ∗
      "%Hcellctr1" ∷ ⌜∀ c0, c0 ∈ all_cells types1 → cell_client c0 = client →
          (uint.Z (cell_clock c0) + Z.of_nat (length (ic_run c0)) <= uint.Z k)%Z⌝ ∗
      "%Hlocdup1" ∷ ⌜NoDup (ic_loc <$> all_cells types1)⌝ ∗
      "%Hrangedisj1" ∷ ⌜cells_range_disjoint (all_cells types1)⌝ ∗
      "%Hrunfits1" ∷ ⌜∀ c0, c0 ∈ all_cells types1 → cell_fits c0⌝ ∗
      "%Horiginclk1" ∷ ⌜∀ c0, c0 ∈ all_cells types1 → cell_origin_clk c0⌝)%I
      with "[s left right offset Htext Hrest Hitemsf Hitemmap]".
  { (* offset > 0: split [left] at the offset *)
    destruct Hoff as [Hoffeq | (Hoffpos & Hpge1 & (cw & Hcw & Hcwdel & Hofflen))];
      first (exfalso; subst off; move: l; word).
    have Hts_eta : MkTypeState ts.(ty_cells) ts.(ty_arr) = ts by (destruct ts; reflexivity).
    have Htspm : types !! tv.(yjs.Text.inner') = Some (MkTypeState ts.(ty_cells) ts.(ty_arr))
      by rewrite Hts_eta.
    have Hdiffb : (0 < uint.nat off < length (ic_run cw))%nat by word.
    have Hfits64 : ∀ c0, c0 ∈ all_cells types →
        (uint.Z (cell_clock c0) + Z.of_nat (length (ic_run c0)) < 2^64)%Z.
    { move=> c0 Hc0. exact (Hrunfits c0 Hc0). }
    have Hcwmem : cw ∈ all_cells types.
    { apply all_cells_elem_of.
      exists (tv.(yjs.Text.inner')), (MkTypeState ts.(ty_cells) ts.(ty_arr)).
      split; [exact Htspm | exact (list_elem_of_lookup_2 _ _ _ Hcw)]. }
    have Hdisjcw : ∀ c0, c0 ∈ all_cells types → cell_client c0 = cell_client cw →
        ic_loc c0 ≠ ic_loc cw →
       (uint.Z (cell_clock c0) + Z.of_nat (length (ic_run c0)) <= uint.Z (cell_clock cw))%Z ∨
       (uint.Z (cell_clock cw) + Z.of_nat (length (ic_run cw)) <= uint.Z (cell_clock c0))%Z.
    { move=> c0 Hc0 Hcc Hne. exact (Hrangedisj c0 cw Hc0 Hcwmem Hcc Hne). }
    (* pack the store big-sep back together for the splitNode call *)
    iAssert ([∗ map] kk↦y ∈ types,
        own_ytype_cells kk (DfracOwn 1) (ty_cells y) (ty_arr y) ∗
        ⌜YjsArrInvariant (ty_arr y)⌝)%I with "[Htext Hrest]" as "Htypes".
    { rewrite -{2}(insert_id types (tv.(yjs.Text.inner')) ts Htsp) -insert_delete_eq.
      rewrite big_sepM_insert; last apply lookup_delete_eq.
      iFrame "Hrest". iSplitL "Htext"; [iExact "Htext" | iPureIntro; exact Hinvarr]. }
    iDestruct (types_cells_id_bounds2 with "Htypes") as %Hbnds.
    have Hckbnd : (Z.of_nat (clock (item_id (run_head cw))) < 2^64)%Z := proj2 (Hbnds cw Hcwmem).
    iDestruct (types_runs_wf2 with "Htypes") as %Hrunwfall.
    have Hrunwfcw : run_wf (ic_run cw) := Hrunwfall cw Hcwmem.
    have Hndl : node_loc ts.(ty_cells) (Z.of_nat p - 1) = ic_loc cw.
    { rewrite /node_loc decide_True; last lia.
      have -> : Z.to_nat (Z.of_nat p - 1) = (p - 1)%nat by lia.
      rewrite Hcw //. }
    rewrite Hndl.
    wp_apply (wp_store__splitNode (tv.(yjs.Text.store')) items_mref types
                (tv.(yjs.Text.inner')) ts.(ty_cells) ts.(ty_arr) (p - 1)%nat cw off
                Htspm Hcw Hdiffb Hfits64 Hlocdup Hdisjcw
                with "[$Hitemsf $Hitemmap $Htypes]").
    iIntros (rloc) "(%Hrlocnn & %Hrlocfresh & Hitemsf & Hitemmap & Htypes)".
    wp_auto.
    set (cells1 := split_cells ts.(ty_cells) (p - 1)%nat (uint.nat off) rloc).
    set (ts1 := MkTypeState cells1 ts.(ty_arr)).
    iDestruct (big_sepM_delete _ _ (tv.(yjs.Text.inner')) ts1 with "Htypes") as "[[Htext %Hinvarr1] Hrest]";
      first apply lookup_insert_eq.
    rewrite delete_insert_eq.
    (* pool transports across the split *)
    have Hsub1 := split_pool_subrange types (tv.(yjs.Text.inner')) ts.(ty_cells) ts.(ty_arr)
                    (p - 1)%nat cw (uint.nat off) rloc Htspm Hcw Hrunwfcw Hdiffb Hckbnd
                    (Hrunfits cw Hcwmem).
    have Hcellctr1 : ∀ c0, c0 ∈ all_cells (<[tv.(yjs.Text.inner') := ts1]> types) →
        cell_client c0 = client →
        (uint.Z (cell_clock c0) + Z.of_nat (length (ic_run c0)) <= uint.Z k)%Z.
    { move=> c0 Hc0 Hcc.
      destruct (Hsub1 c0 Hc0) as (cold & Hcold & Hccold & Hlo & Hhi).
      have := Hcellctr cold Hcold ltac:(congruence). lia. }
    have Hlocdup1 : NoDup (ic_loc <$> all_cells (<[tv.(yjs.Text.inner') := ts1]> types))
      := split_pool_locdup types (tv.(yjs.Text.inner')) ts.(ty_cells) ts.(ty_arr)
           (p - 1)%nat cw (uint.nat off) rloc Htspm Hcw Hrlocfresh Hlocdup.
    have Hrangedisj1 : cells_range_disjoint (all_cells (<[tv.(yjs.Text.inner') := ts1]> types))
      := split_pool_rangedisj types (tv.(yjs.Text.inner')) ts.(ty_cells) ts.(ty_arr)
           (p - 1)%nat cw (uint.nat off) rloc Htspm Hcw Hrunwfcw Hdiffb Hckbnd
           (Hrunfits cw Hcwmem) Hlocdup Hrangedisj.
    have Hrunfits1 : ∀ c0, c0 ∈ all_cells (<[tv.(yjs.Text.inner') := ts1]> types) → cell_fits c0.
    { move=> c0 Hc0. rewrite /cell_fits.
      exact (split_pool_fits types (tv.(yjs.Text.inner')) ts.(ty_cells) ts.(ty_arr)
               (p - 1)%nat cw (uint.nat off) rloc Htspm Hcw Hrunwfcw Hdiffb Hckbnd
               Hfits64 c0 Hc0). }
    have Horiginclk1 : ∀ c0, c0 ∈ all_cells (<[tv.(yjs.Text.inner') := ts1]> types) → cell_origin_clk c0
      := split_pool_originclk types (tv.(yjs.Text.inner')) ts.(ty_cells) ts.(ty_arr)
           (p - 1)%nat cw (uint.nat off) rloc Htspm Hcw Hrunwfcw Hdiffb Horiginclk.
    (* the two halves sit at cell cursors p-1 / p of the split list *)
    have Hcl1 : cells1 !! (p - 1)%nat = Some (split_cell_left cw (uint.nat off))
      := split_cells_lookup_left ts.(ty_cells) (p - 1)%nat (uint.nat off) rloc cw Hcw.
    have Hcr1 : cells1 !! p = Some (split_cell_right cw (uint.nat off) rloc).
    { have H := split_cells_lookup_right ts.(ty_cells) (p - 1)%nat (uint.nat off) rloc cw Hcw.
      have -> : p = S (p - 1)%nat by lia.
      exact H. }
    have Hlen1 : length cells1 = S (length ts.(ty_cells))
      := split_cells_length ts.(ty_cells) (p - 1)%nat (uint.nat off) rloc cw Hcw.
    have Hleftloc1 : ic_loc cw = node_loc cells1 (Z.of_nat p - 1).
    { rewrite /node_loc decide_True; last lia.
      have -> : Z.to_nat (Z.of_nat p - 1) = (p - 1)%nat by lia.
      rewrite Hcl1 //. }
    have Hrightloc1 : rloc = node_loc cells1 (Z.of_nat p).
    { rewrite /node_loc decide_True; last lia.
      rewrite Nat2Z.id Hcr1 //. }
    iSplitR; first done.
    iExists (<[tv.(yjs.Text.inner') := ts1]> types), ts1, p.
    iEval (rewrite Hleftloc1) in "left". iEval (rewrite Hrightloc1) in "right".
    rewrite delete_insert_eq.
    iFrame "s Hitemsf Hitemmap Hrest Htext left right".
    iPureIntro. split_and!.
    - apply lookup_insert_eq.
    - reflexivity.
    - move=> p' Hne. rewrite lookup_insert_ne //.
    - rewrite /ts1 /= Hlen1. lia.
    - exact Hcellctr1.
    - exact Hlocdup1.
    - exact Hrangedisj1.
    - exact Hrunfits1.
    - exact Horiginclk1. }
  { (* offset = 0: the index already sits on a boundary *)
    have Hoffeq : off = W64 0.
    { destruct Hoff as [-> | (Hoffpos & _)]; [done | exfalso; apply n; word]. }
    subst off.
    iSplitR; first done.
    iExists types, ts, p.
    iFrame "s Hitemsf Hitemmap Hrest Htext left right".
    iPureIntro. split_and!;
      [exact Htsp | reflexivity | move=> p' _; reflexivity | exact Hpbound
      | exact Hcellctr | exact Hlocdup | exact Hrangedisj | exact Hrunfits | exact Horiginclk]. }
  iIntros (v) "[%Hv HQ]". subst v. iNamed "HQ".
  (* rebind the normalized state under the boundary-form names: everything
     the remaining proof consumes is restated at (types1, ts1, p1), the old
     cell layer is cleared, and the primed names take the old ones over *)
  have Hctr1 : ∀ parent' ts' x, types1 !! parent' = Some ts' → x ∈ ty_arr ts' →
      clientId (item_id x) = uint.nat client → (clock (item_id x) < uint.nat k)%nat.
  { move=> parent' ts' x Hlk Hx Hcx.
    destruct (decide (parent' = tv.(yjs.Text.inner'))) as [-> | Hne].
    - rewrite Htsp1 in Hlk. injection Hlk as <-. rewrite Harr1 in Hx.
      exact (Hctr _ _ x Htsp Hx Hcx).
    - rewrite (Hdomeq1 parent' Hne) in Hlk. exact (Hctr _ _ x Hlk Hx Hcx). }
  have Hbindtypes1 : ∀ name' p', bind !! name' = Some p' → is_Some (types1 !! p').
  { move=> n' p' Hb. destruct (decide (p' = tv.(yjs.Text.inner'))) as [-> | Hne].
    - rewrite Htsp1. by eexists.
    - rewrite (Hdomeq1 _ Hne). exact (Hbindtypes _ _ Hb). }
  have Htypesbound1 : ∀ p', is_Some (types1 !! p') → ∃ name', bind !! name' = Some p'.
  { move=> p' [ts' Hts']. destruct (decide (p' = tv.(yjs.Text.inner'))) as [-> | Hne].
    - exact (Htypesbound _ (ex_intro _ ts Htsp)).
    - rewrite (Hdomeq1 _ Hne) in Hts'. exact (Htypesbound _ (ex_intro _ _ Hts')). }
  have Hmtypes1 : ∀ name' p' ts', bind !! name' = Some p' → types1 !! p' = Some ts' →
      doc_model_get m (RootId name') = ty_arr ts'.
  { move=> n' p' ts' Hb Hts'. destruct (decide (p' = tv.(yjs.Text.inner'))) as [-> | Hne].
    - rewrite Htsp1 in Hts'. injection Hts' as <-. rewrite Harr1.
      exact (Hmtypes n' _ ts Hb Htsp).
    - rewrite (Hdomeq1 _ Hne) in Hts'. exact (Hmtypes n' p' ts' Hb Hts'). }
  have HLsub1 : (list_to_set L : gset (YjsItem A)) ⊆ list_to_set (ty_arr ts1)
    by rewrite Harr1.
  have Hmt1 : doc_model_get m (RootId name) = ty_arr ts1 by rewrite Harr1.
  have Hinvarr1 : YjsArrInvariant (ty_arr ts1) by rewrite Harr1.
  have Hseqeq1 : ((λ ts0 : type_state, (list_to_set ts0.(ty_arr) : gset (YjsItem A))) <$> types1)
               = ((λ ts0 : type_state, (list_to_set ts0.(ty_arr) : gset (YjsItem A))) <$> types).
  { apply map_eq. move=> p'. destruct (decide (p' = tv.(yjs.Text.inner'))) as [-> | Hne].
    - rewrite !lookup_fmap Htsp1 Htsp /= Harr1 //.
    - rewrite !lookup_fmap (Hdomeq1 _ Hne) //. }
  iEval (rewrite -Hseqeq1) in "Hseq".
  clear Hctr Hbindtypes Htypesbound Hmtypes HLsub Hmt Hinvarr Htsp Hpbound
        Hcellctr Hlocdup Hrangedisj Hrunfits Horiginclk Hoff Hlftloc Hrgtloc
        Hbound Hlen Hrepr Hcpar.
  clear Harr1 Hdomeq1 Hseqeq1.
  clear off lft rgt yt0 tl0.
  clear p ts types.
  rename types1 into types. rename ts1 into ts. rename p1 into p.
  rename Htsp1 into Htsp. rename Hpb1 into Hpbound.
  rename Hctr1 into Hctr. rename Hcellctr1 into Hcellctr.
  rename Hlocdup1 into Hlocdup. rename Hrangedisj1 into Hrangedisj.
  rename Hrunfits1 into Hrunfits. rename Horiginclk1 into Horiginclk.
  rename Hbindtypes1 into Hbindtypes. rename Htypesbound1 into Htypesbound.
  rename Hmtypes1 into Hmtypes. rename HLsub1 into HLsub. rename Hmt1 into Hmt.
  rename Hinvarr1 into Hinvarr.
  (* re-open the DLL pures for the new cell list, and re-pin the two cursors
     as opaque locs with their node_loc equations (the pre-normalize shape) *)
  iAssert (⌜cells_repr ts.(ty_arr) ts.(ty_cells) ts.(ty_arr)⌝ ∗
           own_ytype_cells (tv.(yjs.Text.inner')) (DfracOwn 1) ts.(ty_cells) ts.(ty_arr))%I
    with "[Htext]" as "[%Hrepr Htext]".
  { iDestruct "Htext" as (ytx tlx) "(Hp & Hd & %Hl & %Hr & %Hc)".
    iSplitR; first done. iExists ytx, tlx. iFrame "Hp Hd".
    iPureIntro. split_and!; assumption. }
  have [lft Hlftloc] : ∃ l0 : loc, l0 = node_loc ts.(ty_cells) (Z.of_nat p - 1) by eexists.
  iEval (rewrite -Hlftloc) in "left".
  have [rgt Hrgtloc] : ∃ r0 : loc, r0 = node_loc ts.(ty_cells) (Z.of_nat p) by eexists.
  iEval (rewrite -Hrgtloc) in "right".
  wp_auto.
  (* the model position of the cell boundary [p] (issue #28 U3): all
     couplings are derived from the run structure, independent of the
     unit scaffold *)
  have [mp Hmpdef] : ∃ mp0 : nat, mp0 = length (run_flatten (take p ts.(ty_cells)))
    by (eexists; reflexivity).
  (* shared right origin *)
  wp_if_join (λ v : val, ⌜v = execute_val⌝ ∗ ∃ (oRptr : loc) (in_rO : option yjs.id.t),
      "HoR" ∷ originRightId_ptr ↦ oRptr ∗ "HisR" ∷ is_origin_id oRptr in_rO ∗
      "Htext" ∷ own_ytype_cells (tv.(yjs.Text.inner')) (DfracOwn 1) ts.(ty_cells) ts.(ty_arr) ∗ "Hright" ∷ right_ptr ↦ rgt ∗
      "%Hrightinit" ∷ ⌜(in_rO = None ∧ (p = length ts.(ty_cells))%nat) ∨
        (∃ (ri : YjsItem A) (rightOriginId : yjs.id.t), ts.(ty_arr) !! mp = Some ri ∧ in_rO = Some rightOriginId ∧ item_id ri = toYjsId rightOriginId)⌝)%I
      with "[right Htext originRightId]".
  { iSplitR; [done|].
    destruct (decide (p = length ts.(ty_cells))%nat) as [Hpeq|Hne].
    - iExists null, None. iFrame "originRightId right Htext".
      iSplit; [by rewrite /is_origin_id | iPureIntro; left; split; [reflexivity | exact Hpeq]].
    - iDestruct "Htext" as (yt1 tl1) "(Hpar1 & Hdll1 & %Hlen1 & %Hrepr1 & %Hcpar1)".
      have Hlt : (p < length ts.(ty_cells))%nat by lia.
      iDestruct (node_loc_lt_not_null (DfracOwn 1) ts.(ty_cells) yt1.(yjs.yType.start') tl1 (p) Hlt with "Hdll1") as "[%Hnn _]".
      exfalso. exact (Hnn e). }
  { iDestruct "Htext" as (yt1 tl1) "(Hpar1 & Hdll1 & %Hlen1 & %Hrepr1 & %Hcpar1)".
    have Hposlt : (p < length ts.(ty_cells))%nat.
    { destruct (decide (p < length ts.(ty_cells))%nat) as [Hlt|Hge]; [exact Hlt|exfalso].
      apply n. rewrite /node_loc decide_True; [|lia].
      have Hpe : (p = length ts.(ty_cells))%nat by lia.
      rewrite Hpe Nat2Z.id lookup_ge_None_2; [done|lia]. }
    destruct (ts.(ty_cells) !! p) as [c0|] eqn:Hc0; [| apply lookup_ge_None in Hc0; lia].
    iDestruct (own_dll_acc (DfracOwn 1) ts.(ty_cells) yt1.(yjs.yType.start') tl1 (p) c0 Hc0 with "Hdll1") as "Hacc". iNamed "Hacc".
    iEval (rewrite Hcloc) in "Hcval".
    wp_load. wp_pures. wp_store.
    iDestruct (typed_pointsto_not_null with "rid") as %Hridnn.
    iPersist "rid".
    wp_auto.
    iEval (rewrite -Hcloc) in "Hcval".
    iDestruct ("Hback" with "Hcval") as "Hdll1".
    iSplitR; [done|].
    iExists rid_ptr, (Some itemVal.(yjs.item.id')).
    iFrame "originRightId right".
    iSplitR "Hpar1 Hdll1".
    { rewrite /is_origin_id. iSplit; [iPureIntro; exact Hridnn | iFrame "rid"]. }
    iSplitL "Hpar1 Hdll1".
    { iExists yt1, tl1. iFrame "Hpar1 Hdll1". iPureIntro. split_and!; [exact Hlen1 | exact Hrepr1 | exact Hcpar1]. }
    iPureIntro. right. exists (run_head c0), itemVal.(yjs.item.id').
    have Hr1 : ts.(ty_arr) = run_flatten ts.(ty_cells) by move: Hrepr1; rewrite /cells_repr //.
    have Hhd0 : ic_run c0 !! 0%nat = Some (run_head c0).
    { rewrite /run_head. destruct (ic_run c0); [exact (False_ind _ (proj1 Hrun eq_refl)) | reflexivity]. }
    have Hpos := run_flatten_lookup_of_cell ts.(ty_cells) p 0%nat c0 (run_head c0) Hc0 Hhd0.
    rewrite Nat.add_0_r in Hpos.
    split_and!; [rewrite Hr1; exact Hpos | reflexivity | exact Hid]. }
  iIntros (v) "[%Hv HQ]". subst v. iNamed "HQ". wp_auto.
  (* fix the run's shared right origin oR and the first item's left origin oL as values *)
  assert (∃ (oR : YjsPtr A),
     (in_rO = None ∧ oR = Last ∧ (mp = length ts.(ty_arr))%nat) ∨
     (∃ (ri : YjsItem A) (rightOriginId : yjs.id.t), ts.(ty_arr) !! mp = Some ri ∧ in_rO = Some rightOriginId ∧ item_id ri = toYjsId rightOriginId ∧ oR = itemPtr ri))
     as [oR HoRspec].
  { destruct Hrightinit as [[Hn Hpe] | (ri & rightOriginId & Hria & Hrs & Hrid)].
    - exists Last. left. split_and!; [exact Hn | reflexivity |].
      have Hr1 : ts.(ty_arr) = run_flatten ts.(ty_cells) by move: Hrepr; rewrite /cells_repr //.
      rewrite Hmpdef Hpe take_ge; last lia.
      rewrite Hr1 //.
    - exists (itemPtr ri). right. exists ri, rightOriginId. split_and!; [exact Hria | exact Hrs | exact Hrid | reflexivity]. }
  iAssert (⌜∀ c0, c0 ∈ ts.(ty_cells) → run_wf (ic_run c0)⌝ ∗
           own_ytype_cells (tv.(yjs.Text.inner')) (DfracOwn 1) ts.(ty_cells) ts.(ty_arr))%I
    with "[Htext]" as "[%Hrunwf0 Htext]".
  { iDestruct "Htext" as (ytw tlw) "(Hpw & Hdw & %Hlw & %Hrw & %Hcw)".
    iDestruct (own_dll_runs_wf with "Hdw") as %Hrwf.
    iSplitR; [by iPureIntro|]. iExists ytw, tlw. iFrame "Hpw Hdw". iPureIntro.
    split_and!; [exact Hlw | exact Hrw | exact Hcw]. }
  have Hnec00 : Forall (λ c0, ic_run c0 ≠ []) ts.(ty_cells).
  { apply Forall_forall. move=> c0 Hc0. exact (proj1 (Hrunwf0 c0 Hc0)). }
  have Hr10 : ts.(ty_arr) = run_flatten ts.(ty_cells) by move: Hrepr; rewrite /cells_repr //.
  have Hmple : (mp <= length ts.(ty_arr))%nat.
  { rewrite Hmpdef Hr10.
    have Htg : take (length ts.(ty_cells)) ts.(ty_cells) = ts.(ty_cells)
      by (apply take_ge; lia).
    have := run_flatten_take_length_le ts.(ty_cells) p (length ts.(ty_cells)) Hpbound.
    rewrite Htg. lia. }
  have Hmp1 : (1 <= p)%nat -> (1 <= mp)%nat.
  { move=> Hp1. rewrite Hmpdef.
    have := run_flatten_take_length_lt ts.(ty_cells) 0 p Hnec00 Hp1 Hpbound.
    rewrite take_0 /run_flatten /=. lia. }
  assert (∃ (oL : YjsPtr A),
     (oL = First ∧ (p = 0)%nat) ∨
     (∃ (lc : item_cell) (li : YjsItem A), (1 <= p)%nat ∧
        ts.(ty_cells) !! (p - 1)%nat = Some lc ∧
        ic_run lc !! (length (ic_run lc) - 1)%nat = Some li ∧
        ts.(ty_arr) !! (mp - 1)%nat = Some li ∧ oL = itemPtr li))
     as [oL HoLspec].
  { destruct (decide (p = 0)%nat) as [Hidx0 | Hidxpos].
    - exists First. left. split; [reflexivity | exact Hidx0].
    - have Hidxm : (p - 1 < length ts.(ty_cells))%nat by lia.
      destruct (ts.(ty_cells) !! (p - 1)%nat) as [lc|] eqn:Hlc; [| apply lookup_ge_None in Hlc; lia].
      have Hwflc : run_wf (ic_run lc) := Hrunwf0 lc (list_elem_of_lookup_2 _ _ _ Hlc).
      have Hlen1lc : (1 <= length (ic_run lc))%nat.
      { destruct (ic_run lc) eqn:Hrc; [exact (False_ind _ (proj1 Hwflc eq_refl)) | simpl; lia]. }
      destruct (lookup_lt_is_Some_2 (ic_run lc) (length (ic_run lc) - 1)%nat ltac:(lia)) as [lch Hlch].
      have Hpos := run_flatten_lookup_of_cell ts.(ty_cells) (p - 1)%nat _ lc lch Hlc Hlch.
      have Hpstep : length (run_flatten (take p ts.(ty_cells)))
                  = (length (run_flatten (take (p - 1)%nat ts.(ty_cells))) + length (ic_run lc))%nat.
      { have Hps : p = S (p - 1)%nat by lia.
        rewrite {1}Hps (run_flatten_take_S _ _ _ Hlc) length_app //. }
      exists (itemPtr lch). right. exists lc, lch. split_and!; [lia | reflexivity | exact Hlch | | reflexivity].
      rewrite Hmpdef Hr10.
      replace (length (run_flatten (take p ts.(ty_cells))) - 1)%nat
        with (length (run_flatten (take (p - 1)%nat ts.(ty_cells))) + (length (ic_run lc) - 1))%nat
        by lia.
      exact Hpos. }
  (* loop invariant: [j] inserted so far, [arr]/[cells]/[leftloc] grow, [ins] is the run;
     the ghost history [hj] grows by one mint per inserted item, staying coherent
     with [arr], and the certificates of the run accumulate in [Hcertsj]. *)
  iAssert (∃ (j : nat) (arr : list (YjsItem A)) (cells : list item_cell) (leftloc : loc)
             (ins : list (YjsItem A)) (hj : list Ev),
    "Hi" ∷ i_ptr ↦ W64 j ∗
    "Htptr" ∷ t_ptr ↦ t ∗
    "Hcontentp" ∷ content_ptr ↦ cs ∗
    "Hclientp" ∷ client_ptr ↦ client ∗
    "HoRp" ∷ originRightId_ptr ↦ oRptr ∗
    "Hleftp" ∷ left_ptr ↦ leftloc ∗
    "Hsp" ∷ s_ptr ↦ tv.(yjs.Text.store') ∗
    "Hclient" ∷ (tv.(yjs.Text.store')).[yjs.store.t, "client"] ↦ client ∗
    "Hclock" ∷ (tv.(yjs.Text.store')).[yjs.store.t, "clock"] ↦ W64 (uint.Z k + Z.of_nat j) ∗
    "Hitemsf" ∷ (tv.(yjs.Text.store')).[yjs.store.t, "items"] ↦ items_mref ∗
    "Hitemmap" ∷ own_item_map items_mref (DfracOwn 1) (<[tv.(yjs.Text.inner') := MkTypeState cells arr]> types) ∗
    "Htypesf" ∷ (tv.(yjs.Text.store')).[yjs.store.t, "types"] ↦ types_mref ∗
    "Hdset" ∷ (tv.(yjs.Text.store')).[yjs.store.t, "deletedSet"] ↦ dset ∗
    "Hpendf" ∷ (tv.(yjs.Text.store')).[yjs.store.t, "pending"] ↦ pend_sl ∗
    "Hpend" ∷ own_update_structs pend_sl (DfracOwn 1) pend ∗
    "Hlk" ∷ own_wlock γs ∗
    "Hseq" ∷ own γs.(sn_seq) (● ((λ ts0 : type_state, (list_to_set ts0.(ty_arr) : gset (YjsItem A))) <$> types) : authR (gmapUR loc (gsetUR (YjsItem A)))) ∗
    "HtypesAuth" ∷ ghost_map_auth γs.(sn_types) 1 bind ∗
    "Htypesmap" ∷ own_map types_mref (DfracOwn 1) bind ∗
    "Hrightp" ∷ right_ptr ↦ rgt ∗
    "Hrest" ∷ ([∗ map] kk↦y ∈ delete (tv.(yjs.Text.inner')) types,
        own_ytype_cells kk (DfracOwn 1) y.(ty_cells) y.(ty_arr) ∗
        ⌜YjsArrInvariant y.(ty_arr)⌝) ∗
    "Htextj" ∷ own_ytype_cells (tv.(yjs.Text.inner')) (DfracOwn 1) cells arr ∗
    "%Hinvj" ∷ ⌜YjsArrInvariant arr⌝ ∗
    "%Hlenarr" ∷ ⌜length arr = (length ts.(ty_arr) + j)%nat⌝ ∗
    "%Hclensj" ∷ ⌜length cells = (length ts.(ty_cells) + j)%nat⌝ ∗
    "%Hjle" ∷ ⌜(j <= length cs)%nat⌝ ∗
    "%Hctrj" ∷ ⌜∀ x : YjsItem A, ArrSet arr (itemPtr x) → clientId (item_id x) = uint.nat client → (clock (item_id x) < uint.nat k + j)%nat⌝ ∗
    "%Hleftj" ∷ ⌜(leftloc = null ∧ (p + j = 0)%nat)
      ∨ (∃ (lc : item_cell) (li : YjsItem A),
           cells !! (p + j - 1)%nat = Some lc ∧ ic_loc lc = leftloc ∧
           arr !! (mp + j - 1)%nat = Some li ∧
           ic_run lc !! (length (ic_run lc) - 1)%nat = Some li ∧ (1 <= p + j)%nat ∧
           (j = 0%nat → itemPtr li = oL) ∧ (∀ j', j = S j' → ins !! j' = Some li))⌝ ∗
    "%Hrightj" ∷ ⌜(in_rO = None ∧ oR = Last ∧ (mp + j = length arr)%nat)
      ∨ (∃ (ri : YjsItem A) (rightOriginId : yjs.id.t),
           arr !! (mp + j)%nat = Some ri ∧ in_rO = Some rightOriginId ∧ item_id ri = toYjsId rightOriginId ∧ oR = itemPtr ri)⌝ ∗
    "%Hinslen" ∷ ⌜length ins = j⌝ ∗
    "%Hins" ∷ ⌜∀ (i : nat) (it : YjsItem A), ins !! i = Some it →
       it ∈ arr ∧
       (∀ b : w8, cs !! i = Some b → content it = [b]) ∧
       item_id it = MkYjsId (uint.nat client) (uint.nat k + i)%nat ∧
       rightOrigin it = oR ∧
       (i = 0%nat → origin it = oL) ∧
       (∀ (j' : nat) (itj : YjsItem A), i = S j' → ins !! j' = Some itj → origin it = itemPtr itj)⌝ ∗
    "%Hsubold" ∷ ⌜∀ x : YjsItem A, x ∈ ts.(ty_arr) → x ∈ arr⌝ ∗
    "%Hrgtj" ∷ ⌜rgt = node_loc cells (Z.of_nat (p + j))⌝ ∗
    "%Hcoupj" ∷ ⌜length (run_flatten (take (p + j)%nat cells)) = (mp + j)%nat⌝ ∗
    "%Hcellbnd" ∷ ⌜∀ c0 : item_cell, c0 ∈ all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells arr]> types) →
       cell_client c0 = client → (uint.Z (cell_clock c0) + Z.of_nat (length (ic_run c0)) <= uint.Z k + Z.of_nat j)%Z⌝ ∗
    "%Hlocdupj" ∷ ⌜NoDup (ic_loc <$> all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells arr]> types))⌝ ∗
    "%Hrangedisjj" ∷ ⌜cells_range_disjoint (all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells arr]> types))⌝ ∗
    "%Hrunfitsj" ∷ ⌜∀ c0, c0 ∈ all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells arr]> types) → cell_fits c0⌝ ∗
    "%Horiginclkj" ∷ ⌜∀ c0, c0 ∈ all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells arr]> types) → cell_origin_clk c0⌝ ∗
    "Hhistj" ∷ own_client_history γh (uint.nat client) hj ∗
    "%Hhcohj" ∷ ⌜history_state_coh hj (<[RootId name := arr]> m)⌝ ∗
    "Hcertsj" ∷ ([∗ list] it ∈ ins,
                   is_op_cert γh (RootId name, OpInsert (input_of_item it)))
    )%I with "[i t content client HoR left s Hclient Hclock Hitemsf Hitemmap Htypesf Hdset Hpendf Hpend Hlk Hseq HtypesAuth Htypesmap Hright Hrest Htext Hhist]" as "IH".
  { iExists 0%nat, ts.(ty_arr), ts.(ty_cells), lft, [], h.
    replace (W64 (uint.Z k + Z.of_nat 0)) with k by word.
    have Hts_eta : MkTypeState ts.(ty_cells) ts.(ty_arr) = ts by (destruct ts; reflexivity).
    rewrite Hts_eta (insert_id types (tv.(yjs.Text.inner')) ts Htsp).
    iFrame "i t content client HoR left s Hclient Hclock Hitemsf Hitemmap Htypesf Hdset Hpendf Hpend Hlk Hseq HtypesAuth Htypesmap Hright Hrest Htext Hhist".
    rewrite big_sepL_nil sep_emp.
    iPureIntro. split_and!.
    - exact Hinvarr.
    - lia.
    - rewrite Nat.add_0_r //.
    - lia.
    - intros x Hx Hc. have := Hctr (tv.(yjs.Text.inner')) ts x Htsp Hx Hc. lia.
    - destruct HoLspec as [[HoLF Hidx0] | (lc & li & Hge1 & Hlc & Hlast & Hli & HoLi)].
      + left. split; [| lia].
        rewrite Hlftloc /node_loc. case_decide as Hd; [exfalso; rewrite Hidx0 in Hd; simpl in Hd; lia | reflexivity].
      + right.
        exists lc, li. split_and!.
        * replace (p + 0 - 1)%nat with (p - 1)%nat by lia. exact Hlc.
        * rewrite Hlftloc /node_loc. case_decide as Hd; [| lia].
          have -> : Z.to_nat (Z.of_nat (p) - 1) = (p - 1)%nat by lia.
          rewrite Hlc //.
        * replace (mp + 0 - 1)%nat with (mp - 1)%nat by lia. exact Hli.
        * exact Hlast.
        * lia.
        * intros _. rewrite HoLi //.
        * intros j' Hj'. lia.
    - destruct HoRspec as [(Hn & HoRl & Hidxlen) | (ri & rightOriginId & Hria & Hrs & Hrid & HoRi)].
      + left. split_and!; [exact Hn | exact HoRl | rewrite Nat.add_0_r; exact Hidxlen].
      + right. exists ri, rightOriginId. split_and!; [rewrite Nat.add_0_r; exact Hria | exact Hrs | exact Hrid | exact HoRi].
    - reflexivity.
    - intros i it Hii. rewrite lookup_nil in Hii. inversion Hii.
    - intros x Hx. exact Hx.
    - rewrite Nat.add_0_r. exact Hrgtloc.
    - rewrite !Nat.add_0_r Hmpdef //.
    - intros c0 Hc0 Hcc0. have := Hcellctr c0 Hc0 Hcc0. lia.
    - exact Hlocdup.
    - exact Hrangedisj.
    - exact Hrunfits.
    - exact Horiginclk.
    - destruct Hhcoh as (sdoc & Hsd & Hmd). exists sdoc. split; [exact Hsd|].
      move=> t'. destruct (decide (t' = RootId name)) as [-> | Hne'].
      + rewrite docm_get_insert_eq (Hmd (RootId name)). exact Hmt.
      + rewrite docm_get_insert_ne //. }
  wp_for "IH".
  wp_apply strings.wp_string_len. iIntros "%Hlcb2". wp_auto. case_bool_decide as Hjlt.
  { (* loop body: integrate the [j]-th character *)
    have Hjpos : (j < length cs)%nat by word.
    rewrite decide_True; [| reflexivity].
    wp_auto.
    (* left origin = current [left] (the previously inserted item, or findPos's left) *)
    wp_if_join (λ v : val, ⌜v = execute_val⌝ ∗
      ∃ (oLptr : loc) (olo : option yjs.id.t),
        "HoL" ∷ originLeftId_ptr ↦ oLptr ∗
        "HisL" ∷ is_origin_id oLptr olo ∗
        "Htextj" ∷ own_ytype_cells tv.(yjs.Text.inner') (DfracOwn 1) cells arr ∗
        "Hleftp" ∷ left_ptr ↦ leftloc ∗
        "%Hleftspec" ∷ ⌜(olo = None ∧ (p + length ins = 0)%nat) ∨
           (∃ (li : YjsItem A), (1 <= p + length ins)%nat ∧ arr !! (mp + length ins - 1)%nat = Some li ∧ (toYjsId <$> olo) = Some (item_id li))⌝)%I
      with "[Hleftp Htextj originLeftId]".
    { destruct Hleftj as [[Hln Hpe0] | (lc & li & Hlccells & Hlcloc & Hliarr & Hliitem & Hge1 & _)].
      - iSplitR; [done|]. iExists null, None. iFrame "originLeftId Htextj Hleftp".
        iSplit; [by rewrite /is_origin_id|]. iPureIntro. left. split; [reflexivity | exact Hpe0].
      - iDestruct "Htextj" as (yth tlh) "(Hpar & Hdll & %Hlenh & %Hreprh & %Hcparh)".
        iDestruct (own_dll_acc (DfracOwn 1) cells yth.(yjs.yType.start') tlh (p + length ins - 1)%nat lc Hlccells with "Hdll") as "Hacc". iNamed "Hacc".
        iDestruct (typed_pointsto_not_null with "Hcval") as %Hlcnn.
        exfalso. exact (Hlcnn Hlcloc). }
    { destruct Hleftj as [[Hln _] | (lc & li & Hlccells & Hlcloc & Hliarr & Hliitem & Hge1 & _)].
      { exfalso; exact (n Hln). }
      iDestruct "Htextj" as (yth tlh) "(Hpar & Hdll & %Hlenh & %Hreprh & %Hcparh)".
      iDestruct (own_dll_acc (DfracOwn 1) cells yth.(yjs.yType.start') tlh (p + length ins - 1)%nat lc Hlccells with "Hdll") as "Hacc". iNamed "Hacc".
      iEval (rewrite Hlcloc) in "Hcval".
      wp_method_call. wp_call. wp_auto.
      wp_method_call. wp_call. rewrite /yjs.item__LastIdⁱᵐᵖˡ. wp_auto.
      wp_alloc icopy as "Hic". wp_auto.
      wp_bind (icopy @! (go.PointerType yjs.item) @! "Len" (# ()))%E.
      wp_apply (wp_item__Len icopy (DfracOwn 1) itemVal with "[$Hic]"). iIntros "Hic".
      have Hlenrun : length (itemVal.(yjs.item.content').(yjs.content.content')) = length (ic_run lc).
      { have Hleq := f_equal length Hcontent.
        rewrite length_fmap explode_length /toContent in Hleq. lia. }
      wp_pures. wp_store.
      iDestruct (typed_pointsto_not_null with "lid") as %Hlidnn.
      iPersist "lid". wp_auto.
      iEval (rewrite -Hlcloc) in "Hcval".
      iDestruct ("Hback" with "Hcval") as "Hdll".
      iSplitR; [done|].
      iExists lid_ptr, (Some {| yjs.id.clientId' := itemVal.(yjs.item.id').(yjs.id.clientId'); yjs.id.clock' := w64_word_instance.(word.sub) (w64_word_instance.(word.add) itemVal.(yjs.item.id').(yjs.id.clock') (W64 (length (itemVal.(yjs.item.content').(yjs.content.content'))))) (W64 1) |}).
      iFrame "originLeftId Hleftp".
      iSplitR "Hpar Hdll".
      { rewrite /is_origin_id. iSplit; [iPureIntro; exact Hlidnn | iFrame "lid"]. }
      iSplitL "Hpar Hdll".
      { iExists yth, tlh. iFrame "Hpar Hdll". iPureIntro. split_and!; [exact Hlenh | exact Hreprh | exact Hcparh]. }
      (* the produced id is the LAST char of the left cell's run:
         head clock + run length - 1 (run_wf), no-wrap from the pool fits *)
      have Hmemlc : lc ∈ all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells arr]> types).
      { rewrite (all_cells_insert types (tv.(yjs.Text.inner')) ts (MkTypeState cells arr) Htsp) /=.
        apply elem_of_app. left. exact (list_elem_of_lookup_2 _ _ _ Hlccells). }
      have Hfitslc := Hrunfitsj lc Hmemlc.
      have Hlen1lc : (1 <= length (ic_run lc))%nat.
      { destruct (ic_run lc) eqn:Hrc; [exact (False_ind _ (proj1 Hrun eq_refl)) | simpl; lia]. }
      have Hnw : (uint.Z (itemVal.(yjs.item.id').(yjs.id.clock')) + Z.of_nat (length (ic_run lc)) < 2^64)%Z.
      { move: Hfitslc. rewrite /cell_fits /cell_clock Hid /toYjsId /=. move=> H. word. }
      iPureIntro. right. exists li. split_and!.
      - exact Hge1.
      - exact Hliarr.
      - rewrite (run_wf_char_id _ _ _ Hrun Hliitem) /=.
        rewrite /run_head in Hid.
        rewrite Hid /toYjsId /=.
        do 2 f_equal.
        rewrite Hlenrun. clear -Hnw Hlen1lc. word. }
    iIntros (v) "[%Hv HQL]". subst v. iNamed "HQL". wp_auto.
    wp_func_call. wp_call.
    destruct (cs !! sint.nat (W64 j)) as [b|] eqn:Hb;
      [ wp_auto | exfalso; apply lookup_ge_None in Hb; revert Hb Hjlt Hlcb2; word ].
    wp_alloc client_l as "Hcl2". wp_auto.
    rewrite Hb. wp_auto. wp_func_call. wp_call.
    wp_alloc oR2 as "HoR2". wp_auto. wp_alloc oL2 as "HoL2". wp_auto.
    (* build the model item [newItem] and integrate *)
    have Hclocknit : uint.nat (W64 (uint.Z k + j)) = (uint.nat k + j)%nat by word.
    rewrite Hinslen in Hleftspec.
    have Horig : ∃ (o : YjsPtr A),
       (toYjsId <$> olo = None ∧ o = First ∧ (mp + j)%nat = 0%nat) ∨
       (∃ li, (1 <= mp + j)%nat ∧ arr !! (mp + j - 1)%nat = Some li ∧ toYjsId <$> olo = Some (item_id li) ∧ o = itemPtr li).
    { destruct Hleftspec as [[Hon Hp0] | (li & Hge & Hla & Hom)].
      - exists First. left. subst olo. split_and!; [reflexivity | reflexivity |].
        have Hp00 : p = 0%nat by lia.
        have Hj00 : j = 0%nat by lia.
        rewrite Hmpdef Hp00 take_0 /run_flatten /= Hj00 //.
      - exists (itemPtr li). right. exists li. split_and!; [| exact Hla | exact Hom | reflexivity].
        destruct j as [|j']; [| lia].
        have Hp1 : (1 <= p)%nat by lia.
        have := Hmp1 Hp1. lia. }
    destruct Horig as [morigin Horig].
    have Hrorig : ∃ (r : YjsPtr A),
       (toYjsId <$> in_rO = None ∧ r = Last ∧ (mp + j)%nat = length arr) ∨
       (∃ ri, arr !! (mp + j)%nat = Some ri ∧ toYjsId <$> in_rO = Some (item_id ri) ∧ r = itemPtr ri).
    { destruct Hrightj as [(Hrn & Hoeq & Hpl) | (ri & rightOriginId & Hria & Hros & Hrii & HoRi)].
      - exists Last. left. subst in_rO. split_and!; [reflexivity | reflexivity | exact Hpl].
      - exists (itemPtr ri). right. exists ri. split_and!; [exact Hria | rewrite Hros /= Hrii // | reflexivity]. }
    destruct Hrorig as [mrightorigin Hrorig].
    set (in_id1 := MkYjsId (uint.nat client) (uint.nat (W64 (uint.Z k + j)))).
    set (input := MkIntegrateInput (toYjsId <$> olo) (toYjsId <$> in_rO) ([b] : A) in_id1).
    set (newItem := Item (A:=A) morigin mrightorigin in_id1 [b]).
    have Htoitem : toItem input arr = Some newItem.
    { apply (toItem_at arr in_id1 [b] morigin mrightorigin (toYjsId <$> olo) (toYjsId <$> in_rO) Hinvj).
      - destruct Horig as [(Hon & Ho & _) | (li & _ & Hla & Hom & Ho)]; [left; split; [exact Hon | exact Ho] | right; exists li; split_and!; [exact Hom | exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Hla) | exact Ho]].
      - destruct Hrorig as [(Hrn & Hr & _) | (ri & Hria & Hri & Hr)]; [left; split; [exact Hrn | exact Hr] | right; exists ri; split_and!; [exact Hri | exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Hria) | exact Hr]]. }
    have Hvalid : IsItemValid newItem :=
      insert_item_valid arr (mp + j) in_id1 [b] morigin mrightorigin
        (toYjsId <$> olo) (toYjsId <$> in_rO) Hinvj Horig Hrorig.
    have Hmax' : maximalId newItem arr.
    { apply (insert_maximalId arr morigin mrightorigin (uint.nat client) (uint.nat (W64 (uint.Z k + j))) [b]).
      intros x Hx Hc. rewrite Hclocknit. exact (Hctrj x Hx Hc). }
    iDestruct "HisR" as "#HisRp".
    (* the resolved neighbour indices the Integrate spec takes (issue #49) *)
    have HfindLj : findLeftIdx (in_originId input) arr = Some (Z.of_nat (mp + j) - 1).
    { destruct Horig as [(Hon & _ & Hp0) | (li & Hge & Hla & Hom & _)].
      - rewrite /input /= Hon /findLeftIdx Hp0 //.
      - rewrite /input /= Hom
          (findLeftIdx_at arr (mp + j - 1) li (yai_unique _ Hinvj) Hla).
        f_equal. lia. }
    have HfindRj : findRightIdx (in_rightOriginId input) arr = Some (Z.of_nat (mp + j)).
    { destruct Hrorig as [(Hrn & _ & Hpl) | (ri & Hria & Hri & _)].
      - rewrite /input /= Hrn /findRightIdx Hpl //.
      - rewrite /input /= Hri
          (findRightIdx_at arr (mp + j) ri (yai_unique _ Hinvj) Hria) //. }
    have Hleftloc_eq : leftloc = node_loc cells (Z.of_nat (p + j) - 1).
    { destruct Hleftj as [[-> Hp0] | (lc & li & Hlccells & Hlcloc & _ & _ & Hge1 & _)].
      - rewrite /node_loc. case_decide as Hd; [exfalso; lia | done].
      - rewrite /node_loc decide_True; last lia.
        have -> : Z.to_nat (Z.of_nat (p + j) - 1) = (p + j - 1)%nat by lia.
        rewrite Hlccells /= Hlcloc //. }
    (* the local item is created pre-linked (left/right/parent stores) *)
    iAssert (own_linked_item oL2 input (tv.(yjs.Text.inner'))
               (node_loc cells (Z.of_nat (p + j) - 1)) (node_loc cells (Z.of_nat (p + j))))
      with "[HoL2 HisL]" as "Hfresh".
    { iExists _, olo, in_rO. rewrite /own_fresh_item_raw /=. iFrame "HoL2 HisL HisRp".
      iPureIntro. split_and!;
        [reflexivity | reflexivity | reflexivity | reflexivity
        | rewrite -Hleftloc_eq // | rewrite -Hrgtj // | reflexivity | reflexivity | reflexivity]. }
    iDestruct (linked_item_fresh_ytype with "Hfresh Htextj") as %Hfr1.
    iDestruct (linked_item_fresh2 with "Hfresh Hrest") as %Hfr2.
    have Hfr : oL2 ∉ ic_loc <$> all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells arr]> types).
    { rewrite (all_cells_insert types (tv.(yjs.Text.inner')) ts (MkTypeState cells arr) Htsp) /=.
      rewrite fmap_app not_elem_of_app. split; [exact Hfr1 | exact Hfr2]. }
    have Hlookj : (<[tv.(yjs.Text.inner') := MkTypeState cells arr]> types) !! tv.(yjs.Text.inner')
                  = Some (MkTypeState cells arr) by apply lookup_insert_eq.
    iDestruct (types_runs_wf2 with "Hrest") as %Hrunwfrest.
    iAssert (⌜∀ c0, c0 ∈ cells → run_wf (ic_run c0)⌝ ∗
             own_ytype_cells (tv.(yjs.Text.inner')) (DfracOwn 1) cells arr)%I
      with "[Htextj]" as "[%Hrunwfc Htextj]".
    { iDestruct "Htextj" as (ytw tlw) "(Hpw & Hdw & %Hlw & %Hrw & %Hcw)".
      iDestruct (own_dll_runs_wf with "Hdw") as %Hrwf.
      iSplitR; [by iPureIntro|]. iExists ytw, tlw. iFrame "Hpw Hdw". iPureIntro.
      split_and!; [exact Hlw | exact Hrw | exact Hcw]. }
    have Hgmaxj : ∀ c0, c0 ∈ all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells arr]> types) →
                    cell_client c0 = W64 (clientId (item_id newItem)) →
                    (uint.Z (cell_clock c0) < uint.Z (W64 (clock (item_id newItem))))%Z ∧
                    (uint.Z (cell_clock c0) + Z.of_nat (length (ic_run c0)) <= uint.Z (W64 (clock (item_id newItem))))%Z.
    { intros c0 Hc0 Hcc0.
      have Hcl0 : cell_client c0 = client by (rewrite Hcc0 /newItem /in_id1 /=; word).
      have Hrhs : uint.Z (W64 (clock (item_id newItem))) = uint.Z k + Z.of_nat j
        by (rewrite /newItem /in_id1 /= Hclocknit; word).
      have Hlen1 : (1 <= length (ic_run c0))%nat.
      { have Hwf : run_wf (ic_run c0).
        { move: Hc0. rewrite (all_cells_insert types (tv.(yjs.Text.inner')) ts (MkTypeState cells arr) Htsp) /=.
          move=> /elem_of_app [Hin | Hin].
          - exact (Hrunwfc c0 Hin).
          - exact (Hrunwfrest c0 Hin). }
        destruct (ic_run c0) eqn:Hrc; [exact (False_ind _ (proj1 Hwf eq_refl)) | simpl; lia]. }
      have Hrg := Hcellbnd c0 Hc0 Hcl0.
      rewrite Hrhs. split; lia. }
    have Hfitsj : ∀ c0, c0 ∈ cells -> cell_fits c0.
    { move=> c0 Hc0. apply Hrunfitsj.
      rewrite (all_cells_lookup _ _ _ Hlookj).
      apply elem_of_app. left. exact Hc0. }
    have Hoclkj : ∀ c0, c0 ∈ cells -> cell_origin_clk c0.
    { move=> c0 Hc0. apply Horiginclkj.
      rewrite (all_cells_lookup _ _ _ Hlookj).
      apply elem_of_app. left. exact Hc0. }
    (* place the boundary cursors for the C1e Integrate spec: under the unit
       scaffold the boundary cell of model index p+j is cell p+j itself *)
    iAssert (⌜cells_repr arr cells arr⌝ ∗
             own_ytype_cells (tv.(yjs.Text.inner')) (DfracOwn 1) cells arr)%I
      with "[Htextj]" as "[%Hreprj Htextj]".
    { iDestruct "Htextj" as (ytj tlj) "(Hpj & Hdj & %Hlj & %Hrj & %Hcpj)".
      iSplitR; [done|]. iExists ytj, tlj. iFrame "Hpj Hdj". iPureIntro.
      split_and!; [exact Hlj | exact Hrj | exact Hcpj]. }
    have Hple : (mp + j <= length arr)%nat by (rewrite Hlenarr; lia).
    have HpjLb : ((p + j) <= length cells)%nat by (rewrite Hclensj; lia).
    have Hnecj : Forall (λ c0, ic_run c0 ≠ []) cells.
    { apply Forall_forall. move=> c0 Hc0. exact (proj1 (Hrunwfc c0 Hc0)). }
    have HcurLj : (Z.of_nat (length (run_flatten (take (p + j)%nat cells))) = Z.of_nat (mp + j) - 1 + 1)%Z.
    { rewrite Hcoupj. lia. }
    have HcurRj : (Z.of_nat (length (run_flatten (take (p + j)%nat cells))) = Z.of_nat (mp + j))%Z.
    { rewrite Hcoupj. lia. }
    wp_apply (wp_Store__Integrate (tv.(yjs.Text.store')) (tv.(yjs.Text.inner')) oL2 arr input newItem cells
                (<[tv.(yjs.Text.inner') := MkTypeState cells arr]> types) items_mref
                (Z.of_nat (mp + j) - 1) (Z.of_nat (mp + j)) (p + j)%nat (p + j)%nat
                Hinvj Htoitem Hvalid Hmax' HfindLj HfindRj Hlookj Hgmaxj Hnecj Hfitsj Hoclkj
                HcurLj HpjLb HcurRj HpjLb
                with "[$Hfresh $Htextj $Hitemsf $Hitemmap]").
    iIntros (arr' nx iidx cells' c) "(%Hile & %Harr'eq & %Hinv' & Htext' & Hitemsf & Hitemmap & %Hpermc & %Hsi & %Hcellsp & %Hnxb & %Hcoupx & %Harrsp2 & %Hclook & %Hcloc2 & %Hchead & %Hcdel2 & %Hcunit)".
    have Hinsins : <[tv.(yjs.Text.inner') := MkTypeState cells' arr']>
                 (<[tv.(yjs.Text.inner') := MkTypeState cells arr]> types)
             = <[tv.(yjs.Text.inner') := MkTypeState cells' arr']> types.
    { rewrite insert_insert. case_decide as Hd; [reflexivity | congruence]. }
    iEval (rewrite Hinsins) in "Hitemmap".
    (* --- mint the op certificate (issue #42): the heap integrate above is
       mirrored by a ghost broadcast(+self-delivery) of the op this item
       denotes, keeping the history coherent with the new [arr']. --- *)
    rewrite (setintegrate_eq_integrate input arr newItem Hinvj Htoitem Hvalid Hmax') in Hsi.
    have HmaskN : ↑histN ⊆ (⊤ : coPset) by solve_ndisj.
    have Hdg : doc_model_get (<[RootId name := arr]> m) (RootId name) = arr
      := docm_get_insert_eq m (RootId name) arr.
    have Htoitem2 : toItem input (doc_model_get (<[RootId name := arr]> m) (RootId name)) = Some newItem
      by rewrite Hdg.
    have Hmax2 : maximalId newItem (doc_model_get (<[RootId name := arr]> m) (RootId name))
      by rewrite Hdg.
    have Hsi2' : integrate input (doc_model_get (<[RootId name := arr]> m) (RootId name)) = Some arr'
      by rewrite Hdg.
    have Hboundj : ∀ (t' : TId) (x : YjsItem A),
        x ∈ doc_model_get (<[RootId name := arr]> m) t' → clientId (item_id x) = uint.nat client →
        (clock (item_id x) < uint.nat (W64 (uint.Z k + j)))%nat.
    { move=> t' x Hx Hcx. rewrite Hclocknit.
      destruct (decide (t' = RootId name)) as [-> | Hne'].
      - rewrite Hdg in Hx. exact (Hctrj x Hx Hcx).
      - rewrite docm_get_insert_ne // in Hx.
        have Hnem : doc_model_get m t' ≠ [] by (move=> Hnil; rewrite Hnil in Hx; set_solver).
        destruct (Hmdom t' Hnem) as (name' & p' & -> & Hbind').
        destruct (Hbindtypes name' p' Hbind') as [ts' Hts'].
        rewrite (Hmtypes name' p' ts' Hbind' Hts') in Hx.
        have := Hctr p' ts' x Hts' Hx Hcx. lia. }
    iMod (history_broadcast γh (uint.nat client) (uint.nat (W64 (uint.Z k + j))) hj
            (<[RootId name := arr]> m) (RootId name) arr'
            input newItem ⊤ HmaskN Htoitem2 Hvalid Hmax2 eq_refl Hboundj Hsi2' Hhcohj
            with "His_hist Hhistj") as "(Hhistj & #Hlbj & #Hcertj & %Hhcohj2)".
    have Hcollm : <[RootId name := arr']> (<[RootId name := arr]> m) = <[RootId name := arr']> m
      by (rewrite insert_insert; case_decide; [reflexivity | congruence]).
    rewrite Hcollm in Hhcohj2.
    pose proof (toItem_input_of_item input arr newItem Htoitem) as Hinputeq.
    iEval (rewrite Hinputeq) in "Hcertj".
    iAssert ([∗ list] it ∈ (ins ++ [newItem]),
               is_op_cert γh (RootId name, OpInsert (input_of_item it)))%I
      with "[Hcertsj]" as "Hcertsj".
    { rewrite big_sepL_snoc. iFrame "Hcertsj". iApply "Hcertj". }
    wp_auto.
    (* place the new item, identify its index *)
    have Hplace : arr' = take (mp + j)%nat arr ++ newItem :: drop (mp + j)%nat arr.
    { rewrite Harr'eq. apply (insert_straddle arr newItem iidx (mp + j)%nat Hinvj ltac:(rewrite -Harr'eq; exact Hinv') Hile Hple).
      - destruct Horig as [(_ & Ho & Hp0) | (li & Hge & Hla & _ & Ho)]; [left; split; [exact Hp0 | rewrite /newItem /=; exact Ho] | right; split; [exact Hge | exists li; split; [exact Hla | rewrite /newItem /=; exact Ho]]].
      - destruct Hrorig as [(_ & Hr & Hpl) | (ri & Hria & _ & Hr)]; [left; split; [exact Hpl | rewrite /newItem /=; exact Hr] | right; exists ri; split; [exact Hria | rewrite /newItem /=; exact Hr]]. }
    have Hnitpos : arr' !! (mp + j)%nat = Some newItem.
    { rewrite Hplace. apply list_lookup_middle. symmetry. apply length_take_le. exact Hple. }
    have Hshift : arr' !! (mp + j + 1)%nat = arr !! (mp + j)%nat.
    { rewrite Hplace. rewrite lookup_app_r; last (rewrite length_take_le; [lia | exact Hple]).
      rewrite length_take_le; last exact Hple.
      replace (mp + j + 1 - (mp + j))%nat with 1%nat by lia.
      simpl. rewrite lookup_drop. f_equal. lia. }
    iDestruct "Htext'" as (yt3 tl3) "(Hp3 & Hdll3 & %Hlen3 & %Hrepr3 & %Hcpar3)".
    have HnitIn : newItem ∈ arr' by exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Hnitpos).
    (* the splice index is the cell cursor: the model index of the new cell
       is mp + j (order theory), and prefix-sum injectivity pins nx *)
    have Hnec0 : Forall (λ c0, ic_run c0 ≠ []) cells.
    { apply Forall_forall. move=> c0 Hc0. exact (proj1 (Hrunwfc c0 Hc0)). }
    have Hiidx0 : iidx = (mp + j)%nat.
    { have Hnit_i0 : arr' !! iidx = Some newItem.
      { rewrite Harrsp2. apply list_lookup_middle. rewrite length_take_le //. }
      destruct (Nat.lt_trichotomy iidx (mp + j)%nat) as [Hlt|[Heq|Hgt]]; [exfalso|exact Heq|exfalso].
      - have HH := invariant_yjsarray_idx.getElem_lt_YjsLt' arr' iidx (mp + j)%nat newItem newItem Hinv' Hnit_i0 Hnitpos Hlt.
        exact (asymmetry.yjs_lt_asymm (yai_closed _ Hinv') (yai_item_set_inv _ Hinv') (itemPtr newItem) (itemPtr newItem) HnitIn HnitIn HH HH).
      - have HH := invariant_yjsarray_idx.getElem_lt_YjsLt' arr' (mp + j)%nat iidx newItem newItem Hinv' Hnitpos Hnit_i0 Hgt.
        exact (asymmetry.yjs_lt_asymm (yai_closed _ Hinv') (yai_item_set_inv _ Hinv') (itemPtr newItem) (itemPtr newItem) HnitIn HnitIn HH HH). }
    have Hnxpos0 : nx = (p + j)%nat.
    { apply (run_flatten_take_length_inj cells nx (p + j)%nat Hnec0 Hnxb HpjLb).
      rewrite Hcoupx Hcoupj Hiidx0 //. }
    have Hcx : cells' !! (p + j)%nat = Some c by (rewrite -Hnxpos0; exact Hclook).
    have Hcloc : ic_loc c = oL2 := Hcloc2.
    have Hcid : run_head c = newItem := Hchead.
    have Hlast_c : ic_run c !! (length (ic_run c) - 1)%nat = Some newItem.
    { have Hcu : length (ic_run c) = 1%nat := Hcunit.
      have Hh := Hcid. rewrite /run_head in Hh.
      rewrite Hcu /=.
      destruct (ic_run c) as [|hc tc]; [simpl in Hcu; discriminate |].
      simpl in Hh. by rewrite /= Hh. }
    wp_for_post.
    (* re-establish the loop invariant for [S j] with [ins ++ [newItem]] *)
    iFrame "Ht His_lb HΦ HisRp Hpendf Hpend".
    iExists (S j), arr', cells', oL2, (ins ++ [newItem]),
      (hj ++ [EvBroadcast (RootId name, OpInsert input);
              EvDeliver (RootId name, OpInsert input)]).
    replace (W64 (uint.Z k + Z.of_nat (S j))) with (w64_word_instance.(word.add) (W64 (uint.Z k + j)) (W64 1)) by word.
    replace (W64 (S j)) with (w64_word_instance.(word.add) (W64 j) (W64 1)) by word.
    iFrame "Hi Htptr Hcontentp Hclientp HoRp Hleftp Hsp Hclient Hclock Hitemsf Hitemmap Htypesf Hdset Hlk Hseq HtypesAuth Htypesmap Hrightp Hrest Hhistj Hcertsj".
    iSplitL "Hp3 Hdll3".
    { iExists yt3, tl3. iFrame "Hp3 Hdll3". iPureIntro. split_and!; [exact Hlen3 | exact Hrepr3 | exact Hcpar3]. }
    have HmroR : mrightorigin = oR.
    { destruct in_rO as [rightOriginId|] eqn:Hino.
      - destruct Hrorig as [(Hrn & _ & _) | (ri & Hria & _ & Hmr)]; [simpl in Hrn; discriminate |].
        destruct Hrightj as [(Hrn2 & _ & _) | (ri2 & rid2 & Hria2 & _ & _ & HoRi)]; [discriminate |].
        rewrite Hmr HoRi. rewrite Hria in Hria2. injection Hria2 as ->. reflexivity.
      - destruct Hrorig as [(_ & Hmr & _) | (ri & _ & Hri & _)]; [| simpl in Hri; discriminate].
        destruct Hrightj as [(_ & HoRl & _) | (ri2 & rid2 & _ & Hros2 & _ & _)]; [| discriminate].
        rewrite Hmr HoRl //. }
    iPureIntro. split_and!.
    - exact Hinv'.
    - rewrite Hplace length_app length_take_le; [| exact Hple]. simpl. rewrite length_drop. lia.
    - rewrite Hcellsp length_app /= length_take_le; last exact Hnxb.
      rewrite length_drop. lia.
    - lia.
    - intros x Hx Hc. rewrite Hplace in Hx.
      apply elem_of_app in Hx as [Hxt | Hxc].
      + have Hxa : ArrSet arr x by (rewrite -(take_drop (mp + j)%nat arr); apply elem_of_app; left; exact Hxt).
        have := Hctrj x Hxa Hc. lia.
      + apply elem_of_cons in Hxc as [-> | Hxd].
        * rewrite /newItem /in_id1 /=. rewrite Hclocknit. lia.
        * have Hxa : ArrSet arr x by (rewrite -(take_drop (mp + j)%nat arr); apply elem_of_app; right; exact Hxd).
          have := Hctrj x Hxa Hc. lia.
    - right. exists c, newItem. split_and!.
      + replace (p + S j - 1)%nat with (p + j)%nat by lia. exact Hcx.
      + exact Hcloc.
      + replace (mp + S j - 1)%nat with (mp + j)%nat by lia. exact Hnitpos.
      + exact Hlast_c.
      + lia.
      + intros Hsj. lia.
      + intros j' Hsj. injection Hsj as ->. rewrite lookup_app_r; [| rewrite Hinslen; lia]. rewrite Hinslen. rewrite Nat.sub_diag. reflexivity.
    - destruct Hrightj as [(Hrn & HoRl & Hpl) | (ri & rightOriginId & Hria & Hros & Hrii & HoRi)].
      + left. split_and!; [exact Hrn | exact HoRl |].
        rewrite Hplace length_app length_take_le; [| exact Hple]. simpl. rewrite length_drop. lia.
      + right. exists ri, rightOriginId. split_and!.
        * replace (mp + S j)%nat with (mp + j + 1)%nat by lia. rewrite Hshift. exact Hria.
        * exact Hros.
        * exact Hrii.
        * exact HoRi.
    - rewrite length_app Hinslen /=. lia.
    - intros i it Hii.
      destruct (decide (i < length ins)%nat) as [Hilt | Hige].
      + rewrite lookup_app_l in Hii; [| exact Hilt].
        have [Hitin [Hcont [Hid [Hror [Horg Hchain]]]]] := Hins i it Hii.
        split_and!.
        * rewrite Hplace. rewrite -(take_drop (mp + j)%nat arr) in Hitin. apply elem_of_app in Hitin as [H1 | H2]; [apply elem_of_app; left; exact H1 | apply elem_of_app; right; apply elem_of_cons; right; exact H2].
        * exact Hcont.
        * exact Hid.
        * exact Hror.
        * exact Horg.
        * intros j' itj Hisj Hlookj'. rewrite lookup_app_l in Hlookj'; [| lia]. exact (Hchain j' itj Hisj Hlookj').
      + have Hieq : i = length ins.
        { apply lookup_lt_Some in Hii. rewrite length_app /= in Hii. lia. }
        rewrite Hieq lookup_app_r in Hii; [| lia]. rewrite Nat.sub_diag /= in Hii. injection Hii as <-.
        split_and!.
        * exact HnitIn.
        * intros b0 Hcsb. have Hsn : sint.nat (W64 j) = j by word. rewrite Hsn in Hb. rewrite Hieq Hinslen in Hcsb. rewrite Hb in Hcsb. injection Hcsb as Hbb. rewrite /newItem /= Hbb //.
        * rewrite /newItem /in_id1 /=. rewrite Hieq Hinslen Hclocknit. reflexivity.
        * rewrite /newItem /=. exact HmroR.
        * intros Hi0. rewrite /newItem /=. rewrite Hieq Hinslen in Hi0.
          destruct Horig as [(_ & Hmo & Hp0) | (li & Hge & Hla & _ & Hmo)].
          -- rewrite Hmo. destruct HoLspec as [[HoLF _] | (lc2 & li2 & Hge2 & _)]; [rewrite HoLF // | lia].
          -- rewrite Hmo. destruct Hleftj as [[_ Hp0] | (lc2 & li2 & _ & _ & Hla2 & _ & _ & Hlk0 & _)].
             { exfalso. have Hp00 : p = 0%nat by lia. have Hj00 : j = 0%nat by lia.
               move: Hge. rewrite Hmpdef Hp00 take_0 /run_flatten /= Hj00. lia. }
             have -> : li = li2 by (rewrite Hla in Hla2; injection Hla2 as ->; reflexivity). exact (Hlk0 Hi0).
        * intros j' itj Hisj Hlookj'. rewrite /newItem /=. rewrite Hieq Hinslen in Hisj. rewrite lookup_app_l in Hlookj'; [| rewrite Hinslen; lia].
          destruct Horig as [(_ & _ & Hp0) | (li & Hge & Hla & _ & Hmo)]; [lia |].
          rewrite Hmo. destruct Hleftj as [[_ Hp0] | (lc2 & li2 & _ & _ & Hla2 & _ & _ & _ & Hlk)]; [lia |]. have -> : li = li2 by (rewrite Hla in Hla2; injection Hla2 as ->; reflexivity). have Hli2 := Hlk j' Hisj. rewrite Hli2 in Hlookj'. injection Hlookj' as <-. reflexivity.
    - intros x Hx. have Hxa := Hsubold x Hx. rewrite Hplace. rewrite -(take_drop (mp + j)%nat arr) in Hxa. apply elem_of_app in Hxa as [H1 | H2]; [apply elem_of_app; left; exact H1 | apply elem_of_app; right; apply elem_of_cons; right; exact H2].
    - (* the loop-constant [right] pointer's index shifts across the splice *)
      rewrite Hcellsp Hnxpos0.
      have Hpjlen : ((p + j) <= length cells)%nat by rewrite -Hnxpos0; exact Hnxb.
      have -> : (Z.of_nat (p + S j)) = (Z.of_nat (p + j) + 1)%Z by lia.
      rewrite (node_loc_splice_ge cells c (p + j)%nat (Z.of_nat (p + j)) ltac:(lia) Hpjlen).
      exact Hrgtj.
    - (* Hcoupj at S j: the splice adds one unit cell at the cursor *)
      replace (p + S j)%nat with (S (p + j))%nat by lia.
      rewrite Hcellsp Hnxpos0.
      have Hpjlen2 : ((p + j) <= length cells)%nat by rewrite -Hnxpos0; exact Hnxb.
      have Htk : take (S (p + j)) (take (p + j)%nat cells ++ c :: drop (p + j)%nat cells)
               = take (p + j)%nat cells ++ [c].
      { rewrite take_app_ge; last (rewrite length_take_le; lia).
        rewrite length_take_le; last lia.
        replace (S (p + j) - (p + j))%nat with 1%nat by lia. done. }
      rewrite Htk run_flatten_app length_app Hcoupj.
      have Hcu1 : length (ic_run c) = 1%nat := Hcunit.
      rewrite run_flatten_cons length_app Hcu1 /run_flatten /=. lia.
    - intros c0 Hc0 Hcc0.
      have Hac_step : all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells' arr']> types)
                    ≡ₚ all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells arr]> types) ++ [c]
        by (rewrite -Hinsins; apply (all_cells_insert_snoc (<[tv.(yjs.Text.inner') := MkTypeState cells arr]> types)
               (tv.(yjs.Text.inner')) cells arr cells' arr' c Hlookj Hpermc)).
      rewrite Hac_step in Hc0. apply elem_of_app in Hc0 as [Hold | Hnew].
      + have := Hcellbnd c0 Hold Hcc0. lia.
      + apply list_elem_of_singleton in Hnew as ->.
        have Hcu1 : length (ic_run c) = 1%nat := Hcunit.
        rewrite /cell_clock Hcid Hcu1 /newItem /in_id1 /=. rewrite Hclocknit. word.
    - (* Hlocdupj at S j *)
      have Hac_step2 : all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells' arr']> types)
                    ≡ₚ all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells arr]> types) ++ [c]
        by (rewrite -Hinsins; apply (all_cells_insert_snoc (<[tv.(yjs.Text.inner') := MkTypeState cells arr]> types)
               (tv.(yjs.Text.inner')) cells arr cells' arr' c Hlookj Hpermc)).
      apply (nodup_locs_snoc _ _ c Hac_step2); [| exact Hlocdupj].
      rewrite Hcloc. exact Hfr.
    - (* Hrangedisjj at S j *)
      have Hac_step2 : all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells' arr']> types)
                    ≡ₚ all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells arr]> types) ++ [c]
        by (rewrite -Hinsins; apply (all_cells_insert_snoc (<[tv.(yjs.Text.inner') := MkTypeState cells arr]> types)
               (tv.(yjs.Text.inner')) cells arr cells' arr' c Hlookj Hpermc)).
      apply (rangedisj_snoc _ _ c Hac_step2); [| exact Hrangedisjj].
      move=> c0 Hc0 Hcc0.
      have Hcc0' : cell_client c0 = W64 (clientId (item_id newItem)).
      { rewrite Hcc0 /cell_client Hcid //. }
      have Hle := proj2 (Hgmaxj c0 Hc0 Hcc0').
      have Hck : cell_clock c = W64 (clock (item_id newItem)) by rewrite /cell_clock Hcid //.
      rewrite Hck. lia.
    - (* Hrunfitsj at S j *)
      have Hac_step2 : all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells' arr']> types)
                    ≡ₚ all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells arr]> types) ++ [c]
        by (rewrite -Hinsins; apply (all_cells_insert_snoc (<[tv.(yjs.Text.inner') := MkTypeState cells arr]> types)
               (tv.(yjs.Text.inner')) cells arr cells' arr' c Hlookj Hpermc)).
      apply (fits_snoc _ _ c Hac_step2); [| exact Hrunfitsj].
      have Hu1 : length (ic_run c) = 1%nat := Hcunit.
      rewrite /cell_fits /cell_clock Hcid Hu1 /newItem /in_id1 /=. rewrite Hclocknit. word.
    - (* Horiginclkj at S j: the new head [newItem]'s same-client origin is an
         existing doc item below the local clock counter *)
      have Hac_step2 : all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells' arr']> types)
                    ≡ₚ all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells arr]> types) ++ [c]
        by (rewrite -Hinsins; apply (all_cells_insert_snoc (<[tv.(yjs.Text.inner') := MkTypeState cells arr]> types)
               (tv.(yjs.Text.inner')) cells arr cells' arr' c Hlookj Hpermc)).
      apply (originclk_snoc _ _ c Hac_step2); [| exact Horiginclkj].
      move=> originId Hoid Hcl.
      rewrite Hcid in Hoid Hcl. rewrite Hcid.
      destruct Horig as [(Hon & Ho & _) | (li & Hge & Hla & Hom & Ho)].
      + exfalso. move: Hoid. rewrite /newItem /= Ho //.
      + move: Hoid. rewrite /newItem /= Ho /origin_id /=. move=> [= Hoideq].
        rewrite -Hoideq in Hcl. rewrite -Hoideq.
        have Hliarr : li ∈ arr := list_elem_of_lookup_2 _ _ _ Hla.
        have Hclli : clientId (item_id li) = uint.nat client := Hcl.
        have := Hctrj li Hliarr Hclli.
        rewrite /newItem /in_id1 /= Hclocknit. lia.
    - exact Hhcohj2. }
  (* loop exit: the whole run is integrated; rebuild [store_inv] and return. *)
  have Hjend : (j = length cs)%nat by word.
  rewrite decide_False; [| done]. wp_auto.
  rewrite decide_True; [| reflexivity]. wp_auto.
  have Hk'val : uint.nat (W64 (uint.Z k + j)) = (uint.nat k + j)%nat by word.
  have Hsubarr : list_to_set (ts.(ty_arr)) ⊆ (list_to_set arr : gset (YjsItem A)).
  { intros y Hy. rewrite elem_of_list_to_set in Hy. rewrite elem_of_list_to_set. apply Hsubold. exact Hy. }
  have Hmk : ((λ ts0 : type_state, (list_to_set (ty_arr ts0) : gset (YjsItem A))) <$> types) !! (tv.(yjs.Text.inner')) = Some (list_to_set ts.(ty_arr)).
  { rewrite lookup_fmap Htsp //. }
  iMod (auth_gmap_gset_grow γs.(sn_seq) _ (tv.(yjs.Text.inner')) (list_to_set ts.(ty_arr)) (list_to_set arr) Hmk Hsubarr with "Hseq") as "[Hseq Hfrag]".
  iAssert ([∗ map] kk↦y ∈ <[tv.(yjs.Text.inner') := MkTypeState cells arr]> types,
      own_ytype_cells kk (DfracOwn 1) (ty_cells y) (ty_arr y) ∗
      ⌜YjsArrInvariant (ty_arr y)⌝)%I
    with "[Htextj Hrest]" as "Htypes".
  { rewrite -insert_delete_eq.
    rewrite big_sepM_insert; last apply lookup_delete_eq.
    iFrame "Hrest". simpl. iFrame "Htextj".
    iPureIntro. exact Hinvj. }
  wp_apply (wp_Store__wunlock with "[$His_store $Hlk Hclient Hclock Hitemsf Hitemmap Htypesf Htypesmap Hdset Hpendf Hpend Hseq HtypesAuth Htypes Hhistj]").
  { iNext. iExists client, (W64 (uint.Z k + j)), items_mref, types_mref, dset,
      pend_sl,
      (<[tv.(yjs.Text.inner') := MkTypeState cells arr]> types), bind, hj,
      (<[RootId name := arr]> m), pend.
    iSplitR "Hseq Htypes"; last first.
    { rewrite /store_inv_ro fmap_insert /=. iFrame "Hseq Htypes". }
    iFrame "Hclient Hclock Hitemsf Hitemmap Htypesf Htypesmap Hdset Hpendf Hpend Hhistj HtypesAuth Hbinds".
    iFrame "Hpendcert Hpendroot".
    iPureIntro. split_and!.
    - exact Hpendbnd.
    - intros parent' ts' x Hlook Hxin Hxc. rewrite Hk'val.
      destruct (decide (parent' = tv.(yjs.Text.inner'))) as [-> | Hne].
      + rewrite lookup_insert in Hlook. rewrite decide_True in Hlook; [| reflexivity]. injection Hlook as <-. simpl in Hxin. exact (Hctrj x Hxin Hxc).
      + rewrite lookup_insert_ne in Hlook; last (intros HH; apply Hne; symmetry; exact HH).
        have := Hctr parent' ts' x Hlook Hxin Hxc. lia.
    - intros c0 Hc0 Hcc0.
      have Hkw : uint.Z (W64 (uint.Z k + Z.of_nat j)) = uint.Z k + Z.of_nat j by word.
      rewrite Hkw. exact (Hcellbnd c0 Hc0 Hcc0).
    - exact Hlocdupj.
    - exact Hrangedisjj.
    - exact Hrunfitsj.
    - exact Horiginclkj.
    - move=> name' p' Hb'. destruct (Hbindtypes name' p' Hb') as [ts' Hts'].
      destruct (decide (p' = tv.(yjs.Text.inner'))) as [-> | Hne];
        [rewrite lookup_insert_eq; by eexists
        | rewrite lookup_insert_ne; [by eexists | congruence]].
    - exact Hbindinj.
    - move=> p' [ts' Hts'].
      destruct (decide (p' = tv.(yjs.Text.inner'))) as [-> | Hne].
      + exact (Htypesbound (tv.(yjs.Text.inner')) (ex_intro _ ts Htsp)).
      + rewrite lookup_insert_ne in Hts'; [| congruence].
        exact (Htypesbound p' (ex_intro _ ts' Hts')).
    - exact Hhcohj.
    - move=> name' p' ts' Hb' Hts'.
      destruct (decide (p' = tv.(yjs.Text.inner'))) as [-> | Hne].
      + have Heqn : name' = name := Hbindinj name' name _ Hb' Hbindlk.
        subst name'. rewrite lookup_insert_eq in Hts'. injection Hts' as <-.
        rewrite docm_get_insert_eq //.
      + rewrite lookup_insert_ne in Hts'; [| congruence].
        rewrite docm_get_insert_ne.
        * exact (Hmtypes name' p' ts' Hb' Hts').
        * move=> Heqr. injection Heqr as Heqn. subst name'.
          rewrite Hbindlk in Hb'. injection Hb' as He'. exact (Hne (eq_sym He')).
    - move=> t' Hne'.
      destruct (decide (t' = RootId name)) as [-> | Hnr].
      + exists name, (tv.(yjs.Text.inner')). split; [reflexivity | exact Hbindlk].
      + rewrite docm_get_insert_ne // in Hne'. exact (Hmdom t' Hne'). }
  iApply ("HΦ" $! arr ins (uint.nat client) (uint.nat k) oL oR).
  iSplitL "Hfrag Ht".
  { iExists tv, tv.(yjs.Text.store'), tv.(yjs.Text.inner'). iFrame "Ht His_store His_hist Hbind Hfrag". iPureIntro. split_and!; [reflexivity | reflexivity | exact (yai_sorted _ Hinvj)]. }
  iSplit.
  { iPureIntro. apply (sorted_subseteq_sublist L arr Hinvj Hsorted (yai_sorted _ Hinvj)).
    intros x Hx. have Hxg : x ∈ (list_to_set arr : gset (YjsItem A)).
    { apply Hsubarr. apply HLsub. rewrite elem_of_list_to_set. exact Hx. }
    rewrite elem_of_list_to_set in Hxg. exact Hxg. }
  iSplit.
  { iPureIntro. right. rewrite Hinslen. exact Hjend. }
  iSplit.
  { iPureIntro. intros i it b Hii Hcsb.
    have [Hitin [Hcont [Hid [Hror [Horg Hchain]]]]] := Hins i it Hii.
    split_and!.
    - exact Hitin.
    - intros HinL. have HitTs : it ∈ ts.(ty_arr).
      { have Htg : it ∈ (list_to_set ts.(ty_arr) : gset (YjsItem A)).
        { apply HLsub. rewrite elem_of_list_to_set. exact HinL. }
        rewrite elem_of_list_to_set in Htg. exact Htg. }
      have Hclk := Hctr (tv.(yjs.Text.inner')) ts it Htsp HitTs. rewrite Hid in Hclk. simpl in Hclk. specialize (Hclk eq_refl). lia.
    - exact (Hcont b Hcsb).
    - exact Hid.
    - exact Hror.
    - exact Horg.
    - exact Hchain. }
  iFrame "Hcertsj".
Qed.

(* ===== Text.Delete: WP proof ============================================ *)

(** [Text.Delete] tombstones a range of visible characters and preserves the
    (persistent) document handle [is_Text t L] UNCHANGED: deletion never
    removes or reorders model items (it only flips [ic_deleted] bits, splitting
    a run cell when a range boundary lands inside it), so the model item list
    [ty_arr] (hence [YjsArrInvariant] and the item-set lower bound [L]) is
    untouched: splits preserve the flatten, flips only the tombstone bit. Only
    the heap cell layer and the visible length [yType.len] change. Proof shape:
    take the store lock, extract THIS text, [findPos] to the cursor (splitting
    at the start offset via [splitNode] when it lands mid-run, issue #28 M3),
    then a loop that walks forward tombstoning whole visible runs
    ([own_dll_update_gen] in place, [num_visible_flip_run] shrinks the count by
    the run length) and splits once more at the range end when the budget ends
    inside a run; the pool invariants transport across splits
    ([split_pool_*]) and flips ([locs_run_perm_*]); rebuild [store_inv] with
    the same [ty_arr] (so the auth [Hseq] / counter [Hctr] are preserved),
    Unlock, and return [is_Text t L]. *)
Lemma wp_Text__Delete (t : loc) (index len : w64) (γs : store_names) (γh : history_names)
    (name : P) (L : list (YjsItem A)) :
  {{{ is_pkg_init yjs ∗ is_Text t γs γh name L }}}
    t @! (go.PointerType yjs.Text) @! "Delete" #index #len
  {{{ RET #(); is_Text t γs γh name L }}}.
Proof.
  (* ---- Prologue: take the store lock, extract THIS text. ---- *)
  wp_start as "Hpre". iNamed "Hpre".
  iDestruct "His_store" as "#His_store".
  wp_auto.
  subst s_loc.
  wp_apply (wp_Store__wlock with "[$His_store]"). iIntros "[Hlk Hinv]".
  iNamed "Hinv". iNamed "Hexcl". iNamed "Hro".
  iDestruct (auth_gmap_gset_lookup with "Hseq His_lb") as %(S' & HmS & HLsub).
  rewrite lookup_fmap in HmS.
  apply fmap_Some in HmS as (ts & Htsp & ->).
  (* the registry binds [name] to this text; the history is untouched by
     Delete ([ty_arr] is tombstone-only), so [Hhist]/[Hhcoh] just thread. *)
  iDestruct (ghost_map_lookup with "HtypesAuth Hbind") as %Hbindlk.
  have Hmt : doc_model_get m (RootId name) = ty_arr ts := Hmtypes name parent ts Hbindlk Htsp.
  iDestruct (big_sepM_delete _ _ _ _ Htsp with "Htypes") as "[Hbody Hrest]".
  iDestruct "Hbody" as "(Htext & %Hinvarr)".
  iDestruct "Htext" as (yt0 tl0) "(Hparent & Hdll & %Hlen & %Hrepr & %Hcpar)".
  subst parent. wp_auto.
  (* findPos: locate the cursor [right] at some list position [p]. *)
  iAssert (own_ytype_cells (tv.(yjs.Text.inner')) (DfracOwn 1) ts.(ty_cells) ts.(ty_arr)) with "[Hparent Hdll]" as "Htext".
  { iExists yt0, tl0. iFrame "Hparent Hdll". iPureIntro. split_and!; [exact Hlen | exact Hrepr | exact Hcpar]. }
  wp_apply (wp_yType__findPos (tv.(yjs.Text.inner')) (DfracOwn 1) ts.(ty_cells) ts.(ty_arr) index with "[$Htext]").
  iIntros (lft rgt p off) "(Htext & %Hpbound & %Hlftloc & %Hrgtloc & %Hoff)".
  wp_auto.
  (* normalize the position (issue #28 M3): when the index lands inside a
     multi-char run, split the straddled node at the offset so the insertion
     point sits on a cell boundary. The flatten is unchanged, so only the
     cell layer and the cursor move; both branches rebind the state under
     the shared boundary-form names. *)
  wp_if_join (λ v : val, ⌜v = execute_val⌝ ∗
      ∃ (types1 : gmap loc type_state) (ts1 : type_state) (p1 : nat),
      "s" ∷ s_ptr ↦ tv.(yjs.Text.store') ∗
      "Hitemsf" ∷ (tv.(yjs.Text.store')).[yjs.store.t, "items"] ↦ items_mref ∗
      "Hitemmap" ∷ own_item_map items_mref (DfracOwn 1) types1 ∗
      "Hrest" ∷ ([∗ map] kk↦y ∈ delete (tv.(yjs.Text.inner')) types1,
          own_ytype_cells kk (DfracOwn 1) y.(ty_cells) y.(ty_arr) ∗
          ⌜YjsArrInvariant y.(ty_arr)⌝) ∗
      "Htext" ∷ own_ytype_cells (tv.(yjs.Text.inner')) (DfracOwn 1) ts1.(ty_cells) ts1.(ty_arr) ∗
      "left" ∷ left_ptr ↦ node_loc ts1.(ty_cells) (Z.of_nat p1 - 1) ∗
      "right" ∷ right_ptr ↦ node_loc ts1.(ty_cells) (Z.of_nat p1) ∗
      "%Htsp1" ∷ ⌜types1 !! tv.(yjs.Text.inner') = Some ts1⌝ ∗
      "%Harr1" ∷ ⌜ty_arr ts1 = ty_arr ts⌝ ∗
      "%Hdomeq1" ∷ ⌜∀ p', p' ≠ tv.(yjs.Text.inner') → types1 !! p' = types !! p'⌝ ∗
      "%Hpb1" ∷ ⌜(p1 <= length ts1.(ty_cells))%nat⌝ ∗
      "%Hcellctr1" ∷ ⌜∀ c0, c0 ∈ all_cells types1 → cell_client c0 = client →
          (uint.Z (cell_clock c0) + Z.of_nat (length (ic_run c0)) <= uint.Z k)%Z⌝ ∗
      "%Hlocdup1" ∷ ⌜NoDup (ic_loc <$> all_cells types1)⌝ ∗
      "%Hrangedisj1" ∷ ⌜cells_range_disjoint (all_cells types1)⌝ ∗
      "%Hrunfits1" ∷ ⌜∀ c0, c0 ∈ all_cells types1 → cell_fits c0⌝ ∗
      "%Horiginclk1" ∷ ⌜∀ c0, c0 ∈ all_cells types1 → cell_origin_clk c0⌝)%I
      with "[s left right offset Htext Hrest Hitemsf Hitemmap]".
  { (* offset > 0: split [left] at the offset *)
    destruct Hoff as [Hoffeq | (Hoffpos & Hpge1 & (cw & Hcw & Hcwdel & Hofflen))];
      first (exfalso; subst off; move: l; word).
    have Hts_eta : MkTypeState ts.(ty_cells) ts.(ty_arr) = ts by (destruct ts; reflexivity).
    have Htspm : types !! tv.(yjs.Text.inner') = Some (MkTypeState ts.(ty_cells) ts.(ty_arr))
      by rewrite Hts_eta.
    have Hdiffb : (0 < uint.nat off < length (ic_run cw))%nat by word.
    have Hfits64 : ∀ c0, c0 ∈ all_cells types →
        (uint.Z (cell_clock c0) + Z.of_nat (length (ic_run c0)) < 2^64)%Z.
    { move=> c0 Hc0. exact (Hrunfits c0 Hc0). }
    have Hcwmem : cw ∈ all_cells types.
    { apply all_cells_elem_of.
      exists (tv.(yjs.Text.inner')), (MkTypeState ts.(ty_cells) ts.(ty_arr)).
      split; [exact Htspm | exact (list_elem_of_lookup_2 _ _ _ Hcw)]. }
    have Hdisjcw : ∀ c0, c0 ∈ all_cells types → cell_client c0 = cell_client cw →
        ic_loc c0 ≠ ic_loc cw →
       (uint.Z (cell_clock c0) + Z.of_nat (length (ic_run c0)) <= uint.Z (cell_clock cw))%Z ∨
       (uint.Z (cell_clock cw) + Z.of_nat (length (ic_run cw)) <= uint.Z (cell_clock c0))%Z.
    { move=> c0 Hc0 Hcc Hne. exact (Hrangedisj c0 cw Hc0 Hcwmem Hcc Hne). }
    (* pack the store big-sep back together for the splitNode call *)
    iAssert ([∗ map] kk↦y ∈ types,
        own_ytype_cells kk (DfracOwn 1) (ty_cells y) (ty_arr y) ∗
        ⌜YjsArrInvariant (ty_arr y)⌝)%I with "[Htext Hrest]" as "Htypes".
    { rewrite -{2}(insert_id types (tv.(yjs.Text.inner')) ts Htsp) -insert_delete_eq.
      rewrite big_sepM_insert; last apply lookup_delete_eq.
      iFrame "Hrest". iSplitL "Htext"; [iExact "Htext" | iPureIntro; exact Hinvarr]. }
    iDestruct (types_cells_id_bounds2 with "Htypes") as %Hbnds.
    have Hckbnd : (Z.of_nat (clock (item_id (run_head cw))) < 2^64)%Z := proj2 (Hbnds cw Hcwmem).
    iDestruct (types_runs_wf2 with "Htypes") as %Hrunwfall.
    have Hrunwfcw : run_wf (ic_run cw) := Hrunwfall cw Hcwmem.
    have Hndl : node_loc ts.(ty_cells) (Z.of_nat p - 1) = ic_loc cw.
    { rewrite /node_loc decide_True; last lia.
      have -> : Z.to_nat (Z.of_nat p - 1) = (p - 1)%nat by lia.
      rewrite Hcw //. }
    rewrite Hndl.
    wp_apply (wp_store__splitNode (tv.(yjs.Text.store')) items_mref types
                (tv.(yjs.Text.inner')) ts.(ty_cells) ts.(ty_arr) (p - 1)%nat cw off
                Htspm Hcw Hdiffb Hfits64 Hlocdup Hdisjcw
                with "[$Hitemsf $Hitemmap $Htypes]").
    iIntros (rloc) "(%Hrlocnn & %Hrlocfresh & Hitemsf & Hitemmap & Htypes)".
    wp_auto.
    set (cells1 := split_cells ts.(ty_cells) (p - 1)%nat (uint.nat off) rloc).
    set (ts1 := MkTypeState cells1 ts.(ty_arr)).
    iDestruct (big_sepM_delete _ _ (tv.(yjs.Text.inner')) ts1 with "Htypes") as "[[Htext %Hinvarr1] Hrest]";
      first apply lookup_insert_eq.
    rewrite delete_insert_eq.
    (* pool transports across the split *)
    have Hsub1 := split_pool_subrange types (tv.(yjs.Text.inner')) ts.(ty_cells) ts.(ty_arr)
                    (p - 1)%nat cw (uint.nat off) rloc Htspm Hcw Hrunwfcw Hdiffb Hckbnd
                    (Hrunfits cw Hcwmem).
    have Hcellctr1 : ∀ c0, c0 ∈ all_cells (<[tv.(yjs.Text.inner') := ts1]> types) →
        cell_client c0 = client →
        (uint.Z (cell_clock c0) + Z.of_nat (length (ic_run c0)) <= uint.Z k)%Z.
    { move=> c0 Hc0 Hcc.
      destruct (Hsub1 c0 Hc0) as (cold & Hcold & Hccold & Hlo & Hhi).
      have := Hcellctr cold Hcold ltac:(congruence). lia. }
    have Hlocdup1 : NoDup (ic_loc <$> all_cells (<[tv.(yjs.Text.inner') := ts1]> types))
      := split_pool_locdup types (tv.(yjs.Text.inner')) ts.(ty_cells) ts.(ty_arr)
           (p - 1)%nat cw (uint.nat off) rloc Htspm Hcw Hrlocfresh Hlocdup.
    have Hrangedisj1 : cells_range_disjoint (all_cells (<[tv.(yjs.Text.inner') := ts1]> types))
      := split_pool_rangedisj types (tv.(yjs.Text.inner')) ts.(ty_cells) ts.(ty_arr)
           (p - 1)%nat cw (uint.nat off) rloc Htspm Hcw Hrunwfcw Hdiffb Hckbnd
           (Hrunfits cw Hcwmem) Hlocdup Hrangedisj.
    have Hrunfits1 : ∀ c0, c0 ∈ all_cells (<[tv.(yjs.Text.inner') := ts1]> types) → cell_fits c0.
    { move=> c0 Hc0. rewrite /cell_fits.
      exact (split_pool_fits types (tv.(yjs.Text.inner')) ts.(ty_cells) ts.(ty_arr)
               (p - 1)%nat cw (uint.nat off) rloc Htspm Hcw Hrunwfcw Hdiffb Hckbnd
               Hfits64 c0 Hc0). }
    have Horiginclk1 : ∀ c0, c0 ∈ all_cells (<[tv.(yjs.Text.inner') := ts1]> types) → cell_origin_clk c0
      := split_pool_originclk types (tv.(yjs.Text.inner')) ts.(ty_cells) ts.(ty_arr)
           (p - 1)%nat cw (uint.nat off) rloc Htspm Hcw Hrunwfcw Hdiffb Horiginclk.
    (* the two halves sit at cell cursors p-1 / p of the split list *)
    have Hcl1 : cells1 !! (p - 1)%nat = Some (split_cell_left cw (uint.nat off))
      := split_cells_lookup_left ts.(ty_cells) (p - 1)%nat (uint.nat off) rloc cw Hcw.
    have Hcr1 : cells1 !! p = Some (split_cell_right cw (uint.nat off) rloc).
    { have H := split_cells_lookup_right ts.(ty_cells) (p - 1)%nat (uint.nat off) rloc cw Hcw.
      have -> : p = S (p - 1)%nat by lia.
      exact H. }
    have Hlen1 : length cells1 = S (length ts.(ty_cells))
      := split_cells_length ts.(ty_cells) (p - 1)%nat (uint.nat off) rloc cw Hcw.
    have Hleftloc1 : ic_loc cw = node_loc cells1 (Z.of_nat p - 1).
    { rewrite /node_loc decide_True; last lia.
      have -> : Z.to_nat (Z.of_nat p - 1) = (p - 1)%nat by lia.
      rewrite Hcl1 //. }
    have Hrightloc1 : rloc = node_loc cells1 (Z.of_nat p).
    { rewrite /node_loc decide_True; last lia.
      rewrite Nat2Z.id Hcr1 //. }
    iSplitR; first done.
    iExists (<[tv.(yjs.Text.inner') := ts1]> types), ts1, p.
    iEval (rewrite Hleftloc1) in "left". iEval (rewrite Hrightloc1) in "right".
    rewrite delete_insert_eq.
    iFrame "s Hitemsf Hitemmap Hrest Htext left right".
    iPureIntro. split_and!.
    - apply lookup_insert_eq.
    - reflexivity.
    - move=> p' Hne. rewrite lookup_insert_ne //.
    - rewrite /ts1 /= Hlen1. lia.
    - exact Hcellctr1.
    - exact Hlocdup1.
    - exact Hrangedisj1.
    - exact Hrunfits1.
    - exact Horiginclk1. }
  { (* offset = 0: the index already sits on a boundary *)
    have Hoffeq : off = W64 0.
    { destruct Hoff as [-> | (Hoffpos & _)]; [done | exfalso; apply n; word]. }
    subst off.
    iSplitR; first done.
    iExists types, ts, p.
    iFrame "s Hitemsf Hitemmap Hrest Htext left right".
    iPureIntro. split_and!;
      [exact Htsp | reflexivity | move=> p' _; reflexivity | exact Hpbound
      | exact Hcellctr | exact Hlocdup | exact Hrangedisj | exact Hrunfits | exact Horiginclk]. }
  iIntros (v) "[%Hv HQ]". subst v. iNamed "HQ".
  (* rebind the normalized state under the boundary-form names: everything
     the remaining proof consumes is restated at (types1, ts1, p1), the old
     cell layer is cleared, and the primed names take the old ones over *)
  have Hctr1 : ∀ parent' ts' x, types1 !! parent' = Some ts' → x ∈ ty_arr ts' →
      clientId (item_id x) = uint.nat client → (clock (item_id x) < uint.nat k)%nat.
  { move=> parent' ts' x Hlk Hx Hcx.
    destruct (decide (parent' = tv.(yjs.Text.inner'))) as [-> | Hne].
    - rewrite Htsp1 in Hlk. injection Hlk as <-. rewrite Harr1 in Hx.
      exact (Hctr _ _ x Htsp Hx Hcx).
    - rewrite (Hdomeq1 parent' Hne) in Hlk. exact (Hctr _ _ x Hlk Hx Hcx). }
  have Hbindtypes1 : ∀ name' p', bind !! name' = Some p' → is_Some (types1 !! p').
  { move=> n' p' Hb. destruct (decide (p' = tv.(yjs.Text.inner'))) as [-> | Hne].
    - rewrite Htsp1. by eexists.
    - rewrite (Hdomeq1 _ Hne). exact (Hbindtypes _ _ Hb). }
  have Htypesbound1 : ∀ p', is_Some (types1 !! p') → ∃ name', bind !! name' = Some p'.
  { move=> p' [ts' Hts']. destruct (decide (p' = tv.(yjs.Text.inner'))) as [-> | Hne].
    - exact (Htypesbound _ (ex_intro _ ts Htsp)).
    - rewrite (Hdomeq1 _ Hne) in Hts'. exact (Htypesbound _ (ex_intro _ _ Hts')). }
  have Hmtypes1 : ∀ name' p' ts', bind !! name' = Some p' → types1 !! p' = Some ts' →
      doc_model_get m (RootId name') = ty_arr ts'.
  { move=> n' p' ts' Hb Hts'. destruct (decide (p' = tv.(yjs.Text.inner'))) as [-> | Hne].
    - rewrite Htsp1 in Hts'. injection Hts' as <-. rewrite Harr1.
      exact (Hmtypes n' _ ts Hb Htsp).
    - rewrite (Hdomeq1 _ Hne) in Hts'. exact (Hmtypes n' p' ts' Hb Hts'). }
  have HLsub1 : (list_to_set L : gset (YjsItem A)) ⊆ list_to_set (ty_arr ts1)
    by rewrite Harr1.
  have Hmt1 : doc_model_get m (RootId name) = ty_arr ts1 by rewrite Harr1.
  have Hinvarr1 : YjsArrInvariant (ty_arr ts1) by rewrite Harr1.
  have Hseqeq1 : ((λ ts0 : type_state, (list_to_set ts0.(ty_arr) : gset (YjsItem A))) <$> types1)
               = ((λ ts0 : type_state, (list_to_set ts0.(ty_arr) : gset (YjsItem A))) <$> types).
  { apply map_eq. move=> p'. destruct (decide (p' = tv.(yjs.Text.inner'))) as [-> | Hne].
    - rewrite !lookup_fmap Htsp1 Htsp /= Harr1 //.
    - rewrite !lookup_fmap (Hdomeq1 _ Hne) //. }
  iEval (rewrite -Hseqeq1) in "Hseq".
  clear Hctr Hbindtypes Htypesbound Hmtypes HLsub Hmt Hinvarr Htsp Hpbound
        Hcellctr Hlocdup Hrangedisj Hrunfits Horiginclk Hoff Hlftloc Hrgtloc
        Hlen Hrepr Hcpar.
  clear Harr1 Hdomeq1 Hseqeq1.
  clear off lft rgt yt0 tl0.
  clear p ts types.
  rename types1 into types. rename ts1 into ts. rename p1 into p.
  rename Htsp1 into Htsp. rename Hpb1 into Hpbound.
  rename Hctr1 into Hctr. rename Hcellctr1 into Hcellctr.
  rename Hlocdup1 into Hlocdup. rename Hrangedisj1 into Hrangedisj.
  rename Hrunfits1 into Hrunfits. rename Horiginclk1 into Horiginclk.
  rename Hbindtypes1 into Hbindtypes. rename Htypesbound1 into Htypesbound.
  rename Hmtypes1 into Hmtypes. rename HLsub1 into HLsub. rename Hmt1 into Hmt.
  rename Hinvarr1 into Hinvarr.
  (* re-open the DLL pures for the new cell list, and re-pin the two cursors
     as opaque locs with their node_loc equations (the pre-normalize shape) *)
  iAssert (⌜cells_repr ts.(ty_arr) ts.(ty_cells) ts.(ty_arr)⌝ ∗
           own_ytype_cells (tv.(yjs.Text.inner')) (DfracOwn 1) ts.(ty_cells) ts.(ty_arr))%I
    with "[Htext]" as "[%Hrepr Htext]".
  { iDestruct "Htext" as (ytx tlx) "(Hp & Hd & %Hl & %Hr & %Hc)".
    iSplitR; first done. iExists ytx, tlx. iFrame "Hp Hd".
    iPureIntro. split_and!; assumption. }
  have [lft Hlftloc] : ∃ l0 : loc, l0 = node_loc ts.(ty_cells) (Z.of_nat p - 1) by eexists.
  iEval (rewrite -Hlftloc) in "left".
  have [rgt Hrgtloc] : ∃ r0 : loc, r0 = node_loc ts.(ty_cells) (Z.of_nat p) by eexists.
  iEval (rewrite -Hrgtloc) in "right".
  wp_auto.
  iDestruct "Htext" as (yt0' tl0') "(Hparent & Hdll & %Hlen0 & %Hrepr0 & %Hcpar0)".
  (* Loop invariant: the cursor [q] walks the (possibly re-split) cell list
     [cells'], tombstoning whole visible runs; a range-end split may grow the
     list. The flattened model [ty_arr] never changes ([cells_repr] threads),
     so the item-set auth / counter / registry facts survive; the per-type
     entry inside the store carries the CURRENT cells', and the item map and
     the pool invariants are maintained at that insert. *)
  iAssert (∃ (q : nat) (rem : w64) (cells' : list item_cell) (yt' : yjs.yType.t) (tl' : loc),
    "Htptr" ∷ t_ptr ↦ t ∗
    "Hsp" ∷ s_ptr ↦ tv.(yjs.Text.store') ∗
    "Hcur" ∷ cur_ptr ↦ node_loc cells' (Z.of_nat q) ∗
    "Hrem" ∷ remaining_ptr ↦ rem ∗
    "Hparent" ∷ tv.(yjs.Text.inner') ↦ yt' ∗
    "Hdll" ∷ own_dll (DfracOwn 1) yt'.(yjs.yType.start') tl' null null cells' ∗
    "Hlk" ∷ own_wlock γs ∗
    "Hclient" ∷ (tv.(yjs.Text.store')).[yjs.store.t, "client"] ↦ client ∗
    "Hclock" ∷ (tv.(yjs.Text.store')).[yjs.store.t, "clock"] ↦ k ∗
    "Hitemsf" ∷ (tv.(yjs.Text.store')).[yjs.store.t, "items"] ↦ items_mref ∗
    "Hitemmap" ∷ own_item_map items_mref (DfracOwn 1) (<[tv.(yjs.Text.inner') := MkTypeState cells' ts.(ty_arr)]> types) ∗
    "Htypesf" ∷ (tv.(yjs.Text.store')).[yjs.store.t, "types"] ↦ types_mref ∗
    "Hdset" ∷ (tv.(yjs.Text.store')).[yjs.store.t, "deletedSet"] ↦ dset ∗
    "Hpendf" ∷ (tv.(yjs.Text.store')).[yjs.store.t, "pending"] ↦ pend_sl ∗
    "Hpend" ∷ own_update_structs pend_sl (DfracOwn 1) pend ∗
    "Hseq" ∷ own γs.(sn_seq) (● ((λ ts0 : type_state, (list_to_set ts0.(ty_arr) : gset (YjsItem A))) <$> types) : authR (gmapUR loc (gsetUR (YjsItem A)))) ∗
    "Hhist" ∷ own_client_history γh (uint.nat client) h ∗
    "HtypesAuth" ∷ ghost_map_auth γs.(sn_types) 1 bind ∗
    "Htypesmap" ∷ own_map types_mref (DfracOwn 1) bind ∗
    "Hrest" ∷ ([∗ map] kk↦y ∈ delete (tv.(yjs.Text.inner')) types,
        own_ytype_cells kk (DfracOwn 1) y.(ty_cells) y.(ty_arr) ∗
        ⌜YjsArrInvariant y.(ty_arr)⌝) ∗
    "%Hqlen" ∷ ⌜(q <= length cells')%nat⌝ ∗
    "%Hytlen" ∷ ⌜yt'.(yjs.yType.len') = W64 (num_visible cells')⌝ ∗
    "%Hrepr'" ∷ ⌜cells_repr ts.(ty_arr) cells' ts.(ty_arr)⌝ ∗
    "%Hcparj" ∷ ⌜∀ c0, c0 ∈ cells' -> ic_parent c0 = tv.(yjs.Text.inner')⌝ ∗
    "%Hcellctrj" ∷ ⌜∀ c0, c0 ∈ all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells' ts.(ty_arr)]> types) → cell_client c0 = client →
        (uint.Z (cell_clock c0) + Z.of_nat (length (ic_run c0)) <= uint.Z k)%Z⌝ ∗
    "%Hlocdupj" ∷ ⌜NoDup (ic_loc <$> all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells' ts.(ty_arr)]> types))⌝ ∗
    "%Hrangedisjj" ∷ ⌜cells_range_disjoint (all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells' ts.(ty_arr)]> types))⌝ ∗
    "%Hrunfitsj" ∷ ⌜∀ c0, c0 ∈ all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells' ts.(ty_arr)]> types) → cell_fits c0⌝ ∗
    "%Horiginclkj" ∷ ⌜∀ c0, c0 ∈ all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells' ts.(ty_arr)]> types) → cell_origin_clk c0⌝)%I
    with "[t s cur remaining Hparent Hdll Hlk Hclient Hclock Hitemsf Hitemmap Htypesf Htypesmap Hdset Hpendf Hpend Hseq Hhist HtypesAuth Hrest]" as "IH".
  { iExists p, len, ts.(ty_cells), yt0', tl0'.
    have Hts_eta : MkTypeState ts.(ty_cells) ts.(ty_arr) = ts by (destruct ts; reflexivity).
    rewrite Hts_eta (insert_id types (tv.(yjs.Text.inner')) ts Htsp).
    iFrame "t s Hparent Hdll remaining Hlk Hclient Hclock Hitemsf Hitemmap Htypesf Htypesmap Hdset Hpendf Hpend Hseq Hhist HtypesAuth Hrest".
    iEval (rewrite Hrgtloc) in "cur". iFrame "cur".
    iPureIntro. split_and!;
      [exact Hpbound | exact Hlen0 | exact Hrepr0 | exact Hcpar0
      | exact Hcellctr | exact Hlocdup | exact Hrangedisj | exact Hrunfits | exact Horiginclk]. }
  wp_for "IH".
  case_bool_decide as Hrem.
  2:{ (* budget exhausted: rebuild store_inv (same ty_arr), Unlock, return. *)
      wp_auto. rewrite decide_False; [|done]. rewrite decide_True; [|done]. wp_auto.
      iAssert ([∗ map] kk↦y ∈ <[tv.(yjs.Text.inner') := MkTypeState cells' ts.(ty_arr)]> types,
          own_ytype_cells kk (DfracOwn 1) (ty_cells y) (ty_arr y) ∗
          ⌜YjsArrInvariant (ty_arr y)⌝)%I with "[Hparent Hdll Hrest]" as "Htypes".
      { rewrite -insert_delete_eq.
        rewrite big_sepM_insert; last apply lookup_delete_eq.
        iFrame "Hrest". iSplitL.
        - iExists yt', tl'. iFrame "Hparent Hdll". iPureIntro.
          split_and!; [exact Hytlen | exact Hrepr' | exact Hcparj].
        - iPureIntro. exact Hinvarr. }
      have Hmk : ((λ ts0 : type_state, (list_to_set (ty_arr ts0) : gset (YjsItem A))) <$> types) !! (tv.(yjs.Text.inner')) = Some (list_to_set ts.(ty_arr)).
      { rewrite lookup_fmap Htsp //. }
      wp_apply (wp_Store__wunlock with "[$His_store $Hlk Hclient Hclock Hitemsf Hitemmap Htypesf Htypesmap Hdset Hpendf Hpend Hseq HtypesAuth Htypes Hhist]").
      { iNext. iExists client, k, items_mref, types_mref, dset,
          pend_sl,
          (<[tv.(yjs.Text.inner') := MkTypeState cells' ts.(ty_arr)]> types), bind, h, m, pend.
        iSplitR "Hseq Htypes"; last first.
        { rewrite /store_inv_ro fmap_insert /=.
          rewrite (insert_id _ (tv.(yjs.Text.inner')) (list_to_set ts.(ty_arr)) Hmk).
          iFrame "Hseq Htypes". }
        iFrame "Hclient Hclock Hitemsf Hitemmap Htypesf Htypesmap Hdset Hpendf Hpend Hhist HtypesAuth Hbinds".
        iFrame "Hpendcert Hpendroot".
        iPureIntro. split_and!.
        - exact Hpendbnd.
        - intros parent' ts' x Hlook Hxin Hxc.
          destruct (decide (parent' = tv.(yjs.Text.inner'))) as [-> | Hne].
          + rewrite lookup_insert in Hlook. rewrite decide_True in Hlook; [| reflexivity]. injection Hlook as <-. simpl in Hxin. exact (Hctr (tv.(yjs.Text.inner')) ts x Htsp Hxin Hxc).
          + rewrite lookup_insert_ne in Hlook; last (intros HH; apply Hne; symmetry; exact HH).
            exact (Hctr parent' ts' x Hlook Hxin Hxc).
        - exact Hcellctrj.
        - exact Hlocdupj.
        - exact Hrangedisjj.
        - exact Hrunfitsj.
        - exact Horiginclkj.
        - move=> name' p' Hb'. destruct (Hbindtypes name' p' Hb') as [ts' Hts'].
          destruct (decide (p' = tv.(yjs.Text.inner'))) as [-> | Hne];
            [rewrite lookup_insert_eq; by eexists
            | rewrite lookup_insert_ne; [by eexists | congruence]].
        - exact Hbindinj.
        - move=> p' [ts' Hts'].
          destruct (decide (p' = tv.(yjs.Text.inner'))) as [-> | Hne].
          + exact (Htypesbound (tv.(yjs.Text.inner')) (ex_intro _ ts Htsp)).
          + rewrite lookup_insert_ne in Hts'; [| congruence].
            exact (Htypesbound p' (ex_intro _ ts' Hts')).
        - exact Hhcoh.
        - move=> name' p' ts' Hb' Hts'.
          destruct (decide (p' = tv.(yjs.Text.inner'))) as [-> | Hne].
          + have Heqn : name' = name := Hbindinj name' name _ Hb' Hbindlk.
            subst name'. rewrite lookup_insert_eq in Hts'. injection Hts' as <-.
            simpl. exact Hmt.
          + rewrite lookup_insert_ne in Hts'; [| congruence].
            exact (Hmtypes name' p' ts' Hb' Hts').
        - exact Hmdom. }
      iApply "HΦ". iExists tv, tv.(yjs.Text.store'), tv.(yjs.Text.inner').
      iFrame "Ht His_store His_hist Hbind His_lb". iPureIntro. split_and!; [reflexivity | reflexivity | exact Hsorted]. }
  wp_auto.
  destruct (decide (q < length cells')%nat) as [Hqlt | Hqge].
  2:{ (* cursor at end: rebuild store_inv (same ty_arr), Unlock, return. *)
      have Hnull : node_loc cells' (Z.of_nat q) = null.
      { rewrite /node_loc decide_True; [| lia]. rewrite Nat2Z.id lookup_ge_None_2; [done | lia]. }
      rewrite (bool_decide_eq_true_2 (node_loc cells' (Z.of_nat q) = null) Hnull). simpl negb.
      rewrite decide_False; [| done]. rewrite decide_True; [| done]. wp_auto.
      iAssert ([∗ map] kk↦y ∈ <[tv.(yjs.Text.inner') := MkTypeState cells' ts.(ty_arr)]> types,
          own_ytype_cells kk (DfracOwn 1) (ty_cells y) (ty_arr y) ∗
          ⌜YjsArrInvariant (ty_arr y)⌝)%I with "[Hparent Hdll Hrest]" as "Htypes".
      { rewrite -insert_delete_eq.
        rewrite big_sepM_insert; last apply lookup_delete_eq.
        iFrame "Hrest". iSplitL.
        - iExists yt', tl'. iFrame "Hparent Hdll". iPureIntro.
          split_and!; [exact Hytlen | exact Hrepr' | exact Hcparj].
        - iPureIntro. exact Hinvarr. }
      have Hmk : ((λ ts0 : type_state, (list_to_set (ty_arr ts0) : gset (YjsItem A))) <$> types) !! (tv.(yjs.Text.inner')) = Some (list_to_set ts.(ty_arr)).
      { rewrite lookup_fmap Htsp //. }
      wp_apply (wp_Store__wunlock with "[$His_store $Hlk Hclient Hclock Hitemsf Hitemmap Htypesf Htypesmap Hdset Hpendf Hpend Hseq HtypesAuth Htypes Hhist]").
      { iNext. iExists client, k, items_mref, types_mref, dset,
          pend_sl,
          (<[tv.(yjs.Text.inner') := MkTypeState cells' ts.(ty_arr)]> types), bind, h, m, pend.
        iSplitR "Hseq Htypes"; last first.
        { rewrite /store_inv_ro fmap_insert /=.
          rewrite (insert_id _ (tv.(yjs.Text.inner')) (list_to_set ts.(ty_arr)) Hmk).
          iFrame "Hseq Htypes". }
        iFrame "Hclient Hclock Hitemsf Hitemmap Htypesf Htypesmap Hdset Hpendf Hpend Hhist HtypesAuth Hbinds".
        iFrame "Hpendcert Hpendroot".
        iPureIntro. split_and!.
        - exact Hpendbnd.
        - intros parent' ts' x Hlook Hxin Hxc.
          destruct (decide (parent' = tv.(yjs.Text.inner'))) as [-> | Hne].
          + rewrite lookup_insert in Hlook. rewrite decide_True in Hlook; [| reflexivity]. injection Hlook as <-. simpl in Hxin. exact (Hctr (tv.(yjs.Text.inner')) ts x Htsp Hxin Hxc).
          + rewrite lookup_insert_ne in Hlook; last (intros HH; apply Hne; symmetry; exact HH).
            exact (Hctr parent' ts' x Hlook Hxin Hxc).
        - exact Hcellctrj.
        - exact Hlocdupj.
        - exact Hrangedisjj.
        - exact Hrunfitsj.
        - exact Horiginclkj.
        - move=> name' p' Hb'. destruct (Hbindtypes name' p' Hb') as [ts' Hts'].
          destruct (decide (p' = tv.(yjs.Text.inner'))) as [-> | Hne];
            [rewrite lookup_insert_eq; by eexists
            | rewrite lookup_insert_ne; [by eexists | congruence]].
        - exact Hbindinj.
        - move=> p' [ts' Hts'].
          destruct (decide (p' = tv.(yjs.Text.inner'))) as [-> | Hne].
          + exact (Htypesbound (tv.(yjs.Text.inner')) (ex_intro _ ts Htsp)).
          + rewrite lookup_insert_ne in Hts'; [| congruence].
            exact (Htypesbound p' (ex_intro _ ts' Hts')).
        - exact Hhcoh.
        - move=> name' p' ts' Hb' Hts'.
          destruct (decide (p' = tv.(yjs.Text.inner'))) as [-> | Hne].
          + have Heqn : name' = name := Hbindinj name' name _ Hb' Hbindlk.
            subst name'. rewrite lookup_insert_eq in Hts'. injection Hts' as <-.
            simpl. exact Hmt.
          + rewrite lookup_insert_ne in Hts'; [| congruence].
            exact (Hmtypes name' p' ts' Hb' Hts').
        - exact Hmdom. }
      iApply "HΦ". iExists tv, tv.(yjs.Text.store'), tv.(yjs.Text.inner').
      iFrame "Ht His_store His_hist Hbind His_lb". iPureIntro. split_and!; [reflexivity | reflexivity | exact Hsorted]. }
  (* cursor in range: read node [q] (single borrow exposing [itemVal] + the update
     wand), decide visible/deleted via [Indexable], advance to [q+1]. *)
  iDestruct (node_loc_lt_not_null (DfracOwn 1) cells' yt'.(yjs.yType.start') tl' q Hqlt with "Hdll") as "[%Hnn Hdll]".
  rewrite (bool_decide_eq_false_2 (node_loc cells' (Z.of_nat q) = null) Hnn). simpl negb.
  rewrite decide_True; [| done].
  destruct (cells' !! q) as [cq|] eqn:Hcq; [| apply lookup_ge_None in Hcq; lia].
  iDestruct (own_dll_update_gen cells' yt'.(yjs.yType.start') tl' q cq Hcq with "Hdll")
    as (itemVal) "(%Hcloc & %Hcr & %Hflags & %Hrunwf & %Hcontq & Hcval & Hback)".
  have Hcountq : is_countable_flag itemVal = true := flags_if_countable itemVal (ic_deleted cq) Hflags.
  have Hdelq : is_deleted_flag itemVal = ic_deleted cq := flags_if_deleted itemVal (ic_deleted cq) Hflags.
  iEval (rewrite -Hcloc) in "Hcur".
  wp_auto.
  wp_apply (wp_item__Indexable cq.(ic_loc) (DfracOwn 1) itemVal Hcountq with "[$Hcval]"). iIntros "Hcval".
  rewrite Hdelq.
  destruct (ic_deleted cq) eqn:Hdq.
  - (* already a tombstone: [Indexable] is false, walk past it unchanged *)
    simpl negb. wp_auto.
    iDestruct ("Hback" $! itemVal true eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl Hflags with "Hcval") as "Hdll".
    have Hins0 : <[q := MkItemCell cq.(ic_loc) cq.(ic_run) true cq.(ic_parent)]> cells' = cells'.
    { rewrite -Hdq.
      have -> : MkItemCell cq.(ic_loc) cq.(ic_run) cq.(ic_deleted) cq.(ic_parent) = cq by destruct cq.
      apply list_insert_id; exact Hcq. }
    rewrite Hins0.
    wp_for_post.
    iFrame "Ht His_lb HΦ". iExists (S q), rem, cells', yt', tl'.
    iFrame "Htptr Hsp Hparent Hdll Hrem Hlk Hclient Hclock Hitemsf Hitemmap Htypesf Htypesmap Hdset Hpendf Hpend Hseq Hhist HtypesAuth Hrest".
    rewrite Hcr. replace (Z.of_nat (S q)) with (Z.of_nat q + 1)%Z by lia. iFrame "Hcur".
    iPureIntro. split_and!;
      [lia | exact Hytlen | exact Hrepr' | exact Hcparj
      | exact Hcellctrj | exact Hlocdupj | exact Hrangedisjj | exact Hrunfitsj | exact Horiginclkj].
  - (* visible node: spend the whole run, or split at the range end first *)
    simpl negb. wp_auto.
    have Hlenq : length (itemVal.(yjs.item.content').(yjs.content.content')) = length (ic_run cq).
    { have Hleq := f_equal length Hcontq.
      rewrite length_fmap explode_length /toContent in Hleq. lia. }
    wp_apply (wp_item__Len cq.(ic_loc) (DfracOwn 1) itemVal with "[$Hcval]"). iIntros "Hcval".
    rewrite Hlenq.
    wp_auto.
    have Hcqmem : cq ∈ all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells' ts.(ty_arr)]> types).
    { apply all_cells_elem_of.
      exists (tv.(yjs.Text.inner')), (MkTypeState cells' ts.(ty_arr)).
      split; [apply lookup_insert_eq | exact (list_elem_of_lookup_2 _ _ _ Hcq)]. }
    have Hfitscq : (uint.Z (cell_clock cq) + Z.of_nat (length (ic_run cq)) < 2^64)%Z
      := Hrunfitsj cq Hcqmem.
    wp_if_destruct.
    + (* remaining < Len: split the run at the budget, tombstone the truncated
         left half; both Len() reads below then return the truncated length,
         so the budget hits zero and the loop exits on its next test *)
      (* return the borrow unchanged, re-pack the store big-sep *)
      iDestruct ("Hback" $! itemVal false eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl Hflags with "Hcval") as "Hdll".
      have Hins0 : <[q := MkItemCell cq.(ic_loc) cq.(ic_run) false cq.(ic_parent)]> cells' = cells'.
      { rewrite -Hdq.
        have -> : MkItemCell cq.(ic_loc) cq.(ic_run) cq.(ic_deleted) cq.(ic_parent) = cq by destruct cq.
        apply list_insert_id; exact Hcq. }
      rewrite Hins0.
      iAssert ([∗ map] kk↦y ∈ <[tv.(yjs.Text.inner') := MkTypeState cells' ts.(ty_arr)]> types,
          own_ytype_cells kk (DfracOwn 1) (ty_cells y) (ty_arr y) ∗
          ⌜YjsArrInvariant (ty_arr y)⌝)%I with "[Hparent Hdll Hrest]" as "Htypes".
      { rewrite -insert_delete_eq.
        rewrite big_sepM_insert; last apply lookup_delete_eq.
        iFrame "Hrest". iSplitL.
        - iExists yt', tl'. iFrame "Hparent Hdll". iPureIntro.
          split_and!; [exact Hytlen | exact Hrepr' | exact Hcparj].
        - iPureIntro. exact Hinvarr. }
      iDestruct (types_cells_id_bounds2 with "Htypes") as %Hbnds.
      have Hckbnd : (Z.of_nat (clock (item_id (run_head cq))) < 2^64)%Z := proj2 (Hbnds cq Hcqmem).
      have Htspj : (<[tv.(yjs.Text.inner') := MkTypeState cells' ts.(ty_arr)]> types) !! tv.(yjs.Text.inner')
                 = Some (MkTypeState cells' ts.(ty_arr)) by apply lookup_insert_eq.
      have Hdiffb : (0 < uint.nat rem < length (ic_run cq))%nat by word.
      have Hfits64j : ∀ c0, c0 ∈ all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells' ts.(ty_arr)]> types) →
          (uint.Z (cell_clock c0) + Z.of_nat (length (ic_run c0)) < 2^64)%Z.
      { move=> c0 Hc0. exact (Hrunfitsj c0 Hc0). }
      have Hdisjcq : ∀ c0, c0 ∈ all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells' ts.(ty_arr)]> types) →
          cell_client c0 = cell_client cq → ic_loc c0 ≠ ic_loc cq →
         (uint.Z (cell_clock c0) + Z.of_nat (length (ic_run c0)) <= uint.Z (cell_clock cq))%Z ∨
         (uint.Z (cell_clock cq) + Z.of_nat (length (ic_run cq)) <= uint.Z (cell_clock c0))%Z.
      { move=> c0 Hc0 Hcc Hne. exact (Hrangedisjj c0 cq Hc0 Hcqmem Hcc Hne). }
      wp_apply (wp_store__splitNode (tv.(yjs.Text.store')) items_mref
                  (<[tv.(yjs.Text.inner') := MkTypeState cells' ts.(ty_arr)]> types)
                  (tv.(yjs.Text.inner')) cells' ts.(ty_arr) q cq rem
                  Htspj Hcq Hdiffb Hfits64j Hlocdupj Hdisjcq
                  with "[$Hitemsf $Hitemmap $Htypes]").
      iIntros (rloc) "(%Hrlocnn & %Hrlocfresh & Hitemsf & Hitemmap & Htypes)".
      wp_auto.
      set (cells2 := split_cells cells' q (uint.nat rem) rloc).
      have Hii : <[tv.(yjs.Text.inner') := MkTypeState cells2 ts.(ty_arr)]>
                   (<[tv.(yjs.Text.inner') := MkTypeState cells' ts.(ty_arr)]> types)
               = <[tv.(yjs.Text.inner') := MkTypeState cells2 ts.(ty_arr)]> types.
      { rewrite insert_insert. case_decide as Hd; [reflexivity | congruence]. }
      iEval (rewrite Hii) in "Hitemmap".
      iEval (rewrite Hii) in "Htypes".
      (* pool transports across the split, then collapse the double insert *)
      have Hrunwfcq : run_wf (ic_run cq) := Hrunwf.
      have Hsub2 := split_pool_subrange _ (tv.(yjs.Text.inner')) cells' ts.(ty_arr)
                      q cq (uint.nat rem) rloc Htspj Hcq Hrunwfcq Hdiffb Hckbnd Hfitscq.
      have Hcellctr2 : ∀ c0, c0 ∈ all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells2 ts.(ty_arr)]> types) →
          cell_client c0 = client →
          (uint.Z (cell_clock c0) + Z.of_nat (length (ic_run c0)) <= uint.Z k)%Z.
      { move=> c0 Hc0 Hcc. rewrite -Hii in Hc0.
        destruct (Hsub2 c0 Hc0) as (cold & Hcold & Hccold & Hlo & Hhi).
        have := Hcellctrj cold Hcold ltac:(congruence). lia. }
      have Hlocdup2 : NoDup (ic_loc <$> all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells2 ts.(ty_arr)]> types)).
      { rewrite -Hii.
        exact (split_pool_locdup _ (tv.(yjs.Text.inner')) cells' ts.(ty_arr)
                 q cq (uint.nat rem) rloc Htspj Hcq Hrlocfresh Hlocdupj). }
      have Hrangedisj2 : cells_range_disjoint (all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells2 ts.(ty_arr)]> types)).
      { rewrite -Hii.
        exact (split_pool_rangedisj _ (tv.(yjs.Text.inner')) cells' ts.(ty_arr)
                 q cq (uint.nat rem) rloc Htspj Hcq Hrunwfcq Hdiffb Hckbnd Hfitscq
                 Hlocdupj Hrangedisjj). }
      have Hrunfits2 : ∀ c0, c0 ∈ all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells2 ts.(ty_arr)]> types) → cell_fits c0.
      { move=> c0 Hc0. rewrite -Hii in Hc0. rewrite /cell_fits.
        exact (split_pool_fits _ (tv.(yjs.Text.inner')) cells' ts.(ty_arr)
                 q cq (uint.nat rem) rloc Htspj Hcq Hrunwfcq Hdiffb Hckbnd Hfits64j c0 Hc0). }
      have Horiginclk2 : ∀ c0, c0 ∈ all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells2 ts.(ty_arr)]> types) → cell_origin_clk c0.
      { move=> c0 Hc0. rewrite -Hii in Hc0.
        exact (split_pool_originclk _ (tv.(yjs.Text.inner')) cells' ts.(ty_arr)
                 q cq (uint.nat rem) rloc Htspj Hcq Hrunwfcq Hdiffb Horiginclkj c0 Hc0). }
      (* re-carve THIS text, re-borrow the truncated left half at [q] *)
      iDestruct (big_sepM_delete _ _ (tv.(yjs.Text.inner')) (MkTypeState cells2 ts.(ty_arr)) with "Htypes") as "[[Htext %Hinvarr2] Hrest]";
        first apply lookup_insert_eq.
      rewrite delete_insert_eq.
      iDestruct "Htext" as (yt2 tl2) "(Hparent & Hdll & %Hlen2 & %Hrepr2 & %Hcpar2)".
      set (cl := split_cell_left cq (uint.nat rem)).
      have Hcl2 : cells2 !! q = Some cl
        := split_cells_lookup_left cells' q (uint.nat rem) rloc cq Hcq.
      iDestruct (own_dll_update_gen cells2 yt2.(yjs.yType.start') tl2 q cl Hcl2 with "Hdll")
        as (iv2) "(%Hcloc2 & %Hcr2 & %Hflags2 & %Hrunwf2 & %Hcontq2 & Hcval & Hback)".
      have Hcllocq : ic_loc cl = ic_loc cq by rewrite /cl //.
      have Hcldel : ic_deleted cl = false by rewrite /cl /= Hdq //.
      have Hlenl : length (ic_run cl) = uint.nat rem.
      { rewrite /cl /= length_take. lia. }
      have Hlenl2 : length (iv2.(yjs.item.content').(yjs.content.content')) = uint.nat rem.
      { have Hleq := f_equal length Hcontq2.
        rewrite length_fmap explode_length /toContent in Hleq. rewrite -Hlenl. lia. }
      iEval (rewrite Hcllocq) in "Hcval".
      wp_auto.
      (* both Len() reads below return the TRUNCATED length [rem] *)
      wp_apply (wp_item__Len cq.(ic_loc) (DfracOwn 1) (set_deleted iv2) with "[$Hcval]"). iIntros "Hcval".
      rewrite Hlenl2. wp_auto.
      wp_apply (wp_item__Len cq.(ic_loc) (DfracOwn 1) (set_deleted iv2) with "[$Hcval]"). iIntros "Hcval".
      rewrite Hlenl2. wp_auto.
      iEval (rewrite -Hcllocq) in "Hcval".
      have Hflagspin2 : iv2.(yjs.item.flags') = (if false then W8 6 else W8 2)
        by rewrite Hflags2 Hcldel //.
      iDestruct ("Hback" $! (set_deleted iv2) true eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                   eq_refl (set_deleted_flags iv2 false Hflagspin2) with "Hcval") as "Hdll".
      have Hflip2 : MkItemCell cl.(ic_loc) cl.(ic_run) true cl.(ic_parent) = flip_cell cl by reflexivity.
      rewrite Hflip2.
      wp_for_post.
      (* invariant at S q over the flipped split list *)
      set (cells3 := <[q := flip_cell cl]> cells2).
      have Hnv2 : num_visible cells2 = num_visible cells'
        := split_cells_num_visible cells' q (uint.nat rem) rloc cq Hcq.
      have Hnvge : (uint.nat rem <= num_visible cells2)%nat.
      { rewrite /num_visible -(take_drop_middle cells2 q cl Hcl2) fmap_app list_sum_app fmap_cons /=.
        rewrite Hcldel Hlenl. lia. }
      have Hnv3 : num_visible cells3 = (num_visible cells2 - uint.nat rem)%nat.
      { rewrite /cells3 (num_visible_flip_run cells2 q cl Hcl2 Hcldel) Hlenl //. }
      (* the flip is (loc, run)-invisible: transport the pool facts *)
      have Hlreq3 : (λ c0, (ic_loc c0, ic_run c0)) <$> cells3 = (λ c0, (ic_loc c0, ic_run c0)) <$> cells2.
      { rewrite /cells3 list_fmap_insert /flip_cell /=.
        apply list_insert_id. rewrite list_lookup_fmap Hcl2 //. }
      have Hkpeq3 : cell_kp <$> cells3 = cell_kp <$> cells2.
      { rewrite /cells3 list_fmap_insert cell_kp_flip.
        apply list_insert_id. rewrite list_lookup_fmap Hcl2 //. }
      have Hlrperm3 : (λ c0, (ic_loc c0, ic_run c0)) <$> all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells3 ts.(ty_arr)]> types)
                    ≡ₚ (λ c0, (ic_loc c0, ic_run c0)) <$> all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells2 ts.(ty_arr)]> types).
      { rewrite (all_cells_insert types _ ts _ Htsp) (all_cells_insert types _ ts _ Htsp) /=.
        rewrite !fmap_app Hlreq3 //. }
      have Hkpperm3 : cell_kp <$> all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells3 ts.(ty_arr)]> types)
                    ≡ₚ cell_kp <$> all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells2 ts.(ty_arr)]> types).
      { rewrite (all_cells_insert types _ ts _ Htsp) (all_cells_insert types _ ts _ Htsp) /=.
        rewrite !fmap_app Hkpeq3 //. }
      iDestruct (own_item_map_kp_perm items_mref (DfracOwn 1) _ _ Hkpperm3 with "Hitemmap") as "Hitemmap".
      iFrame "Ht His_lb HΦ".
      iExists (S q), (w64_word_instance.(word.sub) rem (W64 (uint.nat rem))), cells3,
        (yt2 <| yjs.yType.len' := w64_word_instance.(word.sub) yt2.(yjs.yType.len') (W64 (uint.nat rem)) |>), tl2.
      iFrame "Htptr Hsp Hparent Hdll Hrem Hlk Hclient Hclock Hitemsf Hitemmap Htypesf Htypesmap Hdset Hpendf Hpend Hseq Hhist HtypesAuth Hrest".
      have Hcurloc3 : node_loc cells3 (Z.of_nat (S q)) = iv2.(yjs.item.right').
      { rewrite Hcr2 /cells3 /node_loc.
        replace (Z.of_nat (S q)) with (Z.of_nat q + 1)%Z by lia.
        have Hq1lt : (q < length cells2)%nat by (apply lookup_lt_Some in Hcl2; exact Hcl2).
        rewrite !decide_True; [| lia | lia]. f_equal. f_equal.
        rewrite list_lookup_insert_ne; [reflexivity | lia]. }
      rewrite Hcurloc3. iFrame "Hcur".
      iPureIntro. split_and!.
      * rewrite /cells3 length_insert.
        have := lookup_lt_Some _ _ _ Hcl2. lia.
      * simpl. rewrite Hlen2 Hnv3.
        have Hnvle := Hnvge.
        simpl. word.
      * rewrite /cells3.
        apply (cells_repr_update_run ts.(ty_arr) cells2 ts.(ty_arr) q cl (flip_cell cl) Hcl2 eq_refl).
        rewrite /cells2 /cells_repr (split_cells_flatten cells' q (uint.nat rem) rloc cq Hcq).
        exact Hrepr'.
      * move=> c0 Hc0.
        apply list_elem_of_lookup_1 in Hc0 as [i0 Hi0].
        rewrite /cells3 in Hi0.
        destruct (decide (i0 = q)) as [-> | Hne0].
        { rewrite list_lookup_insert_eq in Hi0; last (apply lookup_lt_Some in Hcl2; exact Hcl2).
          injection Hi0 as <-. rewrite /flip_cell /cl /= //.
          exact (Hcparj cq (list_elem_of_lookup_2 _ _ _ Hcq)). }
        { rewrite list_lookup_insert_ne in Hi0; last congruence.
          have Hc0mem : c0 ∈ all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells2 ts.(ty_arr)]> types).
          { apply all_cells_elem_of.
            exists (tv.(yjs.Text.inner')), (MkTypeState cells2 ts.(ty_arr)).
            split; [apply lookup_insert_eq | exact (list_elem_of_lookup_2 _ _ _ Hi0)]. }
          destruct (Hsub2 c0 ltac:(rewrite -Hii in Hc0mem; exact Hc0mem)) as (cold & Hcold & _).
          (* parent of every cells2 cell is inner: from split parents *)
          apply list_elem_of_lookup_2 in Hi0.
          rewrite /cells2 /split_cells Hcq in Hi0.
          move: Hi0 => /elem_of_app [Hi0 | /elem_of_app [Hi0 | Hi0]].
          - exact (Hcparj c0 (subseteq_take _ _ _ Hi0)).
          - move: Hi0 => /elem_of_cons [-> | /elem_of_cons [-> | Hf]].
            + rewrite /split_cell_left /=. exact (Hcparj cq (list_elem_of_lookup_2 _ _ _ Hcq)).
            + rewrite /split_cell_right /=. exact (Hcparj cq (list_elem_of_lookup_2 _ _ _ Hcq)).
            + by apply elem_of_nil in Hf.
          - exact (Hcparj c0 (subseteq_drop _ _ _ Hi0)). }
      * exact (cellctr_locs_run_perm _ _ client k Hlrperm3 Hcellctr2).
      * exact (locs_run_perm_nodup _ _ Hlrperm3 Hlocdup2).
      * exact (locs_run_perm_rangedisj _ _ Hlrperm3 Hrangedisj2).
      * exact (locs_run_perm_fits _ _ Hlrperm3 Hrunfits2).
      * exact (locs_run_perm_originclk _ _ Hlrperm3 Horiginclk2).
    + (* Len <= remaining: tombstone the WHOLE run and spend its length *)
      wp_apply (wp_item__Len cq.(ic_loc) (DfracOwn 1) (set_deleted itemVal) with "[$Hcval]"). iIntros "Hcval".
      rewrite Hlenq. wp_auto.
      wp_apply (wp_item__Len cq.(ic_loc) (DfracOwn 1) (set_deleted itemVal) with "[$Hcval]"). iIntros "Hcval".
      rewrite Hlenq. wp_auto.
      iDestruct ("Hback" $! (set_deleted itemVal) true eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                   eq_refl (set_deleted_flags itemVal false Hflags) with "Hcval") as "Hdll".
      have Hflip : MkItemCell cq.(ic_loc) cq.(ic_run) true cq.(ic_parent) = flip_cell cq by reflexivity.
      rewrite Hflip.
      wp_for_post.
      set (cells3 := <[q := flip_cell cq]> cells').
      have Hnvge : (length (ic_run cq) <= num_visible cells')%nat.
      { rewrite /num_visible -(take_drop_middle cells' q cq Hcq) fmap_app list_sum_app fmap_cons /=.
        rewrite Hdq. lia. }
      have Hnv3 : num_visible cells3 = (num_visible cells' - length (ic_run cq))%nat
        := num_visible_flip_run cells' q cq Hcq Hdq.
      have Hlreq3 : (λ c0, (ic_loc c0, ic_run c0)) <$> cells3 = (λ c0, (ic_loc c0, ic_run c0)) <$> cells'.
      { rewrite /cells3 list_fmap_insert /flip_cell /=.
        apply list_insert_id. rewrite list_lookup_fmap Hcq //. }
      have Hkpeq3 : cell_kp <$> cells3 = cell_kp <$> cells'.
      { rewrite /cells3 list_fmap_insert cell_kp_flip.
        apply list_insert_id. rewrite list_lookup_fmap Hcq //. }
      have Hlrperm3 : (λ c0, (ic_loc c0, ic_run c0)) <$> all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells3 ts.(ty_arr)]> types)
                    ≡ₚ (λ c0, (ic_loc c0, ic_run c0)) <$> all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells' ts.(ty_arr)]> types).
      { rewrite (all_cells_insert types _ ts _ Htsp) (all_cells_insert types _ ts _ Htsp) /=.
        rewrite !fmap_app Hlreq3 //. }
      have Hkpperm3 : cell_kp <$> all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells3 ts.(ty_arr)]> types)
                    ≡ₚ cell_kp <$> all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells' ts.(ty_arr)]> types).
      { rewrite (all_cells_insert types _ ts _ Htsp) (all_cells_insert types _ ts _ Htsp) /=.
        rewrite !fmap_app Hkpeq3 //. }
      iDestruct (own_item_map_kp_perm items_mref (DfracOwn 1) _ _ Hkpperm3 with "Hitemmap") as "Hitemmap".
      iFrame "Ht His_lb HΦ".
      iExists (S q), (w64_word_instance.(word.sub) rem (W64 (length (ic_run cq)))), cells3,
        (yt' <| yjs.yType.len' := w64_word_instance.(word.sub) yt'.(yjs.yType.len') (W64 (length (ic_run cq))) |>), tl'.
      iFrame "Htptr Hsp Hparent Hdll Hrem Hlk Hclient Hclock Hitemsf Hitemmap Htypesf Htypesmap Hdset Hpendf Hpend Hseq Hhist HtypesAuth Hrest".
      have Hcurloc : node_loc cells3 (Z.of_nat (S q)) = itemVal.(yjs.item.right').
      { rewrite Hcr /cells3 /node_loc.
        replace (Z.of_nat (S q)) with (Z.of_nat q + 1)%Z by lia.
        rewrite !decide_True; [| lia | lia]. f_equal. f_equal.
        rewrite list_lookup_insert_ne; [reflexivity | lia]. }
      rewrite Hcurloc. iFrame "Hcur".
      iPureIntro. split_and!.
      * rewrite /cells3 length_insert. lia.
      * simpl. rewrite Hnv3 Hytlen. word.
      * rewrite /cells3.
        exact (cells_repr_update_run ts.(ty_arr) cells' ts.(ty_arr) q cq (flip_cell cq) Hcq eq_refl Hrepr').
      * move=> c0 Hc0.
        apply list_elem_of_lookup_1 in Hc0 as [i0 Hi0].
        rewrite /cells3 in Hi0.
        destruct (decide (i0 = q)) as [-> | Hne0].
        { rewrite list_lookup_insert_eq in Hi0; last (apply lookup_lt_Some in Hcq; lia).
          injection Hi0 as <-. rewrite /flip_cell /=.
          exact (Hcparj cq (list_elem_of_lookup_2 _ _ _ Hcq)). }
        { rewrite list_lookup_insert_ne in Hi0; last congruence.
          exact (Hcparj c0 (list_elem_of_lookup_2 _ _ _ Hi0)). }
      * exact (cellctr_locs_run_perm _ _ client k Hlrperm3 Hcellctrj).
      * exact (locs_run_perm_nodup _ _ Hlrperm3 Hlocdupj).
      * exact (locs_run_perm_rangedisj _ _ Hlrperm3 Hrangedisjj).
      * exact (locs_run_perm_fits _ _ Hlrperm3 Hrunfitsj).
      * exact (locs_run_perm_originclk _ _ Hlrperm3 Horiginclkj).
Qed.

(** [Text.Len]: a CONCURRENT read (issue #22). Takes the RWMutex read lock, reads
    the type's visible length off its DLL through a fractional [store_inv_ro]
    share (so it runs alongside other readers), then releases. The read
    capability [own_read_cap] (one reader slot) is threaded and returned;
    [is_Text] is preserved. This exercises the verified RLock read path. *)
Lemma wp_Text__Len (t : loc) (γs : store_names) (γh : history_names) (name : P) (L : list (YjsItem A)) :
  {{{ is_pkg_init yjs ∗ is_Text t γs γh name L ∗ own_read_cap γs }}}
    t @! (go.PointerType yjs.Text) @! "Len" #()
  {{{ (n : w64), RET #n; is_Text t γs γh name L ∗ own_read_cap γs }}}.
Proof.
  wp_start as "[Hpre Hcap]". iNamed "Hpre".
  iDestruct "His_store" as "#His_store".
  wp_auto. subst s_loc.
  wp_apply (wp_Store__rlock with "[$His_store $Hcap]"). iIntros (types) "[Hrlo Hro]".
  iNamed "Hro".
  iDestruct (auth_gmap_gset_lookup_dq with "Hseq His_lb") as %(S' & HmS & HLsub).
  rewrite lookup_fmap in HmS. apply fmap_Some in HmS as (ts & Htsp & ->).
  iDestruct (big_sepM_lookup_acc _ _ _ _ Htsp with "Htypes") as "[Hbody Hclose]".
  iDestruct "Hbody" as "(Htext & %Hinvarr)".
  iDestruct "Htext" as (yt0 tl0) "(Hparent & Hdll & %Hlen & %Hrepr & %Hcpar)".
  subst parent.
  wp_auto.
  iDestruct ("Hclose" with "[Hparent Hdll]") as "Htypes".
  { iSplitL "Hparent Hdll"; [ iExists yt0, tl0; iFrame "Hparent Hdll"; iPureIntro; done | iPureIntro; exact Hinvarr ]. }
  wp_apply (wp_Store__runlock with "[$His_store $Hrlo Hseq Htypes]").
  { iFrame "Hseq Htypes". }
  iIntros "Hcap".
  wp_auto.
  iApply "HΦ". iFrame "Hcap".
  iExists tv, tv.(yjs.Text.store'), tv.(yjs.Text.inner'). iFrame "Ht His_store His_hist Hbind His_lb".
  iPureIntro. split_and!; [reflexivity | reflexivity | exact Hsorted].
Qed.

End text.
