(** The [item] type: its per-method WP specs and the heap representation of an
    item sequence with its model correspondence.

    Bottom to top:
    - per-method WP specs for an individual node: [item.Indexable] / [item.Len] /
      [item.Deleted] and [itemPtrEqual] (pointer identity = model id). All are
      read-only, so they take the struct points-to at a generic [dfrac].
    - [own_dll dq l last prev next cells]: the doubly-linked-list spine of [item]
      nodes (each carrying its [Item] struct and the two origin-id cells), with
      its split / join / accessor / insert lemmas. Adapted from the reference
      sorted-DLL proof (iasakura/perennial-sandbox, dll/list.go, [is_dlist_node]).
      An owning predicate, so [dfrac]-parameterized ([DfracOwn 1] to mutate).
    - [resolve_*] / [cell_repr] / [cells_repr]: the cellwise isomorphism between
      the heap node list and a model [list (YjsItem A)] (origins resolved by id).

    The [yType]-level predicates built on top of this DLL ([own_ytype_cells] /
    [own_ytype], and the deletion layer's [num_visible]) live in [yjs_ytype]; the
    [Store.Integrate] / [Text.Insert] proofs ([yjs_store] / [yjs_text]) are
    stated against them. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import yjs_core.
From New.proof Require Import yjs_common yjs_id.

Section item.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.

(* ===== per-method WP specs for individual items ======================== *)

(* The node / GC / Skip enum is codec-only now (refs.go is //go:build !goose), so
   its projections are no longer part of the verified model. *)

(** [itemPtrEqual] compares two item pointers by identity (= model id, ids being
    unique), with the null cases of y-octo's [Somr] comparison. *)
Lemma wp_itemPtrEqual (pa pb : loc) (ova ovb : option yjs.item.t) (dqa dqb : dfrac) :
  {{{ is_pkg_init yjs ∗ item_or_null pa ova dqa ∗ item_or_null pb ovb dqb }}}
    @! yjs.itemPtrEqual #pa #pb
  {{{ RET #(bool_decide (originId_of ova = originId_of ovb));
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
    have Heq : bool_decide (originId_of (Some va) = originId_of (Some vb))
             = bool_decide (toYjsId va.(yjs.item.id') = toYjsId vb.(yjs.item.id')).
    { apply bool_decide_ext. rewrite /originId_of /=. by split; congruence. }
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

(* ----- per-node accessors read by yType.findPos -------------------------- *)

(** The Deleted bit (y-octo ITEM_DELETED = 0x04) of a heap item's [flags], read
    exactly as [item.Deleted] computes it ([flags & 0x04 ≠ 0]). This boolean is
    the heap source of truth for visibility (a tombstoned node has it set). *)
Definition is_deleted_flag (v : yjs.item.t) : bool :=
  negb (bool_decide (w8_word_instance.(word.and) v.(yjs.item.flags') (W8 4) = W8 0)).

(** The Countable bit (ITEM_COUNTABLE = 0x02), read as [item.Countable] does.
    Every string item NewItem builds is countable, so this is [true] of every
    integrated node; it is what [item.Indexable] gates visibility on. *)
Definition is_countable_flag (v : yjs.item.t) : bool :=
  negb (bool_decide (w8_word_instance.(word.and) v.(yjs.item.flags') (W8 2) = W8 0)).

(** Number of visible (non-deleted) CHARACTERS: the value carried in the heap
    [yType.len] field. Every cell is Countable, so visible ⇔ not Deleted; the
    flag is promoted onto the abstract cell as [ic_deleted], and a visible cell
    contributes its whole run length (issue #28; the Go bumps [parent.len] by
    [item.Len()]). *)
Definition num_visible (cells : list item_cell) : nat :=
  list_sum ((λ c, if ic_deleted c then 0%nat else length (ic_run c)) <$> cells).

(** Read the promoted Deleted / Countable bits back off the [own_dll] flag pin
    ([flags'] = [if d then W8 6 else W8 2]): the struct is always Countable, and
    its Deleted bit is exactly [d]. Used by [findPos] / [Delete] after opening a
    node, to learn its visibility from the cell's [ic_deleted]. *)
Lemma flags_if_deleted (v : yjs.item.t) (d : bool) :
  v.(yjs.item.flags') = (if d then W8 6 else W8 2) -> is_deleted_flag v = d.
Proof. rewrite /is_deleted_flag => ->. by destruct d. Qed.

Lemma flags_if_countable (v : yjs.item.t) (d : bool) :
  v.(yjs.item.flags') = (if d then W8 6 else W8 2) -> is_countable_flag v = true.
Proof. rewrite /is_countable_flag => ->. by destruct d. Qed.

(** Per-node method specs [findPos] reads off each cursor node. Every cell is
    Countable ([is_countable_flag]) with single-byte content, so [Indexable] is
    "not Deleted" and [Len] is the content byte length (1 for our cells). Proving
    these once keeps the [findPos] loop free of nested method-call stepping.
    Read-only, hence stated at a generic [dq]. *)
Lemma wp_item__Indexable (l : loc) (dq : dfrac) (v : yjs.item.t) :
  is_countable_flag v = true ->
  {{{ is_pkg_init yjs ∗ l ↦{dq} v }}}
    l @! (go.PointerType yjs.item) @! "Indexable" #()
  {{{ RET #(negb (is_deleted_flag v)); l ↦{dq} v }}}.
Proof.
  intros Hcount.
  rewrite /is_countable_flag in Hcount. apply negb_true_iff in Hcount.
  wp_start as "Hl".
  wp_auto.
  wp_method_call. wp_call. rewrite /yjs.item__Indexableⁱᵐᵖˡ. wp_auto.
  wp_method_call. wp_call. wp_auto.
  wp_method_call. wp_call. rewrite /yjs.item__Countableⁱᵐᵖˡ. wp_auto.
  wp_alloc i2 as "Hi2". wp_auto.
  rewrite Hcount. simpl negb. wp_auto.
  wp_method_call. wp_call. rewrite /yjs.item__Deletedⁱᵐᵖˡ. wp_auto.
  wp_method_call. wp_call. rewrite /yjs.item__Deletedⁱᵐᵖˡ. wp_auto.
  rewrite -/(is_deleted_flag v). iApply "HΦ". iFrame "Hl".
Qed.

Lemma wp_item__Len (l : loc) (dq : dfrac) (v : yjs.item.t) :
  {{{ is_pkg_init yjs ∗ l ↦{dq} v }}}
    l @! (go.PointerType yjs.item) @! "Len" #()
  {{{ RET #(W64 (length (v.(yjs.item.content').(yjs.content.content')))); l ↦{dq} v }}}.
Proof.
  wp_start as "Hl". wp_auto.
  wp_method_call. wp_call. rewrite /yjs.item__Lenⁱᵐᵖˡ. wp_auto.
  wp_method_call. wp_call. rewrite /yjs.content__Lenⁱᵐᵖˡ. wp_auto.
  wp_method_call. wp_call. rewrite /yjs.content__Lenⁱᵐᵖˡ. wp_auto.
  wp_apply strings.wp_string_len. iIntros "_". wp_auto.
  iApply "HΦ". iFrame "Hl".
Qed.

Lemma wp_item__Deleted (l : loc) (dq : dfrac) (v : yjs.item.t) :
  {{{ is_pkg_init yjs ∗ l ↦{dq} v }}}
    l @! (go.PointerType yjs.item) @! "Deleted" #()
  {{{ RET #(is_deleted_flag v); l ↦{dq} v }}}.
Proof.
  wp_start as "Hl". wp_auto.
  wp_method_call. wp_call. rewrite /yjs.item__Deletedⁱᵐᵖˡ. wp_auto.
  iApply "HΦ". iFrame "Hl".
Qed.
(* ----- the doubly-linked spine (adapted from the reference DLL) ----------- *)

(** [own_dll dq l last prev next cells]: the DLL segment whose head node is [l]
    and whose last node is [last]; [prev] is the [left]-pointer of [l] and [next]
    is the [right]-pointer of [last]. Mirrors the reference [is_dlist_node].
    Owns each node's struct points-to at [dq] ([DfracOwn 1] to relink / flip
    flags; any [dq] to read).

    Each node existentially quantifies its full heap struct [itemVal : yjs.item.t] and
    the two resolved origin ids [olid]/[orid], constrained to *translate* to the
    HEAD of the cell's model run [ic_run c] (issue #28): the heap id
    [toYjsId]-maps to [item_id (run_head c)], the content explodes to the
    per-char contents of the run, and the origin pointers carry ids whose
    [toYjsId] images are the head's origin ids. The non-head run items carry no
    heap data of their own: [run_wf] pins their ids/origins to the head. The
    volatile spine links ([left'] = [prev], [right'] heads the rest) are also
    constraints on [itemVal], NOT data of the cell — so [Store.Integrate]'s neighbour
    relinking changes only [itemVal] and leaves the abstract [cells] (hence
    [run_flatten cells]) unchanged. The flag pin lives here too: the struct is
    Countable and its Deleted bit equals the cell's [ic_deleted] ([flags'] =
    [W8 6] when deleted, [W8 2] when visible). *)
Fixpoint own_dll (dq : dfrac) (l last prev next : loc) (cells : list item_cell) : iProp Σ :=
  match cells with
  | [] => ⌜l = next ∧ last = prev⌝
  | c :: rest =>
      ∃ (itemVal : yjs.item.t) (olid orid : option yjs.id.t),
      "%Hloc" ∷ ⌜l = ic_loc c ∧ l ≠ null⌝ ∗
      "%Hprev" ∷ ⌜itemVal.(yjs.item.left') = prev⌝ ∗
      "%Hpar" ∷ ⌜itemVal.(yjs.item.parent') = ic_parent c⌝ ∗
      "%Hid" ∷ ⌜item_id (run_head c) = toYjsId itemVal.(yjs.item.id')⌝ ∗
      "%Hcontent" ∷ ⌜content <$> ic_run c = explode (toContent itemVal.(yjs.item.content'))⌝ ∗
      "%Holid" ∷ ⌜origin_id (origin (run_head c)) = toYjsId <$> olid⌝ ∗
      "%Horid" ∷ ⌜origin_id (rightOrigin (run_head c)) = toYjsId <$> orid⌝ ∗
      "%Hflags" ∷ ⌜itemVal.(yjs.item.flags') = (if ic_deleted c then W8 6 else W8 2)⌝ ∗
      "%Hrun" ∷ ⌜run_wf (ic_run c)⌝ ∗
      "Hval" ∷ ic_loc c ↦{dq} itemVal ∗
      "Holeft" ∷ is_origin_id itemVal.(yjs.item.originLeftId') olid ∗
      "Horight" ∷ is_origin_id itemVal.(yjs.item.originRightId') orid ∗
      "Hrest" ∷ own_dll dq itemVal.(yjs.item.right') last l next rest
  end.

(* ----- structural lemmas for the DLL spine ------------------------------- *)

(** Split / join a DLL segment at a list append (cf. reference [is_dlist_node_app]). *)
Lemma own_dll_app (dq : dfrac) (cs1 cs2 : list item_cell) (l last prev next : loc) :
  own_dll dq l last prev next (cs1 ++ cs2)
  ⊣⊢ ∃ mid_last mid_fst,
       own_dll dq l mid_last prev mid_fst cs1 ∗ own_dll dq mid_fst last mid_last next cs2.
Proof.
  revert l prev. induction cs1 as [|c cs1 IH] => l prev /=.
  - iSplit.
    + iIntros "H". iExists prev, l. by iFrame.
    + iIntros "(%ml & %mf & [%H1 %H2] & H)". subst. by iFrame.
  - iSplit.
    + iIntros "H". iNamed "H". rewrite IH.
      iDestruct "Hrest" as "(%ml & %mf & H1 & H2)".
      iExists ml, mf. iFrame "H2". iExists itemVal, olid, orid.
      iFrame "Hval Holeft Horight H1". by iPureIntro.
    + iIntros "(%ml & %mf & H1 & H2)". iNamed "H1".
      iExists itemVal, olid, orid. iFrame "Hval Holeft Horight".
      iAssert (own_dll dq itemVal.(yjs.item.right') last l next (cs1 ++ cs2)) with "[Hrest H2]" as "HR".
      { rewrite IH. iExists ml, mf. iFrame "Hrest H2". }
      iFrame "HR". by iPureIntro.
Qed.

(** Splice a fresh node [newc] between two DLL segments whose boundary fields are
    already relinked to it ([cs1]'s last [right'] and [cs2]'s first [left'] point
    at [ic_loc newc], and [newc]'s [left']/[right'] at the two boundaries). Used to
    rejoin the document DLL after [Store.Integrate] inserts an item. *)
Lemma own_dll_insert_middle (dq : dfrac) (cs1 cs2 : list item_cell) (newc : item_cell)
    (itemVal : yjs.item.t) (olid orid : option yjs.id.t) (hd tl ml mr : loc) :
  ic_loc newc ≠ null ->
  itemVal.(yjs.item.left') = ml ->
  itemVal.(yjs.item.right') = mr ->
  itemVal.(yjs.item.parent') = ic_parent newc ->
  item_id (run_head newc) = toYjsId itemVal.(yjs.item.id') ->
  content <$> ic_run newc = explode (toContent itemVal.(yjs.item.content')) ->
  origin_id (origin (run_head newc)) = toYjsId <$> olid ->
  origin_id (rightOrigin (run_head newc)) = toYjsId <$> orid ->
  itemVal.(yjs.item.flags') = (if ic_deleted newc then W8 6 else W8 2) ->
  run_wf (ic_run newc) ->
  own_dll dq hd ml null (ic_loc newc) cs1 ∗
  ic_loc newc ↦{dq} itemVal ∗
  is_origin_id itemVal.(yjs.item.originLeftId') olid ∗
  is_origin_id itemVal.(yjs.item.originRightId') orid ∗
  own_dll dq mr tl (ic_loc newc) null cs2
  ⊢ own_dll dq hd tl null null (cs1 ++ newc :: cs2).
Proof.
  move=> Hnn Hl Hr Hpart Hidt Hcont Holidt Horidt Hflags Hrun.
  iIntros "(Hdll1 & Hnode & Hol & Hor & Hdll2)".
  rewrite own_dll_app. iExists ml, (ic_loc newc). iFrame "Hdll1".
  simpl. iExists itemVal, olid, orid. rewrite Hr. iFrame "Hnode Hol Hor Hdll2".
  iPureIntro; split_and!;
    [reflexivity | exact Hnn | exact Hl | exact Hpart | exact Hidt | exact Hcont
    | exact Holidt | exact Horidt | exact Hflags | exact Hrun].
Qed.

(** Split one run node into two adjacent nodes [cl] (left half, same loc) and
    [cr] (right half, fresh loc) in place: the caller (the [splitNode] WP) has
    already truncated [cl]'s struct, allocated [cr]'s struct, and relinked the
    following segment's head [left'] to [cr]. This is the DLL-spine counterpart
    of the pure [split_cells] surgery; both [cl] and [cr] carry ordinary node
    field conditions, discharged from [run_wf] telescoping at the call site. It
    is [own_dll_insert_middle] applied to [cl], with [cr] pre-consed onto the
    tail. *)
Lemma own_dll_split (dq : dfrac) (cs1 cs2 : list item_cell) (cl cr : item_cell)
    (ivl ivr : yjs.item.t) (olidl oridl olidr oridr : option yjs.id.t)
    (hd tl ml : loc) :
  ic_loc cl ≠ null ->
  ic_loc cr ≠ null ->
  ivl.(yjs.item.left') = ml ->
  ivl.(yjs.item.right') = ic_loc cr ->
  ivl.(yjs.item.parent') = ic_parent cl ->
  item_id (run_head cl) = toYjsId ivl.(yjs.item.id') ->
  content <$> ic_run cl = explode (toContent ivl.(yjs.item.content')) ->
  origin_id (origin (run_head cl)) = toYjsId <$> olidl ->
  origin_id (rightOrigin (run_head cl)) = toYjsId <$> oridl ->
  ivl.(yjs.item.flags') = (if ic_deleted cl then W8 6 else W8 2) ->
  run_wf (ic_run cl) ->
  ivr.(yjs.item.left') = ic_loc cl ->
  ivr.(yjs.item.parent') = ic_parent cr ->
  item_id (run_head cr) = toYjsId ivr.(yjs.item.id') ->
  content <$> ic_run cr = explode (toContent ivr.(yjs.item.content')) ->
  origin_id (origin (run_head cr)) = toYjsId <$> olidr ->
  origin_id (rightOrigin (run_head cr)) = toYjsId <$> oridr ->
  ivr.(yjs.item.flags') = (if ic_deleted cr then W8 6 else W8 2) ->
  run_wf (ic_run cr) ->
  own_dll dq hd ml null (ic_loc cl) cs1 ∗
  ic_loc cl ↦{dq} ivl ∗
  is_origin_id ivl.(yjs.item.originLeftId') olidl ∗
  is_origin_id ivl.(yjs.item.originRightId') oridl ∗
  ic_loc cr ↦{dq} ivr ∗
  is_origin_id ivr.(yjs.item.originLeftId') olidr ∗
  is_origin_id ivr.(yjs.item.originRightId') oridr ∗
  own_dll dq ivr.(yjs.item.right') tl (ic_loc cr) null cs2
  ⊢ own_dll dq hd tl null null (cs1 ++ cl :: cr :: cs2).
Proof.
  move=> Hclnn Hcrnn Hivl_l Hivl_r Hivl_p Hclid Hclcont Holidl Horidl Hclflags Hclrun
         Hivr_l Hivr_p Hcrid Hcrcont Holidr Horidr Hcrflags Hcrrun.
  iIntros "(Hdll1 & Hnodel & Holl & Horl & Hnoder & Holr & Horr & Hdll2)".
  iAssert (own_dll dq (ic_loc cr) tl (ic_loc cl) null (cr :: cs2))
    with "[Hnoder Holr Horr Hdll2]" as "Hdllr".
  { simpl. iExists ivr, olidr, oridr. iFrame "Hnoder Holr Horr Hdll2".
    iPureIntro; split_and!;
      [reflexivity | exact Hcrnn | exact Hivr_l | exact Hivr_p | exact Hcrid | exact Hcrcont
      | exact Holidr | exact Horidr | exact Hcrflags | exact Hcrrun]. }
  iApply (own_dll_insert_middle dq cs1 (cr :: cs2) cl ivl olidl oridl hd tl ml (ic_loc cr)
            Hclnn Hivl_l Hivl_r Hivl_p Hclid Hclcont Holidl Horidl Hclflags Hclrun).
  iFrame "Hdll1 Hnodel Holl Horl Hdllr".
Qed.

(** A DLL headed by [null] is empty. *)
Lemma own_dll_null_nil dq last prev next cells :
  own_dll dq null last prev next cells -∗ ⌜cells = []⌝.
Proof.
  destruct cells as [|c cs]; [by auto|].
  iIntros "H". iNamed "H". iPureIntro. exfalso. by apply (proj2 Hloc).
Qed.

(** The [last] pointer of a DLL segment is the location of its last node (or the
    [prev] sentinel when empty); the resource is returned. Used to read a node's
    [left'] neighbour. *)
Lemma own_dll_lastptr (dq : dfrac) (l lst prev nxt : loc) (cs : list item_cell) :
  own_dll dq l lst prev nxt cs -∗
    ⌜lst = default prev (ic_loc <$> list.last cs)⌝ ∗ own_dll dq l lst prev nxt cs.
Proof.
  iInduction cs as [|c cs IH] forall (l prev).
  - iIntros "H". iDestruct "H" as %[Hl Hlst]. iPureIntro; split; [exact Hlst | split; done].
  - iIntros "H". iNamed "H".
    iDestruct ("IH" with "Hrest") as "[%Hlst Hrest]".
    iSplitR.
    + iPureIntro. rewrite last_cons. destruct (list.last cs) as [y|] eqn:Hl.
      * by rewrite Hlst /=.
      * rewrite /= in Hlst. rewrite Hlst. by destruct Hloc as [-> _].
    + iExists itemVal, olid, orid. iFrame "Hval Holeft Horight Hrest".
      iPureIntro; split_and!;
        [exact (proj1 Hloc) | exact (proj2 Hloc) | exact Hprev | exact Hpar | exact Hid
        | exact Hcontent | exact Holid | exact Horid | exact Hflags | exact Hrun].
Qed.

(** The head pointer of a DLL segment is the location of its first node (or the
    [nxt] sentinel when empty); the resource is returned. The head-side analogue
    of [own_dll_lastptr], used to read a node's [right'] neighbour. *)
Lemma own_dll_headptr (dq : dfrac) (l lst prev nxt : loc) (cs : list item_cell) :
  own_dll dq l lst prev nxt cs -∗
    ⌜l = default nxt (ic_loc <$> head cs)⌝ ∗ own_dll dq l lst prev nxt cs.
Proof.
  destruct cs as [|c cs'].
  - iIntros "H". iDestruct "H" as %[Hl Hlst].
    iSplit; iPureIntro; [rewrite /= Hl // | split; [exact Hl | exact Hlst]].
  - iIntros "H". iNamed "H".
    iSplit.
    + iPureIntro. rewrite /=. exact (proj1 Hloc).
    + iExists itemVal, olid, orid. iFrame "Hval Holeft Horight Hrest".
      iPureIntro; split_and!;
        [exact (proj1 Hloc) | exact (proj2 Hloc) | exact Hprev | exact Hpar | exact Hid
        | exact Hcontent | exact Holid | exact Horid | exact Hflags | exact Hrun].
Qed.

(** The head of a full DLL is [node_loc cells 0] (the first node, or [null] when
    empty) — the head-side analogue of [own_dll_lastptr]. Used to align
    [parent.start] with [node_loc cells 0] for a head insertion. *)
Lemma own_dll_head_node (dq : dfrac) (cells : list item_cell) (hd tl : loc) :
  own_dll dq hd tl null null cells -∗ ⌜hd = node_loc cells 0⌝.
Proof.
  destruct cells as [|c cs].
  - iIntros "H". iDestruct "H" as %[Hl _]. iPureIntro.
    rewrite Hl /node_loc. case_decide; reflexivity.
  - iIntros "H". iNamed "H". iPureIntro.
    rewrite /node_loc. case_decide as Hdec; [| exfalso; lia].
    simpl. exact (proj1 Hloc).
Qed.

(** Index accessor: borrow the node at index [k] out of a full DLL — its struct
    points-to and (persistent) origin cells — together with its location
    [node_loc cells k], its [left']/[right'] neighbours [node_loc cells (k∓1)],
    and a wand to give the node back and restore the DLL. Used to read the cursor
    node in the conflict scan (and the [left]/[right] anchors in the entry test). *)
Lemma own_dll_acc (dq : dfrac) (cells : list item_cell) (hd tl : loc) (k : nat) (c : item_cell) :
  cells !! k = Some c ->
  own_dll dq hd tl null null cells -∗
    ∃ (itemVal : yjs.item.t) (olid orid : option yjs.id.t),
    "%Hcloc" ∷ ⌜ic_loc c = node_loc cells (Z.of_nat k)⌝ ∗
    "%Hcl" ∷ ⌜itemVal.(yjs.item.left') = node_loc cells (Z.of_nat k - 1)⌝ ∗
    "%Hcr" ∷ ⌜itemVal.(yjs.item.right') = node_loc cells (Z.of_nat k + 1)⌝ ∗
    "%Hid" ∷ ⌜item_id (run_head c) = toYjsId itemVal.(yjs.item.id')⌝ ∗
    "%Hcontent" ∷ ⌜content <$> ic_run c = explode (toContent itemVal.(yjs.item.content'))⌝ ∗
    "%Holid" ∷ ⌜origin_id (origin (run_head c)) = toYjsId <$> olid⌝ ∗
    "%Horid" ∷ ⌜origin_id (rightOrigin (run_head c)) = toYjsId <$> orid⌝ ∗
    "%Hflags" ∷ ⌜itemVal.(yjs.item.flags') = (if ic_deleted c then W8 6 else W8 2)⌝ ∗
    "%Hrun" ∷ ⌜run_wf (ic_run c)⌝ ∗
    "%Hpar" ∷ ⌜itemVal.(yjs.item.parent') = ic_parent c⌝ ∗
    "Hcval" ∷ ic_loc c ↦{dq} itemVal ∗
    "Hcol" ∷ is_origin_id itemVal.(yjs.item.originLeftId') olid ∗
    "Hcor" ∷ is_origin_id itemVal.(yjs.item.originRightId') orid ∗
    "Hback" ∷ (ic_loc c ↦{dq} itemVal -∗ own_dll dq hd tl null null cells).
Proof.
  move=> Hk. iIntros "Hdll".
  (* the [left'] neighbour as a pure fact: [last (take k cells) = cells !! (k-1)] *)
  have Hpe : default null (ic_loc <$> list.last (take k cells)) = node_loc cells (Z.of_nat k - 1).
  { destruct k as [|k'].
    - rewrite take_0 /= /node_loc. case_decide as Hdec; [exfalso; lia | done].
    - have Hk' : (k' < length cells)%nat by (apply lookup_lt_Some in Hk; lia).
      destruct (cells !! k') as [c'|] eqn:Hck'; last by (apply lookup_ge_None in Hck'; lia).
      rewrite (take_S_r cells k' c' Hck') last_snoc /= /node_loc decide_True; last lia.
      have -> : Z.to_nat (Z.of_nat (S k') - 1) = k' by lia.
      by rewrite Hck' /=. }
  pose proof (take_drop_middle cells k c Hk) as Hsplit.
  set (pre := take k cells) in Hsplit.
  set (suf := drop (S k) cells) in Hsplit.
  iEval (rewrite -Hsplit) in "Hdll".
  iEval (rewrite own_dll_app) in "Hdll".
  iDestruct "Hdll" as (ml mf) "[Hpre Hrest]".
  iDestruct "Hrest" as (itemVal olid orid)
    "(%Hloc & %Hprev & %Hparc & %Hidc & %Hcontentc & %Holidc & %Horidc & %Hflagsc & %Hrunc & Hval & #Hol & #Hor & Hrest2)".
  iDestruct (own_dll_lastptr with "Hpre") as "[%Hml Hpre]".
  iDestruct (own_dll_headptr with "Hrest2") as "[%Hhd Hrest2]".
  have Hcl : itemVal.(yjs.item.left') = node_loc cells (Z.of_nat k - 1).
  { rewrite Hprev Hml. exact Hpe. }
  have Hcloc : c.(ic_loc) = node_loc cells k by rewrite /node_loc decide_True; [rewrite Nat2Z.id Hk | lia].
  have Hnn : c.(ic_loc) ≠ null by rewrite -(proj1 Hloc); exact (proj2 Hloc).
  have Hcr : itemVal.(yjs.item.right') = node_loc cells (Z.of_nat k + 1).
  { rewrite Hhd /node_loc decide_True; last lia.
    have HZ : Z.to_nat (Z.of_nat k + 1) = S k by lia.
    rewrite HZ. f_equal. f_equal. rewrite /suf head_lookup lookup_drop Nat.add_0_r //. }
  iExists itemVal, olid, orid. iFrame "Hval Hol Hor".
  (* the wand: re-splice [c] between [pre] and [suf] (relinking is invisible to
     the abstract cells, so the same [itemVal] goes back in) *)
  iAssert (ic_loc c ↦{dq} itemVal -∗ own_dll dq hd tl null null cells)%I with "[Hpre Hrest2]" as "Hback".
  { iIntros "Hval2". iEval (rewrite -Hsplit).
    iApply (own_dll_insert_middle dq pre suf c itemVal olid orid hd tl ml itemVal.(yjs.item.right')
              Hnn Hprev eq_refl Hparc Hidc Hcontentc Holidc Horidc Hflagsc Hrunc).
    iFrame "Hval2 Hol Hor". rewrite -(proj1 Hloc). iFrame "Hpre Hrest2". }
  iFrame "Hback". by iPureIntro.
Qed.

(** Every node at an in-bounds index is a non-null location (DLL nodes are
    non-null); the DLL resource is returned. Used to argue [node_loc cells
    (destIdx-1) = null] forces [destIdx = 0] (head insertion). *)
Lemma node_loc_lt_not_null (dq : dfrac) (cells : list item_cell) (hd tl : loc) (k : nat) :
  (k < length cells)%nat ->
  own_dll dq hd tl null null cells -∗ ⌜node_loc cells (Z.of_nat k) ≠ null⌝ ∗ own_dll dq hd tl null null cells.
Proof.
  move=> Hk. iIntros "Hdll".
  destruct (cells !! k) as [c|] eqn:Hc; last by (apply lookup_ge_None in Hc; lia).
  iDestruct (own_dll_acc dq cells hd tl k c Hc with "Hdll") as "H". iNamed "H".
  iDestruct (typed_pointsto_not_null with "Hcval") as %Hnn.
  iSplitR "Hcval Hback".
  - iPureIntro. rewrite -Hcloc. exact Hnn.
  - iApply "Hback". iFrame "Hcval".
Qed.

(** Every cell's HEAD model id round-trips through the heap's [w64] id fields
    ([own_dll] pins [item_id (run_head c) = toYjsId itemVal.(id')]), so both id
    components are bounded by [2^64]. This is what lets W64-level clock
    comparisons ([cell_clock] / [cell_client]) be recovered from nat-level
    model facts (used by the certificate-based [applyUpdate] spec). *)
Lemma own_dll_id_bounds (dq : dfrac) (l last prev next : loc) (cells : list item_cell) :
  own_dll dq l last prev next cells -∗
  ⌜∀ c, c ∈ cells → (Z.of_nat (clientId (item_id (run_head c))) < 2^64)%Z ∧
                    (Z.of_nat (clock (item_id (run_head c))) < 2^64)%Z⌝.
Proof.
  iInduction cells as [|c0 cells] "IH" forall (l prev).
  - iIntros "_". iPureIntro. move=> c Hc. rewrite elem_of_nil in Hc. done.
  - iIntros "H". iNamed "H".
    iDestruct ("IH" with "Hrest") as %Hrest.
    iPureIntro. move=> c Hc.
    apply elem_of_cons in Hc as [-> | Hc]; last exact (Hrest c Hc).
    rewrite Hid /toYjsId /=. split; word.
Qed.

(** A plain value accessor: borrow the node's (existential) heap struct at index
    [k] from *any* DLL segment (arbitrary [prev]/[nxt]), with its local
    translation facts and a wand to restore it. Unlike [own_dll_acc] it carries no
    [node_loc] facts, so it composes on sub-segments (used to read the
    loop-constant [right] node out of the suffix). *)
Lemma own_dll_lookup_acc (dq : dfrac) (l lst prev nxt : loc) (cs : list item_cell) (k : nat) (c : item_cell) :
  cs !! k = Some c ->
  own_dll dq l lst prev nxt cs -∗
    ∃ (itemVal : yjs.item.t) (olid orid : option yjs.id.t),
      "%Hid" ∷ ⌜item_id (run_head c) = toYjsId itemVal.(yjs.item.id')⌝ ∗
      "%Hcontent" ∷ ⌜content <$> ic_run c = explode (toContent itemVal.(yjs.item.content'))⌝ ∗
      "%Holid" ∷ ⌜origin_id (origin (run_head c)) = toYjsId <$> olid⌝ ∗
      "%Horid" ∷ ⌜origin_id (rightOrigin (run_head c)) = toYjsId <$> orid⌝ ∗
      "%Hflags" ∷ ⌜itemVal.(yjs.item.flags') = (if ic_deleted c then W8 6 else W8 2)⌝ ∗
      "%Hrun" ∷ ⌜run_wf (ic_run c)⌝ ∗
      "Hval" ∷ c.(ic_loc) ↦{dq} itemVal ∗
      "Hcol" ∷ is_origin_id itemVal.(yjs.item.originLeftId') olid ∗
      "Hcor" ∷ is_origin_id itemVal.(yjs.item.originRightId') orid ∗
      "Hback" ∷ (c.(ic_loc) ↦{dq} itemVal -∗ own_dll dq l lst prev nxt cs).
Proof.
  move=> Hk. iIntros "Hdll".
  pose proof (take_drop_middle cs k c Hk) as Hsplit.
  set (pre := take k cs) in Hsplit.
  set (suf := drop (S k) cs) in Hsplit.
  iEval (rewrite -Hsplit own_dll_app) in "Hdll".
  iDestruct "Hdll" as (ml mf) "[Hpre Hrest]".
  iDestruct "Hrest" as (itemVal olid orid)
    "(%Hloc & %Hprev & %Hparc & %Hidc & %Hcontentc & %Holidc & %Horidc & %Hflagsc & %Hrunc & Hval & #Hol & #Hor & Hrest)".
  iExists itemVal, olid, orid. iFrame "Hval Hol Hor".
  iAssert (c.(ic_loc) ↦{dq} itemVal -∗ own_dll dq l lst prev nxt cs)%I with "[Hpre Hrest]" as "Hback".
  { iIntros "Hval2". rewrite -Hsplit own_dll_app. iExists ml, mf. iFrame "Hpre".
    iExists itemVal, olid, orid. iFrame "Hval2 Hol Hor Hrest". by iPureIntro. }
  iFrame "Hback". by iPureIntro.
Qed.

(** In-place node update: borrow the node at index [k] (its existential heap
    struct [itemVal] with the location / right-neighbour facts), and a wand that takes
    *any* replacement struct [v'] agreeing with [itemVal] on every translated field
    (links / id / content / origins) and carrying flags [if d' then W8 6 else
    W8 2], and gives back the DLL with the cell's [ic_deleted] set to [d'].
    Writing the replacement requires exclusive ownership, so this is the one
    spine lemma pinned to [DfracOwn 1].

    This is the heap counterpart of [Text.Delete]'s [cur.flags |= itemDeleted]:
    storing [set_deleted itemVal] (which keeps every field but the flags, and is
    [W8 6] = Countable+Deleted) flips the cell to [ic_deleted = true]. Passing
    [v' := itemVal], [d' := ic_deleted c] re-establishes the unchanged DLL (the
    already-tombstoned, no-op branch). *)
Lemma own_dll_update_gen (cells : list item_cell) (hd tl : loc) (k : nat) (c : item_cell) :
  cells !! k = Some c ->
  own_dll (DfracOwn 1) hd tl null null cells -∗
    ∃ (itemVal : yjs.item.t),
      "%Hcloc" ∷ ⌜ic_loc c = node_loc cells (Z.of_nat k)⌝ ∗
      "%Hcr" ∷ ⌜itemVal.(yjs.item.right') = node_loc cells (Z.of_nat k + 1)⌝ ∗
      "%Hflags" ∷ ⌜itemVal.(yjs.item.flags') = (if ic_deleted c then W8 6 else W8 2)⌝ ∗
      "%Hrun" ∷ ⌜run_wf (ic_run c)⌝ ∗
      "%Hcontent" ∷ ⌜content <$> ic_run c = explode (toContent itemVal.(yjs.item.content'))⌝ ∗
      "Hval" ∷ ic_loc c ↦ itemVal ∗
      "Hback" ∷ (∀ (v' : yjs.item.t) (d' : bool),
        ⌜v'.(yjs.item.left') = itemVal.(yjs.item.left')⌝ -∗
        ⌜v'.(yjs.item.right') = itemVal.(yjs.item.right')⌝ -∗
        ⌜v'.(yjs.item.id') = itemVal.(yjs.item.id')⌝ -∗
        ⌜v'.(yjs.item.content') = itemVal.(yjs.item.content')⌝ -∗
        ⌜v'.(yjs.item.originLeftId') = itemVal.(yjs.item.originLeftId')⌝ -∗
        ⌜v'.(yjs.item.originRightId') = itemVal.(yjs.item.originRightId')⌝ -∗
        ⌜v'.(yjs.item.parent') = itemVal.(yjs.item.parent')⌝ -∗
        ⌜v'.(yjs.item.flags') = (if d' then W8 6 else W8 2)⌝ -∗
        ic_loc c ↦ v' -∗
        own_dll (DfracOwn 1) hd tl null null
          (<[k := MkItemCell (ic_loc c) (ic_run c) d' (ic_parent c)]> cells)).
Proof.
  move=> Hk. iIntros "Hdll".
  pose proof (take_drop_middle cells k c Hk) as Hsplit.
  set (pre := take k cells) in Hsplit.
  set (suf := drop (S k) cells) in Hsplit.
  iEval (rewrite -Hsplit own_dll_app) in "Hdll".
  iDestruct "Hdll" as (ml mf) "[Hpre Hrest]".
  iDestruct "Hrest" as (itemVal olid orid)
    "(%Hloc & %Hprev & %Hparc & %Hidc & %Hcontentc & %Holidc & %Horidc & %Hflagsc & %Hrunc & Hval & #Hol & #Hor & Hrest2)".
  iDestruct (own_dll_headptr with "Hrest2") as "[%Hhd Hrest2]".
  have Hcloc : ic_loc c = node_loc cells (Z.of_nat k)
    by rewrite /node_loc decide_True; [rewrite Nat2Z.id Hk | lia].
  have Hnn : ic_loc c ≠ null by rewrite -(proj1 Hloc); exact (proj2 Hloc).
  have Hcr : itemVal.(yjs.item.right') = node_loc cells (Z.of_nat k + 1).
  { rewrite Hhd /node_loc decide_True; last lia.
    have HZ : Z.to_nat (Z.of_nat k + 1) = S k by lia.
    rewrite HZ. f_equal. f_equal. rewrite /suf head_lookup lookup_drop Nat.add_0_r //. }
  iExists itemVal. iFrame "Hval".
  iSplit; [iPureIntro; exact Hcloc|].
  iSplit; [iPureIntro; exact Hcr|].
  iSplit; [iPureIntro; exact Hflagsc|].
  iSplit; [iPureIntro; exact Hrunc|].
  iSplit; [iPureIntro; exact Hcontentc|].
  iIntros (v' d' Hl' Hr' Hid' Hcont' HoL' HoR' Hpar' Hfl') "Hval2".
  have Hpv : v'.(yjs.item.left') = ml by rewrite Hl'; exact Hprev.
  have Hparv : v'.(yjs.item.parent') = ic_parent c by rewrite Hpar'; exact Hparc.
  have Hidt : item_id (run_head c) = toYjsId v'.(yjs.item.id') by rewrite Hid'; exact Hidc.
  have Hcontt : content <$> ic_run c = explode (toContent v'.(yjs.item.content'))
    by rewrite Hcont'; exact Hcontentc.
  have Hins : <[k := MkItemCell (ic_loc c) (ic_run c) d' (ic_parent c)]> cells
            = pre ++ MkItemCell (ic_loc c) (ic_run c) d' (ic_parent c) :: suf.
  { rewrite /pre /suf. apply insert_take_drop. apply lookup_lt_Some in Hk; exact Hk. }
  rewrite Hins.
  iApply (own_dll_insert_middle (DfracOwn 1) pre suf
            (MkItemCell (ic_loc c) (ic_run c) d' (ic_parent c)) v' olid orid
            hd tl ml v'.(yjs.item.right')
            Hnn Hpv eq_refl Hparv Hidt Hcontt Holidc Horidc Hfl' Hrunc).
  rewrite Hr' HoL' HoR'.
  iEval (rewrite (proj1 Hloc)) in "Hpre".
  iEval (rewrite (proj1 Hloc)) in "Hrest2".
  iFrame "Hpre Hval2 Hol Hor Hrest2".
Qed.

(* ----- isomorphism to a YjsArrInvariant model ---------------------------- *)

(** [cell_repr m c yi]: the heap cell [c] represents the SINGLE model item
    [yi], i.e. its run is the singleton [[yi]]. Every current creator mints
    such cells; multi-element cells relate to the model only through
    [cells_repr]'s flatten. ([m] is kept for signature uniformity with the
    call sites.) *)
Definition cell_repr (m : list (YjsItem A)) (c : item_cell) (yi : YjsItem A) : Prop :=
  ic_run c = [yi].

(** A [cell_repr] cell is a unit cell. *)
Lemma cell_repr_unit m c yi : cell_repr m c yi -> cell_unit c.
Proof. rewrite /cell_repr /cell_unit => -> //. Qed.

Lemma cell_repr_head m c yi : cell_repr m c yi -> run_head c = yi.
Proof. rewrite /cell_repr /run_head => -> //. Qed.

(** [cells_repr m cells items]: the heap cell list represents the model item
    list by flattening the runs (issue #28): [items = run_flatten cells]. *)
Definition cells_repr (m : list (YjsItem A)) (cells : list item_cell) (items : list (YjsItem A)) : Prop :=
  items = run_flatten cells.

(** Under the all-singleton invariant the isomorphism is length-preserving and
    cellwise (the pre-#28 1:1 correspondence). *)
Lemma cells_repr_length m cells items :
  Forall cell_unit cells ->
  cells_repr m cells items -> length cells = length items.
Proof.
  rewrite /cells_repr => Hunit ->.
  by rewrite (run_flatten_singletons cells Hunit) length_fmap.
Qed.

Lemma cells_repr_lookup m cells items k c :
  Forall cell_unit cells ->
  cells_repr m cells items -> cells !! k = Some c ->
  ∃ yi, items !! k = Some yi ∧ cell_repr m c yi.
Proof.
  rewrite /cells_repr /cell_repr => Hunit -> Hk. exists (run_head c).
  rewrite (run_flatten_singletons cells Hunit) list_lookup_fmap Hk /=.
  split; first done.
  have Hu : cell_unit c := Forall_lookup_1 _ _ _ _ Hunit Hk.
  rewrite /cell_unit in Hu. rewrite /run_head.
  destruct (ic_run c) as [|y [|y' r']]; simpl in Hu; [lia | done | lia].
Qed.

Lemma cells_repr_nil m : cells_repr m [] [].
Proof. reflexivity. Qed.

Lemma cells_repr_cons m c yi cs ys :
  cell_repr m c yi -> cells_repr m cs ys -> cells_repr m (c :: cs) (yi :: ys).
Proof.
  rewrite /cells_repr /cell_repr => Hc Hcs.
  by rewrite run_flatten_cons Hc Hcs.
Qed.

(** Inserting a corresponding cell/item at the same position preserves the
    isomorphism (the splice's model side); position alignment needs the
    all-singleton invariant. *)
Lemma cells_repr_insert m cells items (k : nat) c yi :
  Forall cell_unit cells ->
  cells_repr m cells items -> cell_repr m c yi ->
  cells_repr m (take k cells ++ c :: drop k cells) (take k items ++ yi :: drop k items).
Proof.
  rewrite /cells_repr /cell_repr => Hunit -> Hc.
  rewrite run_flatten_app run_flatten_cons Hc.
  rewrite (run_flatten_singletons _ (Forall_take _ _ _ Hunit)).
  rewrite (run_flatten_singletons _ (Forall_drop _ _ _ Hunit)).
  by rewrite (run_flatten_singletons cells Hunit) fmap_take fmap_drop.
Qed.

(** [cells_repr] does not depend on the resolution context [m] (it is a plain
    fmap equality), so threading a fresh model is a no-op. *)
Lemma cells_repr_m_irrel (m m' : list (YjsItem A)) cells items :
  cells_repr m cells items -> cells_repr m' cells items.
Proof. by rewrite /cells_repr. Qed.

Lemma cells_repr_app (m : list (YjsItem A)) cs1 cs2 ys1 ys2 :
  cells_repr m cs1 ys1 -> cells_repr m cs2 ys2 -> cells_repr m (cs1 ++ cs2) (ys1 ++ ys2).
Proof. rewrite /cells_repr => -> ->. by rewrite run_flatten_app. Qed.

Lemma cells_repr_take (m : list (YjsItem A)) cells items k :
  Forall cell_unit cells ->
  cells_repr m cells items -> cells_repr m (take k cells) (take k items).
Proof.
  rewrite /cells_repr => Hunit ->.
  rewrite (run_flatten_singletons _ (Forall_take _ _ _ Hunit)).
  by rewrite (run_flatten_singletons cells Hunit) fmap_take.
Qed.

Lemma cells_repr_drop (m : list (YjsItem A)) cells items k :
  Forall cell_unit cells ->
  cells_repr m cells items -> cells_repr m (drop k cells) (drop k items).
Proof.
  rewrite /cells_repr => Hunit ->.
  rewrite (run_flatten_singletons _ (Forall_drop _ _ _ Hunit)).
  by rewrite (run_flatten_singletons cells Hunit) fmap_drop.
Qed.

(** Replacing a cell with one carrying the SAME run preserves the isomorphism
    (the flatten never reads [ic_deleted] / [ic_loc]). [Text.Delete] flips a
    cell's [ic_deleted] without touching its [ic_run]. *)
Lemma cells_repr_update_run m cells items (k : nat) c c' :
  cells !! k = Some c -> ic_run c' = ic_run c ->
  cells_repr m cells items -> cells_repr m (<[k := c']> cells) items.
Proof.
  rewrite /cells_repr => Hck Hrun ->.
  rewrite /run_flatten list_fmap_insert Hrun. f_equal. symmetry.
  apply list_insert_id. rewrite list_lookup_fmap Hck //.
Qed.

(* ----- the deletion layer: tombstoning a cell ---------------------------- *)

(** Visible count is additive over append. *)
Lemma num_visible_app (l1 l2 : list item_cell) :
  num_visible (l1 ++ l2) = (num_visible l1 + num_visible l2)%nat.
Proof. rewrite /num_visible fmap_app list_sum_app //. Qed.

(** Inserting a *visible* unit cell increments the visible count. Read by
    [Store.Integrate] / [Text.Insert], whose new items are always visible
    1-char runs. *)
Lemma num_visible_insert_visible (cells : list item_cell) (k : nat) (c : item_cell) :
  ic_deleted c = false -> cell_unit c ->
  num_visible (take k cells ++ c :: drop k cells) = S (num_visible cells).
Proof.
  rewrite /cell_unit => Hc Hu. rewrite /num_visible.
  rewrite fmap_app fmap_cons list_sum_app /=. rewrite Hc Hu.
  rewrite -[in S (list_sum _)](take_drop k cells) fmap_app list_sum_app. lia.
Qed.

(** The heap effect of [item.flags |= itemDeleted]: set the Deleted bit. *)
Definition set_deleted (v : yjs.item.t) : yjs.item.t :=
  v <| yjs.item.flags' := w8_word_instance.(word.or) v.(yjs.item.flags') (W8 4) |>.

(** [set_deleted] forces flags to [W8 6] (Countable + Deleted) regardless of the
    prior Deleted bit ([W8 2] or [W8 6] both [or] to [W8 6]). *)
Lemma set_deleted_flags (v : yjs.item.t) (d : bool) :
  v.(yjs.item.flags') = (if d then W8 6 else W8 2) ->
  (set_deleted v).(yjs.item.flags') = W8 6.
Proof. rewrite /set_deleted /= => ->. by destruct d. Qed.

(** The cell with its [ic_deleted] bit set (its model run [ic_run] unchanged). *)
Definition flip_cell (c : item_cell) : item_cell :=
  MkItemCell (ic_loc c) (ic_run c) true (ic_parent c).

(** Flipping a cell's Deleted bit preserves [cell_repr]: [ic_run] is untouched. *)
Lemma cell_repr_flip (m : list (YjsItem A)) (c : item_cell) (yi : YjsItem A) :
  cell_repr m c yi -> cell_repr m (flip_cell c) yi.
Proof. rewrite /cell_repr /flip_cell /=. tauto. Qed.

(** Tombstoning a visible unit cell drops the visible count by one. *)
Lemma num_visible_flip (cells : list item_cell) (k : nat) (c : item_cell) :
  cells !! k = Some c -> ic_deleted c = false -> cell_unit c ->
  num_visible (<[k := flip_cell c]> cells) = pred (num_visible cells).
Proof.
  rewrite /cell_unit => Hk Hd Hu.
  have Hins : <[k := flip_cell c]> cells = take k cells ++ flip_cell c :: drop (S k) cells
    by (apply insert_take_drop; apply lookup_lt_Some in Hk; exact Hk).
  rewrite Hins /num_visible fmap_app fmap_cons list_sum_app /flip_cell /=.
  rewrite -[in pred (list_sum _)](take_drop_middle cells k c Hk).
  rewrite fmap_app fmap_cons list_sum_app /=. rewrite Hd Hu. lia.
Qed.

(* ----- run-aware generalizations (issue #28 part 6) ----------------------- *)

(** Inserting a *visible* cell adds its whole run length to the visible count:
    the general form of [num_visible_insert_visible] (the Go bumps [parent.len]
    by [item.Len()], the run length). *)
Lemma num_visible_insert_visible_run (cells : list item_cell) (k : nat) (c : item_cell) :
  ic_deleted c = false ->
  num_visible (take k cells ++ c :: drop k cells) = (num_visible cells + length (ic_run c))%nat.
Proof.
  move=> Hc. rewrite /num_visible.
  rewrite fmap_app fmap_cons list_sum_app /=. rewrite Hc.
  rewrite -[in X in _ = (X + _)%nat](take_drop k cells) fmap_app list_sum_app. lia.
Qed.

(** Tombstoning a visible cell drops the visible count by its run length: the
    general form of [num_visible_flip]. *)
Lemma num_visible_flip_run (cells : list item_cell) (k : nat) (c : item_cell) :
  cells !! k = Some c -> ic_deleted c = false ->
  num_visible (<[k := flip_cell c]> cells) = (num_visible cells - length (ic_run c))%nat.
Proof.
  move=> Hk Hd.
  have Hins : <[k := flip_cell c]> cells = take k cells ++ flip_cell c :: drop (S k) cells
    by (apply insert_take_drop; apply lookup_lt_Some in Hk; exact Hk).
  rewrite Hins /num_visible fmap_app fmap_cons list_sum_app /flip_cell /=.
  rewrite -[in X in _ = (X - _)%nat](take_drop_middle cells k c Hk).
  rewrite fmap_app fmap_cons list_sum_app /=. rewrite Hd. lia.
Qed.

(* ----- location freshness (issue #28 part 6) ------------------------------ *)

(** A fully-owned [item] struct points-to conflicts with any other points-to at
    the same location. Perennial New's [TypedPointsto] class carries no
    dfrac-validity law (only [typed_pointsto_agree]), so no generic conflict
    lemma exists; derive it for [yjs.item.t] concretely through the generated
    field decomposition and the primitive [heap_pointsto] fraction validity
    (candidate upstream addition: a validity law in [TypedPointsto]). *)
Lemma item_pointsto_conflict (l : loc) (v1 v2 : yjs.item.t) (dq : dfrac) :
  l ↦ v1 -∗ l ↦{dq} v2 -∗ False.
Proof.
  iIntros "H1 H2".
  iDestruct (typed_pointsto_split with "H1") as "H1".
  iDestruct (typed_pointsto_split with "H2") as "H2".
  iDestruct "H1" as "(_ & _ & _ & _ & _ & _ & _ & Hf1 & _)".
  iDestruct "H2" as "(_ & _ & _ & _ & _ & _ & _ & Hf2 & _)".
  iEval (rewrite typed_pointsto_unseal_eq /=) in "Hf1".
  iEval (rewrite typed_pointsto_unseal_eq /=) in "Hf2".
  iDestruct "Hf1" as "[Hf1 _]". iDestruct "Hf2" as "[Hf2 _]".
  iCombine "Hf1 Hf2" gives %[Hvalid _].
  exfalso. exact (exclusive_l (DfracOwn 1) dq Hvalid).
Qed.

(** A fully-owned node struct's location is fresh for any DLL segment: the
    source of the [NoDup (ic_loc <$> cells)] maintenance when [Integrate] /
    [splitNode] splice a freshly allocated node (issue #28 part 6). *)
Lemma own_dll_fresh (dq : dfrac) (p : loc) (v : yjs.item.t)
    (l last prev next : loc) (cells : list item_cell) :
  p ↦ v -∗ own_dll dq l last prev next cells -∗ ⌜p ∉ ic_loc <$> cells⌝.
Proof.
  iIntros "Hp Hdll".
  iInduction cells as [|c rest] "IH" forall (l prev).
  - iPureIntro. apply not_elem_of_nil.
  - iDestruct "Hdll" as (itemVal olid orid) "H". iNamed "H".
    destruct (decide (p = ic_loc c)) as [-> | Hne].
    + iExFalso. iApply (item_pointsto_conflict with "Hp Hval").
    + iDestruct ("IH" with "Hp Hrest") as %Hnotin.
      iPureIntro. rewrite fmap_cons. apply not_elem_of_cons.
      split; [exact Hne | exact Hnotin].
Qed.

End item.
