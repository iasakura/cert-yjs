(** The [item] type: its per-method WP specs and the heap representation of an
    item sequence with its model correspondence.

    Bottom to top:
    - per-method WP specs for an individual node: [item.Indexable] / [item.Len] /
      [item.Deleted] and [itemPtrEqual] (pointer identity = model id).
    - [is_dll l last prev next cells]: the doubly-linked-list spine of [item]
      nodes (each carrying its [Item] struct and the two origin-id cells), with
      its split / join / accessor / insert lemmas. Adapted from the reference
      sorted-DLL proof (iasakura/perennial-sandbox, dll/list.go, [is_dlist_node]).
    - [resolve_*] / [cell_repr] / [cells_repr]: the cellwise isomorphism between
      the heap node list and a model [list (YjsItem A)] (origins resolved by id).
    - [is_ytext] / [is_valid_ytext]: a heap [yType] whose [start] heads such a
      DLL, isomorphic to a model list that — for [is_valid_ytext] — satisfies
      [YjsArrInvariant].

    This is the data-structure invariant the [Store.Integrate] / [Text.Insert]
    proofs ([yjs_store] / [yjs_text]) are stated against. *)
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

(** Number of visible (non-deleted) cells: the value carried in the heap
    [yType.len] field. Every cell is Countable, so visible ⇔ not Deleted; the
    flag is promoted onto the abstract cell as [ic_deleted]. *)
Definition num_visible (cells : list item_cell) : nat :=
  length (List.filter (λ c, negb (ic_deleted c)) cells).

(** Read the promoted Deleted / Countable bits back off the [is_dll] flag pin
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
    these once keeps the [findPos] loop free of nested method-call stepping. *)
Lemma wp_item__Indexable (l : loc) (v : yjs.item.t) :
  is_countable_flag v = true ->
  {{{ is_pkg_init yjs ∗ l ↦ v }}}
    l @! (go.PointerType yjs.item) @! "Indexable" #()
  {{{ RET #(negb (is_deleted_flag v)); l ↦ v }}}.
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
  {{{ is_pkg_init yjs ∗ l ↦ v }}}
    l @! (go.PointerType yjs.item) @! "Deleted" #()
  {{{ RET #(is_deleted_flag v); l ↦ v }}}.
Proof.
  wp_start as "Hl". wp_auto.
  wp_method_call. wp_call. rewrite /yjs.item__Deletedⁱᵐᵖˡ. wp_auto.
  iApply "HΦ". iFrame "Hl".
Qed.
(* ----- the doubly-linked spine (adapted from the reference DLL) ----------- *)

(** [is_dll l last prev next cells]: the DLL segment whose head node is [l] and
    whose last node is [last]; [prev] is the [left]-pointer of [l] and [next] is
    the [right]-pointer of [last]. Mirrors the reference [is_dlist_node].

    Each node existentially quantifies its full heap struct [iv : yjs.item.t] and
    the two resolved origin ids [olid]/[orid], constrained to *translate* to the
    cell's model item [ic_item c]: the heap id [toYjsId]-maps to [item_id], the
    content matches, and the origin pointers carry ids whose [toYjsId] images are
    [ic_item c]'s origin ids. The volatile spine links ([left'] = [prev],
    [right'] heads the rest) are also constraints on [iv], NOT data of the cell —
    so [Store.Integrate]'s neighbour relinking changes only [iv] and leaves the
    abstract [cells] (hence [ic_item <$> cells]) unchanged. The flag / length pins
    live here too: the struct is Countable and its Deleted bit equals the cell's
    [ic_deleted] ([flags'] = [W8 6] when deleted, [W8 2] when visible), and its
    content is one byte. *)
Fixpoint is_dll (l last prev next : loc) (cells : list item_cell) : iProp Σ :=
  match cells with
  | [] => ⌜l = next ∧ last = prev⌝
  | c :: rest =>
      ∃ (iv : yjs.item.t) (olid orid : option yjs.id.t),
      "%Hloc" ∷ ⌜l = ic_loc c ∧ l ≠ null⌝ ∗
      "%Hprev" ∷ ⌜iv.(yjs.item.left') = prev⌝ ∗
      "%Hid" ∷ ⌜item_id (ic_item c) = toYjsId iv.(yjs.item.id')⌝ ∗
      "%Hcontent" ∷ ⌜content (ic_item c) = toContent iv.(yjs.item.content')⌝ ∗
      "%Holid" ∷ ⌜origin_id (origin (ic_item c)) = toYjsId <$> olid⌝ ∗
      "%Horid" ∷ ⌜origin_id (rightOrigin (ic_item c)) = toYjsId <$> orid⌝ ∗
      "%Hflags" ∷ ⌜iv.(yjs.item.flags') = (if ic_deleted c then W8 6 else W8 2)⌝ ∗
      "%Hcontlen" ∷ ⌜length (iv.(yjs.item.content').(yjs.content.content')) = 1%nat⌝ ∗
      "Hval" ∷ ic_loc c ↦ iv ∗
      "Holeft" ∷ is_origin_id iv.(yjs.item.originLeftId') olid ∗
      "Horight" ∷ is_origin_id iv.(yjs.item.originRightId') orid ∗
      "Hrest" ∷ is_dll iv.(yjs.item.right') last l next rest
  end.

(* ----- structural lemmas for the DLL spine ------------------------------- *)

(** Split / join a DLL segment at a list append (cf. reference [is_dlist_node_app]). *)
Lemma is_dll_app (cs1 cs2 : list item_cell) (l last prev next : loc) :
  is_dll l last prev next (cs1 ++ cs2)
  ⊣⊢ ∃ mid_last mid_fst,
       is_dll l mid_last prev mid_fst cs1 ∗ is_dll mid_fst last mid_last next cs2.
Proof.
  revert l prev. induction cs1 as [|c cs1 IH] => l prev /=.
  - iSplit.
    + iIntros "H". iExists prev, l. by iFrame.
    + iIntros "(%ml & %mf & [%H1 %H2] & H)". subst. by iFrame.
  - iSplit.
    + iIntros "H". iNamed "H". rewrite IH.
      iDestruct "Hrest" as "(%ml & %mf & H1 & H2)".
      iExists ml, mf. iFrame "H2". iExists iv, olid, orid.
      iFrame "Hval Holeft Horight H1". by iPureIntro.
    + iIntros "(%ml & %mf & H1 & H2)". iNamed "H1".
      iExists iv, olid, orid. iFrame "Hval Holeft Horight".
      iAssert (is_dll iv.(yjs.item.right') last l next (cs1 ++ cs2)) with "[Hrest H2]" as "HR".
      { rewrite IH. iExists ml, mf. iFrame "Hrest H2". }
      iFrame "HR". by iPureIntro.
Qed.

(** Splice a fresh node [newc] between two DLL segments whose boundary fields are
    already relinked to it ([cs1]'s last [right'] and [cs2]'s first [left'] point
    at [ic_loc newc], and [newc]'s [left']/[right'] at the two boundaries). Used to
    rejoin the document DLL after [Store.Integrate] inserts an item. *)
Lemma is_dll_insert_middle (cs1 cs2 : list item_cell) (newc : item_cell)
    (iv : yjs.item.t) (olid orid : option yjs.id.t) (hd tl ml mr : loc) :
  ic_loc newc ≠ null ->
  iv.(yjs.item.left') = ml ->
  iv.(yjs.item.right') = mr ->
  item_id (ic_item newc) = toYjsId iv.(yjs.item.id') ->
  content (ic_item newc) = toContent iv.(yjs.item.content') ->
  origin_id (origin (ic_item newc)) = toYjsId <$> olid ->
  origin_id (rightOrigin (ic_item newc)) = toYjsId <$> orid ->
  iv.(yjs.item.flags') = (if ic_deleted newc then W8 6 else W8 2) ->
  length (iv.(yjs.item.content').(yjs.content.content')) = 1%nat ->
  is_dll hd ml null (ic_loc newc) cs1 ∗
  ic_loc newc ↦ iv ∗
  is_origin_id iv.(yjs.item.originLeftId') olid ∗
  is_origin_id iv.(yjs.item.originRightId') orid ∗
  is_dll mr tl (ic_loc newc) null cs2
  ⊢ is_dll hd tl null null (cs1 ++ newc :: cs2).
Proof.
  move=> Hnn Hl Hr Hidt Hcont Holidt Horidt Hflags Hcontlen.
  iIntros "(Hdll1 & Hnode & Hol & Hor & Hdll2)".
  rewrite is_dll_app. iExists ml, (ic_loc newc). iFrame "Hdll1".
  simpl. iExists iv, olid, orid. rewrite Hr. iFrame "Hnode Hol Hor Hdll2".
  iPureIntro; split_and!;
    [reflexivity | exact Hnn | exact Hl | exact Hidt | exact Hcont
    | exact Holidt | exact Horidt | exact Hflags | exact Hcontlen].
Qed.

(** A DLL headed by [null] is empty. *)
Lemma is_dll_null_nil last prev next cells :
  is_dll null last prev next cells -∗ ⌜cells = []⌝.
Proof.
  destruct cells as [|c cs]; [by auto|].
  iIntros "H". iNamed "H". iPureIntro. exfalso. by apply (proj2 Hloc).
Qed.

(** The [last] pointer of a DLL segment is the location of its last node (or the
    [prev] sentinel when empty); the resource is returned. Used to read a node's
    [left'] neighbour. *)
Lemma is_dll_lastptr (l lst prev nxt : loc) (cs : list item_cell) :
  is_dll l lst prev nxt cs -∗
    ⌜lst = default prev (ic_loc <$> list.last cs)⌝ ∗ is_dll l lst prev nxt cs.
Proof.
  iInduction cs as [|c cs IH] forall (l prev).
  - iIntros "H". iDestruct "H" as %[Hl Hlst]. iPureIntro; split; [exact Hlst | split; done].
  - iIntros "H". iNamed "H".
    iDestruct ("IH" with "Hrest") as "[%Hlst Hrest]".
    iSplitR.
    + iPureIntro. rewrite last_cons. destruct (list.last cs) as [y|] eqn:Hl.
      * by rewrite Hlst /=.
      * rewrite /= in Hlst. rewrite Hlst. by destruct Hloc as [-> _].
    + iExists iv, olid, orid. iFrame "Hval Holeft Horight Hrest".
      iPureIntro; split_and!;
        [exact (proj1 Hloc) | exact (proj2 Hloc) | exact Hprev | exact Hid
        | exact Hcontent | exact Holid | exact Horid | exact Hflags | exact Hcontlen].
Qed.

(** The head pointer of a DLL segment is the location of its first node (or the
    [nxt] sentinel when empty); the resource is returned. The head-side analogue
    of [is_dll_lastptr], used to read a node's [right'] neighbour. *)
Lemma is_dll_headptr (l lst prev nxt : loc) (cs : list item_cell) :
  is_dll l lst prev nxt cs -∗
    ⌜l = default nxt (ic_loc <$> head cs)⌝ ∗ is_dll l lst prev nxt cs.
Proof.
  destruct cs as [|c cs'].
  - iIntros "H". iDestruct "H" as %[Hl Hlst].
    iSplit; iPureIntro; [rewrite /= Hl // | split; [exact Hl | exact Hlst]].
  - iIntros "H". iNamed "H".
    iSplit.
    + iPureIntro. rewrite /=. exact (proj1 Hloc).
    + iExists iv, olid, orid. iFrame "Hval Holeft Horight Hrest".
      iPureIntro; split_and!;
        [exact (proj1 Hloc) | exact (proj2 Hloc) | exact Hprev | exact Hid
        | exact Hcontent | exact Holid | exact Horid | exact Hflags | exact Hcontlen].
Qed.

(** The head of a full DLL is [node_loc cells 0] (the first node, or [null] when
    empty) — the head-side analogue of [is_dll_lastptr]. Used to align
    [parent.start] with [node_loc cells 0] for a head insertion. *)
Lemma is_dll_head_node (cells : list item_cell) (hd tl : loc) :
  is_dll hd tl null null cells -∗ ⌜hd = node_loc cells 0⌝.
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
Lemma is_dll_acc (cells : list item_cell) (hd tl : loc) (k : nat) (c : item_cell) :
  cells !! k = Some c ->
  is_dll hd tl null null cells -∗
    ∃ (iv : yjs.item.t) (olid orid : option yjs.id.t),
    "%Hcloc" ∷ ⌜ic_loc c = node_loc cells (Z.of_nat k)⌝ ∗
    "%Hcl" ∷ ⌜iv.(yjs.item.left') = node_loc cells (Z.of_nat k - 1)⌝ ∗
    "%Hcr" ∷ ⌜iv.(yjs.item.right') = node_loc cells (Z.of_nat k + 1)⌝ ∗
    "%Hid" ∷ ⌜item_id (ic_item c) = toYjsId iv.(yjs.item.id')⌝ ∗
    "%Hcontent" ∷ ⌜content (ic_item c) = toContent iv.(yjs.item.content')⌝ ∗
    "%Holid" ∷ ⌜origin_id (origin (ic_item c)) = toYjsId <$> olid⌝ ∗
    "%Horid" ∷ ⌜origin_id (rightOrigin (ic_item c)) = toYjsId <$> orid⌝ ∗
    "%Hflags" ∷ ⌜iv.(yjs.item.flags') = (if ic_deleted c then W8 6 else W8 2)⌝ ∗
    "%Hcontlen" ∷ ⌜length (iv.(yjs.item.content').(yjs.content.content')) = 1%nat⌝ ∗
    "Hcval" ∷ ic_loc c ↦ iv ∗
    "Hcol" ∷ is_origin_id iv.(yjs.item.originLeftId') olid ∗
    "Hcor" ∷ is_origin_id iv.(yjs.item.originRightId') orid ∗
    "Hback" ∷ (ic_loc c ↦ iv -∗ is_dll hd tl null null cells).
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
  iEval (rewrite is_dll_app) in "Hdll".
  iDestruct "Hdll" as (ml mf) "[Hpre Hrest]".
  iDestruct "Hrest" as (iv olid orid)
    "(%Hloc & %Hprev & %Hidc & %Hcontentc & %Holidc & %Horidc & %Hflagsc & %Hcontlenc & Hval & #Hol & #Hor & Hrest2)".
  iDestruct (is_dll_lastptr with "Hpre") as "[%Hml Hpre]".
  iDestruct (is_dll_headptr with "Hrest2") as "[%Hhd Hrest2]".
  have Hcl : iv.(yjs.item.left') = node_loc cells (Z.of_nat k - 1).
  { rewrite Hprev Hml. exact Hpe. }
  have Hcloc : c.(ic_loc) = node_loc cells k by rewrite /node_loc decide_True; [rewrite Nat2Z.id Hk | lia].
  have Hnn : c.(ic_loc) ≠ null by rewrite -(proj1 Hloc); exact (proj2 Hloc).
  have Hcr : iv.(yjs.item.right') = node_loc cells (Z.of_nat k + 1).
  { rewrite Hhd /node_loc decide_True; last lia.
    have HZ : Z.to_nat (Z.of_nat k + 1) = S k by lia.
    rewrite HZ. f_equal. f_equal. rewrite /suf head_lookup lookup_drop Nat.add_0_r //. }
  iExists iv, olid, orid. iFrame "Hval Hol Hor".
  (* the wand: re-splice [c] between [pre] and [suf] (relinking is invisible to
     the abstract cells, so the same [iv] goes back in) *)
  iAssert (ic_loc c ↦ iv -∗ is_dll hd tl null null cells)%I with "[Hpre Hrest2]" as "Hback".
  { iIntros "Hval2". iEval (rewrite -Hsplit).
    iApply (is_dll_insert_middle pre suf c iv olid orid hd tl ml iv.(yjs.item.right')
              Hnn Hprev eq_refl Hidc Hcontentc Holidc Horidc Hflagsc Hcontlenc).
    iFrame "Hval2 Hol Hor". rewrite -(proj1 Hloc). iFrame "Hpre Hrest2". }
  iFrame "Hback". by iPureIntro.
Qed.

(** Every node at an in-bounds index is a non-null location (DLL nodes are
    non-null); the DLL resource is returned. Used to argue [node_loc cells
    (destIdx-1) = null] forces [destIdx = 0] (head insertion). *)
Lemma node_loc_lt_not_null (cells : list item_cell) (hd tl : loc) (k : nat) :
  (k < length cells)%nat ->
  is_dll hd tl null null cells -∗ ⌜node_loc cells (Z.of_nat k) ≠ null⌝ ∗ is_dll hd tl null null cells.
Proof.
  move=> Hk. iIntros "Hdll".
  destruct (cells !! k) as [c|] eqn:Hc; last by (apply lookup_ge_None in Hc; lia).
  iDestruct (is_dll_acc cells hd tl k c Hc with "Hdll") as "H". iNamed "H".
  iDestruct (typed_pointsto_not_null with "Hcval") as %Hnn.
  iSplitR "Hcval Hback".
  - iPureIntro. rewrite -Hcloc. exact Hnn.
  - iApply "Hback". iFrame "Hcval".
Qed.

(** A plain value accessor: borrow the node's (existential) heap struct at index
    [k] from *any* DLL segment (arbitrary [prev]/[nxt]), with its local
    translation facts and a wand to restore it. Unlike [is_dll_acc] it carries no
    [node_loc] facts, so it composes on sub-segments (used to read the
    loop-constant [right] node out of the suffix). *)
Lemma is_dll_lookup_acc (l lst prev nxt : loc) (cs : list item_cell) (k : nat) (c : item_cell) :
  cs !! k = Some c ->
  is_dll l lst prev nxt cs -∗
    ∃ (iv : yjs.item.t) (olid orid : option yjs.id.t),
      "%Hid" ∷ ⌜item_id (ic_item c) = toYjsId iv.(yjs.item.id')⌝ ∗
      "%Hcontent" ∷ ⌜content (ic_item c) = toContent iv.(yjs.item.content')⌝ ∗
      "%Holid" ∷ ⌜origin_id (origin (ic_item c)) = toYjsId <$> olid⌝ ∗
      "%Horid" ∷ ⌜origin_id (rightOrigin (ic_item c)) = toYjsId <$> orid⌝ ∗
      "%Hflags" ∷ ⌜iv.(yjs.item.flags') = (if ic_deleted c then W8 6 else W8 2)⌝ ∗
      "%Hcontlen" ∷ ⌜length (iv.(yjs.item.content').(yjs.content.content')) = 1%nat⌝ ∗
      "Hval" ∷ c.(ic_loc) ↦ iv ∗
      "Hcol" ∷ is_origin_id iv.(yjs.item.originLeftId') olid ∗
      "Hcor" ∷ is_origin_id iv.(yjs.item.originRightId') orid ∗
      "Hback" ∷ (c.(ic_loc) ↦ iv -∗ is_dll l lst prev nxt cs).
Proof.
  move=> Hk. iIntros "Hdll".
  pose proof (take_drop_middle cs k c Hk) as Hsplit.
  set (pre := take k cs) in Hsplit.
  set (suf := drop (S k) cs) in Hsplit.
  iEval (rewrite -Hsplit is_dll_app) in "Hdll".
  iDestruct "Hdll" as (ml mf) "[Hpre Hrest]".
  iDestruct "Hrest" as (iv olid orid)
    "(%Hloc & %Hprev & %Hidc & %Hcontentc & %Holidc & %Horidc & %Hflagsc & %Hcontlenc & Hval & #Hol & #Hor & Hrest)".
  iExists iv, olid, orid. iFrame "Hval Hol Hor".
  iAssert (c.(ic_loc) ↦ iv -∗ is_dll l lst prev nxt cs)%I with "[Hpre Hrest]" as "Hback".
  { iIntros "Hval2". rewrite -Hsplit is_dll_app. iExists ml, mf. iFrame "Hpre".
    iExists iv, olid, orid. iFrame "Hval2 Hol Hor Hrest". by iPureIntro. }
  iFrame "Hback". by iPureIntro.
Qed.

(** In-place node update: borrow the node at index [k] (its existential heap
    struct [iv] with the location / right-neighbour facts), and a wand that takes
    *any* replacement struct [v'] agreeing with [iv] on every translated field
    (links / id / content / origins) and carrying flags [if d' then W8 6 else
    W8 2], and gives back the DLL with the cell's [ic_deleted] set to [d'].

    This is the heap counterpart of [Text.Delete]'s [cur.flags |= itemDeleted]:
    storing [set_deleted iv] (which keeps every field but the flags, and is
    [W8 6] = Countable+Deleted) flips the cell to [ic_deleted = true]. Passing
    [v' := iv], [d' := ic_deleted c] re-establishes the unchanged DLL (the
    already-tombstoned, no-op branch). *)
Lemma is_dll_update_gen (cells : list item_cell) (hd tl : loc) (k : nat) (c : item_cell) :
  cells !! k = Some c ->
  is_dll hd tl null null cells -∗
    ∃ (iv : yjs.item.t),
      "%Hcloc" ∷ ⌜ic_loc c = node_loc cells (Z.of_nat k)⌝ ∗
      "%Hcr" ∷ ⌜iv.(yjs.item.right') = node_loc cells (Z.of_nat k + 1)⌝ ∗
      "%Hflags" ∷ ⌜iv.(yjs.item.flags') = (if ic_deleted c then W8 6 else W8 2)⌝ ∗
      "%Hcontlen" ∷ ⌜length (iv.(yjs.item.content').(yjs.content.content')) = 1%nat⌝ ∗
      "Hval" ∷ ic_loc c ↦ iv ∗
      "Hback" ∷ (∀ (v' : yjs.item.t) (d' : bool),
        ⌜v'.(yjs.item.left') = iv.(yjs.item.left')⌝ -∗
        ⌜v'.(yjs.item.right') = iv.(yjs.item.right')⌝ -∗
        ⌜v'.(yjs.item.id') = iv.(yjs.item.id')⌝ -∗
        ⌜v'.(yjs.item.content') = iv.(yjs.item.content')⌝ -∗
        ⌜v'.(yjs.item.originLeftId') = iv.(yjs.item.originLeftId')⌝ -∗
        ⌜v'.(yjs.item.originRightId') = iv.(yjs.item.originRightId')⌝ -∗
        ⌜v'.(yjs.item.flags') = (if d' then W8 6 else W8 2)⌝ -∗
        ic_loc c ↦ v' -∗
        is_dll hd tl null null (<[k := MkItemCell (ic_loc c) (ic_item c) d']> cells)).
Proof.
  move=> Hk. iIntros "Hdll".
  pose proof (take_drop_middle cells k c Hk) as Hsplit.
  set (pre := take k cells) in Hsplit.
  set (suf := drop (S k) cells) in Hsplit.
  iEval (rewrite -Hsplit is_dll_app) in "Hdll".
  iDestruct "Hdll" as (ml mf) "[Hpre Hrest]".
  iDestruct "Hrest" as (iv olid orid)
    "(%Hloc & %Hprev & %Hidc & %Hcontentc & %Holidc & %Horidc & %Hflagsc & %Hcontlenc & Hval & #Hol & #Hor & Hrest2)".
  iDestruct (is_dll_headptr with "Hrest2") as "[%Hhd Hrest2]".
  have Hcloc : ic_loc c = node_loc cells (Z.of_nat k)
    by rewrite /node_loc decide_True; [rewrite Nat2Z.id Hk | lia].
  have Hnn : ic_loc c ≠ null by rewrite -(proj1 Hloc); exact (proj2 Hloc).
  have Hcr : iv.(yjs.item.right') = node_loc cells (Z.of_nat k + 1).
  { rewrite Hhd /node_loc decide_True; last lia.
    have HZ : Z.to_nat (Z.of_nat k + 1) = S k by lia.
    rewrite HZ. f_equal. f_equal. rewrite /suf head_lookup lookup_drop Nat.add_0_r //. }
  iExists iv. iFrame "Hval".
  iSplit; [iPureIntro; exact Hcloc|].
  iSplit; [iPureIntro; exact Hcr|].
  iSplit; [iPureIntro; exact Hflagsc|].
  iSplit; [iPureIntro; exact Hcontlenc|].
  iIntros (v' d' Hl' Hr' Hid' Hcont' HoL' HoR' Hfl') "Hval2".
  have Hpv : v'.(yjs.item.left') = ml by rewrite Hl'; exact Hprev.
  have Hidt : item_id (ic_item c) = toYjsId v'.(yjs.item.id') by rewrite Hid'; exact Hidc.
  have Hcontt : content (ic_item c) = toContent v'.(yjs.item.content') by rewrite Hcont'; exact Hcontentc.
  have Hcontlent : length (v'.(yjs.item.content').(yjs.content.content')) = 1%nat
    by rewrite Hcont'; exact Hcontlenc.
  have Hins : <[k := MkItemCell (ic_loc c) (ic_item c) d']> cells
            = pre ++ MkItemCell (ic_loc c) (ic_item c) d' :: suf.
  { rewrite /pre /suf. apply insert_take_drop. apply lookup_lt_Some in Hk; exact Hk. }
  rewrite Hins.
  iApply (is_dll_insert_middle pre suf (MkItemCell (ic_loc c) (ic_item c) d') v' olid orid
            hd tl ml v'.(yjs.item.right')
            Hnn Hpv eq_refl Hidt Hcontt Holidc Horidc Hfl' Hcontlent).
  rewrite Hr' HoL' HoR'.
  iEval (rewrite (proj1 Hloc)) in "Hpre".
  iEval (rewrite (proj1 Hloc)) in "Hrest2".
  iFrame "Hpre Hval2 Hol Hor Hrest2".
Qed.

(* ----- isomorphism to a YjsArrInvariant model ---------------------------- *)

(** [cell_repr m c yi]: the model item [yi] the heap cell [c] represents is
    exactly [ic_item c]. Since the cell now carries its model item directly, the
    "isomorphism" collapses to near-identity: the id / content / origin / flag /
    length facts that the old [cell_repr] spelled out are now carried by [is_dll]
    (constraining the existential heap struct), and order-defining origins live in
    [ic_item]. ([m] is kept for signature uniformity with the call sites.) *)
Definition cell_repr (m : list (YjsItem A)) (c : item_cell) (yi : YjsItem A) : Prop :=
  yi = ic_item c.

(** [cells_repr m cells items]: the heap cell list represents the model item list
    cellwise, i.e. [items = ic_item <$> cells]. This is the (now trivial)
    "isomorphism" between the heap node sequence and a [list (YjsItem A)]. *)
Definition cells_repr (m : list (YjsItem A)) (cells : list item_cell) (items : list (YjsItem A)) : Prop :=
  items = ic_item <$> cells.

(** The isomorphism is length-preserving and cellwise. *)
Lemma cells_repr_length m cells items :
  cells_repr m cells items -> length cells = length items.
Proof. rewrite /cells_repr => ->. by rewrite length_fmap. Qed.

Lemma cells_repr_lookup m cells items k c :
  cells_repr m cells items -> cells !! k = Some c ->
  ∃ yi, items !! k = Some yi ∧ cell_repr m c yi.
Proof.
  rewrite /cells_repr /cell_repr => -> Hk. exists (ic_item c).
  by rewrite list_lookup_fmap Hk /=.
Qed.

Lemma cells_repr_nil m : cells_repr m [] [].
Proof. reflexivity. Qed.

Lemma cells_repr_cons m c yi cs ys :
  cell_repr m c yi -> cells_repr m cs ys -> cells_repr m (c :: cs) (yi :: ys).
Proof. rewrite /cells_repr /cell_repr => -> ->. reflexivity. Qed.

(** Inserting a corresponding cell/item at the same position preserves the
    isomorphism (the splice's model side). *)
Lemma cells_repr_insert m cells items (k : nat) c yi :
  cells_repr m cells items -> cell_repr m c yi ->
  cells_repr m (take k cells ++ c :: drop k cells) (take k items ++ yi :: drop k items).
Proof.
  rewrite /cells_repr /cell_repr => -> ->.
  by rewrite fmap_app fmap_cons fmap_take fmap_drop.
Qed.

(** [cells_repr] does not depend on the resolution context [m] (it is a plain
    fmap equality), so threading a fresh model is a no-op. *)
Lemma cells_repr_m_irrel (m m' : list (YjsItem A)) cells items :
  cells_repr m cells items -> cells_repr m' cells items.
Proof. by rewrite /cells_repr. Qed.

Lemma cells_repr_app (m : list (YjsItem A)) cs1 cs2 ys1 ys2 :
  cells_repr m cs1 ys1 -> cells_repr m cs2 ys2 -> cells_repr m (cs1 ++ cs2) (ys1 ++ ys2).
Proof. rewrite /cells_repr => -> ->. by rewrite fmap_app. Qed.

Lemma cells_repr_take (m : list (YjsItem A)) cells items k :
  cells_repr m cells items -> cells_repr m (take k cells) (take k items).
Proof. rewrite /cells_repr => ->. by rewrite fmap_take. Qed.

Lemma cells_repr_drop (m : list (YjsItem A)) cells items k :
  cells_repr m cells items -> cells_repr m (drop k cells) (drop k items).
Proof. rewrite /cells_repr => ->. by rewrite fmap_drop. Qed.

(** Replacing a cell with another carrying the *same* model item ([cell_repr] to
    the same [yi]) preserves the isomorphism. [Text.Delete] flips a cell's
    [ic_deleted] without touching its [ic_item], so this keeps [cells_repr]. *)
Lemma cells_repr_update m cells items (k : nat) c yi c' :
  cells_repr m cells items -> cells !! k = Some c -> items !! k = Some yi -> cell_repr m c' yi ->
  cells_repr m (<[k := c']> cells) items.
Proof.
  rewrite /cells_repr /cell_repr => Hrepr Hck Hik Hc'.
  rewrite Hrepr list_fmap_insert -Hc'. symmetry. apply list_insert_id.
  rewrite -Hrepr. exact Hik.
Qed.

(* ----- the deletion layer: tombstoning a cell ---------------------------- *)

(** Visible count is additive over append. *)
Lemma num_visible_app (l1 l2 : list item_cell) :
  num_visible (l1 ++ l2) = (num_visible l1 + num_visible l2)%nat.
Proof. rewrite /num_visible List.filter_app length_app //. Qed.

(** Inserting a *visible* cell increments the visible count. Read by
    [Store.Integrate] / [Text.Insert], whose new items are always visible. *)
Lemma num_visible_insert_visible (cells : list item_cell) (k : nat) (c : item_cell) :
  ic_deleted c = false ->
  num_visible (take k cells ++ c :: drop k cells) = S (num_visible cells).
Proof.
  move=> Hc. rewrite /num_visible.
  rewrite List.filter_app /=. rewrite Hc /=. rewrite length_app /=.
  rewrite -{3}(take_drop k cells) List.filter_app length_app. lia.
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

(** The cell with its [ic_deleted] bit set (its model item [ic_item] unchanged). *)
Definition flip_cell (c : item_cell) : item_cell :=
  MkItemCell (ic_loc c) (ic_item c) true.

(** Flipping a cell's Deleted bit preserves [cell_repr]: [ic_item] is untouched. *)
Lemma cell_repr_flip (m : list (YjsItem A)) (c : item_cell) (yi : YjsItem A) :
  cell_repr m c yi -> cell_repr m (flip_cell c) yi.
Proof. rewrite /cell_repr /flip_cell /=. tauto. Qed.

(** Tombstoning a visible cell drops the visible count by one. *)
Lemma num_visible_flip (cells : list item_cell) (k : nat) (c : item_cell) :
  cells !! k = Some c -> ic_deleted c = false ->
  num_visible (<[k := flip_cell c]> cells) = pred (num_visible cells).
Proof.
  move=> Hk Hd.
  have Hins : <[k := flip_cell c]> cells = take k cells ++ flip_cell c :: drop (S k) cells
    by (apply insert_take_drop; apply lookup_lt_Some in Hk; exact Hk).
  rewrite Hins /num_visible List.filter_app /flip_cell /=.
  rewrite length_app.
  rewrite -{3}(take_drop_middle cells k c Hk).
  rewrite List.filter_app /=. rewrite Hd /=. rewrite length_app /=. lia.
Qed.

(** [is_ytext parent cells arr]: [parent] is a heap [YText] whose [start] heads
    the DLL [cells], which is isomorphic to the model [arr]. [len] counts the
    visible (non-deleted) cells ([num_visible]); a deletion tombstones a cell (set
    its [ic_deleted] bit) without removing it, so [cells] / [arr] keep every
    item. *)
Definition is_ytext (parent : loc) (cells : list item_cell) (arr : list (YjsItem A)) : iProp Σ :=
  ∃ (yt : yjs.yType.t) (tl : loc),
    "Hparent" ∷ parent ↦ yt ∗
    "Hdll" ∷ is_dll yt.(yjs.yType.start') tl null null cells ∗
    "%Hlen" ∷ ⌜yt.(yjs.yType.len') = W64 (num_visible cells)⌝ ∗
    "%Hrepr" ∷ ⌜cells_repr arr cells arr⌝.

(** The full data-structure invariant: a heap [YText] representing a *valid*
    model [arr] — DLL structure + isomorphism to a [YjsArrInvariant] list. *)
Definition is_valid_ytext (parent : loc) (arr : list (YjsItem A)) : iProp Σ :=
  ∃ cells,
    "Htext" ∷ is_ytext parent cells arr ∗
    "%Hinv" ∷ ⌜YjsArrInvariant arr⌝.

End item.
