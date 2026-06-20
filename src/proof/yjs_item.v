(** The heap representation of the [item] sequence and its model correspondence.

    Bottom to top:
    - [is_dll l last prev next cells]: the doubly-linked-list spine of [item]
      nodes (each carrying its [Item] struct and the two origin-id cells), with
      its split / join / accessor / insert lemmas. Adapted from the reference
      sorted-DLL proof (iasakura/perennial-sandbox, dll/list.go, [is_dlist_node]).
    - [resolve_*] / [cell_repr] / [cells_repr]: the cellwise isomorphism between
      the heap node list and a model [list (YjsItem A)] (origins resolved by id).
    - [is_ytext] / [is_valid_ytext]: a heap [yText] whose [start] heads such a
      DLL, isomorphic to a model list that — for [is_valid_ytext] — satisfies
      [YjsArrInvariant].

    This is the data-structure invariant the [Store.Integrate] / [Text.Insert]
    proofs ([yjs_store] / [yjs_text]) are stated against. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import yjs_core.
From New.proof Require Import yjs_common.

Section item.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.

(* ----- the doubly-linked spine (adapted from the reference DLL) ----------- *)

(** [is_dll l last prev next cells]: the DLL segment whose head node is [l] and
    whose last node is [last]; [prev] is the [left]-pointer of [l] and [next] is
    the [right]-pointer of [last]. Mirrors the reference [is_dlist_node], with
    each node carrying its [Item] struct and the two origin-id cells. *)
Fixpoint is_dll (l last prev next : loc) (cells : list item_cell) : iProp Σ :=
  match cells with
  | [] => ⌜l = next ∧ last = prev⌝
  | c :: rest =>
      "%Hloc" ∷ ⌜l = ic_loc c ∧ l ≠ null⌝ ∗
      "%Hprev" ∷ ⌜(ic_val c).(yjs.item.left') = prev⌝ ∗
      "Hval" ∷ ic_loc c ↦ ic_val c ∗
      "Holeft" ∷ is_origin_id (ic_val c).(yjs.item.originLeftId') (ic_oleft c) ∗
      "Horight" ∷ is_origin_id (ic_val c).(yjs.item.originRightId') (ic_oright c) ∗
      "Hrest" ∷ is_dll (ic_val c).(yjs.item.right') last l next rest
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
      iExists ml, mf. iFrame "H2 Hval Holeft Horight H1". done.
    + iIntros "(%ml & %mf & H1 & H2)". iNamed "H1".
      rewrite IH. iFrame "Hval Holeft Horight". iSplitR; [done|].
      iSplitR; [done|]. iExists ml, mf. iFrame.
Qed.

(** Splice a fresh node [newc] between two DLL segments whose boundary fields are
    already relinked to it ([cs1]'s last [right'] and [cs2]'s first [left'] point
    at [ic_loc newc], and [newc]'s [left']/[right'] at the two boundaries). Used to
    rejoin the document DLL after [Store.Integrate] inserts an item. *)
Lemma is_dll_insert_middle (cs1 cs2 : list item_cell) (newc : item_cell)
    (hd tl ml mr : loc) :
  ic_loc newc ≠ null ->
  (ic_val newc).(yjs.item.left') = ml ->
  (ic_val newc).(yjs.item.right') = mr ->
  is_dll hd ml null (ic_loc newc) cs1 ∗
  ic_loc newc ↦ ic_val newc ∗
  is_origin_id (ic_val newc).(yjs.item.originLeftId') (ic_oleft newc) ∗
  is_origin_id (ic_val newc).(yjs.item.originRightId') (ic_oright newc) ∗
  is_dll mr tl (ic_loc newc) null cs2
  ⊢ is_dll hd tl null null (cs1 ++ newc :: cs2).
Proof.
  move=> Hnn Hl Hr.
  iIntros "(Hdll1 & Hnode & Hol & Hor & Hdll2)".
  rewrite is_dll_app. iExists ml, (ic_loc newc). iFrame "Hdll1".
  simpl. rewrite Hr. iFrame "Hnode Hol Hor Hdll2".
  iPureIntro; split_and!; [reflexivity | exact Hnn | exact Hl].
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
    + iFrame "Hval Holeft Horight Hrest".
      iPureIntro; split_and!; [exact (proj1 Hloc) | exact (proj2 Hloc) | exact Hprev].
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
    "%Hcloc" ∷ ⌜ic_loc c = node_loc cells (Z.of_nat k)⌝ ∗
    "%Hcl" ∷ ⌜(ic_val c).(yjs.item.left') = node_loc cells (Z.of_nat k - 1)⌝ ∗
    "%Hcr" ∷ ⌜(ic_val c).(yjs.item.right') = node_loc cells (Z.of_nat k + 1)⌝ ∗
    "Hcval" ∷ ic_loc c ↦ ic_val c ∗
    "Hcol" ∷ is_origin_id (ic_val c).(yjs.item.originLeftId') (ic_oleft c) ∗
    "Hcor" ∷ is_origin_id (ic_val c).(yjs.item.originRightId') (ic_oright c) ∗
    "Hback" ∷ (ic_loc c ↦ ic_val c -∗ is_dll hd tl null null cells).
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
  iDestruct "Hrest" as "(%Hloc & %Hprev & Hval & #Hol & #Hor & Hrest2)".
  iDestruct (is_dll_lastptr with "Hpre") as "[%Hml Hpre]".
  have Hcl : c.(ic_val).(yjs.item.left') = node_loc cells (Z.of_nat k - 1).
  { rewrite Hprev Hml. exact Hpe. }
  have Hcloc : c.(ic_loc) = node_loc cells k by rewrite /node_loc decide_True; [rewrite Nat2Z.id Hk | lia].
  have Hd : suf !! 0%nat = cells !! (S k) by rewrite /suf lookup_drop Nat.add_0_r.
  have Hnl1 : node_loc cells (k+1) = default null (ic_loc <$> suf !! 0%nat).
  { rewrite /node_loc decide_True; last lia.
    have HZ : Z.to_nat (Z.of_nat k + 1) = S k by lia.
    by rewrite HZ Hd. }
  clearbody suf pre.
  destruct suf as [|c' rest].
  - iDestruct "Hrest2" as %[Hrn Htm].
    have Hcr : c.(ic_val).(yjs.item.right') = node_loc cells (k+1) by rewrite Hrn Hnl1.
    iSplitR; [iPureIntro; exact Hcloc|].
    iSplitR; [iPureIntro; exact Hcl|].
    iSplitR; [iPureIntro; exact Hcr|].
    iFrame "Hval Hol Hor".
    iIntros "Hval2". rewrite -Hsplit is_dll_app.
    iExists ml, mf. iFrame "Hpre". simpl. iFrame "Hval2 Hol Hor".
    iPureIntro; split_and!; [exact (proj1 Hloc) | exact (proj2 Hloc) | exact Hprev | exact Hrn | exact Htm].
  - iDestruct "Hrest2" as "(%Hloc' & %Hprev' & Hval' & #Hol' & #Hor' & Hrest2')".
    have Hcr : c.(ic_val).(yjs.item.right') = node_loc cells (k+1).
    { rewrite Hnl1 /=. exact (proj1 Hloc'). }
    iSplitR; [iPureIntro; exact Hcloc|].
    iSplitR; [iPureIntro; exact Hcl|].
    iSplitR; [iPureIntro; exact Hcr|].
    iFrame "Hval Hol Hor".
    iIntros "Hval2". rewrite -Hsplit is_dll_app.
    iExists ml, mf. iFrame "Hpre". simpl.
    iFrame "Hval2 Hol Hor Hval' Hol' Hor' Hrest2'".
    iPureIntro; split_and!; [exact (proj1 Hloc) | exact (proj2 Hloc) | exact Hprev | exact (proj1 Hloc') | exact (proj2 Hloc') | exact Hprev'].
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

(** A plain value accessor: borrow the node struct at index [k] from *any* DLL
    segment (arbitrary [prev]/[nxt]), with a wand to restore it. Unlike
    [is_dll_acc] it carries no [node_loc] facts, so it composes on sub-segments
    (used to read the loop-constant [right] node out of the suffix). *)
Lemma is_dll_lookup_acc (l lst prev nxt : loc) (cs : list item_cell) (k : nat) (c : item_cell) :
  cs !! k = Some c ->
  is_dll l lst prev nxt cs -∗
    c.(ic_loc) ↦ c.(ic_val) ∗ (c.(ic_loc) ↦ c.(ic_val) -∗ is_dll l lst prev nxt cs).
Proof.
  move=> Hk. iIntros "Hdll".
  pose proof (take_drop_middle cs k c Hk) as Hsplit.
  set (pre := take k cs) in Hsplit.
  set (suf := drop (S k) cs) in Hsplit.
  iEval (rewrite -Hsplit is_dll_app) in "Hdll".
  iDestruct "Hdll" as (ml mf) "[Hpre Hrest]".
  iDestruct "Hrest" as "(%Hloc & %Hprev & Hval & Hol & Hor & Hrest)".
  iFrame "Hval". iIntros "Hval2". rewrite -Hsplit is_dll_app.
  iExists ml, mf. iFrame "Hpre". simpl. iFrame "Hval2 Hol Hor Hrest".
  iPureIntro; split_and!; [exact (proj1 Hloc) | exact (proj2 Hloc) | exact Hprev].
Qed.

(* ----- isomorphism to a YjsArrInvariant model ---------------------------- *)

(** Resolve a left origin id against the model [m]: [None] is the [First]
    sentinel, otherwise the model item carrying that id. *)
Definition resolve_left (m : list (YjsItem A)) (oid : option yjs.id.t) : YjsPtr A :=
  match oid with
  | None => First
  | Some idv =>
      match list_find (λ it, item_id it = toYjsId idv) m with
      | Some (_, it) => itemPtr it
      | None => First
      end
  end.

(** Resolve a right origin id: [None] is the [Last] sentinel. *)
Definition resolve_right (m : list (YjsItem A)) (oid : option yjs.id.t) : YjsPtr A :=
  match oid with
  | None => Last
  | Some idv =>
      match list_find (λ it, item_id it = toYjsId idv) m with
      | Some (_, it) => itemPtr it
      | None => Last
      end
  end.

(** [cell_repr m c yi]: the model item [yi] is the one the heap cell [c]
    represents — same id and content, and [yi]'s origins carry exactly [c]'s
    heap origin ids (as model ids). Stating origins by id (rather than by
    resolution against [m]) is what the conflict scan needs to match
    [setfii_loop]'s id tests, and rules out a heap origin id that fails to
    resolve. ([m] is kept for uniformity with [cells_repr] / [resolve_*].)

    The last two conjuncts pin the heap flags / content length uniformly:
    every cell is Countable and non-Deleted ([flags' = W8 2], y-octo's
    ITEM_COUNTABLE) and one clock wide ([Len() = 1]). The Go model has no
    [Delete] in the goose build (it is [//go:build !goose]) and [newItem]
    always sets exactly [ITEM_COUNTABLE] over single-byte content, so this
    holds of every node ever integrated. [yText.findPos] reads [Deleted] /
    [Indexable] / [Len] off each node, so it needs these facts to walk by
    visible index.

    TODO: both pins are current-model simplifications and must relax as the
    verified model grows. Once deletions enter the goose build ([Delete] is
    presently [//go:build !goose]), [flags' = W8 2] weakens to "the Countable
    bit is set" (the Deleted bit may also be set, and [Indexable] / [findPos]
    must then skip deleted nodes); once items can span several clocks or split,
    [Len() = 1] goes ([content yi] becomes the whole run and [LastId]/[Len]
    reasoning generalises). [cell_repr] and its readers would then need these
    general forms. *)
Definition cell_repr (m : list (YjsItem A)) (c : item_cell) (yi : YjsItem A) : Prop :=
  item_id yi = toYjsId (ic_val c).(yjs.item.id') /\
  content yi = toContent (ic_val c).(yjs.item.content') /\
  origin_id (origin yi) = toYjsId <$> ic_oleft c /\
  origin_id (rightOrigin yi) = toYjsId <$> ic_oright c /\
  (ic_val c).(yjs.item.flags') = W8 2 /\
  length ((ic_val c).(yjs.item.content').(yjs.content.content')) = 1%nat.

(** [cells_repr m cells items]: the heap cell list represents the model item
    list cellwise (origins resolved against the full model [m]). This is the
    "isomorphism" between the heap node sequence and a [list (YjsItem A)]. *)
Inductive cells_repr (m : list (YjsItem A)) : list item_cell -> list (YjsItem A) -> Prop :=
  | cells_repr_nil : cells_repr m [] []
  | cells_repr_cons c yi cs ys :
      cell_repr m c yi ->
      cells_repr m cs ys ->
      cells_repr m (c :: cs) (yi :: ys).

(** The isomorphism is length-preserving and cellwise. *)
Lemma cells_repr_length m cells items :
  cells_repr m cells items -> length cells = length items.
Proof. by elim=> [|c yi cs ys _ _ IH] //=; rewrite IH. Qed.

Lemma cells_repr_lookup m cells items k c :
  cells_repr m cells items -> cells !! k = Some c ->
  ∃ yi, items !! k = Some yi ∧ cell_repr m c yi.
Proof.
  move=> H; elim: H k c => [|c0 yi cs ys Hc _ IH] k c.
  - by case: k.
  - case: k => [|k'] /=; first by move=> [<-]; exists yi.
    exact: IH.
Qed.

(** Inserting a corresponding cell/item at the same position preserves the
    isomorphism (the splice's model side). *)
Lemma cells_repr_insert m cells items (k : nat) c yi :
  cells_repr m cells items -> cell_repr m c yi ->
  cells_repr m (take k cells ++ c :: drop k cells) (take k items ++ yi :: drop k items).
Proof.
  move=> H Hc; elim: H k => [|c0 yi0 cs ys Hc0 Hrec IH] k.
  - rewrite !take_nil !drop_nil /=. apply: cells_repr_cons; [exact Hc | exact: cells_repr_nil].
  - case: k => [|k'] /=.
    + apply: cells_repr_cons; first exact Hc.
      apply: cells_repr_cons; [exact Hc0 | exact Hrec].
    + apply: cells_repr_cons; [exact Hc0 | exact: IH].
Qed.

(** [cell_repr] constrains only id / content / origin-ids — it ignores both the
    resolution context [m] and the cell's [left']/[right'] heap fields. The splice
    relinks boundary nodes' [left']/[right'] and threads a fresh resolution model,
    so these congruences keep the isomorphism intact across the surgery. *)
Lemma cells_repr_m_irrel (m m' : list (YjsItem A)) cells items :
  cells_repr m cells items -> cells_repr m' cells items.
Proof.
  elim=> [|c yi cs ys Hc _ IH]; [apply: cells_repr_nil | apply: cells_repr_cons; [exact Hc | exact IH]].
Qed.

Lemma cells_repr_app (m : list (YjsItem A)) cs1 cs2 ys1 ys2 :
  cells_repr m cs1 ys1 -> cells_repr m cs2 ys2 -> cells_repr m (cs1 ++ cs2) (ys1 ++ ys2).
Proof.
  move=> H1 H2. elim: H1 => [|c yi cs ys Hc _ IH] //=.
  apply: cells_repr_cons; [exact Hc | exact IH].
Qed.

Lemma cells_repr_take (m : list (YjsItem A)) cells items k :
  cells_repr m cells items -> cells_repr m (take k cells) (take k items).
Proof.
  move=> H. elim: H k => [|c yi cs ys Hc _ IH] k.
  - rewrite !take_nil. apply: cells_repr_nil.
  - case: k => [|k'] /=; [apply: cells_repr_nil | apply: cells_repr_cons; [exact Hc | exact: IH]].
Qed.

Lemma cells_repr_drop (m : list (YjsItem A)) cells items k :
  cells_repr m cells items -> cells_repr m (drop k cells) (drop k items).
Proof.
  move=> H. elim: H k => [|c yi cs ys Hc Htl IH] k.
  - rewrite !drop_nil. apply: cells_repr_nil.
  - case: k => [|k'] /=; [apply: cells_repr_cons; [exact Hc | exact Htl] | exact: IH].
Qed.

Lemma cell_repr_val_irrel (m : list (YjsItem A)) (c : item_cell) (v' : yjs.item.t) yi :
  cell_repr m c yi ->
  (ic_val c).(yjs.item.id') = v'.(yjs.item.id') ->
  (ic_val c).(yjs.item.content') = v'.(yjs.item.content') ->
  (ic_val c).(yjs.item.flags') = v'.(yjs.item.flags') ->
  cell_repr m (MkItemCell (ic_loc c) v' (ic_oleft c) (ic_oright c)) yi.
Proof.
  rewrite /cell_repr /=. move=> [Hid [Hcon [Hol [Hor [Hfl Hcl]]]]] Hid' Hcon' Hfl'.
  split_and!;
    [rewrite Hid Hid' // | rewrite Hcon Hcon' // | exact Hol | exact Hor
    | rewrite -Hfl' // | rewrite -Hcon' // ].
Qed.

(** [is_ytext parent cells arr]: [parent] is a heap [YText] whose [start] heads
    the DLL [cells], which is isomorphic to the model [arr]. (Phase-2: every item
    is countable / non-deleted, so [len] = number of nodes.) *)
Definition is_ytext (parent : loc) (cells : list item_cell) (arr : list (YjsItem A)) : iProp Σ :=
  ∃ (yt : yjs.yText.t) (tl : loc),
    "Hparent" ∷ parent ↦ yt ∗
    "Hdll" ∷ is_dll yt.(yjs.yText.start') tl null null cells ∗
    "%Hlen" ∷ ⌜yt.(yjs.yText.len') = W64 (length cells)⌝ ∗
    "%Hrepr" ∷ ⌜cells_repr arr cells arr⌝.

(** The full data-structure invariant: a heap [YText] representing a *valid*
    model [arr] — DLL structure + isomorphism to a [YjsArrInvariant] list. *)
Definition is_valid_ytext (parent : loc) (arr : list (YjsItem A)) : iProp Σ :=
  ∃ cells,
    "Htext" ∷ is_ytext parent cells arr ∗
    "%Hinv" ∷ ⌜YjsArrInvariant arr⌝.

End item.
