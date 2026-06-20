  (** The cert-yjs heap representation of a [YText] and the invariants for
    verifying [Store.Integrate].

    Design (two combined invariants, per the plan):

    1. DATA-STRUCTURE invariant.
       - [is_dll]: the doubly-linked-list structure invariant, adapted from the
         reference sorted-DLL proof (iasakura/perennial-sandbox, dll/list.go,
         [is_dlist_node]). Each node is an [Item] with [left]=prev / [right]=next
         pointers; a segment is described by its head [l], last node [last], the
         prev-pointer of the head [prev] and the next-pointer of the last [next].
       - [is_ytext] / [is_valid_ytext]: a heap [YText] whose [start] heads such a
         DLL, where the node list is ISOMORPHIC to a [list (YjsItem A)] that
         satisfies [YjsArrInvariant] (origins resolved by id via [cell_repr]).
         This combines the DLL structure invariant with the order/origin
         well-formedness of the pure model, as requested.

    2. LOOP invariant ([integrate_loop_inv]) for [Integrate]'s conflict scan:
       it couples the heap loop state (the [conflict]/[left] pointers and the
       [itemsBeforeOrigin]/[conflictingItems] slices) to the pure set-based loop
       [setfii_loop] of iris-yjs (via [Couple]), so the scan refines
       [setfindIntegratedIndex].

    Phase-2 simplification: content is a 1-char string ([go_string]); every item
    is countable and non-deleted, so [YText.len] = number of nodes. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import yjs_core.

Section invariant.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

#[global] Instance : IsPkgInit (iProp Σ) yjs := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) yjs := build_get_is_pkg_init_wf.

Collection W := sem + package_sem.
Set Default Proof Using "W".

(** Document content type. *)
Notation A := go_string.

(* ===== abstraction of scalar fields ====================================== *)

(** Heap id (two [w64]s) to model id (two [nat]s). *)
Definition toYjsId (i : yjs.id.t) : YjsId :=
  MkYjsId (uint.nat i.(yjs.id.clientId')) (uint.nat i.(yjs.id.clock')).

Definition toContent (c : yjs.content.t) : A := c.(yjs.content.content').

(** One node of the heap DLL: its location, struct value, and the optional
    origin ids it points at (resolved out of the [originLeftId]/[originRightId]
    pointers). *)
Record item_cell := MkItemCell {
  ic_loc : loc;
  ic_val : yjs.item.t;
  ic_oleft : option yjs.id.t;
  ic_oright : option yjs.id.t;
}.

(** The loc of the node at index [k] of [cells] ([null] outside [0, len)).
    Used to place the heap [conflict] / [left] pointers within the DLL. *)
Definition node_loc (cells : list item_cell) (k : Z) : loc :=
  if decide (0 <= k)%Z then default null (ic_loc <$> cells !! Z.to_nat k) else null.

(** An origin pointer is either null (no origin) or a read-only [Id] cell.
    Origins are immutable once integrated, hence persistent ([↦□]). *)
Definition is_origin_id (p : loc) (oid : option yjs.id.t) : iProp Σ :=
  match oid with
  | None => ⌜p = null⌝
  | Some idv => ⌜p ≠ null⌝ ∗ p ↦□ idv
  end.

(** Origins are read-only, hence the predicate is persistent. *)
Global Instance is_origin_id_persistent p oid : Persistent (is_origin_id p oid).
Proof. rewrite /is_origin_id. by destruct oid; apply _. Qed.

(* ===== (1) DATA-STRUCTURE invariant ====================================== *)

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

(* ===== (2) LOOP invariant for Integrate ================================== *)


(** A heap id-slice abstracts to a [gset YjsId]: its elements, mapped to model
    ids, are exactly [gs]. The Go set ops are [containsId] / [append] / reset to
    [[]]; [list_to_set] makes membership (not order/duplicates) the observable,
    matching the pure [gset] with [∪] / [∈]. *)
Definition is_id_set (s : slice.t) (gs : gset YjsId) : iProp Σ :=
  ∃ (vs : list yjs.id.t),
    "Hsl" ∷ s ↦* vs ∗
    "Hcap" ∷ own_slice_cap yjs.id.t s (DfracOwn 1) ∗
    "%Hset" ∷ ⌜list_to_set (toYjsId <$> vs) = gs⌝.

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

(** A heap item pointer is null or owns a node; [oid_of] is its model id. *)
Definition oid_of (ov : option yjs.item.t) : option YjsId :=
  (λ v, toYjsId v.(yjs.item.id')) <$> ov.

Definition item_or_null (p : loc) (ov : option yjs.item.t) (dq : dfrac) : iProp Σ :=
  match ov with
  | None => ⌜p = null⌝
  | Some v => ⌜p ≠ null⌝ ∗ p ↦{dq} v
  end.

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

(** [containsId] decides membership of the id slice as a [gset] (via [toYjsId]). *)
Lemma wp_containsId (s : slice.t) (vs : list yjs.id.t) (id : yjs.id.t) (dq : dfrac) :
  {{{ is_pkg_init yjs ∗ s ↦*{dq} vs }}}
    @! yjs.containsId #s #id
  {{{ RET #(bool_decide (toYjsId id ∈ (list_to_set (toYjsId <$> vs) : gset YjsId)));
      s ↦*{dq} vs }}}.
Proof.
  wp_start as "Hs". wp_auto.
  iAssert (∃ (i : w64) (xv : yjs.id.t),
    "Hi" ∷ i_ptr ↦ i ∗ "Hx" ∷ x_ptr ↦ xv ∗ "Hs" ∷ s ↦*{dq} vs ∗
    "%Hib" ∷ ⌜(0 ≤ uint.Z i ≤ Z.of_nat (length vs))%Z⌝ ∗
    "%Hnf" ∷ ⌜toYjsId id ∉ (list_to_set (toYjsId <$> take (uint.nat i) vs) : gset YjsId)⌝)%I
    with "[i x Hs]" as "IH".
  { iExists (W64 0), _. iFrame. iPureIntro.
    replace (uint.nat (W64 0)) with 0%nat by word.
    rewrite take_0 /=. split_and!; [word | word | set_solver]. }
  wp_for "IH".
  iDestruct (own_slice_len with "Hs") as %[Hslen Hslen0].
  destruct (bool_decide (sint.Z i < sint.Z s.(slice.len))) eqn:Hlt.
  - apply bool_decide_eq_true_1 in Hlt.
    have Hilt : (uint.nat i < length vs)%nat by word.
    wp_auto. rewrite decide_True; last by word.
    destruct (vs !! uint.nat i) as [v|] eqn:Hv;
      last by (apply lookup_lt_is_Some_2 in Hilt; rewrite Hv in Hilt; by destruct Hilt).
    iDestruct (own_slice_elem_acc (sint.Z i) v s dq vs with "Hs") as "[Hel Hrest]".
    { word. }
    { replace (Z.to_nat (sint.Z i)) with (uint.nat i) by word. exact Hv. }
    wp_auto. wp_method_call; wp_call; wp_auto. wp_apply (wp_Id__Equal v id).
    have Hv' : vs !! sint.nat i = Some v.
    { replace (sint.nat i) with (uint.nat i) by word. exact Hv. }
    iDestruct ("Hrest" $! v with "Hel") as "Hs".
    iEval (rewrite (list_insert_id _ _ _ Hv')) in "Hs".
    wp_if_destruct.
    + wp_for_post.
      have Hin : toYjsId id ∈ (list_to_set (toYjsId <$> vs) : gset YjsId).
      { rewrite elem_of_list_to_set.
        apply (list_elem_of_fmap_2' toYjsId vs v);
          [ by eapply list_elem_of_lookup_2 | by rewrite e ]. }
      iEval (rewrite (bool_decide_eq_true_2 _ Hin)) in "HΦ". iApply "HΦ". iFrame.
    + wp_for_post.
      iFrame "HΦ id". iExists (word.add i (W64 1)), v. iFrame.
      iPureIntro. split.
      * word.
      * replace (uint.nat (word.add i (W64 1))) with (S (uint.nat i)) by word.
        rewrite (take_S_r _ _ v); [| exact Hv].
        rewrite fmap_app list_to_set_app.
        apply not_elem_of_union. split; [exact Hnf | set_solver].
  - apply bool_decide_eq_false in Hlt. wp_auto.
    have Hge : (length vs <= uint.nat i)%nat by word.
    rewrite (take_ge _ _ Hge) in Hnf.
    iEval (rewrite (bool_decide_eq_false_2 _ Hnf)) in "HΦ".
    iApply "HΦ". iFrame.
Qed.

(* ----- findById: locate a node by id in the DLL ------------------------- *)

(** The cell predicate [findById] decides: a cell whose model id is [toYjsId idv].
    [findById] returns the first matching node's location, or [null]. *)
Definition cell_has_id (idv : yjs.id.t) (c : item_cell) : Prop :=
  toYjsId (ic_val c).(yjs.item.id') = toYjsId idv.

#[local] Instance cell_has_id_dec idv c : Decision (cell_has_id idv c).
Proof. rewrite /cell_has_id. apply _. Defined.

(** Result location of [findById] over a cell list: first match, else [null]. *)
Definition findById_res (cells : list item_cell) (idv : yjs.id.t) : loc :=
  match list_find (cell_has_id idv) cells with
  | Some (_, c) => ic_loc c
  | None => null
  end.

(** Under the isomorphism, the heap [cell_has_id] search and the model id search
    agree (same index, corresponding cell/item). *)
Lemma list_find_cells_repr m cells items (idv : yjs.id.t) :
  cells_repr m cells items ->
  match list_find (cell_has_id idv) cells,
        list_find (fun it => item_id it = toYjsId idv) items with
  | Some (k1, c), Some (k2, yi) => k1 = k2 /\ cell_repr m c yi
  | None, None => True
  | _, _ => False
  end.
Proof.
  elim=> [|c0 yi0 cs ys Hc Hcs IH] //=.
  have [Hid _] := Hc.
  have Hiff : cell_has_id idv c0 <-> item_id yi0 = toYjsId idv by rewrite /cell_has_id Hid.
  case: (decide (cell_has_id idv c0)) => Hd1; case: (decide (item_id yi0 = toYjsId idv)) => Hd2 /=.
  - split; [done | exact Hc].
  - exfalso; apply Hd2; apply/Hiff; exact: Hd1.
  - exfalso; apply Hd1; apply/Hiff; exact: Hd2.
  - move: IH; case: (list_find (cell_has_id idv) cs) => [[k1 c]|];
      case: (list_find (fun it => item_id it = toYjsId idv) ys) => [[k2 yi']|] //=.
    by move=> [-> ?].
Qed.

(** Repair correspondence: [findById] returns the node at the model index of the
    item with the given id (or [null] when absent). *)
Lemma findById_res_correspond cells arr (idv : yjs.id.t) (k : nat) (yi : YjsItem A) :
  cells_repr arr cells arr ->
  list_find (fun it => item_id it = toYjsId idv) arr = Some (k, yi) ->
  findById_res cells idv = node_loc cells (Z.of_nat k).
Proof.
  move=> Hrepr Hfind.
  have Hmatch := list_find_cells_repr arr cells arr idv Hrepr.
  rewrite Hfind in Hmatch.
  move: Hmatch. case Hcf: (list_find (cell_has_id idv) cells) => [[k1 c]|]; last done.
  move=> [<- Hcr].
  rewrite /findById_res Hcf.
  have /list_find_Some [Hck _] := Hcf.
  rewrite /node_loc decide_True; last lia.
  by rewrite Nat2Z.id Hck.
Qed.

Lemma findById_res_none cells arr (idv : yjs.id.t) :
  cells_repr arr cells arr ->
  list_find (fun it => item_id it = toYjsId idv) arr = None ->
  findById_res cells idv = null.
Proof.
  move=> Hrepr Hfind. rewrite /findById_res.
  have Hmatch := list_find_cells_repr arr cells arr idv Hrepr.
  rewrite Hfind in Hmatch.
  by case: (list_find (cell_has_id idv) cells) Hmatch => [[k c]|].
Qed.

(** What [findById] yields in the repair step (left origin): the resolved
    left-origin pointer equals the node at the model index [findLeftIdx]. The
    [None] origin maps to [null = node_loc cells (-1)]. *)
Lemma findById_left_node_loc cells arr (oid : option yjs.id.t) (idx : Z) :
  cells_repr arr cells arr ->
  findLeftIdx (toYjsId <$> oid) arr = Some idx ->
  match oid with Some idv => findById_res cells idv | None => null end = node_loc cells idx.
Proof.
  move=> Hrepr. case: oid => [idv|] /=.
  - rewrite /findLeftIdx.
    case Hlf: (list_find (fun item => item_id item = toYjsId idv) arr) => [[k yi]|] //=.
    move=> [<-]. exact: (findById_res_correspond cells arr idv k yi Hrepr Hlf).
  - move=> [<-]. rewrite /node_loc. by case: (decide (0 <= -1)%Z) => H; [exfalso; lia|].
Qed.

(** Same for the right origin: [None] maps to [null = node_loc cells (length)]. *)
Lemma findById_right_node_loc cells arr (oid : option yjs.id.t) (idx : Z) :
  cells_repr arr cells arr ->
  findRightIdx (toYjsId <$> oid) arr = Some idx ->
  match oid with Some idv => findById_res cells idv | None => null end = node_loc cells idx.
Proof.
  move=> Hrepr. case: oid => [idv|] /=.
  - rewrite /findRightIdx.
    case Hlf: (list_find (fun item => item_id item = toYjsId idv) arr) => [[k yi]|] //=.
    move=> [<-]. exact: (findById_res_correspond cells arr idv k yi Hrepr Hlf).
  - move=> [<-]. rewrite /node_loc decide_True; last lia.
    have Hlen := cells_repr_length _ _ _ Hrepr.
    rewrite Nat2Z.id (lookup_ge_None_2 cells (length arr)) //. lia.
Qed.

Lemma wp_findById (parent : loc) (cells : list item_cell) (arr : list (YjsItem A))
    (idv : yjs.id.t) :
  {{{ is_pkg_init yjs ∗ is_ytext parent cells arr }}}
    @! yjs.findById #parent #idv
  {{{ RET #(findById_res cells idv); is_ytext parent cells arr }}}.
Proof.
  wp_start as "Ht". iNamed "Ht". wp_auto.
  iAssert (∃ (cur ml : loc) (scanned remaining : list item_cell),
    "Hcur" ∷ cur_ptr ↦ cur ∗
    "Hpre" ∷ is_dll yt.(yjs.yText.start') ml null cur scanned ∗
    "Hrem" ∷ is_dll cur tl ml null remaining ∗
    "%Hsplit" ∷ ⌜cells = scanned ++ remaining⌝ ∗
    "%Hnone" ∷ ⌜list_find (cell_has_id idv) scanned = None⌝)%I
    with "[cur Hdll]" as "IH".
  { iExists yt.(yjs.yText.start'), null, [], cells. iFrame "cur Hdll". simpl. iPureIntro.
    split_and!; done. }
  wp_for "IH".
  case_bool_decide as Hcn; simpl.
  - rewrite decide_False //. rewrite decide_True //. wp_auto.
    subst cur. iDestruct (is_dll_null_nil with "Hrem") as %->.
    rewrite app_nil_r in Hsplit. subst cells.
    have Hres : findById_res scanned idv = null by (rewrite /findById_res Hnone //).
    iEval (rewrite Hres) in "HΦ". iApply "HΦ". iExists yt, ml. iFrame "Hparent Hpre". done.
  - rewrite decide_True //.
    destruct remaining as [|c rest];
      first by (iDestruct "Hrem" as %[Hc _]; rewrite Hc in Hcn; done).
    iNamed "Hrem". destruct Hloc as [Hcureq Hcurnn]. subst cur.
    wp_auto. wp_method_call; wp_call; wp_auto.
    wp_apply (wp_Id__Equal (ic_val c).(yjs.item.id') idv).
    destruct (bool_decide (toYjsId c.(ic_val).(yjs.item.id') = toYjsId idv)) eqn:Heq.
    + apply bool_decide_eq_true_1 in Heq. wp_auto. wp_for_post.
      have Hres : findById_res cells idv = c.(ic_loc).
      { rewrite /findById_res Hsplit (list_find_app_r _ _ _ Hnone) /=.
        destruct (decide (cell_has_id idv c)) as [Hd|Hd]; [done | exfalso; apply Hd; exact Heq]. }
      iEval (rewrite Hres) in "HΦ". iApply "HΦ".
      iExists yt, tl. iFrame "Hparent".
      iSplitL "Hpre Hval Holeft Horight Hrest".
      * rewrite Hsplit. iApply is_dll_app. iExists ml, (c.(ic_loc)). iFrame "Hpre".
        simpl. iFrame "Hval Holeft Horight Hrest".
        iPureIntro; split_and!; [done | exact Hcurnn | exact Hprev].
      * iPureIntro; split; [exact Hlen | exact Hrepr].
    + apply bool_decide_eq_false in Heq. wp_auto. wp_for_post.
      iFrame "HΦ id Hparent".
      iExists (c.(ic_val).(yjs.item.right')), (c.(ic_loc)), (scanned ++ [c]), rest.
      iFrame "Hcur".
      iSplitL "Hpre Hval Holeft Horight".
      * iApply is_dll_app. iExists ml, (c.(ic_loc)). iFrame "Hpre".
        simpl. iFrame "Hval Holeft Horight".
        iPureIntro; split_and!; [done | exact Hcurnn | exact Hprev | done | done].
      * iFrame "Hrest". iPureIntro. split.
        { by rewrite Hsplit -app_assoc. }
        apply list_find_app_None. split; [exact Hnone|].
        simpl. destruct (decide (cell_has_id idv c)) as [Hc|Hc];
          [exfalso; exact (Heq Hc) | done].
Qed.

(** Comparing a node pointer with itself is always [true] (it has its own id). *)
Lemma wp_itemPtrEqual_self (p : loc) (v : yjs.item.t) (dq : dfrac) :
  {{{ is_pkg_init yjs ∗ p ↦{dq} v }}}
    @! yjs.itemPtrEqual #p #p
  {{{ RET #true; p ↦{dq} v }}}.
Proof.
  wp_start as "Hp". iDestruct (typed_pointsto_not_null with "Hp") as %Hnn. wp_auto.
  rewrite (bool_decide_eq_false_2 (p = null) Hnn). wp_auto.
  rewrite (bool_decide_eq_false_2 (p = null) Hnn). wp_auto.
  rewrite (bool_decide_eq_false_2 (p = null) Hnn). wp_auto.
  wp_method_call; wp_call; wp_auto.
  wp_apply (wp_Id__Equal v.(yjs.item.id') v.(yjs.item.id')).
  rewrite bool_decide_eq_true_2; last reflexivity.
  iApply "HΦ". iFrame "Hp".
Qed.

(** Comparing two DLL nodes by [itemPtrEqual] decides index equality: under the
    id-uniqueness of [arr], two nodes have the same id exactly when they are the
    same node. [a]/[b] range over [[0, length cells]] (the [length] sentinel is
    the [null] / [Last] boundary), with [a <= b]. Used for the [conflict == right]
    break test and the entry [left.right == right] test. *)
Lemma wp_itemPtrEqual_node (parent : loc) (cells : list item_cell) (arr : list (YjsItem A))
    (a b : Z) :
  YjsArrInvariant arr ->
  (0 <= a)%Z -> (a <= b)%Z -> (b <= Z.of_nat (length cells))%Z ->
  {{{ is_pkg_init yjs ∗ is_ytext parent cells arr }}}
    @! yjs.itemPtrEqual #(node_loc cells a) #(node_loc cells b)
  {{{ RET #(bool_decide (a = b)); is_ytext parent cells arr }}}.
Proof.
  move=> Harr Ha0 Hab Hblen.
  iIntros (Φ) "[#Hpkg Ht] HΦ". iNamed "Ht".
  have Hlen_eq : length cells = length arr := cells_repr_length _ _ _ Hrepr.
  destruct (decide (a = b)) as [Heq | Hne].
  - subst b. rewrite bool_decide_eq_true_2; last reflexivity.
    destruct (decide (a < Z.of_nat (length cells))%Z) as [Halt | Hage].
    + have Ha_lt : (Z.to_nat a < length cells)%nat by lia.
      destruct (cells !! Z.to_nat a) as [ca|] eqn:Hca; last by (apply lookup_ge_None in Hca; lia).
      have Hpa : node_loc cells a = ic_loc ca by rewrite /node_loc decide_True; [rewrite Hca | lia].
      iDestruct (is_dll_lookup_acc _ _ _ _ _ _ _ Hca with "Hdll") as "[Hval Hback]".
      rewrite Hpa. wp_apply (wp_itemPtrEqual_self (ic_loc ca) (ic_val ca) (DfracOwn 1) with "[$Hpkg $Hval]").
      iIntros "Hval". iApply "HΦ". iExists yt, tl. iFrame "Hparent".
      iDestruct ("Hback" with "Hval") as "Hdll". iFrame "Hdll". done.
    + have Hpa : node_loc cells a = null.
      { rewrite /node_loc. case_decide; [|done]. rewrite lookup_ge_None_2; [done | lia]. }
      rewrite Hpa. wp_apply (wp_itemPtrEqual null null None None (DfracOwn 1) (DfracOwn 1) with "[$Hpkg]").
      { rewrite /item_or_null. iSplit; done. }
      rewrite (bool_decide_eq_true_2 (oid_of None = oid_of None)); last reflexivity.
      iIntros "_". iApply "HΦ". iExists yt, tl. iFrame "Hparent Hdll". done.
  - rewrite bool_decide_eq_false_2; last exact Hne.
    have Hab' : (a < b)%Z by lia.
    destruct (decide (b < Z.of_nat (length cells))%Z) as [Hblt | Hbge].
    + (* a < b < length: borrow both nodes, distinct ids by uniqueness *)
      have Ha_lt : (Z.to_nat a < length cells)%nat by lia.
      have Hb_lt : (Z.to_nat b < length cells)%nat by lia.
      destruct (cells !! Z.to_nat a) as [ca|] eqn:Hca; last by (apply lookup_ge_None in Hca; lia).
      destruct (cells !! Z.to_nat b) as [cb|] eqn:Hcb; last by (apply lookup_ge_None in Hcb; lia).
      have Hpa : node_loc cells a = ic_loc ca by rewrite /node_loc decide_True; [rewrite Hca | lia].
      have Hpb : node_loc cells b = ic_loc cb by rewrite /node_loc decide_True; [rewrite Hcb | lia].
      pose proof (take_drop_middle cells (Z.to_nat a) ca Hca) as Hsa.
      set (pre := take (Z.to_nat a) cells) in Hsa.
      set (suf := drop (S (Z.to_nat a)) cells) in Hsa.
      iEval (rewrite -Hsa is_dll_app) in "Hdll".
      iDestruct "Hdll" as (ml mf) "[Hpre Hrest]".
      iDestruct "Hrest" as "(%Hloca & %Hpreva & Hvala & #Hola & #Hora & Htail)".
      have Hsuf_b : suf !! (Z.to_nat b - S (Z.to_nat a))%nat = Some cb.
      { rewrite /suf lookup_drop. rewrite -Hcb. f_equal. lia. }
      iDestruct (is_dll_lookup_acc _ _ _ _ _ _ _ Hsuf_b with "Htail") as "[Hvalb Hbackb]".
      have Hids_unique := yai_unique _ Harr.
      have [ya [Hya Hcra]] := cells_repr_lookup _ _ _ _ _ Hrepr Hca.
      have [yb [Hyb Hcrb]] := cells_repr_lookup _ _ _ _ _ Hrepr Hcb.
      have Hlt : (Z.to_nat a < Z.to_nat b)%nat by lia.
      have Hid_ne : item_id ya ≠ item_id yb
        by apply: (invariant_yjsarray_idx.ss_lookup_lt arr (Z.to_nat a) (Z.to_nat b) ya yb Hids_unique Hya Hyb Hlt).
      have Hoid_ne : oid_of (Some (ic_val ca)) ≠ oid_of (Some (ic_val cb)).
      { rewrite /oid_of /= => Heqsome. apply Hid_ne.
        have Heqid := Some_inj _ _ Heqsome. by rewrite (proj1 Hcra) (proj1 Hcrb) Heqid. }
      rewrite Hpa Hpb.
      iDestruct (typed_pointsto_not_null with "Hvalb") as %Hnnb.
      wp_apply (wp_itemPtrEqual (ic_loc ca) (ic_loc cb) (Some (ic_val ca)) (Some (ic_val cb)) (DfracOwn 1) (DfracOwn 1) with "[$Hpkg Hvala Hvalb]").
      { rewrite /item_or_null. iFrame "Hvala Hvalb". iSplit; iPureIntro.
        - rewrite -(proj1 Hloca). exact (proj2 Hloca).
        - exact Hnnb. }
      rewrite (bool_decide_eq_false_2 (oid_of (Some (ic_val ca)) = oid_of (Some (ic_val cb))) Hoid_ne).
      iIntros "[Ha Hb]". rewrite /item_or_null.
      iDestruct "Ha" as "[_ Hvala]". iDestruct "Hb" as "[_ Hvalb]".
      iDestruct ("Hbackb" with "Hvalb") as "Htail".
      iApply "HΦ". iExists yt, tl. iFrame "Hparent".
      iSplitL; last (iPureIntro; split; [exact Hlen | exact Hrepr]).
      rewrite -Hsa is_dll_app. iExists ml, mf. iFrame "Hpre".
      simpl. iFrame "Hvala Hola Hora Htail".
      iPureIntro; split_and!; [exact (proj1 Hloca) | exact (proj2 Hloca) | exact Hpreva].
    + (* b = length: [b] is null, [a] a node *)
      have Ha_lt : (Z.to_nat a < length cells)%nat by lia.
      destruct (cells !! Z.to_nat a) as [ca|] eqn:Hca; last by (apply lookup_ge_None in Hca; lia).
      have Hpa : node_loc cells a = ic_loc ca by rewrite /node_loc decide_True; [rewrite Hca | lia].
      have Hpb : node_loc cells b = null.
      { rewrite /node_loc. case_decide; [|done]. rewrite lookup_ge_None_2; [done | lia]. }
      iDestruct (is_dll_lookup_acc _ _ _ _ _ _ _ Hca with "Hdll") as "[Hval Hback]".
      iDestruct (typed_pointsto_not_null with "Hval") as %Hnna.
      rewrite Hpa Hpb.
      wp_apply (wp_itemPtrEqual (ic_loc ca) null (Some (ic_val ca)) None (DfracOwn 1) (DfracOwn 1) with "[$Hpkg Hval]").
      { rewrite /item_or_null. iSplitL "Hval"; [iFrame "Hval"; iPureIntro; exact Hnna | done]. }
      rewrite (bool_decide_eq_false_2 (oid_of (Some (ic_val ca)) = oid_of None)); last done.
      iIntros "[Ha _]". rewrite /item_or_null. iDestruct "Ha" as "[_ Hval]".
      iApply "HΦ". iExists yt, tl. iFrame "Hparent".
      iDestruct ("Hback" with "Hval") as "Hdll". iFrame "Hdll". done.
Qed.

(** Small-context set rewrites for the scan accumulators. After a Go [append] of
    the conflict id, an id slice abstracts to [X ∪ ({[a]} ∪ ∅)] (the trailing [∅]
    is [list_to_set []] from the singleton tail); these relate that to the
    [setfii_loop] accumulator form [{[a]} ∪ X]. Proving them as standalone lemmas
    keeps [set_solver] on a tiny context — calling [set_solver] inside
    [wp_scanConflicts] instead does [set_unfold in *] over the whole proof state
    (including the [list_to_set] slice hypotheses) and is prohibitively slow. *)
Lemma gset_union_singleton_swap (X : gset YjsId) (a : YjsId) :
  (X ∪ ({[a]} ∪ ∅) : gset YjsId) = {[a]} ∪ X.
Proof. set_solver. Qed.

Lemma gset_elem_union_singleton_swap (X : gset YjsId) (a b : YjsId) :
  b ∈ ({[a]} ∪ X) -> b ∈ (X ∪ ({[a]} ∪ ∅) : gset YjsId).
Proof. set_solver. Qed.

Lemma gset_not_elem_union_singleton_swap (X : gset YjsId) (a b : YjsId) :
  b ∉ ({[a]} ∪ X) -> b ∉ (X ∪ ({[a]} ∪ ∅) : gset YjsId).
Proof. set_solver. Qed.

(** Loop invariant for the conflict scan in [Integrate]. The heap loop refines
    the pure set-based loop [setfii_loop] *directly*: the heap slices
    [itemsBeforeOrigin] / [conflictingItems] literally carry the [setfii_loop]
    accumulators [idsBeforeOrigin] / [conflictIds] (as [gset]s), and the loop's
    progress is tracked by a fuel equation — the remaining run from the current
    state equals the fixed overall result [loopResult]. (The
    [setfii_loop ↔ fii_loop] equivalence is a separate, already-proved fact used
    only to inherit [YjsArrInvariant].)

    - [conflict_l] (Go [conflict]) sits at the cursor node, index [leftIdx+offset]
      — the next item to scan ([other = arr !! (leftIdx + offset)]);
    - [left_l] (Go [left]) is the anchor: the node just left of the insert point,
      index [destIdx - 1] (so [item] is spliced after it);
    - [right_l] (Go [right]) is loop-constant at index [rightIdx] (the right
      origin / [Last]); the [conflict == right] break is [leftIdx+offset = rightIdx];
    - [Hloop]: from the current accumulators, the remaining
      [Z.to_nat (rightIdx - leftIdx) - offset] steps of [setfii_loop] still
      compute [loopResult]. With [Hbound] / [Hdest] this makes the Go
      [for conflict ≠ nil] test (with the [== right] break) consume exactly the
      loop's fuel.
    [is_fresh_item_raw] and the [parent.len] field are loop-constant, framed outside. *)
Definition integrate_loop_inv
    (parent : loc) (cells : list item_cell) (arr : list (YjsItem A))
    (leftIdx rightIdx : Z) (originLeftId originRightId : option YjsId) (newItemId : YjsId)
    (loopResult : option Z)
    (conflict_l left_l right_l idsBeforeOrigin_l conflictIds_l : loc)
    (offset : nat) (idsBeforeOrigin conflictIds : gset YjsId) (destIdx : Z) : iProp Σ :=
  "Htext" ∷ is_ytext parent cells arr ∗
  "Hconflict" ∷ conflict_l ↦ node_loc cells (leftIdx + Z.of_nat offset) ∗
  "Hleft" ∷ left_l ↦ node_loc cells (destIdx - 1) ∗
  "Hright" ∷ right_l ↦ node_loc cells rightIdx ∗
  "Hids_before" ∷ (∃ s : slice.t, "Hids_before_ref" ∷ idsBeforeOrigin_l ↦ s ∗
                     "Hids_before_set" ∷ is_id_set s idsBeforeOrigin) ∗
  "Hconflict_ids" ∷ (∃ s : slice.t, "Hconflict_ids_ref" ∷ conflictIds_l ↦ s ∗
                     "Hconflict_ids_set" ∷ is_id_set s conflictIds) ∗
  "%Hoff" ∷ ⌜(1 <= offset)%nat⌝ ∗
  "%Hdest" ∷ ⌜(leftIdx + 1 <= destIdx <= leftIdx + Z.of_nat offset)%Z⌝ ∗
  "%Hbound" ∷ ⌜(leftIdx + Z.of_nat offset <= rightIdx)%Z⌝ ∗
  "%Hloop" ∷ ⌜setfii_loop (Z.to_nat (rightIdx - leftIdx) - offset) offset leftIdx rightIdx
                 originLeftId originRightId newItemId arr idsBeforeOrigin conflictIds destIdx
               = loopResult⌝.

(* ===== the Integrate WP specification ==================================== *)

(** [is_fresh_item_raw item_l input iv oleft oright]: [item_l] is a heap [Item] whose
    id / content and origin-id cells carry the integration [input]. Its abstract
    model item is [newItem = toItem input arr] — that link is a side condition of
    the spec (a fresh item's resolved origins depend on the current document
    [arr]), so it is *not* restated here. The [left']/[right'] fields are *not*
    constrained: the scan / entry-guard never read them, and [Store.Integrate]
    has already repaired (set) them by the time it calls the scan. *)
Definition is_fresh_item_raw (item_l : loc) (input : IntegrateInput (A := A))
    (iv : yjs.item.t) (oleft oright : option yjs.id.t) : iProp Σ :=
  "Hitem" ∷ item_l ↦ iv ∗
  "Holeft" ∷ is_origin_id iv.(yjs.item.originLeftId') oleft ∗
  "Horight" ∷ is_origin_id iv.(yjs.item.originRightId') oright ∗
  "%Hin_l" ∷ ⌜(toYjsId <$> oleft) = in_originId input⌝ ∗   (* heap ids = input ids *)
  "%Hin_r" ∷ ⌜(toYjsId <$> oright) = in_rightOriginId input⌝ ∗
  "%Hid" ∷ ⌜toYjsId iv.(yjs.item.id') = in_id input⌝ ∗
  "%Hcontent" ∷ ⌜toContent iv.(yjs.item.content') = in_content input⌝.

(** [is_fresh_item item_l input]: the freshly-built, not-yet-integrated heap
    [Item] that [Store.Integrate] is about to splice in — everything about the
    caller's item is encapsulated here (its model value [iv] and origin pointers
    are existentially hidden). On top of [is_fresh_item_raw] it records that the
    item is unlinked ([left']/[right'] = null) and is a countable, single-char
    insert ([flags'] = ItemCountable, content length 1) — exactly what [NewItem]
    produces. This is the item-side half of the top-level Integrate spec; the
    document-side half is [is_valid_ytext]. *)
Definition is_fresh_item (item_l : loc) (input : IntegrateInput (A := A)) : iProp Σ :=
  ∃ (iv : yjs.item.t) (oleft oright : option yjs.id.t),
    is_fresh_item_raw item_l input iv oleft oright ∗
    ⌜iv.(yjs.item.left') = null⌝ ∗
    ⌜iv.(yjs.item.right') = null⌝ ∗
    ⌜iv.(yjs.item.flags') = W8 2⌝ ∗
    ⌜length (iv.(yjs.item.content').(yjs.content.content')) = 1%nat⌝.

(** The algorithmic core (extracted Go function [scanConflicts]): starting at the
    cursor [node_loc cells (leftIdx + 1)] with the anchor at [node_loc cells leftIdx],
    the scan returns the resolved left anchor [node_loc cells (destIdx - 1)], where
    [destIdx] is the pure [setfindIntegratedIndex]. This is the WP refinement of the
    loop onto [setfii_loop]: the loop invariant [integrate_loop_inv] couples the heap
    loop state to a [setfii_loop] run, and each Go branch matches a [setfii_loop]
    unfold (via [wp_idOptEqual] / [wp_itemPtrEqual_node] / [wp_containsId] and the
    [cell_repr] origin facts). *)
Lemma wp_scanConflicts (parent item_l : loc)
    (cells : list item_cell) (arr : list (YjsItem A))
    (input : IntegrateInput (A := A)) (newItem : YjsItem A)
    (iv : yjs.item.t) (oleft oright : option yjs.id.t)
    (leftIdx rightIdx : Z) (destIdx : nat) :
  YjsArrInvariant arr ->
  toItem input arr = Some newItem ->
  IsItemValid newItem ->
  maximalId newItem arr ->
  findLeftIdx (in_originId input) arr = Some leftIdx ->
  findRightIdx (in_rightOriginId input) arr = Some rightIdx ->
  setfindIntegratedIndex leftIdx rightIdx input arr = Some destIdx ->
  {{{ is_pkg_init yjs ∗ is_ytext parent cells arr ∗
      is_fresh_item_raw item_l input iv oleft oright }}}
    @! yjs.scanConflicts #item_l #(node_loc cells leftIdx)
        #(node_loc cells (leftIdx + 1)) #(node_loc cells rightIdx)
  {{{ RET #(node_loc cells (Z.of_nat destIdx - 1));
      is_ytext parent cells arr ∗ is_fresh_item_raw item_l input iv oleft oright }}}.
Proof using All.
  move=> Harr Htoitem Hvalid Hmax HfindL HfindR HfindD.
  wp_start as "(Htext & Hfresh)". iNamed "Htext". iNamed "Hfresh".
  (* Index bounds via the pure model. *)
  have Hids_unique := yai_unique _ Harr.
  have HfindLeftPtr : findPtrIdx (origin newItem) arr = Some leftIdx.
  { rewrite -(toitem_lemmas.findLeftIdx_findPtrIdx_eq input newItem arr Hids_unique Htoitem). exact HfindL. }
  have HfindRightPtr : findPtrIdx (rightOrigin newItem) arr = Some rightIdx.
  { rewrite -(toitem_lemmas.findRightIdx_findPtrIdx_eq input newItem arr Hids_unique Htoitem). exact HfindR. }
  have HoriginInArr := findptridx_getelem.findPtrIdx_ArrSet arr (origin newItem) leftIdx HfindLeftPtr.
  have HrightOriginInArr := findptridx_getelem.findPtrIdx_ArrSet arr (rightOrigin newItem) rightIdx HfindRightPtr.
  have HleftLB := insert_lemmas.findPtrIdx_ge_minus_1 arr (origin newItem) leftIdx HfindLeftPtr.
  have HleftLtRight := findptridx_order2.YjsLt'_findPtrIdx_lt arr (origin newItem) (rightOrigin newItem)
                leftIdx rightIdx Harr HoriginInArr HrightOriginInArr (iiv_origin_lt _ Hvalid) HfindLeftPtr HfindRightPtr.
  have HrightUB := insert_lemmas.findPtrIdx_le_size arr (rightOrigin newItem) rightIdx HfindRightPtr.
  have Hcells_len : length cells = length arr := cells_repr_length _ _ _ Hrepr.
  have Hrlen : (rightIdx <= Z.of_nat (length cells))%Z by rewrite Hcells_len; exact HrightUB.
  wp_auto.
  (* the two id-set accumulators start empty *)
  wp_apply wp_slice_literal. iSplitR; first done. iIntros "%ci_sl [Hci_sl Hci_cap]". wp_auto.
  wp_apply wp_slice_literal. iSplitR; first done. iIntros "%ibo_sl [Hibo_sl Hibo_cap]". wp_auto.
  (* expose the pure loop result [d] (with [Z.to_nat d = destIdx]) *)
  rewrite /setfindIntegratedIndex in HfindD.
  destruct (setfii_loop (Z.to_nat (rightIdx - leftIdx) - 1) 1 leftIdx rightIdx
              (in_originId input) (in_rightOriginId input) (in_id input) arr ∅ ∅ (leftIdx + 1))
    as [d|] eqn:Hsetfii; last by (simpl in HfindD; done).
  simpl in HfindD. injection HfindD as Hd_eq.
  (* loop invariant: offset = 1, accumulators empty, dest = leftIdx + 1 *)
  iAssert (∃ (offset : nat) (idsB conflictI : gset YjsId) (destL : Z),
    integrate_loop_inv parent cells arr leftIdx rightIdx input.(in_originId)
      input.(in_rightOriginId) input.(in_id) (Some d) conflict_ptr left_ptr right_ptr
      itemsBeforeOrigin_ptr conflictingItems_ptr offset idsB conflictI destL
    ∗ is_fresh_item_raw item_l input iv oleft oright)%I
    with "[Hparent Hdll conflict left right conflictingItems Hci_sl Hci_cap itemsBeforeOrigin Hibo_sl Hibo_cap Hitem Holeft Horight]" as "IH".
  { iExists 1%nat, ∅, ∅, (leftIdx + 1)%Z.
    rewrite /integrate_loop_inv /is_fresh_item_raw.
    replace (leftIdx + 1 - 1)%Z with leftIdx by lia.
    replace (leftIdx + Z.of_nat 1)%Z with (leftIdx + 1)%Z by lia.
    iFrame "conflict left right Hitem Holeft Horight".
    iSplitL "Hparent Hdll itemsBeforeOrigin Hibo_sl Hibo_cap conflictingItems Hci_sl Hci_cap".
    - iSplitL "Hparent Hdll".
      { iExists yt, tl. iFrame "Hparent Hdll". done. }
      iSplitL "itemsBeforeOrigin Hibo_sl Hibo_cap".
      { iExists _. iFrame "itemsBeforeOrigin". iExists ([] : list yjs.id.t). iFrame "Hibo_sl Hibo_cap". done. }
      iSplitL "conflictingItems Hci_sl Hci_cap".
      { iExists _. iFrame "conflictingItems". iExists ([] : list yjs.id.t). iFrame "Hci_sl Hci_cap". done. }
      iPureIntro; split_and!; [lia | lia | lia | lia | exact Hsetfii].
    - iPureIntro; split_and!; [exact Hin_l | exact Hin_r | exact Hid | exact Hcontent]. }
  wp_for "IH".
  iDestruct "IH" as "[Hinv Hfresh]". iNamed "Hinv". iNamed "Hfresh".
  iDestruct "Holeft" as "#Holeft". iDestruct "Horight" as "#Horight".
  wp_auto.
  destruct (decide (leftIdx + offset = Z.of_nat (length cells))%Z) as [Heq_len | Hne_len].
  - (* cursor reached the end: [conflict = nil], loop exits; fuel 0 pins [destL = d] *)
    have Hnull : node_loc cells (leftIdx + offset) = null.
    { rewrite /node_loc decide_True; last lia.
      rewrite Heq_len Nat2Z.id lookup_ge_None_2; [done | lia]. }
    have HdestL : destL = d.
    { have Hfuel0 : (Z.to_nat (rightIdx - leftIdx) - offset = 0)%nat by lia.
      rewrite Hfuel0 /= in Hloop. by injection Hloop. }
    rewrite Hnull bool_decide_eq_true_2; last reflexivity. simpl.
    rewrite decide_False; last done.
    wp_auto. subst destL.
    have Hdpos : (0 <= d)%Z by lia.
    replace (node_loc cells (d - 1)) with (node_loc cells (Z.of_nat destIdx - 1))
      by (f_equal; rewrite -Hd_eq Z2Nat.id //).
    rewrite decide_True; last reflexivity. wp_auto.
    iApply "HΦ". iFrame "Htext". rewrite /is_fresh_item_raw. iFrame "Hitem Holeft Horight".
    iPureIntro; split_and!; done.
  - (* cursor in range: run one scan step, matched to a [setfii_loop] unfold. *)
    have Hlt : (leftIdx + offset < Z.of_nat (length cells))%Z by lia.
    have Hi_lt : (Z.to_nat (leftIdx + offset) < length cells)%nat by lia.
    destruct (cells !! Z.to_nat (leftIdx + offset)) as [ci|] eqn:Hci;
      last by (apply lookup_ge_None in Hci; lia).
    have Hci_loc : node_loc cells (leftIdx + offset) = ic_loc ci
      by rewrite /node_loc decide_True; [rewrite Hci | lia].
    iAssert (⌜ic_loc ci ≠ null⌝ ∗ is_ytext parent cells arr)%I with "[Htext]" as "[%Hci_nn Htext]".
    { iNamed "Htext". iDestruct (is_dll_lookup_acc _ _ _ _ _ _ _ Hci with "Hdll") as "[Hcival Hback]".
      iDestruct (typed_pointsto_not_null with "Hcival") as %Hnn.
      iDestruct ("Hback" with "Hcival") as "Hdll".
      iSplitR; first (iPureIntro; exact Hnn). iExists yt0, tl0. iFrame "Hparent Hdll". done. }
    have Hnnull : node_loc cells (leftIdx + offset) ≠ null by rewrite Hci_loc; exact Hci_nn.
    rewrite (bool_decide_eq_false_2 _ Hnnull). simpl. rewrite decide_True; last reflexivity.
    wp_auto.
    wp_apply (wp_itemPtrEqual_node parent cells arr (leftIdx + offset) rightIdx Harr
                ltac:(lia) Hbound Hrlen with "[$Htext]").
    iIntros "Htext".
    destruct (decide (leftIdx + offset = rightIdx)) as [Heqr | Hner].
    + (* conflict = right: break; fuel 0 pins [destL = d] *)
      rewrite (bool_decide_eq_true_2 _ Heqr).
      have HdestL : destL = d.
      { have Hfuel0 : (Z.to_nat (rightIdx - leftIdx) - offset = 0)%nat by lia.
        rewrite Hfuel0 /= in Hloop. by injection Hloop. }
      wp_auto. subst destL.
      have Hdpos : (0 <= d)%Z by lia.
      replace (node_loc cells (d - 1)) with (node_loc cells (Z.of_nat destIdx - 1))
        by (f_equal; rewrite -Hd_eq Z2Nat.id //).
      wp_for_post.
      iApply "HΦ". iFrame "Htext". rewrite /is_fresh_item_raw. iFrame "Hitem Holeft Horight".
      iPureIntro; split_and!; done.
    + (* conflict ≠ right: scan one item; match the [setfii_loop] branches *)
      rewrite (bool_decide_eq_false_2 _ Hner).
      have Hir : (leftIdx + offset < rightIdx)%Z by lia.
      wp_auto.
      have [yi [Hyi Hcr_repr]] := cells_repr_lookup _ _ _ _ _ Hrepr Hci.
      iNamed "Htext".
      iDestruct (is_dll_acc cells _ _ (Z.to_nat (leftIdx + offset)) ci Hci with "Hdll")
        as "(%Hcloc0 & %Hcl0 & %Hcr0 & Hcival & #Hcol & #Hcor & Hback)".
      iEval (rewrite -Hci_loc) in "Hcival".
      wp_auto.
      iDestruct "Hids_before" as (ibo_s) "[Hibo_ref Hibo_setf]".
      iDestruct "Hibo_setf" as (vs_ibo) "(Hibo_sl & Hibo_cap & %Hibo_set)".
      iDestruct "Hconflict_ids" as (ci_s) "[Hci_ref Hci_setf]".
      iDestruct "Hci_setf" as (vs_ci) "(Hci_sl & Hci_cap & %Hci_set)".
      wp_auto.
      wp_apply wp_slice_literal. iSplitR; first done. iIntros "%sing1 [Hsing1 _]". wp_auto.
      wp_apply (wp_slice_append with "[$Hibo_sl $Hibo_cap $Hsing1]").
      iIntros "%ibo_s2 (Hibo_sl & Hibo_cap & _)". wp_auto.
      wp_apply wp_slice_literal. iSplitR; first done. iIntros "%sing2 [Hsing2 _]". wp_auto.
      wp_apply (wp_slice_append with "[$Hci_sl $Hci_cap $Hsing2]").
      iIntros "%ci_s2 (Hci_sl & Hci_cap & _)". wp_auto.
      wp_apply (wp_idOptEqual iv.(yjs.item.originLeftId') ci.(ic_val).(yjs.item.originLeftId')
                  oleft ci.(ic_oleft) with "[$Holeft $Hcol]").
      remember ((Z.to_nat (rightIdx - leftIdx) - offset)%nat) as fuel eqn:Hfuel_eq.
      destruct fuel as [|count']; first (exfalso; lia).
      cbn [setfii_loop] in Hloop. rewrite Hyi /= in Hloop.
      have HcId := proj1 Hcr_repr.
      have HoL := proj1 (proj2 (proj2 Hcr_repr)).
      have HoR := proj1 (proj2 (proj2 (proj2 Hcr_repr))).
      case_bool_decide as Hoeq.
      * (* same left origin as the new item *)
        have HoeqL : origin_id (origin yi) = input.(in_originId) by rewrite HoL -Hoeq Hin_l.
        rewrite (decide_True _ _ HoeqL) in Hloop.
        wp_auto.
        case_bool_decide as Hclt.
        -- (* smaller client id: advance the anchor (left := conflict) *)
           have HcltL : ((item_id yi).(clientId) < input.(in_id).(clientId))%nat
             by (rewrite HcId -Hid /toYjsId /=; word).
           rewrite (decide_True _ _ HcltL) in Hloop.
           wp_auto.
           wp_apply wp_slice_literal. iSplitR; first done.
           iIntros "%ci_empty [Hci_empty Hci_empty_cap]". wp_auto.
           wp_for_post.
           iEval (rewrite Hci_loc) in "Hcival".
           iDestruct ("Hback" with "Hcival") as "Hdll".
           iFrame "HΦ item".
           iExists (S offset), ({[item_id yi]} ∪ idsB), ∅, (leftIdx + Z.of_nat offset + 1)%Z.
           rewrite /integrate_loop_inv /is_fresh_item_raw.
           iSplitL "Hparent Hdll Hconflict Hleft Hright Hibo_ref Hibo_sl Hibo_cap Hci_ref Hci_empty Hci_empty_cap"; last first.
           { iFrame "Hitem Holeft Horight".
             iPureIntro; split_and!; [exact Hin_l0|exact Hin_r0|exact Hid0|exact Hcontent0]. }
           iSplitL "Hparent Hdll". { iExists yt0, tl0. iFrame "Hparent Hdll". done. }
           iSplitL "Hconflict".
           { rewrite Hcr0. replace (leftIdx + Z.of_nat (S offset))%Z with (Z.to_nat (leftIdx + offset) + 1)%Z by lia. iFrame "Hconflict". }
           iSplitL "Hleft".
           { replace (leftIdx + Z.of_nat offset + 1 - 1)%Z with (leftIdx + offset)%Z by lia. iFrame "Hleft". }
           iSplitL "Hright". { iFrame "Hright". }
           iSplitL "Hibo_ref Hibo_sl Hibo_cap".
           { iExists ibo_s2. iFrame "Hibo_ref". iExists _. iFrame "Hibo_sl Hibo_cap". iPureIntro.
             have H0 : sint.nat (W64 0) = 0%nat by word.
             rewrite H0 fmap_app list_to_set_app_L Hibo_set; cbn [insert list_insert fmap list_fmap list_to_set]; rewrite -HcId; apply gset_union_singleton_swap. }
           iSplitL "Hci_ref Hci_empty Hci_empty_cap".
           { iExists _. iFrame "Hci_ref". iExists ([] : list yjs.id.t). iFrame "Hci_empty Hci_empty_cap". done. }
           iPureIntro; split_and!;
             [lia | lia | lia | lia
             | replace (Z.to_nat (rightIdx - leftIdx) - S offset)%nat with count' by lia;
               replace (leftIdx + Z.of_nat offset + 1)%Z with (Z.of_nat (Z.to_nat (leftIdx + offset) + 1)) by lia;
               exact Hloop].
        -- (* larger-or-equal client id: same right origin -> break, else keep scanning *)
           have HcltGe : ¬ ((item_id yi).(clientId) < input.(in_id).(clientId))%nat
             by (rewrite HcId -Hid /toYjsId /=; word).
           rewrite (decide_False _ _ HcltGe) in Hloop.
           wp_auto.
           wp_apply (wp_idOptEqual iv.(yjs.item.originRightId') ci.(ic_val).(yjs.item.originRightId')
                       oright ci.(ic_oright) with "[$Horight $Hcor]").
           case_bool_decide as HoeqR.
           ++ (* same right origin: integration points coincide -> break *)
              have HoeqRR : origin_id (rightOrigin yi) = input.(in_rightOriginId)
                by rewrite HoR -HoeqR Hin_r.
              rewrite (decide_True _ _ HoeqRR) in Hloop.
              injection Hloop as HdestL.
              wp_auto. subst destL.
              iEval (rewrite Hci_loc) in "Hcival". iDestruct ("Hback" with "Hcival") as "Hdll".
              wp_for_post.
              have Hdpos : (0 <= d)%Z by lia.
              replace (node_loc cells (d - 1)) with (node_loc cells (Z.of_nat destIdx - 1))
                by (f_equal; rewrite -Hd_eq Z2Nat.id //).
              iApply "HΦ". iSplitL "Hparent Hdll". { iExists yt0, tl0. iFrame "Hparent Hdll". done. }
              rewrite /is_fresh_item_raw. iFrame "Hitem Holeft Horight". iPureIntro; split_and!; done.
           ++ (* different right origin: keep scanning, anchor unchanged *)
              have HneqRR : origin_id (rightOrigin yi) ≠ input.(in_rightOriginId).
              { rewrite HoR -Hin_r; move=> Heq; apply HoeqR; by rewrite Heq. }
              rewrite (decide_False _ _ HneqRR) in Hloop.
              wp_auto.
              wp_for_post.
              iEval (rewrite Hci_loc) in "Hcival". iDestruct ("Hback" with "Hcival") as "Hdll".
              iFrame "HΦ item".
              iExists (S offset), ({[item_id yi]} ∪ idsB), ({[item_id yi]} ∪ conflictI), destL.
              rewrite /integrate_loop_inv /is_fresh_item_raw.
              iSplitL "Hparent Hdll Hconflict Hleft Hright Hibo_ref Hibo_sl Hibo_cap Hci_ref Hci_sl Hci_cap"; last first.
              { iFrame "Hitem Holeft Horight".
                iPureIntro; split_and!; [exact Hin_l0|exact Hin_r0|exact Hid0|exact Hcontent0]. }
              iSplitL "Hparent Hdll". { iExists yt0, tl0. iFrame "Hparent Hdll". done. }
              iSplitL "Hconflict".
              { rewrite Hcr0. replace (leftIdx + Z.of_nat (S offset))%Z with (Z.to_nat (leftIdx + offset) + 1)%Z by lia. iFrame "Hconflict". }
              iSplitL "Hleft". { iFrame "Hleft". }
              iSplitL "Hright". { iFrame "Hright". }
              iSplitL "Hibo_ref Hibo_sl Hibo_cap".
              { iExists ibo_s2. iFrame "Hibo_ref". iExists _. iFrame "Hibo_sl Hibo_cap". iPureIntro.
                have H0 : sint.nat (W64 0) = 0%nat by word.
                rewrite H0 fmap_app list_to_set_app_L Hibo_set; cbn [insert list_insert fmap list_fmap list_to_set]; rewrite -HcId; apply gset_union_singleton_swap. }
              iSplitL "Hci_ref Hci_sl Hci_cap".
              { iExists ci_s2. iFrame "Hci_ref". iExists _. iFrame "Hci_sl Hci_cap". iPureIntro.
                have H0 : sint.nat (W64 0) = 0%nat by word.
                rewrite H0 fmap_app list_to_set_app_L Hci_set; cbn [insert list_insert fmap list_fmap list_to_set]; rewrite -HcId; apply gset_union_singleton_swap. }
              iPureIntro; split_and!;
                [lia | lia | lia | lia
                | replace (Z.to_nat (rightIdx - leftIdx) - S offset)%nat with count' by lia; exact Hloop].
      * (* different left origin from the new item *)
        have HoLne : origin_id (origin yi) ≠ input.(in_originId)
          by (rewrite HoL -Hin_l; move=> Heq; apply Hoeq; by rewrite Heq).
        rewrite (decide_False _ _ HoLne) in Hloop.
        rewrite HoL in Hloop.
        destruct (ci.(ic_oleft)) as [idv|] eqn:Hcoleft; last first.
        -- (* conflict has no left origin: origins would cross -> break *)
           iDestruct "Hcol" as "%Hcol_null".
           simpl in Hloop. injection Hloop as HdestL.
           wp_auto. rewrite Hcol_null. wp_auto. subst destL.
           iEval (rewrite Hci_loc) in "Hcival". iDestruct ("Hback" with "Hcival") as "Hdll".
           wp_for_post.
           have Hdpos : (0 <= d)%Z by lia.
           replace (node_loc cells (d - 1)) with (node_loc cells (Z.of_nat destIdx - 1))
             by (f_equal; rewrite -Hd_eq Z2Nat.id //).
           iApply "HΦ". iSplitL "Hparent Hdll". { iExists yt0, tl0. iFrame "Hparent Hdll". done. }
           rewrite /is_fresh_item_raw. iFrame "Hitem Holeft Horight". iPureIntro; split_and!; done.
        -- (* conflict has a left origin [idv] (different from the new item's) *)
           iDestruct "Hcol" as "[%Hcol_nn #Hcol_pt]".
           simpl in Hloop.
           wp_auto. rewrite bool_decide_eq_false_2; last exact Hcol_nn. wp_auto.
           wp_apply (wp_containsId with "[$Hibo_sl]"). iIntros "Hibo_sl".
           have H0 : sint.nat (W64 0) = 0%nat by word.
           rewrite H0 fmap_app list_to_set_app_L Hibo_set.
           cbn [insert list_insert fmap list_fmap list_to_set]. rewrite -HcId.
           destruct (decide (toYjsId idv ∈ ({[item_id yi]} ∪ idsB : gset YjsId))) as [Hin_ibo | Hnin_ibo].
           ++ (* conflict's left origin was already scanned (case 2) *)
              have Hmem_ibo := gset_elem_union_singleton_swap idsB (item_id yi) (toYjsId idv) Hin_ibo.
              rewrite (bool_decide_eq_true_2 _ Hmem_ibo).
              (* the [destruct (decide ... ∈ idsB)] above already reduced Hloop's
                 outer guard (it shares the Decision instance), so Hloop is now the
                 inner [if decide (... ∉ conflictI)]. *)
              wp_auto.
              wp_apply (wp_containsId with "[$Hci_sl]"). iIntros "Hci_sl".
              rewrite fmap_app list_to_set_app_L Hci_set.
              cbn [insert list_insert fmap list_fmap list_to_set]. rewrite -HcId.
              destruct (decide (toYjsId idv ∈ ({[item_id yi]} ∪ conflictI : gset YjsId))) as [Hin_ci | Hnin_ci].
              ** (* already in conflictingItems: no anchor move, keep scanning (continue) *)
                 have Hmem_ci := gset_elem_union_singleton_swap conflictI (item_id yi) (toYjsId idv) Hin_ci.
                 rewrite (bool_decide_eq_true_2 _ Hmem_ci).
                 have Hnn : ¬ (toYjsId idv ∉ ({[item_id yi]} ∪ conflictI : gset YjsId))
                   by (move=> Hcontra; exact (Hcontra Hin_ci)).
                 rewrite (decide_False _ _ Hnn) in Hloop.
                 wp_auto.
                 wp_for_post.
                 iEval (rewrite Hci_loc) in "Hcival". iDestruct ("Hback" with "Hcival") as "Hdll".
                 iFrame "HΦ item".
                 iExists (S offset), ({[item_id yi]} ∪ idsB), ({[item_id yi]} ∪ conflictI), destL.
                 rewrite /integrate_loop_inv /is_fresh_item_raw.
                 iSplitL "Hparent Hdll Hconflict Hleft Hright Hibo_ref Hibo_sl Hibo_cap Hci_ref Hci_sl Hci_cap"; last first.
                 { iFrame "Hitem Holeft Horight".
                   iPureIntro; split_and!; [exact Hin_l0|exact Hin_r0|exact Hid0|exact Hcontent0]. }
                 iSplitL "Hparent Hdll". { iExists yt0, tl0. iFrame "Hparent Hdll". done. }
                 iSplitL "Hconflict".
                 { rewrite Hcr0. replace (leftIdx + Z.of_nat (S offset))%Z with (Z.to_nat (leftIdx + offset) + 1)%Z by lia. iFrame "Hconflict". }
                 iSplitL "Hleft". { iFrame "Hleft". }
                 iSplitL "Hright". { iFrame "Hright". }
                 iSplitL "Hibo_ref Hibo_sl Hibo_cap".
                 { iExists ibo_s2. iFrame "Hibo_ref". iExists _. iFrame "Hibo_sl Hibo_cap". iPureIntro.
                   rewrite fmap_app list_to_set_app_L Hibo_set; cbn [insert list_insert fmap list_fmap list_to_set]; rewrite -HcId; apply gset_union_singleton_swap. }
                 iSplitL "Hci_ref Hci_sl Hci_cap".
                 { iExists ci_s2. iFrame "Hci_ref". iExists _. iFrame "Hci_sl Hci_cap". iPureIntro.
                   rewrite fmap_app list_to_set_app_L Hci_set; cbn [insert list_insert fmap list_fmap list_to_set]; rewrite -HcId; apply gset_union_singleton_swap. }
                 iPureIntro; split_and!;
                   [lia | lia | lia | lia
                   | replace (Z.to_nat (rightIdx - leftIdx) - S offset)%nat with count' by lia; exact Hloop].
              ** (* not yet in conflictingItems: advance the anchor (left := conflict) *)
                 have Hmem_ci_neg := gset_not_elem_union_singleton_swap conflictI (item_id yi) (toYjsId idv) Hnin_ci.
                 rewrite (bool_decide_eq_false_2 _ Hmem_ci_neg).
                 rewrite (decide_True _ _ Hnin_ci) in Hloop.
                 wp_auto.
                 wp_apply wp_slice_literal. iSplitR; first done.
                 iIntros "%ci_empty [Hci_empty Hci_empty_cap]". wp_auto.
                 wp_for_post.
                 iEval (rewrite Hci_loc) in "Hcival". iDestruct ("Hback" with "Hcival") as "Hdll".
                 iFrame "HΦ item".
                 iExists (S offset), ({[item_id yi]} ∪ idsB), ∅, (leftIdx + Z.of_nat offset + 1)%Z.
                 rewrite /integrate_loop_inv /is_fresh_item_raw.
                 iSplitL "Hparent Hdll Hconflict Hleft Hright Hibo_ref Hibo_sl Hibo_cap Hci_ref Hci_empty Hci_empty_cap"; last first.
                 { iFrame "Hitem Holeft Horight".
                   iPureIntro; split_and!; [exact Hin_l0|exact Hin_r0|exact Hid0|exact Hcontent0]. }
                 iSplitL "Hparent Hdll". { iExists yt0, tl0. iFrame "Hparent Hdll". done. }
                 iSplitL "Hconflict".
                 { rewrite Hcr0. replace (leftIdx + Z.of_nat (S offset))%Z with (Z.to_nat (leftIdx + offset) + 1)%Z by lia. iFrame "Hconflict". }
                 iSplitL "Hleft".
                 { replace (leftIdx + Z.of_nat offset + 1 - 1)%Z with (leftIdx + offset)%Z by lia. iFrame "Hleft". }
                 iSplitL "Hright". { iFrame "Hright". }
                 iSplitL "Hibo_ref Hibo_sl Hibo_cap".
                 { iExists ibo_s2. iFrame "Hibo_ref". iExists _. iFrame "Hibo_sl Hibo_cap". iPureIntro.
                   rewrite fmap_app list_to_set_app_L Hibo_set; cbn [insert list_insert fmap list_fmap list_to_set]; rewrite -HcId; apply gset_union_singleton_swap. }
                 iSplitL "Hci_ref Hci_empty Hci_empty_cap".
                 { iExists _. iFrame "Hci_ref". iExists ([] : list yjs.id.t). iFrame "Hci_empty Hci_empty_cap". done. }
                 iPureIntro; split_and!;
                   [lia | lia | lia | lia
                   | replace (Z.to_nat (rightIdx - leftIdx) - S offset)%nat with count' by lia;
                     replace (leftIdx + Z.of_nat offset + 1)%Z with (Z.of_nat (Z.to_nat (leftIdx + offset) + 1)) by lia;
                     exact Hloop].
           ++ (* conflict's left origin is before this run: origins cross -> break *)
              have Hmem_ibo_neg := gset_not_elem_union_singleton_swap idsB (item_id yi) (toYjsId idv) Hnin_ibo.
              rewrite (bool_decide_eq_false_2 _ Hmem_ibo_neg).
              (* the [destruct] already reduced Hloop's guard to its else branch. *)
              injection Hloop as HdestL.
              wp_auto. subst destL.
              iEval (rewrite Hci_loc) in "Hcival". iDestruct ("Hback" with "Hcival") as "Hdll".
              wp_for_post.
              have Hdpos : (0 <= d)%Z by lia.
              replace (node_loc cells (d - 1)) with (node_loc cells (Z.of_nat destIdx - 1))
                by (f_equal; rewrite -Hd_eq Z2Nat.id //).
              iApply "HΦ". iSplitL "Hparent Hdll". { iExists yt0, tl0. iFrame "Hparent Hdll". done. }
              rewrite /is_fresh_item_raw. iFrame "Hitem Holeft Horight". iPureIntro; split_and!; done.
Qed.

(** The conflict scan with its entry guard: resolves whether to scan at all
    (y-octo's left/right-connection check), sets the initial cursor, and delegates
    to [scanConflicts]. When the guard is false the anchors are adjacent
    ([leftIdx + 1 = rightIdx]) so [destIdx = leftIdx + 1] and the unchanged [left]
    already equals [node_loc cells (destIdx - 1)]. *)
Lemma wp_findIntegrationLeft (parent item_l left_loc right_loc : loc)
    (cells : list item_cell) (arr : list (YjsItem A))
    (input : IntegrateInput (A := A)) (newItem : YjsItem A)
    (iv : yjs.item.t) (oleft oright : option yjs.id.t)
    (leftIdx rightIdx : Z) (destIdx : nat) :
  YjsArrInvariant arr ->
  toItem input arr = Some newItem ->
  IsItemValid newItem ->
  maximalId newItem arr ->
  findLeftIdx (in_originId input) arr = Some leftIdx ->
  findRightIdx (in_rightOriginId input) arr = Some rightIdx ->
  setfindIntegratedIndex leftIdx rightIdx input arr = Some destIdx ->
  left_loc = node_loc cells leftIdx ->
  right_loc = node_loc cells rightIdx ->
  {{{ is_pkg_init yjs ∗ is_ytext parent cells arr ∗
      is_fresh_item_raw item_l input iv oleft oright }}}
    @! yjs.findIntegrationLeft #parent #item_l #left_loc #right_loc
  {{{ RET #(node_loc cells (Z.of_nat destIdx - 1));
      is_ytext parent cells arr ∗ is_fresh_item_raw item_l input iv oleft oright }}}.
Proof using All.
  move=> Harr Htoitem Hvalid Hmax HfindL HfindR HfindD Hll Hrl.
  wp_start as "(Htext & Hfresh)". iNamed "Htext". iNamed "Hfresh". wp_auto.
  (* Index bounds via the pure model (mirrors setintegrate_eq_integrate). *)
  have Huniq := yai_unique _ Harr.
  have HfLp : findPtrIdx (origin newItem) arr = Some leftIdx.
  { rewrite -(toitem_lemmas.findLeftIdx_findPtrIdx_eq input newItem arr Huniq Htoitem). exact HfindL. }
  have HfRp : findPtrIdx (rightOrigin newItem) arr = Some rightIdx.
  { rewrite -(toitem_lemmas.findRightIdx_findPtrIdx_eq input newItem arr Huniq Htoitem). exact HfindR. }
  have Horig := findptridx_getelem.findPtrIdx_ArrSet arr (origin newItem) leftIdx HfLp.
  have Hror := findptridx_getelem.findPtrIdx_ArrSet arr (rightOrigin newItem) rightIdx HfRp.
  have HlB := insert_lemmas.findPtrIdx_ge_minus_1 arr (origin newItem) leftIdx HfLp.
  have Hlr := findptridx_order2.YjsLt'_findPtrIdx_lt arr (origin newItem) (rightOrigin newItem)
                leftIdx rightIdx Harr Horig Hror (iiv_origin_lt _ Hvalid) HfLp HfRp.
  have HrUB := insert_lemmas.findPtrIdx_le_size arr (rightOrigin newItem) rightIdx HfRp.
  have Hcells_len : length cells = length arr := cells_repr_length _ _ _ Hrepr.
  have Hrlen : (rightIdx <= Z.of_nat (length cells))%Z by rewrite Hcells_len; exact HrUB.
  (* Entry guard: read the left/right neighbour connections to decide whether the
     conflict scan runs. The guard is false exactly when [leftIdx + 1 = rightIdx]
     (so [destIdx = leftIdx + 1] and the unchanged anchor is the answer); otherwise
     [scanConflicts] resolves the anchor. Four boundary combos: left/right null? *)
  destruct (decide (rightIdx = Z.of_nat (length cells))) as [HrN | HrNN].
  { (* right is null: rightIsNullOrHasLeft = true (no read of right.left) *)
    have Hrnull : right_loc = null.
    { rewrite Hrl HrN /node_loc decide_True; last lia. rewrite Nat2Z.id lookup_ge_None_2; [done | lia]. }
    rewrite (bool_decide_eq_true_2 (right_loc = null) Hrnull). wp_auto.
    destruct (decide (leftIdx = -1)) as [Hl0 | HlP].
    { (* combo 1: left null -> scan from parent.start *)
      have Hlnull : left_loc = null.
      { rewrite Hll Hl0 /node_loc. case_decide; [lia | done]. }
      rewrite Hlnull. wp_auto.
      iAssert (⌜yt.(yjs.yText.start') = node_loc cells 0⌝ ∗ is_dll yt.(yjs.yText.start') tl null null cells)%I with "[Hdll]" as "[%Hstart Hdll]".
      { destruct cells as [|c rest].
        { iDestruct "Hdll" as %[Hl Hlst]. iSplit; iPureIntro; [rewrite Hl /node_loc // | split; [exact Hl | exact Hlst]]. }
        iNamed "Hdll". iSplitR.
        { iPureIntro. rewrite /node_loc /=. by destruct Hloc as [-> _]. }
        iFrame "Hval Holeft Horight Hrest". iPureIntro; split_and!; [exact (proj1 Hloc) | exact (proj2 Hloc) | exact Hprev]. }
      replace (# null) with (# (node_loc cells leftIdx)) by (rewrite -Hll Hlnull //).
      replace (yt.(yjs.yText.start')) with (node_loc cells (leftIdx + 1)) by (rewrite Hstart Hl0; f_equal; lia).
      rewrite Hrl.
      wp_apply (wp_scanConflicts parent item_l cells arr input newItem iv oleft oright leftIdx rightIdx destIdx
                  Harr Htoitem Hvalid Hmax HfindL HfindR HfindD with "[Hparent Hdll Hitem Holeft Horight]").
      { iSplitL "Hparent Hdll".
        { iExists yt, tl. iFrame "Hparent".
          replace (yt.(yjs.yText.start')) with (node_loc cells (leftIdx + 1)) by (rewrite Hstart Hl0; f_equal; lia).
          iFrame "Hdll". done. }
        rewrite /is_fresh_item_raw. iFrame "Hitem Holeft Horight". iPureIntro; split_and!; done. }
      iIntros "[Htext Hfresh]". wp_auto. iApply "HΦ". iFrame "Htext Hfresh". }
    { (* combo 3: left non-null, right null -> compare left.right with right *)
      have HlP' : (0 <= leftIdx)%Z by lia.
      have Hi_lt : (Z.to_nat leftIdx < length cells)%nat by lia.
      destruct (cells !! Z.to_nat leftIdx) as [cl|] eqn:Hcl_lookup; last by (apply lookup_ge_None in Hcl_lookup; lia).
      have Hcl_loc : node_loc cells leftIdx = ic_loc cl.
      { rewrite /node_loc decide_True; last lia. rewrite Hcl_lookup //. }
      iAssert (⌜ic_loc cl ≠ null⌝ ∗ is_dll yt.(yjs.yText.start') tl null null cells)%I with "[Hdll]" as "[%Hclnn Hdll]".
      { iDestruct (is_dll_lookup_acc _ _ _ _ _ _ _ Hcl_lookup with "Hdll") as "[Hclval Hbk]".
        iDestruct (typed_pointsto_not_null with "Hclval") as %Hnn.
        iDestruct ("Hbk" with "Hclval") as "Hdll". iSplitR; [done | iFrame "Hdll"]. }
      have Hlnn : left_loc ≠ null by rewrite Hll Hcl_loc; exact Hclnn.
      rewrite (bool_decide_eq_false_2 (left_loc = null) Hlnn).
      iDestruct (is_dll_acc cells _ _ (Z.to_nat leftIdx) cl Hcl_lookup with "Hdll")
        as "(%Hcloc & %Hcl_l & %Hcr_l & Hcval & #Hcol_l & #Hcor_l & Hback)".
      iEval (rewrite -Hcl_loc) in "Hcval". iEval (rewrite Hll) in "left". wp_auto.
      have Hcr_l' : cl.(ic_val).(yjs.item.right') = node_loc cells (leftIdx + 1).
      { rewrite Hcr_l. f_equal. rewrite Z2Nat.id; lia. }
      rewrite Hcr_l' Hrl.
      iEval (rewrite Hcl_loc) in "Hcval". iDestruct ("Hback" with "Hcval") as "Hdll".
      iAssert (is_ytext parent cells arr) with "[Hparent Hdll]" as "Htext".
      { iExists yt, tl. iFrame "Hparent Hdll". done. }
      wp_apply (wp_itemPtrEqual_node parent cells arr (leftIdx + 1) rightIdx Harr ltac:(lia) ltac:(lia) Hrlen with "[$Htext]").
      iIntros "Htext".
      destruct (decide (leftIdx + 1 = rightIdx)) as [Hadj | Hnadj].
      { (* no scan: leftIdx+1 = rightIdx -> destIdx = leftIdx+1 *)
        rewrite (bool_decide_eq_true_2 _ Hadj). wp_auto.
        rewrite (bool_decide_eq_false_2 (node_loc cells leftIdx = null) ltac:(rewrite -Hll; exact Hlnn)). wp_auto.
        have Hdestadj : Z.of_nat destIdx = leftIdx + 1.
        { rewrite /setfindIntegratedIndex in HfindD.
          replace (Z.to_nat (rightIdx - leftIdx) - 1)%nat with 0%nat in HfindD by lia.
          simpl in HfindD. injection HfindD as HfindD'. rewrite -HfindD' Z2Nat.id; lia. }
        replace (node_loc cells (Z.of_nat destIdx - 1)) with (node_loc cells leftIdx) by (f_equal; lia).
        iApply "HΦ". iFrame "Htext". rewrite /is_fresh_item_raw. iFrame "Hitem Holeft Horight". iPureIntro; split_and!; done. }
      { (* scan: leftIdx+1 < rightIdx, conflict = left.right *)
        rewrite (bool_decide_eq_false_2 _ Hnadj). wp_auto.
        have Hlnn' : node_loc cells leftIdx ≠ null by (rewrite -Hll; exact Hlnn).
        rewrite (bool_decide_eq_false_2 (node_loc cells leftIdx = null) Hlnn'). wp_auto.
        rewrite (bool_decide_eq_false_2 (node_loc cells leftIdx = null) Hlnn').
        iDestruct "Htext" as (yt' tl') "(Hparent & Hdll & %Hlen' & %Hrepr')".
        iDestruct (is_dll_acc cells _ _ (Z.to_nat leftIdx) cl Hcl_lookup with "Hdll") as "(%Hcloc2 & %Hcl_l2 & %Hcr_l2 & Hcval & #Hcol2 & #Hcor2 & Hback)".
        iEval (rewrite -Hcl_loc) in "Hcval". wp_auto. rewrite Hcr_l'.
        iEval (rewrite Hcl_loc) in "Hcval". iDestruct ("Hback" with "Hcval") as "Hdll".
        iAssert (is_ytext parent cells arr) with "[Hparent Hdll]" as "Htext".
        { iExists yt', tl'. iFrame "Hparent Hdll". iPureIntro; split; [exact Hlen' | exact Hrepr']. }
        wp_apply (wp_scanConflicts parent item_l cells arr input newItem iv oleft oright leftIdx rightIdx destIdx
                    Harr Htoitem Hvalid Hmax HfindL HfindR HfindD with "[Htext Hitem Holeft Horight]").
        { iSplitL "Htext"; [iFrame "Htext" | rewrite /is_fresh_item_raw; iFrame "Hitem Holeft Horight"; iPureIntro; split_and!; done]. }
        iIntros "[Htext Hfresh]". wp_auto. iApply "HΦ". iFrame "Htext Hfresh". } } }
  { (* right non-null (rightIdx < length cells): read right.left *)
    have Hr_lt : (Z.to_nat rightIdx < length cells)%nat by lia.
    destruct (cells !! Z.to_nat rightIdx) as [cr|] eqn:Hcr_lookup; last by (apply lookup_ge_None in Hcr_lookup; lia).
    have Hcr_loc : node_loc cells rightIdx = ic_loc cr.
    { rewrite /node_loc decide_True; last lia. rewrite Hcr_lookup //. }
    iAssert (⌜ic_loc cr ≠ null⌝ ∗ is_dll yt.(yjs.yText.start') tl null null cells)%I with "[Hdll]" as "[%Hcrnn Hdll]".
    { iDestruct (is_dll_lookup_acc _ _ _ _ _ _ _ Hcr_lookup with "Hdll") as "[Hcrval Hbk]".
      iDestruct (typed_pointsto_not_null with "Hcrval") as %Hnn.
      iDestruct ("Hbk" with "Hcrval") as "Hdll". iSplitR; [done | iFrame "Hdll"]. }
    have Hrnn : right_loc ≠ null by rewrite Hrl Hcr_loc; exact Hcrnn.
    rewrite (bool_decide_eq_false_2 (right_loc = null) Hrnn).
    iDestruct (is_dll_acc cells _ _ (Z.to_nat rightIdx) cr Hcr_lookup with "Hdll") as "(%Hcloc_r & %Hcl_r & %Hcr_r & Hcrval & #Hcol_r & #Hcor_r & Hback)".
    iEval (rewrite -Hcr_loc) in "Hcrval". iEval (rewrite Hrl) in "right". wp_auto.
    iEval (rewrite Hcr_loc) in "Hcrval". iDestruct ("Hback" with "Hcrval") as "Hdll".
    destruct (decide (leftIdx = -1)) as [Hl0 | HlP].
    { (* combo 2: left null; guard = rightIsNullOrHasLeft = (rightIdx != 0) *)
      have Hlnull : left_loc = null by (rewrite Hll Hl0 /node_loc; case_decide; [lia | done]).
      rewrite Hlnull.
      destruct (decide (rightIdx = 0)) as [Hr0 | HrP].
      { (* rightIdx = 0: no scan *)
        have Hcrl_null : cr.(ic_val).(yjs.item.left') = null by (rewrite Hcl_r /node_loc; case_decide; [lia | done]).
        rewrite Hcrl_null. wp_auto.
        have Hdest0 : destIdx = 0%nat.
        { rewrite /setfindIntegratedIndex in HfindD.
          replace (Z.to_nat (rightIdx - leftIdx) - 1)%nat with 0%nat in HfindD by lia.
          simpl in HfindD. injection HfindD as HfindD'. lia. }
        replace (# null) with (# (node_loc cells (Z.of_nat destIdx - 1))).
        { iApply "HΦ". iSplitR "Hitem Holeft Horight".
          { iExists yt, tl. iFrame "Hparent Hdll". done. }
          rewrite /is_fresh_item_raw. iFrame "Hitem Holeft Horight". iPureIntro; split_and!; done. }
        f_equal. rewrite Hdest0 /node_loc /=. done. }
      { (* rightIdx >= 1: scan from parent.start *)
        have Hcrl_eq : cr.(ic_val).(yjs.item.left') = node_loc cells (rightIdx - 1) by (rewrite Hcl_r; f_equal; rewrite Z2Nat.id; lia).
        have Hr1_lt : (Z.to_nat (rightIdx - 1) < length cells)%nat by lia.
        destruct (cells !! Z.to_nat (rightIdx - 1)) as [crl|] eqn:Hcrl_lookup; last by (apply lookup_ge_None in Hcrl_lookup; lia).
        have Hcrl_loc : node_loc cells (rightIdx - 1) = ic_loc crl by (rewrite /node_loc decide_True; [rewrite Hcrl_lookup // | lia]).
        iAssert (⌜ic_loc crl ≠ null⌝ ∗ is_dll yt.(yjs.yText.start') tl null null cells)%I with "[Hdll]" as "[%Hcrlnn Hdll]".
        { iDestruct (is_dll_lookup_acc _ _ _ _ _ _ _ Hcrl_lookup with "Hdll") as "[Hv Hb]".
          iDestruct (typed_pointsto_not_null with "Hv") as %Hnn2.
          iDestruct ("Hb" with "Hv") as "Hdll". iSplitR; [done | iFrame "Hdll"]. }
        have Hcrl_nn : cr.(ic_val).(yjs.item.left') ≠ null by rewrite Hcrl_eq Hcrl_loc; exact Hcrlnn.
        rewrite (bool_decide_eq_false_2 (cr.(ic_val).(yjs.item.left') = null) Hcrl_nn). wp_auto.
        iAssert (⌜yt.(yjs.yText.start') = node_loc cells 0⌝ ∗ is_dll yt.(yjs.yText.start') tl null null cells)%I with "[Hdll]" as "[%Hstart Hdll]".
        { destruct cells as [|c rest].
          { iDestruct "Hdll" as %[Hl Hlst]. iSplit; iPureIntro; [rewrite Hl /node_loc // | split; [exact Hl | exact Hlst]]. }
          iNamed "Hdll". iSplitR.
          { iPureIntro. rewrite /node_loc /=. by destruct Hloc as [-> _]. }
          iFrame "Hval Holeft Horight Hrest". iPureIntro; split_and!; [exact (proj1 Hloc) | exact (proj2 Hloc) | exact Hprev]. }
        replace (# null) with (# (node_loc cells leftIdx)) by (rewrite -Hll Hlnull //).
        replace (yt.(yjs.yText.start')) with (node_loc cells (leftIdx + 1)) by (rewrite Hstart Hl0; f_equal; lia).
        wp_apply (wp_scanConflicts parent item_l cells arr input newItem iv oleft oright leftIdx rightIdx destIdx
                    Harr Htoitem Hvalid Hmax HfindL HfindR HfindD with "[Hparent Hdll Hitem Holeft Horight]").
        { iSplitL "Hparent Hdll".
          { iExists yt, tl. iFrame "Hparent".
            replace (yt.(yjs.yText.start')) with (node_loc cells (leftIdx + 1)) by (rewrite Hstart Hl0; f_equal; lia).
            iFrame "Hdll". done. }
          rewrite /is_fresh_item_raw. iFrame "Hitem Holeft Horight". iPureIntro; split_and!; done. }
        iIntros "[Htext Hfresh]". wp_auto. iApply "HΦ". iFrame "Htext Hfresh". } }
    { (* combo 4: left non-null, right non-null -> compare left.right with right *)
      have HlP' : (0 <= leftIdx)%Z by lia.
      have Hi_lt : (Z.to_nat leftIdx < length cells)%nat by lia.
      destruct (cells !! Z.to_nat leftIdx) as [cl|] eqn:Hcl_lookup; last by (apply lookup_ge_None in Hcl_lookup; lia).
      have Hcl_loc : node_loc cells leftIdx = ic_loc cl.
      { rewrite /node_loc decide_True; last lia. rewrite Hcl_lookup //. }
      iAssert (⌜ic_loc cl ≠ null⌝ ∗ is_dll yt.(yjs.yText.start') tl null null cells)%I with "[Hdll]" as "[%Hclnn Hdll]".
      { iDestruct (is_dll_lookup_acc _ _ _ _ _ _ _ Hcl_lookup with "Hdll") as "[Hclval Hbk]".
        iDestruct (typed_pointsto_not_null with "Hclval") as %Hnn3.
        iDestruct ("Hbk" with "Hclval") as "Hdll". iSplitR; [done | iFrame "Hdll"]. }
      have Hlnn : left_loc ≠ null by rewrite Hll Hcl_loc; exact Hclnn.
      rewrite (bool_decide_eq_false_2 (left_loc = null) Hlnn).
      iDestruct (is_dll_acc cells _ _ (Z.to_nat leftIdx) cl Hcl_lookup with "Hdll")
        as "(%Hcloc & %Hcl_l & %Hcr_l2 & Hcval & #Hcol_l & #Hcor_l & Hback)".
      iEval (rewrite -Hcl_loc) in "Hcval". iEval (rewrite Hll) in "left". wp_auto.
      have Hcr_l' : cl.(ic_val).(yjs.item.right') = node_loc cells (leftIdx + 1).
      { rewrite Hcr_l2. f_equal. rewrite Z2Nat.id; lia. }
      rewrite Hcr_l'.
      iEval (rewrite Hcl_loc) in "Hcval". iDestruct ("Hback" with "Hcval") as "Hdll".
      iAssert (is_ytext parent cells arr) with "[Hparent Hdll]" as "Htext".
      { iExists yt, tl. iFrame "Hparent Hdll". done. }
      wp_apply (wp_itemPtrEqual_node parent cells arr (leftIdx + 1) rightIdx Harr ltac:(lia) ltac:(lia) Hrlen with "[$Htext]").
      iIntros "Htext".
      destruct (decide (leftIdx + 1 = rightIdx)) as [Hadj | Hnadj].
      { (* no scan *)
        rewrite (bool_decide_eq_true_2 _ Hadj). wp_auto.
        rewrite (bool_decide_eq_false_2 (node_loc cells leftIdx = null) ltac:(rewrite -Hll; exact Hlnn)). wp_auto.
        have Hdestadj : Z.of_nat destIdx = leftIdx + 1.
        { rewrite /setfindIntegratedIndex in HfindD.
          replace (Z.to_nat (rightIdx - leftIdx) - 1)%nat with 0%nat in HfindD by lia.
          simpl in HfindD. injection HfindD as HfindD'. rewrite -HfindD' Z2Nat.id; lia. }
        replace (node_loc cells (Z.of_nat destIdx - 1)) with (node_loc cells leftIdx) by (f_equal; lia).
        iApply "HΦ". iFrame "Htext". rewrite /is_fresh_item_raw. iFrame "Hitem Holeft Horight". iPureIntro; split_and!; done. }
      { (* scan *)
        rewrite (bool_decide_eq_false_2 _ Hnadj). wp_auto.
        have Hlnn' : node_loc cells leftIdx ≠ null by (rewrite -Hll; exact Hlnn).
        rewrite (bool_decide_eq_false_2 (node_loc cells leftIdx = null) Hlnn'). wp_auto.
        rewrite (bool_decide_eq_false_2 (node_loc cells leftIdx = null) Hlnn').
        iDestruct "Htext" as (yt' tl') "(Hparent & Hdll & %Hlen' & %Hrepr')".
        iDestruct (is_dll_acc cells _ _ (Z.to_nat leftIdx) cl Hcl_lookup with "Hdll") as "(%Hcloc2 & %Hcl_l2b & %Hcr_l2b & Hcval & #Hcol2 & #Hcor2 & Hback)".
        iEval (rewrite -Hcl_loc) in "Hcval". wp_auto. rewrite Hcr_l'.
        iEval (rewrite Hcl_loc) in "Hcval". iDestruct ("Hback" with "Hcval") as "Hdll".
        iAssert (is_ytext parent cells arr) with "[Hparent Hdll]" as "Htext".
        { iExists yt', tl'. iFrame "Hparent Hdll". iPureIntro; split; [exact Hlen' | exact Hrepr']. }
        wp_apply (wp_scanConflicts parent item_l cells arr input newItem iv oleft oright leftIdx rightIdx destIdx
                    Harr Htoitem Hvalid Hmax HfindL HfindR HfindD with "[Htext Hitem Holeft Horight]").
        { iSplitL "Htext"; [iFrame "Htext" | rewrite /is_fresh_item_raw; iFrame "Hitem Holeft Horight"; iPureIntro; split_and!; done]. }
        iIntros "[Htext Hfresh]". wp_auto. iApply "HΦ". iFrame "Htext Hfresh". } } }
Qed.

(** Auxiliary spec (the raw refinement): integrating a valid item into a valid
    document yields the document updated per the pure [setintegrate]. Kept as the
    detailed functional characterisation (exposes [setintegrate]/[iv]); the
    public [wp_Store__Integrate] below repackages it as invariant preservation. *)
Lemma wp_Store__Integrate_aux (s parent item_l : loc) (arr arr' : list (YjsItem A))
    (input : IntegrateInput (A := A)) (newItem : YjsItem A)
    (iv : yjs.item.t) (oleft oright : option yjs.id.t) :
  YjsArrInvariant arr ->
  toItem input arr = Some newItem ->
  IsItemValid newItem ->
  maximalId newItem arr ->
  iv.(yjs.item.left') = null ->   (* the caller's item is freshly built / unlinked *)
  iv.(yjs.item.right') = null ->
  iv.(yjs.item.flags') = W8 2 ->   (* freshly built item is Countable (NewItem sets ItemCountable) *)
  length (iv.(yjs.item.content').(yjs.content.content')) = 1%nat ->   (* single-char content => Len() = 1 *)
  setintegrate input arr = Some arr' ->
  {{{ is_pkg_init yjs ∗ is_valid_ytext parent arr ∗
      is_fresh_item_raw item_l input iv oleft oright }}}
    s @! (go.PointerType yjs.store) @! "Integrate" #parent #item_l
  {{{ (cells' : list item_cell) (idx : nat) (c : item_cell), RET #();
      is_ytext parent cells' arr' ∗ ⌜YjsArrInvariant arr'⌝ ∗
      ⌜cells' !! idx = Some c⌝ ∗ ⌜ic_loc c = item_l⌝ ∗
      ⌜toYjsId (ic_val c).(yjs.item.id') = in_id input⌝ ∗
      ⌜length ((ic_val c).(yjs.item.content').(yjs.content.content')) = 1%nat⌝ }}}.
Proof using All.
  move=> Harr Htoitem Hvalid Hmax Hfl Hfr Hflags Hcontlen.
  (* Decompose the pure result: leftIdx / rightIdx / destIdx / itemM and
     arr' = insertIdxIfInBounds destIdx itemM arr. *)
  rewrite /setintegrate.
  case HfindL: (findLeftIdx (in_originId input) arr) => [leftIdx|] //=.
  case HfindR: (findRightIdx (in_rightOriginId input) arr) => [rightIdx|] //=.
  case HfindD: (setfindIntegratedIndex leftIdx rightIdx input arr) => [destIdx|] //=.
  case HmkI: (mkItemByIndex leftIdx rightIdx input arr) => [itemM|] //=.
  move=> [<-].
  wp_start as "(Hvtext & Hfresh)".
  iDestruct "Hvtext" as (cells) "[Htext %Hinv]".
  iNamed "Hfresh".
  have Huniq := yai_unique _ Harr.
  have HfLp : findPtrIdx (origin newItem) arr = Some leftIdx.
  { rewrite -(toitem_lemmas.findLeftIdx_findPtrIdx_eq input newItem arr Huniq Htoitem). exact HfindL. }
  have HfRp : findPtrIdx (rightOrigin newItem) arr = Some rightIdx.
  { rewrite -(toitem_lemmas.findRightIdx_findPtrIdx_eq input newItem arr Huniq Htoitem). exact HfindR. }
  have HlB := insert_lemmas.findPtrIdx_ge_minus_1 arr (origin newItem) leftIdx HfLp.
  have Horig := findptridx_getelem.findPtrIdx_ArrSet arr (origin newItem) leftIdx HfLp.
  have Hror := findptridx_getelem.findPtrIdx_ArrSet arr (rightOrigin newItem) rightIdx HfRp.
  have Hlr := findptridx_order2.YjsLt'_findPtrIdx_lt arr (origin newItem) (rightOrigin newItem)
                leftIdx rightIdx Harr Horig Hror (iiv_origin_lt _ Hvalid) HfLp HfRp.
  have HrUB := insert_lemmas.findPtrIdx_le_size arr (rightOrigin newItem) rightIdx HfRp.
  iDestruct "Htext" as (yt tl) "(Hparent & Hdll & %Hlen & %Hrepr)".
  have Hcells_len : length cells = length arr := cells_repr_length _ _ _ Hrepr.
  have Hrlen : (rightIdx <= Z.of_nat (length cells))%Z by rewrite Hcells_len; exact HrUB.
  have HfindLnode := findById_left_node_loc cells arr oleft leftIdx Hrepr.
  have HfindRnode := findById_right_node_loc cells arr oright rightIdx Hrepr.
  rewrite Hin_l in HfindLnode. rewrite Hin_r in HfindRnode.
  specialize (HfindLnode HfindL). specialize (HfindRnode HfindR).
  wp_auto.
  (* Repair (y-octo Store::repair): resolve item.left / item.right from the origin
     ids. Both branches of each [if] leave the field = node_loc cells leftIdx /
     rightIdx, joined with wp_if_join. *)
  iDestruct "Holeft" as "#Holeft". iDestruct "Horight" as "#Horight".
  wp_if_join (λ v, ⌜v = execute_val⌝ ∗
    ∃ iv1 : yjs.item.t, "Hitem" ∷ item_l ↦ iv1 ∗
      "%Hiv1L" ∷ ⌜iv1.(yjs.item.left') = node_loc cells leftIdx⌝ ∗
      "%Hiv1oL" ∷ ⌜iv1.(yjs.item.originLeftId') = iv.(yjs.item.originLeftId')⌝ ∗
      "%Hiv1oR" ∷ ⌜iv1.(yjs.item.originRightId') = iv.(yjs.item.originRightId')⌝ ∗
      "%Hiv1id" ∷ ⌜iv1.(yjs.item.id') = iv.(yjs.item.id')⌝ ∗
      "%Hiv1con" ∷ ⌜iv1.(yjs.item.content') = iv.(yjs.item.content')⌝ ∗
      "%Hiv1R" ∷ ⌜iv1.(yjs.item.right') = null⌝ ∗
      "%Hiv1flags" ∷ ⌜iv1.(yjs.item.flags') = iv.(yjs.item.flags')⌝ ∗
      "Htext" ∷ is_ytext parent cells arr ∗
      "item" ∷ item_ptr ↦ item_l ∗ "parent" ∷ parent_ptr ↦ parent)%I
    with "[Hparent Hdll Hitem item parent]".
  { destruct oleft as [idv|].
    { iDestruct "Holeft" as "[%Hne _]". rewrite e in Hne. done. }
    iSplitR; first done. iExists iv. iFrame "Hitem item parent".
    iSplitR. { iPureIntro. rewrite Hfl. exact HfindLnode. }
    iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
    iSplitR. { iPureIntro. exact Hfr. }
    iSplitR; [done|].
    iExists yt, tl. iFrame "Hparent Hdll". done. }
  { destruct oleft as [idv|]; last first.
    { iDestruct "Holeft" as "%He". rewrite He in n. done. }
    iDestruct "Holeft" as "[%Hne #Holpt]".
    wp_auto.
    iAssert (is_ytext parent cells arr) with "[Hparent Hdll]" as "Htext".
    { iExists yt, tl. iFrame "Hparent Hdll". done. }
    wp_apply (wp_findById parent cells arr idv with "[$Htext]"). iIntros "Htext".
    wp_auto.
    iSplitR; first done. iExists _. iFrame "Hitem item parent Htext".
    iPureIntro; split_and!; [exact HfindLnode | done | done | done | done | exact Hfr | done]. }
  iIntros (v) "[%Hv Hjoin]". iNamed "Hjoin". subst v.
  iDestruct "Htext" as (yt2 tl2) "(Hparent & Hdll & %Hlen2 & %Hrepr2)".
  wp_auto.
  rewrite Hiv1oR.
  wp_if_join (λ v, ⌜v = execute_val⌝ ∗
    ∃ iv2 : yjs.item.t, "Hitem" ∷ item_l ↦ iv2 ∗
      "%Hiv2L" ∷ ⌜iv2.(yjs.item.left') = node_loc cells leftIdx⌝ ∗
      "%Hiv2R" ∷ ⌜iv2.(yjs.item.right') = node_loc cells rightIdx⌝ ∗
      "%Hiv2oL" ∷ ⌜iv2.(yjs.item.originLeftId') = iv.(yjs.item.originLeftId')⌝ ∗
      "%Hiv2oR" ∷ ⌜iv2.(yjs.item.originRightId') = iv.(yjs.item.originRightId')⌝ ∗
      "%Hiv2id" ∷ ⌜iv2.(yjs.item.id') = iv.(yjs.item.id')⌝ ∗
      "%Hiv2con" ∷ ⌜iv2.(yjs.item.content') = iv.(yjs.item.content')⌝ ∗
      "%Hiv2flags" ∷ ⌜iv2.(yjs.item.flags') = iv.(yjs.item.flags')⌝ ∗
      "Htext" ∷ is_ytext parent cells arr ∗
      "item" ∷ item_ptr ↦ item_l ∗ "parent" ∷ parent_ptr ↦ parent)%I
    with "[Hparent Hdll Hitem item parent]".
  { destruct oright as [idv|].
    { iDestruct "Horight" as "[%Hne _]". rewrite e in Hne. done. }
    iSplitR; first done. iExists iv1. iFrame "Hitem item parent".
    iSplitR. { iPureIntro. exact Hiv1L. }
    iSplitR. { iPureIntro. rewrite Hiv1R. exact HfindRnode. }
    iSplitR. { iPureIntro. exact Hiv1oL. }
    iSplitR. { iPureIntro. exact Hiv1oR. }
    iSplitR. { iPureIntro. exact Hiv1id. }
    iSplitR. { iPureIntro. exact Hiv1con. }
    iSplitR. { iPureIntro. exact Hiv1flags. }
    iExists yt2, tl2. iFrame "Hparent Hdll". done. }
  { destruct oright as [idv|]; last first.
    { iDestruct "Horight" as "%He". rewrite He in n. done. }
    iDestruct "Horight" as "[%Hne #Horpt]".
    try wp_auto.
    replace (iv1.(yjs.item.originRightId')) with (iv.(yjs.item.originRightId')) by (symmetry; exact Hiv1oR).
    wp_auto.
    iAssert (is_ytext parent cells arr) with "[Hparent Hdll]" as "Htext".
    { iExists yt2, tl2. iFrame "Hparent Hdll". done. }
    wp_apply (wp_findById parent cells arr idv with "[$Htext]"). iIntros "Htext".
    wp_auto.
    iSplitR; first done. iExists _. iFrame "Hitem item parent Htext".
    iPureIntro; split_and!; [exact Hiv1L | exact HfindRnode | exact Hiv1oL | exact Hiv1oR | exact Hiv1id | exact Hiv1con | exact Hiv1flags]. }
  iIntros (v) "[%Hv Hjoin]". iNamed "Hjoin". subst v.
  iDestruct "Htext" as (yt3 tl3) "(Hparent & Hdll & %Hlen3 & %Hrepr3)".
  wp_auto.
  (* Conflict scan (the extracted algorithmic core), via the proved spec. *)
  rewrite Hiv2L Hiv2R.
  iAssert (is_ytext parent cells arr) with "[Hparent Hdll]" as "Htext".
  { iExists yt3, tl3. iFrame "Hparent Hdll". done. }
  iAssert (is_fresh_item_raw item_l input iv2 oleft oright) with "[Hitem]" as "Hfresh".
  { rewrite /is_fresh_item_raw. iFrame "Hitem". rewrite Hiv2oL Hiv2oR. iFrame "Holeft Horight".
    iPureIntro; split_and!; [exact Hin_l | exact Hin_r | rewrite Hiv2id; exact Hid | rewrite Hiv2con; exact Hcontent]. }
  wp_apply (wp_findIntegrationLeft parent item_l (node_loc cells leftIdx) (node_loc cells rightIdx)
              cells arr input newItem iv2 oleft oright leftIdx rightIdx destIdx
              Harr Htoitem Hvalid Hmax HfindL HfindR HfindD eq_refl eq_refl with "[$Htext $Hfresh]").
  iIntros "[Htext Hfresh]".
  wp_auto.
  (* [destIdx] is in bounds ([≤ rightIdx ≤ length]), so the splice index is valid
     and [insertIdxIfInBounds] actually inserts (mirrors setintegrate_eq_integrate
     to reach findIntegratedIndex_bounds). *)
  have Hsameid : forall x, ArrSet arr (itemPtr x) -> item_id x = item_id newItem -> x = newItem.
  { move=> x Hx Hxid. exfalso.
    have Hcc : clientId (item_id x) = clientId (item_id newItem) by rewrite Hxid.
    have Hcl := Hmax x Hx Hcc. rewrite Hxid in Hcl. lia. }
  have Hclosed : IsClosedItemSet (ArrSet (newItem :: arr)) :=
    arr_set_closed_push arr newItem (yai_closed _ Harr) Horig Hror.
  have Hinv2 : ItemSetInvariant (ArrSet (newItem :: arr)) :=
    item_set_invariant_push arr newItem (yai_item_set_inv _ Harr) (yai_closed _ Harr)
      (iiv_origin_lt _ Hvalid) (iiv_reachable _ Hvalid) Hsameid.
  have Hsfeq := setfindIntegratedIndex_eq arr newItem input leftIdx rightIdx
    Harr Hclosed Hinv2 Hmax Htoitem HfLp HfRp HlB Hlr HrUB.
  have Hfii : findIntegratedIndex leftIdx rightIdx input arr = Some destIdx by (rewrite -Hsfeq; exact HfindD).
  have Hdle_r := findIntegratedIndex_bounds leftIdx rightIdx input arr destIdx HlB Hlr Hfii.
  have Hdle : (destIdx <= length cells)%nat by (rewrite Hcells_len; lia).
  (* Splice [item] in at index [destIdx]: relink left.right / right.left / item /
     parent.start (is_dll_app to split at destIdx, wp_store to relink, rejoin via
     is_dll_insert_middle), bump parent.len, then conclude is_valid_ytext parent
     (insertIdxIfInBounds destIdx itemM arr) via cells_repr_insert and
     YjsArrInvariant_setintegrate. *)
  iDestruct "Htext" as (yt' tl') "(Hparent & Hdll & %Hlen' & %Hrepr')".
  iDestruct "Hfresh" as "(Hitem & #Holeft2 & #Horight2 & %Hin_l2 & %Hin_r2 & %Hid2 & %Hcont2)".
  iDestruct (typed_pointsto_not_null with "Hitem") as %Hitem_nn.
  (* First [if] (y-octo: link [item] after [left]/[parent.start]). The two index
     cases ([destIdx=0] head insertion vs [destIdx>=1]) converge to a uniform
     left fragment [cs1m] + an untouched right fragment [drop destIdx cells]. *)
  wp_if_join (λ v, ⌜v = execute_val⌝ ∗
    ∃ (cs1m : list item_cell) (hd' : loc) (ytv : yjs.yText.t) (ivL : yjs.item.t),
      "Hparent" ∷ parent ↦ ytv ∗
      "%Hyts" ∷ ⌜ytv.(yjs.yText.start') = hd'⌝ ∗
      "%Hytl" ∷ ⌜ytv.(yjs.yText.len') = W64 (length cells)⌝ ∗
      "Hleftdll" ∷ is_dll hd' (node_loc cells (Z.of_nat destIdx - 1)) null item_l cs1m ∗
      "%Hcs1m" ∷ ⌜cells_repr arr cs1m (take destIdx arr)⌝ ∗
      "Hitem" ∷ item_l ↦ ivL ∗
      "%HivLl" ∷ ⌜ivL.(yjs.item.left') = node_loc cells (Z.of_nat destIdx - 1)⌝ ∗
      "%HivLf" ∷ ⌜ivL.(yjs.item.flags') = iv2.(yjs.item.flags')⌝ ∗
      "%HivLc" ∷ ⌜ivL.(yjs.item.content') = iv2.(yjs.item.content')⌝ ∗
      "%HivLid" ∷ ⌜ivL.(yjs.item.id') = iv2.(yjs.item.id')⌝ ∗
      "%HivLoL" ∷ ⌜ivL.(yjs.item.originLeftId') = iv2.(yjs.item.originLeftId')⌝ ∗
      "%HivLoR" ∷ ⌜ivL.(yjs.item.originRightId') = iv2.(yjs.item.originRightId')⌝ ∗
      "Hrightdll" ∷ is_dll (node_loc cells (Z.of_nat destIdx)) tl' (node_loc cells (Z.of_nat destIdx - 1)) null (drop destIdx cells) ∗
      "Hrightptr" ∷ right_ptr ↦ node_loc cells (Z.of_nat destIdx) ∗
      "item" ∷ item_ptr ↦ item_l ∗
      "parent" ∷ parent_ptr ↦ parent)%I
    with "[Hparent Hdll Hitem left right item parent]".
  { (* destIdx = 0 : head insertion (else branch already executed) *)
    iAssert (⌜destIdx = 0%nat⌝ ∗ is_dll yt'.(yjs.yText.start') tl' null null cells)%I
      with "[Hdll]" as "(%Hd0 & Hdll)".
    { destruct (decide (destIdx = 0%nat)) as [->|Hne].
      - iFrame "Hdll". done.
      - iDestruct (node_loc_lt_not_null cells yt'.(yjs.yText.start') tl' (destIdx - 1) with "Hdll") as "(%Hnn & Hdll)".
        { lia. }
        iFrame "Hdll". iPureIntro. exfalso. apply Hnn.
        have -> : Z.of_nat (destIdx - 1) = (Z.of_nat destIdx - 1)%Z by lia.
        exact e. }
    iDestruct (is_dll_head_node with "Hdll") as %Hhd.
    have Hhd2 : node_loc cells (Z.of_nat destIdx) = yt'.(yjs.yText.start').
    { rewrite Hhd. f_equal. lia. }
    have Hdrop : drop destIdx cells = cells by rewrite Hd0 //.
    iSplitR; first done.
    iExists [], item_l, (yt' <| yjs.yText.start' := item_l |>), (iv2 <| yjs.item.left' := null |>).
    iFrame "Hparent Hitem".
    iSplitR. { iPureIntro. done. }
    iSplitR. { iPureIntro. exact Hlen'. }
    iSplitR. { simpl. iPureIntro. split; [done | exact e]. }
    iSplitR. { iPureIntro. rewrite Hd0 /=. apply cells_repr_nil. }
    iSplitR. { iPureIntro. rewrite e //. }
    iSplitR. { iPureIntro. done. }
    iSplitR. { iPureIntro. done. }
    iSplitR. { iPureIntro. done. }
    iSplitR. { iPureIntro. done. }
    iSplitR. { iPureIntro. done. }
    rewrite Hhd2 e Hdrop.
    iFrame "Hdll right item parent". }
  { (* destIdx >= 1 : splice [item] after node (destIdx-1) (then branch). Relink
       that node's [right'] to [item] via is_dll_app + cons unfold + wp_store. *)
    have Hdpos : (1 <= destIdx)%nat.
    { destruct (decide (1 <= destIdx)%nat) as [?|Hlt]; [done | exfalso; apply n].
      have Hd0 : destIdx = 0%nat by lia.
      rewrite Hd0 /node_loc. case_decide as Hdc; [exfalso; lia | done]. }
    have Hltlen : (destIdx - 1 < length cells)%nat by lia.
    destruct (cells !! (destIdx - 1)%nat) as [lc|] eqn:Hlc; last by (apply lookup_ge_None in Hlc; lia).
    have Hlcloc : node_loc cells (Z.of_nat destIdx - 1) = ic_loc lc.
    { rewrite /node_loc decide_True; last lia.
      have -> : Z.to_nat (Z.of_nat destIdx - 1) = (destIdx - 1)%nat by lia.
      rewrite Hlc //. }
    iDestruct (is_dll_acc cells yt'.(yjs.yText.start') tl' (destIdx - 1)%nat lc Hlc with "Hdll") as "Hacc". iNamed "Hacc".
    have Hcr' : (ic_val lc).(yjs.item.right') = node_loc cells (Z.of_nat destIdx).
    { rewrite Hcr. f_equal. lia. }
    iDestruct ("Hback" with "Hcval") as "Hdll".
    have Hdrop_eq : drop (destIdx - 1)%nat cells = lc :: drop destIdx cells.
    { rewrite (drop_S cells lc (destIdx-1)%nat Hlc). have -> : S (destIdx - 1)%nat = destIdx by lia. done. }
    have Hce : cells = take (destIdx - 1)%nat cells ++ lc :: drop destIdx cells.
    { rewrite -Hdrop_eq. symmetry. apply take_drop. }
    iEval (rewrite {1}Hce) in "Hdll".
    iEval (rewrite is_dll_app) in "Hdll".
    iDestruct "Hdll" as (ml1 mf1) "[Hleft1 Hright1]".
    iDestruct "Hright1" as "(%Hloc1 & %Hprev1 & Hval & #Holc & #Horc & Hrest)".
    destruct Hloc1 as [Hmf1 Hmf1nn].
    iEval (rewrite Hlcloc) in "left".
    rewrite Hlcloc.
    wp_auto.
    iSplitR; first done.
    iExists (take (destIdx - 1)%nat cells ++ [MkItemCell lc.(ic_loc) (lc.(ic_val) <| yjs.item.right' := item_l |>) lc.(ic_oleft) lc.(ic_oright)]), yt'.(yjs.yText.start'), yt', (iv2 <| yjs.item.left' := lc.(ic_loc) |>).
    iFrame "Hparent Hitem".
    iSplitR. { iPureIntro. done. }
    iSplitR. { iPureIntro. exact Hlen'. }
    iSplitL "Hleft1 Hval".
    { rewrite is_dll_app. iExists ml1, lc.(ic_loc).
      iEval (rewrite Hmf1) in "Hleft1". iFrame "Hleft1".
      simpl. iFrame "Hval Holc Horc". iPureIntro.
      split_and!; [reflexivity | (rewrite -Hmf1; exact Hmf1nn) | exact Hprev1 | reflexivity | reflexivity]. }
    iSplitR.
    { iPureIntro.
      destruct (cells_repr_lookup arr cells arr (destIdx-1)%nat lc Hrepr' Hlc) as [la [Hla Hlcla]].
      have Htarr : take destIdx arr = take (destIdx-1)%nat arr ++ [la].
      { rewrite -(take_S_r arr (destIdx-1)%nat la Hla). f_equal. lia. }
      rewrite Htarr. apply cells_repr_app.
      - apply cells_repr_take. exact Hrepr'.
      - apply cells_repr_cons; [| apply cells_repr_nil].
        apply (cell_repr_val_irrel arr lc (lc.(ic_val) <| yjs.item.right' := item_l |>) la Hlcla); reflexivity. }
    iSplitR. { iPureIntro. done. }
    iSplitR. { iPureIntro. done. }
    iSplitR. { iPureIntro. done. }
    iSplitR. { iPureIntro. done. }
    iSplitR. { iPureIntro. done. }
    iSplitR. { iPureIntro. done. }
    iEval (rewrite Hcr' Hmf1) in "Hrest".
    iEval (rewrite Hcr') in "right".
    iFrame "Hrest right item parent". }
  iIntros (v) "[%Hv HQ]". iNamed "HQ". subst v. wp_auto.
  (* Second [if] (y-octo: link [right.left] to [item] when a right neighbour
     exists). The [destIdx<length] / [destIdx=length] cases converge to a right
     fragment [cs2m] whose first [left'] points at [item]. *)
  wp_if_join (λ v, ⌜v = execute_val⌝ ∗
    ∃ (cs2m : list item_cell) (tlN : loc),
      "Hrightdll2" ∷ is_dll (node_loc cells destIdx) tlN item_l null cs2m ∗
      "%Hcs2m" ∷ ⌜cells_repr arr cs2m (drop destIdx arr)⌝ ∗
      "Hrightptr" ∷ right_ptr ↦ node_loc cells (Z.of_nat destIdx) ∗
      "item" ∷ item_ptr ↦ item_l)%I
    with "[Hrightdll Hrightptr item]".
  { (* destIdx = length cells: no right neighbour (else / no-op) *)
    destruct (drop destIdx cells) as [|rc rest] eqn:Hdrop.
    - iSplitR; first done. iExists [], item_l. iFrame "Hrightptr item".
      iSplitR. { simpl. iPureIntro. split; [exact e | reflexivity]. }
      iPureIntro.
      have Hge : (length cells <= destIdx)%nat.
      { have Hlen0 : length (drop destIdx cells) = 0%nat by rewrite Hdrop //.
        rewrite length_drop in Hlen0. lia. }
      rewrite drop_ge; [apply cells_repr_nil | lia].
    - iDestruct "Hrightdll" as "(%Hl & _)". destruct Hl as [_ Hnn]. exfalso. exact (Hnn e). }
  { (* destIdx < length cells: relink right neighbour's left to item *)
    have Hltlen : (destIdx < length cells)%nat.
    { destruct (decide (destIdx < length cells)%nat) as [?|Hge]; [done|].
      exfalso. apply n. rewrite /node_loc decide_True; last lia.
      rewrite Nat2Z.id lookup_ge_None_2; [done | lia]. }
    destruct (drop destIdx cells) as [|rc rest] eqn:Hdrop.
    { exfalso. have Hl0 : length (drop destIdx cells) = 0%nat by rewrite Hdrop //.
      rewrite length_drop in Hl0. lia. }
    iDestruct "Hrightdll" as "(%Hlocr & %Hprevr & Hvalr & #Holr & #Horr & Hrestr)".
    destruct Hlocr as [Hrcloc Hrcnn].
    rewrite Hrcloc.
    wp_auto.
    iDestruct (typed_pointsto_not_null with "Hvalr") as %Hrcnn2.
    iSplitR; first done.
    iExists (MkItemCell rc.(ic_loc) (rc.(ic_val) <| yjs.item.left' := item_l |>) rc.(ic_oleft) rc.(ic_oright) :: rest), tl'.
    iFrame "Hrightptr item".
    iSplitL "Hvalr Hrestr".
    { simpl. iFrame "Hvalr Holr Horr Hrestr". iPureIntro. split_and!; [reflexivity | exact Hrcnn2 | reflexivity]. }
    iPureIntro.
    have Hlenarr : (destIdx < length arr)%nat by (rewrite -Hcells_len; exact Hltlen).
    destruct (drop destIdx arr) as [|ra rest_a] eqn:Hdropa.
    { exfalso. have Hl0 : length (drop destIdx arr) = 0%nat by rewrite Hdropa //.
      rewrite length_drop in Hl0. lia. }
    have Hdr : cells_repr arr (rc :: rest) (ra :: rest_a).
    { rewrite -Hdrop -Hdropa. apply cells_repr_drop. exact Hrepr'. }
    inversion Hdr; subst.
    apply cells_repr_cons.
    - apply (cell_repr_val_irrel arr rc (rc.(ic_val) <| yjs.item.left' := item_l |>) ra); [assumption | reflexivity | reflexivity | reflexivity].
    - assumption. }
  iIntros (v) "[%Hv HQ2]". iNamed "HQ2". subst v. wp_auto.
  (* item.right := right (node_loc cells destIdx) already done; now [Countable()]
     is true (flags = ItemCountable) and [Len()] is 1 (single-char content), so
     [parent.len += 1]. Step the [Item.Countable] / [Item.Len] / [Content.Len]
     methods, resolving the symbolic word tests with [Hflv] / [Hclv]. *)
  have Hflv : ivL.(yjs.item.flags') = W8 2 by rewrite HivLf Hiv2flags Hflags.
  have Hclv : length ivL.(yjs.item.content').(yjs.content.content') = 1%nat by rewrite HivLc Hiv2con //.
  wp_method_call. wp_call. wp_auto. wp_method_call. wp_auto. wp_call. wp_auto.
  rewrite Hflv.
  rewrite (bool_decide_eq_false_2 (w8_word_instance.(word.and) (W8 2) (W8 2) = W8 0)); last by vm_compute.
  simpl negb. wp_auto.
  wp_method_call. wp_call. wp_auto. wp_method_call. wp_call. wp_call. wp_auto.
  wp_method_call. wp_call. wp_auto. wp_method_call. wp_call. wp_call. wp_auto.
  wp_func_call. wp_auto. rewrite Hclv. wp_auto.
  (* Conclude [is_valid_ytext parent (insertIdxIfInBounds destIdx itemM arr)]:
     spell out [itemM]'s resolved origins, the validity of the result, and
     reassemble the DLL with the new node spliced in. *)
  destruct (findptridx_insert.findLeftIdx_getElemExcept arr input leftIdx HfindL) as [lptr [HgetL HisL]].
  destruct (findptridx_insert.findRightIdx_getElemExcept arr input rightIdx HfindR) as [rptr [HgetR HisR]].
  have HitemM : itemM = Item lptr rptr input.(in_id) input.(in_content).
  { move: HmkI. rewrite /mkItemByIndex HgetL HgetR /=. by move=> [<-]. }
  have Hlpo : origin_id lptr = input.(in_originId).
  { destruct (input.(in_originId)) as [pid|] eqn:Hpid.
    - destruct HisL as [it [-> Hfind]]. by rewrite /= (toitem_lemmas.find_by_id_id _ _ _ Hfind).
    - by rewrite HisL. }
  have Hrpo : origin_id rptr = input.(in_rightOriginId).
  { destruct (input.(in_rightOriginId)) as [pid|] eqn:Hpid.
    - destruct HisR as [it [-> Hfind]]. by rewrite /= (toitem_lemmas.find_by_id_id _ _ _ Hfind).
    - by rewrite HisR. }
  have Hsetint : setintegrate input arr = Some (insertIdxIfInBounds destIdx itemM arr).
  { rewrite /setintegrate HfindL /= HfindR /= HfindD /= HmkI //. }
  have Hinv'' : YjsArrInvariant (insertIdxIfInBounds destIdx itemM arr).
  { eapply YjsArrInvariant_setintegrate; (try eassumption); (try exact _). }
  have Harr'' : insertIdxIfInBounds destIdx itemM arr = take destIdx arr ++ itemM :: drop destIdx arr.
  { rewrite /insertIdxIfInBounds decide_True; [done | rewrite -Hcells_len; exact Hdle]. }
  have Hcellrepr : cell_repr arr (MkItemCell item_l (ivL <| yjs.item.right' := node_loc cells destIdx |>) oleft oright) itemM.
  { rewrite /cell_repr HitemM /=. split_and!.
    - rewrite -Hid2 -HivLid //.
    - rewrite -Hcont2 -HivLc //.
    - rewrite Hlpo -Hin_l2 //.
    - rewrite Hrpo -Hin_r2 //.
    - exact Hflv.
    - exact Hclv. }
  have Hlen0 : length (cs1m ++ MkItemCell item_l (ivL <| yjs.item.right' := node_loc cells destIdx |>) oleft oright :: cs2m) = (length cells + 1)%nat.
  { rewrite length_app /= (cells_repr_length _ _ _ Hcs1m) (cells_repr_length _ _ _ Hcs2m) length_take length_drop. lia. }
  have Hstart : (ytv <| yjs.yText.len' := w64_word_instance.(word.add) ytv.(yjs.yText.len') (W64 1%nat) |>).(yjs.yText.start') = hd'.
  { simpl. exact Hyts. }
  have Hcs1len : length cs1m = destIdx.
  { rewrite (cells_repr_length _ _ _ Hcs1m) length_take_le; [done | rewrite -Hcells_len; exact Hdle]. }
  iApply ("HΦ" $! (cs1m ++ MkItemCell item_l (ivL <| yjs.item.right' := node_loc cells destIdx |>) oleft oright :: cs2m)
            destIdx (MkItemCell item_l (ivL <| yjs.item.right' := node_loc cells destIdx |>) oleft oright)).
  iSplitL "Hparent Hleftdll Hitem Hrightdll2".
  { iExists (ytv <| yjs.yText.len' := w64_word_instance.(word.add) ytv.(yjs.yText.len') (W64 1%nat) |>), tlN.
    iFrame "Hparent".
    iSplitL.
    { rewrite Hstart.
      have HrightEq : (ivL <| yjs.item.right' := node_loc cells destIdx |>).(yjs.item.right') = node_loc cells destIdx by reflexivity.
      have HleftEq : (ivL <| yjs.item.right' := node_loc cells destIdx |>).(yjs.item.left') = node_loc cells (destIdx - 1).
      { simpl. exact HivLl. }
      iApply (is_dll_insert_middle cs1m cs2m (MkItemCell item_l (ivL <| yjs.item.right' := node_loc cells destIdx |>) oleft oright) hd' tlN (node_loc cells (destIdx - 1)) (node_loc cells destIdx) Hitem_nn HleftEq HrightEq).
      simpl. rewrite HivLoL HivLoR. iFrame "Hleftdll Hitem Holeft2 Horight2 Hrightdll2". }
    iPureIntro. split.
    - rewrite /= Hytl Hlen0. word.
    - rewrite Harr''. apply cells_repr_app.
      + apply (cells_repr_m_irrel arr). exact Hcs1m.
      + apply cells_repr_cons; [exact Hcellrepr | apply (cells_repr_m_irrel arr); exact Hcs2m]. }
  iSplit; [iPureIntro; exact Hinv''|].
  iSplit; [iPureIntro; apply list_lookup_middle; by rewrite Hcs1len|].
  iSplit; [iPureIntro; reflexivity|].
  iSplit; [iPureIntro; rewrite /= HivLid Hiv2id; exact Hid|].
  iPureIntro. rewrite /= HivLc Hiv2con. exact Hcontlen.
Qed.

(** Public top-level spec — [Store.Integrate] inserts the item and preserves the
    document invariant. The result [arr'] is the model document with [newItem]
    spliced in at *some* in-bounds position [i] (the position is existential, so
    the conflict-resolution algorithm is not exposed — only the abstract effect
    "the item was inserted somewhere, and the document stays valid"). The
    document invariant [is_valid_ytext] already carries [YjsArrInvariant], so it
    pins [arr'] uniquely given the item set; the caller's item is encapsulated in
    [is_fresh_item]; the document/input side conditions are the only premises.
    Proven from [wp_Store__Integrate_aux]: integration succeeds ([integrate_some]),
    bridges to [setintegrate] ([setintegrate_eq_integrate]); the insertion
    position and the post-state's validity come from the rocq-yjs preservation
    theorem [YjsArrInvariant_integrate]. *)

(** [item_valid_adjacent]: the pure (model-level) heart of the Text.Insert proof.
    An item whose origin / right-origin are two *adjacent* elements of a valid
    document array is [IsItemValid]. [iiv_origin_lt] is immediate from the array
    being sorted ([yai_sorted]); [iiv_reachable] follows from
    [origin_nearest_reachable] plus the fact that nothing in a sorted array lies
    strictly between adjacent elements (the index lemmas). This isolates the only
    hard obligation of an insert into the order theory, so the WP side only has
    to maintain that the chosen left/right neighbours are adjacent. *)
Lemma item_valid_adjacent (arr : list (YjsItem A)) (i : nat) (a b : YjsItem A)
    (newid : YjsId) (c : A) :
  YjsArrInvariant arr ->
  base.lookup i arr = Some a ->
  base.lookup (S i) arr = Some b ->
  IsItemValid (Item (itemPtr a) (itemPtr b) newid c).
Proof.
  intros Hinv Ha Hb.
  destruct a as [oa ra ida ca]. destruct b as [ob rb idb cb].
  pose proof (yai_item_set_inv _ Hinv) as Hisi.
  pose proof (yai_closed _ Hinv) as Hclosed.
  assert (HaIn : ArrSet arr (Item oa ra ida ca)) by exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Ha).
  assert (HbIn : ArrSet arr (Item ob rb idb cb)) by exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Hb).
  assert (Hab : YjsLt' (Item oa ra ida ca) (Item ob rb idb cb))
    by exact (invariant_yjsarray_idx.getElem_lt_YjsLt' arr i (S i) _ _ Hinv Ha Hb ltac:(lia)).
  assert (Hlo : forall p, ArrSet arr p -> YjsLt' p (Item ob rb idb cb) -> YjsLeq' p (Item oa ra ida ca)).
  { intros p Hp Hpb. destruct p as [q | | ].
    - destruct (list_basics.list.list_elem_of_lookup_1 _ _ Hp) as [iq Hiq].
      assert (iq < S i)%nat by exact (findptridx_order2.getElem_YjsLt'_index_lt arr iq (S i) q (Item ob rb idb cb) Hinv Hiq Hb Hpb).
      apply (invariant_yjsarray_idx.getElem_leq_YjsLeq' arr iq i q (Item oa ra ida ca) Hinv Hiq Ha). lia.
    - exact (YjsLeq'_leqLt _ _ (YjsLt'_ltOriginOrder _ _ (lt_first (Item oa ra ida ca)))).
    - exfalso. destruct Hpb as [h Hh]. exact (not_last_lt_ptr Hclosed Hisi h _ HbIn Hh). }
  assert (Hhi : forall p, ArrSet arr p -> YjsLt' (Item oa ra ida ca) p -> YjsLeq' (Item ob rb idb cb) p).
  { intros p Hp Hap. destruct p as [q | | ].
    - destruct (list_basics.list.list_elem_of_lookup_1 _ _ Hp) as [iq Hiq].
      assert (i < iq)%nat by exact (findptridx_order2.getElem_YjsLt'_index_lt arr i iq (Item oa ra ida ca) q Hinv Ha Hiq Hap).
      apply (invariant_yjsarray_idx.getElem_leq_YjsLeq' arr (S i) iq (Item ob rb idb cb) q Hinv Hb Hiq). lia.
    - exfalso. exact (not_ptr_lt'_first Hclosed Hisi _ HaIn Hap).
    - exact (YjsLeq'_leqLt _ _ (YjsLt'_ltOriginOrder _ _ (lt_last (Item ob rb idb cb)))). }
  assert (HF1 : YjsLeq' (Item ob rb idb cb) ra)
    by exact (Hhi ra (closedRight _ Hclosed oa ra ida ca HaIn) (item_lt_rightOrigin (Item oa ra ida ca))).
  assert (HF2 : YjsLeq' ob (Item oa ra ida ca))
    by exact (Hlo ob (closedLeft _ Hclosed ob rb idb cb HbIn) (item_origin_lt (Item ob rb idb cb))).
  apply Build_IsItemValid.
  - exact Hab.
  - intros x Hreach.
    inversion Hreach as [p1 q1 Hstep | p1 q1 r1 Hstep Hrest]; subst.
    + inversion Hstep; subst; [ left | right ]; apply YjsLeq'_leqSame.
    + inversion Hstep; subst.
      * pose proof (reachable_in arr (Item oa ra ida ca) Hclosed x Hrest HaIn) as HxIn.
        pose proof (origin_nearest_reachable (ArrSet arr) Hisi oa ra ca ida x HaIn Hrest) as [Hxoa | Hrax].
        -- left. apply YjsLeq'_leqLt.
           exact (transitivity.yjs_leq'_p_trans1 Hisi x oa (Item oa ra ida ca) HxIn (closedLeft _ Hclosed oa ra ida ca HaIn) HaIn Hclosed Hxoa (item_origin_lt (Item oa ra ida ca))).
        -- right.
           exact (transitivity.yjs_leq'_p_trans Hisi (Item ob rb idb cb) ra x HbIn (closedRight _ Hclosed oa ra ida ca HaIn) HxIn Hclosed HF1 Hrax).
      * pose proof (reachable_in arr (Item ob rb idb cb) Hclosed x Hrest HbIn) as HxIn.
        pose proof (origin_nearest_reachable (ArrSet arr) Hisi ob rb cb idb x HbIn Hrest) as [Hxob | Hrbx].
        -- left.
           exact (transitivity.yjs_leq'_p_trans Hisi x ob (Item oa ra ida ca) HxIn (closedLeft _ Hclosed ob rb idb cb HbIn) HaIn Hclosed Hxob HF2).
        -- right.
           exact (transitivity.yjs_leq'_p_trans Hisi (Item ob rb idb cb) rb x HbIn (closedRight _ Hclosed ob rb idb cb HbIn) HxIn Hclosed (YjsLeq'_leqLt _ _ (item_lt_rightOrigin (Item ob rb idb cb))) Hrbx).
Qed.

(** Boundary variants of [item_valid_adjacent] for the ends of the document:
    inserting before the head ([First] origin), after the tail ([Last]
    right-origin), or into an empty document ([First]/[Last]). *)
Lemma item_valid_empty (newid : YjsId) (c : A) : IsItemValid (Item First Last newid c).
Proof.
  apply Build_IsItemValid.
  - exact (YjsLt'_ltOriginOrder _ _ lt_first_last).
  - intros x Hreach.
    inversion Hreach as [p1 q1 Hstep | p1 q1 r1 Hstep Hrest]; subst.
    + inversion Hstep; subst; [left|right]; apply YjsLeq'_leqSame.
    + exfalso. inversion Hstep; subst; inversion Hrest as [u v Hs | u v w Hs Hr]; inversion Hs.
Qed.

Lemma item_valid_head (arr : list (YjsItem A)) (b : YjsItem A) (newid : YjsId) (c : A) :
  YjsArrInvariant arr -> base.lookup 0%nat arr = Some b ->
  IsItemValid (Item First (itemPtr b) newid c).
Proof.
  intros Hinv Hb. destruct b as [ob rb idb cb].
  pose proof (yai_item_set_inv _ Hinv) as Hisi.
  pose proof (yai_closed _ Hinv) as Hclosed.
  assert (HbIn : ArrSet arr (Item ob rb idb cb)) by exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Hb).
  assert (Hob : ob = First).
  { pose proof (closedLeft _ Hclosed ob rb idb cb HbIn) as Hobin.
    pose proof (item_origin_lt (Item ob rb idb cb)) as Hoblt.
    destruct ob as [q | | ].
    - exfalso. destruct (list_basics.list.list_elem_of_lookup_1 _ _ Hobin) as [iq Hiq].
      assert (iq < 0)%nat by exact (findptridx_order2.getElem_YjsLt'_index_lt arr iq 0 q (Item (itemPtr q) rb idb cb) Hinv Hiq Hb Hoblt). lia.
    - reflexivity.
    - exfalso. destruct Hoblt as [h Hh]. exact (not_last_lt_ptr Hclosed Hisi h _ HbIn Hh). }
  subst ob.
  apply Build_IsItemValid.
  - exact (YjsLt'_ltOriginOrder _ _ (lt_first (Item First rb idb cb))).
  - intros x Hreach.
    inversion Hreach as [p1 q1 Hstep | p1 q1 r1 Hstep Hrest]; subst.
    + inversion Hstep; subst; [left|right]; apply YjsLeq'_leqSame.
    + inversion Hstep; subst.
      * exfalso. inversion Hrest as [u v Hs | u v w Hs Hr]; inversion Hs.
      * pose proof (origin_nearest_reachable (ArrSet arr) Hisi First rb cb idb x HbIn Hrest) as [Hxob | Hrbx].
        -- left. exact Hxob.
        -- right.
           pose proof (reachable_in arr (Item First rb idb cb) Hclosed x Hrest HbIn) as HxIn.
           exact (transitivity.yjs_leq'_p_trans Hisi (Item First rb idb cb) rb x HbIn (closedRight _ Hclosed First rb idb cb HbIn) HxIn Hclosed (YjsLeq'_leqLt _ _ (item_lt_rightOrigin (Item First rb idb cb))) Hrbx).
Qed.

Lemma item_valid_tail (arr : list (YjsItem A)) (a : YjsItem A) (newid : YjsId) (c : A) :
  YjsArrInvariant arr -> base.lookup (length arr - 1)%nat arr = Some a ->
  IsItemValid (Item (itemPtr a) Last newid c).
Proof.
  intros Hinv Ha. destruct a as [oa ra ida ca].
  pose proof (yai_item_set_inv _ Hinv) as Hisi.
  pose proof (yai_closed _ Hinv) as Hclosed.
  assert (HaIn : ArrSet arr (Item oa ra ida ca)) by exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Ha).
  assert (Hra : ra = Last).
  { pose proof (closedRight _ Hclosed oa ra ida ca HaIn) as Hrain.
    pose proof (item_lt_rightOrigin (Item oa ra ida ca)) as Hralt.
    destruct ra as [q | | ].
    - exfalso. destruct (list_basics.list.list_elem_of_lookup_1 _ _ Hrain) as [iq Hiq].
      assert (length arr - 1 < iq)%nat by exact (findptridx_order2.getElem_YjsLt'_index_lt arr (length arr - 1) iq (Item oa (itemPtr q) ida ca) q Hinv Ha Hiq Hralt).
      pose proof (list_basics.list.lookup_lt_Some _ _ _ Hiq) as Hbound. lia.
    - exfalso. exact (not_ptr_lt'_first Hclosed Hisi _ HaIn Hralt).
    - reflexivity. }
  subst ra.
  apply Build_IsItemValid.
  - exact (YjsLt'_ltOriginOrder _ _ (lt_last (Item oa Last ida ca))).
  - intros x Hreach.
    inversion Hreach as [p1 q1 Hstep | p1 q1 r1 Hstep Hrest]; subst.
    + inversion Hstep; subst; [left|right]; apply YjsLeq'_leqSame.
    + inversion Hstep; subst.
      * pose proof (origin_nearest_reachable (ArrSet arr) Hisi oa Last ca ida x HaIn Hrest) as [Hxoa | Hrax].
        -- left.
           pose proof (reachable_in arr (Item oa Last ida ca) Hclosed x Hrest HaIn) as HxIn.
           apply YjsLeq'_leqLt.
           exact (transitivity.yjs_leq'_p_trans1 Hisi x oa (Item oa Last ida ca) HxIn (closedLeft _ Hclosed oa Last ida ca HaIn) HaIn Hclosed Hxoa (item_origin_lt (Item oa Last ida ca))).
        -- right. exact Hrax.
      * exfalso. inversion Hrest as [u v Hs | u v w Hs Hr]; inversion Hs.
Qed.

(** When [newItem]'s left origin is the current tail element [a] of a valid
    [arr] and its right origin is [Last], the integrate insertion index can only
    be the end: [newItem] is greater than every element of [arr] (its origin is
    the maximum), so sortedness of the result forces it last. Hence integrating
    it yields [arr ++ [newItem]]. This keeps the freshly integrated node at the
    DLL tail across [Text.Insert]'s loop iterations. *)
Lemma insert_tail_snoc (arr : list (YjsItem A)) (a newItem : YjsItem A) (i : nat) :
  YjsArrInvariant arr ->
  YjsArrInvariant (insertIdxIfInBounds i newItem arr) ->
  (i <= length arr)%nat ->
  base.lookup (length arr - 1)%nat arr = Some a ->
  origin newItem = itemPtr a ->
  insertIdxIfInBounds i newItem arr = arr ++ [newItem].
Proof.
  intros Hinv Hinv' Hle Ha Horig.
  have Hisi' := yai_item_set_inv _ Hinv'.
  have Hclosed' := yai_closed _ Hinv'.
  assert (Hi : i = length arr).
  2:{ subst i. rewrite /insertIdxIfInBounds decide_True; [|done].
      rewrite take_ge; [|done]. rewrite drop_ge; [|done]. done. }
  destruct (decide (i = length arr)) as [Heq | Hne]; [exact Heq | exfalso].
  have Hlt : (i < length arr)%nat by lia.
  destruct (arr !! i) as [y|] eqn:Hy;
    [| apply lookup_lt_is_Some_2 in Hlt; rewrite Hy in Hlt; by destruct Hlt].
  have Htlen : length (take i arr) = i by rewrite length_take_le; [done | lia].
  have Harr' : insertIdxIfInBounds i newItem arr = take i arr ++ newItem :: drop i arr
    by rewrite /insertIdxIfInBounds decide_True; [done | exact Hle].
  have Hnewi : insertIdxIfInBounds i newItem arr !! i = Some newItem
    by rewrite Harr'; apply list_lookup_middle; rewrite Htlen.
  assert (Hyi1 : insertIdxIfInBounds i newItem arr !! S i = Some y)
    by (rewrite Harr' lookup_app_r; rewrite Htlen;
        [ replace (S i - i)%nat with 1%nat by lia;
          rewrite /= lookup_drop Nat.add_0_r; exact Hy | lia]).
  have HltNewY : YjsLt' newItem y
    by apply (invariant_yjsarray_idx.getElem_lt_YjsLt'
                (insertIdxIfInBounds i newItem arr) i (S i) newItem y Hinv' Hnewi Hyi1); lia.
  have PnewItem : newItem ∈ insertIdxIfInBounds i newItem arr
    by exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Hnewi).
  have Py : y ∈ insertIdxIfInBounds i newItem arr
    by exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Hyi1).
  have HltANew : YjsLt' a newItem by rewrite -Horig; apply item_origin_lt.
  have HltYNew : YjsLt' y newItem.
  { destruct (decide (i = length arr - 1)%nat) as [Hieq | Hilt].
    - rewrite Hieq in Hy. have Hya : y = a by congruence. rewrite Hya; exact HltANew.
    - have HltYA : YjsLt' y a
        by apply (invariant_yjsarray_idx.getElem_lt_YjsLt'
                    arr i (length arr - 1)%nat y a Hinv Hy Ha); lia.
      have HaArr : a ∈ arr by exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Ha).
      have Pa : a ∈ insertIdxIfInBounds i newItem arr
        by apply (proj2 (mem_insertIdxIfInBounds _ _ _ _ Hle)); right; exact HaArr.
      exact (transitivity.yjs_lt_trans Hisi' Hclosed'
               (itemPtr y) (itemPtr a) (itemPtr newItem) Py Pa PnewItem HltYA HltANew). }
  exact (asymmetry.yjs_lt_asymm Hclosed' Hisi'
           (itemPtr y) (itemPtr newItem) Py PnewItem HltYNew HltNewY).
Qed.

(** General placement: if [newItem] is order-bounded by position [p] of the
    valid [arr] (everything strictly before [p] is [<yjs newItem], everything
    from [p] on is [>yjs newItem]), then integrate places it at exactly [p].
    This generalises [insert_tail_snoc] (the [p = length arr] case) to head /
    middle insertion, which is what a non-tail [Text.Insert] needs. The two
    order bounds are discharged in the WP loop from the new item's origin /
    right-origin being the neighbours straddling position [p]. *)
Lemma insert_at_pos (arr : list (YjsItem A)) (newItem : YjsItem A) (i p : nat) :
  YjsArrInvariant arr ->
  YjsArrInvariant (insertIdxIfInBounds i newItem arr) ->
  (i <= length arr)%nat ->
  (p <= length arr)%nat ->
  (forall k (a : YjsItem A), (k < p)%nat -> base.lookup k arr = Some a -> YjsLt' a newItem) ->
  (forall k (b : YjsItem A), (p <= k)%nat -> (k < length arr)%nat -> base.lookup k arr = Some b -> YjsLt' newItem b) ->
  insertIdxIfInBounds i newItem arr = take p arr ++ newItem :: drop p arr.
Proof.
  intros Hinv Hinv' Hile Hp Hleft Hright.
  have Hisi' := yai_item_set_inv _ Hinv'.
  have Hclosed' := yai_closed _ Hinv'.
  have Harr' : insertIdxIfInBounds i newItem arr = take i arr ++ newItem :: drop i arr
    by rewrite /insertIdxIfInBounds decide_True; [done | exact Hile].
  have Htlen : length (take i arr) = i by rewrite length_take_le; [done | exact Hile].
  have Hnewi : insertIdxIfInBounds i newItem arr !! i = Some newItem
    by rewrite Harr'; apply list_lookup_middle; rewrite Htlen.
  have PnewItem : newItem ∈ insertIdxIfInBounds i newItem arr
    by exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Hnewi).
  have Hi : i = p.
  { destruct (Nat.lt_trichotomy i p) as [Hlt | [Heq | Hgt]].
    - exfalso.
      have HilenA : (i < length arr)%nat by lia.
      destruct (arr !! i) as [a|] eqn:Ha; [| apply lookup_lt_is_Some_2 in HilenA; rewrite Ha in HilenA; by destruct HilenA].
      have HaLt : YjsLt' a newItem by exact (Hleft i a Hlt Ha).
      have Hai : insertIdxIfInBounds i newItem arr !! S i = Some a.
      { rewrite Harr' lookup_app_r; rewrite Htlen;
        [ replace (S i - i)%nat with 1%nat by lia; rewrite /= lookup_drop Nat.add_0_r; exact Ha | lia]. }
      have Pa : a ∈ insertIdxIfInBounds i newItem arr by exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Hai).
      have HltNewA : YjsLt' newItem a
        by apply (invariant_yjsarray_idx.getElem_lt_YjsLt' (insertIdxIfInBounds i newItem arr) i (S i) newItem a Hinv' Hnewi Hai); lia.
      exact (asymmetry.yjs_lt_asymm Hclosed' Hisi' (itemPtr a) (itemPtr newItem) Pa PnewItem HaLt HltNewA).
    - exact Heq.
    - exfalso.
      have HplenB : (p < length arr)%nat by lia.
      destruct (arr !! p) as [b|] eqn:Hb; [| apply lookup_lt_is_Some_2 in HplenB; rewrite Hb in HplenB; by destruct HplenB].
      have HbGt : YjsLt' newItem b by exact (Hright p b (Nat.le_refl p) HplenB Hb).
      have Hbp : insertIdxIfInBounds i newItem arr !! p = Some b.
      { rewrite Harr' lookup_app_l; [| rewrite Htlen; lia]. rewrite lookup_take_lt; [exact Hb | lia]. }
      have Pb : b ∈ insertIdxIfInBounds i newItem arr by exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Hbp).
      have HltBNew : YjsLt' b newItem
        by apply (invariant_yjsarray_idx.getElem_lt_YjsLt' (insertIdxIfInBounds i newItem arr) p i b newItem Hinv' Hbp Hnewi); lia.
      exact (asymmetry.yjs_lt_asymm Hclosed' Hisi' (itemPtr newItem) (itemPtr b) PnewItem Pb HbGt HltBNew). }
  subst p. exact Harr'.
Qed.

(** Unified validity for an insert straddling position [p]: the new item's
    origin is either [First] (at the head, [p = 0]) or the element at [p-1], and
    its right-origin is either [Last] (at the tail, [p = length arr]) or the
    element at [p]. Dispatches to the four boundary lemmas. This is what a
    general [Text.Insert] needs: the loop only has to know the [findPos]
    neighbours straddle [p]. *)
Lemma item_valid_at (arr : list (YjsItem A)) (p : nat) (newid : YjsId) (c : A) (o r : YjsPtr A) :
  YjsArrInvariant arr ->
  (p = 0%nat /\ o = First \/ (1 <= p)%nat /\ ∃ a, base.lookup (p-1)%nat arr = Some a /\ o = itemPtr a) ->
  (p = length arr /\ r = Last \/ ∃ b, base.lookup p arr = Some b /\ r = itemPtr b) ->
  IsItemValid (Item o r newid c).
Proof.
  intros Hinv Hleft Hright.
  destruct Hleft as [[Hp0 ->] | [Hp1 [a [Ha ->]]]].
  - destruct Hright as [[Hplen ->] | [b [Hb ->]]].
    + exact (item_valid_empty newid c).
    + subst p. exact (item_valid_head arr b newid c Hinv Hb).
  - destruct Hright as [[Hplen ->] | [b [Hb ->]]].
    + subst p. exact (item_valid_tail arr a newid c Hinv Ha).
    + have Hb' : base.lookup (S (p-1)) arr = Some b by (replace (S (p-1)) with p by lia; exact Hb).
      exact (item_valid_adjacent arr (p-1) a b newid c Hinv Ha Hb').
Qed.

(** Companion placement for [item_valid_at]: integrate places the straddling
    item at exactly [p] ([take p arr ++ nit :: drop p arr]). Discharges the two
    order bounds of [insert_at_pos] from the origin / right-origin being the
    [p-1] / [p] neighbours (boundary cases [First] / [Last] make a bound
    vacuous). *)
Lemma insert_straddle (arr : list (YjsItem A)) (nit : YjsItem A) (i p : nat) :
  YjsArrInvariant arr ->
  YjsArrInvariant (insertIdxIfInBounds i nit arr) ->
  (i <= length arr)%nat -> (p <= length arr)%nat ->
  (p = 0%nat /\ origin nit = First \/ (1 <= p)%nat /\ ∃ a, base.lookup (p-1)%nat arr = Some a /\ origin nit = itemPtr a) ->
  (p = length arr /\ rightOrigin nit = Last \/ ∃ b, base.lookup p arr = Some b /\ rightOrigin nit = itemPtr b) ->
  insertIdxIfInBounds i nit arr = take p arr ++ nit :: drop p arr.
Proof.
  intros Hinv Hinv' Hile Hple Hleft Hright.
  have Hisi' := yai_item_set_inv _ Hinv'.
  have Hclosed' := yai_closed _ Hinv'.
  have Pnit : nit ∈ insertIdxIfInBounds i nit arr by (apply (proj2 (mem_insertIdxIfInBounds _ _ _ _ Hile)); left; reflexivity).
  apply (insert_at_pos arr nit i p Hinv Hinv' Hile Hple).
  - intros k a Hk Hak.
    destruct Hleft as [[Hp0 _] | [Hp1 [a0 [Ha0 Horig]]]]; [exfalso; lia |].
    have Ha0nit : YjsLt' a0 nit by (rewrite -Horig; apply item_origin_lt).
    destruct (decide (k = (p - 1)%nat)) as [Hkeq | Hne].
    + rewrite Hkeq Ha0 in Hak. injection Hak as ->. exact Ha0nit.
    + have Hka0 : YjsLt' a a0 by (apply (invariant_yjsarray_idx.getElem_lt_YjsLt' arr k (p-1)%nat a a0 Hinv Hak Ha0); lia).
      have Pa : a ∈ insertIdxIfInBounds i nit arr by (apply (proj2 (mem_insertIdxIfInBounds _ _ _ _ Hile)); right; exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Hak)).
      have Pa0 : a0 ∈ insertIdxIfInBounds i nit arr by (apply (proj2 (mem_insertIdxIfInBounds _ _ _ _ Hile)); right; exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Ha0)).
      exact (transitivity.yjs_lt_trans Hisi' Hclosed' (itemPtr a) (itemPtr a0) (itemPtr nit) Pa Pa0 Pnit Hka0 Ha0nit).
  - intros k b Hk1 Hk2 Hbk.
    destruct Hright as [[Hplen _] | [b0 [Hb0 Horigr]]]; [exfalso; lia |].
    have Hnitb0 : YjsLt' nit b0 by (rewrite -Horigr; apply item_lt_rightOrigin).
    destruct (decide (k = p)) as [Hkeq | Hne].
    + rewrite Hkeq Hb0 in Hbk. injection Hbk as ->. exact Hnitb0.
    + have Hb0b : YjsLt' b0 b by (apply (invariant_yjsarray_idx.getElem_lt_YjsLt' arr p k b0 b Hinv Hb0 Hbk); lia).
      have Pb : b ∈ insertIdxIfInBounds i nit arr by (apply (proj2 (mem_insertIdxIfInBounds _ _ _ _ Hile)); right; exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Hbk)).
      have Pb0 : b0 ∈ insertIdxIfInBounds i nit arr by (apply (proj2 (mem_insertIdxIfInBounds _ _ _ _ Hile)); right; exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Hb0)).
      exact (transitivity.yjs_lt_trans Hisi' Hclosed' (itemPtr nit) (itemPtr b0) (itemPtr b) Pnit Pb0 Pb Hnitb0 Hb0b).
Qed.

(** In a valid (id-unique) array, [find_by_id] of an element's own id returns
    that element. The reverse of [cells_repr]: locates a model item by id. *)
Lemma find_by_id_self (arr : list (YjsItem A)) (a : YjsItem A) :
  YjsArrInvariant arr -> a ∈ arr -> find_by_id (item_id a) arr = Some a.
Proof.
  intros Hinv Hin. rewrite /find_by_id.
  destruct (list_find (λ item : YjsItem A, item_id item = item_id a) arr) as [[i y]|] eqn:Hlf; last first.
  { exfalso. destruct (list_find_elem_of (λ item : YjsItem A, item_id item = item_id a) arr a Hin eq_refl) as [r Hr]. rewrite Hlf in Hr. done. }
  apply list_find_Some in Hlf as (Hyi & Hpy & _).
  have HyIn : y ∈ arr by exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Hyi).
  have Hya : y = a by exact (id_unique (ArrSet arr) (yai_item_set_inv _ Hinv) y a Hpy HyIn Hin).
  rewrite /= Hya //.
Qed.

(** Companion to [item_valid_at] on the model side: [toItem] resolves the
    straddling input to the [Item] with origins [o]/[r], given each origin id is
    either absent (boundary) or the id of the named neighbour. *)
Lemma toItem_at (arr : list (YjsItem A)) (newid : YjsId) (cont : A) (o r : YjsPtr A)
    (oL oR : option YjsId) :
  YjsArrInvariant arr ->
  (oL = None /\ o = First \/ ∃ a, oL = Some (item_id a) /\ a ∈ arr /\ o = itemPtr a) ->
  (oR = None /\ r = Last \/ ∃ b, oR = Some (item_id b) /\ b ∈ arr /\ r = itemPtr b) ->
  toItem (MkIntegrateInput oL oR cont newid) arr = Some (Item o r newid cont).
Proof.
  intros Hinv Hleft Hright. rewrite /toItem /=.
  destruct Hleft as [[-> ->] | [a [-> [Ha ->]]]].
  - destruct Hright as [[-> ->] | [b [-> [Hb ->]]]].
    + reflexivity.
    + rewrite (find_by_id_self arr b Hinv Hb) /=. reflexivity.
  - rewrite (find_by_id_self arr a Hinv Ha) /=.
    destruct Hright as [[-> ->] | [b [-> [Hb ->]]]].
    + reflexivity.
    + rewrite (find_by_id_self arr b Hinv Hb) /=. reflexivity.
Qed.

Lemma wp_Store__Integrate (s parent item_l : loc) (arr : list (YjsItem A))
    (input : IntegrateInput (A := A)) (newItem : YjsItem A) :
  toItem input arr = Some newItem ->
  IsItemValid newItem ->
  maximalId newItem arr ->
  {{{ is_pkg_init yjs ∗ is_valid_ytext parent arr ∗ is_fresh_item item_l input }}}
    s @! (go.PointerType yjs.store) @! "Integrate" #parent #item_l
  {{{ (arr' : list (YjsItem A)) (i : nat) (cells' : list item_cell) (c : item_cell), RET #();
      ⌜(i <= length arr)%nat⌝ ∗ ⌜arr' = insertIdxIfInBounds i newItem arr⌝ ∗
      ⌜YjsArrInvariant arr'⌝ ∗ is_ytext parent cells' arr' ∗
      ∃ idx, ⌜cells' !! idx = Some c⌝ ∗ ⌜ic_loc c = item_l⌝ ∗
             ⌜toYjsId (ic_val c).(yjs.item.id') = in_id input⌝ ∗
             ⌜length ((ic_val c).(yjs.item.content').(yjs.content.content')) = 1%nat⌝ }}}.
Proof using All.
  move=> Htoitem Hvalid Hmax.
  iIntros (Φ) "(Hpkg & Hvalid & Hfresh) HΦ".
  iDestruct "Hfresh" as (iv oleft oright) "(Hraw & %Hfl & %Hfr & %Hflags & %Hcontlen)".
  iDestruct "Hvalid" as (cells) "[Htext %Hinv]".
  destruct (integrate_some input arr newItem Hinv Htoitem) as [arr' Hintegrate].
  destruct (YjsArrInvariant_integrate input arr arr' newItem Hinv Htoitem Hvalid Hmax Hintegrate)
    as [i [Hile [Harr'eq _]]].
  have Hsi : setintegrate input arr = Some arr'.
  { rewrite (setintegrate_eq_integrate input arr newItem Hinv Htoitem Hvalid Hmax). exact Hintegrate. }
  wp_apply (wp_Store__Integrate_aux s parent item_l arr arr' input newItem iv oleft oright
              Hinv Htoitem Hvalid Hmax Hfl Hfr Hflags Hcontlen Hsi with "[$Hpkg $Hraw Htext]").
  { iExists cells. iFrame "Htext". iPureIntro. exact Hinv. }
  iIntros (cells' idx c) "(Htext' & %Hinv' & %Hlook & %Hloc & %Hcid & %Hclen1)".
  iApply ("HΦ" $! arr' i cells' c). iFrame "Htext'".
  iPureIntro. split_and!; [exact Hile | exact Harr'eq | exact Hinv' |].
  exists idx. split_and!; [exact Hlook | exact Hloc | exact Hcid | exact Hclen1].
Qed.

(* ===== Text.Insert: WP proof ============================================ *)

(** The document invariant seen by Text.Insert: the heap Text/Doc/store structs,
    the validity of the target sequence, and the counter invariant that makes
    each generated id maximal (every same-client clock in [arr] is below the
    Doc clock [k], so a fresh item at clock [k] satisfies [maximalId]). *)
Definition own_insert_doc (t : loc) (arr : list (YjsItem A)) (cl k : w64) : iProp Σ :=
  ∃ (tv : yjs.Text.t) (dv : yjs.Doc.t) (sv : yjs.store.t),
    "Ht" ∷ t ↦ tv ∗
    "Hdoc" ∷ tv.(yjs.Text.doc') ↦ dv ∗
    "Hstore" ∷ dv.(yjs.Doc.store') ↦ sv ∗
    "%Hcl" ∷ ⌜sv.(yjs.store.client') = cl⌝ ∗
    "%Hk" ∷ ⌜dv.(yjs.Doc.clock') = k⌝ ∗
    "Hvalid" ∷ is_valid_ytext (tv.(yjs.Text.inner')) arr ∗
    "%Hmax" ∷ ⌜forall x, ArrSet arr (itemPtr x) ->
                 clientId (item_id x) = uint.nat cl ->
                 (clock (item_id x) < uint.nat k)%nat⌝.

(** findPos on an empty sequence returns (null, null) without reading any flags
    (both loops have an empty list to walk). *)
Lemma wp_yText__findPos_empty (parent : loc) (idx : w64) :
  {{{ is_pkg_init yjs ∗ is_ytext parent [] [] }}}
    parent @! (go.PointerType yjs.yText) @! "findPos" #idx
  {{{ RET (#null, #null); is_ytext parent [] [] }}}.
Proof.
  wp_start as "Hyt". iNamed "Hyt".
  iDestruct "Hdll" as %[Hstart Htl].
  wp_auto. rewrite Hstart.
  (* skip-deleted loop: right = null, so the condition is false on entry *)
  iAssert (
    "Hp" ∷ parent ↦ yt ∗ "Hl" ∷ left_ptr ↦ null ∗
    "Hr" ∷ right_ptr ↦ null ∗ "Hidx" ∷ index_ptr ↦ idx
  )%I with "[Hparent left right index]" as "IH".
  { iFrame. }
  wp_for "IH".
  (* count loop: right = null, so the condition is false on entry *)
  iAssert (
    "Hp" ∷ parent ↦ yt ∗ "Hl" ∷ left_ptr ↦ null ∗
    "Hr" ∷ right_ptr ↦ null ∗ "Hrem" ∷ remaining_ptr ↦ idx
  )%I with "[Hp Hl Hr remaining]" as "IH".
  { iFrame. }
  wp_for "IH".
  wp_if_destruct.
  - wp_auto. iApply "HΦ". iExists yt, null. iFrame "Hp". simpl. iPureIntro.
    split_and!; [exact Hstart | reflexivity | exact Hlen | exact Hrepr].
  - iApply "HΦ". iExists yt, null. iFrame "Hp". simpl. iPureIntro.
    split_and!; [exact Hstart | reflexivity | exact Hlen | exact Hrepr].
Qed.

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

(** General [findPos]: walk to the visible character index [idx] (≤ number of
    nodes) and return the straddling neighbours. Since the goose model has no
    deletions (every cell is Countable / non-Deleted / [Len = 1], pinned by
    [cell_repr]), the skip-deleted loop is a no-op and the count loop advances
    one node per unit of [idx]; the result is the node just before / at position
    [idx]. The two returned locations are uniform via [node_loc] (which is [null]
    out of range), so [idx = 0] gives [left = null] and [idx = length] gives
    [right = null]. *)
Lemma wp_yText__findPos (parent : loc) (cells : list item_cell)
    (arr : list (YjsItem A)) (idx : w64) :
  (uint.nat idx <= length cells)%nat ->
  {{{ is_pkg_init yjs ∗ is_ytext parent cells arr }}}
    parent @! (go.PointerType yjs.yText) @! "findPos" #idx
  {{{ (lft rgt : loc), RET (#lft, #rgt);
      is_ytext parent cells arr ∗
      ⌜lft = node_loc cells (Z.of_nat (uint.nat idx) - 1)⌝ ∗
      ⌜rgt = node_loc cells (Z.of_nat (uint.nat idx))⌝ }}}.
Proof.
  iIntros (Hbound). wp_start as "Hyt". iNamed "Hyt".
  iDestruct (is_dll_head_node cells _ tl with "Hdll") as %Hhead.
  destruct cells as [|c0 cs].
  - (* empty document: both loops are no-ops, return (null, null) *)
    iDestruct "Hdll" as %[Hs Ht]. wp_auto. rewrite Hs.
    iAssert ("Hp" ∷ parent ↦ yt ∗ "Hl" ∷ left_ptr ↦ null ∗ "Hr" ∷ right_ptr ↦ null ∗ "Hidx" ∷ index_ptr ↦ idx)%I
      with "[Hparent left right index]" as "IH".
    { iFrame. }
    wp_for "IH".
    iAssert ("Hp" ∷ parent ↦ yt ∗ "Hl" ∷ left_ptr ↦ null ∗ "Hr" ∷ right_ptr ↦ null ∗ "Hrem" ∷ remaining_ptr ↦ idx)%I
      with "[Hp Hl Hr remaining]" as "IH".
    { iFrame. }
    wp_for "IH".
    wp_if_destruct.
    + wp_auto. iApply ("HΦ" $! null null). iSplitL "Hp".
      { iExists yt, null. iFrame "Hp". iPureIntro. split_and!; [exact Hs | reflexivity | exact Hlen | exact Hrepr]. }
      iPureIntro. split; rewrite /node_loc; case_decide; reflexivity.
    + iApply ("HΦ" $! null null). iSplitL "Hp".
      { iExists yt, null. iFrame "Hp". iPureIntro. split_and!; [exact Hs | reflexivity | exact Hlen | exact Hrepr]. }
      iPureIntro. split; rewrite /node_loc; case_decide; reflexivity.
  - (* non-empty: skip-deleted loop reads node 0 (not deleted), count loop walks idx nodes *)
    have Hc0 : (c0 :: cs) !! 0%nat = Some c0 by reflexivity.
    have Hposlen : (uint.nat idx <= length (c0 :: cs))%nat := Hbound.
    wp_auto.
    iDestruct (node_loc_lt_not_null (c0 :: cs) _ tl 0%nat ltac:(simpl; lia) with "Hdll") as "[%Hnn0 Hdll]".
    have Hstartnn : yt.(yjs.yText.start') ≠ null by (rewrite Hhead; exact Hnn0).
    iAssert ("Hp" ∷ parent ↦ yt ∗ "Hdll" ∷ is_dll yt.(yjs.yText.start') tl null null (c0 :: cs) ∗ "Hindex" ∷ index_ptr ↦ idx ∗ "Hleftp" ∷ left_ptr ↦ null ∗ "Hrightp" ∷ right_ptr ↦ yt.(yjs.yText.start'))%I
      with "[Hparent Hdll index left right]" as "IH".
    { iFrame. }
    wp_for "IH".
    rewrite (bool_decide_eq_false_2 (yt.(yjs.yText.start') = null) Hstartnn). simpl negb.
    have Hstart_c0 : yt.(yjs.yText.start') = ic_loc c0 by (rewrite Hhead /node_loc /=; reflexivity).
    have [yi0 [Hyi0 Hcr0]] := cells_repr_lookup arr (c0 :: cs) arr 0%nat c0 Hrepr Hc0.
    have Hflags0 : (ic_val c0).(yjs.item.flags') = W8 2 := proj1 (proj2 (proj2 (proj2 (proj2 Hcr0)))).
    iDestruct (is_dll_acc (c0 :: cs) yt.(yjs.yText.start') tl 0%nat c0 Hc0 with "Hdll") as "H". iNamed "H".
    iEval (rewrite Hstart_c0) in "Hrightp".
    wp_auto.
    wp_apply (wp_item__Deleted c0.(ic_loc) c0.(ic_val) Hflags0 with "[$Hcval]"). iIntros "Hcval".
    rewrite decide_False; [| done]. rewrite decide_True; [| done].
    iDestruct ("Hback" with "Hcval") as "Hdll".
    wp_auto.
    iAssert (∃ (j : nat) (lloc rloc : loc), "Hp" ∷ parent ↦ yt ∗ "Hdll" ∷ is_dll yt.(yjs.yText.start') tl null null (c0 :: cs) ∗ "Hleftp" ∷ left_ptr ↦ lloc ∗ "Hrightp" ∷ right_ptr ↦ rloc ∗ "Hrem" ∷ remaining_ptr ↦ W64 (uint.Z idx - Z.of_nat j) ∗ "%Hlloc" ∷ ⌜lloc = node_loc (c0 :: cs) (Z.of_nat j - 1)⌝ ∗ "%Hrloc" ∷ ⌜rloc = node_loc (c0 :: cs) (Z.of_nat j)⌝ ∗ "%Hj" ∷ ⌜(j <= uint.nat idx)%nat⌝)%I
      with "[Hp Hdll Hleftp Hrightp remaining]" as "IH".
    { iExists 0%nat, null, c0.(ic_loc). iFrame "Hp Hdll Hleftp Hrightp".
      replace (W64 (uint.Z idx - Z.of_nat 0)) with idx by word. iFrame "remaining".
      iPureIntro. split_and!.
      - rewrite /node_loc. case_decide; [lia | reflexivity].
      - rewrite Hcloc //.
      - lia. }
    wp_for "IH".
    have Hidxj : uint.Z (W64 (uint.Z idx - Z.of_nat j)) = uint.Z idx - Z.of_nat j by word.
    case_bool_decide as Hlt.
    + (* j < idx: read node j (indexable, len 1), advance left/right *)
      have Hjpos : (j < uint.nat idx)%nat by (rewrite Hidxj in Hlt; word).
      have Hjlt : (j < length (c0 :: cs))%nat by lia.
      destruct ((c0 :: cs) !! j) as [cj|] eqn:Hcj; [| apply lookup_ge_None in Hcj; lia].
      have [yij [Hyij Hcrj]] := cells_repr_lookup arr (c0 :: cs) arr j cj Hrepr Hcj.
      have Hflagsj : (ic_val cj).(yjs.item.flags') = W8 2 := proj1 (proj2 (proj2 (proj2 (proj2 Hcrj)))).
      have Hcontlenj : length ((ic_val cj).(yjs.item.content').(yjs.content.content')) = 1%nat := proj2 (proj2 (proj2 (proj2 (proj2 Hcrj)))).
      iDestruct (is_dll_acc (c0 :: cs) yt.(yjs.yText.start') tl j cj Hcj with "Hdll") as "Hacc".
      iDestruct "Hacc" as "(%Hcjloc & %Hcjl & %Hcjr & Hcjval & Hcjol & Hcjor & Hback)".
      have Hrlocj : rloc = cj.(ic_loc) by rewrite Hrloc Hcjloc.
      iDestruct (typed_pointsto_not_null with "Hcjval") as %Hcjnn.
      iEval (rewrite Hrlocj) in "Hrightp".
      wp_auto.
      rewrite (bool_decide_eq_false_2 (cj.(ic_loc) = null) Hcjnn). simpl negb.
      rewrite decide_True; [| done]. wp_auto.
      wp_apply (wp_item__Indexable cj.(ic_loc) cj.(ic_val) Hflagsj with "[$Hcjval]"). iIntros "Hcjval".
      wp_auto.
      wp_apply (wp_item__Len cj.(ic_loc) cj.(ic_val) with "[$Hcjval]"). iIntros "Hcjval".
      rewrite Hcontlenj. wp_auto.
      wp_for_post.
      iDestruct ("Hback" with "Hcjval") as "Hdll".
      iFrame "HΦ Hcol Hcor".
      iExists (S j), cj.(ic_loc), (cj.(ic_val).(yjs.item.right')).
      iFrame "Hp Hdll Hleftp Hrightp".
      replace (w64_word_instance.(word.sub) (W64 (uint.Z idx - Z.of_nat j)) (W64 1%nat)) with (W64 (uint.Z idx - Z.of_nat (S j))) by word.
      iFrame "Hrem".
      iPureIntro. split_and!.
      * rewrite Hcjloc. f_equal. lia.
      * rewrite Hcjr. f_equal. lia.
      * lia.
    + (* j = idx: loop exits, return (left, right) at positions idx-1, idx *)
      have Hjeq : j = uint.nat idx by (rewrite Hidxj in Hlt; word).
      wp_auto.
      rewrite decide_False; [| done]. rewrite decide_True; [| done]. wp_auto.
      iApply ("HΦ" $! lloc rloc).
      iSplitL "Hp Hdll".
      { iExists yt, tl. iFrame "Hp Hdll". iPureIntro. split; [exact Hlen | exact Hrepr]. }
      iPureIntro. split; [ rewrite Hlloc Hjeq // | rewrite Hrloc Hjeq // ].
Qed.

(** Text.Insert at an arbitrary visible index preserves the document invariant.
    [findPos] locates the straddling neighbours; the per-character loop integrates
    one 1-char item per byte, chaining each new item's left origin to the previous
    one while sharing the fixed right origin. Validity of each integrate is
    [item_valid_at] (head / middle / tail / empty by which neighbours exist) and
    its placement is [insert_straddle], which keeps the inserted run between the
    neighbours so the loop's left/right tracking is maintained. *)
Lemma wp_Text__Insert (t : loc) (cl k idx : w64) (content : go_string) (arr0 : list (YjsItem A)) :
  (uint.Z k + Z.of_nat (length content) < 2 ^ 63)%Z ->
  {{{ is_pkg_init yjs ∗ own_insert_doc t arr0 cl k }}}
    t @! (go.PointerType yjs.Text) @! "Insert" #idx #content
  {{{ (arr' : list (YjsItem A)) (k' : w64), RET #(); own_insert_doc t arr' cl k' }}}.
Proof.
  intros Hovf.
  wp_start as "Hown". iNamed "Hown".
  iDestruct "Hvalid" as (cells0) "[Hyt %Hinv0]". iNamed "Hyt".
  iDestruct "Htext" as (yt0 tl0) "(Hparent & Hdll & %Hlen & %Hrepr)".
  wp_auto.
  case_bool_decide as Hcond.
  { wp_auto.
    iAssert (is_ytext tv.(yjs.Text.inner') cells0 arr0) with "[Hparent Hdll]" as "Hyt".
    { iExists yt0, tl0. iFrame "Hparent Hdll". iPureIntro. split; [exact Hlen | exact Hrepr]. }
    iAssert (is_valid_ytext tv.(yjs.Text.inner') arr0) with "[Hyt]" as "Hvalid".
    { iExists cells0. iFrame "Hyt". iPureIntro. exact Hinv0. }
    iApply ("HΦ" $! arr0 k). iExists tv, dv, sv. iFrame "Ht Hdoc Hstore Hvalid".
    iPureIntro. split_and!; [exact Hcl | exact Hk | exact Hmax]. }
  rewrite Hlen in Hcond.
  have Hposle : (uint.nat idx <= length cells0)%nat by word.
  wp_auto.
  iAssert (is_ytext tv.(yjs.Text.inner') cells0 arr0) with "[Hparent Hdll]" as "Htext".
  { iExists yt0, tl0. iFrame "Hparent Hdll". iPureIntro. split; [exact Hlen | exact Hrepr]. }
  wp_apply (wp_yText__findPos (tv.(yjs.Text.inner')) cells0 arr0 idx Hposle with "[$Htext]").
  iIntros (lft rgt) "(Htext & %Hlftloc & %Hrgtloc)".
  wp_auto.
  wp_if_join (λ v : val, ⌜v = execute_val⌝ ∗ ∃ (oRptr : loc) (in_rO : option yjs.id.t),
      "HoR" ∷ originRightId_ptr ↦ oRptr ∗ "HisR" ∷ is_origin_id oRptr in_rO ∗
      "Htext" ∷ is_ytext tv.(yjs.Text.inner') cells0 arr0 ∗ "Hright" ∷ right_ptr ↦ rgt ∗
      "%Hrightinit" ∷ ⌜(in_rO = None ∧ (uint.nat idx = length cells0)%nat) ∨
        (∃ (ri : YjsItem A) (rid : yjs.id.t), arr0 !! (uint.nat idx) = Some ri ∧ in_rO = Some rid ∧ item_id ri = toYjsId rid)⌝)%I
      with "[right Htext originRightId]".
  { iDestruct "Htext" as (yt1 tl1) "(Hpar1 & Hdll1 & %Hlen1 & %Hrepr1)".
    iSplitR; [done|].
    destruct (decide (uint.nat idx = length cells0)%nat) as [Hpeq|Hne];
    [ iExists null, None; iFrame "originRightId right";
      (iSplitR "Hpar1 Hdll1"; [by rewrite /is_origin_id |]);
      (iSplitL "Hpar1 Hdll1"; [ iExists yt1, tl1; iFrame "Hpar1 Hdll1"; iPureIntro; split; [exact Hlen1 | exact Hrepr1] |]);
      iPureIntro; left; split; [reflexivity | exact Hpeq]
    | have Hlt : (uint.nat idx < length cells0)%nat by lia;
      iDestruct (node_loc_lt_not_null cells0 yt1.(yjs.yText.start') tl1 (uint.nat idx) Hlt with "Hdll1") as "[%Hnn _]";
      exfalso; exact (Hnn e) ].
    iDestruct (node_loc_lt_not_null cells0 yt1.(yjs.yText.start') tl1 (uint.nat idx) Hlt with "Hdll1") as "[%Hnn _]".
    exfalso; exact (Hnn e). }
  { iDestruct "Htext" as (yt1 tl1) "(Hpar1 & Hdll1 & %Hlen1 & %Hrepr1)".
    have Hposlt : (uint.nat idx < length cells0)%nat.
    { destruct (decide (uint.nat idx < length cells0)%nat) as [Hlt|Hge]; [exact Hlt|exfalso].
      apply n. rewrite /node_loc decide_True; [|lia].
      have Hpe : (uint.nat idx = length cells0)%nat by lia.
      rewrite Hpe Nat2Z.id lookup_ge_None_2; [done|lia]. }
    destruct (cells0 !! uint.nat idx) as [c0|] eqn:Hc0; [| apply lookup_ge_None in Hc0; lia].
    have [yi0 [Hyi0 Hcr0]] := cells_repr_lookup arr0 cells0 arr0 (uint.nat idx) c0 Hrepr1 Hc0.
    iDestruct (is_dll_acc cells0 yt1.(yjs.yText.start') tl1 (uint.nat idx) c0 Hc0 with "Hdll1") as "Hacc". iNamed "Hacc".
    iEval (rewrite Hcloc) in "Hcval".
    wp_load. wp_pures. wp_store.
    iDestruct (typed_pointsto_not_null with "rid") as %Hridnn.
    iPersist "rid".
    wp_auto.
    iEval (rewrite -Hcloc) in "Hcval".
    iDestruct ("Hback" with "Hcval") as "Hdll1".
    iSplitR; [done|].
    iExists rid_ptr, (Some c0.(ic_val).(yjs.item.id')).
    iFrame "originRightId right".
    iSplitR "Hpar1 Hdll1".
    { rewrite /is_origin_id. iSplit; [iPureIntro; exact Hridnn | iFrame "rid"]. }
    iSplitL "Hpar1 Hdll1".
    { iExists yt1, tl1. iFrame "Hpar1 Hdll1". iPureIntro. split; [exact Hlen1 | exact Hrepr1]. }
    iPureIntro. right. exists yi0, c0.(ic_val).(yjs.item.id'). split_and!; [exact Hyi0 | reflexivity | exact (proj1 Hcr0)]. }
  iIntros (v) "[%Hv HQ]". subst v. iNamed "HQ". wp_auto.
  iEval (rewrite Hcl) in "client".
  iAssert (∃ (j : nat) (arr : list (YjsItem A)) (cells : list item_cell) (leftloc : loc) (dvj : yjs.Doc.t),
    "Hi" ∷ i_ptr ↦ W64 j ∗
    "Htptr0" ∷ t_ptr ↦ t ∗
    "Hcontent" ∷ content_ptr ↦ content ∗
    "Hclient" ∷ client_ptr ↦ cl ∗
    "HoRk" ∷ originRightId_ptr ↦ oRptr ∗
    "Hleftp" ∷ left_ptr ↦ leftloc ∗
    "Htv" ∷ t ↦ tv ∗
    "Hdocj" ∷ tv.(yjs.Text.doc') ↦ dvj ∗
    "Hstorej" ∷ dv.(yjs.Doc.store') ↦ sv ∗
    "Htextj" ∷ is_ytext tv.(yjs.Text.inner') cells arr ∗
    "%Hdvstore" ∷ ⌜dvj.(yjs.Doc.store') = dv.(yjs.Doc.store')⌝ ∗
    "%Hdvclock" ∷ ⌜dvj.(yjs.Doc.clock') = W64 (uint.Z k + j)⌝ ∗
    "%Hinvj" ∷ ⌜YjsArrInvariant arr⌝ ∗
    "%Hlenarr" ∷ ⌜length arr = (length arr0 + j)%nat⌝ ∗
    "%Hjle" ∷ ⌜(j <= length content)%nat⌝ ∗
    "%Hctr" ∷ ⌜∀ x : YjsItem A, ArrSet arr (itemPtr x) → clientId (item_id x) = uint.nat cl → (clock (item_id x) < uint.nat k + j)%nat⌝ ∗
    "%Hleftj" ∷ ⌜(leftloc = null ∧ (uint.nat idx + j = 0)%nat)
      ∨ (∃ (lc : item_cell) (li : YjsItem A),
           cells !! (uint.nat idx + j - 1)%nat = Some lc ∧ ic_loc lc = leftloc ∧
           arr !! (uint.nat idx + j - 1)%nat = Some li ∧
           item_id li = toYjsId (ic_val lc).(yjs.item.id') ∧
           length ((ic_val lc).(yjs.item.content').(yjs.content.content')) = 1%nat ∧ (1 <= uint.nat idx + j)%nat)⌝ ∗
    "%Hrightj" ∷ ⌜(in_rO = None ∧ (uint.nat idx + j = length arr)%nat)
      ∨ (∃ (ri : YjsItem A) (rid : yjs.id.t),
           arr !! (uint.nat idx + j)%nat = Some ri ∧ in_rO = Some rid ∧ item_id ri = toYjsId rid)⌝
    )%I with "[i t content client HoR left Ht Hdoc Hstore Htext]" as "IH".
  { iExists 0%nat, arr0, cells0, lft, dv.
    iFrame "i t content client HoR left Ht Hdoc Hstore Htext".
    iPureIntro. split_and!.
    - reflexivity.
    - rewrite Hk. word.
    - exact Hinv0.
    - lia.
    - lia.
    - intros x Hx Hc. have := Hmax x Hx Hc. lia.
    - destruct (decide (uint.nat idx = 0)%nat) as [Hidx0 | Hidxpos].
      + left. rewrite Hlftloc Hidx0. split; [rewrite /node_loc; case_decide as Hd; [exfalso; lia | reflexivity] | lia].
      + right.
        have Hidxm : (uint.nat idx - 1 < length cells0)%nat by lia.
        destruct (cells0 !! (uint.nat idx - 1)%nat) as [lc|] eqn:Hlc; [| apply lookup_ge_None in Hlc; lia].
        have [li [Hli Hcrlc]] := cells_repr_lookup arr0 cells0 arr0 (uint.nat idx - 1) lc Hrepr Hlc.
        exists lc, li. split_and!.
        * replace (uint.nat idx + 0 - 1)%nat with (uint.nat idx - 1)%nat by lia. exact Hlc.
        * rewrite Hlftloc /node_loc. case_decide as Hd; [| exfalso; lia].
          have -> : Z.to_nat (Z.of_nat (uint.nat idx) - 1) = (uint.nat idx - 1)%nat by lia.
          rewrite Hlc //.
        * replace (uint.nat idx + 0 - 1)%nat with (uint.nat idx - 1)%nat by lia. exact Hli.
        * exact (proj1 Hcrlc).
        * exact (proj2 (proj2 (proj2 (proj2 (proj2 Hcrlc))))).
        * lia.
    - destruct Hrightinit as [[Hrn Hpe] | (ri & rid & Hriarr & Hrosome & Hriid)].
      + left. split; [exact Hrn |]. rewrite Nat.add_0_r Hpe. exact (cells_repr_length _ _ _ Hrepr).
      + right. exists ri, rid. split_and!; [rewrite Nat.add_0_r; exact Hriarr | exact Hrosome | exact Hriid]. }
  wp_for "IH".
  wp_apply strings.wp_string_len. iIntros "%Hlcb". wp_auto. case_bool_decide as Hjlt.
  2:{ rewrite decide_False; [|done]. rewrite decide_True; [|done]. wp_auto.
      iApply ("HΦ" $! arr (W64 (uint.Z k + j))).
      rewrite /own_insert_doc. iExists tv, dvj, sv.
      rewrite Hdvstore. iFrame "Htv Hdocj Hstorej".
      iSplitR; [iPureIntro; exact Hcl|].
      iSplitR; [iPureIntro; exact Hdvclock|].
      iSplitL "Htextj"; [ iExists cells; iFrame "Htextj"; iPureIntro; exact Hinvj |].
      iPureIntro. intros x Hx Hc. have Hkj : uint.nat (W64 (uint.Z k + j)) = (uint.nat k + j)%nat by word. rewrite Hkj. exact (Hctr x Hx Hc). }
  rewrite decide_True; [|done]. wp_auto.
  wp_if_join (λ v : val, ⌜v = execute_val⌝ ∗
    ∃ (oLptr : loc) (oL : option yjs.id.t),
      "HoL" ∷ originLeftId_ptr ↦ oLptr ∗
      "HisL" ∷ is_origin_id oLptr oL ∗
      "Htextj" ∷ is_ytext tv.(yjs.Text.inner') cells arr ∗
      "Hleftp" ∷ left_ptr ↦ leftloc ∗
      "%Hleftspec" ∷ ⌜(oL = None ∧ (uint.nat idx + j = 0)%nat) ∨
         (∃ (li : YjsItem A), (1 <= uint.nat idx + j)%nat ∧ arr !! (uint.nat idx + j - 1)%nat = Some li ∧ (toYjsId <$> oL) = Some (item_id li))⌝)%I
    with "[Hleftp Htextj originLeftId]".
  { destruct Hleftj as [[_ Hpe0] | (lc & li & Hlccells & Hlcloc & Hliarr & Hliid & Hlclen & Hge1)].
    - iSplitR; [done|]. iExists null, None. iFrame "originLeftId Htextj Hleftp".
      iSplit; [by rewrite /is_origin_id|]. iPureIntro. left. split; [reflexivity | exact Hpe0].
    - iDestruct "Htextj" as (yth tlh) "(Hpar & Hdll & %Hlenh & %Hreprh)".
      iDestruct (is_dll_acc cells yth.(yjs.yText.start') tlh (uint.nat idx + j - 1)%nat lc Hlccells with "Hdll") as "Hacc". iNamed "Hacc".
      iDestruct (typed_pointsto_not_null with "Hcval") as %Hlcnn.
      exfalso. exact (Hlcnn Hlcloc). }
  { destruct Hleftj as [[Hln _] | (lc & li & Hlccells & Hlcloc & Hliarr & Hliid & Hlclen & Hge1)].
    { exfalso; exact (n Hln). }
    iDestruct "Htextj" as (yth tlh) "(Hpar & Hdll & %Hlenh & %Hreprh)".
    iDestruct (is_dll_acc cells yth.(yjs.yText.start') tlh (uint.nat idx + j - 1)%nat lc Hlccells with "Hdll") as "Hacc". iNamed "Hacc".
    iEval (rewrite Hlcloc) in "Hcval".
    wp_method_call. wp_call. wp_auto.
    wp_method_call. wp_call. rewrite /yjs.item__LastIdⁱᵐᵖˡ. wp_auto.
    wp_alloc icopy as "Hic". wp_auto.
    wp_bind (icopy @! (go.PointerType yjs.item) @! "Len" (# ()))%E.
    wp_apply (wp_item__Len icopy lc.(ic_val) with "[$Hic]"). iIntros "Hic".
    rewrite Hlclen. wp_pures. wp_store.
    iDestruct (typed_pointsto_not_null with "lid") as %Hlidnn.
    iPersist "lid". wp_auto.
    iEval (rewrite -Hlcloc) in "Hcval".
    iDestruct ("Hback" with "Hcval") as "Hdll".
    iSplitR; [done|].
    iExists lid_ptr, (Some {| yjs.id.clientId' := lc.(ic_val).(yjs.item.id').(yjs.id.clientId'); yjs.id.clock' := w64_word_instance.(word.sub) (w64_word_instance.(word.add) lc.(ic_val).(yjs.item.id').(yjs.id.clock') (W64 1%nat)) (W64 1) |}).
    iFrame "originLeftId Hleftp".
    iSplitR "Hpar Hdll".
    { rewrite /is_origin_id. iSplit; [iPureIntro; exact Hlidnn | iFrame "lid"]. }
    iSplitL "Hpar Hdll".
    { iExists yth, tlh. iFrame "Hpar Hdll". iPureIntro. split; [exact Hlenh | exact Hreprh]. }
    iPureIntro. right. exists li. split_and!.
    - exact Hge1.
    - exact Hliarr.
    - rewrite Hliid /toYjsId /=. f_equal. f_equal. word. }
  iIntros (v) "[%Hv HQL]". subst v. iNamed "HQL". wp_auto.
  wp_func_call. wp_call. wp_auto.
  wp_alloc client_l as "Hcl2". wp_auto.
  destruct (content !! sint.nat (W64 j)) as [b|] eqn:Hb;
    [ wp_auto | exfalso; apply lookup_ge_None in Hb; revert Hb Hjlt Hlcb; word ].
  wp_func_call. wp_call.
  wp_alloc oR2 as "HoR2". wp_auto.
  wp_alloc newit_l as "Hnewit". wp_auto.
  have Hclocknit : uint.nat dvj.(yjs.Doc.clock') = (uint.nat k + j)%nat by (rewrite Hdvclock; word).
  have Horig : ∃ (o : YjsPtr A),
     (toYjsId <$> oL = None ∧ o = First ∧ (uint.nat idx + j)%nat = 0%nat) ∨
     (∃ li, (1 <= uint.nat idx + j)%nat ∧ arr !! (uint.nat idx + j - 1)%nat = Some li ∧ toYjsId <$> oL = Some (item_id li) ∧ o = itemPtr li).
  { destruct Hleftspec as [[Hon Hp0] | (li & Hge & Hla & Hom)].
    - exists First. left. subst oL. split_and!; [reflexivity | reflexivity | exact Hp0].
    - exists (itemPtr li). right. exists li. split_and!; [exact Hge | exact Hla | exact Hom | reflexivity]. }
  destruct Horig as [morigin Horig].
  have Hrorig : ∃ (r : YjsPtr A),
     (toYjsId <$> in_rO = None ∧ r = Last ∧ (uint.nat idx + j)%nat = length arr) ∨
     (∃ ri, arr !! (uint.nat idx + j)%nat = Some ri ∧ toYjsId <$> in_rO = Some (item_id ri) ∧ r = itemPtr ri).
  { destruct Hrightj as [[Hrn Hpl] | (ri & rid & Hria & Hros & Hrii)].
    - exists Last. left. subst in_rO. split_and!; [reflexivity | reflexivity | exact Hpl].
    - exists (itemPtr ri). right. exists ri. split_and!; [exact Hria | rewrite Hros /= Hrii // | reflexivity]. }
  destruct Hrorig as [mrightorigin Hrorig].
  set (in_id1 := MkYjsId (uint.nat cl) (uint.nat dvj.(yjs.Doc.clock'))).
  set (input := MkIntegrateInput (toYjsId <$> oL) (toYjsId <$> in_rO) ([b] : A) in_id1).
  set (nit := Item (A:=A) morigin mrightorigin in_id1 [b]).
  have Htoitem : toItem input arr = Some nit.
  { apply (toItem_at arr in_id1 [b] morigin mrightorigin (toYjsId <$> oL) (toYjsId <$> in_rO) Hinvj).
    - destruct Horig as [(Hon & Ho & _) | (li & _ & Hla & Hom & Ho)]; [left; split; [exact Hon | exact Ho] | right; exists li; split_and!; [exact Hom | exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Hla) | exact Ho]].
    - destruct Hrorig as [(Hrn & Hr & _) | (ri & Hria & Hri & Hr)]; [left; split; [exact Hrn | exact Hr] | right; exists ri; split_and!; [exact Hri | exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Hria) | exact Hr]]. }
  have Hvalid : IsItemValid nit.
  { apply (item_valid_at arr (uint.nat idx + j) in_id1 [b] morigin mrightorigin Hinvj).
    - destruct Horig as [(_ & Ho & Hp0) | (li & Hge & Hla & _ & Ho)]; [left; split; [exact Hp0 | exact Ho] | right; split; [exact Hge | exists li; split; [exact Hla | exact Ho]]].
    - destruct Hrorig as [(_ & Hr & Hpl) | (ri & Hria & _ & Hr)]; [left; split; [exact Hpl | exact Hr] | right; exists ri; split; [exact Hria | exact Hr]]. }
  have Hmax' : maximalId nit arr.
  { intros x Hx Hc. change (clock (item_id x) < uint.nat dvj.(yjs.Doc.clock'))%nat. rewrite Hclocknit. exact (Hctr x Hx Hc). }
  iDestruct "HisR" as "#HisRp".
  iAssert (is_fresh_item newit_l input) with "[Hnewit HisL]" as "Hfresh".
  { iExists _, oL, in_rO. rewrite /is_fresh_item_raw /=. iFrame "Hnewit HisL HisRp". iPureIntro. split_and!; reflexivity. }
  wp_apply (wp_Store__Integrate (dvj.(yjs.Doc.store')) (tv.(yjs.Text.inner')) newit_l arr input nit Htoitem Hvalid Hmax' with "[$Hfresh Htextj]").
  { iExists cells. iFrame "Htextj". iPureIntro. exact Hinvj. }
  iIntros (arr' i cells' c) "(%Hile & %Harr'eq & %Hinv' & Htext' & %Hnode)".
  wp_auto. wp_for_post.
  have Hple : (uint.nat idx + j <= length arr)%nat.
  { have Hlc := cells_repr_length arr0 cells0 arr0 Hrepr. rewrite Hlenarr. lia. }
  have Hplace : arr' = take (uint.nat idx + j)%nat arr ++ nit :: drop (uint.nat idx + j)%nat arr.
  { rewrite Harr'eq. apply (insert_straddle arr nit i (uint.nat idx + j)%nat Hinvj ltac:(rewrite -Harr'eq; exact Hinv') Hile Hple).
    - destruct Horig as [(_ & Ho & Hp0) | (li & Hge & Hla & _ & Ho)]; [left; split; [exact Hp0 | rewrite /nit /=; exact Ho] | right; split; [exact Hge | exists li; split; [exact Hla | rewrite /nit /=; exact Ho]]].
    - destruct Hrorig as [(_ & Hr & Hpl) | (ri & Hria & _ & Hr)]; [left; split; [exact Hpl | rewrite /nit /=; exact Hr] | right; exists ri; split; [exact Hria | rewrite /nit /=; exact Hr]]. }
  have Hnitpos : arr' !! (uint.nat idx + j)%nat = Some nit.
  { rewrite Hplace. apply list_lookup_middle. symmetry. apply length_take_le. exact Hple. }
  have Hshift : arr' !! (uint.nat idx + j + 1)%nat = arr !! (uint.nat idx + j)%nat.
  { rewrite Hplace. rewrite lookup_app_r; last (rewrite length_take_le; [lia | exact Hple]).
    rewrite length_take_le; last exact Hple.
    replace (uint.nat idx + j + 1 - (uint.nat idx + j))%nat with 1%nat by lia.
    simpl. rewrite lookup_drop. f_equal. lia. }
  iDestruct "Htext'" as (yt3 tl3) "(Hp3 & Hdll3 & %Hlen3 & %Hrepr3)".
  destruct Hnode as [x (Hcx & Hcloc & Hcid & Hcclen)].
  destruct (cells_repr_lookup arr' cells' arr' x c Hrepr3 Hcx) as [yi [Hyi Hcr3]].
  have Hyiid : item_id yi = item_id nit by (destruct Hcr3 as (Hidr & _); rewrite Hidr Hcid; reflexivity).
  have HnitIn : nit ∈ arr' by exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Hnitpos).
  have HyiIn : yi ∈ arr' by exact (list_basics.list.list_elem_of_lookup_2 _ _ _ Hyi).
  have Hyinit : yi = nit by exact (id_unique (ArrSet arr') (yai_item_set_inv _ Hinv') yi nit Hyiid HyiIn HnitIn).
  subst yi.
  have Hxpos : x = (uint.nat idx + j)%nat.
  { destruct (Nat.lt_trichotomy x (uint.nat idx + j)%nat) as [Hlt|[Heq|Hgt]]; [exfalso|exact Heq|exfalso].
    - have HH := invariant_yjsarray_idx.getElem_lt_YjsLt' arr' x (uint.nat idx + j)%nat nit nit Hinv' Hyi Hnitpos Hlt.
      exact (asymmetry.yjs_lt_asymm (yai_closed _ Hinv') (yai_item_set_inv _ Hinv') (itemPtr nit) (itemPtr nit) HnitIn HnitIn HH HH).
    - have HH := invariant_yjsarray_idx.getElem_lt_YjsLt' arr' (uint.nat idx + j)%nat x nit nit Hinv' Hnitpos Hyi Hgt.
      exact (asymmetry.yjs_lt_asymm (yai_closed _ Hinv') (yai_item_set_inv _ Hinv') (itemPtr nit) (itemPtr nit) HnitIn HnitIn HH HH). }
  subst x.
  iFrame "HΦ HisRp".
  iExists (S j), arr', cells', newit_l, (dvj <| yjs.Doc.clock' := w64_word_instance.(word.add) dvj.(yjs.Doc.clock') (W64 1) |>).
  have HiEq : w64_word_instance.(word.add) (W64 j) (W64 1) = W64 (S j) by word.
  iEval (rewrite HiEq) in "Hi".
  iFrame "Hi Htptr0 Hcontent Hclient HoRk Hleftp Htv Hdocj Hstorej".
  iSplitL "Hp3 Hdll3".
  { iExists yt3, tl3. iFrame "Hp3 Hdll3". iPureIntro. split; [exact Hlen3 | exact Hrepr3]. }
  iPureIntro. split_and!.
  - exact Hdvstore.
  - change (w64_word_instance.(word.add) dvj.(yjs.Doc.clock') (W64 1) = W64 (uint.Z k + S j)). rewrite Hdvclock. word.
  - exact Hinv'.
  - rewrite Hplace length_app length_take_le; [| exact Hple]. simpl. rewrite length_drop. lia.
  - have HH : (j < length content)%nat by word. lia.
  - intros y Hy Hc. rewrite Hplace in Hy.
    apply elem_of_app in Hy as [Hyt | Hyc].
    + have Hya : y ∈ arr by (rewrite -(take_drop (uint.nat idx + j)%nat arr); apply elem_of_app; left; exact Hyt).
      have := Hctr y Hya Hc. lia.
    + apply elem_of_cons in Hyc as [-> | Hyd].
      * rewrite /nit /in_id1 /=. rewrite Hclocknit. lia.
      * have Hya : y ∈ arr by (rewrite -(take_drop (uint.nat idx + j)%nat arr); apply elem_of_app; right; exact Hyd).
        have := Hctr y Hya Hc. lia.
  - right. exists c, nit. split_and!.
    + replace (uint.nat idx + S j - 1)%nat with (uint.nat idx + j)%nat by lia. exact Hcx.
    + exact Hcloc.
    + replace (uint.nat idx + S j - 1)%nat with (uint.nat idx + j)%nat by lia. exact Hnitpos.
    + rewrite /nit /=. symmetry. exact Hcid.
    + exact Hcclen.
    + lia.
  - destruct Hrightj as [[Hrn Hpl] | (ri & rid & Hria & Hros & Hrii)].
    + left. split; [exact Hrn |]. rewrite Hplace length_app length_take_le; [| exact Hple]. simpl. rewrite length_drop. lia.
    + right. exists ri, rid. split_and!.
      * replace (uint.nat idx + S j)%nat with (uint.nat idx + j + 1)%nat by lia. rewrite Hshift. exact Hria.
      * exact Hros.
      * exact Hrii.
Qed.

End invariant.
