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
Definition toYjsId (i : yjs.Id.t) : YjsId :=
  MkYjsId (uint.nat i.(yjs.Id.clientId')) (uint.nat i.(yjs.Id.clock')).

Definition toContent (c : yjs.Content.t) : A := c.(yjs.Content.content').

(** One node of the heap DLL: its location, struct value, and the optional
    origin ids it points at (resolved out of the [originLeftId]/[originRightId]
    pointers). *)
Record item_cell := MkItemCell {
  ic_loc : loc;
  ic_val : yjs.Item.t;
  ic_oleft : option yjs.Id.t;
  ic_oright : option yjs.Id.t;
}.

(** The loc of the node at index [k] of [cells] ([null] outside [0, len)).
    Used to place the heap [conflict] / [left] pointers within the DLL. *)
Definition node_loc (cells : list item_cell) (k : Z) : loc :=
  if decide (0 <= k)%Z then default null (ic_loc <$> cells !! Z.to_nat k) else null.

(** An origin pointer is either null (no origin) or a read-only [Id] cell.
    Origins are immutable once integrated, hence persistent ([↦□]). *)
Definition is_origin_id (p : loc) (oid : option yjs.Id.t) : iProp Σ :=
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
      "%Hprev" ∷ ⌜(ic_val c).(yjs.Item.left') = prev⌝ ∗
      "Hval" ∷ ic_loc c ↦ ic_val c ∗
      "Holeft" ∷ is_origin_id (ic_val c).(yjs.Item.originLeftId') (ic_oleft c) ∗
      "Horight" ∷ is_origin_id (ic_val c).(yjs.Item.originRightId') (ic_oright c) ∗
      "Hrest" ∷ is_dll (ic_val c).(yjs.Item.right') last l next rest
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

(** Index accessor: borrow the node at index [k] out of a full DLL — its struct
    points-to and (persistent) origin cells — together with its location
    [node_loc cells k], its [left']/[right'] neighbours [node_loc cells (k∓1)],
    and a wand to give the node back and restore the DLL. Used to read the cursor
    node in the conflict scan (and the [left]/[right] anchors in the entry test). *)
Lemma is_dll_acc (cells : list item_cell) (hd tl : loc) (k : nat) (c : item_cell) :
  cells !! k = Some c ->
  is_dll hd tl null null cells -∗
    "%Hcloc" ∷ ⌜ic_loc c = node_loc cells (Z.of_nat k)⌝ ∗
    "%Hcl" ∷ ⌜(ic_val c).(yjs.Item.left') = node_loc cells (Z.of_nat k - 1)⌝ ∗
    "%Hcr" ∷ ⌜(ic_val c).(yjs.Item.right') = node_loc cells (Z.of_nat k + 1)⌝ ∗
    "Hcval" ∷ ic_loc c ↦ ic_val c ∗
    "Hcol" ∷ is_origin_id (ic_val c).(yjs.Item.originLeftId') (ic_oleft c) ∗
    "Hcor" ∷ is_origin_id (ic_val c).(yjs.Item.originRightId') (ic_oright c) ∗
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
  have Hcl : c.(ic_val).(yjs.Item.left') = node_loc cells (Z.of_nat k - 1).
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
    have Hcr : c.(ic_val).(yjs.Item.right') = node_loc cells (k+1) by rewrite Hrn Hnl1.
    iSplitR; [iPureIntro; exact Hcloc|].
    iSplitR; [iPureIntro; exact Hcl|].
    iSplitR; [iPureIntro; exact Hcr|].
    iFrame "Hval Hol Hor".
    iIntros "Hval2". rewrite -Hsplit is_dll_app.
    iExists ml, mf. iFrame "Hpre". simpl. iFrame "Hval2 Hol Hor".
    iPureIntro; split_and!; [exact (proj1 Hloc) | exact (proj2 Hloc) | exact Hprev | exact Hrn | exact Htm].
  - iDestruct "Hrest2" as "(%Hloc' & %Hprev' & Hval' & #Hol' & #Hor' & Hrest2')".
    have Hcr : c.(ic_val).(yjs.Item.right') = node_loc cells (k+1).
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
Definition resolve_left (m : list (YjsItem A)) (oid : option yjs.Id.t) : YjsPtr A :=
  match oid with
  | None => First
  | Some idv =>
      match list_find (λ it, item_id it = toYjsId idv) m with
      | Some (_, it) => itemPtr it
      | None => First
      end
  end.

(** Resolve a right origin id: [None] is the [Last] sentinel. *)
Definition resolve_right (m : list (YjsItem A)) (oid : option yjs.Id.t) : YjsPtr A :=
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
    resolve. ([m] is kept for uniformity with [cells_repr] / [resolve_*].) *)
Definition cell_repr (m : list (YjsItem A)) (c : item_cell) (yi : YjsItem A) : Prop :=
  item_id yi = toYjsId (ic_val c).(yjs.Item.id') /\
  content yi = toContent (ic_val c).(yjs.Item.content') /\
  origin_id (origin yi) = toYjsId <$> ic_oleft c /\
  origin_id (rightOrigin yi) = toYjsId <$> ic_oright c.

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

(** [is_ytext parent cells arr]: [parent] is a heap [YText] whose [start] heads
    the DLL [cells], which is isomorphic to the model [arr]. (Phase-2: every item
    is countable / non-deleted, so [len] = number of nodes.) *)
Definition is_ytext (parent : loc) (cells : list item_cell) (arr : list (YjsItem A)) : iProp Σ :=
  ∃ (yt : yjs.YText.t) (tl : loc),
    "Hparent" ∷ parent ↦ yt ∗
    "Hdll" ∷ is_dll yt.(yjs.YText.start') tl null null cells ∗
    "%Hlen" ∷ ⌜yt.(yjs.YText.len') = W64 (length cells)⌝ ∗
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
  ∃ (vs : list yjs.Id.t),
    "Hsl" ∷ s ↦* vs ∗
    "Hcap" ∷ own_slice_cap yjs.Id.t s (DfracOwn 1) ∗
    "%Hset" ∷ ⌜list_to_set (toYjsId <$> vs) = gs⌝.

(** [toYjsId] is injective (it is [uint.nat] on both [w64] fields), so heap id
    equality matches model id equality — the bridge between the Go id ops and
    the pure [gset] tests. *)
Lemma toYjsId_inj (a b : yjs.Id.t) : toYjsId a = toYjsId b -> a = b.
Proof.
  destruct a as [ca ka], b as [cb kb]. rewrite /toYjsId /=.
  injection 1 as Hc Hk. f_equal; word.
Qed.

(** [Id.Equal] computes the conjunction of the two field equalities; this is
    exactly [bool_decide] of the model id equality. *)
Lemma Id_eqb_toYjsId (a b : yjs.Id.t) :
  (bool_decide (a.(yjs.Id.clientId') = b.(yjs.Id.clientId'))
   && bool_decide (a.(yjs.Id.clock') = b.(yjs.Id.clock')))%bool
  = bool_decide (toYjsId a = toYjsId b).
Proof.
  rewrite -bool_decide_and. apply bool_decide_ext. rewrite /toYjsId. split.
  - move=> [Hc Hk]. by rewrite Hc Hk.
  - move=> H. injection H => Hk Hc. split; word.
Qed.

(* ----- WP specs for the id / set helper functions ------------------------ *)

Lemma wp_Id__Equal (a b : yjs.Id.t) :
  {{{ is_pkg_init yjs }}}
    a @! yjs.Id @! "Equal" #b
  {{{ RET #(bool_decide (toYjsId a = toYjsId b)); True }}}.
Proof.
  wp_start as "_". wp_auto. wp_if_destruct.
  - have -> : bool_decide (a.(yjs.Id.clock') = b.(yjs.Id.clock'))
             = bool_decide (toYjsId a = toYjsId b).
    { rewrite -Id_eqb_toYjsId. by rewrite (bool_decide_eq_true_2 _ e). }
    iApply "HΦ". done.
  - have Hf : bool_decide (toYjsId a = toYjsId b) = false.
    { apply bool_decide_eq_false_2 => H. apply n. by rewrite (toYjsId_inj _ _ H). }
    iEval (rewrite Hf) in "HΦ". iApply "HΦ". done.
Qed.

(** [idOptEqual] on two optional-id pointers ([is_origin_id]) decides equality of
    the abstract model ids. (Both origin facts are persistent, so kept.) *)
Lemma wp_idOptEqual (pa pb : loc) (oa ob : option yjs.Id.t) :
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
Definition oid_of (ov : option yjs.Item.t) : option YjsId :=
  (λ v, toYjsId v.(yjs.Item.id')) <$> ov.

Definition item_or_null (p : loc) (ov : option yjs.Item.t) (dq : dfrac) : iProp Σ :=
  match ov with
  | None => ⌜p = null⌝
  | Some v => ⌜p ≠ null⌝ ∗ p ↦{dq} v
  end.

(** [itemPtrEqual] compares two item pointers by identity (= model id, ids being
    unique), with the null cases of y-octo's [Somr] comparison. *)
Lemma wp_itemPtrEqual (pa pb : loc) (ova ovb : option yjs.Item.t) (dqa dqb : dfrac) :
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
    wp_apply (wp_Id__Equal va.(yjs.Item.id') vb.(yjs.Item.id')).
    have Heq : bool_decide (oid_of (Some va) = oid_of (Some vb))
             = bool_decide (toYjsId va.(yjs.Item.id') = toYjsId vb.(yjs.Item.id')).
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
Lemma wp_containsId (s : slice.t) (vs : list yjs.Id.t) (id : yjs.Id.t) (dq : dfrac) :
  {{{ is_pkg_init yjs ∗ s ↦*{dq} vs }}}
    @! yjs.containsId #s #id
  {{{ RET #(bool_decide (toYjsId id ∈ (list_to_set (toYjsId <$> vs) : gset YjsId)));
      s ↦*{dq} vs }}}.
Proof.
  wp_start as "Hs". wp_auto.
  iAssert (∃ (i : w64) (xv : yjs.Id.t),
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
Definition cell_has_id (idv : yjs.Id.t) (c : item_cell) : Prop :=
  toYjsId (ic_val c).(yjs.Item.id') = toYjsId idv.

#[local] Instance cell_has_id_dec idv c : Decision (cell_has_id idv c).
Proof. rewrite /cell_has_id. apply _. Defined.

(** Result location of [findById] over a cell list: first match, else [null]. *)
Definition findById_res (cells : list item_cell) (idv : yjs.Id.t) : loc :=
  match list_find (cell_has_id idv) cells with
  | Some (_, c) => ic_loc c
  | None => null
  end.

(** Under the isomorphism, the heap [cell_has_id] search and the model id search
    agree (same index, corresponding cell/item). *)
Lemma list_find_cells_repr m cells items (idv : yjs.Id.t) :
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
Lemma findById_res_correspond cells arr (idv : yjs.Id.t) (k : nat) (yi : YjsItem A) :
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

Lemma findById_res_none cells arr (idv : yjs.Id.t) :
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
Lemma findById_left_node_loc cells arr (oid : option yjs.Id.t) (idx : Z) :
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
Lemma findById_right_node_loc cells arr (oid : option yjs.Id.t) (idx : Z) :
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
    (idv : yjs.Id.t) :
  {{{ is_pkg_init yjs ∗ is_ytext parent cells arr }}}
    @! yjs.findById #parent #idv
  {{{ RET #(findById_res cells idv); is_ytext parent cells arr }}}.
Proof.
  wp_start as "Ht". iNamed "Ht". wp_auto.
  iAssert (∃ (cur ml : loc) (scanned remaining : list item_cell),
    "Hcur" ∷ cur_ptr ↦ cur ∗
    "Hpre" ∷ is_dll yt.(yjs.YText.start') ml null cur scanned ∗
    "Hrem" ∷ is_dll cur tl ml null remaining ∗
    "%Hsplit" ∷ ⌜cells = scanned ++ remaining⌝ ∗
    "%Hnone" ∷ ⌜list_find (cell_has_id idv) scanned = None⌝)%I
    with "[cur Hdll]" as "IH".
  { iExists yt.(yjs.YText.start'), null, [], cells. iFrame "cur Hdll". simpl. iPureIntro.
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
    wp_apply (wp_Id__Equal (ic_val c).(yjs.Item.id') idv).
    destruct (bool_decide (toYjsId c.(ic_val).(yjs.Item.id') = toYjsId idv)) eqn:Heq.
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
      iExists (c.(ic_val).(yjs.Item.right')), (c.(ic_loc)), (scanned ++ [c]), rest.
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
Lemma wp_itemPtrEqual_self (p : loc) (v : yjs.Item.t) (dq : dfrac) :
  {{{ is_pkg_init yjs ∗ p ↦{dq} v }}}
    @! yjs.itemPtrEqual #p #p
  {{{ RET #true; p ↦{dq} v }}}.
Proof.
  wp_start as "Hp". iDestruct (typed_pointsto_not_null with "Hp") as %Hnn. wp_auto.
  rewrite (bool_decide_eq_false_2 (p = null) Hnn). wp_auto.
  rewrite (bool_decide_eq_false_2 (p = null) Hnn). wp_auto.
  rewrite (bool_decide_eq_false_2 (p = null) Hnn). wp_auto.
  wp_method_call; wp_call; wp_auto.
  wp_apply (wp_Id__Equal v.(yjs.Item.id') v.(yjs.Item.id')).
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
    [is_fresh_item] and the [parent.len] field are loop-constant, framed outside. *)
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

(** [is_fresh_item item_l input iv oleft oright]: [item_l] is a freshly-built
    heap [Item] (not yet linked) whose id / content and origin-id cells carry the
    integration [input]. Its abstract model item is [newItem = toItem input arr]
    — that link is a side condition of the spec (a fresh item's resolved origins
    depend on the current document [arr]), so it is *not* restated here. The
    integrate algorithm resolves [left]/[right] from the origin ids and splices
    [item_l] into the document. *)
Definition is_fresh_item (item_l : loc) (input : IntegrateInput (A := A))
    (iv : yjs.Item.t) (oleft oright : option yjs.Id.t) : iProp Σ :=
  "Hitem" ∷ item_l ↦ iv ∗
  "Holeft" ∷ is_origin_id iv.(yjs.Item.originLeftId') oleft ∗
  "Horight" ∷ is_origin_id iv.(yjs.Item.originRightId') oright ∗
  "%Hfl" ∷ ⌜iv.(yjs.Item.left') = null⌝ ∗   (* unlinked: NewItem sets left/right nil *)
  "%Hfr" ∷ ⌜iv.(yjs.Item.right') = null⌝ ∗
  "%Hin_l" ∷ ⌜(toYjsId <$> oleft) = in_originId input⌝ ∗   (* heap ids = input ids *)
  "%Hin_r" ∷ ⌜(toYjsId <$> oright) = in_rightOriginId input⌝ ∗
  "%Hid" ∷ ⌜toYjsId iv.(yjs.Item.id') = in_id input⌝ ∗
  "%Hcontent" ∷ ⌜toContent iv.(yjs.Item.content') = in_content input⌝.

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
    (iv : yjs.Item.t) (oleft oright : option yjs.Id.t)
    (leftIdx rightIdx : Z) (destIdx : nat) :
  YjsArrInvariant arr ->
  toItem input arr = Some newItem ->
  IsItemValid newItem ->
  maximalId newItem arr ->
  findLeftIdx (in_originId input) arr = Some leftIdx ->
  findRightIdx (in_rightOriginId input) arr = Some rightIdx ->
  setfindIntegratedIndex leftIdx rightIdx input arr = Some destIdx ->
  {{{ is_pkg_init yjs ∗ is_ytext parent cells arr ∗
      is_fresh_item item_l input iv oleft oright }}}
    @! yjs.scanConflicts #item_l #(node_loc cells leftIdx)
        #(node_loc cells (leftIdx + 1)) #(node_loc cells rightIdx)
  {{{ RET #(node_loc cells (Z.of_nat destIdx - 1));
      is_ytext parent cells arr ∗ is_fresh_item item_l input iv oleft oright }}}.
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
    ∗ is_fresh_item item_l input iv oleft oright)%I
    with "[Hparent Hdll conflict left right conflictingItems Hci_sl Hci_cap itemsBeforeOrigin Hibo_sl Hibo_cap Hitem Holeft Horight]" as "IH".
  { iExists 1%nat, ∅, ∅, (leftIdx + 1)%Z.
    rewrite /integrate_loop_inv /is_fresh_item.
    replace (leftIdx + 1 - 1)%Z with leftIdx by lia.
    replace (leftIdx + Z.of_nat 1)%Z with (leftIdx + 1)%Z by lia.
    iFrame "conflict left right Hitem Holeft Horight".
    iSplitL "Hparent Hdll itemsBeforeOrigin Hibo_sl Hibo_cap conflictingItems Hci_sl Hci_cap".
    - iSplitL "Hparent Hdll".
      { iExists yt, tl. iFrame "Hparent Hdll". done. }
      iSplitL "itemsBeforeOrigin Hibo_sl Hibo_cap".
      { iExists _. iFrame "itemsBeforeOrigin". iExists ([] : list yjs.Id.t). iFrame "Hibo_sl Hibo_cap". done. }
      iSplitL "conflictingItems Hci_sl Hci_cap".
      { iExists _. iFrame "conflictingItems". iExists ([] : list yjs.Id.t). iFrame "Hci_sl Hci_cap". done. }
      iPureIntro; split_and!; [lia | lia | lia | lia | exact Hsetfii].
    - iPureIntro; split_and!; [exact Hfl | exact Hfr | exact Hin_l | exact Hin_r | exact Hid | exact Hcontent]. }
  wp_for "IH".
  iDestruct "IH" as "[Hinv Hfresh]". iNamed "Hinv". iNamed "Hfresh".
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
    iApply "HΦ". iFrame "Htext". rewrite /is_fresh_item. iFrame "Hitem Holeft Horight".
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
      iApply "HΦ". iFrame "Htext". rewrite /is_fresh_item. iFrame "Hitem Holeft Horight".
      iPureIntro; split_and!; done.
    + (* conflict ≠ right: scan one item; match the 6 [setfii_loop] branches *)
      rewrite (bool_decide_eq_false_2 _ Hner).
      admit.
Admitted.

(** The conflict scan with its entry guard: resolves whether to scan at all
    (y-octo's left/right-connection check), sets the initial cursor, and delegates
    to [scanConflicts]. When the guard is false the anchors are adjacent
    ([leftIdx + 1 = rightIdx]) so [destIdx = leftIdx + 1] and the unchanged [left]
    already equals [node_loc cells (destIdx - 1)]. *)
Lemma wp_findIntegrationLeft (parent item_l left_loc right_loc : loc)
    (cells : list item_cell) (arr : list (YjsItem A))
    (input : IntegrateInput (A := A)) (newItem : YjsItem A)
    (iv : yjs.Item.t) (oleft oright : option yjs.Id.t)
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
      is_fresh_item item_l input iv oleft oright }}}
    @! yjs.findIntegrationLeft #parent #item_l #left_loc #right_loc
  {{{ RET #(node_loc cells (Z.of_nat destIdx - 1));
      is_ytext parent cells arr ∗ is_fresh_item item_l input iv oleft oright }}}.
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
  (* Remaining: entry condition (read left/right neighbour fields) -> conflict
     scan via wp_for + integrate_loop_inv (each Go branch matched to a setfii_loop
     unfold using wp_idOptEqual / wp_itemPtrEqual / wp_containsId and the
     cell_repr origin_id facts) -> exit pinned by HfindD. *)
  admit.
Admitted.

(** Top-level spec: integrating a valid item into a valid document yields the
    document updated per the pure [setintegrate]; validity (hence order /
    convergence, via [setintegrate_eq_integrate]) is preserved. *)
Lemma wp_Store__Integrate (s parent item_l : loc) (arr arr' : list (YjsItem A))
    (input : IntegrateInput (A := A)) (newItem : YjsItem A)
    (iv : yjs.Item.t) (oleft oright : option yjs.Id.t) :
  YjsArrInvariant arr ->
  toItem input arr = Some newItem ->
  IsItemValid newItem ->
  maximalId newItem arr ->
  setintegrate input arr = Some arr' ->
  {{{ is_pkg_init yjs ∗ is_valid_ytext parent arr ∗
      is_fresh_item item_l input iv oleft oright }}}
    s @! (go.PointerType yjs.Store) @! "Integrate" #parent #item_l
  {{{ RET #(); is_valid_ytext parent arr' }}}.
Proof using All.
  move=> Harr Htoitem Hvalid Hmax.
  (* Decompose the pure result: leftIdx / rightIdx / destIdx / itemM and
     arr' = insertIdxIfInBounds destIdx itemM arr. *)
  rewrite /setintegrate.
  case HfindL: (findLeftIdx (in_originId input) arr) => [leftIdx|] //=.
  case HfindR: (findRightIdx (in_rightOriginId input) arr) => [rightIdx|] //=.
  case HfindD: (setfindIntegratedIndex leftIdx rightIdx input arr) => [destIdx|] //=.
  case HmkI: (mkItemByIndex leftIdx rightIdx input arr) => [itemM|] //=.
  move=> [<-].
  (* Operational refinement (remaining work):
     1. repair: item.left/right := findById (origin ids); by
        findById_res_correspond (+ HfindL/HfindR, is_fresh_item's left'/right' =
        null) they equal node_loc cells leftIdx / rightIdx.
     2. entry condition + conflict scan: wp_for with integrate_loop_inv, each Go
        branch matched to a setfii_loop unfold; HfindD pins the exit destIdx.
     3. splice: is_dll_app to split at destIdx, wp_store to relink
        left.right / right.left / item, is_dll_app to rejoin; cells_repr_insert
        for the model side; parent.len += 1.
     4. conclude is_valid_ytext parent (insertIdxIfInBounds destIdx itemM arr),
        YjsArrInvariant via YjsArrInvariant_setintegrate. *)
  admit.
Admitted.

End invariant.
