(** The [item] type, Iris layer over [item/value.v].

    Definitions
    - [own_dll dq l last prev next cells]: the doubly-linked list the heap
      nodes form, each carrying its [Item] struct and its two origin-id cells.
      An owning predicate, so [dfrac]-parameterized ([DfracOwn 1] to mutate).
      Adapted from the reference sorted-DLL proof (iasakura/perennial-sandbox,
      dll/list.go, [is_dlist_node]).
    - [item_or_null p ov]: a heap item pointer is null or owns a node.
    - [own_item_node l dq input deleted parent prev nxt]: one heap [Item]
      node in full: the wire item it denotes, its tombstone bit, its parent
      and its two spine links (docs/plan-item-run-split.md stage 3: the
      node payload [own_dll] moves onto, and what the borrow lemmas will
      hand out).
    - [own_dll_runs dq parent l last prev next ls runs]: the DLL at run
      granularity: node addresses paired with the runs they hold, one
      [own_item_node] per node ([own_dll_as_runs] is the fold/unfold to
      the cell-level [own_dll], under per-cell parent coherence;
      [own_dll_runs_length] aligns the two lists; [own_dll_runs_app]
      splits and joins a segment, [own_dll_runs_insert_middle] splices a
      fresh node, and [own_dll_runs_lookup_acc] /
      [own_dll_runs_update] borrow the [k]-th node whole, the update
      wand flipping its tombstone bit, mirroring the cell laws).

    Laws
    - the spine is a monoid: [own_dll_app] splits and joins a segment, and
      [own_dll_split] / [own_dll_insert_middle] are the relink steps
      [Store.Integrate] and [store.splitNode] perform.
    - endpoints: the head and last pointers are determined by the cells
      ([own_dll_headptr], [own_dll_lastptr], [own_dll_head_node],
      [own_dll_last_agree]), and a null head means an empty segment.
    - access: [own_dll_acc] / [own_dll_lookup_acc] borrow the [k]-th node,
      [own_dll_update_gen] borrows it for an update, and [node_loc] of an
      in-range index is non-null. Their stage-3 forms hand the node out
      WHOLE, as [own_item_node] at [input_of_run], each also exposing the
      run's spelled length ([own_dll_acc_node] / [own_dll_lookup_acc_node]
      / [own_dll_update_gen_node]).
    - freshness: a fully owned node is fresh for any segment
      ([own_dll_fresh], via [item_pointsto_conflict]), which is where the
      [NoDup] of locations comes from.
    - ids in a segment are bounded ([own_dll_id_bounds]), and every cell's run
      is well-formed ([own_dll_runs_wf]).

    The per-node method specs are [item/wp_private.v]. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core prelude.
From New.proof.item Require Import run_theory model value.
From New.proof.id Require Import value heap.

Section item_heap.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.

(* ===== definitions ======================================================== *)

Definition item_or_null (p : loc) (ov : option yjs.item.t) (dq : dfrac) : iProp Σ :=
  match ov with
  | None => ⌜p = null⌝
  | Some v => ⌜p ≠ null⌝ ∗ p ↦{dq} v
  end.

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

(** [own_item_node l dq input deleted parent prev nxt]: one heap [Item] node
    in full: the struct and its two origin-id cells are existential, pinned
    to the wire item [input] (the [toYjsId] images of the id and the origins,
    [toContent] of the content), tombstoned iff [deleted] (the flag byte is
    [W8 6] / [W8 2], so a node is always Countable), under [parent], its
    [left'] / [right'] spine links at [prev] / [nxt]. The per-node payload
    the stage-3 [own_dll] holds and the borrow lemmas hand out
    (docs/plan-item-run-split.md); [own_linked_item] is its [DfracOwn 1]
    live form ([own_linked_item_as_node], [store/heap.v]). *)
Definition own_item_node (l : loc) (dq : dfrac) (input : IntegrateInput (A := A))
    (deleted : bool) (parent prev nxt : loc) : iProp Σ :=
  ∃ (v : yjs.item.t) (olid orid : option yjs.id.t),
    "Hval" ∷ l ↦{dq} v ∗
    "Holeft" ∷ is_origin_id v.(yjs.item.originLeftId') olid ∗
    "Horight" ∷ is_origin_id v.(yjs.item.originRightId') orid ∗
    "%Hin_l" ∷ ⌜(toYjsId <$> olid) = in_originId input⌝ ∗
    "%Hin_r" ∷ ⌜(toYjsId <$> orid) = in_rightOriginId input⌝ ∗
    "%Hid" ∷ ⌜toYjsId v.(yjs.item.id') = in_id input⌝ ∗
    "%Hcontent" ∷ ⌜toContent v.(yjs.item.content') = in_content input⌝ ∗
    "%Hpar" ∷ ⌜v.(yjs.item.parent') = parent⌝ ∗
    "%Hprev" ∷ ⌜v.(yjs.item.left') = prev⌝ ∗
    "%Hnext" ∷ ⌜v.(yjs.item.right') = nxt⌝ ∗
    "%Hflags" ∷ ⌜v.(yjs.item.flags') = (if deleted then W8 6 else W8 2)⌝.

(** [own_dll_runs dq parent l last prev next ls runs]: the DLL segment at run
    granularity (docs/plan-item-run-split.md section 2.2): the node
    addresses [ls] paired with the runs they hold, every node one
    [own_item_node] at the wire item its run denotes, all under one type
    [parent]. Each run also carries [run_wf] and [run_per_char] (the wire
    view alone cannot recover how the content splits over the run's items).
    [own_dll_as_runs] folds and unfolds to the cell-level [own_dll]. *)
Fixpoint own_dll_runs (dq : dfrac) (parent l last prev next : loc)
    (ls : list loc) (runs : list ItemRun) : iProp Σ :=
  match ls, runs with
  | [], [] => ⌜l = next ∧ last = prev⌝
  | lc :: ls', r :: runs' =>
      "%Hloc" ∷ ⌜l = lc ∧ lc ≠ null⌝ ∗
      "%Hperchar" ∷ ⌜run_per_char r⌝ ∗
      "%Hrun" ∷ ⌜run_wf (run_items r)⌝ ∗
      ∃ (nxt0 : loc),
        "Hnode" ∷ own_item_node lc dq (input_of_run r) (run_deleted r) parent prev nxt0 ∗
        "Hrest" ∷ own_dll_runs dq parent nxt0 last lc next ls' runs'
  | _, _ => False
  end.

(* ===== lemmas ============================================================= *)

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

(** Split one run node into two adjacent nodes [leftCell] (left half, same loc) and
    [rightCell] (right half, fresh loc) in place: the caller (the [splitNode] WP) has
    already truncated [leftCell]'s struct, allocated [rightCell]'s struct, and relinked the
    following segment's head [left'] to [rightCell]. This is the DLL-spine counterpart
    of the pure [split_cells] surgery; both [leftCell] and [rightCell] carry ordinary node
    field conditions, discharged from [run_wf] telescoping at the call site. It
    is [own_dll_insert_middle] applied to [leftCell], with [rightCell] pre-consed onto the
    tail. *)
Lemma own_dll_split (dq : dfrac) (cs1 cs2 : list item_cell) (leftCell rightCell : item_cell)
    (ivl ivr : yjs.item.t) (olidl oridl olidr oridr : option yjs.id.t)
    (hd tl ml : loc) :
  ic_loc leftCell ≠ null ->
  ic_loc rightCell ≠ null ->
  ivl.(yjs.item.left') = ml ->
  ivl.(yjs.item.right') = ic_loc rightCell ->
  ivl.(yjs.item.parent') = ic_parent leftCell ->
  item_id (run_head leftCell) = toYjsId ivl.(yjs.item.id') ->
  content <$> ic_run leftCell = explode (toContent ivl.(yjs.item.content')) ->
  origin_id (origin (run_head leftCell)) = toYjsId <$> olidl ->
  origin_id (rightOrigin (run_head leftCell)) = toYjsId <$> oridl ->
  ivl.(yjs.item.flags') = (if ic_deleted leftCell then W8 6 else W8 2) ->
  run_wf (ic_run leftCell) ->
  ivr.(yjs.item.left') = ic_loc leftCell ->
  ivr.(yjs.item.parent') = ic_parent rightCell ->
  item_id (run_head rightCell) = toYjsId ivr.(yjs.item.id') ->
  content <$> ic_run rightCell = explode (toContent ivr.(yjs.item.content')) ->
  origin_id (origin (run_head rightCell)) = toYjsId <$> olidr ->
  origin_id (rightOrigin (run_head rightCell)) = toYjsId <$> oridr ->
  ivr.(yjs.item.flags') = (if ic_deleted rightCell then W8 6 else W8 2) ->
  run_wf (ic_run rightCell) ->
  own_dll dq hd ml null (ic_loc leftCell) cs1 ∗
  ic_loc leftCell ↦{dq} ivl ∗
  is_origin_id ivl.(yjs.item.originLeftId') olidl ∗
  is_origin_id ivl.(yjs.item.originRightId') oridl ∗
  ic_loc rightCell ↦{dq} ivr ∗
  is_origin_id ivr.(yjs.item.originLeftId') olidr ∗
  is_origin_id ivr.(yjs.item.originRightId') oridr ∗
  own_dll dq ivr.(yjs.item.right') tl (ic_loc rightCell) null cs2
  ⊢ own_dll dq hd tl null null (cs1 ++ leftCell :: rightCell :: cs2).
Proof.
  move=> Hclnn Hcrnn Hivl_l Hivl_r Hivl_p Hclid Hclcont Holidl Horidl Hclflags Hclrun
         Hivr_l Hivr_p Hcrid Hcrcont Holidr Horidr Hcrflags Hcrrun.
  iIntros "(Hdll1 & Hnodel & Holl & Horl & Hnoder & Holr & Horr & Hdll2)".
  iAssert (own_dll dq (ic_loc rightCell) tl (ic_loc leftCell) null (rightCell :: cs2))
    with "[Hnoder Holr Horr Hdll2]" as "Hdllr".
  { simpl. iExists ivr, olidr, oridr. iFrame "Hnoder Holr Horr Hdll2".
    iPureIntro; split_and!;
      [reflexivity | exact Hcrnn | exact Hivr_l | exact Hivr_p | exact Hcrid | exact Hcrcont
      | exact Holidr | exact Horidr | exact Hcrflags | exact Hcrrun]. }
  iApply (own_dll_insert_middle dq cs1 (rightCell :: cs2) leftCell ivl olidl oridl hd tl ml (ic_loc rightCell)
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
      "%Hcpar" ∷ ⌜itemVal.(yjs.item.parent') = ic_parent c⌝ ∗
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
  iSplit; [iPureIntro; exact Hparc|].
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

(** [own_dll_lookup_acc] at the node predicate (stage 3): borrow the [k]-th
    node WHOLE, as [own_item_node] at the wire item its run denotes
    ([input_of_run]), its spine links existential; the wand takes the node
    back (any struct satisfying the pins) and restores the DLL. The content
    pin travels through [items_string_explode]; the run is unchanged through
    the borrow, so the exploded form is recovered from the original pin. *)
Lemma own_dll_lookup_acc_node (dq : dfrac) (l lst prev nxt : loc)
    (cs : list item_cell) (k : nat) (c : item_cell) :
  cs !! k = Some c ->
  own_dll dq l lst prev nxt cs -∗
    ∃ (prev' nxt' : loc),
      "%Hrun" ∷ ⌜run_wf (ic_run c)⌝ ∗
      "%Hclen" ∷ ⌜length (items_string (ic_run c)) = length (ic_run c)⌝ ∗
      "Hnode" ∷ own_item_node (ic_loc c) dq (input_of_run (cell_run c))
                  (ic_deleted c) (ic_parent c) prev' nxt' ∗
      "Hback" ∷ (own_item_node (ic_loc c) dq (input_of_run (cell_run c))
                   (ic_deleted c) (ic_parent c) prev' nxt' -∗
                 own_dll dq l lst prev nxt cs).
Proof.
  move=> Hk. iIntros "Hdll".
  pose proof (take_drop_middle cs k c Hk) as Hsplit.
  set (pre := take k cs) in Hsplit.
  set (suf := drop (S k) cs) in Hsplit.
  iEval (rewrite -Hsplit own_dll_app) in "Hdll".
  iDestruct "Hdll" as (ml mf) "[Hpre Hrest]".
  iDestruct "Hrest" as (itemVal olid orid)
    "(%Hloc & %Hprevml & %Hparc & %Hidc & %Hcontentc & %Holidc & %Horidc & %Hflagsc & %Hrunc & Hval0 & Hol0 & Hor0 & Hrest2)".
  have Hstr : toContent itemVal.(yjs.item.content') = items_string (ic_run c).
  { symmetry. exact (items_string_explode _ _ Hcontentc). }
  have Hexp : content <$> ic_run c = explode (items_string (ic_run c)).
  { rewrite -Hstr. exact Hcontentc. }
  have Hclen : length (items_string (ic_run c)) = length (ic_run c).
  { have Hleq := f_equal length Hcontentc.
    rewrite length_fmap explode_length in Hleq. rewrite -Hstr. lia. }
  iExists itemVal.(yjs.item.left'), itemVal.(yjs.item.right').
  iSplitR; [iPureIntro; exact Hrunc |].
  iSplitR; [iPureIntro; exact Hclen |].
  iSplitL "Hval0 Hol0 Hor0".
  { iExists itemVal, olid, orid.
    iFrame "Hval0 Hol0 Hor0".
    iPureIntro. split_and!.
    - exact (eq_sym Holidc).
    - exact (eq_sym Horidc).
    - exact (eq_sym Hidc).
    - exact Hstr.
    - exact Hparc.
    - reflexivity.
    - reflexivity.
    - exact Hflagsc. }
  iIntros "Hnode".
  iDestruct "Hnode" as (v' olid' orid') "H". iNamed "H".
  iEval (rewrite -Hsplit own_dll_app).
  iExists ml, mf. iFrame "Hpre".
  iExists v', olid', orid'.
  rewrite Hnext.
  iFrame "Hval Holeft Horight Hrest2".
  iPureIntro. split_and!.
  - exact (proj1 Hloc).
  - exact (proj2 Hloc).
  - rewrite Hprev. exact Hprevml.
  - exact Hpar.
  - exact (eq_sym Hid).
  - rewrite Hcontent. exact Hexp.
  - exact (eq_sym Hin_l).
  - exact (eq_sym Hin_r).
  - exact Hflags.
  - exact Hrunc.
Qed.

(** [own_dll_acc] at the node predicate (stage 3): borrow the [k]-th node of
    a WHOLE DLL as [own_item_node] at [input_of_run], its spine links the
    [node_loc] cursors; the wand takes the node back (any struct satisfying
    the pins: relinking is invisible to the abstract cells) and restores the
    DLL. *)
Lemma own_dll_acc_node (dq : dfrac) (cells : list item_cell) (hd tl : loc) (k : nat) (c : item_cell) :
  cells !! k = Some c ->
  own_dll dq hd tl null null cells -∗
    ∃ (prev' nxt' : loc),
      "%Hcloc" ∷ ⌜ic_loc c = node_loc cells (Z.of_nat k)⌝ ∗
      "%Hcl" ∷ ⌜prev' = node_loc cells (Z.of_nat k - 1)⌝ ∗
      "%Hcr" ∷ ⌜nxt' = node_loc cells (Z.of_nat k + 1)⌝ ∗
      "%Hrun" ∷ ⌜run_wf (ic_run c)⌝ ∗
      "%Hclen" ∷ ⌜length (items_string (ic_run c)) = length (ic_run c)⌝ ∗
      "Hnode" ∷ own_item_node (ic_loc c) dq (input_of_run (cell_run c))
                  (ic_deleted c) (ic_parent c) prev' nxt' ∗
      "Hback" ∷ (own_item_node (ic_loc c) dq (input_of_run (cell_run c))
                   (ic_deleted c) (ic_parent c) prev' nxt' -∗
                 own_dll dq hd tl null null cells).
Proof.
  move=> Hk. iIntros "Hdll".
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
  iEval (rewrite -Hsplit own_dll_app) in "Hdll".
  iDestruct "Hdll" as (ml mf) "[Hpre Hrest]".
  iDestruct "Hrest" as (itemVal olid orid)
    "(%Hloc & %Hprevml & %Hparc & %Hidc & %Hcontentc & %Holidc & %Horidc & %Hflagsc & %Hrunc & Hval0 & Hol0 & Hor0 & Hrest2)".
  iDestruct (own_dll_lastptr with "Hpre") as "[%Hml Hpre]".
  iDestruct (own_dll_headptr with "Hrest2") as "[%Hhd Hrest2]".
  have Hcl : itemVal.(yjs.item.left') = node_loc cells (Z.of_nat k - 1).
  { rewrite Hprevml Hml. exact Hpe. }
  have Hcloc : c.(ic_loc) = node_loc cells (Z.of_nat k)
    by rewrite /node_loc decide_True; [rewrite Nat2Z.id Hk | lia].
  have Hnn : c.(ic_loc) ≠ null by rewrite -(proj1 Hloc); exact (proj2 Hloc).
  have Hcr : itemVal.(yjs.item.right') = node_loc cells (Z.of_nat k + 1).
  { rewrite Hhd /node_loc decide_True; last lia.
    have HZ : Z.to_nat (Z.of_nat k + 1) = S k by lia.
    rewrite HZ. f_equal. f_equal. rewrite /suf head_lookup lookup_drop Nat.add_0_r //. }
  have Hstr : toContent itemVal.(yjs.item.content') = items_string (ic_run c).
  { symmetry. exact (items_string_explode _ _ Hcontentc). }
  have Hexp : content <$> ic_run c = explode (items_string (ic_run c)).
  { rewrite -Hstr. exact Hcontentc. }
  have Hclen : length (items_string (ic_run c)) = length (ic_run c).
  { have Hleq := f_equal length Hcontentc.
    rewrite length_fmap explode_length in Hleq. rewrite -Hstr. lia. }
  iExists itemVal.(yjs.item.left'), itemVal.(yjs.item.right').
  iSplit; [iPureIntro; exact Hcloc|].
  iSplit; [iPureIntro; exact Hcl|].
  iSplit; [iPureIntro; exact Hcr|].
  iSplit; [iPureIntro; exact Hrunc|].
  iSplit; [iPureIntro; exact Hclen|].
  iSplitL "Hval0 Hol0 Hor0".
  { iExists itemVal, olid, orid.
    iFrame "Hval0 Hol0 Hor0".
    iPureIntro. split_and!.
    - exact (eq_sym Holidc).
    - exact (eq_sym Horidc).
    - exact (eq_sym Hidc).
    - exact Hstr.
    - exact Hparc.
    - reflexivity.
    - reflexivity.
    - exact Hflagsc. }
  iIntros "Hnode".
  iDestruct "Hnode" as (v' olid' orid') "H". iNamed "H".
  have Hpv : v'.(yjs.item.left') = ml by rewrite Hprev; exact Hprevml.
  have Hparv : v'.(yjs.item.parent') = ic_parent c by exact Hpar.
  have Hidt : item_id (run_head c) = toYjsId v'.(yjs.item.id') by exact (eq_sym Hid).
  have Hcontt : content <$> ic_run c = explode (toContent v'.(yjs.item.content')).
  { rewrite Hcontent. exact Hexp. }
  have Holid' : origin_id (origin (run_head c)) = toYjsId <$> olid' by exact (eq_sym Hin_l).
  have Horid' : origin_id (rightOrigin (run_head c)) = toYjsId <$> orid' by exact (eq_sym Hin_r).
  iEval (rewrite -Hsplit).
  iApply (own_dll_insert_middle dq pre suf c v' olid' orid' hd tl ml v'.(yjs.item.right')
            Hnn Hpv eq_refl Hparv Hidt Hcontt Holid' Horid' Hflags Hrunc).
  rewrite Hnext.
  iEval (rewrite (proj1 Hloc)) in "Hpre".
  iEval (rewrite (proj1 Hloc)) in "Hrest2".
  iFrame "Hpre Hval Holeft Horight Hrest2".
Qed.

(** [own_dll_update_gen] at the node predicate (stage 3): borrow the [k]-th
    node WHOLE for an update; the wand takes the node back at ANY tombstone
    bit [d'] and gives the DLL with the cell flipped to [d']. Replaces the
    eight field equations of [own_dll_update_gen] with one node predicate. *)
Lemma own_dll_update_gen_node (cells : list item_cell) (hd tl : loc) (k : nat) (c : item_cell) :
  cells !! k = Some c ->
  own_dll (DfracOwn 1) hd tl null null cells -∗
    ∃ (prev' nxt' : loc),
      "%Hcloc" ∷ ⌜ic_loc c = node_loc cells (Z.of_nat k)⌝ ∗
      "%Hcr" ∷ ⌜nxt' = node_loc cells (Z.of_nat k + 1)⌝ ∗
      "%Hrun" ∷ ⌜run_wf (ic_run c)⌝ ∗
      "%Hclen" ∷ ⌜length (items_string (ic_run c)) = length (ic_run c)⌝ ∗
      "Hnode" ∷ own_item_node (ic_loc c) (DfracOwn 1) (input_of_run (cell_run c))
                  (ic_deleted c) (ic_parent c) prev' nxt' ∗
      "Hback" ∷ (∀ d' : bool,
         own_item_node (ic_loc c) (DfracOwn 1) (input_of_run (cell_run c))
           d' (ic_parent c) prev' nxt' -∗
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
    "(%Hloc & %Hprevml & %Hparc & %Hidc & %Hcontentc & %Holidc & %Horidc & %Hflagsc & %Hrunc & Hval0 & Hol0 & Hor0 & Hrest2)".
  iDestruct (own_dll_headptr with "Hrest2") as "[%Hhd Hrest2]".
  have Hcloc : ic_loc c = node_loc cells (Z.of_nat k)
    by rewrite /node_loc decide_True; [rewrite Nat2Z.id Hk | lia].
  have Hnn : ic_loc c ≠ null by rewrite -(proj1 Hloc); exact (proj2 Hloc).
  have Hcr : itemVal.(yjs.item.right') = node_loc cells (Z.of_nat k + 1).
  { rewrite Hhd /node_loc decide_True; last lia.
    have HZ : Z.to_nat (Z.of_nat k + 1) = S k by lia.
    rewrite HZ. f_equal. f_equal. rewrite /suf head_lookup lookup_drop Nat.add_0_r //. }
  have Hstr : toContent itemVal.(yjs.item.content') = items_string (ic_run c).
  { symmetry. exact (items_string_explode _ _ Hcontentc). }
  have Hexp : content <$> ic_run c = explode (items_string (ic_run c)).
  { rewrite -Hstr. exact Hcontentc. }
  have Hclen : length (items_string (ic_run c)) = length (ic_run c).
  { have Hleq := f_equal length Hcontentc.
    rewrite length_fmap explode_length in Hleq. rewrite -Hstr. lia. }
  iExists itemVal.(yjs.item.left'), itemVal.(yjs.item.right').
  iSplit; [iPureIntro; exact Hcloc|].
  iSplit; [iPureIntro; exact Hcr|].
  iSplit; [iPureIntro; exact Hrunc|].
  iSplit; [iPureIntro; exact Hclen|].
  iSplitL "Hval0 Hol0 Hor0".
  { iExists itemVal, olid, orid.
    iFrame "Hval0 Hol0 Hor0".
    iPureIntro. split_and!.
    - exact (eq_sym Holidc).
    - exact (eq_sym Horidc).
    - exact (eq_sym Hidc).
    - exact Hstr.
    - exact Hparc.
    - reflexivity.
    - reflexivity.
    - exact Hflagsc. }
  iIntros (d') "Hnode".
  iDestruct "Hnode" as (v' olid' orid') "H". iNamed "H".
  have Hpv : v'.(yjs.item.left') = ml by rewrite Hprev; exact Hprevml.
  have Hparv : v'.(yjs.item.parent') = ic_parent c by exact Hpar.
  have Hidt : item_id (run_head c) = toYjsId v'.(yjs.item.id') by exact (eq_sym Hid).
  have Hcontt : content <$> ic_run c = explode (toContent v'.(yjs.item.content')).
  { rewrite Hcontent. exact Hexp. }
  have Holid' : origin_id (origin (run_head c)) = toYjsId <$> olid' by exact (eq_sym Hin_l).
  have Horid' : origin_id (rightOrigin (run_head c)) = toYjsId <$> orid' by exact (eq_sym Hin_r).
  have Hins : <[k := MkItemCell (ic_loc c) (ic_run c) d' (ic_parent c)]> cells
            = pre ++ MkItemCell (ic_loc c) (ic_run c) d' (ic_parent c) :: suf.
  { rewrite /pre /suf. apply insert_take_drop. apply lookup_lt_Some in Hk; exact Hk. }
  rewrite Hins.
  iApply (own_dll_insert_middle (DfracOwn 1) pre suf
            (MkItemCell (ic_loc c) (ic_run c) d' (ic_parent c)) v' olid' orid'
            hd tl ml v'.(yjs.item.right')
            Hnn Hpv eq_refl Hparv Hidt Hcontt Holid' Horid' Hflags Hrunc).
  rewrite Hnext.
  iEval (rewrite (proj1 Hloc)) in "Hpre".
  iEval (rewrite (proj1 Hloc)) in "Hrest2".
  iFrame "Hpre Hval Holeft Horight Hrest2".
Qed.

(** The cell-level DLL IS the run-granular one at the projected addresses and
    runs, under per-cell parent coherence (the [own_ytype_cells] fact): the
    stage-3 migration bridge, letting one file at a time trade [own_dll] for
    [own_dll_runs]. The content pin translates through
    [items_string_explode] / [run_per_char]. *)
Lemma own_dll_as_runs (dq : dfrac) (l last prev next parent : loc) (cells : list item_cell) :
  (∀ c, c ∈ cells -> ic_parent c = parent) ->
  own_dll dq l last prev next cells ⊣⊢
  own_dll_runs dq parent l last prev next (ic_loc <$> cells) (cell_run <$> cells).
Proof.
  revert l prev. induction cells as [|c cells IH] => l prev Hpars /=.
  - reflexivity.
  - have Hparc : ic_parent c = parent := Hpars c (list_elem_of_here _ _).
    have Hpars' : ∀ c0, c0 ∈ cells -> ic_parent c0 = parent
      := λ c0 Hc0, Hpars c0 (list_elem_of_further _ _ _ Hc0).
    iSplit.
    + iIntros "H". iNamed "H".
      have Hstr : toContent itemVal.(yjs.item.content') = items_string (ic_run c).
      { symmetry. exact (items_string_explode _ _ Hcontent). }
      have Hpc : run_per_char (cell_run c).
      { rewrite /run_per_char /=. rewrite -Hstr. exact Hcontent. }
      iSplitR.
      { iPureIntro. split; [exact (proj1 Hloc) | rewrite -(proj1 Hloc); exact (proj2 Hloc)]. }
      iSplitR; [iPureIntro; exact Hpc |].
      iSplitR; [iPureIntro; exact Hrun |].
      iExists itemVal.(yjs.item.right').
      iSplitL "Hval Holeft Horight".
      { iExists itemVal, olid, orid. iFrame "Hval Holeft Horight".
        iPureIntro. split_and!.
        - exact (eq_sym Holid).
        - exact (eq_sym Horid).
        - exact (eq_sym Hid).
        - exact Hstr.
        - rewrite Hpar. exact Hparc.
        - exact Hprev.
        - reflexivity.
        - exact Hflags. }
      iEval (rewrite (proj1 Hloc)) in "Hrest".
      iEval (rewrite (IH _ _ Hpars')) in "Hrest".
      iExact "Hrest".
    + iIntros "H".
      iDestruct "H" as "(%Hlocr & %Hpc & %Hrunr & H)".
      iDestruct "H" as (nxt0) "[Hnode Hrest]".
      iDestruct "Hnode" as (v olid orid)
        "(Hval & Holeft & Horight & %Hinl & %Hinr & %Hid & %Hcont & %Hparv & %Hprev & %Hnext & %Hflags)".
      have Hpc' : content <$> ic_run c = explode (items_string (ic_run c)) := Hpc.
      have Hstr : toContent v.(yjs.item.content') = items_string (ic_run c) := Hcont.
      iExists v, olid, orid.
      rewrite Hnext.
      iEval (rewrite -(IH _ _ Hpars')) in "Hrest".
      iEval (rewrite -(proj1 Hlocr)) in "Hrest".
      iFrame "Hval Holeft Horight Hrest".
      iPureIntro. split_and!.
      * exact (proj1 Hlocr).
      * rewrite (proj1 Hlocr). exact (proj2 Hlocr).
      * exact Hprev.
      * rewrite Hparv Hparc //.
      * exact (eq_sym Hid).
      * rewrite Hstr. exact Hpc'.
      * exact (eq_sym Hinl).
      * exact (eq_sym Hinr).
      * exact Hflags.
      * exact Hrunr.
Qed.

(** Split / join a run-granular DLL segment at an aligned list append: the
    run form of [own_dll_app]. *)
Lemma own_dll_runs_app (dq : dfrac) (parent l last prev next : loc)
    (ls1 ls2 : list loc) (runs1 runs2 : list ItemRun) :
  length ls1 = length runs1 ->
  own_dll_runs dq parent l last prev next (ls1 ++ ls2) (runs1 ++ runs2)
  ⊣⊢ ∃ ml mf,
     own_dll_runs dq parent l ml prev mf ls1 runs1 ∗
     own_dll_runs dq parent mf last ml next ls2 runs2.
Proof.
  revert runs1 l prev.
  induction ls1 as [|lc ls1 IH] => runs1 l prev Hlen.
  - destruct runs1; [| discriminate]. simpl.
    iSplit.
    + iIntros "H". iExists prev, l. by iFrame.
    + iIntros "(%ml & %mf & [%H1 %H2] & H)". subst. by iFrame.
  - destruct runs1 as [|r runs1]; [discriminate |].
    injection Hlen as Hlen. simpl.
    iSplit.
    + iIntros "H".
      iDestruct "H" as "(%Hloc & %Hpc & %Hrun & H)".
      iDestruct "H" as (nxt0) "[Hnode Hrest]".
      iEval (rewrite (IH _ _ _ Hlen)) in "Hrest".
      iDestruct "Hrest" as (ml mf) "[H1 H2]".
      iExists ml, mf. iFrame "H2".
      iSplitR; [by iPureIntro |].
      iSplitR; [by iPureIntro |].
      iSplitR; [by iPureIntro |].
      iExists nxt0. iFrame "Hnode H1".
    + iIntros "H". iDestruct "H" as (ml mf) "[H1 H2]".
      iDestruct "H1" as "(%Hloc & %Hpc & %Hrun & H1)".
      iDestruct "H1" as (nxt0) "[Hnode Hrest]".
      iSplitR; [by iPureIntro |].
      iSplitR; [by iPureIntro |].
      iSplitR; [by iPureIntro |].
      iExists nxt0. iFrame "Hnode".
      iEval (rewrite (IH _ _ _ Hlen)).
      iExists ml, mf. iFrame "Hrest H2".
Qed.

(** Splice a fresh node between two run-granular segments whose boundary
    links already point at it: the run form of [own_dll_insert_middle],
    which [Store.Integrate]'s stage-4 rewrite splices with. *)
Lemma own_dll_runs_insert_middle (dq : dfrac) (parent : loc)
    (ls1 ls2 : list loc) (runs1 runs2 : list ItemRun)
    (newl : loc) (r : ItemRun) (hd tl ml mr : loc) :
  length ls1 = length runs1 ->
  newl ≠ null ->
  run_wf (run_items r) ->
  run_per_char r ->
  own_dll_runs dq parent hd ml null newl ls1 runs1 ∗
  own_item_node newl dq (input_of_run r) (run_deleted r) parent ml mr ∗
  own_dll_runs dq parent mr tl newl null ls2 runs2
  ⊢ own_dll_runs dq parent hd tl null null (ls1 ++ newl :: ls2) (runs1 ++ r :: runs2).
Proof.
  move=> Hlen Hnn Hwf Hpc.
  iIntros "(H1 & Hnode & H2)".
  rewrite (own_dll_runs_app dq parent hd tl null null ls1 (newl :: ls2)
             runs1 (r :: runs2) Hlen).
  iExists ml, newl. iFrame "H1". simpl.
  iSplitR; [by iPureIntro |].
  iSplitR; [by iPureIntro |].
  iSplitR; [by iPureIntro |].
  iExists mr. iFrame "Hnode H2".
Qed.

(** The run-granular spine aligns addresses with runs. *)
Lemma own_dll_runs_length (dq : dfrac) (parent l last prev next : loc)
    (ls : list loc) (runs : list ItemRun) :
  own_dll_runs dq parent l last prev next ls runs -∗ ⌜length ls = length runs⌝.
Proof.
  iIntros "H".
  iInduction ls as [|lc ls] "IH" forall (runs l prev); destruct runs as [|r runs]; simpl.
  - done.
  - iDestruct "H" as %[].
  - iDestruct "H" as %[].
  - iDestruct "H" as "(%Hloc & %Hpc & %Hrun & H)".
    iDestruct "H" as (nxt0) "[Hnode Hrest]".
    iDestruct ("IH" with "Hrest") as %Hlen.
    iPureIntro. lia.
Qed.

(** Borrow the [k]-th node of a run-granular segment WHOLE, as
    [own_item_node] with existential spine links; the wand takes back any
    struct satisfying the pins and restores the segment. The run form of
    [own_dll_lookup_acc_node]; no address facts are exposed, since the
    caller already holds the address list. *)
Lemma own_dll_runs_lookup_acc (dq : dfrac) (parent l lst prev nxt : loc)
    (ls : list loc) (runs : list ItemRun) (k : nat) (lc : loc) (r : ItemRun) :
  ls !! k = Some lc ->
  runs !! k = Some r ->
  own_dll_runs dq parent l lst prev nxt ls runs -∗
    ∃ (prev' nxt' : loc),
      "Hnode" ∷ own_item_node lc dq (input_of_run r) (run_deleted r) parent prev' nxt' ∗
      "Hback" ∷ (own_item_node lc dq (input_of_run r) (run_deleted r) parent prev' nxt' -∗
                 own_dll_runs dq parent l lst prev nxt ls runs).
Proof.
  move=> Hlk Hrk. iIntros "H".
  iDestruct (own_dll_runs_length with "H") as %Hlen.
  pose proof (take_drop_middle ls k lc Hlk) as Hsplitl.
  pose proof (take_drop_middle runs k r Hrk) as Hsplitr.
  set (prel := take k ls) in Hsplitl.
  set (sufl := drop (S k) ls) in Hsplitl.
  set (prer := take k runs) in Hsplitr.
  set (sufr := drop (S k) runs) in Hsplitr.
  have Hlent : length prel = length prer.
  { rewrite /prel /prer !length_take Hlen //. }
  iEval (rewrite -Hsplitl -Hsplitr (own_dll_runs_app _ _ _ _ _ _ _ _ _ _ Hlent)) in "H".
  iDestruct "H" as (ml mf) "[Hpre Hrest]".
  iDestruct "Hrest" as "(%Hloc & %Hpc & %Hrun & Hrest)".
  iDestruct "Hrest" as (nxt0) "[Hnode Hrest2]".
  iExists ml, nxt0.
  iFrame "Hnode".
  iIntros "Hnode".
  iEval (rewrite -Hsplitl -Hsplitr (own_dll_runs_app _ _ _ _ _ _ _ _ _ _ Hlent)).
  iExists ml, mf.
  iFrame "Hpre".
  iSplitR; [by iPureIntro |].
  iSplitR; [by iPureIntro |].
  iSplitR; [by iPureIntro |].
  iExists nxt0.
  iFrame "Hnode Hrest2".
Qed.

(** Borrow the [k]-th node for an update: the wand takes the node back at
    ANY tombstone bit [d'] and returns the segment with that run flipped to
    [d']. The run form of [own_dll_update_gen_node]. *)
Lemma own_dll_runs_update (parent l lst prev nxt : loc)
    (ls : list loc) (runs : list ItemRun) (k : nat) (lc : loc) (r : ItemRun) :
  ls !! k = Some lc ->
  runs !! k = Some r ->
  own_dll_runs (DfracOwn 1) parent l lst prev nxt ls runs -∗
    ∃ (prev' nxt' : loc),
      "Hnode" ∷ own_item_node lc (DfracOwn 1) (input_of_run r) (run_deleted r) parent prev' nxt' ∗
      "Hback" ∷ (∀ d' : bool,
         own_item_node lc (DfracOwn 1) (input_of_run r) d' parent prev' nxt' -∗
         own_dll_runs (DfracOwn 1) parent l lst prev nxt ls
           (<[k := MkItemRun (run_items r) d']> runs)).
Proof.
  move=> Hlk Hrk. iIntros "H".
  iDestruct (own_dll_runs_length with "H") as %Hlen.
  pose proof (take_drop_middle ls k lc Hlk) as Hsplitl.
  pose proof (take_drop_middle runs k r Hrk) as Hsplitr.
  set (prel := take k ls) in Hsplitl.
  set (sufl := drop (S k) ls) in Hsplitl.
  set (prer := take k runs) in Hsplitr.
  set (sufr := drop (S k) runs) in Hsplitr.
  have Hlent : length prel = length prer.
  { rewrite /prel /prer !length_take Hlen //. }
  iEval (rewrite -Hsplitl -Hsplitr (own_dll_runs_app _ _ _ _ _ _ _ _ _ _ Hlent)) in "H".
  iDestruct "H" as (ml mf) "[Hpre Hrest]".
  iDestruct "Hrest" as "(%Hloc & %Hpc & %Hrun & Hrest)".
  iDestruct "Hrest" as (nxt0) "[Hnode Hrest2]".
  iExists ml, nxt0.
  iFrame "Hnode".
  iIntros (d') "Hnode".
  have Hins : <[k := MkItemRun (run_items r) d']> runs
            = prer ++ MkItemRun (run_items r) d' :: sufr.
  { rewrite /prer /sufr. apply insert_take_drop.
    apply lookup_lt_Some in Hrk; exact Hrk. }
  iEval (rewrite Hins -Hsplitl (own_dll_runs_app _ _ _ _ _ _ _ _ _ _ Hlent)).
  iExists ml, mf.
  iFrame "Hpre".
  iSplitR; [by iPureIntro |].
  iSplitR; [iPureIntro; rewrite /run_per_char /=; exact Hpc |].
  iSplitR; [iPureIntro; rewrite /=; exact Hrun |].
  iExists nxt0.
  iFrame "Hnode Hrest2".
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



Lemma own_dll_last_agree dq1 dq2 (l la1 la2 prev next : loc) (cells : list item_cell) :
  own_dll dq1 l la1 prev next cells -∗ own_dll dq2 l la2 prev next cells -∗ ⌜la1 = la2⌝.
Proof.
  revert l la1 la2 prev next.
  induction cells as [|c rest IH]; intros l la1 la2 prev next; simpl.
  - iIntros "[%H1a %H1b] [%H2a %H2b]". subst. done.
  - iIntros "H1 H2".
    iDestruct "H1" as (iv1 ol1 or1) "H1". iNamedSuffix "H1" "1".
    iDestruct "H2" as (iv2 ol2 or2) "H2". iNamedSuffix "H2" "2".
    iCombine "Hval1 Hval2" gives %->.
    iApply (IH with "Hrest1 Hrest2").
Qed.

(** Every cell of a DLL segment carries a well-formed run (pure extraction;
    the run-aware counterpart of the unit scaffold's per-cell length pin). *)
Lemma own_dll_runs_wf (dq : dfrac) (l last prev next : loc) (cells : list item_cell) :
  own_dll dq l last prev next cells -∗
  ⌜∀ c, c ∈ cells → run_wf (ic_run c)⌝.
Proof.
  iInduction cells as [|c0 cells] "IH" forall (l prev).
  - iIntros "_". iPureIntro. move=> c Hc. rewrite elem_of_nil in Hc. done.
  - iIntros "H". iNamed "H".
    iDestruct ("IH" with "Hrest") as %Hrest.
    iPureIntro. move=> c Hc.
    apply elem_of_cons in Hc as [-> | Hc]; last exact (Hrest c Hc).
    exact Hrun.
Qed.

End item_heap.
