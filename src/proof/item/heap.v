(** The [item] type, Iris layer over [item/value.v].

    Definitions
    - [item_or_null p ov]: a heap item pointer is null or owns a node.
    - [own_item_node l dq input deleted parent prev nxt]: one heap [Item]
      node in full: the wire item it denotes, its tombstone bit, its parent
      and its two spine links. This is what the spine is made of and what
      the borrow lemmas hand out.
    - [own_dll dq parent l last prev next ls runs]: THE doubly-linked
      list,: node addresses paired with the runs they
      hold, one [own_item_node] per node, each node pinning its run's
      [run_wf] and [run_per_char]. An owning predicate, so
      [dfrac]-parameterized ([DfracOwn 1] to mutate), and fractional
      ([own_dll_fractional]). Adapted from the reference sorted-DLL
      proof (iasakura/perennial-sandbox, dll/list.go, [is_dlist_node]).

    Laws
    - the spine is a monoid: [own_dll_app] splits and joins a segment,
      [own_dll_insert_middle] splices a fresh node in and
      [own_dll_split] rejoins a split node's two halves;
      [own_dll_length] aligns the address list with the run list.
    - endpoints: the head and last pointers are determined by the lists
      ([own_dll_headptr] / [own_dll_lastptr]), and
      [loc_at_lt_not_null] says an in-range address is not null.
    - access: [own_dll_lookup_acc] and [own_dll_update] borrow the
      [k]-th node whole (the update wand flipping its tombstone bit),
      [own_dll_acc] the same with the spine links named as the address
      list's neighbours, [own_dll_lookup_acc_2] borrows two nodes of one
      segment at once, and [own_dll_cons_unfold] / [_fold] take one node
      off a segment's head and put one back. [own_item_node_not_null] reads
      the address's non-nullness off the node.
    - freshness: a fully owned node is fresh for any segment
      ([own_dll_fresh], via [item_pointsto_conflict]), which is where
      the [NoDup] of addresses comes from.
    - the pure content of the spine, read off it: every run is chained
      ([own_dll_run_wf]) and every head id fits a machine word
      ([own_dll_id_bounds]).

    The per-node method specs are [item/wp_private.v]. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core prelude.
From New.proof.item Require Import run_theory model value.
From New.proof.id Require Import value heap.
From iris.bi.lib Require Import fractional.

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


(** [own_item_node l dq input deleted parent prev nxt]: one heap [Item] node
    in full: the struct and its two origin-id cells are existential, pinned
    to the wire item [input] (the [toYjsId] images of the id and the origins,
    [toContent] of the content), tombstoned iff [deleted] (the flag byte is
    [W8 6] / [W8 2], so a node is always Countable), under [parent], its
    [left'] / [right'] spine links at [prev] / [nxt]. The per-node payload
    [own_dll] holds and the borrow lemmas hand out; [own_linked_item]
    is its [DfracOwn 1] live form ([own_linked_item_as_node], [store/heap.v]). *)
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

(** [own_dll dq parent l last prev next ls runs]: one DLL segment, the node
    addresses [ls] paired with the runs they hold, every node one
    [own_item_node] at the wire item its run denotes, all under one type
    [parent]. Each run also carries [run_wf] and [run_per_char] (the wire
    view alone cannot recover how the content splits over the run's items). *)
Fixpoint own_dll (dq : dfrac) (parent l last prev next : loc)
    (ls : list loc) (runs : list ItemRun) : iProp Σ :=
  match ls, runs with
  | [], [] => ⌜l = next ∧ last = prev⌝
  | lc :: ls', r :: runs' =>
      "%Hloc" ∷ ⌜l = lc ∧ lc ≠ null⌝ ∗
      "%Hperchar" ∷ ⌜run_per_char r⌝ ∗
      "%Hrun" ∷ ⌜run_wf (run_items r)⌝ ∗
      ∃ (nxt0 : loc),
        "Hnode" ∷ own_item_node lc dq (input_of_run r) (run_deleted r) parent prev nxt0 ∗
        "Hrest" ∷ own_dll dq parent nxt0 last lc next ls' runs'
  | _, _ => False
  end.

(* ===== lemmas ============================================================= *)

(* ----- structural lemmas for the DLL spine ------------------------------- *)

(** A node's location is never null: the heap points-to inside says so. *)
Lemma own_item_node_not_null (l : loc) (dq : dfrac) (input : IntegrateInput (A := A))
    (deleted : bool) (parent prev nxt : loc) :
  own_item_node l dq input deleted parent prev nxt -∗
    ⌜l ≠ null⌝ ∗ own_item_node l dq input deleted parent prev nxt.
Proof.
  iIntros "Hnode". iDestruct "Hnode" as (v olid orid) "(Hval & Hrest)".
  iDestruct (typed_pointsto_not_null with "Hval") as %Hnn.
  iSplitR; first (iPureIntro; exact Hnn).
  iExists v, olid, orid. iFrame "Hval Hrest".
Qed.


(** Split / join a DLL segment at an aligned list append. *)
Lemma own_dll_app (dq : dfrac) (parent l last prev next : loc)
    (ls1 ls2 : list loc) (runs1 runs2 : list ItemRun) :
  length ls1 = length runs1 ->
  own_dll dq parent l last prev next (ls1 ++ ls2) (runs1 ++ runs2)
  ⊣⊢ ∃ ml mf,
     own_dll dq parent l ml prev mf ls1 runs1 ∗
     own_dll dq parent mf last ml next ls2 runs2.
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

(** Splice a fresh node between two segments whose boundary
    links already point at it: what [Store.Integrate] splices with. *)
Lemma own_dll_insert_middle (dq : dfrac) (parent : loc)
    (ls1 ls2 : list loc) (runs1 runs2 : list ItemRun)
    (newl : loc) (r : ItemRun) (hd tl ml mr : loc) :
  length ls1 = length runs1 ->
  newl ≠ null ->
  run_wf (run_items r) ->
  run_per_char r ->
  own_dll dq parent hd ml null newl ls1 runs1 ∗
  own_item_node newl dq (input_of_run r) (run_deleted r) parent ml mr ∗
  own_dll dq parent mr tl newl null ls2 runs2
  ⊢ own_dll dq parent hd tl null null (ls1 ++ newl :: ls2) (runs1 ++ r :: runs2).
Proof.
  move=> Hlen Hnn Hwf Hpc.
  iIntros "(H1 & Hnode & H2)".
  rewrite (own_dll_app dq parent hd tl null null ls1 (newl :: ls2)
             runs1 (r :: runs2) Hlen).
  iExists ml, newl. iFrame "H1". simpl.
  iSplitR; [by iPureIntro |].
  iSplitR; [by iPureIntro |].
  iSplitR; [by iPureIntro |].
  iExists mr. iFrame "Hnode H2".
Qed.

(** Unfold / fold one node off the front of a DLL segment. *)
Lemma own_dll_cons_unfold (dq : dfrac) (parent l lst prev nxt lc : loc)
    (ls : list loc) (r : ItemRun) (runs : list ItemRun) :
  own_dll dq parent l lst prev nxt (lc :: ls) (r :: runs) -∗
  ∃ nxt0 : loc,
    ⌜l = lc ∧ lc ≠ null⌝ ∗ ⌜run_per_char r⌝ ∗ ⌜run_wf (run_items r)⌝ ∗
    own_item_node lc dq (input_of_run r) (run_deleted r) parent prev nxt0 ∗
    own_dll dq parent nxt0 lst lc nxt ls runs.
Proof.
  simpl. iIntros "(%Hloc & %Hpc & %Hwf & H)".
  iDestruct "H" as (nxt0) "[Hnode Hrest]".
  iExists nxt0. iFrame "Hnode Hrest". by iPureIntro.
Qed.

Lemma own_dll_cons_fold (dq : dfrac) (parent lst prev nxt nxt0 lc : loc)
    (ls : list loc) (r : ItemRun) (runs : list ItemRun) :
  lc ≠ null -> run_wf (run_items r) -> run_per_char r ->
  own_item_node lc dq (input_of_run r) (run_deleted r) parent prev nxt0 ∗
  own_dll dq parent nxt0 lst lc nxt ls runs -∗
  own_dll dq parent lc lst prev nxt (lc :: ls) (r :: runs).
Proof.
  move=> Hnn Hwf Hpc. simpl. iIntros "[Hnode Hrest]".
  iSplitR; first (iPureIntro; done).
  iSplitR; first (iPureIntro; exact Hpc).
  iSplitR; first (iPureIntro; exact Hwf).
  iExists nxt0. iFrame "Hnode Hrest".
Qed.

(** Rejoin the two halves of a split node between two relinked
    segments. The halves' [run_wf] and [run_per_char] are premises; the split
    surgery itself is the pure [split_runs]. *)
Lemma own_dll_split (dq : dfrac) (parent : loc)
    (ls1 ls2 : list loc) (runs1 runs2 : list ItemRun)
    (lc rloc : loc) (r : ItemRun) (o : nat) (hd tl ml mr : loc) :
  length ls1 = length runs1 ->
  lc ≠ null ->
  rloc ≠ null ->
  run_per_char (split_run_left r o) ->
  run_per_char (split_run_right r o) ->
  run_wf (run_items (split_run_left r o)) ->
  run_wf (run_items (split_run_right r o)) ->
  own_dll dq parent hd ml null lc ls1 runs1 ∗
  own_item_node lc dq (input_of_run (split_run_left r o))
    (run_deleted (split_run_left r o)) parent ml rloc ∗
  own_item_node rloc dq (input_of_run (split_run_right r o))
    (run_deleted (split_run_right r o)) parent lc mr ∗
  own_dll dq parent mr tl rloc null ls2 runs2
  ⊢ own_dll dq parent hd tl null null
      (ls1 ++ [lc; rloc] ++ ls2)
      (runs1 ++ [split_run_left r o; split_run_right r o] ++ runs2).
Proof.
  move=> Hlen Hlcnn Hrlnn Hpcl Hpcr Hwfl Hwfr.
  iIntros "(H1 & Hnl & Hnr & H2)".
  rewrite (own_dll_app dq parent hd tl null null ls1 ([lc; rloc] ++ ls2)
             runs1 ([split_run_left r o; split_run_right r o] ++ runs2) Hlen).
  iExists ml, lc. iFrame "H1". simpl.
  iSplitR; [by iPureIntro |].
  iSplitR; [by iPureIntro |].
  iSplitR; [by iPureIntro |].
  iExists rloc. iFrame "Hnl".
  iSplitR; [by iPureIntro |].
  iSplitR; [by iPureIntro |].
  iSplitR; [by iPureIntro |].
  iExists mr. iFrame "Hnr H2".
Qed.

(** The spine aligns addresses with runs. *)
Lemma own_dll_length (dq : dfrac) (parent l last prev next : loc)
    (ls : list loc) (runs : list ItemRun) :
  own_dll dq parent l last prev next ls runs -∗ ⌜length ls = length runs⌝.
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

(** The head and last pointers of a segment are its address
    list's ends; the resource is returned. *)
Lemma own_dll_headptr (dq : dfrac) (parent l lst prev nxt : loc)
    (ls : list loc) (runs : list ItemRun) :
  own_dll dq parent l lst prev nxt ls runs -∗
    ⌜l = default nxt (head ls)⌝ ∗ own_dll dq parent l lst prev nxt ls runs.
Proof.
  destruct ls as [|lc ls']; destruct runs as [|r runs'].
  - iIntros "H". iDestruct "H" as %[Hl Hlst].
    iSplit; iPureIntro; [rewrite /= Hl // | done].
  - iIntros "H". iDestruct "H" as %[].
  - iIntros "H". iDestruct "H" as %[].
  - iIntros "H". iDestruct "H" as "(%Hloc & %Hpc & %Hrun & H)".
    iSplitR; first (iPureIntro; rewrite /=; exact (proj1 Hloc)).
    iSplitR; first by iPureIntro.
    iSplitR; first by iPureIntro.
    iSplitR; first by iPureIntro.
    iExact "H".
Qed.

Lemma own_dll_lastptr (dq : dfrac) (parent l lst prev nxt : loc)
    (ls : list loc) (runs : list ItemRun) :
  own_dll dq parent l lst prev nxt ls runs -∗
    ⌜lst = default prev (list.last ls)⌝ ∗ own_dll dq parent l lst prev nxt ls runs.
Proof.
  iInduction ls as [|lc ls' IH] "IH" forall (runs l prev); destruct runs as [|r runs'].
  - iIntros "H". iDestruct "H" as %[Hl Hlst].
    iSplit; iPureIntro; [rewrite /= Hlst // | done].
  - iIntros "H". iDestruct "H" as %[].
  - iIntros "H". iDestruct "H" as %[].
  - iIntros "H". iDestruct "H" as "(%Hloc & %Hpc & %Hrun & H)".
    iDestruct "H" as (nxt0) "[Hnode Hrest]".
    iDestruct ("IH" with "Hrest") as "[%Hlst Hrest]".
    iSplitR.
    { iPureIntro. rewrite last_cons. destruct (list.last ls') as [y|] eqn:Hl.
      - by rewrite Hlst /=.
      - rewrite /= in Hlst. rewrite Hlst. by destruct Hloc as [-> _]. }
    iSplitR; first by iPureIntro.
    iSplitR; first by iPureIntro.
    iSplitR; first by iPureIntro.
    iExists nxt0. iFrame "Hnode Hrest".
Qed.

(** Borrow the [k]-th node of a WHOLE DLL, with its spine links
    named as the address list's neighbours ([loc_at]); the wand gives the
    node back and restores the DLL: what a walk over [(ls, runs)] reads its
    cursor through. *)
Lemma own_dll_acc (dq : dfrac) (parent hd tl : loc)
    (ls : list loc) (runs : list ItemRun) (k : nat) (lc : loc) (r : ItemRun) :
  ls !! k = Some lc ->
  runs !! k = Some r ->
  own_dll dq parent hd tl null null ls runs -∗
    ∃ (prev' nxt' : loc),
      "%Hcl" ∷ ⌜prev' = loc_at ls (Z.of_nat k - 1)⌝ ∗
      "%Hcr" ∷ ⌜nxt' = loc_at ls (Z.of_nat k + 1)⌝ ∗
      "%Hrun" ∷ ⌜run_wf (run_items r)⌝ ∗
      "%Hperchar" ∷ ⌜run_per_char r⌝ ∗
      "%Hclen" ∷ ⌜length (items_string (run_items r)) = length (run_items r)⌝ ∗
      "Hnode" ∷ own_item_node lc dq (input_of_run r) (run_deleted r) parent prev' nxt' ∗
      "Hback" ∷ (own_item_node lc dq (input_of_run r) (run_deleted r) parent prev' nxt' -∗
                 own_dll dq parent hd tl null null ls runs).
Proof.
  move=> Hlk Hrk. iIntros "H".
  iDestruct (own_dll_length with "H") as %Hlen.
  have Hpe : default null (list.last (take k ls)) = loc_at ls (Z.of_nat k - 1).
  { destruct k as [|k'].
    - rewrite take_0 /= /loc_at. case_decide as Hdec; [exfalso; lia | done].
    - have Hk' : (k' < length ls)%nat by (apply lookup_lt_Some in Hlk; lia).
      destruct (ls !! k') as [l'|] eqn:Hlk'; last by (apply lookup_ge_None in Hlk'; lia).
      rewrite (take_S_r ls k' l' Hlk') last_snoc /= /loc_at decide_True; last lia.
      have -> : Z.to_nat (Z.of_nat (S k') - 1) = k' by lia.
      by rewrite Hlk' /=. }
  have Hhe : default null (head (drop (S k) ls)) = loc_at ls (Z.of_nat k + 1).
  { rewrite /loc_at decide_True; last lia.
    have HZ : Z.to_nat (Z.of_nat k + 1) = S k by lia.
    rewrite HZ head_lookup lookup_drop Nat.add_0_r //. }
  pose proof (take_drop_middle ls k lc Hlk) as Hsplitl.
  pose proof (take_drop_middle runs k r Hrk) as Hsplitr.
  set (prel := take k ls) in Hsplitl.
  set (sufl := drop (S k) ls) in Hsplitl.
  set (prer := take k runs) in Hsplitr.
  set (sufr := drop (S k) runs) in Hsplitr.
  have Hlent : length prel = length prer.
  { rewrite /prel /prer !length_take Hlen //. }
  iEval (rewrite -Hsplitl -Hsplitr (own_dll_app _ _ _ _ _ _ _ _ _ _ Hlent)) in "H".
  iDestruct "H" as (ml mf) "[Hpre Hrest]".
  iDestruct "Hrest" as "(%Hloc & %Hpc & %Hrun & Hrest)".
  iDestruct "Hrest" as (nxt0) "[Hnode Hrest2]".
  iDestruct (own_dll_lastptr with "Hpre") as "[%Hml Hpre]".
  iDestruct (own_dll_headptr with "Hrest2") as "[%Hhd Hrest2]".
  have Hclen : length (items_string (run_items r)) = length (run_items r).
  { have Hleq := f_equal length Hpc.
    rewrite length_fmap explode_length in Hleq. lia. }
  iExists ml, nxt0.
  iSplitR; first (iPureIntro; rewrite Hml -Hpe //).
  iSplitR; first (iPureIntro; rewrite Hhd -Hhe //).
  iSplitR; first by iPureIntro.
  iSplitR; first by iPureIntro.
  iSplitR; first by iPureIntro.
  iFrame "Hnode".
  iIntros "Hnode".
  iEval (rewrite -Hsplitl -Hsplitr (own_dll_app _ _ _ _ _ _ _ _ _ _ Hlent)).
  iExists ml, mf.
  iFrame "Hpre".
  iSplitR; first by iPureIntro.
  iSplitR; first by iPureIntro.
  iSplitR; first by iPureIntro.
  iExists nxt0. iFrame "Hnode Hrest2".
Qed.

(** Borrow the [k]-th node of a segment WHOLE, as
    [own_item_node] with existential spine links; the wand takes back any
    struct satisfying the pins and restores the segment; no address facts
    are exposed, since the caller already holds the address list. *)
Lemma own_dll_lookup_acc (dq : dfrac) (parent l lst prev nxt : loc)
    (ls : list loc) (runs : list ItemRun) (k : nat) (lc : loc) (r : ItemRun) :
  ls !! k = Some lc ->
  runs !! k = Some r ->
  own_dll dq parent l lst prev nxt ls runs -∗
    ∃ (prev' nxt' : loc),
      "Hnode" ∷ own_item_node lc dq (input_of_run r) (run_deleted r) parent prev' nxt' ∗
      "Hback" ∷ (own_item_node lc dq (input_of_run r) (run_deleted r) parent prev' nxt' -∗
                 own_dll dq parent l lst prev nxt ls runs).
Proof.
  move=> Hlk Hrk. iIntros "H".
  iDestruct (own_dll_length with "H") as %Hlen.
  pose proof (take_drop_middle ls k lc Hlk) as Hsplitl.
  pose proof (take_drop_middle runs k r Hrk) as Hsplitr.
  set (prel := take k ls) in Hsplitl.
  set (sufl := drop (S k) ls) in Hsplitl.
  set (prer := take k runs) in Hsplitr.
  set (sufr := drop (S k) runs) in Hsplitr.
  have Hlent : length prel = length prer.
  { rewrite /prel /prer !length_take Hlen //. }
  iEval (rewrite -Hsplitl -Hsplitr (own_dll_app _ _ _ _ _ _ _ _ _ _ Hlent)) in "H".
  iDestruct "H" as (ml mf) "[Hpre Hrest]".
  iDestruct "Hrest" as "(%Hloc & %Hpc & %Hrun & Hrest)".
  iDestruct "Hrest" as (nxt0) "[Hnode Hrest2]".
  iExists ml, nxt0.
  iFrame "Hnode".
  iIntros "Hnode".
  iEval (rewrite -Hsplitl -Hsplitr (own_dll_app _ _ _ _ _ _ _ _ _ _ Hlent)).
  iExists ml, mf.
  iFrame "Hpre".
  iSplitR; [by iPureIntro |].
  iSplitR; [by iPureIntro |].
  iSplitR; [by iPureIntro |].
  iExists nxt0.
  iFrame "Hnode Hrest2".
Qed.

(** Borrow two nodes of a DLL at once, the earlier one first. *)
Lemma own_dll_lookup_acc_2 (dq : dfrac) (parent l lst prev nxt : loc)
    (ls : list loc) (runs : list ItemRun) (k1 k2 : nat) (l1 l2 : loc) (r1 r2 : ItemRun) :
  (k1 < k2)%nat ->
  ls !! k1 = Some l1 -> runs !! k1 = Some r1 ->
  ls !! k2 = Some l2 -> runs !! k2 = Some r2 ->
  own_dll dq parent l lst prev nxt ls runs -∗
    ∃ (prev1 nxt1 prev2 nxt2 : loc),
      "Hnode1" ∷ own_item_node l1 dq (input_of_run r1) (run_deleted r1) parent prev1 nxt1 ∗
      "Hnode2" ∷ own_item_node l2 dq (input_of_run r2) (run_deleted r2) parent prev2 nxt2 ∗
      "Hback" ∷ (own_item_node l1 dq (input_of_run r1) (run_deleted r1) parent prev1 nxt1 -∗
                 own_item_node l2 dq (input_of_run r2) (run_deleted r2) parent prev2 nxt2 -∗
                 own_dll dq parent l lst prev nxt ls runs).
Proof.
  move=> Hk12 Hl1 Hr1 Hl2 Hr2. iIntros "H".
  iDestruct (own_dll_length with "H") as %Hlen.
  pose proof (take_drop_middle ls k1 l1 Hl1) as Hsl1.
  pose proof (take_drop_middle runs k1 r1 Hr1) as Hsr1.
  set (prel := take k1 ls) in Hsl1.
  set (sufl := drop (S k1) ls) in Hsl1.
  set (prer := take k1 runs) in Hsr1.
  set (sufr := drop (S k1) runs) in Hsr1.
  have Hlent1 : length prel = length prer.
  { rewrite /prel /prer !length_take Hlen //. }
  iEval (rewrite -Hsl1 -Hsr1 (own_dll_app _ _ _ _ _ _ _ _ _ _ Hlent1)) in "H".
  iDestruct "H" as (ml mf) "[Hpre Hrest]".
  iDestruct "Hrest" as "(%Hloc & %Hpc & %Hrun1 & Hrest)".
  iDestruct "Hrest" as (nxt0) "[Hnode1 Hsuf]".
  have Hl2' : sufl !! (k2 - S k1)%nat = Some l2.
  { rewrite /sufl lookup_drop. replace (S k1 + (k2 - S k1))%nat with k2 by lia. exact Hl2. }
  have Hr2' : sufr !! (k2 - S k1)%nat = Some r2.
  { rewrite /sufr lookup_drop. replace (S k1 + (k2 - S k1))%nat with k2 by lia. exact Hr2. }
  iDestruct (own_dll_lookup_acc _ _ _ _ _ _ _ _ _ _ _ Hl2' Hr2' with "Hsuf") as (prev2 nxt2) "[Hnode2 Hback2]".
  iExists ml, nxt0, prev2, nxt2.
  iFrame "Hnode1 Hnode2".
  iIntros "Hnode1 Hnode2".
  iDestruct ("Hback2" with "Hnode2") as "Hsuf".
  iEval (rewrite -Hsl1 -Hsr1 (own_dll_app _ _ _ _ _ _ _ _ _ _ Hlent1)).
  iExists ml, mf.
  iFrame "Hpre".
  iSplitR; [by iPureIntro |].
  iSplitR; [by iPureIntro |].
  iSplitR; [by iPureIntro |].
  iExists nxt0.
  iFrame "Hnode1 Hsuf".
Qed.

(** An in-range address of a DLL is never null; the resource is
    returned. *)
Lemma loc_at_lt_not_null (dq : dfrac) (parent hd tl : loc)
    (ls : list loc) (runs : list ItemRun) (k : nat) :
  (k < length ls)%nat ->
  own_dll dq parent hd tl null null ls runs -∗
    ⌜loc_at ls (Z.of_nat k) ≠ null⌝ ∗ own_dll dq parent hd tl null null ls runs.
Proof.
  move=> Hk. iIntros "H".
  iDestruct (own_dll_length with "H") as %Hlen.
  destruct (ls !! k) as [lc|] eqn:Hlk; last by (apply lookup_ge_None in Hlk; lia).
  destruct (runs !! k) as [r|] eqn:Hrk; last by (apply lookup_ge_None in Hrk; lia).
  iDestruct (own_dll_acc dq parent hd tl ls runs k lc r Hlk Hrk with "H")
    as (prev' nxt') "(%Hcl & %Hcr & %Hrun & %Hpc & %Hclen & Hnode & Hback)".
  iDestruct (own_item_node_not_null with "Hnode") as "[%Hnn Hnode]".
  iSplitR.
  - iPureIntro. rewrite /loc_at decide_True; last lia. rewrite Nat2Z.id Hlk /=. exact Hnn.
  - iApply ("Hback" with "Hnode").
Qed.

(** Borrow the [k]-th node for an update: the wand takes the node back at
    ANY tombstone bit [d'] and returns the segment with that run flipped to
    [d']. *)
Lemma own_dll_update (parent l lst prev nxt : loc)
    (ls : list loc) (runs : list ItemRun) (k : nat) (lc : loc) (r : ItemRun) :
  ls !! k = Some lc ->
  runs !! k = Some r ->
  own_dll (DfracOwn 1) parent l lst prev nxt ls runs -∗
    ∃ (prev' nxt' : loc),
      "%Hrun" ∷ ⌜run_wf (run_items r)⌝ ∗
      "%Hperchar" ∷ ⌜run_per_char r⌝ ∗
      "%Hclen" ∷ ⌜length (items_string (run_items r)) = length (run_items r)⌝ ∗
      "Hnode" ∷ own_item_node lc (DfracOwn 1) (input_of_run r) (run_deleted r) parent prev' nxt' ∗
      "Hback" ∷ (∀ d' : bool,
         own_item_node lc (DfracOwn 1) (input_of_run r) d' parent prev' nxt' -∗
         own_dll (DfracOwn 1) parent l lst prev nxt ls
           (<[k := MkItemRun (run_items r) d']> runs)).
Proof.
  move=> Hlk Hrk. iIntros "H".
  iDestruct (own_dll_length with "H") as %Hlen.
  pose proof (take_drop_middle ls k lc Hlk) as Hsplitl.
  pose proof (take_drop_middle runs k r Hrk) as Hsplitr.
  set (prel := take k ls) in Hsplitl.
  set (sufl := drop (S k) ls) in Hsplitl.
  set (prer := take k runs) in Hsplitr.
  set (sufr := drop (S k) runs) in Hsplitr.
  have Hlent : length prel = length prer.
  { rewrite /prel /prer !length_take Hlen //. }
  iEval (rewrite -Hsplitl -Hsplitr (own_dll_app _ _ _ _ _ _ _ _ _ _ Hlent)) in "H".
  iDestruct "H" as (ml mf) "[Hpre Hrest]".
  iDestruct "Hrest" as "(%Hloc & %Hpc & %Hrun & Hrest)".
  iDestruct "Hrest" as (nxt0) "[Hnode Hrest2]".
  have Hclen : length (items_string (run_items r)) = length (run_items r).
  { have Hleq := f_equal length Hpc.
    rewrite length_fmap explode_length in Hleq. lia. }
  iExists ml, nxt0.
  iSplitR; first by iPureIntro.
  iSplitR; first by iPureIntro.
  iSplitR; first by iPureIntro.
  iFrame "Hnode".
  iIntros (d') "Hnode".
  have Hins : <[k := MkItemRun (run_items r) d']> runs
            = prer ++ MkItemRun (run_items r) d' :: sufr.
  { rewrite /prer /sufr. apply insert_take_drop.
    apply lookup_lt_Some in Hrk; exact Hrk. }
  iEval (rewrite Hins -Hsplitl (own_dll_app _ _ _ _ _ _ _ _ _ _ Hlent)).
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


(** A fully-owned node's address is outside a segment's address
    list: the [NoDup] source when a fresh node is spliced in. *)
Lemma own_dll_fresh (dq : dfrac) (q : loc) (v : yjs.item.t)
    (parent l last prev next : loc) (ls : list loc) (runs : list ItemRun) :
  q ↦ v -∗ own_dll dq parent l last prev next ls runs -∗ ⌜q ∉ ls⌝.
Proof.
  iIntros "Hq Hdll".
  iInduction ls as [|lc ls] "IH" forall (runs l prev); destruct runs as [|r runs]; simpl.
  - iPureIntro. apply not_elem_of_nil.
  - iDestruct "Hdll" as %[].
  - iDestruct "Hdll" as %[].
  - iDestruct "Hdll" as "(%Hloc & %Hpc & %Hrun & H)".
    iDestruct "H" as (nxt0) "[Hnode Hrest]".
    iDestruct "Hnode" as (v' olid orid) "(Hval & Hrestnode)".
    destruct (decide (q = lc)) as [-> | Hne].
    + iExFalso. iApply (item_pointsto_conflict with "Hq Hval").
    + iDestruct ("IH" with "Hq Hrest") as %Hrest.
      iPureIntro. rewrite not_elem_of_cons. by split.
Qed.


(** The same read directly off the run spine, plus the head id's word
    bounds: what the pool-level extractions are built from. *)
Lemma own_dll_run_wf (dq : dfrac) (parent l last prev next : loc)
    (ls : list loc) (runs : list ItemRun) :
  own_dll dq parent l last prev next ls runs -∗
  ⌜∀ r, r ∈ runs -> run_wf (run_items r)⌝.
Proof.
  iInduction ls as [|lc ls] "IH" forall (l prev runs).
  - destruct runs as [|r runs]; last (iIntros "[]").
    iIntros "_". iPureIntro. move=> r Hr. by apply elem_of_nil in Hr.
  - destruct runs as [|r0 runs]; first (iIntros "[]").
    iIntros "H". iNamed "H". iDestruct "H" as (nxt0) "H". iNamed "H".
    iDestruct ("IH" with "Hrest") as %Hrest.
    iPureIntro. move=> r Hr.
    apply elem_of_cons in Hr as [-> | Hr]; last exact (Hrest r Hr).
    exact Hrun.
Qed.

(** The run spine is fractional: the share of every node splits and the
    tail splits by induction, and combining agrees on each node's struct
    (hence on its next pointer). What makes a type's run view, and the
    pool's, fractional for the read path. *)
#[global] Instance own_dll_fractional parent l last prev next ls runs :
  Fractional (λ q, own_dll (DfracOwn q) parent l last prev next ls runs).
Proof.
  intros q1 q2. revert l prev runs.
  induction ls as [|lc ls IH]; intros l prev runs; destruct runs as [|r runs]; simpl;
    try (iSplit; [iIntros "[]" | iIntros "[[] _]"]).
  - iSplit; [ iIntros "#H"; iSplit; iFrame "H" | iIntros "[H _]"; iFrame "H" ].
  - iSplit.
    + iIntros "H". iNamed "H". iDestruct "H" as (nxt0) "H". iNamed "H".
      iDestruct "Hnode" as (v olid orid) "H". iNamed "H".
      iDestruct "Holeft" as "#Holeft". iDestruct "Horight" as "#Horight".
      iDestruct "Hval" as "[Hv1 Hv2]".
      iDestruct (IH with "Hrest") as "[Hr1 Hr2]".
      iSplitL "Hv1 Hr1".
      * iSplitR; first done. iSplitR; first done. iSplitR; first done.
        iExists nxt0. iSplitL "Hv1"; last iExact "Hr1".
        iExists v, olid, orid. iFrame "Hv1 Holeft Horight". done.
      * iSplitR; first done. iSplitR; first done. iSplitR; first done.
        iExists nxt0. iSplitL "Hv2"; last iExact "Hr2".
        iExists v, olid, orid. iFrame "Hv2 Holeft Horight". done.
    + iIntros "[H1 H2]".
      iNamedSuffix "H1" "1". iDestruct "H1" as (nxt1) "H1". iNamedSuffix "H1" "1".
      iNamedSuffix "H2" "2". iDestruct "H2" as (nxt2) "H2". iNamedSuffix "H2" "2".
      iDestruct "Hnode1" as (v1 olid1 orid1) "Hn1". iNamedSuffix "Hn1" "1".
      iDestruct "Hnode2" as (v2 olid2 orid2) "Hn2". iNamedSuffix "Hn2" "2".
      iDestruct "Holeft1" as "#Holeft1". iDestruct "Horight1" as "#Horight1".
      iCombine "Hval1 Hval2" gives %Hv. subst v2.
      have Hnxt : nxt2 = nxt1 by rewrite -Hnext1 -Hnext2.
      rewrite Hnxt.
      iCombine "Hval1 Hval2" as "Hval".
      iDestruct (IH with "[$Hrest1 $Hrest2]") as "Hrest".
      iSplitR; first done. iSplitR; first done. iSplitR; first done.
      iExists nxt1. iSplitL "Hval"; last iExact "Hrest".
      iExists v1, olid1, orid1. iFrame "Hval Holeft1 Horight1". done.
Qed.

Lemma own_dll_id_bounds (dq : dfrac) (parent l last prev next : loc)
    (ls : list loc) (runs : list ItemRun) :
  own_dll dq parent l last prev next ls runs -∗
  ⌜∀ r, r ∈ runs -> (Z.of_nat (run_client r) < 2^64)%Z ∧
                    (Z.of_nat (run_clock r) < 2^64)%Z⌝.
Proof.
  iInduction ls as [|lc ls] "IH" forall (l prev runs).
  - destruct runs as [|r runs]; last (iIntros "[]").
    iIntros "_". iPureIntro. move=> r Hr. by apply elem_of_nil in Hr.
  - destruct runs as [|r0 runs]; first (iIntros "[]").
    iIntros "H". iNamed "H". iDestruct "H" as (nxt0) "H". iNamed "H".
    iDestruct ("IH" with "Hrest") as %Hrest.
    iDestruct "Hnode" as (v olid orid) "(_ & _ & _ & _ & _ & %Hid & _)".
    iPureIntro. move=> r Hr.
    apply elem_of_cons in Hr as [-> | Hr]; last exact (Hrest r Hr).
    rewrite /run_client /run_clock.
    have Hidr : item_id (run_head_item r0) = toYjsId v.(yjs.item.id').
    { rewrite Hid /input_of_run //. }
    rewrite Hidr /toYjsId /=. split; word.
Qed.


End item_heap.
