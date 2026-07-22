(** The [yType] type: the heap representation of a root sequence and the WP spec
    of its visible-index navigation.

    In y-octo [YType] is the lock-guarded inner data structure while the [YText]
    handle lives outside the lock; this module owns the [YType] side and is closed
    over implementation ([yjs/ytype.go]), spec, and proof:

    - [own_ytype parent dq m]: the PUBLIC representation predicate — [parent] is
      a heap [yType] representing the abstract model [m : list (YjsItem A * bool)]
      (each document item with its tombstone bit; [m.*1] is the document list).
      The heap cells (node locations, spine links) are existentially hidden, so
      public specs speak only about [m]. [dfrac]-parameterized (idiom: plain
      owned heap data).
    - [own_ytype_cells parent dq cells arr]: the cells-level predicate under it —
      a heap [yType] whose [start] heads an item DLL ([own_dll], from
      [yjs_item]), isomorphic to a model list. [len] counts the visible
      (non-deleted) cells ([num_visible]); deletions tombstone cells without
      removing them, so [cells] / [arr] keep every item. Internal proofs
      ([findPos], the Integrate scan / splice, the Insert / Delete loops) work at
      this level because they track node locations.
    - [wp_yType__findPos]: the tombstone-aware walk to a visible character index,
      returning the straddling neighbours (an existential list position [p]);
      feeds the [Store.Integrate] loop in [Text.Insert] and [Text.Delete].
      Read-only, so stated at a generic [dq].

    Sits between [yjs_item] (the per-node / DLL / deletion layer it builds on) and
    [yjs_store] (which states [Store.Integrate] against these predicates). *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import yjs_core.
From New.proof Require Import yjs_common yjs_id yjs_item.

(* The [findPos] word-arithmetic proof writes [Z] comparisons unannotated, so fix
   [Z_scope] as the default (matching the environment it was developed in). *)
Local Open Scope Z_scope.

Section ytype.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.

(** [own_ytype_cells parent dq cells arr]: [parent] is a heap [yType] whose
    [start] heads the DLL [cells], which is isomorphic to the model [arr]. [len]
    counts the visible (non-deleted) cells ([num_visible]); a deletion tombstones
    a cell (set its [ic_deleted] bit) without removing it, so [cells] / [arr]
    keep every item. Every cell's [ic_parent] is this type's own loc (issue #49:
    items carry their parent; [store.repair]'s borrow-from-neighbour reads it). *)
Definition own_ytype_cells (parent : loc) (dq : dfrac)
    (cells : list item_cell) (arr : list (YjsItem A)) : iProp Σ :=
  ∃ (yt : yjs.yType.t) (tl : loc),
    "Hparent" ∷ parent ↦{dq} yt ∗
    "Hdll" ∷ own_dll dq yt.(yjs.yType.start') tl null null cells ∗
    "%Hlen" ∷ ⌜yt.(yjs.yType.len') = W64 (num_visible cells)⌝ ∗
    "%Hrepr" ∷ ⌜cells_repr arr cells arr⌝ ∗
    "%Hcpar" ∷ ⌜∀ c, c ∈ cells -> ic_parent c = parent⌝.

(* ----- the abstract model and the public predicate ----------------------- *)

(** The abstract per-char cells a heap cell denotes: each model item of its run
    paired with the cell's tombstone bit. The heap location is dropped — this
    is the abstraction wall (the model stays per-char; runs are invisible,
    issue #28). *)
Definition cell_models (c : item_cell) : list (YjsItem A * bool) :=
  (λ x, (x, ic_deleted c)) <$> ic_run c.

Definition cells_model (cells : list item_cell) : list (YjsItem A * bool) :=
  mjoin (cell_models <$> cells).

Lemma fmap_pair_fst (d : bool) (r : list (YjsItem A)) :
  ((λ x : YjsItem A, (x, d)) <$> r).*1 = r.
Proof. induction r as [|x r IH]; [done | by rewrite !fmap_cons IH]. Qed.

Lemma cells_model_fst (cells : list item_cell) :
  (cells_model cells).*1 = run_flatten cells.
Proof.
  induction cells as [|c cs IH]; first done.
  rewrite /cells_model /run_flatten /= fmap_app IH /cell_models fmap_pair_fst //.
Qed.

(** [own_ytype parent dq m]: the public [yType] predicate. [m] pairs each
    document (per-char) item with its tombstone bit, in document order; [m.*1]
    is the document list ([YjsArrInvariant] etc. are stated about it as pure
    side conditions of the specs, not baked in here). *)
Definition own_ytype (parent : loc) (dq : dfrac) (m : list (YjsItem A * bool)) : iProp Σ :=
  ∃ (cells : list item_cell),
    "Hcells" ∷ own_ytype_cells parent dq cells m.*1 ∗
    "%Hm" ∷ ⌜m = cells_model cells⌝.

(** Introduction: any cells-level view is the public view at its cell model
    (whose item list is the cells-level [arr]). *)
Lemma own_ytype_intro (parent : loc) (dq : dfrac)
    (cells : list item_cell) (arr : list (YjsItem A)) :
  own_ytype_cells parent dq cells arr ⊢
    own_ytype parent dq (cells_model cells) ∗ ⌜(cells_model cells).*1 = arr⌝.
Proof.
  iIntros "H". iDestruct "H" as (yt tl) "(Hp & Hdll & %Hlen & %Hrepr & %Hcpar)".
  have Harr : (cells_model cells).*1 = arr.
  { rewrite cells_model_fst. rewrite /cells_repr in Hrepr. rewrite Hrepr //. }
  iSplitL; last (iPureIntro; exact Harr).
  iExists cells. rewrite Harr. iSplitL; last done.
  iExists yt, tl. iFrame "Hp Hdll". iPureIntro. split_and!; [exact Hlen | exact Hrepr | exact Hcpar].
Qed.

(** General tombstone-aware [findPos]: walk to the visible character index [idx]
    and return the straddling neighbours plus the in-node offset. The Go walks
    two loops: a skip loop that advances past leading tombstones, then a count
    loop that spends the budget [idx] on visible ([Indexable]) nodes. Deletions
    make the answer a *list* position [p] (the node index, ≥ the visible index
    because tombstones are skipped), so the spec returns an existential [p ≤
    length cells] with the two straddle locations [node_loc cells (p-1)] /
    [node_loc cells p] (which are [null] out of range). When the budget lands
    strictly inside a multi-element run (issue #28) the returned [off] is
    nonzero and measures into the VISIBLE node at [p-1], strictly below its run
    length; [off] = 0 means a node-boundary position. The adjacent
    ([left]/[right]) pair is all the M1 [Insert] / [Delete] callers consume;
    the offset feeds the normalize/split path (M3). *)
Lemma wp_yType__findPos (parent : loc) (dq : dfrac) (cells : list item_cell)
    (arr : list (YjsItem A)) (idx : w64) :
  {{{ is_pkg_init yjs ∗ own_ytype_cells parent dq cells arr }}}
    parent @! (go.PointerType yjs.yType) @! "findPos" #idx
  {{{ (lft rgt : loc) (p : nat) (off : w64), RET (#lft, #rgt, #off);
      own_ytype_cells parent dq cells arr ∗
      ⌜(p <= length cells)%nat⌝ ∗
      ⌜lft = node_loc cells (Z.of_nat p - 1)⌝ ∗
      ⌜rgt = node_loc cells (Z.of_nat p)⌝ ∗
      ⌜off = W64 0 ∨
       (0 < uint.Z off)%Z ∧ (1 <= p)%nat ∧
       (∃ c, cells !! (p - 1)%nat = Some c ∧ ic_deleted c = false ∧
             (uint.nat off < length (ic_run c))%nat)⌝ }}}.
Proof.
  wp_start as "Hyt". iNamed "Hyt".
  iDestruct (own_dll_head_node dq cells _ tl with "Hdll") as %Hhead.
  destruct cells as [|c0 cs].
  - (* empty document: both loops are no-ops, return (null, null, 0) at p = 0 *)
    iDestruct "Hdll" as %[Hs Ht]. wp_auto. rewrite Hs.
    iAssert ("Hp" ∷ parent ↦{dq} yt ∗ "Hl" ∷ left_ptr ↦ null ∗ "Hr" ∷ right_ptr ↦ null ∗ "Hidx" ∷ index_ptr ↦ idx)%I
      with "[Hparent left right index]" as "IH".
    { iFrame. }
    wp_for "IH".
    iAssert ("Hp" ∷ parent ↦{dq} yt ∗ "Hl" ∷ left_ptr ↦ null ∗ "Hr" ∷ right_ptr ↦ null ∗ "Hrem" ∷ remaining_ptr ↦ idx ∗ "Hoff" ∷ offset_ptr ↦ (W64 0))%I
      with "[Hp Hl Hr remaining offset]" as "IH".
    { iFrame. }
    wp_for "IH".
    wp_if_destruct.
    + wp_auto. iApply ("HΦ" $! null null 0%nat (W64 0)). iSplitL "Hp".
      { iExists yt, null. iFrame "Hp". iPureIntro. split_and!; [exact Hs | reflexivity | exact Hlen | exact Hrepr | exact Hcpar]. }
      iPureIntro. split_and!; [lia | rewrite /node_loc; case_decide; reflexivity | rewrite /node_loc; case_decide; reflexivity | by left].
    + iApply ("HΦ" $! null null 0%nat (W64 0)). iSplitL "Hp".
      { iExists yt, null. iFrame "Hp". iPureIntro. split_and!; [exact Hs | reflexivity | exact Hlen | exact Hrepr | exact Hcpar]. }
      iPureIntro. split_and!; [lia | rewrite /node_loc; case_decide; reflexivity | rewrite /node_loc; case_decide; reflexivity | by left].
  - (* non-empty: skip leading tombstones, then count visible nodes to [idx] *)
    wp_auto.
    (* ----- skip loop invariant (runs before [remaining := index]) ----- *)
    iAssert (∃ (q : nat),
      "Hp" ∷ parent ↦{dq} yt ∗
      "Hdll" ∷ own_dll dq yt.(yjs.yType.start') tl null null (c0 :: cs) ∗
      "Hindex" ∷ index_ptr ↦ idx ∗
      "Hleftp" ∷ left_ptr ↦ node_loc (c0 :: cs) (Z.of_nat q - 1) ∗
      "Hrightp" ∷ right_ptr ↦ node_loc (c0 :: cs) (Z.of_nat q) ∗
      "%Hq" ∷ ⌜(q <= length (c0 :: cs))%nat⌝)%I
      with "[Hparent Hdll index left right]" as "IH".
    { iExists 0%nat. iFrame "Hparent Hdll index".
      replace (Z.of_nat 0 - 1)%Z with (-1)%Z by lia.
      have Hm1 : node_loc (c0 :: cs) (-1)%Z = null by (rewrite /node_loc; case_decide; [lia | done]).
      rewrite Hm1. iFrame "left".
      have Hr0 : node_loc (c0 :: cs) (Z.of_nat 0) = yt.(yjs.yType.start') by rewrite Hhead.
      rewrite Hr0. iFrame "right". iPureIntro. simpl; lia. }
    wp_for "IH".
    destruct (decide (q < length (c0 :: cs))%nat) as [Hqlt | Hqge].
    + (* right ≠ null: evaluate Deleted; tombstone ⇒ advance, else exit to count *)
      iDestruct (node_loc_lt_not_null dq (c0 :: cs) yt.(yjs.yType.start') tl q Hqlt with "Hdll") as "[%Hnn Hdll]".
      rewrite (bool_decide_eq_false_2 (node_loc (c0 :: cs) q = null) Hnn). simpl negb.
      destruct ((c0 :: cs) !! q) as [cq|] eqn:Hcq; [| apply lookup_ge_None in Hcq; lia].
      iDestruct (own_dll_acc dq (c0 :: cs) yt.(yjs.yType.start') tl q cq Hcq with "Hdll") as "H". iNamed "H".
      iEval (rewrite -Hcloc) in "Hrightp".
      wp_auto.
      wp_apply (wp_item__Deleted cq.(ic_loc) dq iv with "[$Hcval]"). iIntros "Hcval".
      rewrite (flags_if_deleted iv (ic_deleted cq) Hflags).
      destruct (ic_deleted cq) eqn:Hdq.
      * (* tombstone: advance the cursor, re-establish the skip invariant *)
        rewrite decide_True; [| reflexivity].
        wp_auto.
        iDestruct ("Hback" with "Hcval") as "Hdll".
        wp_for_post.
        iFrame "HΦ". iExists (S q). iFrame "Hp Hdll Hindex".
        rewrite Hcr. replace (Z.of_nat (S q) - 1)%Z with (Z.of_nat q) by lia.
        replace (Z.of_nat (S q)) with (Z.of_nat q + 1)%Z by lia.
        rewrite Hcloc. iFrame "Hleftp Hrightp". iPureIntro. lia.
      * (* first visible node: skip loop exits, run the count loop from [q] *)
        rewrite decide_False; [| done]. rewrite decide_True; [| done].
        iDestruct ("Hback" with "Hcval") as "Hdll".
        iEval (rewrite Hcloc) in "Hrightp".
        iClear "Hcol Hcor".
        wp_auto.
        iAssert (∃ (q2 : nat) (rem off : w64),
          "Hp" ∷ parent ↦{dq} yt ∗
          "Hdll" ∷ own_dll dq yt.(yjs.yType.start') tl null null (c0 :: cs) ∗
          "Hleftp" ∷ left_ptr ↦ node_loc (c0 :: cs) (Z.of_nat q2 - 1) ∗
          "Hrightp" ∷ right_ptr ↦ node_loc (c0 :: cs) (Z.of_nat q2) ∗
          "Hrem" ∷ remaining_ptr ↦ rem ∗
          "Hoffp" ∷ offset_ptr ↦ off ∗
          "%Hq2" ∷ ⌜(q2 <= length (c0 :: cs))%nat⌝ ∗
          "%Hoffinv" ∷ ⌜off = W64 0 ∨
             (0 < uint.Z off)%Z ∧ rem = W64 0 ∧ (1 <= q2)%nat ∧
             (∃ c, (c0 :: cs) !! (q2 - 1)%nat = Some c ∧ ic_deleted c = false ∧
                   (uint.nat off < length (ic_run c))%nat)⌝)%I
          with "[Hp Hdll Hleftp Hrightp remaining offset]" as "IH".
        { iExists q, idx, (W64 0). iFrame "Hp Hdll Hleftp Hrightp remaining offset".
          iPureIntro. split; [exact Hq | by left]. }
        wp_for "IH".
        case_bool_decide as Hrem.
        2:{ wp_auto. rewrite decide_False; [| done]. rewrite decide_True; [| done]. wp_auto.
            iApply ("HΦ" $! (node_loc (c0 :: cs) (Z.of_nat q2 - 1)) (node_loc (c0 :: cs) q2) q2 off).
            iSplitR "".
            { iExists yt, tl. iFrame "Hp Hdll". iPureIntro. split_and!; [exact Hlen | exact Hrepr | exact Hcpar]. }
            iPureIntro. split_and!; [exact Hq2 | reflexivity | reflexivity |].
            destruct Hoffinv as [-> | (Hpos & _ & Hq21 & Hc)]; [by left | right; exact (conj Hpos (conj Hq21 Hc))]. }
        wp_auto.
        have Hoff0 : off = W64 0.
        { destruct Hoffinv as [-> | (_ & Hrem0 & _)]; [done | exfalso; rewrite Hrem0 in Hrem; word]. }
        subst off.
        destruct (decide (q2 < length (c0 :: cs))%nat) as [Hq2lt | Hq2ge].
        2:{ have Hnull2 : node_loc (c0 :: cs) q2 = null.
            { rewrite /node_loc decide_True; [| lia]. rewrite Nat2Z.id lookup_ge_None_2; [done | lia]. }
            rewrite (bool_decide_eq_true_2 (node_loc (c0 :: cs) q2 = null) Hnull2). simpl negb.
            rewrite decide_False; [| done]. rewrite decide_True; [| done]. wp_auto.
            iApply ("HΦ" $! (node_loc (c0 :: cs) (Z.of_nat q2 - 1)) (node_loc (c0 :: cs) q2) q2 (W64 0)).
            iSplitR "".
            { iExists yt, tl. iFrame "Hp Hdll". iPureIntro. split_and!; [exact Hlen | exact Hrepr | exact Hcpar]. }
            iPureIntro. split_and!; [exact Hq2 | reflexivity | reflexivity | by left]. }
        iDestruct (node_loc_lt_not_null dq (c0 :: cs) yt.(yjs.yType.start') tl q2 Hq2lt with "Hdll") as "[%Hnn2 Hdll]".
        rewrite (bool_decide_eq_false_2 (node_loc (c0 :: cs) q2 = null) Hnn2). simpl negb.
        rewrite decide_True; [| done].
        destruct ((c0 :: cs) !! q2) as [c2|] eqn:Hc2; [| apply lookup_ge_None in Hc2; lia].
        iDestruct (own_dll_acc dq (c0 :: cs) yt.(yjs.yType.start') tl q2 c2 Hc2 with "Hdll") as (iv2 olid2 orid2)
          "(%Hc2loc & %Hc2l & %Hc2r & %Hc2id & %Hc2cont & %Hc2olid & %Hc2orid & %Hc2flags & %Hc2run & %Hc2par & Hc2val & #Hc2ol & #Hc2or & Hback2)".
        have Hcount2 : is_countable_flag iv2 = true := flags_if_countable iv2 (ic_deleted c2) Hc2flags.
        have Hdel2 : is_deleted_flag iv2 = ic_deleted c2 := flags_if_deleted iv2 (ic_deleted c2) Hc2flags.
        iEval (rewrite -Hc2loc) in "Hrightp".
        wp_auto.
        wp_apply (wp_item__Indexable c2.(ic_loc) dq iv2 Hcount2 with "[$Hc2val]"). iIntros "Hc2val".
        rewrite Hdel2.
        destruct (ic_deleted c2) eqn:Hd2; simpl negb; wp_auto.
        2:{ (* visible node: spend the budget, or record the in-run offset *)
            wp_apply (wp_item__Len c2.(ic_loc) dq iv2 with "[$Hc2val]"). iIntros "Hc2val".
            wp_auto.
            case_bool_decide as Hcmp; wp_auto.
            - (* remaining < Len: the index lands inside this run (issue #28) *)
              iDestruct ("Hback2" with "Hc2val") as "Hdll".
              wp_for_post.
              iFrame "HΦ". iExists (S q2), (W64 0), rem.
              iFrame "Hp Hdll Hrem Hoffp".
              rewrite Hc2r. replace (Z.of_nat (S q2) - 1)%Z with (Z.of_nat q2) by lia.
              replace (Z.of_nat (S q2)) with (Z.of_nat q2 + 1)%Z by lia.
              rewrite Hc2loc. iFrame "Hleftp Hrightp". iPureIntro.
              have Hrlen : length (ic_run c2) = length (iv2.(yjs.item.content').(yjs.content.content')).
              { by rewrite -(length_fmap content (ic_run c2)) Hc2cont /toContent explode_length. }
              split; [lia |]. right.
              split_and!; [word | done | lia |].
              exists c2. replace (S q2 - 1)%nat with q2 by lia.
              split_and!; [exact Hc2 | exact Hd2 | rewrite Hrlen; word].
            - (* Len <= remaining: spend the whole node (the else branch
                 re-reads right.Len(), a second method call) *)
              wp_apply (wp_item__Len c2.(ic_loc) dq iv2 with "[$Hc2val]"). iIntros "Hc2val".
              wp_auto.
              iDestruct ("Hback2" with "Hc2val") as "Hdll".
              wp_for_post.
              iFrame "HΦ".
              iExists (S q2), (w64_word_instance.(word.sub) rem (W64 (length (iv2.(yjs.item.content').(yjs.content.content'))))), (W64 0).
              iFrame "Hp Hdll Hrem Hoffp".
              rewrite Hc2r. replace (Z.of_nat (S q2) - 1)%Z with (Z.of_nat q2) by lia.
              replace (Z.of_nat (S q2)) with (Z.of_nat q2 + 1)%Z by lia.
              rewrite Hc2loc. iFrame "Hleftp Hrightp". iPureIntro. split; [lia | by left]. }
        iDestruct ("Hback2" with "Hc2val") as "Hdll".
        wp_for_post.
        iFrame "HΦ". iExists (S q2), rem, (W64 0).
        iFrame "Hp Hdll Hrem Hoffp".
        rewrite Hc2r. replace (Z.of_nat (S q2) - 1)%Z with (Z.of_nat q2) by lia.
        replace (Z.of_nat (S q2)) with (Z.of_nat q2 + 1)%Z by lia.
        rewrite Hc2loc. iFrame "Hleftp Hrightp". iPureIntro. split; [lia | by left].
    + (* right = null (q = length): skip loop exits, count loop exits at once *)
      have Hnull : node_loc (c0 :: cs) q = null.
      { rewrite /node_loc decide_True; [| lia]. rewrite Nat2Z.id lookup_ge_None_2; [done | lia]. }
      rewrite (bool_decide_eq_true_2 (node_loc (c0 :: cs) q = null) Hnull). simpl negb.
      wp_auto.
      rewrite decide_False; [| done]. rewrite decide_True; [| done].
      wp_auto.
        iAssert (∃ (q2 : nat) (rem off : w64),
          "Hp" ∷ parent ↦{dq} yt ∗
          "Hdll" ∷ own_dll dq yt.(yjs.yType.start') tl null null (c0 :: cs) ∗
          "Hleftp" ∷ left_ptr ↦ node_loc (c0 :: cs) (Z.of_nat q2 - 1) ∗
          "Hrightp" ∷ right_ptr ↦ node_loc (c0 :: cs) (Z.of_nat q2) ∗
          "Hrem" ∷ remaining_ptr ↦ rem ∗
          "Hoffp" ∷ offset_ptr ↦ off ∗
          "%Hq2" ∷ ⌜(q2 <= length (c0 :: cs))%nat⌝ ∗
          "%Hoffinv" ∷ ⌜off = W64 0 ∨
             (0 < uint.Z off)%Z ∧ rem = W64 0 ∧ (1 <= q2)%nat ∧
             (∃ c, (c0 :: cs) !! (q2 - 1)%nat = Some c ∧ ic_deleted c = false ∧
                   (uint.nat off < length (ic_run c))%nat)⌝)%I
          with "[Hp Hdll Hleftp Hrightp remaining offset]" as "IH".
        { iExists q, idx, (W64 0). iFrame "Hp Hdll Hleftp Hrightp remaining offset".
          iPureIntro. split; [exact Hq | by left]. }
        wp_for "IH".
        case_bool_decide as Hrem.
        2:{ wp_auto. rewrite decide_False; [| done]. rewrite decide_True; [| done]. wp_auto.
            iApply ("HΦ" $! (node_loc (c0 :: cs) (Z.of_nat q2 - 1)) (node_loc (c0 :: cs) q2) q2 off).
            iSplitR "".
            { iExists yt, tl. iFrame "Hp Hdll". iPureIntro. split_and!; [exact Hlen | exact Hrepr | exact Hcpar]. }
            iPureIntro. split_and!; [exact Hq2 | reflexivity | reflexivity |].
            destruct Hoffinv as [-> | (Hpos & _ & Hq21 & Hc)]; [by left | right; exact (conj Hpos (conj Hq21 Hc))]. }
        wp_auto.
        have Hoff0 : off = W64 0.
        { destruct Hoffinv as [-> | (_ & Hrem0 & _)]; [done | exfalso; rewrite Hrem0 in Hrem; word]. }
        subst off.
        destruct (decide (q2 < length (c0 :: cs))%nat) as [Hq2lt | Hq2ge].
        2:{ have Hnull2 : node_loc (c0 :: cs) q2 = null.
            { rewrite /node_loc decide_True; [| lia]. rewrite Nat2Z.id lookup_ge_None_2; [done | lia]. }
            rewrite (bool_decide_eq_true_2 (node_loc (c0 :: cs) q2 = null) Hnull2). simpl negb.
            rewrite decide_False; [| done]. rewrite decide_True; [| done]. wp_auto.
            iApply ("HΦ" $! (node_loc (c0 :: cs) (Z.of_nat q2 - 1)) (node_loc (c0 :: cs) q2) q2 (W64 0)).
            iSplitR "".
            { iExists yt, tl. iFrame "Hp Hdll". iPureIntro. split_and!; [exact Hlen | exact Hrepr | exact Hcpar]. }
            iPureIntro. split_and!; [exact Hq2 | reflexivity | reflexivity | by left]. }
        iDestruct (node_loc_lt_not_null dq (c0 :: cs) yt.(yjs.yType.start') tl q2 Hq2lt with "Hdll") as "[%Hnn2 Hdll]".
        rewrite (bool_decide_eq_false_2 (node_loc (c0 :: cs) q2 = null) Hnn2). simpl negb.
        rewrite decide_True; [| done].
        destruct ((c0 :: cs) !! q2) as [c2|] eqn:Hc2; [| apply lookup_ge_None in Hc2; lia].
        iDestruct (own_dll_acc dq (c0 :: cs) yt.(yjs.yType.start') tl q2 c2 Hc2 with "Hdll") as (iv2 olid2 orid2)
          "(%Hc2loc & %Hc2l & %Hc2r & %Hc2id & %Hc2cont & %Hc2olid & %Hc2orid & %Hc2flags & %Hc2run & %Hc2par & Hc2val & #Hc2ol & #Hc2or & Hback2)".
        have Hcount2 : is_countable_flag iv2 = true := flags_if_countable iv2 (ic_deleted c2) Hc2flags.
        have Hdel2 : is_deleted_flag iv2 = ic_deleted c2 := flags_if_deleted iv2 (ic_deleted c2) Hc2flags.
        iEval (rewrite -Hc2loc) in "Hrightp".
        wp_auto.
        wp_apply (wp_item__Indexable c2.(ic_loc) dq iv2 Hcount2 with "[$Hc2val]"). iIntros "Hc2val".
        rewrite Hdel2.
        destruct (ic_deleted c2) eqn:Hd2; simpl negb; wp_auto.
        2:{ (* visible node: spend the budget, or record the in-run offset *)
            wp_apply (wp_item__Len c2.(ic_loc) dq iv2 with "[$Hc2val]"). iIntros "Hc2val".
            wp_auto.
            case_bool_decide as Hcmp; wp_auto.
            - (* remaining < Len: the index lands inside this run (issue #28) *)
              iDestruct ("Hback2" with "Hc2val") as "Hdll".
              wp_for_post.
              iFrame "HΦ". iExists (S q2), (W64 0), rem.
              iFrame "Hp Hdll Hrem Hoffp".
              rewrite Hc2r. replace (Z.of_nat (S q2) - 1)%Z with (Z.of_nat q2) by lia.
              replace (Z.of_nat (S q2)) with (Z.of_nat q2 + 1)%Z by lia.
              rewrite Hc2loc. iFrame "Hleftp Hrightp". iPureIntro.
              have Hrlen : length (ic_run c2) = length (iv2.(yjs.item.content').(yjs.content.content')).
              { by rewrite -(length_fmap content (ic_run c2)) Hc2cont /toContent explode_length. }
              split; [lia |]. right.
              split_and!; [word | done | lia |].
              exists c2. replace (S q2 - 1)%nat with q2 by lia.
              split_and!; [exact Hc2 | exact Hd2 | rewrite Hrlen; word].
            - (* Len <= remaining: spend the whole node (the else branch
                 re-reads right.Len(), a second method call) *)
              wp_apply (wp_item__Len c2.(ic_loc) dq iv2 with "[$Hc2val]"). iIntros "Hc2val".
              wp_auto.
              iDestruct ("Hback2" with "Hc2val") as "Hdll".
              wp_for_post.
              iFrame "HΦ".
              iExists (S q2), (w64_word_instance.(word.sub) rem (W64 (length (iv2.(yjs.item.content').(yjs.content.content'))))), (W64 0).
              iFrame "Hp Hdll Hrem Hoffp".
              rewrite Hc2r. replace (Z.of_nat (S q2) - 1)%Z with (Z.of_nat q2) by lia.
              replace (Z.of_nat (S q2)) with (Z.of_nat q2 + 1)%Z by lia.
              rewrite Hc2loc. iFrame "Hleftp Hrightp". iPureIntro. split; [lia | by left]. }
        iDestruct ("Hback2" with "Hc2val") as "Hdll".
        wp_for_post.
        iFrame "HΦ". iExists (S q2), rem, (W64 0).
        iFrame "Hp Hdll Hrem Hoffp".
        rewrite Hc2r. replace (Z.of_nat (S q2) - 1)%Z with (Z.of_nat q2) by lia.
        replace (Z.of_nat (S q2)) with (Z.of_nat q2 + 1)%Z by lia.
        rewrite Hc2loc. iFrame "Hleftp Hrightp". iPureIntro. split; [lia | by left].
Qed.

End ytype.
