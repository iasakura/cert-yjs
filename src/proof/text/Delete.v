(** [wp_Text__Delete]: the [Text] handle's delete path, tombstoning a visible
    run under the store's write lock. Shares [is_Text] etc. via [text/heap.v]. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core.
From New.proof Require Import algebra.
From New.proof Require Import prelude.
From New.proof Require Import history.
From New.proof.id Require Import id.
From New.proof.item Require Import item.
From New.proof.ytype Require Import ytype.
From New.proof.store Require Import store.
From New.proof.sync_proof Require Import mutex.
From iris.algebra Require Import auth gmap gset.
From iris.algebra.lib Require Import dfrac_agree.
From stdpp Require Import sorting.
From New.proof.text Require Import heap.

(* iris.algebra / stdpp.sorting push [nat_scope], retuning the default [<] / [≤];
   the verified word-arithmetic proofs write [Z] comparisons unannotated, so
   restore [Z_scope] as the default. *)
Local Open Scope Z_scope.

Section text.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.
(** Store lock = a [sync.RWMutex] (write path here, via [wp_Store__wlock] /
    [wp_Store__wunlock]); the per-text item set lives in a grow-only auth
    (the same RA as [store/store], used by [is_type_lb]). *)
Context {sync_pkg : sync.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.
Context {seq_inG : inG Σ (authR (gmapUR loc (gsetUR (YjsItem A))))}.
Context {acc_inG : inG Σ (authR (gsetUR YjsId))}.
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
      wp_apply (wp_Store__wunlock with "[$His_store $Hlk Hclient Hclock Hitemsf Hitemmap Htypesf Htypesmap Hdset Hpendf Hpend Hseq HtypesAuth Htypes Hhist Hacc Hds]").
      { iNext. iExists client, k, items_mref, types_mref, dset,
          pend_sl,
          (<[tv.(yjs.Text.inner') := MkTypeState cells' ts.(ty_arr)]> types), bind, h, m, pend.
        iSplitR "Hseq Htypes"; last first.
        { rewrite /store_inv_ro fmap_insert /=.
          rewrite (insert_id _ (tv.(yjs.Text.inner')) (list_to_set ts.(ty_arr)) Hmk).
          iFrame "Hseq Htypes". }
        iExists acc.
        iFrame "Hclient Hclock Hitemsf Hitemmap Htypesf Htypesmap Hdset Hpendf Hpend Hhist HtypesAuth Hbinds Hacc Hds".
        iFrame "Hpendcert Hclientpin".
        iPureIntro. split_and!.
        - exact Hpendroot.
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
        - exact Hmdom.
        - exact Hacccoh. }
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
      wp_apply (wp_Store__wunlock with "[$His_store $Hlk Hclient Hclock Hitemsf Hitemmap Htypesf Htypesmap Hdset Hpendf Hpend Hseq HtypesAuth Htypes Hhist Hacc Hds]").
      { iNext. iExists client, k, items_mref, types_mref, dset,
          pend_sl,
          (<[tv.(yjs.Text.inner') := MkTypeState cells' ts.(ty_arr)]> types), bind, h, m, pend.
        iSplitR "Hseq Htypes"; last first.
        { rewrite /store_inv_ro fmap_insert /=.
          rewrite (insert_id _ (tv.(yjs.Text.inner')) (list_to_set ts.(ty_arr)) Hmk).
          iFrame "Hseq Htypes". }
        iExists acc.
        iFrame "Hclient Hclock Hitemsf Hitemmap Htypesf Htypesmap Hdset Hpendf Hpend Hhist HtypesAuth Hbinds Hacc Hds".
        iFrame "Hpendcert Hclientpin".
        iPureIntro. split_and!.
        - exact Hpendroot.
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
        - exact Hmdom.
        - exact Hacccoh. }
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
    iFrame "Hacc Hds".
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
      set (leftCell := split_cell_left cq (uint.nat rem)).
      have Hcl2 : cells2 !! q = Some leftCell
        := split_cells_lookup_left cells' q (uint.nat rem) rloc cq Hcq.
      iDestruct (own_dll_update_gen cells2 yt2.(yjs.yType.start') tl2 q leftCell Hcl2 with "Hdll")
        as (iv2) "(%Hcloc2 & %Hcr2 & %Hflags2 & %Hrunwf2 & %Hcontq2 & Hcval & Hback)".
      have Hcllocq : ic_loc leftCell = ic_loc cq by rewrite /leftCell //.
      have Hcldel : ic_deleted leftCell = false by rewrite /leftCell /= Hdq //.
      have Hlenl : length (ic_run leftCell) = uint.nat rem.
      { rewrite /leftCell /= length_take. lia. }
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
      have Hflip2 : MkItemCell leftCell.(ic_loc) leftCell.(ic_run) true leftCell.(ic_parent) = flip_cell leftCell by reflexivity.
      rewrite Hflip2.
      wp_for_post.
      iFrame "Hacc".
      (* invariant at S q over the flipped split list *)
      set (cells3 := <[q := flip_cell leftCell]> cells2).
      have Hnv2 : num_visible cells2 = num_visible cells'
        := split_cells_num_visible cells' q (uint.nat rem) rloc cq Hcq.
      have Hnvge : (uint.nat rem <= num_visible cells2)%nat.
      { rewrite /num_visible -(take_drop_middle cells2 q leftCell Hcl2) fmap_app list_sum_app fmap_cons /=.
        rewrite Hcldel Hlenl. lia. }
      have Hnv3 : num_visible cells3 = (num_visible cells2 - uint.nat rem)%nat.
      { rewrite /cells3 (num_visible_flip_run cells2 q leftCell Hcl2 Hcldel) Hlenl //. }
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
      iFrame "Ht His_lb HΦ Hds".
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
        apply (cells_repr_update_run ts.(ty_arr) cells2 ts.(ty_arr) q leftCell (flip_cell leftCell) Hcl2 eq_refl).
        rewrite /cells2 /cells_repr (split_cells_flatten cells' q (uint.nat rem) rloc cq Hcq).
        exact Hrepr'.
      * move=> c0 Hc0.
        apply list_elem_of_lookup_1 in Hc0 as [i0 Hi0].
        rewrite /cells3 in Hi0.
        destruct (decide (i0 = q)) as [-> | Hne0].
        { rewrite list_lookup_insert_eq in Hi0; last (apply lookup_lt_Some in Hcl2; exact Hcl2).
          injection Hi0 as <-. rewrite /flip_cell /leftCell /= //.
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
      iFrame "Hacc".
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
      iFrame "Ht His_lb HΦ Hds".
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

End text.
