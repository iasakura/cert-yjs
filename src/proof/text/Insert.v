(** Text handle: the top-level [wp_Text__Insert] (lock-based per-byte
    Integrate loop, one op certificate per inserted item). Split out of
    [text/text]; shares [is_Text] etc. via [text/heap]. *)
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
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
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

Lemma wp_Text__Insert (t : loc) (idx : w64) (cs : go_string) (γs : store_names) (γh : history_names)
    (name : P) (L : list (YjsItem A)) :
  {{{ is_pkg_init yjs ∗ is_Text t γs γh name L }}}
    t @! (go.PointerType yjs.Text) @! "Insert" #idx #cs
  {{{ (L' ins : list (YjsItem A)) (client k0 : nat) (originLeft originRight : YjsPtr A), RET #();
      is_Text t γs γh name L' ∗
      ⌜inserted_run L L' ins cs client k0 originLeft originRight⌝ ∗
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
  iDestruct "Hinv" as (c0 h m pend) "Hown". iNamed "Hown". subst c0.
  iNamed "Hcells". iNamed "Hfields".
  have [Hpool Hreg] : pool_invs types ∧ registry_coh bind types := Hinvs.
  have [Hrunfits [Hlocdup [Hrangedisj Horiginclk]]] := Hpool.
  have [Hbindtypes [Hbindinj Htypesbound]] := Hreg.
  have [Hmtypes Hmdom] := Hregmodel.
  iDestruct (own_type_pool_client_clock_bound types client k Hctr with "Htypes") as %Hcellctr.
  (* snapshot the lock-time history: only appends happen under the lock, so at
     Unlock the accepted-set coherence transports across the (grown) history *)
  iDestruct (own_client_history_lb with "Hhist") as "[Hhist #Hlb_h]".
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
    iDestruct (own_store_struct_intro _ (MkStoreState client k types bind pend pdel) (conj Hpool Hreg)
                with "Hclient Hclock HdeletedSet Hitems Hregistry Htypes Hpending Hpdeletes") as "Hcells".
    wp_apply (wp_Store__wunlock _ _ _ (uint.nat client) h m pend
                with "[$His_store $Hlk Hcells Hseq HtypesAuth Hhist Hacc Hdelete_set]").
    { iExists client, k, pdel, types, bind, acc.
      iFrame "∗#". iPureIntro.
      split_and!;
        [reflexivity | exact Hpendroot | exact Hpendbnd | exact Hregmodel | exact Hhcoh
        | exact Hctr | exact Hacccoh]. }
    iApply ("HΦ" $! L [] 0%nat 0%nat First Last).
    iSplit.
    { iExists tv, tv.(yjs.Text.store'), tv.(yjs.Text.inner').
      iFrame "Ht His_store His_hist Hbind His_lb". iPureIntro. split_and!; [reflexivity | reflexivity | exact Hsorted]. }
    iSplit.
    { iPureIntro. split_and!; [reflexivity | left; reflexivity |].
      intros i it b Hii. rewrite lookup_nil in Hii. inversion Hii. }
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
    iDestruct (own_store_struct_intro _ (MkStoreState client k types bind pend pdel) (conj Hpool Hreg)
                with "Hclient Hclock HdeletedSet Hitems Hregistry Htypes Hpending Hpdeletes") as "Hcells".
    wp_apply (wp_Store__wunlock _ _ _ (uint.nat client) h m pend
                with "[$His_store $Hlk Hcells Hseq HtypesAuth Hhist Hacc Hdelete_set]").
    { iExists client, k, pdel, types, bind, acc.
      iFrame "∗#". iPureIntro.
      split_and!;
        [reflexivity | exact Hpendroot | exact Hpendbnd | exact Hregmodel | exact Hhcoh
        | exact Hctr | exact Hacccoh]. }
    iApply ("HΦ" $! L [] 0%nat 0%nat First Last).
    iSplit.
    { iExists tv, tv.(yjs.Text.store'), tv.(yjs.Text.inner').
      iFrame "Ht His_store His_hist Hbind His_lb". iPureIntro. split_and!; [reflexivity | reflexivity | exact Hsorted]. }
    iSplit.
    { iPureIntro. split_and!; [reflexivity | left; reflexivity |].
      intros i it b Hii. rewrite lookup_nil in Hii. inversion Hii. }
    rewrite big_sepL_nil. done. }
  (* no overflow: the run fits. *)
  have Hnoof : (uint.Z k + Z.of_nat (length cs) < 2^64)%Z by word.
  wp_auto.
  iAssert (own_ytype_cells (tv.(yjs.Text.inner')) (DfracOwn 1) ts.(ty_cells) ts.(ty_arr)) with "[Hparent Hdll]" as "Htext".
  { iExists yt0, tl0. iFrame "Hparent Hdll". iPureIntro. split_and!; [exact Hlen | exact Hrepr | exact Hcpar]. }
  wp_apply (wp_yType__findPos (tv.(yjs.Text.inner')) (DfracOwn 1) ts.(ty_cells) ts.(ty_arr) idx with "[$Htext]").
  iIntros (lft rgt p off) "(Htext & %Hfp)".
  destruct Hfp as (Hpbound & Hlftloc & Hrgtloc & Hoff).
  wp_auto.
  (* normalize the position (issue #28 M3): when the index lands inside a
     multi-char run, split the straddled node at the offset so the insertion
     point sits on a cell boundary. The flatten is unchanged, so only the
     cell layer and the cursor move; both branches rebind the state under
     the shared boundary-form names. *)
  wp_if_join (λ v : val, ⌜v = execute_val⌝ ∗
      ∃ (types1 : gmap loc type_state) (ts1 : type_state) (p1 : nat),
      "s" ∷ s_ptr ↦ tv.(yjs.Text.store') ∗
      "Hitems" ∷ own_items_field ((tv.(yjs.Text.store')) .[(yjs.store.t), "items"]) types1 ∗
      "Hclient" ∷ (tv.(yjs.Text.store')).[yjs.store.t, "client"] ↦ client ∗
      "Hclock" ∷ (tv.(yjs.Text.store')).[yjs.store.t, "clock"] ↦ k ∗
      "HdeletedSet" ∷ own_deleted_set_field ((tv.(yjs.Text.store')) .[(yjs.store.t), "deletedSet"]) ∗
      "Hregistry" ∷ own_registry_field ((tv.(yjs.Text.store')) .[(yjs.store.t), "types"]) bind ∗
      "Hpending" ∷ own_pending_field ((tv.(yjs.Text.store')) .[(yjs.store.t), "pending"]) pend ∗
      "Hpdeletes" ∷ own_pending_deletes_field ((tv.(yjs.Text.store')) .[(yjs.store.t), "pendingDeletes"]) pdel ∗
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
      "%Horiginclk1" ∷ ⌜∀ c0, c0 ∈ all_cells types1 → cell_origin_clk c0⌝ ∗
      "%Hreg1" ∷ ⌜registry_coh bind types1⌝ ∗
      "%Hlr1" ∷ ⌜live_refine types types1⌝)%I
      with "[s left right offset Htext Hrest Hitems Hclient Hclock HdeletedSet Hregistry Hpending Hpdeletes]".
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
    iDestruct (own_type_pool_id_bounds with "Htypes") as %Hbnds.
    have Hckbnd : (Z.of_nat (clock (item_id (run_head cw))) < 2^64)%Z := proj2 (Hbnds cw Hcwmem).
    iDestruct (own_type_pool_runs_wf with "Htypes") as %Hrunwfall.
    have Hrunwfcw : run_wf (ic_run cw) := Hrunwfall cw Hcwmem.
    have Hndl : node_loc ts.(ty_cells) (Z.of_nat p - 1) = ic_loc cw.
    { rewrite /node_loc decide_True; last lia.
      have -> : Z.to_nat (Z.of_nat p - 1) = (p - 1)%nat by lia.
      rewrite Hcw //. }
    rewrite Hndl.
    iDestruct (own_store_struct_intro _ (MkStoreState client k types bind pend pdel) (conj Hpool Hreg)
                with "Hclient Hclock HdeletedSet Hitems Hregistry Htypes Hpending Hpdeletes") as "Hcells".
    wp_apply (wp_store__splitNode (tv.(yjs.Text.store')) (MkStoreState client k types bind pend pdel)
                (tv.(yjs.Text.inner')) ts.(ty_cells) ts.(ty_arr) (p - 1)%nat cw off
                Htspm Hcw Hdiffb
                with "[$Hcells]").
    iIntros (rloc) "(Hcells & %Hrlocfresh')".
    iEval (simpl) in "Hcells".
    iDestruct "Hcells" as "(Hfields1 & %Hinvs1)".
    iDestruct "Hfields1" as "(Hclient & Hclock & HdeletedSet & Hitems & Hregistry & Htypes & Hpending & Hpdeletes)".
    rewrite /own_type_pool.
    have [Hrlocnn Hrlocfresh] := Hrlocfresh'.
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
    iFrame "s Hitems Hrest Htext left right Hclient Hclock HdeletedSet Hregistry Hpending Hpdeletes".
    iPureIntro. split_and!.
    - apply lookup_insert_eq.
    - reflexivity.
    - move=> p' Hne. rewrite lookup_insert_ne //.
    - rewrite /ts1 /= Hlen1. lia.
    - exact Hcellctr1.
    - exact Hlocdup1.
    - exact Hrangedisj1.
    - exact Hrunfits1.
    - exact Horiginclk1.
    - exact (proj2 Hinvs1).
    - exact (split_pool_live_refine types (tv.(yjs.Text.inner')) ts.(ty_cells) ts.(ty_arr)
               (p - 1)%nat (uint.nat off) rloc cw Htspm Hcw). }
  { (* offset = 0: the index already sits on a boundary *)
    have Hoffeq : off = W64 0.
    { destruct Hoff as [-> | (Hoffpos & _)]; [done | exfalso; apply n; word]. }
    subst off.
    iSplitR; first done.
    iExists types, ts, p.
    iFrame "s Hitems Hrest Htext left right Hclient Hclock HdeletedSet Hregistry Hpending Hpdeletes".
    iPureIntro. split_and!;
      [exact Htsp | reflexivity | move=> p' _; reflexivity | exact Hpbound
      | exact Hcellctr | exact Hlocdup | exact Hrangedisj | exact Hrunfits | exact Horiginclk
      | exact Hreg | exact (live_refine_refl types)]. }
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
  (* the tombstone-set invariant follows the normalization: a split only
     refines the live cells (plan-delete-set.md section 3) *)
  iDestruct (own_delete_set_refine γs m types types1 Hlr1 with "Hdelete_set") as "Hdelete_set".
  clear Hctr Hbindtypes Htypesbound Hmtypes HLsub Hmt Hinvarr Htsp Hpbound
        Hcellctr Hlocdup Hrangedisj Hrunfits Horiginclk Hoff Hlftloc Hrgtloc
        Hbound Hlen Hrepr Hcpar.
  clear Harr1 Hdomeq1 Hseqeq1 Hlr1.
  clear off lft rgt yt0 tl0.
  clear Hpool Hreg Hregmodel Hinvs.
  clear p ts types.
  rename types1 into types. rename ts1 into ts. rename p1 into p.
  rename Hreg1 into Hreg.
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
    iDestruct (own_dll_acc_node (DfracOwn 1) ts.(ty_cells) yt1.(yjs.yType.start') tl1 (p) c0 Hc0 with "Hdll1")
      as (prevn nxtn) "(%Hcloc & %Hcl & %Hcrn & %Hrun & %Hclen & %Hpc & Hnode & Hback)".
    iDestruct "Hnode" as (itemVal olid orid)
      "(Hcval & Hol & Hor & %Hinl & %Hinr & %Hidn & %Hcont & %Hparf & %Hprevf & %Hnextf & %Hflagsn)".
    have Hid : item_id (run_head c0) = toYjsId itemVal.(yjs.item.id').
    { symmetry. exact Hidn. }
    iEval (rewrite Hcloc) in "Hcval".
    wp_load. wp_pures. wp_store.
    iDestruct (typed_pointsto_not_null with "rid") as %Hridnn.
    iPersist "rid".
    wp_auto.
    iEval (rewrite -Hcloc) in "Hcval".
    iAssert (own_item_node (ic_loc c0) (DfracOwn 1) (input_of_run (cell_run c0))
               (ic_deleted c0) (ic_parent c0) prevn nxtn) with "[Hcval Hol Hor]" as "Hnode".
    { iExists itemVal, olid, orid. iFrame "Hcval Hol Hor".
      iPureIntro. split_and!;
        [exact Hinl | exact Hinr | exact Hidn | exact Hcont | exact Hparf
        | exact Hprevf | exact Hnextf | exact Hflagsn]. }
    iDestruct ("Hback" with "Hnode") as "Hdll1".
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
  (* fix the run's shared right origin originRight and the first item's left origin originLeft as values *)
  assert (∃ (originRight : YjsPtr A),
     (in_rO = None ∧ originRight = Last ∧ (mp = length ts.(ty_arr))%nat) ∨
     (∃ (ri : YjsItem A) (rightOriginId : yjs.id.t), ts.(ty_arr) !! mp = Some ri ∧ in_rO = Some rightOriginId ∧ item_id ri = toYjsId rightOriginId ∧ originRight = itemPtr ri))
     as [originRight HoRspec].
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
  assert (∃ (originLeft : YjsPtr A),
     (originLeft = First ∧ (p = 0)%nat) ∨
     (∃ (lc : item_cell) (li : YjsItem A), (1 <= p)%nat ∧
        ts.(ty_cells) !! (p - 1)%nat = Some lc ∧
        ic_run lc !! (length (ic_run lc) - 1)%nat = Some li ∧
        ts.(ty_arr) !! (mp - 1)%nat = Some li ∧ originLeft = itemPtr li))
     as [originLeft HoLspec].
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
    "Hitems" ∷ own_items_field ((tv.(yjs.Text.store')) .[(yjs.store.t), "items"]) (<[tv.(yjs.Text.inner') := MkTypeState cells arr]> types) ∗
    "HdeletedSet" ∷ own_deleted_set_field ((tv.(yjs.Text.store')) .[(yjs.store.t), "deletedSet"]) ∗
    "Hregistry" ∷ own_registry_field ((tv.(yjs.Text.store')) .[(yjs.store.t), "types"]) bind ∗
    "Hpending" ∷ own_pending_field ((tv.(yjs.Text.store')) .[(yjs.store.t), "pending"]) pend ∗
    "Hpdeletes" ∷ own_pending_deletes_field ((tv.(yjs.Text.store')) .[(yjs.store.t), "pendingDeletes"]) pdel ∗
    "Hlk" ∷ own_wlock γs ∗
    "Hdelete_set" ∷ own_delete_set γs m (all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells arr]> types)) ∗
    "Hseq" ∷ own γs.(sn_seq) (● ((λ ts0 : type_state, (list_to_set ts0.(ty_arr) : gset (YjsItem A))) <$> types) : authR (gmapUR loc (gsetUR (YjsItem A)))) ∗
    "HtypesAuth" ∷ ghost_map_auth γs.(sn_types) 1 bind ∗
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
           (j = 0%nat → itemPtr li = originLeft) ∧ (∀ j', j = S j' → ins !! j' = Some li))⌝ ∗
    "%Hrightj" ∷ ⌜(in_rO = None ∧ originRight = Last ∧ (mp + j = length arr)%nat)
      ∨ (∃ (ri : YjsItem A) (rightOriginId : yjs.id.t),
           arr !! (mp + j)%nat = Some ri ∧ in_rO = Some rightOriginId ∧ item_id ri = toYjsId rightOriginId ∧ originRight = itemPtr ri)⌝ ∗
    "%Hinslen" ∷ ⌜length ins = j⌝ ∗
    "%Hins" ∷ ⌜∀ (i : nat) (it : YjsItem A), ins !! i = Some it →
       it ∈ arr ∧
       (∀ b : w8, cs !! i = Some b → content it = [b]) ∧
       item_id it = MkYjsId (uint.nat client) (uint.nat k + i)%nat ∧
       rightOrigin it = originRight ∧
       (i = 0%nat → origin it = originLeft) ∧
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
    )%I with "[i t content client HoR left s Hclient Hclock Hitems HdeletedSet Hregistry Hpending Hpdeletes Hlk Hdelete_set Hseq HtypesAuth Hright Hrest Htext Hhist]" as "IH".
  { iExists 0%nat, ts.(ty_arr), ts.(ty_cells), lft, [], h.
    replace (W64 (uint.Z k + Z.of_nat 0)) with k by word.
    have Hts_eta : MkTypeState ts.(ty_cells) ts.(ty_arr) = ts by (destruct ts; reflexivity).
    rewrite Hts_eta (insert_id types (tv.(yjs.Text.inner')) ts Htsp).
    iFrame "i t content client HoR left s Hclient Hclock Hitems HdeletedSet Hregistry Hpending Hpdeletes Hlk Hdelete_set Hseq HtypesAuth Hright Hrest Htext Hhist".
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
        iDestruct (own_dll_acc_node (DfracOwn 1) cells yth.(yjs.yType.start') tlh (p + length ins - 1)%nat lc Hlccells with "Hdll")
          as (prevn nxtn) "(%Hcloc & %Hcl & %Hcrn & %Hrun & %Hclen & %Hpc & Hnode & Hback)".
        iDestruct "Hnode" as (itemVal olid orid)
          "(Hcval & #Hol & #Hor & %Hinl & %Hinr & %Hidn & %Hcont & %Hparf & %Hprevf & %Hnextf & %Hflagsn)".
        iDestruct (typed_pointsto_not_null with "Hcval") as %Hlcnn.
        exfalso. exact (Hlcnn Hlcloc). }
    { destruct Hleftj as [[Hln _] | (lc & li & Hlccells & Hlcloc & Hliarr & Hliitem & Hge1 & _)].
      { exfalso; exact (n Hln). }
      iDestruct "Htextj" as (yth tlh) "(Hpar & Hdll & %Hlenh & %Hreprh & %Hcparh)".
      iDestruct (own_dll_acc_node (DfracOwn 1) cells yth.(yjs.yType.start') tlh (p + length ins - 1)%nat lc Hlccells with "Hdll")
        as (prevn nxtn) "(%Hcloc & %Hcl & %Hcrn & %Hrun & %Hclen & %Hpc & Hnode & Hback)".
      iDestruct "Hnode" as (itemVal olid orid)
        "(Hcval & Hol & Hor & %Hinl & %Hinr & %Hidn & %Hcont & %Hparf & %Hprevf & %Hnextf & %Hflagsn)".
      have Hid : item_id (run_head lc) = toYjsId itemVal.(yjs.item.id').
      { symmetry. exact Hidn. }
      iEval (rewrite Hlcloc) in "Hcval".
      wp_method_call. wp_call. wp_auto.
      wp_method_call. wp_call. rewrite /yjs.item__LastIdⁱᵐᵖˡ. wp_auto.
      wp_alloc icopy as "Hic". wp_auto.
      wp_bind (icopy @! (go.PointerType yjs.item) @! "Len" (# ()))%E.
      wp_apply (wp_item__Len icopy (DfracOwn 1) itemVal with "[$Hic]"). iIntros "Hic".
      have Hlenrun : length (itemVal.(yjs.item.content').(yjs.content.content')) = length (ic_run lc).
      { have Hstr : itemVal.(yjs.item.content').(yjs.content.content')
                  = in_content (input_of_run (cell_run lc)) := Hcont.
        rewrite Hstr. exact Hclen. }
      wp_pures. wp_store.
      iDestruct (typed_pointsto_not_null with "lid") as %Hlidnn.
      iPersist "lid". wp_auto.
      iEval (rewrite -Hlcloc) in "Hcval".
      iAssert (own_item_node (ic_loc lc) (DfracOwn 1) (input_of_run (cell_run lc))
                 (ic_deleted lc) (ic_parent lc) prevn nxtn) with "[Hcval Hol Hor]" as "Hnode".
      { iExists itemVal, olid, orid. iFrame "Hcval Hol Hor".
        iPureIntro. split_and!;
          [exact Hinl | exact Hinr | exact Hidn | exact Hcont | exact Hparf
          | exact Hprevf | exact Hnextf | exact Hflagsn]. }
      iDestruct ("Hback" with "Hnode") as "Hdll".
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
        | rewrite -Hleftloc_eq // | rewrite -Hrgtj // | reflexivity | reflexivity | simpl; lia]. }
    iDestruct (linked_item_fresh_ytype with "Hfresh Htextj") as %Hfr1.
    iDestruct (linked_item_fresh2 with "Hfresh Hrest") as %Hfr2.
    have Hfr : oL2 ∉ ic_loc <$> all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells arr]> types).
    { rewrite (all_cells_insert types (tv.(yjs.Text.inner')) ts (MkTypeState cells arr) Htsp) /=.
      rewrite fmap_app not_elem_of_app. split; [exact Hfr1 | exact Hfr2]. }
    have Hlookj : (<[tv.(yjs.Text.inner') := MkTypeState cells arr]> types) !! tv.(yjs.Text.inner')
                  = Some (MkTypeState cells arr) by apply lookup_insert_eq.
    iDestruct (own_type_pool_runs_wf with "Hrest") as %Hrunwfrest.
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
    (* the one-char input's model step, and its run form *)
    destruct (integrate_some input arr newItem Hinvj Htoitem) as [arr' Hintegrate].
    have Hsi : setintegrate input arr = Some arr'.
    { rewrite (setintegrate_eq_integrate input arr newItem Hinvj Htoitem Hvalid Hmax'). exact Hintegrate. }
    have Hlen1 : length (in_content input) = 1%nat := eq_refl.
    have Hall : integrate_all (ops_of_input input (explode (in_content input))) arr = Some arr'.
    { rewrite (explode_singleton _ Hlen1) ops_of_input_singleton integrate_all_singleton. exact Hintegrate. }
    have Hpoolj : pool_invs (<[tv.(yjs.Text.inner') := MkTypeState cells arr]> types).
    { split_and!; [exact Hrunfitsj | exact Hlocdupj | exact Hrangedisjj | exact Horiginclkj]. }
    have Hidnew_in : item_id newItem = in_id input := commutativity.toItem_id input arr newItem Htoitem.
    have Hgmaxj' : pool_clock_below (<[tv.(yjs.Text.inner') := MkTypeState cells arr]> types) (in_id input)
      by rewrite -Hidnew_in; exact Hgmaxj.
    have Hfitsin : input_fits input.
    { rewrite /input_fits /input /in_id1 /=. rewrite Hclocknit. word. }
    have Hregj : registry_coh bind (<[tv.(yjs.Text.inner') := MkTypeState cells arr]> types)
      := registry_coh_insert bind types _ ts (MkTypeState cells arr) Htsp Hreg.
    iAssert (own_type_pool (DfracOwn 1) (<[tv.(yjs.Text.inner') := MkTypeState cells arr]> types))
      with "[Htextj Hrest]" as "Htypes".
    { rewrite /own_type_pool -insert_delete_eq big_sepM_insert; last apply lookup_delete_eq.
      iFrame "Hrest". simpl. iFrame "Htextj". iPureIntro. exact Hinvj. }
    iDestruct (own_store_struct_intro _
                 (MkStoreState client _ (<[tv.(yjs.Text.inner') := MkTypeState cells arr]> types) bind pend pdel)
                 (conj Hpoolj Hregj) with "Hclient Hclock HdeletedSet Hitems Hregistry Htypes Hpending Hpdeletes") as "Hcells".
    wp_apply (wp_Store__Integrate (tv.(yjs.Text.store')) (tv.(yjs.Text.inner')) (tv.(yjs.Text.inner')) oL2
                (MkStoreState client _ (<[tv.(yjs.Text.inner') := MkTypeState cells arr]> types) bind pend pdel)
                cells arr arr' input newItem
                (node_loc cells (Z.of_nat (p + j) - 1)) (node_loc cells (Z.of_nat (p + j)))
                (or_introl eq_refl) Hlookj (conj Htoitem (conj Hvalid Hmax')) Hfitsin Hall
                (ex_intro _ _ (ex_intro _ _ (ex_intro _ (p + j)%nat (ex_intro _ (p + j)%nat
                 (conj HfindLj (conj HfindRj (conj eq_refl (conj eq_refl
                   (conj HcurLj (conj HpjLb (conj HcurRj HpjLb)))))))))))
                Hgmaxj'
                with "[$Hfresh $Hcells]").
    iIntros (cells' run) "(Hcells & %Hinv' & %Hsplice' & %Hrun)".
    have Hinsins : <[tv.(yjs.Text.inner') := MkTypeState cells' arr']>
                 (<[tv.(yjs.Text.inner') := MkTypeState cells arr]> types)
             = <[tv.(yjs.Text.inner') := MkTypeState cells' arr']> types
      by (rewrite insert_insert; case_decide as Hd; [reflexivity | congruence]).
    iEval (simpl) in "Hcells". iEval (rewrite Hinsins) in "Hcells".
    iDestruct "Hcells" as "(Hfields' & %Hinvs')".
    iDestruct "Hfields'" as "(Hclient & Hclock & HdeletedSet & Hitems & Hregistry & Htypes & Hpending & Hpdeletes)".
    rewrite /own_type_pool.
    iDestruct (big_sepM_delete _ _ (tv.(yjs.Text.inner')) (MkTypeState cells' arr') with "Htypes")
      as "[[Htext' _] Hrest]"; first apply lookup_insert_eq.
    rewrite delete_insert_eq.
    have Hpool' : pool_invs (<[tv.(yjs.Text.inner') := MkTypeState cells' arr']> types) := proj1 Hinvs'.
    have Hrunsub : ∀ x, x ∈ run -> x ∈ arr'.
    { destruct Hsplice' as (idx0 & _ & _ & _ & ->). move=> x Hx.
      apply elem_of_app. right. apply elem_of_app. by left. }
    have Hruneq : run = [newItem]
      := integrate_unit_run arr arr' input newItem run Hinvj (conj Htoitem (conj Hvalid Hmax'))
           Hintegrate Hinv' Hrun Hlen1 Hrunsub.
    subst run.
    set (c := MkItemCell oL2 [newItem] false (tv.(yjs.Text.inner'))).
    destruct Hsplice' as (nx & Hnxb & Hile & Hcellsp & Harrsp2').
    set (iidx := length (run_flatten (take nx cells))) in Hile, Harrsp2'.
    have Hcoupx : length (run_flatten (take nx cells)) = iidx := eq_refl.
    have Harrsp2 : arr' = take iidx arr ++ newItem :: drop iidx arr := Harrsp2'.
    have Harr'eq : arr' = insertIdxIfInBounds iidx newItem arr.
    { rewrite /insertIdxIfInBounds decide_True; [exact Harrsp2 | exact Hile]. }
    have Hpermc : cells' ≡ₚ cells ++ [c]
      := integrate_splice_perm _ _ _ _ _ _ _
           (ex_intro _ nx (conj Hnxb (conj Hile (conj Hcellsp Harrsp2')))).
    have Hclook : cells' !! nx = Some c := integrate_splice_lookup _ _ _ _ _ nx Hnxb Hcellsp.
    have Hcloc2 : ic_loc c = oL2 := eq_refl.
    have Hchead : run_head c = newItem := eq_refl.
    have Hcdel2 : ic_deleted c = false := eq_refl.
    have Hcunit : cell_unit c := eq_refl.
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
    have Hlast_c : ic_run c !! (length (ic_run c) - 1)%nat = Some newItem by rewrite /c //=.
    (* the tombstone-set invariant across the splice: the pool grows by the
       one fresh LIVE cell, whose single char cannot be in the delete set
       because the set only holds ids already in [m] and this id's clock sits
       at the counter, above every same-client item of [m] *)
    have Hac_ds : all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells' arr']> types)
                ≡ₚ all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells arr]> types) ++ [c]
      by (rewrite -Hinsins; apply (all_cells_insert_snoc (<[tv.(yjs.Text.inner') := MkTypeState cells arr]> types)
             (tv.(yjs.Text.inner')) cells arr cells' arr' c Hlookj Hpermc)).
    have Hfresh_ds : ∀ y, y ∈ ic_run c -> doc_model_has m (item_id y) = false.
    { move=> y Hy.
      have Hcu1 : length (ic_run c) = 1%nat := Hcunit.
      have Hyn : y = newItem.
      { move: Hy. rewrite /c /=. move=> Hy'. by apply list_elem_of_singleton in Hy'. }
      subst y.
      apply (docm_has_registry_false bind types m (item_id newItem)
               Hmtypes Hmdom Hbindtypes).
      move=> q tq x Hq Hx Hid.
      have Hxcl : clientId (item_id x) = uint.nat client
        by rewrite Hid /newItem /in_id1 /=.
      have := Hctr q tq x Hq Hx Hxcl.
      rewrite Hid /newItem /in_id1 /=. rewrite Hclocknit. lia. }
    iDestruct (own_delete_set_snoc γs m
                 (all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells arr]> types))
                 (all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells' arr']> types))
                 c Hac_ds Hfresh_ds with "Hdelete_set") as "Hdelete_set".
    wp_for_post.
    (* re-establish the loop invariant for [S j] with [ins ++ [newItem]] *)
    iFrame "Ht His_lb HΦ HisRp Hacc".
    iExists (S j), arr', cells', oL2, (ins ++ [newItem]),
      (hj ++ [EvBroadcast (RootId name, OpInsert input);
              EvDeliver (RootId name, OpInsert input)]).
    replace (W64 (uint.Z k + Z.of_nat (S j))) with (w64_word_instance.(word.add) (W64 (uint.Z k + j)) (W64 1)) by word.
    replace (W64 (S j)) with (w64_word_instance.(word.add) (W64 j) (W64 1)) by word.
    iFrame "Hi Htptr Hcontentp Hclientp HoRp Hleftp Hsp Hclient Hclock Hitems HdeletedSet Hregistry Hpending Hpdeletes Hlk Hdelete_set Hseq HtypesAuth Hrightp Hrest Hhistj Hcertsj".
    iSplitL "Hp3 Hdll3".
    { iExists yt3, tl3. iFrame "Hp3 Hdll3". iPureIntro. split_and!; [exact Hlen3 | exact Hrepr3 | exact Hcpar3]. }
    have HmroR : mrightorigin = originRight.
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
    - exact (proj1 (proj2 Hpool')).
    - exact (proj1 (proj2 (proj2 Hpool'))).
    - exact (proj1 Hpool').
    - exact (proj2 (proj2 (proj2 Hpool'))).
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
  (* transport the accepted-set coherence across the history the loop grew:
     only appends happened under the lock ([h] is a prefix of [hj]), so
     [delivered_ids] only grew and [accepted_coh] still holds at [hj] *)
  iDestruct (is_history_lb_prefix with "Hhistj Hlb_h") as %Hpref_hj.
  have Hacccoh' : accepted_coh acc hj pend.
  { eapply accepted_coh_hist_grow; [exact Hacccoh | exact (delivered_ids_prefix _ _ Hpref_hj)]. }
  (* the delete set's model-domain bound survives the insert: the type's list
     only grew (Hsubarr), so every id present before is still present *)
  iDestruct (own_delete_set_insert γs m
               (all_cells (<[tv.(yjs.Text.inner') := MkTypeState cells arr]> types)) (RootId name) arr with "Hdelete_set") as "Hdelete_set".
  { move=> x Hx.
    have Hdg : doc_model_get m (RootId name) = ty_arr ts
      := Hmtypes name (tv.(yjs.Text.inner')) ts Hbindlk Htsp.
    rewrite Hdg in Hx.
    have Hxg : x ∈ (list_to_set arr : gset (YjsItem A)).
    { apply Hsubarr. rewrite elem_of_list_to_set. exact Hx. }
    rewrite elem_of_list_to_set in Hxg. exact Hxg. }
  have Hpool_close : pool_invs (<[tv.(yjs.Text.inner') := MkTypeState cells arr]> types).
  { rewrite /pool_invs. split_and!; [exact Hrunfitsj | exact Hlocdupj | exact Hrangedisjj | exact Horiginclkj]. }
  have Hreg_close : registry_coh bind (<[tv.(yjs.Text.inner') := MkTypeState cells arr]> types).
  { rewrite /registry_coh. split_and!.
    { move=> name' p' Hb'. destruct (Hbindtypes name' p' Hb') as [ts' Hts'].
      destruct (decide (p' = tv.(yjs.Text.inner'))) as [-> | Hne];
        [rewrite lookup_insert_eq; by eexists
        | rewrite lookup_insert_ne; [by eexists | congruence]]. }
    { exact Hbindinj. }
    { move=> p' [ts' Hts'].
      destruct (decide (p' = tv.(yjs.Text.inner'))) as [-> | Hne].
      + exact (Htypesbound (tv.(yjs.Text.inner')) (ex_intro _ ts Htsp)).
      + rewrite lookup_insert_ne in Hts'; [| congruence].
        exact (Htypesbound p' (ex_intro _ ts' Hts')). }
  }
  have Hregmodel_close : registry_models (<[RootId name := arr]> m) bind (<[tv.(yjs.Text.inner') := MkTypeState cells arr]> types).
  { rewrite /registry_models. split.
    { move=> name' p' ts' Hb' Hts'.
      destruct (decide (p' = tv.(yjs.Text.inner'))) as [-> | Hne].
      + have Heqn : name' = name := Hbindinj name' name _ Hb' Hbindlk.
        subst name'. rewrite lookup_insert_eq in Hts'. injection Hts' as <-.
        rewrite docm_get_insert_eq //.
      + rewrite lookup_insert_ne in Hts'; [| congruence].
        rewrite docm_get_insert_ne.
        * exact (Hmtypes name' p' ts' Hb' Hts').
        * move=> Heqr. injection Heqr as Heqn. subst name'.
          rewrite Hbindlk in Hb'. injection Hb' as He'. exact (Hne (eq_sym He')). }
    { move=> t' Hne'.
      destruct (decide (t' = RootId name)) as [-> | Hnr].
      + exists name, (tv.(yjs.Text.inner')). split; [reflexivity | exact Hbindlk].
      + rewrite docm_get_insert_ne // in Hne'. exact (Hmdom t' Hne'). }
  }
  have Hctr_close : ∀ parent' ts' x, (<[tv.(yjs.Text.inner') := MkTypeState cells arr]> types) !! parent' = Some ts' → x ∈ ty_arr ts' →
      clientId (item_id x) = uint.nat client → (clock (item_id x) < uint.nat (W64 (uint.Z k + j)))%nat.
  { intros parent' ts' x Hlook Hxin Hxc. rewrite Hk'val.
      destruct (decide (parent' = tv.(yjs.Text.inner'))) as [-> | Hne].
      + rewrite lookup_insert in Hlook. rewrite decide_True in Hlook; [| reflexivity]. injection Hlook as <-. simpl in Hxin. exact (Hctrj x Hxin Hxc).
      + rewrite lookup_insert_ne in Hlook; last (intros HH; apply Hne; symmetry; exact HH).
        have := Hctr parent' ts' x Hlook Hxin Hxc. lia. }
  iDestruct (own_store_struct_intro _
               (MkStoreState client (W64 (uint.Z k + j)) (<[tv.(yjs.Text.inner') := MkTypeState cells arr]> types) bind pend pdel)
               (conj Hpool_close Hreg_close) with "Hclient Hclock HdeletedSet Hitems Hregistry Htypes Hpending Hpdeletes") as "Hcells".
  wp_apply (wp_Store__wunlock _ _ _ (uint.nat client) hj (<[RootId name := arr]> m) pend
              with "[$His_store $Hlk Hcells Hseq HtypesAuth Hhistj Hacc Hdelete_set]").
  { iExists client, (W64 (uint.Z k + j)), pdel, (<[tv.(yjs.Text.inner') := MkTypeState cells arr]> types), bind, acc.
    rewrite fmap_insert /=.
    iFrame "∗#". iPureIntro. split_and!;
      [reflexivity | exact Hpendroot | exact Hpendbnd | exact Hregmodel_close
      | exact Hhcohj | exact Hctr_close | exact Hacccoh']. }
  iApply ("HΦ" $! arr ins (uint.nat client) (uint.nat k) originLeft originRight).
  iSplitL "Hfrag Ht".
  { iExists tv, tv.(yjs.Text.store'), tv.(yjs.Text.inner'). iFrame "Ht His_store His_hist Hbind Hfrag". iPureIntro. split_and!; [reflexivity | reflexivity | exact (yai_sorted _ Hinvj)]. }
  iSplit.
  { iPureIntro. split_and!.
    - apply (sorted_subseteq_sublist L arr Hinvj Hsorted (yai_sorted _ Hinvj)).
      intros x Hx. have Hxg : x ∈ (list_to_set arr : gset (YjsItem A)).
      { apply Hsubarr. apply HLsub. rewrite elem_of_list_to_set. exact Hx. }
      rewrite elem_of_list_to_set in Hxg. exact Hxg.
    - right. rewrite Hinslen. exact Hjend.
    - intros i it b Hii Hcsb.
      have [Hitin [Hcont [Hid [Hror [Horg Hchain]]]]] := Hins i it Hii.
      split_and!.
      + exact Hitin.
      + intros HinL. have HitTs : it ∈ ts.(ty_arr).
        { have Htg : it ∈ (list_to_set ts.(ty_arr) : gset (YjsItem A)).
          { apply HLsub. rewrite elem_of_list_to_set. exact HinL. }
          rewrite elem_of_list_to_set in Htg. exact Htg. }
        have Hclk := Hctr (tv.(yjs.Text.inner')) ts it Htsp HitTs. rewrite Hid in Hclk. simpl in Hclk. specialize (Hclk eq_refl). lia.
      + exact (Hcont b Hcsb).
      + exact Hid.
      + exact Hror.
      + exact Horg.
      + exact Hchain. }
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
End text.
