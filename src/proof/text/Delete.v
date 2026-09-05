(** [wp_Text__Delete]: the [Text] handle's delete path at run granularity
    over [own_store_runs], tombstoning visible runs under the store's write
    lock. Shares [is_Text] etc. via [text/heap]. *)
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
Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO addressed_pool))}.

(* The ghost op-history types at the document content type; type names are Go
   strings (issue #49). *)
Local Notation P := go_string.
Local Notation TId := (TypeId P).
Local Notation Op := (TId * @YjsOperation A)%type.
Local Notation Ev := (@Event Op).
Local Notation DocModel := (gmap TId (list (YjsItem A))).

(** [Text.Delete] tombstones a range of visible characters and preserves the
    (persistent) document handle [is_Text t L] UNCHANGED: deletion never
    removes or reorders model items (it only flips runs to deleted, splitting
    a run when a range boundary lands inside it), so the model item list
    [ty_arr] (hence [YjsArrInvariant] and the item-set lower bound [L]) is
    untouched: splits preserve the flatten, flips only the tombstone bit.
    Only the type's address list, its run list and the visible length
    [yType.len] change. Proof shape: take the store lock, lift the store to
    run granularity ([own_store_runs]), [findPos] through a borrow of this
    type ([own_store_runs_ytype_acc]) to the cursor (splitting at the start
    offset via [wp_store__splitNode_runs] when it lands mid-run, issue #28
    M3), then a loop that walks forward tombstoning whole visible runs
    through [wp_deleteNode_store_runs] (reading each node's flags, length
    and right link through [own_store_runs_node_acc_links]) and splits once
    more at the range end when the budget ends inside a run; the
    tombstone-set ghost follows the materialized cells
    ([cells_of_locs_runs_split] / [cells_of_locs_runs_flip] under
    [own_delete_set_refine]); lower the store to its cell registry
    ([types_of_locs_pool_ext_insert]) with the same [ty_arr] (so the auth
    [Hseq] / counter [Hctr] are preserved), Unlock, and return
    [is_Text t L]. *)
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
  iDestruct "Hinv" as (c0 h m pend) "Hown". iEval (rewrite own_store_as_cells) in "Hown". iNamed "Hown". subst c0.
  iDestruct "Hcells" as "(Hfields & %Hinvs)".
  have [Hpool Hreg] : pool_invs types ∧ registry_coh bind types := Hinvs.
  have [Hbindtypes [Hbindinj Htypesbound]] := Hreg.
  have [Hmtypes Hmdom] := Hregmodel.
  iDestruct "Hfields" as "(Hclient & Hclock & HdeletedSet & Hitems & Hregistry & Htypes & Hpending & Hpdeletes)".
  iDestruct (own_type_pool_parents with "Htypes") as %Hpar.
  iDestruct (own_store_struct_intro _ (MkStoreState client k types bind pend pdel) Hinvs
               with "Hclient Hclock HdeletedSet Hitems Hregistry Htypes Hpending Hpdeletes") as "Hcells".
  iDestruct (auth_gmap_gset_lookup with "Hseq His_lb") as %(S' & HmS & HLsub).
  rewrite lookup_fmap in HmS.
  apply fmap_Some in HmS as (ts & Htsp & ->).
  (* the registry binds [name] to this text; the history is untouched by
     Delete ([ty_arr] is tombstone-only), so [Hhist]/[Hhcoh] just thread. *)
  iDestruct (ghost_map_lookup with "HtypesAuth Hbind") as %Hbindlk.
  have Hmt : doc_model_get m (RootId name) = ty_arr ts := Hmtypes name parent ts Hbindlk Htsp.
  subst parent.
  (* the store at run granularity: this text's addresses and runs *)
  iAssert (own_store_runs tv.(yjs.Text.store') (MkStoreStateRuns client k (locs_of types) (pool_of types) bind pend pdel))
    with "[Hcells]" as "Hruns".
  { rewrite own_store_runs_as_state. iExists _. iFrame "Hcells". done. }
  set (locs0 := locs_of types). set (p0 := pool_of types).
  set (runs0 := cell_run <$> ts.(ty_cells)). set (ls0 := ic_loc <$> ts.(ty_cells)).
  have Hp0 : p0 !! tv.(yjs.Text.inner') = Some (MkTypeModel runs0 ts.(ty_arr)).
  { rewrite /p0 /pool_of lookup_fmap Htsp //. }
  have Hl0 : locs0 !! tv.(yjs.Text.inner') = Some ls0.
  { rewrite /locs0 /locs_of lookup_fmap Htsp //. }
  have Hlsl0 : length ls0 = length runs0 by rewrite /ls0 /runs0 !length_fmap.
  have Hts_eta : MkTypeState ts.(ty_cells) ts.(ty_arr) = ts by (destruct ts; reflexivity).
  have Htspm : types !! tv.(yjs.Text.inner') = Some (MkTypeState ts.(ty_cells) ts.(ty_arr)) by rewrite Hts_eta.
  have Hcells0 : cells_of_locs_runs tv.(yjs.Text.inner') ls0 runs0 = ts.(ty_cells).
  { rewrite /ls0 /runs0. apply cells_of_locs_runs_projections.
    move=> c Hc. exact (Hpar _ ts c Htsp Hc). }
  wp_auto.
  (* findPos: locate the cursor [right] at some run position [p]. *)
  iDestruct (own_store_runs_ytype_acc tv.(yjs.Text.store') (MkStoreStateRuns client k locs0 p0 bind pend pdel) tv.(yjs.Text.inner') ls0 (MkTypeModel runs0 ts.(ty_arr)) Hl0 Hp0 with "Hruns") as "[Hyt Hytback]".
  wp_apply (wp_yType__findPos tv.(yjs.Text.inner') (DfracOwn 1) ls0 (MkTypeModel runs0 ts.(ty_arr)) index with "[$Hyt]").
  iIntros (lft rgt p off) "(Hyt & %Hfp)".
  iDestruct ("Hytback" with "Hyt") as "Hruns".
  simpl in Hfp.
  destruct Hfp as (Hpbound & Hlftloc & Hrgtloc & Hoff).
  wp_auto.
  (* normalize the position (issue #28 M3): when the index lands inside a
     multi-char run, split the straddled node at the offset so the range
     starts on a run boundary. The flatten is unchanged, so only the
     address list, the run list and the cursor move; both branches rebind
     the state under the shared boundary-form names. *)
  wp_if_join (λ v : val, ⌜v = execute_val⌝ ∗
      ∃ (locs1 : gmap loc (list loc)) (p1 : pool) (ls1 : list loc) (runs1 : list ItemRun) (p1i : nat),
      "s" ∷ s_ptr ↦ tv.(yjs.Text.store') ∗
      "Hruns" ∷ own_store_runs tv.(yjs.Text.store') (MkStoreStateRuns client k locs1 p1 bind pend pdel) ∗
      "left" ∷ left_ptr ↦ loc_at ls1 (Z.of_nat p1i - 1) ∗
      "right" ∷ right_ptr ↦ loc_at ls1 (Z.of_nat p1i) ∗
      "%Hp1" ∷ ⌜p1 !! tv.(yjs.Text.inner') = Some (MkTypeModel runs1 ts.(ty_arr))⌝ ∗
      "%Hl1" ∷ ⌜locs1 !! tv.(yjs.Text.inner') = Some ls1⌝ ∗
      "%Hdomp1" ∷ ⌜∀ q, q ≠ tv.(yjs.Text.inner') → p1 !! q = p0 !! q⌝ ∗
      "%Hdoml1" ∷ ⌜∀ q, q ≠ tv.(yjs.Text.inner') → locs1 !! q = locs0 !! q⌝ ∗
      "%Hpb1" ∷ ⌜(p1i <= length runs1)%nat⌝ ∗
      "%Hlr1" ∷ ⌜live_refine types (<[tv.(yjs.Text.inner') := MkTypeState (cells_of_locs_runs tv.(yjs.Text.inner') ls1 runs1) ts.(ty_arr)]> types)⌝)%I
      with "[s left right offset Hruns]".
  { (* offset > 0: split [left] at the offset *)
    destruct Hoff as [Hoffeq | (Hoffpos & Hpge1 & (r & Hr & Hrdel & Hofflen))];
      first (exfalso; subst off; move: l; word).
    have Hdiffb : (0 < uint.nat off < length (run_items r))%nat by word.
    have Hrlt : (p - 1 < length ls0)%nat by (rewrite Hlsl0; exact (lookup_lt_Some _ _ _ Hr)).
    have Hlk : ls0 !! (p - 1)%nat = Some (loc_at ls0 (Z.of_nat p - 1)).
    { rewrite /loc_at decide_True; last lia.
      have -> : Z.to_nat (Z.of_nat p - 1) = (p - 1)%nat by lia.
      destruct (ls0 !! (p - 1)%nat) as [l0|] eqn:Hl0k; [done | apply lookup_ge_None in Hl0k; lia]. }
    wp_apply (wp_store__splitNode_runs tv.(yjs.Text.store') (MkStoreStateRuns client k locs0 p0 bind pend pdel)
                tv.(yjs.Text.inner') (loc_at ls0 (Z.of_nat p - 1)) ls0 (MkTypeModel runs0 ts.(ty_arr)) (p - 1)%nat r off
                Hp0 Hl0 Hr Hlk Hdiffb with "[$Hruns]").
    iIntros (rloc) "(Hruns & %Hrlocfresh)".
    iEval (simpl) in "Hruns".
    wp_auto.
    set (runs1 := split_runs runs0 (p - 1)%nat (uint.nat off)).
    set (ls1 := split_locs ls0 (p - 1)%nat rloc).
    have Hll1 : ls1 !! (p - 1)%nat = Some (loc_at ls0 (Z.of_nat p - 1))
      := split_locs_lookup_left ls0 (p - 1)%nat rloc _ Hlk.
    have Hlr1 : ls1 !! p = Some rloc.
    { have H := split_locs_lookup_right ls0 (p - 1)%nat rloc _ Hlk.
      have -> : p = S (p - 1)%nat by lia. exact H. }
    have Hlen1 : length runs1 = S (length runs0) := split_runs_length runs0 (p - 1)%nat (uint.nat off) r Hr.
    have Hleftloc1 : loc_at ls0 (Z.of_nat p - 1) = loc_at ls1 (Z.of_nat p - 1).
    { rewrite {2}/loc_at decide_True; last lia.
      have -> : Z.to_nat (Z.of_nat p - 1) = (p - 1)%nat by lia.
      rewrite Hll1 //. }
    have Hrightloc1 : rloc = loc_at ls1 (Z.of_nat p).
    { rewrite /loc_at decide_True; last lia. rewrite Nat2Z.id Hlr1 //. }
    iSplitR; first done.
    iExists (<[tv.(yjs.Text.inner') := ls1]> locs0), (<[tv.(yjs.Text.inner') := MkTypeModel runs1 ts.(ty_arr)]> p0), ls1, runs1, p.
    iEval (rewrite Hleftloc1) in "left". iEval (rewrite Hrightloc1) in "right".
    iFrame "s Hruns left right".
    iPureIntro. split_and!.
    - apply lookup_insert_eq.
    - apply lookup_insert_eq.
    - move=> q Hne. rewrite lookup_insert_ne //.
    - move=> q Hne. rewrite lookup_insert_ne //.
    - rewrite Hlen1. lia.
    - have Hcw : ts.(ty_cells) !! (p - 1)%nat
                 = Some (MkItemCell (loc_at ls0 (Z.of_nat p - 1)) (run_items r) (run_deleted r) tv.(yjs.Text.inner')).
      { rewrite -Hcells0 /cells_of_locs_runs lookup_zip_with Hlk Hr //. }
      rewrite /ls1 /runs1
        (cells_of_locs_runs_split tv.(yjs.Text.inner') ls0 runs0 (p - 1)%nat (uint.nat off) _ rloc r Hlsl0 Hlk Hr)
        Hcells0.
      exact (split_pool_live_refine types tv.(yjs.Text.inner') ts.(ty_cells) ts.(ty_arr) (p - 1)%nat (uint.nat off) rloc _ Htspm Hcw). }
  { (* offset = 0: the index already sits on a boundary *)
    have Hoffeq : off = W64 0.
    { destruct Hoff as [-> | (Hoffpos & _)]; [done | exfalso; apply n; word]. }
    subst off.
    iSplitR; first done.
    iExists locs0, p0, ls0, runs0, p.
    iFrame "s Hruns left right".
    iPureIntro. split_and!;
      [exact Hp0 | exact Hl0 | move=> q _; reflexivity | move=> q _; reflexivity
      | exact Hpbound | rewrite Hcells0 Hts_eta (insert_id types tv.(yjs.Text.inner') ts Htsp); exact (live_refine_refl types)]. }
  iIntros (v) "[%Hv HQ]". subst v. iNamed "HQ".
  clear Hoff Hlftloc Hrgtloc Hpbound.
  (* the tombstone-set invariant follows the normalization: a split only
     refines the live cells (plan-delete-set.md section 3) *)
  iDestruct (own_delete_set_refine γs m types _ Hlr1 with "Hdelete_set") as "Hdelete_set".
  wp_auto.
  (* Loop invariant: the cursor [q] walks the (possibly re-split) run list
     of this text, tombstoning whole visible runs through [deleteNode]; a
     range-end split may grow the list. The flattened model [ty_arr] never
     changes, so the item-set auth / registry facts survive; the store
     carries the CURRENT addresses and runs of this text, every other type
     untouched. *)
  iAssert (∃ (q : nat) (rem : w64) (locsj : gmap loc (list loc)) (pj : pool) (lsj : list loc) (runsj : list ItemRun),
    "Hsp" ∷ s_ptr ↦ tv.(yjs.Text.store') ∗
    "Hcur" ∷ cur_ptr ↦ loc_at lsj (Z.of_nat q) ∗
    "Hrem" ∷ remaining_ptr ↦ rem ∗
    "Hruns" ∷ own_store_runs tv.(yjs.Text.store') (MkStoreStateRuns client k locsj pj bind pend pdel) ∗
    "Hlk" ∷ own_wlock γs ∗
    "Hseq" ∷ own γs.(sn_seq) (● ((λ ts0 : type_state, (list_to_set ts0.(ty_arr) : gset (YjsItem A))) <$> types) : authR (gmapUR loc (gsetUR (YjsItem A)))) ∗
    "Hhist" ∷ own_client_history γh (uint.nat client) h ∗
    "Hdelete_set" ∷ own_delete_set γs m (all_cells (<[tv.(yjs.Text.inner') := MkTypeState (cells_of_locs_runs tv.(yjs.Text.inner') lsj runsj) ts.(ty_arr)]> types)) ∗
    "HtypesAuth" ∷ ghost_map_auth γs.(sn_types) 1 bind ∗
    "%Hpj" ∷ ⌜pj !! tv.(yjs.Text.inner') = Some (MkTypeModel runsj ts.(ty_arr))⌝ ∗
    "%Hlj" ∷ ⌜locsj !! tv.(yjs.Text.inner') = Some lsj⌝ ∗
    "%Hdompj" ∷ ⌜∀ q', q' ≠ tv.(yjs.Text.inner') → pj !! q' = p0 !! q'⌝ ∗
    "%Hdomlj" ∷ ⌜∀ q', q' ≠ tv.(yjs.Text.inner') → locsj !! q' = locs0 !! q'⌝ ∗
    "%Hqlen" ∷ ⌜(q <= length runsj)%nat⌝)%I
    with "[s cur remaining Hruns Hlk Hseq Hhist Hdelete_set HtypesAuth]" as "IH".
  { iExists p1i, len, locs1, p1, ls1, runs1.
    iFrame "s cur remaining Hruns Hlk Hseq Hhist Hdelete_set HtypesAuth".
    iPureIntro. split_and!; [exact Hp1 | exact Hl1 | exact Hdomp1 | exact Hdoml1 | exact Hpb1]. }
  clear Hp1 Hl1 Hdomp1 Hdoml1 Hpb1 Hlr1 locs1 p1 ls1 runs1 p1i.
  wp_for "IH".
  (* the store at the loop head: this text's addresses are aligned with its runs *)
  iDestruct (own_store_runs_aligned with "Hruns") as %Halj.
  have Hlslj : length lsj = length runsj.
  { destruct (locs_aligned_lens _ _ Halj tv.(yjs.Text.inner') _ Hpj) as (ls' & Hls' & Hlen').
    simpl in Hls'. rewrite Hlj in Hls'. injection Hls' as <-. exact Hlen'. }
  case_bool_decide as Hrem.
  2:{ (* budget exhausted: rebuild [store_inv] (same [ty_arr]), Unlock, return. *)
      wp_auto. rewrite decide_False; [|done]. rewrite decide_True; [|done]. wp_auto.
      iDestruct (own_store_runs_to_state with "Hruns") as "(Hcells & %Halj')".
      have Htypes' : types_of_locs_pool locsj pj
                   = <[tv.(yjs.Text.inner') := MkTypeState (cells_of_locs_runs tv.(yjs.Text.inner') lsj runsj) ts.(ty_arr)]> types.
      { rewrite (types_of_locs_pool_ext_insert locsj locs0 pj p0 tv.(yjs.Text.inner') lsj (MkTypeModel runsj ts.(ty_arr)) Hlj Hpj Hdomlj Hdompj) /=
          (types_of_locs_pool_of types Hpar) //. }
      iEval (rewrite /state_of_runs /= Htypes') in "Hcells".
      have Hmk : ((λ ts0 : type_state, (list_to_set (ty_arr ts0) : gset (YjsItem A))) <$> types) !! tv.(yjs.Text.inner') = Some (list_to_set ts.(ty_arr)).
      { rewrite lookup_fmap Htsp //. }
      have Hregmodel_close : registry_models m bind (<[tv.(yjs.Text.inner') := MkTypeState (cells_of_locs_runs tv.(yjs.Text.inner') lsj runsj) ts.(ty_arr)]> types).
      { rewrite /registry_models. split.
        { move=> name' p' ts' Hb' Hts'.
          destruct (decide (p' = tv.(yjs.Text.inner'))) as [-> | Hne].
          + have Heqn : name' = name := Hbindinj name' name _ Hb' Hbindlk.
            subst name'. rewrite lookup_insert_eq in Hts'. injection Hts' as <-.
            simpl. exact Hmt.
          + rewrite lookup_insert_ne in Hts'; [| congruence].
            exact (Hmtypes name' p' ts' Hb' Hts'). }
        { exact Hmdom. } }
      have Hctr_close : ∀ parent' ts' x,
          (<[tv.(yjs.Text.inner') := MkTypeState (cells_of_locs_runs tv.(yjs.Text.inner') lsj runsj) ts.(ty_arr)]> types) !! parent' = Some ts' →
          x ∈ ty_arr ts' → clientId (item_id x) = uint.nat client → (clock (item_id x) < uint.nat k)%nat.
      { intros parent' ts' x Hlook Hxin Hxc.
        destruct (decide (parent' = tv.(yjs.Text.inner'))) as [-> | Hne].
        + rewrite lookup_insert_eq in Hlook. injection Hlook as <-. simpl in Hxin.
          exact (Hctr (tv.(yjs.Text.inner')) ts x Htsp Hxin Hxc).
        + rewrite lookup_insert_ne in Hlook; last (intros HH; apply Hne; symmetry; exact HH).
          exact (Hctr parent' ts' x Hlook Hxin Hxc). }
      wp_apply (wp_Store__wunlock _ _ _ (uint.nat client) h m pend
                  with "[$His_store $Hlk Hcells Hseq HtypesAuth Hhist Hacc Hdelete_set]").
      { rewrite own_store_as_cells. iExists client, k, pdel, (<[tv.(yjs.Text.inner') := MkTypeState (cells_of_locs_runs tv.(yjs.Text.inner') lsj runsj) ts.(ty_arr)]> types), bind, acc.
        rewrite fmap_insert /= (insert_id _ (tv.(yjs.Text.inner')) (list_to_set ts.(ty_arr)) Hmk).
        iFrame "∗#". iPureIntro. split_and!;
          [reflexivity | exact Hpendroot | exact Hpendbnd | exact Hregmodel_close
          | exact Hhcoh | exact Hctr_close | exact Hacccoh]. }
      iApply "HΦ". iExists tv, tv.(yjs.Text.store'), tv.(yjs.Text.inner').
      iFrame "Ht His_store His_hist Hbind His_lb". iPureIntro. split_and!; [reflexivity | reflexivity | exact Hsorted]. }
  wp_auto.
  destruct (decide (q < length runsj)%nat) as [Hqlt | Hqge].
  2:{ (* cursor at end: rebuild [store_inv] (same [ty_arr]), Unlock, return. *)
      have Hnull : loc_at lsj (Z.of_nat q) = null.
      { rewrite /loc_at decide_True; [| lia]. rewrite Nat2Z.id lookup_ge_None_2; [done | lia]. }
      rewrite (bool_decide_eq_true_2 (loc_at lsj (Z.of_nat q) = null) Hnull). simpl negb.
      rewrite decide_False; [| done]. rewrite decide_True; [| done]. wp_auto.
      iDestruct (own_store_runs_to_state with "Hruns") as "(Hcells & %Halj')".
      have Htypes' : types_of_locs_pool locsj pj
                   = <[tv.(yjs.Text.inner') := MkTypeState (cells_of_locs_runs tv.(yjs.Text.inner') lsj runsj) ts.(ty_arr)]> types.
      { rewrite (types_of_locs_pool_ext_insert locsj locs0 pj p0 tv.(yjs.Text.inner') lsj (MkTypeModel runsj ts.(ty_arr)) Hlj Hpj Hdomlj Hdompj) /=
          (types_of_locs_pool_of types Hpar) //. }
      iEval (rewrite /state_of_runs /= Htypes') in "Hcells".
      have Hmk : ((λ ts0 : type_state, (list_to_set (ty_arr ts0) : gset (YjsItem A))) <$> types) !! tv.(yjs.Text.inner') = Some (list_to_set ts.(ty_arr)).
      { rewrite lookup_fmap Htsp //. }
      have Hregmodel_close : registry_models m bind (<[tv.(yjs.Text.inner') := MkTypeState (cells_of_locs_runs tv.(yjs.Text.inner') lsj runsj) ts.(ty_arr)]> types).
      { rewrite /registry_models. split.
        { move=> name' p' ts' Hb' Hts'.
          destruct (decide (p' = tv.(yjs.Text.inner'))) as [-> | Hne].
          + have Heqn : name' = name := Hbindinj name' name _ Hb' Hbindlk.
            subst name'. rewrite lookup_insert_eq in Hts'. injection Hts' as <-.
            simpl. exact Hmt.
          + rewrite lookup_insert_ne in Hts'; [| congruence].
            exact (Hmtypes name' p' ts' Hb' Hts'). }
        { exact Hmdom. } }
      have Hctr_close : ∀ parent' ts' x,
          (<[tv.(yjs.Text.inner') := MkTypeState (cells_of_locs_runs tv.(yjs.Text.inner') lsj runsj) ts.(ty_arr)]> types) !! parent' = Some ts' →
          x ∈ ty_arr ts' → clientId (item_id x) = uint.nat client → (clock (item_id x) < uint.nat k)%nat.
      { intros parent' ts' x Hlook Hxin Hxc.
        destruct (decide (parent' = tv.(yjs.Text.inner'))) as [-> | Hne].
        + rewrite lookup_insert_eq in Hlook. injection Hlook as <-. simpl in Hxin.
          exact (Hctr (tv.(yjs.Text.inner')) ts x Htsp Hxin Hxc).
        + rewrite lookup_insert_ne in Hlook; last (intros HH; apply Hne; symmetry; exact HH).
          exact (Hctr parent' ts' x Hlook Hxin Hxc). }
      wp_apply (wp_Store__wunlock _ _ _ (uint.nat client) h m pend
                  with "[$His_store $Hlk Hcells Hseq HtypesAuth Hhist Hacc Hdelete_set]").
      { rewrite own_store_as_cells. iExists client, k, pdel, (<[tv.(yjs.Text.inner') := MkTypeState (cells_of_locs_runs tv.(yjs.Text.inner') lsj runsj) ts.(ty_arr)]> types), bind, acc.
        rewrite fmap_insert /= (insert_id _ (tv.(yjs.Text.inner')) (list_to_set ts.(ty_arr)) Hmk).
        iFrame "∗#". iPureIntro. split_and!;
          [reflexivity | exact Hpendroot | exact Hpendbnd | exact Hregmodel_close
          | exact Hhcoh | exact Hctr_close | exact Hacccoh]. }
      iApply "HΦ". iExists tv, tv.(yjs.Text.store'), tv.(yjs.Text.inner').
      iFrame "Ht His_store His_hist Hbind His_lb". iPureIntro. split_and!; [reflexivity | reflexivity | exact Hsorted]. }
  (* cursor in range: read node [q] through the store (a single borrow
     exposing [itemVal] and its links), decide visible/deleted via
     [Indexable], advance to [q+1]. *)
  destruct (lsj !! q) as [lc|] eqn:Hlc; [| apply lookup_ge_None in Hlc; lia].
  destruct (runsj !! q) as [rq|] eqn:Hrq; [| apply lookup_ge_None in Hrq; lia].
  have Hcurq : loc_at lsj (Z.of_nat q) = lc.
  { rewrite /loc_at decide_True; [| lia]. rewrite Nat2Z.id Hlc //. }
  iDestruct (own_store_runs_node_acc_links tv.(yjs.Text.store') (MkStoreStateRuns client k locsj pj bind pend pdel)
               tv.(yjs.Text.inner') lsj (MkTypeModel runsj ts.(ty_arr)) q lc rq Hlj Hpj Hlc Hrq with "Hruns")
    as (itemVal) "Hacc'". iNamed "Hacc'".
  iDestruct (typed_pointsto_not_null with "Haccval") as %Hnn.
  rewrite Hcurq. clear Hcurq.
  rewrite (bool_decide_eq_false_2 (lc = null) Hnn). simpl negb.
  rewrite decide_True; [| done].
  have Hcountq : is_countable_flag itemVal = true := flags_if_countable itemVal (run_deleted rq) Haccflags.
  have Hdelq : is_deleted_flag itemVal = run_deleted rq := flags_if_deleted itemVal (run_deleted rq) Haccflags.
  wp_auto.
  wp_apply (wp_item__Indexable lc (DfracOwn 1) itemVal Hcountq with "[$Haccval]"). iIntros "Haccval".
  rewrite Hdelq.
  have Hnextq : loc_at lsj (Z.of_nat (S q)) = loc_at lsj (Z.of_nat q + 1).
  { f_equal. lia. }
  destruct (run_deleted rq) eqn:Hdq.
  - (* already a tombstone: [Indexable] is false, walk past it unchanged *)
    simpl negb. wp_auto.
    iDestruct ("Haccback" with "Haccval") as "Hruns".
    wp_for_post.
    iFrame "Hacc".
    iFrame "Ht His_lb HΦ". iExists (S q), rem, locsj, pj, lsj, runsj.
    iFrame "Hsp Hrem Hruns Hlk Hseq Hhist Hdelete_set HtypesAuth".
    rewrite Hnextq -Haccright. iFrame "Hcur".
    iPureIntro. split_and!; [exact Hpj | exact Hlj | exact Hdompj | exact Hdomlj | lia].
  - (* visible node: spend the whole run, or split at the range end first *)
    simpl negb. wp_auto.
    wp_apply (wp_item__Len lc (DfracOwn 1) itemVal with "[$Haccval]"). iIntros "Haccval".
    rewrite Haccle.
    wp_auto.
    (* the node goes back to the store before the store methods run *)
    iDestruct ("Haccback" with "Haccval") as "Hruns".
    have Hcellsq : cells_of_locs_runs tv.(yjs.Text.inner') lsj runsj !! q
                 = Some (MkItemCell lc (run_items rq) (run_deleted rq) tv.(yjs.Text.inner')).
    { rewrite /cells_of_locs_runs lookup_zip_with Hlc Hrq //. }
    have Htspj : (<[tv.(yjs.Text.inner') := MkTypeState (cells_of_locs_runs tv.(yjs.Text.inner') lsj runsj) ts.(ty_arr)]> types)
                   !! tv.(yjs.Text.inner')
               = Some (MkTypeState (cells_of_locs_runs tv.(yjs.Text.inner') lsj runsj) ts.(ty_arr)) by apply lookup_insert_eq.
    wp_if_destruct.
    + (* remaining < Len: split the run at the budget, tombstone the truncated
         left half; the Len() read below then returns the truncated length,
         so the budget hits zero and the loop exits on its next test *)
      have Hdiffb : (0 < uint.nat rem < length (run_items rq))%nat by word.
      wp_apply (wp_store__splitNode_runs tv.(yjs.Text.store') (MkStoreStateRuns client k locsj pj bind pend pdel)
                  tv.(yjs.Text.inner') lc lsj (MkTypeModel runsj ts.(ty_arr)) q rq rem
                  Hpj Hlj Hrq Hlc Hdiffb with "[$Hruns]").
      iIntros (rloc) "(Hruns & %Hrlocfresh)".
      iEval (simpl) in "Hruns".
      wp_auto.
      set (runs2 := split_runs runsj q (uint.nat rem)).
      set (ls2 := split_locs lsj q rloc).
      set (leftRun := split_run_left rq (uint.nat rem)).
      have Hll2 : ls2 !! q = Some lc := split_locs_lookup_left lsj q rloc _ Hlc.
      have Hlr2 : ls2 !! S q = Some rloc := split_locs_lookup_right lsj q rloc _ Hlc.
      have Hrl2 : runs2 !! q = Some leftRun := split_runs_lookup_left runsj q (uint.nat rem) rq Hrq.
      have Hlen2 : length runs2 = S (length runsj) := split_runs_length runsj q (uint.nat rem) rq Hrq.
      (* tombstone the truncated left half through the store *)
      wp_apply (wp_deleteNode_store_runs tv.(yjs.Text.store')
                  (MkStoreStateRuns client k (<[tv.(yjs.Text.inner') := ls2]> locsj)
                     (<[tv.(yjs.Text.inner') := MkTypeModel runs2 ts.(ty_arr)]> pj) bind pend pdel)
                  tv.(yjs.Text.inner') ls2 (MkTypeModel runs2 ts.(ty_arr)) q lc leftRun
                  (lookup_insert_eq _ _ _) (lookup_insert_eq _ _ _) Hll2 Hrl2 with "[$Hruns]").
      iIntros "Hruns".
      iEval (simpl; rewrite insert_insert_eq) in "Hruns".
      wp_auto.
      set (runs3 := <[q := flip_run leftRun]> runs2).
      have Hrl3 : runs3 !! q = Some (flip_run leftRun).
      { rewrite /runs3 list_lookup_insert_eq //. apply lookup_lt_Some in Hrl2. exact Hrl2. }
      (* [remaining -= cur.Len()] reads the TRUNCATED length [rem] *)
      iDestruct (own_store_runs_node_acc_links tv.(yjs.Text.store')
                   (MkStoreStateRuns client k (<[tv.(yjs.Text.inner') := ls2]> locsj)
                      (<[tv.(yjs.Text.inner') := MkTypeModel runs3 ts.(ty_arr)]> pj) bind pend pdel)
                   tv.(yjs.Text.inner') ls2 (MkTypeModel runs3 ts.(ty_arr)) q lc (flip_run leftRun)
                   (lookup_insert_eq _ _ _) (lookup_insert_eq _ _ _) Hll2 Hrl3 with "Hruns")
        as (iv2) "Hacc2". iNamed "Hacc2".
      have Hlenl : length (run_items (flip_run leftRun)) = uint.nat rem.
      { rewrite /flip_run /leftRun /split_run_left /= length_take. lia. }
      wp_apply (wp_item__Len lc (DfracOwn 1) iv2 with "[$Haccval]"). iIntros "Haccval".
      rewrite Haccle0 Hlenl. wp_auto.
      iDestruct ("Haccback" with "Haccval") as "Hruns".
      wp_for_post.
      iFrame "Hacc".
      iFrame "Ht His_lb HΦ".
      iExists (S q), (w64_word_instance.(word.sub) rem (W64 (uint.nat rem))),
        (<[tv.(yjs.Text.inner') := ls2]> locsj), (<[tv.(yjs.Text.inner') := MkTypeModel runs3 ts.(ty_arr)]> pj), ls2, runs3.
      iFrame "Hsp Hrem Hruns Hlk Hseq Hhist HtypesAuth".
      have Hnext2 : loc_at ls2 (Z.of_nat (S q)) = loc_at ls2 (Z.of_nat q + 1) by (f_equal; lia).
      rewrite Hnext2 -Haccright0. iFrame "Hcur".
      (* the tombstone-set invariant across this step: the range-end split
         refines the live cells, and so does the flip that follows it *)
      iSplitL "Hdelete_set".
      { iApply (own_delete_set_refine with "Hdelete_set").
        rewrite /runs3 (cells_of_locs_runs_flip tv.(yjs.Text.inner') ls2 runs2 q lc leftRun Hll2 Hrl2).
        rewrite /ls2 /runs2 (cells_of_locs_runs_split tv.(yjs.Text.inner') lsj runsj q (uint.nat rem) lc rloc rq Hlslj Hlc Hrq).
        set (cellsj := cells_of_locs_runs tv.(yjs.Text.inner') lsj runsj).
        set (cells2 := split_cells cellsj q (uint.nat rem) rloc).
        have Hcl2 : cells2 !! q = Some (split_cell_left (MkItemCell lc (run_items rq) (run_deleted rq) tv.(yjs.Text.inner')) (uint.nat rem))
          := split_cells_lookup_left cellsj q (uint.nat rem) rloc _ Hcellsq.
        have Hii : <[tv.(yjs.Text.inner') := MkTypeState cells2 ts.(ty_arr)]>
                     (<[tv.(yjs.Text.inner') := MkTypeState cellsj ts.(ty_arr)]> types)
                 = <[tv.(yjs.Text.inner') := MkTypeState cells2 ts.(ty_arr)]> types by rewrite insert_insert_eq.
        apply (live_refine_trans _ (<[tv.(yjs.Text.inner') := MkTypeState cells2 ts.(ty_arr)]> types)).
        - rewrite -Hii.
          exact (split_pool_live_refine _ tv.(yjs.Text.inner') cellsj ts.(ty_arr) q (uint.nat rem) rloc _ Htspj Hcellsq).
        - have Hii3 : <[tv.(yjs.Text.inner') := MkTypeState (<[q := flip_cell (split_cell_left (MkItemCell lc (run_items rq) (run_deleted rq) tv.(yjs.Text.inner')) (uint.nat rem))]> cells2) ts.(ty_arr)]>
                        (<[tv.(yjs.Text.inner') := MkTypeState cells2 ts.(ty_arr)]> types)
                    = <[tv.(yjs.Text.inner') := MkTypeState (<[q := flip_cell (split_cell_left (MkItemCell lc (run_items rq) (run_deleted rq) tv.(yjs.Text.inner')) (uint.nat rem))]> cells2) ts.(ty_arr)]> types
            by rewrite insert_insert_eq.
          rewrite -Hii3.
          exact (live_refine_flip _ tv.(yjs.Text.inner') (MkTypeState cells2 ts.(ty_arr)) q _ (lookup_insert_eq _ _ _) Hcl2). }
      iPureIntro. split_and!.
      * apply lookup_insert_eq.
      * apply lookup_insert_eq.
      * move=> q' Hne. rewrite lookup_insert_ne //. exact (Hdompj q' Hne).
      * move=> q' Hne. rewrite lookup_insert_ne //. exact (Hdomlj q' Hne).
      * rewrite /runs3 length_insert Hlen2. lia.
    + (* Len <= remaining: tombstone the WHOLE run and spend its length *)
      wp_apply (wp_deleteNode_store_runs tv.(yjs.Text.store') (MkStoreStateRuns client k locsj pj bind pend pdel)
                  tv.(yjs.Text.inner') lsj (MkTypeModel runsj ts.(ty_arr)) q lc rq Hlj Hpj Hlc Hrq with "[$Hruns]").
      iIntros "Hruns".
      iEval (simpl) in "Hruns".
      wp_auto.
      set (runs3 := <[q := flip_run rq]> runsj).
      have Hrl3 : runs3 !! q = Some (flip_run rq).
      { rewrite /runs3 list_lookup_insert_eq //. }
      iDestruct (own_store_runs_node_acc_links tv.(yjs.Text.store')
                   (MkStoreStateRuns client k locsj (<[tv.(yjs.Text.inner') := MkTypeModel runs3 ts.(ty_arr)]> pj) bind pend pdel)
                   tv.(yjs.Text.inner') lsj (MkTypeModel runs3 ts.(ty_arr)) q lc (flip_run rq)
                   Hlj (lookup_insert_eq _ _ _) Hlc Hrl3 with "Hruns")
        as (iv2) "Hacc2". iNamed "Hacc2".
      have Hlenf : length (run_items (flip_run rq)) = length (run_items rq) by rewrite /flip_run //.
      wp_apply (wp_item__Len lc (DfracOwn 1) iv2 with "[$Haccval]"). iIntros "Haccval".
      rewrite Haccle0 Hlenf. wp_auto.
      iDestruct ("Haccback" with "Haccval") as "Hruns".
      wp_for_post.
      iFrame "Hacc".
      iFrame "Ht His_lb HΦ".
      iExists (S q), (w64_word_instance.(word.sub) rem (W64 (length (run_items rq)))),
        locsj, (<[tv.(yjs.Text.inner') := MkTypeModel runs3 ts.(ty_arr)]> pj), lsj, runs3.
      iFrame "Hsp Hrem Hruns Hlk Hseq Hhist HtypesAuth".
      rewrite Hnextq -Haccright0. iFrame "Hcur".
      (* the tombstone-set invariant across this step: a flip only turns bits
         ON, so the live cells refine *)
      iSplitL "Hdelete_set".
      { iApply (own_delete_set_refine with "Hdelete_set").
        rewrite /runs3 (cells_of_locs_runs_flip tv.(yjs.Text.inner') lsj runsj q lc rq Hlc Hrq).
        have Hii3 : <[tv.(yjs.Text.inner') := MkTypeState (<[q := flip_cell (MkItemCell lc (run_items rq) (run_deleted rq) tv.(yjs.Text.inner'))]> (cells_of_locs_runs tv.(yjs.Text.inner') lsj runsj)) ts.(ty_arr)]>
                        (<[tv.(yjs.Text.inner') := MkTypeState (cells_of_locs_runs tv.(yjs.Text.inner') lsj runsj) ts.(ty_arr)]> types)
                    = <[tv.(yjs.Text.inner') := MkTypeState (<[q := flip_cell (MkItemCell lc (run_items rq) (run_deleted rq) tv.(yjs.Text.inner'))]> (cells_of_locs_runs tv.(yjs.Text.inner') lsj runsj)) ts.(ty_arr)]> types
          by rewrite insert_insert_eq.
        rewrite -Hii3.
        exact (live_refine_flip _ tv.(yjs.Text.inner') _ q _ Htspj Hcellsq). }
      iPureIntro. split_and!.
      * apply lookup_insert_eq.
      * exact Hlj.
      * move=> q' Hne. rewrite lookup_insert_ne //. exact (Hdompj q' Hne).
      * exact Hdomlj.
      * rewrite /runs3 length_insert. lia.
Qed.

End text.
