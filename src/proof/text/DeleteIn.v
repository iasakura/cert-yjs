(** [wp_Text__DeleteIn]: the [Text] handle's delete path inside a transaction
    (issue #206 T1, issue #198 Part II), tombstoning visible runs over
    [own_transaction]; the transaction's record grows by the tombstoned chars
    and this text's name. [Text.Delete] is the one-write transaction around it
    ([text/Delete]). Shares [is_Text] etc. via [text/heap]. *)
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
From New.proof.transaction Require Import transaction.
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
(** The store's write lock is held by the transaction ([store.transact]);
    the per-text item set lives in a grow-only auth (the same RA as
    [store/store], used by [is_type_lb]). *)
Context {sync_pkg : sync.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.
Context {seq_inG : inG Σ (authR (gmapUR loc (gsetUR (YjsItem A))))}.
Context {acc_inG : inG Σ (authR (gsetUR YjsId))}.
(* [is_Store]'s reader-count accounting ties the readers' share to the store's
   [types] map via a [dfrac_agree]; threaded here so [is_Text]/[is_Store] uses
   in this file (Insert/Delete/Len) can discharge the instance. *)
Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO addressed_pool))}.
(* the observers' tokens and registrations (issue #198 Part II), as [store/heap] *)
Context {observed_inG : ghost_varG Σ (list (YjsItem go_string * bool))}.
Context {observers_inG : inG Σ (authR (gsetUR (gname * go_string)))}.

(* The ghost op-history types at the document content type; type names are Go
   strings (issue #49). *)
Local Notation P := go_string.
Local Notation TId := (TypeId P).
Local Notation Op := (TId * @YjsOperation A)%type.
Local Notation Ev := (@Event Op).
Local Notation DocModel := (gmap TId (list (YjsItem A))).

(* One flipped run marks its type, whether or not the record already had it:
   the record's changed set after a flip of a nonempty run. *)
Local Lemma marked_step (C : gset loc) (q : loc) (dels : gset YjsId) (r : list (YjsItem A)) :
  r ≠ [] ->
  C ∪ (if decide (dels = ∅) then ∅ else {[q]}) ∪ {[q]}
  = C ∪ (if decide (dels ∪ char_ids r = ∅) then ∅ else {[q]}).
Proof.
  move=> Hne.
  have Hnot : ¬ (dels ∪ char_ids r = ∅).
  { move=> Habs. apply (char_ids_nonempty r Hne).
    apply sets.set_eq => i. split.
    - move=> Hi. rewrite -Habs. apply elem_of_union_r. exact Hi.
    - move=> Hi. exfalso. exact (not_elem_of_empty i Hi). }
  rewrite (decide_False _ _ Hnot).
  destruct (decide (dels = ∅)) as [-> | _]; [rewrite /= (right_id_L ∅ (∪)) // | rewrite /= -assoc_L union_idemp_L //].
Qed.

(** [Text.DeleteIn] tombstones a range of visible characters and preserves the
    (persistent) document handle [is_Text t L] UNCHANGED: deletion never
    removes or reorders model items (it only flips runs to deleted, splitting
    a run when a range boundary lands inside it), so the model item list
    [tm_arr] (hence [YjsArrInvariant] and the item-set lower bound [L]) is
    untouched: splits preserve the flatten, flips only the tombstone bit.
    Only the type's address list, its run list and the visible length
    [yType.len] change. Proof shape: open the transaction, then the store
    ([own_store_state]), [findPos] through a borrow of this
    type ([own_store_state_ytype_acc]) to the cursor (splitting at the start
    offset via [wp_store__splitNode] when it lands mid-run, issue #28
    M3), then a loop that walks forward tombstoning whole visible runs
    through [wp_deleteNode_store] (reading each node's flags, length
    and right link through [own_store_state_node_acc_links]) and splits once
    more at the range end when the budget ends inside a run; the
    tombstone-set ghost follows the type's runs across each surgery
    ([own_delete_set_refine]), the type's [tm_arr] is the same
    throughout (so the auth [Hseq] / counter [Hctr] are preserved), Unlock,
    and return [is_Text t L]. *)
(** Inside a transaction: the handle learns the tombstoned ids [dels] (chars
    of this text's document), the tombstone state grows by them, and the
    transaction's record grows by exactly them and, when any char was
    tombstoned, this text's name. The model, the history and the pending
    buffer are untouched. *)
Lemma wp_Text__DeleteIn (t tr s_loc : loc) (index len : w64) (γs : store_names) (γh : history_names)
    (name : P) (L : list (YjsItem A)) (deleted_ids : gset YjsId)
    (c : ClientId) (h : list Ev) (m : DocModel) (pend : list (TId * IntegrateInput (A := A)))
    (deleted inserted tombstoned : gset YjsId) (changed : gset P) :
  {{{ is_pkg_init yjs ∗ is_Text t γs γh name L deleted_ids ∗
      own_transaction tr s_loc γs γh c h m pend deleted inserted tombstoned changed }}}
    t @! (go.PointerType yjs.Text) @! "DeleteIn" #tr #index #len
  {{{ (dels : gset YjsId), RET #();
      is_Text t γs γh name L (deleted_ids ∪ dels) ∗
      own_transaction tr s_loc γs γh c h m pend (deleted ∪ dels) inserted (tombstoned ∪ dels)
        (changed ∪ (if decide (dels = ∅) then ∅ else {[name]})) ∗
      ⌜dels ⊆ char_ids (doc_model_get m (RootId name))⌝ }}}.
Proof.
  (* ---- Prologue: open the transaction, extract THIS text. ---- *)
  wp_start as "(Htext & Htx)".
  (* the ghost updates at the exits happen after the last program step *)
  iApply wp_fupd.
  iDestruct "Htext" as (tv text_store parent deleted_items) "Htext". iNamed "Htext".
  iDestruct "His_store" as "#His_store".
  subst text_store.
  iDestruct "Htx" as (changed_locs m0 deleted0) "Htx". iNamed "Htx".
  iDestruct "Hstore" as (client k pdel locs0 p0 bind acc) "Hown". iNamed "Hown". subst c.
  (* [s := tr.store]: the record names the store *)
  iDestruct (own_transaction_changes_store with "Hchanges") as (trv) "(Htr & %Htrstore & Hchangesback)".
  wp_auto.
  iDestruct ("Hchangesback" with "Htr") as "Hchanges".
  iEval (rewrite Htrstore) in "s". clear Htrstore.
  iDestruct (own_store_state_registry_coh with "Hstate") as %Hreg.
  iDestruct (own_store_state_aligned with "Hstate") as %Haligned.
  iDestruct (own_store_state_run_wf with "Hstate") as %Hwf0.
  have [Hbindtypes [Hbindinj Htypesbound]] := Hreg.
  have [Hmtypes Hmdom] := Hregmodel.
  iDestruct (auth_gmap_gset_lookup with "Hseq His_lb") as %(S' & HmS & HLsub).
  rewrite lookup_fmap in HmS.
  apply fmap_Some in HmS as (ts & Htsp & ->).
  (* the registry binds [name] to this text; the history is untouched by
     Delete ([tm_arr] is tombstone-only), so [Hhist]/[Hhcoh] just thread. *)
  (* the handle's deleted-id witness sits at the same key, so the same
     comparison places it in THIS type's document *)
  iDestruct (auth_gmap_gset_lookup with "Hseq Hdeleted_items") as %(Sd & HmSd & Hdelitemssub).
  rewrite lookup_fmap Htsp /= in HmSd. injection HmSd as <-.
  have Hdelitems_arr : ∀ x, x ∈ deleted_items -> x ∈ tm_arr ts.
  { intros x Hx. have Hxg : x ∈ (list_to_set (tm_arr ts) : gset (YjsItem A)).
    { apply Hdelitemssub. rewrite elem_of_list_to_set. exact Hx. }
    rewrite elem_of_list_to_set in Hxg. exact Hxg. }
  iDestruct (ghost_map_lookup with "HtypesAuth Hbind") as %Hbindlk.
  have Hmt : doc_model_get m (RootId name) = (tm_arr ts) := Hmtypes name parent ts Hbindlk Htsp.
  subst parent.
  iRename "Hstate" into "Hruns".
  set (runs0 := tm_runs ts).
  have Hp0 : p0 !! tv.(yjs.Text.inner') = Some (MkTypeModel runs0).
  { rewrite /runs0. destruct ts; exact Htsp. }
  have [ls0 Hl0] : ∃ ls0, locs0 !! tv.(yjs.Text.inner') = Some ls0.
  { apply elem_of_dom. rewrite (proj1 Haligned). apply elem_of_dom. by exists ts. }
  have Hlsl0 : length ls0 = length runs0 := proj2 Haligned _ _ _ Hl0 Htsp.
  (* findPos: locate the cursor [right] at some run position [p]. *)
  iDestruct (own_store_state_ytype_acc s_loc (MkStoreState client k locs0 p0 bind pend pdel) tv.(yjs.Text.inner') ls0 (MkTypeModel runs0) Hl0 Hp0 with "Hruns") as "[Hyt Hytback]".
  wp_apply (wp_yType__findPos tv.(yjs.Text.inner') (DfracOwn 1) ls0 (MkTypeModel runs0) index with "[$Hyt]").
  iIntros (leftNode rightNode p off) "(Hyt & %Hfp)".
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
      "s" ∷ s_ptr ↦ s_loc ∗
      "Hruns" ∷ own_store_state s_loc (MkStoreState client k locs1 p1 bind pend pdel) ∗
      "left" ∷ left_ptr ↦ loc_at ls1 (Z.of_nat p1i - 1) ∗
      "right" ∷ right_ptr ↦ loc_at ls1 (Z.of_nat p1i) ∗
      "%Hp1" ∷ ⌜p1 !! tv.(yjs.Text.inner') = Some (MkTypeModel runs1)⌝ ∗
      "%Hl1" ∷ ⌜locs1 !! tv.(yjs.Text.inner') = Some ls1⌝ ∗
      "%Hdomp1" ∷ ⌜∀ q, q ≠ tv.(yjs.Text.inner') → p1 !! q = p0 !! q⌝ ∗
      "%Hdoml1" ∷ ⌜∀ q, q ≠ tv.(yjs.Text.inner') → locs1 !! q = locs0 !! q⌝ ∗
      "%Hpb1" ∷ ⌜(p1i <= length runs1)%nat⌝ ∗
      "%Hlr1" ∷ ⌜pool_after_delete p0 p1⌝ ∗
      "%Htomb1" ∷ ⌜pool_tombstoned p1 = pool_tombstoned p0⌝)%I
      with "[s left right offset Hruns]".
  { (* offset > 0: split [left] at the offset *)
    destruct Hoff as [Hoffeq | (Hoffpos & Hpge1 & (r & Hr & Hrdel & Hofflen))];
      first (exfalso; subst off; move: l; word).
    have Hdiffb : (0 < uint.nat off < length (run_items r))%nat by word.
    have Hrmem0 : r ∈ all_runs p0.
    { apply elem_of_all_runs. exists tv.(yjs.Text.inner'), (MkTypeModel runs0).
      split; [exact Hp0 | exact (list_elem_of_lookup_2 _ _ _ Hr)]. }
    have Hrlt : (p - 1 < length ls0)%nat by (rewrite Hlsl0; exact (lookup_lt_Some _ _ _ Hr)).
    have Hlk : ls0 !! (p - 1)%nat = Some (loc_at ls0 (Z.of_nat p - 1)).
    { rewrite /loc_at decide_True; last lia.
      have -> : Z.to_nat (Z.of_nat p - 1) = (p - 1)%nat by lia.
      destruct (ls0 !! (p - 1)%nat) as [l0|] eqn:Hl0k; [done | apply lookup_ge_None in Hl0k; lia]. }
    wp_apply (wp_store__splitNode s_loc (MkStoreState client k locs0 p0 bind pend pdel)
                tv.(yjs.Text.inner') (loc_at ls0 (Z.of_nat p - 1)) ls0 (MkTypeModel runs0) (p - 1)%nat r off
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
    iExists (<[tv.(yjs.Text.inner') := ls1]> locs0), (<[tv.(yjs.Text.inner') := MkTypeModel runs1]> p0), ls1, runs1, p.
    iEval (rewrite Hleftloc1) in "left". iEval (rewrite Hrightloc1) in "right".
    iFrame "s Hruns left right".
    iPureIntro. split_and!.
    - apply lookup_insert_eq.
    - apply lookup_insert_eq.
    - move=> q Hne. rewrite lookup_insert_ne //.
    - move=> q Hne. rewrite lookup_insert_ne //.
    - rewrite Hlen1. lia.
    - apply pool_after_split_delete with (parent := tv.(yjs.Text.inner')) (k := (p - 1)%nat).
      rewrite /runs1.
      exact (pool_after_split_of_split_runs p0 tv.(yjs.Text.inner') (MkTypeModel runs0)
               (p - 1)%nat (uint.nat off) r Hp0 Hr (Hwf0 r Hrmem0) Hdiffb).
    - rewrite /runs1.
      exact (pool_tombstoned_split p0 tv.(yjs.Text.inner') (MkTypeModel runs0) (p - 1)%nat (uint.nat off) r Hp0 Hr). }
  { (* offset = 0: the index already sits on a boundary *)
    have Hoffeq : off = W64 0.
    { destruct Hoff as [-> | (Hoffpos & _)]; [done | exfalso; apply n; word]. }
    subst off.
    iSplitR; first done.
    iExists locs0, p0, ls0, runs0, p.
    iFrame "s Hruns left right".
    iPureIntro. split_and!;
      [exact Hp0 | exact Hl0 | move=> q _; reflexivity | move=> q _; reflexivity
      | exact Hpbound | exact (pool_after_delete_refl p0) | reflexivity]. }
  iIntros (v) "[%Hv HQ]". subst v. iNamed "HQ".
  clear Hoff Hlftloc Hrgtloc Hpbound.
  (* the tombstone-set invariant follows the normalization: a split only
     refines the live cells (plan-delete-set.md section 3) *)
  iDestruct (own_delete_set_refine γs m p0 p1 (proj1 (proj2 (proj2 Hlr1))) with "Hdelete_set") as "Hdelete_set".
  wp_auto.
  (* Loop invariant: the cursor [q] walks the (possibly re-split) run list
     of this text, tombstoning whole visible runs through [deleteNode]; a
     range-end split may grow the list. The flattened model [tm_arr] never
     changes, so the item-set auth / registry facts survive; the store
     carries the CURRENT addresses and runs of this text, every other type
     untouched. *)
  iAssert (∃ (q : nat) (rem : w64) (locsj : gmap loc (list loc)) (pj : pool) (lsj : list loc) (runsj : list ItemRun)
             (dels : gset YjsId),
    "Hsp" ∷ s_ptr ↦ s_loc ∗
    "Hcur" ∷ cur_ptr ↦ loc_at lsj (Z.of_nat q) ∗
    "Hrem" ∷ remaining_ptr ↦ rem ∗
    "Hruns" ∷ own_store_state s_loc (MkStoreState client k locsj pj bind pend pdel) ∗
    (* the transaction's record so far: the chars tombstoned here and, once
       one is, this text *)
    "Hchanges" ∷ own_transaction_changes tr s_loc inserted (tombstoned ∪ dels)
                   (changed_locs ∪ (if decide (dels = ∅) then ∅ else {[tv.(yjs.Text.inner')]})) ∗
    "Htrp" ∷ tr_ptr ↦ tr ∗
    "Hseq" ∷ own γs.(sn_seq) (● ((λ tm : type_model, (list_to_set (tm_arr tm) : gset (YjsItem A))) <$> p0) : authR (gmapUR loc (gsetUR (YjsItem A)))) ∗
    "Hhist" ∷ own_client_history γh (uint.nat client) h ∗
    "Hdelete_set" ∷ own_delete_set γs m (all_runs pj) ∗
    "HtypesAuth" ∷ ghost_map_auth γs.(sn_types) 1 bind ∗
    "%Hpj" ∷ ⌜pj !! tv.(yjs.Text.inner') = Some (MkTypeModel runsj)⌝ ∗
    "%Hlj" ∷ ⌜locsj !! tv.(yjs.Text.inner') = Some lsj⌝ ∗
    "%Hdompj" ∷ ⌜∀ q', q' ≠ tv.(yjs.Text.inner') → pj !! q' = p0 !! q'⌝ ∗
    "%Hdomlj" ∷ ⌜∀ q', q' ≠ tv.(yjs.Text.inner') → locsj !! q' = locs0 !! q'⌝ ∗
    "%Harrj" ∷ ⌜tm_arr (MkTypeModel runsj) = tm_arr ts⌝ ∗
    (* what this call has tombstoned so far: every id of [dels] sits in a run
       whose deleted bit is now set, and all of them are chars of THIS text *)
    "%Hdelstomb" ∷ ⌜ids_tombstoned dels (all_runs pj)⌝ ∗
    "%Hdelsarr" ∷ ⌜dels ⊆ char_ids (tm_arr ts)⌝ ∗
    "%Htombj" ∷ ⌜pool_tombstoned pj = pool_tombstoned p0 ∪ dels⌝ ∗
    (* what this call tombstoned was live: the transaction's start state
       keeps its tombstones *)
    "%Hdelsfresh" ∷ ⌜dels ## pool_tombstoned p0⌝ ∗
    "%Hqlen" ∷ ⌜(q <= length runsj)%nat⌝)%I
    with "[s cur remaining Hruns Hchanges tr Hseq Hhist Hdelete_set HtypesAuth]" as "IH".
  { iExists p1i, len, locs1, p1, ls1, runs1, ∅.
    repeat (rewrite decide_True; last reflexivity).
    rewrite ?(right_id_L (∅ : gset YjsId) (∪)) ?(right_id_L (∅ : gset loc) (∪)).
    iFrame "s cur remaining Hruns Hchanges tr Hseq Hhist Hdelete_set HtypesAuth".
    iPureIntro. split_and!; [exact Hp1 | exact Hl1 | exact Hdomp1 | exact Hdoml1 | |
      move=> i Hi; exfalso; exact (not_elem_of_empty i Hi) | exact (empty_subseteq _) | exact Htomb1
      | apply disjoint_empty_l | exact Hpb1].
    destruct (proj1 Hlr1 tv.(yjs.Text.inner') (MkTypeModel runs1) Hp1) as (tm0 & Htm0 & Harr0).
    rewrite Harr0 Htsp in Htm0 |- *. by injection Htm0 as <-. }
  clear Hp1 Hl1 Hdomp1 Hdoml1 Hpb1 Hlr1 Htomb1 locs1 p1 ls1 runs1 p1i.
  wp_for "IH".
  (* the store at the loop head: this text's addresses are aligned with its runs *)
  iDestruct (own_store_state_aligned with "Hruns") as %Halj.
  have Hlslj : length lsj = length runsj.
  { destruct (locs_aligned_lens _ _ Halj tv.(yjs.Text.inner') _ Hpj) as (ls' & Hls' & Hlen').
    simpl in Hls'. rewrite Hlj in Hls'. injection Hls' as <-. exact Hlen'. }
  case_bool_decide as Hrem.
  2:{ (* budget exhausted: rebuild [store_inv] (same [tm_arr]), Unlock, return. *)
      wp_auto.
      have Hnf : ¬ ((#false : val) = #true) by done.
      rewrite (decide_False _ _ Hnf) (decide_True _ _ (eq_refl (#false : val))). wp_auto.
      have Hregmodel_close : pool_registry_models m bind pj
        := pool_registry_models_ext m bind p0 pj tv.(yjs.Text.inner') ts (MkTypeModel runsj)
             Hdompj Htsp Hpj Harrj Hregmodel.
      have Hctr_close : pool_next_clock pj (uint.nat client) (uint.nat k)
        := pool_next_clock_ext p0 pj tv.(yjs.Text.inner') ts (MkTypeModel runsj) _ _
             Hdompj Htsp Hpj Harrj Hctr.
      (* ---- the delete's certificate ----
         the ids the loop tombstoned join the store's delete set: each is a
         char of THIS text's document ([Hdelsarr] and the registry), and the
         loop's record says each sits in a run whose deleted bit is now set,
         which is what [own_delete_set_grow] demands. *)
      iDestruct (own_store_state_run_pool_invs with "Hruns") as %Hpoolj.
      have Hdelsdom : ∀ i, i ∈ dels -> doc_model_has m i = true.
      { move=> i Hi. apply docm_has_spec.
        have Hi' := Hdelsarr i Hi.
        rewrite /char_ids elem_of_list_to_set list_elem_of_fmap in Hi'.
        destruct Hi' as (x & -> & Hx).
        exists (RootId name), x. split; [rewrite Hmt; exact Hx | reflexivity]. }
      iMod (own_delete_set_grow γs m pj dels Hpoolj Hdelsdom Hdelstomb with "Hdelete_set")
        as "[Hdelete_set #Hdelslb]".
      iDestruct (is_delete_set_lb_union with "Hdeleted_lb Hdelslb") as "#Hdelsunion".
      (* the witness for the grown delete set: this text's whole document, which
         holds the chars the handle already knew deleted and the ones just
         deleted alike. [Delete] never touches [tm_arr], so the item-set
         authority already holds it *)
      have Hseqlk : ((λ tm : type_model, (list_to_set (tm_arr tm) : gset (YjsItem A))) <$> p0)
                      !! tv.(yjs.Text.inner') = Some (list_to_set (tm_arr ts)).
      { rewrite lookup_fmap Htsp //. }
      iMod (auth_gmap_gset_grow γs.(sn_seq) _ tv.(yjs.Text.inner')
              (list_to_set (tm_arr ts)) (list_to_set (tm_arr ts)) Hseqlk (reflexivity _)
              with "Hseq") as "[Hseq #Hfulllb]".
      iEval (rewrite (insert_id _ _ _ Hseqlk)) in "Hseq".
      iEval (rewrite -(pool_seq_map_ext p0 pj tv.(yjs.Text.inner') ts (MkTypeModel runsj)
                         Hdompj Htsp Hpj Harrj)) in "Hseq".
      (* the store after the delete, the tombstone state grown by [dels]:
         what the transaction carries on *)
      iAssert (own_store s_loc γs γh (uint.nat client) h m pend (deleted ∪ dels))
        with "[Hruns Hseq HtypesAuth Hhist Hacc Hdelete_set]" as "Hstore".
      { iExists client, k, pdel, locsj, pj, bind, acc.
        iFrame "∗#". iPureIntro. split_and!;
          [reflexivity | exact Hpendroot | exact Hpendbnd | exact Hregmodel_close
          | exact Hhcoh | exact Hctr_close | exact Hacccoh | rewrite Htombj Hdeleted //]. }
      (* the transaction's start state, over this delete: the same documents,
         the tombstones grown by this call's, which were live *)
      have Hstart' : transaction_start m (deleted ∪ dels) inserted (tombstoned ∪ dels) m0 deleted0.
      { destruct Hstart as (Hfilter & Hdel & Hdisj & Htop). split_and!; [exact Hfilter | | | exact Htop].
        - rewrite Hdel -assoc_L //.
        - rewrite elem_of_disjoint => i Hi Hi0. apply elem_of_union in Hi as [Hi | Hi].
          + exact (proj1 (elem_of_disjoint _ _) Hdisj i Hi Hi0).
          + apply (proj1 (elem_of_disjoint _ _) Hdelsfresh i Hi).
            rewrite -Hdeleted Hdel. apply elem_of_union_l. exact Hi0. }
      iModIntro.
      iApply ("HΦ" $! dels).
      iSplitL "Ht His_store His_lb".
      { iExists tv, tv.(yjs.Text.store'), tv.(yjs.Text.inner'), (tm_arr ts).
        iFrame "Ht His_store His_hist Hbind His_lb Hfulllb Hdelsunion".
        iPureIntro. split_and!;
          [reflexivity | reflexivity
          | apply union_least;
              [etrans; [exact Hdeleted_known
                       | exact (char_ids_mono deleted_items (tm_arr ts) Hdelitems_arr)]
              | exact Hdelsarr]
          | exact Hsorted]. }
      (* the transaction after the delete: the record's meaning at the same
         model, this text among the changed types once a char is tombstoned *)
      iSplitL "Hchanges Hstore Hregistry".
      { iExists (changed_locs ∪ (if decide (dels = ∅) then ∅ else {[tv.(yjs.Text.inner')]})), m0, deleted0.
        iFrame "Hchanges Hstore Hregistry".
        iSplitR; first (iPureIntro; exact Hstart').
        iSplitR.
        { destruct (decide (dels = ∅)) as [-> | Hne].
          - repeat (rewrite decide_True; last reflexivity).
            rewrite ?(right_id_L (∅ : gset P) (∪)) ?(right_id_L (∅ : gset loc) (∪)). iFrame "Hchanged_bound".
          - iApply (changed_types_bound_mark with "Hbind Hchanged_bound"). }
        iPureIntro. split_and!.
        - exact Hinserted_dom.
        - apply union_mono; [exact Htombstoned_sub | done].
        - (* every recorded id sits in a changed type: the old ones as before,
             the tombstoned chars in this text, which they mark *)
          move=> i Hi.
          destruct (decide (i ∈ inserted ∪ tombstoned)) as [Hold | Hnew].
          + destruct (Hrecorded i Hold) as (name0 & x & Hn & Hx & Hid).
            exists name0, x. split_and!; [apply elem_of_union_l; exact Hn | exact Hx | exact Hid].
          + have Hi' : i ∈ dels.
            { apply elem_of_union in Hi as [Hi | Hi]; [exfalso; apply Hnew; apply elem_of_union_l; exact Hi |].
              apply elem_of_union in Hi as [Hi | Hi]; [exfalso; apply Hnew; apply elem_of_union_r; exact Hi | exact Hi]. }
            have Hnotempty : ¬ (dels = ∅) by (move=> Hemp; rewrite Hemp in Hi'; exact (not_elem_of_empty i Hi')).
            have Hi'' := Hdelsarr i Hi'.
            apply elem_of_char_ids in Hi'' as (x & Hx & Hid).
            exists name, x. split_and!.
            * rewrite (decide_False _ _ Hnotempty). apply elem_of_union_r. by apply elem_of_singleton.
            * rewrite Hmt. exact Hx.
            * exact Hid. }
      iPureIntro. rewrite Hmt. exact Hdelsarr. }
  wp_auto.
  destruct (decide (q < length runsj)%nat) as [Hqlt | Hqge].
  2:{ (* cursor at end: rebuild [store_inv] (same [tm_arr]), Unlock, return. *)
      have Hnull : loc_at lsj (Z.of_nat q) = null.
      { rewrite /loc_at decide_True; [| lia]. rewrite Nat2Z.id lookup_ge_None_2; [done | lia]. }
      rewrite (bool_decide_eq_true_2 (loc_at lsj (Z.of_nat q) = null) Hnull). simpl negb.
      have Hnf : ¬ ((#false : val) = #true) by done.
      rewrite (decide_False _ _ Hnf) (decide_True _ _ (eq_refl (#false : val))). wp_auto.
      have Hregmodel_close : pool_registry_models m bind pj
        := pool_registry_models_ext m bind p0 pj tv.(yjs.Text.inner') ts (MkTypeModel runsj)
             Hdompj Htsp Hpj Harrj Hregmodel.
      have Hctr_close : pool_next_clock pj (uint.nat client) (uint.nat k)
        := pool_next_clock_ext p0 pj tv.(yjs.Text.inner') ts (MkTypeModel runsj) _ _
             Hdompj Htsp Hpj Harrj Hctr.
      (* ---- the delete's certificate ----
         the ids the loop tombstoned join the store's delete set: each is a
         char of THIS text's document ([Hdelsarr] and the registry), and the
         loop's record says each sits in a run whose deleted bit is now set,
         which is what [own_delete_set_grow] demands. *)
      iDestruct (own_store_state_run_pool_invs with "Hruns") as %Hpoolj.
      have Hdelsdom : ∀ i, i ∈ dels -> doc_model_has m i = true.
      { move=> i Hi. apply docm_has_spec.
        have Hi' := Hdelsarr i Hi.
        rewrite /char_ids elem_of_list_to_set list_elem_of_fmap in Hi'.
        destruct Hi' as (x & -> & Hx).
        exists (RootId name), x. split; [rewrite Hmt; exact Hx | reflexivity]. }
      iMod (own_delete_set_grow γs m pj dels Hpoolj Hdelsdom Hdelstomb with "Hdelete_set")
        as "[Hdelete_set #Hdelslb]".
      iDestruct (is_delete_set_lb_union with "Hdeleted_lb Hdelslb") as "#Hdelsunion".
      (* the witness for the grown delete set: this text's whole document, which
         holds the chars the handle already knew deleted and the ones just
         deleted alike. [Delete] never touches [tm_arr], so the item-set
         authority already holds it *)
      have Hseqlk : ((λ tm : type_model, (list_to_set (tm_arr tm) : gset (YjsItem A))) <$> p0)
                      !! tv.(yjs.Text.inner') = Some (list_to_set (tm_arr ts)).
      { rewrite lookup_fmap Htsp //. }
      iMod (auth_gmap_gset_grow γs.(sn_seq) _ tv.(yjs.Text.inner')
              (list_to_set (tm_arr ts)) (list_to_set (tm_arr ts)) Hseqlk (reflexivity _)
              with "Hseq") as "[Hseq #Hfulllb]".
      iEval (rewrite (insert_id _ _ _ Hseqlk)) in "Hseq".
      iEval (rewrite -(pool_seq_map_ext p0 pj tv.(yjs.Text.inner') ts (MkTypeModel runsj)
                         Hdompj Htsp Hpj Harrj)) in "Hseq".
      (* the store after the delete, the tombstone state grown by [dels]:
         what the transaction carries on *)
      iAssert (own_store s_loc γs γh (uint.nat client) h m pend (deleted ∪ dels))
        with "[Hruns Hseq HtypesAuth Hhist Hacc Hdelete_set]" as "Hstore".
      { iExists client, k, pdel, locsj, pj, bind, acc.
        iFrame "∗#". iPureIntro. split_and!;
          [reflexivity | exact Hpendroot | exact Hpendbnd | exact Hregmodel_close
          | exact Hhcoh | exact Hctr_close | exact Hacccoh | rewrite Htombj Hdeleted //]. }
      (* the transaction's start state, over this delete: the same documents,
         the tombstones grown by this call's, which were live *)
      have Hstart' : transaction_start m (deleted ∪ dels) inserted (tombstoned ∪ dels) m0 deleted0.
      { destruct Hstart as (Hfilter & Hdel & Hdisj & Htop). split_and!; [exact Hfilter | | | exact Htop].
        - rewrite Hdel -assoc_L //.
        - rewrite elem_of_disjoint => i Hi Hi0. apply elem_of_union in Hi as [Hi | Hi].
          + exact (proj1 (elem_of_disjoint _ _) Hdisj i Hi Hi0).
          + apply (proj1 (elem_of_disjoint _ _) Hdelsfresh i Hi).
            rewrite -Hdeleted Hdel. apply elem_of_union_l. exact Hi0. }
      iModIntro.
      iApply ("HΦ" $! dels).
      iSplitL "Ht His_store His_lb".
      { iExists tv, tv.(yjs.Text.store'), tv.(yjs.Text.inner'), (tm_arr ts).
        iFrame "Ht His_store His_hist Hbind His_lb Hfulllb Hdelsunion".
        iPureIntro. split_and!;
          [reflexivity | reflexivity
          | apply union_least;
              [etrans; [exact Hdeleted_known
                       | exact (char_ids_mono deleted_items (tm_arr ts) Hdelitems_arr)]
              | exact Hdelsarr]
          | exact Hsorted]. }
      (* the transaction after the delete: the record's meaning at the same
         model, this text among the changed types once a char is tombstoned *)
      iSplitL "Hchanges Hstore Hregistry".
      { iExists (changed_locs ∪ (if decide (dels = ∅) then ∅ else {[tv.(yjs.Text.inner')]})), m0, deleted0.
        iFrame "Hchanges Hstore Hregistry".
        iSplitR; first (iPureIntro; exact Hstart').
        iSplitR.
        { destruct (decide (dels = ∅)) as [-> | Hne].
          - repeat (rewrite decide_True; last reflexivity).
            rewrite ?(right_id_L (∅ : gset P) (∪)) ?(right_id_L (∅ : gset loc) (∪)). iFrame "Hchanged_bound".
          - iApply (changed_types_bound_mark with "Hbind Hchanged_bound"). }
        iPureIntro. split_and!.
        - exact Hinserted_dom.
        - apply union_mono; [exact Htombstoned_sub | done].
        - (* every recorded id sits in a changed type: the old ones as before,
             the tombstoned chars in this text, which they mark *)
          move=> i Hi.
          destruct (decide (i ∈ inserted ∪ tombstoned)) as [Hold | Hnew].
          + destruct (Hrecorded i Hold) as (name0 & x & Hn & Hx & Hid).
            exists name0, x. split_and!; [apply elem_of_union_l; exact Hn | exact Hx | exact Hid].
          + have Hi' : i ∈ dels.
            { apply elem_of_union in Hi as [Hi | Hi]; [exfalso; apply Hnew; apply elem_of_union_l; exact Hi |].
              apply elem_of_union in Hi as [Hi | Hi]; [exfalso; apply Hnew; apply elem_of_union_r; exact Hi | exact Hi]. }
            have Hnotempty : ¬ (dels = ∅) by (move=> Hemp; rewrite Hemp in Hi'; exact (not_elem_of_empty i Hi')).
            have Hi'' := Hdelsarr i Hi'.
            apply elem_of_char_ids in Hi'' as (x & Hx & Hid).
            exists name, x. split_and!.
            * rewrite (decide_False _ _ Hnotempty). apply elem_of_union_r. by apply elem_of_singleton.
            * rewrite Hmt. exact Hx.
            * exact Hid. }
      iPureIntro. rewrite Hmt. exact Hdelsarr. }
  (* cursor in range: read node [q] through the store (a single borrow
     exposing [itemVal] and its links), decide visible/deleted via
     [Indexable], advance to [q+1]. *)
  destruct (lsj !! q) as [lc|] eqn:Hlc; [| apply lookup_ge_None in Hlc; lia].
  destruct (runsj !! q) as [rq|] eqn:Hrq; [| apply lookup_ge_None in Hrq; lia].
  have Hcurq : loc_at lsj (Z.of_nat q) = lc.
  { rewrite /loc_at decide_True; [| lia]. rewrite Nat2Z.id Hlc //. }
  iDestruct (own_store_state_node_acc_links s_loc (MkStoreState client k locsj pj bind pend pdel)
               tv.(yjs.Text.inner') lsj (MkTypeModel runsj) q lc rq Hlj Hpj Hlc Hrq with "Hruns")
    as (itemVal) "Hacc'". iNamed "Hacc'".
  iDestruct (typed_pointsto_not_null with "Haccval") as %Hnn.
  rewrite Hcurq. clear Hcurq.
  rewrite (bool_decide_eq_false_2 (lc = null) Hnn). simpl negb.
  rewrite (decide_True _ _ (eq_refl (#true : val))).
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
    iFrame "Hacc Hregistry".
    iFrame "Ht His_lb HΦ". iExists (S q), rem, locsj, pj, lsj, runsj, dels.
    iFrame "Hsp Hrem Hruns Hchanges Htrp Hseq Hhist Hdelete_set HtypesAuth".
    rewrite Hnextq -Haccright. iFrame "Hcur".
    iPureIntro. split_and!; [exact Hpj | exact Hlj | exact Hdompj | exact Hdomlj | exact Harrj
      | exact Hdelstomb | exact Hdelsarr | exact Htombj | exact Hdelsfresh | lia].
  - (* visible node: spend the whole run, or split at the range end first *)
    simpl negb. wp_auto.
    wp_apply (wp_item__Len lc (DfracOwn 1) itemVal with "[$Haccval]"). iIntros "[Haccval _]".
    rewrite Haccle.
    wp_auto.
    (* the node goes back to the store before the store methods run *)
    iDestruct ("Haccback" with "Haccval") as "Hruns".
    iDestruct (own_store_state_run_wf with "Hruns") as %Hwfj.
    iDestruct (own_store_state_run_pool_invs with "Hruns") as %Hpoolj0.
    have Hrqmem : rq ∈ all_runs pj.
    { apply elem_of_all_runs. exists tv.(yjs.Text.inner'), (MkTypeModel runsj).
      split; [exact Hpj | exact (list_elem_of_lookup_2 _ _ _ Hrq)]. }
    wp_if_destruct.
    + (* remaining < Len: split the run at the budget, tombstone the truncated
         left half; the Len() read below then returns the truncated length,
         so the budget hits zero and the loop exits on its next test *)
      have Hdiffb : (0 < uint.nat rem < length (run_items rq))%nat by word.
      wp_apply (wp_store__splitNode s_loc (MkStoreState client k locsj pj bind pend pdel)
                  tv.(yjs.Text.inner') lc lsj (MkTypeModel runsj) q rq rem
                  Hpj Hlj Hrq Hlc Hdiffb with "[$Hruns]").
      iIntros (rloc) "(Hruns & %Hrlocfresh)".
      iEval (simpl) in "Hruns".
      iDestruct (own_store_state_run_pool_invs with "Hruns") as %Hpool2.
      wp_auto.
      set (runs2 := split_runs runsj q (uint.nat rem)).
      set (ls2 := split_locs lsj q rloc).
      set (leftRun := split_run_left rq (uint.nat rem)).
      have Hll2 : ls2 !! q = Some lc := split_locs_lookup_left lsj q rloc _ Hlc.
      have Hlr2 : ls2 !! S q = Some rloc := split_locs_lookup_right lsj q rloc _ Hlc.
      have Hrl2 : runs2 !! q = Some leftRun := split_runs_lookup_left runsj q (uint.nat rem) rq Hrq.
      have Hlen2 : length runs2 = S (length runsj) := split_runs_length runsj q (uint.nat rem) rq Hrq.
      (* tombstone the truncated left half through the store *)
      wp_apply (wp_deleteNode_store tr s_loc
                  (MkStoreState client k (<[tv.(yjs.Text.inner') := ls2]> locsj)
                     (<[tv.(yjs.Text.inner') := MkTypeModel runs2]> pj) bind pend pdel)
                  tv.(yjs.Text.inner') ls2 (MkTypeModel runs2) q lc leftRun _ _ _
                  (lookup_insert_eq _ _ _) (lookup_insert_eq _ _ _) Hll2 Hrl2 with "[$Hruns $Hchanges]").
      iIntros "[Hruns Hchanges]".
      iEval (simpl; rewrite insert_insert_eq) in "Hruns".
      (* the record after this step: the left half's chars, and this text marked *)
      have Hdl : run_deleted leftRun = false by rewrite /leftRun /split_run_left /= Hdq //.
      have Hlne : run_items leftRun ≠ [].
      { rewrite /leftRun /split_run_left /=. move=> Hnil. apply (f_equal length) in Hnil.
        rewrite length_take /= in Hnil. lia. }
      iEval (rewrite Hdl /= -(assoc_L (∪)) (marked_step _ _ _ _ Hlne)) in "Hchanges".
      wp_auto.
      set (runs3 := <[q := flip_run leftRun]> runs2).
      have Hrl3 : runs3 !! q = Some (flip_run leftRun).
      { rewrite /runs3 list_lookup_insert_eq //. apply lookup_lt_Some in Hrl2. exact Hrl2. }
      (* [remaining -= cur.Len()] reads the TRUNCATED length [rem] *)
      iDestruct (own_store_state_node_acc_links s_loc
                   (MkStoreState client k (<[tv.(yjs.Text.inner') := ls2]> locsj)
                      (<[tv.(yjs.Text.inner') := MkTypeModel runs3]> pj) bind pend pdel)
                   tv.(yjs.Text.inner') ls2 (MkTypeModel runs3) q lc (flip_run leftRun)
                   (lookup_insert_eq _ _ _) (lookup_insert_eq _ _ _) Hll2 Hrl3 with "Hruns")
        as (iv2) "Hacc2". iNamed "Hacc2".
      have Hlenl : length (run_items (flip_run leftRun)) = uint.nat rem.
      { rewrite /flip_run /leftRun /split_run_left /= length_take. lia. }
      wp_apply (wp_item__Len lc (DfracOwn 1) iv2 with "[$Haccval]"). iIntros "[Haccval _]".
      rewrite Haccle0 Hlenl. wp_auto.
      iDestruct ("Haccback" with "Haccval") as "Hruns".
      wp_for_post.
      (* this step's pool move, once: a range-end split followed by the flip of
         the truncated left half *)
      set (p2 := <[tv.(yjs.Text.inner') := MkTypeModel runs2]> pj).
      have Hsplit2 : pool_after_delete pj p2.
      { apply pool_after_split_delete with (parent := tv.(yjs.Text.inner')) (k := q).
        exact (pool_after_split_of_split_runs pj tv.(yjs.Text.inner') (MkTypeModel runsj)
                 q (uint.nat rem) rq Hpj Hrq (Hwfj rq Hrqmem) Hdiffb). }
      have Hp2 : p2 !! tv.(yjs.Text.inner') = Some (MkTypeModel runs2)
        by apply lookup_insert_eq.
      have Hflip2 : pool_after_delete p2 (<[tv.(yjs.Text.inner') := MkTypeModel runs3]> p2)
        := pool_after_delete_flip p2 tv.(yjs.Text.inner') (MkTypeModel runs2) q leftRun Hp2 Hrl2.
      have Hstep : pool_after_delete pj (<[tv.(yjs.Text.inner') := MkTypeModel runs3]> pj).
      { have H := pool_after_delete_trans _ _ _ Hsplit2 Hflip2.
        rewrite /p2 insert_insert_eq in H. exact H. }
      (* the chars just tombstoned: the left half's, which are chars of the run
         the cursor was on, hence of this text's document *)
      have Hdelstomb' : ids_tombstoned (dels ∪ char_ids (run_items (flip_run leftRun)))
                          (all_runs (<[tv.(yjs.Text.inner') := MkTypeModel runs3]> pj)).
      { move=> i Hi. apply elem_of_union in Hi as [Hi | Hi].
        - exact (ids_tombstoned_dead_kept dels pj _ (proj1 (proj2 (proj2 (proj2 Hstep))))
                   Hdelstomb i Hi).
        - exists (flip_run leftRun). split_and!; [| reflexivity | exact Hi].
          apply elem_of_all_runs. exists tv.(yjs.Text.inner'), (MkTypeModel runs3).
          split; [apply lookup_insert_eq | exact (list_elem_of_lookup_2 _ _ _ Hrl3)]. }
      have Hdelsarr' : dels ∪ char_ids (run_items (flip_run leftRun)) ⊆ char_ids (tm_arr ts).
      { apply union_least; [exact Hdelsarr |].
        rewrite /flip_run /leftRun /split_run_left /=.
        etrans; [exact (char_ids_take (uint.nat rem) (run_items rq)) |].
        rewrite -Harrj /tm_arr /=. exact (char_ids_flatten runsj q rq Hrq). }
      iFrame "Hacc Hregistry".
      iFrame "Ht His_lb HΦ".
      iExists (S q), (w64_word_instance.(word.sub) rem (W64 (uint.nat rem))),
        (<[tv.(yjs.Text.inner') := ls2]> locsj), (<[tv.(yjs.Text.inner') := MkTypeModel runs3]> pj), ls2, runs3,
        (dels ∪ char_ids (run_items leftRun)).
      iFrame "Hsp Hrem Hruns Hchanges Htrp Hseq Hhist HtypesAuth".
      have Hnext2 : loc_at ls2 (Z.of_nat (S q)) = loc_at ls2 (Z.of_nat q + 1) by (f_equal; lia).
      rewrite Hnext2 -Haccright0. iFrame "Hcur".
      (* the tombstone-set invariant across this step: both surgeries only
         refine the live cells *)
      iSplitL "Hdelete_set".
      { iApply (own_delete_set_refine with "Hdelete_set").
        exact (proj1 (proj2 (proj2 Hstep))). }
      iPureIntro. split_and!.
      * apply lookup_insert_eq.
      * apply lookup_insert_eq.
      * move=> q' Hne. rewrite lookup_insert_ne //. exact (Hdompj q' Hne).
      * move=> q' Hne. rewrite lookup_insert_ne //. exact (Hdomlj q' Hne).
      * rewrite -Harrj /tm_arr /= /runs3 (runs_flatten_flip_run runs2 q leftRun Hrl2)
          /runs2 (split_runs_flatten runsj q (uint.nat rem) rq Hrq) //.
      * exact Hdelstomb'.
      * exact Hdelsarr'.
      * (* the tombstone state: the split moved no bit, the flip added the left half's chars *)
        rewrite /runs3.
        have Hflip := pool_tombstoned_flip p2 tv.(yjs.Text.inner') (MkTypeModel runs2) q leftRun Hp2 Hrl2.
        rewrite /p2 insert_insert_eq /= in Hflip.
        rewrite Hflip (pool_tombstoned_split pj tv.(yjs.Text.inner') (MkTypeModel runsj) q (uint.nat rem) rq Hpj Hrq)
          Htombj -assoc_L //.
      * (* freshness: the left half was live *)
        have Hp2tomb : pool_tombstoned p2 = pool_tombstoned pj
          := pool_tombstoned_split pj tv.(yjs.Text.inner') (MkTypeModel runsj) q (uint.nat rem) rq Hpj Hrq.
        rewrite elem_of_disjoint => i Hi Hi0. apply elem_of_union in Hi as [Hi | Hi].
        -- exact (proj1 (elem_of_disjoint _ _) Hdelsfresh i Hi Hi0).
        -- apply (proj1 (elem_of_disjoint _ _)
                    (live_run_chars_not_tombstoned p2 tv.(yjs.Text.inner') (MkTypeModel runs2) q leftRun Hpool2 Hp2 Hrl2 Hdl) i Hi).
           rewrite Hp2tomb Htombj. apply elem_of_union_l. exact Hi0.
      * rewrite /runs3 length_insert Hlen2. lia.
    + (* Len <= remaining: tombstone the WHOLE run and spend its length *)
      wp_apply (wp_deleteNode_store tr s_loc (MkStoreState client k locsj pj bind pend pdel)
                  tv.(yjs.Text.inner') lsj (MkTypeModel runsj) q lc rq _ _ _ Hlj Hpj Hlc Hrq with "[$Hruns $Hchanges]").
      iIntros "[Hruns Hchanges]".
      iEval (simpl) in "Hruns".
      (* the record after this step: the run's chars, and this text marked *)
      have Hlne : run_items rq ≠ [] := proj1 (Hwfj rq Hrqmem).
      iEval (rewrite Hdq /= -(assoc_L (∪)) (marked_step _ _ _ _ Hlne)) in "Hchanges".
      wp_auto.
      set (runs3 := <[q := flip_run rq]> runsj).
      have Hrl3 : runs3 !! q = Some (flip_run rq).
      { rewrite /runs3 list_lookup_insert_eq //. }
      iDestruct (own_store_state_node_acc_links s_loc
                   (MkStoreState client k locsj (<[tv.(yjs.Text.inner') := MkTypeModel runs3]> pj) bind pend pdel)
                   tv.(yjs.Text.inner') lsj (MkTypeModel runs3) q lc (flip_run rq)
                   Hlj (lookup_insert_eq _ _ _) Hlc Hrl3 with "Hruns")
        as (iv2) "Hacc2". iNamed "Hacc2".
      have Hlenf : length (run_items (flip_run rq)) = length (run_items rq) by rewrite /flip_run //.
      wp_apply (wp_item__Len lc (DfracOwn 1) iv2 with "[$Haccval]"). iIntros "[Haccval _]".
      rewrite Haccle0 Hlenf. wp_auto.
      iDestruct ("Haccback" with "Haccval") as "Hruns".
      wp_for_post.
      have Hstep : pool_after_delete pj (<[tv.(yjs.Text.inner') := MkTypeModel runs3]> pj)
        := pool_after_delete_flip pj tv.(yjs.Text.inner') (MkTypeModel runsj) q rq Hpj Hrq.
      (* the chars just tombstoned: the whole run the cursor was on *)
      have Hdelstomb' : ids_tombstoned (dels ∪ char_ids (run_items rq))
                          (all_runs (<[tv.(yjs.Text.inner') := MkTypeModel runs3]> pj)).
      { move=> i Hi. apply elem_of_union in Hi as [Hi | Hi].
        - exact (ids_tombstoned_dead_kept dels pj _ (proj1 (proj2 (proj2 (proj2 Hstep))))
                   Hdelstomb i Hi).
        - exists (flip_run rq). split_and!; [| reflexivity | exact Hi].
          apply elem_of_all_runs. exists tv.(yjs.Text.inner'), (MkTypeModel runs3).
          split; [apply lookup_insert_eq | exact (list_elem_of_lookup_2 _ _ _ Hrl3)]. }
      have Hdelsarr' : dels ∪ char_ids (run_items rq) ⊆ char_ids (tm_arr ts).
      { apply union_least; [exact Hdelsarr |].
        rewrite -Harrj /tm_arr /=. exact (char_ids_flatten runsj q rq Hrq). }
      iFrame "Hacc Hregistry".
      iFrame "Ht His_lb HΦ".
      iExists (S q), (w64_word_instance.(word.sub) rem (W64 (length (run_items rq)))),
        locsj, (<[tv.(yjs.Text.inner') := MkTypeModel runs3]> pj), lsj, runs3,
        (dels ∪ char_ids (run_items rq)).
      iFrame "Hsp Hrem Hruns Hchanges Htrp Hseq Hhist HtypesAuth".
      rewrite Hnextq -Haccright0. iFrame "Hcur".
      (* the tombstone-set invariant across this step: a flip only turns bits
         ON, so the live cells refine *)
      iSplitL "Hdelete_set".
      { iApply (own_delete_set_refine with "Hdelete_set").
        exact (proj1 (proj2 (proj2 Hstep))). }
      iPureIntro. split_and!.
      * apply lookup_insert_eq.
      * exact Hlj.
      * move=> q' Hne. rewrite lookup_insert_ne //. exact (Hdompj q' Hne).
      * exact Hdomlj.
      * rewrite -Harrj /tm_arr /= /runs3 (runs_flatten_flip_run runsj q rq Hrq) //.
      * exact Hdelstomb'.
      * exact Hdelsarr'.
      * (* the tombstone state: the flip added the run's chars *)
        rewrite /runs3 (pool_tombstoned_flip pj tv.(yjs.Text.inner') (MkTypeModel runsj) q rq Hpj Hrq)
          Htombj -assoc_L //.
      * (* freshness: the run was live *)
        rewrite elem_of_disjoint => i Hi Hi0. apply elem_of_union in Hi as [Hi | Hi].
        -- exact (proj1 (elem_of_disjoint _ _) Hdelsfresh i Hi Hi0).
        -- apply (proj1 (elem_of_disjoint _ _)
                    (live_run_chars_not_tombstoned pj tv.(yjs.Text.inner') (MkTypeModel runsj) q rq Hpoolj0 Hpj Hrq Hdq) i Hi).
           rewrite Htombj. apply elem_of_union_l. exact Hi0.
      * rewrite /runs3 length_insert. lia.
Qed.

End text.
