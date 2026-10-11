(** The [Transaction]'s unexported methods (issue #206 T1): what a
    transaction records while it runs, and the two cell-level steps that
    record.

    - [wp_newTransaction]: a fresh record, of the given store, that has
      recorded nothing.
    - [wp_Transaction__recordInsert] / [_recordDelete]: a node joins the
      insert set or the delete set (its head id and length as one span) and
      its parent joins the changed types. Both read the node's id and length
      off its points-to, which the caller borrows for the call.
    - [wp_Transaction__integrate]: the store's [Integrate] (the splice into
      the type) followed by [recordInsert] of the new run, over the public
      [own_store] and the record (issue #219); [_integrate_state] is its
      second spec at cell level, over [own_store_state], because
      [Text.InsertIn] and the drain loop call it while the clock tie is
      broken.
    - [wp_Transaction__deleteNode] / [_deleteNode_store]: the store's
      [deleteNode] (the flip) followed by [recordDelete] when the node was
      live; over the public [own_store] (issue #219), and at cell level
      ([own_store_state]) for the delete loops that step by it. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core.
From New.proof Require Import prelude.
From New.proof Require Import algebra.
From New.proof Require Import history.
From iris.algebra Require Import auth gmap gset.
From iris.algebra.lib Require Import dfrac_agree.
From New.proof.id Require Import id.
From New.proof.item Require Import item.
From New.proof.ytype Require Import ytype.
From New.proof.store Require Import store.
From New.proof.transaction Require Import model heap.
From RecordUpdate Require Import RecordSet.

Section transaction_wp.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.

Notation P := go_string.

Local Notation TId := (TypeId P).

Local Notation Ev := (@Event (TId * @YjsOperation A)).

Local Notation DocModel := (gmap TId (list (YjsItem A))).

(* the store's ghost state, as [store/heap]: the record predicate is stated in
   a section that carries it *)
Context {seq_inG : inG Σ (authR (gmapUR loc (gsetUR (YjsItem A))))}.
Context {acc_inG : inG Σ (authR (gsetUR YjsId))}.
Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO store_state))}.
Context {observed_inG : ghost_varG Σ (list (YjsItem go_string * bool))}.
Context {observers_inG : inG Σ (authR (gsetUR (gname * go_string)))}.
Context {observers_agree_inG : inG Σ (dfrac_agreeR (leibnizO registered_entries))}.

Lemma wp_newTransaction (s_loc : loc) :
  {{{ is_pkg_init yjs }}}
    @! yjs.newTransaction #s_loc
  {{{ (tr : loc), RET #tr; own_transaction_changes tr s_loc ∅ ∅ ∅ }}}.
Proof.
  wp_start. wp_auto.
  wp_apply wp_map_make1. iIntros (changed_mref) "Hchanged". wp_auto.
  wp_alloc tr as "Htr". wp_auto.
  iApply "HΦ".
  iStructNamed "Htr". simpl.
  iExists slice.nil, slice.nil, changed_mref, [], []. iFrame "store insertSet deleteSet changed".
  rewrite gset_to_gmap_empty. iFrame "Hchanged".
  iSplitL; first iApply own_slice_nil.
  iSplitL; first iApply own_slice_cap_nil.
  iSplitR; first done.
  iSplitR; first done.
  iSplitL; first iApply own_slice_nil.
  iSplitL; first iApply own_slice_cap_nil.
  done.
Qed.

Lemma wp_Transaction__recordInsert (tr s_loc parent lc : loc) (dq : dfrac) (v : yjs.item.t)
    (inserted tombstoned : gset YjsId) (changed : gset loc) :
  span_no_overflow (node_span v) ->
  {{{ is_pkg_init yjs ∗ own_transaction_changes tr s_loc inserted tombstoned changed ∗ lc ↦{dq} v }}}
    tr @! (go.PointerType yjs.Transaction) @! "recordInsert" #parent #lc
  {{{ RET #();
      own_transaction_changes tr s_loc (inserted ∪ span_ids (node_span v)) tombstoned
        (changed ∪ {[parent]}) ∗
      lc ↦{dq} v }}}.
Proof.
  move=> Hfits.
  wp_start as "(Hchanges & Hv)". iNamed "Hchanges". wp_auto.
  wp_apply (wp_item__Len with "[$Hv]"). iIntros "[Hv _]". wp_auto.
  wp_apply wp_slice_literal. iSplitR; first done. iIntros "%s2 [Hs2 _]". wp_auto.
  wp_apply (wp_slice_append with "[$Hinsert $Hinsertcap $Hs2]").
  iIntros (sl') "(Hinsert & Hinsertcap & _)". wp_auto.
  wp_apply (wp_map_insert with "Hchanged"). iIntros "Hchanged". wp_auto.
  iApply "HΦ". iFrame "Hv".
  iExists sl', delete_sl, changed_mref, (insert_vs ++ [node_span v]), delete_vs. simpl.
  iFrame "Htrstore Hinsertf Hinsert Hinsertcap Hdeletef Hdelete Hdeletecap Hchangedf".
  rewrite (union_comm_L changed) gset_to_gmap_union_singleton. iFrame "Hchanged".
  iPureIntro. split_and!; [ | | done | done].
  - apply Forall_app. split; [exact Hinsertwf | by apply Forall_singleton].
  - rewrite span_union_snoc Hinserted. apply union_comm_L.
Qed.

Lemma wp_Transaction__recordDelete (tr s_loc lc : loc) (dq : dfrac) (v : yjs.item.t)
    (inserted tombstoned : gset YjsId) (changed : gset loc) :
  span_no_overflow (node_span v) ->
  {{{ is_pkg_init yjs ∗ own_transaction_changes tr s_loc inserted tombstoned changed ∗ lc ↦{dq} v }}}
    tr @! (go.PointerType yjs.Transaction) @! "recordDelete" #lc
  {{{ RET #();
      own_transaction_changes tr s_loc inserted (tombstoned ∪ span_ids (node_span v))
        (changed ∪ {[v.(yjs.item.parent')]}) ∗
      lc ↦{dq} v }}}.
Proof.
  move=> Hfits.
  wp_start as "(Hchanges & Hv)". iNamed "Hchanges". wp_auto.
  wp_apply (wp_item__Len with "[$Hv]"). iIntros "[Hv _]". wp_auto.
  wp_apply wp_slice_literal. iSplitR; first done. iIntros "%s2 [Hs2 _]". wp_auto.
  wp_apply (wp_slice_append with "[$Hdelete $Hdeletecap $Hs2]").
  iIntros (sl') "(Hdelete & Hdeletecap & _)". wp_auto.
  wp_apply (wp_map_insert with "Hchanged"). iIntros "Hchanged". wp_auto.
  iApply "HΦ". iFrame "Hv".
  iExists insert_sl, sl', changed_mref, insert_vs, (delete_vs ++ [node_span v]). simpl.
  iFrame "Htrstore Hinsertf Hinsert Hinsertcap Hdeletef Hdelete Hdeletecap Hchangedf".
  rewrite (union_comm_L changed) gset_to_gmap_union_singleton. iFrame "Hchanged".
  iPureIntro. split_and!; [done | done | | ].
  - apply Forall_app. split; [exact Hdeletewf | by apply Forall_singleton].
  - rewrite span_union_snoc Htombstoned. apply union_comm_L.
Qed.

(** [Transaction.integrate]: the store's splice ([wp_store__Integrate_state]),
    then the new run joins the record: its chars the insert set, its type
    the changed types. The statement is [wp_store__Integrate_state]'s with the
    record threaded through. *)
Lemma wp_Transaction__integrate_state (tr s parent parent_arg item_l : loc)
    (state : store_state) (tm : type_model) (ls : list loc)
    (arr' : list (YjsItem A)) (input : IntegrateInput (A := A))
    (newItem : YjsItem A) (kL kR : nat)
    (inserted tombstoned : gset YjsId) (changed : gset loc) :
  parent_arg = parent ∨ parent_arg = null ->
  ss_pool state !! parent = Some tm ->
  ss_locs state !! parent = Some ls ->
  integrate_ready (tm_arr tm) input newItem ->
  input_fits input ->
  integrate_all (ops_of_input input (explode (in_content input))) (tm_arr tm) = Some arr' ->
  origins_resolved (tm_runs tm) (tm_arr tm) input kL kR ->
  pool_next_clock (ss_pool state) (clientId (in_id input)) (clock (in_id input)) ->
  {{{ is_pkg_init yjs ∗ own_store_state s 1 state ∗
      own_linked_item item_l input parent
        (loc_at ls (Z.of_nat kL - 1)) (loc_at ls (Z.of_nat kR)) ∗
      own_transaction_changes tr s inserted tombstoned changed }}}
    tr @! (go.PointerType yjs.Transaction) @! "integrate" #parent_arg #item_l
  {{{ (runs' : list ItemRun) (ls' : list loc) (run : list (YjsItem A)), RET #();
      own_store_state s 1 (state <| ss_pool := <[parent := MkTypeModel runs']> (ss_pool state) |>
                            <| ss_locs := <[parent := ls']> (ss_locs state) |>) ∗
      own_transaction_changes tr s (inserted ∪ char_ids run) tombstoned (changed ∪ {[parent]}) ∗
      ⌜YjsArrInvariant arr'⌝ ∗
      ⌜∃ idx : nat, runs_integrate_splice_at idx (tm_runs tm) (tm_arr tm) run runs' arr' ∧
                    ls' = integrate_locs ls idx item_l⌝ ∗
      ⌜run_denotes input newItem run⌝ }}}.
Proof using Type*.
  move=> Hparg Hpl Hlocs Hready Hfitsin Hall Hres Hnext.
  iIntros (Φ) "(#Hpkg & Hruns & Hfresh & Hchanges) HΦ".
  iDestruct (own_store_state_aligned with "Hruns") as %[_ Hlens].
  have Hlsl : length ls = length (tm_runs tm) := Hlens parent ls tm Hlocs Hpl.
  iDestruct (own_transaction_changes_store_acc with "Hchanges") as "[Htrstore Hchangesback]".
  wp_method_call. wp_call. wp_call. wp_auto.
  wp_apply (wp_store__Integrate_state s parent parent_arg item_l state tm ls arr' input newItem kL kR
              Hparg Hpl Hlocs Hready Hfitsin Hall Hres Hnext with "[$Hpkg $Hruns $Hfresh]").
  iIntros (runs' ls' run) "(Hruns & %Hinv' & %Hsplice & %Hden)".
  iDestruct ("Hchangesback" with "Htrstore") as "Hchanges".
  destruct Hsplice as (idx & Hsp & Hls'eq).
  have Hsp0 := Hsp.
  destruct Hsp as (Hidxb & _ & Hruns'eq & _).
  (* the new run's slot in the type *)
  set (r := MkItemRun run false).
  have Hrk' : runs' !! idx = Some r.
  { rewrite Hruns'eq. apply list_lookup_middle. rewrite length_take_le; [done | lia]. }
  have Hlk' : ls' !! idx = Some item_l.
  { rewrite Hls'eq /integrate_locs. apply list_lookup_middle. rewrite length_take_le; [done | lia]. }
  have Hpl' : ss_pool (state <| ss_pool := <[parent := MkTypeModel runs']> (ss_pool state) |>
                            <| ss_locs := <[parent := ls']> (ss_locs state) |>) !! parent
              = Some (MkTypeModel runs') by apply lookup_insert_eq.
  have Hlocs' : ss_locs (state <| ss_pool := <[parent := MkTypeModel runs']> (ss_pool state) |>
                            <| ss_locs := <[parent := ls']> (ss_locs state) |>) !! parent
              = Some ls' by apply lookup_insert_eq.
  (* the run is in the pool now: well formed and fitting *)
  iDestruct (own_store_state_run_wf with "Hruns") as %Hwf'.
  iDestruct (own_store_state_run_pool_invs with "Hruns") as %Hrpi'.
  have Hrmem : r ∈ all_runs (<[parent := MkTypeModel runs']> (ss_pool state)).
  { apply (elem_of_all_runs_lookup _ parent (MkTypeModel runs') r (lookup_insert_eq _ _ _)).
    left. exact (list_elem_of_lookup_2 _ _ _ Hrk'). }
  have Hwfr : run_wf (run_items r) := Hwf' r Hrmem.
  have Hfitsr : run_fits r := proj1 (proj2 (proj1 Hrpi' r Hrmem)).
  (* the parent is a real type, so the result is not nil *)
  iDestruct (own_store_state_ytype_acc s 1 _ parent ls' (MkTypeModel runs') Hlocs' Hpl' with "Hruns") as "[Hyt Hytback]".
  iDestruct "Hyt" as (yt tl) "(Hparent & Hdll & %Hlen)".
  iDestruct (typed_pointsto_not_null with "Hparent") as %Hpnn.
  iAssert (own_ytype parent (DfracOwn 1) ls' (MkTypeModel runs')) with "[Hparent Hdll]" as "Hyt".
  { iExists yt, tl. iFrame "Hparent Hdll". iPureIntro. exact Hlen. }
  iDestruct ("Hytback" with "Hyt") as "Hruns".
  wp_auto.
  rewrite (bool_decide_eq_false_2 (parent = null) Hpnn). wp_auto.
  (* record the run: borrow its node to read the id and the length *)
  iDestruct (own_store_state_node_acc s _ parent ls' (MkTypeModel runs') idx item_l r Hlocs' Hpl' Hlk' Hrk'
               with "Hruns") as (itemVal) "H". iNamed "H".
  have Hid' : toYjsId itemVal.(yjs.item.id') = item_id (run_head_item r) by rewrite Haccid.
  destruct (node_span_char_ids itemVal r Hwfr Hid' Haccle Hfitsr) as [Hfits Hspan].
  wp_apply (wp_Transaction__recordInsert tr s parent item_l (DfracOwn 1) itemVal inserted tombstoned changed
              Hfits with "[$Hchanges $Haccval]").
  iIntros "[Hchanges Haccval]".
  iDestruct ("Haccback" with "Haccval") as "Hruns".
  wp_auto.
  iApply ("HΦ" $! runs' ls' run).
  rewrite Hspan. iFrame "Hruns Hchanges".
  iPureIntro. split_and!; [exact Hinv' | exists idx; split; [exact Hsp0 | exact Hls'eq] | exact Hden].
Qed.

(** [Transaction.deleteNode] at the pool: the store's [deleteNode] flips the
    run ([wp_store__deleteNode_pool]) and, when it was live, [recordDelete] records its
    chars and its type. The statement is [wp_store__deleteNode_pool]'s with the record
    threaded through. *)
#[local] Lemma wp_Transaction__deleteNode_pool (tr s_loc : loc) (locs : gmap loc (list loc)) (p : pool)
    (parent : loc) (ls : list loc) (tm : type_model) (k : nat) (lc : loc) (r : ItemRun)
    (inserted tombstoned : gset YjsId) (changed : gset loc) :
  locs !! parent = Some ls ->
  p !! parent = Some tm ->
  ls !! k = Some lc ->
  tm_runs tm !! k = Some r ->
  run_fits r ->
  {{{ is_pkg_init yjs ∗ own_type_pool (DfracOwn 1) locs p ∗
      own_transaction_changes tr s_loc inserted tombstoned changed }}}
    tr @! (go.PointerType yjs.Transaction) @! "deleteNode" #lc
  {{{ RET #(); own_type_pool (DfracOwn 1) locs
        (<[parent := MkTypeModel (<[k := flip_run r]> (tm_runs tm))]> p) ∗
      own_transaction_changes tr s_loc inserted
        (if run_deleted r then tombstoned else tombstoned ∪ char_ids (run_items r))
        (if run_deleted r then changed else changed ∪ {[parent]}) }}}.
Proof using Type*.
  move=> Hlp Hpp Hlk Hrk Hrfits.
  wp_start as "[Hpool Hchanges]".
  iDestruct (own_type_pool_run_wf with "Hpool") as %Hwfall.
  have Hrmem : r ∈ all_runs p.
  { apply (elem_of_all_runs_lookup p parent tm r Hpp). left. exact (list_elem_of_lookup_2 _ _ _ Hrk). }
  have Hwfr : run_wf (run_items r) := Hwfall r Hrmem.
  iDestruct (own_transaction_changes_store_acc with "Hchanges") as "[Htrstore Hchangesback]".
  wp_auto.
  wp_apply (wp_store__deleteNode_pool s_loc locs p parent ls tm k lc r Hlp Hpp Hlk Hrk Hrfits with "[$Hpool]").
  iIntros "Hpool".
  iDestruct ("Hchangesback" with "Htrstore") as "Hchanges".
  destruct (run_deleted r) eqn:Hd; simpl negb.
  - (* already a tombstone: nothing to record *)
    wp_auto. iApply "HΦ". iFrame "Hpool Hchanges".
  - (* live: record the node, borrowed from the pool after the flip *)
    wp_auto.
    have Hklt : (k < length (tm_runs tm))%nat := lookup_lt_Some _ _ _ Hrk.
    iDestruct (own_type_pool_node_acc locs _ parent ls (MkTypeModel (<[k := flip_run r]> (tm_runs tm))) k lc (flip_run r)
                 Hlp (lookup_insert_eq _ _ _) Hlk (list_lookup_insert_eq _ _ _ Hklt) with "Hpool") as (itemVal) "H".
    iNamed "H". simpl in Haccid, Haccle.
    have Hid' : toYjsId itemVal.(yjs.item.id') = item_id (run_head_item r) by rewrite Haccid.
    destruct (node_span_char_ids itemVal r Hwfr Hid' Haccle Hrfits) as [Hfits Hspan].
    wp_apply (wp_Transaction__recordDelete tr s_loc lc (DfracOwn 1) itemVal inserted tombstoned changed
                Hfits with "[$Hchanges $Haccval]").
    iIntros "[Hchanges Haccval]".
    iDestruct ("Haccback" with "Haccval") as "Hpool".
    wp_auto.
    iApply "HΦ". rewrite Hspan Haccpar. iFrame "Hpool Hchanges".
Qed.

(** [Transaction.deleteNode] on the store: the addressed run is tombstoned
    and recorded, every other field untouched (the store re-closed around
    [wp_Transaction__deleteNode_pool]); what the delete loops ([deleteRange] /
    [applyDeleteSpans] here, [Text.DeleteIn] in [text/DeleteIn]) step by. *)
Lemma wp_Transaction__deleteNode_store (tr s : loc) (state : store_state)
    (parent : loc) (ls : list loc) (tm : type_model) (k : nat) (lc : loc) (r : ItemRun)
    (inserted tombstoned : gset YjsId) (changed : gset loc) :
  ss_locs state !! parent = Some ls ->
  ss_pool state !! parent = Some tm ->
  ls !! k = Some lc ->
  tm_runs tm !! k = Some r ->
  {{{ is_pkg_init yjs ∗ own_store_state s 1 state ∗
      own_transaction_changes tr s inserted tombstoned changed }}}
    tr @! (go.PointerType yjs.Transaction) @! "deleteNode" #lc
  {{{ RET #(); own_store_state s 1
        (state <| ss_pool := <[parent := MkTypeModel (<[k := flip_run r]> (tm_runs tm))]>
                             (ss_pool state) |>) ∗
      own_transaction_changes tr s inserted
        (if run_deleted r then tombstoned else tombstoned ∪ char_ids (run_items r))
        (if run_deleted r then changed else changed ∪ {[parent]}) }}}.
Proof.
  move=> Hls Hp Hlk Hrk.
  iIntros (Φ) "(#Hpkg & Hruns & Hchanges) HΦ".
  destruct state as [client0 k0 locs p bind pend pdel]. simpl in *.
  iDestruct "Hruns" as "(Hfields & %Hinvs)".
  have Hrpi : pool_invs p := proj1 Hinvs.
  have Hreg : pool_registry_coh bind p := proj1 (proj2 Hinvs).
  have Hcontig : pool_clocks_contiguous p := proj2 (proj2 Hinvs).
  have Hrmem : r ∈ all_runs p.
  { apply (elem_of_all_runs_lookup p parent tm r Hp). left. exact (list_elem_of_lookup_2 _ _ _ Hrk). }
  have Hrfits : run_fits r := proj1 (proj2 (proj1 Hrpi r Hrmem)).
  iDestruct "Hfields" as "(Hclient & Hclock & HdeletedSet & Hitems & Hregistry & Htypes & Hpending & Hpdeletes)".
  iEval (simpl) in "Hitems Htypes".
  wp_apply (wp_Transaction__deleteNode_pool tr s locs p parent ls tm k lc r inserted tombstoned changed
              Hls Hp Hlk Hrk Hrfits with "[$Hpkg $Htypes $Hchanges]").
  iIntros "[Htypes Hchanges]".
  set (tm' := MkTypeModel (<[k := flip_run r]> (tm_runs tm))) in *.
  have Hrpi' : pool_invs (<[parent := tm']> p) := pool_invs_flip p parent tm k r Hp Hrk Hrpi.
  have Hreg' : pool_registry_coh bind (<[parent := tm']> p)
    := pool_registry_coh_insert_existing bind p parent tm tm' Hp Hreg.
  have Hcontig' : pool_clocks_contiguous (<[parent := tm']> p).
  { apply (pool_clocks_contiguous_ext p _ parent tm tm'); [| exact Hp | apply lookup_insert_eq | | exact Hcontig].
    - move=> q Hne. rewrite lookup_insert_ne //.
    - rewrite /tm' /tm_arr /=. exact (runs_flatten_flip_run (tm_runs tm) k r Hrk). }
  (* the item index is unchanged: a flip keeps every entry's key *)
  have Hkps : entry_key_pair <$> pool_entries locs (<[parent := tm']> p) ≡ₚ entry_key_pair <$> pool_entries locs p
    := pool_entries_flip_key_pairs locs p parent ls tm k lc r Hls Hp Hlk Hrk.
  iDestruct "Hitems" as (mref) "(Hitemsf & Hitemmap)".
  iEval (rewrite /own_item_map) in "Hitemmap".
  iDestruct (own_item_map_key_pairs_keys_perm mref (DfracOwn 1) _ _ (Permutation_sym Hkps) with "Hitemmap") as "Hitemmap".
  iApply "HΦ".
  iSplitR "Hchanges"; last iExact "Hchanges".
  iSplitL; last (iPureIntro; split_and!; [exact Hrpi' | exact Hreg' | exact Hcontig']).
  rewrite /own_store_fields /=.
  iFrame "Hclient Hclock HdeletedSet Hregistry Htypes Hpending Hpdeletes".
  iExists mref. iFrame "Hitemsf Hitemmap".
Qed.

(** [Transaction.deleteNode], the public form (issue #219): the store
    taken and returned whole ([own_store]) beside the record. The flip
    moves no authority and only strengthens the tombstone clause, so the
    closure is the public store wrapper's, with the record stepped as in
    the state form above. *)
Lemma wp_Transaction__deleteNode (tr s : loc) (γs : store_names) (γh : history_names)
    (parent : loc) (ls : list loc) (tm : type_model) (k : nat) (lc : loc) (r : ItemRun)
    (state : store_state) (ds : gset YjsId) (m0 : DocModel) (deleted0 : gset YjsId)
    (inserted tombstoned : gset YjsId) (changed : gset loc) :
  ss_locs state !! parent = Some ls ->
  ss_pool state !! parent = Some tm ->
  ls !! k = Some lc ->
  tm_runs tm !! k = Some r ->
  {{{ is_pkg_init yjs ∗ own_store s γs γh 1 state ds m0 deleted0 ∗
      own_transaction_changes tr s inserted tombstoned changed }}}
    tr @! (go.PointerType yjs.Transaction) @! "deleteNode" #lc
  {{{ RET #(); own_store s γs γh 1
        (state <| ss_pool := <[parent := MkTypeModel (<[k := flip_run r]> (tm_runs tm))]>
                             (ss_pool state) |>) ds m0 deleted0 ∗
      own_transaction_changes tr s inserted
        (if run_deleted r then tombstoned else tombstoned ∪ char_ids (run_items r))
        (if run_deleted r then changed else changed ∪ {[parent]}) }}}.
Proof using Type*.
  move=> Hls Hp Hlk Hrk.
  iIntros (Φ) "(#Hpkg & Hstore & Hchanges) HΦ".
  iNamed "Hstore". iNamed "Hcore".
  destruct state as [client0 k0 locs p bind pend pdel]. simpl in *.
  have Hrmem : r ∈ all_runs p.
  { apply elem_of_all_runs. exists parent, tm.
    split; [exact Hp | exact (list_elem_of_lookup_2 _ _ _ Hrk)]. }
  iDestruct (own_store_state_run_pool_invs with "Hstate") as %Hrpi0.
  iApply wp_fupd.
  wp_apply (wp_Transaction__deleteNode_store tr s (MkStoreState client0 k0 locs p bind pend pdel)
              parent ls tm k lc r inserted tombstoned changed Hls Hp Hlk Hrk
              with "[$Hpkg $Hstate $Hchanges]").
  iIntros "[Hstate Hchanges]". iEval (simpl) in "Hstate".
  set (tm' := MkTypeModel (<[k := flip_run r]> (tm_runs tm))) in *.
  have Hfmap : ((λ tm0, (list_to_set (tm_arr tm0) : gset (YjsItem A))) <$> (<[parent := tm']> p))
             = ((λ tm0, (list_to_set (tm_arr tm0) : gset (YjsItem A))) <$> p).
  { apply map_eq => q. destruct (decide (q = parent)) as [-> | Hne].
    - rewrite lookup_fmap lookup_insert_eq lookup_fmap Hp /=.
      do 2 f_equal. rewrite /tm' /tm_arr /=.
      exact (runs_flatten_flip_run (tm_runs tm) k r Hrk).
    - rewrite !lookup_fmap lookup_insert_ne //. }
  have Hds_tomb' : delete_set_tombstoned ds (all_runs (<[parent := tm']> p))
    := delete_set_tombstoned_flip ds p parent tm k r Hp Hrk Hds_tomb.
  iMod (state_frag_update γs _ with "Hstate_agree") as "Hstate_agree".
  iModIntro.
  iApply "HΦ".
  iFrame "Hchanges".
  rewrite /own_store /own_store_core /= Hfmap.
  iFrame "Hobservers Hclientpin Hseq HtypesAuth Hbinds Hdelete_set_auth Hstate_agree Hstate".
  iPureIntro. exact Hds_tomb'.
Qed.


(** [Transaction.integrate], the public form (issue #219): the store
    taken and returned whole beside the record. As in the public
    [wp_store__Integrate], the item-set authority grows at the parent by
    the spliced run, and the live splice demands the one premise the
    store alone cannot supply, [input_char_ids input ## ds] (the replica
    history's domain bound hands it to the callers: a fresh id is in no
    model). Delegates to the state form, which does the splice and the
    record step. *)
Lemma wp_Transaction__integrate (tr s parent parent_arg item_l : loc)
    (γs : store_names) (γh : history_names)
    (tm : type_model) (ls : list loc)
    (arr' : list (YjsItem A)) (input : IntegrateInput (A := A))
    (newItem : YjsItem A) (kL kR : nat)
    (state : store_state) (ds : gset YjsId) (m0 : DocModel) (deleted0 : gset YjsId)
    (inserted tombstoned : gset YjsId) (changed : gset loc) :
  parent_arg = parent ∨ parent_arg = null ->
  ss_pool state !! parent = Some tm ->
  ss_locs state !! parent = Some ls ->
  integrate_ready (tm_arr tm) input newItem ->
  input_fits input ->
  integrate_all (ops_of_input input (explode (in_content input))) (tm_arr tm) = Some arr' ->
  origins_resolved (tm_runs tm) (tm_arr tm) input kL kR ->
  pool_next_clock (ss_pool state) (clientId (in_id input)) (clock (in_id input)) ->
  input_char_ids input ## ds ->
  {{{ is_pkg_init yjs ∗ own_store s γs γh 1 state ds m0 deleted0 ∗
      own_linked_item item_l input parent
        (loc_at ls (Z.of_nat kL - 1)) (loc_at ls (Z.of_nat kR)) ∗
      own_transaction_changes tr s inserted tombstoned changed }}}
    tr @! (go.PointerType yjs.Transaction) @! "integrate" #parent_arg #item_l
  {{{ (runs' : list ItemRun) (ls' : list loc) (run : list (YjsItem A)), RET #();
      own_store s γs γh 1
        (state <| ss_pool := <[parent := MkTypeModel runs']> (ss_pool state) |>
               <| ss_locs := <[parent := ls']> (ss_locs state) |>) ds m0 deleted0 ∗
      own_transaction_changes tr s (inserted ∪ char_ids run) tombstoned (changed ∪ {[parent]}) ∗
      ⌜YjsArrInvariant arr'⌝ ∗
      ⌜∃ idx : nat, runs_integrate_splice_at idx (tm_runs tm) (tm_arr tm) run runs' arr' ∧
                    ls' = integrate_locs ls idx item_l⌝ ∗
      ⌜run_denotes input newItem run⌝ }}}.
Proof using Type*.
  move=> Hparg Hpl Hlocs Hready Hfitsin Hall Hres Hnext Hdisj.
  iIntros (Φ) "(#Hpkg & Hstore & Hfresh & Hchanges) HΦ".
  iNamed "Hstore". iNamed "Hcore".
  destruct state as [client0 k0 locs p bind pend pdel]. simpl in *.
  iApply wp_fupd.
  wp_apply (wp_Transaction__integrate_state tr s parent parent_arg item_l
              (MkStoreState client0 k0 locs p bind pend pdel) tm ls arr' input newItem kL kR
              inserted tombstoned changed
              Hparg Hpl Hlocs Hready Hfitsin Hall Hres Hnext
              with "[$Hpkg $Hstate $Hfresh $Hchanges]").
  iIntros (runs' ls' run) "(Hstate & Hchanges & %Hinv' & %Hsplice & %Hden)".
  iEval (simpl) in "Hstate".
  destruct Hsplice as (idx & Hsp & Hls'eq).
  have Hsp0 := Hsp.
  destruct Hsp as (Hidxb & Hmile & Hruns'eq & Harr'eq).
  iDestruct (own_store_state_run_wf with "Hstate") as %Hwf'.
  have Hrmem' : MkItemRun run false ∈ all_runs (<[parent := MkTypeModel runs']> p).
  { apply elem_of_all_runs. exists parent, (MkTypeModel runs').
    split; [apply lookup_insert_eq |].
    simpl. rewrite Hruns'eq. apply elem_of_app. right. by left. }
  have Hwfr : run_wf run := Hwf' _ Hrmem'.
  have Hcids : char_ids run = input_char_ids input
    := run_denotes_char_ids input newItem run Hwfr Hden.
  have Hmk : ((λ tm0, (list_to_set (tm_arr tm0) : gset (YjsItem A))) <$> p) !! parent
           = Some (list_to_set (tm_arr tm)) by rewrite lookup_fmap Hpl //.
  have Hsub : (list_to_set (tm_arr tm) : gset (YjsItem A)) ⊆ list_to_set arr'.
  { rewrite Harr'eq. intros x. rewrite !elem_of_list_to_set. intros Hx.
    rewrite -(take_drop (length (runs_flatten (take idx (tm_runs tm)))) (tm_arr tm)) in Hx.
    apply elem_of_app in Hx as [Hx | Hx].
    - apply elem_of_app. by left.
    - apply elem_of_app. right. apply elem_of_app. by right. }
  iMod (auth_gmap_gset_grow γs.(sn_seq) _ parent (list_to_set (tm_arr tm)) (list_to_set arr')
          Hmk Hsub with "Hseq") as "[Hseq _]".
  have Hfmap : <[parent := (list_to_set arr' : gset (YjsItem A))]>
                 ((λ tm0, (list_to_set (tm_arr tm0) : gset (YjsItem A))) <$> p)
             = ((λ tm0, (list_to_set (tm_arr tm0) : gset (YjsItem A))) <$> (<[parent := MkTypeModel runs']> p)).
  { rewrite fmap_insert. f_equal.
    rewrite /tm_arr /= (runs_integrate_splice_at_flatten idx (tm_runs tm) runs' run arr' Hsp0) //. }
  have Hperm2 : all_runs (<[parent := MkTypeModel runs']> p) ≡ₚ all_runs p ++ [MkItemRun run false].
  { have Hcons : all_runs (<[parent := MkTypeModel runs']> p) ≡ₚ MkItemRun run false :: all_runs p.
    { rewrite Hruns'eq (all_runs_insert p parent tm _ Hpl) /= (all_runs_lookup p parent tm Hpl).
      rewrite -app_assoc /=. rewrite -{3}(take_drop idx (tm_runs tm)) -app_assoc.
      symmetry. apply Permutation_middle. }
    rewrite Hcons. apply Permutation_cons_append. }
  have Hfreshids : ∀ y, y ∈ run_items (MkItemRun run false) -> item_id y ∉ ds.
  { move=> y Hy Hin. simpl in Hy.
    have Hinc : item_id y ∈ char_ids run.
    { rewrite /char_ids elem_of_list_to_set. apply list_elem_of_fmap. by exists y. }
    rewrite Hcids in Hinc. exact (Hdisj (item_id y) Hinc Hin). }
  have Hds_tomb' := delete_set_tombstoned_snoc ds (all_runs p)
                      (all_runs (<[parent := MkTypeModel runs']> p)) (MkItemRun run false)
                      Hperm2 Hfreshids Hds_tomb.
  iMod (state_frag_update γs _ with "Hstate_agree") as "Hstate_agree".
  iModIntro. iApply ("HΦ" $! runs' ls' run).
  iFrame "Hchanges".
  iSplitL; last (iPureIntro; split_and!;
    [exact Hinv' | exists idx; split; [exact Hsp0 | exact Hls'eq] | exact Hden]).
  rewrite /own_store /own_store_core /= -Hfmap.
  iFrame "Hobservers Hclientpin Hseq HtypesAuth Hbinds Hdelete_set_auth Hstate_agree Hstate".
  iPureIntro. exact Hds_tomb'.
Qed.

End transaction_wp.
