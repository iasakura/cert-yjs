(** [deleteNode] (issue #133, plan section 5): tombstone one integrated
    node, reporting whether it was live. [wp_deleteNode] is the pool-level
    core, [wp_deleteNode_store] the store re-closed around it. Records
    nothing: [Transaction.deleteNode] ([transaction/wp_private]) records the
    flip, and the delete loops ([Transaction.deleteRange] /
    [applyDeleteSpans], [transaction/deleteRange]) step by that. *)
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
From New.proof.sync_proof Require Import base mutex rwmutex rwmutex_guard.
From New.proof Require Import tok_set.
From iris.algebra Require Import auth gmap gset.
From iris.algebra.lib Require Import dfrac_agree.
From stdpp Require Import sorting.
Local Open Scope Z_scope.
From New.proof.store Require Import model value heap wp_private GetNode splitNode repair.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Section store_deleteNode.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.

Notation P := go_string.

Local Notation TId := (TypeId P).

Local Notation Op := (TId * @YjsOperation A)%type.

Local Notation Ev := (@Event Op).

Local Notation DocModel := (gmap TId (list (YjsItem A))).

Context {sync_pkg : sync.Assumptions}.

Notation seqUR := (authR (gmapUR loc (gsetUR (YjsItem A)))).

Context {seq_inG : inG Σ seqUR}.

Notation accUR := (authR (gsetUR YjsId)).

Context {acc_inG : inG Σ accUR}.

Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO addressed_pool))}.
(* the observers' tokens and registrations (issue #198 Part II), as [store/heap] *)
Context {observed_inG : ghost_varG Σ (list (YjsItem go_string * bool))}.
Context {observers_inG : inG Σ (authR (gsetUR (gname * go_string)))}.

(* ===== lemmas ============================================================= *)

(** [deleteNode]:
    the pool at [(locs, p)], the node named by its type's address list and
    the run it holds; the post flips that run's bit ([flip_run]) and leaves
    everything else, the address map included, and the result says whether
    the run was live. The Deleted branch is the identity on the nose. *)
Lemma wp_deleteNode (locs : gmap loc (list loc)) (p : pool)
    (parent : loc) (ls : list loc) (tm : type_model) (k : nat) (lc : loc) (r : ItemRun) :
  locs !! parent = Some ls ->
  p !! parent = Some tm ->
  ls !! k = Some lc ->
  tm_runs tm !! k = Some r ->
  run_fits r ->
  {{{ is_pkg_init yjs ∗ own_type_pool (DfracOwn 1) locs p }}}
    @! yjs.deleteNode #lc
  {{{ RET #(negb (run_deleted r)); own_type_pool (DfracOwn 1) locs
        (<[parent := MkTypeModel (<[k := flip_run r]> (tm_runs tm))]> p) }}}.
Proof using Type*.
  move=> Hlp Hpp Hlk Hrk Hrfits.
  destruct tm as [runs]. simpl in *.
  wp_start as "Hpool".
  iDestruct "Hpool" as "(%Hlocswf & Hpool)".
  iDestruct (big_sepM_delete _ _ parent _ Hpp with "Hpool") as "[Hpc Hrest]".
  iDestruct "Hpc" as (ls0) "(%Hls0 & Hyt & %Harrinv)".
  rewrite Hlp in Hls0. injection Hls0 as <-.
  iDestruct "Hyt" as (yt tl) "(Hparent & Hdll & %Hlen)". simpl in Hlen.
  iDestruct (own_dll_update parent yt.(yjs.yType.start') tl null null ls runs k lc r Hlk Hrk with "Hdll")
    as (prev' nxt') "(%Hrun & %Hpc & %Hclen & Hnode & Hback)".
  iDestruct "Hnode" as (itemVal olid orid)
    "(Hval & Hol & Hor & %Hinl & %Hinr & %Hid & %Hcont & %Hpar & %Hprevf & %Hnextf & %Hflags)".
  wp_auto.
  wp_apply (wp_item__Indexable lc (DfracOwn 1) itemVal
              (flags_if_countable itemVal (run_deleted r) Hflags) with "[$Hval]").
  iIntros "Hval".
  rewrite (flags_if_deleted itemVal (run_deleted r) Hflags).
  destruct (run_deleted r) eqn:Hd; simpl negb.
  - (* already tombstoned: nothing happens, and the flip is the identity *)
    wp_auto.
    iAssert (own_item_node lc (DfracOwn 1) (input_of_run r) true parent prev' nxt')
      with "[Hval Hol Hor]" as "Hnode".
    { iExists itemVal, olid, orid. iFrame "Hval Hol Hor".
      iPureIntro. split_and!;
        [exact Hinl | exact Hinr | exact Hid | exact Hcont | exact Hpar
        | exact Hprevf | exact Hnextf | (by rewrite Hflags ?Hd)]. }
    iDestruct ("Hback" $! true with "Hnode") as "Hdll".
    have Hr : MkItemRun (run_items r) true = r.
    { destruct r as [items d]. simpl in Hd. subst d. reflexivity. }
    rewrite Hr (list_insert_id runs k r Hrk).
    iApply "HΦ".
    rewrite /flip_run Hr (list_insert_id runs k r Hrk).
    have Hpid : <[parent := MkTypeModel runs]> p = p by apply insert_id; exact Hpp.
    rewrite Hpid.
    rewrite /own_type_pool.
    iSplitR; first (iPureIntro; exact Hlocswf).
    iApply big_sepM_delete; first exact Hpp.
    iFrame "Hrest".
    iExists ls. iSplitR; first (iPureIntro; exact Hlp).
    iSplitL; last (iPureIntro; exact Harrinv).
    iExists yt, tl. iFrame "Hparent Hdll". iPureIntro. exact Hlen.
  - (* visible: set the bit and shrink the type's [len] by the run length *)
    wp_auto.
    rewrite Hpar. wp_auto.
    wp_apply (wp_item__Len lc (DfracOwn 1) (set_deleted itemVal) with "[$Hval]").
    iIntros "[Hval _]".
    wp_auto. rewrite Hpar. wp_auto.
    have Hflagspin : itemVal.(yjs.item.flags') = (if false then W8 6 else W8 2)
      by rewrite Hflags ?Hd.
    iAssert (own_item_node lc (DfracOwn 1) (input_of_run r) true parent prev' nxt')
      with "[Hval Hol Hor]" as "Hnode".
    { iExists (set_deleted itemVal), olid, orid.
      iEval (rewrite /set_deleted /=).
      iFrame "Hval Hol Hor".
      iPureIntro. split_and!;
        [exact Hinl | exact Hinr | exact Hid | exact Hcont | exact Hpar
        | exact Hprevf | exact Hnextf | (rewrite Hflagspin; vm_compute; reflexivity)]. }
    iDestruct ("Hback" $! true with "Hnode") as "Hdll".
    iEval (change (MkItemRun (run_items r) true) with (flip_run r)) in "Hdll".
    have Hrunlen : length (run_items r) = length (itemVal.(yjs.item.content').(yjs.content.content')).
    { have Hstr : itemVal.(yjs.item.content').(yjs.content.content') = in_content (input_of_run r) := Hcont.
      rewrite Hstr. symmetry. exact Hclen. }
    have Hnv : runs_visible (<[k := flip_run r]> runs) = (runs_visible runs - length (run_items r))%nat
      := runs_visible_flip_run runs k r Hrk Hd.
    have Hnvge : (length (run_items r) <= runs_visible runs)%nat.
    { rewrite /runs_visible -(take_drop_middle runs k r Hrk) fmap_app list_sum_app fmap_cons /=.
      rewrite Hd. lia. }
    iApply "HΦ".
    rewrite /own_type_pool.
    iSplitR.
    { iPureIntro.
      apply (locs_wf_insert_same_len locs p parent (MkTypeModel runs)
               (MkTypeModel (<[k := flip_run r]> runs)) Hpp); last exact Hlocswf.
      simpl. rewrite length_insert //. }
    iEval (rewrite big_sepM_insert_delete).
    iSplitR "Hrest"; last iExact "Hrest".
    iExists ls. iSplitR; first (iPureIntro; exact Hlp).
    iSplitL; last first.
    { iPureIntro. rewrite /tm_arr /= (runs_flatten_flip_run runs k r Hrk). exact Harrinv. }
    iExists (yt <| yjs.yType.len' := w64_word_instance.(word.sub) yt.(yjs.yType.len')
                     (W64 (length (itemVal.(yjs.item.content').(yjs.content.content')))) |>), tl.
    iFrame "Hparent Hdll". iPureIntro.
    simpl. rewrite Hlen Hnv -Hrunlen. word.
Qed.


(** [deleteNode] on the store: the addressed run is tombstoned and every
    other field is untouched (the store re-closed around [wp_deleteNode]);
    what [Transaction.deleteNode] steps by. *)
Lemma wp_deleteNode_store (s : loc) (state : store_state)
    (parent : loc) (ls : list loc) (tm : type_model) (k : nat) (lc : loc) (r : ItemRun) :
  ss_locs state !! parent = Some ls ->
  ss_pool state !! parent = Some tm ->
  ls !! k = Some lc ->
  tm_runs tm !! k = Some r ->
  {{{ is_pkg_init yjs ∗ own_store_state s state }}}
    @! yjs.deleteNode #lc
  {{{ RET #(negb (run_deleted r)); own_store_state s
        (state <| ss_pool := <[parent := MkTypeModel (<[k := flip_run r]> (tm_runs tm))]>
                             (ss_pool state) |>) }}}.
Proof.
  move=> Hls Hp Hlk Hrk.
  iIntros (Φ) "(#Hpkg & Hruns) HΦ".
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
  wp_apply (wp_deleteNode locs p parent ls tm k lc r Hls Hp Hlk Hrk Hrfits with "[$Hpkg $Htypes]").
  iIntros "Htypes".
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
  iSplitL; last (iPureIntro; split_and!; [exact Hrpi' | exact Hreg' | exact Hcontig']).
  rewrite /own_store_fields /=.
  iFrame "Hclient Hclock HdeletedSet Hregistry Htypes Hpending Hpdeletes".
  iExists mref. iFrame "Hitemsf Hitemmap".
Qed.


End store_deleteNode.
