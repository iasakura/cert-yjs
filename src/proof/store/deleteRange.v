(** The wire delete path (issue #133, plan section 5): [store.deleteNode]
    tombstones one integrated node, [store.deleteRange] tombstones a whole
    clock range, splitting at the range boundaries so the deletion covers
    exactly the requested chars, and [store.applyDeleteSpans] retries the
    buffered spans plus a decoded batch, keeping what did not land.

    The specs are stated at run granularity (docs/plan-item-run-split.md
    stage C5): [wp_store__deleteRange_runs] and
    [wp_store__applyDeleteSpans_runs] over [own_store_runs], stepping the
    pool by [pool_after_delete] and recording coverage as
    [ids_tombstoned_runs]. The loops speak indices, addresses and runs;
    the store is opened and re-closed around the node-level cores by the
    local [wp_deleteNode_store_runs] and the store's node borrow
    [own_store_runs_node_acc]. The cell-level
    [wp_store__applyDeleteSpans] is derived from the run-granular proof
    for [wp_store__applyDeleteSpans_store], the [own_store] form the lock
    layer consumes. *)
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

Section store_deleteRange.

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

Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO (gmap loc type_state)))}.

(* ===== lemmas ============================================================= *)

(** [deleteNode] at run granularity:
    the pool at [(locs, p)], the node named by its type's address list and
    the run it holds; the post flips that run's bit ([flip_run]) and leaves
    everything else, the address map included. The Deleted branch is the
    identity on the nose. *)
#[local] Lemma wp_deleteNode_runs (locs : gmap loc (list loc)) (p : pool)
    (parent : loc) (ls : list loc) (tm : type_model) (k : nat) (lc : loc) (r : ItemRun) :
  locs !! parent = Some ls ->
  p !! parent = Some tm ->
  ls !! k = Some lc ->
  tm_runs tm !! k = Some r ->
  {{{ is_pkg_init yjs ∗ own_type_pool_runs (DfracOwn 1) locs p }}}
    @! yjs.deleteNode #lc
  {{{ RET #(); own_type_pool_runs (DfracOwn 1) locs
        (<[parent := MkTypeModel (<[k := flip_run r]> (tm_runs tm)) (tm_arr tm)]> p) }}}.
Proof using Type*.
  move=> Hlp Hpp Hlk Hrk.
  destruct tm as [runs arr]. simpl in *.
  wp_start as "Hpool".
  iDestruct "Hpool" as "(%Hlocswf & Hpool)".
  iDestruct (big_sepM_delete _ _ parent _ Hpp with "Hpool") as "[Hpc Hrest]".
  iDestruct "Hpc" as (ls0) "(%Hls0 & Hyt & %Harrinv)".
  rewrite Hlp in Hls0. injection Hls0 as <-.
  iDestruct "Hyt" as (yt tl) "(Hparent & Hdll & %Hlen & %Harr)". simpl in Hlen, Harr.
  iDestruct (own_dll_runs_update parent yt.(yjs.yType.start') tl null null ls runs k lc r Hlk Hrk with "Hdll")
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
    have Hpid : <[parent := MkTypeModel runs arr]> p = p by apply insert_id; exact Hpp.
    rewrite Hpid.
    rewrite /own_type_pool_runs.
    iSplitR; first (iPureIntro; exact Hlocswf).
    iApply big_sepM_delete; first exact Hpp.
    iFrame "Hrest".
    iExists ls. iSplitR; first (iPureIntro; exact Hlp).
    iSplitL; last (iPureIntro; exact Harrinv).
    iExists yt, tl. iFrame "Hparent Hdll". iPureIntro. split; [exact Hlen | exact Harr].
  - (* visible: set the bit and shrink the type's [len] by the run length *)
    wp_auto.
    rewrite Hpar. wp_auto.
    wp_apply (wp_item__Len lc (DfracOwn 1) (set_deleted itemVal) with "[$Hval]").
    iIntros "Hval".
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
    rewrite /own_type_pool_runs.
    iSplitR.
    { iPureIntro.
      apply (locs_wf_insert_same_len locs p parent (MkTypeModel runs arr)
               (MkTypeModel (<[k := flip_run r]> runs) arr) Hpp); last exact Hlocswf.
      simpl. rewrite length_insert //. }
    iEval (rewrite big_sepM_insert_delete).
    iSplitR "Hrest"; last iExact "Hrest".
    iExists ls. iSplitR; first (iPureIntro; exact Hlp).
    iSplitL; last (iPureIntro; simpl; exact Harrinv).
    iExists (yt <| yjs.yType.len' := w64_word_instance.(word.sub) yt.(yjs.yType.len')
                     (W64 (length (itemVal.(yjs.item.content').(yjs.content.content')))) |>), tl.
    iFrame "Hparent Hdll". iPureIntro. split.
    + simpl. rewrite Hlen Hnv -Hrunlen. word.
    + simpl. rewrite (runs_flatten_flip_run runs k r Hrk). exact Harr.
Qed.


(** [deleteNode] on the store: the addressed run is tombstoned and every
    other field is untouched (the store re-closed around
    [wp_deleteNode_runs]; a stepping stone of the two delete loops). *)
#[local] Lemma wp_deleteNode_store_runs (s : loc) (str : store_state_runs)
    (parent : loc) (ls : list loc) (tm : type_model) (k : nat) (lc : loc) (r : ItemRun) :
  sr_locs str !! parent = Some ls ->
  sr_pool str !! parent = Some tm ->
  ls !! k = Some lc ->
  tm_runs tm !! k = Some r ->
  {{{ is_pkg_init yjs ∗ own_store_runs s str }}}
    @! yjs.deleteNode #lc
  {{{ RET #(); own_store_runs s
        (str <| sr_pool := <[parent := MkTypeModel (<[k := flip_run r]> (tm_runs tm)) (tm_arr tm)]>
                             (sr_pool str) |>) }}}.
Proof.
  move=> Hls Hp Hlk Hrk.
  iIntros (Φ) "(#Hpkg & Hruns) HΦ".
  destruct str as [client0 k0 locs p bind pend pdel]. simpl in *.
  iDestruct "Hruns" as "(Hstruct & %Haligned)".
  iDestruct "Hstruct" as "(Hfields & %Hinvs)".
  have Hpool : pool_invs (types_of_locs_pool locs p) := proj1 Hinvs.
  have Hreg : registry_coh bind (types_of_locs_pool locs p) := proj2 Hinvs.
  iDestruct "Hfields" as "(Hclient & Hclock & HdeletedSet & Hitems & Hregistry & Htypes & Hpending & Hpdeletes)".
  iEval (simpl) in "Htypes".
  iDestruct (own_type_pool_runs_of _ (proj1 (proj2 Hpool)) with "Htypes") as "Htypes".
  have Hprem : ∀ parent0 tm0, p !! parent0 = Some tm0 ->
      ∃ ls0, locs !! parent0 = Some ls0 ∧ length ls0 = length (tm_runs tm0).
  { destruct Haligned as [Hdom Hlens].
    move=> parent0 tm0 Hp0.
    have His : is_Some (locs !! parent0).
    { apply elem_of_dom. rewrite Hdom. apply elem_of_dom. by exists tm0. }
    destruct His as [ls0 Hls0]. exists ls0. split; [done | exact (Hlens parent0 ls0 tm0 Hls0 Hp0)]. }
  rewrite (locs_of_types_of_locs_pool locs p (proj1 Haligned) Hprem)
          (pool_of_types_of_locs_pool locs p Hprem).
  wp_apply (wp_deleteNode_runs locs p parent ls tm k lc r Hls Hp Hlk Hrk with "[$Hpkg $Htypes]").
  iIntros "Htypes".
  set (tm' := MkTypeModel (<[k := flip_run r]> (tm_runs tm)) (tm_arr tm)).
  set (c := MkItemCell lc (run_items r) (run_deleted r) parent).
  set (ts0 := MkTypeState (cells_of_locs_runs parent ls (tm_runs tm)) (tm_arr tm)).
  iDestruct (own_type_pool_runs_to_cells with "Htypes") as "(Htypes & _ & _ & _)".
  (* the materialized pool after the flip is the cell-level flip *)
  have Hmat : types_of_locs_pool locs (<[parent := tm']> p)
            = <[parent := MkTypeState (<[k := flip_cell c]> (ty_cells ts0)) (ty_arr ts0)]>
                (types_of_locs_pool locs p).
  { rewrite (types_of_locs_pool_insert locs p parent ls tm' Hls) /tm' /ts0 /=.
    rewrite (cells_of_locs_runs_flip parent ls (tm_runs tm) k lc r Hlk Hrk) //. }
  have Hts : types_of_locs_pool locs p !! parent = Some ts0.
  { rewrite /types_of_locs_pool map_lookup_imap Hp /= Hls //. }
  have Hck : ty_cells ts0 !! k = Some c.
  { rewrite /ts0 /cells_of_locs_runs /= lookup_zip_with Hlk Hrk //. }
  rewrite Hmat.
  iDestruct (store_items_kp_perm s (types_of_locs_pool locs p) _
               (locs_run_perm_kp _ _ (flip_locs_run_perm _ parent ts0 k c Hts Hck))
               with "Hitems") as "Hitems".
  have Hpool' := pool_invs_flip _ parent ts0 k c Hts Hck Hpool.
  have Hreg' := registry_coh_delete_step _ _ _ (delete_types_update_rel_of_flip _ parent ts0 k c Hts Hck) Hreg.
  iApply "HΦ".
  iSplitL.
  { iEval (rewrite /state_of_runs /= Hmat).
    iApply (own_store_struct_intro _ (MkStoreState client0 k0 _ bind pend pdel) (conj Hpool' Hreg')
              with "Hclient Hclock HdeletedSet Hitems Hregistry Htypes Hpending Hpdeletes"). }
  iPureIntro. simpl.
  apply (locs_aligned_insert_same_len locs p parent tm tm' Hp); last exact Haligned.
  rewrite /tm' /= length_insert //.
Qed.


(** [store.deleteRange]: tombstone the chars [(client, dclock) ..
    (client, dclock + dlen)) that are integrated. Each iteration looks the
    current char up, makes it START a node ([splitAtAndGetRight]), makes the
    range's last char END that node when the range stops inside it
    ([splitAtAndGetLeft]), and tombstones the node whole ([deleteNode]).

    The pool steps by [pool_after_delete] (each type's document survives, no
    type disappears, live and dead chars refine), which is what the caller
    needs to put the store invariant back together. On top of that the loop
    REPORTS its coverage: when it returns [true], every id of the span sits
    in a run that is now tombstoned ([ids_tombstoned_runs]). That is the
    content half, and it is what lets the caller mint an [is_delete_set_lb]
    certificate through [own_delete_set_grow].

    Nothing is claimed about a span whose clock range WRAPS. Spans come off
    the wire, so a peer can send one; the Go loop's [cur < clock + length]
    test then fails immediately and the loop tombstones nothing, which is
    exactly what the guarded postcondition says. *)
(* NB: the two range binders are [dclock] / [dlen], not [clock] / [length]:
   the Go parameters are called [clock] and [length], but those are [YjsId]'s
   clock projection and [list]'s length in Rocq, and shadowing them breaks
   every [clock (item_id ...)] / [length (run_items r)] below. *)
Lemma wp_store__deleteRange_runs (s : loc) (str : store_state_runs)
    (client dclock dlen : w64) :
  {{{ is_pkg_init yjs ∗ own_store_runs s str }}}
    s @! (go.PointerType yjs.store) @! "deleteRange" #client #dclock #dlen
  {{{ (p' : pool) (locs' : gmap loc (list loc)) (covered : bool), RET #covered;
      own_store_runs s (str <| sr_pool := p' |> <| sr_locs := locs' |>) ∗
      ⌜pool_after_delete (sr_pool str) p'⌝ ∗
      ⌜range_no_overflow dclock dlen -> covered = true ->
         ids_tombstoned_runs (range_ids client dclock dlen) (all_runs p')⌝ }}}.
Proof using Type*.
  iIntros (Φ) "(#Hpkg & Hruns) HΦ".
  destruct str as [client0 k0 locs p bind pend pdel]. simpl.
  wp_method_call. wp_call. wp_call. wp_auto.
  iAssert (∃ (cur : w64) (cov : bool) (locs_i : gmap loc (list loc)) (p_i : pool),
    "Hcur" ∷ cur_ptr ↦ cur ∗
    "Hcov" ∷ covered_ptr ↦ cov ∗
    "Hruns" ∷ own_store_runs s (MkStoreStateRuns client0 k0 locs_i p_i bind pend pdel) ∗
    "%Hcurb" ∷ ⌜(uint.Z dclock <= uint.Z cur)%Z⌝ ∗
    "%Hcovj" ∷ ⌜range_no_overflow dclock dlen -> cov = true ->
        ids_tombstoned_runs (range_ids client dclock (w64_word_instance.(word.sub) cur dclock))
                            (all_runs p_i)⌝ ∗
    "%Hfacts" ∷ ⌜pool_after_delete p p_i⌝)%I
    with "[cur covered Hruns]" as "IH".
  { iExists dclock, true, locs, p. iFrame "cur covered Hruns". iPureIntro.
    split_and!; [lia | | exact (pool_after_delete_refl p)].
    move=> _ _ i Hi. exfalso. move: Hi.
    rewrite range_ids_elem /=.
    have -> : uint.nat (w64_word_instance.(word.sub) dclock dclock) = 0%nat by word.
    lia. }
  wp_for "IH".
  wp_if_destruct; last first.
  { iApply ("HΦ" $! p_i locs_i cov). simpl. iFrame "Hruns". iPureIntro.
    split_and!; [exact Hfacts |].
    move=> Hnw Hcov i Hi. apply (Hcovj Hnw Hcov i).
    move: Hi. rewrite !range_ids_elem.
    have -> : uint.nat (w64_word_instance.(word.sub) cur dclock)
            = (uint.nat cur - uint.nat dclock)%nat by word.
    move: n Hnw. rewrite /range_no_overflow /= => Hstop Hnw2. word. }
  wp_apply wp_NewId.
  wp_apply (wp_store__GetNode_runs s _ (MkStoreStateRuns client0 k0 locs_i p_i bind pend pdel)
              with "[$Hpkg $Hruns]").
  iIntros (nl found) "(Hruns & %Hres)". simpl in Hres.
  wp_auto.
  destruct found; last first.
  { wp_auto. wp_for_post.
    iFrame "HΦ s client end".
    iExists (w64_word_instance.(word.add) cur (W64 1)), false, locs_i, p_i.
    iFrame "Hcur Hcov Hruns". iPureIntro.
    split_and!; [word | by move=> _ | exact Hfacts]. }
  destruct Hres as (pw & kw & Hcovw & Hlocw).
  wp_auto.
  wp_apply wp_NewId.
  destruct Hcovw as (tmw & rw & Hpw & Hrw & Hrwcov).
  destruct (locs_i !! pw) as [lsw|] eqn:Hlsw; last done. simpl in Hlocw.
  iDestruct (own_store_runs_run_wf with "Hruns") as %Hwf_i.
  wp_apply (wp_store__splitAtAndGetRight_runs s _ (MkStoreStateRuns client0 k0 locs_i p_i bind pend pdel)
              pw tmw lsw kw rw nl Hpw Hlsw Hrw Hlocw Hrwcov with "[$Hpkg $Hruns]").
  iIntros (rl p1 locs1) "(Hruns & %Hrstep1)".
  iEval (simpl) in "Hruns".
  have Hrwslot : ∃ tm, p_i !! pw = Some tm ∧ tm_runs tm !! kw = Some rw := ex_intro _ tmw (conj Hpw Hrw).
  have Hrwwf : run_wf (run_items rw).
  { apply Hwf_i. apply (elem_of_all_runs p_i rw). exists pw, tmw.
    split; [exact Hpw | exact (list_elem_of_lookup_2 _ _ _ Hrw)]. }
  have Hstep1 : pool_after_split p_i p1 pw kw
    := pool_after_split_of_split_step _ _ _ _ _ _ Hwf_i
         (pool_split_step_of_right _ _ _ _ _ _ _ _ _ Hrwslot Hrwcov Hrstep1).
  destruct (pool_split_right_step_starts_at _ _ _ _ _ _ _ _ _ Hrwslot Hrwwf Hrwcov Hrstep1)
    as (kR & HkRstart & HkRloc).
  destruct HkRstart as (tmR & HpR & rR & HrR & HrRid).
  destruct (locs1 !! pw) as [lsR|] eqn:HlsR; last done. simpl in HkRloc.
  have HrRcl : run_client rR = uint.nat client by rewrite /run_client HrRid.
  have HrRclk : run_clock rR = uint.nat cur by rewrite /run_clock HrRid.
  iDestruct (own_store_runs_run_pool_invs with "Hruns") as %Hrinv1.
  have HrRmem : rR ∈ all_runs p1.
  { apply (elem_of_all_runs_lookup p1 pw tmR rR HpR). left. exact (list_elem_of_lookup_2 _ _ _ HrR). }
  have HrRfits : run_fits rR := proj1 Hrinv1 rR HrRmem.
  iDestruct (own_store_runs_node_acc s (MkStoreStateRuns client0 k0 locs1 p1 bind pend pdel) pw lsR tmR kR rl rR
               HlsR HpR HkRloc HrR with "Hruns") as (ivR) "H".
  iNamed "H".
  (* the parent pin names [pw]; [wp_if_destruct]'s bare [subst] would take it *)
  clear Haccpar.
  wp_auto.
  wp_apply (wp_item__Len rl (DfracOwn 1) ivR with "[$Haccval]").
  iIntros "Haccval".
  iDestruct ("Haccback" with "Haccval") as "Hruns".
  (* kept at the [uint.Z] level on purpose: [wp_if_destruct]'s bare [subst]
     would consume a [clock' = cur] equation and take [cur] with it *)
  have HivRclk : uint.Z ivR.(yjs.item.id').(yjs.id.clock') = uint.Z cur.
  { move: Haccid. rewrite HrRid /toYjsId /=. move=> [_ Hk]. word. }
  have HivRlen : length (ivR.(yjs.item.content').(yjs.content.content')) = length (run_items rR) := Haccle.
  iDestruct (own_store_runs_run_wf with "Hruns") as %Hwf1.
  have HrRwf : run_wf (run_items rR) := Hwf1 rR HrRmem.
  have Hcurlt : (uint.Z cur < uint.Z (w64_word_instance.(word.add) dclock dlen))%Z := l.
  have HrRclkZ : Z.of_nat (run_clock rR) = uint.Z cur by rewrite HrRclk; word.
  have HrRfitsZ : (uint.Z cur + Z.of_nat (length (run_items rR)) < 2^64)%Z.
  { move: HrRfits. rewrite /run_fits HrRclkZ //. }
  have Hnext : uint.Z (w64_word_instance.(word.add) ivR.(yjs.item.id').(yjs.id.clock')
                        (W64 (length ivR.(yjs.item.content').(yjs.content.content'))))
             = (uint.Z cur + Z.of_nat (length (run_items rR)))%Z.
  { rewrite HivRlen. move: HivRclk HrRfitsZ. word. }
  wp_auto.
  wp_if_destruct.
  - (* the range stops inside this node: cut it at the range's last char *)
    wp_apply wp_NewId.
    set (idL := {| yjs.id.clientId' := client;
                   yjs.id.clock' := w64_word_instance.(word.sub)
                     (w64_word_instance.(word.add) dclock dlen) (W64 1) |}).
    have HrRcovL : run_covers rR (toYjsId idL).
    { rewrite /run_covers /toYjsId /= HrRcl HrRclk. split_and!; [done | word | word]. }
    wp_apply (wp_store__splitAtAndGetLeft_runs s idL (MkStoreStateRuns client0 k0 locs1 p1 bind pend pdel)
                pw tmR lsR kR rR rl HpR HlsR HrR HkRloc HrRcovL with "[$Hpkg $Hruns]").
    iIntros (p2 locs2) "(Hruns & %Hlstep2)".
    iEval (simpl) in "Hruns".
    have HrRslot : ∃ tm, p1 !! pw = Some tm ∧ tm_runs tm !! kR = Some rR := ex_intro _ tmR (conj HpR HrR).
    have Hstep2 : pool_after_split p1 p2 pw kR
      := pool_after_split_of_split_step _ _ _ _ _ _ Hwf1
           (pool_split_step_of_left _ _ _ _ _ _ _ _ HrRslot HrRcovL Hlstep2).
    have HkRloc' : (locs1 !! pw) ≫= (λ ls, ls !! kR) = Some rl by rewrite HlsR /= HkRloc.
    destruct (pool_split_left_step_ends_at _ _ _ _ _ _ _ _ _ HrRslot HkRloc' HrRwf HrRcovL Hlstep2)
      as (HkLstart & HkLend & HkLloc).
    destruct HkLstart as (tmL & HpL & rL & HrL & HrLid).
    destruct HkLend as (tmL' & HpL' & rL' & HrL' & HrLcl & HrLend).
    rewrite HpL in HpL'. injection HpL' as <-. rewrite HrL in HrL'. injection HrL' as <-.
    destruct (locs2 !! pw) as [lsL|] eqn:HlsL; last done. simpl in HkLloc.
    iDestruct (own_store_runs_run_wf with "Hruns") as %Hwf2.
    have HrLmem : rL ∈ all_runs p2.
    { apply (elem_of_all_runs_lookup p2 pw tmL rL HpL). left. exact (list_elem_of_lookup_2 _ _ _ HrL). }
    have HrLwf : run_wf (run_items rL) := Hwf2 rL HrLmem.
    wp_auto.
    (* tombstone the truncated node *)
    wp_apply (wp_deleteNode_store_runs s (MkStoreStateRuns client0 k0 locs2 p2 bind pend pdel)
                pw lsL tmL kR rl rL HlsL HpL HkLloc HrL with "[$Hpkg $Hruns]").
    iIntros "Hruns".
    iEval (simpl) in "Hruns".
    set (p3 := <[pw := MkTypeModel (<[kR := flip_run rL]> (tm_runs tmL)) (tm_arr tmL)]> p2).
    wp_auto. wp_for_post.
    iFrame "HΦ s client end".
    iExists (w64_word_instance.(word.add) dclock dlen), cov, locs2, p3.
    iFrame "Hcur Hcov Hruns".
    have Hstep3 : pool_after_delete p_i p3.
    { eapply pool_after_delete_trans; first exact (pool_after_split_delete _ _ _ _ Hstep1).
      eapply pool_after_delete_trans; first exact (pool_after_split_delete _ _ _ _ Hstep2).
      exact (pool_after_delete_flip p2 pw tmL kR rL HpL HrL). }
    have Hdk3 : runs_dead_kept p_i p3 := proj1 (proj2 (proj2 (proj2 Hstep3))).
    have HrLcl' : run_client rL = uint.nat client.
    { rewrite /run_client HrLid HrRid //. }
    have HrLclk : run_clock rL = uint.nat cur.
    { rewrite /run_clock HrLid HrRid //. }
    have HrLendn : (run_clock rL + length (run_items rL))%nat
                 = uint.nat (w64_word_instance.(word.add) dclock dlen).
    { rewrite HrLend /idL /toYjsId /=. word. }
    iPureIntro. split_and!.
    + word.
    + (* the record grows by the truncated node's chars, which reach exactly
         the end of the requested range *)
      move=> Hnw Hcov i Hi.
      move: Hi. rewrite range_ids_elem /=.
      move=> [Hcid [Hlo Hhi]].
      destruct (decide (clock i < uint.nat cur)%nat) as [Hold | Hnew].
      * apply (ids_tombstoned_runs_dead_kept _ _ _ Hdk3 (Hcovj Hnw Hcov)).
        rewrite range_ids_elem /=. split_and!; [exact Hcid | | ].
        -- move: Hlo. rewrite /=. word.
        -- word.
      * exists (flip_run rL). split_and!.
        -- apply (elem_of_all_runs_insert p2 pw tmL _ _ HpL). left. simpl.
           apply list_elem_of_insert. exact (lookup_lt_Some _ _ _ HrL).
        -- done.
        -- rewrite flip_run_items.
           apply (run_covers_char_ids rL i HrLwf).
           rewrite /run_covers HrLendn HrLcl' HrLclk. split_and!; [by rewrite Hcid | lia |].
           move: Hhi Hnw. rewrite /range_no_overflow /=. word.
    + exact (pool_after_delete_trans _ _ _ Hfacts Hstep3).
  - (* the node ends inside the range: tombstone it whole *)
    wp_apply (wp_deleteNode_store_runs s (MkStoreStateRuns client0 k0 locs1 p1 bind pend pdel)
                pw lsR tmR kR rl rR HlsR HpR HkRloc HrR with "[$Hpkg $Hruns]").
    iIntros "Hruns".
    iEval (simpl) in "Hruns".
    set (p3 := <[pw := MkTypeModel (<[kR := flip_run rR]> (tm_runs tmR)) (tm_arr tmR)]> p1).
    wp_auto. wp_for_post.
    iFrame "HΦ s client end".
    iExists (w64_word_instance.(word.add) ivR.(yjs.item.id').(yjs.id.clock')
               (W64 (length ivR.(yjs.item.content').(yjs.content.content')))), cov, locs1, p3.
    iFrame "Hcur Hcov Hruns".
    have Hstep3 : pool_after_delete p_i p3.
    { eapply pool_after_delete_trans; first exact (pool_after_split_delete _ _ _ _ Hstep1).
      exact (pool_after_delete_flip p1 pw tmR kR rR HpR HrR). }
    have Hdk3 : runs_dead_kept p_i p3 := proj1 (proj2 (proj2 (proj2 Hstep3))).
    have Hcurstep : uint.nat (w64_word_instance.(word.add) ivR.(yjs.item.id').(yjs.id.clock')
                       (W64 (length ivR.(yjs.item.content').(yjs.content.content'))))
                  = (uint.nat cur + length (run_items rR))%nat.
    { move: Hnext. word. }
    iPureIntro. split_and!.
    + move: Hnext Hcurb. word.
    + (* the record grows by exactly this node's chars *)
      move=> Hnw Hcov i Hi.
      move: Hi. rewrite range_ids_elem /=.
      move=> [Hcid [Hlo Hhi]].
      destruct (decide (clock i < uint.nat cur)%nat) as [Hold | Hnew].
      * apply (ids_tombstoned_runs_dead_kept _ _ _ Hdk3 (Hcovj Hnw Hcov)).
        rewrite range_ids_elem /=. split_and!; [exact Hcid | | ].
        -- move: Hlo. rewrite /=. word.
        -- word.
      * exists (flip_run rR). split_and!.
        -- apply (elem_of_all_runs_insert p1 pw tmR _ _ HpR). left. simpl.
           apply list_elem_of_insert. exact (lookup_lt_Some _ _ _ HrR).
        -- done.
        -- rewrite flip_run_items.
           apply (run_covers_char_ids rR i HrRwf).
           rewrite /run_covers HrRcl HrRclk. split_and!; [by rewrite Hcid | lia |].
           move: Hhi Hcurstep Hcurb Hnw. rewrite /range_no_overflow /=. word.
    + exact (pool_after_delete_trans _ _ _ Hfacts Hstep3).
Qed.

(** [store.applyDeleteSpans]: apply a batch of decoded spans on top of the
    buffered ones and keep the ones that did not land in full. Safety-shaped
    like [deleteRange]: the pool steps by [pool_after_delete]; which spans
    stay buffered is existential (pinning it needs the per-char coverage the
    delete set records, D3), but every span that landed has its ids in the
    tombstone record [D].

    The buffer's own spans and the batch's are both consumed as VALUES (a
    span is a triple of machine words), so the batch comes back untouched
    and the new buffer is a fresh slice. *)
Lemma wp_store__applyDeleteSpans_runs (s : loc) (str : store_state_runs)
    (sp_sl : slice.t) (dq : dfrac) (spans : list delete_span) :
  {{{ is_pkg_init yjs ∗ own_store_runs s str ∗ own_delete_spans sp_sl dq spans }}}
    s @! (go.PointerType yjs.store) @! "applyDeleteSpans" #sp_sl
  {{{ (p' : pool) (locs' : gmap loc (list loc)) (rest : list delete_span), RET #();
      own_store_runs s (str <| sr_pool := p' |> <| sr_locs := locs' |>
                            <| sr_pending_deletes := rest |>) ∗
      own_delete_spans sp_sl dq spans ∗
      ⌜pool_after_delete (sr_pool str) p'⌝ ∗
      ⌜∃ D : gset YjsId,
         ids_tombstoned_runs D (all_runs p') ∧
         (∀ sp, sp ∈ sr_pending_deletes str ++ spans -> delete_span_no_overflow sp ->
            delete_span_ids sp ⊆ D ∪ delete_batch_ids rest)⌝ }}}.
Proof using Type*.
  iIntros (Φ) "(#Hpkg & Hruns & Hsp) HΦ".
  destruct str as [client0 k0 locs p bind pend pdel]. simpl.
  iDestruct "Hruns" as "(Hstruct & %Haligned)".
  iEval (simpl) in "Hstruct".
  iDestruct "Hstruct" as "(Hfields0 & %Hinvs0)".
  have Hpool0 : pool_invs (types_of_locs_pool locs p) := proj1 Hinvs0.
  have Hreg0 : registry_coh bind (types_of_locs_pool locs p) := proj2 Hinvs0.
  iDestruct "Hfields0" as "(Hclient & Hclock & HdeletedSet & Hitems & Hregistry & Htypes & Hpending & Hpdeletes)".
  iDestruct "Hpdeletes" as (pdel_sl) "(Hpddelf & Hpddel)".
  (* open the pure model: the decoded structs live only inside this proof *)
  iDestruct "Hpddel" as (pdel_vs) "(Hspsl & Hspcap & %Hpdelmodel)".
  iDestruct "Hsp" as (spans_vs) "(Hspsl2 & Hspcap2 & %Hspansmodel)".
  simpl in Hpdelmodel.
  (* the pure lists ARE the denotations of the concrete ones; substituting
     them away keeps the rest of the proof over the structs the loop walks *)
  subst pdel spans.
  wp_method_call. wp_call. wp_call. wp_auto.
  (* ---- loop 1: [all] accumulates the buffer plus the batch ---- *)
  iAssert (∃ (i : w64) (all_sl : slice.t),
    "Hi" ∷ i_ptr ↦ i ∗
    "Hallp" ∷ all_ptr ↦ all_sl ∗
    "Hall" ∷ all_sl ↦* (pdel_vs ++ take (uint.nat i) spans_vs) ∗
    "Hallcap" ∷ own_slice_cap yjs.deleteSpan.t all_sl (DfracOwn 1) ∗
    "Hspsl2" ∷ sp_sl ↦*{dq} spans_vs ∗
    "%Hib" ∷ ⌜(uint.nat i <= length spans_vs)%nat⌝)%I
    with "[i all Hspsl Hspcap Hspsl2]" as "IH".
  { iExists (W64 0), pdel_sl.
    rewrite (_ : uint.nat (W64 0) = 0%nat); last word.
    rewrite take_0 app_nil_r.
    iFrame "i all Hspsl Hspcap Hspsl2". iPureIntro. lia. }
  wp_for "IH".
  iDestruct (own_slice_len with "Hspsl2") as %[Hsplen _].
  wp_if_destruct; last first.
  { (* the batch is copied: [all] is the buffer plus the batch. Loop 2
       applies each span and keeps the ones that did not land. *)
    have Hiend : uint.nat i = length spans_vs by word.
    rewrite Hiend take_ge; last lia.
    wp_apply wp_slice_literal. iSplitR; first done.
    iIntros "%rsl0 [Hrest Hrestcap]". wp_auto.
    iAssert (∃ (j : w64) (rest_sl : slice.t) (rest_vs : list yjs.deleteSpan.t)
               (locs_j : gmap loc (list loc)) (p_j : pool) (Dj : gset YjsId),
      "Hj" ∷ i_ptr ↦ j ∗
      "Hrestp" ∷ rest_ptr ↦ rest_sl ∗
      "Hrest" ∷ rest_sl ↦* rest_vs ∗
      "Hrestcap" ∷ own_slice_cap yjs.deleteSpan.t rest_sl (DfracOwn 1) ∗
      "Hall" ∷ all_sl ↦* (pdel_vs ++ spans_vs) ∗
      "Hruns" ∷ own_store_runs s (MkStoreStateRuns client0 k0 locs_j p_j bind pend []) ∗
      "%Hjb" ∷ ⌜(uint.nat j <= length (pdel_vs ++ spans_vs))%nat⌝ ∗
      "%HdelDj" ∷ ⌜ids_tombstoned_runs Dj (all_runs p_j)⌝ ∗
      "%HspanDj" ∷ ⌜∀ sp, sp ∈ take (uint.nat j) (pdel_vs ++ spans_vs) ->
          delete_span_no_overflow (delete_span_of_val sp) ->
          delete_span_ids (delete_span_of_val sp)
            ⊆ Dj ∪ delete_batch_ids (delete_span_of_val <$> rest_vs)⌝ ∗
      "%Hfactsj" ∷ ⌜pool_after_delete p p_j⌝)%I
      with "[i rest Hrest Hrestcap Hall Hclient Hclock HdeletedSet Hitems Hregistry Htypes Hpending Hpddelf]" as "IH".
    { iExists (W64 0), _, [], locs, p, (∅ : gset YjsId).
      iFrame "i rest Hrest Hrestcap Hall".
      iSplitL.
      { iSplitL; last (iPureIntro; exact Haligned).
        iEval (simpl).
        iApply (own_store_struct_intro _ (MkStoreState client0 k0 _ bind pend []) (conj Hpool0 Hreg0)
                  with "Hclient Hclock HdeletedSet Hitems Hregistry Htypes Hpending [Hpddelf]").
        iExists slice.nil. iFrame "Hpddelf". iExists [].
        iSplitL; [iApply own_slice_nil | iSplitL; [iApply own_slice_cap_nil | done]]. }
      iPureIntro.
      split_and!; [word | | | exact (pool_after_delete_refl p)].
      - move=> i0 Hi0. exfalso. set_solver.
      - move=> sp0 Hsp0. exfalso. move: Hsp0.
        rewrite (_ : uint.nat (W64 0) = 0%nat); last word.
        rewrite take_0. apply elem_of_nil. }
    wp_for "IH".
    iDestruct (own_slice_len with "Hall") as %[Halllen _].
    iDestruct "Hruns" as "(Hstruct & %Halignedj)".
    iEval (simpl) in "Hstruct".
    iDestruct "Hstruct" as "(Hfieldsj & %Hinvsj)".
    have Hpoolj : pool_invs (types_of_locs_pool locs_j p_j) := proj1 Hinvsj.
    have Hregj : registry_coh bind (types_of_locs_pool locs_j p_j) := proj2 Hinvsj.
    iDestruct "Hfieldsj" as "(Hclient & Hclock & HdeletedSet & Hitems & Hregistry & Htypes & Hpending & Hpdeletes)".
    iDestruct "Hpdeletes" as (pd_sl) "(Hpddelf & Hpdnil)".
    wp_if_destruct; last first.
    { (* every span has been retried: install the leftover as the new buffer,
         and hand the whole thing back over the PURE model *)
      iApply ("HΦ" $! p_j locs_j (delete_span_of_val <$> rest_vs)).
      iAssert (own_pending_deletes_field (s .[(yjs.store.t), "pendingDeletes"]) (delete_span_of_val <$> rest_vs))%I
        with "[Hpddelf Hrest Hrestcap]" as "Hpdeletes".
      { iExists rest_sl. iFrame "Hpddelf". iExists rest_vs. by iFrame "Hrest Hrestcap". }
      iSplitL "Hclient Hclock HdeletedSet Hitems Hregistry Htypes Hpending Hpdeletes".
      { simpl.
        iSplitL; last (iPureIntro; exact Halignedj).
        iEval (simpl).
        iApply (own_store_struct_intro _ (MkStoreState client0 k0 _ bind pend (delete_span_of_val <$> rest_vs))
                  (conj Hpoolj Hregj)
                  with "Hclient Hclock HdeletedSet Hitems Hregistry Htypes Hpending Hpdeletes"). }
      iSplitL "Hspsl2 Hspcap2"; first (iExists spans_vs; by iFrame "Hspsl2 Hspcap2").
      iPureIntro. split_and!; [exact Hfactsj |].
      exists Dj. split; first exact HdelDj.
      (* transport the record from the decoded structs to the spans they
         denote *)
      move=> sp Hsp Hnw.
      rewrite -fmap_app in Hsp.
      apply list_elem_of_fmap in Hsp as (v & -> & Hv).
      apply (HspanDj v); [by rewrite take_ge; last word | exact Hnw]. }
    (* retry one span *)
    destruct ((pdel_vs ++ spans_vs) !! uint.nat j) as [sp|] eqn:Hsp; last first.
    { exfalso. apply lookup_ge_None in Hsp. word. }
    iDestruct (own_slice_elem_acc (sint.Z j) sp all_sl (DfracOwn 1) _ with "Hall")
      as "[Hel Hgive]".
    { word. }
    { replace (Z.to_nat (sint.Z j)) with (uint.nat j) by word. exact Hsp. }
    rewrite decide_True; last word.
    wp_auto.
    iDestruct ("Hgive" with "Hel") as "Hall".
    rewrite list_insert_id; last first.
    { replace (Z.to_nat (sint.Z j)) with (uint.nat j) by word. exact Hsp. }
    wp_apply (wp_store__deleteRange_runs s (MkStoreStateRuns client0 k0 locs_j p_j bind pend []) _ _ _
                with "[Hclient Hclock HdeletedSet Hitems Hregistry Htypes Hpending Hpddelf Hpdnil]").
    { iFrame "#".
      iSplitL; last (iPureIntro; exact Halignedj).
      iEval (simpl).
      iApply (own_store_struct_intro _ (MkStoreState client0 k0 _ bind pend []) (conj Hpoolj Hregj)
                with "Hclient Hclock HdeletedSet Hitems Hregistry Htypes Hpending [Hpddelf Hpdnil]").
      iExists pd_sl. iFrame "Hpddelf Hpdnil". }
    iIntros (p_j' locs_j' cov) "(Hruns & %Hfactsj' & %Hcovj')".
    iEval (simpl) in "Hruns".
    have Hfactsj'' : pool_after_delete p p_j'
      := pool_after_delete_trans _ _ _ Hfactsj Hfactsj'.
    (* the tombstone record of everything applied so far moves to the new pool *)
    have Hdkj' : runs_dead_kept p_j p_j' := proj1 (proj2 (proj2 (proj2 Hfactsj'))).
    have Hmove : ∀ D : gset YjsId,
        ids_tombstoned_runs D (all_runs p_j) -> ids_tombstoned_runs D (all_runs p_j')
      := λ D, ids_tombstoned_runs_dead_kept D _ _ Hdkj'.
    have Htakestep : take (uint.nat (w64_word_instance.(word.add) j (W64 1)))
                          (pdel_vs ++ spans_vs)
                   = take (uint.nat j) (pdel_vs ++ spans_vs) ++ [sp].
    { rewrite (_ : uint.nat (w64_word_instance.(word.add) j (W64 1))
                 = S (uint.nat j)); last word.
      apply (take_S_r _ _ sp). exact Hsp. }
    destruct cov.
    - (* the span landed in full: drop it, and record its ids *)
      wp_auto. wp_for_post.
      iFrame "HΦ s Hspsl2 Hspcap2 Hallp Hallcap".
      iExists (w64_word_instance.(word.add) j (W64 1)), rest_sl, rest_vs, locs_j', p_j',
        (Dj ∪ (if decide (delete_span_no_overflow (delete_span_of_val sp)) then delete_span_ids (delete_span_of_val sp) else ∅)).
      iFrame "Hj Hrestp Hrest Hrestcap Hall Hruns".
      iPureIntro. split_and!; [word | | | exact Hfactsj''].
      + move=> i0 /elem_of_union [Hi0 | Hi0]; first exact (Hmove Dj HdelDj i0 Hi0).
        destruct (decide (delete_span_no_overflow (delete_span_of_val sp))) as [Hnw | _]; last set_solver.
        exact (Hcovj' Hnw eq_refl i0 Hi0).
      + move=> sp' Hsp' Hnw'.
        rewrite Htakestep in Hsp'. apply elem_of_app in Hsp' as [Hsp' | Hsp'].
        * have := HspanDj sp' Hsp' Hnw'. set_solver.
        * apply list_elem_of_singleton in Hsp' as ->.
          rewrite decide_True //. set_solver.
    - (* not covered yet: keep it buffered *)
      wp_auto.
      wp_apply wp_slice_literal. iSplitR; first done.
      iIntros "%ssl [Hssl _]". wp_auto.
      wp_apply (wp_slice_append with "[$Hrest $Hrestcap $Hssl]").
      iIntros (rest_sl') "(Hrest & Hrestcap & _)".
      wp_auto. wp_for_post.
      iFrame "HΦ s Hspsl2 Hspcap2 Hallp Hallcap".
      iExists (w64_word_instance.(word.add) j (W64 1)), rest_sl', (rest_vs ++ [sp]), locs_j', p_j',
        Dj.
      iFrame "Hj Hrestp Hrest Hrestcap Hall Hruns".
      iPureIntro. split_and!; [word | exact (Hmove Dj HdelDj) | | exact Hfactsj''].
      have Hgrow : delete_batch_ids (delete_span_of_val <$> rest_vs)
                 ⊆ delete_batch_ids (delete_span_of_val <$> (rest_vs ++ [sp])).
      { apply delete_batch_ids_mono => x Hx. rewrite fmap_app.
        apply elem_of_app. by left. }
      move=> sp' Hsp' Hnw'.
      rewrite Htakestep in Hsp'. apply elem_of_app in Hsp' as [Hsp' | Hsp'].
      + have := HspanDj sp' Hsp' Hnw'. set_solver.
      + (* the span just buffered: its ids are in the new leftover *)
        apply list_elem_of_singleton in Hsp' as ->.
        have Hin : delete_span_of_val sp ∈ delete_span_of_val <$> (rest_vs ++ [sp]).
        { apply list_elem_of_fmap. exists sp. split; first done.
          apply elem_of_app. right. apply list_elem_of_here. }
        have := delete_span_ids_subseteq_batch _ _ Hin. set_solver. }
  (* copy one span into [all] *)
  destruct (spans_vs !! uint.nat i) as [sp|] eqn:Hsp; last first.
  { exfalso. apply lookup_ge_None in Hsp. word. }
  iDestruct (own_slice_elem_acc (sint.Z i) sp sp_sl dq _ with "Hspsl2") as "[Hel Hgive]".
  { word. }
  { replace (Z.to_nat (sint.Z i)) with (uint.nat i) by word. exact Hsp. }
  rewrite decide_True; last word.
  wp_auto.
  iDestruct ("Hgive" with "Hel") as "Hspsl2".
  rewrite list_insert_id; last first.
  { replace (Z.to_nat (sint.Z i)) with (uint.nat i) by word. exact Hsp. }
  wp_apply wp_slice_literal. iSplitR; first done.
  iIntros "%sl0 [Hsl0 _]". wp_auto.
  wp_apply (wp_slice_append with "[$Hall $Hallcap $Hsl0]").
  iIntros (all_sl') "(Hall & Hallcap & _)".
  wp_auto. wp_for_post.
  iFrame "HΦ s spans Hclient Hclock HdeletedSet Hitems Hregistry Htypes Hpending Hpddelf Hspcap2".
  iExists (w64_word_instance.(word.add) i (W64 1)), all_sl'.
  iFrame "Hi Hallp Hallcap Hspsl2".
  rewrite (_ : uint.nat (w64_word_instance.(word.add) i (W64 1))
             = S (uint.nat i)); last word.
  rewrite (take_S_r spans_vs (uint.nat i) sp Hsp) app_assoc.
  iFrame "Hall". iPureIntro. word.
Qed.

(** [store.applyDeleteSpans] at the cells: the shape [own_store] still
    speaks ([wp_store__applyDeleteSpans_store]). Derived from the
    run-granular proof through [state_runs_of] / [state_of_runs]. *)
Lemma wp_store__applyDeleteSpans (s : loc) (st : store_state)
    (sp_sl : slice.t) (dq : dfrac) (spans : list delete_span) :
  {{{ is_pkg_init yjs ∗ own_store_struct s st ∗ own_delete_spans sp_sl dq spans }}}
    s @! (go.PointerType yjs.store) @! "applyDeleteSpans" #sp_sl
  {{{ (types' : gmap loc type_state) (rest : list delete_span), RET #();
      own_store_struct s (st <| ss_types := types' |> <| ss_pending_deletes := rest |>) ∗
      own_delete_spans sp_sl dq spans ∗
      ⌜delete_types_update_rel (ss_types st) types'⌝ ∗
      ⌜∃ D : gset YjsId,
         ids_tombstoned D (all_cells types') ∧
         (∀ sp, sp ∈ ss_pending_deletes st ++ spans -> delete_span_no_overflow sp ->
            delete_span_ids sp ⊆ D ∪ delete_batch_ids rest)⌝ }}}.
Proof using Type*.
  iIntros (Φ) "(#Hpkg & Hcells & Hsp) HΦ".
  destruct st as [client0 k0 types bind pend pdel]. simpl.
  iDestruct "Hcells" as "(Hfields0 & %Hinvs0)".
  iDestruct "Hfields0" as "(Hclient & Hclock & HdeletedSet & Hitems & Hregistry & Htypes & Hpending & Hpdeletes)".
  iDestruct (own_type_pool_id_bounds with "Htypes") as %Hbndb.
  iDestruct (own_store_struct_intro _ (MkStoreState client0 k0 types bind pend pdel) Hinvs0
               with "Hclient Hclock HdeletedSet Hitems Hregistry Htypes Hpending Hpdeletes") as "Hcells".
  iAssert (own_store_runs s (state_runs_of (MkStoreState client0 k0 types bind pend pdel)))
    with "[Hcells]" as "Hruns".
  { rewrite own_store_runs_as_state. iExists _. iFrame "Hcells". done. }
  wp_apply (wp_store__applyDeleteSpans_runs s _ sp_sl dq spans with "[$Hpkg $Hruns $Hsp]").
  iIntros (p' locs' rest) "(Hruns & Hsp & %Hstep & %Hcov)".
  iEval (simpl) in "Hruns".
  iDestruct "Hruns" as "(Hstruct & %Haligned)".
  iEval (simpl) in "Hstruct".
  iDestruct "Hstruct" as "(Hfields1 & %Hinvs1)".
  iDestruct "Hfields1" as "(Hclient & Hclock & HdeletedSet & Hitems & Hregistry & Htypes & Hpending & Hpdeletes)".
  iDestruct (own_type_pool_id_bounds with "Htypes") as %Hbnda.
  iDestruct (own_store_struct_intro _ (MkStoreState client0 k0 (types_of_locs_pool locs' p') bind pend rest) Hinvs1
               with "Hclient Hclock HdeletedSet Hitems Hregistry Htypes Hpending Hpdeletes") as "Hcells".
  iApply ("HΦ" $! (types_of_locs_pool locs' p') rest). iFrame "Hcells Hsp".
  have Hprem := locs_aligned_lens _ _ Haligned.
  have Hpeq : pool_of (types_of_locs_pool locs' p') = p' := pool_of_types_of_locs_pool _ _ Hprem.
  iPureIntro. simpl in Hstep. split.
  - apply (pool_after_delete_of_types types (types_of_locs_pool locs' p')
             (λ c Hc, proj2 (Hbndb c Hc)) (λ c Hc, proj1 (Hbndb c Hc))
             (λ c Hc, proj2 (Hbnda c Hc)) (λ c Hc, proj1 (Hbnda c Hc))).
    rewrite Hpeq. exact Hstep.
  - destruct Hcov as (D & Htomb & Hspans). exists D. split; [| exact Hspans].
    apply ids_tombstoned_of_runs. rewrite -all_runs_pool_of Hpeq. exact Htomb.
Qed.

(** The public form of the wire delete step: [own_store] in, [own_store] out
    at the SAME model, history and pending buffer. Deletes are model no-ops in
    the insert-only document model (they only flip tombstone bits and split
    runs), which is exactly why the whole store predicate is preserved: the
    per-type item lists [ty_arr] do not move, so the registry coherence, the
    item-set authority and the counter clause all transfer verbatim, and the
    pool invariants come back from the loop.

    The inner loop's coverage record ([Hdels] below) is DROPPED here rather
    than turned into an [is_delete_set_lb] certificate, deliberately. At the inner
    level the record is worth something because the leftover buffer is a
    return value, so "this span is not in the leftover" pins which spans
    landed. [own_store] hides that buffer, so the same statement out here
    would be "there is a set, and the spans that landed are inside it" with
    nothing pinning which landed: a receipt the empty set satisfies, the same
    vacuity that made the first no-loss attempt worthless (PR #99).

    Making it enforceable wants the delete-side analogue of [is_accepted]: a
    per-span receipt the store invariant ties to covered-or-buffered, so a
    holder learns its span is in the delete set or still pending. That is its
    own milestone, not a line of plumbing. *)
Lemma wp_store__applyDeleteSpans_store (s_loc : loc) (γs : store_names)
    (γh : history_names) (c : ClientId) (h : list Ev) (m : DocModel)
    (pend : list (TId * IntegrateInput (A := A)))
    (sp_sl : slice.t) (dq : dfrac) (spans : list delete_span) :
  {{{ is_pkg_init yjs ∗ own_store s_loc γs γh c h m pend ∗
      own_delete_spans sp_sl dq spans }}}
    s_loc @! (go.PointerType yjs.store) @! "applyDeleteSpans" #sp_sl
  {{{ RET #(); own_store s_loc γs γh c h m pend ∗ own_delete_spans sp_sl dq spans }}}.
Proof using Type*.
  iIntros (Φ) "(#Hpkg & Hstore & Hsp) HΦ".
  iNamed "Hstore".
  have [Hmtypes Hmdom] := Hregmodel.
  wp_apply (wp_store__applyDeleteSpans s_loc (MkStoreState client k types bind pend pdel) sp_sl dq spans
              with "[$Hcells $Hsp]").
  iIntros (types' rest) "(Hcells & Hsp & %Hfacts & %_Hdels)".
  iEval (simpl) in "Hcells". simpl in Hfacts.
  destruct Hfacts as (Harr & Hdom & Hlr & _ & Hcoord).
  (* the tombstone-set invariant follows the delete: both surgeries the loop
     performs (a split and a flip) only refine the live cells *)
  iDestruct (own_delete_set_refine γs m types types' Hlr with "Hdelete_set") as "Hdelete_set".
  (* equal domains and equal model lists, so the item-set authority is
     literally the same map *)
  have Hdomeq : ∀ q, is_Some (types !! q) <-> is_Some (types' !! q).
  { move=> q. split; first exact (Hdom q).
    move=> [ts' Hts']. destruct (Harr q ts' Hts') as (ts & Hts & _). by exists ts. }
  have Hfmapeq : ((λ ts, (list_to_set (ty_arr ts) : gset (YjsItem A))) <$> types')
               = ((λ ts, (list_to_set (ty_arr ts) : gset (YjsItem A))) <$> types).
  { apply map_eq => q. rewrite !lookup_fmap.
    destruct (types' !! q) as [ts'|] eqn:Hts'.
    - destruct (Harr q ts' Hts') as (ts & Hts & Heq). rewrite Hts /= Heq //.
    - destruct (types !! q) as [ts|] eqn:Hts; last done.
      exfalso. destruct (Hdom q (mk_is_Some _ _ Hts)) as [ts0 Hts0].
      rewrite Hts0 in Hts'. done. }
  iEval (rewrite -Hfmapeq) in "Hseq".
  (* the registry still describes the same documents *)
  have Hregmodel' : registry_models m bind types'.
  { rewrite /registry_models. split.
    - move=> name p ts' Hb Hts'.
      destruct (Harr p ts' Hts') as (ts & Hts & Heq).
      rewrite Heq. exact (Hmtypes name p ts Hb Hts).
    - exact Hmdom. }
  have Hctr' : ∀ parent ts' x, types' !! parent = Some ts' -> x ∈ ty_arr ts' ->
      clientId (item_id x) = c -> (clock (item_id x) < uint.nat k)%nat.
  { move=> parent ts' x Hts' Hx.
    destruct (Harr parent ts' Hts') as (ts & Hts & Heq).
    rewrite Heq in Hx. exact (Hctr parent ts x Hts Hx). }
  iApply "HΦ". iFrame "Hsp".
  iExists client, k, rest, types', bind, acc.
  iFrame "Hcells Hseq HtypesAuth Hhist Hacc Hdelete_set".
  iFrame "Hclientpin Hpendcert Hbinds".
  iPureIntro. split_and!;
    [exact Hclientc | exact Hpendroot | exact Hpendbnd | exact Hregmodel' | exact Hhcoh
    | exact Hctr' | exact Hacccoh].
Qed.

End store_deleteRange.
