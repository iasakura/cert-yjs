(** The top of the [store] update path: the [applyUpdate] stack, from the
    [ValidReplay] refinement [wp_store__applyUpdate] through the wire-drain
    subset / replay lemmas and the certificate machinery up to the public
    [own_store]-level spec [wp_store__applyUpdate] (delivered content
    comes back as [is_root_lb] fragments).

    The layers it stands on are [store/GetNode] (node lookup, input expansion),
    [store/splitNode] and [store/repair] (registry, repair, the [store_inv ⊣⊢
    own_store] bridge); downstream files see everything through the
    [store/store] facade. Same [Section] boilerplate; [Type*] footprints. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core.
From New.proof Require Import algebra.
From New.proof Require Import prelude.
From New.proof.id Require Import id.
From New.proof.item Require Import item.
From New.proof.ytype Require Import ytype.
From New.proof.item Require Import run_theory model value heap.
From New.proof Require Import history.
From New.proof.store Require Import model value heap Integrate.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
From iris.algebra Require Import auth gmap gset.
From stdpp Require Import sorting.

(* iris.algebra / stdpp.sorting push [nat_scope], retuning the default [<] / [≤].
   The verified WP proofs write [Z] comparisons (e.g. [sint.Z i < …]) unannotated
   and annotate [nat] ones with [%nat], so restore [Z_scope] as the default. *)
Local Open Scope Z_scope.
From New.proof.store Require Import GetNode splitNode repair.
Section store_update.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.
Notation P := go_string.
Local Notation TId := (TypeId P).
Local Notation Op := (TId * @YjsOperation A)%type.
Local Notation Ev := (@Event Op).
Local Notation DocModel := (gmap TId (list (YjsItem A))).

(* the grow-only item-set RA (the certificate proofs grow the [sn_seq]
   authority and mint [is_type_lb] fragments) *)
Context {seq_inG : inG Σ (authR (gmapUR loc (gsetUR (YjsItem A))))}.
Context {acc_inG : inG Σ (authR (gsetUR YjsId))}.
(* The store's reader-count accounting ties the readers' share to the [types]
   map via a [dfrac_agree]; [store/heap] declares it up front, so the specs
   reached from here carry it too. *)
Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO addressed_pool))}.

(* [pending_item_rooted] / [is_pending_rooted] are pure [Prop]s (issue #54), so
   [store_inv_excl] / [own_store] carry them as [⌜..⌝] and no Persistent /
   Timeless instances are needed here. *)


(** [store.applyUpdate] (issue #40), the internal total loop: the pending
    buffer plus the incoming batch drain to the structural-dependency
    fixpoint. The pure [wire_drain] names the applied list, the leftover pending
    and the final model; [ValidReplay applied] carries the per-struct validity
    facts (the certificate layer produces it via [history_deliver_pending]); and
    [pending_ready_total] excludes the ready-but-stuck branch, so the Go loop
    (which integrates whenever the arrival gate passes) stays aligned with the
    model scan. Origin-less pending structs must target registered roots (the
    issue #49 pre-bound-roots restriction); origin-carrying structs derive
    their binding from the origin's arrival at integration time. *)
(** [doc_model_has] is monotone under a doc model that only grows per type. *)
Lemma docm_has_mono (m m' : DocModel) (i : YjsId) :
  (∀ (t : TId) x, x ∈ doc_model_get m t -> x ∈ doc_model_get m' t) ->
  doc_model_has m i = true -> doc_model_has m' i = true.
Proof.
  move=> Hmono Hh. apply docm_has_spec in Hh. apply docm_has_spec.
  destruct Hh as (t & x & Hx & Hid). exists t, x. split; [exact (Hmono t x Hx) | exact Hid].
Qed.

(** [integrate_all] only splices: it preserves membership of its base list. *)
Lemma integrate_all_preserves_mem (ops : list (IntegrateInput (A := A)))
    (arr arr' : list (YjsItem A)) :
  integrate_all ops arr = Some arr' -> ∀ x, x ∈ arr -> x ∈ arr'.
Proof.
  elim: ops arr => [| op ops IH] arr /=.
  - move=> [= <-] x Hx //.
  - move=> Hbind x Hx.
    destruct (integrate op arr) as [arr0 |] eqn:Hint; simpl in Hbind; last done.
    exact (IH arr0 Hbind x (integrate_preserves_mem op arr arr0 Hint x Hx)).
Qed.

(** [wire_integrate] preserves membership of the target type's item list. *)
Lemma wire_integrate_preserves_mem (m : DocModel)
    (typedInput : TId * IntegrateInput (A := A)) (arr' : list (YjsItem A)) :
  wire_integrate m typedInput = Some arr' ->
  ∀ x, x ∈ doc_model_get m typedInput.1 -> x ∈ arr'.
Proof. rewrite /wire_integrate. apply integrate_all_preserves_mem. Qed.

(** A wire replay only grows the doc model, per type. *)
Lemma WireReplay_mem (m m' : DocModel) (applied : list (TId * IntegrateInput (A := A))) :
  WireReplay m applied m' -> ∀ (t : TId) x, x ∈ doc_model_get m t -> x ∈ doc_model_get m' t.
Proof.
  elim => [m0 | m0 typedInput arr' rest0 m0' _ _ Hint _ IH] t x Hx; first exact Hx.
  apply IH.
  destruct (decide (t = typedInput.1)) as [-> | Hne].
  - rewrite docm_get_insert_eq. exact (wire_integrate_preserves_mem m0 typedInput arr' Hint x Hx).
  - rewrite (docm_get_insert_ne m0 typedInput.1 t arr' Hne) //.
Qed.

(** [store.applyUpdate] over the unlocked store fields: the drain loop's
    contract stated on the raw registry / run pool / pending buffer, at run
    granularity ([own_store_runs]). The registry follows the model
    ([pool_registry_models]) and the live chars refine up to the chars this
    apply integrated ([runs_apply_live_refine]). Local: the stepping stone of
    [wp_store__applyUpdate] below, which is the spec. *)
#[local] Lemma wp_store__applyUpdate_unlocked (s : loc) (sl : slice.t) (dq : dfrac)
    (inputs pend0 applied rest : list (TId * IntegrateInput (A := A)))
    (m m' : DocModel) (str : store_state_runs) :
  sr_pending str = pend0 ->
  wire_drain m (pend0 ++ inputs) = (applied, rest, m') ->
  ValidReplay (expand_inputs applied) m m' ->
  wire_ready_total m (pend0 ++ inputs) applied ->
  (∀ typedInput : TId * IntegrateInput (A := A), typedInput ∈ applied -> typedInput ∈ pend0 ++ inputs) ->
  (∀ typedInput : TId * IntegrateInput (A := A), typedInput ∈ pend0 ++ inputs ->
     (1 <= length (in_content typedInput.2))%nat) ->
  pool_registry_models m (sr_bind str) (sr_pool str) ->
  (∀ typedInput : TId * IntegrateInput (A := A), typedInput ∈ pend0 ++ inputs ->
     (Z.of_nat (clock (in_id typedInput.2)) + Z.of_nat (length (in_content typedInput.2)) < 2^64)%Z) ->
  {{{ is_pkg_init yjs ∗ own_update_structs sl dq inputs ∗ own_store_runs s str }}}
    s @! (go.PointerType yjs.store) @! "applyUpdate" #sl
  {{{ (p' : pool) (locs' : gmap loc (list loc)) (bind' : gmap P loc), RET #();
      own_update_structs sl dq inputs ∗
      own_store_runs s (str <| sr_pool := p' |> <| sr_locs := locs' |>
                            <| sr_bind := bind' |> <| sr_pending := rest |>) ∗
      ⌜sr_bind str ⊆ bind'⌝ ∗
      ⌜pool_registry_models m' bind' p'⌝ ∗
      ⌜runs_apply_live_refine m (all_runs (sr_pool str)) (all_runs p')⌝ }}}.
Proof using Type*.
  move=> Hpend0 Hdrain Hvr Hrtot Happliedsub Hnonempty [Hmtypes Hmdom] Hkb1.
  destruct str as [client0 k0 locs p bind pend1 pdel]. simpl in *. subst pend1.
  iIntros (Φ) "(#Hpkg & Hupd & Hruns) HΦ".
  (* the INITIAL pool's run structure, read while [Hruns] is over [p]
     (pure, non-consuming): needed in the ready branch to bound an original
     run's clock range below a fresh batch item via [expand_inputs_arr_fresh]. *)
  iDestruct (own_store_runs_arr with "Hruns") as %Harr_init.
  iDestruct (own_store_runs_run_wf with "Hruns") as %Hrunwf_init.
  iDestruct "Hruns" as "(Hfields0 & %Hinvs0)".
  iEval (simpl) in "Hfields0".
  have Hrpi0 : run_pool_invs p := proj1 Hinvs0.
  have Hpreg0 : pool_registry_coh bind p := proj2 Hinvs0.
  have [Hbindtypes [Hbindinj Htypesbound]] := Hpreg0.
  iDestruct "Hfields0" as "(Hclient & Hclock & HdeletedSet & Hitems & Hregistry & Htypes & Hpending & Hpdeletes)".
  iDestruct "Hpending" as (pend_sl) "(Hpendf & Hpend)".
  iDestruct "Hupd" as (uivs_in) "(Hslin & Hcapin & #Hitemsin)".
  iDestruct (big_sepL2_length with "Hitemsin") as %Hlenin.
  iDestruct "Hpend" as (uivs_pd) "(Hslpd & Hcappd & #Hitemspd)".
  iDestruct (big_sepL2_length with "Hitemspd") as %Hlenpd.
  wp_method_call. wp_call. wp_call. wp_auto.
  (* ----- phase A: pending := pending ++ structs ----- *)
  iDestruct (own_slice_len with "Hslin") as %[Hinlen Hinlen0].
  iAssert (∃ (j : nat) (pslA : slice.t) (uivsA : list yjs.updateItem.t),
      "Hi" ∷ i_ptr ↦ W64 j ∗
      "Hpendingp" ∷ pending_ptr ↦ pslA ∗
      "HslA" ∷ pslA ↦* uivsA ∗
      "HcapA" ∷ own_slice_cap yjs.updateItem.t pslA (DfracOwn 1) ∗
      "#HitemsA" ∷ ([∗ list] updateItemVal;typedInput ∈ uivsA;(pend0 ++ take j inputs),
          is_update_item updateItemVal typedInput) ∗
      "Hslin" ∷ sl ↦*{dq} uivs_in ∗
      "%HjA" ∷ ⌜(j <= length uivs_in)%nat⌝)%I
    with "[i pending Hslpd Hcappd Hslin]" as "IH".
  { iExists 0%nat, pend_sl, uivs_pd. iFrame "i pending Hslpd Hcappd Hslin".
    rewrite take_0 app_nil_r. iFrame "Hitemspd".
    iPureIntro. lia. }
  wp_for "IH".
  case_bool_decide as Hcond.
  - (* append structs[j] *)
    have Hjlt : (j < length uivs_in)%nat.
    { move: Hcond. rewrite Hinlen. word. }
    destruct (uivs_in !! j) as [updateItemVal|] eqn:Huiv;
      last by (apply lookup_ge_None in Huiv; lia).
    have [typedInput Hti] : is_Some (inputs !! j).
    { apply lookup_lt_is_Some_2. rewrite -Hlenin. exact Hjlt. }
    iDestruct (big_sepL2_lookup _ _ _ j with "Hitemsin") as "#Hui";
      [exact Huiv | exact Hti |].
    wp_auto.
    rewrite decide_True; last by word.
    iDestruct (own_slice_elem_acc (sint.Z (W64 j)) updateItemVal sl dq uivs_in with "Hslin")
      as "[Hel Hgive]".
    { word. }
    { replace (Z.to_nat (sint.Z (W64 j))) with j by word. exact Huiv. }
    wp_auto.
    iDestruct ("Hgive" $! updateItemVal with "Hel") as "Hslin".
    have Hinsid : (<[sint.nat (W64 j) := updateItemVal]> uivs_in) = uivs_in.
    { apply list_insert_id. replace (sint.nat (W64 j)) with j by word. exact Huiv. }
    iEval (rewrite Hinsid) in "Hslin".
    wp_apply wp_slice_literal. iSplitR; first done.
    iIntros "%sing [Hsing _]". wp_auto.
    wp_apply (wp_slice_append with "[$HslA $HcapA $Hsing]").
    iIntros (pslA') "(HslA' & HcapA' & _)". wp_auto.
    wp_for_post.
    iFrame "Hcapin Hpendf Hclient Hclock HdeletedSet Hpdeletes Hitems Hregistry Htypes HΦ s structs".
    iExists (S j), pslA', (uivsA ++ [updateItemVal]).
    replace (word.add (W64 j) (W64 1)) with (W64 (S j)) by word.
    have H00 : sint.nat (W64 0) = 0%nat by word.
    iEval (rewrite H00 /=) in "HslA'".
    iFrame "Hi Hpendingp HslA' HcapA' Hslin".
    iSplit.
    { erewrite take_S_r; last exact Hti.
      rewrite app_assoc. rewrite big_sepL2_snoc.
      iSplit; [iFrame "HitemsA" | iFrame "Hui"]. }
    iPureIntro. lia.
  - (* pending complete: content is pend0 ++ inputs; pending := nil *)
    wp_auto.
    have Hjge : (j >= length uivs_in)%nat.
    { move: Hcond. rewrite Hinlen. rewrite Hinlen in HjA. word. }
    have Htakeall : take j inputs = inputs.
    { apply take_ge. rewrite -Hlenin. lia. }
    iEval (rewrite Htakeall) in "HitemsA".
    (* ----- phase B: the drain loop ----- *)
    iAssert (∃ (pv : bool) (pendingS : slice.t) (uivsP : list yjs.updateItem.t)
               (pendingj appliedj suffix : list (TId * IntegrateInput (A := A)))
               (locs_j : gmap loc (list loc)) (p_j : pool) (bindj : gmap P loc) (mj : DocModel),
        "Hprog" ∷ progress_ptr ↦ pv ∗
        "Hpendingp" ∷ pending_ptr ↦ pendingS ∗
        "HslP" ∷ pendingS ↦* uivsP ∗
        "HcapP" ∷ own_slice_cap yjs.updateItem.t pendingS (DfracOwn 1) ∗
        "#HitemsPj" ∷ ([∗ list] updateItemVal;typedInput ∈ uivsP;pendingj, is_update_item updateItemVal typedInput) ∗
        "Hruns" ∷ own_store_runs s (MkStoreStateRuns client0 k0 locs_j p_j bindj [] pdel) ∗
        "%Hpendingsubj" ∷ ⌜∀ typedInput : TId * IntegrateInput (A := A),
            typedInput ∈ pendingj -> typedInput ∈ pend0 ++ inputs⌝ ∗
        "%Hprj" ∷ ⌜WireReplay m appliedj mj⌝ ∗
        "%Hbindsubj" ∷ ⌜bind ⊆ bindj⌝ ∗
        "%Hmtypesj" ∷ ⌜∀ name pl tm, bindj !! name = Some pl ->
            p_j !! pl = Some tm -> doc_model_get mj (RootId name) = tm_arr tm⌝ ∗
        "%Hmdomj" ∷ ⌜∀ t, doc_model_get mj t ≠ [] ->
            ∃ name pl, t = RootId name ∧ bindj !! name = Some pl⌝ ∗
        "%Hprovj" ∷ ⌜runs_within_or_from appliedj (all_runs p) (all_runs p_j)⌝ ∗
        "%Halrj" ∷ ⌜runs_apply_live_refine m (all_runs p) (all_runs p_j)⌝ ∗
        "%Hmid" ∷ ⌜pv = true ->
            wire_drain mj pendingj = (suffix, rest, m') ∧
            applied = appliedj ++ suffix ∧ ValidReplay (expand_inputs suffix) mj m'⌝ ∗
        "%Hfin" ∷ ⌜pv = false -> pendingj = rest ∧ mj = m' ∧ applied = appliedj⌝)%I
      with "[progress Hpendingp HslA HcapA Hclient Hclock HdeletedSet Hitems Hregistry Htypes Hpendf Hpdeletes]"
      as "IH".
    { iExists true, pslA, uivsA, (pend0 ++ inputs), [], applied, locs, p, bind, m.
      iFrame "progress Hpendingp HslA HcapA".
      iFrame "HitemsA".
      iSplitL "Hclient Hclock HdeletedSet Hitems Hregistry Htypes Hpendf Hpdeletes".
      { iSplitL; last (iPureIntro; split; [exact Hrpi0 | exact Hpreg0]).
        rewrite /own_store_fields_runs /=.
        iFrame "Hclient Hclock HdeletedSet Hitems Hregistry Htypes Hpdeletes".
        iExists slice.nil. iFrame "Hpendf". iExists [].
        iSplitL; [iApply own_slice_nil | iSplitL; [iApply own_slice_cap_nil | by rewrite big_sepL2_nil]]. }
      iPureIntro. split_and!.
      - done.
      - constructor.
      - done.
      - exact Hmtypes.
      - exact Hmdom.
      - exact (runs_within_or_from_refl [] (all_runs p)).
      - exact (runs_apply_live_refine_refl m (all_runs p)).
      - move=> _. split_and!; [exact Hdrain | done | exact Hvr].
      - move=> Hf. discriminate. }
    wp_for "IH".
    destruct pv.
    + (* progress: run one more pass *)
      rewrite decide_True; last done.
      destruct (Hmid eq_refl) as (Hdrainj & Happj & Hvrj).
      wp_auto.
      wp_apply wp_slice_literal. iSplitR; first done.
      iIntros "%rsl0 [Hrsl0 Hrcap0]". wp_auto.
      (* the pass computation this iteration refines *)
      destruct (wire_pass mj pendingj []) as [[app_rem0 keptfin0] m_pend0] eqn:Hpass0.
      (* the future passes' applied list ([suffix] is introduced as [suffix0]:
         the binder shadows stdpp's [suffix]) *)
      have [af [Hsufdec Hvraf]] : ∃ af,
          suffix0 = app_rem0 ++ af ∧ ValidReplay (expand_inputs (app_rem0 ++ af)) mj m'.
      { destruct app_rem0 as [| a0 ar0].
        - have Hdd := wire_drain_step_nil mj pendingj keptfin0 m_pend0 Hpass0.
          rewrite Hdrainj in Hdd.
          move: Hdd => [= Hsuf Hrest2 Hm2].
          have Hmp0 : m_pend0 = mj :=
            wire_pass_no_progress pendingj mj [] keptfin0 m_pend0 Hpass0.
          subst suffix0. exists []. split; first done.
          rewrite Hm2 Hmp0 /expand_inputs /=. constructor.
        - destruct (wire_drain m_pend0 keptfin0) as [[app2 rest2] m2] eqn:Hdrec.
          have Hdd := wire_drain_step_cons mj pendingj a0 ar0 keptfin0 app2 rest2
                        m_pend0 m2 Hpass0 Hdrec.
          rewrite Hdrainj in Hdd.
          move: Hdd => [= Hsuf Hrest2 Hm2].
          exists app2. split; first exact Hsuf.
          rewrite Hsuf in Hvrj. exact Hvrj. }
      iDestruct (big_sepL2_length with "HitemsPj") as %HlenP.
      iDestruct (own_slice_len with "HslP") as %[HPlen HPlen0].
      (* ----- the inner scan ----- *)
      iAssert (∃ (i : nat) (pvi : bool) (restS : slice.t)
                 (uivsR : list yjs.updateItem.t)
                 (keptacc appacc app_rem af2 : list (TId * IntegrateInput (A := A)))
                 (locs_c : gmap loc (list loc)) (p_c : pool) (bind_c : gmap P loc) (m_c : DocModel),
          "Hii" ∷ i_ptr ↦ W64 i ∗
          "Hprog" ∷ progress_ptr ↦ pvi ∗
          "Hrestp" ∷ rest_ptr ↦ restS ∗
          "HslR" ∷ restS ↦* uivsR ∗
          "HcapR" ∷ own_slice_cap yjs.updateItem.t restS (DfracOwn 1) ∗
          "#HitemsR" ∷ ([∗ list] updateItemVal;typedInput ∈ uivsR;keptacc, is_update_item updateItemVal typedInput) ∗
          "Hruns" ∷ own_store_runs s (MkStoreStateRuns client0 k0 locs_c p_c bind_c [] pdel) ∗
          "%Hilen" ∷ ⌜(i <= length pendingj)%nat⌝ ∗
          "%Hpassa" ∷ ⌜wire_pass m_c (drop i pendingj) keptacc =
              (app_rem, keptfin0, m_pend0)⌝ ∗
          "%Hpassc" ∷ ⌜wire_pass mj pendingj [] =
              (appacc ++ app_rem, keptfin0, m_pend0)⌝ ∗
          "%Happdec" ∷ ⌜applied = appliedj ++ appacc ++ app_rem ++ af2⌝ ∗
          "%Hvrc" ∷ ⌜ValidReplay (expand_inputs (app_rem ++ af2)) m_c m'⌝ ∗
          "%Hprc" ∷ ⌜WireReplay m (appliedj ++ appacc) m_c⌝ ∗
          "%Hkeptsub" ∷ ⌜∀ typedInput, typedInput ∈ keptacc -> typedInput ∈ pendingj⌝ ∗
          "%Hpv" ∷ ⌜pvi = false <-> appacc = []⌝ ∗
          "%Hbindsubc" ∷ ⌜bind ⊆ bind_c⌝ ∗
          "%Hmtypesc" ∷ ⌜∀ name pl tm, bind_c !! name = Some pl ->
              p_c !! pl = Some tm -> doc_model_get m_c (RootId name) = tm_arr tm⌝ ∗
          "%Hmdomc" ∷ ⌜∀ t, doc_model_get m_c t ≠ [] ->
              ∃ name pl, t = RootId name ∧ bind_c !! name = Some pl⌝ ∗
          "%Hprovc" ∷ ⌜runs_within_or_from (appliedj ++ appacc) (all_runs p) (all_runs p_c)⌝ ∗
          "%Hgrowc" ∷ ⌜∀ (t : TId) x, x ∈ doc_model_get m t -> x ∈ doc_model_get m_c t⌝ ∗
          "%Halrc" ∷ ⌜runs_apply_live_refine m (all_runs p) (all_runs p_c)⌝)%I
        with "[i Hprog rest Hrsl0 Hrcap0 Hruns]"
        as "IHin".
      { iExists 0%nat, false, _, [], [], [], app_rem0, af, locs_j, p_j, bindj, mj.
        iFrame "i Hprog rest Hrsl0 Hrcap0 Hruns".
        iSplit; first by rewrite big_sepL2_nil.
        iPureIntro. split_and!.
        - lia.
        - rewrite drop_0. exact Hpass0.
        - exact Hpass0.
        - rewrite Happj Hsufdec //.
        - exact Hvraf.
        - rewrite app_nil_r. exact Hprj.
        - move=> typedInput Hti. by apply elem_of_nil in Hti.
        - done.
        - exact Hbindsubj.
        - exact Hmtypesj.
        - exact Hmdomj.
        - rewrite app_nil_r. exact Hprovj.
        - exact (WireReplay_mem m mj appliedj Hprj).
        - exact Halrj. }
      wp_for "IHin".
      case_bool_decide as Hcondi.
      * (* scan struct i *)
        have Hilt : (i < length uivsP)%nat.
        { move: Hcondi. rewrite HPlen. word. }
        destruct (uivsP !! i) as [updateItemVal|] eqn:Huiv;
          last by (apply lookup_ge_None in Huiv; lia).
        destruct (pendingj !! i) as [[targetType input]|] eqn:Hpi;
          last by (apply lookup_ge_None in Hpi; rewrite -HlenP in Hpi; lia).
        iDestruct (big_sepL2_lookup _ _ _ i with "HitemsPj") as "#Hui";
          [exact Huiv | exact Hpi |].
        iDestruct (big_sepL2_lookup _ _ _ i with "HitemsPj") as
          (oleft oright opn)
          "(#HisL & #HisR & #HisPN & %Hin_l & %Hin_r & %Hin_id & %Hin_c & %Hunonempty & %Htid & %Hborrow)";
          [exact Huiv | exact Hpi |].
        simpl in Hin_l, Hin_r, Hin_id, Hin_c, Htid, Hborrow.
        have Hpending0in : (targetType, input) ∈ pend0 ++ inputs.
        { apply Hpendingsubj. exact (list_elem_of_lookup_2 _ _ _ Hpi). }
        (* read pending[i] into ui *)
        wp_auto.
        rewrite decide_True; last by word.
        iDestruct (own_slice_elem_acc (sint.Z (W64 i)) updateItemVal pendingS (DfracOwn 1)
                     uivsP with "HslP") as "[Hel Hgive]".
        { word. }
        { replace (Z.to_nat (sint.Z (W64 i))) with i by word. exact Huiv. }
        wp_auto.
        iDestruct ("Hgive" $! updateItemVal with "Hel") as "HslP".
        have Hinsid : (<[sint.nat (W64 i) := updateItemVal]> uivsP) = uivsP.
        { apply list_insert_id.
          replace (sint.nat (W64 i)) with i by word. exact Huiv. }
        iEval (rewrite Hinsid) in "HslP".
        (* the arrival probe: hasNode *)
        wp_apply (wp_store__hasNode_runs s (updateItemVal.(yjs.updateItem.id')) m_c
                    (MkStoreStateRuns client0 k0 locs_c p_c bind_c [] pdel) (conj Hmtypesc Hmdomc)
                    with "[$Hruns]").
        iIntros (ok) "(Hruns & %Hok)".
        rewrite Hin_id in Hok.
        have Hokm : ok = doc_model_has m_c (in_id input).
        { destruct ok, (doc_model_has m_c (in_id input)) eqn:Hd;
            [done | have := proj1 Hok eq_refl; done
             | have := proj2 Hok eq_refl; done | done]. }
        destruct (doc_model_has m_c (in_id input)) eqn:Hd; subst ok.
        { (* duplicate: continue *)
          wp_auto. wp_for_post.
          iFrame "Hcapin HΦ s Hslin Hpendingp HslP HcapP".
          iExists (S i), pvi, restS, uivsR, keptacc, appacc, app_rem, af2,
            locs_c, p_c, bind_c, m_c.
          replace (word.add (W64 i) (W64 1)) with (W64 (S i)) by word.
          iFrame "Hii Hprog Hrestp HslR HcapR Hruns".
          iFrame "HitemsR".
          iPureIntro. split_and!; try done.
          - apply (lookup_lt_Some _ _ _ Hpi).
          - rewrite (drop_S pendingj (targetType, input) i Hpi) /= Hd in Hpassa.
            exact Hpassa. }
        (* fresh: probe the structural gate *)
        wp_auto.
        wp_apply (wp_store__depsArrived_runs s updateItemVal (targetType, input) m_c
                    (MkStoreStateRuns client0 k0 locs_c p_c bind_c [] pdel) (conj Hmtypesc Hmdomc)
                    with "[$Hui $Hruns]").
        iIntros "Hruns".
        destruct (input_ready m_c input) eqn:Hready.
        -- (* ready: certified pendings always integrate the whole chunk *)
           have Hsome : is_Some (wire_integrate m_c (targetType, input)).
           { apply (Hrtot (appliedj ++ appacc) (app_rem ++ af2) m_c (targetType, input)).
             - rewrite Happdec !app_assoc //.
             - exact Hprc.
             - exact Hpending0in.
             - exact Hd.
             - exact Hready. }
           destruct Hsome as [arr' Hint'].
           (* step the wire pass equation *)
           rewrite (drop_S pendingj (targetType, input) i Hpi) /= Hd Hready Hint' in Hpassa.
           destruct (wire_pass (<[targetType := arr']> m_c) (drop (S i) pendingj) keptacc)
             as [[app2 kept2] m2] eqn:Hrec.
           move: Hpassa => [= Happrem Hkeq Hmeq].
           subst app_rem kept2 m2.
           (* peel this wire item's chunk off the per-char replay *)
           have Hne1 : (1 <= length (in_content input))%nat by (rewrite -Hin_c; exact Hunonempty).
           rewrite -app_comm_cons in Hvrc.
           have Hlk0 : ((targetType, input) :: app2 ++ af2) !! 0%nat = Some (targetType, input) by done.
           destruct (applyUpdate_peel_step ((targetType, input) :: app2 ++ af2) 0%nat targetType input
                       m_c m' (doc_model_get m_c targetType) Hlk0 Hne1 eq_refl Hvrc)
             as (newItem & arrp & Htoit & Hvld & Hmax & Hall & Hvrtail & Hclkbound).
           simpl in Hvrtail.
           have Harr2 : arrp = arr'.
           { move: Hint'. rewrite /wire_integrate Hall. by move=> [= <-]. }
           subst arrp.
           (* the target root's binding *)
           have [nm Htjeq] : ∃ nm, targetType = RootId nm.
           { destruct (decide (in_originId input = None ∧
                               in_rightOriginId input = None)) as [[HoN HrN] | Hor].
             - (* origin-free: [is_update_item] pins the root name; issue #54
                  no longer needs it BOUND (the grow dispatcher creates it) *)
               destruct opn as [nm'|].
               + exists nm'. exact (Htid nm' eq_refl).
               + exfalso. destruct (Hborrow eq_refl) as [Ho | Ho]; [exact (Ho HoN) | exact (Ho HrN)].
             - have Hne : doc_model_get m_c targetType ≠ [].
               { apply (toItem_nonempty_of_origin input _ newItem Htoit).
                 apply not_and_l in Hor.
                 by destruct Hor as [Ho | Ho]; [left | right]. }
               destruct (Hmdomc targetType Hne) as (nm & pl & Heq & Hb). by exists nm. }
           have Hnwc : (Z.of_nat (clock (in_id input)) + Z.of_nat (length (in_content input)) < 2^64)%Z
             := Hkb1 (targetType, input) Hpending0in.
           iDestruct (own_store_runs_run_wf with "Hruns") as %Hrunwfc.
           (* the current item's flat position in [applied] *)
           have HKlk : applied !! (length (appliedj ++ appacc)) = Some (targetType, input).
           { rewrite Happdec (app_assoc appliedj appacc) lookup_app_r; last done.
             rewrite Nat.sub_diag /=. done. }
           (* freshness: existing same-client runs lie below this item's clock *)
           have Hbelow : pool_run_clock_below p_c (in_id input).
           { move=> r0 Hr0 Hcc0.
             have Hwfr0 : run_wf (run_items r0) := Hrunwfc r0 Hr0.
             destruct (Hprovc r0 Hr0) as [(r1 & Hr1 & Hcl1 & Hlo1 & Hhi1) | (typedInput & Hti & Hcc1 & Hlo1 & Hhi1)].
             - (* original run r1 of p: [expand_inputs_arr_fresh] via its last char *)
               have Hwf1 : run_wf (run_items r1) := Hrunwf_init r1 Hr1.
               have Hlen1 : (1 <= length (run_items r1))%nat.
               { destruct (run_items r1) eqn:E; [exact (False_ind _ (proj1 Hwf1 eq_refl)) | simpl; lia]. }
               destruct (lookup_lt_is_Some_2 (run_items r1) (length (run_items r1) - 1)%nat ltac:(lia)) as [xl Hxl].
               have Hxlid := run_wf_char_id (run_items r1) _ xl Hwf1 Hxl.
               apply elem_of_all_runs in Hr1 as (q1 & tm1 & Hq1 & Hrt1).
               destruct (Htypesbound q1 (ex_intro _ tm1 Hq1)) as [name1 Hbnm1].
               have Hdg1 : doc_model_get m (RootId name1) = tm_arr tm1 := Hmtypes name1 q1 tm1 Hbnm1 Hq1.
               have Hrep1 : tm_arr tm1 = runs_flatten (tm_runs tm1) := Harr_init q1 tm1 Hq1.
               apply list_elem_of_lookup_1 in Hrt1 as [ci1 Hci1].
               have Hxlmem : xl ∈ doc_model_get m (RootId name1).
               { rewrite Hdg1 Hrep1.
                 apply (list_elem_of_lookup_2 _
                          (length (runs_flatten (take ci1 (tm_runs tm1))) + (length (run_items r1) - 1))%nat).
                 exact (runs_flatten_lookup_of_run (tm_runs tm1) ci1 _ r1 xl Hci1 Hxl). }
               have Hxlcl : clientId (item_id xl) = clientId (in_id input).
               { rewrite Hxlid /=. rewrite -Hcc0 Hcl1 /run_client /run_head_item //. }
               have Hxlfr := expand_inputs_arr_fresh applied m m' Hvr (length (appliedj ++ appacc))
                               (targetType, input) HKlk Hne1 (RootId name1) xl Hxlmem Hxlcl.
               change ((targetType, input).2) with input in Hxlfr.
               (* no [simpl] on [Hxlfr]: it would unfold [inhabitant] under the
                  [hd] and split the atom [run_clock r1] sees *)
               have Hxlck : clock (item_id xl) = (run_clock r1 + (length (run_items r1) - 1))%nat
                 by rewrite Hxlid /run_clock /run_head_item //.
               have Hend1 : (run_clock r1 + length (run_items r1) <= clock (in_id input))%nat.
               { move: Hxlfr Hxlck Hlen1. lia. }
               lia.
             - (* batch run: [expand_inputs_range_causal] on the applied replay *)
               have Hti_in : typedInput ∈ applied.
               { rewrite Happdec (app_assoc appliedj appacc). apply elem_of_app. by left. }
               have Hti_pi : typedInput ∈ pend0 ++ inputs := Happliedsub typedInput Hti_in.
               destruct (list_elem_of_lookup_1 _ _ Hti) as [jb Hj0].
               have Hjlt : (jb < length (appliedj ++ appacc))%nat := lookup_lt_Some _ _ _ Hj0.
               have Hjapp : applied !! jb = Some typedInput.
               { rewrite Happdec (app_assoc appliedj appacc) lookup_app_l; last exact Hjlt.
                 exact Hj0. }
               have Hcln : clientId (in_id typedInput.2) = clientId (in_id input) by congruence.
               have Hnei : (1 <= length (in_content typedInput.2))%nat := Hnonempty typedInput Hti_pi.
               have Htifr := expand_inputs_range_causal applied m m' Hvr
                               (length (appliedj ++ appacc)) jb (targetType, input) typedInput HKlk Hjapp Hjlt
                               Hcln Hnei Hne1.
               change ((targetType, input).2) with input in Htifr.
               lia. }
           simpl. rewrite Hready. wp_auto.
           wp_apply (wp_store__integrateDecoded_runs s updateItemVal (targetType, input)
                       m_c (MkStoreStateRuns client0 k0 locs_c p_c bind_c [] pdel) newItem arr' nm
                       Htjeq Htoit Hvld Hmax Hall Hbelow (conj Hmtypesc Hmdomc) Hnwc
                       with "[$Hui $Hruns]").
           iIntros (p'' locs'' bind'') "(Hruns & %Hbindsub'' & %Hregmodel'' & %Hprov'' & %Hilr'')".
           iEval (simpl) in "Hruns".
           have [Hmtypes'' Hmdom''] := Hregmodel''.
           have Hstep1 : WireReplay m_c [(targetType, input)] (<[targetType := arr']> m_c)
             := WireReplay_cons m_c (targetType, input) arr' [] _ Hd Hready Hint'
                  (WireReplay_nil _).
           have Hgrow_step := WireReplay_mem m_c _ _ Hstep1.
           have Hgrowc_has : ∀ i0, doc_model_has m i0 = true -> doc_model_has m_c i0 = true
             := λ i0, docm_has_mono m m_c i0 Hgrowc.
           wp_auto. wp_for_post.
           iFrame "Hcapin HΦ s Hslin Hpendingp HslP HcapP".
           iExists (S i), true, restS, uivsR, keptacc, (appacc ++ [(targetType, input)]),
             app2, af2, locs'', p'', bind'', (<[targetType := arr']> m_c).
           replace (word.add (W64 i) (W64 1)) with (W64 (S i)) by word.
           iFrame "Hii Hprog Hrestp HslR HcapR Hruns".
           iFrame "HitemsR".
           iPureIntro. split_and!.
           ++ apply (lookup_lt_Some _ _ _ Hpi).
           ++ exact Hrec.
           ++ rewrite -app_assoc /=. exact Hpassc.
           ++ rewrite -app_assoc /=. exact Happdec.
           ++ exact Hvrtail.
           ++ rewrite app_assoc.
              apply (WireReplay_app m m_c _ (appliedj ++ appacc) [(targetType, input)] Hprc).
              apply (WireReplay_cons m_c (targetType, input) arr' [] _ Hd Hready Hint').
              constructor.
           ++ exact Hkeptsub.
           ++ split; [move=> Hf; discriminate | move=> Habs; by destruct appacc].
           ++ etrans; [exact Hbindsubc | exact Hbindsub''].
           ++ exact Hmtypes''.
           ++ exact Hmdom''.
           ++ rewrite app_assoc.
              exact (runs_within_or_from_trans _ _ _ _ _ Hprovc Hprov'').
           ++ (* the model grows by this one integrate step *)
              move=> t x Hx. exact (Hgrow_step t x (Hgrowc t x Hx)).
           ++ (* the tombstone-set refinement: the repaired/spliced pool's live
                 chars are old live chars or chars this step just integrated,
                 which the replay's client bound puts outside the old model *)
              apply (runs_apply_live_refine_trans m m_c (all_runs p)
                       (all_runs p_c) (all_runs p'') Hgrowc_has Halrc).
              exact (runs_apply_live_refine_of_integrate input m_c
                       (all_runs p_c) (all_runs p'') Hclkbound Hilr'').
        -- (* blocked: keep (deduplicated by id) *)
           rewrite (drop_S pendingj (targetType, input) i Hpi) /= Hd Hready in Hpassa.
           simpl. rewrite Hready. wp_auto.
           wp_apply (wp_containsUpdateItemId restS (DfracOwn 1) keptacc
                       (updateItemVal.(yjs.updateItem.id')) with "[HslR HcapR]").
           { iExists uivsR. iFrame "HslR HcapR HitemsR". }
           iIntros "Hos". iDestruct "Hos" as (uivsR2) "(HslR & HcapR & #HitemsR2)".
           rewrite Hin_id.
           destruct (existsb (λ tj0, bool_decide (in_id tj0.2 = in_id input))
                       keptacc) eqn:Hex.
           ** (* already kept: skip *)
              wp_auto. wp_for_post.
              iFrame "Hcapin HΦ s Hslin Hpendingp HslP HcapP".
              iExists (S i), pvi, restS, uivsR2, keptacc, appacc, app_rem, af2,
                locs_c, p_c, bind_c, m_c.
              replace (word.add (W64 i) (W64 1)) with (W64 (S i)) by word.
              iFrame "Hii Hprog Hrestp HslR HcapR Hruns".
              iFrame "HitemsR2".
              iPureIntro. split_and!; try done.
              --- apply (lookup_lt_Some _ _ _ Hpi).
              --- rewrite /pending_keep /= Hex in Hpassa. exact Hpassa.
           ** (* newly kept: append to rest *)
              wp_auto.
              wp_apply wp_slice_literal. iSplitR; first done.
              iIntros "%sing [Hsing _]". wp_auto.
              wp_apply (wp_slice_append with "[$HslR $HcapR $Hsing]").
              iIntros (restS') "(HslR' & HcapR' & _)". wp_auto.
              wp_for_post.
              iFrame "Hcapin HΦ s Hslin Hpendingp HslP HcapP".
              iExists (S i), pvi, restS', (uivsR2 ++ [updateItemVal]),
                (keptacc ++ [(targetType, input)]), appacc, app_rem, af2, locs_c, p_c, bind_c, m_c.
              replace (word.add (W64 i) (W64 1)) with (W64 (S i)) by word.
              have H00 : sint.nat (W64 0) = 0%nat by word.
              iEval (rewrite H00 /=) in "HslR'".
              iFrame "Hii Hprog Hrestp HslR' HcapR' Hruns".
              iSplit.
              { rewrite big_sepL2_snoc.
                iSplit; [iFrame "HitemsR2" | iFrame "Hui"]. }
              iPureIntro. split_and!; try done.
              --- apply (lookup_lt_Some _ _ _ Hpi).
              --- rewrite /pending_keep /= Hex in Hpassa. exact Hpassa.
              --- move=> typedInput Hti. apply elem_of_app in Hti.
                  destruct Hti as [Hti | Hti]; first exact (Hkeptsub typedInput Hti).
                  apply list_elem_of_singleton in Hti. subst typedInput.
                  exact (list_elem_of_lookup_2 _ _ _ Hpi).
      * (* scan done: close the pass *)
        have Hige : (length pendingj <= i)%nat.
        { rewrite -HlenP HPlen. rewrite -HlenP HPlen in Hilen.
          move: Hcondi. word. }
        rewrite drop_ge in Hpassa; last exact Hige.
        simpl in Hpassa.
        move: Hpassa => [= Happrem Hkeq Hmeq].
        subst app_rem keptfin0 m_pend0.
        rewrite app_nil_r in Hpassc.
        have Hsufeq : suffix0 = appacc ++ af2.
        { apply (app_inv_head appliedj). rewrite -Happj.
          rewrite Happdec /= //. }
        wp_auto. wp_for_post.
        iFrame "Hcapin HΦ s Hslin".
        iExists pvi, restS, uivsR, keptacc, (appliedj ++ appacc), af2,
          locs_c, p_c, bind_c, m_c.
        iFrame "Hprog Hpendingp HslR HcapR Hruns".
        iFrame "HitemsR".
        iPureIntro. split_and!.
        ** move=> typedInput Hti. apply Hpendingsubj. exact (Hkeptsub typedInput Hti).
        ** exact Hprc.
        ** exact Hbindsubc.
        ** exact Hmtypesc.
        ** exact Hmdomc.
        ** exact Hprovc.
        ** exact Halrc.
        ** (* progress: one more drain iteration remains *)
           move=> Hpvt.
           destruct appacc as [| a0 acc0].
           { have := proj2 Hpv eq_refl. rewrite Hpvt.
             move=> Hcontra. discriminate. }
           destruct (wire_drain m_c keptacc) as [[app2' rest2'] m2'] eqn:Hdrec2.
           have Hdd := wire_drain_step_cons mj pendingj a0 acc0 keptacc app2'
                         rest2' m_c m2' Hpassc Hdrec2.
           rewrite Hdrainj in Hdd.
           move: Hdd => [= Hsuf Hrest2 Hm2].
           have Haf2 : af2 = app2'.
           { apply (app_inv_head (a0 :: acc0)). rewrite -Hsufeq Hsuf //. }
           split_and!.
           --- rewrite Haf2 Hrest2 Hm2 //.
           --- rewrite -app_assoc. exact Happdec.
           --- exact Hvrc.
        ** (* no progress: the drain is complete *)
           move=> Hpvf.
           have Hacc0 : appacc = [] := proj1 Hpv Hpvf.
           subst appacc.
           have Hdd := wire_drain_step_nil mj pendingj keptacc m_c Hpassc.
           rewrite Hdrainj in Hdd.
           move: Hdd => [= Hsuf Hrest2 Hm2].
           split_and!.
           --- by rewrite Hrest2.
           --- by rewrite Hm2.
           --- rewrite Happj Hsuf app_nil_r //.
    + (* drain complete: write back the pending and return *)
      rewrite decide_False; last done.
      rewrite decide_True; last done.
      destruct (Hfin eq_refl) as (Hpendingeq & Hmeq & Happeq).
      subst pendingj mj.
      iDestruct "Hruns" as "(Hfieldsj & %Hinvsj)".
      iEval (simpl) in "Hfieldsj".
      have Hrpij : run_pool_invs p_j := proj1 Hinvsj.
      have Hregj : pool_registry_coh bindj p_j := proj2 Hinvsj.
      iDestruct "Hfieldsj" as "(Hclient & Hclock & HdeletedSet & Hitems & Hregistry & Htypes & Hpending & Hpdeletes)".
      iDestruct "Hpending" as (pnil) "(Hpendf & _)".
      wp_auto.
      iApply ("HΦ" $! p_j locs_j bindj). simpl.
      iAssert (own_pending_field (s .[(yjs.store.t), "pending"]) rest)%I with "[Hpendf HslP HcapP]" as "Hpending".
      { iExists pendingS. iFrame "Hpendf". iExists uivsP. iFrame "HslP HcapP HitemsPj". }
      iSplitL "Hslin Hcapin".
      { iExists uivs_in. iFrame "Hslin Hcapin Hitemsin". }
      iSplitL "Hclient Hclock HdeletedSet Hitems Hregistry Htypes Hpending Hpdeletes".
      { iSplitL; last (iPureIntro; split; [exact Hrpij | exact Hregj]).
        rewrite /own_store_fields_runs /=.
        iFrame "Hclient Hclock HdeletedSet Hitems Hregistry Htypes Hpending Hpdeletes". }
      iPureIntro. split_and!.
      * exact Hbindsubj.
      * exact (conj Hmtypesj Hmdomj).
      * exact Halrj.
Qed.

(* ===== wire-drain bridge lemmas (issue #40 x issue #28 U7c) ===============
   Pure structural facts relating a [wire_drain] to its applied/leftover lists
   and to the per-char model, all provable against the [wire_pass] / [wire_drain]
   / [WireReplay] definitions in [store/GetNode]. The certificate spec below
   composes them: [wire_drain_subset] recertifies the leftover pending,
   [wire_drain_replay] exposes the applied list as a [WireReplay], and
   [expand_inputs_subset] carries the per-char certificates from the drained
   batch to its applied sublist. *)

(** The applied and leftover lists of a wire pass are drawn from the pending. *)
Lemma wire_pass_subset (pending : list (TId * IntegrateInput (A := A))) :
  ∀ m kept app kept' m',
    wire_pass m pending kept = (app, kept', m') ->
    (∀ typedInput, typedInput ∈ app -> typedInput ∈ pending) ∧
    (∀ typedInput, typedInput ∈ kept' -> typedInput ∈ kept ∨ typedInput ∈ pending).
Proof.
  elim: pending => [| ti0 tl IH] m kept app kept' m' /=.
  - move=> [= <- <- _]. split; [move=> typedInput Hin; by apply elem_of_nil in Hin |].
    move=> typedInput Hin. by left.
  - destruct (doc_model_has m (in_id ti0.2)).
    { move=> /IH [Happ Hkept]. split.
      - move=> typedInput Hin. apply elem_of_cons. right. exact (Happ typedInput Hin).
      - move=> typedInput Hin. destruct (Hkept typedInput Hin) as [Hk | Hp]; [by left |].
        right. apply elem_of_cons. by right. }
    destruct (input_ready m ti0.2); last first.
    { move=> /IH [Happ Hkept]. split.
      - move=> typedInput Hin. apply elem_of_cons. right. exact (Happ typedInput Hin).
      - move=> typedInput Hin. destruct (Hkept typedInput Hin) as [Hk | Hp].
        + destruct (pending_keep_subset kept ti0 typedInput Hk) as [Hk' | ->]; [by left |].
          right. apply elem_of_cons. by left.
        + right. apply elem_of_cons. by right. }
    destruct (wire_integrate m ti0) as [arr' |]; last first.
    { move=> /IH [Happ Hkept]. split.
      - move=> typedInput Hin. apply elem_of_cons. right. exact (Happ typedInput Hin).
      - move=> typedInput Hin. destruct (Hkept typedInput Hin) as [Hk | Hp].
        + destruct (pending_keep_subset kept ti0 typedInput Hk) as [Hk' | ->]; [by left |].
          right. apply elem_of_cons. by left.
        + right. apply elem_of_cons. by right. }
    destruct (wire_pass (<[ti0.1 := arr']> m) tl kept) as [[app0 kept0] m0] eqn:Hrec.
    move=> [= <- <- _].
    destruct (IH _ _ _ _ _ Hrec) as [Happ Hkept]. split.
    + move=> typedInput Hin. apply elem_of_cons in Hin.
      destruct Hin as [-> | Hin]; [by left | right; exact (Happ typedInput Hin)].
    + move=> typedInput Hin. destruct (Hkept typedInput Hin) as [Hk | Hp]; [by left |].
      right. apply elem_of_cons. by right.
Qed.

Lemma wire_drain_aux_subset (fuel : nat) :
  ∀ (m : DocModel) (pending app rest : list (TId * IntegrateInput (A := A))) (m' : DocModel),
    wire_drain_aux fuel m pending = (app, rest, m') ->
    (∀ typedInput, typedInput ∈ app -> typedInput ∈ pending) ∧ (∀ typedInput, typedInput ∈ rest -> typedInput ∈ pending).
Proof.
  elim: fuel => [| f IH] m pending app rest m' /=.
  - move=> [= <- <- _]. split; [move=> typedInput Hin; by apply elem_of_nil in Hin | done].
  - destruct (wire_pass m pending []) as [[app0 kept] m0] eqn:Hpass.
    destruct (wire_pass_subset pending m [] app0 kept m0 Hpass) as [Happ0 Hkept0].
    have Hkept0' : ∀ typedInput, typedInput ∈ kept -> typedInput ∈ pending.
    { move=> typedInput Hin. destruct (Hkept0 typedInput Hin) as [Hk | Hp];
        [by apply elem_of_nil in Hk | done]. }
    destruct app0 as [| a app0'].
    { move=> [= <- <- _]. split; [move=> typedInput Hin; by apply elem_of_nil in Hin | done]. }
    destruct (wire_drain_aux f m0 kept) as [[app2 rest2] m2] eqn:Hrec.
    move=> [= <- <- _].
    destruct (IH _ _ _ _ _ Hrec) as [Happ2 Hrest2]. split.
    + move=> typedInput Hin.
      apply elem_of_cons in Hin. destruct Hin as [-> | Hin].
      * apply (Happ0 a). apply elem_of_cons. by left.
      * apply elem_of_app in Hin. destruct Hin as [Hin | Hin].
        -- apply (Happ0 typedInput). apply elem_of_cons. by right.
        -- exact (Hkept0' typedInput (Happ2 typedInput Hin)).
    + move=> typedInput Hin. exact (Hkept0' typedInput (Hrest2 typedInput Hin)).
Qed.

Lemma wire_drain_subset (m : DocModel)
    (pending app rest : list (TId * IntegrateInput (A := A))) (m' : DocModel) :
  wire_drain m pending = (app, rest, m') ->
  (∀ typedInput, typedInput ∈ app -> typedInput ∈ pending) ∧ (∀ typedInput, typedInput ∈ rest -> typedInput ∈ pending).
Proof. apply wire_drain_aux_subset. Qed.

Lemma wire_drain_aux_replay (fuel : nat) :
  ∀ (m : DocModel) (pending app rest : list (TId * IntegrateInput (A := A))) (m' : DocModel),
    wire_drain_aux fuel m pending = (app, rest, m') ->
    WireReplay m app m'.
Proof.
  elim: fuel => [| f IH] m pending app rest m' /=.
  - move=> [= <- _ <-]. constructor.
  - destruct (wire_pass m pending []) as [[app0 kept] m0] eqn:Hpass.
    destruct app0 as [| a app0'].
    { move=> [= <- _ <-].
      rewrite (wire_pass_no_progress pending m [] kept m0 Hpass). constructor. }
    destruct (wire_drain_aux f m0 kept) as [[app2 rest2] m2] eqn:Hrec.
    move=> [= <- _ <-].
    exact (WireReplay_app _ _ _ _ _ (wire_pass_replay pending m [] _ _ _ Hpass)
             (IH _ _ _ _ _ Hrec)).
Qed.

Lemma wire_drain_replay (m : DocModel)
    (pending app rest : list (TId * IntegrateInput (A := A))) (m' : DocModel) :
  wire_drain m pending = (app, rest, m') ->
  WireReplay m app m'.
Proof. apply wire_drain_aux_replay. Qed.

(** [expand_inputs] is monotone over list membership: a per-char certificate for
    the whole drained batch specializes to any applied/leftover sublist. *)
Lemma expand_inputs_subset (a b : list (TId * IntegrateInput (A := A))) :
  (∀ typedInput, typedInput ∈ a -> typedInput ∈ b) ->
  (∀ typedInput, typedInput ∈ expand_inputs a -> typedInput ∈ expand_inputs b).
Proof.
  move=> Hsub typedInput. rewrite /expand_inputs !list_elem_of_join.
  move=> [l [Hti Hl]]. exists l. split; [exact Hti |].
  apply list_elem_of_fmap in Hl as [x [-> Hx]].
  apply list_elem_of_fmap. exists x. split; [done | exact (Hsub x Hx)].
Qed.

(* ===== no-loss id conservation of the drain (this branch) =================
   The [wire_drain] loop can retire a pending wire item three ways: integrate
   it (into [applied]), keep it for a later pass (into [rest], possibly deduped
   by id via [pending_keep]), or skip it because its id is already in the doc
   model ([doc_model_has], a re-delivered struct). These lemmas prove none of
   the three loses the item: EVERY pending item is accounted for at the id
   level -- some applied item shares its id, some kept item shares its id, or
   the final model already carries its id. [wp_store__applyUpdate] turns
   this into the per-input guarantee that each input is either delivered into
   the history or buffered in the new pending: no input silently vanishes. *)

(** A single pass grows the doc model (per type). *)
Lemma wire_pass_model_grows (pending : list (TId * IntegrateInput (A := A))) :
  ∀ m kept app kept' m',
    wire_pass m pending kept = (app, kept', m') ->
    ∀ (t : TId) x, x ∈ doc_model_get m t -> x ∈ doc_model_get m' t.
Proof.
  move=> m kept app kept' m' Hpass.
  exact (WireReplay_mem m m' app (wire_pass_replay pending m kept app kept' m' Hpass)).
Qed.

(** A drain (fuelled) grows the doc model (per type). *)
Lemma wire_drain_aux_model_grows (fuel : nat) (m : DocModel)
    (pending app rest : list (TId * IntegrateInput (A := A))) (m' : DocModel) :
  wire_drain_aux fuel m pending = (app, rest, m') ->
  ∀ (t : TId) x, x ∈ doc_model_get m t -> x ∈ doc_model_get m' t.
Proof.
  move=> Hdr.
  exact (WireReplay_mem m m' app (wire_drain_aux_replay fuel m pending app rest m' Hdr)).
Qed.

(** [pending_keep] never drops a kept item. *)
Lemma pending_keep_incl_l (kept : list (TId * IntegrateInput (A := A)))
    (typedInput : TId * IntegrateInput (A := A)) :
  ∀ y, y ∈ kept -> y ∈ pending_keep kept typedInput.
Proof.
  move=> y Hy. rewrite /pending_keep.
  destruct (existsb (λ typedInput2, bool_decide (in_id typedInput2.2 = in_id typedInput.2)) kept);
    [exact Hy | apply elem_of_app; by left].
Qed.

(** [pending_keep kept ti] always contains an item with [ti]'s id: either the
    pre-existing duplicate it dedups against, or [ti] itself appended. *)
Lemma pending_keep_has_id (kept : list (TId * IntegrateInput (A := A)))
    (typedInput : TId * IntegrateInput (A := A)) :
  ∃ y, y ∈ pending_keep kept typedInput ∧ in_id y.2 = in_id typedInput.2.
Proof.
  rewrite /pending_keep.
  destruct (existsb (λ typedInput2, bool_decide (in_id typedInput2.2 = in_id typedInput.2)) kept) eqn:Hex.
  - apply existsb_exists in Hex. destruct Hex as [y [Hy Hid]].
    apply bool_decide_eq_true in Hid. exists y.
    split; [apply list_elem_of_In; exact Hy | exact Hid].
  - exists typedInput.
    split; [apply elem_of_app; right; apply elem_of_cons; by left | done].
Qed.

(** A pass keeps every item it started with. *)
Lemma wire_pass_kept_incl (pending : list (TId * IntegrateInput (A := A))) :
  ∀ m kept app kept' m',
    wire_pass m pending kept = (app, kept', m') ->
    ∀ y, y ∈ kept -> y ∈ kept'.
Proof.
  elim: pending => [| ti0 tl IH] m kept app kept' m' /=.
  - move=> [= _ <- _] y Hy //.
  - destruct (doc_model_has m (in_id ti0.2)).
    { move=> Hpass y Hy. exact (IH m kept app kept' m' Hpass y Hy). }
    destruct (input_ready m ti0.2); last first.
    { move=> Hpass y Hy.
      exact (IH m (pending_keep kept ti0) app kept' m' Hpass y (pending_keep_incl_l kept ti0 y Hy)). }
    destruct (wire_integrate m ti0) as [arr' |]; last first.
    { move=> Hpass y Hy.
      exact (IH m (pending_keep kept ti0) app kept' m' Hpass y (pending_keep_incl_l kept ti0 y Hy)). }
    destruct (wire_pass (<[ti0.1 := arr']> m) tl kept) as [[app0 kept0] m0] eqn:Hrec.
    move=> [= _ <- _] y Hy. exact (IH (<[ti0.1 := arr']> m) kept app0 kept0 m0 Hrec y Hy).
Qed.

(** Single-pass id conservation: every item in [pending] is applied (by id) in
    [app], kept (by id) in [kept'], or its id is already in the pass's final
    model [m']. *)
Lemma wire_pass_id_conservation (pending : list (TId * IntegrateInput (A := A))) :
  ∀ m kept app kept' m',
    wire_pass m pending kept = (app, kept', m') ->
    ∀ x, x ∈ pending ->
      (∃ y, y ∈ app ∧ in_id y.2 = in_id x.2) ∨
      (∃ y, y ∈ kept' ∧ in_id y.2 = in_id x.2) ∨
      doc_model_has m' (in_id x.2) = true.
Proof.
  elim: pending => [| ti0 tl IH] m kept app kept' m' /=.
  - move=> [= <- <- <-] x Hx. by apply elem_of_nil in Hx.
  - destruct (doc_model_has m (in_id ti0.2)) eqn:Hdup.
    { move=> Hpass x Hx. apply elem_of_cons in Hx. destruct Hx as [-> | Hx].
      - right; right.
        exact (docm_has_mono m m' (in_id ti0.2)
                 (wire_pass_model_grows tl m kept app kept' m' Hpass) Hdup).
      - exact (IH m kept app kept' m' Hpass x Hx). }
    destruct (input_ready m ti0.2) eqn:Hready; last first.
    { move=> Hpass x Hx. apply elem_of_cons in Hx. destruct Hx as [-> | Hx].
      - right; left. destruct (pending_keep_has_id kept ti0) as [y [Hy Hid]].
        exists y. split;
          [exact (wire_pass_kept_incl tl m (pending_keep kept ti0) app kept' m' Hpass y Hy) | exact Hid].
      - exact (IH m (pending_keep kept ti0) app kept' m' Hpass x Hx). }
    destruct (wire_integrate m ti0) as [arr' |] eqn:Hint; last first.
    { move=> Hpass x Hx. apply elem_of_cons in Hx. destruct Hx as [-> | Hx].
      - right; left. destruct (pending_keep_has_id kept ti0) as [y [Hy Hid]].
        exists y. split;
          [exact (wire_pass_kept_incl tl m (pending_keep kept ti0) app kept' m' Hpass y Hy) | exact Hid].
      - exact (IH m (pending_keep kept ti0) app kept' m' Hpass x Hx). }
    destruct (wire_pass (<[ti0.1 := arr']> m) tl kept) as [[app0 kept0] m0] eqn:Hrec.
    move=> [= <- <- <-] x Hx. apply elem_of_cons in Hx. destruct Hx as [-> | Hx].
    + left. exists ti0. split; [apply elem_of_cons; by left | done].
    + destruct (IH (<[ti0.1 := arr']> m) kept app0 kept0 m0 Hrec x Hx)
        as [[y [Hy Hid]] | [[y [Hy Hid]] | Hh]].
      * left. exists y. split; [apply elem_of_cons; by right | exact Hid].
      * right; left. exists y. by split.
      * right; right. exact Hh.
Qed.

(** Fuelled-drain id conservation. *)
Lemma wire_drain_aux_id_conservation (fuel : nat) :
  ∀ (m : DocModel) (pending applied rest : list (TId * IntegrateInput (A := A))) (m' : DocModel),
    wire_drain_aux fuel m pending = (applied, rest, m') ->
    ∀ x, x ∈ pending ->
      (∃ y, y ∈ applied ∧ in_id y.2 = in_id x.2) ∨
      (∃ y, y ∈ rest ∧ in_id y.2 = in_id x.2) ∨
      doc_model_has m' (in_id x.2) = true.
Proof.
  elim: fuel => [| f IH] m pending applied rest m' /=.
  - move=> [= <- <- <-] x Hx. right; left. exists x. by split.
  - destruct (wire_pass m pending []) as [[app kept] m0] eqn:Hpass.
    destruct app as [| a app0].
    { move=> [= <- <- <-] x Hx.
      destruct (wire_pass_id_conservation pending m [] [] kept m0 Hpass x Hx)
        as [[y [Hy _]] | Hrest]; [by apply elem_of_nil in Hy | by right]. }
    destruct (wire_drain_aux f m0 kept) as [[app2 rest2] m2] eqn:Hrec.
    move=> [= <- <- <-] x Hx.
    destruct (wire_pass_id_conservation pending m [] (a :: app0) kept m0 Hpass x Hx)
      as [[y [Hy Hid]] | [[y [Hy Hid]] | Hh]].
    + (* [applied = (a :: app0) ++ app2] normalises to the cons [a :: _], so go
         via [elem_of_cons] rather than [elem_of_app] *)
      left. exists y. split; [| exact Hid].
      apply elem_of_cons in Hy. apply elem_of_cons.
      destruct Hy as [-> | Hy]; [by left | right; apply elem_of_app; by left].
    + destruct (IH m0 kept app2 rest2 m2 Hrec y Hy)
        as [[z [Hz Hzid]] | [[z [Hz Hzid]] | Hzh]].
      * left. exists z. split; [| by rewrite Hzid].
        apply elem_of_cons; right; apply elem_of_app; by right.
      * right; left. exists z. split; [exact Hz | by rewrite Hzid].
      * right; right. by rewrite -Hid.
    + right; right.
      exact (docm_has_mono m0 m2 (in_id x.2)
               (wire_drain_aux_model_grows f m0 kept app2 rest2 m2 Hrec) Hh).
Qed.

(** THE no-loss lemma: draining [pending] loses no item's id. *)
Lemma wire_drain_id_conservation (m : DocModel)
    (pending applied rest : list (TId * IntegrateInput (A := A))) (m' : DocModel) :
  wire_drain m pending = (applied, rest, m') ->
  ∀ x, x ∈ pending ->
    (∃ y, y ∈ applied ∧ in_id y.2 = in_id x.2) ∨
    (∃ y, y ∈ rest ∧ in_id y.2 = in_id x.2) ∨
    doc_model_has m' (in_id x.2) = true.
Proof. rewrite /wire_drain. apply wire_drain_aux_id_conservation. Qed.

(* ===== wire chunk -> per-char PendingReplay bridge (issue #40 x #28 U7c) ===
   A WIRE item integrates its whole run atomically ([wire_integrate] =
   [integrate_all] over [ops_of_input]); the certificate layer needs the
   PER-CHAR view ([PendingReplay] over [expand_input]) to reuse the causal
   validity machinery ([pending_ValidReplay]). These lemmas turn one atomic
   chunk integration into the sequence of per-char [PendingReplay] steps it
   denotes. Freshness of char [k>0] follows from head-freshness alone (the
   earlier chars only add their own consecutive ids), so no run-completeness
   invariant is needed at this level. *)

(** [integrate] adds an item of exactly the input's id: a replayed item is
    either the new item or an original one (membership inversion). *)
Lemma integrate_mem_inv (input : IntegrateInput (A := A)) (arr arr2 : list (YjsItem A))
    (x : YjsItem A) :
  integrate input arr = Some arr2 -> x ∈ arr2 -> item_id x = in_id input ∨ x ∈ arr.
Proof.
  move=> Hint Hx.
  pose proof (integrate_insertIdx_form input arr arr2 Hint) as (didx & item & Hitid & Hres).
  rewrite Hres in Hx.
  case: (decide (didx <= length arr)%nat) => Hd.
  - apply (proj1 (mem_insertIdxIfInBounds arr item x didx Hd)) in Hx.
    destruct Hx as [-> | Hin]; [left; exact Hitid | by right].
  - rewrite /insertIdxIfInBounds decide_False // in Hx. by right.
Qed.

(** Integrating one item leaves every OTHER id's presence unchanged: an id that
    is absent and is not the integrated input's id stays absent. *)
Lemma docm_has_integrate_ne (m : DocModel) (t : TId) (input : IntegrateInput (A := A))
    (arr' : list (YjsItem A)) (d : YjsId) :
  integrate input (doc_model_get m t) = Some arr' ->
  d ≠ in_id input ->
  doc_model_has m d = false ->
  doc_model_has (<[t := arr']> m) d = false.
Proof.
  move=> Hint Hne Hfalse.
  destruct (doc_model_has (<[t := arr']> m) d) eqn:Hh; [| done].
  exfalso. apply docm_has_spec in Hh. destruct Hh as (t' & x & Hx & Hid).
  destruct (decide (t' = t)) as [-> | Hnet].
  - rewrite docm_get_insert_eq in Hx.
    destruct (integrate_mem_inv input (doc_model_get m t) arr' x Hint Hx) as [Hxid | Hin].
    + apply Hne. by rewrite -Hid Hxid.
    + have : doc_model_has m d = true.
      { apply docm_has_spec. exists t, x. split; [exact Hin | exact Hid]. }
      by rewrite Hfalse.
  - rewrite docm_get_insert_ne // in Hx.
    have : doc_model_has m d = true.
    { apply docm_has_spec. exists t', x. split; [exact Hx | exact Hid]. }
    by rewrite Hfalse.
Qed.

(** The core chunk-replay: folding [integrate] over one wire item's per-char
    op chain ([ops_from]) is a valid per-char [PendingReplay] at a single type
    [t], provided the head's dependencies are present and every char id is
    fresh. Freshness of char [k>0] follows from the head-freshness plus
    [docm_has_integrate_ne] (the earlier chars only add their own ids). *)
Lemma ops_from_pending_replay (t : TId) (client : nat) (rightOriginId : option YjsId) :
  ∀ (chars : list A) (clock : nat) (originId : option YjsId) (m : DocModel) (arr' : list (YjsItem A)),
    is_Some (m !! t) ->
    (∀ o, originId = Some o -> doc_model_has m o = true) ->
    (∀ o, rightOriginId = Some o -> doc_model_has m o = true) ->
    (∀ j, clock = S j -> doc_model_has m (MkYjsId client j) = true) ->
    (∀ j, (j < length chars)%nat -> doc_model_has m (MkYjsId client (clock + j)) = false) ->
    integrate_all (ops_from client clock originId rightOriginId chars) (doc_model_get m t) = Some arr' ->
    PendingReplay m ((λ op, (t, op)) <$> ops_from client clock originId rightOriginId chars) (<[t := arr']> m).
Proof.
  elim => [| ch rest IH] clock originId m arr' Hsome Hoid Hrid Hpred Hfresh Hint /=.
  - simpl in Hint. injection Hint as <-.
    destruct Hsome as [v Hv].
    have -> : doc_model_get m t = v by rewrite /doc_model_get Hv.
    rewrite insert_id //. constructor.
  - simpl in Hint.
    apply bind_Some in Hint. destruct Hint as (arr0 & Hint0 & Hintr).
    set hop := MkIntegrateInput originId rightOriginId ch (MkYjsId client clock).
    have Hhid : in_id hop = MkYjsId client clock by done.
    have Hfresh0 : doc_model_has m (MkYjsId client clock) = false.
    { have := Hfresh 0%nat ltac:(simpl; lia). rewrite Nat.add_0_r //. }
    have Hready : input_ready m hop = true.
    { apply input_ready_true_of.
      - move=> o Ho. exact (Hoid o Ho).
      - move=> o Ho. exact (Hrid o Ho).
      - move=> k Hk. exact (Hpred k Hk). }
    set m1 := <[t := arr0]> m.
    have Hsome1 : is_Some (m1 !! t). { exists arr0. rewrite /m1 lookup_insert_eq //. }
    have Hhead_in : doc_model_has m1 (MkYjsId client clock) = true.
    { destruct (integrate_new_mem hop (doc_model_get m t) arr0 Hint0) as (it & Hitid & Hitmem).
      apply docm_has_spec. exists t, it. split.
      - rewrite /m1 docm_get_insert_eq. exact Hitmem.
      - rewrite Hitid /hop //. }
    have Hoid1 : ∀ o, Some (MkYjsId client clock) = Some o -> doc_model_has m1 o = true.
    { move=> o [= <-]. exact Hhead_in. }
    have Hrid1 : ∀ o, rightOriginId = Some o -> doc_model_has m1 o = true.
    { move=> o Ho. rewrite /m1. apply (docm_has_integrate_mono m t hop arr0 o Hint0).
      exact (Hrid o Ho). }
    have Hpred1 : ∀ j, S clock = S j -> doc_model_has m1 (MkYjsId client j) = true.
    { move=> j [= <-]. exact Hhead_in. }
    have Hfresh1 : ∀ j, (j < length rest)%nat -> doc_model_has m1 (MkYjsId client (S clock + j)) = false.
    { move=> j Hj.
      have Hfr : doc_model_has m (MkYjsId client (S clock + j)) = false.
      { have := Hfresh (S j) ltac:(simpl; lia). by rewrite -Nat.add_succ_comm. }
      rewrite /m1. apply (docm_has_integrate_ne m t hop arr0 _ Hint0); [| exact Hfr].
      rewrite Hhid. move=> [= Habs]. lia. }
    have Hint1 : integrate_all (ops_from client (S clock) (Some (MkYjsId client clock)) rightOriginId rest)
                   (doc_model_get m1 t) = Some arr'.
    { rewrite /m1 docm_get_insert_eq. exact Hintr. }
    have Hstep := IH (S clock) (Some (MkYjsId client clock)) m1 arr' Hsome1 Hoid1 Hrid1 Hpred1 Hfresh1 Hint1.
    have Hrw : <[t := arr']> m1 = <[t := arr']> m by rewrite /m1 insert_insert_eq.
    rewrite Hrw in Hstep.
    apply (PendingReplay_cons m (t, hop) arr0
             ((λ op, (t, op)) <$> ops_from client (S clock) (Some (MkYjsId client clock)) rightOriginId rest)
             (<[t := arr']> m)).
    + exact Hfresh0.
    + exact Hready.
    + exact Hint0.
    + exact Hstep.
Qed.

(* ===== the public certificate spec (issue #40) ============================ *)

(** An applied struct's target type is nonempty at the final model (its own
    item landed there and membership is monotone) -- what lets the public spec
    mint one [is_root_lb] content certificate per applied struct. *)
Lemma ValidReplay_applied_nonempty
    (l : list (TId * IntegrateInput (A := A))) (m0 m1 : DocModel) :
  ValidReplay l m0 m1 ->
  ∀ typedInput : TId * IntegrateInput (A := A), typedInput ∈ l -> doc_model_get m1 typedInput.1 ≠ [].
Proof.
  elim => [mx | t input rest0 mr arr2 mr' newItem Htoit Hvld Hmax Hglob Hint Hrest IH]
    typedInput Hin.
  - by apply elem_of_nil in Hin.
  - apply elem_of_cons in Hin. destruct Hin as [-> | Hin]; last exact (IH typedInput Hin).
    simpl.
    destruct (integrate_new_mem input _ _ Hint) as (it & Hid & Hit).
    have Hit' : it ∈ doc_model_get mr' t.
    { apply (ValidReplay_mem rest0 (<[t := arr2]> mr) mr' Hrest t).
      rewrite docm_get_insert_eq //. }
    move=> Heq. rewrite Heq in Hit'. by apply elem_of_nil in Hit'.
Qed.

(* ===== NEW lemmas ======================================================== *)

Lemma expand_inputs_cons (typedInput : TId * IntegrateInput (A := A))
    (rest : list (TId * IntegrateInput (A := A))) :
  expand_inputs (typedInput :: rest) = expand_input typedInput ++ expand_inputs rest.
Proof. rewrite /expand_inputs fmap_cons join_cons //. Qed.

(** The [is_Some]-free variant: for a NONEMPTY chunk, the first char's
    integration establishes the key, so no [is_Some (m !! typedInput.1)] hypothesis is
    needed (the origin-less-into-empty-root case, issue #49). *)
Lemma expand_input_pending_replay_ne (m : DocModel) (typedInput : TId * IntegrateInput (A := A))
    (arr' : list (YjsItem A)) :
  (1 <= length (in_content typedInput.2))%nat ->
  input_ready m typedInput.2 = true ->
  (∀ k, (k < length (in_content typedInput.2))%nat ->
     doc_model_has m (MkYjsId (clientId (in_id typedInput.2)) (clock (in_id typedInput.2) + k)) = false) ->
  wire_integrate m typedInput = Some arr' ->
  PendingReplay m (expand_input typedInput) (<[typedInput.1 := arr']> m).
Proof.
  move=> Hne Hready Hfresh Hint.
  rewrite /expand_input /wire_integrate /ops_of_input in Hint *.
  set client := clientId (in_id typedInput.2).
  set idClock := clock (in_id typedInput.2).
  set originId := in_originId typedInput.2.
  set rightOriginId := in_rightOriginId typedInput.2.
  have Hexplen : length (explode (in_content typedInput.2)) = length (in_content typedInput.2)
    by rewrite /explode length_fmap.
  destruct (explode (in_content typedInput.2)) as [| ch rest'] eqn:Hexp.
  { simpl in Hexplen. lia. }
  simpl in Hint.
  set hop := MkIntegrateInput originId rightOriginId ch (MkYjsId client idClock).
  apply bind_Some in Hint. destruct Hint as (arr0 & Hint0 & Hintr).
  have Hhid : in_id hop = MkYjsId client idClock by done.
  have Hfresh0 : doc_model_has m (MkYjsId client idClock) = false.
  { have := Hfresh 0%nat ltac:(lia). rewrite Nat.add_0_r //. }
  have Hready0 : input_ready m hop = true.
  { apply input_ready_true_of.
    - move=> o Ho. apply (proj1 (input_ready_spec m typedInput.2) Hready).
      exact (input_deps_originL typedInput.2 o Ho).
    - move=> o Ho. apply (proj1 (input_ready_spec m typedInput.2) Hready).
      exact (input_deps_originR typedInput.2 o Ho).
    - move=> k Hk. apply (proj1 (input_ready_spec m typedInput.2) Hready).
      rewrite /input_deps !elem_of_app. right. right.
      have Hck : clock (in_id typedInput.2) = S k by exact Hk.
      rewrite Hck /=. apply list_elem_of_singleton. done. }
  set m1 := <[typedInput.1 := arr0]> m.
  have Hsome1 : is_Some (m1 !! typedInput.1). { exists arr0. rewrite /m1 lookup_insert_eq //. }
  have Hhead_in : doc_model_has m1 (MkYjsId client idClock) = true.
  { destruct (integrate_new_mem hop (doc_model_get m typedInput.1) arr0 Hint0) as (it & Hitid & Hitmem).
    apply docm_has_spec. exists typedInput.1, it. split.
    - rewrite /m1 docm_get_insert_eq. exact Hitmem.
    - rewrite Hitid /hop //. }
  have Hpred1 : ∀ j, S idClock = S j -> doc_model_has m1 (MkYjsId client j) = true.
  { move=> j [= <-]. exact Hhead_in. }
  have Hoid1 : ∀ o, Some (MkYjsId client idClock) = Some o -> doc_model_has m1 o = true.
  { move=> o [= <-]. exact Hhead_in. }
  have Hrid1 : ∀ o, rightOriginId = Some o -> doc_model_has m1 o = true.
  { move=> o Ho. rewrite /m1. apply (docm_has_integrate_mono m typedInput.1 hop arr0 o Hint0).
    apply (proj1 (input_ready_spec m typedInput.2) Hready).
    exact (input_deps_originR typedInput.2 o Ho). }
  have Hfresh1 : ∀ j, (j < length rest')%nat -> doc_model_has m1 (MkYjsId client (S idClock + j)) = false.
  { move=> j Hj.
    have Hfr : doc_model_has m (MkYjsId client (S idClock + j)) = false.
    { have Hbnd : (S j < length (in_content typedInput.2))%nat by simpl in Hexplen; lia.
      have := Hfresh (S j) Hbnd. by rewrite -Nat.add_succ_comm. }
    rewrite /m1. apply (docm_has_integrate_ne m typedInput.1 hop arr0 _ Hint0); [| exact Hfr].
    rewrite Hhid. move=> [= Habs]. lia. }
  have Hint1 : integrate_all (ops_from client (S idClock) (Some (MkYjsId client idClock)) rightOriginId rest')
                 (doc_model_get m1 typedInput.1) = Some arr'.
  { rewrite /m1 docm_get_insert_eq. exact Hintr. }
  have Hstep := ops_from_pending_replay typedInput.1 client rightOriginId rest' (S idClock) (Some (MkYjsId client idClock))
                  m1 arr' Hsome1 Hoid1 Hrid1 Hpred1 Hfresh1 Hint1.
  have Hrw : <[typedInput.1 := arr']> m1 = <[typedInput.1 := arr']> m by rewrite /m1 insert_insert_eq.
  rewrite Hrw in Hstep.
  simpl.
  apply (PendingReplay_cons m (typedInput.1, hop) arr0
           ((λ op, (typedInput.1, op)) <$> ops_from client (S idClock) (Some (MkYjsId client idClock)) rightOriginId rest')
           (<[typedInput.1 := arr']> m) Hfresh0 Hready0 Hint0 Hstep).
Qed.

(** From HEAD freshness to WHOLE-CHUNK freshness at a coherent document: the
    item's head is the newest op of its author (its FIRST per-char op, the one
    in the log, via [delivered_clock_bound]), so every char clock >= the head's
    is absent. The multi-char wire op itself is never in the log, so the head
    certificate is taken from the first per-char op. *)
Lemma chunk_fresh_of_head
    (N : gmap ClientId (list Ev)) (c : ClientId) (h : list Ev)
    (m : DocModel) (typedInput : TId * IntegrateInput (A := A)) :
  history_wf N -> N !! c = Some h -> history_state_coh h m ->
  (∀ op : TId * IntegrateInput (A := A), op ∈ expand_input typedInput ->
     op_broadcast N (op.1, OpInsert op.2)) ->
  (1 <= length (in_content typedInput.2))%nat ->
  doc_model_has m (in_id typedInput.2) = false ->
  ∀ k, (k < length (in_content typedInput.2))%nat ->
     doc_model_has m (MkYjsId (clientId (in_id typedInput.2)) (clock (in_id typedInput.2) + k)) = false.
Proof.
  move=> Hwf HNc Hcoh Hcert Hnonempty Hfreshhead.
  have Hidti : in_id typedInput.2 = MkYjsId (clientId (in_id typedInput.2)) (clock (in_id typedInput.2))
    by destruct (in_id typedInput.2).
  have Hlen : length (explode (in_content typedInput.2)) = length (in_content typedInput.2)
    by rewrite /explode length_fmap.
  have [fop Hfop] : is_Some (ops_of_input typedInput.2 (explode (in_content typedInput.2)) !! 0%nat).
  { apply lookup_lt_is_Some_2. rewrite /ops_of_input ops_from_length Hlen. lia. }
  have Hfopid : in_id fop = in_id typedInput.2.
  { have [Hid _] := ops_from_lookup (clientId (in_id typedInput.2)) (clock (in_id typedInput.2))
      (in_originId typedInput.2) (in_rightOriginId typedInput.2) (explode (in_content typedInput.2)) 0%nat fop Hfop.
    rewrite Hid Nat.add_0_r -Hidti //. }
  have Hbcfop : op_broadcast N (typedInput.1, OpInsert fop).
  { have Hmem : (typedInput.1, fop) ∈ expand_input typedInput.
    { apply (list_elem_of_lookup_2 _ 0%nat). by apply expand_input_lookup. }
    exact (Hcert (typedInput.1, fop) Hmem). }
  have Hfreshfop : doc_model_has m (in_id fop) = false by rewrite Hfopid.
  have Hnotdel : in_id fop ∉ delivered_ids h.
  { move=> Hdel. apply elem_of_delivered_ids in Hdel. destruct Hdel as (y & Hyh & Hyid).
    have Hins : ∃ inputy, y.2 = OpInsert inputy.
    { apply (hwf_insert_only N Hwf c y). right. rewrite (to_histories_lookup N c h HNc) //. }
    destruct Hins as (inputy & Hy2). destruct y as [ty y2]. simpl in Hy2. subst y2.
    have Hdel2 : (ty, OpInsert inputy) ∈ delivered_ops h by apply elem_of_delivered_ops_ev.
    have := delivered_docm_has h m ty inputy Hcoh Hdel2.
    have -> : in_id inputy = in_id fop by exact Hyid.
    rewrite Hfreshfop //. }
  have Hclk := delivered_clock_bound N c h m ((typedInput.1, OpInsert fop) : Op) Hwf HNc Hcoh Hbcfop Hnotdel.
  move=> k Hk.
  destruct (doc_model_has m (MkYjsId (clientId (in_id typedInput.2)) (clock (in_id typedInput.2) + k))) eqn:Hh;
    [| done].
  exfalso. apply docm_has_spec in Hh. destruct Hh as (t' & x & Hx & Hxid).
  have Hcc : clientId (item_id x) = clientId (in_id fop).
  { rewrite Hxid /=. rewrite Hfopid //. }
  have Hlt := Hclk t' x Hx Hcc.
  rewrite Hxid /= in Hlt.
  change (DocOp_id (typedInput.1, OpInsert fop)) with (in_id fop) in Hlt.
  rewrite Hfopid /= in Hlt. lia.
Qed.

(** THE CRUX: a wire drain refines a per-char [PendingReplay] of its
    expansion. Chunk freshness at each intermediate is RE-DERIVED from the
    head's freshness via [chunk_fresh_of_head], keeping the
    intermediate coherent via [pending_ValidReplay]; no batch range-disjointness
    is needed. *)
Lemma WireReplay_to_PendingReplay
    (m0 : DocModel) (applied : list (TId * IntegrateInput (A := A))) (m0' : DocModel)
    (HWR : WireReplay m0 applied m0') :
  ∀ (N : gmap ClientId (list Ev)) (c : ClientId) (h : list Ev),
    history_wf N -> N !! c = Some h -> history_state_coh h m0 ->
    (∀ t : TId, YjsArrInvariant (doc_model_get m0 t)) ->
    (∀ (typedInput : TId * IntegrateInput (A := A)) (op : TId * IntegrateInput (A := A)),
       typedInput ∈ applied -> op ∈ expand_input typedInput ->
       op_broadcast N (op.1, OpInsert op.2)) ->
    (∀ typedInput : TId * IntegrateInput (A := A), typedInput ∈ applied ->
       (1 <= length (in_content typedInput.2))%nat) ->
    PendingReplay m0 (expand_inputs applied) m0'.
Proof.
  elim: HWR => [mx | mx typedInput arr' rest mx' Hdup Hready Hint Hrest IH]
    N c h Hwf HNc Hcoh Harrinv Hcharcert Hnonempty.
  - rewrite /expand_inputs /=. constructor.
  - have Hin_ti : typedInput ∈ typedInput :: rest by left.
    have Hne := Hnonempty typedInput Hin_ti.
    have Hfresh := chunk_fresh_of_head N c h mx typedInput Hwf HNc Hcoh
                     (λ op Hop, Hcharcert typedInput op Hin_ti Hop) Hne Hdup.
    have Hpr1 : PendingReplay mx (expand_input typedInput) (<[typedInput.1 := arr']> mx)
      := expand_input_pending_replay_ne mx typedInput arr' Hne Hready Hfresh Hint.
    (* coherence at mx1 via pending_ValidReplay on the chunk *)
    have Hcharcert_ti : ∀ op : TId * IntegrateInput (A := A), op ∈ expand_input typedInput ->
        op_broadcast N (op.1, OpInsert op.2) := λ op Hop, Hcharcert typedInput op Hin_ti Hop.
    pose proof (pending_ValidReplay N c h mx (expand_input typedInput) (<[typedInput.1 := arr']> mx)
                  Hwf HNc Hcoh Hcharcert_ti Hpr1) as (Hvr1 & Hcoh1 & Hwf1 & _).
    set N' := <[c := h ++ (deliver_ev <$> expand_input typedInput)]> N.
    set h' := h ++ (deliver_ev <$> expand_input typedInput).
    have HN'c : N' !! c = Some h' by rewrite /N' lookup_insert_eq.
    have Harrinv1 : ∀ t : TId, YjsArrInvariant (doc_model_get (<[typedInput.1 := arr']> mx) t)
      := ValidReplay_arrinv (expand_input typedInput) mx (<[typedInput.1 := arr']> mx) Hvr1 Harrinv.
    have Hcharcert' : ∀ (typedInput2 : TId * IntegrateInput (A := A)) (op : TId * IntegrateInput (A := A)),
        typedInput2 ∈ rest -> op ∈ expand_input typedInput2 -> op_broadcast N' (op.1, OpInsert op.2).
    { move=> typedInput2 op Htj Hop. apply (proj2 (op_broadcast_append N c h _ _ HNc)). left.
      apply (Hcharcert typedInput2 op); [by right | done]. }
    have Hnonempty' : ∀ typedInput2 : TId * IntegrateInput (A := A), typedInput2 ∈ rest ->
        (1 <= length (in_content typedInput2.2))%nat.
    { move=> typedInput2 Htj. apply Hnonempty. by right. }
    have Hpr2 := IH N' c h' Hwf1 HN'c Hcoh1 Harrinv1 Hcharcert' Hnonempty'.
    rewrite expand_inputs_cons.
    exact (PendingReplay_app mx (<[typedInput.1 := arr']> mx) mx' _ _ Hpr1 Hpr2).
Qed.

(** Chunk-integration totality: a certified, fresh, ready per-char chain
    integrates fully at a coherent document. Mirrors [ops_from_pending_replay]
    (same freshness cascade) but PRODUCES [is_Some] of the fold, deriving each
    char's [integrate] via [docm_valid_from_deps] + [delivered_clock_bound] +
    [integrate_some_of_toItem] at the coherence advanced along the chunk. *)
Lemma ops_from_ready (t : TId) (client : nat) (rightOriginId : option YjsId) :
  ∀ (chars : list A) (startClock : nat) (originId : option YjsId)
    (N : gmap ClientId (list Ev)) (c : ClientId) (h : list Ev) (m : DocModel),
    history_wf N -> N !! c = Some h -> history_state_coh h m ->
    (∀ t' : TId, YjsArrInvariant (doc_model_get m t')) ->
    (∀ o, originId = Some o -> doc_model_has m o = true) ->
    (∀ o, rightOriginId = Some o -> doc_model_has m o = true) ->
    (∀ j, startClock = S j -> doc_model_has m (MkYjsId client j) = true) ->
    (∀ j, (j < length chars)%nat -> doc_model_has m (MkYjsId client (startClock + j)) = false) ->
    (∀ k op, ops_from client startClock originId rightOriginId chars !! k = Some op ->
       op_broadcast N (t, OpInsert op)) ->
    is_Some (integrate_all (ops_from client startClock originId rightOriginId chars) (doc_model_get m t)).
Proof.
  elim => [| ch rest IH] startClock originId N c h m Hwf HNc Hcoh Hinvs Hoid Hrid Hpred Hfresh Hcert /=.
  - by eexists.
  - set hop := MkIntegrateInput originId rightOriginId ch (MkYjsId client startClock).
    have Hbc : op_broadcast N (t, OpInsert hop).
    { apply (Hcert 0%nat hop). done. }
    (* origins arrive as delivered ops *)
    have Harrive : ∀ o : YjsId, (in_originId hop = Some o ∨ in_rightOriginId hop = Some o) ->
        ∃ (t' : TId) (x : IntegrateInput (A := A)),
          (t', OpInsert x) ∈ delivered_ops h ∧ in_id x = o.
    { move=> o Ho.
      have Hhas : doc_model_has m o = true.
      { destruct Ho as [Ho | Ho]; simpl in Ho; [exact (Hoid o Ho) | exact (Hrid o Ho)]. }
      apply docm_has_spec in Hhas. destruct Hhas as (t' & x & Hx & Hxid).
      destruct (docm_mem_delivered h m t' x Hcoh Hx) as (xin & Hxdel & Hxinid).
      exists t', xin. split; [exact Hxdel | by rewrite Hxinid Hxid]. }
    have Hval := docm_valid_from_deps N c h m t hop Hwf HNc Hcoh Hbc Harrive.
    destruct Hval as (it0 & Htoit & Hvld).
    (* head fresh -> not delivered -> maximalId *)
    have Hfresh0 : doc_model_has m (MkYjsId client startClock) = false.
    { have := Hfresh 0%nat ltac:(simpl; lia). rewrite Nat.add_0_r //. }
    have Hnotdel : in_id hop ∉ delivered_ids h.
    { move=> Hdel. apply elem_of_delivered_ids in Hdel. destruct Hdel as (y & Hyh & Hyid).
      have Hins : ∃ inputy, y.2 = OpInsert inputy.
      { apply (hwf_insert_only N Hwf c y). right. rewrite (to_histories_lookup N c h HNc) //. }
      destruct Hins as (inputy & Hy2). destruct y as [ty y2]. simpl in Hy2. subst y2.
      have Hdel2 : (ty, OpInsert inputy) ∈ delivered_ops h by apply elem_of_delivered_ops_ev.
      have := delivered_docm_has h m ty inputy Hcoh Hdel2.
      have -> : in_id inputy = in_id hop by exact Hyid.
      have -> : in_id hop = MkYjsId client startClock by done. rewrite Hfresh0 //. }
    have Hclk := delivered_clock_bound N c h m ((t, OpInsert hop) : Op) Hwf HNc Hcoh Hbc Hnotdel.
    have Hmax : maximalId it0 (doc_model_get m t).
    { move=> x Hx Hcx.
      rewrite (toItem_id hop (doc_model_get m t) it0 Htoit).
      have Heq : clock (in_id hop) = clock (DocOp_id ((t, OpInsert hop) : Op)) by done.
      rewrite Heq. apply (Hclk t x Hx).
      rewrite (toItem_id hop (doc_model_get m t) it0 Htoit) in Hcx.
      have -> : clientId (DocOp_id ((t, OpInsert hop) : Op)) = clientId (in_id hop) by done.
      exact Hcx. }
    have Hintsome := integrate_some_of_toItem hop (doc_model_get m t) it0 (Hinvs t) Htoit Hvld Hmax.
    destruct (Hintsome _) as [arr0 Hint0].
    (* advance coherence along the head via pending_ValidReplay of the singleton *)
    have Hready0 : input_ready m hop = true.
    { apply input_ready_true_of.
      - move=> o Ho. apply (Hoid o Ho).
      - move=> o Ho. apply (Hrid o Ho).
      - move=> k Hk. exact (Hpred k Hk). }
    have Hpr : PendingReplay m [(t, hop)] (<[t := arr0]> m).
    { apply (PendingReplay_cons m (t, hop) arr0 [] (<[t := arr0]> m) Hfresh0 Hready0 Hint0).
      constructor. }
    have Hcerthead : ∀ op : TId * IntegrateInput (A := A), op ∈ [(t, hop)] ->
        op_broadcast N (op.1, OpInsert op.2).
    { move=> op Hop. apply list_elem_of_singleton in Hop. subst op. exact Hbc. }
    pose proof (pending_ValidReplay N c h m [(t, hop)] (<[t := arr0]> m)
                  Hwf HNc Hcoh Hcerthead Hpr) as (Hvr1 & Hcoh1 & Hwf1 & _).
    set N' := <[c := h ++ (deliver_ev <$> [(t, hop)])]> N.
    set h' := h ++ (deliver_ev <$> [(t, hop)]).
    have HN'c : N' !! c = Some h' by rewrite /N' lookup_insert_eq.
    set m1 := <[t := arr0]> m.
    have Hgett : doc_model_get m1 t = arr0 by rewrite /m1 docm_get_insert_eq.
    have Hinvs1 : ∀ t' : TId, YjsArrInvariant (doc_model_get m1 t').
    { move=> t'. exact (ValidReplay_arrinv [(t, hop)] m m1 Hvr1 Hinvs t'). }
    (* head now present *)
    have Hhead_in : doc_model_has m1 (MkYjsId client startClock) = true.
    { destruct (integrate_new_mem hop (doc_model_get m t) arr0 Hint0) as (itn & Hitid & Hitmem).
      apply docm_has_spec. exists t, itn. split.
      - rewrite Hgett. exact Hitmem.
      - rewrite Hitid //. }
    have Hoid1 : ∀ o, Some (MkYjsId client startClock) = Some o -> doc_model_has m1 o = true.
    { move=> o [= <-]. exact Hhead_in. }
    have Hrid1 : ∀ o, rightOriginId = Some o -> doc_model_has m1 o = true.
    { move=> o Ho. rewrite /m1. apply (docm_has_integrate_mono m t hop arr0 o Hint0).
      exact (Hrid o Ho). }
    have Hpred1 : ∀ j, S startClock = S j -> doc_model_has m1 (MkYjsId client j) = true.
    { move=> j [= <-]. exact Hhead_in. }
    have Hfresh1 : ∀ j, (j < length rest)%nat -> doc_model_has m1 (MkYjsId client (S startClock + j)) = false.
    { move=> j Hj.
      have Hfr : doc_model_has m (MkYjsId client (S startClock + j)) = false.
      { have := Hfresh (S j) ltac:(simpl; lia). by rewrite -Nat.add_succ_comm. }
      rewrite /m1. apply (docm_has_integrate_ne m t hop arr0 _ Hint0); [| exact Hfr].
      have -> : in_id hop = MkYjsId client startClock by done. move=> [= Habs]. lia. }
    have Hcert1 : ∀ k op, ops_from client (S startClock) (Some (MkYjsId client startClock)) rightOriginId rest !! k = Some op ->
        op_broadcast N' (t, OpInsert op).
    { move=> k op Hk. apply (proj2 (op_broadcast_append N c h _ _ HNc)). left.
      apply (Hcert (S k) op). simpl. exact Hk. }
    have Hrec := IH (S startClock) (Some (MkYjsId client startClock)) N' c h' m1
                   Hwf1 HN'c Hcoh1 Hinvs1 Hoid1 Hrid1 Hpred1 Hfresh1 Hcert1.
    rewrite Hgett in Hrec. destruct Hrec as [arr' Hia].
    exists arr'. rewrite Hint0 /=. exact Hia.
Qed.

(** A fresh, ready, certified wire item integrates its whole chunk at a
    coherent document (the ready-but-stuck branch never fires). Chunk freshness
    is derived from head freshness ([delivered_clock_bound]); head origins and
    the own-predecessor gate come from [input_ready]. *)
Lemma wire_integrate_some_of_certs
    (N : gmap ClientId (list Ev)) (c : ClientId) (h : list Ev)
    (m : DocModel) (typedInput : TId * IntegrateInput (A := A)) :
  history_wf N -> N !! c = Some h -> history_state_coh h m ->
  (∀ t' : TId, YjsArrInvariant (doc_model_get m t')) ->
  (∀ op : TId * IntegrateInput (A := A), op ∈ expand_input typedInput ->
     op_broadcast N (op.1, OpInsert op.2)) ->
  (1 <= length (in_content typedInput.2))%nat ->
  input_ready m typedInput.2 = true ->
  doc_model_has m (in_id typedInput.2) = false ->
  is_Some (wire_integrate m typedInput).
Proof.
  move=> Hwf HNc Hcoh Hinvs Hcert Hnonempty Hready Hfreshhead.
  rewrite /wire_integrate /ops_of_input.
  have Hlen : length (explode (in_content typedInput.2)) = length (in_content typedInput.2)
    by rewrite /explode length_fmap.
  have Hfresh := chunk_fresh_of_head N c h m typedInput Hwf HNc Hcoh Hcert Hnonempty Hfreshhead.
  apply (ops_from_ready typedInput.1 (clientId (in_id typedInput.2)) (in_rightOriginId typedInput.2)
           (explode (in_content typedInput.2)) (clock (in_id typedInput.2)) (in_originId typedInput.2)
           N c h m Hwf HNc Hcoh Hinvs).
  - move=> o Ho. apply (proj1 (input_ready_spec m typedInput.2) Hready).
    exact (input_deps_originL typedInput.2 o Ho).
  - move=> o Ho. apply (proj1 (input_ready_spec m typedInput.2) Hready).
    exact (input_deps_originR typedInput.2 o Ho).
  - move=> j Hj. apply (proj1 (input_ready_spec m typedInput.2) Hready).
    rewrite /input_deps !elem_of_app. right. right. rewrite Hj /=.
    apply list_elem_of_singleton. done.
  - move=> j Hj. apply Hfresh. rewrite -Hlen. exact Hj.
  - move=> k op Hk.
    have Hmem : (typedInput.1, op) ∈ expand_input typedInput.
    { apply (list_elem_of_lookup_2 _ k). by apply expand_input_lookup. }
    exact (Hcert (typedInput.1, op) Hmem).
Qed.

(** [wire_ready_total] from the certificates: mirrors
    [pending_ready_total_of_certs] but for whole chunks. At any wire-drain
    prefix [mx], [WireReplay_to_PendingReplay] + [pending_ValidReplay] give
    coherence at [mx], and then [wire_integrate_some_of_certs] fires. *)
Lemma wire_ready_total_of_certs
    (N : gmap ClientId (list Ev)) (c : ClientId) (h : list Ev) (m : DocModel)
    (pending applied : list (TId * IntegrateInput (A := A))) :
  history_wf N -> N !! c = Some h -> history_state_coh h m ->
  (∀ t' : TId, YjsArrInvariant (doc_model_get m t')) ->
  (∀ (typedInput : TId * IntegrateInput (A := A)) (op : TId * IntegrateInput (A := A)),
     typedInput ∈ pending -> op ∈ expand_input typedInput -> op_broadcast N (op.1, OpInsert op.2)) ->
  (∀ typedInput : TId * IntegrateInput (A := A), typedInput ∈ pending ->
     (1 <= length (in_content typedInput.2))%nat) ->
  (∀ typedInput : TId * IntegrateInput (A := A), typedInput ∈ applied -> typedInput ∈ pending) ->
  wire_ready_total m pending applied.
Proof.
  move=> Hwf HNc Hcoh Hinvs Hcharcert Hnonempty Happsub.
  move=> pre suf mx typedInput Heq HWRpre Hin Hfresh Hready.
  have Hpresub : ∀ typedInput2 : TId * IntegrateInput (A := A), typedInput2 ∈ pre -> typedInput2 ∈ pending.
  { move=> typedInput2 Htj. apply Happsub. rewrite Heq elem_of_app. by left. }
  have Hpr := WireReplay_to_PendingReplay m pre mx HWRpre N c h Hwf HNc Hcoh Hinvs
                (λ typedInput2 op Htj Hop, Hcharcert typedInput2 op (Hpresub typedInput2 Htj) Hop)
                (λ typedInput2 Htj, Hnonempty typedInput2 (Hpresub typedInput2 Htj)).
  have Hcharcertpre : ∀ op : TId * IntegrateInput (A := A), op ∈ expand_inputs pre ->
      op_broadcast N (op.1, OpInsert op.2).
  { move=> op Hop.
    rewrite /expand_inputs list_elem_of_join in Hop.
    destruct Hop as (l & Hl & Hopl).
    rewrite list_elem_of_fmap in Hopl. destruct Hopl as (typedInput2 & -> & Htj).
    exact (Hcharcert typedInput2 op (Hpresub typedInput2 Htj) Hl). }
  pose proof (pending_ValidReplay N c h m (expand_inputs pre) mx Hwf HNc Hcoh Hcharcertpre Hpr)
    as (Hvrpre & Hcohmx & Hwfmx & _).
  set N' := <[c := h ++ (deliver_ev <$> expand_inputs pre)]> N.
  set h' := h ++ (deliver_ev <$> expand_inputs pre).
  have HN'c : N' !! c = Some h' by rewrite /N' lookup_insert_eq.
  have Hinvsmx : ∀ t' : TId, YjsArrInvariant (doc_model_get mx t').
  { move=> t'. exact (ValidReplay_arrinv (expand_inputs pre) m mx Hvrpre Hinvs t'). }
  have Hcertti : ∀ op : TId * IntegrateInput (A := A), op ∈ expand_input typedInput ->
      op_broadcast N' (op.1, OpInsert op.2).
  { move=> op Hop. apply (proj2 (op_broadcast_append N c h _ _ HNc)). left.
    exact (Hcharcert typedInput op Hin Hop). }
  exact (wire_integrate_some_of_certs N' c h' mx typedInput Hwfmx HN'c Hcohmx Hinvsmx
           Hcertti (Hnonempty typedInput Hin) Hready Hfresh).
Qed.

(** Per-char [op_broadcast] of a wire pending, extracted from the ghost history:
    the log holds one certificate per CHARACTER, so [is_pending_certified] over
    [expand_inputs pending] yields [op_broadcast] for each per-char op (hence for
    each op of any [expand_input typedInput], [typedInput ∈ pending]). Shared preamble for the
    two wire wrappers below. *)
Local Lemma wire_pending_op_broadcast (γh : history_names)
    (N : gmap ClientId (list Ev)) (ops : gmap YjsId Op)
    (pending : list (TId * IntegrateInput (A := A))) :
  ops_coh N ops ->
  ([∗ list] op ∈ expand_inputs pending, is_op_cert γh (op.1, OpInsert op.2)) -∗
  ghost_map_auth γh.(hn_ops) 1 ops -∗
  ⌜∀ (typedInput op : TId * IntegrateInput (A := A)), typedInput ∈ pending -> op ∈ expand_input typedInput ->
     op_broadcast N (op.1, OpInsert op.2)⌝.
Proof.
  iIntros (Hopscoh) "#Hcertsin HopsAuth".
  iAssert (⌜∀ op : TId * IntegrateInput (A := A), op ∈ expand_inputs pending ->
             ops !! (in_id op.2) = Some ((op.1, OpInsert op.2) : Op)⌝)%I as %Hlk.
  { iIntros (op Hin).
    destruct (list_elem_of_lookup_1 _ _ Hin) as (i & Hi).
    iDestruct (big_sepL_lookup _ _ i with "Hcertsin") as "Hc"; [exact Hi |].
    iApply (ghost_map_lookup with "HopsAuth Hc"). }
  iPureIntro. move=> typedInput op Hti Hop.
  have Hin : op ∈ expand_inputs pending.
  { rewrite /expand_inputs. apply list_elem_of_join.
    exists (expand_input typedInput). split; [exact Hop | by apply list_elem_of_fmap_2]. }
  destruct Hopscoh as [Hc1 _].
  have [_ Hreg] := Hc1 _ _ (Hlk op Hin).
  exists (clientId (DocOp_id ((op.1, OpInsert op.2) : Op))). exact Hreg.
Qed.

(** [wire_ready_total] from the ghost history (issue #40 x n-char): opens the
    invariant read-only, gets the per-char [op_broadcast] and hands them to the
    pure [wire_ready_total_of_certs]. Mirrors the per-char
    [pending_ready_total_of_certs] gate in [network_model]. *)
Lemma history_wire_ready_total γh (c : ClientId) h (m : DocModel)
    (pending applied : list (TId * IntegrateInput (A := A))) E :
  ↑histN ⊆ E ->
  history_state_coh h m ->
  (∀ t : TId, YjsArrInvariant (doc_model_get m t)) ->
  (∀ typedInput : TId * IntegrateInput (A := A), typedInput ∈ pending ->
     (1 <= length (in_content typedInput.2))%nat) ->
  (∀ typedInput : TId * IntegrateInput (A := A), typedInput ∈ applied -> typedInput ∈ pending) ->
  is_history (A := A) (P := P) γh -∗ own_client_history γh c h -∗
  is_pending_certified γh (expand_inputs pending) ={E}=∗
    own_client_history γh c h ∗ ⌜wire_ready_total m pending applied⌝.
Proof.
  iIntros (HE Hcoh Hinvs Hnonempty Happsub) "#Hinv Hown #Hcertsin".
  iInv "Hinv" as ">H" "Hclose". iNamed "H".
  iDestruct (hist_auth_elem_lookup with "HhistAuth Hown") as %HNc.
  iDestruct (wire_pending_op_broadcast γh N ops pending Hopscoh with "Hcertsin HopsAuth") as %Hcharcert.
  have Hrt := wire_ready_total_of_certs N c h m pending applied Hwf HNc Hcoh
                Hinvs Hcharcert Hnonempty Happsub.
  iMod ("Hclose" with "[HhistAuth HopsAuth]") as "_".
  { iNext. iExists _, _. iFrame "HhistAuth HopsAuth Hcerts".
    iPureIntro. split; [exact Hwf | exact Hopscoh]. }
  iModIntro. iFrame "Hown". iPureIntro. exact Hrt.
Qed.

(** Delivering a whole wire drain (issue #40 x n-char): the applied wire items,
    expanded per char, are a valid replay; the client's ghost history advances by
    [deliver_ev <$> expand_inputs applied]. Mirrors [history_deliver_pending] but
    goes through the wire bridge [wire_drain_replay] + [WireReplay_to_PendingReplay]
    + [pending_ValidReplay]; the drain equation is only used for [wire_drain_subset]
    / [wire_drain_replay], never an atomicity lemma. *)
Lemma history_deliver_wire γh (c : ClientId) h (m : DocModel)
    (pending applied rest : list (TId * IntegrateInput (A := A))) (m' : DocModel) E :
  ↑histN ⊆ E ->
  wire_drain m pending = (applied, rest, m') ->
  history_state_coh h m ->
  (∀ t : TId, YjsArrInvariant (doc_model_get m t)) ->
  (∀ typedInput : TId * IntegrateInput (A := A), typedInput ∈ pending ->
     (1 <= length (in_content typedInput.2))%nat) ->
  is_history (A := A) (P := P) γh -∗ own_client_history γh c h -∗
  is_pending_certified γh (expand_inputs pending) ={E}=∗
    own_client_history γh c (h ++ (deliver_ev <$> expand_inputs applied)) ∗
    is_history_lb γh c (h ++ (deliver_ev <$> expand_inputs applied)) ∗
    ⌜ValidReplay (expand_inputs applied) m m'⌝ ∗
    ⌜history_state_coh (h ++ (deliver_ev <$> expand_inputs applied)) m'⌝ ∗
    ⌜inputs_not_from (expand_inputs applied) c⌝.
Proof.
  iIntros (HE Hdrain Hcoh Hinvs Hnonempty) "#Hinv Hown #Hcertsin".
  iInv "Hinv" as ">H" "Hclose". iNamed "H".
  iDestruct (hist_auth_elem_lookup with "HhistAuth Hown") as %HNc.
  iDestruct (wire_pending_op_broadcast γh N ops pending Hopscoh with "Hcertsin HopsAuth") as %Hcharcert.
  have Happsub := proj1 (wire_drain_subset m pending applied rest m' Hdrain).
  have HWR := wire_drain_replay m pending applied rest m' Hdrain.
  have Hcharcertapp : ∀ (typedInput op : TId * IntegrateInput (A := A)), typedInput ∈ applied ->
      op ∈ expand_input typedInput -> op_broadcast N (op.1, OpInsert op.2)
    := λ typedInput op Hti Hop, Hcharcert typedInput op (Happsub typedInput Hti) Hop.
  have Hnonemptyapp : ∀ typedInput : TId * IntegrateInput (A := A), typedInput ∈ applied ->
      (1 <= length (in_content typedInput.2))%nat := λ typedInput Hti, Hnonempty typedInput (Happsub typedInput Hti).
  have Hpr := WireReplay_to_PendingReplay m applied m' HWR N c h Hwf HNc Hcoh Hinvs
                Hcharcertapp Hnonemptyapp.
  have Hbcapp : ∀ op : TId * IntegrateInput (A := A), op ∈ expand_inputs applied ->
      op_broadcast N (op.1, OpInsert op.2).
  { move=> op Hin.
    rewrite /expand_inputs list_elem_of_join in Hin. destruct Hin as (l & Hl & Hll).
    rewrite list_elem_of_fmap in Hll. destruct Hll as (typedInput & -> & Hti).
    exact (Hcharcert typedInput op (Happsub typedInput Hti) Hl). }
  pose proof (pending_ValidReplay N c h m (expand_inputs applied) m' Hwf HNc Hcoh Hbcapp Hpr)
    as (Hvr & Hcoh' & Hwf' & Hnoc).
  iMod (hist_auth_elem_advance γh N c h (deliver_ev <$> expand_inputs applied)
          HNc with "HhistAuth Hown") as "(HhistAuth & Hown & #Hlb)".
  iMod ("Hclose" with "[HhistAuth HopsAuth]") as "_".
  { iNext. iExists _, _. iFrame "HhistAuth HopsAuth Hcerts".
    iPureIntro. split; [exact Hwf' |].
    apply (ops_coh_deliver_tail N c h ops _ Hwf HNc); [| exact Hopscoh].
    move=> e He. move: He. rewrite list_elem_of_fmap.
    move=> [typedInput [Heq _]]. rewrite /deliver_ev in Heq. discriminate. }
  iModIntro. iFrame "Hown Hlb".
  iPureIntro. split_and!; [exact Hvr | exact Hcoh' | exact Hnoc].
Qed.

(** Each decoded wire item carries a nonempty run ([is_update_item]'s
    [Hunonempty]); the [applyUpdate] drain loop needs this per-item bound on the
    whole [pend ++ inputs]. Preserves the resource (the fact rides the persistent
    [is_update_item]s). *)
Lemma own_update_structs_nonempty (sl : slice.t) (dq : dfrac)
    (inputs : list (TId * IntegrateInput (A := A))) :
  own_update_structs sl dq inputs -∗ own_update_structs sl dq inputs ∗
    ⌜∀ typedInput : TId * IntegrateInput (A := A), typedInput ∈ inputs ->
       (1 <= length (in_content typedInput.2))%nat⌝.
Proof.
  iIntros "H". iDestruct "H" as (uivs) "(Hsl & Hcap & #Hitems)".
  iAssert (⌜∀ typedInput : TId * IntegrateInput (A := A), typedInput ∈ inputs ->
             (1 <= length (in_content typedInput.2))%nat⌝)%I as %Hnem.
  { iIntros (typedInput Hin). destruct (list_elem_of_lookup_1 _ _ Hin) as (i & Hi).
    iDestruct (big_sepL2_lookup_r _ _ _ i with "Hitems") as (updateItemVal Huiv) "Hit"; [exact Hi |].
    iNamed "Hit". iPureIntro. rewrite -Hin_c. exact Hunonempty. }
  iSplitR ""; [iExists uivs; iFrame "Hsl Hcap Hitems" | done].
Qed.

(** Every applied wire item's target root is nonempty at [m'] (its first char
    landed there): the head of its [expand_input] is in [expand_inputs applied]
    and carries the item's [TId], so [ValidReplay_applied_nonempty] on the
    expansion pins [doc_model_get m' typedInput.1 ≠ []]. *)
Lemma applied_root_nonempty
    (applied : list (TId * IntegrateInput (A := A))) (m m' : DocModel)
    (typedInput : TId * IntegrateInput (A := A)) :
  ValidReplay (expand_inputs applied) m m' ->
  typedInput ∈ applied ->
  (1 <= length (in_content typedInput.2))%nat ->
  doc_model_get m' typedInput.1 ≠ [].
Proof.
  move=> Hvr Hin Hne.
  have [fop Hfop] : is_Some (ops_of_input typedInput.2 (explode (in_content typedInput.2)) !! 0%nat).
  { apply lookup_lt_is_Some_2. rewrite /ops_of_input ops_from_length /explode length_fmap. lia. }
  have Hmem : (typedInput.1, fop) ∈ expand_inputs applied.
  { rewrite /expand_inputs. apply list_elem_of_join.
    exists (expand_input typedInput). split; [| by apply list_elem_of_fmap_2].
    apply (list_elem_of_lookup_2 _ 0%nat). by apply expand_input_lookup. }
  exact (ValidReplay_applied_nonempty (expand_inputs applied) m m' Hvr (typedInput.1, fop) Hmem).
Qed.

(** [input_accounted] at the id level: an accounted input's id is either in the
    delivered-id set of [h'] or in the pending-id set of [rest]. This is what
    lets [applyUpdate] both re-establish [accepted_coh] and mint the receipts. *)
Lemma input_accounted_id (h' : list Ev)
    (rest : list (TId * IntegrateInput (A := A))) (x : TId * IntegrateInput (A := A)) :
  input_accounted h' rest x -> in_id x.2 ∈ delivered_ids h' ∪ pending_id_set rest.
Proof.
  move=> [[t [input [Hdel Hid]]] | [y [Hy Hid]]].
  - apply elem_of_union_l, elem_of_delivered_ids.
    exists (t, OpInsert input). split; [by apply elem_of_delivered_ops_ev | by rewrite -Hid].
  - apply elem_of_union_r, elem_of_pending_id_set. by exists y.
Qed.

(** [applyUpdate], the PUBLIC certificate spec (issue #40): the whole store
    state is ONE [own_store] before and after. The incoming batch carries its
    persistent certificates and its rooted-head witnesses; there is NO
    causal-order assumption, not even within the batch, and no state-vector
    tracking -- the heap drains the pending buffer plus the batch to the
    structural-dependency fixpoint. [wire_drain] names the applied list, the
    new pending buffer and the final model; the delivery's pure content is
    [ValidReplay applied m m'] (which determines [m']), every applied struct
    is foreign (a replica never receives its own insert back before minting
    the next one: per-author FIFO), and each applied struct yields one
    monotone content certificate [is_root_lb] at its root's full
    post-delivery item set. Finally, the batch is not lost: every input is
    accounted for ([input_accounted]) -- delivered into the new history or
    buffered by id in the new pending [rest] -- so nothing silently vanishes. *)
Lemma wp_store__applyUpdate (s_loc : loc) (sl : slice.t) (dq : dfrac)
    (γs : store_names) (γh : history_names)
    (c : ClientId) (h : list Ev) (m : DocModel)
    (pend inputs : list (TId * IntegrateInput (A := A))) :
  update_wf inputs ->
  {{{ is_pkg_init yjs ∗ is_history (A := A) (P := P) γh ∗
      own_store s_loc γs γh c h m pend ∗
      own_update_structs sl dq inputs ∗
      is_pending_certified γh (expand_inputs inputs) }}}
    s_loc @! (go.PointerType yjs.store) @! "applyUpdate" #sl
  {{{ (applied rest : list (TId * IntegrateInput (A := A))) (m' : DocModel),
      RET #();
      own_update_structs sl dq inputs ∗
      own_store s_loc γs γh c (h ++ (deliver_ev <$> expand_inputs applied)) m' rest ∗
      is_history_lb γh c (h ++ (deliver_ev <$> expand_inputs applied)) ∗
      ⌜wire_drain m (pend ++ inputs) = (applied, rest, m')⌝ ∗
      ⌜ValidReplay (expand_inputs applied) m m'⌝ ∗
      ⌜∀ x, x ∈ inputs ->
         input_accounted (h ++ (deliver_ev <$> expand_inputs applied)) rest x⌝ ∗
      is_applied_certs γs applied m' }}}.
Proof using Type*.
  move=> [Hnowrapb Hrooted].
  iIntros (Φ) "(#Hpkg & #Hishist & Hstore & Hupd & #Hcertsin) HΦ".
  iNamed "Hstore".
  iDestruct "Hcells" as "(Hfields0 & %Hinvs0)".
  have Hrpi : run_pool_invs p := proj1 Hinvs0.
  have Hreg : pool_registry_coh bind p := proj2 Hinvs0.
  iDestruct "Hfields0" as "(Hclient & Hclock & HdeletedSet & Hitems & Hregistry & Htypes & Hpending & Hpdeletes)".
  iDestruct "Hpending" as (pend_sl) "(Hpendf & Hpend)".
  have [Hbindtypes [Hbindinj Htypesbound]] := Hreg.
  have [Hmtypes Hmdom] := Hregmodel.
  iDestruct (own_type_pool_runs_arr_inv with "Htypes") as %Htsinv.
  have Harrinv : ∀ t : TId, YjsArrInvariant (doc_model_get m t).
  { move=> t. destruct (doc_model_get m t) as [|x l] eqn:Hdg.
    - exact YjsArrInvariant_empty.
    - rewrite -Hdg.
      have Hne : doc_model_get m t ≠ [] by rewrite Hdg.
      destruct (Hmdom t Hne) as (nm & q & -> & Hbnm).
      destruct (Hbindtypes nm q Hbnm) as [tm Htm].
      rewrite (Hmtypes nm q tm Hbnm Htm). exact (Htsinv q tm Htm). }
  (* per-item content nonemptiness of the whole drained pending, from the heap *)
  iDestruct (own_update_structs_nonempty with "Hupd") as "[Hupd %Hnem_in]".
  iDestruct (own_update_structs_nonempty with "Hpend") as "[Hpend %Hnem_pd]".
  have Hnonemptyb : ∀ typedInput : TId * IntegrateInput (A := A), typedInput ∈ pend ++ inputs ->
      (1 <= length (in_content typedInput.2))%nat.
  { move=> typedInput /elem_of_app [Hin | Hin]; [exact (Hnem_pd typedInput Hin) | exact (Hnem_in typedInput Hin)]. }
  have Hkb1c : ∀ typedInput : TId * IntegrateInput (A := A), typedInput ∈ pend ++ inputs ->
      (Z.of_nat (clock (in_id typedInput.2)) + Z.of_nat (length (in_content typedInput.2)) < 2^64)%Z.
  { move=> typedInput /elem_of_app [Hin | Hin];
      [exact (Hpendbnd typedInput Hin) | exact (Hnowrapb typedInput Hin)]. }
  (* the whole drained pending and its per-char certificates *)
  iAssert (is_pending_certified γh (expand_inputs (pend ++ inputs))) as "#Hcertpending".
  { rewrite /is_pending_certified expand_inputs_app big_sepL_app.
    iSplit; [iFrame "Hpendcert" | iFrame "Hcertsin"]. }
  have Hrootpending : is_pending_rooted (pend ++ inputs).
  { move=> typedInput /elem_of_app [Hin | Hin];
      [exact (Hpendroot typedInput Hin) | exact (Hrooted typedInput Hin)]. }
  destruct (wire_drain m (pend ++ inputs)) as [[applied rest'] m'] eqn:Hdrainc.
  have Happsub := proj1 (wire_drain_subset m (pend ++ inputs) applied rest' m' Hdrainc).
  have Hrestsub := proj2 (wire_drain_subset m (pend ++ inputs) applied rest' m' Hdrainc).
  (* ghost first: the gate totality, then the batch delivery *)
  iApply wp_fupd.
  iApply fupd_wp.
  have HmaskN : ↑histN ⊆ (⊤ : coPset) by solve_ndisj.
  iMod (history_wire_ready_total γh c h m (pend ++ inputs) applied ⊤ HmaskN
          Hhcoh Harrinv Hnonemptyb Happsub with "Hishist Hhist Hcertpending") as "[Hhist %Hrtot]".
  iMod (history_deliver_wire γh c h m (pend ++ inputs) applied rest' m' ⊤ HmaskN
          Hdrainc Hhcoh Harrinv Hnonemptyb with "Hishist Hhist Hcertpending")
    as "(Hhist & #Hlbnew & %Hvr & %Hcoh' & %Hnoc)".
  iModIntro.
  iAssert (own_pending_field (s_loc .[(yjs.store.t), "pending"]) pend)%I with "[Hpendf Hpend]" as "Hpending".
  { iExists pend_sl. iFrame "Hpendf Hpend". }
  iAssert (own_store_runs s_loc (MkStoreStateRuns client k locs p bind pend pdel))
    with "[Hclient Hclock HdeletedSet Hitems Hregistry Htypes Hpending Hpdeletes]" as "Hruns".
  { iSplitL; last (iPureIntro; split; [exact Hrpi | exact Hreg]).
    rewrite /own_store_fields_runs /=.
    iFrame "Hclient Hclock HdeletedSet Hitems Hregistry Htypes Hpending Hpdeletes". }
  wp_apply (wp_store__applyUpdate_unlocked s_loc sl dq
              inputs pend applied rest' m m' (MkStoreStateRuns client k locs p bind pend pdel) eq_refl
              Hdrainc Hvr Hrtot Happsub Hnonemptyb (conj Hmtypes Hmdom) Hkb1c
              with "[$Hupd $Hruns]").
  iIntros (p' locs' bind') "(Hupd & Hruns & %Hbindsub' & %Hregmodelp & %Halrp)".
  iEval (simpl) in "Hruns".
  simpl in Hregmodelp, Halrp.
  have [Hmtypes' Hmdom'] := Hregmodelp.
  iDestruct "Hruns" as "(Hfields' & %Hinvs')".
  iEval (simpl) in "Hfields'".
  have Hrpi' : run_pool_invs p' := proj1 Hinvs'.
  have Hreg' : pool_registry_coh bind' p' := proj2 Hinvs'.
  iDestruct "Hfields'" as "(Hclient & Hclock & HdeletedSet & Hitems & Hregistry & Htypes & Hpending & Hpdeletes)".
  have Hdom' : dom p ⊆ dom p' := pool_registry_coh_dom_mono bind bind' p p' Hreg Hreg' Hbindsub'.
  have [Hbindtypes' [Hbindinj' Htypesbound']] := Hreg'.
  (* grow the item-set authority to the (possibly larger) pool and snapshot it;
     the registry may have grown by fresh empty root types (issue #54), so the
     domain only INCREASES. *)
  have Hdomf : dom ((λ tm : type_model, (list_to_set (tm_arr tm) : gset (YjsItem A))) <$> p)
             ⊆ dom ((λ tm : type_model, (list_to_set (tm_arr tm) : gset (YjsItem A))) <$> p')
    by rewrite !dom_fmap_L; exact Hdom'.
  have Hgrowf : ∀ q S S',
      ((λ tm : type_model, (list_to_set (tm_arr tm) : gset (YjsItem A))) <$> p) !! q = Some S ->
      ((λ tm : type_model, (list_to_set (tm_arr tm) : gset (YjsItem A))) <$> p') !! q = Some S' ->
      S ⊆ S'.
  { move=> q S S'. rewrite !lookup_fmap. move=> Hq Hq'.
    apply fmap_Some in Hq as (tm & Hts & ->).
    apply fmap_Some in Hq' as (tm' & Hts' & ->).
    destruct (Htypesbound q (ex_intro _ tm Hts)) as [nm Hbnm].
    have Hbnm' : bind' !! nm = Some q := lookup_weaken _ _ _ _ Hbnm Hbindsub'.
    have Hdg : doc_model_get m (RootId nm) = tm_arr tm := Hmtypes nm q tm Hbnm Hts.
    have Hdg' : doc_model_get m' (RootId nm) = tm_arr tm' := Hmtypes' nm q tm' Hbnm' Hts'.
    move=> x. rewrite !elem_of_list_to_set. move=> Hx.
    rewrite -Hdg'. apply (ValidReplay_mem (expand_inputs applied) m m' Hvr (RootId nm)).
    by rewrite Hdg. }
  iMod (auth_gmap_gset_grow_snap γs.(sn_seq) _ _ Hdomf Hgrowf with "Hseq")
    as "[Hseq #Hsnap]".
  (* reconcile the registry ghost_map with the grown concrete map (issue #54):
     mint one persistent [is_type_binding] per newly registered root name *)
  iMod (ghost_map_grow_persist γs.(sn_types) bind bind' Hbindsub' with "HtypesAuth Hbinds")
    as "[HtypesAuth #Hbinds']".
  (* per-applied bindings: the applied wire item's first char landed in its root *)
  have Happbnd : ∀ typedInput : TId * IntegrateInput (A := A), typedInput ∈ applied ->
      ∃ nm p, typedInput.1 = RootId nm ∧ bind' !! nm = Some p.
  { move=> typedInput Hin.
    have Hne := applied_root_nonempty applied m m' typedInput Hvr Hin
                 (Hnonemptyb typedInput (Happsub typedInput Hin)).
    destruct (Hmdom' typedInput.1 Hne) as (nm & q & Heq & Hb). by exists nm, q. }
  iAssert (is_applied_root_lb γs applied m') as "#Hlbs".
  { rewrite /is_applied_root_lb. iApply big_sepL_intro.
    iIntros "!#" (i typedInput Hi).
    destruct (Happbnd typedInput (list_elem_of_lookup_2 _ _ _ Hi)) as (nm & q & Htieq & Hbnm).
    destruct (Hbindtypes' nm q Hbnm) as [tm' Hts'].
    have Hdg' : doc_model_get m' (RootId nm) = tm_arr tm' := Hmtypes' nm q tm' Hbnm Hts'.
    iDestruct (big_sepM_lookup _ _ nm q Hbnm with "Hbinds'") as "#Hbind".
    iExists nm. iSplit; [done |].
    iExists q. iFrame "Hbind".
    rewrite /is_type_lb Htieq Hdg'.
    iApply (auth_gmap_gset_frag_lookup with "Hsnap").
    rewrite lookup_fmap Hts' //. }
  (* the leftover pending re-certifies the new pending buffer (per-char) *)
  iAssert (is_pending_certified γh (expand_inputs rest')) as "#Hpendcert'".
  { rewrite /is_pending_certified. iApply big_sepL_intro.
    iIntros "!#" (i typedInput Hi).
    iApply (big_sepL_elem_of _ _ typedInput
              (expand_inputs_subset rest' (pend ++ inputs) Hrestsub typedInput
                 (list_elem_of_lookup_2 _ _ _ Hi))
              with "Hcertpending"). }
  have Hpendroot' : is_pending_rooted rest'.
  { move=> typedInput Hin. exact (Hrootpending typedInput (Hrestsub typedInput Hin)). }
  have Hpendbnd' : ∀ typedInput : TId * IntegrateInput (A := A), typedInput ∈ rest' ->
      (Z.of_nat (clock (in_id typedInput.2)) + Z.of_nat (length (in_content typedInput.2)) < 2^64)%Z.
  { move=> typedInput Hin. exact (Hkb1c typedInput (Hrestsub typedInput Hin)). }
  (* the counter clause survives: nothing applied is ours *)
  have Hctrm : ∀ (t : TId) x, x ∈ doc_model_get m t -> clientId (item_id x) = c ->
      (clock (item_id x) < uint.nat k)%nat.
  { move=> t x Hx Hcx.
    have Hne : doc_model_get m t ≠ [].
    { move=> Heq. move: Hx. rewrite Heq elem_of_nil. done. }
    destruct (Hmdom t Hne) as (nm & q & -> & Hbnm).
    destruct (Hbindtypes nm q Hbnm) as [tm Htm].
    rewrite (Hmtypes nm q tm Hbnm Htm) in Hx.
    exact (Hctr q tm x Htm Hx Hcx). }
  have Hctrm' : ∀ (t : TId) x, x ∈ doc_model_get m' t -> clientId (item_id x) = c ->
      (clock (item_id x) < uint.nat k)%nat.
  { move=> t x Hx Hcx.
    destruct (ValidReplay_prov (expand_inputs applied) m m' Hvr t x Hx)
      as [Hold | (i & typedInput & Hi & Hid)].
    - exact (Hctrm t x Hold Hcx).
    - exfalso. apply (Hnoc typedInput (list_elem_of_lookup_2 _ _ _ Hi)). by rewrite -Hid. }
  have Hctr' : ∀ parent tm x, p' !! parent = Some tm -> x ∈ tm_arr tm ->
      clientId (item_id x) = c -> (clock (item_id x) < uint.nat k)%nat.
  { move=> parent tm x Htm Hx Hcx.
    destruct (Htypesbound' parent (ex_intro _ tm Htm)) as [nm Hbnm].
    rewrite -(Hmtypes' nm parent tm Hbnm Htm) in Hx.
    exact (Hctrm' (RootId nm) x Hx Hcx). }
  (* no input is lost: each is delivered into the new history (applied this
     batch, or already present) or buffered by id in the new pending [rest'] *)
  have Hnoloss : ∀ x, x ∈ pend ++ inputs ->
      input_accounted (h ++ (deliver_ev <$> expand_inputs applied)) rest' x.
  { move=> x Hxin'. rewrite /input_accounted.
    destruct (wire_drain_id_conservation m (pend ++ inputs) applied rest' m' Hdrainc x Hxin')
      as [[y [Hy Hid]] | [[y [Hy Hid]] | Hh]].
    - (* applied by id: the head char of [y] is delivered in the new history *)
      left.
      have Hyne : (1 <= length (in_content y.2))%nat := Hnonemptyb y (Happsub y Hy).
      have [fop Hfop] : is_Some (ops_of_input y.2 (explode (in_content y.2)) !! 0%nat).
      { apply lookup_lt_is_Some_2. rewrite /ops_of_input ops_from_length explode_length. lia. }
      have Hidfop : in_id fop = in_id y.2.
      { destruct (ops_from_lookup (clientId (in_id y.2)) (clock (in_id y.2))
                    (in_originId y.2) (in_rightOriginId y.2) (explode (in_content y.2)) 0%nat fop Hfop)
          as [Hidop _].
        rewrite Hidop Nat.add_0_r. by destruct (in_id y.2). }
      have Hmemexp : (y.1, fop) ∈ expand_inputs applied.
      { rewrite /expand_inputs. apply list_elem_of_join. exists (expand_input y).
        split; [| by apply list_elem_of_fmap_2].
        apply (list_elem_of_lookup_2 _ 0%nat). by apply expand_input_lookup. }
      exists y.1, fop. split.
      + rewrite delivered_ops_app. apply elem_of_app. right.
        rewrite delivered_ops_deliver_batch. apply list_elem_of_fmap.
        exists (y.1, fop). split; [done | exact Hmemexp].
      + rewrite Hidfop. exact Hid.
    - (* kept by id in the leftover pending *)
      right. exists y. split; [exact Hy | exact Hid].
    - (* already present in the final model: delivered by [docm_mem_delivered] *)
      left.
      apply docm_has_spec in Hh. destruct Hh as (t & xitem & Hxit & Hxitid).
      destruct (docm_mem_delivered (h ++ (deliver_ev <$> expand_inputs applied)) m' t xitem Hcoh' Hxit)
        as (input & Hdel & Hinid).
      exists t, input. split; [exact Hdel | rewrite Hinid; exact Hxitid]. }
  have Hnoloss_in : ∀ x, x ∈ inputs ->
      input_accounted (h ++ (deliver_ev <$> expand_inputs applied)) rest' x.
  { move=> x Hx. apply Hnoloss, elem_of_app. by right. }
  (* transport the accepted-set coherence across the drain to (h', rest') *)
  have Hdids : delivered_ids h
             ⊆ delivered_ids (h ++ (deliver_ev <$> expand_inputs applied)).
  { rewrite delivered_ids_app. apply union_subseteq_l. }
  have Hacccoh' : accepted_coh acc (h ++ (deliver_ev <$> expand_inputs applied)) rest'.
  { apply (accepted_coh_applyUpdate acc h _ pend rest' Hacccoh Hdids).
    move=> x Hx. apply input_accounted_id, Hnoloss, elem_of_app. by left. }
  (* the delete set transports across the apply: the domain bound follows the
     replay, and the tombstone coherence follows the pool refinement the store
     op reports (old live chars, or chars this apply just integrated) *)
  have Hmono' : ∀ i, doc_model_has m i = true -> doc_model_has m' i = true
    := λ i, docm_has_mono m m' i (ValidReplay_mem (expand_inputs applied) m m' Hvr).
  iDestruct (own_delete_set_runs_apply γs m m' (all_runs p) (all_runs p')
               Hmono' Halrp with "Hdelete_set") as "Hdelete_set".
  iModIntro. iApply ("HΦ" $! applied rest' m').
  iAssert (is_applied_certs γs applied m') with "[Hlbs]" as "#Hcerts".
  { iFrame "Hlbs". iPureIntro. exact (ValidReplay_input_mem (expand_inputs applied) m m' Hvr). }
  iFrame "Hupd". iFrame "Hlbnew". iFrame "Hcerts".
  have Hregmodel' : pool_registry_models m' bind' p'.
  { rewrite /pool_registry_models. split; [exact Hmtypes' | exact Hmdom']. }
  iAssert (own_store_runs s_loc (MkStoreStateRuns client k locs' p' bind' rest' pdel))
    with "[Hclient Hclock HdeletedSet Hitems Hregistry Htypes Hpending Hpdeletes]" as "Hcells".
  { iSplitL; last (iPureIntro; split; [exact Hrpi' | exact Hreg']).
    rewrite /own_store_fields_runs /=.
    iFrame "Hclient Hclock HdeletedSet Hitems Hregistry Htypes Hpending Hpdeletes". }
  iSplitL "Hcells Hseq HtypesAuth Hhist Hacc Hdelete_set";
    last by (iPureIntro; split_and!; [done | exact Hvr | exact Hnoloss_in]).
  iExists client, k, pdel, locs', p', bind', acc.
  iFrame "Hcells Hseq HtypesAuth Hbinds' Hhist Hacc Hdelete_set".
  iFrame "Hpendcert' Hclientpin".
  iPureIntro. split_and!;
    [exact Hclientc | exact Hpendroot' | exact Hpendbnd' | exact Hregmodel' | exact Hcoh'
    | exact Hctr' | exact Hacccoh'].
Qed.

End store_update.
