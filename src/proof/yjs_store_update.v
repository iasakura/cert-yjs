(** WP proofs for the [store] update path: [getNodeIndex] / [GetNode], the
    registry hit [getOrCreateYType], [store.repair], and the [applyUpdate]
    stack (the [ValidReplay] refinement [wp_store__applyUpdate], the internal
    certificate lemma, and the public [own_store]-level certificate spec
    [wp_store__applyUpdate_certs]), plus the [store_inv ⊣⊢ own_store] bridge.

    Split out of [yjs_store_base] / [yjs_store_integrate] so applyUpdate-side
    work recompiles only this file; downstream files see everything through
    the [yjs_store] facade. Same [Section] boilerplate; [Type*] footprints. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import yjs_core.
From New.proof Require Import yjs_common yjs_id yjs_item yjs_ytype.
From New.proof Require Import yjs_run_theory.
From New.proof Require Import yjs_history.
From New.proof Require Import yjs_store_base yjs_store_integrate.
From iris.algebra Require Import auth gmap gset.
From stdpp Require Import sorting.

(* iris.algebra / stdpp.sorting push [nat_scope], retuning the default [<] / [≤].
   The verified WP proofs write [Z] comparisons (e.g. [sint.Z i < …]) unannotated
   and annotate [nat] ones with [%nat], so restore [Z_scope] as the default. *)
Local Open Scope Z_scope.
From New.proof Require Import yjs_store_node.
Section store_update.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.
Notation P := go_string.
Local Notation TId := (TypeId P).
Local Notation Op := (TId * @YjsOperation A)%type.
Local Notation Ev := (@Event Op).
Local Notation DocM := (gmap TId (list (YjsItem A))).

(* the grow-only item-set RA (the certificate proofs grow the [sn_seq]
   authority and mint [is_type_lb] fragments) *)
Context {seq_inG : inG Σ (authR (gmapUR loc (gsetUR (YjsItem A))))}.

(* [client_run]'s merge_sort instances are [#[local]] in [yjs_store_base];
   the run-list lemmas here need them again. *)
#[local] Instance cell_le_dec : RelDecision cell_le.
Proof. rewrite /cell_le. solve_decision. Defined.
#[local] Instance cell_le_trans : Transitive cell_le.
Proof. rewrite /cell_le. move=> x y z. lia. Qed.
#[local] Instance cell_le_total : Total cell_le.
Proof. rewrite /cell_le. move=> x y. lia. Qed.

(* [is_pending_rooted]'s instances are declared in [yjs_store_base] under its
   wider section context ([Proof using Type*] closes them over instances this
   file's section lacks), so re-declare them here (the [cell_le] pattern
   above); without them [iNamed] stalls at the persistent [#Hpendroot]
   conjunct of [store_inv_excl] / [own_store]. *)
#[local] Instance pending_item_rooted_persistent' γs ti :
  Persistent (pending_item_rooted γs ti).
Proof. rewrite /pending_item_rooted. destruct (decide _); apply _. Qed.
#[local] Instance is_pending_rooted_persistent' γs pending :
  Persistent (is_pending_rooted γs pending).
Proof. apply _. Qed.
#[local] Instance pending_item_rooted_timeless' γs ti :
  Timeless (pending_item_rooted γs ti).
Proof. rewrite /pending_item_rooted. destruct (decide _); apply _. Qed.
#[local] Instance is_pending_rooted_timeless' γs pending :
  Timeless (is_pending_rooted γs pending).
Proof. apply _. Qed.


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
Lemma wp_store__applyUpdate (s mref tref : loc) (sl pend_sl0 : slice.t)
    (dq : dfrac)
    (inputs pend0 applied rest : list (TId * IntegrateInput (A := A)))
    (m m' : DocM) (types : gmap loc type_state) (bind : gmap P loc) :
  wire_drain m (pend0 ++ inputs) = (applied, rest, m') ->
  ValidReplay (expand_inputs applied) m m' ->
  wire_ready_total m (pend0 ++ inputs) applied ->
  (∀ ti : TId * IntegrateInput (A := A), ti ∈ applied -> ti ∈ pend0 ++ inputs) ->
  (∀ ti : TId * IntegrateInput (A := A), ti ∈ pend0 ++ inputs ->
     (1 <= length (in_content ti.2))%nat) ->
  (∀ name p, bind !! name = Some p -> is_Some (types !! p)) ->
  (∀ n1 n2 p, bind !! n1 = Some p -> bind !! n2 = Some p -> n1 = n2) ->
  (∀ p, is_Some (types !! p) -> ∃ name, bind !! name = Some p) ->
  (∀ name p ts, bind !! name = Some p -> types !! p = Some ts ->
     docm_get m (RootId name) = ty_arr ts) ->
  (∀ t, docm_get m t ≠ [] -> ∃ name p, t = RootId name ∧ bind !! name = Some p) ->
  (∀ ti : TId * IntegrateInput (A := A), ti ∈ pend0 ++ inputs ->
     in_originId ti.2 = None -> in_rightOriginId ti.2 = None ->
     ∃ nm, ti.1 = RootId nm ∧ is_Some (bind !! nm)) ->
  (∀ c, c ∈ all_cells types -> cell_fits c) ->
  (∀ ti : TId * IntegrateInput (A := A), ti ∈ pend0 ++ inputs ->
     (Z.of_nat (clock (in_id ti.2)) + Z.of_nat (length (in_content ti.2)) < 2^64)%Z) ->
  NoDup (ic_loc <$> all_cells types) ->
  cells_range_disjoint (all_cells types) ->
  (∀ c, c ∈ all_cells types -> cell_origin_clk c) ->
  {{{ is_pkg_init yjs ∗ own_update_structs sl dq inputs ∗
      (s .[(yjs.store.t), "pending"]) ↦ pend_sl0 ∗
      own_update_structs pend_sl0 (DfracOwn 1) pend0 ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types ∗
      (s .[(yjs.store.t), "types"]) ↦ tref ∗ own_map tref (DfracOwn 1) bind ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) }}}
    s @! (go.PointerType yjs.store) @! "applyUpdate" #sl
  {{{ (pend_sl' : slice.t) (types' : gmap loc type_state), RET #();
      own_update_structs sl dq inputs ∗
      (s .[(yjs.store.t), "pending"]) ↦ pend_sl' ∗
      own_update_structs pend_sl' (DfracOwn 1) rest ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types' ∗
      (s .[(yjs.store.t), "types"]) ↦ tref ∗ own_map tref (DfracOwn 1) bind ∗
      ([∗ map] parent ↦ ts ∈ types',
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) ∗
      ⌜dom types' = dom types⌝ ∗
      ⌜∀ name p ts', bind !! name = Some p -> types' !! p = Some ts' ->
         docm_get m' (RootId name) = ty_arr ts'⌝ ∗
      ⌜∀ t, docm_get m' t ≠ [] -> ∃ name p, t = RootId name ∧ bind !! name = Some p⌝ ∗
      ⌜∀ c, c ∈ all_cells types' ->
         (∃ c0, c0 ∈ all_cells types ∧ cell_client c = cell_client c0 ∧
            (uint.Z (cell_clock c0) <= uint.Z (cell_clock c))%Z ∧
            (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) <=
             uint.Z (cell_clock c0) + Z.of_nat (length (ic_run c0)))%Z) ∨
         ∃ ti : TId * IntegrateInput (A := A), ti ∈ applied ∧
            cell_client c = W64 (clientId (in_id ti.2)) ∧
            (uint.Z (W64 (clock (in_id ti.2))) <= uint.Z (cell_clock c))%Z ∧
            (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) <=
             uint.Z (W64 (clock (in_id ti.2))) + Z.of_nat (length (in_content ti.2)))%Z⌝ ∗
      ⌜NoDup (ic_loc <$> all_cells types')⌝ ∗
      ⌜cells_range_disjoint (all_cells types')⌝ ∗
      ⌜∀ c, c ∈ all_cells types' -> cell_fits c⌝ ∗
      ⌜∀ c, c ∈ all_cells types' -> cell_origin_clk c⌝ }}}.
Proof using Type*.
  move=> Hdrain Hvr Hrtot Happliedsub Hnonempty Hbindtypes Hbindinj Htypesbound Hmtypes Hmdom
         Hrooted Hfits Hkb1 Hlocdup Hrangedisj Horiginclk.
  iIntros (Φ) "(#Hpkg & Hupd & Hpendf & Hpend & Hitemsf & Hitemmap & Htypesf & Htypesmap & Htypes) HΦ".
  (* W64 id bounds of the whole pending, from the two heap slices *)
  iDestruct (own_update_id_bounds with "Hupd") as %Hidbin.
  iDestruct (own_update_id_bounds with "Hpend") as %Hidbpd.
  have Hidb : ∀ ti : TId * IntegrateInput (A := A), ti ∈ pend0 ++ inputs ->
      (Z.of_nat (clientId (in_id ti.2)) < 2^64)%Z ∧
      (Z.of_nat (clock (in_id ti.2)) < 2^64)%Z.
  { move=> ti /elem_of_app [Hin | Hin];
      apply list_elem_of_lookup_1 in Hin; destruct Hin as [ix Hix];
      [exact (Hidbpd ix ti Hix) | exact (Hidbin ix ti Hix)]. }
  iDestruct "Hupd" as (uivs_in) "(Hslin & Hcapin & #Hitemsin)".
  iDestruct (big_sepL2_length with "Hitemsin") as %Hlenin.
  iDestruct "Hpend" as (uivs_pd) "(Hslpd & Hcappd & #Hitemspd)".
  iDestruct (big_sepL2_length with "Hitemspd") as %Hlenpd.
  (* the INITIAL types' run structure, extracted while [Htypes] is over [types]
     (pure, non-consuming): needed in the ready branch to bound an original
     cell's clock range below a fresh batch item via [expand_inputs_arr_fresh]. *)
  iDestruct (types_repr_all2 with "Htypes") as %Hreprall_init.
  iDestruct (types_runs_wf2 with "Htypes") as %Hrunwf_init.
  iDestruct (types_cells_id_bounds2 with "Htypes") as %Hbnds_init.
  wp_method_call. wp_call. wp_call. wp_auto.
  (* ----- phase A: pending := pending ++ structs ----- *)
  iDestruct (own_slice_len with "Hslin") as %[Hinlen Hinlen0].
  iAssert (∃ (j : nat) (pslA : slice.t) (uivsA : list yjs.updateItem.t),
      "Hi" ∷ i_ptr ↦ W64 j ∗
      "Hpendingp" ∷ pending_ptr ↦ pslA ∗
      "HslA" ∷ pslA ↦* uivsA ∗
      "HcapA" ∷ own_slice_cap yjs.updateItem.t pslA (DfracOwn 1) ∗
      "#HitemsA" ∷ ([∗ list] uiv;ti ∈ uivsA;(pend0 ++ take j inputs),
          is_update_item uiv ti) ∗
      "Hslin" ∷ sl ↦*{dq} uivs_in ∗
      "%HjA" ∷ ⌜(j <= length uivs_in)%nat⌝)%I
    with "[i pending Hslpd Hcappd Hslin]" as "IH".
  { iExists 0%nat, pend_sl0, uivs_pd. iFrame "i pending Hslpd Hcappd Hslin".
    rewrite take_0 app_nil_r. iFrame "Hitemspd".
    iPureIntro. lia. }
  wp_for "IH".
  case_bool_decide as Hcond.
  - (* append structs[j] *)
    have Hjlt : (j < length uivs_in)%nat.
    { move: Hcond. rewrite Hinlen. word. }
    destruct (uivs_in !! j) as [uiv|] eqn:Huiv;
      last by (apply lookup_ge_None in Huiv; lia).
    have [ti Hti] : is_Some (inputs !! j).
    { apply lookup_lt_is_Some_2. rewrite -Hlenin. exact Hjlt. }
    iDestruct (big_sepL2_lookup _ _ _ j with "Hitemsin") as "#Hui";
      [exact Huiv | exact Hti |].
    wp_auto.
    rewrite decide_True; last by word.
    iDestruct (own_slice_elem_acc (sint.Z (W64 j)) uiv sl dq uivs_in with "Hslin")
      as "[Hel Hgive]".
    { word. }
    { replace (Z.to_nat (sint.Z (W64 j))) with j by word. exact Huiv. }
    wp_auto.
    iDestruct ("Hgive" $! uiv with "Hel") as "Hslin".
    have Hinsid : (<[sint.nat (W64 j) := uiv]> uivs_in) = uivs_in.
    { apply list_insert_id. replace (sint.nat (W64 j)) with j by word. exact Huiv. }
    iEval (rewrite Hinsid) in "Hslin".
    wp_apply wp_slice_literal. iSplitR; first done.
    iIntros "%sing [Hsing _]". wp_auto.
    wp_apply (wp_slice_append with "[$HslA $HcapA $Hsing]").
    iIntros (pslA') "(HslA' & HcapA' & _)". wp_auto.
    wp_for_post.
    iFrame "Hcapin Hpendf Hitemsf Hitemmap Htypesf Htypesmap Htypes HΦ s structs".
    iExists (S j), pslA', (uivsA ++ [uiv]).
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
               (typesj : gmap loc type_state) (mj : DocM),
        "Hprog" ∷ progress_ptr ↦ pv ∗
        "Hpendingp" ∷ pending_ptr ↦ pendingS ∗
        "HslP" ∷ pendingS ↦* uivsP ∗
        "HcapP" ∷ own_slice_cap yjs.updateItem.t pendingS (DfracOwn 1) ∗
        "#HitemsPj" ∷ ([∗ list] uiv;ti ∈ uivsP;pendingj, is_update_item uiv ti) ∗
        "Hitemsf" ∷ (s .[(yjs.store.t), "items"]) ↦ mref ∗
        "Hitemmap" ∷ own_item_map mref (DfracOwn 1) typesj ∗
        "Htypesf" ∷ (s .[(yjs.store.t), "types"]) ↦ tref ∗
        "Htypesmap" ∷ own_map tref (DfracOwn 1) bind ∗
        "Htypes" ∷ ([∗ map] parent ↦ ts ∈ typesj,
            own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
            ⌜YjsArrInvariant (ty_arr ts)⌝) ∗
        "%Hpendingsubj" ∷ ⌜∀ ti : TId * IntegrateInput (A := A),
            ti ∈ pendingj -> ti ∈ pend0 ++ inputs⌝ ∗
        "%Hprj" ∷ ⌜WireReplay m appliedj mj⌝ ∗
        "%Hdomj" ∷ ⌜dom typesj = dom types⌝ ∗
        "%Hmtypesj" ∷ ⌜∀ name pl ts, bind !! name = Some pl ->
            typesj !! pl = Some ts -> docm_get mj (RootId name) = ty_arr ts⌝ ∗
        "%Hmdomj" ∷ ⌜∀ t, docm_get mj t ≠ [] ->
            ∃ name pl, t = RootId name ∧ bind !! name = Some pl⌝ ∗
        "%Hfitsj" ∷ ⌜∀ c0, c0 ∈ all_cells typesj -> cell_fits c0⌝ ∗
        "%Horiginclkj" ∷ ⌜∀ c0, c0 ∈ all_cells typesj -> cell_origin_clk c0⌝ ∗
        "%Hprovj" ∷ ⌜∀ c0, c0 ∈ all_cells typesj ->
            (∃ c1, c1 ∈ all_cells types ∧ cell_client c0 = cell_client c1 ∧
               (uint.Z (cell_clock c1) <= uint.Z (cell_clock c0))%Z ∧
               (uint.Z (cell_clock c0) + Z.of_nat (length (ic_run c0)) <=
                uint.Z (cell_clock c1) + Z.of_nat (length (ic_run c1)))%Z) ∨
            (∃ ti : TId * IntegrateInput (A := A), ti ∈ appliedj ∧
               cell_client c0 = W64 (clientId (in_id ti.2)) ∧
               (uint.Z (W64 (clock (in_id ti.2))) <= uint.Z (cell_clock c0))%Z ∧
               (uint.Z (cell_clock c0) + Z.of_nat (length (ic_run c0)) <=
                uint.Z (W64 (clock (in_id ti.2))) + Z.of_nat (length (in_content ti.2)))%Z)⌝ ∗
        "%Hlocdupj" ∷ ⌜NoDup (ic_loc <$> all_cells typesj)⌝ ∗
        "%Hrangedisjj" ∷ ⌜cells_range_disjoint (all_cells typesj)⌝ ∗
        "%Hmid" ∷ ⌜pv = true ->
            wire_drain mj pendingj = (suffix, rest, m') ∧
            applied = appliedj ++ suffix ∧ ValidReplay (expand_inputs suffix) mj m'⌝ ∗
        "%Hfin" ∷ ⌜pv = false -> pendingj = rest ∧ mj = m' ∧ applied = appliedj⌝)%I
      with "[progress Hpendingp HslA HcapA Hitemsf Hitemmap Htypesf Htypesmap Htypes]"
      as "IH".
    { iExists true, pslA, uivsA, (pend0 ++ inputs), [], applied, types, m.
      iFrame "progress Hpendingp HslA HcapA Hitemsf Hitemmap Htypesf Htypesmap Htypes".
      iFrame "HitemsA".
      iPureIntro. split_and!.
      - done.
      - constructor.
      - done.
      - exact Hmtypes.
      - exact Hmdom.
      - exact Hfits.
      - exact Horiginclk.
      - move=> c0 Hc0. left. exists c0. split_and!; [exact Hc0 | done | lia | lia].
      - exact Hlocdup.
      - exact Hrangedisj.
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
                 (types_c : gmap loc type_state) (m_c : DocM),
          "Hii" ∷ i_ptr ↦ W64 i ∗
          "Hprog" ∷ progress_ptr ↦ pvi ∗
          "Hrestp" ∷ rest_ptr ↦ restS ∗
          "HslR" ∷ restS ↦* uivsR ∗
          "HcapR" ∷ own_slice_cap yjs.updateItem.t restS (DfracOwn 1) ∗
          "#HitemsR" ∷ ([∗ list] uiv;ti ∈ uivsR;keptacc, is_update_item uiv ti) ∗
          "Hitemsf" ∷ (s .[(yjs.store.t), "items"]) ↦ mref ∗
          "Hitemmap" ∷ own_item_map mref (DfracOwn 1) types_c ∗
          "Htypesf" ∷ (s .[(yjs.store.t), "types"]) ↦ tref ∗
          "Htypesmap" ∷ own_map tref (DfracOwn 1) bind ∗
          "Htypes" ∷ ([∗ map] parent ↦ ts ∈ types_c,
              own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
              ⌜YjsArrInvariant (ty_arr ts)⌝) ∗
          "%Hilen" ∷ ⌜(i <= length pendingj)%nat⌝ ∗
          "%Hpassa" ∷ ⌜wire_pass m_c (drop i pendingj) keptacc =
              (app_rem, keptfin0, m_pend0)⌝ ∗
          "%Hpassc" ∷ ⌜wire_pass mj pendingj [] =
              (appacc ++ app_rem, keptfin0, m_pend0)⌝ ∗
          "%Happdec" ∷ ⌜applied = appliedj ++ appacc ++ app_rem ++ af2⌝ ∗
          "%Hvrc" ∷ ⌜ValidReplay (expand_inputs (app_rem ++ af2)) m_c m'⌝ ∗
          "%Hprc" ∷ ⌜WireReplay m (appliedj ++ appacc) m_c⌝ ∗
          "%Hkeptsub" ∷ ⌜∀ ti, ti ∈ keptacc -> ti ∈ pendingj⌝ ∗
          "%Hpv" ∷ ⌜pvi = false <-> appacc = []⌝ ∗
          "%Hdomc" ∷ ⌜dom types_c = dom types⌝ ∗
          "%Hmtypesc" ∷ ⌜∀ name pl ts, bind !! name = Some pl ->
              types_c !! pl = Some ts -> docm_get m_c (RootId name) = ty_arr ts⌝ ∗
          "%Hmdomc" ∷ ⌜∀ t, docm_get m_c t ≠ [] ->
              ∃ name pl, t = RootId name ∧ bind !! name = Some pl⌝ ∗
          "%Hfitsc" ∷ ⌜∀ c0, c0 ∈ all_cells types_c -> cell_fits c0⌝ ∗
          "%Horiginclkc" ∷ ⌜∀ c0, c0 ∈ all_cells types_c -> cell_origin_clk c0⌝ ∗
          "%Hprovc" ∷ ⌜∀ c0, c0 ∈ all_cells types_c ->
              (∃ c1, c1 ∈ all_cells types ∧ cell_client c0 = cell_client c1 ∧
                 (uint.Z (cell_clock c1) <= uint.Z (cell_clock c0))%Z ∧
                 (uint.Z (cell_clock c0) + Z.of_nat (length (ic_run c0)) <=
                  uint.Z (cell_clock c1) + Z.of_nat (length (ic_run c1)))%Z) ∨
              (∃ ti : TId * IntegrateInput (A := A), ti ∈ (appliedj ++ appacc) ∧
                 cell_client c0 = W64 (clientId (in_id ti.2)) ∧
                 (uint.Z (W64 (clock (in_id ti.2))) <= uint.Z (cell_clock c0))%Z ∧
                 (uint.Z (cell_clock c0) + Z.of_nat (length (ic_run c0)) <=
                  uint.Z (W64 (clock (in_id ti.2))) + Z.of_nat (length (in_content ti.2)))%Z)⌝ ∗
          "%Hlocdupc" ∷ ⌜NoDup (ic_loc <$> all_cells types_c)⌝ ∗
          "%Hrangedisjc" ∷ ⌜cells_range_disjoint (all_cells types_c)⌝)%I
        with "[i Hprog rest Hrsl0 Hrcap0 Hitemsf Hitemmap Htypesf Htypesmap Htypes]"
        as "IHin".
      { iExists 0%nat, false, _, [], [], [], app_rem0, af, typesj, mj.
        iFrame "i Hprog rest Hrsl0 Hrcap0 Hitemsf Hitemmap Htypesf Htypesmap Htypes".
        iSplit; first by rewrite big_sepL2_nil.
        iPureIntro. split_and!.
        - lia.
        - rewrite drop_0. exact Hpass0.
        - exact Hpass0.
        - rewrite Happj Hsufdec //.
        - exact Hvraf.
        - rewrite app_nil_r. exact Hprj.
        - move=> ti Hti. by apply elem_of_nil in Hti.
        - done.
        - exact Hdomj.
        - exact Hmtypesj.
        - exact Hmdomj.
        - exact Hfitsj.
        - exact Horiginclkj.
        - move=> c0 Hc0. destruct (Hprovj c0 Hc0) as [Ho | Ho]; [by left | right].
          destruct Ho as (ti & Hti & Hcc & Hlo & Hhi). exists ti.
          rewrite app_nil_r. split_and!; [exact Hti | exact Hcc | exact Hlo | exact Hhi].
        - exact Hlocdupj.
        - exact Hrangedisjj. }
      wp_for "IHin".
      case_bool_decide as Hcondi.
      * (* scan struct i *)
        have Hilt : (i < length uivsP)%nat.
        { move: Hcondi. rewrite HPlen. word. }
        destruct (uivsP !! i) as [uiv|] eqn:Huiv;
          last by (apply lookup_ge_None in Huiv; lia).
        destruct (pendingj !! i) as [[tj input]|] eqn:Hpi;
          last by (apply lookup_ge_None in Hpi; rewrite -HlenP in Hpi; lia).
        iDestruct (big_sepL2_lookup _ _ _ i with "HitemsPj") as "#Hui";
          [exact Huiv | exact Hpi |].
        iDestruct (big_sepL2_lookup _ _ _ i with "HitemsPj") as
          (oleft oright opn)
          "(#HisL & #HisR & #HisPN & %Hin_l & %Hin_r & %Hin_id & %Hin_c & %Hunonempty & %Htid & %Hborrow)";
          [exact Huiv | exact Hpi |].
        simpl in Hin_l, Hin_r, Hin_id, Hin_c, Htid, Hborrow.
        (* registry coherence, transported to the current [types_c] *)
        have Hbindtypesc : ∀ name pl, bind !! name = Some pl ->
            is_Some (types_c !! pl).
        { move=> name pl Hb. apply elem_of_dom. rewrite Hdomc.
          apply elem_of_dom. exact (Hbindtypes name pl Hb). }
        have Htypesboundc : ∀ pl, is_Some (types_c !! pl) ->
            ∃ name, bind !! name = Some pl.
        { move=> pl Hs0. apply Htypesbound. apply elem_of_dom. rewrite -Hdomc.
          apply elem_of_dom. exact Hs0. }
        iDestruct (types_repr_all2 with "Htypes") as %Hreprallc.
        iDestruct (types_runs_wf2 with "Htypes") as %Hrunwfc.
        have Hagreec : ∀ d : YjsId, docm_has m_c d = true <->
            ∃ c0, c0 ∈ all_cells types_c ∧ cell_covers c0 d.
        { move=> d.
          exact (docm_cells_agree m_c bind types_c d Hmtypesc Hmdomc
                   Hbindtypesc Htypesboundc Hreprallc Hrunwfc). }
        have Hpending0in : (tj, input) ∈ pend0 ++ inputs.
        { apply Hpendingsubj. exact (list_elem_of_lookup_2 _ _ _ Hpi). }
        (* read pending[i] into ui *)
        wp_auto.
        rewrite decide_True; last by word.
        iDestruct (own_slice_elem_acc (sint.Z (W64 i)) uiv pendingS (DfracOwn 1)
                     uivsP with "HslP") as "[Hel Hgive]".
        { word. }
        { replace (Z.to_nat (sint.Z (W64 i))) with i by word. exact Huiv. }
        wp_auto.
        iDestruct ("Hgive" $! uiv with "Hel") as "HslP".
        have Hinsid : (<[sint.nat (W64 i) := uiv]> uivsP) = uivsP.
        { apply list_insert_id.
          replace (sint.nat (W64 i)) with i by word. exact Huiv. }
        iEval (rewrite Hinsid) in "HslP".
        (* the arrival probe: hasNode *)
        wp_apply (wp_store__hasNode s mref (DfracOwn 1)
                    (uiv.(yjs.updateItem.id')) m_c types_c Hagreec Hfitsc Hlocdupc Hrangedisjc
                    with "[$Hitemsf $Hitemmap $Htypes]").
        iIntros (ok) "(Hitemsf & Hitemmap & Htypes & %Hok)".
        rewrite Hin_id in Hok.
        have Hokm : ok = docm_has m_c (in_id input).
        { destruct ok, (docm_has m_c (in_id input)) eqn:Hd;
            [done | have := proj1 Hok eq_refl; done
             | have := proj2 Hok eq_refl; done | done]. }
        destruct (docm_has m_c (in_id input)) eqn:Hd; subst ok.
        { (* duplicate: continue *)
          wp_auto. wp_for_post.
          iFrame "Hcapin Hpendf HΦ s Hslin Hpendingp HslP HcapP".
          iExists (S i), pvi, restS, uivsR, keptacc, appacc, app_rem, af2,
            types_c, m_c.
          replace (word.add (W64 i) (W64 1)) with (W64 (S i)) by word.
          iFrame "Hii Hprog Hrestp HslR HcapR Hitemsf Hitemmap Htypesf Htypesmap Htypes".
          iFrame "HitemsR".
          iPureIntro. split_and!; try done.
          - apply (lookup_lt_Some _ _ _ Hpi).
          - rewrite (drop_S pendingj (tj, input) i Hpi) /= Hd in Hpassa.
            exact Hpassa. }
        (* fresh: probe the structural gate *)
        wp_auto.
        wp_apply (wp_store__depsArrived s mref (DfracOwn 1) uiv (tj, input)
                    m_c types_c Hagreec Hfitsc Hlocdupc Hrangedisjc
                    with "[$Hui $Hitemsf $Hitemmap $Htypes]").
        iIntros "(Hitemsf & Hitemmap & Htypes)".
        destruct (input_ready m_c input) eqn:Hready.
        -- (* ready: certified pendings always integrate the whole chunk *)
           have Hsome : is_Some (wire_intg m_c (tj, input)).
           { apply (Hrtot (appliedj ++ appacc) (app_rem ++ af2) m_c (tj, input)).
             - rewrite Happdec !app_assoc //.
             - exact Hprc.
             - exact Hpending0in.
             - exact Hd.
             - exact Hready. }
           destruct Hsome as [arr' Hint'].
           (* step the wire pass equation *)
           rewrite (drop_S pendingj (tj, input) i Hpi) /= Hd Hready Hint' in Hpassa.
           destruct (wire_pass (<[tj := arr']> m_c) (drop (S i) pendingj) keptacc)
             as [[app2 kept2] m2] eqn:Hrec.
           move: Hpassa => [= Happrem Hkeq Hmeq].
           subst app_rem kept2 m2.
           (* peel this wire item's chunk off the per-char replay *)
           have Hne1 : (1 <= length (in_content input))%nat by (rewrite -Hin_c; exact Hunonempty).
           rewrite -app_comm_cons in Hvrc.
           have Hlk0 : ((tj, input) :: app2 ++ af2) !! 0%nat = Some (tj, input) by done.
           destruct (applyUpdate_peel_step ((tj, input) :: app2 ++ af2) 0%nat tj input
                       m_c m' (docm_get m_c tj) Hlk0 Hne1 eq_refl Hvrc)
             as (nit & arrp & Htoit & Hvld & Hmax & Hall & Hvrtail).
           simpl in Hvrtail.
           have Harr2 : arrp = arr'.
           { move: Hint'. rewrite /wire_intg Hall. by move=> [= <-]. }
           subst arrp.
           (* the target root's binding *)
           have [nm [Htjeq [pl Hbnm]]] : ∃ nm, tj = RootId nm ∧ is_Some (bind !! nm).
           { destruct (decide (in_originId input = None ∧
                               in_rightOriginId input = None)) as [[HoN HrN] | Hor].
             - destruct (Hrooted (tj, input) Hpending0in HoN HrN) as (nm & Heq & Hsm).
               by exists nm.
             - have Hne : docm_get m_c tj ≠ [].
               { apply (toItem_nonempty_of_origin input _ nit Htoit).
                 apply not_and_l in Hor.
                 by destruct Hor as [Ho | Ho]; [left | right]. }
               destruct (Hmdomc tj Hne) as (nm & pl & Heq & Hb).
               exists nm. split; [exact Heq | by exists pl]. }
           have Hnwc : (Z.of_nat (clock (in_id input)) + Z.of_nat (length (in_content input)) < 2^64)%Z
             := Hkb1 (tj, input) Hpending0in.
           have Hib : uint.Z (W64 (clock (in_id input))) = Z.of_nat (clock (in_id input))
             := uint_W64_nat_bound (clock (in_id input)) (length (in_content input)) Hnwc.
           iDestruct (types_cells_id_bounds2 with "Htypes") as %Hbndsc.
           (* the current item's flat position in [applied] *)
           have HKlk : applied !! (length (appliedj ++ appacc)) = Some (tj, input).
           { rewrite Happdec (app_assoc appliedj appacc) lookup_app_r; last done.
             rewrite Nat.sub_diag /=. done. }
           (* freshness: existing same-client cells lie below this item's clock *)
           have Hgmax0 : ∀ c0, c0 ∈ all_cells types_c ->
               cell_client c0 = W64 (clientId (in_id input)) ->
               (uint.Z (cell_clock c0) < uint.Z (W64 (clock (in_id input))))%Z ∧
               (uint.Z (cell_clock c0) + Z.of_nat (length (ic_run c0)) <= uint.Z (W64 (clock (in_id input))))%Z.
           { move=> c0 Hc0 Hcc0.
             have [Hcb0 Hkb0] := Hbndsc c0 Hc0.
             have Hzc0 : (uint.Z (cell_clock c0) = Z.of_nat (clock (item_id (run_head c0))))%Z
               by (rewrite /cell_clock; word).
             have Hccn : clientId (item_id (run_head c0)) = clientId (in_id input).
             { move: Hcc0. rewrite /cell_client. move=> Hcc.
               have Hz : uint.Z (W64 (clientId (item_id (run_head c0)))) = uint.Z (W64 (clientId (in_id input)))
                 by rewrite Hcc.
               have Hib2 : (Z.of_nat (clientId (in_id input)) < 2^64)%Z
                 := proj1 (Hidb (tj, input) Hpending0in).
               clear -Hz Hcb0 Hib2. word. }
             have Hwfc0 : run_wf (ic_run c0) := Hrunwfc c0 Hc0.
             have Hlen0 : (1 <= length (ic_run c0))%nat.
             { destruct (ic_run c0) eqn:E; [exact (False_ind _ (proj1 Hwfc0 eq_refl)) | simpl; lia]. }
             destruct (Hprovc c0 Hc0) as [(c1 & Hc1 & Hcl1 & Hlo1 & Hhi1) | (ti & Hti & Hcc1 & Hlo1 & Hhi1)].
             - (* original cell c1 ∈ types: [expand_inputs_arr_fresh] via its last char *)
               have Hc1all := Hc1. apply all_cells_elem_of in Hc1 as (p1 & ts1 & Hp1 & Hcts1).
               have Hwf1 : run_wf (ic_run c1) := Hrunwf_init c1 Hc1all.
               have Hlen1 : (1 <= length (ic_run c1))%nat.
               { destruct (ic_run c1) eqn:E; [exact (False_ind _ (proj1 Hwf1 eq_refl)) | simpl; lia]. }
               destruct (lookup_lt_is_Some_2 (ic_run c1) (length (ic_run c1) - 1)%nat ltac:(lia)) as [xl Hxl].
               have Hxlid := run_wf_char_id (ic_run c1) _ xl Hwf1 Hxl.
               destruct (Htypesbound p1 (ex_intro _ ts1 Hp1)) as [name1 Hbnm1].
               have Hdg1 : docm_get m (RootId name1) = ty_arr ts1 := Hmtypes name1 p1 ts1 Hbnm1 Hp1.
               have Hrep1 : ty_arr ts1 = run_flatten (ty_cells ts1) := Hreprall_init p1 ts1 Hp1.
               apply list_elem_of_lookup_1 in Hcts1 as [ci1 Hci1].
               have Hxlmem : xl ∈ docm_get m (RootId name1).
               { rewrite Hdg1 Hrep1.
                 apply (list_elem_of_lookup_2 _
                          (length (run_flatten (take ci1 (ty_cells ts1))) + (length (ic_run c1) - 1))%nat).
                 exact (run_flatten_lookup_of_cell (ty_cells ts1) ci1 _ c1 xl Hci1 Hxl). }
               have [Hcb1 Hkb1c] := Hbnds_init c1 Hc1all.
               have Hzc1 : (uint.Z (cell_clock c1) = Z.of_nat (clock (item_id (run_head c1))))%Z
                 by (rewrite /cell_clock; word).
               have Hxlcl : clientId (item_id xl) = clientId (in_id input).
               { rewrite Hxlid /run_head /=.
                 have Hclc : clientId (item_id (run_head c1)) = clientId (item_id (run_head c0)).
                 { move: Hcl1. rewrite /cell_client. move=> Hcc.
                   have Hz : uint.Z (W64 (clientId (item_id (run_head c0)))) = uint.Z (W64 (clientId (item_id (run_head c1))))
                     by rewrite Hcc.
                   clear -Hz Hcb0 Hcb1. word. }
                 rewrite /run_head in Hclc. rewrite Hclc Hccn //. }
               have Hxlfr := expand_inputs_arr_fresh applied m m' Hvr (length (appliedj ++ appacc))
                               (tj, input) HKlk Hne1 (RootId name1) xl Hxlmem Hxlcl.
               change ((tj, input).2) with input in Hxlfr.
               have Hxlck : (clock (item_id xl)
                             = clock (item_id (hd inhabitant (ic_run c1))) + (length (ic_run c1) - 1))%nat
                 by rewrite Hxlid.
               rewrite Hxlck in Hxlfr.
               have Hc1fr : (Z.of_nat (clock (item_id (hd inhabitant (ic_run c1)))) + Z.of_nat (length (ic_run c1))
                             <= Z.of_nat (clock (in_id input)))%Z.
               { clear -Hxlfr Hlen1. lia. }
               rewrite /run_head in Hzc0 Hzc1.
               rewrite Hzc0 in Hlo1 Hhi1. rewrite Hzc1 in Hlo1 Hhi1.
               rewrite !Hzc0 !Hib. split; lia.
             - (* batch cell: [expand_inputs_range_causal] on the applied replay *)
               have Hti_in : ti ∈ applied.
               { rewrite Happdec (app_assoc appliedj appacc). apply elem_of_app. by left. }
               have Hti_pi : ti ∈ pend0 ++ inputs := Happliedsub ti Hti_in.
               destruct (list_elem_of_lookup_1 _ _ Hti) as [jb Hj0].
               have Hjlt : (jb < length (appliedj ++ appacc))%nat by (apply lookup_lt_Some in Hj0; lia).
               have Hjapp : applied !! jb = Some ti.
               { rewrite Happdec (app_assoc appliedj appacc) lookup_app_l; last exact Hjlt.
                 exact Hj0. }
               have Hcln : clientId (in_id ti.2) = clientId (in_id input).
               { have Hz : uint.Z (W64 (clientId (in_id ti.2))) = uint.Z (W64 (clientId (in_id input)))
                   by rewrite -Hcc1 Hcc0.
                 have Hib2 : (Z.of_nat (clientId (in_id input)) < 2^64)%Z
                   := proj1 (Hidb (tj, input) Hpending0in).
                 have Hib3 : (Z.of_nat (clientId (in_id ti.2)) < 2^64)%Z
                   := proj1 (Hidb ti Hti_pi).
                 clear -Hz Hib2 Hib3. word. }
               have Hnei : (1 <= length (in_content ti.2))%nat := Hnonempty ti Hti_pi.
               have Htifr := expand_inputs_range_causal applied m m' Hvr
                               (length (appliedj ++ appacc)) jb (tj, input) ti HKlk Hjapp Hjlt
                               Hcln Hnei Hne1.
               change ((tj, input).2) with input in Htifr.
               have Hib4 : uint.Z (W64 (clock (in_id ti.2))) = Z.of_nat (clock (in_id ti.2))
                 := uint_W64_nat_bound _ _ (Hkb1 ti Hti_pi).
               split; move: Hlo1 Hhi1; rewrite !Hib !Hib4; lia. }
           simpl. rewrite Hready. wp_auto.
           wp_apply (wp_store__integrateDecoded s mref tref uiv (tj, input)
                       m_c types_c bind nit arr' nm pl
                       Htjeq Hbnm Htoit Hvld Hmax Hall Hgmax0
                       Hbindtypesc Hbindinj Hmtypesc Hnwc
                       Hlocdupc Hrangedisjc Hfitsc Horiginclkc
                       with "[$Hui $Hitemsf $Hitemmap $Htypesf $Htypesmap $Htypes]").
           iIntros (types'') "(Hitemsf & Hitemmap & Htypesf & Htypesmap & Htypes & %Hdom'' & %Hmtypes'' & %Hprov'' & %Hlocdup'' & %Hrangedisj'' & %Hfits'' & %Horiginclk'')".
           wp_auto. wp_for_post.
           iFrame "Hcapin Hpendf HΦ s Hslin Hpendingp HslP HcapP".
           iExists (S i), true, restS, uivsR, keptacc, (appacc ++ [(tj, input)]),
             app2, af2, types'', (<[tj := arr']> m_c).
           replace (word.add (W64 i) (W64 1)) with (W64 (S i)) by word.
           iFrame "Hii Hprog Hrestp HslR HcapR Hitemsf Hitemmap Htypesf Htypesmap Htypes".
           iFrame "HitemsR".
           iPureIntro. split_and!.
           ++ apply (lookup_lt_Some _ _ _ Hpi).
           ++ exact Hrec.
           ++ rewrite -app_assoc /=. exact Hpassc.
           ++ rewrite -app_assoc /=. exact Happdec.
           ++ exact Hvrtail.
           ++ rewrite app_assoc.
              apply (WireReplay_app m m_c _ (appliedj ++ appacc) [(tj, input)] Hprc).
              apply (WireReplay_cons m_c (tj, input) arr' [] _ Hd Hready Hint').
              constructor.
           ++ exact Hkeptsub.
           ++ split; [move=> Hf; discriminate | move=> Habs; by destruct appacc].
           ++ by rewrite Hdom''.
           ++ exact Hmtypes''.
           ++ move=> t Hne.
              destruct (decide (t = tj)) as [-> | Hnet].
              { exists nm, pl. split; [exact Htjeq | exact Hbnm]. }
              rewrite docm_get_insert_ne // in Hne.
              exact (Hmdomc t Hne).
           ++ exact Hfits''.
           ++ exact Horiginclk''.
           ++ move=> c0 Hc0.
              destruct (Hprov'' c0 Hc0) as [(c1 & Hc1 & Hcl1 & Hlo1 & Hhi1) | (Hcc & Hlo & Hhi)].
              ** destruct (Hprovc c1 Hc1) as [(c2 & Hc2 & Hcl2 & Hlo2 & Hhi2) | (ti & Hti & Hcc2 & Hlo2 & Hhi2)].
                 { left. exists c2. split_and!; [exact Hc2 | congruence | lia | lia]. }
                 { right. exists ti. rewrite app_assoc. split_and!;
                     [apply elem_of_app; by left | congruence | lia | lia]. }
              ** right. exists (tj, input). rewrite app_assoc. split_and!;
                   [apply elem_of_app; right; apply elem_of_cons; by left
                   | exact Hcc | exact Hlo | exact Hhi].
           ++ exact Hlocdup''.
           ++ exact Hrangedisj''.
        -- (* blocked: keep (deduplicated by id) *)
           rewrite (drop_S pendingj (tj, input) i Hpi) /= Hd Hready in Hpassa.
           simpl. rewrite Hready. wp_auto.
           wp_apply (wp_containsUpdateItemId restS (DfracOwn 1) keptacc
                       (uiv.(yjs.updateItem.id')) with "[HslR HcapR]").
           { iExists uivsR. iFrame "HslR HcapR HitemsR". }
           iIntros "Hos". iDestruct "Hos" as (uivsR2) "(HslR & HcapR & #HitemsR2)".
           rewrite Hin_id.
           destruct (existsb (λ tj0, bool_decide (in_id tj0.2 = in_id input))
                       keptacc) eqn:Hex.
           ** (* already kept: skip *)
              wp_auto. wp_for_post.
              iFrame "Hcapin Hpendf HΦ s Hslin Hpendingp HslP HcapP".
              iExists (S i), pvi, restS, uivsR2, keptacc, appacc, app_rem, af2,
                types_c, m_c.
              replace (word.add (W64 i) (W64 1)) with (W64 (S i)) by word.
              iFrame "Hii Hprog Hrestp HslR HcapR Hitemsf Hitemmap Htypesf Htypesmap Htypes".
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
              iFrame "Hcapin Hpendf HΦ s Hslin Hpendingp HslP HcapP".
              iExists (S i), pvi, restS', (uivsR2 ++ [uiv]),
                (keptacc ++ [(tj, input)]), appacc, app_rem, af2, types_c, m_c.
              replace (word.add (W64 i) (W64 1)) with (W64 (S i)) by word.
              have H00 : sint.nat (W64 0) = 0%nat by word.
              iEval (rewrite H00 /=) in "HslR'".
              iFrame "Hii Hprog Hrestp HslR' HcapR' Hitemsf Hitemmap Htypesf Htypesmap Htypes".
              iSplit.
              { rewrite big_sepL2_snoc.
                iSplit; [iFrame "HitemsR2" | iFrame "Hui"]. }
              iPureIntro. split_and!; try done.
              --- apply (lookup_lt_Some _ _ _ Hpi).
              --- rewrite /pending_keep /= Hex in Hpassa. exact Hpassa.
              --- move=> ti Hti. apply elem_of_app in Hti.
                  destruct Hti as [Hti | Hti]; first exact (Hkeptsub ti Hti).
                  apply list_elem_of_singleton in Hti. subst ti.
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
        iFrame "Hcapin Hpendf HΦ s Hslin".
        iExists pvi, restS, uivsR, keptacc, (appliedj ++ appacc), af2,
          types_c, m_c.
        iFrame "Hprog Hpendingp HslR HcapR Hitemsf Hitemmap Htypesf Htypesmap Htypes".
        iFrame "HitemsR".
        iPureIntro. split_and!.
        ** move=> ti Hti. apply Hpendingsubj. exact (Hkeptsub ti Hti).
        ** exact Hprc.
        ** exact Hdomc.
        ** exact Hmtypesc.
        ** exact Hmdomc.
        ** exact Hfitsc.
        ** exact Horiginclkc.
        ** exact Hprovc.
        ** exact Hlocdupc.
        ** exact Hrangedisjc.
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
      wp_auto.
      iApply ("HΦ" $! pendingS typesj).
      iFrame "Hpendf Hitemsf Hitemmap Htypesf Htypesmap Htypes".
      iSplitL "Hslin Hcapin".
      { iExists uivs_in. iFrame "Hslin Hcapin Hitemsin". }
      iSplitL "HslP HcapP".
      { iExists uivsP. iFrame "HslP HcapP HitemsPj". }
      iPureIntro. split_and!.
      * exact Hdomj.
      * exact Hmtypesj.
      * exact Hmdomj.
      * move=> c0 Hc0.
        destruct (Hprovj c0 Hc0) as [Hold | (ti & Hti & Hcc & Hlo & Hhi)]; [by left |].
        right. exists ti. rewrite Happeq. split_and!; [exact Hti | exact Hcc | exact Hlo | exact Hhi].
      * exact Hlocdupj.
      * exact Hrangedisjj.
      * exact Hfitsj.
      * exact Horiginclkj.
Qed.

(* ===== wire-drain bridge lemmas (issue #40 x issue #28 U7c) ===============
   Pure structural facts relating a [wire_drain] to its applied/leftover lists
   and to the per-char model, all provable against the [wire_pass] / [wire_drain]
   / [WireReplay] definitions in [yjs_store_node]. The certificate spec below
   composes them: [wire_drain_subset] recertifies the leftover pending,
   [wire_drain_replay] exposes the applied list as a [WireReplay], and
   [expand_inputs_subset] carries the per-char certificates from the drained
   batch to its applied sublist. *)

(** The applied and leftover lists of a wire pass are drawn from the pending. *)
Lemma wire_pass_subset (pending : list (TId * IntegrateInput (A := A))) :
  ∀ m kept app kept' m',
    wire_pass m pending kept = (app, kept', m') ->
    (∀ ti, ti ∈ app -> ti ∈ pending) ∧
    (∀ ti, ti ∈ kept' -> ti ∈ kept ∨ ti ∈ pending).
Proof.
  elim: pending => [| ti0 tl IH] m kept app kept' m' /=.
  - move=> [= <- <- _]. split; [move=> ti Hin; by apply elem_of_nil in Hin |].
    move=> ti Hin. by left.
  - destruct (docm_has m (in_id ti0.2)).
    { move=> /IH [Happ Hkept]. split.
      - move=> ti Hin. apply elem_of_cons. right. exact (Happ ti Hin).
      - move=> ti Hin. destruct (Hkept ti Hin) as [Hk | Hp]; [by left |].
        right. apply elem_of_cons. by right. }
    destruct (input_ready m ti0.2); last first.
    { move=> /IH [Happ Hkept]. split.
      - move=> ti Hin. apply elem_of_cons. right. exact (Happ ti Hin).
      - move=> ti Hin. destruct (Hkept ti Hin) as [Hk | Hp].
        + destruct (pending_keep_subset kept ti0 ti Hk) as [Hk' | ->]; [by left |].
          right. apply elem_of_cons. by left.
        + right. apply elem_of_cons. by right. }
    destruct (wire_intg m ti0) as [arr' |]; last first.
    { move=> /IH [Happ Hkept]. split.
      - move=> ti Hin. apply elem_of_cons. right. exact (Happ ti Hin).
      - move=> ti Hin. destruct (Hkept ti Hin) as [Hk | Hp].
        + destruct (pending_keep_subset kept ti0 ti Hk) as [Hk' | ->]; [by left |].
          right. apply elem_of_cons. by left.
        + right. apply elem_of_cons. by right. }
    destruct (wire_pass (<[ti0.1 := arr']> m) tl kept) as [[app0 kept0] m0] eqn:Hrec.
    move=> [= <- <- _].
    destruct (IH _ _ _ _ _ Hrec) as [Happ Hkept]. split.
    + move=> ti Hin. apply elem_of_cons in Hin.
      destruct Hin as [-> | Hin]; [by left | right; exact (Happ ti Hin)].
    + move=> ti Hin. destruct (Hkept ti Hin) as [Hk | Hp]; [by left |].
      right. apply elem_of_cons. by right.
Qed.

Lemma wire_drain_aux_subset (fuel : nat) :
  ∀ (m : DocM) (pending app rest : list (TId * IntegrateInput (A := A))) (m' : DocM),
    wire_drain_aux fuel m pending = (app, rest, m') ->
    (∀ ti, ti ∈ app -> ti ∈ pending) ∧ (∀ ti, ti ∈ rest -> ti ∈ pending).
Proof.
  elim: fuel => [| f IH] m pending app rest m' /=.
  - move=> [= <- <- _]. split; [move=> ti Hin; by apply elem_of_nil in Hin | done].
  - destruct (wire_pass m pending []) as [[app0 kept] m0] eqn:Hpass.
    destruct (wire_pass_subset pending m [] app0 kept m0 Hpass) as [Happ0 Hkept0].
    have Hkept0' : ∀ ti, ti ∈ kept -> ti ∈ pending.
    { move=> ti Hin. destruct (Hkept0 ti Hin) as [Hk | Hp];
        [by apply elem_of_nil in Hk | done]. }
    destruct app0 as [| a app0'].
    { move=> [= <- <- _]. split; [move=> ti Hin; by apply elem_of_nil in Hin | done]. }
    destruct (wire_drain_aux f m0 kept) as [[app2 rest2] m2] eqn:Hrec.
    move=> [= <- <- _].
    destruct (IH _ _ _ _ _ Hrec) as [Happ2 Hrest2]. split.
    + move=> ti Hin.
      apply elem_of_cons in Hin. destruct Hin as [-> | Hin].
      * apply (Happ0 a). apply elem_of_cons. by left.
      * apply elem_of_app in Hin. destruct Hin as [Hin | Hin].
        -- apply (Happ0 ti). apply elem_of_cons. by right.
        -- exact (Hkept0' ti (Happ2 ti Hin)).
    + move=> ti Hin. exact (Hkept0' ti (Hrest2 ti Hin)).
Qed.

Lemma wire_drain_subset (m : DocM)
    (pending app rest : list (TId * IntegrateInput (A := A))) (m' : DocM) :
  wire_drain m pending = (app, rest, m') ->
  (∀ ti, ti ∈ app -> ti ∈ pending) ∧ (∀ ti, ti ∈ rest -> ti ∈ pending).
Proof. apply wire_drain_aux_subset. Qed.

Lemma wire_drain_aux_replay (fuel : nat) :
  ∀ (m : DocM) (pending app rest : list (TId * IntegrateInput (A := A))) (m' : DocM),
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

Lemma wire_drain_replay (m : DocM)
    (pending app rest : list (TId * IntegrateInput (A := A))) (m' : DocM) :
  wire_drain m pending = (app, rest, m') ->
  WireReplay m app m'.
Proof. apply wire_drain_aux_replay. Qed.

(** [expand_inputs] is monotone over list membership: a per-char certificate for
    the whole drained batch specializes to any applied/leftover sublist. *)
Lemma expand_inputs_subset (a b : list (TId * IntegrateInput (A := A))) :
  (∀ ti, ti ∈ a -> ti ∈ b) ->
  (∀ ti, ti ∈ expand_inputs a -> ti ∈ expand_inputs b).
Proof.
  move=> Hsub ti. rewrite /expand_inputs !list_elem_of_join.
  move=> [l [Hti Hl]]. exists l. split; [exact Hti |].
  apply list_elem_of_fmap in Hl as [x [-> Hx]].
  apply list_elem_of_fmap. exists x. split; [done | exact (Hsub x Hx)].
Qed.

(* ===== wire chunk -> per-char PendingReplay bridge (issue #40 x #28 U7c) ===
   A WIRE item integrates its whole run atomically ([wire_intg] =
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
Lemma docm_has_integrate_ne (m : DocM) (t : TId) (input : IntegrateInput (A := A))
    (arr' : list (YjsItem A)) (d : YjsId) :
  integrate input (docm_get m t) = Some arr' ->
  d ≠ in_id input ->
  docm_has m d = false ->
  docm_has (<[t := arr']> m) d = false.
Proof.
  move=> Hint Hne Hfalse.
  destruct (docm_has (<[t := arr']> m) d) eqn:Hh; [| done].
  exfalso. apply docm_has_spec in Hh. destruct Hh as (t' & x & Hx & Hid).
  destruct (decide (t' = t)) as [-> | Hnet].
  - rewrite docm_get_insert_eq in Hx.
    destruct (integrate_mem_inv input (docm_get m t) arr' x Hint Hx) as [Hxid | Hin].
    + apply Hne. by rewrite -Hid Hxid.
    + have : docm_has m d = true.
      { apply docm_has_spec. exists t, x. split; [exact Hin | exact Hid]. }
      by rewrite Hfalse.
  - rewrite docm_get_insert_ne // in Hx.
    have : docm_has m d = true.
    { apply docm_has_spec. exists t', x. split; [exact Hx | exact Hid]. }
    by rewrite Hfalse.
Qed.

(** The core chunk-replay: folding [integrate] over one wire item's per-char
    op chain ([ops_from]) is a valid per-char [PendingReplay] at a single type
    [t], provided the head's dependencies are present and every char id is
    fresh. Freshness of char [k>0] follows from the head-freshness plus
    [docm_has_integrate_ne] (the earlier chars only add their own ids). *)
Lemma ops_from_pending_replay (t : TId) (cl : nat) (rid : option YjsId) :
  ∀ (chars : list A) (ck : nat) (oid : option YjsId) (m : DocM) (arr' : list (YjsItem A)),
    is_Some (m !! t) ->
    (∀ o, oid = Some o -> docm_has m o = true) ->
    (∀ o, rid = Some o -> docm_has m o = true) ->
    (∀ j, ck = S j -> docm_has m (MkYjsId cl j) = true) ->
    (∀ j, (j < length chars)%nat -> docm_has m (MkYjsId cl (ck + j)) = false) ->
    integrate_all (ops_from cl ck oid rid chars) (docm_get m t) = Some arr' ->
    PendingReplay m ((λ op, (t, op)) <$> ops_from cl ck oid rid chars) (<[t := arr']> m).
Proof.
  elim => [| ch rest IH] ck oid m arr' Hsome Hoid Hrid Hpred Hfresh Hint /=.
  - simpl in Hint. injection Hint as <-.
    destruct Hsome as [v Hv].
    have -> : docm_get m t = v by rewrite /docm_get Hv.
    rewrite insert_id //. constructor.
  - simpl in Hint.
    apply bind_Some in Hint. destruct Hint as (arr0 & Hint0 & Hintr).
    set hop := MkIntegrateInput oid rid ch (MkYjsId cl ck).
    have Hhid : in_id hop = MkYjsId cl ck by done.
    have Hfresh0 : docm_has m (MkYjsId cl ck) = false.
    { have := Hfresh 0%nat ltac:(simpl; lia). rewrite Nat.add_0_r //. }
    have Hready : input_ready m hop = true.
    { apply input_ready_true_of.
      - move=> o Ho. exact (Hoid o Ho).
      - move=> o Ho. exact (Hrid o Ho).
      - move=> k Hk. exact (Hpred k Hk). }
    set m1 := <[t := arr0]> m.
    have Hsome1 : is_Some (m1 !! t). { exists arr0. rewrite /m1 lookup_insert_eq //. }
    have Hhead_in : docm_has m1 (MkYjsId cl ck) = true.
    { destruct (integrate_new_mem hop (docm_get m t) arr0 Hint0) as (it & Hitid & Hitmem).
      apply docm_has_spec. exists t, it. split.
      - rewrite /m1 docm_get_insert_eq. exact Hitmem.
      - rewrite Hitid /hop //. }
    have Hoid1 : ∀ o, Some (MkYjsId cl ck) = Some o -> docm_has m1 o = true.
    { move=> o [= <-]. exact Hhead_in. }
    have Hrid1 : ∀ o, rid = Some o -> docm_has m1 o = true.
    { move=> o Ho. rewrite /m1. apply (docm_has_integrate_mono m t hop arr0 o Hint0).
      exact (Hrid o Ho). }
    have Hpred1 : ∀ j, S ck = S j -> docm_has m1 (MkYjsId cl j) = true.
    { move=> j [= <-]. exact Hhead_in. }
    have Hfresh1 : ∀ j, (j < length rest)%nat -> docm_has m1 (MkYjsId cl (S ck + j)) = false.
    { move=> j Hj.
      have Hfr : docm_has m (MkYjsId cl (S ck + j)) = false.
      { have := Hfresh (S j) ltac:(simpl; lia). by rewrite -Nat.add_succ_comm. }
      rewrite /m1. apply (docm_has_integrate_ne m t hop arr0 _ Hint0); [| exact Hfr].
      rewrite Hhid. move=> [= Habs]. lia. }
    have Hint1 : integrate_all (ops_from cl (S ck) (Some (MkYjsId cl ck)) rid rest)
                   (docm_get m1 t) = Some arr'.
    { rewrite /m1 docm_get_insert_eq. exact Hintr. }
    have Hstep := IH (S ck) (Some (MkYjsId cl ck)) m1 arr' Hsome1 Hoid1 Hrid1 Hpred1 Hfresh1 Hint1.
    have Hrw : <[t := arr']> m1 = <[t := arr']> m by rewrite /m1 insert_insert_eq.
    rewrite Hrw in Hstep.
    apply (PendingReplay_cons m (t, hop) arr0
             ((λ op, (t, op)) <$> ops_from cl (S ck) (Some (MkYjsId cl ck)) rid rest)
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
    (l : list (TId * IntegrateInput (A := A))) (m0 m1 : DocM) :
  ValidReplay l m0 m1 ->
  ∀ ti : TId * IntegrateInput (A := A), ti ∈ l -> docm_get m1 ti.1 ≠ [].
Proof.
  elim => [mx | t input rest0 mr arr2 mr' nit Htoit Hvld Hmax Hglob Hint Hrest IH]
    ti Hin.
  - by apply elem_of_nil in Hin.
  - apply elem_of_cons in Hin. destruct Hin as [-> | Hin]; last exact (IH ti Hin).
    simpl.
    destruct (integrate_new_mem input _ _ Hint) as (it & Hid & Hit).
    have Hit' : it ∈ docm_get mr' t.
    { apply (ValidReplay_mem rest0 (<[t := arr2]> mr) mr' Hrest t).
      rewrite docm_get_insert_eq //. }
    move=> Heq. rewrite Heq in Hit'. by apply elem_of_nil in Hit'.
Qed.

(* ===== NEW lemmas ======================================================== *)

Lemma expand_inputs_cons (ti : TId * IntegrateInput (A := A))
    (rest : list (TId * IntegrateInput (A := A))) :
  expand_inputs (ti :: rest) = expand_input ti ++ expand_inputs rest.
Proof. rewrite /expand_inputs fmap_cons join_cons //. Qed.

(** The [is_Some]-free variant: for a NONEMPTY chunk, the first char's
    integration establishes the key, so no [is_Some (m !! ti.1)] hypothesis is
    needed (the origin-less-into-empty-root case, issue #49). *)
Lemma expand_input_pending_replay_ne (m : DocM) (ti : TId * IntegrateInput (A := A))
    (arr' : list (YjsItem A)) :
  (1 <= length (in_content ti.2))%nat ->
  input_ready m ti.2 = true ->
  (∀ k, (k < length (in_content ti.2))%nat ->
     docm_has m (MkYjsId (clientId (in_id ti.2)) (clock (in_id ti.2) + k)) = false) ->
  wire_intg m ti = Some arr' ->
  PendingReplay m (expand_input ti) (<[ti.1 := arr']> m).
Proof.
  move=> Hne Hready Hfresh Hint.
  rewrite /expand_input /wire_intg /ops_of_input in Hint *.
  set cl := clientId (in_id ti.2).
  set ck := clock (in_id ti.2).
  set oid := in_originId ti.2.
  set rid := in_rightOriginId ti.2.
  have Hexplen : length (explode (in_content ti.2)) = length (in_content ti.2)
    by rewrite /explode length_fmap.
  destruct (explode (in_content ti.2)) as [| ch rest'] eqn:Hexp.
  { simpl in Hexplen. lia. }
  simpl in Hint.
  set hop := MkIntegrateInput oid rid ch (MkYjsId cl ck).
  apply bind_Some in Hint. destruct Hint as (arr0 & Hint0 & Hintr).
  have Hhid : in_id hop = MkYjsId cl ck by done.
  have Hfresh0 : docm_has m (MkYjsId cl ck) = false.
  { have := Hfresh 0%nat ltac:(lia). rewrite Nat.add_0_r //. }
  have Hready0 : input_ready m hop = true.
  { apply input_ready_true_of.
    - move=> o Ho. apply (proj1 (input_ready_spec m ti.2) Hready).
      exact (input_deps_originL ti.2 o Ho).
    - move=> o Ho. apply (proj1 (input_ready_spec m ti.2) Hready).
      exact (input_deps_originR ti.2 o Ho).
    - move=> k Hk. apply (proj1 (input_ready_spec m ti.2) Hready).
      rewrite /input_deps !elem_of_app. right. right.
      have Hck : clock (in_id ti.2) = S k by exact Hk.
      rewrite Hck /=. apply list_elem_of_singleton. done. }
  set m1 := <[ti.1 := arr0]> m.
  have Hsome1 : is_Some (m1 !! ti.1). { exists arr0. rewrite /m1 lookup_insert_eq //. }
  have Hhead_in : docm_has m1 (MkYjsId cl ck) = true.
  { destruct (integrate_new_mem hop (docm_get m ti.1) arr0 Hint0) as (it & Hitid & Hitmem).
    apply docm_has_spec. exists ti.1, it. split.
    - rewrite /m1 docm_get_insert_eq. exact Hitmem.
    - rewrite Hitid /hop //. }
  have Hpred1 : ∀ j, S ck = S j -> docm_has m1 (MkYjsId cl j) = true.
  { move=> j [= <-]. exact Hhead_in. }
  have Hoid1 : ∀ o, Some (MkYjsId cl ck) = Some o -> docm_has m1 o = true.
  { move=> o [= <-]. exact Hhead_in. }
  have Hrid1 : ∀ o, rid = Some o -> docm_has m1 o = true.
  { move=> o Ho. rewrite /m1. apply (docm_has_integrate_mono m ti.1 hop arr0 o Hint0).
    apply (proj1 (input_ready_spec m ti.2) Hready).
    exact (input_deps_originR ti.2 o Ho). }
  have Hfresh1 : ∀ j, (j < length rest')%nat -> docm_has m1 (MkYjsId cl (S ck + j)) = false.
  { move=> j Hj.
    have Hfr : docm_has m (MkYjsId cl (S ck + j)) = false.
    { have Hbnd : (S j < length (in_content ti.2))%nat by simpl in Hexplen; lia.
      have := Hfresh (S j) Hbnd. by rewrite -Nat.add_succ_comm. }
    rewrite /m1. apply (docm_has_integrate_ne m ti.1 hop arr0 _ Hint0); [| exact Hfr].
    rewrite Hhid. move=> [= Habs]. lia. }
  have Hint1 : integrate_all (ops_from cl (S ck) (Some (MkYjsId cl ck)) rid rest')
                 (docm_get m1 ti.1) = Some arr'.
  { rewrite /m1 docm_get_insert_eq. exact Hintr. }
  have Hstep := ops_from_pending_replay ti.1 cl rid rest' (S ck) (Some (MkYjsId cl ck))
                  m1 arr' Hsome1 Hoid1 Hrid1 Hpred1 Hfresh1 Hint1.
  have Hrw : <[ti.1 := arr']> m1 = <[ti.1 := arr']> m by rewrite /m1 insert_insert_eq.
  rewrite Hrw in Hstep.
  simpl.
  apply (PendingReplay_cons m (ti.1, hop) arr0
           ((λ op, (ti.1, op)) <$> ops_from cl (S ck) (Some (MkYjsId cl ck)) rid rest')
           (<[ti.1 := arr']> m) Hfresh0 Hready0 Hint0 Hstep).
Qed.

(** From HEAD freshness to WHOLE-CHUNK freshness at a coherent document: the
    item's head is the newest op of its author (its FIRST per-char op, the one
    in the log, via [delivered_clock_bound]), so every char clock >= the head's
    is absent. The multi-char wire op itself is never in the log, so the head
    certificate is taken from the first per-char op. *)
Lemma chunk_fresh_of_head
    (N : gmap ClientId (list Ev)) (c : ClientId) (h : list Ev)
    (m : DocM) (ti : TId * IntegrateInput (A := A)) :
  history_wf N -> N !! c = Some h -> history_state_coh h m ->
  (∀ op : TId * IntegrateInput (A := A), op ∈ expand_input ti ->
     op_broadcast N (op.1, OpInsert op.2)) ->
  (1 <= length (in_content ti.2))%nat ->
  docm_has m (in_id ti.2) = false ->
  ∀ k, (k < length (in_content ti.2))%nat ->
     docm_has m (MkYjsId (clientId (in_id ti.2)) (clock (in_id ti.2) + k)) = false.
Proof.
  move=> Hwf HNc Hcoh Hcert Hnonempty Hfreshhead.
  have Hidti : in_id ti.2 = MkYjsId (clientId (in_id ti.2)) (clock (in_id ti.2))
    by destruct (in_id ti.2).
  have Hlen : length (explode (in_content ti.2)) = length (in_content ti.2)
    by rewrite /explode length_fmap.
  have [fop Hfop] : is_Some (ops_of_input ti.2 (explode (in_content ti.2)) !! 0%nat).
  { apply lookup_lt_is_Some_2. rewrite /ops_of_input ops_from_length Hlen. lia. }
  have Hfopid : in_id fop = in_id ti.2.
  { have [Hid _] := ops_from_lookup (clientId (in_id ti.2)) (clock (in_id ti.2))
      (in_originId ti.2) (in_rightOriginId ti.2) (explode (in_content ti.2)) 0%nat fop Hfop.
    rewrite Hid Nat.add_0_r -Hidti //. }
  have Hbcfop : op_broadcast N (ti.1, OpInsert fop).
  { have Hmem : (ti.1, fop) ∈ expand_input ti.
    { apply (list_elem_of_lookup_2 _ 0%nat). by apply expand_input_lookup. }
    exact (Hcert (ti.1, fop) Hmem). }
  have Hfreshfop : docm_has m (in_id fop) = false by rewrite Hfopid.
  have Hnotdel : in_id fop ∉ delivered_ids h.
  { move=> Hdel. apply elem_of_delivered_ids in Hdel. destruct Hdel as (y & Hyh & Hyid).
    have Hins : ∃ inputy, y.2 = OpInsert inputy.
    { apply (hwf_insert_only N Hwf c y). right. rewrite (to_histories_lookup N c h HNc) //. }
    destruct Hins as (inputy & Hy2). destruct y as [ty y2]. simpl in Hy2. subst y2.
    have Hdel2 : (ty, OpInsert inputy) ∈ delivered_ops h by apply elem_of_delivered_ops_ev.
    have := delivered_docm_has h m ty inputy Hcoh Hdel2.
    have -> : in_id inputy = in_id fop by exact Hyid.
    rewrite Hfreshfop //. }
  have Hclk := delivered_clock_bound N c h m ((ti.1, OpInsert fop) : Op) Hwf HNc Hcoh Hbcfop Hnotdel.
  move=> k Hk.
  destruct (docm_has m (MkYjsId (clientId (in_id ti.2)) (clock (in_id ti.2) + k))) eqn:Hh;
    [| done].
  exfalso. apply docm_has_spec in Hh. destruct Hh as (t' & x & Hx & Hxid).
  have Hcc : clientId (item_id x) = clientId (in_id fop).
  { rewrite Hxid /=. rewrite Hfopid //. }
  have Hlt := Hclk t' x Hx Hcc.
  rewrite Hxid /= in Hlt.
  change (DocOp_id (ti.1, OpInsert fop)) with (in_id fop) in Hlt.
  rewrite Hfopid /= in Hlt. lia.
Qed.

(** THE CRUX: a wire drain refines a per-char [PendingReplay] of its
    expansion. Chunk freshness at each intermediate is RE-DERIVED from the
    head's freshness via [chunk_fresh_of_head], keeping the
    intermediate coherent via [pending_ValidReplay]; no batch range-disjointness
    is needed. *)
Lemma WireReplay_to_PendingReplay
    (m0 : DocM) (applied : list (TId * IntegrateInput (A := A))) (m0' : DocM)
    (HWR : WireReplay m0 applied m0') :
  ∀ (N : gmap ClientId (list Ev)) (c : ClientId) (h : list Ev),
    history_wf N -> N !! c = Some h -> history_state_coh h m0 ->
    (∀ t : TId, YjsArrInvariant (docm_get m0 t)) ->
    (∀ (ti : TId * IntegrateInput (A := A)) (op : TId * IntegrateInput (A := A)),
       ti ∈ applied -> op ∈ expand_input ti ->
       op_broadcast N (op.1, OpInsert op.2)) ->
    (∀ ti : TId * IntegrateInput (A := A), ti ∈ applied ->
       (1 <= length (in_content ti.2))%nat) ->
    PendingReplay m0 (expand_inputs applied) m0'.
Proof.
  elim: HWR => [mx | mx ti arr' rest mx' Hdup Hready Hint Hrest IH]
    N c h Hwf HNc Hcoh Harrinv Hcharcert Hnonempty.
  - rewrite /expand_inputs /=. constructor.
  - have Hin_ti : ti ∈ ti :: rest by left.
    have Hne := Hnonempty ti Hin_ti.
    have Hfresh := chunk_fresh_of_head N c h mx ti Hwf HNc Hcoh
                     (λ op Hop, Hcharcert ti op Hin_ti Hop) Hne Hdup.
    have Hpr1 : PendingReplay mx (expand_input ti) (<[ti.1 := arr']> mx)
      := expand_input_pending_replay_ne mx ti arr' Hne Hready Hfresh Hint.
    (* coherence at mx1 via pending_ValidReplay on the chunk *)
    have Hcharcert_ti : ∀ op : TId * IntegrateInput (A := A), op ∈ expand_input ti ->
        op_broadcast N (op.1, OpInsert op.2) := λ op Hop, Hcharcert ti op Hin_ti Hop.
    pose proof (pending_ValidReplay N c h mx (expand_input ti) (<[ti.1 := arr']> mx)
                  Hwf HNc Hcoh Hcharcert_ti Hpr1) as (Hvr1 & Hcoh1 & Hwf1 & _).
    set N' := <[c := h ++ (deliver_ev <$> expand_input ti)]> N.
    set h' := h ++ (deliver_ev <$> expand_input ti).
    have HN'c : N' !! c = Some h' by rewrite /N' lookup_insert_eq.
    have Harrinv1 : ∀ t : TId, YjsArrInvariant (docm_get (<[ti.1 := arr']> mx) t)
      := ValidReplay_arrinv (expand_input ti) mx (<[ti.1 := arr']> mx) Hvr1 Harrinv.
    have Hcharcert' : ∀ (tj : TId * IntegrateInput (A := A)) (op : TId * IntegrateInput (A := A)),
        tj ∈ rest -> op ∈ expand_input tj -> op_broadcast N' (op.1, OpInsert op.2).
    { move=> tj op Htj Hop. apply (proj2 (op_broadcast_append N c h _ _ HNc)). left.
      apply (Hcharcert tj op); [by right | done]. }
    have Hnonempty' : ∀ tj : TId * IntegrateInput (A := A), tj ∈ rest ->
        (1 <= length (in_content tj.2))%nat.
    { move=> tj Htj. apply Hnonempty. by right. }
    have Hpr2 := IH N' c h' Hwf1 HN'c Hcoh1 Harrinv1 Hcharcert' Hnonempty'.
    rewrite expand_inputs_cons.
    exact (PendingReplay_app mx (<[ti.1 := arr']> mx) mx' _ _ Hpr1 Hpr2).
Qed.

(** Chunk-integration totality: a certified, fresh, ready per-char chain
    integrates fully at a coherent document. Mirrors [ops_from_pending_replay]
    (same freshness cascade) but PRODUCES [is_Some] of the fold, deriving each
    char's [integrate] via [docm_valid_from_deps] + [delivered_clock_bound] +
    [integrate_some_of_toItem] at the coherence advanced along the chunk. *)
Lemma ops_from_ready (t : TId) (cl : nat) (rid : option YjsId) :
  ∀ (chars : list A) (ck : nat) (oid : option YjsId)
    (N : gmap ClientId (list Ev)) (c : ClientId) (h : list Ev) (m : DocM),
    history_wf N -> N !! c = Some h -> history_state_coh h m ->
    (∀ t' : TId, YjsArrInvariant (docm_get m t')) ->
    (∀ o, oid = Some o -> docm_has m o = true) ->
    (∀ o, rid = Some o -> docm_has m o = true) ->
    (∀ j, ck = S j -> docm_has m (MkYjsId cl j) = true) ->
    (∀ j, (j < length chars)%nat -> docm_has m (MkYjsId cl (ck + j)) = false) ->
    (∀ k op, ops_from cl ck oid rid chars !! k = Some op ->
       op_broadcast N (t, OpInsert op)) ->
    is_Some (integrate_all (ops_from cl ck oid rid chars) (docm_get m t)).
Proof.
  elim => [| ch rest IH] ck oid N c h m Hwf HNc Hcoh Hinvs Hoid Hrid Hpred Hfresh Hcert /=.
  - by eexists.
  - set hop := MkIntegrateInput oid rid ch (MkYjsId cl ck).
    have Hbc : op_broadcast N (t, OpInsert hop).
    { apply (Hcert 0%nat hop). done. }
    (* origins arrive as delivered ops *)
    have Harrive : ∀ o : YjsId, (in_originId hop = Some o ∨ in_rightOriginId hop = Some o) ->
        ∃ (t' : TId) (x : IntegrateInput (A := A)),
          (t', OpInsert x) ∈ delivered_ops h ∧ in_id x = o.
    { move=> o Ho.
      have Hhas : docm_has m o = true.
      { destruct Ho as [Ho | Ho]; simpl in Ho; [exact (Hoid o Ho) | exact (Hrid o Ho)]. }
      apply docm_has_spec in Hhas. destruct Hhas as (t' & x & Hx & Hxid).
      destruct (docm_mem_delivered h m t' x Hcoh Hx) as (xin & Hxdel & Hxinid).
      exists t', xin. split; [exact Hxdel | by rewrite Hxinid Hxid]. }
    have Hval := docm_valid_from_deps N c h m t hop Hwf HNc Hcoh Hbc Harrive.
    destruct Hval as (it0 & Htoit & Hvld).
    (* head fresh -> not delivered -> maximalId *)
    have Hfresh0 : docm_has m (MkYjsId cl ck) = false.
    { have := Hfresh 0%nat ltac:(simpl; lia). rewrite Nat.add_0_r //. }
    have Hnotdel : in_id hop ∉ delivered_ids h.
    { move=> Hdel. apply elem_of_delivered_ids in Hdel. destruct Hdel as (y & Hyh & Hyid).
      have Hins : ∃ inputy, y.2 = OpInsert inputy.
      { apply (hwf_insert_only N Hwf c y). right. rewrite (to_histories_lookup N c h HNc) //. }
      destruct Hins as (inputy & Hy2). destruct y as [ty y2]. simpl in Hy2. subst y2.
      have Hdel2 : (ty, OpInsert inputy) ∈ delivered_ops h by apply elem_of_delivered_ops_ev.
      have := delivered_docm_has h m ty inputy Hcoh Hdel2.
      have -> : in_id inputy = in_id hop by exact Hyid.
      have -> : in_id hop = MkYjsId cl ck by done. rewrite Hfresh0 //. }
    have Hclk := delivered_clock_bound N c h m ((t, OpInsert hop) : Op) Hwf HNc Hcoh Hbc Hnotdel.
    have Hmax : maximalId it0 (docm_get m t).
    { move=> x Hx Hcx.
      rewrite (toItem_id hop (docm_get m t) it0 Htoit).
      have Heq : clock (in_id hop) = clock (DocOp_id ((t, OpInsert hop) : Op)) by done.
      rewrite Heq. apply (Hclk t x Hx).
      rewrite (toItem_id hop (docm_get m t) it0 Htoit) in Hcx.
      have -> : clientId (DocOp_id ((t, OpInsert hop) : Op)) = clientId (in_id hop) by done.
      exact Hcx. }
    have Hintsome := integrate_some_of_toItem hop (docm_get m t) it0 (Hinvs t) Htoit Hvld Hmax.
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
    have Hgett : docm_get m1 t = arr0 by rewrite /m1 docm_get_insert_eq.
    have Hinvs1 : ∀ t' : TId, YjsArrInvariant (docm_get m1 t').
    { move=> t'. exact (ValidReplay_arrinv [(t, hop)] m m1 Hvr1 Hinvs t'). }
    (* head now present *)
    have Hhead_in : docm_has m1 (MkYjsId cl ck) = true.
    { destruct (integrate_new_mem hop (docm_get m t) arr0 Hint0) as (itn & Hitid & Hitmem).
      apply docm_has_spec. exists t, itn. split.
      - rewrite Hgett. exact Hitmem.
      - rewrite Hitid //. }
    have Hoid1 : ∀ o, Some (MkYjsId cl ck) = Some o -> docm_has m1 o = true.
    { move=> o [= <-]. exact Hhead_in. }
    have Hrid1 : ∀ o, rid = Some o -> docm_has m1 o = true.
    { move=> o Ho. rewrite /m1. apply (docm_has_integrate_mono m t hop arr0 o Hint0).
      exact (Hrid o Ho). }
    have Hpred1 : ∀ j, S ck = S j -> docm_has m1 (MkYjsId cl j) = true.
    { move=> j [= <-]. exact Hhead_in. }
    have Hfresh1 : ∀ j, (j < length rest)%nat -> docm_has m1 (MkYjsId cl (S ck + j)) = false.
    { move=> j Hj.
      have Hfr : docm_has m (MkYjsId cl (S ck + j)) = false.
      { have := Hfresh (S j) ltac:(simpl; lia). by rewrite -Nat.add_succ_comm. }
      rewrite /m1. apply (docm_has_integrate_ne m t hop arr0 _ Hint0); [| exact Hfr].
      have -> : in_id hop = MkYjsId cl ck by done. move=> [= Habs]. lia. }
    have Hcert1 : ∀ k op, ops_from cl (S ck) (Some (MkYjsId cl ck)) rid rest !! k = Some op ->
        op_broadcast N' (t, OpInsert op).
    { move=> k op Hk. apply (proj2 (op_broadcast_append N c h _ _ HNc)). left.
      apply (Hcert (S k) op). simpl. exact Hk. }
    have Hrec := IH (S ck) (Some (MkYjsId cl ck)) N' c h' m1
                   Hwf1 HN'c Hcoh1 Hinvs1 Hoid1 Hrid1 Hpred1 Hfresh1 Hcert1.
    rewrite Hgett in Hrec. destruct Hrec as [arr' Hia].
    exists arr'. rewrite Hint0 /=. exact Hia.
Qed.

(** A fresh, ready, certified wire item integrates its whole chunk at a
    coherent document (the ready-but-stuck branch never fires). Chunk freshness
    is derived from head freshness ([delivered_clock_bound]); head origins and
    the own-predecessor gate come from [input_ready]. *)
Lemma wire_intg_some_of_certs
    (N : gmap ClientId (list Ev)) (c : ClientId) (h : list Ev)
    (m : DocM) (ti : TId * IntegrateInput (A := A)) :
  history_wf N -> N !! c = Some h -> history_state_coh h m ->
  (∀ t' : TId, YjsArrInvariant (docm_get m t')) ->
  (∀ op : TId * IntegrateInput (A := A), op ∈ expand_input ti ->
     op_broadcast N (op.1, OpInsert op.2)) ->
  (1 <= length (in_content ti.2))%nat ->
  input_ready m ti.2 = true ->
  docm_has m (in_id ti.2) = false ->
  is_Some (wire_intg m ti).
Proof.
  move=> Hwf HNc Hcoh Hinvs Hcert Hnonempty Hready Hfreshhead.
  rewrite /wire_intg /ops_of_input.
  have Hlen : length (explode (in_content ti.2)) = length (in_content ti.2)
    by rewrite /explode length_fmap.
  have Hfresh := chunk_fresh_of_head N c h m ti Hwf HNc Hcoh Hcert Hnonempty Hfreshhead.
  apply (ops_from_ready ti.1 (clientId (in_id ti.2)) (in_rightOriginId ti.2)
           (explode (in_content ti.2)) (clock (in_id ti.2)) (in_originId ti.2)
           N c h m Hwf HNc Hcoh Hinvs).
  - move=> o Ho. apply (proj1 (input_ready_spec m ti.2) Hready).
    exact (input_deps_originL ti.2 o Ho).
  - move=> o Ho. apply (proj1 (input_ready_spec m ti.2) Hready).
    exact (input_deps_originR ti.2 o Ho).
  - move=> j Hj. apply (proj1 (input_ready_spec m ti.2) Hready).
    rewrite /input_deps !elem_of_app. right. right. rewrite Hj /=.
    apply list_elem_of_singleton. done.
  - move=> j Hj. apply Hfresh. rewrite -Hlen. exact Hj.
  - move=> k op Hk.
    have Hmem : (ti.1, op) ∈ expand_input ti.
    { apply (list_elem_of_lookup_2 _ k). by apply expand_input_lookup. }
    exact (Hcert (ti.1, op) Hmem).
Qed.

(** [wire_ready_total] from the certificates: mirrors
    [pending_ready_total_of_certs] but for whole chunks. At any wire-drain
    prefix [mx], [WireReplay_to_PendingReplay] + [pending_ValidReplay] give
    coherence at [mx], and then [wire_intg_some_of_certs] fires. *)
Lemma wire_ready_total_of_certs
    (N : gmap ClientId (list Ev)) (c : ClientId) (h : list Ev) (m : DocM)
    (pending applied : list (TId * IntegrateInput (A := A))) :
  history_wf N -> N !! c = Some h -> history_state_coh h m ->
  (∀ t' : TId, YjsArrInvariant (docm_get m t')) ->
  (∀ (ti : TId * IntegrateInput (A := A)) (op : TId * IntegrateInput (A := A)),
     ti ∈ pending -> op ∈ expand_input ti -> op_broadcast N (op.1, OpInsert op.2)) ->
  (∀ ti : TId * IntegrateInput (A := A), ti ∈ pending ->
     (1 <= length (in_content ti.2))%nat) ->
  (∀ ti : TId * IntegrateInput (A := A), ti ∈ applied -> ti ∈ pending) ->
  wire_ready_total m pending applied.
Proof.
  move=> Hwf HNc Hcoh Hinvs Hcharcert Hnonempty Happsub.
  move=> pre suf mx ti Heq HWRpre Hin Hfresh Hready.
  have Hpresub : ∀ tj : TId * IntegrateInput (A := A), tj ∈ pre -> tj ∈ pending.
  { move=> tj Htj. apply Happsub. rewrite Heq elem_of_app. by left. }
  have Hpr := WireReplay_to_PendingReplay m pre mx HWRpre N c h Hwf HNc Hcoh Hinvs
                (λ tj op Htj Hop, Hcharcert tj op (Hpresub tj Htj) Hop)
                (λ tj Htj, Hnonempty tj (Hpresub tj Htj)).
  have Hcharcertpre : ∀ op : TId * IntegrateInput (A := A), op ∈ expand_inputs pre ->
      op_broadcast N (op.1, OpInsert op.2).
  { move=> op Hop.
    rewrite /expand_inputs list_elem_of_join in Hop.
    destruct Hop as (l & Hl & Hopl).
    rewrite list_elem_of_fmap in Hopl. destruct Hopl as (tj & -> & Htj).
    exact (Hcharcert tj op (Hpresub tj Htj) Hl). }
  pose proof (pending_ValidReplay N c h m (expand_inputs pre) mx Hwf HNc Hcoh Hcharcertpre Hpr)
    as (Hvrpre & Hcohmx & Hwfmx & _).
  set N' := <[c := h ++ (deliver_ev <$> expand_inputs pre)]> N.
  set h' := h ++ (deliver_ev <$> expand_inputs pre).
  have HN'c : N' !! c = Some h' by rewrite /N' lookup_insert_eq.
  have Hinvsmx : ∀ t' : TId, YjsArrInvariant (docm_get mx t').
  { move=> t'. exact (ValidReplay_arrinv (expand_inputs pre) m mx Hvrpre Hinvs t'). }
  have Hcertti : ∀ op : TId * IntegrateInput (A := A), op ∈ expand_input ti ->
      op_broadcast N' (op.1, OpInsert op.2).
  { move=> op Hop. apply (proj2 (op_broadcast_append N c h _ _ HNc)). left.
    exact (Hcharcert ti op Hin Hop). }
  exact (wire_intg_some_of_certs N' c h' mx ti Hwfmx HN'c Hcohmx Hinvsmx
           Hcertti (Hnonempty ti Hin) Hready Hfresh).
Qed.

(** Per-char [op_broadcast] of a wire pending, extracted from the ghost history:
    the log holds one certificate per CHARACTER, so [is_pending_certified] over
    [expand_inputs pending] yields [op_broadcast] for each per-char op (hence for
    each op of any [expand_input ti], [ti ∈ pending]). Shared preamble for the
    two wire wrappers below. *)
Local Lemma wire_pending_op_broadcast (γh : history_names)
    (N : gmap ClientId (list Ev)) (ops : gmap YjsId Op)
    (pending : list (TId * IntegrateInput (A := A))) :
  ops_coh N ops ->
  ([∗ list] op ∈ expand_inputs pending, is_op_cert γh (op.1, OpInsert op.2)) -∗
  ghost_map_auth γh.(hn_ops) 1 ops -∗
  ⌜∀ (ti op : TId * IntegrateInput (A := A)), ti ∈ pending -> op ∈ expand_input ti ->
     op_broadcast N (op.1, OpInsert op.2)⌝.
Proof.
  iIntros (Hopscoh) "#Hcertsin HopsAuth".
  iAssert (⌜∀ op : TId * IntegrateInput (A := A), op ∈ expand_inputs pending ->
             ops !! (in_id op.2) = Some ((op.1, OpInsert op.2) : Op)⌝)%I as %Hlk.
  { iIntros (op Hin).
    destruct (list_elem_of_lookup_1 _ _ Hin) as (i & Hi).
    iDestruct (big_sepL_lookup _ _ i with "Hcertsin") as "Hc"; [exact Hi |].
    iApply (ghost_map_lookup with "HopsAuth Hc"). }
  iPureIntro. move=> ti op Hti Hop.
  have Hin : op ∈ expand_inputs pending.
  { rewrite /expand_inputs. apply list_elem_of_join.
    exists (expand_input ti). split; [exact Hop | by apply list_elem_of_fmap_2]. }
  destruct Hopscoh as [Hc1 _].
  have [_ Hreg] := Hc1 _ _ (Hlk op Hin).
  exists (clientId (DocOp_id ((op.1, OpInsert op.2) : Op))). exact Hreg.
Qed.

(** [wire_ready_total] from the ghost history (issue #40 x n-char): opens the
    invariant read-only, gets the per-char [op_broadcast] and hands them to the
    pure [wire_ready_total_of_certs]. Mirrors the per-char
    [pending_ready_total_of_certs] gate in [yjs_network_model]. *)
Lemma history_wire_ready_total γh (c : ClientId) h (m : DocM)
    (pending applied : list (TId * IntegrateInput (A := A))) E :
  ↑histN ⊆ E ->
  history_state_coh h m ->
  (∀ t : TId, YjsArrInvariant (docm_get m t)) ->
  (∀ ti : TId * IntegrateInput (A := A), ti ∈ pending ->
     (1 <= length (in_content ti.2))%nat) ->
  (∀ ti : TId * IntegrateInput (A := A), ti ∈ applied -> ti ∈ pending) ->
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
Lemma history_deliver_wire γh (c : ClientId) h (m : DocM)
    (pending applied rest : list (TId * IntegrateInput (A := A))) (m' : DocM) E :
  ↑histN ⊆ E ->
  wire_drain m pending = (applied, rest, m') ->
  history_state_coh h m ->
  (∀ t : TId, YjsArrInvariant (docm_get m t)) ->
  (∀ ti : TId * IntegrateInput (A := A), ti ∈ pending ->
     (1 <= length (in_content ti.2))%nat) ->
  is_history (A := A) (P := P) γh -∗ own_client_history γh c h -∗
  is_pending_certified γh (expand_inputs pending) ={E}=∗
    own_client_history γh c (h ++ (deliver_ev <$> expand_inputs applied)) ∗
    is_history_lb γh c (h ++ (deliver_ev <$> expand_inputs applied)) ∗
    ⌜ValidReplay (expand_inputs applied) m m'⌝ ∗
    ⌜history_state_coh (h ++ (deliver_ev <$> expand_inputs applied)) m'⌝ ∗
    ⌜∀ ti : TId * IntegrateInput (A := A), ti ∈ expand_inputs applied ->
       clientId (in_id ti.2) ≠ c⌝.
Proof.
  iIntros (HE Hdrain Hcoh Hinvs Hnonempty) "#Hinv Hown #Hcertsin".
  iInv "Hinv" as ">H" "Hclose". iNamed "H".
  iDestruct (hist_auth_elem_lookup with "HhistAuth Hown") as %HNc.
  iDestruct (wire_pending_op_broadcast γh N ops pending Hopscoh with "Hcertsin HopsAuth") as %Hcharcert.
  have Happsub := proj1 (wire_drain_subset m pending applied rest m' Hdrain).
  have HWR := wire_drain_replay m pending applied rest m' Hdrain.
  have Hcharcertapp : ∀ (ti op : TId * IntegrateInput (A := A)), ti ∈ applied ->
      op ∈ expand_input ti -> op_broadcast N (op.1, OpInsert op.2)
    := λ ti op Hti Hop, Hcharcert ti op (Happsub ti Hti) Hop.
  have Hnonemptyapp : ∀ ti : TId * IntegrateInput (A := A), ti ∈ applied ->
      (1 <= length (in_content ti.2))%nat := λ ti Hti, Hnonempty ti (Happsub ti Hti).
  have Hpr := WireReplay_to_PendingReplay m applied m' HWR N c h Hwf HNc Hcoh Hinvs
                Hcharcertapp Hnonemptyapp.
  have Hbcapp : ∀ op : TId * IntegrateInput (A := A), op ∈ expand_inputs applied ->
      op_broadcast N (op.1, OpInsert op.2).
  { move=> op Hin.
    rewrite /expand_inputs list_elem_of_join in Hin. destruct Hin as (l & Hl & Hll).
    rewrite list_elem_of_fmap in Hll. destruct Hll as (ti & -> & Hti).
    exact (Hcharcert ti op (Happsub ti Hti) Hl). }
  pose proof (pending_ValidReplay N c h m (expand_inputs applied) m' Hwf HNc Hcoh Hbcapp Hpr)
    as (Hvr & Hcoh' & Hwf' & Hnoc).
  iMod (hist_auth_elem_advance γh N c h (deliver_ev <$> expand_inputs applied)
          HNc with "HhistAuth Hown") as "(HhistAuth & Hown & #Hlb)".
  iMod ("Hclose" with "[HhistAuth HopsAuth]") as "_".
  { iNext. iExists _, _. iFrame "HhistAuth HopsAuth Hcerts".
    iPureIntro. split; [exact Hwf' |].
    apply (ops_coh_deliver_tail N c h ops _ Hwf HNc); [| exact Hopscoh].
    move=> e He. move: He. rewrite list_elem_of_fmap.
    move=> [ti [Heq _]]. rewrite /deliver_ev in Heq. discriminate. }
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
    ⌜∀ ti : TId * IntegrateInput (A := A), ti ∈ inputs ->
       (1 <= length (in_content ti.2))%nat⌝.
Proof.
  iIntros "H". iDestruct "H" as (uivs) "(Hsl & Hcap & #Hitems)".
  iAssert (⌜∀ ti : TId * IntegrateInput (A := A), ti ∈ inputs ->
             (1 <= length (in_content ti.2))%nat⌝)%I as %Hnem.
  { iIntros (ti Hin). destruct (list_elem_of_lookup_1 _ _ Hin) as (i & Hi).
    iDestruct (big_sepL2_lookup_r _ _ _ i with "Hitems") as (uiv Huiv) "Hit"; [exact Hi |].
    iNamed "Hit". iPureIntro. rewrite -Hin_c. exact Hunonempty. }
  iSplitR ""; [iExists uivs; iFrame "Hsl Hcap Hitems" | done].
Qed.

(** Every applied wire item's target root is nonempty at [m'] (its first char
    landed there): the head of its [expand_input] is in [expand_inputs applied]
    and carries the item's [TId], so [ValidReplay_applied_nonempty] on the
    expansion pins [docm_get m' ti.1 ≠ []]. *)
Lemma applied_root_nonempty
    (applied : list (TId * IntegrateInput (A := A))) (m m' : DocM)
    (ti : TId * IntegrateInput (A := A)) :
  ValidReplay (expand_inputs applied) m m' ->
  ti ∈ applied ->
  (1 <= length (in_content ti.2))%nat ->
  docm_get m' ti.1 ≠ [].
Proof.
  move=> Hvr Hin Hne.
  have [fop Hfop] : is_Some (ops_of_input ti.2 (explode (in_content ti.2)) !! 0%nat).
  { apply lookup_lt_is_Some_2. rewrite /ops_of_input ops_from_length /explode length_fmap. lia. }
  have Hmem : (ti.1, fop) ∈ expand_inputs applied.
  { rewrite /expand_inputs. apply list_elem_of_join.
    exists (expand_input ti). split; [| by apply list_elem_of_fmap_2].
    apply (list_elem_of_lookup_2 _ 0%nat). by apply expand_input_lookup. }
  exact (ValidReplay_applied_nonempty (expand_inputs applied) m m' Hvr (ti.1, fop) Hmem).
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
    post-delivery item set. *)
Lemma wp_store__applyUpdate_certs (s_loc : loc) (sl : slice.t) (dq : dfrac)
    (γs : store_names) (γh : history_names)
    (c : ClientId) (h : list Ev) (m : DocM)
    (pend inputs : list (TId * IntegrateInput (A := A))) :
  (∀ ti : TId * IntegrateInput (A := A), ti ∈ inputs ->
     (Z.of_nat (clock (in_id ti.2)) + Z.of_nat (length (in_content ti.2)) < 2^64)%Z) ->
  {{{ is_pkg_init yjs ∗ is_history (A := A) (P := P) γh ∗
      own_store s_loc γs γh c h m pend ∗
      own_update_structs sl dq inputs ∗
      is_pending_certified γh (expand_inputs inputs) ∗
      is_pending_rooted γs inputs }}}
    s_loc @! (go.PointerType yjs.store) @! "applyUpdate" #sl
  {{{ (applied rest : list (TId * IntegrateInput (A := A))) (m' : DocM),
      RET #();
      own_update_structs sl dq inputs ∗
      own_store s_loc γs γh c (h ++ (deliver_ev <$> expand_inputs applied)) m' rest ∗
      is_history_lb γh c (h ++ (deliver_ev <$> expand_inputs applied)) ∗
      ⌜wire_drain m (pend ++ inputs) = (applied, rest, m')⌝ ∗
      ⌜ValidReplay (expand_inputs applied) m m'⌝ ∗
      ⌜∀ ti : TId * IntegrateInput (A := A), ti ∈ expand_inputs applied ->
         clientId (in_id ti.2) ≠ c⌝ ∗
      ([∗ list] ti ∈ applied, ∃ nm : P, ⌜ti.1 = RootId nm⌝ ∗
         is_root_lb γs nm (list_to_set (docm_get m' ti.1))) }}}.
Proof using Type*.
  move=> Hnowrapb.
  iIntros (Φ) "(#Hpkg & #Hishist & Hstore & Hupd & #Hcertsin & #Hrootsin) HΦ".
  iNamed "Hstore".
  destruct Hregcoh as (Hbindtypes & Hbindinj & Htypesbound & Hmtypes & Hmdom).
  iDestruct (types_arr_inv2 with "Htypes") as %Htsinv.
  have Harrinv : ∀ t : TId, YjsArrInvariant (docm_get m t).
  { move=> t. destruct (docm_get m t) as [|x l] eqn:Hdg.
    - exact YjsArrInvariant_empty.
    - rewrite -Hdg.
      have Hne : docm_get m t ≠ [] by rewrite Hdg.
      destruct (Hmdom t Hne) as (nm & p & -> & Hbnm).
      destruct (Hbindtypes nm p Hbnm) as [ts Hts].
      rewrite (Hmtypes nm p ts Hbnm Hts). exact (Htsinv p ts Hts). }
  (* per-item content nonemptiness of the whole drained pending, from the heap *)
  iDestruct (own_update_structs_nonempty with "Hupd") as "[Hupd %Hnem_in]".
  iDestruct (own_update_structs_nonempty with "Hpend") as "[Hpend %Hnem_pd]".
  have Hnonemptyb : ∀ ti : TId * IntegrateInput (A := A), ti ∈ pend ++ inputs ->
      (1 <= length (in_content ti.2))%nat.
  { move=> ti /elem_of_app [Hin | Hin]; [exact (Hnem_pd ti Hin) | exact (Hnem_in ti Hin)]. }
  have Hkb1c : ∀ ti : TId * IntegrateInput (A := A), ti ∈ pend ++ inputs ->
      (Z.of_nat (clock (in_id ti.2)) + Z.of_nat (length (in_content ti.2)) < 2^64)%Z.
  { move=> ti /elem_of_app [Hin | Hin];
      [exact (Hpendbnd ti Hin) | exact (Hnowrapb ti Hin)]. }
  (* the whole drained pending and its per-char certificates *)
  iAssert (is_pending_certified γh (expand_inputs (pend ++ inputs))) as "#Hcertpending".
  { rewrite /is_pending_certified expand_inputs_app big_sepL_app.
    iSplit; [iFrame "Hpendcert" | iFrame "Hcertsin"]. }
  iAssert (is_pending_rooted γs (pend ++ inputs)) as "#Hrootpending".
  { rewrite /is_pending_rooted big_sepL_app.
    iSplit; [iFrame "Hpendroot" | iFrame "Hrootsin"]. }
  iAssert (⌜∀ ti : TId * IntegrateInput (A := A), ti ∈ pend ++ inputs ->
      in_originId ti.2 = None -> in_rightOriginId ti.2 = None ->
      ∃ nm, ti.1 = RootId nm ∧ is_Some (bind !! nm)⌝)%I as %Hrooted0.
  { iIntros (ti Hin HoN HrN).
    iDestruct (big_sepL_elem_of _ _ ti Hin with "Hrootpending") as "Hri".
    rewrite /pending_item_rooted decide_True; last by split.
    iDestruct "Hri" as (nm) "[%Htieq Hroot]".
    iDestruct "Hroot" as (p) "Hbind".
    iDestruct (ghost_map_lookup with "HtypesAuth Hbind") as %Hb.
    iPureIntro. exists nm. split; [exact Htieq | by exists p]. }
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
  wp_apply (wp_store__applyUpdate s_loc items_mref types_mref sl pend_sl dq
              inputs pend applied rest' m m' types bind
              Hdrainc Hvr Hrtot Happsub Hnonemptyb Hbindtypes Hbindinj Htypesbound Hmtypes Hmdom
              Hrooted0 Hrunfits Hkb1c Hlocdup Hrangedisj Horiginclk
              with "[$Hupd $Hpendf $Hpend $Hitemsf $Hitemmap $Htypesf $Htypesmap $Htypes]").
  iIntros (pend_sl' types') "(Hupd & Hpendf & Hpend' & Hitemsf & Hitemmap & Htypesf & Htypesmap & Htypes & %Hdom' & %Hmtypes' & %Hmdom' & %Hprov' & %Hlocdup' & %Hrangedisj' & %Hfits' & %Horiginclk')".
  have Hbindtypes' : ∀ nm p, bind !! nm = Some p -> is_Some (types' !! p).
  { move=> nm p Hb. apply elem_of_dom. rewrite Hdom'. apply elem_of_dom.
    exact (Hbindtypes nm p Hb). }
  have Htypesbound' : ∀ p, is_Some (types' !! p) -> ∃ nm, bind !! nm = Some p.
  { move=> p Hs. apply Htypesbound. apply elem_of_dom. rewrite -Hdom'.
    apply elem_of_dom. exact Hs. }
  (* grow the item-set authority to the new types and snapshot it *)
  have Hdomf : dom ((λ ts : type_state, (list_to_set (ty_arr ts) : gset (YjsItem A))) <$> types')
             = dom ((λ ts : type_state, (list_to_set (ty_arr ts) : gset (YjsItem A))) <$> types)
    by rewrite !dom_fmap_L Hdom'.
  have Hgrowf : ∀ p S S',
      ((λ ts : type_state, (list_to_set (ty_arr ts) : gset (YjsItem A))) <$> types) !! p = Some S ->
      ((λ ts : type_state, (list_to_set (ty_arr ts) : gset (YjsItem A))) <$> types') !! p = Some S' ->
      S ⊆ S'.
  { move=> p S S'. rewrite !lookup_fmap.
    destruct (types !! p) as [ts|] eqn:Hts; last done.
    destruct (types' !! p) as [ts'|] eqn:Hts'; last done.
    move=> [= <-] [= <-].
    destruct (Htypesbound p (ex_intro _ ts Hts)) as [nm Hbnm].
    have Hdg : docm_get m (RootId nm) = ty_arr ts := Hmtypes nm p ts Hbnm Hts.
    have Hdg' : docm_get m' (RootId nm) = ty_arr ts' := Hmtypes' nm p ts' Hbnm Hts'.
    move=> x. rewrite !elem_of_list_to_set. move=> Hx.
    rewrite -Hdg'. apply (ValidReplay_mem (expand_inputs applied) m m' Hvr (RootId nm)).
    by rewrite Hdg. }
  iMod (auth_gmap_gset_grow_snap γs.(sn_seq) _ _ Hdomf Hgrowf with "Hseq")
    as "[Hseq #Hsnap]".
  (* per-applied bindings: the applied wire item's first char landed in its root *)
  have Happbnd : ∀ ti : TId * IntegrateInput (A := A), ti ∈ applied ->
      ∃ nm p, ti.1 = RootId nm ∧ bind !! nm = Some p.
  { move=> ti Hin.
    have Hne := applied_root_nonempty applied m m' ti Hvr Hin
                 (Hnonemptyb ti (Happsub ti Hin)).
    destruct (Hmdom' ti.1 Hne) as (nm & p & Heq & Hb). by exists nm, p. }
  iAssert ([∗ list] ti ∈ applied, ∃ nm : P, ⌜ti.1 = RootId nm⌝ ∗
             is_root_lb γs nm (list_to_set (docm_get m' ti.1)))%I as "#Hlbs".
  { iApply big_sepL_intro.
    iIntros "!#" (i ti Hi).
    destruct (Happbnd ti (list_elem_of_lookup_2 _ _ _ Hi)) as (nm & p & Htieq & Hbnm).
    destruct (Hbindtypes' nm p Hbnm) as [ts' Hts'].
    have Hdg' : docm_get m' (RootId nm) = ty_arr ts' := Hmtypes' nm p ts' Hbnm Hts'.
    iDestruct (big_sepM_lookup _ _ nm p Hbnm with "Hbinds") as "#Hbind".
    iExists nm. iSplit; [done |].
    iExists p. iFrame "Hbind".
    rewrite /is_type_lb Htieq Hdg'.
    iApply (auth_gmap_gset_frag_lookup with "Hsnap").
    rewrite lookup_fmap Hts' //. }
  (* the leftover pending re-certifies the new pending buffer (per-char) *)
  iAssert (is_pending_certified γh (expand_inputs rest')) as "#Hpendcert'".
  { rewrite /is_pending_certified. iApply big_sepL_intro.
    iIntros "!#" (i ti Hi).
    iApply (big_sepL_elem_of _ _ ti
              (expand_inputs_subset rest' (pend ++ inputs) Hrestsub ti
                 (list_elem_of_lookup_2 _ _ _ Hi))
              with "Hcertpending"). }
  iAssert (is_pending_rooted γs rest') as "#Hpendroot'".
  { rewrite /is_pending_rooted. iApply big_sepL_intro.
    iIntros "!#" (i ti Hi).
    iApply (big_sepL_elem_of _ _ ti (Hrestsub ti (list_elem_of_lookup_2 _ _ _ Hi))
              with "Hrootpending"). }
  have Hpendbnd' : ∀ ti : TId * IntegrateInput (A := A), ti ∈ rest' ->
      (Z.of_nat (clock (in_id ti.2)) + Z.of_nat (length (in_content ti.2)) < 2^64)%Z.
  { move=> ti Hin. exact (Hkb1c ti (Hrestsub ti Hin)). }
  (* the counter clause survives: nothing applied is ours *)
  have Hctr' : ∀ (t : TId) x, x ∈ docm_get m' t -> clientId (item_id x) = c ->
      (clock (item_id x) < uint.nat k)%nat.
  { move=> t x Hx Hcx.
    destruct (ValidReplay_prov (expand_inputs applied) m m' Hvr t x Hx)
      as [Hold | (i & ti & Hi & Hid)].
    - exact (Hctr t x Hold Hcx).
    - exfalso. apply (Hnoc ti (list_elem_of_lookup_2 _ _ _ Hi)). by rewrite -Hid. }
  iModIntro. iApply ("HΦ" $! applied rest' m').
  iFrame "Hupd". iFrame "Hlbnew". iFrame "Hlbs".
  iSplitL "Hclient Hclock Hitemsf Hitemmap Htypesf Htypesmap Hdset Hpendf Hpend' Hseq Htypes HtypesAuth Hhist";
    last by (iPureIntro; split_and!; [done | exact Hvr | exact Hnoc]).
  iExists client, k, items_mref, types_mref, dset, pend_sl', types', bind.
  iFrame "Hclient Hclock Hitemsf Hitemmap Htypesf Htypesmap Hdset Hpendf Hpend' Hseq Htypes HtypesAuth Hbinds Hhist".
  iFrame "Hpendcert' Hpendroot'".
  iPureIntro. split_and!.
  - exact Hclientc.
  - exact Hpendbnd'.
  - rewrite /doc_registry_coh.
    split_and!; [exact Hbindtypes' | exact Hbindinj | exact Htypesbound'
                 | exact Hmtypes' | exact Hmdom'].
  - exact Hcoh'.
  - exact Hctr'.
  - exact Hlocdup'.
  - exact Hrangedisj'.
  - exact Hfits'.
  - exact Horiginclk'.
Qed.

End store_update.
