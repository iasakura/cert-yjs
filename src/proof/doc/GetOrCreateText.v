(** [wp_Doc__GetOrCreateText]: the public root-type accessor (y-octo:
    Doc::get_or_create_text; Yjs doc.getText has the same get-or-create
    semantics under the shorter name). Takes the store's WRITE lock (first use
    registers the type), runs the verified [getOrCreateYType] (issue #54
    proved the miss branch), and hands back the persistent [Text] handle for
    [name] with the empty content lower bound; a caller grows the bound by
    reading ([Len]/[String] intersect it with any [is_root_lb] certificate)
    or writing. Registering a fresh root is model-clean: an empty type adds
    no cells and no items, and the doc model [m] already maps every unbound
    root to [[]], so only the registry ([bind], its ghost map and the item-set
    authority's domain) grows. *)
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
From New.proof.text Require Import text.
From New.proof.sync_proof Require Import mutex.
From iris.algebra Require Import auth gmap gset.
From iris.algebra.lib Require Import dfrac_agree.
From stdpp Require Import sorting.
From New.proof.doc Require Import model heap.

Local Open Scope Z_scope.

Section doc_GetText.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Context {sync_pkg : sync.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.

Notation P := go_string.

Local Notation TId := (TypeId P).

Local Notation Op := (TId * @YjsOperation A)%type.

Local Notation Ev := (@Event Op).

Local Notation DocModel := (gmap TId (list (YjsItem A))).

Context {seq_inG : inG Σ (authR (gmapUR loc (gsetUR (YjsItem A))))}.

Context {acc_inG : inG Σ (authR (gsetUR YjsId))}.

Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO (gmap loc (list loc) * pool)))}.

Lemma wp_Doc__GetOrCreateText (dv s_loc : loc) (γs : store_names) (γh : history_names)
    (name : P) :
  {{{ is_pkg_init yjs ∗ is_Doc dv s_loc γs γh ∗ is_history (A := A) (P := P) γh }}}
    dv @! (go.PointerType yjs.Doc) @! "GetOrCreateText" #name
  {{{ (t : loc), RET #t; is_Text t γs γh name [] }}}.
Proof.
  wp_start as "(#His_doc & #Hishist)".
  iNamed "His_doc". subst s_loc. wp_auto.
  wp_apply (wp_Store__wlock with "[$His_store]"). iIntros "[Hwl Hinv]".
  iDestruct "Hinv" as (c0 h m pend) "Hown". iEval (rewrite own_store_as_cells) in "Hown". iNamed "Hown". subst c0.
  iNamed "Hcells". iNamed "Hfields". iNamed "Hregistry". iNamed "Hpending". iNamed "Hpdeletes".
  have [Hpool Hreg] := Hinvs.
  have [Hrunfits [Hlocdup [Hrangedisj Horiginclk]]] := Hpool.
  have [Hbindtypes [Hbindinj Htypesbound]] := Hreg.
  have [Hmtypes Hmdom] := Hregmodel.
  iDestruct (own_type_pool_client_clock_bound types client k Hctr with "Htypes") as %Hcellctr.
  wp_auto.
  destruct (bind !! name) as [p|] eqn:Hbnd.
  - (* ---- hit: the root is registered; nothing changes ---- *)
    iDestruct (own_store_struct_intro_raw _ (MkStoreState client k types bind pend pdel)
                 types_mref pend_sl pdel_sl Hinvs
                 with "Hclient Hclock HdeletedSet Hitems Htypesf Htypesmap Htypes Hpendf Hpend Hpddelf Hpddel") as "Hcells".
    wp_apply (wp_store__getOrCreateYType _ (MkStoreState client k types bind pend pdel) name with "[$Hcells]").
    iIntros (p' types' bind') "(Hcells & %Hlc)". simpl in Hlc.
    destruct Hlc as [(Hb' & -> & ->) | (Hb' & _)]; last by rewrite Hb' in Hbnd.
    rewrite Hbnd in Hb'. injection Hb' as <-.
    iEval (simpl) in "Hcells".
    iDestruct (big_sepM_lookup _ _ name p Hbnd with "Hbinds") as "#Hbindname".
    destruct (Hbindtypes name p Hbnd) as [ts Hts].
    have Hmk : ((λ ts, (list_to_set (ty_arr ts) : gset (YjsItem A))) <$> types) !! p
             = Some (list_to_set (ty_arr ts)) by rewrite lookup_fmap Hts //.
    iMod (auth_gmap_gset_frag_alloc γs.(sn_seq) (DfracOwn 1) _ p ∅ _
            Hmk (empty_subseteq _) with "Hseq") as "[Hseq #Hlb0]".
    wp_auto.
    wp_apply (wp_Store__wunlock _ _ _ (uint.nat client) h m pend
                with "[$His_store $Hwl Hcells Hseq HtypesAuth Hhist Hacc Hdelete_set]").
    { rewrite own_store_as_cells. iExists client, k, pdel, types, bind, acc.
      iFrame "∗#". iPureIntro.
      split_and!;
        [reflexivity | exact Hpendroot | exact Hpendbnd | exact Hregmodel | exact Hhcoh
        | exact Hctr | exact Hacccoh]. }
    wp_alloc t as "Ht".
    iPersist "Ht".
    wp_auto.
    iApply ("HΦ" $! t).
    iExists _, (dvv.(yjs.Doc.store')), p. iFrame "Ht His_store Hishist Hbindname".
    iSplitR; first done.
    iSplitR; first done.
    iSplitL; last (iPureIntro; constructor).
    iExact "Hlb0".
  - (* ---- miss: register a fresh empty root type ---- *)
    iDestruct (own_store_struct_intro_raw _ (MkStoreState client k types bind pend pdel)
                 types_mref pend_sl pdel_sl Hinvs
                 with "Hclient Hclock HdeletedSet Hitems Htypesf Htypesmap Htypes Hpendf Hpend Hpddelf Hpddel") as "Hcells".
    wp_apply (wp_store__getOrCreateYType _ (MkStoreState client k types bind pend pdel) name with "[$Hcells]").
    iIntros (p types'' bind'') "(Hcells & %Hlc)". simpl in Hlc.
    destruct Hlc as [(Hb' & _) | (_ & Hfresh & -> & ->)]; first by rewrite Hb' in Hbnd.
    iEval (simpl) in "Hcells".
    iDestruct "Hcells" as "(Hfields' & %Hinvs')".
    iDestruct "Hfields'" as "(Hclient & Hclock & HdeletedSet & Hitems & Hregistry & Htypes & Hpending & Hpdeletes)".
    set (types' := <[p := MkTypeState [] []]> types).
    set (bind' := <[name := p]> bind).
    (* registry ghost map: mint the persistent binding *)
    iMod (ghost_map_insert_persist name p Hbnd with "HtypesAuth")
      as "[HtypesAuth #Hbindname]".
    iAssert ([∗ map] nm ↦ q ∈ bind', is_type_binding γs.(sn_types) nm q)%I as "#Hbinds'".
    { rewrite /bind' big_sepM_insert; last exact Hbnd.
      iFrame "Hbinds". iFrame "Hbindname". }
    (* item-set authority: the domain grows by the fresh empty root *)
    have Hfmap' : ((λ ts, (list_to_set (ty_arr ts) : gset (YjsItem A))) <$> types')
                = <[p := (∅ : gset (YjsItem A))]>
                    ((λ ts, (list_to_set (ty_arr ts) : gset (YjsItem A))) <$> types).
    { rewrite /types' fmap_insert //. }
    have Hdomf : dom ((λ ts, (list_to_set (ty_arr ts) : gset (YjsItem A))) <$> types)
               ⊆ dom ((λ ts, (list_to_set (ty_arr ts) : gset (YjsItem A))) <$> types').
    { rewrite Hfmap' dom_insert. apply union_subseteq_r. }
    have Hgrowf : ∀ q S S',
        ((λ ts, (list_to_set (ty_arr ts) : gset (YjsItem A))) <$> types) !! q = Some S ->
        ((λ ts, (list_to_set (ty_arr ts) : gset (YjsItem A))) <$> types') !! q = Some S' ->
        S ⊆ S'.
    { move=> q S S'. rewrite Hfmap'.
      destruct (decide (q = p)) as [-> | Hne].
      - rewrite lookup_fmap Hfresh //.
      - rewrite lookup_insert_ne //. move=> -> [= ->]. done. }
    iMod (auth_gmap_gset_grow_snap γs.(sn_seq) _ _ Hdomf Hgrowf with "Hseq")
      as "[Hseq #Hsnap]".
    have Hlk0 : ((λ ts, (list_to_set (ty_arr ts) : gset (YjsItem A))) <$> types') !! p
              = Some (∅ : gset (YjsItem A)) by rewrite Hfmap' lookup_insert_eq.
    iDestruct (auth_gmap_gset_frag_lookup γs.(sn_seq) _ p ∅ Hlk0 with "Hsnap") as "#Hlb0".
    (* the per-client item map only sees cells, and an empty type adds none *)
    have Hperm : all_cells types' ≡ₚ all_cells types
      := all_cells_insert_empty types p [] Hfresh.
    have Hkp : cell_kp <$> all_cells types' ≡ₚ cell_kp <$> all_cells types
      by rewrite Hperm.
    (* the registry / model coherence survives the fresh binding *)
    have Hbindtypes' : ∀ nm q, bind' !! nm = Some q → is_Some (types' !! q).
    { move=> nm q. rewrite /bind' /types'.
      destruct (decide (nm = name)) as [-> | Hne].
      - rewrite lookup_insert_eq. move=> [= <-]. rewrite lookup_insert_eq //.
      - rewrite lookup_insert_ne //. move=> Hq.
        destruct (Hbindtypes nm q Hq) as [ts Hts].
        destruct (decide (q = p)) as [-> | Hqp].
        + rewrite lookup_insert_eq //.
        + rewrite lookup_insert_ne // Hts //. }
    have Hbindinj' : ∀ n1 n2 q, bind' !! n1 = Some q → bind' !! n2 = Some q → n1 = n2.
    { move=> n1 n2 q. rewrite /bind'.
      destruct (decide (n1 = name)) as [-> | Hne1];
        destruct (decide (n2 = name)) as [-> | Hne2].
      - done.
      - rewrite lookup_insert_eq lookup_insert_ne //.
        move=> [= <-] Hq2.
        destruct (Hbindtypes n2 p Hq2) as [ts Hts]. rewrite Hfresh in Hts. done.
      - rewrite lookup_insert_eq lookup_insert_ne //.
        move=> Hq1 [= Heq]. subst q.
        destruct (Hbindtypes n1 p Hq1) as [ts Hts]. rewrite Hfresh in Hts. done.
      - rewrite !lookup_insert_ne //. exact (Hbindinj n1 n2 q). }
    have Htypesbound' : ∀ q, is_Some (types' !! q) → ∃ nm, bind' !! nm = Some q.
    { move=> q. rewrite /types' /bind'.
      destruct (decide (q = p)) as [-> | Hqp].
      - move=> _. exists name. rewrite lookup_insert_eq //.
      - rewrite lookup_insert_ne //. move=> Hq.
        destruct (Htypesbound q Hq) as [nm Hnm].
        exists nm. rewrite lookup_insert_ne //.
        move=> Heq. subst nm. rewrite Hbnd in Hnm. done. }
    have Hnameempty : doc_model_get m (RootId name) = [].
    { destruct (doc_model_get m (RootId name)) as [| x l] eqn:Hdg; first done.
      have Hne : doc_model_get m (RootId name) ≠ [] by rewrite Hdg.
      destruct (Hmdom (RootId name) Hne) as (nm & q & Heq & Hq).
      injection Heq as <-. rewrite Hbnd in Hq. done. }
    have Hmtypes' : ∀ nm q ts, bind' !! nm = Some q → types' !! q = Some ts →
        doc_model_get m (RootId nm) = ty_arr ts.
    { move=> nm q ts. rewrite /bind' /types'.
      destruct (decide (nm = name)) as [-> | Hne].
      - rewrite lookup_insert_eq. move=> [= <-]. rewrite lookup_insert_eq.
        move=> [= <-]. rewrite Hnameempty //.
      - rewrite lookup_insert_ne //. move=> Hq.
        destruct (decide (q = p)) as [-> | Hqp].
        + destruct (Hbindtypes nm p Hq) as [ts0 Hts0]. rewrite Hfresh in Hts0. done.
        + rewrite lookup_insert_ne //. exact (Hmtypes nm q ts Hq). }
    have Hmdom' : ∀ t, doc_model_get m t ≠ [] →
        ∃ nm q, t = RootId nm ∧ bind' !! nm = Some q.
    { move=> t Hne.
      destruct (Hmdom t Hne) as (nm & q & Heq & Hq).
      exists nm, q. split; first exact Heq.
      rewrite /bind' lookup_insert_ne //.
      move=> Heq2. subst nm. rewrite Hbnd in Hq. done. }
    have Hctr' : ∀ parent ts x, types' !! parent = Some ts → x ∈ ty_arr ts →
        clientId (item_id x) = uint.nat client → (clock (item_id x) < uint.nat k)%nat.
    { move=> parent ts x. rewrite /types'.
      destruct (decide (parent = p)) as [-> | Hne].
      - rewrite lookup_insert_eq. move=> [= <-] Hx. by apply elem_of_nil in Hx.
      - rewrite lookup_insert_ne //. exact (Hctr parent ts x). }
    have Hcellctr' : ∀ c, c ∈ all_cells types' → cell_client c = client →
        (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) <= uint.Z k)%Z.
    { move=> c Hc. rewrite Hperm in Hc. exact (Hcellctr c Hc). }
    have Hlocdup' : NoDup (ic_loc <$> all_cells types').
    { rewrite Hperm //. }
    have Hrangedisj' : cells_range_disjoint (all_cells types').
    { move=> c1 c2 Hc1 Hc2. rewrite Hperm in Hc1 Hc2.
      exact (Hrangedisj c1 c2 Hc1 Hc2). }
    have Hrunfits' : ∀ c, c ∈ all_cells types' → cell_fits c.
    { move=> c Hc. rewrite Hperm in Hc. exact (Hrunfits c Hc). }
    have Horiginclk' : ∀ c, c ∈ all_cells types' → cell_origin_clk c.
    { move=> c Hc. rewrite Hperm in Hc. exact (Horiginclk c Hc). }
    (* registering an empty type moves no cells, so the tombstone-set
       invariant transports over the same permutation *)
    iDestruct (own_delete_set_perm γs m (all_cells types) (all_cells types') Hperm with "Hdelete_set")
      as "Hdelete_set".
    wp_auto.
    have Hregmodel' : registry_models m bind' types'.
    { rewrite /registry_models. split; [exact Hmtypes' | exact Hmdom']. }
    iDestruct (own_store_struct_intro _ (MkStoreState client k types' bind' pend pdel) Hinvs'
                with "Hclient Hclock HdeletedSet Hitems Hregistry Htypes Hpending Hpdeletes") as "Hcells".
    wp_apply (wp_Store__wunlock _ _ _ (uint.nat client) h m pend
                with "[$His_store $Hwl Hcells Hseq HtypesAuth Hhist Hacc Hdelete_set]").
    { rewrite own_store_as_cells. iExists client, k, pdel, types', bind', acc.
      iFrame "∗". iFrame "Hclientpin Hpendcert Hbinds'". iPureIntro.
      split_and!;
        [reflexivity | exact Hpendroot | exact Hpendbnd | exact Hregmodel' | exact Hhcoh
        | exact Hctr' | exact Hacccoh]. }
    wp_alloc t as "Ht".
    iPersist "Ht".
    wp_auto.
    iApply ("HΦ" $! t).
    iExists _, (dvv.(yjs.Doc.store')), p. iFrame "Ht His_store Hishist Hbindname".
    iSplitR; first done.
    iSplitR; first done.
    iSplitL; last (iPureIntro; constructor).
    iExact "Hlb0".
Qed.

End doc_GetText.
