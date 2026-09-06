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

Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO addressed_pool))}.

Lemma wp_Doc__GetOrCreateText (dv s_loc : loc) (γs : store_names) (γh : history_names)
    (name : P) :
  {{{ is_pkg_init yjs ∗ is_Doc dv s_loc γs γh ∗ is_history (A := A) (P := P) γh }}}
    dv @! (go.PointerType yjs.Doc) @! "GetOrCreateText" #name
  {{{ (t : loc), RET #t; is_Text t γs γh name [] }}}.
Proof.
  wp_start as "(#His_doc & #Hishist)".
  iNamed "His_doc". subst s_loc. wp_auto.
  wp_apply (wp_Store__wlock with "[$His_store]"). iIntros "[Hwl Hinv]".
  iDestruct "Hinv" as (c0 h m pend) "Hown". iNamed "Hown". subst c0.
  iDestruct (own_store_state_run_pool_invs with "Hstate") as %Hrpi.
  iDestruct (own_store_state_registry_coh with "Hstate") as %Hreg.
  have [Hbindtypes [Hbindinj Htypesbound]] := Hreg.
  have [Hmtypes Hmdom] := Hregmodel.
  wp_auto.
  wp_apply (wp_store__getOrCreateYType _ (MkStoreState client k locs p bind pend pdel) name
              with "[$Hstate]").
  iIntros (q p' locs' bind') "(Hstate & %Hlc)". iEval (simpl) in "Hstate". simpl in Hlc.
  destruct Hlc as [(Hb' & -> & -> & ->) | (Hb' & Hfresh & -> & -> & ->)].
  - (* ---- hit: the root is registered; nothing changes ---- *)
    iDestruct (big_sepM_lookup _ _ name q Hb' with "Hbinds") as "#Hbindname".
    destruct (Hbindtypes name q Hb') as [tm Htm].
    have Hmk : ((λ tm0, (list_to_set (tm_arr tm0) : gset (YjsItem A))) <$> p) !! q
             = Some (list_to_set (tm_arr tm)) by rewrite lookup_fmap Htm //.
    iMod (auth_gmap_gset_frag_alloc γs.(sn_seq) (DfracOwn 1) _ q ∅ _
            Hmk (empty_subseteq _) with "Hseq") as "[Hseq #Hlb0]".
    wp_auto.
    wp_apply (wp_Store__wunlock _ _ _ (uint.nat client) h m pend
                with "[$His_store $Hwl Hstate Hseq HtypesAuth Hhist Hacc Hdelete_set]").
    { iExists client, k, pdel, locs, p, bind, acc.
      iFrame "∗#". iPureIntro.
      split_and!;
        [reflexivity | exact Hpendroot | exact Hpendbnd | exact Hregmodel | exact Hhcoh
        | exact Hctr | exact Hacccoh]. }
    wp_alloc t as "Ht".
    iPersist "Ht".
    wp_auto.
    iApply ("HΦ" $! t).
    iExists _, (dvv.(yjs.Doc.store')), q. iFrame "Ht His_store Hishist Hbindname".
    iSplitR; first done.
    iSplitR; first done.
    iSplitL; last (iPureIntro; constructor).
    iExact "Hlb0".
  - (* ---- miss: register a fresh empty root type ---- *)
    set (p' := <[q := MkTypeModel []]> p).
    set (bind' := <[name := q]> bind).
    (* registry ghost map: mint the persistent binding *)
    iMod (ghost_map_insert_persist name q Hb' with "HtypesAuth")
      as "[HtypesAuth #Hbindname]".
    iAssert ([∗ map] nm ↦ q0 ∈ bind', is_type_binding γs.(sn_types) nm q0)%I as "#Hbinds'".
    { rewrite /bind' big_sepM_insert; last exact Hb'.
      iFrame "Hbinds". iFrame "Hbindname". }
    (* item-set authority: the domain grows by the fresh empty root *)
    have Hfmap' : ((λ tm, (list_to_set (tm_arr tm) : gset (YjsItem A))) <$> p')
                = <[q := (∅ : gset (YjsItem A))]>
                    ((λ tm, (list_to_set (tm_arr tm) : gset (YjsItem A))) <$> p).
    { rewrite /p' fmap_insert //. }
    have Hdomf : dom ((λ tm, (list_to_set (tm_arr tm) : gset (YjsItem A))) <$> p)
               ⊆ dom ((λ tm, (list_to_set (tm_arr tm) : gset (YjsItem A))) <$> p').
    { rewrite Hfmap' dom_insert. apply union_subseteq_r. }
    have Hgrowf : ∀ q0 S S',
        ((λ tm, (list_to_set (tm_arr tm) : gset (YjsItem A))) <$> p) !! q0 = Some S ->
        ((λ tm, (list_to_set (tm_arr tm) : gset (YjsItem A))) <$> p') !! q0 = Some S' ->
        S ⊆ S'.
    { move=> q0 S S'. rewrite Hfmap'.
      destruct (decide (q0 = q)) as [-> | Hne].
      - rewrite lookup_fmap Hfresh //.
      - rewrite lookup_insert_ne //. move=> -> [= ->]. done. }
    iMod (auth_gmap_gset_grow_snap γs.(sn_seq) _ _ Hdomf Hgrowf with "Hseq")
      as "[Hseq #Hsnap]".
    have Hlk0 : ((λ tm, (list_to_set (tm_arr tm) : gset (YjsItem A))) <$> p') !! q
              = Some (∅ : gset (YjsItem A)) by rewrite Hfmap' lookup_insert_eq.
    iDestruct (auth_gmap_gset_frag_lookup γs.(sn_seq) _ q ∅ Hlk0 with "Hsnap") as "#Hlb0".
    (* an empty type holds no run, so everything the pool's runs speak about
       transports over the same permutation *)
    have Hperm : all_runs p' ≡ₚ all_runs p := all_runs_insert_empty p q [] Hfresh.
    (* the registry / model coherence survives the fresh binding *)
    have Hbindtypes' : ∀ nm q0, bind' !! nm = Some q0 → is_Some (p' !! q0).
    { move=> nm q0. rewrite /bind' /p'.
      destruct (decide (nm = name)) as [-> | Hne].
      - rewrite lookup_insert_eq. move=> [= <-]. rewrite lookup_insert_eq //.
      - rewrite lookup_insert_ne //. move=> Hq.
        destruct (Hbindtypes nm q0 Hq) as [tm Htm].
        destruct (decide (q0 = q)) as [-> | Hqp].
        + rewrite lookup_insert_eq //.
        + rewrite lookup_insert_ne // Htm //. }
    have Hbindinj' : ∀ n1 n2 q0, bind' !! n1 = Some q0 → bind' !! n2 = Some q0 → n1 = n2.
    { move=> n1 n2 q0. rewrite /bind'.
      destruct (decide (n1 = name)) as [-> | Hne1];
        destruct (decide (n2 = name)) as [-> | Hne2].
      - done.
      - rewrite lookup_insert_eq lookup_insert_ne //.
        move=> [= <-] Hq2.
        destruct (Hbindtypes n2 q Hq2) as [tm Htm]. rewrite Hfresh in Htm. done.
      - rewrite lookup_insert_eq lookup_insert_ne //.
        move=> Hq1 [= Heq]. subst q0.
        destruct (Hbindtypes n1 q Hq1) as [tm Htm]. rewrite Hfresh in Htm. done.
      - rewrite !lookup_insert_ne //. exact (Hbindinj n1 n2 q0). }
    have Htypesbound' : ∀ q0, is_Some (p' !! q0) → ∃ nm, bind' !! nm = Some q0.
    { move=> q0. rewrite /p' /bind'.
      destruct (decide (q0 = q)) as [-> | Hqp].
      - move=> _. exists name. rewrite lookup_insert_eq //.
      - rewrite lookup_insert_ne //. move=> Hq.
        destruct (Htypesbound q0 Hq) as [nm Hnm].
        exists nm. rewrite lookup_insert_ne //.
        move=> Heq. subst nm. rewrite Hb' in Hnm. done. }
    have Hnameempty : doc_model_get m (RootId name) = [].
    { destruct (doc_model_get m (RootId name)) as [| x l] eqn:Hdg; first done.
      have Hne : doc_model_get m (RootId name) ≠ [] by rewrite Hdg.
      destruct (Hmdom (RootId name) Hne) as (nm & q0 & Heq & Hq).
      injection Heq as <-. rewrite Hb' in Hq. done. }
    have Hmtypes' : ∀ nm q0 tm, bind' !! nm = Some q0 → p' !! q0 = Some tm →
        doc_model_get m (RootId nm) = tm_arr tm.
    { move=> nm q0 tm. rewrite /bind' /p'.
      destruct (decide (nm = name)) as [-> | Hne].
      - rewrite lookup_insert_eq. move=> [= <-]. rewrite lookup_insert_eq.
        move=> [= <-]. rewrite Hnameempty //.
      - rewrite lookup_insert_ne //. move=> Hq.
        destruct (decide (q0 = q)) as [-> | Hqp].
        + destruct (Hbindtypes nm q Hq) as [tm0 Htm0]. rewrite Hfresh in Htm0. done.
        + rewrite lookup_insert_ne //. exact (Hmtypes nm q0 tm Hq). }
    have Hmdom' : ∀ t, doc_model_get m t ≠ [] →
        ∃ nm q0, t = RootId nm ∧ bind' !! nm = Some q0.
    { move=> t Hne.
      destruct (Hmdom t Hne) as (nm & q0 & Heq & Hq).
      exists nm, q0. split; first exact Heq.
      rewrite /bind' lookup_insert_ne //.
      move=> Heq2. subst nm. rewrite Hb' in Hq. done. }
    have Hctr' : ∀ parent tm x, p' !! parent = Some tm → x ∈ tm_arr tm →
        clientId (item_id x) = uint.nat client → (clock (item_id x) < uint.nat k)%nat.
    { move=> parent tm x. rewrite /p'.
      destruct (decide (parent = q)) as [-> | Hne].
      - rewrite lookup_insert_eq. move=> [= <-] Hx. by apply elem_of_nil in Hx.
      - rewrite lookup_insert_ne //. exact (Hctr parent tm x). }
    (* registering an empty type moves no run, so the tombstone-set
       invariant transports over the same permutation *)
    iDestruct (own_delete_set_perm γs m (all_runs p) (all_runs p') Hperm
                 with "Hdelete_set") as "Hdelete_set".
    wp_auto.
    have Hregmodel' : pool_registry_models m bind' p'.
    { rewrite /pool_registry_models. split; [exact Hmtypes' | exact Hmdom']. }
    wp_apply (wp_Store__wunlock _ _ _ (uint.nat client) h m pend
                with "[$His_store $Hwl Hstate Hseq HtypesAuth Hhist Hacc Hdelete_set]").
    { iExists client, k, pdel, (<[q := []]> locs), p', bind', acc.
      iFrame "∗". iFrame "Hclientpin Hpendcert Hbinds'". iPureIntro.
      split_and!;
        [reflexivity | exact Hpendroot | exact Hpendbnd | exact Hregmodel' | exact Hhcoh
        | exact Hctr' | exact Hacccoh]. }
    wp_alloc t as "Ht".
    iPersist "Ht".
    wp_auto.
    iApply ("HΦ" $! t).
    iExists _, (dvv.(yjs.Doc.store')), q. iFrame "Ht His_store Hishist Hbindname".
    iSplitR; first done.
    iSplitR; first done.
    iSplitL; last (iPureIntro; constructor).
    iExact "Hlb0".
Qed.

End doc_GetText.
