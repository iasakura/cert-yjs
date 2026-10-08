(** [wp_Doc__GetOrCreateText]: the public root-type accessor (y-octo:
    Doc::get_or_create_text; Yjs doc.getText has the same get-or-create
    semantics under the shorter name). Takes the store's WRITE lock (first use
    registers the type), runs the public [wp_store__getOrCreateYType] (the
    store taken and returned whole, issue #219; issue #54 proved the miss
    branch), and hands back the persistent [Text] handle for [name] with the
    empty content lower bound ([own_store_bound_root_lb] mints it off the
    binding); a caller grows the bound by reading ([Len]/[String] intersect
    it with any [is_root_lb] certificate) or writing. Registering a fresh
    root is model-clean: an empty type adds no cells and no items, and the
    doc model [m] already maps every unbound root to [[]], so only the
    session's registry coherence and clock tie transport before release. *)
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

Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO store_state))}.
(* the observers' tokens and registrations (issue #198 Part II), as [store/heap] *)
Context {observed_inG : ghost_varG Σ (list (YjsItem go_string * bool))}.
Context {observers_inG : inG Σ (authR (gsetUR (gname * go_string)))}.
Context {observers_agree_inG : inG Σ (dfrac_agreeR (leibnizO observer_registry_model))}.

Lemma wp_Doc__GetOrCreateText (dv s_loc : loc) (γs : store_names) (γh : history_names)
    (name : P) :
  {{{ is_pkg_init yjs ∗ is_Doc dv s_loc γs γh ∗ is_history (A := A) (P := P) γh }}}
    dv @! (go.PointerType yjs.Doc) @! "GetOrCreateText" #name
  {{{ (t : loc), RET #t; is_Text t γs γh name [] ∅ }}}.
Proof.
  wp_start as "(#His_doc & #Hishist)".
  iNamed "His_doc". subst s_loc. wp_auto.
  wp_apply (wp_Store__wlock with "[$His_store]"). iIntros "[Hwl Hinv]".
  iDestruct "Hinv" as (c0 h m) "Hstore".
  wp_auto.
  iDestruct "Hstore" as (state0 ds0) "(Hstore & Hsession)".
  destruct state0 as [client0 k0 locs0 p0 bind0 pend0 pdel0].
  (* the entry registry coherence, kept to transport the session across the
     registry-growing call *)
  iDestruct "Hstore" as "[Hcore Hobservers]".
  iDestruct (own_store_core_registry_coh with "Hcore") as %Hreg0.
  have [Hbindtypes _] := Hreg0.
  iAssert (own_store (store_of_ref (dvv.(yjs.Doc.store'))) γs γh 1
             (MkStoreState client0 k0 locs0 p0 bind0 pend0 pdel0) ds0 m
             (pool_tombstoned p0)) with "[Hcore Hobservers]" as "Hstore".
  { rewrite /own_store. iFrame "Hcore Hobservers". }
  wp_apply (wp_store__getOrCreateYType with "[$Hstore]").
  iIntros (q p' locs' bind') "(Hstore & #Hbindname & %Hlc)".
  iEval (simpl) in "Hstore". simpl in Hlc.
  destruct Hlc as [(Hb' & -> & -> & ->) | (Hb' & Hfresh & -> & -> & ->)].
  - (* ---- hit: the root is registered; the session closes as it came ---- *)
    iMod (own_store_bound_root_lb _ _ _ 1 (MkStoreState client0 k0 locs0 p0 bind0 pend0 pdel0)
            _ _ _ name q Hb' with "Hstore") as "[Hstore #Hlb0]".
    wp_auto.
    wp_apply (wp_Store__wunlock with "[$His_store $Hwl $Hstore $Hsession]").
    (* a fresh handle knows of no deleted char: the empty lower bound of the
       store's delete set *)
    iMod (is_delete_set_lb_empty γs) as "#Hdel0".
    wp_alloc t as "Ht".
    iPersist "Ht".
    wp_auto.
    iApply ("HΦ" $! t).
    iExists _, (dvv.(yjs.Doc.store')), q, []. iFrame "Ht His_store Hishist Hbindname".
    iSplitR; first done.
    iSplitR; first done.
    iFrame "Hlb0 Hdel0".
    iPureIntro. split; [apply empty_subseteq | constructor].
  - (* ---- miss: a fresh empty root was registered; the model already maps
       the unbound name to [[]], so the registry coherence and the clock tie
       transport over the pool with the fresh empty type ---- *)
    set (p' := <[q := MkTypeModel []]> p0).
    set (bind' := <[name := q]> bind0).
    have Hbq : bind' !! name = Some q by rewrite /bind' lookup_insert_eq.
    iMod (own_store_bound_root_lb _ _ _ 1
            (MkStoreState client0 k0 (<[q := []]> locs0) p' bind' pend0 pdel0)
            _ _ _ name q Hbq with "Hstore") as "[Hstore #Hlb0]".
    wp_auto.
    iDestruct "Hstore" as "[Hcore Hobservers]".
    iNamed "Hsession".
    have [Hmtypes Hmdom] := Hregmodel.
    (* the unbound name's model entry is empty *)
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
    have Hregmodel' : pool_registry_models m bind' p'.
    { split; [exact Hmtypes' | exact Hmdom']. }
    have Hctr' : pool_next_clock p' c0 (uint.nat k0)
      := pool_next_clock_insert_empty p0 q _ _ Hfresh Hctr.
    (* registering an empty type tombstones nothing *)
    have Htomb' : pool_tombstoned p' = pool_tombstoned p0
      := pool_tombstoned_insert_empty p0 q Hfresh.
    iEval (rewrite -Htomb') in "Hobservers".
    iAssert (own_store_session γs γh c0 h m
               (MkStoreState client0 k0 (<[q := []]> locs0) p' bind' pend0 pdel0) ds0)
      with "[Hhist Hacc]" as "Hsession".
    { rewrite /own_store_session /=. iExists acc.
      iFrame "Hhist Hacc Hpendcert".
      iPureIntro.
      split_and!; [exact Hclient_is | exact Hhcoh | exact Hregmodel' | exact Hctr'
                  | exact Hpendroot | exact Hpendbnd | exact Hacccoh | exact Hds_dom]. }
    iAssert (own_store (store_of_ref (dvv.(yjs.Doc.store'))) γs γh 1
               (MkStoreState client0 k0 (<[q := []]> locs0) p' bind' pend0 pdel0) ds0 m
               (pool_tombstoned p'))
      with "[Hcore Hobservers]" as "Hstore".
    { rewrite /own_store. iFrame "Hcore Hobservers". }
    wp_apply (wp_Store__wunlock with "[$His_store $Hwl $Hstore $Hsession]").
    (* a fresh handle knows of no deleted char: the empty lower bound of the
       store's delete set *)
    iMod (is_delete_set_lb_empty γs) as "#Hdel0".
    wp_alloc t as "Ht".
    iPersist "Ht".
    wp_auto.
    iApply ("HΦ" $! t).
    iExists _, (dvv.(yjs.Doc.store')), q, []. iFrame "Ht His_store Hishist Hbindname".
    iSplitR; first done.
    iSplitR; first done.
    iFrame "Hlb0 Hdel0".
    iPureIntro. split; [apply empty_subseteq | constructor].
Qed.

End doc_GetText.
