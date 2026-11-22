(** A Go map range that gives the map back.

    The library's rule for [for k, v := range m]
    ([New.golang.theory.map.wp_map_for_range]) takes the map's ownership
    [mref ↦$ m] and does not return it, so it only fits a map nobody reads
    again. [wp_map_for_range_keep] is the same rule for a body that neither
    breaks nor returns, with the ownership handed back next to the final
    invariant. Its proof is the library's, with the ownership rebuilt at the
    loop's exit. No Cert-Yjs definition is mentioned here (the generated
    package is imported only for the ffi its section context needs). *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.

Section map_range.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context {sem : go.Semantics}.

Context `[!ZeroVal K] `[!EqDecision K] `[!Countable K] `[!ZeroVal V]
  `[IntoValInj0 : !go.IntoValInj K].

Set Default Proof Using "All".

Lemma wp_map_for_range_keep (invariant : list K -> Z -> iProp Σ) stk E (body : func.t)
    key_type elem_type mref (m : gmap K V) dq
    `{!TypedPointsto K} `{!IntoValTyped K key_type} :
  ∀ Φ,
  mref ↦${dq} m -∗
  (∀ keys,
     ⌜ list_to_set keys = dom m ∧ length keys = size m ∧ NoDup keys ⌝ -∗
     (invariant keys 0 ∗
      □ (∀ i key v, ⌜ keys !! (Z.to_nat i) = Some key ∧ m !! key = Some v ⌝ -∗
                    invariant keys i -∗
                    WP #body #key #v @ stk; E
                      {{ result, ⌜ result = execute_val ⌝ ∗ invariant keys (i+1) }}) ∗
      (invariant keys (Z.of_nat (size m)) -∗ mref ↦${dq} m -∗ Φ execute_val))
  ) -∗
  WP map.for_range key_type elem_type #mref #body @ stk; E {{ Φ }}.
Proof.
  iIntros "% Hm HΦ".
  wp_call.
  iDestruct (own_map_not_nil with "[$]") as %?.
  wp_if_destruct; first by exfalso.
  rewrite own_map_unseal. iNamed "Hm".
  wp_apply (_internal_wp_untyped_start_read with "Hown") as "Hown".
  wp_apply (wp_InternalMapForRange with "[//]"). iIntros "%ks %Hdom'".
  eapply go.is_map_domain_pure in Hdom'; last done.
  destruct Hdom' as [Hks_nodup Hks].
  assert (Forall (λ kv, ∃ (k : K), kv = #k) ks) as Heq.
  { rewrite Forall_forall. intros kv. rewrite -list_elem_of_In.
    intros Hk. specialize (Hks kv). specialize (Hdom kv).
    rewrite -Hks in Hk. apply Hdom in Hk. done. }
  apply Forall_exists_Forall2_l in Heq as [keys Heq].
  apply Forall2_fmap_2 in Heq. rewrite -list_eq_Forall2 in Heq.
  rewrite list_fmap_id in Heq. subst.
  iAssert (⌜ _ ⌝)%I with "[]" as "%Hfacts".
  2: iDestruct ("HΦ" $! keys with "[]") as "(HP & #Hiter & HΦ)".
  2: iPureIntro; exact Hfacts.
  { iPureIntro. eassert _ as Hl.
    2:{ split; first eexact Hl.
        apply NoDup_fmap in Hks_nodup; last tc_solve.
        rewrite <- (size_list_to_set (C:=gset K)); last done.
        rewrite Hl. rewrite size_dom //. }
    rewrite sets.set_eq. intros k.
    rewrite elem_of_list_to_set.
    specialize (Hks #k). specialize (Hagree k).
    rewrite list_elem_of_fmap_inj in Hks.
    rewrite -Hks. rewrite Hagree. rewrite elem_of_dom.
    by destruct lookup.
  }
  (* foldr  *)
  pose (i := 0).
  change (invariant keys 0) with (invariant keys i).
  iFreeze "Hiter".
  replace (into_val <$> keys) with (into_val <$> (drop (Z.to_nat i) keys)).
  2:{ rewrite drop_0 //. }
  iThaw "Hiter".
  iAssert (⌜ 0 ≤ i ≤ length keys ⌝)%I as "-#Hi"; first word.
  generalize i. clear i. intros i.
  iLöb as "IH" forall (i). iDestruct "Hi" as "%".
  destruct (decide (i < length keys)).
  2:{
    assert (i = length keys) by word. subst.
    nat_cleanup. rewrite drop_all /=.
    wp_auto. wp_apply "Hown". iIntros "Hown".
    wp_auto. destruct Hfacts as (? & -> & ?).
    iApply ("HΦ" with "HP"). rewrite /own_map_def. iFrame "∗%".
  }
  list_elem keys i as key.
  destruct (m !! key) eqn:Hlookup.
  2:{
    exfalso. apply not_elem_of_dom_2 in Hlookup as Hkey_m.
    destruct Hfacts as [Hfact _]. rewrite <- Hfact in Hkey_m.
    rewrite elem_of_list_to_set in Hkey_m.
    rewrite list_elem_of_lookup in Hkey_m. naive_solver.
  }
  iSpecialize ("Hiter" $! i key v with "[//] HP").
  erewrite drop_S; last done. rewrite fmap_cons foldr_cons.
  rewrite Hagree Hlookup /=. wp_apply (wp_wand with "Hiter").
  iIntros (execv) "[-> H]".
  rewrite -Z2Nat.inj_succ; last lia.
  wp_auto. rewrite execute_val_unseal. wp_auto.
  iApply ("IH" with "[$] [$] [$]").
  word.
Qed.

End map_range.
