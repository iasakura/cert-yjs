(** The ghost layer for the global operation history (issue #42).

    Wraps the pure bridge ([yjs_network_model]) in Perennial ghost state:

    - two [ghost_map]s under one global invariant [inv histN (history_inv γh)]:
      the per-client event histories (mirroring the model's [NodeHistories]
      directly) and the broadcast-op registry whose persistent elements are the
      op certificates;
    - [own_client_history γh c h]: the exclusive per-replica element (= the
      append capability), held by the replica's store-lock invariant;
    - [is_op_cert γh op D]: the persistent certificate — "op was broadcast, and
      [D] covers its strict causal past" — minted by [Text.Insert], consumed by
      [applyUpdate];
    - the ghost API: [history_alloc] / [history_broadcast] /
      [history_deliver_batch]. All are fupd-only (no WP): they open the
      invariant, apply a bridge lemma to re-establish [history_wf]/[ops_coh]
      (THE refinement obligation), and close — all inside one mask-preserving
      fancy update, no program step in between (plan §5.3).

    No goose here; [Σ] enters only through [heapGS] (for [allG] + invariants). *)
From New.proof Require Import proof_prelude.
From New.golang Require Import theory.
From New.proof Require Export yjs_core yjs_network_model.

Section history.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {A : Type} `{EqDA : EqDecision A}.
Context {P : Type} `{EqDP : !EqDecision P} `{CntP : !Countable P}.

Set Default Proof Using "Type*".

Local Notation TId := (TypeId P).
Local Notation Op := (TId * @YjsOperation A)%type.
Local Notation opid := (DocOp_id (A := A) (P := P)).
Local Notation Ev := (@Event Op).
Local Notation RawHistories := (gmap ClientId (list Ev)).
Local Notation DocM := (gmap TId (list (YjsItem A))).

(** One record instead of loose gnames (Perennial house style). *)
Record history_names := HistoryNames {
  hn_hist : gname;   (* ghost_map ClientId (list Ev)      *)
  hn_ops  : gname;   (* ghost_map YjsId (Op * gset YjsId) *)
}.

Definition histN : namespace := nroot .@ "cert_yjs" .@ "history".

(** The global invariant: both authorities, a copy of every certificate (so
    any party that can open the invariant and name a registered id can
    duplicate its certificate — certificate recovery for the network layer),
    and the two pure coherence facts. Re-proving [history_wf] at each ghost
    append is the refinement of the network model. *)
Definition history_inv (γh : history_names) : iProp Σ :=
  ∃ (N : RawHistories) (ops : gmap YjsId (Op * gset YjsId)),
    "HhistAuth" ∷ ghost_map_auth γh.(hn_hist) 1 N ∗
    "HopsAuth"  ∷ ghost_map_auth γh.(hn_ops) 1 ops ∗
    "#Hcerts"   ∷ ([∗ map] id ↦ p ∈ ops, id ↪[γh.(hn_ops)]□ p) ∗
    "%Hwf"      ∷ ⌜history_wf N⌝ ∗
    "%Hopscoh"  ∷ ⌜ops_coh N ops⌝.

Definition is_history (γh : history_names) : iProp Σ :=
  inv histN (history_inv γh).

(** Exclusive: this replica IS client [c], with event history [h]. Lives in
    the store lock invariant. *)
Definition own_client_history (γh : history_names) (c : ClientId) (h : list Ev) : iProp Σ :=
  c ↪[γh.(hn_hist)] h.

(** Persistent: [op] was broadcast; [D] covers its causal past. THE
    certificate. *)
Definition is_op_cert (γh : history_names) (op : Op) (D : gset YjsId) : iProp Σ :=
  (opid op) ↪[γh.(hn_ops)]□ (op, D).

#[global] Instance history_inv_timeless γh : Timeless (history_inv γh).
Proof. apply _. Qed.
#[global] Instance is_history_persistent γh : Persistent (is_history γh).
Proof. apply _. Qed.
#[global] Instance is_op_cert_persistent γh op D : Persistent (is_op_cert γh op D).
Proof. apply _. Qed.
#[global] Instance own_client_history_timeless γh c h : Timeless (own_client_history γh c h).
Proof. apply _. Qed.

(* ===== the ghost API ====================================================== *)

(** Allocation: client set fixed up front (plan §8.2). *)
Lemma history_alloc (C : gset ClientId) E :
  ⊢ |={E}=> ∃ γh, is_history γh ∗ [∗ set] c ∈ C, own_client_history γh c [].
Proof.
  iMod (ghost_map_alloc (gset_to_gmap ([] : list Ev) C)) as (γhist) "[HhistAuth Helems]".
  iMod (ghost_map_alloc (∅ : gmap YjsId (Op * gset YjsId))) as (γops) "[HopsAuth _]".
  set (γh := {| hn_hist := γhist; hn_ops := γops |}).
  iMod (inv_alloc histN _ (history_inv γh) with "[HhistAuth HopsAuth]") as "#Hinv".
  { iNext. iExists _, ∅. iFrame "HhistAuth HopsAuth".
    rewrite big_sepM_empty. iSplit; [done |].
    iPureIntro. split; [exact (history_wf_init C) | exact (ops_coh_init C)]. }
  iModIntro. iExists γh. iFrame "Hinv".
  rewrite big_sepM_gset_to_gmap. iApply "Helems".
Qed.

(** Broadcast (mint): append [EvBroadcast op; EvDeliver op] to the caller's
    own history and register the op with its causal-past cover
    [delivered_ids h]. Preconditions = the broadcast step's hypotheses, all
    available inside [wp_Text__Insert]'s loop at the call site; the clock
    bound is doc-global (all types, issue #49). *)
Lemma history_broadcast γh (c k : nat) h (m : DocM) (t0 : TId)
    (arr' : list (YjsItem A)) (input : IntegrateInput (A := A)) (item : YjsItem A) E :
  ↑histN ⊆ E ->
  toItem input (docm_get m t0) = Some item ->
  IsItemValid item ->
  maximalId item (docm_get m t0) ->
  in_id input = MkYjsId c k ->
  (∀ (t : TId) x, x ∈ docm_get m t -> clientId (item_id x) = c ->
     (clock (item_id x) < k)%nat) ->
  integrate input (docm_get m t0) = Some arr' ->
  history_state_coh h m ->
  is_history γh -∗ own_client_history γh c h ={E}=∗
  ∃ D : gset YjsId,
    own_client_history γh c
      (h ++ [EvBroadcast (t0, OpInsert input); EvDeliver (t0, OpInsert input)]) ∗
    is_op_cert γh (t0, OpInsert input) D ∗
    ⌜D ⊆ delivered_ids h⌝ ∗
    ⌜history_state_coh
       (h ++ [EvBroadcast (t0, OpInsert input); EvDeliver (t0, OpInsert input)])
       (<[t0 := arr']> m)⌝.
Proof.
  iIntros (HE Htoitem Hvalid Hmax Hinid Hbound Hint Hcoh) "#Hinv Hown".
  iInv "Hinv" as ">H" "Hclose". iNamed "H".
  iDestruct (ghost_map_lookup with "HhistAuth Hown") as %HNc.
  have Hfresh : ¬ id_broadcast N (in_id input).
  { rewrite Hinid. exact (history_fresh_id N c h m k Hwf HNc Hcoh Hbound). }
  pose proof (history_wf_broadcast N c h m t0 arr' input item k
                Hwf HNc Hcoh Htoitem Hvalid Hmax Hinid Hbound Hint)
    as (Hwf' & Hcoh' & Hreg').
  iMod (ghost_map_update
          (h ++ [EvBroadcast (t0, OpInsert input); EvDeliver (t0, OpInsert input)])
          with "HhistAuth Hown") as "[HhistAuth Hown]".
  pose proof (ops_coh_lookup_fresh N ops (in_id input) Hopscoh Hfresh) as Hnone.
  iMod (ghost_map_insert (in_id input) ((t0, OpInsert input) : Op, delivered_ids h) Hnone
          with "HopsAuth") as "[HopsAuth Hcert]".
  iMod (ghost_map_elem_persist with "Hcert") as "#Hcert".
  iMod ("Hclose" with "[HhistAuth HopsAuth]") as "_".
  { iNext. iExists _, _. iFrame "HhistAuth HopsAuth".
    iSplit.
    { rewrite big_sepM_insert; [| exact Hnone]. iFrame "Hcert Hcerts". }
    iPureIntro. split; [exact Hwf' |].
    exact (ops_coh_broadcast N c h ops (t0, OpInsert input) (delivered_ids h)
             Hwf HNc Hfresh Hopscoh Hreg'). }
  iModIntro. iExists (delivered_ids h). iFrame "Hown Hcert".
  iPureIntro. split; [done | exact Hcoh'].
Qed.

(** Deliver a certified batch (used by [applyUpdate]'s certificate spec):
    append one [EvDeliver] per batch op to the caller's history. Produces the
    [ValidReplay] the heap-level [applyUpdate] proof consumes, before any code
    runs. *)
Lemma history_deliver_batch γh (c : ClientId) h (m : DocM)
    (inputs : list (TId * IntegrateInput (A := A))) (Ds : list (gset YjsId)) E :
  ↑histN ⊆ E ->
  batch_ok h inputs Ds ->
  history_state_coh h m ->
  (∀ t : TId, YjsArrInvariant (docm_get m t)) ->
  is_history γh -∗ own_client_history γh c h -∗
  ([∗ list] ti;D ∈ inputs;Ds, is_op_cert γh (ti.1, OpInsert ti.2) D) ={E}=∗
  ∃ m' : DocM,
    own_client_history γh c (h ++ (deliver_ev <$> inputs)) ∗
    ⌜ValidReplay inputs m m'⌝ ∗
    ⌜history_state_coh (h ++ (deliver_ev <$> inputs)) m'⌝.
Proof.
  iIntros (HE Hbatch Hcoh Harrinv) "#Hinv Hown #Hcertsin".
  iInv "Hinv" as ">H" "Hclose". iNamed "H".
  iDestruct (ghost_map_lookup with "HhistAuth Hown") as %HNc.
  iDestruct (big_sepL2_length with "Hcertsin") as %Hlen.
  iAssert (⌜∀ (i : nat) (ti : TId * IntegrateInput (A := A)) (D : gset YjsId),
             inputs !! i = Some ti -> Ds !! i = Some D ->
             ops !! (in_id ti.2) = Some ((ti.1, OpInsert ti.2), D)⌝)%I as %Hlk.
  { iIntros (i ti D Hi HD).
    iDestruct (big_sepL2_lookup _ _ _ i with "Hcertsin") as "Hc"; [exact Hi | exact HD |].
    iApply (ghost_map_lookup with "HopsAuth Hc"). }
  have Hreg : ∀ (i : nat) (ti : TId * IntegrateInput (A := A)) (D : gset YjsId),
      inputs !! i = Some ti -> Ds !! i = Some D ->
      op_registered N (ti.1, OpInsert ti.2) D.
  { move=> i ti D Hi HD. destruct Hopscoh as [Hc1 _].
    exact (proj2 (Hc1 _ _ _ (Hlk i ti D Hi HD))). }
  pose proof (certs_ValidReplay N c h m inputs Ds Hwf HNc Hcoh Harrinv Hreg
                (eq_sym Hlen) Hbatch) as (m' & Hvr & Hcoh' & Hwf').
  iMod (ghost_map_update (h ++ (deliver_ev <$> inputs))
          with "HhistAuth Hown") as "[HhistAuth Hown]".
  iMod ("Hclose" with "[HhistAuth HopsAuth]") as "_".
  { iNext. iExists _, _. iFrame "HhistAuth HopsAuth Hcerts".
    iPureIntro. split; [exact Hwf' |].
    apply (ops_coh_deliver_tail N c h ops _ Hwf HNc); [| exact Hopscoh].
    move=> e He. move: He. rewrite list_elem_of_fmap.
    move=> [ti [Heq _]]. rewrite /deliver_ev in Heq. discriminate.
  }
  iModIntro. iExists m'. iFrame "Hown".
  iPureIntro. split; [exact Hvr | exact Hcoh'].
Qed.

(* ===== a two-client smoke test (ghost only, no WP) ======================= *)

(** Non-vacuity of the ghost story: allocate a two-client history, let client
    1 mint the trivial first insert (into the empty document, at an arbitrary
    root type [t]), and let client 2 deliver it — all inside one fancy update.
    This is the end-to-end composition of the three API lemmas over concrete
    data; an accidentally unsatisfiable invariant or step lemma would fail
    here. *)
Lemma history_smoke (a : A) (t : TId) (c1 c2 : ClientId) E :
  ↑histN ⊆ E ->
  c1 ≠ c2 ->
  ⊢ |={E}=> ∃ γh (input : IntegrateInput (A := A)) (D : gset YjsId),
      is_history γh ∗
      own_client_history γh c1
        [EvBroadcast (t, OpInsert input); EvDeliver (t, OpInsert input)] ∗
      own_client_history γh c2 [EvDeliver (t, OpInsert input)] ∗
      is_op_cert γh (t, OpInsert input) D.
Proof.
  iIntros (HE Hne).
  iMod (history_alloc {[c1; c2]} E) as (γh) "[#Hinv Helems]".
  rewrite big_sepS_union; last set_solver.
  rewrite !big_sepS_singleton.
  iDestruct "Helems" as "[H1 H2]".
  set (input := MkIntegrateInput (A := A) None None a (MkYjsId c1 0)).
  set (item := Item (A := A) First Last (MkYjsId c1 0) a).
  have Hnilget : ∀ t' : TId, docm_get (∅ : DocM) t' = []
    by move=> t'; rewrite /docm_get lookup_empty.
  have Htoitem : toItem input (docm_get (∅ : DocM) t) = Some item
    by rewrite Hnilget.
  have Hvalid : IsItemValid item.
  { split.
    - apply YjsLt'_ltOriginOrder. exact lt_first_last.
    - move=> x Hx.
      inversion Hx as [x0 y0 Hstep | x0 y0 z0 Hstep Hreach]; subst.
      + inversion Hstep; subst; [left | right]; exists 0%nat; exact (leqSame _ _).
      + inversion Hstep; subst;
          inversion Hreach as [x1 y1 Hstep2 | x1 y1 z1 Hstep2 ?]; subst;
          inversion Hstep2. }
  have Hmax : maximalId item (docm_get (∅ : DocM) t).
  { rewrite Hnilget. move=> x Hx. exfalso. move: Hx. rewrite /ArrSet /= elem_of_nil //. }
  have Hint : integrate input (docm_get (∅ : DocM) t) = Some [item]
    by rewrite Hnilget; vm_compute.
  have Hbound : ∀ (t' : TId) (x : YjsItem A), x ∈ docm_get (∅ : DocM) t' ->
      clientId (item_id x) = c1 -> (clock (item_id x) < 0)%nat.
  { move=> t' x Hx. exfalso. move: Hx. rewrite Hnilget elem_of_nil //. }
  iMod (history_broadcast γh c1 0%nat [] ∅ t [item] input item E HE
          Htoitem Hvalid Hmax eq_refl Hbound Hint history_state_coh_nil
          with "Hinv H1") as (D) "(H1 & #Hcert & %HDsub & %Hcoh1)".
  have HDempty : D = ∅.
  { move: HDsub. rewrite /delivered_ids /=. set_solver. }
  subst D.
  have Hbatch : batch_ok [] [(t, input)] [∅ : gset YjsId].
  { move=> i ti' D' Hi HD'.
    destruct i as [| i]; last by (destruct i; discriminate).
    injection Hi as <-. injection HD' as <-.
    rewrite /delivered_ids take_0 /=. split; set_solver. }
  have Hinvempty : ∀ t' : TId, YjsArrInvariant (docm_get (∅ : DocM) t').
  { move=> t'. rewrite Hnilget. exact YjsArrInvariant_empty. }
  iMod (history_deliver_batch γh c2 [] ∅ [(t, input)] [∅] E HE Hbatch
          history_state_coh_nil Hinvempty
          with "Hinv H2 []") as (m2) "(H2 & %Hvr & %Hcoh2)".
  { rewrite big_sepL2_singleton. iApply "Hcert". }
  iModIntro. iExists γh, input, ∅.
  iFrame "Hinv Hcert H1 H2".
Qed.

(** Certificate recovery: any party holding the invariant handle can duplicate
    the certificate of a registered id (used by the network layer's relay,
    docs/plan-network-p2p-layer.md §3). Registration is witnessed by any
    (partial) certificate-shaped fact; here we expose the basic agreement
    form: two certificates for ops with the same id agree. *)
Lemma is_op_cert_agree γh (op1 op2 : Op) (D1 D2 : gset YjsId) :
  opid op1 = opid op2 ->
  is_op_cert γh op1 D1 -∗ is_op_cert γh op2 D2 -∗ ⌜op1 = op2 ∧ D1 = D2⌝.
Proof.
  iIntros (Hid) "H1 H2". rewrite /is_op_cert Hid.
  iDestruct (ghost_map_elem_agree with "H1 H2") as %Heq.
  iPureIntro. by injection Heq.
Qed.

End history.
