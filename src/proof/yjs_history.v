(** The ghost layer for the global operation history (issue #42).

    Wraps the pure bridge ([yjs_network_model]) in Perennial ghost state:

    - under one global invariant [inv histN (history_inv γh)]: the per-client
      event histories as ONE auth-of-mono-lists map (mirroring the model's
      [NodeHistories]; elements are the replicas' exclusive handles, lower
      bounds the prefix certificates) and a broadcast-op registry [ghost_map]
      whose persistent elements are the op certificates;
    - [own_client_history γh c h]: the exclusive per-replica element (= the
      append capability), held by the replica's store-lock invariant; its
      persistent fragments [is_history_lb γh c h0] certify [h0] as a history
      prefix (the lossless replica-progress lower bound), minted afresh at
      every ghost append;
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
From iris.algebra Require Import auth gmap max_prefix_list.
From iris.algebra.lib Require Import mono_list.

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
Local Notation DocModel := (gmap TId (list (YjsItem A))).
(** The per-replica history RA: an authoritative map of mono-lists, ONE
    gname for everything history-shaped. The outer [auth] ties the whole map
    [N] to the invariant (membership + agreement); each client's inner
    [●ML h] fragment is that replica's exclusive element (two compose
    invalidly); the inner [◯ML h0] fragments are the persistent
    history-prefix certificates [is_history_lb]. *)
Local Notation EvO := (leibnizO Ev).
Local Notation histUR := (authR (gmapUR ClientId (mono_listR EvO))).

(** One record instead of loose gnames (Perennial house style). *)
Record history_names := HistoryNames {
  hn_hist : gname;   (* histUR: per-client histories (auth map of mono-lists;
                        elements = replicas' exclusive handles, lbs = the
                        prefix certificates) *)
  hn_ops  : gname;   (* ghost_map YjsId Op. Informationally derivable from
                        the histories ([ops_coh] says so), but kept as its
                        own gname: its persisted elements give UNCONDITIONAL
                        certificate agreement ([is_op_cert_agree]), which a
                        prefix-certificate encoding of op certs could only
                        provide under the invariant. Since issue #40 the
                        certificate carries NO causal-cover set: the
                        structural pending gate replaces causal-closure
                        obligations, so "broadcast, with this id" is the
                        whole certificate. *)
}.

Definition histN : namespace := nroot .@ "cert_yjs" .@ "history".

(** The per-client mono-list image of the raw history map (what the
    invariant's authority holds). *)
Definition hist_auth_map (N : RawHistories) : gmap ClientId (mono_listR EvO) :=
  (λ h, ●ML (h : list EvO)) <$> N.

Definition hist_auth (γ : gname) (N : RawHistories) : iProp Σ :=
  own γ (● (hist_auth_map N) : histUR).

(** The global invariant: both authorities, a copy of every certificate (so
    any party that can open the invariant and name a registered id can
    duplicate its certificate — certificate recovery for the network layer),
    and the two pure coherence facts. Re-proving [history_wf] at each ghost
    append is the refinement of the network model. *)
Definition history_inv (γh : history_names) : iProp Σ :=
  ∃ (N : RawHistories) (ops : gmap YjsId Op),
    "HhistAuth" ∷ hist_auth γh.(hn_hist) N ∗
    "HopsAuth"  ∷ ghost_map_auth γh.(hn_ops) 1 ops ∗
    "#Hcerts"   ∷ ([∗ map] id ↦ p ∈ ops, id ↪[γh.(hn_ops)]□ p) ∗
    "%Hwf"      ∷ ⌜history_wf N⌝ ∗
    "%Hopscoh"  ∷ ⌜ops_coh N ops⌝.

Definition is_history (γh : history_names) : iProp Σ :=
  inv histN (history_inv γh).

(** Exclusive: this replica IS client [c], with event history [h]. Lives in
    the store lock invariant. *)
Definition own_client_history (γh : history_names) (c : ClientId) (h : list Ev) : iProp Σ :=
  own γh.(hn_hist) (◯ {[ c := ●ML (h : list EvO) ]} : histUR).

(** Persistent: [h0] is (forever) a prefix of client [c]'s event history —
    the lossless "how far has this replica advanced" certificate. All the
    delivered views are monotone under it ([delivered_ops_prefix] /
    [delivered_ids_prefix] / [delivered_from_prefix_mono] / [sv_of_prefix]),
    and per author the delivered view is a prefix of that author's broadcast
    log ([delivered_from_prefix]), so two certificates about the same author
    are always comparable ([prefix_weak_total]). *)
Definition is_history_lb (γh : history_names) (c : ClientId) (h0 : list Ev) : iProp Σ :=
  own γh.(hn_hist) (◯ {[ c := ◯ML (h0 : list EvO) ]} : histUR).

(** Persistent: [op] was broadcast. THE certificate (issue #40: no
    causal-cover component — the structural pending gate needs none). *)
Definition is_op_cert (γh : history_names) (op : Op) : iProp Σ :=
  (opid op) ↪[γh.(hn_ops)]□ op.

(** Persistent: every struct of a decoded pending is certified — the ONLY
    obligation on an [applyUpdate] pending (issue #40): no ordering, closure,
    freshness, or receiver-relative condition. *)
Definition is_pending_certified (γh : history_names)
    (pending : list (TId * IntegrateInput (A := A))) : iProp Σ :=
  [∗ list] typedInput ∈ pending, is_op_cert γh (typedInput.1, OpInsert typedInput.2).

#[global] Instance history_inv_timeless γh : Timeless (history_inv γh).
Proof. apply _. Qed.
#[global] Instance is_history_persistent γh : Persistent (is_history γh).
Proof. apply _. Qed.
#[global] Instance is_op_cert_persistent γh op : Persistent (is_op_cert γh op).
Proof. apply _. Qed.
#[global] Instance is_pending_certified_persistent γh pending :
  Persistent (is_pending_certified γh pending).
Proof. apply _. Qed.
#[global] Instance own_client_history_timeless γh c h : Timeless (own_client_history γh c h).
Proof. apply _. Qed.
#[global] Instance is_history_lb_persistent γh c h0 : Persistent (is_history_lb γh c h0).
Proof. apply _. Qed.
#[global] Instance is_history_lb_timeless γh c h0 : Timeless (is_history_lb γh c h0).
Proof. apply _. Qed.
#[global] Instance hist_auth_timeless γ N : Timeless (hist_auth γ N).
Proof. apply _. Qed.

(** A saturated mono-list authority is only included in itself. *)
Local Lemma mono_list_auth_included_eq (l l' : list EvO) :
  (●ML l : mono_listR EvO) ≼ ●ML l' -> l = l'.
Proof.
  move=> Hincl.
  have Hincl' : (● (to_max_prefix_list l) : authR (max_prefix_listUR EvO)) ≼
                ● (to_max_prefix_list l') ⋅ ◯ (to_max_prefix_list l').
  { etrans; [apply cmra_included_l | exact Hincl]. }
  move: Hincl'. rewrite auth_auth_included. move=> Heq.
  have Hpre1 : l `prefix_of` l'.
  { apply to_max_prefix_list_included_L.
    exists (to_max_prefix_list l'). rewrite Heq -core_id_dup //. }
  have Hpre2 : l' `prefix_of` l.
  { apply to_max_prefix_list_included_L.
    exists (to_max_prefix_list l). rewrite -Heq -core_id_dup //. }
  by apply (anti_symm prefix).
Qed.

(** Membership + agreement: the authority pins a replica element exactly. *)
Lemma hist_auth_elem_lookup (γ : gname) (N : RawHistories) (c : ClientId) (h : list Ev) :
  hist_auth γ N -∗ own γ (◯ {[ c := ●ML (h : list EvO) ]} : histUR) -∗
  ⌜N !! c = Some h⌝.
Proof.
  iIntros "Ha He". iDestruct (own_valid_2 with "Ha He") as %Hv.
  iPureIntro. move: Hv.
  rewrite auth_both_valid_discrete. move=> [Hincl _].
  apply singleton_included_l in Hincl. destruct Hincl as (y & Hy & Hinc).
  move: Hy. rewrite /hist_auth_map lookup_fmap.
  move=> /fmap_Some_equiv [h' [HN Hyeq]].
  rewrite Hyeq in Hinc.
  have Hle : (●ML (h : list EvO) : mono_listR EvO) ≼ ●ML (h' : list EvO).
  { move: Hinc. rewrite Some_included. move=> [Heq | Hle]; [| exact Hle].
    exists (◯ML (h' : list EvO)). rewrite Heq -mono_list_auth_lb_op //. }
  by rewrite HN (mono_list_auth_included_eq h h' Hle).
Qed.

(** Duplicate the current prefix certificate out of the element (a mono-list
    authority contains its own lower bound). *)
Lemma own_client_history_lb (γh : history_names) (c : ClientId) (h : list Ev) :
  own_client_history γh c h -∗ own_client_history γh c h ∗ is_history_lb γh c h.
Proof.
  iIntros "He".
  iAssert (own γh.(hn_hist) ((◯ {[ c := ●ML (h : list EvO) ]} : histUR) ⋅
                             (◯ {[ c := ◯ML (h : list EvO) ]} : histUR)))%I
    with "[He]" as "[$ $]".
  rewrite -auth_frag_op singleton_op -mono_list_auth_lb_op. iFrame "He".
Qed.

(** A certificate really is a prefix of the current history. *)
Lemma is_history_lb_prefix (γh : history_names) (c : ClientId) (h h0 : list Ev) :
  own_client_history γh c h -∗ is_history_lb γh c h0 -∗ ⌜h0 `prefix_of` h⌝.
Proof.
  iIntros "He Hlb". iDestruct (own_valid_2 with "He Hlb") as %Hv.
  iPureIntro. move: Hv.
  rewrite -auth_frag_op auth_frag_valid singleton_op singleton_valid.
  rewrite mono_list_both_valid_L. done.
Qed.

(** Two replica elements for the same client cannot coexist. *)
Lemma own_client_history_exclusive (γh : history_names) (c : ClientId) (h h' : list Ev) :
  own_client_history γh c h -∗ own_client_history γh c h' -∗ False.
Proof.
  iIntros "H1 H2". iDestruct (own_valid_2 with "H1 H2") as %Hv.
  iPureIntro. move: Hv.
  rewrite -auth_frag_op auth_frag_valid singleton_op singleton_valid.
  rewrite mono_list_auth_op_valid //.
Qed.

(** Append: advance the authority and the element together, minting the new
    certificate (the ghost-step lemmas below use it at each history append). *)
Lemma hist_auth_elem_advance (γh : history_names) (N : RawHistories) (c : ClientId)
    (h tail : list Ev) :
  N !! c = Some h ->
  hist_auth γh.(hn_hist) N -∗ own_client_history γh c h ==∗
  hist_auth γh.(hn_hist) (<[c := h ++ tail]> N) ∗ own_client_history γh c (h ++ tail) ∗
  is_history_lb γh c (h ++ tail).
Proof.
  iIntros (HN) "Ha He".
  iMod (own_update_2 _ _ _
          ((● (hist_auth_map (<[c := h ++ tail]> N)) : histUR) ⋅
           (◯ {[ c := ●ML ((h ++ tail) : list EvO) ]} : histUR))
          with "Ha He") as "[Ha He]".
  { rewrite /hist_auth_map fmap_insert.
    apply auth_update.
    apply (singleton_local_update ((λ h1, ●ML (h1 : list EvO)) <$> N) c
             (●ML (h : list EvO)) (●ML (h : list EvO))
             (●ML ((h ++ tail) : list EvO)) (●ML ((h ++ tail) : list EvO))).
    { rewrite lookup_fmap HN //. }
    rewrite /mono_list_auth.
    apply auth_local_update.
    - apply max_prefix_list_local_update. by exists tail.
    - exists (to_max_prefix_list ((h ++ tail) : list EvO)). rewrite -core_id_dup //.
    - apply to_max_prefix_list_valid. }
  iModIntro. iFrame "Ha".
  iApply (own_client_history_lb with "He").
Qed.

(* ===== the ghost API ====================================================== *)

(** Allocation plumbing: the constant-[[]] authority map, and splitting the
    combined fragment into per-client elements. *)
Local Lemma hist_auth_map_gset_to_gmap (C : gset ClientId) :
  hist_auth_map (gset_to_gmap [] C) = gset_to_gmap (●ML ([] : list EvO)) C.
Proof.
  apply map_eq => c. rewrite /hist_auth_map lookup_fmap !lookup_gset_to_gmap.
  destruct (decide (c ∈ C)).
  - rewrite !option_guard_True //.
  - rewrite !option_guard_False //.
Qed.

Local Lemma own_frag_gset_to_gmap_singletons (γ : gname) (x : mono_listR EvO)
    (C : gset ClientId) :
  own γ (◯ (gset_to_gmap x C) : histUR) -∗
  [∗ set] c ∈ C, own γ (◯ {[ c := x ]} : histUR).
Proof.
  induction C as [| c C Hc IH] using set_ind_L.
  - rewrite gset_to_gmap_empty big_sepS_empty. by iIntros "_".
  - rewrite gset_to_gmap_union_singleton.
    rewrite insert_singleton_op; last by rewrite lookup_gset_to_gmap_None.
    rewrite auth_frag_op. iIntros "[Hc Hrest]".
    rewrite big_sepS_union; last set_solver.
    rewrite big_sepS_singleton. iFrame "Hc".
    by iApply IH.
Qed.

(** Allocation: client set fixed up front (plan §8.2). *)
Lemma history_alloc (C : gset ClientId) E :
  ⊢ |={E}=> ∃ γh, is_history γh ∗ [∗ set] c ∈ C, own_client_history γh c [].
Proof.
  iMod (own_alloc ((● (hist_auth_map (gset_to_gmap [] C)) : histUR) ⋅
                   (◯ (hist_auth_map (gset_to_gmap [] C)) : histUR))) as (γhist) "[HhistAuth Hf]".
  { apply auth_both_valid_discrete. split; [done |].
    move=> c. rewrite /hist_auth_map lookup_fmap lookup_gset_to_gmap.
    destruct (decide (c ∈ C)).
    - rewrite option_guard_True //. apply Some_valid, mono_list_auth_valid.
    - rewrite option_guard_False //. }
  iMod (ghost_map_alloc (∅ : gmap YjsId Op)) as (γops) "[HopsAuth _]".
  set (γh := {| hn_hist := γhist; hn_ops := γops |}).
  iMod (inv_alloc histN _ (history_inv γh) with "[HhistAuth HopsAuth]") as "#Hinv".
  { iNext. iExists _, ∅. iFrame "HhistAuth HopsAuth".
    rewrite big_sepM_empty. iSplit; [done |].
    iPureIntro. split; [exact (history_wf_init C) | exact (ops_coh_init C)]. }
  iModIntro. iExists γh. iFrame "Hinv".
  rewrite hist_auth_map_gset_to_gmap.
  by iApply (own_frag_gset_to_gmap_singletons with "Hf").
Qed.

(** Broadcast (mint): append [EvBroadcast op; EvDeliver op] to the caller's
    own history and register the op. Preconditions = the broadcast step's
    hypotheses, all available inside [wp_Text__Insert]'s loop at the call
    site; the clock bound is doc-global (all types, issue #49). *)
Lemma history_broadcast γh (c k : nat) h (m : DocModel) (t0 : TId)
    (arr' : list (YjsItem A)) (input : IntegrateInput (A := A)) (item : YjsItem A) E :
  ↑histN ⊆ E ->
  toItem input (doc_model_get m t0) = Some item ->
  IsItemValid item ->
  maximalId item (doc_model_get m t0) ->
  in_id input = MkYjsId c k ->
  (∀ (t : TId) x, x ∈ doc_model_get m t -> clientId (item_id x) = c ->
     (clock (item_id x) < k)%nat) ->
  integrate input (doc_model_get m t0) = Some arr' ->
  history_state_coh h m ->
  is_history γh -∗ own_client_history γh c h ={E}=∗
    own_client_history γh c
      (h ++ [EvBroadcast (t0, OpInsert input); EvDeliver (t0, OpInsert input)]) ∗
    is_history_lb γh c
      (h ++ [EvBroadcast (t0, OpInsert input); EvDeliver (t0, OpInsert input)]) ∗
    is_op_cert γh (t0, OpInsert input) ∗
    ⌜history_state_coh
       (h ++ [EvBroadcast (t0, OpInsert input); EvDeliver (t0, OpInsert input)])
       (<[t0 := arr']> m)⌝.
Proof.
  iIntros (HE Htoitem Hvalid Hmax Hinid Hbound Hint Hcoh) "#Hinv Hown".
  iInv "Hinv" as ">H" "Hclose". iNamed "H".
  iDestruct (hist_auth_elem_lookup with "HhistAuth Hown") as %HNc.
  have Hfresh : ¬ id_broadcast N (in_id input).
  { rewrite Hinid. exact (history_fresh_id N c h m k Hwf HNc Hcoh Hbound). }
  pose proof (history_wf_broadcast N c h m t0 arr' input item k
                Hwf HNc Hcoh Htoitem Hvalid Hmax Hinid Hbound Hint)
    as (Hwf' & Hcoh' & Hreg').
  iMod (hist_auth_elem_advance γh N c h
          [EvBroadcast (t0, OpInsert input); EvDeliver (t0, OpInsert input)]
          HNc with "HhistAuth Hown") as "(HhistAuth & Hown & #Hlb)".
  pose proof (ops_coh_lookup_fresh N ops (in_id input) Hopscoh Hfresh) as Hnone.
  iMod (ghost_map_insert (in_id input) ((t0, OpInsert input) : Op) Hnone
          with "HopsAuth") as "[HopsAuth Hcert]".
  iMod (ghost_map_elem_persist with "Hcert") as "#Hcert".
  iMod ("Hclose" with "[HhistAuth HopsAuth]") as "_".
  { iNext. iExists _, _. iFrame "HhistAuth HopsAuth".
    iSplit.
    { rewrite big_sepM_insert; [| exact Hnone]. iFrame "Hcert Hcerts". }
    iPureIntro. split; [exact Hwf' |].
    exact (ops_coh_broadcast N c h ops (t0, OpInsert input)
             Hwf HNc Hfresh Hopscoh Hreg'). }
  iModIntro. iFrame "Hown Hcert Hlb".
  iPureIntro. exact Hcoh'.
Qed.

(** Deliver a certified pending (used by the total [applyUpdate]'s certificate
    spec, issue #40): drain the pending against the coherent model, append one
    [EvDeliver] per APPLIED struct to the caller's history (the pending rest
    is delivered by a later call, when its dependencies have arrived), and
    return the [ValidReplay] the heap-level proof consumes. The ONLY
    obligation on the pending is per-op certification: no ordering, causal
    closure, freshness, or receiver-relative condition. *)
Lemma history_deliver_pending γh (c : ClientId) h (m : DocModel)
    (pending applied rest : list (TId * IntegrateInput (A := A))) (m' : DocModel) E :
  ↑histN ⊆ E ->
  pending_drain m pending = (applied, rest, m') ->
  history_state_coh h m ->
  is_history γh -∗ own_client_history γh c h -∗
  is_pending_certified γh pending ={E}=∗
    own_client_history γh c (h ++ (deliver_ev <$> applied)) ∗
    is_history_lb γh c (h ++ (deliver_ev <$> applied)) ∗
    ⌜ValidReplay applied m m'⌝ ∗
    ⌜history_state_coh (h ++ (deliver_ev <$> applied)) m'⌝ ∗
    ⌜inputs_not_from applied c⌝.
Proof.
  iIntros (HE Hdrain Hcoh) "#Hinv Hown #Hcertsin".
  iInv "Hinv" as ">H" "Hclose". iNamed "H".
  iDestruct (hist_auth_elem_lookup with "HhistAuth Hown") as %HNc.
  iAssert (⌜∀ typedInput : TId * IntegrateInput (A := A), typedInput ∈ pending ->
             ops !! (in_id typedInput.2) = Some ((typedInput.1, OpInsert typedInput.2) : Op)⌝)%I as %Hlk.
  { iIntros (typedInput Hin).
    destruct (list_elem_of_lookup_1 _ _ Hin) as (i & Hi).
    iDestruct (big_sepL_lookup _ _ i with "Hcertsin") as "Hc"; [exact Hi |].
    iApply (ghost_map_lookup with "HopsAuth Hc"). }
  have Hbc : ∀ typedInput : TId * IntegrateInput (A := A), typedInput ∈ pending ->
      op_broadcast N (typedInput.1, OpInsert typedInput.2).
  { move=> typedInput Hin. destruct Hopscoh as [Hc1 _].
    have [_ Hreg] := Hc1 _ _ (Hlk typedInput Hin).
    exists (clientId (opid ((typedInput.1, OpInsert typedInput.2) : Op))). exact Hreg. }
  have Happsub := proj1 (pending_drain_subset m pending applied rest m' Hdrain).
  have Hbcapp : ∀ typedInput : TId * IntegrateInput (A := A), typedInput ∈ applied ->
      op_broadcast N (typedInput.1, OpInsert typedInput.2).
  { move=> typedInput Hin. exact (Hbc typedInput (Happsub typedInput Hin)). }
  pose proof (pending_ValidReplay N c h m applied m' Hwf HNc Hcoh Hbcapp
                (pending_drain_replay m pending applied rest m' Hdrain))
    as (Hvr & Hcoh' & Hwf' & Hnoc).
  iMod (hist_auth_elem_advance γh N c h (deliver_ev <$> applied)
          HNc with "HhistAuth Hown") as "(HhistAuth & Hown & #Hlb)".
  iMod ("Hclose" with "[HhistAuth HopsAuth]") as "_".
  { iNext. iExists _, _. iFrame "HhistAuth HopsAuth Hcerts".
    iPureIntro. split; [exact Hwf' |].
    apply (ops_coh_deliver_tail N c h ops _ Hwf HNc); [| exact Hopscoh].
    move=> e He. move: He. rewrite list_elem_of_fmap.
    move=> [typedInput [Heq _]]. rewrite /deliver_ev in Heq. discriminate.
  }
  iModIntro. iFrame "Hown Hlb".
  iPureIntro. split_and!; [exact Hvr | exact Hcoh' | exact Hnoc].
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
  ⊢ |={E}=> ∃ γh (input : IntegrateInput (A := A)),
      is_history γh ∗
      own_client_history γh c1
        [EvBroadcast (t, OpInsert input); EvDeliver (t, OpInsert input)] ∗
      own_client_history γh c2 [EvDeliver (t, OpInsert input)] ∗
      is_op_cert γh (t, OpInsert input).
Proof.
  iIntros (HE Hne).
  iMod (history_alloc {[c1; c2]} E) as (γh) "[#Hinv Helems]".
  rewrite big_sepS_union; last set_solver.
  rewrite !big_sepS_singleton.
  iDestruct "Helems" as "[H1 H2]".
  set (input := MkIntegrateInput (A := A) None None a (MkYjsId c1 0)).
  set (item := Item (A := A) First Last (MkYjsId c1 0) a).
  have Hnilget : ∀ t' : TId, doc_model_get (∅ : DocModel) t' = []
    by move=> t'; rewrite /doc_model_get lookup_empty.
  have Htoitem : toItem input (doc_model_get (∅ : DocModel) t) = Some item
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
  have Hmax : maximalId item (doc_model_get (∅ : DocModel) t).
  { rewrite Hnilget. move=> x Hx. exfalso. move: Hx. rewrite /ArrSet /= elem_of_nil //. }
  have Hint : integrate input (doc_model_get (∅ : DocModel) t) = Some [item]
    by rewrite Hnilget; vm_compute.
  have Hbound : ∀ (t' : TId) (x : YjsItem A), x ∈ doc_model_get (∅ : DocModel) t' ->
      clientId (item_id x) = c1 -> (clock (item_id x) < 0)%nat.
  { move=> t' x Hx. exfalso. move: Hx. rewrite Hnilget elem_of_nil //. }
  iMod (history_broadcast γh c1 0%nat [] ∅ t [item] input item E HE
          Htoitem Hvalid Hmax eq_refl Hbound Hint history_state_coh_nil
          with "Hinv H1") as "(H1 & #Hlb1 & #Hcert & %Hcoh1)".
  (* client 2 receives the op as a one-struct pending: the drain applies it *)
  have Hdmh : doc_model_has (∅ : DocModel) (in_id input) = false.
  { rewrite /doc_model_has map_to_list_empty //. }
  have Hdrain : pending_drain (∅ : DocModel) [(t, input)]
              = ([(t, input)], [], <[t := [item]]> (∅ : DocModel)).
  { rewrite /pending_drain /= Hdmh /= Hint //=. }
  iMod (history_deliver_pending γh c2 [] ∅ [(t, input)] [(t, input)] []
          (<[t := [item]]> ∅) E HE Hdrain history_state_coh_nil
          with "Hinv H2 []") as "(H2 & #Hlb2 & %Hvr & %Hcoh2 & %Hnoc)".
  { rewrite /is_pending_certified big_sepL_singleton. iApply "Hcert". }
  iModIntro. iExists γh, input.
  iFrame "Hinv Hcert H1 H2".
Qed.

(** Certificate recovery: any party holding the invariant handle can duplicate
    the certificate of a registered id (used by the network layer's relay,
    docs/plan-network-p2p-layer.md §3). Registration is witnessed by any
    (partial) certificate-shaped fact; here we expose the basic agreement
    form: two certificates for ops with the same id agree. *)
Lemma is_op_cert_agree γh (op1 op2 : Op) :
  opid op1 = opid op2 ->
  is_op_cert γh op1 -∗ is_op_cert γh op2 -∗ ⌜op1 = op2⌝.
Proof.
  iIntros (Hid) "H1 H2". rewrite /is_op_cert Hid.
  iDestruct (ghost_map_elem_agree with "H1 H2") as %Heq.
  iPureIntro. exact Heq.
Qed.

End history.
