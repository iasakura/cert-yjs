(** The [store] VALUE layer, part 1: the TYPE POOL, its registry coherence and
    the per-client item index the store invariant is stated over. Go values
    but no Iris.

    Definitions
    - [store_state_runs]: every field of the store as the invariant sees it,
      the type pool as an address map plus a run pool ([sr_locs] / [sr_pool]);
      [locs_wf], the address map covering the registered types with one
      address per run and no address twice; [locs_aligned], its pure
      alignment with a run pool.
    - the registry: [pool_registry_coh] / [pool_registry_models] /
      [pool_doc_registry_coh] (a binding names a registered type, whose runs
      spell the document model), and [pool_lookup_or_create], what
      [getOrCreateYType] does to it.
    - the per-client item index: [pool_entries], the pool's (address, run)
      pairs, read by [entry_client] / [entry_clock] / [entry_pr] / [entry_le]
      / [entry_kp]; [kp_client_locs], one client's addresses in clock order
      off those keys (unique under [kp_clkloc]); [client_locs] /
      [client_entries], the same over the entries; [sorted_client_entries],
      any clock-sorted address-distinct list of one client's entries.
    - what one integrate asks and does: [run_denotes] (the new run is the
      input's) and [integrate_locs] (the address-list half of the splice).

    Laws
    - the address map under the steps a store takes: a same-length type
      update ([locs_wf_insert_same_len]), a fresh empty type
      ([locs_wf_insert_empty]) and one integrate splice
      ([locs_wf_integrate]); [locs_aligned_lens] gives each type a
      same-length address list.
    - the registry only grows: an existing binding survives a type update
      ([pool_registry_coh_insert_existing]), a fresh name extends the map
      ([pool_registry_coh_bind_fresh] / [pool_registry_coh_dom_mono]), and an
      id no registered type holds is absent from the document model
      ([pool_docm_has_registry_false]).
    - the index under those same steps: [kp_client_locs] is stable under any
      key permutation ([kp_client_locs_perm]), ignores another client's keys
      ([_other]) and an absent address ([_absent]), and grows by one address
      at a maximal clock ([_snoc_max] / [_insert]); the pool's entries sit at
      their slots ([pool_entries_slot] / [pool_entries_snd] /
      [pool_entries_locs_NoDup]), one integrate splice adds its entry
      ([pool_entries_integrate]), a tombstoning keeps every key
      ([pool_entries_flip_kp]) and a fresh empty type adds none
      ([pool_entries_insert_empty]).
    - [client_entries] is that index as entries ([client_entries_mem] /
      [_prs] / [_sorted] / [_lookup_slot] / [_NoDup_locs],
      [client_locs_entries]), is itself a [sorted_client_entries]
      ([client_entries_sorted_client]), and any such list has disjoint clock
      ranges ([sorted_client_entries_disjoint]).
    - what a delete step transports ([pool_after_delete_seq_map] /
      [pool_after_delete_arr_pointwise] /
      [pool_registry_models_after_delete]) and what a one-type run rebuild
      transports ([pool_registry_models_ext] / [pool_arr_pointwise_ext] /
      [pool_seq_map_ext] / [pool_seq_map_insert_at]).
    - the entries' addresses are the address map's addresses up to order
      ([pool_entries_locs_perm]), so the map's [NoDup] is the index's
      ([pool_entries_locs_NoDup]).

    The rest of the value layer: [store/value_split.v] (the split surgery),
    [store/value_span.v] (id ranges and wire spans). The Iris layer over all
    of it is [store/heap.v]. *)

From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core prelude algebra network_model.
From iris.algebra Require Import auth gmap gset.
From stdpp Require Import sorting.
Local Open Scope Z_scope.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
From New.proof.store Require Import model value_span.
From New.proof.id Require Import value heap.
From New.proof.item Require Import run_theory model value heap.
From New.proof.ytype Require Import model value heap.

Section store_value_cells.

Set Default Proof Using "Type*".

Notation A := go_string.

Notation P := go_string.

Local Notation TId := (TypeId P).

Local Notation Op := (TId * @YjsOperation A)%type.

Local Notation Ev := (@Event Op).

Local Notation DocModel := (gmap TId (list (YjsItem A))).

(* ===== definitions ======================================================== *)

(* ----- the store's item index: map[Client][]*item ------------------------ *)

(** One client's backing slice in the index is the address sequence of a
    [merge_sort]ed run, so it depends only on each entry's (clock, address)
    pair: [pr_le] is the order that sort runs on, and [kp_client_locs] below
    is where the pair is read. *)
Definition pr_le (p q : Z * loc) : Prop := (p.1 <= q.1)%Z.

#[local] Instance pr_le_dec : RelDecision pr_le.
Proof. rewrite /pr_le. solve_decision. Defined.
#[local] Instance pr_le_trans : Transitive pr_le.
Proof. rewrite /pr_le. move=> x y z. lia. Qed.
#[local] Instance pr_le_total : Total pr_le.
Proof. rewrite /pr_le. move=> x y. lia. Qed.

(** [run_denotes input newItem run]: the run a wire item lands as: its head is
    the item the input resolves to (same id and origins) and it has one char
    per byte of the input's content. *)
Definition run_denotes (input : IntegrateInput (A := A)) (newItem : YjsItem A)
    (run : list (YjsItem A)) : Prop :=
  item_id (hd inhabitant run) = in_id input ∧
  origin (hd inhabitant run) = origin newItem ∧
  rightOrigin (hd inhabitant run) = rightOrigin newItem ∧
  length run = length (in_content input).

(** [integrate_locs ls idx item_l]: the address-list half of one integrate
    splice: the fresh node's address [item_l] inserted at the cursor [idx]
    ([runs_integrate_splice_at] is the run half, at the same cursor). *)
Definition integrate_locs (ls : list loc) (idx : nat) (item_l : loc) : list loc :=
  take idx ls ++ item_l :: drop idx ls.

(** [pool_registry_coh bind p] / [pool_registry_models m bind p]: a binding
    names a registered type and only one, every registered type is named, and
    a named type's runs spell the document model at that name. What the
    repair / applyUpdate specs are stated over. *)
Definition pool_registry_coh (bind : gmap P loc) (p : pool) : Prop :=
  (∀ nm q, bind !! nm = Some q -> is_Some (p !! q)) /\
  (∀ n1 n2 q, bind !! n1 = Some q -> bind !! n2 = Some q -> n1 = n2) /\
  (∀ q, is_Some (p !! q) -> ∃ nm, bind !! nm = Some q).

Definition pool_registry_models (m : DocModel) (bind : gmap P loc) (p : pool) : Prop :=
  (∀ nm q tm, bind !! nm = Some q -> p !! q = Some tm ->
     doc_model_get m (RootId nm) = tm_arr tm) /\
  (∀ t, doc_model_get m t ≠ [] -> ∃ nm q, t = RootId nm /\ bind !! nm = Some q).

(** [pool_doc_registry_coh m bind p]: both registry clauses at once (what the
    lock body carries). *)
Definition pool_doc_registry_coh (m : DocModel) (bind : gmap P loc) (p : pool) : Prop :=
  pool_registry_coh bind p /\ pool_registry_models m bind p.

(** [pool_lookup_or_create p ls bind nm q p' ls' bind']: what
    [getOrCreateYType] does to the registry, over the pool and its address
    map: the root bound to [nm] handed back unchanged, or [nm] bound to a
    fresh empty type at [q] (empty run list, empty address list). *)
Definition pool_lookup_or_create (p : pool) (ls : gmap loc (list loc))
    (bind : gmap P loc) (nm : P) (q : loc)
    (p' : pool) (ls' : gmap loc (list loc)) (bind' : gmap P loc) : Prop :=
  (bind !! nm = Some q ∧ p' = p ∧ ls' = ls ∧ bind' = bind) ∨
  (bind !! nm = None ∧ p !! q = None ∧
   p' = <[q := MkTypeModel [] []]> p ∧ ls' = <[q := []]> ls ∧
   bind' = <[nm := q]> bind).

(* ===== lemmas ============================================================= *)

(** [store_state_runs]: every field of the store as the invariant sees it,
    the type pool as an address map [sr_locs] and a run pool [sr_pool].
    [own_store_runs] ([store/heap.v]) is the store at such a state. *)
Record store_state_runs := MkStoreStateRuns {
  sr_client : w64;
  sr_clock : w64;
  sr_locs : gmap loc (list loc);
  sr_pool : pool;
  sr_bind : gmap P loc;
  sr_pending : list (TId * IntegrateInput (A := A));
  sr_pending_deletes : list delete_span;
}.

#[export] Instance settable_store_state_runs : Settable store_state_runs :=
  settable! MkStoreStateRuns
    <sr_client; sr_clock; sr_locs; sr_pool; sr_bind; sr_pending; sr_pending_deletes>.

(** [locs_aligned locs p]: the pure alignment of an address map with a run
    pool: same type domain, and per type as many addresses as runs. The half
    of [locs_wf] that drops the address [NoDup]. *)
Definition locs_aligned (locs : gmap loc (list loc)) (p : pool) : Prop :=
  dom locs = dom p ∧
  (∀ parent ls tm, locs !! parent = Some ls -> p !! parent = Some tm ->
     length ls = length (tm_runs tm)).

(** [locs_wf locs p]: the well-formedness of the address map: it covers
    exactly the registered types, one node address per run, and no node is in
    two types or at two indices. This is the address half of the pool
    invariants, the pure half being [run_pool_invs] ([store/model.v]). *)
Definition locs_wf (locs : gmap loc (list loc)) (p : pool) : Prop :=
  dom locs = dom p ∧
  NoDup (concat ((map_to_list locs).*2)) ∧
  (∀ parent ls tm, locs !! parent = Some ls -> p !! parent = Some tm ->
     length ls = length (tm_runs tm)).

(** An aligned address map has a same-length address list for every type. *)
Lemma locs_aligned_lens (locs : gmap loc (list loc)) (p : pool) :
  locs_aligned locs p ->
  ∀ parent tm, p !! parent = Some tm ->
    ∃ ls, locs !! parent = Some ls ∧ length ls = length (tm_runs tm).
Proof.
  move=> [Hdom Hlens] parent tm Hp.
  have His : is_Some (locs !! parent).
  { apply elem_of_dom. rewrite Hdom. apply elem_of_dom. by exists tm. }
  destruct His as [ls Hls]. exists ls. split; [done | exact (Hlens parent ls tm Hls Hp)].
Qed.

(** [locs_wf] survives replacing one type's model by one with as many runs
    (a tombstone flip, a per-run update): the address map is untouched. *)
Lemma locs_wf_insert_same_len (locs : gmap loc (list loc)) (p : pool)
    (parent : loc) (tm tm' : type_model) :
  p !! parent = Some tm ->
  length (tm_runs tm') = length (tm_runs tm) ->
  locs_wf locs p -> locs_wf locs (<[parent := tm']> p).
Proof.
  move=> Hp Hlen [Hdom [Hnd Hlens]]. split_and!.
  - rewrite dom_insert_L Hdom. symmetry.
    apply subseteq_union_1_L, singleton_subseteq_l. apply elem_of_dom. by exists tm.
  - exact Hnd.
  - move=> q lsq tmq Hlsq Htmq.
    destruct (decide (q = parent)) as [-> | Hne].
    + rewrite lookup_insert_eq in Htmq. injection Htmq as <-. rewrite Hlen.
      exact (Hlens parent lsq tm Hlsq Hp).
    + rewrite lookup_insert_ne in Htmq; [| congruence]. exact (Hlens q lsq tmq Hlsq Htmq).
Qed.

(** Registering a fresh empty type keeps the address map well formed. *)
Lemma locs_wf_insert_empty (locs : gmap loc (list loc)) (p : pool) (q : loc) :
  p !! q = None ->
  locs_wf locs p ->
  locs_wf (<[q := []]> locs) (<[q := MkTypeModel [] []]> p).
Proof.
  move=> Hq [Hdom [Hnd Hlens]].
  have Hlq : locs !! q = None.
  { destruct (locs !! q) as [ls|] eqn:Hls; last done.
    exfalso. have Hin : q ∈ dom p by (rewrite -Hdom; apply elem_of_dom; by eexists).
    apply elem_of_dom in Hin. rewrite Hq in Hin. by destruct Hin. }
  split_and!.
  - rewrite !dom_insert_L Hdom //.
  - rewrite (concat_perm _ _ (Permutation_map snd (map_to_list_insert locs q [] Hlq))) /= //.
  - move=> q0 ls0 tm0. destruct (decide (q0 = q)) as [-> | Hne].
    + rewrite !lookup_insert_eq. move=> [= <-] [= <-]. done.
    + rewrite !lookup_insert_ne //. exact (Hlens q0 ls0 tm0).
Qed.

(** The pool's registry coherence only reads the pool's domain: replacing a
    registered type's model keeps it. *)
Lemma pool_registry_coh_insert_existing (bind : gmap P loc) (p : pool) (parent : loc) (tm tm' : type_model) :
  p !! parent = Some tm ->
  pool_registry_coh bind p -> pool_registry_coh bind (<[parent := tm']> p).
Proof.
  move=> Hp [H1 [H2 H3]]. split_and!; [| exact H2 |].
  - move=> nm q Hq. destruct (decide (q = parent)) as [-> | Hne].
    + rewrite lookup_insert_eq. by eexists.
    + rewrite lookup_insert_ne; [exact (H1 nm q Hq) | congruence].
  - move=> q Hq. destruct (decide (q = parent)) as [-> | Hne].
    + apply H3. by exists tm.
    + rewrite lookup_insert_ne in Hq; [exact (H3 q Hq) | congruence].
Qed.

(** Registering a fresh name at a fresh type keeps the registry coherent. *)
Lemma pool_registry_coh_bind_fresh (bind : gmap P loc) (p : pool)
    (nm : P) (q : loc) (tm : type_model) :
  bind !! nm = None ->
  p !! q = None ->
  pool_registry_coh bind p ->
  pool_registry_coh (<[nm := q]> bind) (<[q := tm]> p).
Proof.
  move=> Hnm Hq [Hbt [Hinj Htb]].
  have Hqnotbound : ∀ name, bind !! name = Some q -> False.
  { move=> name Hb. destruct (Hbt name q Hb) as [tm0 Htm0]. rewrite Hq in Htm0. done. }
  split_and!.
  - move=> name q0. destruct (decide (name = nm)) as [-> | Hne].
    + rewrite lookup_insert_eq. move=> [= <-]. rewrite lookup_insert_eq. by eexists.
    + rewrite lookup_insert_ne //. move=> Hb.
      destruct (decide (q0 = q)) as [-> | Hqq]; first (exfalso; exact (Hqnotbound name Hb)).
      rewrite lookup_insert_ne //. exact (Hbt name q0 Hb).
  - move=> n1 n2 q0. destruct (decide (n1 = nm)) as [-> | Hne1];
      destruct (decide (n2 = nm)) as [-> | Hne2].
    + done.
    + rewrite lookup_insert_eq lookup_insert_ne //. move=> [= <-] Hb2.
      exfalso. exact (Hqnotbound n2 Hb2).
    + rewrite lookup_insert_eq lookup_insert_ne //. move=> Hb1 [= Heq]. subst q0.
      exfalso. exact (Hqnotbound n1 Hb1).
    + rewrite !lookup_insert_ne //. exact (Hinj n1 n2 q0).
  - move=> q0. destruct (decide (q0 = q)) as [-> | Hne].
    + move=> _. exists nm. by rewrite lookup_insert_eq.
    + rewrite lookup_insert_ne //. move=> Hq0.
      destruct (Htb q0 Hq0) as [name Hb]. exists name.
      rewrite lookup_insert_ne //. move=> Heq. subst name. rewrite Hnm in Hb. done.
Qed.

(** [pool_entries locs p]: the store's nodes as [(address, run)] pairs: every
    run of every registered type zipped with its address, in the registry's
    order ([all_runs p] with the addresses put back). The per-client item
    index ([own_item_map_runs]) is built from it. *)
Definition pool_entries (locs : gmap loc (list loc)) (p : pool) : list (loc * ItemRun) :=
  concat ((λ kv, zip (default [] (locs !! kv.1)) (tm_runs kv.2)) <$> map_to_list p).

(** An entry's client and clock in machine words, its (clock, address) key
    and the clock order the item index sorts by; [entry_kp] bundles the
    (client, clock, address) key. *)
Definition entry_client (e : loc * ItemRun) : w64 := W64 (run_client e.2).
Definition entry_clock (e : loc * ItemRun) : w64 := W64 (run_clock e.2).
Definition entry_pr (e : loc * ItemRun) : Z * loc := (uint.Z (entry_clock e), e.1).
Definition entry_le (a b : loc * ItemRun) : Prop := (uint.Z (entry_clock a) <= uint.Z (entry_clock b))%Z.

#[local] Instance entry_le_dec : RelDecision entry_le.
Proof. rewrite /entry_le. solve_decision. Defined.
#[local] Instance entry_le_trans : Transitive entry_le.
Proof. rewrite /entry_le. move=> x y z. lia. Qed.
#[local] Instance entry_le_total : Total entry_le.
Proof. rewrite /entry_le. move=> x y. lia. Qed.

Definition entry_kp (e : loc * ItemRun) : w64 * (Z * loc) := (entry_client e, entry_pr e).

(** [kp_clkloc kps]: one client's clock names one address, over a
    (client, clock, address) list: the uniqueness the item index relies on
    ([own_item_map_runs]'s [Hclkloc] clause). *)
Definition kp_clkloc (kps : list (w64 * (Z * loc))) : Prop :=
  ∀ a b, a ∈ kps -> b ∈ kps -> a.1 = b.1 -> a.2.1 = b.2.1 -> a.2.2 = b.2.2.

(** [kp_client_locs client kps]: client [client]'s addresses in clock order
    off a (client, clock, address) list: the item index's backing slice for
    that client. [client_locs] is this over the pool's entries. *)
Definition kp_client_locs (client : w64) (kps : list (w64 * (Z * loc))) : list loc :=
  snd <$> merge_sort pr_le ((filter (λ kp, kp.1 = client) kps).*2).

(** [client_locs locs p client]: the client's clock-sorted node-address
    slice at [(locs, p)], the model of that client's backing slice in
    [own_item_map_runs]. *)
Definition client_locs (locs : gmap loc (list loc)) (p : pool) (client : w64) : list loc :=
  kp_client_locs client (entry_kp <$> pool_entries locs p).

(** [client_entries locs p client]: the client's entries in clock order, the
    index's addresses with their runs ([client_locs_entries]); what the
    index walk ([getNodeIndex]) probes. *)
Definition client_entries (locs : gmap loc (list loc)) (p : pool) (client : w64) : list (loc * ItemRun) :=
  merge_sort entry_le (filter (λ e, entry_client e = client) (pool_entries locs p)).

(** [sorted_client_entries locs p client E]: [E] lists entries of client
    [client] from the pool [(locs, p)], clock-sorted and without a repeated
    address: the index's entries for [client] ([client_entries]), or those
    with one run rewritten during a split. What the index walk
    ([wp_getNodeIndex_runs]) searches. *)
Definition sorted_client_entries (locs : gmap loc (list loc)) (p : pool) (client : w64)
    (E : list (loc * ItemRun)) : Prop :=
  StronglySorted entry_le E ∧ NoDup E.*1 ∧
  (∀ e, e ∈ E -> e ∈ pool_entries locs p ∧ entry_client e = client).

(** A one-char input lands as exactly the item it resolves to: the run has
    one char, whose id is the new item's, and ids are unique in the valid
    result ([id_unique]). *)
Lemma integrate_unit_run (arr arr' : list (YjsItem A)) (input : IntegrateInput (A := A))
    (newItem : YjsItem A) (run : list (YjsItem A)) :
  YjsArrInvariant arr ->
  integrate_ready arr input newItem ->
  integrate input arr = Some arr' ->
  YjsArrInvariant arr' ->
  run_denotes input newItem run ->
  length (in_content input) = 1%nat ->
  (∀ x, x ∈ run -> x ∈ arr') ->
  run = [newItem].
Proof.
  move=> Hinv [Htoitem [Hvalid Hmax]] Hintegrate Hinv' [Hid [_ [_ Hlen]]] Hlen1 Hsub.
  rewrite Hlen1 in Hlen.
  destruct run as [| x [| y tl]]; simpl in Hlen; [done | | done].
  have Hxin : x ∈ arr' := Hsub x (list_elem_of_here x []).
  have HnewIn : newItem ∈ arr'.
  { destruct (YjsArrInvariant_integrate input arr arr' newItem Hinv Htoitem Hvalid Hmax Hintegrate)
      as [i [Hile' [Harr'eq _]]].
    rewrite Harr'eq. apply (proj2 (mem_insertIdxIfInBounds _ _ _ _ Hile')). left. reflexivity. }
  have Hidnew : item_id newItem = in_id input := commutativity.toItem_id input arr newItem Htoitem.
  f_equal.
  apply (id_unique (ArrSet arr') (yai_item_set_inv _ Hinv') x newItem);
    [simpl in Hid; rewrite Hid Hidnew // | exact Hxin | exact HnewIn].
Qed.

(** A step that only adds bindings only adds types. *)
Lemma pool_registry_coh_dom_mono (bind bind' : gmap P loc) (p p' : pool) :
  pool_registry_coh bind p -> pool_registry_coh bind' p' -> bind ⊆ bind' ->
  dom p ⊆ dom p'.
Proof.
  move=> [_ [_ Htb]] [Hbt' _] Hsub q. rewrite !elem_of_dom. move=> Hq.
  destruct (Htb q Hq) as [nm Hnm]. exact (Hbt' nm q (lookup_weaken _ _ _ _ Hnm Hsub)).
Qed.

(** [kp_client_locs] only sees the (client, clock, address) multiset: under
    [kp_clkloc] a permutation sorts to the same addresses, a key of another
    client leaves the slice alone, a client absent from the keys has the
    empty slice, a key at the client's newest clock lands
    at the tail (the [addNode] step), and a key strictly between the sorted
    clocks lands at that position (the split step). *)
Lemma kp_client_locs_perm (client : w64) (kps1 kps2 : list (w64 * (Z * loc))) :
  kp_clkloc kps1 -> kps1 ≡ₚ kps2 ->
  kp_client_locs client kps1 = kp_client_locs client kps2.
Proof.
  move=> Hkd Hperm. rewrite /kp_client_locs. f_equal.
  apply (StronglySorted_unique_strong pr_le).
  - move=> p1 p2 Hp1 Hp2 H12 H21.
    rewrite merge_sort_Permutation in Hp1. rewrite merge_sort_Permutation in Hp2.
    apply list_elem_of_fmap in Hp1 as (a & -> & Ha).
    apply list_elem_of_fmap in Hp2 as (b & -> & Hb).
    apply list_elem_of_filter in Ha as [Hac Ha].
    apply list_elem_of_filter in Hb as [Hbc Hb].
    rewrite -Hperm in Hb.
    rewrite /pr_le in H12 H21.
    have Hkeq : a.2.1 = b.2.1 by lia.
    have Hloc := Hkd a b Ha Hb ltac:(congruence) Hkeq.
    destruct a as [ac [aclk al]], b as [bc [bclk bl]]; simpl in *. by subst.
  - apply (StronglySorted_merge_sort pr_le).
  - apply (StronglySorted_merge_sort pr_le).
  - rewrite !merge_sort_Permutation. apply Permutation_map. by rewrite Hperm.
Qed.

Lemma kp_client_locs_other (client : w64) (kps : list (w64 * (Z * loc))) (kp : w64 * (Z * loc)) :
  kp.1 ≠ client -> kp_client_locs client (kps ++ [kp]) = kp_client_locs client kps.
Proof.
  move=> Hne. rewrite /kp_client_locs filter_app filter_cons_False // filter_nil app_nil_r //.
Qed.

Lemma kp_client_locs_absent (client : w64) (kps : list (w64 * (Z * loc))) :
  client ∉ kps.*1 -> kp_client_locs client kps = [].
Proof.
  move=> Hnin.
  have Hfilt : filter (λ kp : w64 * (Z * loc), kp.1 = client) kps = [].
  { move: Hnin. elim: kps => [| a l IH] Hnin; [reflexivity |].
    rewrite filter_cons. case_decide as Hc.
    - exfalso. apply Hnin. rewrite fmap_cons Hc. apply list_elem_of_here.
    - apply IH. move=> Hin. apply Hnin. rewrite fmap_cons. apply elem_of_cons. by right. }
  rewrite /kp_client_locs Hfilt //.
Qed.

Lemma kp_client_locs_snoc_max (client : w64) (kps : list (w64 * (Z * loc))) (kp : w64 * (Z * loc)) :
  kp_clkloc kps -> kp.1 = client ->
  (∀ a, a ∈ kps -> a.1 = client -> (a.2.1 < kp.2.1)%Z) ->
  kp_client_locs client (kps ++ [kp]) = kp_client_locs client kps ++ [kp.2.2].
Proof.
  move=> Hkd Hkc Hmax. rewrite /kp_client_locs.
  rewrite filter_app filter_cons_True // filter_nil fmap_app /=.
  set prs := (filter (λ kp0, kp0.1 = client) kps).*2.
  have Hprs : ∀ a, a ∈ prs -> ∃ b, b ∈ kps ∧ b.1 = client ∧ a = b.2.
  { move=> a Ha. apply list_elem_of_fmap in Ha as (b & -> & Hb).
    apply list_elem_of_filter in Hb as [Hbc Hb]. by exists b. }
  have Hmaxp : ∀ a, a ∈ prs -> (a.1 < kp.2.1)%Z.
  { move=> a Ha. destruct (Hprs a Ha) as (b & Hb & Hbc & ->). exact (Hmax b Hb Hbc). }
  have Hkdp : ∀ a b, a ∈ prs -> b ∈ prs -> a.1 = b.1 -> a = b.
  { move=> a b Ha Hb Hab.
    destruct (Hprs a Ha) as (a' & Ha' & Hac & ->).
    destruct (Hprs b Hb) as (b' & Hb' & Hbc & ->).
    have Hloc := Hkd a' b' Ha' Hb' ltac:(congruence) Hab.
    destruct a' as [ac [aclk al]], b' as [bc [bclk bl]]; simpl in *. by subst. }
  change [kp.2.2] with (snd <$> [kp.2]). rewrite -fmap_app. f_equal.
  apply (StronglySorted_unique_strong pr_le).
  - move=> p1 p2 Hp1 Hp2 H12 H21.
    rewrite merge_sort_Permutation in Hp1.
    rewrite /pr_le in H12 H21.
    have Hkeq : p1.1 = p2.1 by lia.
    apply elem_of_app in Hp1 as [Hp1 | Hp1]; apply elem_of_app in Hp2 as [Hp2 | Hp2].
    + rewrite merge_sort_Permutation in Hp2. exact (Hkdp p1 p2 Hp1 Hp2 Hkeq).
    + apply list_elem_of_singleton in Hp2 as ->. exfalso. have := Hmaxp p1 Hp1. lia.
    + apply list_elem_of_singleton in Hp1 as ->. rewrite merge_sort_Permutation in Hp2.
      exfalso. have := Hmaxp p2 Hp2. lia.
    + apply list_elem_of_singleton in Hp1 as ->. apply list_elem_of_singleton in Hp2 as ->. reflexivity.
  - apply (StronglySorted_merge_sort pr_le).
  - apply StronglySorted_app_2.
    + move=> a z Ha Hz. apply list_elem_of_singleton in Hz as ->.
      rewrite merge_sort_Permutation in Ha. rewrite /pr_le. have := Hmaxp a Ha. lia.
    + apply (StronglySorted_merge_sort pr_le).
    + repeat constructor.
  - rewrite merge_sort_Permutation. apply Permutation_app; [| reflexivity]. symmetry. apply merge_sort_Permutation.
Qed.

Lemma kp_client_locs_insert (client : w64) (kps : list (w64 * (Z * loc))) (kp : w64 * (Z * loc)) (i : nat) :
  kp_clkloc kps -> kp.1 = client ->
  (∀ a, a ∈ take i (merge_sort pr_le ((filter (λ kp0, kp0.1 = client) kps).*2)) -> (a.1 < kp.2.1)%Z) ->
  (∀ a, a ∈ drop i (merge_sort pr_le ((filter (λ kp0, kp0.1 = client) kps).*2)) -> (kp.2.1 < a.1)%Z) ->
  kp_client_locs client (kps ++ [kp])
  = take i (kp_client_locs client kps) ++ kp.2.2 :: drop i (kp_client_locs client kps).
Proof.
  move=> Hkd Hkc Hbef Haft. rewrite /kp_client_locs.
  rewrite filter_app filter_cons_True // filter_nil fmap_app /=.
  set prs := (filter (λ kp0, kp0.1 = client) kps).*2.
  set S := merge_sort pr_le prs.
  have Hprs : ∀ a, a ∈ prs -> ∃ b, b ∈ kps ∧ b.1 = client ∧ a = b.2.
  { move=> a Ha. apply list_elem_of_fmap in Ha as (b & -> & Hb).
    apply list_elem_of_filter in Hb as [Hbc Hb]. by exists b. }
  have Hkdp : ∀ a b, a ∈ prs -> b ∈ prs -> a.1 = b.1 -> a = b.
  { move=> a b Ha Hb Hab.
    destruct (Hprs a Ha) as (a' & Ha' & Hac & ->).
    destruct (Hprs b Hb) as (b' & Hb' & Hbc & ->).
    have Hloc := Hkd a' b' Ha' Hb' ltac:(congruence) Hab.
    destruct a' as [ac [aclk al]], b' as [bc [bclk bl]]; simpl in *. by subst. }
  have HSperm : S ≡ₚ prs := merge_sort_Permutation pr_le prs.
  have HinS_take : ∀ z, z ∈ take i S -> z ∈ S.
  { move=> z Hz. rewrite -(take_drop i S). apply elem_of_app. by left. }
  have HinS_drop : ∀ z, z ∈ drop i S -> z ∈ S.
  { move=> z Hz. rewrite -(take_drop i S). apply elem_of_app. by right. }
  have HSS : StronglySorted pr_le S by apply (StronglySorted_merge_sort pr_le).
  have HSSapp : StronglySorted pr_le (take i S ++ drop i S).
  { rewrite (take_drop i S). exact HSS. }
  rewrite -fmap_take -fmap_drop.
  change (kp.2.2 :: (snd <$> drop i S)) with (snd <$> (kp.2 :: drop i S)).
  rewrite -fmap_app. f_equal.
  apply (StronglySorted_unique_strong pr_le).
  - move=> p1 p2 Hp1 Hp2 H12 H21.
    rewrite /pr_le in H12 H21.
    have Hkeq : p1.1 = p2.1 by lia.
    rewrite merge_sort_Permutation in Hp1.
    have Hp2c : (p2 ∈ S) ∨ p2 = kp.2.
    { apply elem_of_app in Hp2 as [Hp2 | Hp2]; [left; exact (HinS_take p2 Hp2) |].
      apply elem_of_cons in Hp2 as [-> | Hp2]; [by right | left; exact (HinS_drop p2 Hp2)]. }
    apply elem_of_app in Hp1 as [Hp1 | Hp1]; last apply list_elem_of_singleton in Hp1 as ->.
    + destruct Hp2c as [Hp2S | ->].
      * apply Hkdp; [exact Hp1 | by rewrite -HSperm | exact Hkeq].
      * exfalso. rewrite -HSperm -(take_drop i S) in Hp1. apply elem_of_app in Hp1 as [Ht | Hd].
        -- have := Hbef p1 Ht. lia.
        -- have := Haft p1 Hd. lia.
    + destruct Hp2c as [Hp2S | ->]; [| reflexivity].
      exfalso. rewrite -(take_drop i S) in Hp2S. apply elem_of_app in Hp2S as [Ht | Hd].
      * have := Hbef p2 Ht. lia.
      * have := Haft p2 Hd. lia.
  - apply (StronglySorted_merge_sort pr_le).
  - apply StronglySorted_app_2.
    + move=> a c Ha Hc. apply elem_of_cons in Hc as [-> | Hc].
      * rewrite /pr_le. have := Hbef a Ha. lia.
      * rewrite /pr_le. have := Hbef a Ha. have := Haft c Hc. lia.
    + exact (StronglySorted_app_1_l _ _ _ HSSapp).
    + change (kp.2 :: drop i S) with ([kp.2] ++ drop i S).
      apply StronglySorted_app_2.
      * move=> a c Ha Hc. apply list_elem_of_singleton in Ha as ->. rewrite /pr_le. have := Haft c Hc. lia.
      * repeat constructor.
      * exact (StronglySorted_app_1_r _ _ _ HSSapp).
  - rewrite merge_sort_Permutation. rewrite -HSperm -{1}(take_drop i S).
    change (kp.2 :: drop i S) with ([kp.2] ++ drop i S).
    rewrite -app_assoc. apply Permutation_app; [reflexivity |]. apply Permutation_app_comm.
Qed.

(** The client's entries: a permutation of the pool's entries with that
    client tag, clock-sorted; their addresses are the index's slice
    ([client_locs_entries], under the key uniqueness); each sits at a slot of
    the pool ([pool_entries_slot] / [client_entries_lookup_slot]); the pool's
    entries carry the pool's runs ([pool_entries_snd]) and, under the
    address [NoDup], distinct entries of one client have disjoint clock
    ranges ([client_entries_disjoint]). *)
Lemma entry_kp_split (e : loc * ItemRun) : entry_kp e = (entry_client e, entry_pr e).
Proof. reflexivity. Qed.

(** The left half of a split keeps the run's head, so its keys are the
    split run's. *)
Lemma entry_kp_split_left (l : loc) (r : ItemRun) (o : nat) :
  (0 < o)%nat -> entry_kp (l, split_run_left r o) = entry_kp (l, r).
Proof.
  move=> Ho. destruct o as [|o']; [lia |]. destruct r as [items d].
  rewrite /entry_kp /entry_client /entry_pr /entry_clock /run_client /run_clock /run_head_item
          /split_run_left /=.
  destruct items; reflexivity.
Qed.

(** An entry's machine-word clock is its run's clock, under the pool's clock
    bound. *)
Lemma entry_clock_Z (l : loc) (r : ItemRun) :
  (Z.of_nat (run_clock r) < 2^64)%Z -> uint.Z (entry_clock (l, r)) = Z.of_nat (run_clock r).
Proof. move=> Hb. rewrite /entry_clock /=. word. Qed.

Lemma client_entries_mem (locs : gmap loc (list loc)) (p : pool) (client : w64) (e : loc * ItemRun) :
  e ∈ client_entries locs p client <-> (e ∈ pool_entries locs p ∧ entry_client e = client).
Proof. rewrite /client_entries (merge_sort_Permutation entry_le _) list_elem_of_filter. tauto. Qed.

Lemma client_entries_sorted (locs : gmap loc (list loc)) (p : pool) (client : w64) :
  StronglySorted entry_le (client_entries locs p client).
Proof. apply StronglySorted_merge_sort; apply _. Qed.

Lemma entry_pr_filter_kp (client : w64) (l : list (loc * ItemRun)) :
  entry_pr <$> filter (λ e, entry_client e = client) l
  = (filter (λ kp : w64 * (Z * loc), kp.1 = client) (entry_kp <$> l)).*2.
Proof.
  induction l as [|e l IH]; [reflexivity|].
  rewrite fmap_cons filter_cons filter_cons entry_kp_split /=.
  case_decide as Hc.
  - rewrite fmap_cons IH /=. reflexivity.
  - exact IH.
Qed.

Lemma SS_entry_pr_merge (l : list (loc * ItemRun)) :
  StronglySorted pr_le (entry_pr <$> merge_sort entry_le l).
Proof.
  apply (StronglySorted_fmap entry_pr entry_le pr_le).
  - move=> x y Hxy. rewrite /pr_le /entry_pr /entry_le in Hxy |- *. exact Hxy.
  - apply (StronglySorted_merge_sort entry_le).
Qed.

Lemma client_entries_prs (locs : gmap loc (list loc)) (p : pool) (client : w64) :
  kp_clkloc (entry_kp <$> pool_entries locs p) ->
  merge_sort pr_le ((filter (λ kp : w64 * (Z * loc), kp.1 = client) (entry_kp <$> pool_entries locs p)).*2)
  = entry_pr <$> client_entries locs p client.
Proof.
  move=> Hkd. rewrite /client_entries -entry_pr_filter_kp.
  apply (StronglySorted_unique_strong pr_le).
  - move=> p1 p2 Hp1 Hp2 H12 H21.
    rewrite (merge_sort_Permutation pr_le) in Hp1.
    rewrite (merge_sort_Permutation entry_le) in Hp2.
    apply list_elem_of_fmap in Hp1 as (x1 & -> & Hx1).
    apply list_elem_of_fmap in Hp2 as (x2 & -> & Hx2).
    apply list_elem_of_filter in Hx1 as [Hc1 Hx1]. apply list_elem_of_filter in Hx2 as [Hc2 Hx2].
    rewrite /pr_le in H12 H21.
    have Hkeq : (entry_pr x1).1 = (entry_pr x2).1 by lia.
    have Hcc : (entry_kp x1).1 = (entry_kp x2).1.
    { rewrite !entry_kp_split /=. congruence. }
    have Hloc := Hkd (entry_kp x1) (entry_kp x2) (list_elem_of_fmap_2 _ _ _ Hx1) (list_elem_of_fmap_2 _ _ _ Hx2) Hcc Hkeq.
    rewrite /entry_pr. f_equal; [exact Hkeq | exact Hloc].
  - apply (StronglySorted_merge_sort pr_le).
  - apply SS_entry_pr_merge.
  - rewrite (merge_sort_Permutation pr_le). apply Permutation_map. symmetry. apply merge_sort_Permutation.
Qed.

Lemma client_locs_entries (locs : gmap loc (list loc)) (p : pool) (client : w64) :
  kp_clkloc (entry_kp <$> pool_entries locs p) ->
  client_locs locs p client = (client_entries locs p client).*1.
Proof.
  move=> Hkd. rewrite /client_locs /kp_client_locs (client_entries_prs locs p client Hkd).
  rewrite -list_fmap_compose. apply list_fmap_ext. move=> i e _. reflexivity.
Qed.

Lemma pool_entries_slot (locs : gmap loc (list loc)) (p : pool) (l : loc) (r : ItemRun) :
  (l, r) ∈ pool_entries locs p <->
  ∃ parent ls tm k, locs !! parent = Some ls ∧ p !! parent = Some tm ∧ ls !! k = Some l ∧ tm_runs tm !! k = Some r.
Proof.
  rewrite /pool_entries list_elem_of_concat. split.
  - move=> [zl [Hin Hzl]].
    apply list_elem_of_fmap in Hzl as (kv & -> & Hkv).
    destruct kv as [parent tm]. apply elem_of_map_to_list in Hkv. simpl in Hin.
    destruct (locs !! parent) as [ls|] eqn:Hls; simpl in Hin; last by rewrite elem_of_nil in Hin.
    apply list_elem_of_lookup in Hin as [k Hk].
    apply lookup_zip_with_Some in Hk as (x & y & Heq & Hx & Hy).
    injection Heq as <- <-.
    by exists parent, ls, tm, k.
  - intros (parent & ls & tm & k & Hls & Hp & Hl & Hr).
    exists (zip ls (tm_runs tm)). split.
    + apply list_elem_of_lookup. exists k. apply lookup_zip_with_Some. by exists l, r.
    + apply list_elem_of_fmap. exists (parent, tm). split; [by rewrite /= Hls | by apply elem_of_map_to_list].
Qed.

Lemma pool_entries_snd (locs : gmap loc (list loc)) (p : pool) :
  dom locs = dom p ->
  (∀ parent ls tm, locs !! parent = Some ls -> p !! parent = Some tm -> length ls = length (tm_runs tm)) ->
  (pool_entries locs p).*2 = all_runs p.
Proof.
  move=> Hdom Hlens. rewrite /pool_entries /all_runs fmap_concat -!list_fmap_compose.
  f_equal. apply list_fmap_ext. move=> i [parent tm] Hi. simpl.
  have Hp : p !! parent = Some tm by (apply elem_of_map_to_list; exact (list_elem_of_lookup_2 _ _ _ Hi)).
  have His : is_Some (locs !! parent).
  { apply elem_of_dom. rewrite Hdom. apply elem_of_dom. by exists tm. }
  destruct His as [ls Hls]. rewrite Hls /=. apply snd_zip. rewrite (Hlens parent ls tm Hls Hp). lia.
Qed.

(** The entries' addresses are the address map's addresses, up to order:
    each type contributes its whole address list, since it has one address
    per run. So the map's [NoDup] is the index's. *)
Lemma pool_entries_locs_perm (locs : gmap loc (list loc)) (p : pool) :
  dom locs = dom p ->
  (∀ parent tm, p !! parent = Some tm ->
     ∃ ls, locs !! parent = Some ls ∧ length ls = length (tm_runs tm)) ->
  (pool_entries locs p).*1 ≡ₚ concat ((map_to_list locs).*2).
Proof.
  move=> Hdom Hlens.
  have H1 : (pool_entries locs p).*1
          = concat ((λ parent, default [] (locs !! parent)) <$> (map_to_list p).*1).
  { rewrite /pool_entries concat_fmap -!list_fmap_compose.
    f_equal. apply list_fmap_ext => i kv Hkv.
    have Hlk : p !! kv.1 = Some kv.2.
    { apply elem_of_map_to_list. destruct kv. exact (list_elem_of_lookup_2 _ _ _ Hkv). }
    destruct (Hlens kv.1 kv.2 Hlk) as (ls & Hls & Hlen).
    rewrite /= Hls /=. rewrite fst_zip //. lia. }
  have H2 : concat ((map_to_list locs).*2)
          = concat ((λ parent, default [] (locs !! parent)) <$> (map_to_list locs).*1).
  { f_equal. rewrite -!list_fmap_compose. apply list_fmap_ext => i kv Hkv.
    have Hlk : locs !! kv.1 = Some kv.2.
    { apply elem_of_map_to_list. destruct kv. exact (list_elem_of_lookup_2 _ _ _ Hkv). }
    rewrite /= Hlk //. }
  rewrite H1 H2. apply concat_perm. apply fmap_Permutation.
  exact (map_to_list_fst_perm p locs (eq_sym Hdom)).
Qed.

Lemma pool_entries_locs_NoDup (locs : gmap loc (list loc)) (p : pool) :
  dom locs = dom p ->
  (∀ parent tm, p !! parent = Some tm -> ∃ ls, locs !! parent = Some ls ∧ length ls = length (tm_runs tm)) ->
  NoDup (concat ((map_to_list locs).*2)) ->
  NoDup (pool_entries locs p).*1.
Proof.
  move=> Hdom Hlens Hnd. by rewrite (pool_entries_locs_perm locs p Hdom Hlens).
Qed.

(** A fresh empty type adds no entry to the item index. *)
Lemma pool_entries_insert_empty (locs : gmap loc (list loc)) (p : pool) (q : loc) :
  p !! q = None ->
  pool_entries (<[q := []]> locs) (<[q := MkTypeModel [] []]> p) ≡ₚ pool_entries locs p.
Proof.
  move=> Hq. rewrite /pool_entries.
  have Hm : (λ kv : loc * type_model, zip (default [] (<[q := []]> locs !! kv.1)) (tm_runs kv.2))
              <$> map_to_list (<[q := MkTypeModel [] []]> p)
          ≡ₚ (λ kv : loc * type_model, zip (default [] (<[q := []]> locs !! kv.1)) (tm_runs kv.2))
              <$> ((q, MkTypeModel [] []) :: map_to_list p).
  { apply Permutation_map. apply map_to_list_insert. exact Hq. }
  rewrite (concat_perm _ _ Hm) fmap_cons concat_cons /= zip_with_nil_r /=.
  apply Permutation_refl'. f_equal. apply list_fmap_ext.
  move=> i [q0 tm0] Hi. simpl.
  have Hq0 : p !! q0 = Some tm0
    by (apply elem_of_map_to_list; exact (list_elem_of_lookup_2 _ _ _ Hi)).
  have Hne : q0 ≠ q by (move=> Heq; rewrite Heq Hq in Hq0; done).
  rewrite lookup_insert_ne //.
Qed.

(** One integrate splice adds exactly the new entry to the pool's entries:
    the fresh node's address at the cursor of the address list, its run at
    the same cursor of the run list. *)
Lemma pool_entries_integrate (locs : gmap loc (list loc)) (p : pool) (parent : loc)
    (ls : list loc) (tm : type_model) (idx : nat) (item_l : loc) (r : ItemRun)
    (arr' : list (YjsItem A)) :
  locs !! parent = Some ls -> p !! parent = Some tm ->
  length ls = length (tm_runs tm) ->
  pool_entries (<[parent := integrate_locs ls idx item_l]> locs)
               (<[parent := MkTypeModel (take idx (tm_runs tm) ++ r :: drop idx (tm_runs tm)) arr']> p)
    ≡ₚ (item_l, r) :: pool_entries locs p.
Proof.
  move=> Hls Hp Hlen.
  set (F := λ (locs' : gmap loc (list loc)) (kv : loc * type_model),
              zip (default [] (locs' !! kv.1)) (tm_runs kv.2)).
  set (others := concat (F locs <$> map_to_list (delete parent p))).
  have Hpe : ∀ (locs' : gmap loc (list loc)) (tm' : type_model),
      (∀ q, q ≠ parent -> locs' !! q = locs !! q) ->
      pool_entries locs' (<[parent := tm']> p) ≡ₚ F locs' (parent, tm') ++ others.
  { move=> locs' tm' Hq. rewrite /pool_entries.
    have Hm : F locs' <$> map_to_list (<[parent := tm']> p)
            ≡ₚ F locs' <$> ((parent, tm') :: map_to_list (delete parent p)).
    { apply Permutation_map. exact (map_to_list_insert_existing p parent tm tm' Hp). }
    rewrite (concat_perm _ _ Hm) fmap_cons concat_cons. apply Permutation_app_head. rewrite /others.
    have -> : F locs' <$> map_to_list (delete parent p) = F locs <$> map_to_list (delete parent p);
      last reflexivity.
    apply list_fmap_ext. move=> i [q tmq] Hi. rewrite /F /=.
    have Hq' : delete parent p !! q = Some tmq
      by (apply elem_of_map_to_list; exact (list_elem_of_lookup_2 _ _ _ Hi)).
    apply lookup_delete_Some in Hq' as [Hne _]. rewrite (Hq q (λ H, Hne (eq_sym H))) //. }
  set (Ap := zip (take idx ls) (take idx (tm_runs tm))).
  set (Bp := zip (drop idx ls) (drop idx (tm_runs tm))).
  have HlenA : length (take idx ls) = length (take idx (tm_runs tm)) by rewrite !length_take Hlen.
  have Hother : ∀ q, q ≠ parent -> <[parent := integrate_locs ls idx item_l]> locs !! q = locs !! q.
  { move=> q Hne. rewrite lookup_insert_ne //. }
  have Hold : pool_entries locs p ≡ₚ Ap ++ Bp ++ others.
  { rewrite -{1}(insert_id p parent tm Hp) (Hpe locs tm (λ q _, eq_refl)) /F /= Hls /=.
    rewrite -{1}(take_drop idx ls) -{1}(take_drop idx (tm_runs tm)).
    rewrite zip_with_app; last exact HlenA.
    rewrite -/Ap -/Bp -app_assoc //. }
  have Hnew : pool_entries (<[parent := integrate_locs ls idx item_l]> locs)
                (<[parent := MkTypeModel (take idx (tm_runs tm) ++ r :: drop idx (tm_runs tm)) arr']> p)
              ≡ₚ Ap ++ (item_l, r) :: Bp ++ others.
  { rewrite (Hpe _ _ Hother) /F /= lookup_insert_eq /= /integrate_locs.
    rewrite zip_with_app; last exact HlenA.
    simpl. rewrite -/Ap -/Bp -app_assoc //. }
  rewrite Hnew Hold. symmetry. apply Permutation_middle.
Qed.

(** The address map stays well formed across an integrate splice landing at
    a fresh address. *)
Lemma locs_wf_integrate (locs : gmap loc (list loc)) (p : pool) (parent : loc)
    (ls : list loc) (tm : type_model) (idx : nat) (item_l : loc) (r : ItemRun)
    (arr' : list (YjsItem A)) :
  locs !! parent = Some ls -> p !! parent = Some tm ->
  item_l ∉ concat ((map_to_list locs).*2) ->
  locs_wf locs p ->
  locs_wf (<[parent := integrate_locs ls idx item_l]> locs)
          (<[parent := MkTypeModel (take idx (tm_runs tm) ++ r :: drop idx (tm_runs tm)) arr']> p).
Proof.
  move=> Hls Hp Hfresh [Hdom [Hnd Hlens]].
  have Hperm0 : concat ((map_to_list locs).*2) ≡ₚ ls ++ concat ((map_to_list (delete parent locs)).*2).
  { rewrite -{1}(insert_id locs parent ls Hls).
    rewrite (concat_perm _ _ (Permutation_map snd (map_to_list_insert_existing locs parent ls ls Hls))) //. }
  have Hperm : concat ((map_to_list (<[parent := integrate_locs ls idx item_l]> locs)).*2)
             ≡ₚ integrate_locs ls idx item_l ++ concat ((map_to_list (delete parent locs)).*2).
  { rewrite (concat_perm _ _ (Permutation_map snd (map_to_list_insert_existing locs parent ls _ Hls))) //. }
  have Hil : integrate_locs ls idx item_l ≡ₚ item_l :: ls.
  { rewrite /integrate_locs -{3}(take_drop idx ls). symmetry. apply Permutation_middle. }
  split_and!.
  - rewrite !dom_insert_L Hdom //.
  - rewrite Hperm Hil. rewrite Hperm0 in Hnd Hfresh.
    apply NoDup_cons. split; [exact Hfresh | exact Hnd].
  - move=> q lsq tmq. destruct (decide (q = parent)) as [-> | Hne].
    + rewrite !lookup_insert_eq. move=> [<-] [<-]. simpl.
      have Hlsl := Hlens parent ls tm Hls Hp.
      rewrite /integrate_locs !length_app /= !length_take !length_drop. lia.
    + rewrite !lookup_insert_ne //. exact (Hlens q lsq tmq).
Qed.

(** A tombstoning leaves the item index alone: a flip changes no entry's
    (client, clock, address) key. *)
Lemma pool_entries_flip_kp (locs : gmap loc (list loc)) (p : pool) (parent : loc)
    (ls : list loc) (tm : type_model) (k : nat) (lc : loc) (r : ItemRun) :
  locs !! parent = Some ls -> p !! parent = Some tm ->
  ls !! k = Some lc -> tm_runs tm !! k = Some r ->
  entry_kp <$> pool_entries locs (<[parent := MkTypeModel (<[k := flip_run r]> (tm_runs tm)) (tm_arr tm)]> p)
  ≡ₚ entry_kp <$> pool_entries locs p.
Proof.
  move=> Hls Hp Hlk Hrk.
  set (F := λ (kv : loc * type_model), zip (default [] (locs !! kv.1)) (tm_runs kv.2)).
  set (others := concat (F <$> map_to_list (delete parent p))).
  have Hpe : ∀ (tm' : type_model),
      pool_entries locs (<[parent := tm']> p) ≡ₚ F (parent, tm') ++ others.
  { move=> tm'. rewrite /pool_entries.
    have Hm : F <$> map_to_list (<[parent := tm']> p)
            ≡ₚ F <$> ((parent, tm') :: map_to_list (delete parent p)).
    { apply Permutation_map. exact (map_to_list_insert_existing p parent tm tm' Hp). }
    rewrite (concat_perm _ _ Hm) fmap_cons concat_cons //. }
  have Hkp : entry_kp (lc, flip_run r) = entry_kp (lc, r).
  { rewrite /entry_kp /entry_client /entry_pr /entry_clock /run_client /run_clock /run_head_item /flip_run //. }
  have Hzip : zip ls (<[k := flip_run r]> (tm_runs tm)) = <[k := (lc, flip_run r)]> (zip ls (tm_runs tm)).
  { have H := insert_zip_with pair ls (tm_runs tm) k lc (flip_run r).
    rewrite (list_insert_id ls k lc Hlk) in H. rewrite -H //. }
  rewrite (Hpe _) -(insert_id p parent tm Hp) (Hpe tm) /F /= Hls /= Hzip !fmap_app.
  rewrite list_fmap_insert Hkp list_insert_id; first done.
  rewrite list_lookup_fmap lookup_zip_with Hlk Hrk //.
Qed.

(** What a delete step ([pool_after_delete]) transports: the per-type
    item-set map is unchanged, a pointwise fact about the documents
    survives, and so does the registry's model reading. *)
Lemma pool_after_delete_seq_map (p p' : pool) :
  pool_after_delete p p' ->
  ((λ tm, (list_to_set (tm_arr tm) : gset (YjsItem A))) <$> p')
  = ((λ tm, (list_to_set (tm_arr tm) : gset (YjsItem A))) <$> p).
Proof.
  intros (Harr & Hdom & _ & _ & _).
  apply map_eq => q. rewrite !lookup_fmap.
  destruct (p' !! q) as [tm'|] eqn:Htm'.
  - destruct (Harr q tm' Htm') as (tm & Htm & Heq). rewrite Htm' Htm /= Heq //.
  - destruct (p !! q) as [tm|] eqn:Htm; last (rewrite Htm' Htm //).
    exfalso. destruct (Hdom q (mk_is_Some _ _ Htm)) as [tm0 Htm0]. rewrite Htm0 in Htm'. done.
Qed.

Lemma pool_after_delete_arr_pointwise (p p' : pool) (Q : YjsItem A -> Prop) :
  pool_after_delete p p' ->
  (∀ parent tm x, p !! parent = Some tm -> x ∈ tm_arr tm -> Q x) ->
  (∀ parent tm x, p' !! parent = Some tm -> x ∈ tm_arr tm -> Q x).
Proof.
  intros (Harr & _) H parent tm' x Htm' Hx.
  destruct (Harr parent tm' Htm') as (tm & Htm & Heq). rewrite Heq in Hx. exact (H parent tm x Htm Hx).
Qed.

Lemma pool_registry_models_after_delete (m : DocModel) (bind : gmap P loc) (p p' : pool) :
  pool_after_delete p p' -> pool_registry_models m bind p -> pool_registry_models m bind p'.
Proof.
  intros (Harr & _) [Hmtypes Hmdom]. split; [| exact Hmdom].
  move=> nm q tm' Hb Htm'. destruct (Harr q tm' Htm') as (tm & Htm & Heq).
  rewrite Heq. exact (Hmtypes nm q tm Hb Htm).
Qed.

(** What a step that rebuilds ONE type's runs, keeping its document,
    transports: the registry's model reading, a pointwise fact about the
    documents, and the per-type item-set map (the text layer's split and
    tombstone loops step the pool this way). *)
Lemma pool_registry_models_ext (m : DocModel) (bind : gmap P loc) (p p' : pool)
    (parent : loc) (tm tm' : type_model) :
  (∀ q, q ≠ parent -> p' !! q = p !! q) ->
  p !! parent = Some tm -> p' !! parent = Some tm' -> tm_arr tm' = tm_arr tm ->
  pool_registry_models m bind p -> pool_registry_models m bind p'.
Proof.
  move=> Hext Hp Hp' Harr [Hmtypes Hmdom]. split; [| exact Hmdom].
  move=> nm q tmq Hb Hq.
  destruct (decide (q = parent)) as [-> | Hne].
  - rewrite Hp' in Hq. injection Hq as <-. rewrite Harr. exact (Hmtypes nm parent tm Hb Hp).
  - rewrite (Hext q Hne) in Hq. exact (Hmtypes nm q tmq Hb Hq).
Qed.

Lemma pool_arr_pointwise_ext (p p' : pool) (parent : loc) (tm tm' : type_model)
    (Q : YjsItem A -> Prop) :
  (∀ q, q ≠ parent -> p' !! q = p !! q) ->
  p !! parent = Some tm -> p' !! parent = Some tm' -> tm_arr tm' = tm_arr tm ->
  (∀ q tmq x, p !! q = Some tmq -> x ∈ tm_arr tmq -> Q x) ->
  (∀ q tmq x, p' !! q = Some tmq -> x ∈ tm_arr tmq -> Q x).
Proof.
  move=> Hext Hp Hp' Harr H q tmq x Hq Hx.
  destruct (decide (q = parent)) as [-> | Hne].
  - rewrite Hp' in Hq. injection Hq as <-. rewrite Harr in Hx. exact (H parent tm x Hp Hx).
  - rewrite (Hext q Hne) in Hq. exact (H q tmq x Hq Hx).
Qed.

Lemma pool_seq_map_ext (p p' : pool) (parent : loc) (tm tm' : type_model) :
  (∀ q, q ≠ parent -> p' !! q = p !! q) ->
  p !! parent = Some tm -> p' !! parent = Some tm' -> tm_arr tm' = tm_arr tm ->
  ((λ tmq, (list_to_set (tm_arr tmq) : gset (YjsItem A))) <$> p')
  = ((λ tmq, (list_to_set (tm_arr tmq) : gset (YjsItem A))) <$> p).
Proof.
  move=> Hext Hp Hp' Harr. apply map_eq => q. rewrite !lookup_fmap.
  destruct (decide (q = parent)) as [-> | Hne].
  - rewrite Hp Hp' /= Harr //.
  - rewrite (Hext q Hne) //.
Qed.

(** The same when the one type's document DID change: the item-set map is
    the old one with that type's entry replaced (the text insert's step). *)
Lemma pool_seq_map_insert_at (p p' : pool) (parent : loc) (tm tm' : type_model) :
  (∀ q, q ≠ parent -> p' !! q = p !! q) ->
  p !! parent = Some tm -> p' !! parent = Some tm' ->
  ((λ tmq, (list_to_set (tm_arr tmq) : gset (YjsItem A))) <$> p')
  = <[parent := (list_to_set (tm_arr tm') : gset (YjsItem A))]>
      ((λ tmq, (list_to_set (tm_arr tmq) : gset (YjsItem A))) <$> p).
Proof.
  move=> Hext Hp Hp'. apply map_eq => q. rewrite lookup_fmap.
  destruct (decide (q = parent)) as [-> | Hne].
  - rewrite Hp' lookup_insert_eq //.
  - rewrite lookup_insert_ne // lookup_fmap (Hext q Hne) //.
Qed.

(** An id no type's document holds is absent from the model: the pool
    reading of [store/heap]'s [docm_has_registry_false], for a caller that
    knows its fresh id beats every item of the pool (typically by the
    store's clock counter). *)
Lemma pool_docm_has_registry_false (bind : gmap P loc) (p : pool)
    (m : DocModel) (i : YjsId) :
  (∀ name q tm, bind !! name = Some q -> p !! q = Some tm ->
     doc_model_get m (RootId name) = tm_arr tm) ->
  (∀ t, doc_model_get m t ≠ [] ->
     ∃ name q, t = RootId name ∧ bind !! name = Some q) ->
  (∀ name q, bind !! name = Some q -> is_Some (p !! q)) ->
  (∀ q tm x, p !! q = Some tm -> x ∈ tm_arr tm -> item_id x ≠ i) ->
  doc_model_has m i = false.
Proof.
  move=> Hmtypes Hmdom Hbindtypes Hbeats.
  destruct (doc_model_has m i) eqn:Hhas; last done.
  exfalso. apply docm_has_spec in Hhas as (t & x & Hx & Hid).
  have Hne : doc_model_get m t ≠ [].
  { move=> Hnil. rewrite Hnil in Hx. by rewrite elem_of_nil in Hx. }
  destruct (Hmdom t Hne) as (nm & q & -> & Hb).
  destruct (Hbindtypes nm q Hb) as [tm Htm].
  rewrite (Hmtypes nm q tm Hb Htm) in Hx.
  exact (Hbeats q tm x Htm Hx Hid).
Qed.

Lemma client_entries_NoDup_locs (locs : gmap loc (list loc)) (p : pool) (client : w64) :
  NoDup (pool_entries locs p).*1 -> NoDup (client_entries locs p client).*1.
Proof.
  move=> Hnd. rewrite /client_entries.
  have Hperm : (merge_sort entry_le (filter (λ e, entry_client e = client) (pool_entries locs p))).*1
             ≡ₚ (filter (λ e, entry_client e = client) (pool_entries locs p)).*1.
  { apply Permutation_map. apply merge_sort_Permutation. }
  rewrite Hperm. clear Hperm.
  induction (pool_entries locs p) as [|e l IH]; first done.
  rewrite fmap_cons NoDup_cons in Hnd. destruct Hnd as [Hnotin Hnd].
  rewrite filter_cons. case_decide as Hc.
  - rewrite fmap_cons NoDup_cons. split; [| exact (IH Hnd)].
    move=> Hin. apply Hnotin. apply list_elem_of_fmap in Hin as (e' & Heq & He').
    apply list_elem_of_fmap. exists e'. split; [exact Heq |].
    exact (proj2 (proj1 (list_elem_of_filter _ _ _) He')).
  - exact (IH Hnd).
Qed.

Lemma client_entries_lookup_slot (locs : gmap loc (list loc)) (p : pool) (client : w64)
    (i : nat) (l : loc) (r : ItemRun) :
  client_entries locs p client !! i = Some (l, r) ->
  entry_client (l, r) = client ∧
  ∃ parent ls tm k, locs !! parent = Some ls ∧ p !! parent = Some tm ∧ ls !! k = Some l ∧ tm_runs tm !! k = Some r.
Proof.
  move=> Hi. have Hmem := list_elem_of_lookup_2 _ _ _ Hi.
  apply client_entries_mem in Hmem as [Hpe Hc]. split; [exact Hc | by apply pool_entries_slot].
Qed.

Lemma sorted_client_entries_disjoint (locs : gmap loc (list loc)) (p : pool) (client : w64)
    (E : list (loc * ItemRun)) :
  dom locs = dom p ->
  (∀ parent tm, p !! parent = Some tm -> ∃ ls, locs !! parent = Some ls ∧ length ls = length (tm_runs tm)) ->
  NoDup (pool_entries locs p).*1 ->
  (∀ r, r ∈ all_runs p -> (Z.of_nat (run_client r) < 2^64)%Z) ->
  runs_disjoint (all_runs p) ->
  sorted_client_entries locs p client E ->
  ∀ (i j : nat) (l1 l2 : loc) (r1 r2 : ItemRun),
    E !! i = Some (l1, r1) -> E !! j = Some (l2, r2) -> i ≠ j ->
    (run_clock r1 + length (run_items r1) <= run_clock r2)%nat ∨
    (run_clock r2 + length (run_items r2) <= run_clock r1)%nat.
Proof.
  move=> Hdom Hlens Hnd Hclb Hdisj [_ [Hndc Hmem]] i j l1 l2 r1 r2 Hi Hj Hij.
  have Hlens' : ∀ parent ls tm, locs !! parent = Some ls -> p !! parent = Some tm ->
      length ls = length (tm_runs tm).
  { move=> parent ls tm Hls Hp. destruct (Hlens parent tm Hp) as (ls' & Hls' & Hlen).
    rewrite Hls in Hls'. injection Hls' as <-. exact Hlen. }
  have Hsnd := pool_entries_snd locs p Hdom Hlens'.
  have Hl12 : l1 ≠ l2.
  { move=> Heq. apply Hij. apply (NoDup_lookup _ i j l1 Hndc);
      rewrite list_lookup_fmap; [rewrite Hi // | rewrite Hj /= Heq //]. }
  have [Hm1 Hc1] := Hmem _ (list_elem_of_lookup_2 _ _ _ Hi).
  have [Hm2 Hc2] := Hmem _ (list_elem_of_lookup_2 _ _ _ Hj).
  apply list_elem_of_lookup in Hm1 as [n1 Hn1]. apply list_elem_of_lookup in Hm2 as [n2 Hn2].
  have Hn12 : n1 ≠ n2.
  { move=> Heq. subst n2. rewrite Hn1 in Hn2. injection Hn2 as Heq _. exact (Hl12 Heq). }
  have Hr1 : all_runs p !! n1 = Some r1 by rewrite -Hsnd list_lookup_fmap Hn1 //.
  have Hr2 : all_runs p !! n2 = Some r2 by rewrite -Hsnd list_lookup_fmap Hn2 //.
  have Hcl : run_client r1 = run_client r2.
  { have Hb1 := Hclb r1 (list_elem_of_lookup_2 _ _ _ Hr1).
    have Hb2 := Hclb r2 (list_elem_of_lookup_2 _ _ _ Hr2).
    rewrite /entry_client /= in Hc1 Hc2.
    have Hz : uint.Z (W64 (run_client r1)) = uint.Z (W64 (run_client r2)) by rewrite Hc1 Hc2.
    apply Nat2Z.inj. word. }
  exact (Hdisj n1 n2 r1 r2 Hr1 Hr2 Hn12 Hcl).
Qed.

(** The index's own entries are such a list. *)
Lemma client_entries_sorted_client (locs : gmap loc (list loc)) (p : pool) (client : w64) :
  NoDup (pool_entries locs p).*1 ->
  sorted_client_entries locs p client (client_entries locs p client).
Proof.
  move=> Hnd. split_and!; [exact (client_entries_sorted locs p client) | exact (client_entries_NoDup_locs locs p client Hnd) |].
  move=> e He. by apply client_entries_mem.
Qed.

End store_value_cells.
