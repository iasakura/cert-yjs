(** The [store] base: per-store ghost names, the item-set / registry RAs and
    their lemmas, the per-client item map [own_item_map], the store predicates
    ([store_inv_ro] / [store_inv_excl] / [store_inv], the cohesive [own_store],
    the persistent [is_Store] / [is_type_lb] / [is_root] / [is_root_lb]), the
    RWMutex lock layer (write and read acquire/release wrappers), and
    [store_inv_init].

    The method proofs continue in [yjs_store_integrate] (id lookup, conflict
    scan, [Store.Integrate]) and [yjs_store_update] ([GetNode] /
    [getOrCreateYType] / [repair] / [store.applyUpdate] and the certificate
    specs), each reopening the same [Section] boilerplate; the split keeps the
    heavy loop proofs in their own [.vo]s (build-time isolation). Downstream
    files Require the [yjs_store] facade, which Require-Exports all three. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import yjs_core.
From New.proof Require Import yjs_common yjs_id yjs_item yjs_ytype.
From New.proof Require Import yjs_history.             (* ghost op history (issue #42) *)
From New.proof.sync_proof Require Import base mutex rwmutex rwmutex_guard.
                                                      (* store lock: rwmutex.is_RWMutex + LP Lock/Unlock
                                                         (y-octo Arc<RwLock<DocStore>>); the
                                                         guard's rfrac + tok_set reader accounting *)
From New.proof Require Import tok_set.                 (* own_tok_auth / own_toks *)
From iris.algebra Require Import auth gmap gset.       (* grow-only item-set RA *)
From iris.algebra.lib Require Import dfrac_agree.      (* reader/lock agreement on the types map *)
From iris.bi.lib Require Import fractional.            (* Fractional (read-share of store_inv) *)
From stdpp Require Import sorting.                     (* merge_sort for client_run *)

(* iris.algebra / stdpp.sorting push [nat_scope], retuning the default [<] / [≤].
   The verified WP proofs write [Z] comparisons (e.g. [sint.Z i < …]) unannotated
   and annotate [nat] ones with [%nat], so restore [Z_scope] as the default. *)
Local Open Scope Z_scope.

Section store.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.

(* The ghost op-history types ([yjs_history] / [yjs_network_model]) at the
   document content type; type names are Go strings (issue #49). *)
Notation P := go_string.
Local Notation TId := (TypeId P).
Local Notation Op := (TId * @YjsOperation A)%type.
Local Notation Ev := (@Event Op).
Local Notation DocM := (gmap TId (list (YjsItem A))).

(* ----- ghost lemmas for the [auth (gmap K (gset V))] item-set RA --------- *)

(** A fragment [◯ {[k := S]}] combined with the authority [● m] both WITNESSES
    the key ([m !! k = Some S']) AND bounds it ([S ⊆ S']). This is what makes
    [is_type_lb] prove the type is registered and give a lower bound. *)
Lemma auth_gmap_gset_lookup {K V : Type} `{Countable K} `{Countable V}
    `{!inG Σ (authR (gmapUR K (gsetUR V)))} (γ : gname) (m : gmap K (gset V)) (k : K) (S : gset V) :
  own γ (● m) -∗ own γ (◯ {[k := S]}) -∗ ⌜∃ S', m !! k = Some S' ∧ S ⊆ S'⌝.
Proof.
  iIntros "Ha Hf".
  iDestruct (own_valid_2 with "Ha Hf") as %Hv.
  iPureIntro.
  apply auth_both_valid_discrete in Hv as [Hincl _].
  apply singleton_included_l in Hincl as [S' [Hlk Hsub]].
  exists S'.
  apply leibniz_equiv in Hlk.
  rewrite Some_included_total in Hsub.
  rewrite gset_included in Hsub.
  split; assumption.
Qed.

(** Fractional variant of [auth_gmap_gset_lookup]: a reader holding a [dq]-share
    of the authority ([●{dq} m], from [store_inv_ro]) can still learn membership
    and the lower bound. Used by the concurrent read API (Text.Len). *)
Lemma auth_gmap_gset_lookup_dq {K V : Type} `{Countable K} `{Countable V}
    `{!inG Σ (authR (gmapUR K (gsetUR V)))} (γ : gname) (dq : dfrac) (m : gmap K (gset V)) (k : K) (S : gset V) :
  own γ (●{dq} m) -∗ own γ (◯ {[k := S]}) -∗ ⌜∃ S', m !! k = Some S' ∧ S ⊆ S'⌝.
Proof.
  iIntros "Ha Hf".
  iDestruct (own_valid_2 with "Ha Hf") as %Hv.
  iPureIntro.
  apply auth_both_dfrac_valid_discrete in Hv as [_ [Hincl _]].
  apply singleton_included_l in Hincl as [S' [Hlk Hsub]].
  exists S'.
  apply leibniz_equiv in Hlk.
  rewrite Some_included_total in Hsub.
  rewrite gset_included in Hsub.
  split; assumption.
Qed.

(** Grow the set at [k] (from [Sold] to [Snew ⊇ Sold]) in the authority and mint
    the matching fragment [◯ {[k := Snew]}] (= the new [is_type_lb]). *)
Lemma auth_gmap_gset_grow {K V : Type} `{Countable K} `{Countable V}
    `{!inG Σ (authR (gmapUR K (gsetUR V)))} (γ : gname) (m : gmap K (gset V)) (k : K) (Sold Snew : gset V) :
  m !! k = Some Sold -> Sold ⊆ Snew ->
  own γ (● m) ==∗ own γ (● (<[k:=Snew]> m)) ∗ own γ (◯ {[k := Snew]}).
Proof.
  iIntros (Hk Hsub) "Ha".
  iMod (own_update _ _ (● (<[k:=Snew]> m) ⋅ ◯ {[k := Snew]}) with "Ha") as "H".
  { apply auth_update_alloc.
    apply local_update_unital_discrete. intros z Hvm Hz.
    rewrite left_id in Hz. rewrite -Hz. split.
    - by apply insert_valid.
    - intros i. rewrite lookup_op.
      destruct (decide (i = k)) as [->|Hne].
      + rewrite lookup_insert lookup_singleton Hk.
        destruct (decide (k = k)); last done.
        rewrite -Some_op. f_equiv. rewrite gset_op. set_solver.
      + rewrite lookup_insert_ne // lookup_singleton_ne // left_id //. }
  iModIntro. iDestruct "H" as "[$ $]".
Qed.

(** Batch variant of [auth_gmap_gset_grow]: grow EVERY key's set at once
    (same domain, pointwise [⊆]) and mint a persistent whole-map snapshot
    fragment, out of which each key's [◯ {[k := S]}] projects
    ([auth_gmap_gset_frag_lookup]). Used by [applyUpdate], which grows many
    types in one batch. *)
Lemma auth_gmap_gset_grow_snap {K V : Type} `{Countable K} `{Countable V}
    `{!inG Σ (authR (gmapUR K (gsetUR V)))} (γ : gname) (m m' : gmap K (gset V)) :
  dom m' = dom m ->
  (∀ k S S', m !! k = Some S -> m' !! k = Some S' -> S ⊆ S') ->
  own γ (● m) ==∗ own γ (● m') ∗ own γ (◯ m').
Proof.
  iIntros (Hdom Hsub) "Ha".
  iMod (own_update _ _ (● m' ⋅ ◯ m') with "Ha") as "H".
  { apply auth_update_alloc.
    apply local_update_unital_discrete. intros z Hvm Hz.
    rewrite left_id in Hz. rewrite -Hz. split.
    - intros k. destruct (m' !! k) eqn:Hk; rewrite Hk //.
    - intros k. rewrite lookup_op.
      destruct (m !! k) as [S|] eqn:Hmk; destruct (m' !! k) as [S'|] eqn:Hm'k.
      + rewrite Hmk Hm'k -Some_op. f_equiv. rewrite gset_op.
        pose proof (Hsub k S S' Hmk Hm'k). set_solver.
      + exfalso. apply (elem_of_dom_2 (D := gset K)) in Hmk.
        rewrite -Hdom in Hmk. apply elem_of_dom in Hmk.
        rewrite Hm'k in Hmk. exact (is_Some_None Hmk).
      + rewrite Hmk Hm'k right_id //.
      + rewrite Hmk Hm'k //. }
  iModIntro. iDestruct "H" as "[$ $]".
Qed.

(** Project one key's fragment (an [is_type_lb] to be) out of a whole-map
    snapshot fragment. *)
Lemma auth_gmap_gset_frag_lookup {K V : Type} `{Countable K} `{Countable V}
    `{!inG Σ (authR (gmapUR K (gsetUR V)))} (γ : gname) (m : gmap K (gset V)) (k : K) (S : gset V) :
  m !! k = Some S ->
  own γ (◯ m) ⊢ own γ (◯ {[k := S]}).
Proof.
  intros Hk. apply own_mono, auth_frag_mono.
  apply/singleton_included_l. exists S.
  split; [by rewrite Hk | apply/Some_included; by left].
Qed.

(** Store lock = a [sync.Mutex]. The per-type item SET lives in a grow-only ghost
    (below), keyed by the type's [parent] loc. *)
Context {sync_pkg : sync.Assumptions}.

(** Item-SET RA: [auth (gmap loc (gset (YjsItem A)))] — the AUTH wraps the whole
    map (NOT [gmap (auth gset)], where a per-key frag would be valid even for an
    absent key and so would NOT witness registration). The authority [● m] (per
    type-loc item set) sits in [store_inv]; a persistent fragment
    [◯ {[parent := S]}] held by [is_Text] gives, when combined with [● m],
    gmap-inclusion [{[parent := S]} ≼ m] = [∃ S', m !! parent = Some S' ∧ S ⊆ S']
    — i.e. it BOTH witnesses [parent ∈ dom m] (= the type is registered) AND
    bounds [S ⊆ S'] (the lower bound). Insert only adds items (delete just flips a
    flag), so each item set grows monotonically under [⊆]; a recorded lower bound
    stays valid forever.

    We track full ITEMS, not just ids: a membership bound [x ∈ S ⊆ ty_arr ts]
    then pins [x] to a *genuine* document item (same structure, not merely the
    same id), which is what lets [Text.Insert] expose the post as a real
    [sublist L L'] rather than only an id-set inclusion. [gset (YjsItem A)] needs
    [Countable (YjsItem A)] (derived in [yjs_common] via [gen_tree]). Order is not
    tracked in the ghost (recoverable from origins / from [YjsArrInvariant]). *)
Notation seqUR := (authR (gmapUR loc (gsetUR (YjsItem A)))).
Context {seq_inG : inG Σ seqUR}.

(* ----- one registered type's state -------------------------------------- *)

(** What [store_inv] tracks per registered YType (keyed by its [parent] loc): the
    DLL cells and the model item list. *)
Record type_state := MkTypeState {
  ty_cells : list item_cell;
  ty_arr   : list (YjsItem A);
}.

(* reader/lock agreement on the [types] map (concurrent read API); declared here,
   after [type_state], since it mentions it. *)
Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO (gmap loc type_state)))}.

(** All cells across all types (the document-global item pool). *)
Definition all_cells (types : gmap loc type_state) : list item_cell :=
  concat (ty_cells <$> (map_to_list types).*2).

(* ----- the store's item set: map[Client][]*item ------------------------- *)

(** Client / clock a cell's id carries — read off the cell's model item id (a
    [YjsId], whose [nat] fields round-trip through [W64] from the original heap
    id), so [own_item_map] can speak about clocks while owning only the map, not
    the item cells. *)
Definition cell_client (c : item_cell) : w64 := W64 (clientId (item_id (run_head c))).
Definition cell_clock  (c : item_cell) : w64 := W64 (clock (item_id (run_head c))).

Definition cell_le (a b : item_cell) : Prop := (uint.Z (cell_clock a) ≤ uint.Z (cell_clock b))%Z.
#[local] Instance cell_le_dec : RelDecision cell_le.
Proof. rewrite /cell_le. solve_decision. Defined.
#[local] Instance cell_le_trans : Transitive cell_le.
Proof. rewrite /cell_le. move=> x y z. lia. Qed.
#[local] Instance cell_le_total : Total cell_le.
Proof. rewrite /cell_le. move=> x y. lia. Qed.

(** [client_run types client]: [client]'s items across every type, CLOCK-sorted
    — exactly the Go run list [store.items[client]] (AddNode appends in
    integration = clock order). Defining it by [merge_sort] makes sortedness
    DEFINITIONAL: [own_item_map] needs no existential / permutation clause, and
    (clocks being unique per client) the result is the unique clock ordering.
    Preserved per insert by [maximalId] (a fresh max-clock item lands at the
    sorted tail). *)
Definition client_run (types : gmap loc type_state) (client : w64) : list item_cell :=
  merge_sort cell_le (filter (λ c, cell_client c = client) (all_cells types)).

(** [own_item_map]'s backing slice is [ic_loc <$> ...] of a [merge_sort cell_le]
    run, so its content depends only on each cell's (clock, loc) pair. These two
    lemmas express that the loc-sequence of a clock-sorted run is preserved (a)
    under any reshuffle with the same (clock, loc) multiset and (b) when a
    strictly-clock-maximal cell is appended at the tail. *)
Definition cell_pr (c : item_cell) : Z * loc := (uint.Z (cell_clock c), ic_loc c).

(* ===== the split surgery on abstract cells (issue #28 M2) ================
   Splitting a run node is pure cell surgery: the left half keeps the node
   location and the first [o] model items, the right half is a fresh node
   carrying the rest, and BOTH halves inherit the deleted bit and parent (the
   yjs splitItem semantics; y-octo drops the right half's flags, a reported
   divergence). The flatten and the visible count are unchanged, which is why
   every public predicate is invariant under splits. *)

Definition split_cell_left (c : item_cell) (o : nat) : item_cell :=
  MkItemCell (ic_loc c) (take o (ic_run c)) (ic_deleted c) (ic_parent c).
Definition split_cell_right (c : item_cell) (o : nat) (r_loc : loc) : item_cell :=
  MkItemCell r_loc (drop o (ic_run c)) (ic_deleted c) (ic_parent c).

Definition split_cells (cells : list item_cell) (k o : nat) (r_loc : loc) : list item_cell :=
  match cells !! k with
  | Some c => take k cells ++ [split_cell_left c o; split_cell_right c o r_loc] ++ drop (S k) cells
  | None => cells
  end.

(** The split is invisible to the per-char document: the flatten is unchanged. *)
Lemma split_cells_flatten (cells : list item_cell) (k o : nat) (r_loc : loc) (c : item_cell) :
  cells !! k = Some c ->
  run_flatten (split_cells cells k o r_loc) = run_flatten cells.
Proof.
  move=> Hk. rewrite /split_cells Hk.
  rewrite -[in X in _ = X](take_drop_middle cells k c Hk).
  rewrite !run_flatten_app !run_flatten_cons run_flatten_nil.
  rewrite /split_cell_left /split_cell_right /=.
  rewrite app_nil_r take_drop //.
Qed.

(** ... and to the visible count. *)
Lemma split_cells_num_visible (cells : list item_cell) (k o : nat) (r_loc : loc) (c : item_cell) :
  cells !! k = Some c ->
  num_visible (split_cells cells k o r_loc) = num_visible cells.
Proof.
  move=> Hk. rewrite /split_cells Hk.
  rewrite -[in X in _ = X](take_drop_middle cells k c Hk).
  rewrite /num_visible !fmap_app !fmap_cons !list_sum_app /=.
  rewrite /split_cell_left /split_cell_right /=.
  destruct (ic_deleted c); [lia |].
  rewrite !length_take !length_drop. lia.
Qed.

(** Both halves of a well-formed run are well-formed (offset strictly inside). *)
Lemma run_wf_take (r : list (YjsItem A)) (o : nat) :
  (0 < o)%nat -> run_wf r -> run_wf (take o r).
Proof.
  move=> Ho [Hne Hstep]. split.
  - destruct r as [|y r']; [done |]. destruct o; [lia | done].
  - move=> k x y Hx Hy.
    apply lookup_take_Some in Hx as [Hx _]. apply lookup_take_Some in Hy as [Hy _].
    exact (Hstep k x y Hx Hy).
Qed.

Lemma run_wf_drop (r : list (YjsItem A)) (o : nat) :
  (o < length r)%nat -> run_wf r -> run_wf (drop o r).
Proof.
  move=> Ho [Hne Hstep]. split.
  - move=> Hnil. have := f_equal length Hnil. rewrite length_drop /=. lia.
  - move=> k x y Hx Hy.
    rewrite lookup_drop in Hx. rewrite lookup_drop in Hy.
    replace (o + S k)%nat with (S (o + k))%nat in Hy by lia.
    exact (Hstep (o + k)%nat x y Hx Hy).
Qed.

(** A cell's head model item is in the flatten (nonempty run via the unit
    invariant; issue #28). *)
Lemma run_head_in_flatten (cells : list item_cell) (c : item_cell) :
  c ∈ cells -> cell_unit c -> run_head c ∈ run_flatten cells.
Proof.
  intros Hc Hu. rewrite /cell_unit in Hu.
  apply list_elem_of_join. exists (ic_run c).
  split; last (apply list_elem_of_fmap_2; exact Hc).
  rewrite /run_head. destruct (ic_run c) as [|y [|y' r']]; simpl in Hu; [lia | | lia].
  simpl. apply list_elem_of_singleton. reflexivity.
Qed.

(** The all-singleton invariant survives a cell splice (issue #28, M1). *)
Lemma Forall_cell_unit_splice (cells : list item_cell) (k : nat) (c : item_cell) :
  Forall cell_unit cells -> cell_unit c ->
  Forall cell_unit (take k cells ++ c :: drop k cells).
Proof.
  intros H Hc. apply Forall_app_2; [by apply Forall_take |].
  constructor; [exact Hc | by apply Forall_drop].
Qed.

Definition pr_le (p q : Z * loc) : Prop := (p.1 <= q.1)%Z.

Lemma ic_loc_fmap_pr (l : list item_cell) : ic_loc <$> l = snd <$> (cell_pr <$> l).
Proof. rewrite -list_fmap_compose. reflexivity. Qed.

Lemma SS_cell_pr_merge (l : list item_cell) :
  StronglySorted pr_le (cell_pr <$> merge_sort cell_le l).
Proof.
  apply (StronglySorted_fmap cell_pr cell_le pr_le).
  - move=> x y Hxy. rewrite /pr_le /cell_pr /cell_le in Hxy |- *. exact Hxy.
  - apply (StronglySorted_merge_sort cell_le).
Qed.

Lemma merge_sort_loc_perm (l1 l2 : list item_cell) :
  (∀ x1 x2, x1 ∈ l1 → x2 ∈ l2 → (cell_pr x1).1 = (cell_pr x2).1 → ic_loc x1 = ic_loc x2) ->
  cell_pr <$> l1 ≡ₚ cell_pr <$> l2 ->
  ic_loc <$> merge_sort cell_le l1 = ic_loc <$> merge_sort cell_le l2.
Proof.
  move=> Hkd Hperm.
  rewrite (ic_loc_fmap_pr (merge_sort cell_le l1)) (ic_loc_fmap_pr (merge_sort cell_le l2)).
  f_equal.
  apply (StronglySorted_unique_strong pr_le).
  - move=> p1 p2 Hp1 Hp2 H12 H21.
    apply list_elem_of_fmap in Hp1 as (x1 & -> & Hx1).
    apply list_elem_of_fmap in Hp2 as (x2 & -> & Hx2).
    rewrite (merge_sort_Permutation cell_le l1) in Hx1.
    rewrite (merge_sort_Permutation cell_le l2) in Hx2.
    rewrite /pr_le in H12 H21.
    have Hkeq : (cell_pr x1).1 = (cell_pr x2).1 by lia.
    rewrite /cell_pr /=. f_equal; [exact Hkeq | exact (Hkd x1 x2 Hx1 Hx2 Hkeq)].
  - apply SS_cell_pr_merge.
  - apply SS_cell_pr_merge.
  - rewrite (merge_sort_Permutation cell_le l1) (merge_sort_Permutation cell_le l2). exact Hperm.
Qed.

Lemma merge_sort_loc_snoc (L : list item_cell) (x : item_cell) :
  (∀ y1 y2, y1 ∈ L → y2 ∈ L → (cell_pr y1).1 = (cell_pr y2).1 → ic_loc y1 = ic_loc y2) ->
  (∀ y, y ∈ L → ((cell_pr y).1 < (cell_pr x).1)%Z) ->
  ic_loc <$> merge_sort cell_le (L ++ [x]) = (ic_loc <$> merge_sort cell_le L) ++ [ic_loc x].
Proof.
  move=> Hkd Hmax.
  rewrite (ic_loc_fmap_pr (merge_sort cell_le (L ++ [x]))) (ic_loc_fmap_pr (merge_sort cell_le L)).
  replace ((snd <$> (cell_pr <$> merge_sort cell_le L)) ++ [ic_loc x])
    with (snd <$> ((cell_pr <$> merge_sort cell_le L) ++ [cell_pr x]))
    by (rewrite fmap_app /=; reflexivity).
  f_equal.
  apply (StronglySorted_unique_strong pr_le).
  - move=> p1 p2 Hp1 Hp2 H12 H21.
    apply list_elem_of_fmap in Hp1 as (x1 & -> & Hx1).
    rewrite (merge_sort_Permutation cell_le (L ++ [x])) in Hx1.
    apply elem_of_app in Hp2 as [Hp2 | Hp2].
    + apply list_elem_of_fmap in Hp2 as (x2 & -> & Hx2).
      rewrite (merge_sort_Permutation cell_le L) in Hx2.
      rewrite /pr_le in H12 H21.
      have Hkeq : (cell_pr x1).1 = (cell_pr x2).1 by lia.
      apply elem_of_app in Hx1 as [Hx1L | Hx1x].
      * rewrite /cell_pr /=. f_equal; [exact Hkeq | exact (Hkd x1 x2 Hx1L Hx2 Hkeq)].
      * apply list_elem_of_singleton in Hx1x as ->. exfalso. have := Hmax x2 Hx2. rewrite /pr_le in H12 H21. lia.
    + apply list_elem_of_singleton in Hp2 as ->.
      rewrite /pr_le in H12 H21.
      apply elem_of_app in Hx1 as [Hx1L | Hx1x].
      * exfalso. have := Hmax x1 Hx1L. lia.
      * apply list_elem_of_singleton in Hx1x as ->. reflexivity.
  - apply SS_cell_pr_merge.
  - apply StronglySorted_app_2.
    + move=> p z Hp Hz. apply list_elem_of_singleton in Hz as ->.
      apply list_elem_of_fmap in Hp as (y & -> & Hy). rewrite (merge_sort_Permutation cell_le L) in Hy.
      rewrite /pr_le. have := Hmax y Hy. lia.
    + apply SS_cell_pr_merge.
    + repeat constructor.
  - rewrite (merge_sort_Permutation cell_le (L ++ [x])) fmap_app /=.
    apply Permutation_app; [| reflexivity].
    apply Permutation_map. symmetry. apply (merge_sort_Permutation cell_le L).
Qed.

Lemma merge_sort_loc_insert (L : list item_cell) (x : item_cell) (i : nat) :
  (∀ y1 y2, y1 ∈ L → y2 ∈ L → (cell_pr y1).1 = (cell_pr y2).1 → ic_loc y1 = ic_loc y2) ->
  (∀ y, y ∈ take i (merge_sort cell_le L) → ((cell_pr y).1 < (cell_pr x).1)%Z) ->
  (∀ y, y ∈ drop i (merge_sort cell_le L) → ((cell_pr x).1 < (cell_pr y).1)%Z) ->
  ic_loc <$> merge_sort cell_le (L ++ [x])
  = take i (ic_loc <$> merge_sort cell_le L) ++ ic_loc x :: drop i (ic_loc <$> merge_sort cell_le L).
Proof.
  move=> Hkd Hbef Haft.
  remember (merge_sort cell_le L) as S eqn:HS.
  have HinL : ∀ z, z ∈ S -> z ∈ L.
  { move=> z Hz. rewrite HS in Hz. by rewrite (merge_sort_Permutation cell_le L) in Hz. }
  have HinS_take : ∀ z, z ∈ take i S -> z ∈ S.
  { move=> z Hz. rewrite -(take_drop i S). apply elem_of_app. by left. }
  have HinS_drop : ∀ z, z ∈ drop i S -> z ∈ S.
  { move=> z Hz. rewrite -(take_drop i S). apply elem_of_app. by right. }
  have HSSp : StronglySorted pr_le (cell_pr <$> S).
  { rewrite HS. apply SS_cell_pr_merge. }
  have HABeq : cell_pr <$> S = (cell_pr <$> take i S) ++ (cell_pr <$> drop i S).
  { by rewrite -fmap_app take_drop. }
  have HpermSL : cell_pr <$> S ≡ₚ cell_pr <$> L.
  { rewrite HS. apply Permutation_map. apply (merge_sort_Permutation cell_le L). }
  have Hpr : cell_pr <$> merge_sort cell_le (L ++ [x])
           = (cell_pr <$> take i S) ++ cell_pr x :: (cell_pr <$> drop i S).
  { apply (StronglySorted_unique_strong pr_le).
    - move=> p1 p2 Hp1 Hp2 H12 H21.
      have Hkeq : p1.1 = p2.1 by (rewrite /pr_le in H12 H21; lia).
      apply list_elem_of_fmap in Hp1 as (x1 & -> & Hx1).
      rewrite (merge_sort_Permutation cell_le (L ++ [x])) in Hx1.
      have Hp2c : (∃ x2, p2 = cell_pr x2 ∧ x2 ∈ S) ∨ p2 = cell_pr x.
      { apply elem_of_app in Hp2 as [Hp2 | Hp2].
        - apply list_elem_of_fmap in Hp2 as (x2 & -> & Hx2).
          left. exists x2. split; [reflexivity | exact (HinS_take x2 Hx2)].
        - apply elem_of_cons in Hp2 as [-> | Hp2]; [by right |].
          apply list_elem_of_fmap in Hp2 as (x2 & -> & Hx2).
          left. exists x2. split; [reflexivity | exact (HinS_drop x2 Hx2)]. }
      apply elem_of_app in Hx1 as [Hx1L | Hx1x]; last apply list_elem_of_singleton in Hx1x as ->.
      + destruct Hp2c as [(x2 & -> & Hx2S) | ->].
        * have Hx2L := HinL x2 Hx2S.
          rewrite /cell_pr /=. rewrite /cell_pr /= in Hkeq. f_equal;
            [exact Hkeq | exact (Hkd x1 x2 Hx1L Hx2L Hkeq)].
        * exfalso.
          have Hx1S : x1 ∈ S.
          { rewrite HS. by rewrite (merge_sort_Permutation cell_le L). }
          rewrite -(take_drop i S) in Hx1S. apply elem_of_app in Hx1S as [Ht | Hd].
          -- have := Hbef x1 Ht. lia.
          -- have := Haft x1 Hd. lia.
      + destruct Hp2c as [(x2 & -> & Hx2S) | ->]; [| reflexivity].
        exfalso.
        rewrite -(take_drop i S) in Hx2S. apply elem_of_app in Hx2S as [Ht | Hd].
        * have := Hbef x2 Ht. lia.
        * have := Haft x2 Hd. lia.
    - apply SS_cell_pr_merge.
    - apply StronglySorted_app_2.
      + move=> a c Ha Hc.
        apply list_elem_of_fmap in Ha as (ya & -> & Hya).
        apply elem_of_cons in Hc as [-> | Hc].
        * rewrite /pr_le. have := Hbef ya Hya. lia.
        * apply list_elem_of_fmap in Hc as (yc & -> & Hyc).
          rewrite /pr_le. have := Hbef ya Hya. have := Haft yc Hyc. lia.
      + rewrite HABeq in HSSp. exact (StronglySorted_app_1_l _ _ _ HSSp).
      + change (cell_pr x :: (cell_pr <$> drop i S)) with ([cell_pr x] ++ (cell_pr <$> drop i S)).
        apply StronglySorted_app_2.
        * move=> a c Ha Hc. apply list_elem_of_singleton in Ha as ->.
          apply list_elem_of_fmap in Hc as (yc & -> & Hyc).
          rewrite /pr_le. have := Haft yc Hyc. lia.
        * repeat constructor.
        * rewrite HABeq in HSSp. exact (StronglySorted_app_1_r _ _ _ HSSp).
    - transitivity ((cell_pr <$> L) ++ [cell_pr x]).
      { rewrite (merge_sort_Permutation cell_le (L ++ [x])) fmap_app //. }
      symmetry. transitivity (cell_pr x :: (cell_pr <$> S)).
      { rewrite -Permutation_middle -HABeq //. }
      rewrite HpermSL.
      by rewrite Permutation_cons_append. }
  rewrite (ic_loc_fmap_pr (merge_sort cell_le (L ++ [x]))) Hpr.
  rewrite fmap_app fmap_cons -!ic_loc_fmap_pr -fmap_take -fmap_drop.
  done.
Qed.

(** [concat] respects permutation of the outer list. *)
Lemma concat_perm {D : Type} (ll1 ll2 : list (list D)) :
  ll1 ≡ₚ ll2 -> concat ll1 ≡ₚ concat ll2.
Proof.
  induction 1; simpl.
  - reflexivity.
  - apply Permutation_app_head. exact IHPermutation.
  - rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm.
  - etrans; eassumption.
Qed.

(** Updating an existing key's value reshuffles [map_to_list] only at that key. *)
Lemma map_to_list_insert_existing {V : Type} (m : gmap loc V) (k : loc) (v v' : V) :
  m !! k = Some v ->
  map_to_list (<[k:=v']> m) ≡ₚ (k, v') :: map_to_list (delete k m).
Proof.
  move=> Hk.
  pose proof (map_to_list_delete (<[k:=v']> m) k v' (lookup_insert_eq m k v')) as Hp.
  rewrite delete_insert_eq in Hp. symmetry. exact Hp.
Qed.

(** Updating one registered type's cell list reshuffles the document-global cell
    pool [all_cells] only at that type. *)
Lemma all_cells_insert (types : gmap loc type_state) (parent : loc) (ts ts' : type_state) :
  types !! parent = Some ts ->
  all_cells (<[parent:=ts']> types) ≡ₚ ty_cells ts' ++ all_cells (delete parent types).
Proof.
  move=> Hp. rewrite /all_cells.
  apply (concat_perm (ty_cells <$> (map_to_list (<[parent:=ts']> types)).*2)
                     (ty_cells ts' :: (ty_cells <$> (map_to_list (delete parent types)).*2))).
  rewrite (map_to_list_insert_existing types parent ts ts' Hp). simpl. reflexivity.
Qed.

Lemma all_cells_lookup (types : gmap loc type_state) (parent : loc) (ts : type_state) :
  types !! parent = Some ts ->
  all_cells types ≡ₚ ty_cells ts ++ all_cells (delete parent types).
Proof.
  move=> Hp.
  pose proof (all_cells_insert types parent ts ts Hp) as H.
  rewrite (insert_id types parent ts Hp) in H. exact H.
Qed.

(** Replacing the registered type at [parent] by one whose cell list is the old
    one with one cell [c] appended (modulo permutation) grows the document-global
    cell pool by exactly [c]. This is the cell-pool view of [Store.Integrate]'s
    splice ([cells' ≡ₚ cells ++ [c]]): the inserted item adds a single cell, and
    the neighbour relink (invisible to the abstract cells) moves nothing else. It
    feeds both the wrapper's [cell_kp] growth and [Text.Insert]'s loop-carried
    heap-clock bound. *)
Lemma all_cells_insert_snoc (types : gmap loc type_state) (parent : loc)
    (cells arr cells' arr' : list _) (c : item_cell) :
  types !! parent = Some (MkTypeState cells arr) ->
  cells' ≡ₚ cells ++ [c] ->
  all_cells (<[parent := MkTypeState cells' arr']> types) ≡ₚ all_cells types ++ [c].
Proof.
  move=> Hp Hperm.
  rewrite (all_cells_insert types parent (MkTypeState cells arr) (MkTypeState cells' arr') Hp).
  rewrite (all_cells_lookup types parent (MkTypeState cells arr) Hp).
  simpl. rewrite Hperm.
  rewrite -!app_assoc. apply Permutation_app_head. apply Permutation_app_comm.
Qed.

(** A fully-owned node struct's location is fresh for the whole document cell
    pool: the source of the [NoDup (ic_loc <$> all_cells types)] maintenance
    when a freshly allocated node is spliced in (issue #28 part 6). Stated over
    the bare [own_ytype_cells] big-sep; callers peel the pure conjuncts. *)
Lemma all_cells_fresh (p : loc) (v : yjs.item.t) (dq : dfrac) (types : gmap loc type_state) :
  p ↦ v -∗
  ([∗ map] parent ↦ ts ∈ types, own_ytype_cells parent dq (ty_cells ts) (ty_arr ts)) -∗
  ⌜p ∉ ic_loc <$> all_cells types⌝.
Proof using ext ffi ffi_interp0 Σ hG ffi_semantics0 sem package_sem.
  iIntros "Hp Htypes".
  rewrite big_sepM_map_to_list /all_cells.
  remember (map_to_list types) as L eqn:HeqL. clear HeqL.
  iInduction L as [|[parent ts] L] "IH".
  - iPureIntro. apply not_elem_of_nil.
  - simpl. iDestruct "Htypes" as "[Hhd Htypes]".
    iDestruct "Hhd" as (yt tl) "(Hyt & Hdll & _)".
    iDestruct (own_dll_fresh with "Hp Hdll") as %H1.
    iDestruct ("IH" with "Hp Htypes") as %H2.
    iPureIntro. rewrite fmap_app not_elem_of_app.
    split; [exact H1 | exact H2].
Qed.

(** [all_cells_fresh] over the 3-conjunct store big-sep (the shape the store
    proofs thread). *)
Lemma all_cells_fresh3 (p : loc) (v : yjs.item.t) (dq : dfrac) (types : gmap loc type_state) :
  p ↦ v -∗
  ([∗ map] parent ↦ ts ∈ types,
      own_ytype_cells parent dq (ty_cells ts) (ty_arr ts) ∗
      ⌜YjsArrInvariant (ty_arr ts)⌝ ∗
      ⌜Forall cell_unit (ty_cells ts)⌝) -∗
  ⌜p ∉ ic_loc <$> all_cells types⌝.
Proof using ext ffi ffi_interp0 Σ hG ffi_semantics0 sem package_sem.
  iIntros "Hp Htypes".
  iDestruct (big_sepM_sep with "Htypes") as "[Hbare _]".
  iApply (all_cells_fresh with "Hp Hbare").
Qed.

(* ----- the part-6 pool invariants (issue #28): loc NoDup + range disjointness *)

(** Per-client clock-RANGE disjointness of the document cell pool: two distinct
    same-client cells occupy disjoint clock intervals [clock, clock + len).
    This is [wp_store__splitNode]'s [Hdisj] hypothesis shape: it pins the
    covering cell [getNodeIndex] returns uniquely once runs are multi-char. *)
Definition cells_range_disjoint (pool : list item_cell) : Prop :=
  ∀ c1 c2, c1 ∈ pool → c2 ∈ pool →
    cell_client c1 = cell_client c2 → ic_loc c1 ≠ ic_loc c2 →
    (uint.Z (cell_clock c1) + Z.of_nat (length (ic_run c1)) ≤ uint.Z (cell_clock c2))%Z ∨
    (uint.Z (cell_clock c2) + Z.of_nat (length (ic_run c2)) ≤ uint.Z (cell_clock c1))%Z.

(** [NoDup] of the pool's locations survives an integrate splice: the pool
    grows by exactly one cell at a fresh location ([all_cells_fresh]). *)
Lemma nodup_locs_snoc (pool1 pool2 : list item_cell) (c : item_cell) :
  pool2 ≡ₚ pool1 ++ [c] ->
  ic_loc c ∉ ic_loc <$> pool1 ->
  NoDup (ic_loc <$> pool1) ->
  NoDup (ic_loc <$> pool2).
Proof.
  move=> Hperm Hfresh Hnd.
  rewrite Hperm fmap_app /=.
  apply NoDup_app. split_and!; [exact Hnd | | apply NoDup_singleton].
  move=> x Hx Hx1. apply list_elem_of_singleton in Hx1. subst x. done.
Qed.

(** Range disjointness survives an integrate splice whose new cell's range sits
    fully above every same-client range (the range-aware maximality that the
    insert counter / remote-op freshness provides). *)
Lemma rangedisj_snoc (pool1 pool2 : list item_cell) (c : item_cell) :
  pool2 ≡ₚ pool1 ++ [c] ->
  (∀ c0, c0 ∈ pool1 → cell_client c0 = cell_client c →
     (uint.Z (cell_clock c0) + Z.of_nat (length (ic_run c0)) ≤ uint.Z (cell_clock c))%Z) ->
  cells_range_disjoint pool1 ->
  cells_range_disjoint pool2.
Proof.
  move=> Hperm Hmax Hdisj c1 c2 Hc1 Hc2 Hcc Hne.
  rewrite Hperm in Hc1 Hc2.
  apply elem_of_app in Hc1 as [Hc1 | Hc1]; apply elem_of_app in Hc2 as [Hc2 | Hc2].
  - exact (Hdisj c1 c2 Hc1 Hc2 Hcc Hne).
  - apply list_elem_of_singleton in Hc2 as ->. left. exact (Hmax c1 Hc1 Hcc).
  - apply list_elem_of_singleton in Hc1 as ->. right. apply (Hmax c2 Hc2). symmetry. exact Hcc.
  - apply list_elem_of_singleton in Hc1 as ->. apply list_elem_of_singleton in Hc2 as ->. done.
Qed.

(** Both pool invariants only read a cell's location and run; transport them
    across a pool reshuffle preserving those (what [Text.Delete]'s
    [ic_deleted] flip is). *)
Lemma locs_run_perm_nodup (pool1 pool2 : list item_cell) :
  (λ c, (ic_loc c, ic_run c)) <$> pool2 ≡ₚ (λ c, (ic_loc c, ic_run c)) <$> pool1 ->
  NoDup (ic_loc <$> pool1) -> NoDup (ic_loc <$> pool2).
Proof.
  move=> Hperm Hnd.
  have Hcomp : ∀ (l : list item_cell), (fst ∘ (λ c, (ic_loc c, ic_run c))) <$> l = ic_loc <$> l.
  { elim => [//| a l' IH] /=. by f_equal. }
  have Hf : (fst ∘ (λ c, (ic_loc c, ic_run c))) <$> pool2 ≡ₚ (fst ∘ (λ c, (ic_loc c, ic_run c))) <$> pool1.
  { rewrite !list_fmap_compose Hperm //. }
  rewrite !Hcomp in Hf. by rewrite Hf.
Qed.

Lemma locs_run_perm_rangedisj (pool1 pool2 : list item_cell) :
  (λ c, (ic_loc c, ic_run c)) <$> pool2 ≡ₚ (λ c, (ic_loc c, ic_run c)) <$> pool1 ->
  cells_range_disjoint pool1 -> cells_range_disjoint pool2.
Proof.
  move=> Hperm Hdisj c1 c2 Hc1 Hc2 Hcc Hne.
  have Hlift : ∀ c', c' ∈ pool2 → ∃ c'', c'' ∈ pool1 ∧
      ic_loc c' = ic_loc c'' ∧ ic_run c' = ic_run c''.
  { move=> c' Hc'.
    have Hin : (ic_loc c', ic_run c') ∈ ((λ c0, (ic_loc c0, ic_run c0)) <$> pool1).
    { rewrite -Hperm. exact (list_elem_of_fmap_2 _ _ _ Hc'). }
    apply list_elem_of_fmap in Hin as (c'' & Heq & Hc'').
    exists c''. split; [exact Hc'' |].
    split; [exact (f_equal fst Heq) | exact (f_equal snd Heq)]. }
  destruct (Hlift c1 Hc1) as (c1' & Hc1' & Hl1 & Hr1).
  destruct (Hlift c2 Hc2) as (c2' & Hc2' & Hl2 & Hr2).
  have Hcl1 : cell_client c1' = cell_client c1 by (rewrite /cell_client /run_head -Hr1 //).
  have Hcl2 : cell_client c2' = cell_client c2 by (rewrite /cell_client /run_head -Hr2 //).
  have Hck1 : cell_clock c1' = cell_clock c1 by (rewrite /cell_clock /run_head -Hr1 //).
  have Hck2 : cell_clock c2' = cell_clock c2 by (rewrite /cell_clock /run_head -Hr2 //).
  have Hd := Hdisj c1' c2' Hc1' Hc2' ltac:(rewrite Hcl1 Hcl2 //) ltac:(rewrite -Hl1 -Hl2 //).
  rewrite Hck1 Hck2 -Hr1 -Hr2 in Hd. exact Hd.
Qed.

(** [cell_kp] bundles a cell's (client, clock, loc). The slice/run preservation
    consumes a [cell_kp] multiset permutation; on this base the integrate splice
    gives an EXACT [item_cell] permutation [cells' ≡ₚ cells ++ [new]] (the cell
    carries only the model item + loc, both invariant under the neighbour relink
    that lives existentially in [own_dll]), so the [cell_kp] permutation follows by
    [fmap]. *)
Definition cell_kp (c : item_cell) : w64 * (Z * loc) := (cell_client c, cell_pr c).

(** [cell_kp] projections: a cell's (client, clock, loc) is exactly what its
    key-pair records, so equal key-pairs give equal components. Used to transfer
    the run-map / clock-bound side conditions across a [cell_kp]-preserving
    reshuffle (what [Text.Delete]'s [ic_deleted] flip is — [flip_cell] touches
    neither [ic_run] nor [ic_loc], so [cell_kp (flip_cell c) = cell_kp c]). *)
Lemma cell_kp_client (a b : item_cell) : cell_kp a = cell_kp b -> cell_client a = cell_client b.
Proof. move=> H. exact (f_equal fst H). Qed.
Lemma cell_kp_pr (a b : item_cell) : cell_kp a = cell_kp b -> cell_pr a = cell_pr b.
Proof. move=> H. exact (f_equal snd H). Qed.
Lemma cell_kp_clock (a b : item_cell) : cell_kp a = cell_kp b -> uint.Z (cell_clock a) = uint.Z (cell_clock b).
Proof. move=> H. exact (f_equal (fun p => p.2.1) H). Qed.
Lemma cell_kp_loc (a b : item_cell) : cell_kp a = cell_kp b -> ic_loc a = ic_loc b.
Proof. move=> H. exact (f_equal snd (cell_kp_pr a b H)). Qed.
Lemma cell_kp_flip (c : item_cell) : cell_kp (flip_cell c) = cell_kp c.
Proof. reflexivity. Qed.

Lemma cell_pr_filter_kp (client : w64) (l : list item_cell) :
  cell_pr <$> filter (λ c, cell_client c = client) l
  = snd <$> filter (λ kp : w64 * (Z * loc), kp.1 = client) (cell_kp <$> l).
Proof.
  induction l as [|c l IH]; [reflexivity|].
  rewrite fmap_cons filter_cons filter_cons /cell_kp /=.
  case_decide as Hc.
  - rewrite fmap_cons IH /=. reflexivity.
  - exact IH.
Qed.

Lemma cell_pr_filter_perm (client : w64) (l1 l2 : list item_cell) :
  cell_kp <$> l1 ≡ₚ cell_kp <$> l2 ->
  cell_pr <$> filter (λ c, cell_client c = client) l1
  ≡ₚ cell_pr <$> filter (λ c, cell_client c = client) l2.
Proof.
  move=> H. rewrite !cell_pr_filter_kp. apply Permutation_map. rewrite H. reflexivity.
Qed.


(** Re-establishing the run after [Store.Integrate]'s [AddNode]: the new cell's
    loc lands at the TAIL of its client's clock-sorted run, and other clients'
    runs are untouched — at the loc-sequence level (what the slice stores), given
    the document-global [cell_kp] multiset grows by exactly the new cell ([Hkp])
    and clock determines loc per client ([Hclkloc], the [own_item_map] side cond).
    [Hmax] (the new cell is strictly clock-maximal for its client) puts it last. *)
Lemma client_run_loc_tail (types types2 : gmap loc type_state) (newcell : item_cell) :
  cell_kp <$> all_cells types2 ≡ₚ (cell_kp <$> all_cells types) ++ [cell_kp newcell] ->
  (∀ c1 c2, c1 ∈ all_cells types → c2 ∈ all_cells types → cell_client c1 = cell_client c2 →
            (cell_pr c1).1 = (cell_pr c2).1 → ic_loc c1 = ic_loc c2) ->
  (∀ c, c ∈ all_cells types → cell_client c = cell_client newcell → ((cell_pr c).1 < (cell_pr newcell).1)%Z) ->
  ic_loc <$> client_run types2 (cell_client newcell)
  = (ic_loc <$> client_run types (cell_client newcell)) ++ [ic_loc newcell].
Proof.
  move=> Hkp Hclkloc Hmax.
  set client := cell_client newcell.
  set Lpre := filter (λ c, cell_client c = client) (all_cells types).
  set Lpost := filter (λ c, cell_client c = client) (all_cells types2).
  have Hkp2 : cell_kp <$> all_cells types2 ≡ₚ cell_kp <$> (all_cells types ++ [newcell]).
  { rewrite fmap_app /=. exact Hkp. }
  have Hfilt : filter (λ c, cell_client c = client) (all_cells types ++ [newcell])
             = Lpre ++ [newcell].
  { rewrite filter_app /Lpre. f_equal. rewrite filter_cons.
    rewrite decide_True; [reflexivity | rewrite /client; reflexivity]. }
  have Hpermf : cell_pr <$> Lpost ≡ₚ (cell_pr <$> Lpre) ++ [cell_pr newcell].
  { rewrite /Lpost (cell_pr_filter_perm client (all_cells types2) (all_cells types ++ [newcell]) Hkp2).
    rewrite Hfilt fmap_app /=. reflexivity. }
  have Hkdl2 : ∀ x y, x ∈ Lpre ++ [newcell] → y ∈ Lpre ++ [newcell] →
                (cell_pr x).1 = (cell_pr y).1 → ic_loc x = ic_loc y.
  { move=> x y Hx Hy Hxy.
    have Hin : ∀ z, z ∈ Lpre ++ [newcell] → (z ∈ all_cells types ∧ cell_client z = client) ∨ z = newcell.
    { move=> z Hz. apply elem_of_app in Hz as [Hz | Hz].
      - left. rewrite /Lpre list_elem_of_filter in Hz. tauto.
      - right. by apply list_elem_of_singleton in Hz. }
    destruct (Hin x Hx) as [[Hxa Hxc] | ->]; destruct (Hin y Hy) as [[Hya Hyc] | ->].
    - apply (Hclkloc x y Hxa Hya); [rewrite Hxc Hyc // | exact Hxy].
    - exfalso. have := Hmax x Hxa Hxc. lia.
    - exfalso. have := Hmax y Hya Hyc. lia.
    - reflexivity. }
  have Hcross : ∀ x1 x2, x1 ∈ Lpost → x2 ∈ Lpre ++ [newcell] →
                  (cell_pr x1).1 = (cell_pr x2).1 → ic_loc x1 = ic_loc x2.
  { move=> x1 x2 Hx1 Hx2 H12.
    have Hp1 : cell_pr x1 ∈ cell_pr <$> Lpost by apply list_elem_of_fmap_2.
    rewrite Hpermf in Hp1.
    have Hp1' : cell_pr x1 ∈ cell_pr <$> (Lpre ++ [newcell]) by (rewrite fmap_app /=; exact Hp1).
    apply list_elem_of_fmap in Hp1' as (x2' & Hx1eq & Hx2').
    have Hloc1 : ic_loc x1 = ic_loc x2' by (rewrite /cell_pr /= in Hx1eq; injection Hx1eq; auto).
    rewrite Hloc1. apply (Hkdl2 x2' x2 Hx2' Hx2). rewrite -Hx1eq. exact H12. }
  rewrite /client_run -/client.
  rewrite (merge_sort_loc_perm Lpost (Lpre ++ [newcell]) Hcross).
  { rewrite (merge_sort_loc_snoc Lpre newcell).
    - reflexivity.
    - move=> y1 y2 Hy1 Hy2 Hk. rewrite /Lpre list_elem_of_filter in Hy1.
      rewrite /Lpre list_elem_of_filter in Hy2.
      apply (Hclkloc y1 y2 (proj2 Hy1) (proj2 Hy2)); [rewrite (proj1 Hy1) (proj1 Hy2) // | exact Hk].
    - move=> y Hy. rewrite /Lpre list_elem_of_filter in Hy. apply (Hmax y (proj2 Hy) (proj1 Hy)). }
  rewrite fmap_app /=. exact Hpermf.
Qed.

(** The insert-at-position-[i] analogue of [client_run_loc_tail]: when the new
    cell's clock is NOT maximal but sits strictly between the sorted-run cells
    at [i-1] and [i] (the two [take]/[drop] strict-clock premises), its loc lands
    at position [i]. This is the [store.splitNode] item-map effect: the right
    half is inserted just after its (unchanged-loc) left half in the client run.
    Wraps [merge_sort_loc_insert] the way the tail lemma wraps
    [merge_sort_loc_snoc]. *)
Lemma client_run_loc_insert (types types2 : gmap loc type_state) (newcell : item_cell) (i : nat) :
  cell_kp <$> all_cells types2 ≡ₚ (cell_kp <$> all_cells types) ++ [cell_kp newcell] ->
  (∀ c1 c2, c1 ∈ all_cells types → c2 ∈ all_cells types → cell_client c1 = cell_client c2 →
            (cell_pr c1).1 = (cell_pr c2).1 → ic_loc c1 = ic_loc c2) ->
  (∀ y, y ∈ take i (client_run types (cell_client newcell)) → ((cell_pr y).1 < (cell_pr newcell).1)%Z) ->
  (∀ y, y ∈ drop i (client_run types (cell_client newcell)) → ((cell_pr newcell).1 < (cell_pr y).1)%Z) ->
  ic_loc <$> client_run types2 (cell_client newcell)
  = take i (ic_loc <$> client_run types (cell_client newcell))
      ++ ic_loc newcell :: drop i (ic_loc <$> client_run types (cell_client newcell)).
Proof.
  move=> Hkp Hclkloc Hbef Haft.
  set client := cell_client newcell.
  set Lpre := filter (λ c, cell_client c = client) (all_cells types).
  set Lpost := filter (λ c, cell_client c = client) (all_cells types2).
  have Hkp2 : cell_kp <$> all_cells types2 ≡ₚ cell_kp <$> (all_cells types ++ [newcell]).
  { rewrite fmap_app /=. exact Hkp. }
  have Hfilt : filter (λ c, cell_client c = client) (all_cells types ++ [newcell])
             = Lpre ++ [newcell].
  { rewrite filter_app /Lpre. f_equal. rewrite filter_cons.
    rewrite decide_True; [reflexivity | rewrite /client; reflexivity]. }
  have Hpermf : cell_pr <$> Lpost ≡ₚ (cell_pr <$> Lpre) ++ [cell_pr newcell].
  { rewrite /Lpost (cell_pr_filter_perm client (all_cells types2) (all_cells types ++ [newcell]) Hkp2).
    rewrite Hfilt fmap_app /=. reflexivity. }
  have HLpre_CR : ∀ z, z ∈ Lpre → z ∈ client_run types client.
  { move=> z Hz. change (client_run types client) with (merge_sort cell_le Lpre).
    by rewrite (merge_sort_Permutation cell_le Lpre). }
  have Hkd_pre : ∀ y1 y2, y1 ∈ Lpre → y2 ∈ Lpre → (cell_pr y1).1 = (cell_pr y2).1 → ic_loc y1 = ic_loc y2.
  { move=> y1 y2 Hy1 Hy2 Hk. rewrite /Lpre list_elem_of_filter in Hy1.
    rewrite /Lpre list_elem_of_filter in Hy2.
    apply (Hclkloc y1 y2 (proj2 Hy1) (proj2 Hy2)); [rewrite (proj1 Hy1) (proj1 Hy2) // | exact Hk]. }
  have Hkdl2 : ∀ x y, x ∈ Lpre ++ [newcell] → y ∈ Lpre ++ [newcell] →
                (cell_pr x).1 = (cell_pr y).1 → ic_loc x = ic_loc y.
  { move=> x y Hx Hy Hxy.
    have Hin : ∀ z, z ∈ Lpre ++ [newcell] → (z ∈ all_cells types ∧ cell_client z = client) ∨ z = newcell.
    { move=> z Hz. apply elem_of_app in Hz as [Hz | Hz].
      - left. rewrite /Lpre list_elem_of_filter in Hz. tauto.
      - right. by apply list_elem_of_singleton in Hz. }
    destruct (Hin x Hx) as [[Hxa Hxc] | ->]; destruct (Hin y Hy) as [[Hya Hyc] | ->].
    - apply (Hclkloc x y Hxa Hya); [rewrite Hxc Hyc // | exact Hxy].
    - exfalso.
      have HxLpre : x ∈ Lpre by (rewrite /Lpre list_elem_of_filter; split; [exact Hxc | exact Hxa]).
      have HxS : x ∈ client_run types client := HLpre_CR x HxLpre.
      rewrite -(take_drop i (client_run types client)) in HxS. apply elem_of_app in HxS as [Ht|Hd].
      + have := Hbef x Ht. lia.
      + have := Haft x Hd. lia.
    - exfalso.
      have HyLpre : y ∈ Lpre by (rewrite /Lpre list_elem_of_filter; split; [exact Hyc | exact Hya]).
      have HyS : y ∈ client_run types client := HLpre_CR y HyLpre.
      rewrite -(take_drop i (client_run types client)) in HyS. apply elem_of_app in HyS as [Ht|Hd].
      + have := Hbef y Ht. lia.
      + have := Haft y Hd. lia.
    - reflexivity. }
  have Hcross : ∀ x1 x2, x1 ∈ Lpost → x2 ∈ Lpre ++ [newcell] →
                  (cell_pr x1).1 = (cell_pr x2).1 → ic_loc x1 = ic_loc x2.
  { move=> x1 x2 Hx1 Hx2 H12.
    have Hp1 : cell_pr x1 ∈ cell_pr <$> Lpost by apply list_elem_of_fmap_2.
    rewrite Hpermf in Hp1.
    have Hp1' : cell_pr x1 ∈ cell_pr <$> (Lpre ++ [newcell]) by (rewrite fmap_app /=; exact Hp1).
    apply list_elem_of_fmap in Hp1' as (x2' & Hx1eq & Hx2').
    have Hloc1 : ic_loc x1 = ic_loc x2' by (rewrite /cell_pr /= in Hx1eq; injection Hx1eq; auto).
    rewrite Hloc1. apply (Hkdl2 x2' x2 Hx2' Hx2). rewrite -Hx1eq. exact H12. }
  rewrite /client_run -/client.
  rewrite (merge_sort_loc_perm Lpost (Lpre ++ [newcell]) Hcross).
  { rewrite (merge_sort_loc_insert Lpre newcell i Hkd_pre).
    - reflexivity.
    - move=> y Hy. apply Hbef. exact Hy.
    - move=> y Hy. apply Haft. exact Hy. }
  rewrite fmap_app /=. exact Hpermf.
Qed.

Lemma client_run_loc_other (types types2 : gmap loc type_state) (newcell : item_cell) (c' : w64) :
  cell_kp <$> all_cells types2 ≡ₚ (cell_kp <$> all_cells types) ++ [cell_kp newcell] ->
  (∀ c1 c2, c1 ∈ all_cells types → c2 ∈ all_cells types → cell_client c1 = cell_client c2 →
            (cell_pr c1).1 = (cell_pr c2).1 → ic_loc c1 = ic_loc c2) ->
  c' ≠ cell_client newcell ->
  ic_loc <$> client_run types2 c' = ic_loc <$> client_run types c'.
Proof.
  move=> Hkp Hclkloc Hne.
  set Lpre := filter (λ c, cell_client c = c') (all_cells types).
  set Lpost := filter (λ c, cell_client c = c') (all_cells types2).
  have Hkp2 : cell_kp <$> all_cells types2 ≡ₚ cell_kp <$> (all_cells types ++ [newcell]).
  { rewrite fmap_app /=. exact Hkp. }
  have Hfilt : filter (λ c, cell_client c = c') (all_cells types ++ [newcell]) = Lpre.
  { rewrite filter_app /Lpre. rewrite filter_cons.
    rewrite decide_False; [rewrite app_nil_r // | move=> H; apply Hne; by rewrite H]. }
  have Hpermf : cell_pr <$> Lpost ≡ₚ cell_pr <$> Lpre.
  { rewrite /Lpost (cell_pr_filter_perm c' (all_cells types2) (all_cells types ++ [newcell]) Hkp2).
    rewrite Hfilt. reflexivity. }
  have Hcross : ∀ x1 x2, x1 ∈ Lpost → x2 ∈ Lpre → (cell_pr x1).1 = (cell_pr x2).1 → ic_loc x1 = ic_loc x2.
  { move=> x1 x2 Hx1 Hx2 H12.
    have Hp1 : cell_pr x1 ∈ cell_pr <$> Lpost by apply list_elem_of_fmap_2.
    rewrite Hpermf in Hp1.
    apply list_elem_of_fmap in Hp1 as (x2' & Hx1eq & Hx2').
    have Hloc1 : ic_loc x1 = ic_loc x2' by (rewrite /cell_pr /= in Hx1eq; injection Hx1eq; auto).
    rewrite Hloc1.
    rewrite /Lpre list_elem_of_filter in Hx2'. rewrite /Lpre list_elem_of_filter in Hx2.
    apply (Hclkloc x2' x2 (proj2 Hx2') (proj2 Hx2)); [rewrite (proj1 Hx2') (proj1 Hx2) // |].
    rewrite -Hx1eq. exact H12. }
  rewrite /client_run.
  apply (merge_sort_loc_perm Lpost Lpre Hcross Hpermf).
Qed.

(** [own_item_map mref dq types]: the heap map at [mref] (Go [store.items]) owns
    the map header and, per client, the backing slice of [*item] *locations*
    (+ cap) — but NOT the item cells (those live in the DLL, [own_ytype_cells]).
    The slice for [client] is exactly [client_run types client]. Takes the
    [types] map directly (not a pre-flattened list); sortedness is baked into
    [client_run]. Owning heap data, it takes a [dfrac] ([DfracOwn 1] to append
    in [AddNode]). *)
Definition own_item_map (mref : loc) (dq : dfrac) (types : gmap loc type_state) : iProp Σ :=
  ∃ (gm : gmap w64 slice.t),
    "Hmap" ∷ own_map mref dq gm ∗
    "Hruns" ∷ ([∗ map] client ↦ s ∈ gm,
        "Hslice" ∷ s ↦*{dq} (ic_loc <$> client_run types client) ∗
        "Hcap"   ∷ own_slice_cap loc s dq) ∗
    "%Hcomplete" ∷ ⌜∀ c, c ∈ (cell_client <$> all_cells types) → is_Some (gm !! c)⌝ ∗
    "%Hclkloc" ∷ ⌜∀ c1 c2, c1 ∈ all_cells types → c2 ∈ all_cells types →
                    cell_client c1 = cell_client c2 → (cell_pr c1).1 = (cell_pr c2).1 →
                    ic_loc c1 = ic_loc c2⌝.

(* The [∷] (named) wrapper blocks [Timeless] TC resolution; unfold it (as
   [New.proof.sync_proof.rwmutex] does) so the [Timeless] instances below go
   through the named conjuncts of [own_item_map] / [store_inv]. *)
#[local] Hint Extern 100 (Timeless (?n ∷ ?P)) =>
  (change (n ∷ P) with P) : typeclass_instances.

(* [own_slice_cap] (a sealed disjunction of pure facts and a [↦{dq}] array) is
   timeless, but the New.golang slice library ships no such instance; provide it
   here (candidate upstream addition) so [own_item_map] / [store_inv] are
   timeless. *)
#[global] Instance own_slice_cap_timeless (V : Type) `{!ZeroVal V} `{!TypedPointsto V} (s : slice.t) (dq : dfrac) :
  Timeless (own_slice_cap V s dq).
Proof. rewrite own_slice_cap_unseal /own_slice_cap_def. apply _. Qed.

#[global] Instance own_item_map_timeless mref dq types : Timeless (own_item_map mref dq types).
Proof. rewrite /own_item_map. apply _. Qed.

(* The DLL predicate stack is timeless too (heap points-to + pure + persistent
   origin handles); register the instances so [store_inv] is timeless. *)
#[global] Instance is_origin_id_timeless p oid : Timeless (is_origin_id p oid).
Proof. rewrite /is_origin_id. by destruct oid; apply _. Qed.

#[global] Instance own_dll_timeless dq l last prev next cells :
  Timeless (own_dll dq l last prev next cells).
Proof.
  revert l last prev next.
  induction cells as [|c rest IH]; intros l last prev next; simpl.
  - apply _.
  - repeat (apply bi.exist_timeless; intros ?).
    repeat (apply bi.sep_timeless; [ apply _ | ]).
    apply IH.
Qed.

#[global] Instance own_ytype_cells_timeless parent dq cells arr :
  Timeless (own_ytype_cells parent dq cells arr).
Proof. rewrite /own_ytype_cells. apply _. Qed.

(* ----- fractional DLL stack (for the concurrent-read share of [store_inv]) ---
   The read lock hands each reader a fractional share of the read-only part of
   [store_inv] (its DLLs + the item-set auth). These make that share splittable:
   [own_dll] / [own_ytype_cells] are [Fractional] in their [DfracOwn q]. The
   [⊣⊢]-backward direction needs the existential heap struct ([iv] / [yt]) and
   the DLL tail loc ([tl]) to AGREE across the two shares; [own_dll_last_agree]
   supplies the [tl] agreement (both DLLs over the same cells end at the same
   node); [iv]/[yt] agree by [pointsto] agreement. *)
#[global] Instance own_dll_fractional l last prev next cells :
  Fractional (λ q, own_dll (DfracOwn q) l last prev next cells).
Proof.
  intros q1 q2. revert l last prev next.
  induction cells as [|c rest IH]; intros l last prev next; simpl.
  - iSplit; [ iIntros "#H"; iSplit; iFrame "H" | iIntros "[H _]"; iFrame "H" ].
  - iSplit.
    + iIntros "H". iNamed "H".
      iDestruct "Holeft" as "#Holeft". iDestruct "Horight" as "#Horight".
      iDestruct "Hval" as "[Hv1 Hv2]".
      iDestruct (IH with "Hrest") as "[Hr1 Hr2]".
      iSplitL "Hv1 Hr1".
      * iExists iv, olid, orid. iFrame "Hv1 Holeft Horight Hr1". done.
      * iExists iv, olid, orid. iFrame "Hv2 Holeft Horight Hr2". done.
    + iIntros "[H1 H2]".
      iDestruct "H1" as (iv1 olid1 orid1) "H1". iNamedSuffix "H1" "1".
      iDestruct "H2" as (iv2 olid2 orid2) "H2". iNamedSuffix "H2" "2".
      iCombine "Hval1 Hval2" gives %Hiv. subst iv2.
      iCombine "Hval1 Hval2" as "Hval".
      iDestruct (IH with "[$Hrest1 $Hrest2]") as "Hrest".
      iExists iv1, olid1, orid1. iFrame "Hval Hrest Holeft1 Horight1". done.
Qed.

Lemma own_dll_last_agree dq1 dq2 (l la1 la2 prev next : loc) (cells : list item_cell) :
  own_dll dq1 l la1 prev next cells -∗ own_dll dq2 l la2 prev next cells -∗ ⌜la1 = la2⌝.
Proof.
  revert l la1 la2 prev next.
  induction cells as [|c rest IH]; intros l la1 la2 prev next; simpl.
  - iIntros "[%H1a %H1b] [%H2a %H2b]". subst. done.
  - iIntros "H1 H2".
    iDestruct "H1" as (iv1 ol1 or1) "H1". iNamedSuffix "H1" "1".
    iDestruct "H2" as (iv2 ol2 or2) "H2". iNamedSuffix "H2" "2".
    iCombine "Hval1 Hval2" gives %->.
    iApply (IH with "Hrest1 Hrest2").
Qed.

#[global] Instance own_ytype_cells_fractional parent cells arr :
  Fractional (λ q, own_ytype_cells parent (DfracOwn q) cells arr).
Proof.
  intros q1 q2. rewrite /own_ytype_cells. iSplit.
  - iIntros "H". iNamed "H".
    iDestruct "Hparent" as "[Hp1 Hp2]".
    iDestruct (own_dll_fractional _ _ _ _ _ q1 q2 with "Hdll") as "[Hd1 Hd2]".
    iSplitL "Hp1 Hd1".
    + iExists yt, tl. iFrame "Hp1 Hd1". auto.
    + iExists yt, tl. iFrame "Hp2 Hd2". auto.
  - iIntros "[H1 H2]".
    iDestruct "H1" as (yt1 tl1) "H1". iNamedSuffix "H1" "1".
    iDestruct "H2" as (yt2 tl2) "H2". iNamedSuffix "H2" "2".
    iCombine "Hparent1 Hparent2" gives %Hyt. subst yt2.
    iDestruct (own_dll_last_agree with "Hdll1 Hdll2") as %Htl. subst tl2.
    iCombine "Hparent1 Hparent2" as "Hparent".
    iDestruct (own_dll_fractional _ _ _ _ _ q1 q2 with "[$Hdll1 $Hdll2]") as "Hdll".
    iExists yt1, tl1. iFrame "Hparent Hdll". auto.
Qed.

(** [own_item_map] is a function of the document-global (client, clock, loc)
    projection [cell_kp <$> all_cells] alone: two [types] with the same [cell_kp]
    multiset carry the same run-map. [Text.Delete] flips [ic_deleted] bits, which
    leaves every cell's [cell_kp] untouched, so the store's item set is preserved
    verbatim across a delete — this lemma converts the item map from the
    pre-delete [types] to the flipped-cells [types]. *)
Lemma own_item_map_kp_perm (mref : loc) (dq : dfrac) (M1 M2 : gmap loc type_state) :
  cell_kp <$> all_cells M2 ≡ₚ cell_kp <$> all_cells M1 ->
  own_item_map mref dq M1 -∗ own_item_map mref dq M2.
Proof.
  iIntros (Hperm) "Hm". iNamed "Hm".
  have Htwin : ∀ x, x ∈ all_cells M2 → ∃ y, y ∈ all_cells M1 ∧ cell_kp x = cell_kp y.
  { move=> x Hx.
    have Hin : cell_kp x ∈ cell_kp <$> all_cells M2 by apply list_elem_of_fmap_2.
    rewrite Hperm in Hin. apply list_elem_of_fmap in Hin as (y & Hxy & Hy). by exists y. }
  have Hrun : ∀ client, ic_loc <$> client_run M2 client = ic_loc <$> client_run M1 client.
  { move=> client. rewrite /client_run.
    apply merge_sort_loc_perm; [| exact (cell_pr_filter_perm client (all_cells M2) (all_cells M1) Hperm)].
    move=> x1 x2 Hx1 Hx2 H12.
    rewrite list_elem_of_filter in Hx1. rewrite list_elem_of_filter in Hx2.
    destruct (Htwin x1 (proj2 Hx1)) as (y1 & Hy1 & Hkp1).
    rewrite (cell_kp_loc x1 y1 Hkp1).
    apply (Hclkloc y1 x2 Hy1 (proj2 Hx2)).
    - rewrite -(cell_kp_client x1 y1 Hkp1) (proj1 Hx1) (proj1 Hx2) //.
    - rewrite -(cell_kp_pr x1 y1 Hkp1). exact H12. }
  iExists gm. iFrame "Hmap". iSplitL "Hruns".
  - iApply (big_sepM_impl with "Hruns").
    iIntros "!>" (client s Hgm) "H". iNamed "H".
    rewrite (Hrun client). iFrame "Hslice Hcap".
  - iPureIntro. split.
    + move=> c Hc. apply list_elem_of_fmap in Hc as (x & -> & Hx).
      destruct (Htwin x Hx) as (y & Hy & Hkp).
      rewrite (cell_kp_client x y Hkp). apply Hcomplete. apply list_elem_of_fmap_2. exact Hy.
    + move=> c1 c2 Hc1 Hc2 Hcc Hpr.
      destruct (Htwin c1 Hc1) as (y1 & Hy1 & Hkp1).
      destruct (Htwin c2 Hc2) as (y2 & Hy2 & Hkp2).
      rewrite (cell_kp_loc c1 y1 Hkp1) (cell_kp_loc c2 y2 Hkp2).
      apply (Hclkloc y1 y2 Hy1 Hy2).
      * rewrite -(cell_kp_client c1 y1 Hkp1) -(cell_kp_client c2 y2 Hkp2). exact Hcc.
      * rewrite -(cell_kp_pr c1 y1 Hkp1) -(cell_kp_pr c2 y2 Hkp2). exact Hpr.
Qed.

(** The cell-clock bound ([store_inv]'s [Hcellctr]) likewise transfers across a
    [cell_kp]-preserving reshuffle: same client, same clock. *)
Lemma cellctr_kp_perm (M1 M2 : gmap loc type_state) (client k : w64) :
  cell_kp <$> all_cells M2 ≡ₚ cell_kp <$> all_cells M1 ->
  (∀ c, c ∈ all_cells M1 → cell_client c = client → (uint.Z (cell_clock c) < uint.Z k)%Z) ->
  (∀ c, c ∈ all_cells M2 → cell_client c = client → (uint.Z (cell_clock c) < uint.Z k)%Z).
Proof.
  move=> Hperm Hbnd c Hc Hcc.
  have Hin : cell_kp c ∈ cell_kp <$> all_cells M2 by apply list_elem_of_fmap_2.
  rewrite Hperm in Hin. apply list_elem_of_fmap in Hin as (c' & Hkp & Hc').
  rewrite (cell_kp_clock c c' Hkp).
  apply (Hbnd c' Hc'). rewrite -(cell_kp_client c c' Hkp). exact Hcc.
Qed.

(* ----- per-store ghost names and the root-type registry ------------------ *)

(** Per-store ghost names: the item-set authority ([is_type_lb]'s auth) and
    the name↔loc bindings of the root-type registry ([store.types], issue
    #49): a [ghost_map] whose persisted elements are the per-name binding
    witnesses every [is_Text] handle carries. *)
Record store_names := StoreNames {
  sn_seq : gname;    (* authR (gmapUR loc (gsetUR (YjsItem A)))  *)
  sn_types : gname;  (* ghost_map go_string loc                  *)
  sn_wl : gname;     (* [own_wlock]: the exclusive write-lock witness (ghost_var _ 1 ()) *)
  (* --- RWMutex lock layer (reader-count accounting for the concurrent read API) --- *)
  sn_rw : RWMutex_names; (* the logically-atomic RWMutex ghost names             *)
  sn_rmax : gname;   (* own_toks bound: # readers ≤ actualMaxReaders            *)
  sn_rrlocked : gname; (* own_tok_auth: the active reader count                 *)
  sn_types_agree : gname; (* dfrac_agree on the types map (reader/inv agreement) *)
}.

(** The root-type binding: [name] is bound to the type at [p], forever
    (bindings are insert-only — [getOrCreateYType] never rebinds a name).
    Persistent (a discarded ghost-map element), so both [store_inv] and every
    [is_Text] handle carry a copy; combining them under the lock identifies
    the handle's type with the one the registry binds to its name. *)
Definition is_type_binding (γ : gname) (name : P) (p : loc) : iProp Σ :=
  name ↪[γ]□ p.

#[global] Instance is_type_binding_persistent γ name p : Persistent (is_type_binding γ name p).
Proof. apply _. Qed.

Lemma is_type_binding_agree (γ : gname) (name : P) (p q : loc) :
  is_type_binding γ name p -∗ is_type_binding γ name q -∗ ⌜p = q⌝.
Proof.
  iIntros "H1 H2". iDestruct (ghost_map_elem_agree with "H1 H2") as %Heq.
  iPureIntro. exact Heq.
Qed.

(* ----- the lock invariant ----------------------------------------------- *)

(** [store_inv_ro γs types q]: the read-only-shareable slice of [store_inv] that a
    concurrent reader needs: the per-type DLLs (from which [Text.String]/[Len]
    read visible content / length) and the item-set authority (combined with a
    reader's [is_type_lb] to locate its type). Fractional in [q]: the read lock
    hands each of up to [rwmutexMaxReaders] readers a share, and the write lock
    reassembles the whole ([q = 1]). The store's mutable-exclusive parts (the
    struct fields, [own_item_map], the registry [ghost_map_auth], the ghost
    history) are NOT here; they stay whole in the lock invariant while readers
    hold shares, since no writer runs concurrently with readers. *)
(* ----- the decoded update pool (issue #40) --------------------------------
   [own_update_structs] abstracts a heap slice of decoded structs to the model list of
   type-tagged integrate inputs. It lives here (moved from the update proofs)
   because the lock invariant now owns the store's PENDING pool through it. *)

(** A decoded parent name is either absent (Parent::None: borrow from a
    neighbour in [store.repair]) or a read-only string cell (Parent::String).
    Mirrors [is_origin_id]. *)
Definition is_parent_name (p : loc) (opn : option go_string) : iProp Σ :=
  match opn with
  | None => ⌜p = null⌝
  | Some nm => ⌜p ≠ null⌝ ∗ p ↦□ nm
  end.

Global Instance is_parent_name_persistent p opn : Persistent (is_parent_name p opn).
Proof. rewrite /is_parent_name. by destruct opn; apply _. Qed.

(** [is_update_item uiv ti]: the decoded heap struct [uiv] (a [updateItem])
    translates to the model doc-op payload [ti = (tid, input)] -- its id /
    content / both origin pointers map across (origins via [is_origin_id],
    persistent), its content is a single char, and its decoded parent name
    (when present) is the name of the root type [tid] (issue #49; when absent
    the batch-level well-formedness pins [tid] through the origins). *)
Definition is_update_item (uiv : yjs.updateItem.t)
    (ti : TId * IntegrateInput (A := A)) : iProp Σ :=
  ∃ (oleft oright : option yjs.id.t) (opn : option go_string),
    "HisL" ∷ is_origin_id uiv.(yjs.updateItem.originLeftId') oleft ∗
    "HisR" ∷ is_origin_id uiv.(yjs.updateItem.originRightId') oright ∗
    "HisPN" ∷ is_parent_name uiv.(yjs.updateItem.parentName') opn ∗
    "%Hin_l" ∷ ⌜(toYjsId <$> oleft) = in_originId ti.2⌝ ∗
    "%Hin_r" ∷ ⌜(toYjsId <$> oright) = in_rightOriginId ti.2⌝ ∗
    "%Hin_id" ∷ ⌜toYjsId uiv.(yjs.updateItem.id') = in_id ti.2⌝ ∗
    "%Hin_c" ∷ ⌜uiv.(yjs.updateItem.content') = in_content ti.2⌝ ∗
    "%Hulen" ∷ ⌜length uiv.(yjs.updateItem.content') = 1%nat⌝ ∗
    "%Htid" ∷ ⌜∀ nm, opn = Some nm -> ti.1 = RootId nm⌝ ∗
    "%Hborrow" ∷ ⌜opn = None -> in_originId ti.2 ≠ None ∨ in_rightOriginId ti.2 ≠ None⌝.

#[global] Instance is_update_item_persistent uiv ti : Persistent (is_update_item uiv ti).
Proof. rewrite /is_update_item. apply _. Qed.

(** [own_update_structs sl dq inputs]: the heap slice of decoded structs at [sl] (Go
    [Update.structs]) abstracts to the model list [inputs] of type-tagged
    integrate inputs. Owns the backing array (+ cap) at [dq] — [applyUpdate]
    only reads it, so any fraction works — and, per element, the persistent
    [is_update_item]. *)
Definition own_update_structs (sl : slice.t) (dq : dfrac)
    (inputs : list (TId * IntegrateInput (A := A))) : iProp Σ :=
  ∃ (uivs : list yjs.updateItem.t),
    "Hsl" ∷ sl ↦*{dq} uivs ∗
    "Hcap" ∷ own_slice_cap yjs.updateItem.t sl dq ∗
    "Hitems" ∷ ([∗ list] uiv;ti ∈ uivs;inputs, is_update_item uiv ti).


(** [is_root γs name]: persistent witness that the root type [name] is
    registered in the store (bound in the registry to SOME type loc, which
    stays hidden). This is what the [applyUpdate] certificate spec asks for
    per target root, in place of a raw registry lookup; any holder of the
    binding (a [Text] handle, [getOrCreateYType]'s hit path) can mint it. *)
Definition is_root (γs : store_names) (name : P) : iProp Σ :=
  ∃ p : loc, is_type_binding γs.(sn_types) name p.

#[global] Instance is_root_persistent γs name : Persistent (is_root γs name).
Proof. apply _. Qed.

(** [pool_item_rooted]/[is_pool_rooted] (issue #40): every HEAD struct of a
    decoded pool (both origins absent, so it carries its root's name on the
    wire) targets a REGISTERED root. This is the #49 pre-bound-roots
    restriction, kept under the total applyUpdate: structs with an origin
    derive their binding from the origin's arrival at integration time, so
    only head structs need a witness; the store carries it for the pending
    buffer so a later drain can re-discharge it without the caller knowing
    what is buffered. Lifted when [getOrCreateYType]'s miss branch enters the
    verified subset. *)
Definition pool_item_rooted (γs : store_names)
    (ti : TId * IntegrateInput (A := A)) : iProp Σ :=
  if decide (in_originId ti.2 = None ∧ in_rightOriginId ti.2 = None)
  then (∃ nm : P, ⌜ti.1 = RootId nm⌝ ∗ is_root γs nm)%I
  else True%I.

Definition is_pool_rooted (γs : store_names)
    (pool : list (TId * IntegrateInput (A := A))) : iProp Σ :=
  [∗ list] ti ∈ pool, pool_item_rooted γs ti.

#[global] Instance pool_item_rooted_persistent γs ti : Persistent (pool_item_rooted γs ti).
Proof. rewrite /pool_item_rooted. destruct (decide _); apply _. Qed.
#[global] Instance is_pool_rooted_persistent γs pool : Persistent (is_pool_rooted γs pool).
Proof. apply _. Qed.
#[global] Instance pool_item_rooted_timeless γs ti : Timeless (pool_item_rooted γs ti).
Proof. rewrite /pool_item_rooted. destruct (decide _); apply _. Qed.
#[global] Instance is_pool_rooted_timeless γs pool : Timeless (is_pool_rooted γs pool).
Proof. apply _. Qed.

Definition store_inv_ro (γs : store_names) (types : gmap loc type_state) (q : Qp) : iProp Σ :=
  "Hseq" ∷ own γs.(sn_seq) (●{DfracOwn q} ((λ ts, (list_to_set (ty_arr ts) : gset (YjsItem A))) <$> types) : seqUR) ∗
  "Htypes" ∷ ([∗ map] parent ↦ ts ∈ types,
                own_ytype_cells parent (DfracOwn q) (ty_cells ts) (ty_arr ts) ∗
                ⌜YjsArrInvariant (ty_arr ts)⌝ ∗
                (* all-singleton invariant (issue #28): every creator today
                   mints 1-char runs; dropped in M4 with the run-scan bridge *)
                ⌜Forall cell_unit (ty_cells ts)⌝).

#[global] Instance store_inv_ro_fractional γs types : Fractional (store_inv_ro γs types).
Proof.
  rewrite /store_inv_ro /named. apply fractional_sep.
  - intros q1 q2. rewrite -own_op -auth_auth_dfrac_op dfrac_op_own //.
  - apply fractional_big_sepM. intros parent ts.
    apply fractional_sep; [ apply own_ytype_cells_fractional | apply _ ].
Qed.

(** [store_inv_excl]: the complement of [store_inv_ro] within [store_inv], the
    mutable-exclusive state the read lock does NOT share (struct fields, the
    per-client item map, the registry [ghost_map_auth], the ghost history, and
    the counter / registry side conditions). It stays whole in the lock
    invariant while readers hold fractional shares of [store_inv_ro]. *)
Definition store_inv_excl (s_loc : loc) (γs : store_names) (γh : history_names)
    (client k : w64) (items_mref types_mref : loc) (dset : yjs.deletedSet.t)
    (pend_sl : slice.t)
    (types : gmap loc type_state) (bind : gmap P loc) (h : list Ev) (m : DocM)
    (pend : list (TId * IntegrateInput (A := A))) : iProp Σ :=
    "Hclient" ∷ (s_loc .[(yjs.store.t), "client"]) ↦ client ∗
    "Hclock"  ∷ (s_loc .[(yjs.store.t), "clock"]) ↦ k ∗
    "Hitemsf" ∷ (s_loc .[(yjs.store.t), "items"]) ↦ items_mref ∗
    "Hitemmap" ∷ own_item_map items_mref (DfracOwn 1) types ∗
    "Htypesf" ∷ (s_loc .[(yjs.store.t), "types"]) ↦ types_mref ∗
    "Htypesmap" ∷ own_map types_mref (DfracOwn 1) bind ∗
    "Hdset"   ∷ (s_loc .[(yjs.store.t), "deletedSet"]) ↦ dset ∗
    (* the pending pool (issue #40): the buffered structs whose dependencies
       have not arrived, with their certificates (persistent), so the next
       applyUpdate can re-certify the whole drained pool without the caller
       knowing what is buffered. *)
    "Hpendf"  ∷ (s_loc .[(yjs.store.t), "pending"]) ↦ pend_sl ∗
    "Hpend"   ∷ own_update_structs pend_sl (DfracOwn 1) pend ∗
    "#Hpendcert" ∷ is_pool_certified γh pend ∗
    "#Hpendroot" ∷ is_pool_rooted γs pend ∗
    "%Hpendbnd" ∷ ⌜∀ ti : TId * IntegrateInput (A := A), ti ∈ pend ->
                    (Z.of_nat (clock (in_id ti.2)) + 1 < 2^64)%Z⌝ ∗
    "%Hctr"   ∷ ⌜∀ parent ts x, types !! parent = Some ts → x ∈ ty_arr ts →
                   clientId (item_id x) = uint.nat client →
                   (clock (item_id x) < uint.nat k)%nat⌝ ∗
    "%Hcellctr" ∷ ⌜∀ c, c ∈ all_cells types → cell_client c = client →
                   (uint.Z (cell_clock c) < uint.Z k)%Z⌝ ∗
    (* part-6 pool invariants (issue #28): the split branches' index pin *)
    "%Hlocdup" ∷ ⌜NoDup (ic_loc <$> all_cells types)⌝ ∗
    "%Hrangedisj" ∷ ⌜cells_range_disjoint (all_cells types)⌝ ∗
    "HtypesAuth" ∷ ghost_map_auth γs.(sn_types) 1 bind ∗
    "#Hbinds" ∷ ([∗ map] name ↦ p ∈ bind, is_type_binding γs.(sn_types) name p) ∗
    "%Hbindtypes" ∷ ⌜∀ name p, bind !! name = Some p → is_Some (types !! p)⌝ ∗
    "%Hbindinj" ∷ ⌜∀ n1 n2 p, bind !! n1 = Some p → bind !! n2 = Some p → n1 = n2⌝ ∗
    "%Htypesbound" ∷ ⌜∀ p, is_Some (types !! p) → ∃ name, bind !! name = Some p⌝ ∗
    "Hhist"   ∷ own_client_history γh (uint.nat client) h ∗
    "%Hhcoh"  ∷ ⌜history_state_coh h m⌝ ∗
    "%Hmtypes" ∷ ⌜∀ name p ts, bind !! name = Some p → types !! p = Some ts →
                    docm_get m (RootId name) = ty_arr ts⌝ ∗
    "%Hmdom" ∷ ⌜∀ t, docm_get m t ≠ [] →
                  ∃ name p, t = RootId name ∧ bind !! name = Some p⌝.

#[global] Instance store_inv_ro_timeless γs types q : Timeless (store_inv_ro γs types q).
Proof. rewrite /store_inv_ro. apply _. Qed.
#[global] Instance store_inv_excl_timeless s_loc γs γh client k im tm dset psl types bind h m pend :
  Timeless (store_inv_excl s_loc γs γh client k im tm dset psl types bind h m pend).
Proof. rewrite /store_inv_excl /own_update_structs /is_update_item. apply _. Qed.

(** [store_inv s_loc γs γh]: everything the store lock protects.
    - store struct NON-mu fields (client/clock/items/types/deletedSet field ptrs;
      [mu] is owned by the [sync.RWMutex] ([rwmutex.is_RWMutex] in [is_Store]), not here);
    - the item-set authority [own γ (●…)] per type loc (id-set), whose fragments
      are the [is_type_lb] lower bounds / registration witnesses [Text] holds;
    - each registered type's DLL (keyed by [parent]) + [YjsArrInvariant];
    - the store's per-client item set ([own_item_map]: [store.items] holds every
      integrated item's loc, clock-sorted — maintained by Integrate's [AddNode]);
    - the global per-client counter [Hctr] (source of [maximalId]) and its
      cell-level shadow [Hcellctr] (every same-local-client cell across ALL types
      has heap clock [< k]) — what lets [Text.Insert] discharge the wrapper's
      global-max side condition for the OTHER types, whose [cells_repr] is sealed
      in the [big_sepM] accumulator once THIS type is borrowed; re-established at
      each [Unlock] from the loop's carried bound (no [W64] round-trip).
    [client]/[k]/[types] etc. are existential — the fixed lock invariant hides
    the per-operation state. [own_item_map] and [Htypes] share the SAME [types], so
    Insert grows both consistently (DLL splice + [AddNode] tail-append).

    Network layer (issues #42 / #49): the lock also holds this replica's
    exclusive ghost-history element [own_client_history] for the store's
    client. The history's replayed *doc model* [m] is coherent with the whole
    registry, not a single governed type ([history_state_coh h m], plus
    [Hmtypes]: each registered type's [ty_arr] equals [docm_get m] at its
    bound name).

    The body is [store_inv_excl] (the mutable-exclusive clauses, documented
    there) next to [store_inv_ro] at full fraction: exactly the two halves
    the RWMutex tie invariant tracks separately while readers hold shares,
    so [store_inv_bridge] is definitional. *)
Definition store_inv (s_loc : loc) (γs : store_names) (γh : history_names) : iProp Σ :=
  ∃ (client k : w64) (items_mref types_mref : loc) (dset : yjs.deletedSet.t)
    (pend_sl : slice.t)
    (types : gmap loc type_state) (bind : gmap P loc) (h : list Ev) (m : DocM)
    (pend : list (TId * IntegrateInput (A := A))),
    "Hexcl" ∷ store_inv_excl s_loc γs γh client k items_mref types_mref dset pend_sl types bind h m pend ∗
    "Hro"   ∷ store_inv_ro γs types 1.

(** [store_inv] is timeless (heap points-to + ghost state over discrete cameras +
    pure facts), so the write [Lock] wrapper hands it back WITHOUT a [▷] even
    though it is extracted from the tie invariant — the Insert/Delete proofs use
    it immediately (no intervening program step to strip a later). *)
#[global] Instance store_inv_timeless s_loc γs γh : Timeless (store_inv s_loc γs γh).
Proof. rewrite /store_inv. apply _. Qed.

(** [store_inv] partitions into its exclusive part and the read-shareable part
    at full fraction; since the body IS that split, the bridge is definitional
    (kept as a lemma for the lock-layer proofs that rewrite with it). *)
Lemma store_inv_bridge (s_loc : loc) (γs : store_names) (γh : history_names) :
  store_inv s_loc γs γh ⊣⊢
  ∃ client k items_mref types_mref dset pend_sl types bind h m pend,
    store_inv_excl s_loc γs γh client k items_mref types_mref dset pend_sl types bind h m pend ∗
    store_inv_ro γs types 1.
Proof. rewrite /store_inv /named //. Qed.

(** ---------------------------------------------------------------------------
    Store lock = a [sync.RWMutex] (y-octo's [Arc<RwLock<DocStore>>]).

    Writers (Insert/Delete/GetText/applyUpdate) take the write lock; the pure
    readers (String/Len) take the read lock, so concurrent reads are allowed.
    [is_Store] is a PERSISTENT handle built over Perennial's logically-atomic
    RWMutex ([New.proof.sync_proof.rwmutex]): a tying [inv] relates the RWMutex's
    abstract lock state to [store_inv]. The RWMutex ghost names [γrw] are hidden
    (existential) inside [is_Store], so [is_Store]'s signature is unchanged.

    Write path (this port): the write [Lock] linearizes only at [RLocked 0] (no
    readers outstanding), where it can take the WHOLE [store_inv]; [Unlock]
    returns it. So [store_lock_res] maps [RLocked _ ↦ store_inv ∗ own_wlock] and
    [Locked ↦ True]; a writer never observes [RLocked (S _)]. [own_wlock] is the
    exclusive "I hold the write lock" witness (like [own_Mutex]); it makes the
    [Unlock] proof's "not actually locked" case a clean [ghost_var] clash.
    Concurrent readers (the verified String/Len read API) only REFINE the
    [RLocked (S _)] branch to a fractional share of [store_inv]; that is a
    follow-on and does not touch these write proofs. --------------------------- *)

(** The exclusive write-lock witness (mirrors [own_Mutex]). *)
Definition own_wlock (γs : store_names) : iProp Σ :=
  ghost_var γs.(sn_wl) 1 ().

(** ---------- reader-count accounting (concurrent read API) ----------------
    The tie invariant carries [rwmutex_guard]-style accounting so multiple readers
    can each hold a fractional [store_inv_ro] share:
    - [own_tok_auth γs.(sn_rrlocked) n]: the active reader count [n];
    - [own_toks γs.(sn_rmax) n] bounded by the persistent
      [own_tok_auth_dfrac γs.(sn_rmax) □ (max)]: [n ≤ actualMaxReaders], so the
      per-reader fraction stays positive;
    - [types_frag] ([dfrac_agree] on the [types] map) ties the readers' share to
      the store's current [types] (needed to recombine at RUnlock, since the
      item-set auth alone does not determine the [type_state] map);
    - the mutable-exclusive [store_inv_excl] whole + the shared [store_inv_ro] at
      the remaining fraction [frac_of n]. The write [Lock] linearizes at
      [RLocked 0] (fraction 1 = the whole [store_inv] via [store_inv_bridge]);
      each read [RLock] peels off one [rfrac] share. The fraction arithmetic
      mirrors [rwmutex_guard.rfrac]. ------------------------------------------ *)

Definition frac_of (n : nat) : Qp :=
  (pos_to_Qp (Z.to_pos (rwmutex.actualMaxReaders + 1 - Z.of_nat n)) * rwmutex_guard.rfrac)%Qp.

Lemma frac_of_0 : frac_of 0 = 1%Qp.
Proof.
  rewrite /frac_of rwmutex_guard.rfrac_unseal /rwmutex_guard.rfrac_def.
  replace (rwmutex.actualMaxReaders + 1 - Z.of_nat 0)%Z with (rwmutex.actualMaxReaders + 1)%Z by lia.
  rewrite Qp.mul_inv_r //.
Qed.

Lemma frac_of_split (n : nat) : (Z.of_nat n < rwmutex.actualMaxReaders)%Z →
  frac_of n = (rwmutex_guard.rfrac + frac_of (S n))%Qp.
Proof.
  intros Hn. rewrite /frac_of.
  rewrite -{2}(Qp.mul_1_l rwmutex_guard.rfrac) -Qp.mul_add_distr_r. f_equal.
  replace (Z.to_pos (rwmutex.actualMaxReaders + 1 - n))
    with (1 + Z.to_pos (rwmutex.actualMaxReaders + 1 - S n))%positive by lia.
  rewrite pos_to_Qp_add. f_equal.
Qed.

(** Fractional agreement on the [types] map between a reader's share and the
    lock invariant. *)
Definition types_frag (γs : store_names) (q : Qp) (types : gmap loc type_state) : iProp Σ :=
  own γs.(sn_types_agree) (to_frac_agree q (types : leibnizO (gmap loc type_state))).

Lemma tf_split γs q1 q2 types :
  types_frag γs (q1 + q2) types ⊣⊢ types_frag γs q1 types ∗ types_frag γs q2 types.
Proof. rewrite /types_frag -own_op -frac_agree_op //. Qed.

Lemma tf_agree γs q1 q2 t1 t2 : types_frag γs q1 t1 -∗ types_frag γs q2 t2 -∗ ⌜t1 = t2⌝.
Proof.
  iIntros "H1 H2". iCombine "H1 H2" gives %Hv.
  iPureIntro. by apply frac_agree_op_valid_L in Hv as [_ ->].
Qed.

Definition storeN : namespace := nroot .@ "yjs_store".

(** Needed to commute [▷ ∃ st : rwmutex, …] when opening the tie invariant. *)
#[local] Instance rwmutex_inhabited : Inhabited rwmutex := populate Locked.

Definition tie_body (s_loc : loc) (γs : store_names) (γh : history_names) (st : rwmutex) : iProp Σ :=
  match st with
  | Locked => ∃ types, own_tok_auth γs.(sn_rrlocked) 0 ∗ types_frag γs 1 types
  | RLocked n =>
      own_tok_auth γs.(sn_rrlocked) n ∗ own_toks γs.(sn_rmax) n ∗ own_wlock γs ∗
      (∃ client k items_mref types_mref dset pend_sl types bind h m pend,
         types_frag γs (frac_of n) types ∗
         store_inv_excl s_loc γs γh client k items_mref types_mref dset pend_sl types bind h m pend ∗
         store_inv_ro γs types (frac_of n))
  end.

(** Store handle (persistent): the [sync.RWMutex] at [&store.mu] with the
    reader-count accounting invariant. The lock ghost names live in [γs] (see
    [store_names]); ALL store-field / item-set / DLL references are sealed here or
    in [store_inv]. *)
Definition is_Store (s_loc : loc) (γs : store_names) (γh : history_names) : iProp Σ :=
  "#Hrw" ∷ rwmutex.is_RWMutex (s_loc .[(yjs.store.t), "mu"]) γs.(sn_rw) (storeN .@ "rw") ∗
  "#Hmax" ∷ own_tok_auth_dfrac γs.(sn_rmax) DfracDiscarded (Z.to_nat rwmutex.actualMaxReaders) ∗
  "#Htie" ∷ inv (storeN .@ "tie") (∃ st, rwmutex.own_RWMutex γs.(sn_rw) st ∗ tie_body s_loc γs γh st).

(** The read capability (one reader slot) and the post-RLock reader state. *)
Definition own_read_cap (γs : store_names) : iProp Σ :=
  rwmutex.own_RLock_token γs.(sn_rw) ∗ own_toks γs.(sn_rmax) 1.
Definition own_read_locked (γs : store_names) (types : gmap loc type_state) : iProp Σ :=
  own_toks γs.(sn_rrlocked) 1 ∗ types_frag γs rwmutex_guard.rfrac types.

(** [is_type_lb γ parent S]: a persistent SUBSET (membership) lower bound on the
    type at [parent] — [S ⊆] its current item set (of full [YjsItem]s) — AND the
    registration witness (the key [parent] exists in the store's auth). [Insert]
    combines it with [store_inv]'s [Hseq] (auth) under the lock to (a) learn
    [parent ∈ dom types] and extract its DLL, and (b) grow the lower bound. Each
    [x ∈ S] is thereby pinned to a genuine document item, so the sorted [S]
    yields a [sublist] (hence string) lower bound. *)
Definition is_type_lb (γ : gname) (parent : loc) (S : gset (YjsItem A)) : iProp Σ :=
  own γ (◯ {[ parent := S ]} : seqUR).

#[global] Instance is_Store_persistent s_loc γs γh : Persistent (is_Store s_loc γs γh).
Proof. apply _. Qed.
#[global] Instance own_wlock_timeless γs : Timeless (own_wlock γs).
Proof. apply _. Qed.
#[global] Instance is_type_lb_persistent γ parent S : Persistent (is_type_lb γ parent S).
Proof. apply _. Qed.

(* ----- name-keyed public witnesses + the cohesive store-state predicate --- *)

(** [is_root_lb γs name S]: the name-keyed monotone content lower bound,
    i.e. the loc-keyed [is_type_lb] lifted through the persistent binding:
    [S] is a subset of the item set of the root named [name], now and at all
    future times (the item-set authority is grow-only). This is the "how the
    store grew" certificate [applyUpdate] hands back per delivered root. *)
Definition is_root_lb (γs : store_names) (name : P) (S : gset (YjsItem A)) : iProp Σ :=
  ∃ p : loc, is_type_binding γs.(sn_types) name p ∗ is_type_lb γs.(sn_seq) p S.

#[global] Instance is_root_lb_persistent γs name S : Persistent (is_root_lb γs name S).
Proof. apply _. Qed.



(** The store's *registry coherence*: the name->loc bindings [bind], the
    per-type heap state [types], and the replayed doc model [m] fit together:
    every bound name has a live type and vice versa, [bind] is injective, the
    model agrees with each bound type's item list, and the model is populated
    only at bound names. This is exactly the [bind]/[types]/[m] invariant
    [store_inv] maintains inline; naming it keeps [own_store] (and through
    it the [applyUpdate] spec) readable instead of a wall of raw quantified
    side conditions. *)
Definition doc_registry_coh (m : DocM) (bind : gmap P loc)
    (types : gmap loc type_state) : Prop :=
  (∀ nm p, bind !! nm = Some p -> is_Some (types !! p)) /\
  (∀ n1 n2 p, bind !! n1 = Some p -> bind !! n2 = Some p -> n1 = n2) /\
  (∀ p, is_Some (types !! p) -> ∃ nm, bind !! nm = Some p) /\
  (∀ nm p ts, bind !! nm = Some p -> types !! p = Some ts ->
     docm_get m (RootId nm) = ty_arr ts) /\
  (∀ t, docm_get m t ≠ [] -> ∃ nm p, t = RootId nm /\ bind !! nm = Some p).

(** [own_store s γs γh c h m]: the WHOLE lock-protected store state, as one
    exclusive predicate over its public model: this replica is client [c]
    with ghost op history [h], whose replayed doc model is [m]. Everything
    else ([types], [bind], the field locs, the local clock) is existential.
    [store_inv] is exactly its model-existential closure
    ([store_inv_own_store] below), so a lock-holding caller can trade the
    lock body for [own_store] and back; top-level specs over store state
    ([wp_store__applyUpdate_certs]) are stated [own_store] in, [own_store]
    out, per the public-spec rule (no fields, no raw registry maps).

    The per-client counter clause [Hctr] is stated over the MODEL [m] (all
    items of the replayed doc); the W64 cell-level shadow that [store_inv]
    carries ([Hcellctr]) is derivable from it plus the DLL id-bound pins
    (see [store_inv_own_store]), not a separate clause here. *)
Definition own_store (s_loc : loc) (γs : store_names) (γh : history_names)
    (c : ClientId) (h : list Ev) (m : DocM)
    (pend : list (TId * IntegrateInput (A := A))) : iProp Σ :=
  ∃ (client k : w64) (items_mref types_mref : loc) (dset : yjs.deletedSet.t)
    (pend_sl : slice.t)
    (types : gmap loc type_state) (bind : gmap P loc),
    "%Hclientc" ∷ ⌜uint.nat client = c⌝ ∗
    "Hclient" ∷ (s_loc .[(yjs.store.t), "client"]) ↦ client ∗
    "Hclock"  ∷ (s_loc .[(yjs.store.t), "clock"]) ↦ k ∗
    "Hitemsf" ∷ (s_loc .[(yjs.store.t), "items"]) ↦ items_mref ∗
    "Hitemmap" ∷ own_item_map items_mref (DfracOwn 1) types ∗
    "Htypesf" ∷ (s_loc .[(yjs.store.t), "types"]) ↦ types_mref ∗
    "Htypesmap" ∷ own_map types_mref (DfracOwn 1) bind ∗
    "Hdset"   ∷ (s_loc .[(yjs.store.t), "deletedSet"]) ↦ dset ∗
    "Hpendf"  ∷ (s_loc .[(yjs.store.t), "pending"]) ↦ pend_sl ∗
    "Hpend"   ∷ own_update_structs pend_sl (DfracOwn 1) pend ∗
    "#Hpendcert" ∷ is_pool_certified γh pend ∗
    "#Hpendroot" ∷ is_pool_rooted γs pend ∗
    "%Hpendbnd" ∷ ⌜∀ ti : TId * IntegrateInput (A := A), ti ∈ pend ->
                    (Z.of_nat (clock (in_id ti.2)) + 1 < 2^64)%Z⌝ ∗
    "Hseq"    ∷ own γs.(sn_seq) (● ((λ ts, (list_to_set (ty_arr ts) : gset (YjsItem A))) <$> types) : seqUR) ∗
    "Htypes"  ∷ ([∗ map] parent ↦ ts ∈ types,
                  own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
                  ⌜YjsArrInvariant (ty_arr ts)⌝ ∗
                  (* all-singleton invariant (issue #28): dropped in M4 *)
                  ⌜Forall cell_unit (ty_cells ts)⌝) ∗
    "HtypesAuth" ∷ ghost_map_auth γs.(sn_types) 1 bind ∗
    "#Hbinds" ∷ ([∗ map] name ↦ p ∈ bind, is_type_binding γs.(sn_types) name p) ∗
    "Hhist"   ∷ own_client_history γh c h ∗
    "%Hregcoh" ∷ ⌜doc_registry_coh m bind types⌝ ∗
    "%Hhcoh"  ∷ ⌜history_state_coh h m⌝ ∗
    "%Hctr"   ∷ ⌜∀ (t : TId) x, x ∈ docm_get m t -> clientId (item_id x) = c ->
                   (clock (item_id x) < uint.nat k)%nat⌝ ∗
    (* part-6 pool invariants (issue #28): heap-level facts the model does not
       determine, so [own_store] carries them (store_inv ⊣⊢ ∃ own_store) *)
    "%Hlocdup" ∷ ⌜NoDup (ic_loc <$> all_cells types)⌝ ∗
    "%Hrangedisj" ∷ ⌜cells_range_disjoint (all_cells types)⌝.

(* ---- lock-layer compile-time fix -------------------------------------------
   Opening the tie invariant at [RLocked n] hands back [▷ tie_body … (RLocked
   n)], whose payload nests [store_inv_excl ∗ store_inv_ro] (the latter an auth
   plus a [big_sepM] of the DLL fixpoint). Stripping the [▷] off the payload
   conjunct-by-conjunct with those predicates TRANSPARENT makes the [Timeless]
   search unfold that whole structure into its normal form: ~750 s per lock
   proof (wlock / rlock / runlock), i.e. essentially the entire ~37 min compile
   of this file. Instead we strip the later exactly ONCE, off the whole
   [tie_body], via a dedicated instance; sealing [tie_body] for typeclass
   resolution makes that strip a single instance lookup (never unfolding the
   store payload), and [cbn [tie_body]] afterwards still reduces the [match]
   (delta reduction ignores [Typeclasses Opaque]). Only [tie_body] is sealed for
   typeclass resolution (nothing frames into or [iNamed]s it, so this is safe);
   the payload predicates stay transparent so [iFrame] / [iNamed] on them keep
   working (store_inv_init, store_inv_own_store, Insert / Delete). The one-off
   [tie_body_timeless] proof decomposes the [∗]/[∃] by hand so each leaf
   [Timeless] goal is a flat instance lookup (store_inv_excl_timeless etc.);
   letting [apply _] tackle the whole nested goal instead costs ~85 s of TC
   backtracking. Each lock proof drops from ~750 s to sub-second, and the file
   from ~37 min to well under a minute. *)
#[global] Instance types_frag_timeless γs q types : Timeless (types_frag γs q types).
Proof. rewrite /types_frag. apply _. Qed.

#[local] Instance tie_body_timeless s_loc γs γh st : Timeless (tie_body s_loc γs γh st).
Proof.
  destruct st; rewrite /tie_body;
    repeat first [ apply sep_timeless | apply exist_timeless; intros ? ]; apply _.
Qed.

#[global] Typeclasses Opaque tie_body.

(** Write-lock acquire. The write [Lock] linearizes at [RLocked 0] (fraction 1),
    where [store_inv_bridge] reassembles the whole [store_inv]; the invariant is
    left holding [Locked] (which keeps the [types_frag] for the next transition).
    Signature unchanged from the Phase-1 wrapper, so Insert/Delete are untouched. *)
Lemma wp_Store__wlock (s_loc : loc) (γs : store_names) (γh : history_names) :
  {{{ is_pkg_init sync ∗ is_Store s_loc γs γh }}}
    (s_loc .[(yjs.store.t), "mu"]) @! (go.PointerType sync.RWMutex) @! "Lock" #()
  {{{ RET #(); own_wlock γs ∗ store_inv s_loc γs γh }}}.
Proof.
  wp_start_folded as "His". iNamed "His".
  wp_apply (rwmutex.wp_RWMutex__Lock with "[$Hrw]").
  iInv "Htie" as "Hi" "Hclose".
  iDestruct "Hi" as (st) "[>Hown Hbody]".
  iFrame "Hown". iApply fupd_mask_intro; first solve_ndisj. iIntros "Hmask".
  iIntros "%Hst Hlocked". subst st.
  iDestruct "Hbody" as ">Hbody". iEval (cbn [tie_body]) in "Hbody".
  iDestruct "Hbody" as "(Hrauth & Htoks0 & Hwl & Hrest)".
  iDestruct "Hrest" as (client k items_mref types_mref dset pend_sl types bind h m pend) "(Hfrag & Hexcl & Hro)".
  rewrite frac_of_0.
  iMod "Hmask" as "_".
  iMod ("Hclose" with "[Hlocked Hrauth Hfrag]") as "_".
  { iExists Locked. iFrame "Hlocked". iExists types. iFrame "Hrauth Hfrag". }
  iModIntro. iApply "HΦ". iFrame "Hwl".
  iApply store_inv_bridge. iExists client, k, items_mref, types_mref, dset, pend_sl, types, bind, h, m, pend. iFrame "Hexcl Hro".
Qed.

(** Write-lock release. Consumes [own_wlock] and returns [store_inv]; updates the
    lock invariant's [types_frag] to the (possibly changed) current [types] read
    off the returned [store_inv] via the bridge; this is what lets the write
    proofs stay ignorant of the reader accounting. The "invariant is in [RLocked]"
    case (unlock without the lock) is impossible: the [own_wlock] clash. *)
Lemma wp_Store__wunlock (s_loc : loc) (γs : store_names) (γh : history_names) :
  {{{ is_pkg_init sync ∗ is_Store s_loc γs γh ∗ own_wlock γs ∗ ▷ store_inv s_loc γs γh }}}
    (s_loc .[(yjs.store.t), "mu"]) @! (go.PointerType sync.RWMutex) @! "Unlock" #()
  {{{ RET #(); True }}}.
Proof.
  wp_start_folded as "(His & Hwl & HR)". iNamed "His".
  wp_apply (rwmutex.wp_RWMutex__Unlock with "[$Hrw]").
  iInv "Htie" as "Hi" "Hclose".
  iDestruct "Hi" as (st) "[>Hown Hbody]".
  destruct st.
  - iEval (cbn [tie_body]) in "Hbody".
    iDestruct "Hbody" as "(_ & _ & >Hwl2 & _)".
    iDestruct (ghost_var_valid_2 with "Hwl Hwl2") as %[Hbad _].
    exfalso. by apply (Qp.not_add_le_l 1 1).
  - iEval (cbn [tie_body]) in "Hbody".
    iDestruct "Hbody" as (types_old) "(>Hrauth & >Hfrag)".
    iFrame "Hown". iApply fupd_mask_intro; first solve_ndisj. iIntros "Hmask".
    iIntros "Hrl0".
    iMod "Hmask" as "_".
    iMod (own_toks_0 γs.(sn_rmax)) as "Htoks0".
    iEval (rewrite store_inv_bridge) in "HR".
    iDestruct "HR" as (client k items_mref types_mref dset pend_sl types' bind h m pend) "[Hexcl Hro]".
    iMod (own_update _ _ (to_frac_agree 1 (types' : leibnizO _)) with "Hfrag") as "Hfrag".
    { apply cmra_update_exclusive. done. }
    iMod ("Hclose" with "[Hrl0 Hrauth Htoks0 Hwl Hfrag Hexcl Hro]") as "_".
    { iExists (RLocked 0). iFrame "Hrl0". iEval (cbn [tie_body]). iFrame "Hrauth Htoks0 Hwl".
      iExists client, k, items_mref, types_mref, dset, pend_sl, types', bind, h, m, pend.
      rewrite frac_of_0. iFrame "Hfrag Hexcl Hro". }
    iModIntro. by iApply "HΦ".
Qed.

(** Read-lock acquire: peels one [rfrac] share of [store_inv_ro] off the lock
    invariant (bumping the reader count), returning the reader's slot witness
    [own_read_locked] and that share for the specific current [types]. *)
Lemma wp_Store__rlock (s_loc : loc) (γs : store_names) (γh : history_names) :
  {{{ is_pkg_init sync ∗ is_Store s_loc γs γh ∗ own_read_cap γs }}}
    (s_loc .[(yjs.store.t), "mu"]) @! (go.PointerType sync.RWMutex) @! "RLock" #()
  {{{ types, RET #(); own_read_locked γs types ∗ store_inv_ro γs types rwmutex_guard.rfrac }}}.
Proof.
  wp_start_folded as "(His & Hcap)". iNamed "His".
  iDestruct "Hcap" as "[Htok Hmaxtok]".
  wp_apply (rwmutex.wp_RWMutex__RLock with "[$Hrw $Htok]").
  iInv "Htie" as "Hi" "Hclose".
  iDestruct "Hi" as (st) "[>Hown Hbody]".
  iFrame "Hown". iApply fupd_mask_intro; first solve_ndisj. iIntros "Hmask".
  iIntros (n) "%Hst Hrl". subst st.
  iDestruct "Hbody" as ">Hbody". iEval (cbn [tie_body]) in "Hbody".
  iDestruct "Hbody" as "(Hrauth & Hmaxn & Hwl & Hrest)".
  iDestruct "Hrest" as (client k items_mref types_mref dset pend_sl types bind h m pend) "(Hfrag & Hexcl & Hro)".
  iCombine "Hmaxn Hmaxtok" as "Hmaxn1".
  iCombine "Hmax Hmaxn1" gives %Hbound.
  iMod (own_tok_auth_S with "Hrauth") as "[Hrauth Hrtok]".
  assert (Z.of_nat n < rwmutex.actualMaxReaders)%Z as Hlt by (rewrite rwmutex.actualMaxReaders_unseal in Hbound |- *; lia).
  rewrite (frac_of_split n Hlt).
  iDestruct (tf_split with "Hfrag") as "[Hfrag_r Hfrag_i]".
  iDestruct (store_inv_ro_fractional γs types with "Hro") as "[Hro_r Hro_i]".
  iMod "Hmask" as "_".
  iMod ("Hclose" with "[Hrl Hrauth Hmaxn1 Hwl Hfrag_i Hexcl Hro_i]") as "_".
  { iExists (RLocked (S n)). iFrame "Hrl". iEval (cbn [tie_body]).
    replace (S n) with (n + 1)%nat by lia.
    iFrame "Hrauth Hmaxn1 Hwl".
    iExists client, k, items_mref, types_mref, dset, pend_sl, types, bind, h, m, pend.
    iFrame "Hfrag_i Hexcl Hro_i". }
  iModIntro. iApply ("HΦ" $! types). iFrame "Hrtok Hfrag_r Hro_r".
Qed.

(** Read-lock release: returns the reader's [rfrac] share (proving via [tf_agree]
    that the store's [types] is unchanged since the [RLock], so the share
    recombines) and the reader slot; returns [own_read_cap]. *)
Lemma wp_Store__runlock (s_loc : loc) (γs : store_names) (γh : history_names) types_r :
  {{{ is_pkg_init sync ∗ is_Store s_loc γs γh ∗ own_read_locked γs types_r ∗
        store_inv_ro γs types_r rwmutex_guard.rfrac }}}
    (s_loc .[(yjs.store.t), "mu"]) @! (go.PointerType sync.RWMutex) @! "RUnlock" #()
  {{{ RET #(); own_read_cap γs }}}.
Proof.
  wp_start_folded as "(His & Hrlo & Hro_r)". iNamed "His".
  iDestruct "Hrlo" as "[Hrtok Hfrag_r]".
  wp_apply (rwmutex.wp_RWMutex__RUnlock with "[$Hrw]").
  iInv "Htie" as "Hi" "Hclose".
  iDestruct "Hi" as (st) "[>Hown Hbody]".
  destruct st as [nr | ].
  2:{ iEval (cbn [tie_body]) in "Hbody". iDestruct "Hbody" as (types0) "(>Hrauth & _)".
      iCombine "Hrauth Hrtok" gives %Hbad. exfalso. lia. }
  destruct nr as [ | n ].
  { iEval (cbn [tie_body]) in "Hbody". iDestruct "Hbody" as "(>Hrauth & _)".
    iCombine "Hrauth Hrtok" gives %Hbad. exfalso. lia. }
  iDestruct "Hbody" as ">Hbody". iEval (cbn [tie_body]) in "Hbody".
  iDestruct "Hbody" as "(Hrauth & Hmaxsn & Hwl & Hrest)".
  iDestruct "Hrest" as (client k items_mref types_mref dset pend_sl types_i bind h m pend) "(Hfrag_i & Hexcl & Hro_i)".
  iDestruct (tf_agree with "Hfrag_r Hfrag_i") as %->.
  iCombine "Hmax Hmaxsn" gives %Hbound.
  assert (Z.of_nat n < rwmutex.actualMaxReaders)%Z as Hlt by (rewrite rwmutex.actualMaxReaders_unseal in Hbound |- *; lia).
  iExists n. iFrame "Hown".
  iApply fupd_mask_intro; first solve_ndisj. iIntros "Hmask".
  iIntros "[Hrln Htok]".
  iMod "Hmask" as "_".
  iMod (own_tok_auth_delete_S with "Hrauth Hrtok") as "Hrauth".
  iEval (rewrite -Nat.add_1_r) in "Hmaxsn".
  iDestruct (own_toks_add_1 1 n γs.(sn_rmax) with "Hmaxsn") as "[Hmaxn Hmaxtok]".
  iDestruct (tf_split γs rwmutex_guard.rfrac (frac_of (S n)) types_i with "[$Hfrag_r $Hfrag_i]") as "Hfrag".
  iDestruct (store_inv_ro_fractional γs types_i rwmutex_guard.rfrac (frac_of (S n)) with "[$Hro_r $Hro_i]") as "Hro".
  rewrite -(frac_of_split n Hlt).
  iMod ("Hclose" with "[Hrln Hrauth Hmaxn Hwl Hfrag Hexcl Hro]") as "_".
  { iExists (RLocked n). iFrame "Hrln". iEval (cbn [tie_body]). iFrame "Hrauth Hmaxn Hwl".
    iExists client, k, items_mref, types_mref, dset, pend_sl, types_i, bind, h, m, pend.
    iFrame "Hfrag Hexcl Hro". }
  iModIntro. iApply "HΦ". iFrame "Htok Hmaxtok".
Qed.

(** Non-vacuity witness / the [wp_NewDoc] seam: a fresh store's heap fields, a
    fresh empty registered type, and this client's (empty) history element
    assemble into [store_inv] — allocating the store's ghost names and handing
    back the governed-type binding and the empty item-set lower bound. *)
Lemma store_inv_init (s_loc : loc) (γh : history_names) (client k : w64)
    (items_mref types_mref : loc) (dset : yjs.deletedSet.t) :
  "Hclient" ∷ (s_loc .[(yjs.store.t), "client"]) ↦ client -∗
  "Hclock"  ∷ (s_loc .[(yjs.store.t), "clock"]) ↦ k -∗
  "Hitemsf" ∷ (s_loc .[(yjs.store.t), "items"]) ↦ items_mref -∗
  "Hmap"    ∷ own_map items_mref (DfracOwn 1) (∅ : gmap w64 slice.t) -∗
  "Htypesf" ∷ (s_loc .[(yjs.store.t), "types"]) ↦ types_mref -∗
  "Htypesmap" ∷ own_map types_mref (DfracOwn 1) (∅ : gmap P loc) -∗
  "Hdset"   ∷ (s_loc .[(yjs.store.t), "deletedSet"]) ↦ dset -∗
  "Hpendf"  ∷ (s_loc .[(yjs.store.t), "pending"]) ↦ slice.nil -∗
  "Hhist"   ∷ own_client_history γh (uint.nat client) ([] : list Ev) ==∗
  ∃ γs : store_names, store_inv s_loc γs γh.
Proof.
  iIntros "Hclient Hclock Hitemsf Hmap Htypesf Htypesmap Hdset Hpendf Hhist".
  set (types := ∅ : gmap loc type_state).
  iMod (own_alloc (● ((λ ts, (list_to_set (ty_arr ts) : gset (YjsItem A))) <$> types) : seqUR))
    as (γseq) "Hseq".
  { apply auth_auth_valid. rewrite /types fmap_empty //. }
  iMod (ghost_map_alloc_empty (K := P) (V := loc)) as (γtypes) "HtypesAuth".
  (* [sn_wl] names the write-lock witness [own_wlock]; it belongs to the lock
     layer ([is_Store]'s tie invariant), not to [store_inv], so allocate the
     name and drop the token here. *)
  iMod (ghost_var_alloc ()) as (γwl) "Hwl". iClear "Hwl".
  (* The RWMutex-lock-layer ghosts (reader accounting + types agreement) also
     belong to [is_Store]'s tie invariant, not to [store_inv]; allocate the names
     and drop the tokens here (a future [wp_NewDoc] wires the physical lock). The
     RWMutex names are a placeholder record over a fresh dummy gname. *)
  iMod (ghost_var_alloc ()) as (γd) "Hd". iClear "Hd".
  iMod (own_tok_auth_alloc) as (γrmax) "Hrmax". iClear "Hrmax".
  iMod (own_tok_auth_alloc) as (γrrlocked) "Hrrlocked". iClear "Hrrlocked".
  iMod (own_alloc (to_frac_agree 1 (∅ : leibnizO (gmap loc type_state)))) as (γta) "Hta".
  { done. }
  iClear "Hta".
  set (γrw := {| prot_gn := {| read_wait_gn := γd; rlock_overflow_gn := γd;
                               wlock_gn := γd; writer_sem_tok_gn := γd; state_gn := γd |};
                 reader_sem_gn := γd; writer_sem_gn := γd |} : RWMutex_names).
  set (γs := {| sn_seq := γseq; sn_types := γtypes; sn_wl := γwl;
                sn_rw := γrw; sn_rmax := γrmax; sn_rrlocked := γrrlocked;
                sn_types_agree := γta |}).
  iModIntro. iExists γs.
  iExists client, k, items_mref, types_mref, dset, slice.nil, types, (∅ : gmap P loc),
    ([] : list Ev), (∅ : DocM), ([] : list (TId * IntegrateInput (A := A))).
  iSplitR "Hseq"; last first.
  { (* store_inv_ro over the empty types map *)
    iFrame "Hseq". rewrite /types big_sepM_empty //. }
  (* store_inv_excl *)
  iFrame "Hclient Hclock Hitemsf Htypesf Htypesmap Hdset Hpendf Hhist HtypesAuth".
  iSplitL "Hmap".
  { (* own_item_map over the empty run map *)
    iExists (∅ : gmap w64 slice.t). iFrame "Hmap".
    rewrite big_sepM_empty. iSplit; [done |].
    iPureIntro. split.
    - move=> c Hc. exfalso. move: Hc.
      rewrite /types /all_cells map_to_list_empty /= elem_of_nil //.
    - move=> c1 c2 Hc1. exfalso. move: Hc1.
      rewrite /types /all_cells map_to_list_empty /= elem_of_nil //. }
  iSplitR.
  { (* the empty pending pool over the nil slice *)
    iExists []. iSplitR; [iApply own_slice_nil |].
    iSplitR; [iApply own_slice_cap_nil |]. rewrite big_sepL2_nil //. }
  iSplitR.
  { rewrite /is_pool_certified big_sepL_nil //. }
  iSplitR.
  { rewrite /is_pool_rooted big_sepL_nil //. }
  iSplitR.
  { iPureIntro. move=> ti Hin. by apply elem_of_nil in Hin. }
  iSplitR. { iPureIntro. move=> parent' ts' x Hlk. rewrite /types lookup_empty // in Hlk. }
  iSplitR. { iPureIntro. move=> c Hc. exfalso. move: Hc.
    rewrite /types /all_cells map_to_list_empty /= elem_of_nil //. }
  iSplitR. { iPureIntro. rewrite /types /all_cells map_to_list_empty /=. constructor. }
  iSplitR. { iPureIntro. move=> c1 c2 Hc1. exfalso. move: Hc1.
    rewrite /types /all_cells map_to_list_empty /= elem_of_nil //. }
  iSplitR. { rewrite big_sepM_empty //. }
  iPureIntro. split_and!.
  - move=> name p' Hlk. rewrite lookup_empty // in Hlk.
  - move=> n1 n2 p' Hlk. rewrite lookup_empty // in Hlk.
  - move=> p' [ts' Hlk]. rewrite /types lookup_empty // in Hlk.
  - exact history_state_coh_nil.
  - move=> name p' ts' Hlk. rewrite lookup_empty // in Hlk.
  - move=> t Hne. exfalso. apply Hne. rewrite /docm_get lookup_empty //.
Qed.

End store.
