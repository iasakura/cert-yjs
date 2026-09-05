(** store update path, node layer: the id lookups, [wp_getNodeIndex_runs]
    (the binary search over one client's entries) and [wp_store__GetNode_runs]
    (direct, over [own_store_runs]; the cell-level [wp_getNodeIndex] stays
    for [store/splitNode]'s cell body until C6-3 converts it) and the
    applyUpdate input-expansion helpers ([expand_inputs_*],
    [ValidReplay_chunk_extract], the [types_*] accessors). The heavier
    [splitNode] and repair/applyUpdate proofs live in [store/splitNode]
    and [store/repair]; all three reached via the [store/store] facade. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core.
From New.proof Require Import prelude.
From New.proof.id Require Import id.
From New.proof.item Require Import item.
From New.proof.ytype Require Import ytype.
From New.proof.item Require Import run_theory model value heap.
From New.proof Require Import history.
From New.proof.store Require Import model value heap Integrate.
From iris.algebra Require Import auth gmap gset.
From stdpp Require Import sorting.

(* iris.algebra / stdpp.sorting push [nat_scope], retuning the default [<] / [≤].
   The verified WP proofs write [Z] comparisons (e.g. [sint.Z i < …]) unannotated
   and annotate [nat] ones with [%nat], so restore [Z_scope] as the default. *)
Local Open Scope Z_scope.

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

(* [client_run]'s merge_sort instances are [#[local]] in [store/model];
   the run-list lemmas here need them again. *)
#[local] Instance cell_le_dec : RelDecision cell_le.
Proof. rewrite /cell_le. solve_decision. Defined.
#[local] Instance cell_le_trans : Transitive cell_le.
Proof. rewrite /cell_le. move=> x y z. lia. Qed.
#[local] Instance cell_le_total : Total cell_le.
Proof. rewrite /cell_le. move=> x y. lia. Qed.

(** [word] does not use [0 <= Z.of_nat l] on its own, so a [clock + length <
    2^64] bound needs the length-nonneg fact spelled out to recover the
    per-clock [< 2^64] word conversion (issue #28 U7c). Isolated here to keep
    [word] on clean variables. *)
Lemma uint_W64_nat_bound (n l : nat) :
  (Z.of_nat n + Z.of_nat l < 2^64)%Z ->
  uint.Z (W64 n) = Z.of_nat n.
Proof. move=> H. have Hlp : (0 <= Z.of_nat l)%Z by lia. clear -H Hlp. word. Qed.

Lemma uint_W64_nat_add_bound (n l : nat) :
  (Z.of_nat n + Z.of_nat l < 2^64)%Z ->
  (uint.Z (W64 n) + Z.of_nat l < 2^64)%Z.
Proof. move=> H. have Hlp : (0 <= Z.of_nat l)%Z by lia. clear -H Hlp. word. Qed.

(* ===== per-char op expansion of a wire batch (issue #28 U7c) =============
   An n-character wire item denotes n chained per-char ops ([ops_of_input]).
   [expand_inputs] flattens a wire batch into its per-op list; it is just a
   LONGER [list (TId * IntegrateInput)], so the network-model and history
   lemmas ([ValidReplay], [batch_ok], [certs_ValidReplay],
   [history_deliver_batch]) apply to it unchanged. At n = 1 it is the
   identity ([expand_inputs_all_singleton]), so the generalized applyUpdate
   spec strictly refines the single-char one. *)

(** [expand_input] / [expand_inputs] are defined UPSTREAM in [store/model]
    (so [own_store]'s per-char [Hpendcert] can name them); this file only adds
    their theory. *)

(** Flattening a concatenation: [expand_inputs] distributes over [++]. *)
Lemma expand_inputs_app (a b : list (TId * IntegrateInput (A := A))) :
  expand_inputs (a ++ b) = expand_inputs a ++ expand_inputs b.
Proof. rewrite /expand_inputs fmap_app join_app //. Qed.

(** [expand_input] as a plain [fmap] over the item's ops (avoids the beta-redex
    that unfolding the definition leaves in front of [list_lookup_fmap]). *)
Lemma expand_input_lookup (typedInput : TId * IntegrateInput (A := A)) (k : nat)
    (op : IntegrateInput (A := A)) :
  ops_of_input typedInput.2 (explode (in_content typedInput.2)) !! k = Some op ->
  expand_input typedInput !! k = Some (typedInput.1, op).
Proof.
  move=> H.
  change (expand_input typedInput) with
    ((λ op0 : IntegrateInput (A := A), (typedInput.1, op0)) <$> ops_of_input typedInput.2 (explode (in_content typedInput.2))).
  rewrite list_lookup_fmap H //.
Qed.

Lemma expand_input_length (typedInput : TId * IntegrateInput (A := A)) :
  length (expand_input typedInput) = length (in_content typedInput.2).
Proof.
  change (expand_input typedInput) with
    ((λ op0 : IntegrateInput (A := A), (typedInput.1, op0)) <$> ops_of_input typedInput.2 (explode (in_content typedInput.2))).
  rewrite length_fmap /ops_of_input ops_from_length explode_length //.
Qed.

Lemma expand_input_singleton (typedInput : TId * IntegrateInput (A := A)) :
  length (in_content typedInput.2) = 1%nat ->
  expand_input typedInput = [typedInput].
Proof.
  move=> Hlen. rewrite /expand_input (explode_singleton _ Hlen) ops_of_input_singleton /=.
  by destruct typedInput.
Qed.

Lemma expand_inputs_all_singleton (inputs : list (TId * IntegrateInput (A := A))) :
  (forall typedInput, typedInput ∈ inputs -> length (in_content typedInput.2) = 1%nat) ->
  expand_inputs inputs = inputs.
Proof.
  induction inputs as [|typedInput rest IH]; first done.
  move=> Hall.
  have Hti : typedInput ∈ typedInput :: rest by apply elem_of_cons; left.
  rewrite /expand_inputs /= (expand_input_singleton typedInput (Hall typedInput Hti)) /=.
  rewrite -/(expand_inputs rest) IH //.
  move=> typedInput2 Htj. apply Hall, elem_of_cons. by right.
Qed.

(** The heart of the U7c loop rethread: a same-type chunk of a valid replay
    realizes the chained [integrate_all], and peeling it advances the doc by
    that fold. Both directions in one shot. [is_Some (m !! t)] holds in the
    loop (the target type is in the doc), and is what lets the empty-chunk
    base case use [insert_id]. *)
Lemma ValidReplay_chunk_extract (t : TId) (ops : list (IntegrateInput (A := A)))
    (rest : list (TId * IntegrateInput (A := A))) (m m' : DocModel) :
  is_Some (m !! t) ->
  ValidReplay (((λ op, (t, op)) <$> ops) ++ rest) m m' ->
  ∃ arr', integrate_all ops (doc_model_get m t) = Some arr' ∧
          ValidReplay rest (<[t := arr']> m) m'.
Proof.
  revert m. induction ops as [|op ops' IH]; move=> m Hsome Hvr.
  - simpl in Hvr. exists (doc_model_get m t). split; first done.
    destruct Hsome as [arr Harr]. rewrite /doc_model_get Harr /=.
    by rewrite (insert_id _ _ _ Harr).
  - simpl in Hvr.
    inversion Hvr as [| t0 input0 rest0 m0 arr2 m'0 newItem Htoit Hvalid Hmax Hfresh Hint Hvr' Heq1 Heq2 Heq3]; subst.
    have Hsome2 : is_Some ((<[t := arr2]> m) !! t) by rewrite lookup_insert_eq; eauto.
    destruct (IH (<[t := arr2]> m) Hsome2 Hvr') as (arr' & Hia & Hvrrest).
    rewrite docm_get_insert_eq in Hia.
    exists arr'. split.
    + simpl. rewrite Hint /=. exact Hia.
    + have Hii : <[t := arr']> (<[t := arr2]> m) = <[t := arr']> m.
      { rewrite insert_insert. case_decide; [reflexivity | congruence]. }
      rewrite Hii in Hvrrest. exact Hvrrest.
Qed.

(** One loop step's chunk boundary: the [j]-th wire item's ops are the head of
    the remaining flattened batch (issue #28 U7c). *)
Lemma expand_inputs_drop_cons (inputs : list (TId * IntegrateInput (A := A)))
    (j : nat) (typedInput : TId * IntegrateInput (A := A)) :
  inputs !! j = Some typedInput ->
  expand_inputs (drop j inputs) = expand_input typedInput ++ expand_inputs (drop (S j) inputs).
Proof.
  move=> Hj. rewrite (drop_S inputs typedInput j Hj) /expand_inputs /=. done.
Qed.

(** Range-form batch causality (issue #28 U7c): an earlier same-client wire
    item's whole clock range lies below a later item's clock. This strengthens
    the per-op [ValidReplay_batch_causal] (strict [<] on single ops) to the run
    setting, and is what bounds a freshly-integrated RUN cell (occupying the
    range [clock, clock + length)) below the remaining batch. It is derived by
    comparing item [j]'s LAST char op with item [i]'s FIRST char op in the flat
    [expand_inputs] list (they sit at flat positions [Pj < Pi]). *)
Lemma expand_inputs_range_causal (inputs : list (TId * IntegrateInput (A := A)))
    (m m' : DocModel) :
  ValidReplay (expand_inputs inputs) m m' ->
  ∀ (i j : nat) (typedInput typedInput2 : TId * IntegrateInput (A := A)),
    inputs !! i = Some typedInput -> inputs !! j = Some typedInput2 -> (j < i)%nat ->
    clientId (in_id typedInput2.2) = clientId (in_id typedInput.2) ->
    (1 <= length (in_content typedInput2.2))%nat ->
    (1 <= length (in_content typedInput.2))%nat ->
    (clock (in_id typedInput2.2) + length (in_content typedInput2.2) <= clock (in_id typedInput.2))%nat.
Proof.
  move=> Hvr i j typedInput typedInput2 Hi Hj Hji Hcc Hnj Hni.
  set nj := length (in_content typedInput2.2).
  set ls := (expand_input <$> inputs).
  have Hlsj : ls !! j = Some (expand_input typedInput2) by rewrite /ls list_lookup_fmap Hj.
  have Hlsi : ls !! i = Some (expand_input typedInput) by rewrite /ls list_lookup_fmap Hi.
  have Hchj : length (explode (in_content typedInput2.2)) = nj by rewrite explode_length.
  (* item j's last char op *)
  have Hlenj' : (nj - 1 < length (ops_of_input typedInput2.2 (explode (in_content typedInput2.2))))%nat.
  { rewrite /ops_of_input ops_from_length Hchj. lia. }
  destruct (lookup_lt_is_Some_2 _ _ Hlenj') as [lop Hlop].
  have Hlopf := ops_from_lookup _ _ _ _ _ _ _ Hlop.
  have Heplj : expand_input typedInput2 !! (nj - 1)%nat = Some (typedInput2.1, lop)
    := expand_input_lookup typedInput2 (nj - 1)%nat lop Hlop.
  (* item i's first char op *)
  have Hleni' : (0 < length (ops_of_input typedInput.2 (explode (in_content typedInput.2))))%nat.
  { rewrite /ops_of_input ops_from_length explode_length. lia. }
  destruct (lookup_lt_is_Some_2 _ _ Hleni') as [fop Hfop].
  have Hfopf := ops_from_lookup _ _ _ _ _ _ _ Hfop.
  have Hepli : expand_input typedInput !! 0%nat = Some (typedInput.1, fop)
    := expand_input_lookup typedInput 0%nat fop Hfop.
  have Helenj : length (expand_input typedInput2) = nj.
  { rewrite expand_input_length //. }
  (* their flat positions in expand_inputs *)
  set Pj := (sum_list (length <$> take j ls) + (nj - 1))%nat.
  set Pi := (sum_list (length <$> take i ls) + 0)%nat.
  have HPj : expand_inputs inputs !! Pj = Some (typedInput2.1, lop).
  { rewrite /expand_inputs -/ls join_lookup_Some.
    exists j, (expand_input typedInput2), (nj - 1)%nat.
    split_and!; [exact Hlsj | exact Heplj | rewrite /Pj //]. }
  have HPi : expand_inputs inputs !! Pi = Some (typedInput.1, fop).
  { rewrite /expand_inputs -/ls join_lookup_Some.
    exists i, (expand_input typedInput), 0%nat.
    split_and!; [exact Hlsi | exact Hepli | rewrite /Pi //]. }
  (* Pj < Pi: item j's chunk sits entirely before item i's *)
  have Hsplit : take i ls = take (S j) ls ++ drop (S j) (take i ls).
  { rewrite -{1}(take_drop (S j) (take i ls)) take_take Nat.min_l //. }
  have HSj : take (S j) ls = take j ls ++ [expand_input typedInput2]
    by rewrite (take_S_r _ _ _ Hlsj).
  have HPjPi : (Pj < Pi)%nat.
  { rewrite /Pj /Pi Nat.add_0_r Hsplit HSj !fmap_app !sum_list_with_app /=.
    have Hejl := Helenj. lia. }
  (* now the per-op strict causality on the two boundary ops *)
  have Hclientj : clientId (in_id (typedInput2.1, lop).2) = clientId (in_id (typedInput.1, fop).2).
  { simpl. rewrite (proj1 Hlopf) (proj1 Hfopf) /=. exact Hcc. }
  move: (ValidReplay_batch_causal (expand_inputs inputs) m m' Hvr Pi Pj
            (typedInput.1, fop) (typedInput2.1, lop) HPi HPj HPjPi Hclientj) => Hcaus.
  simpl in Hcaus. rewrite (proj1 Hlopf) (proj1 Hfopf) /= in Hcaus. lia.
Qed.

(** Bridge from the per-char [expand_inputs] replay back to WIRE-item freshness
    (issue #28 U7c): an existing same-client item in [m] has a clock strictly
    below wire item [typedInput]'s clock. Proved via [typedInput]'s HEAD char op, which sits in
    [expand_inputs] (flat position [Pi]) and shares [typedInput]'s id, so
    [ValidReplay_arr_fresh] on the expanded replay yields the wire-level bound.
    This is what lets the loop's cell-freshness invariant stay indexed by the
    wire batch [inputs] while the model replay [Hvr] is per-char. *)
Lemma expand_inputs_arr_fresh (inputs : list (TId * IntegrateInput (A := A)))
    (m m' : DocModel) :
  ValidReplay (expand_inputs inputs) m m' ->
  ∀ (i : nat) (typedInput : TId * IntegrateInput (A := A)),
    inputs !! i = Some typedInput ->
    (1 <= length (in_content typedInput.2))%nat ->
    ∀ (t : TId) (x : YjsItem A),
      x ∈ doc_model_get m t ->
      clientId (item_id x) = clientId (in_id typedInput.2) ->
      (clock (item_id x) < clock (in_id typedInput.2))%nat.
Proof.
  move=> Hvr i typedInput Hi Hni t x Hx Hcl.
  set ls := (expand_input <$> inputs).
  have Hlsi : ls !! i = Some (expand_input typedInput) by rewrite /ls list_lookup_fmap Hi.
  have Hleni' : (0 < length (ops_of_input typedInput.2 (explode (in_content typedInput.2))))%nat.
  { rewrite /ops_of_input ops_from_length explode_length. lia. }
  destruct (lookup_lt_is_Some_2 _ _ Hleni') as [fop Hfop].
  have Hfopf := ops_from_lookup _ _ _ _ _ _ _ Hfop.
  have Hepli : expand_input typedInput !! 0%nat = Some (typedInput.1, fop)
    := expand_input_lookup typedInput 0%nat fop Hfop.
  set Pi := (sum_list (length <$> take i ls) + 0)%nat.
  have HPi : expand_inputs inputs !! Pi = Some (typedInput.1, fop).
  { rewrite /expand_inputs -/ls join_lookup_Some.
    exists i, (expand_input typedInput), 0%nat.
    split_and!; [exact Hlsi | exact Hepli | rewrite /Pi //]. }
  have Hfcl : clientId (in_id (typedInput.1, fop).2) = clientId (in_id typedInput.2)
    by simpl; rewrite (proj1 Hfopf) /=.
  have Hfck : clock (in_id (typedInput.1, fop).2) = clock (in_id typedInput.2)
    by simpl; rewrite (proj1 Hfopf) /=; lia.
  have Hcl' : clientId (item_id x) = clientId (in_id (typedInput.1, fop).2)
    := eq_trans Hcl (eq_sym Hfcl).
  have Hlt := ValidReplay_arr_fresh (expand_inputs inputs) m m' Hvr Pi (typedInput.1, fop) HPi t x Hx Hcl'.
  rewrite Hfck in Hlt. exact Hlt.
Qed.

(** [applyUpdate_peel_step]: one loop iteration's replay accounting (issue #28
    U7c). Peel the [j]-th wire item's op chunk off the flat replay, recover its
    head op's scan facts bridged to the wire item ([toItem] / [IsItemValid] /
    [maximalId] over the full-content [newItem], via [toItem_content_swap] /
    [IsItemValid_content_irrel] / [maximalId_id_irrel]), the chained run fold
    [integrate_all (ops_of_input ...)], and the advanced replay for the next
    iteration. *)
Lemma applyUpdate_peel_step (inputs : list (TId * IntegrateInput (A := A))) (j : nat)
    (t : TId) (input : IntegrateInput (A := A)) (mj m' : DocModel) (arrj : list (YjsItem A)) :
  inputs !! j = Some (t, input) ->
  (1 <= length (in_content input))%nat ->
  doc_model_get mj t = arrj ->
  ValidReplay (expand_inputs (drop j inputs)) mj m' ->
  ∃ (newItem : YjsItem A) (arr' : list (YjsItem A)),
    toItem input arrj = Some newItem /\
    IsItemValid newItem /\
    maximalId newItem arrj /\
    integrate_all (ops_of_input input (explode (in_content input))) arrj = Some arr' /\
    ValidReplay (expand_inputs (drop (S j) inputs)) (<[t := arr']> mj) m' /\
    (∀ (t' : TId) x, x ∈ doc_model_get mj t' ->
       clientId (item_id x) = clientId (in_id input) ->
       (clock (item_id x) < clock (in_id input))%nat).
Proof.
  move=> Hj Hne Hdg Hvr.
  rewrite (expand_inputs_drop_cons inputs j (t, input) Hj) in Hvr.
  have Hei : expand_input (t, input)
           = (λ op, (t, op)) <$> ops_of_input input (explode (in_content input)) by done.
  rewrite Hei in Hvr.
  have [ch0 [chrest Hchars]] : ∃ ch0 chrest, explode (in_content input) = ch0 :: chrest.
  { destruct (explode (in_content input)) as [|a b] eqn:E.
    - exfalso. move: Hne. rewrite -(explode_length (in_content input)) E /=. lia.
    - eauto. }
  have Hidin : in_id input = MkYjsId (clientId (in_id input)) (clock (in_id input))
    by (destruct (in_id input); reflexivity).
  set (hop := MkIntegrateInput (in_originId input) (in_rightOriginId input) ch0 (in_id input)).
  set (opstail := ops_from (clientId (in_id input)) (S (clock (in_id input)))
                    (Some (in_id input)) (in_rightOriginId input) chrest).
  have Hopseq : ops_of_input input (ch0 :: chrest) = hop :: opstail.
  { rewrite /ops_of_input /= /hop /opstail -Hidin //. }
  rewrite Hchars Hopseq /= in Hvr.
  inversion Hvr as
    [| t0 hop0 rest0 m0 arr1 mf nit_h Htoith Hvldh Hmaxh Hglob Hinth Hvrtail Heqhd [Heqi Heqa Heqf]];
    subst.
  set (arrj := doc_model_get mj t) in *.
  have Hswaph := toItem_content_swap hop hop arrj nit_h eq_refl eq_refl Htoith.
  rewrite Htoith in Hswaph. injection Hswaph as Hnith.
  have Hidhop : in_id hop = in_id input by rewrite /hop.
  have Hchop : in_content hop = ch0 by rewrite /hop.
  set (newItem := Item (origin nit_h) (rightOrigin nit_h) (in_id input) (in_content input)).
  have Htoit : toItem input arrj = Some newItem.
  { rewrite /newItem. exact (toItem_content_swap hop input arrj nit_h eq_refl eq_refl Htoith). }
  have Hvld : IsItemValid newItem.
  { rewrite /newItem.
    apply (IsItemValid_content_irrel (origin nit_h) (rightOrigin nit_h) (in_id input) ch0 (in_content input)).
    rewrite Hnith in Hvldh. exact Hvldh. }
  have Hidnit : item_id nit_h = item_id newItem.
  { rewrite Hnith /newItem /= //. }
  have Hmaxj : maximalId newItem arrj := maximalId_id_irrel nit_h newItem arrj Hidnit Hmaxh.
  have Hsome1 : is_Some ((<[t := arr1]> mj) !! t) by rewrite lookup_insert_eq; eauto.
  destruct (ValidReplay_chunk_extract t opstail (expand_inputs (drop (S j) inputs))
              (<[t := arr1]> mj) m' Hsome1 Hvrtail) as (arr' & Hiatail & Hvrrest).
  rewrite docm_get_insert_eq in Hiatail.
  exists newItem, arr'. split_and!.
  - exact Htoit.
  - exact Hvld.
  - exact Hmaxj.
  - rewrite Hchars Hopseq /= Hinth /=. exact Hiatail.
  - have Hii : <[t := arr']> (<[t := arr1]> mj) = <[t := arr']> mj.
    { rewrite insert_insert. case_decide; [reflexivity | congruence]. }
    rewrite Hii in Hvrrest. exact Hvrrest.
  - (* the [VR_cons] client bound of the chunk's HEAD char, which carries the
       wire item's own id: every item of [mj] from this client sits strictly
       below it, so none of the chunk's chars (all at clocks at or above it)
       is already in the model *)
    move=> t' x Hx Hcx. exact (Hglob t' x Hx Hcx).
Qed.

(* ===== applyUpdate (doc-level, #49): store-wide node lookup ==============
   [store.repair] resolves a decoded struct's origins through the store-wide
   [GetNode] (per-client clock-sorted run lists + binary search) instead of
   walking one type's DLL. The heap cells backing the probes live in the
   per-type DLLs, so the lookup specs borrow single cells out of the
   document-wide big-sep (what [store_inv] holds as [Htypes]) via
   [own_type_pool_acc]. *)

(** A client run holds exactly the pool's cells with that client tag. *)
Lemma client_run_mem (types : gmap loc type_state) (kc : w64) (c : item_cell) :
  c ∈ client_run types kc <-> (c ∈ all_cells types /\ cell_client c = kc).
Proof.
  rewrite /client_run (merge_sort_Permutation cell_le _) list_elem_of_filter. tauto.
Qed.

(** The run is clock-sorted (definitional: [merge_sort]). *)
Lemma client_run_sorted (types : gmap loc type_state) (kc : w64) :
  StronglySorted cell_le (client_run types kc).
Proof. apply StronglySorted_merge_sort; apply _. Qed.

(** Sortedness, index form. *)
Lemma StronglySorted_lookup_le {D : Type} (R : D -> D -> Prop) (l : list D)
    (i j : nat) (x y : D) :
  StronglySorted R l -> l !! i = Some x -> l !! j = Some y -> (i < j)%nat -> R x y.
Proof.
  move=> Hss Hi Hj Hij.
  have Hss' : StronglySorted R (take (S i) l ++ drop (S i) l) by rewrite take_drop.
  apply (StronglySorted_app_1_elem_of _ (take (S i) l) (drop (S i) l) x y Hss').
  - apply (list_elem_of_lookup_2 _ i). rewrite lookup_take_lt; [exact Hi | lia].
  - apply (list_elem_of_lookup_2 _ (j - S i)%nat). rewrite lookup_drop.
    have -> : (S i + (j - S i))%nat = j by lia. exact Hj.
Qed.





(** [getNodeIndex] (binary search over one client's clock-sorted run), raw
    form: [ok] iff some run cell's clock range [cell_clock, cell_clock + len)
    covers [clk] (issue #40 x issue #28 U7c). Index-wise range-disjointness of
    the run ([Hidisj]) makes the covering cell unique so the binary search
    corners it; the empty-window exit certifies that no run cell covers [clk].
    Local: [wp_getNodeIndex] restates it over [sorted_client_run]. *)
#[local] Lemma wp_getNodeIndex_raw (sl : slice.t) (dq : dfrac) (types : gmap loc type_state)
    (run : list item_cell) (clk : w64) :
  StronglySorted cell_le run ->
  (∀ c, c ∈ run -> c ∈ all_cells types) ->
  (∀ c, c ∈ run -> (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) < 2^64)%Z) ->
  (∀ (k1 k2 : nat) (c1 c2 : item_cell),
     run !! k1 = Some c1 -> run !! k2 = Some c2 -> k1 ≠ k2 ->
     (uint.Z (cell_clock c1) + Z.of_nat (length (ic_run c1)) <= uint.Z (cell_clock c2))%Z ∨
     (uint.Z (cell_clock c2) + Z.of_nat (length (ic_run c2)) <= uint.Z (cell_clock c1))%Z) ->
  {{{ is_pkg_init yjs ∗ sl ↦*{dq} (ic_loc <$> run) ∗
      (own_type_pool (DfracOwn 1) types) }}}
    @! yjs.getNodeIndex #sl #clk
  {{{ (i : w64) (ok : bool), RET (#i, #ok);
      sl ↦*{dq} (ic_loc <$> run) ∗
      (own_type_pool (DfracOwn 1) types) ∗
      ⌜if ok then ∃ c, run !! uint.nat i = Some c ∧
             (uint.Z (cell_clock c) <= uint.Z clk)%Z ∧
             (uint.Z clk < uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)))%Z
       else ∀ (k : nat) (c : item_cell), run !! k = Some c ->
             (uint.Z (cell_clock c) <= uint.Z clk)%Z ->
             (uint.Z clk < uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)))%Z -> False⌝ }}}.
Proof using Type*.
  move=> Hsort Hmem Hrunfits Hidisj.
  wp_start as "(Hsl & Htypes)".
  iDestruct (own_slice_len with "Hsl") as %[Hsllen Hsllen0].
  rewrite length_fmap in Hsllen Hsllen0.
  wp_auto.
  (* loop invariant: the window [lo, hi) contains every COVERING cell *)
  iAssert (∃ (lo hi : w64),
    "Hleft" ∷ left_ptr ↦ lo ∗ "Hright" ∷ right_ptr ↦ hi ∗
    "Hnodes" ∷ nodes_ptr ↦ sl ∗ "Hclock" ∷ clock_ptr ↦ clk ∗
    "Hsl" ∷ sl ↦*{dq} (ic_loc <$> run) ∗
    "Htypes" ∷ (own_type_pool (DfracOwn 1) types) ∗
    "%Hbnd" ∷ ⌜(0 <= uint.Z lo /\ uint.Z hi <= Z.of_nat (length run))%Z⌝ ∗
    "%Hwin" ∷ ⌜∀ (k : nat) (c : item_cell), run !! k = Some c ->
                (uint.Z (cell_clock c) <= uint.Z clk)%Z ->
                (uint.Z clk < uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)))%Z ->
                (uint.Z lo <= Z.of_nat k < uint.Z hi)%Z⌝)%I
    with "[left right nodes clock Hsl Htypes]" as "IH".
  { iExists (W64 0), sl.(slice.len).
    iFrame "left right nodes clock Hsl Htypes".
    iPureIntro. split; [word |].
    move=> k c Hk _ _. have Hklt := lookup_lt_Some _ _ _ Hk. word. }
  wp_for "IH".
  case_bool_decide as Hcond.
  - (* probe the middle *)
    set (mid := word.add lo (word.divu (word.sub hi lo) (W64 2))).
    have Hmid : (uint.Z lo <= uint.Z mid < uint.Z hi)%Z.
    { rewrite /mid. destruct Hbnd as [Hb1 Hb2]. word. }
    wp_auto.
    rewrite decide_True; last word.
    have Hmidlt : (uint.nat mid < length run)%nat by word.
    destruct (run !! uint.nat mid) as [cmid|] eqn:Hcmid;
      last by (apply lookup_ge_None in Hcmid; lia).
    have Hlocmid : (ic_loc <$> run) !! uint.nat mid = Some cmid.(ic_loc)
      by rewrite list_lookup_fmap Hcmid //.
    iDestruct (own_slice_elem_acc (sint.Z mid) (ic_loc cmid) sl dq (ic_loc <$> run) with "Hsl") as "[Hel Hgive]".
    { word. }
    { replace (Z.to_nat (sint.Z mid)) with (uint.nat mid) by word. exact Hlocmid. }
    wp_auto.
    iDestruct ("Hgive" $! cmid.(ic_loc) with "Hel") as "Hsl".
    have Hinsid : (<[sint.nat mid := cmid.(ic_loc)]> (ic_loc <$> run)) = (ic_loc <$> run).
    { apply list_insert_id. replace (sint.nat mid) with (uint.nat mid) by word. exact Hlocmid. }
    iEval (rewrite Hinsid) in "Hsl".
    have Hcmemall : cmid ∈ all_cells types
      by (apply Hmem; exact (list_elem_of_lookup_2 _ _ _ Hcmid)).
    iDestruct (own_type_pool_acc types cmid Hcmemall with "Htypes") as "Hacc".
    iNamed "Hacc".
    wp_auto.
    have Hmcv : cell_clock cmid = itemVal.(yjs.item.id').(yjs.id.clock')
      by (rewrite /cell_clock Hid /toYjsId /=; word).
    have HlenEq : length (itemVal.(yjs.item.content').(yjs.content.content')) = length (ic_run cmid).
    { have H := f_equal length Hcontent.
      rewrite length_fmap explode_length /toContent in H. lia. }
    have Hlenpos : (1 <= Z.of_nat (length (ic_run cmid)))%Z.
    { have [Hne _] := Hrun. destruct (ic_run cmid) as [|? ?]; [done | simpl; lia]. }
    have Hnw : (uint.Z (cell_clock cmid) + Z.of_nat (length (ic_run cmid)) < 2^64)%Z
      by (apply Hrunfits; exact (list_elem_of_lookup_2 _ _ _ Hcmid)).
    wp_apply (wp_item__Len cmid.(ic_loc) (DfracOwn 1) itemVal with "[$Hval]"). iIntros "Hval".
    rewrite HlenEq.
    iDestruct ("Hback" with "Hval") as "Htypes".
    wp_auto.
    destruct (bool_decide (uint.Z clk < uint.Z itemVal.(yjs.item.id').(yjs.id.clock'))) eqn:Hcmp1.
    + (* clk < middleClock: every covering cell sits strictly left of [mid] *)
      apply bool_decide_eq_true_1 in Hcmp1.
      wp_auto. wp_for_post.
      iFrame "HΦ". iExists lo, mid.
      iFrame "Hleft Hright Hnodes Hclock Hsl Htypes".
      iPureIntro. split.
      { lia. }
      move=> k c Hk Hcov1 Hcov2.
      have [Hlo Hhi] := Hwin k c Hk Hcov1 Hcov2.
      split; [exact Hlo |].
      destruct (Nat.lt_trichotomy k (uint.nat mid)) as [Hlt | [Heq | Hgt]].
      * lia.
      * exfalso. subst k. rewrite Hcmid in Hk. injection Hk as <-.
        rewrite Hmcv in Hcov1. lia.
      * exfalso.
        have Hle := StronglySorted_lookup_le cell_le run (uint.nat mid) k cmid c Hsort Hcmid Hk Hgt.
        rewrite /cell_le Hmcv in Hle. lia.
    + apply bool_decide_eq_false_1 in Hcmp1.
      rewrite Hmcv in Hnw.
      wp_auto.
      case_bool_decide as Hcmp2.
      * (* clk >= middleEnd: every covering cell sits strictly right of [mid] *)
        wp_auto. wp_for_post.
        iFrame "HΦ". iExists (word.add mid (W64 1)), hi.
        iFrame "Hleft Hright Hnodes Hclock Hsl Htypes".
        have Hmide : (uint.Z (w64_word_instance.(word.add) itemVal.(yjs.item.id').(yjs.id.clock') (W64 (length (ic_run cmid))))
                      = uint.Z itemVal.(yjs.item.id').(yjs.id.clock') + Z.of_nat (length (ic_run cmid)))%Z by word.
        rewrite Hmide in Hcmp2.
        iPureIntro. split.
        { word. }
        move=> k c Hk Hcov1 Hcov2.
        have [Hlo Hhi] := Hwin k c Hk Hcov1 Hcov2.
        split; [| exact Hhi].
        destruct (Nat.lt_trichotomy k (uint.nat mid)) as [Hlt | [Heq | Hgt]].
        { exfalso.
          have Hle := StronglySorted_lookup_le cell_le run k (uint.nat mid) c cmid Hsort Hk Hcmid Hlt.
          rewrite /cell_le Hmcv in Hle.
          destruct (Hidisj k (uint.nat mid) c cmid Hk Hcmid ltac:(lia)) as [Hd | Hd];
            rewrite Hmcv in Hd; lia. }
        { exfalso. subst k. rewrite Hcmid in Hk. injection Hk as <-.
          rewrite Hmcv in Hcov2. lia. }
        word.
      * (* middleClock <= clk < middleEnd: the probe COVERS clk *)
        wp_auto. wp_for_post.
        iApply ("HΦ" $! mid true). iFrame "Hsl Htypes".
        iExists cmid. iPureIntro. split; [exact Hcmid |].
        split; rewrite Hmcv; word.
  - (* the window is empty: no run cell covers [clk] *)
    wp_auto.
    iApply ("HΦ" $! (W64 0) false). iFrame "Hsl Htypes".
    iPureIntro. move=> k c Hk Hcov1 Hcov2.
    have := Hwin k c Hk Hcov1 Hcov2. lia.
Qed.

(** [getNodeIndex]: search one client's run ([sorted_client_run]) for the cell
    whose clock range covers [clk]; [ok = false] certifies no cell of the run
    does. The pool invariants give the range disjointness the search relies on. *)
Lemma wp_getNodeIndex (sl : slice.t) (dq : dfrac) (types : gmap loc type_state)
    (kc : w64) (run : list item_cell) (clk : w64) :
  sorted_client_run types kc run ->
  pool_invs types ->
  {{{ is_pkg_init yjs ∗ sl ↦*{dq} (ic_loc <$> run) ∗ own_type_pool (DfracOwn 1) types }}}
    @! yjs.getNodeIndex #sl #clk
  {{{ (i : w64) (ok : bool), RET (#i, #ok);
      sl ↦*{dq} (ic_loc <$> run) ∗ own_type_pool (DfracOwn 1) types ∗
      ⌜if ok then ∃ c, run !! uint.nat i = Some c ∧ cell_covers_clock c (uint.nat clk)
       else ∀ c, c ∈ run -> ¬ cell_covers_clock c (uint.nat clk)⌝ }}}.
Proof using Type*.
  move=> [Hss [Hnd Hmem]] [Hfits [Hnodup [Hrangedisj _]]].
  iIntros (Φ) "(#Hpkg & Hslice & Htypes) HΦ".
  iDestruct (own_type_pool_id_bounds with "Htypes") as %Hbnds.
  have Hmemall : ∀ c, c ∈ run -> c ∈ all_cells types
    := λ c Hc, proj1 (proj1 (client_run_mem types kc c) (Hmem c Hc)).
  have Hfits' : ∀ c, c ∈ run -> (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) < 2^64)%Z
    := λ c Hc, Hfits c (Hmemall c Hc).
  have Hidisj : ∀ (k1 k2 : nat) (c1 c2 : item_cell),
      run !! k1 = Some c1 -> run !! k2 = Some c2 -> k1 ≠ k2 ->
      (uint.Z (cell_clock c1) + Z.of_nat (length (ic_run c1)) <= uint.Z (cell_clock c2))%Z ∨
      (uint.Z (cell_clock c2) + Z.of_nat (length (ic_run c2)) <= uint.Z (cell_clock c1))%Z.
  { move=> k1 k2 c1 c2 Hk1 Hk2 Hkne.
    have Hc1r := list_elem_of_lookup_2 _ _ _ Hk1.
    have Hc2r := list_elem_of_lookup_2 _ _ _ Hk2.
    have Hlocne : ic_loc c1 ≠ ic_loc c2.
    { move=> Heq.
      have Hl1 : (ic_loc <$> run) !! k1 = Some (ic_loc c2) by rewrite list_lookup_fmap Hk1 /= Heq.
      have Hl2 : (ic_loc <$> run) !! k2 = Some (ic_loc c2) by rewrite list_lookup_fmap Hk2.
      exact (Hkne (NoDup_lookup _ _ _ _ Hnd Hl1 Hl2)). }
    apply (Hrangedisj c1 c2 (Hmemall c1 Hc1r) (Hmemall c2 Hc2r)); [| exact Hlocne].
    rewrite (proj2 (proj1 (client_run_mem types kc c1) (Hmem c1 Hc1r)))
            (proj2 (proj1 (client_run_mem types kc c2) (Hmem c2 Hc2r))) //. }
  wp_apply (wp_getNodeIndex_raw sl dq types run clk Hss Hmemall Hfits' Hidisj
              with "[$Hpkg $Hslice $Htypes]").
  iIntros (i ok) "(Hslice & Htypes & %Hres)".
  iApply ("HΦ" $! i ok). iFrame "Hslice Htypes". iPureIntro.
  destruct ok.
  - destruct Hres as (c & Hc & Hle & Hlt). exists c. split; [exact Hc |].
    have Hb := proj2 (Hbnds c (Hmemall c (list_elem_of_lookup_2 _ _ _ Hc))).
    rewrite /cell_clock in Hle Hlt. rewrite /cell_covers_clock. split; word.
  - move=> c Hc [Hle Hlt].
    apply list_elem_of_lookup_1 in Hc as [kx Hkx].
    have Hb := proj2 (Hbnds c (Hmemall c (list_elem_of_lookup_2 _ _ _ Hkx))).
    apply (Hres kx c Hkx); rewrite /cell_clock; word.
Qed.

(** [getNodeIndex] over one client's entries ([client_entries]), the run
    form of [wp_getNodeIndex]: [ok] iff some entry's run covers [clk]
    ([run_covers_clock]); the clock ranges of distinct entries are disjoint
    ([client_entries_disjoint]), so the binary search corners the covering
    one, and the empty-window exit certifies that no entry covers [clk]. *)
Lemma wp_getNodeIndex_runs (sl : slice.t) (dq : dfrac) (locs : gmap loc (list loc)) (p : pool)
    (kc clk : w64) (E : list (loc * ItemRun)) :
  run_pool_invs p ->
  sorted_client_entries locs p kc E ->
  {{{ is_pkg_init yjs ∗ sl ↦*{dq} E.*1 ∗ own_type_pool_runs (DfracOwn 1) locs p }}}
    @! yjs.getNodeIndex #sl #clk
  {{{ (i : w64) (ok : bool), RET (#i, #ok);
      sl ↦*{dq} E.*1 ∗ own_type_pool_runs (DfracOwn 1) locs p ∗
      ⌜if ok then ∃ l r, E !! uint.nat i = Some (l, r) ∧ run_covers_clock r (uint.nat clk)
       else ∀ l r, (l, r) ∈ E -> ¬ run_covers_clock r (uint.nat clk)⌝ }}}.
Proof using Type*.
  move=> Hrpi Hsce.
  wp_start as "(Hsl & Htypes)".
  iAssert (⌜locs_wf locs p⌝)%I as %Hlocswf; first by iDestruct "Htypes" as "[%Hwf _]".
  destruct Hlocswf as (Hdom & Hnd & Hlens).
  have Hlens' : ∀ parent tm, p !! parent = Some tm ->
      ∃ ls, locs !! parent = Some ls ∧ length ls = length (tm_runs tm).
  { move=> parent tm Hp.
    have His : is_Some (locs !! parent).
    { apply elem_of_dom. rewrite Hdom. apply elem_of_dom. by exists tm. }
    destruct His as [ls Hls]. exists ls. split; [done | exact (Hlens parent ls tm Hls Hp)]. }
  iDestruct (own_type_pool_runs_id_bounds with "Htypes") as %Hbnds.
  iDestruct (own_type_pool_runs_run_wf with "Htypes") as %Hwfall.
  have [Hfits [Hdisj _]] := Hrpi.
  have Hsort : StronglySorted entry_le E := proj1 Hsce.
  have Hndl : NoDup (pool_entries locs p).*1 := pool_entries_locs_NoDup locs p Hdom Hlens' Hnd.
  have Hidisj := sorted_client_entries_disjoint locs p kc E Hdom Hlens' Hndl (λ r Hr, proj1 (Hbnds r Hr)) Hdisj Hsce.
  have Hlookup_slot : ∀ k l r, E !! k = Some (l, r) ->
      ∃ parent ls tm k', locs !! parent = Some ls ∧ p !! parent = Some tm ∧ ls !! k' = Some l ∧ tm_runs tm !! k' = Some r.
  { move=> k l r Hk. apply pool_entries_slot.
    exact (proj1 (proj2 (proj2 Hsce) _ (list_elem_of_lookup_2 _ _ _ Hk))). }
  have Hslot : ∀ k l r, E !! k = Some (l, r) -> r ∈ all_runs p.
  { move=> k l r Hk.
    destruct (Hlookup_slot k l r Hk) as (parent & ls & tm & k' & Hls & Hp & Hl & Hr).
    apply elem_of_all_runs. exists parent, tm. split; [exact Hp | exact (list_elem_of_lookup_2 _ _ _ Hr)]. }
  have Hclk : ∀ k l r, E !! k = Some (l, r) -> uint.Z (entry_clock (l, r)) = Z.of_nat (run_clock r).
  { move=> k l r Hk. apply entry_clock_Z. exact (proj2 (Hbnds r (Hslot k l r Hk))). }
  iDestruct (own_slice_len with "Hsl") as %[Hsllen Hsllen0].
  rewrite length_fmap in Hsllen Hsllen0.
  wp_auto.
  (* loop invariant: the window [lo, hi) contains every COVERING entry *)
  iAssert (∃ (lo hi : w64),
    "Hleft" ∷ left_ptr ↦ lo ∗ "Hright" ∷ right_ptr ↦ hi ∗
    "Hnodes" ∷ nodes_ptr ↦ sl ∗ "Hclock" ∷ clock_ptr ↦ clk ∗
    "Hsl" ∷ sl ↦*{dq} E.*1 ∗
    "Htypes" ∷ own_type_pool_runs (DfracOwn 1) locs p ∗
    "%Hbnd" ∷ ⌜(0 <= uint.Z lo /\ uint.Z hi <= Z.of_nat (length E))%Z⌝ ∗
    "%Hwin" ∷ ⌜∀ (k : nat) (l : loc) (r : ItemRun), E !! k = Some (l, r) ->
                (Z.of_nat (run_clock r) <= uint.Z clk)%Z ->
                (uint.Z clk < Z.of_nat (run_clock r) + Z.of_nat (length (run_items r)))%Z ->
                (uint.Z lo <= Z.of_nat k < uint.Z hi)%Z⌝)%I
    with "[left right nodes clock Hsl Htypes]" as "IH".
  { iExists (W64 0), sl.(slice.len).
    iFrame "left right nodes clock Hsl Htypes".
    iPureIntro. split; [word |].
    move=> k l r Hk _ _. have Hklt := lookup_lt_Some _ _ _ Hk. word. }
  wp_for "IH".
  case_bool_decide as Hcond.
  - (* probe the middle *)
    set (mid := word.add lo (word.divu (word.sub hi lo) (W64 2))).
    have Hmid : (uint.Z lo <= uint.Z mid < uint.Z hi)%Z.
    { rewrite /mid. destruct Hbnd as [Hb1 Hb2]. word. }
    wp_auto.
    rewrite decide_True; last word.
    have Hmidlt : (uint.nat mid < length E)%nat by word.
    destruct (E !! uint.nat mid) as [[lmid rmid]|] eqn:Hemid;
      last by (apply lookup_ge_None in Hemid; lia).
    have Hlocmid : E.*1 !! uint.nat mid = Some lmid
      by rewrite list_lookup_fmap Hemid //.
    iDestruct (own_slice_elem_acc (sint.Z mid) lmid sl dq E.*1 with "Hsl") as "[Hel Hgive]".
    { word. }
    { replace (Z.to_nat (sint.Z mid)) with (uint.nat mid) by word. exact Hlocmid. }
    wp_auto.
    iDestruct ("Hgive" $! lmid with "Hel") as "Hsl".
    have Hinsid : (<[sint.nat mid := lmid]> E.*1) = E.*1.
    { apply list_insert_id. replace (sint.nat mid) with (uint.nat mid) by word. exact Hlocmid. }
    iEval (rewrite Hinsid) in "Hsl".
    destruct (Hlookup_slot (uint.nat mid) lmid rmid Hemid)
      as (parent & ls & tm & km & Hls & Hp & Hlk & Hrk).
    iDestruct (own_type_pool_runs_node_acc locs p parent ls tm km lmid rmid Hls Hp Hlk Hrk with "Htypes")
      as (itemVal) "Hacc". iNamed "Hacc".
    wp_auto.
    have Hrmid : rmid ∈ all_runs p := Hslot _ _ _ Hemid.
    have Hfitsm : run_fits rmid := Hfits rmid Hrmid.
    have Hwfm : run_wf (run_items rmid) := Hwfall rmid Hrmid.
    have Hmcv : uint.Z itemVal.(yjs.item.id').(yjs.id.clock') = Z.of_nat (run_clock rmid).
    { rewrite /run_clock Haccid /toYjsId /=. word. }
    have Hlenpos : (1 <= Z.of_nat (length (run_items rmid)))%Z.
    { have [Hne _] := Hwfm. destruct (run_items rmid) as [|? ?]; [done | simpl; lia]. }
    have Hnw : (Z.of_nat (run_clock rmid) + Z.of_nat (length (run_items rmid)) < 2^64)%Z := Hfitsm.
    wp_apply (wp_item__Len lmid (DfracOwn 1) itemVal with "[$Haccval]"). iIntros "Haccval".
    rewrite Haccle.
    iDestruct ("Haccback" with "Haccval") as "Htypes".
    wp_auto.
    destruct (bool_decide (uint.Z clk < uint.Z itemVal.(yjs.item.id').(yjs.id.clock'))) eqn:Hcmp1.
    + (* clk < middleClock: every covering entry sits strictly left of [mid] *)
      apply bool_decide_eq_true_1 in Hcmp1.
      wp_auto. wp_for_post.
      iFrame "HΦ". iExists lo, mid.
      iFrame "Hleft Hright Hnodes Hclock Hsl Htypes".
      iPureIntro. split.
      { lia. }
      move=> k l r Hk Hcov1 Hcov2.
      have [Hlo Hhi] := Hwin k l r Hk Hcov1 Hcov2.
      split; [exact Hlo |].
      destruct (Nat.lt_trichotomy k (uint.nat mid)) as [Hlt | [Heq | Hgt]].
      * lia.
      * exfalso. subst k. rewrite Hemid in Hk. injection Hk as <- <-.
        rewrite Hmcv in Hcmp1. lia.
      * exfalso.
        have Hle := StronglySorted_lookup_le entry_le E (uint.nat mid) k (lmid, rmid) (l, r) Hsort Hemid Hk Hgt.
        rewrite /entry_le (Hclk _ _ _ Hemid) (Hclk _ _ _ Hk) in Hle.
        rewrite Hmcv in Hcmp1. lia.
    + apply bool_decide_eq_false_1 in Hcmp1.
      rewrite Hmcv in Hcmp1.
      wp_auto.
      case_bool_decide as Hcmp2.
      * (* clk >= middleEnd: every covering entry sits strictly right of [mid] *)
        wp_auto. wp_for_post.
        iFrame "HΦ". iExists (word.add mid (W64 1)), hi.
        iFrame "Hleft Hright Hnodes Hclock Hsl Htypes".
        have Hmide : (uint.Z (w64_word_instance.(word.add) itemVal.(yjs.item.id').(yjs.id.clock') (W64 (length (run_items rmid))))
                      = Z.of_nat (run_clock rmid) + Z.of_nat (length (run_items rmid)))%Z by word.
        rewrite Hmide in Hcmp2.
        iPureIntro. split.
        { word. }
        move=> k l r Hk Hcov1 Hcov2.
        have [Hlo Hhi] := Hwin k l r Hk Hcov1 Hcov2.
        split; [| exact Hhi].
        destruct (Nat.lt_trichotomy k (uint.nat mid)) as [Hlt | [Heq | Hgt]].
        { exfalso.
          have Hle := StronglySorted_lookup_le entry_le E k (uint.nat mid) (l, r) (lmid, rmid) Hsort Hk Hemid Hlt.
          rewrite /entry_le (Hclk _ _ _ Hemid) (Hclk _ _ _ Hk) in Hle.
          destruct (Hidisj k (uint.nat mid) l lmid r rmid Hk Hemid ltac:(lia)) as [Hd | Hd]; lia. }
        { exfalso. subst k. rewrite Hemid in Hk. injection Hk as <- <-. lia. }
        word.
      * (* middleClock <= clk < middleEnd: the probe COVERS clk *)
        wp_auto. wp_for_post.
        iApply ("HΦ" $! mid true). iFrame "Hsl Htypes".
        iExists lmid, rmid. iPureIntro. split; [exact Hemid |].
        rewrite /run_covers_clock. split; word.
  - (* the window is empty: no entry covers [clk] *)
    wp_auto.
    iApply ("HΦ" $! (W64 0) false). iFrame "Hsl Htypes".
    iPureIntro. move=> l r Hmem [Hcov1 Hcov2].
    apply list_elem_of_lookup in Hmem as [k Hk].
    have Hc1 : (Z.of_nat (run_clock r) <= uint.Z clk)%Z by word.
    have Hc2 : (uint.Z clk < Z.of_nat (run_clock r) + Z.of_nat (length (run_items r)))%Z by word.
    have := Hwin k l r Hk Hc1 Hc2. lia.
Qed.

(** [store.GetNode] at run granularity, DIRECT: the item index's slice for
    the id's client is [client_locs] ([client_locs_entries]), the walk
    corners the covering entry, and the entry sits at a slot of the pool
    ([client_entries_lookup_slot]); a miss certifies no run covers the id,
    because every slot of that client is an entry of the walked list
    ([pool_entries_slot]), or, for a client with no slice at all, because
    the index is complete. *)
Lemma wp_store__GetNode_runs (s : loc) (idv : yjs.id.t) (str : store_state_runs) :
  {{{ is_pkg_init yjs ∗ own_store_runs s str }}}
    s @! (go.PointerType yjs.store) @! "GetNode" #idv
  {{{ (l : loc) (ok : bool), RET (#l, #ok);
      own_store_runs s str ∗
      ⌜if ok then ∃ parent k, pool_run_covers (sr_pool str) parent k (toYjsId idv) ∧
                    (sr_locs str !! parent) ≫= (λ ls, ls !! k) = Some l
       else ∀ parent k, ¬ pool_run_covers (sr_pool str) parent k (toYjsId idv)⌝ }}}.
Proof using Type*.
  iIntros (Φ) "(#Hpkg & Hruns) HΦ".
  destruct str as [client0 k0 locs p bind pend pdel]. simpl in *.
  iDestruct "Hruns" as "(Hfields & %Hinvs)".
  have Hrpi : run_pool_invs p := proj1 Hinvs.
  iDestruct "Hfields" as "(Hclient & Hclock & HdeletedSet & Hitems & Hregistry & Htypes & Hpending & Hpdeletes)".
  iEval (simpl) in "Hitems Htypes".
  iDestruct "Hitems" as (items_mref) "(Hitemsf & Hitemmap)".
  iDestruct (own_type_pool_runs_id_bounds with "Htypes") as %Hbnds.
  iAssert (⌜locs_wf locs p⌝)%I as %Hlocswf; first by iDestruct "Htypes" as "[%Hwf _]".
  destruct Hlocswf as (Hdom & Hnd & Hlens).
  have Hlens' : ∀ parent tm, p !! parent = Some tm ->
      ∃ ls, locs !! parent = Some ls ∧ length ls = length (tm_runs tm).
  { move=> parent tm Hp.
    have His : is_Some (locs !! parent).
    { apply elem_of_dom. rewrite Hdom. apply elem_of_dom. by exists tm. }
    destruct His as [ls Hls]. exists ls. split; [done | exact (Hlens parent ls tm Hls Hp)]. }
  set (kc := idv.(yjs.id.clientId')).
  iDestruct "Hitemmap" as (gm) "(Hmap & Hruns & %Hcomplete & %Hclkloc)".
  have Hce : client_locs locs p kc = (client_entries locs p kc).*1 := client_locs_entries locs p kc Hclkloc.
  (* a slot of client [kc] is an entry of the walked list *)
  have Hslot_entry : ∀ parent k tm r, p !! parent = Some tm -> tm_runs tm !! k = Some r ->
      run_client r = uint.nat kc ->
      ∃ l, (l, r) ∈ client_entries locs p kc ∧ (locs !! parent) ≫= (λ ls, ls !! k) = Some l.
  { move=> parent k tm r Hp Hrk Hcl.
    destruct (Hlens' parent tm Hp) as (ls & Hls & Hlen).
    have Hk : (k < length ls)%nat by (rewrite Hlen; exact (lookup_lt_Some _ _ _ Hrk)).
    destruct (lookup_lt_is_Some_2 ls k Hk) as [l Hl].
    exists l. split; last by rewrite Hls /=.
    apply client_entries_mem. split.
    - apply pool_entries_slot. by exists parent, ls, tm, k.
    - rewrite /entry_client /= Hcl. word. }
  wp_method_call. wp_call. wp_call. wp_auto.
  wp_apply (wp_map_lookup2 with "Hmap"). iIntros "Hmap".
  destruct (gm !! kc) as [slk |] eqn:Hslk; rewrite Hslk /=.
  - (* known client: run the binary search over its entries *)
    wp_auto.
    iDestruct (big_sepM_lookup_acc _ _ kc slk Hslk with "Hruns") as "[Hrun Hrunsback]".
    iNamed "Hrun".
    iEval (rewrite -/(client_locs locs p kc) Hce) in "Hslice".
    have Hndl : NoDup (pool_entries locs p).*1 := pool_entries_locs_NoDup locs p Hdom Hlens' Hnd.
    wp_apply (wp_getNodeIndex_runs slk (DfracOwn 1) locs p kc idv.(yjs.id.clock') (client_entries locs p kc) Hrpi
                (client_entries_sorted_client locs p kc Hndl)
                with "[$Hslice $Htypes]").
    iIntros (i ok) "(Hslice & Htypes & %Hires)".
    destruct ok.
    + (* hit: the probe covers the id *)
      destruct Hires as (lres & rres & Hres & Hcov).
      wp_auto.
      iDestruct (own_slice_len with "Hslice") as %[Hsllen Hsllen0].
      rewrite length_fmap in Hsllen Hsllen0.
      have Hilt : (uint.nat i < length (client_entries locs p kc))%nat
        by (apply lookup_lt_Some in Hres; lia).
      rewrite decide_True; last word.
      have Hlocres : (client_entries locs p kc).*1 !! uint.nat i = Some lres
        by rewrite list_lookup_fmap Hres //.
      iDestruct (own_slice_elem_acc (sint.Z i) lres slk (DfracOwn 1) (client_entries locs p kc).*1 with "Hslice") as "[Hel Hgive]".
      { word. }
      { replace (Z.to_nat (sint.Z i)) with (uint.nat i) by word. exact Hlocres. }
      wp_auto.
      iDestruct ("Hgive" $! lres with "Hel") as "Hslice".
      have Hinsid : (<[sint.nat i := lres]> (client_entries locs p kc).*1) = (client_entries locs p kc).*1.
      { apply list_insert_id. replace (sint.nat i) with (uint.nat i) by word. exact Hlocres. }
      iEval (rewrite Hinsid -Hce) in "Hslice".
      iDestruct ("Hrunsback" with "[$Hslice $Hcap]") as "Hruns".
      destruct (client_entries_lookup_slot locs p kc (uint.nat i) lres rres Hres)
        as [Hcres (parent & ls & tm & kr & Hls & Hp & Hlk & Hrk)].
      have Hrmem : rres ∈ all_runs p.
      { apply elem_of_all_runs. exists parent, tm. split; [exact Hp | exact (list_elem_of_lookup_2 _ _ _ Hrk)]. }
      iApply ("HΦ" $! lres true).
      iSplitL "Hclient Hclock HdeletedSet Hitemsf Hmap Hruns Hregistry Htypes Hpending Hpdeletes".
      { iSplitL; last (iPureIntro; exact Hinvs).
        rewrite /own_store_fields_runs /=.
        iFrame "Hclient Hclock HdeletedSet Hregistry Htypes Hpending Hpdeletes".
        iExists items_mref. iFrame "Hitemsf". iExists gm. iFrame "Hmap Hruns".
        iPureIntro. split; [exact Hcomplete | exact Hclkloc]. }
      iPureIntro. exists parent, kr. split.
      * exists tm, rres. split_and!; [exact Hp | exact Hrk |].
        rewrite /run_covers /toYjsId /=.
        have Hb := proj1 (Hbnds rres Hrmem).
        rewrite /entry_client /= in Hcres.
        split; [| exact Hcov].
        rewrite /kc in Hcres. word.
      * rewrite Hls /=. exact Hlk.
    + (* clock miss within a known client: no run of this client covers the id *)
      wp_auto.
      iEval (rewrite -Hce) in "Hslice".
      iDestruct ("Hrunsback" with "[$Hslice $Hcap]") as "Hruns".
      iApply ("HΦ" $! null false).
      iSplitL "Hclient Hclock HdeletedSet Hitemsf Hmap Hruns Hregistry Htypes Hpending Hpdeletes".
      { iSplitL; last (iPureIntro; exact Hinvs).
        rewrite /own_store_fields_runs /=.
        iFrame "Hclient Hclock HdeletedSet Hregistry Htypes Hpending Hpdeletes".
        iExists items_mref. iFrame "Hitemsf". iExists gm. iFrame "Hmap Hruns".
        iPureIntro. split; [exact Hcomplete | exact Hclkloc]. }
      iPureIntro. move=> parent k [tm [r [Hp [Hrk Hcov]]]].
      destruct Hcov as (Hcl & Hc1 & Hc2).
      destruct (Hslot_entry parent k tm r Hp Hrk Hcl) as (l & Hmem & _).
      exact (Hires l r Hmem (conj Hc1 Hc2)).
  - (* unknown client: no run of this author at all *)
    wp_auto.
    iApply ("HΦ" $! null false).
    iSplitL "Hclient Hclock HdeletedSet Hitemsf Hmap Hruns Hregistry Htypes Hpending Hpdeletes".
    { iSplitL; last (iPureIntro; exact Hinvs).
      rewrite /own_store_fields_runs /=.
      iFrame "Hclient Hclock HdeletedSet Hregistry Htypes Hpending Hpdeletes".
      iExists items_mref. iFrame "Hitemsf". iExists gm. iFrame "Hmap Hruns".
      iPureIntro. split; [exact Hcomplete | exact Hclkloc]. }
    iPureIntro. move=> parent k [tm [r [Hp [Hrk Hcov]]]].
    destruct Hcov as (Hcl & _ & _).
    destruct (Hslot_entry parent k tm r Hp Hrk Hcl) as (l & Hmem & _).
    apply client_entries_mem in Hmem as [Hpe Hc].
    have Hkcin : kc ∈ (entry_kp <$> pool_entries locs p).*1.
    { rewrite -Hc. apply list_elem_of_fmap. exists (entry_kp (l, r)). split; [reflexivity |].
      apply list_elem_of_fmap_2. exact Hpe. }
    destruct (Hcomplete kc Hkcin) as [slk Hslk'].
    rewrite Hslk in Hslk'. discriminate.
Qed.

End store_update.
