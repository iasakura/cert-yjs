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
#[local] Instance pending_item_rooted_persistent' γs typedInput :
  Persistent (pending_item_rooted γs typedInput).
Proof. rewrite /pending_item_rooted. destruct (decide _); apply _. Qed.
#[local] Instance is_pending_rooted_persistent' γs pending :
  Persistent (is_pending_rooted γs pending).
Proof. apply _. Qed.
#[local] Instance pending_item_rooted_timeless' γs typedInput :
  Timeless (pending_item_rooted γs typedInput).
Proof. rewrite /pending_item_rooted. destruct (decide _); apply _. Qed.
#[local] Instance is_pending_rooted_timeless' γs pending :
  Timeless (is_pending_rooted γs pending).
Proof. apply _. Qed.

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

(** [expand_input] / [expand_inputs] are defined UPSTREAM in [yjs_store_base]
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
    ValidReplay (expand_inputs (drop (S j) inputs)) (<[t := arr']> mj) m'.
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
Qed.

(* ===== applyUpdate (doc-level, #49): store-wide node lookup ==============
   [store.repair] resolves a decoded struct's origins through the store-wide
   [GetNode] (per-client clock-sorted run lists + binary search) instead of
   walking one type's DLL. The heap cells backing the probes live in the
   per-type DLLs, so the lookup specs borrow single cells out of the
   document-wide big-sep (what [store_inv] holds as [Htypes]) via
   [types_cell_acc_gen]. *)

Lemma list_elem_of_concat {D : Type} (x : D) (ls : list (list D)) :
  x ∈ concat ls <-> ∃ l, x ∈ l ∧ l ∈ ls.
Proof.
  induction ls as [| l0 ls IH]; simpl.
  - rewrite elem_of_nil. split; [done | move=> [l [_ Hl]]; by rewrite elem_of_nil in Hl].
  - rewrite elem_of_app IH. split.
    + move=> [Hx | [l [Hx Hl]]].
      * exists l0. split; [exact Hx | apply elem_of_cons; by left].
      * exists l. split; [exact Hx | apply elem_of_cons; by right].
    + move=> [l [Hx Hl]]. apply elem_of_cons in Hl as [-> | Hl]; [by left | right; by exists l].
Qed.

(** Pool membership, decomposed to the owning type. *)
Lemma all_cells_elem_of (types : gmap loc type_state) (c : item_cell) :
  c ∈ all_cells types <-> ∃ p ts, types !! p = Some ts /\ c ∈ ty_cells ts.
Proof.
  rewrite /all_cells list_elem_of_concat.
  split.
  - move=> [l [Hcl Hl]].
    apply list_elem_of_fmap in Hl. destruct Hl as (ts & -> & Hts).
    apply list_elem_of_fmap in Hts. destruct Hts as ([p ts'] & -> & Hpts).
    simpl in *. exists p, ts'. split; [| exact Hcl].
    by apply elem_of_map_to_list.
  - move=> [p [ts [Hp Hcts]]].
    exists (ty_cells ts). split; [exact Hcts |].
    apply list_elem_of_fmap. exists ts. split; [done |].
    apply list_elem_of_fmap. exists (p, ts). split; [done |].
    by apply elem_of_map_to_list.
Qed.

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

(** Borrow one pool cell's heap struct out of the per-type DLL big-sep,
    exposing the full [own_dll_acc] translation facts (id / parent / content
    coupling / origins / flags / [run_wf]) and a wand restoring the big-sep.
    What [GetNode] / [getNodeIndex] / [splitNode] / [repair] read through. *)
Lemma types_cell_acc_gen (types : gmap loc type_state) (c : item_cell) :
  c ∈ all_cells types ->
  ([∗ map] parent ↦ ts ∈ types,
      own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
      ⌜YjsArrInvariant (ty_arr ts)⌝) -∗
    ∃ (itemVal : yjs.item.t) (olid orid : option yjs.id.t),
      "%Hid" ∷ ⌜item_id (run_head c) = toYjsId itemVal.(yjs.item.id')⌝ ∗
      "%Hpar" ∷ ⌜itemVal.(yjs.item.parent') = ic_parent c⌝ ∗
      "%Hcontent" ∷ ⌜content <$> ic_run c = explode (toContent itemVal.(yjs.item.content'))⌝ ∗
      "%Holid" ∷ ⌜origin_id (origin (run_head c)) = toYjsId <$> olid⌝ ∗
      "%Horid" ∷ ⌜origin_id (rightOrigin (run_head c)) = toYjsId <$> orid⌝ ∗
      "%Hflags" ∷ ⌜itemVal.(yjs.item.flags') = (if ic_deleted c then W8 6 else W8 2)⌝ ∗
      "%Hrun" ∷ ⌜run_wf (ic_run c)⌝ ∗
      "Hval" ∷ ic_loc c ↦ itemVal ∗
      "Hcol" ∷ is_origin_id itemVal.(yjs.item.originLeftId') olid ∗
      "Hcor" ∷ is_origin_id itemVal.(yjs.item.originRightId') orid ∗
      "Hback" ∷ (ic_loc c ↦ itemVal -∗
        ([∗ map] parent ↦ ts ∈ types,
            own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
            ⌜YjsArrInvariant (ty_arr ts)⌝)).
Proof using Type*.
  move=> Hc. iIntros "Htypes".
  apply all_cells_elem_of in Hc. destruct Hc as (p & ts & Hp & Hcts).
  apply list_elem_of_lookup_1 in Hcts. destruct Hcts as [k Hk].
  iDestruct (big_sepM_lookup_acc _ _ p ts Hp with "Htypes") as "[(Hyt & %Hinvp) Hrest]".
  iDestruct "Hyt" as (yt tl) "(Hparent & Hdll & %Hlen & %Hrepr & %Hcpar)".
  iDestruct (own_dll_acc (DfracOwn 1) (ty_cells ts) yt.(yjs.yType.start') tl k c Hk with "Hdll") as "Hacc".
  iNamed "Hacc".
  iExists itemVal, olid, orid.
  iSplitR; [iPureIntro; exact Hid |].
  iSplitR; [iPureIntro; exact Hpar |].
  iSplitR; [iPureIntro; exact Hcontent |].
  iSplitR; [iPureIntro; exact Holid |].
  iSplitR; [iPureIntro; exact Horid |].
  iSplitR; [iPureIntro; exact Hflags |].
  iSplitR; [iPureIntro; exact Hrun |].
  iFrame "Hcval Hcol Hcor".
  iIntros "Hval".
  iDestruct ("Hback" with "Hval") as "Hdll".
  iApply "Hrest". iSplitL; [| iPureIntro; exact Hinvp].
  iExists yt, tl. iFrame "Hparent Hdll". iPureIntro.
  split_and!; [exact Hlen | exact Hrepr | exact Hcpar].
Qed.

(** [getNodeIndex] (binary search over a clock-sorted run), specified for the
    hit path only: the verified update path always resolves (a [ValidReplay]
    input's origins exist), witnessed by [k0]/[c0], so the not-found return is
    dead code (the loop cannot exhaust a window that provably contains a hit).
    The probed cells are read through the per-type DLL big-sep ([types_cell_acc_gen]);
    their 1-char pin makes [Len() = 1], so a run covers [clk] iff some cell's
    clock IS [clk]. [Hnowrap] rules out [middleClock + 1] wrap-around (the
    [middleEnd] compare would otherwise skip a max-clock hit). *)
Lemma wp_getNodeIndex (sl : slice.t) (dq : dfrac) (types : gmap loc type_state)
    (run : list item_cell) (clk : w64) (k0 : nat) (c0 : item_cell) :
  StronglySorted cell_le run ->
  (∀ c, c ∈ run -> c ∈ all_cells types) ->
  (∀ c, c ∈ run -> (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) < 2^64)%Z) ->
  run !! k0 = Some c0 ->
  cell_clock c0 = clk ->
  {{{ is_pkg_init yjs ∗ sl ↦*{dq} (ic_loc <$> run) ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) }}}
    @! yjs.getNodeIndex #sl #clk
  {{{ (i : w64), RET (#i, #true);
      sl ↦*{dq} (ic_loc <$> run) ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) ∗
      ∃ c, ⌜run !! uint.nat i = Some c ∧
             (uint.Z (cell_clock c) <= uint.Z clk)%Z ∧
             (uint.Z clk < uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)))%Z⌝ }}}.
Proof using Type*.
  move=> Hsort Hmem Hrunfits Hk0 Hclk0.
  wp_start as "(Hsl & Htypes)".
  iDestruct (own_slice_len with "Hsl") as %[Hsllen Hsllen0].
  rewrite length_fmap in Hsllen Hsllen0.
  wp_auto.
  (* loop invariant: the window [lo, hi) contains every hit (a cell whose head
     clock IS [clk]); the returned cell only COVERS [clk] (run-aware) *)
  iAssert (∃ (lo hi : w64),
    "Hleft" ∷ left_ptr ↦ lo ∗ "Hright" ∷ right_ptr ↦ hi ∗
    "Hnodes" ∷ nodes_ptr ↦ sl ∗ "Hclock" ∷ clock_ptr ↦ clk ∗
    "Hsl" ∷ sl ↦*{dq} (ic_loc <$> run) ∗
    "Htypes" ∷ ([∗ map] parent ↦ ts ∈ types,
        own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
        ⌜YjsArrInvariant (ty_arr ts)⌝) ∗
    "%Hbnd" ∷ ⌜(0 <= uint.Z lo /\ uint.Z hi <= Z.of_nat (length run))%Z⌝ ∗
    "%Hwin" ∷ ⌜∀ (k : nat) (c : item_cell), run !! k = Some c -> cell_clock c = clk ->
                (uint.Z lo <= Z.of_nat k < uint.Z hi)%Z⌝)%I
    with "[left right nodes clock Hsl Htypes]" as "IH".
  { iExists (W64 0), sl.(slice.len).
    iFrame "left right nodes clock Hsl Htypes".
    iPureIntro. split; [word |].
    move=> k c Hk Hc. have Hklt := lookup_lt_Some _ _ _ Hk. word. }
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
    iDestruct (types_cell_acc_gen types cmid Hcmemall with "Htypes") as "Hacc".
    iNamed "Hacc".
    wp_auto.
    have Hmcv : cell_clock cmid = itemVal.(yjs.item.id').(yjs.id.clock')
      by (rewrite /cell_clock Hid /toYjsId /=; word).
    (* the run length is what [Len()] reads (the content byte length couples to
       the run via [Hcontent]), replacing the pre-#28 unit-length reasoning *)
    have HlenEq : length (itemVal.(yjs.item.content').(yjs.content.content')) = length (ic_run cmid).
    { have H := f_equal length Hcontent.
      rewrite length_fmap explode_length /toContent in H. lia. }
    have Hlenpos : (1 <= Z.of_nat (length (ic_run cmid)))%Z.
    { have [Hne _] := Hrun. destruct (ic_run cmid) as [|? ?]; [done | simpl; lia]. }
    wp_apply (wp_item__Len cmid.(ic_loc) (DfracOwn 1) itemVal with "[$Hval]"). iIntros "Hval".
    rewrite HlenEq.
    iDestruct ("Hback" with "Hval") as "Htypes".
    wp_auto.
    destruct (bool_decide (uint.Z clk < uint.Z itemVal.(yjs.item.id').(yjs.id.clock'))) eqn:Hcmp1.
    + (* clk < middleClock: shrink [right] to [mid] *)
      apply bool_decide_eq_true_1 in Hcmp1.
      wp_auto. wp_for_post.
      iFrame "HΦ". iExists lo, mid.
      iFrame "Hleft Hright Hnodes Hclock Hsl Htypes".
      iPureIntro. split.
      { lia. }
      move=> k c Hk Hc.
      have [Hlo Hhi] := Hwin k c Hk Hc.
      split; [exact Hlo |].
      destruct (Nat.lt_trichotomy k (uint.nat mid)) as [Hlt | [Heq | Hgt]].
      * lia.
      * exfalso. subst k. rewrite Hcmid in Hk. injection Hk as <-.
        rewrite -Hmcv Hc in Hcmp1. lia.
      * exfalso.
        have Hle := StronglySorted_lookup_le cell_le run (uint.nat mid) k cmid c Hsort Hcmid Hk Hgt.
        rewrite /cell_le Hc Hmcv in Hle. lia.
    + (* clk >= middleClock *)
      apply bool_decide_eq_false_1 in Hcmp1.
      have Hnw : (uint.Z (cell_clock cmid) + Z.of_nat (length (ic_run cmid)) < 2^64)%Z
        by (apply Hrunfits; exact (list_elem_of_lookup_2 _ _ _ Hcmid)).
      rewrite Hmcv in Hnw.
      wp_auto.
      case_bool_decide as Hcmp2.
      * (* clk >= middleEnd: move [left] past [mid] *)
        have Hgtm : (uint.Z itemVal.(yjs.item.id').(yjs.id.clock') < uint.Z clk)%Z by word.
        wp_auto. wp_for_post.
        iFrame "HΦ". iExists (word.add mid (W64 1)), hi.
        iFrame "Hleft Hright Hnodes Hclock Hsl Htypes".
        iPureIntro. split.
        { word. }
        move=> k c Hk Hc.
        have [Hlo Hhi] := Hwin k c Hk Hc.
        split; [| exact Hhi].
        destruct (Nat.lt_trichotomy k (uint.nat mid)) as [Hlt | [Heq | Hgt]].
        { exfalso.
          have Hle := StronglySorted_lookup_le cell_le run k (uint.nat mid) c cmid Hsort Hk Hcmid Hlt.
          rewrite /cell_le Hc Hmcv in Hle. lia. }
        { exfalso. subst k. rewrite Hcmid in Hk. injection Hk as <-.
          rewrite -Hmcv Hc in Hgtm. lia. }
        word.
      * (* middleClock <= clk < middleEnd = middleClock + Len: the probe COVERS clk *)
        wp_auto. wp_for_post.
        iApply ("HΦ" $! mid). iFrame "Hsl Htypes".
        iExists cmid. iPureIntro. split; [exact Hcmid |].
        split; rewrite Hmcv; word.
  - (* [left >= right] never happens: the witness pins a nonempty window *)
    exfalso. have [Hf1 Hf2] := Hwin k0 c0 Hk0 Hclk0. lia.
Qed.

(** [getNodeIndex], general covering-witness form (issue #28 stage D1): the
    witness cell [c0]'s run COVERS [clk] (it need not START there), so the
    search may end on a cell probed mid-run. The window argument needs
    index-wise clock-range disjointness of the run ([Hidisj], sourced from
    the pool's [cells_range_disjoint] + loc-NoDup at the call site): at most
    one run cell covers [clk], and the binary search corners it. Additive
    alongside the exact-hit form above, which dies with the unit scaffold at
    the C2 flip. *)
Lemma wp_getNodeIndex_range (sl : slice.t) (dq : dfrac) (types : gmap loc type_state)
    (run : list item_cell) (clk : w64) (k0 : nat) (c0 : item_cell) :
  StronglySorted cell_le run ->
  (∀ c, c ∈ run -> c ∈ all_cells types) ->
  (∀ c, c ∈ run -> (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) < 2^64)%Z) ->
  (∀ (k1 k2 : nat) (c1 c2 : item_cell),
     run !! k1 = Some c1 -> run !! k2 = Some c2 -> k1 ≠ k2 ->
     (uint.Z (cell_clock c1) + Z.of_nat (length (ic_run c1)) <= uint.Z (cell_clock c2))%Z ∨
     (uint.Z (cell_clock c2) + Z.of_nat (length (ic_run c2)) <= uint.Z (cell_clock c1))%Z) ->
  run !! k0 = Some c0 ->
  (uint.Z (cell_clock c0) <= uint.Z clk)%Z ->
  (uint.Z clk < uint.Z (cell_clock c0) + Z.of_nat (length (ic_run c0)))%Z ->
  {{{ is_pkg_init yjs ∗ sl ↦*{dq} (ic_loc <$> run) ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) }}}
    @! yjs.getNodeIndex #sl #clk
  {{{ (i : w64), RET (#i, #true);
      sl ↦*{dq} (ic_loc <$> run) ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) ∗
      ∃ c, ⌜run !! uint.nat i = Some c ∧
             (uint.Z (cell_clock c) <= uint.Z clk)%Z ∧
             (uint.Z clk < uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)))%Z⌝ }}}.
Proof using Type*.
  move=> Hsort Hmem Hrunfits Hidisj Hk0 Hc0le Hc0lt.
  wp_start as "(Hsl & Htypes)".
  iDestruct (own_slice_len with "Hsl") as %[Hsllen Hsllen0].
  rewrite length_fmap in Hsllen Hsllen0.
  wp_auto.
  (* loop invariant: the window [lo, hi) contains every COVERING cell *)
  iAssert (∃ (lo hi : w64),
    "Hleft" ∷ left_ptr ↦ lo ∗ "Hright" ∷ right_ptr ↦ hi ∗
    "Hnodes" ∷ nodes_ptr ↦ sl ∗ "Hclock" ∷ clock_ptr ↦ clk ∗
    "Hsl" ∷ sl ↦*{dq} (ic_loc <$> run) ∗
    "Htypes" ∷ ([∗ map] parent ↦ ts ∈ types,
        own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
        ⌜YjsArrInvariant (ty_arr ts)⌝) ∗
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
    iDestruct (types_cell_acc_gen types cmid Hcmemall with "Htypes") as "Hacc".
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
      * (* clk >= middleEnd: every covering cell sits strictly right of [mid]
           (a left cell's range would have to swallow [mid]'s whole range,
           contradicting the index-wise disjointness) *)
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
        iApply ("HΦ" $! mid). iFrame "Hsl Htypes".
        iExists cmid. iPureIntro. split; [exact Hcmid |].
        split; rewrite Hmcv; word.
  - (* [left >= right] never happens: the covering witness pins a nonempty window *)
    exfalso. have [Hf1 Hf2] := Hwin k0 c0 Hk0 Hc0le Hc0lt. lia.
Qed.

(** [store.GetNode], general covering form (issue #28 stage D1): the id may
    address ANY char of the witness cell's run; the returned node is pinned
    to [cw] by per-client clock-range disjointness (two same-client cells
    whose ranges both cover the id must share a location) instead of the
    all-singleton identification. *)
Lemma wp_store__GetNode_range (s mref : loc) (dq : dfrac) (idv : yjs.id.t)
    (types : gmap loc type_state) (cw : item_cell) :
  cw ∈ all_cells types ->
  cell_client cw = idv.(yjs.id.clientId') ->
  (uint.Z (cell_clock cw) <= uint.Z idv.(yjs.id.clock'))%Z ->
  (uint.Z idv.(yjs.id.clock') < uint.Z (cell_clock cw) + Z.of_nat (length (ic_run cw)))%Z ->
  (∀ c, c ∈ all_cells types -> (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) < 2^64)%Z) ->
  NoDup (ic_loc <$> all_cells types) ->
  cells_range_disjoint (all_cells types) ->
  {{{ is_pkg_init yjs ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref dq types ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) }}}
    s @! (go.PointerType yjs.store) @! "GetNode" #idv
  {{{ RET (#(ic_loc cw), #true);
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref dq types ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) }}}.
Proof using Type*.
  move=> Hcw Hcwcc Hcwle Hcwlt Hrunfits Hnodup Hrangedisj.
  iIntros (Φ) "(#Hpkg & Hitemsf & Hitemmap & Htypes) HΦ".
  set (kc := idv.(yjs.id.clientId')).
  have Hcwkc : cell_client cw = kc := Hcwcc.
  iNamed "Hitemmap".
  have Hkcin : kc ∈ (cell_client <$> all_cells types).
  { rewrite -Hcwkc. apply list_elem_of_fmap_2. exact Hcw. }
  destruct (Hcomplete kc Hkcin) as [slk Hslk].
  wp_method_call. wp_call. wp_call. wp_auto.
  wp_apply (wp_map_lookup2 with "Hmap"). iIntros "Hmap".
  rewrite Hslk /=.
  wp_auto.
  iDestruct (big_sepM_lookup_acc _ _ kc slk Hslk with "Hruns") as "[Hrun Hrunsback]".
  iNamed "Hrun".
  have Hcwrun : cw ∈ client_run types kc by (apply client_run_mem; split; [exact Hcw | exact Hcwcc]).
  apply list_elem_of_lookup_1 in Hcwrun. destruct Hcwrun as [kw Hkw].
  have Hrunfits' : ∀ c, c ∈ client_run types kc ->
      (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) < 2^64)%Z.
  { move=> c Hc. exact (Hrunfits c (proj1 (proj1 (client_run_mem types kc c) Hc))). }
  (* index-wise disjointness of the run from the pool invariants *)
  have HndAll : NoDup (all_cells types) := NoDup_fmap_1 ic_loc _ Hnodup.
  have Hndrun : NoDup (client_run types kc).
  { rewrite /client_run (merge_sort_Permutation cell_le _). apply NoDup_filter. exact HndAll. }
  have Hinj : ∀ x y, x ∈ client_run types kc → y ∈ client_run types kc → ic_loc x = ic_loc y → x = y.
  { move=> x y Hx Hy Hxy.
    have Hxa : x ∈ all_cells types := proj1 (proj1 (client_run_mem types kc x) Hx).
    have Hya : y ∈ all_cells types := proj1 (proj1 (client_run_mem types kc y) Hy).
    apply list_elem_of_lookup_1 in Hxa as [ix Hix]. apply list_elem_of_lookup_1 in Hya as [iy Hiy].
    have Hlix : (ic_loc <$> all_cells types) !! ix = Some (ic_loc y) by (rewrite list_lookup_fmap Hix /= Hxy //).
    have Hliy : (ic_loc <$> all_cells types) !! iy = Some (ic_loc y) by (rewrite list_lookup_fmap Hiy //).
    have Hijeq : ix = iy := NoDup_lookup _ _ _ _ Hnodup Hlix Hliy.
    congruence. }
  have Hidisj : ∀ (k1 k2 : nat) (c1 c2 : item_cell),
      client_run types kc !! k1 = Some c1 -> client_run types kc !! k2 = Some c2 -> k1 ≠ k2 ->
      (uint.Z (cell_clock c1) + Z.of_nat (length (ic_run c1)) <= uint.Z (cell_clock c2))%Z ∨
      (uint.Z (cell_clock c2) + Z.of_nat (length (ic_run c2)) <= uint.Z (cell_clock c1))%Z.
  { move=> k1 k2 c1 c2 Hk1 Hk2 Hkne.
    have Hc1r : c1 ∈ client_run types kc := list_elem_of_lookup_2 _ _ _ Hk1.
    have Hc2r : c2 ∈ client_run types kc := list_elem_of_lookup_2 _ _ _ Hk2.
    have Hlocne : ic_loc c1 ≠ ic_loc c2.
    { move=> Heq. have Hceq : c1 = c2 := Hinj c1 c2 Hc1r Hc2r Heq.
      rewrite Hceq in Hk1. exact (Hkne (NoDup_lookup _ _ _ _ Hndrun Hk1 Hk2)). }
    apply (Hrangedisj c1 c2
             (proj1 (proj1 (client_run_mem types kc c1) Hc1r))
             (proj1 (proj1 (client_run_mem types kc c2) Hc2r)));
      [| exact Hlocne].
    rewrite (proj2 (proj1 (client_run_mem types kc c1) Hc1r))
            (proj2 (proj1 (client_run_mem types kc c2) Hc2r)) //. }
  wp_apply (wp_getNodeIndex_range slk dq types (client_run types kc) idv.(yjs.id.clock') kw cw
              (client_run_sorted types kc)
              (fun c Hc => proj1 (proj1 (client_run_mem types kc c) Hc))
              Hrunfits' Hidisj Hkw Hcwle Hcwlt
              with "[$Hslice $Htypes]").
  iIntros (i) "(Hslice & Htypes & %Hires)".
  destruct Hires as (cres & Hcres & Hcresle & Hcreslt).
  wp_auto.
  iDestruct (own_slice_len with "Hslice") as %[Hsllen Hsllen0].
  rewrite length_fmap in Hsllen Hsllen0.
  have Hilt : (uint.nat i < length (client_run types kc))%nat by (apply lookup_lt_Some in Hcres; lia).
  rewrite decide_True; last word.
  have Hlocres : (ic_loc <$> client_run types kc) !! uint.nat i = Some cres.(ic_loc)
    by rewrite list_lookup_fmap Hcres //.
  iDestruct (own_slice_elem_acc (sint.Z i) (ic_loc cres) slk dq (ic_loc <$> client_run types kc) with "Hslice") as "[Hel Hgive]".
  { word. }
  { replace (Z.to_nat (sint.Z i)) with (uint.nat i) by word. exact Hlocres. }
  wp_auto.
  iDestruct ("Hgive" $! cres.(ic_loc) with "Hel") as "Hslice".
  have Hinsid : (<[sint.nat i := cres.(ic_loc)]> (ic_loc <$> client_run types kc)) = (ic_loc <$> client_run types kc).
  { apply list_insert_id. replace (sint.nat i) with (uint.nat i) by word. exact Hlocres. }
  iEval (rewrite Hinsid) in "Hslice".
  (* both [cres] and [cw] cover the requested clock at the same client:
     range disjointness forces the same location *)
  have Hcresmem : cres ∈ all_cells types /\ cell_client cres = kc.
  { apply client_run_mem. exact (list_elem_of_lookup_2 _ _ _ Hcres). }
  have Hloceq : cres.(ic_loc) = cw.(ic_loc).
  { destruct (decide (cres.(ic_loc) = cw.(ic_loc))) as [He | Hne]; [exact He | exfalso].
    destruct (Hrangedisj cres cw (proj1 Hcresmem) Hcw
                ltac:(rewrite (proj2 Hcresmem) Hcwcc //) Hne) as [Hd | Hd]; lia. }
  rewrite Hloceq.
  iApply "HΦ".
  iFrame "Hitemsf".
  iDestruct ("Hrunsback" with "[$Hslice $Hcap]") as "Hruns".
  iSplitL "Hmap Hruns".
  { iExists gm. iFrame "Hmap Hruns". iPureIntro. split; [exact Hcomplete | exact Hclkloc]. }
  iFrame "Htypes".
Qed.

(** [store.splitNode n diff] (issue #28 M4): split the run cell [cw] (at DLL
    index [k] of type [parent]) at offset [diff] into a truncated left half (same
    node loc) and a fresh right half ([rloc]), updating both the per-type DLL and
    the per-client run list. The pure cell effect is [split_cells cells k
    (uint.nat diff) rloc], invisible to the flattened document.

    Standalone M4 infrastructure (not yet wired into repair / the update path).

    NOTE (spec deviations from the issue-28 M2 plan sketch, reported):
    - The no-wrap hypothesis is strengthened from [cell_clock c + 1 < 2^64] to
      the run-aware [cell_clock c + length (ic_run c) < 2^64] for every cell,
      because [getNodeIndex] (now run-aware) computes [middleClock + Len()] with
      [Len()] the RUN length, so the +1 bound no longer rules out overflow at a
      multi-char probe. It subsumes the separate [+ length (ic_run cw)] bound.
    - The non-overlap hypothesis is corrected to genuine range-disjointness
      ([c.clock + length (ic_run c) <= cw.clock ∨ cw.clock + length (ic_run cw)
      <= c.clock] for [ic_loc c ≠ ic_loc cw]). The sketch's [c.clock <= cw.clock]
      left half does NOT prevent a left cell from overlapping [cw]'s clock range,
      so the covering cell [getNodeIndex] returns would not be uniquely pinned to
      [cw]'s position. Disjointness is the true store invariant. *)

Lemma wp_store__splitNode (s mref : loc) (types : gmap loc type_state)
    (parent : loc) (cells arr : list _) (k : nat) (cw : item_cell) (diff : w64) :
  types !! parent = Some (MkTypeState cells arr) ->
  cells !! k = Some cw ->
  (0 < uint.nat diff < length (ic_run cw))%nat ->
  (∀ c, c ∈ all_cells types -> (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) < 2^64)%Z) ->
  NoDup (ic_loc <$> all_cells types) ->
  (∀ c, c ∈ all_cells types -> cell_client c = cell_client cw -> ic_loc c ≠ ic_loc cw ->
     (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) <= uint.Z (cell_clock cw))%Z ∨
     (uint.Z (cell_clock cw) + Z.of_nat (length (ic_run cw)) <= uint.Z (cell_clock c))%Z) ->
  {{{ is_pkg_init yjs ∗ (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types ∗
      ([∗ map] p ↦ ts ∈ types, own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗ ⌜YjsArrInvariant (ty_arr ts)⌝) }}}
    s @! (go.PointerType yjs.store) @! "splitNode" #(ic_loc cw) #diff
  {{{ (rloc : loc), RET (#(ic_loc cw), #rloc);
      ⌜rloc ≠ null⌝ ∗ ⌜rloc ∉ ic_loc <$> all_cells types⌝ ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗
      own_item_map mref (DfracOwn 1) (<[parent := MkTypeState (split_cells cells k (uint.nat diff) rloc) arr]> types) ∗
      ([∗ map] p ↦ ts ∈ (<[parent := MkTypeState (split_cells cells k (uint.nat diff) rloc) arr]> types),
          own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗ ⌜YjsArrInvariant (ty_arr ts)⌝) }}}.
Proof using Type*.
  move=> Htypes Hcellk Hdiff Hrunfits Hnodup Hdisj.
  iIntros (Φ) "(#Hpkg & Hitemsf & Hitemmap & Htypes) HΦ".
  (* open [parent]'s [own_ytype_cells], peel node [k] out of the DLL *)
  iDestruct (big_sepM_delete _ _ parent _ Htypes with "Htypes") as "[(Hpc & %Harrinv) Hrestmap]".
  simpl.
  iDestruct "Hpc" as (yt tl0) "(Hparent & Hdll & %Hlen0 & %Hrepr0 & %Hcpar0)".
  pose proof (take_drop_middle cells k cw Hcellk) as Hsplit.
  set (pre := take k cells) in Hsplit.
  set (suf := drop (S k) cells) in Hsplit.
  iEval (rewrite -Hsplit) in "Hdll".
  iEval (rewrite own_dll_app) in "Hdll".
  iDestruct "Hdll" as (ml mf) "[Hseg1 Hseg2]".
  iDestruct "Hseg2" as (itemVal olidcw oridcw) "Hcons".
  iNamed "Hcons".
  destruct Hloc as [Hmfeq Hmfnn]. subst mf.
  iDestruct (typed_pointsto_not_null with "Hval") as %Hcwnn.
  wp_method_call. wp_call. wp_call. wp_auto.
  (* olid := newId(client, clock+diff-1) *)
  wp_apply wp_NewId.
  (* cb := []byte(n.content.content) via the byte round-trip *)
  wp_apply wp_string_to_bytes. iIntros (cbs) "[Hcb Hcbcap]". wp_auto.
  (* the right cell's id := newId(client, clock+diff) *)
  wp_apply wp_NewId.
  have Hsclen : length (itemVal.(yjs.item.content').(yjs.content.content')) = length cw.(ic_run).
  { have H := f_equal length Hcontent. rewrite length_fmap explode_length /toContent in H. lia. }
  iDestruct (own_slice_len with "Hcb") as %Hcbwf.
  iDestruct (own_slice_wf with "Hcb") as %Hcapwf.
  destruct Hcbwf as [Hcbwf1 Hcbwf2].
  have Hdiffb : 0 ≤ sint.Z diff ≤ sint.Z cbs.(slice.len) by word.
  (* right.content := string(cb[diff:]) *)
  rewrite decide_True; last (split; [word | word]).
  have Hslbound : 0 ≤ sint.Z diff ≤ sint.Z cbs.(slice.len) ≤ sint.Z cbs.(slice.len) by word.
  iDestruct (own_slice_slice diff cbs.(slice.len) cbs (DfracOwn 1) _ Hslbound with "Hcb") as "(Hcb_lo & Hcb_mid & Hcb_hi)".
  wp_apply (wp_bytes_to_string with "Hcb_mid"). iIntros "Hcb_mid".
  wp_auto.
  wp_alloc rs as "Hrs". wp_auto.
  (* n.content := string(cb[:diff]) *)
  rewrite decide_True; last word.
  wp_apply (wp_bytes_to_string with "Hcb_lo"). iIntros "Hcb_lo".
  wp_auto.
  (* ===== branch-agnostic pure run-telescoping facts (the split's model core) *)
  iDestruct (typed_pointsto_not_null with "Hrs") as %Hrsnn.
  (* the fresh right node's location misses the whole pool (issue #28 D2a):
     the parent's cells conflict through the opened DLL segments, the other
     types' through the delete-map big-sep *)
  iDestruct (own_dll_fresh with "Hrs Hseg1") as %Hfr_pre.
  iDestruct (own_dll_fresh with "Hrs Hrest") as %Hfr_suf.
  iAssert (⌜rs ≠ ic_loc cw⌝)%I as %Hfr_cw.
  { destruct (decide (rs = ic_loc cw)) as [Heqloc | Hneloc]; last by iPureIntro.
    iEval (rewrite Heqloc) in "Hrs".
    iDestruct (item_pointsto_conflict with "Hrs Hval") as %[]. }
  iDestruct (big_sepM_sep with "Hrestmap") as "[Hrestown Hrestinv]".
  iDestruct (all_cells_fresh rs _ (DfracOwn 1) (delete parent types) with "Hrs Hrestown") as %Hfr_rest.
  iAssert ([∗ map] p0 ↦ ts0 ∈ delete parent types,
      own_ytype_cells p0 (DfracOwn 1) (ty_cells ts0) (ty_arr ts0) ∗
      ⌜YjsArrInvariant (ty_arr ts0)⌝)%I with "[Hrestown Hrestinv]" as "Hrestmap".
  { rewrite big_sepM_sep. iFrame "Hrestown Hrestinv". }
  have Hrsfresh : rs ∉ ic_loc <$> all_cells types.
  { move=> Hin.
    rewrite (all_cells_lookup types parent _ Htypes) /= in Hin.
    rewrite -Hsplit in Hin.
    rewrite fmap_app in Hin. apply elem_of_app in Hin as [Hin | Hin].
    - rewrite fmap_app in Hin. apply elem_of_app in Hin as [Hin | Hin].
      + exact (Hfr_pre Hin).
      + rewrite fmap_cons in Hin. apply elem_of_cons in Hin as [Heqc | Hin].
        * exact (Hfr_cw Heqc).
        * exact (Hfr_suf Hin).
    - exact (Hfr_rest Hin). }
  set (o := uint.nat diff).
  have Hcwmem : cw ∈ all_cells types.
  { apply all_cells_elem_of. exists parent, (MkTypeState cells arr).
    split; [exact Htypes | exact (list_elem_of_lookup_2 _ _ _ Hcellk)]. }
  have Hnowrapcw := Hrunfits cw Hcwmem.
  have Hcwck : cell_clock cw = itemVal.(yjs.item.id').(yjs.id.clock').
  { rewrite /cell_clock Hid /toYjsId /=. word. }
  have Hsintlen : sint.nat cbs.(slice.len) = length cw.(ic_run).
  { rewrite -Hsclen. symmetry. exact Hcbwf1. }
  have Hsintdiff : sint.nat diff = o.
  { rewrite /o. word. }
  have Hoinrun : (o < length cw.(ic_run))%nat by (rewrite /o; lia).
  have Hrun0 : cw.(ic_run) !! 0%nat = Some (run_head cw).
  { rewrite /run_head. destruct Hrun as [Hne _]. destruct (ic_run cw) as [|a r']; [done | reflexivity]. }
  destruct (cw.(ic_run) !! o) as [yo|] eqn:Hyo; [| apply lookup_ge_None in Hyo; lia].
  have Hyoid := run_wf_lookup_clock cw.(ic_run) o (run_head cw) yo Hrun Hrun0 Hyo.
  have Hyoro := run_wf_lookup_rightOrigin cw.(ic_run) o (run_head cw) yo Hrun Hrun0 Hyo.
  iDestruct (typed_pointsto_not_null with "olid") as %Holidnn.
  iPersist "olid".
  have Hrhcl : run_head (split_cell_left cw o) = run_head cw.
  { rewrite /run_head /split_cell_left /=. apply hd_inhabitant_take. rewrite /o; lia. }
  have Hrhcr : run_head (split_cell_right cw o rs) = yo.
  { rewrite /run_head /split_cell_right /=. exact (hd_inhabitant_drop _ o yo Hyo). }
  have Hcontl : content <$> take o cw.(ic_run) = explode (take (sint.nat diff) itemVal.(yjs.item.content').(yjs.content.content')).
  { rewrite Hsintdiff fmap_take Hcontent /toContent /explode fmap_take //. }
  have Hsubdrop : subslice (sint.nat diff) (sint.nat cbs.(slice.len)) itemVal.(yjs.item.content').(yjs.content.content')
                = drop o itemVal.(yjs.item.content').(yjs.content.content').
  { rewrite Hsintdiff Hsintlen -Hsclen /subslice. rewrite take_ge; [reflexivity | lia]. }
  have Hcontr : content <$> drop o cw.(ic_run) = explode (drop o itemVal.(yjs.item.content').(yjs.content.content')).
  { rewrite fmap_drop Hcontent /toContent /explode fmap_drop //. }
  (* [if n.right != nil] branches on whether [cw] is the run's last cell (suf) *)
  destruct suf as [|d0 drest] eqn:Hsufeq.
  - (* cw is last: no downstream relink. Remaining: own_dll_split (cs2=[]),
       own_ytype_cells rebuild over split_cells, and the item-map surgery
       (getNodeIndex over the split run + client_run_loc_insert). *)
    (* ----- guard + n.right := rs ----- *)
    iDestruct "Hrest" as %[Hrnull Htl0eq].
    rewrite (bool_decide_eq_true_2 (itemVal.(yjs.item.right') = null) Hrnull).
    wp_auto.
    (* ----- branch-agnostic split-cell pure facts (origin telescoping) ----- *)
    set (leftCell := split_cell_left cw o).
    set (rightCell := split_cell_right cw o rs).
    set (originId := {| yjs.id.clientId' := itemVal.(yjs.item.id').(yjs.id.clientId');
                   yjs.id.clock' := word.sub (word.add itemVal.(yjs.item.id').(yjs.id.clock') diff) (W64 1) |}).
    have Hopos : (0 < o)%nat by (rewrite /o; lia).
    have Hnowrap_add : (uint.Z itemVal.(yjs.item.id').(yjs.id.clock') + uint.Z diff < 2^64)%Z.
    { rewrite -Hcwck. have H1 := Hnowrapcw. have H2 := Hdiff. word. }
    have Hadd_eq : (uint.nat itemVal.(yjs.item.id').(yjs.id.clock') + o)%nat = uint.nat (word.add itemVal.(yjs.item.id').(yjs.id.clock') diff).
    { rewrite /o. clear -Hnowrap_add. word. }
    have [xprev Hxprev] : is_Some (cw.(ic_run) !! (o - 1)%nat).
    { apply lookup_lt_is_Some. rewrite /o. lia. }
    have Hyo2 : cw.(ic_run) !! S (o - 1)%nat = Some yo.
    { replace (S (o - 1))%nat with o by (rewrite /o; lia). exact Hyo. }
    have Hstep := proj2 Hrun (o - 1)%nat xprev yo Hxprev Hyo2.
    have Horig : origin yo = itemPtr xprev by (destruct Hstep as [_ [Hh _]]; exact Hh).
    have Hxpid := run_wf_lookup_clock cw.(ic_run) (o - 1)%nat (run_head cw) xprev Hrun Hrun0 Hxprev.
    have Hcrorig : origin_id (origin (run_head rightCell)) = toYjsId <$> Some originId.
    { rewrite /rightCell Hrhcr Horig /origin_id /=. f_equal.
      rewrite Hxpid Hid /toYjsId /originId /=. f_equal. clear -Hnowrap_add Hdiff. word. }
    have Hrhck : clock (item_id (run_head cw)) = uint.nat itemVal.(yjs.item.id').(yjs.id.clock') by (rewrite Hid /toYjsId /=).
    have Hclcl : cell_clock leftCell = cell_clock cw by (rewrite /leftCell /cell_clock Hrhcl).
    have Hcccl : cell_client leftCell = cell_client cw by (rewrite /leftCell /cell_client Hrhcl).
    have Hcccr : cell_client rightCell = cell_client cw by (rewrite /rightCell /cell_client Hrhcr Hyoid /=).
    have Hccr_clock : uint.Z (cell_clock rightCell) = (uint.Z (cell_clock cw) + Z.of_nat o)%Z.
    { rewrite /rightCell /cell_clock Hrhcr Hyoid /= Hrhck. clear -Hnowrap_add Hdiff. rewrite /o. word. }
    have Hsc : split_cells cells k o rs = pre ++ leftCell :: rightCell :: [].
    { rewrite /split_cells Hcellk. rewrite -/suf Hsufeq. rewrite app_nil_r. reflexivity. }
    (* the split-cell struct values [ivl] (truncated cw) / [ivr] (right half) *)
    set (ivl := itemVal <| yjs.item.content' := {| yjs.content.content' := take (sint.nat diff) itemVal.(yjs.item.content').(yjs.content.content') |} |> <| yjs.item.right' := rs |>).
    set (ivr := {| yjs.item.id' := {| yjs.id.clientId' := itemVal.(yjs.item.id').(yjs.id.clientId'); yjs.id.clock' := word.add itemVal.(yjs.item.id').(yjs.id.clock') diff |};
                   yjs.item.originLeftId' := olid_ptr;
                   yjs.item.originRightId' := itemVal.(yjs.item.originRightId');
                   yjs.item.left' := cw.(ic_loc);
                   yjs.item.right' := itemVal.(yjs.item.right');
                   yjs.item.parent' := itemVal.(yjs.item.parent');
                   yjs.item.content' := {| yjs.content.content' := subslice (sint.nat diff) (sint.nat cbs.(slice.len)) itemVal.(yjs.item.content').(yjs.content.content') |};
                   yjs.item.flags' := itemVal.(yjs.item.flags') |}).
    have Hivl_ol : ivl.(yjs.item.originLeftId') = itemVal.(yjs.item.originLeftId') by (rewrite /ivl /=).
    have Hivl_or : ivl.(yjs.item.originRightId') = itemVal.(yjs.item.originRightId') by (rewrite /ivl /=).
    have Hivl_left : ivl.(yjs.item.left') = ml by (rewrite /ivl /=; exact Hprev).
    have Hivr_r : ivr.(yjs.item.right') = null by (rewrite /ivr /=; exact Hrnull).
    have Hrhcl' : run_head leftCell = run_head cw by (rewrite /leftCell; exact Hrhcl).
    have Hrhcr' : run_head rightCell = yo by (rewrite /rightCell; exact Hrhcr).
    have Hrhcli : clientId (item_id (run_head cw)) = uint.nat itemVal.(yjs.item.id').(yjs.id.clientId') by (rewrite Hid /toYjsId /=).
    have Hclloc : ic_loc leftCell = cw.(ic_loc) by (rewrite /leftCell /=).
    have Hcrloc : ic_loc rightCell = rs by (rewrite /rightCell /=).
    have Hivr_ol : ivr.(yjs.item.originLeftId') = olid_ptr by (rewrite /ivr /=).
    have Hivr_or : ivr.(yjs.item.originRightId') = itemVal.(yjs.item.originRightId') by (rewrite /ivr /=).
    have Hp1 : ic_loc leftCell ≠ null by (rewrite /leftCell /=; exact Hmfnn).
    have Hp2 : ic_loc rightCell ≠ null by (rewrite /rightCell /=; exact Hrsnn).
    have Hp4 : ivl.(yjs.item.right') = ic_loc rightCell by (rewrite /ivl /rightCell /=).
    have Hp5 : ivl.(yjs.item.parent') = ic_parent leftCell by (rewrite /ivl /leftCell /=; exact Hpar).
    have Hp6 : item_id (run_head leftCell) = toYjsId ivl.(yjs.item.id'). { rewrite Hrhcl' /ivl /=. exact Hid. }
    have Hp7 : content <$> ic_run leftCell = explode (toContent ivl.(yjs.item.content')). { rewrite /leftCell /ivl /toContent /=. exact Hcontl. }
    have Hp8 : origin_id (origin (run_head leftCell)) = toYjsId <$> olidcw. { rewrite Hrhcl'. exact Holid. }
    have Hp9 : origin_id (rightOrigin (run_head leftCell)) = toYjsId <$> oridcw. { rewrite Hrhcl'. exact Horid. }
    have Hp10 : ivl.(yjs.item.flags') = (if ic_deleted leftCell then W8 6 else W8 2). { rewrite /ivl /leftCell /=. exact Hflags. }
    have Hp11 : run_wf (ic_run leftCell). { rewrite /leftCell /=. exact (run_wf_take cw.(ic_run) o Hopos Hrun). }
    have Hp12 : ivr.(yjs.item.left') = ic_loc leftCell. { rewrite /ivr /leftCell /=. reflexivity. }
    have Hp13 : ivr.(yjs.item.parent') = ic_parent rightCell. { rewrite /ivr /rightCell /=. exact Hpar. }
    have Hp14 : item_id (run_head rightCell) = toYjsId ivr.(yjs.item.id'). { rewrite Hrhcr' Hyoid /ivr /toYjsId /=. rewrite Hrhck Hrhcli Hadd_eq. reflexivity. }
    have Hp15 : content <$> ic_run rightCell = explode (toContent ivr.(yjs.item.content')). { rewrite /rightCell /ivr /toContent /= Hsubdrop. exact Hcontr. }
    have Hp17 : origin_id (rightOrigin (run_head rightCell)) = toYjsId <$> oridcw. { rewrite Hrhcr' Hyoro. exact Horid. }
    have Hp18 : ivr.(yjs.item.flags') = (if ic_deleted rightCell then W8 6 else W8 2). { rewrite /ivr /rightCell /=. exact Hflags. }
    have Hp19 : run_wf (ic_run rightCell). { rewrite /rightCell /=. exact (run_wf_drop cw.(ic_run) o Hoinrun Hrun). }
    (* ----- read the client run slice (map.lookup1), BEFORE Phase A locks cw ----- *)
    iNamed "Hitemmap".
    set (kc := itemVal.(yjs.item.id').(yjs.id.clientId')).
    have Hcwcc : cell_client cw = kc by (rewrite /cell_client Hrhcli /kc; word).
    have Hkcin : kc ∈ (cell_client <$> all_cells types).
    { rewrite -Hcwcc. apply list_elem_of_fmap_2. exact Hcwmem. }
    have Hcwrun : cw ∈ client_run types kc.
    { apply client_run_mem. split; [exact Hcwmem | exact Hcwcc]. }
    apply list_elem_of_lookup_1 in Hcwrun. destruct Hcwrun as [kw Hkw].
    destruct (Hcomplete kc Hkcin) as [slk Hslk].
    iDestruct (big_sepM_lookup_acc _ _ kc slk Hslk with "Hruns") as "[Hrunslk Hrunsback]".
    iNamed "Hrunslk".
    wp_apply (wp_map_lookup1 with "Hmap"). iIntros "Hmap".
    rewrite Hslk /=.
    wp_auto.
    (* ----- Phase A: own_dll_split, own_ytype_cells rebuild, close over types2 ----- *)
    iAssert (own_dll (DfracOwn 1) yt.(yjs.yType.start') rs null null (split_cells cells k o rs))
      with "[Hseg1 Hval Holeft Horight Hrs]" as "Hdll2".
    { rewrite Hsc.
      iApply (own_dll_split (DfracOwn 1) pre (@nil item_cell) leftCell rightCell ivl ivr olidcw oridcw (Some originId) oridcw yt.(yjs.yType.start') rs ml Hp1 Hp2 Hivl_left Hp4 Hp5 Hp6 Hp7 Hp8 Hp9 Hp10 Hp11 Hp12 Hp13 Hp14 Hp15 Hcrorig Hp17 Hp18 Hp19).
      rewrite Hclloc Hcrloc Hivl_ol Hivl_or Hivr_ol Hivr_or Hivr_r.
      iDestruct "Horight" as "#HorightP".
      iFrame "Hseg1 Hval Hrs Holeft HorightP".
      iSplit.
      - simpl. iFrame "olid". iPureIntro. exact Holidnn.
      - simpl. iPureIntro. done. }
    have Hcparcw : ic_parent cw = parent by (apply Hcpar0; apply (list_elem_of_lookup_2 _ _ _ Hcellk)).
    have Hcpar_split : ∀ c, c ∈ split_cells cells k o rs -> ic_parent c = parent.
    { rewrite Hsc. move=> c Hc. apply elem_of_app in Hc as [Hc | Hc].
      - apply Hcpar0. rewrite -Hsplit. apply elem_of_app; by left.
      - apply elem_of_cons in Hc as [-> | Hc]; [rewrite /leftCell /=; exact Hcparcw |].
        apply elem_of_cons in Hc as [-> | Hc]; [rewrite /rightCell /=; exact Hcparcw | by apply elem_of_nil in Hc]. }
    iAssert (own_ytype_cells parent (DfracOwn 1) (split_cells cells k o rs) arr) with "[Hparent Hdll2]" as "Hyt2".
    { iExists yt, rs. iFrame "Hparent Hdll2". iPureIntro. split_and!.
      - rewrite (split_cells_num_visible cells k o rs cw Hcellk). exact Hlen0.
      - rewrite /cells_repr (split_cells_flatten cells k o rs cw Hcellk). exact Hrepr0.
      - exact Hcpar_split. }
    iAssert ([∗ map] p0 ↦ ts0 ∈ <[parent := {| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types,
        own_ytype_cells p0 (DfracOwn 1) (ty_cells ts0) (ty_arr ts0) ∗
        ⌜YjsArrInvariant (ty_arr ts0)⌝)%I with "[Hyt2 Hrestmap]" as "Htypes2".
    { rewrite -insert_delete_eq big_sepM_insert_delete delete_delete_eq.
      iFrame "Hrestmap". simpl. iFrame "Hyt2". iPureIntro. exact Harrinv. }
    (* ----- getNodeIndex over the split run [run_half] = client_run with cw -> leftCell ----- *)
    have Hss_replace : ∀ (ll : list item_cell) (i : nat) (a b : item_cell),
        StronglySorted cell_le ll → ll !! i = Some a → cell_clock b = cell_clock a →
        StronglySorted cell_le (<[i:=b]> ll).
    { elim => [| c ll IH] i a b Hss Hi Hclk.
      - by rewrite /=.
      - apply StronglySorted_inv in Hss as [Hssll Hfa].
        destruct i as [|i']; simpl.
        + simpl in Hi. injection Hi as Hca. rewrite Hca in Hfa.
          apply SSorted_cons; [exact Hssll |].
          apply Forall_forall => x Hx. rewrite /cell_le Hclk.
          exact (proj1 (Forall_forall _ _) Hfa x Hx).
        + apply SSorted_cons; [exact (IH i' a b Hssll Hi Hclk) |].
          apply Forall_insert; [exact Hfa |].
          rewrite /cell_le Hclk.
          exact (proj1 (Forall_forall _ _) Hfa a (list_elem_of_lookup_2 ll i' a Hi)). }
    have Hss_half : StronglySorted cell_le (<[kw := leftCell]> (client_run types kc)) := Hss_replace (client_run types kc) kw cw leftCell (client_run_sorted types kc) Hkw Hclcl.
    set (run_half := <[kw := leftCell]> (client_run types kc)).
    have HndAll : NoDup (all_cells types) := NoDup_fmap_1 ic_loc _ Hnodup.
    have Hndrun : NoDup (client_run types kc).
    { rewrite /client_run (merge_sort_Permutation cell_le _). apply NoDup_filter. exact HndAll. }
    have Hkwlt : (kw < length (client_run types kc))%nat by (apply lookup_lt_Some in Hkw; exact Hkw).
    have Hlockw : (ic_loc <$> client_run types kc) !! kw = Some (ic_loc leftCell).
    { rewrite list_lookup_fmap Hkw /=. done. }
    have Hlocs : ic_loc <$> run_half = ic_loc <$> client_run types kc.
    { rewrite /run_half list_fmap_insert (list_insert_id _ _ _ Hlockw) //. }
    have Hkw_half : run_half !! kw = Some leftCell.
    { rewrite /run_half. apply list_lookup_insert_Some. left. split_and!; [reflexivity | reflexivity | exact Hkwlt]. }
    have Hclk_half : cell_clock leftCell = itemVal.(yjs.item.id').(yjs.id.clock') by (rewrite Hclcl Hcwck).
    have Hsub : ∀ c, c ∈ run_half → c = leftCell ∨ c ∈ client_run types kc.
    { move=> c Hc. apply list_elem_of_lookup_1 in Hc as [j Hj]. rewrite /run_half in Hj.
      apply list_lookup_insert_Some in Hj as [(_ & <- & _) | (_ & Hj)]; [by left | right; exact (list_elem_of_lookup_2 _ _ _ Hj)]. }
    have Hfits_half : ∀ c, c ∈ run_half → (uint.Z (cell_clock c) + length (ic_run c) < 2^64)%Z.
    { move=> c Hc. destruct (Hsub c Hc) as [-> | HcL].
      - rewrite Hclcl /leftCell /= length_take. have H := Hnowrapcw. lia.
      - exact (Hrunfits c (proj1 (proj1 (client_run_mem types kc c) HcL))). }
    have Hmem_half : ∀ c, c ∈ run_half → c ∈ all_cells (<[parent := {| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types).
    { move=> c Hc. apply list_elem_of_lookup_1 in Hc as [j Hj]. rewrite /run_half in Hj.
      apply list_lookup_insert_Some in Hj as [(_ & <- & _) | (Hne & Hj)].
      - apply all_cells_elem_of. exists parent, {| ty_cells := split_cells cells k o rs; ty_arr := arr |}.
        split; [apply lookup_insert_eq |]. rewrite /= Hsc. apply elem_of_app; right. apply list_elem_of_here.
      - have HcL : c ∈ client_run types kc := list_elem_of_lookup_2 _ _ _ Hj.
        have Hcne : c ≠ cw. { move=> Heq. rewrite Heq in Hj. exact (Hne (NoDup_lookup _ _ _ _ Hndrun Hkw Hj)). }
        have Hcall : c ∈ all_cells types := proj1 (proj1 (client_run_mem types kc c) HcL).
        apply all_cells_elem_of in Hcall as (p & ts & Hp & Hcts).
        destruct (decide (p = parent)) as [-> | Hpne].
        + rewrite Htypes in Hp. injection Hp as <-. simpl in Hcts.
          rewrite -Hsplit in Hcts. apply elem_of_app in Hcts as [Hcpre | Hcw].
          * apply all_cells_elem_of. exists parent, {| ty_cells := split_cells cells k o rs; ty_arr := arr |}.
            split; [apply lookup_insert_eq |]. rewrite /= Hsc. apply elem_of_app; by left.
          * apply list_elem_of_singleton in Hcw. done.
        + apply all_cells_elem_of. exists p, ts.
          split; [rewrite lookup_insert_ne; [exact Hp | congruence] | exact Hcts]. }
    iEval (rewrite -Hlocs) in "Hslice".
    wp_apply (wp_getNodeIndex slk (DfracOwn 1) (<[parent := {| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) run_half (itemVal.(yjs.item.id').(yjs.id.clock')) kw leftCell Hss_half Hmem_half Hfits_half Hkw_half Hclk_half with "[$Hslice $Htypes2]").
    iIntros (idx) "(Hslice & Htypes2 & %Hires)".
    destruct Hires as (cres & Hcres & Hcresle & Hcreslt).
    (* pin [uint.nat idx = kw]: the covering cell in [run_half] is [leftCell] (NoDup locs) *)
    have Hinj : ∀ x y, x ∈ client_run types kc → y ∈ client_run types kc → ic_loc x = ic_loc y → x = y.
    { move=> x y Hx Hy Hxy.
      have Hxa : x ∈ all_cells types := proj1 (proj1 (client_run_mem types kc x) Hx).
      have Hya : y ∈ all_cells types := proj1 (proj1 (client_run_mem types kc y) Hy).
      apply list_elem_of_lookup_1 in Hxa as [ix Hix]. apply list_elem_of_lookup_1 in Hya as [iy Hiy].
      have Hlix : (ic_loc <$> all_cells types) !! ix = Some (ic_loc y) by (rewrite list_lookup_fmap Hix /= Hxy //).
      have Hliy : (ic_loc <$> all_cells types) !! iy = Some (ic_loc y) by (rewrite list_lookup_fmap Hiy //).
      have Hijeq : ix = iy := NoDup_lookup _ _ _ _ Hnodup Hlix Hliy.
      congruence. }
    have HndLocRun : NoDup (ic_loc <$> client_run types kc).
    { apply NoDup_fmap_inj_on; [exact Hinj | exact Hndrun]. }
    have Hcresmem : cres ∈ run_half := list_elem_of_lookup_2 _ _ _ Hcres.
    have Hcresloc : ic_loc cres = ic_loc leftCell.
    { destruct (Hsub cres Hcresmem) as [-> | HcresL]; [reflexivity |].
      have Hcresall : cres ∈ all_cells types := proj1 (proj1 (client_run_mem types kc cres) HcresL).
      have Hcrescc : cell_client cres = cell_client cw.
      { rewrite (proj2 (proj1 (client_run_mem types kc cres) HcresL)) -Hcwcc //. }
      destruct (decide (ic_loc cres = ic_loc cw)) as [Heq | Hne].
      - rewrite Heq Hclloc //.
      - exfalso. rewrite -Hcwck in Hcresle Hcreslt.
        destruct (Hdisj cres Hcresall Hcrescc Hne) as [Hd | Hd]; lia. }
    have Hidxloc : (ic_loc <$> run_half) !! (uint.nat idx) = Some (ic_loc leftCell) by (rewrite list_lookup_fmap Hcres /= Hcresloc //).
    have Hkwloc : (ic_loc <$> run_half) !! kw = Some (ic_loc leftCell) by (rewrite list_lookup_fmap Hkw_half //).
    have HndLocRunHalf : NoDup (ic_loc <$> run_half) by (rewrite Hlocs; exact HndLocRun).
    have Hidxkw : uint.nat idx = kw := NoDup_lookup _ _ _ _ HndLocRunHalf Hidxloc Hkwloc.
    have Hcrescl : cres = leftCell.
    { have Htmp : run_half !! kw = Some cres by (rewrite -Hidxkw; exact Hcres). congruence. }
    iEval (rewrite Hlocs) in "Hslice".
    (* ----- the append-based item-map surgery (no length-fit side condition:
       append's growth is modeled with an overflow assume, so no client-run
       capacity premise is needed, unlike a pre-sized make) ----- *)
    iDestruct (own_slice_len with "Hslice") as %[Hslklen Hslklen0].
    rewrite length_fmap in Hslklen Hslklen0.
    have Hkwlt2 : (kw < length (client_run types kc))%nat by (apply lookup_lt_Some in Hkw).
    have Hidxsint : sint.Z idx = Z.of_nat kw by (move: Hslklen Hslklen0 Hkwlt2; rewrite -Hidxkw => ? ? ?; word).
    wp_auto.
    iDestruct (own_slice_wf with "Hslice") as %Hslkwf.
    (* newNodes = append(nil, nodes[:index+1]...) *)
    rewrite decide_True; last word.
    wp_auto.
    have Hsplitbnd : (0 ≤ sint.Z (w64_word_instance.(word.add) idx (W64 1)) ≤ sint.Z slk.(slice.len) ≤ sint.Z slk.(slice.len))%Z by word.
    iDestruct (own_slice_slice (w64_word_instance.(word.add) idx (W64 1)) slk.(slice.len) slk (DfracOwn 1) (ic_loc <$> client_run types kc) Hsplitbnd with "Hslice") as "(Hsl_pre & Hsl_suf & Hsl_tail)".
    iAssert (slice.nil ↦* ([] : list loc))%I with "[]" as "Hnil0"; first iApply own_slice_nil.
    iAssert (own_slice_cap loc slice.nil (DfracOwn 1))%I with "[]" as "Hnilcap"; first iApply own_slice_cap_nil.
    wp_apply (wp_slice_append with "[Hnil0 Hnilcap Hsl_pre]"); first (iFrame "Hnil0 Hnilcap Hsl_pre").
    iIntros (sl1) "(Hsl1 & Hsl1cap & Hsl_pre)".
    wp_auto.
    (* newNodes = append(newNodes, right) *)
    wp_apply wp_slice_literal. iSplitR; first done. iIntros "%slit [Hslit _]". wp_auto.
    wp_apply (wp_slice_append with "[Hsl1 Hsl1cap Hslit]"); first (iFrame "Hsl1 Hsl1cap Hslit").
    iIntros (sl2) "(Hsl2 & Hsl2cap & _)".
    wp_auto.
    (* newNodes = append(newNodes, nodes[index+1:]...) *)
    rewrite decide_True; last word.
    wp_auto.
    wp_apply (wp_slice_append with "[Hsl2 Hsl2cap Hsl_suf]"); first (iFrame "Hsl2 Hsl2cap Hsl_suf").
    iIntros (newSl) "(HnewNodes & HnewCap & Hsl_suf)".
    wp_auto.
    have HnkB : sint.nat (w64_word_instance.(word.add) idx (W64 1)) = (kw + 1)%nat.
    { move: Hslklen Hslklen0 Hkwlt2 Hidxsint => ? ? ? ?. word. }
    have Esrc : subslice (sint.nat (w64_word_instance.(word.add) idx (W64 1))) (sint.nat slk.(slice.len)) (ic_loc <$> client_run types kc) = drop (kw + 1) (ic_loc <$> client_run types kc).
    { rewrite HnkB -Hslklen /subslice take_ge; [reflexivity | rewrite length_fmap; clear -Hkwlt2; lia]. }
    have Elit : <[sint.nat (W64 0) := rs]> ([null] : list loc) = [rs].
    { have -> : sint.nat (W64 0) = 0%nat by word. reflexivity. }
    have Eall : (([] ++ take (sint.nat (w64_word_instance.(word.add) idx (W64 1))) (ic_loc <$> client_run types kc)) ++ <[sint.nat (W64 0) := rs]> ([null] : list loc)) ++ subslice (sint.nat (w64_word_instance.(word.add) idx (W64 1))) (sint.nat slk.(slice.len)) (ic_loc <$> client_run types kc) = take (kw + 1) (ic_loc <$> client_run types kc) ++ rs :: drop (kw + 1) (ic_loc <$> client_run types kc).
    { rewrite Esrc Elit HnkB app_nil_l -app_assoc /=. reflexivity. }
    iEval (rewrite Eall) in "HnewNodes".
    iAssert (slk ↦* (ic_loc <$> client_run types kc))%I with "[Hsl_pre Hsl_suf Hsl_tail]" as "Hslice".
    { rewrite (own_slice_slice (w64_word_instance.(word.add) idx (W64 1)) slk.(slice.len) slk (DfracOwn 1) (ic_loc <$> client_run types kc) Hsplitbnd). iFrame. }
    (* s.items[client] = newNodes: the key read borrows cl's node back from types2 *)
    have Hklt : (k < length cells)%nat by (apply lookup_lt_Some in Hcellk).
    have Hsck : split_cells cells k o rs !! k = Some leftCell.
    { rewrite Hsc /pre lookup_app_r; last (rewrite length_take; clear -Hklt; lia).
      rewrite length_take Nat.min_l; last (clear -Hklt; lia).
      have -> : (k - k)%nat = 0%nat by (clear -k; lia).
      reflexivity. }
    have Hlk2 : (<[parent:={| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) !! parent = Some {| ty_cells := split_cells cells k o rs; ty_arr := arr |} by apply lookup_insert_eq.
    iDestruct (big_sepM_lookup_acc _ _ parent {| ty_cells := split_cells cells k o rs; ty_arr := arr |} Hlk2 with "Htypes2") as "[(Hpc2 & %Harrinv2) Hclose2]".
    iDestruct "Hpc2" as (yt2 tl2) "(Hparent2 & Hdll2 & %Hlen2 & %Hrepr2 & %Hcpar2)".
    iDestruct (own_dll_acc (DfracOwn 1) (split_cells cells k o rs) yt2.(yjs.yType.start') tl2 k leftCell Hsck with "Hdll2") as (iv2 olid2 orid2) "(%Hcloc2 & %Hcl2 & %Hcr2 & %Hid2 & %Hcontent2 & %Holid2 & %Horid2 & %Hflags2 & %Hrun2 & %Hpar2 & Hcval2 & Hcol2 & Hcor2 & Hback2)".
    iEval (rewrite Hclloc) in "Hcval2".
    have Hkey : iv2.(yjs.item.id').(yjs.id.clientId') = kc.
    { move: Hid2. rewrite Hrhcl' Hid /toYjsId /=. move=> Heq.
      have Hc1 := f_equal clientId Heq. simpl in Hc1. rewrite /kc.
      clear -Hc1. word. }
    wp_auto.
    wp_apply (wp_map_insert with "Hmap").
    iIntros "Hmap".
    iEval (rewrite Hkey) in "Hmap".
    iEval (rewrite -Hclloc) in "Hcval2".
    iDestruct ("Hback2" with "Hcval2") as "Hdll2".
    iAssert (own_ytype_cells parent (DfracOwn 1) (split_cells cells k o rs) arr) with "[Hparent2 Hdll2]" as "Hyt2b".
    { iExists yt2, tl2. iFrame "Hparent2 Hdll2". iPureIntro.
      split_and!; [exact Hlen2 | exact Hrepr2 | exact Hcpar2]. }
    iDestruct ("Hclose2" with "[Hyt2b]") as "Htypes2"; first (iFrame "Hyt2b"; iPureIntro; exact Harrinv2).
    (* the item-map model surgery: the right half's loc lands at position kw+1 *)
    have Hkpcl : cell_kp leftCell = cell_kp cw.
    { rewrite /cell_kp /cell_pr Hcccl Hclcl Hclloc. reflexivity. }
    have Hkp : cell_kp <$> all_cells (<[parent:={| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) ≡ₚ (cell_kp <$> all_cells types) ++ [cell_kp rightCell].
    { etransitivity.
      { apply Permutation_map.
        exact (all_cells_insert types parent {| ty_cells := cells; ty_arr := arr |} {| ty_cells := split_cells cells k o rs; ty_arr := arr |} Htypes). }
      simpl. rewrite Hsc.
      etransitivity; last first.
      { apply Permutation_app_tail. apply Permutation_map. symmetry.
        exact (all_cells_lookup types parent {| ty_cells := cells; ty_arr := arr |} Htypes). }
      simpl. rewrite -Hsplit !map_app /= Hkpcl -!app_assoc /=.
      apply Permutation_app_head. apply perm_skip. apply Permutation_cons_append. }
    have Hbef : forall y, y ∈ take (kw + 1) (client_run types (cell_client rightCell)) -> ((cell_pr y).1 < (cell_pr rightCell).1)%Z.
    { move=> y Hy.
      rewrite Hcccr Hcwcc in Hy.
      apply list_elem_of_lookup_1 in Hy as [j Hj].
      apply lookup_take_Some in Hj as [Hj Hjlt].
      have Hple : (uint.Z (cell_clock y) <= uint.Z (cell_clock cw))%Z.
      { destruct (decide (j = kw)) as [-> | Hne].
        - rewrite Hkw in Hj. injection Hj as <-. lia.
        - exact (StronglySorted_lookup_le cell_le (client_run types kc) j kw y cw (client_run_sorted types kc) Hj Hkw ltac:(clear -Hjlt Hne; lia)). }
      rewrite /cell_pr /= Hccr_clock. clear -Hple Hopos. lia. }
    have Haft : forall y, y ∈ drop (kw + 1) (client_run types (cell_client rightCell)) -> ((cell_pr rightCell).1 < (cell_pr y).1)%Z.
    { move=> y Hy.
      rewrite Hcccr Hcwcc in Hy.
      apply list_elem_of_lookup_1 in Hy as [j Hj].
      rewrite lookup_drop in Hj.
      have HyCR : y ∈ client_run types kc := list_elem_of_lookup_2 _ _ _ Hj.
      have Hyall : y ∈ all_cells types := proj1 (proj1 (client_run_mem types kc y) HyCR).
      have Hycc : cell_client y = cell_client cw.
      { rewrite (proj2 (proj1 (client_run_mem types kc y) HyCR)) Hcwcc //. }
      have Hyne : y ≠ cw.
      { move=> Heq. rewrite Heq in Hj.
        have := NoDup_lookup _ _ _ _ Hndrun Hkw Hj. clear -k. lia. }
      have Hylocne : y.(ic_loc) ≠ cw.(ic_loc).
      { move=> Heq. apply Hyne. exact (Hinj y cw HyCR (list_elem_of_lookup_2 _ _ _ Hkw) Heq). }
      have Hle : (uint.Z (cell_clock cw) <= uint.Z (cell_clock y))%Z.
      { exact (StronglySorted_lookup_le cell_le (client_run types kc) kw (kw + 1 + j) cw y (client_run_sorted types kc) Hkw Hj ltac:(clear -k; lia)). }
      rewrite /cell_pr /= Hccr_clock.
      destruct (Hdisj y Hyall Hycc Hylocne) as [Hd | Hd].
      - exfalso.
        have Hyeq : uint.Z (cell_clock y) = uint.Z (cell_clock cw) by (clear -Hd Hle; lia).
        apply Hylocne. apply (Hclkloc y cw Hyall Hcwmem Hycc).
        rewrite /cell_pr /=. exact Hyeq.
      - clear -Hd Hoinrun. lia. }
    have Hrun_eq := client_run_loc_insert types (<[parent:={| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) rightCell (kw + 1) Hkp Hclkloc Hbef Haft.
    rewrite Hcccr Hcwcc Hcrloc in Hrun_eq.
    iEval (rewrite -Hrun_eq) in "HnewNodes".
    (* re-establish the own_item_map side conditions over types2 *)
    have HinjAll : forall x y, x ∈ all_cells types -> y ∈ all_cells types -> x.(ic_loc) = y.(ic_loc) -> x = y.
    { move=> x y Hx Hy Hxy.
      apply list_elem_of_lookup_1 in Hx as [ix Hix]. apply list_elem_of_lookup_1 in Hy as [iy Hiy].
      have Hlix : (ic_loc <$> all_cells types) !! ix = Some (y.(ic_loc)) by (rewrite list_lookup_fmap Hix /= Hxy //).
      have Hliy : (ic_loc <$> all_cells types) !! iy = Some (y.(ic_loc)) by (rewrite list_lookup_fmap Hiy //).
      have Hijeq : ix = iy := NoDup_lookup _ _ _ _ Hnodup Hlix Hliy.
      congruence. }
    have Hdecomp : forall c0, c0 ∈ all_cells (<[parent:={| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) -> c0 ∈ all_cells types \/ c0 = leftCell \/ c0 = rightCell.
    { move=> c0 Hc0.
      have Hp := all_cells_insert types parent {| ty_cells := cells; ty_arr := arr |} {| ty_cells := split_cells cells k o rs; ty_arr := arr |} Htypes.
      rewrite Hp /= Hsc in Hc0.
      apply elem_of_app in Hc0 as [Hc0 | Hc0].
      - apply elem_of_app in Hc0 as [Hc0 | Hc0].
        + left. apply all_cells_elem_of. exists parent, {| ty_cells := cells; ty_arr := arr |}.
          split; [exact Htypes |]. simpl. rewrite -Hsplit. apply elem_of_app. by left.
        + apply elem_of_cons in Hc0 as [-> | Hc0]; [by right; left |].
          apply elem_of_cons in Hc0 as [-> | Hc0]; [by right; right | by apply elem_of_nil in Hc0].
      - left.
        have Hq := all_cells_lookup types parent {| ty_cells := cells; ty_arr := arr |} Htypes.
        rewrite Hq /=. apply elem_of_app. by right. }
    have Hcomplete2 : forall c0 : w64, c0 ∈ cell_client <$> all_cells (<[parent:={| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) -> is_Some (<[kc := newSl]> gm !! c0).
    { move=> c0 Hc0. apply list_elem_of_fmap in Hc0 as (cc & -> & Hcc0).
      destruct (Hdecomp cc Hcc0) as [Hin | [-> | ->]].
      - destruct (decide (cell_client cc = kc)) as [He | Hne].
        + rewrite He lookup_insert_eq. eauto.
        + rewrite lookup_insert_ne; [| congruence]. apply Hcomplete. apply list_elem_of_fmap_2. exact Hin.
      - rewrite Hcccl Hcwcc lookup_insert_eq. eauto.
      - rewrite Hcccr Hcwcc lookup_insert_eq. eauto. }
    have HF2 : forall c, c ∈ all_cells types -> cell_client c = cell_client cw -> (cell_pr c).1 = (cell_pr rightCell).1 -> False.
    { move=> c Hc Hcc Hpr.
      rewrite /cell_pr /= Hccr_clock in Hpr.
      destruct (decide (c.(ic_loc) = cw.(ic_loc))) as [He | Hne].
      - have Heq : c = cw := HinjAll c cw Hc Hcwmem He.
        rewrite Heq in Hpr. clear -Hpr Hopos. lia.
      - destruct (Hdisj c Hc Hcc Hne) as [Hd | Hd].
        + clear -Hd Hpr Hopos. lia.
        + clear -Hd Hpr Hoinrun. lia. }
    have Hprcl : (cell_pr leftCell).1 = (cell_pr cw).1 by (rewrite /cell_pr /= Hclcl //).
    have Hclkloc2 : forall c1 c2, c1 ∈ all_cells (<[parent:={| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) -> c2 ∈ all_cells (<[parent:={| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) -> cell_client c1 = cell_client c2 -> (cell_pr c1).1 = (cell_pr c2).1 -> c1.(ic_loc) = c2.(ic_loc).
    { move=> c1 c2 Hc1 Hc2 Hcc Hpr.
      destruct (Hdecomp c1 Hc1) as [Hin1 | [-> | ->]]; destruct (Hdecomp c2 Hc2) as [Hin2 | [-> | ->]].
      - exact (Hclkloc c1 c2 Hin1 Hin2 Hcc Hpr).
      - rewrite Hclloc.
        apply (Hclkloc c1 cw Hin1 Hcwmem); [rewrite Hcc Hcccl // | rewrite Hpr Hprcl //].
      - exfalso. apply (HF2 c1 Hin1); [rewrite Hcc Hcccr // | exact Hpr].
      - rewrite Hclloc. symmetry.
        apply (Hclkloc c2 cw Hin2 Hcwmem); [rewrite -Hcc Hcccl // | rewrite -Hpr Hprcl //].
      - reflexivity.
      - exfalso. rewrite /cell_pr /= Hclcl Hccr_clock in Hpr. clear -Hpr Hopos. lia.
      - exfalso. apply (HF2 c2 Hin2); [rewrite -Hcc Hcccr // | rewrite -Hpr //].
      - exfalso. rewrite /cell_pr /= Hclcl Hccr_clock in Hpr. clear -Hpr Hopos. lia.
      - reflexivity. }
    iDestruct ("Hrunsback" with "[$Hslice $Hcap]") as "Hruns".
    iAssert (own_item_map mref (DfracOwn 1) (<[parent:={| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types)) with "[Hmap HnewNodes HnewCap Hruns]" as "Hitemmap2".
    { iExists (<[kc := newSl]> gm). iFrame "Hmap".
      iSplitL "HnewNodes HnewCap Hruns".
      - rewrite big_sepM_insert_delete. iSplitL "HnewNodes HnewCap"; [iFrame |].
        iDestruct (big_sepM_delete _ _ kc slk Hslk with "Hruns") as "[_ Hrest]".
        iApply (big_sepM_impl with "Hrest").
        iIntros "!#" (client s0 Hcs) "H". iNamed "H".
        have Hne2 : client ≠ cell_client rightCell.
        { rewrite Hcccr Hcwcc. move=> Heqc. rewrite Heqc lookup_delete_eq in Hcs. discriminate. }
        rewrite (client_run_loc_other types (<[parent:={| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) rightCell client Hkp Hclkloc Hne2). iFrame.
      - iPureIntro. split; [exact Hcomplete2 | exact Hclkloc2]. }
    wp_auto.
    iApply ("HΦ" $! rs).
    iFrame "Hitemsf Hitemmap2 Htypes2".
    iPureIntro. split; [exact Hrsnn | exact Hrsfresh].
  - (* cw has a right neighbour d0: relink d0.left := right, then the same DLL
       split, ytype rebuild, getNodeIndex pin, and item-map surgery as the
       last-cell branch (suf = d0 :: drest threads through own_dll_split's cs2
       and the split_cells shape; the item-map tail is otherwise identical). *)
    iDestruct "Hrest" as (ivd olidd oridd) "(%Hlocd & %Hprevd & %Hpard & %Hidd & %Hcontentd & %Holidd & %Horidd & %Hflagsd & %Hrund & Hvald & Holeftd & Horightd & Hrestd)".
    destruct Hlocd as [Hlocd1 Hlocdnn].
    (* ----- guard (n.right ≠ nil): relink d0.left := right, then n.right := rs ----- *)
    rewrite (bool_decide_eq_false_2 (itemVal.(yjs.item.right') = null) Hlocdnn).
    iEval (rewrite -Hlocd1) in "Hvald".
    wp_auto.
    iEval (rewrite Hlocd1) in "Hvald".
    set (ivd2 := ivd <| yjs.item.left' := rs |>).
    have Hd2l : ivd2.(yjs.item.left') = rs by reflexivity.
    have Hd2r : ivd2.(yjs.item.right') = ivd.(yjs.item.right') by reflexivity.
    have Hd2p : ivd2.(yjs.item.parent') = ivd.(yjs.item.parent') by reflexivity.
    have Hd2id : ivd2.(yjs.item.id') = ivd.(yjs.item.id') by reflexivity.
    have Hd2c : ivd2.(yjs.item.content') = ivd.(yjs.item.content') by reflexivity.
    have Hd2ol : ivd2.(yjs.item.originLeftId') = ivd.(yjs.item.originLeftId') by reflexivity.
    have Hd2or : ivd2.(yjs.item.originRightId') = ivd.(yjs.item.originRightId') by reflexivity.
    have Hd2f : ivd2.(yjs.item.flags') = ivd.(yjs.item.flags') by reflexivity.
    (* ----- branch-agnostic split-cell pure facts (origin telescoping) ----- *)
    set (leftCell := split_cell_left cw o).
    set (rightCell := split_cell_right cw o rs).
    set (originId := {| yjs.id.clientId' := itemVal.(yjs.item.id').(yjs.id.clientId');
                   yjs.id.clock' := word.sub (word.add itemVal.(yjs.item.id').(yjs.id.clock') diff) (W64 1) |}).
    have Hopos : (0 < o)%nat by (rewrite /o; lia).
    have Hnowrap_add : (uint.Z itemVal.(yjs.item.id').(yjs.id.clock') + uint.Z diff < 2^64)%Z.
    { rewrite -Hcwck. have H1 := Hnowrapcw. have H2 := Hdiff. word. }
    have Hadd_eq : (uint.nat itemVal.(yjs.item.id').(yjs.id.clock') + o)%nat = uint.nat (word.add itemVal.(yjs.item.id').(yjs.id.clock') diff).
    { rewrite /o. clear -Hnowrap_add. word. }
    have [xprev Hxprev] : is_Some (cw.(ic_run) !! (o - 1)%nat).
    { apply lookup_lt_is_Some. rewrite /o. lia. }
    have Hyo2 : cw.(ic_run) !! S (o - 1)%nat = Some yo.
    { replace (S (o - 1))%nat with o by (rewrite /o; lia). exact Hyo. }
    have Hstep := proj2 Hrun (o - 1)%nat xprev yo Hxprev Hyo2.
    have Horig : origin yo = itemPtr xprev by (destruct Hstep as [_ [Hh _]]; exact Hh).
    have Hxpid := run_wf_lookup_clock cw.(ic_run) (o - 1)%nat (run_head cw) xprev Hrun Hrun0 Hxprev.
    have Hcrorig : origin_id (origin (run_head rightCell)) = toYjsId <$> Some originId.
    { rewrite /rightCell Hrhcr Horig /origin_id /=. f_equal.
      rewrite Hxpid Hid /toYjsId /originId /=. f_equal. clear -Hnowrap_add Hdiff. word. }
    have Hrhck : clock (item_id (run_head cw)) = uint.nat itemVal.(yjs.item.id').(yjs.id.clock') by (rewrite Hid /toYjsId /=).
    have Hclcl : cell_clock leftCell = cell_clock cw by (rewrite /leftCell /cell_clock Hrhcl).
    have Hcccl : cell_client leftCell = cell_client cw by (rewrite /leftCell /cell_client Hrhcl).
    have Hcccr : cell_client rightCell = cell_client cw by (rewrite /rightCell /cell_client Hrhcr Hyoid /=).
    have Hccr_clock : uint.Z (cell_clock rightCell) = (uint.Z (cell_clock cw) + Z.of_nat o)%Z.
    { rewrite /rightCell /cell_clock Hrhcr Hyoid /= Hrhck. clear -Hnowrap_add Hdiff. rewrite /o. word. }
    have Hsc : split_cells cells k o rs = pre ++ leftCell :: rightCell :: d0 :: drest.
    { rewrite /split_cells Hcellk. rewrite -/suf Hsufeq. reflexivity. }
    (* the split-cell struct values [ivl] (truncated cw) / [ivr] (right half) *)
    set (ivl := itemVal <| yjs.item.content' := {| yjs.content.content' := take (sint.nat diff) itemVal.(yjs.item.content').(yjs.content.content') |} |> <| yjs.item.right' := rs |>).
    set (ivr := {| yjs.item.id' := {| yjs.id.clientId' := itemVal.(yjs.item.id').(yjs.id.clientId'); yjs.id.clock' := word.add itemVal.(yjs.item.id').(yjs.id.clock') diff |};
                   yjs.item.originLeftId' := olid_ptr;
                   yjs.item.originRightId' := itemVal.(yjs.item.originRightId');
                   yjs.item.left' := cw.(ic_loc);
                   yjs.item.right' := itemVal.(yjs.item.right');
                   yjs.item.parent' := itemVal.(yjs.item.parent');
                   yjs.item.content' := {| yjs.content.content' := subslice (sint.nat diff) (sint.nat cbs.(slice.len)) itemVal.(yjs.item.content').(yjs.content.content') |};
                   yjs.item.flags' := itemVal.(yjs.item.flags') |}).
    have Hivl_ol : ivl.(yjs.item.originLeftId') = itemVal.(yjs.item.originLeftId') by (rewrite /ivl /=).
    have Hivl_or : ivl.(yjs.item.originRightId') = itemVal.(yjs.item.originRightId') by (rewrite /ivl /=).
    have Hivl_left : ivl.(yjs.item.left') = ml by (rewrite /ivl /=; exact Hprev).
    have Hivr_r : ivr.(yjs.item.right') = itemVal.(yjs.item.right') by reflexivity.
    have Hrhcl' : run_head leftCell = run_head cw by (rewrite /leftCell; exact Hrhcl).
    have Hrhcr' : run_head rightCell = yo by (rewrite /rightCell; exact Hrhcr).
    have Hrhcli : clientId (item_id (run_head cw)) = uint.nat itemVal.(yjs.item.id').(yjs.id.clientId') by (rewrite Hid /toYjsId /=).
    have Hclloc : ic_loc leftCell = cw.(ic_loc) by (rewrite /leftCell /=).
    have Hcrloc : ic_loc rightCell = rs by (rewrite /rightCell /=).
    have Hivr_ol : ivr.(yjs.item.originLeftId') = olid_ptr by (rewrite /ivr /=).
    have Hivr_or : ivr.(yjs.item.originRightId') = itemVal.(yjs.item.originRightId') by (rewrite /ivr /=).
    have Hp1 : ic_loc leftCell ≠ null by (rewrite /leftCell /=; exact Hmfnn).
    have Hp2 : ic_loc rightCell ≠ null by (rewrite /rightCell /=; exact Hrsnn).
    have Hp4 : ivl.(yjs.item.right') = ic_loc rightCell by (rewrite /ivl /rightCell /=).
    have Hp5 : ivl.(yjs.item.parent') = ic_parent leftCell by (rewrite /ivl /leftCell /=; exact Hpar).
    have Hp6 : item_id (run_head leftCell) = toYjsId ivl.(yjs.item.id'). { rewrite Hrhcl' /ivl /=. exact Hid. }
    have Hp7 : content <$> ic_run leftCell = explode (toContent ivl.(yjs.item.content')). { rewrite /leftCell /ivl /toContent /=. exact Hcontl. }
    have Hp8 : origin_id (origin (run_head leftCell)) = toYjsId <$> olidcw. { rewrite Hrhcl'. exact Holid. }
    have Hp9 : origin_id (rightOrigin (run_head leftCell)) = toYjsId <$> oridcw. { rewrite Hrhcl'. exact Horid. }
    have Hp10 : ivl.(yjs.item.flags') = (if ic_deleted leftCell then W8 6 else W8 2). { rewrite /ivl /leftCell /=. exact Hflags. }
    have Hp11 : run_wf (ic_run leftCell). { rewrite /leftCell /=. exact (run_wf_take cw.(ic_run) o Hopos Hrun). }
    have Hp12 : ivr.(yjs.item.left') = ic_loc leftCell. { rewrite /ivr /leftCell /=. reflexivity. }
    have Hp13 : ivr.(yjs.item.parent') = ic_parent rightCell. { rewrite /ivr /rightCell /=. exact Hpar. }
    have Hp14 : item_id (run_head rightCell) = toYjsId ivr.(yjs.item.id'). { rewrite Hrhcr' Hyoid /ivr /toYjsId /=. rewrite Hrhck Hrhcli Hadd_eq. reflexivity. }
    have Hp15 : content <$> ic_run rightCell = explode (toContent ivr.(yjs.item.content')). { rewrite /rightCell /ivr /toContent /= Hsubdrop. exact Hcontr. }
    have Hp17 : origin_id (rightOrigin (run_head rightCell)) = toYjsId <$> oridcw. { rewrite Hrhcr' Hyoro. exact Horid. }
    have Hp18 : ivr.(yjs.item.flags') = (if ic_deleted rightCell then W8 6 else W8 2). { rewrite /ivr /rightCell /=. exact Hflags. }
    have Hp19 : run_wf (ic_run rightCell). { rewrite /rightCell /=. exact (run_wf_drop cw.(ic_run) o Hoinrun Hrun). }
    (* ----- read the client run slice (map.lookup1), BEFORE Phase A locks cw ----- *)
    iNamed "Hitemmap".
    set (kc := itemVal.(yjs.item.id').(yjs.id.clientId')).
    have Hcwcc : cell_client cw = kc by (rewrite /cell_client Hrhcli /kc; word).
    have Hkcin : kc ∈ (cell_client <$> all_cells types).
    { rewrite -Hcwcc. apply list_elem_of_fmap_2. exact Hcwmem. }
    have Hcwrun : cw ∈ client_run types kc.
    { apply client_run_mem. split; [exact Hcwmem | exact Hcwcc]. }
    apply list_elem_of_lookup_1 in Hcwrun. destruct Hcwrun as [kw Hkw].
    destruct (Hcomplete kc Hkcin) as [slk Hslk].
    iDestruct (big_sepM_lookup_acc _ _ kc slk Hslk with "Hruns") as "[Hrunslk Hrunsback]".
    iNamed "Hrunslk".
    wp_apply (wp_map_lookup1 with "Hmap"). iIntros "Hmap".
    rewrite Hslk /=.
    wp_auto.
    (* ----- Phase A: reassemble the suffix DLL behind [rightCell], own_dll_split, close ----- *)
    iAssert (own_dll (DfracOwn 1) itemVal.(yjs.item.right') tl0 rs null (d0 :: drest))
      with "[Hvald Holeftd Horightd Hrestd]" as "Hsufdll".
    { simpl. iExists ivd2, olidd, oridd.
      rewrite Hd2ol Hd2or Hd2r.
      iFrame "Hvald Holeftd Horightd Hrestd".
      iPureIntro. split_and!;
        [ exact Hlocd1 | exact Hlocdnn | exact Hd2l
        | rewrite Hd2p; exact Hpard
        | rewrite Hd2id; exact Hidd
        | rewrite Hd2c; exact Hcontentd
        | exact Holidd | exact Horidd
        | rewrite Hd2f; exact Hflagsd | exact Hrund ]. }
    iAssert (own_dll (DfracOwn 1) yt.(yjs.yType.start') tl0 null null (split_cells cells k o rs))
      with "[Hseg1 Hval Holeft Horight Hrs Hsufdll]" as "Hdll2".
    { rewrite Hsc.
      iApply (own_dll_split (DfracOwn 1) pre (d0 :: drest) leftCell rightCell ivl ivr olidcw oridcw (Some originId) oridcw yt.(yjs.yType.start') tl0 ml Hp1 Hp2 Hivl_left Hp4 Hp5 Hp6 Hp7 Hp8 Hp9 Hp10 Hp11 Hp12 Hp13 Hp14 Hp15 Hcrorig Hp17 Hp18 Hp19).
      rewrite Hclloc Hcrloc Hivl_ol Hivl_or Hivr_ol Hivr_or Hivr_r.
      iDestruct "Horight" as "#HorightP".
      (* [iFrame "HorightP"] would leak into the cons segment's existentials
         (the fix unfolds on [d0 :: drest]); split the conjuncts off by hand. *)
      iFrame "Hseg1 Hval Hrs Holeft".
      iSplitR; first iExact "HorightP".
      iSplitR.
      { simpl. iFrame "olid". iPureIntro. exact Holidnn. }
      iSplitR; first iExact "HorightP".
      iExact "Hsufdll". }
    have Hcparcw : ic_parent cw = parent by (apply Hcpar0; apply (list_elem_of_lookup_2 _ _ _ Hcellk)).
    have Hcpar_split : ∀ c, c ∈ split_cells cells k o rs -> ic_parent c = parent.
    { rewrite Hsc. move=> c Hc. apply elem_of_app in Hc as [Hc | Hc].
      - apply Hcpar0. rewrite -Hsplit. apply elem_of_app; by left.
      - apply elem_of_cons in Hc as [-> | Hc]; [rewrite /leftCell /=; exact Hcparcw |].
        apply elem_of_cons in Hc as [-> | Hc]; [rewrite /rightCell /=; exact Hcparcw |].
        apply Hcpar0. rewrite -Hsplit. apply elem_of_app; right.
        apply elem_of_cons; right. exact Hc. }
    iAssert (own_ytype_cells parent (DfracOwn 1) (split_cells cells k o rs) arr) with "[Hparent Hdll2]" as "Hyt2".
    { iExists yt, tl0. iFrame "Hparent Hdll2". iPureIntro. split_and!.
      - rewrite (split_cells_num_visible cells k o rs cw Hcellk). exact Hlen0.
      - rewrite /cells_repr (split_cells_flatten cells k o rs cw Hcellk). exact Hrepr0.
      - exact Hcpar_split. }
    iAssert ([∗ map] p0 ↦ ts0 ∈ <[parent := {| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types,
        own_ytype_cells p0 (DfracOwn 1) (ty_cells ts0) (ty_arr ts0) ∗
        ⌜YjsArrInvariant (ty_arr ts0)⌝)%I with "[Hyt2 Hrestmap]" as "Htypes2".
    { rewrite -insert_delete_eq big_sepM_insert_delete delete_delete_eq.
      iFrame "Hrestmap". simpl. iFrame "Hyt2". iPureIntro. exact Harrinv. }
    (* ----- getNodeIndex over the split run [run_half] = client_run with cw -> leftCell ----- *)
    have Hss_replace : ∀ (ll : list item_cell) (i : nat) (a b : item_cell),
        StronglySorted cell_le ll → ll !! i = Some a → cell_clock b = cell_clock a →
        StronglySorted cell_le (<[i:=b]> ll).
    { elim => [| c ll IH] i a b Hss Hi Hclk.
      - by rewrite /=.
      - apply StronglySorted_inv in Hss as [Hssll Hfa].
        destruct i as [|i']; simpl.
        + simpl in Hi. injection Hi as Hca. rewrite Hca in Hfa.
          apply SSorted_cons; [exact Hssll |].
          apply Forall_forall => x Hx. rewrite /cell_le Hclk.
          exact (proj1 (Forall_forall _ _) Hfa x Hx).
        + apply SSorted_cons; [exact (IH i' a b Hssll Hi Hclk) |].
          apply Forall_insert; [exact Hfa |].
          rewrite /cell_le Hclk.
          exact (proj1 (Forall_forall _ _) Hfa a (list_elem_of_lookup_2 ll i' a Hi)). }
    have Hss_half : StronglySorted cell_le (<[kw := leftCell]> (client_run types kc)) := Hss_replace (client_run types kc) kw cw leftCell (client_run_sorted types kc) Hkw Hclcl.
    set (run_half := <[kw := leftCell]> (client_run types kc)).
    have HndAll : NoDup (all_cells types) := NoDup_fmap_1 ic_loc _ Hnodup.
    have Hndrun : NoDup (client_run types kc).
    { rewrite /client_run (merge_sort_Permutation cell_le _). apply NoDup_filter. exact HndAll. }
    have Hkwlt : (kw < length (client_run types kc))%nat by (apply lookup_lt_Some in Hkw; exact Hkw).
    have Hlockw : (ic_loc <$> client_run types kc) !! kw = Some (ic_loc leftCell).
    { rewrite list_lookup_fmap Hkw /=. done. }
    have Hlocs : ic_loc <$> run_half = ic_loc <$> client_run types kc.
    { rewrite /run_half list_fmap_insert (list_insert_id _ _ _ Hlockw) //. }
    have Hkw_half : run_half !! kw = Some leftCell.
    { rewrite /run_half. apply list_lookup_insert_Some. left. split_and!; [reflexivity | reflexivity | exact Hkwlt]. }
    have Hclk_half : cell_clock leftCell = itemVal.(yjs.item.id').(yjs.id.clock') by (rewrite Hclcl Hcwck).
    have Hsub : ∀ c, c ∈ run_half → c = leftCell ∨ c ∈ client_run types kc.
    { move=> c Hc. apply list_elem_of_lookup_1 in Hc as [j Hj]. rewrite /run_half in Hj.
      apply list_lookup_insert_Some in Hj as [(_ & <- & _) | (_ & Hj)]; [by left | right; exact (list_elem_of_lookup_2 _ _ _ Hj)]. }
    have Hfits_half : ∀ c, c ∈ run_half → (uint.Z (cell_clock c) + length (ic_run c) < 2^64)%Z.
    { move=> c Hc. destruct (Hsub c Hc) as [-> | HcL].
      - rewrite Hclcl /leftCell /= length_take. have H := Hnowrapcw. lia.
      - exact (Hrunfits c (proj1 (proj1 (client_run_mem types kc c) HcL))). }
    have Hmem_half : ∀ c, c ∈ run_half → c ∈ all_cells (<[parent := {| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types).
    { move=> c Hc. apply list_elem_of_lookup_1 in Hc as [j Hj]. rewrite /run_half in Hj.
      apply list_lookup_insert_Some in Hj as [(_ & <- & _) | (Hne & Hj)].
      - apply all_cells_elem_of. exists parent, {| ty_cells := split_cells cells k o rs; ty_arr := arr |}.
        split; [apply lookup_insert_eq |]. rewrite /= Hsc. apply elem_of_app; right. apply list_elem_of_here.
      - have HcL : c ∈ client_run types kc := list_elem_of_lookup_2 _ _ _ Hj.
        have Hcne : c ≠ cw. { move=> Heq. rewrite Heq in Hj. exact (Hne (NoDup_lookup _ _ _ _ Hndrun Hkw Hj)). }
        have Hcall : c ∈ all_cells types := proj1 (proj1 (client_run_mem types kc c) HcL).
        apply all_cells_elem_of in Hcall as (p & ts & Hp & Hcts).
        destruct (decide (p = parent)) as [-> | Hpne].
        + rewrite Htypes in Hp. injection Hp as <-. simpl in Hcts.
          rewrite -Hsplit in Hcts. apply elem_of_app in Hcts as [Hcpre | Hcw].
          * apply all_cells_elem_of. exists parent, {| ty_cells := split_cells cells k o rs; ty_arr := arr |}.
            split; [apply lookup_insert_eq |]. rewrite /= Hsc. apply elem_of_app; by left.
          * apply elem_of_cons in Hcw as [-> | Hcsuf]; [done |].
            apply all_cells_elem_of. exists parent, {| ty_cells := split_cells cells k o rs; ty_arr := arr |}.
            split; [apply lookup_insert_eq |]. rewrite /= Hsc. apply elem_of_app; right.
            apply elem_of_cons; right. apply elem_of_cons; right. exact Hcsuf.
        + apply all_cells_elem_of. exists p, ts.
          split; [rewrite lookup_insert_ne; [exact Hp | congruence] | exact Hcts]. }
    iEval (rewrite -Hlocs) in "Hslice".
    wp_apply (wp_getNodeIndex slk (DfracOwn 1) (<[parent := {| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) run_half (itemVal.(yjs.item.id').(yjs.id.clock')) kw leftCell Hss_half Hmem_half Hfits_half Hkw_half Hclk_half with "[$Hslice $Htypes2]").
    iIntros (idx) "(Hslice & Htypes2 & %Hires)".
    destruct Hires as (cres & Hcres & Hcresle & Hcreslt).
    (* pin [uint.nat idx = kw]: the covering cell in [run_half] is [leftCell] (NoDup locs) *)
    have Hinj : ∀ x y, x ∈ client_run types kc → y ∈ client_run types kc → ic_loc x = ic_loc y → x = y.
    { move=> x y Hx Hy Hxy.
      have Hxa : x ∈ all_cells types := proj1 (proj1 (client_run_mem types kc x) Hx).
      have Hya : y ∈ all_cells types := proj1 (proj1 (client_run_mem types kc y) Hy).
      apply list_elem_of_lookup_1 in Hxa as [ix Hix]. apply list_elem_of_lookup_1 in Hya as [iy Hiy].
      have Hlix : (ic_loc <$> all_cells types) !! ix = Some (ic_loc y) by (rewrite list_lookup_fmap Hix /= Hxy //).
      have Hliy : (ic_loc <$> all_cells types) !! iy = Some (ic_loc y) by (rewrite list_lookup_fmap Hiy //).
      have Hijeq : ix = iy := NoDup_lookup _ _ _ _ Hnodup Hlix Hliy.
      congruence. }
    have HndLocRun : NoDup (ic_loc <$> client_run types kc).
    { apply NoDup_fmap_inj_on; [exact Hinj | exact Hndrun]. }
    have Hcresmem : cres ∈ run_half := list_elem_of_lookup_2 _ _ _ Hcres.
    have Hcresloc : ic_loc cres = ic_loc leftCell.
    { destruct (Hsub cres Hcresmem) as [-> | HcresL]; [reflexivity |].
      have Hcresall : cres ∈ all_cells types := proj1 (proj1 (client_run_mem types kc cres) HcresL).
      have Hcrescc : cell_client cres = cell_client cw.
      { rewrite (proj2 (proj1 (client_run_mem types kc cres) HcresL)) -Hcwcc //. }
      destruct (decide (ic_loc cres = ic_loc cw)) as [Heq | Hne].
      - rewrite Heq Hclloc //.
      - exfalso. rewrite -Hcwck in Hcresle Hcreslt.
        destruct (Hdisj cres Hcresall Hcrescc Hne) as [Hd | Hd]; lia. }
    have Hidxloc : (ic_loc <$> run_half) !! (uint.nat idx) = Some (ic_loc leftCell) by (rewrite list_lookup_fmap Hcres /= Hcresloc //).
    have Hkwloc : (ic_loc <$> run_half) !! kw = Some (ic_loc leftCell) by (rewrite list_lookup_fmap Hkw_half //).
    have HndLocRunHalf : NoDup (ic_loc <$> run_half) by (rewrite Hlocs; exact HndLocRun).
    have Hidxkw : uint.nat idx = kw := NoDup_lookup _ _ _ _ HndLocRunHalf Hidxloc Hkwloc.
    have Hcrescl : cres = leftCell.
    { have Htmp : run_half !! kw = Some cres by (rewrite -Hidxkw; exact Hcres). congruence. }
    iEval (rewrite Hlocs) in "Hslice".
    (* ----- the append-based item-map surgery (no length-fit side condition:
       append's growth is modeled with an overflow assume, so no client-run
       capacity premise is needed, unlike a pre-sized make) ----- *)
    iDestruct (own_slice_len with "Hslice") as %[Hslklen Hslklen0].
    rewrite length_fmap in Hslklen Hslklen0.
    have Hkwlt2 : (kw < length (client_run types kc))%nat by (apply lookup_lt_Some in Hkw).
    have Hidxsint : sint.Z idx = Z.of_nat kw by (move: Hslklen Hslklen0 Hkwlt2; rewrite -Hidxkw => ? ? ?; word).
    wp_auto.
    iDestruct (own_slice_wf with "Hslice") as %Hslkwf.
    (* newNodes = append(nil, nodes[:index+1]...) *)
    rewrite decide_True; last word.
    wp_auto.
    have Hsplitbnd : (0 ≤ sint.Z (w64_word_instance.(word.add) idx (W64 1)) ≤ sint.Z slk.(slice.len) ≤ sint.Z slk.(slice.len))%Z by word.
    iDestruct (own_slice_slice (w64_word_instance.(word.add) idx (W64 1)) slk.(slice.len) slk (DfracOwn 1) (ic_loc <$> client_run types kc) Hsplitbnd with "Hslice") as "(Hsl_pre & Hsl_suf & Hsl_tail)".
    iAssert (slice.nil ↦* ([] : list loc))%I with "[]" as "Hnil0"; first iApply own_slice_nil.
    iAssert (own_slice_cap loc slice.nil (DfracOwn 1))%I with "[]" as "Hnilcap"; first iApply own_slice_cap_nil.
    wp_apply (wp_slice_append with "[Hnil0 Hnilcap Hsl_pre]"); first (iFrame "Hnil0 Hnilcap Hsl_pre").
    iIntros (sl1) "(Hsl1 & Hsl1cap & Hsl_pre)".
    wp_auto.
    (* newNodes = append(newNodes, right) *)
    wp_apply wp_slice_literal. iSplitR; first done. iIntros "%slit [Hslit _]". wp_auto.
    wp_apply (wp_slice_append with "[Hsl1 Hsl1cap Hslit]"); first (iFrame "Hsl1 Hsl1cap Hslit").
    iIntros (sl2) "(Hsl2 & Hsl2cap & _)".
    wp_auto.
    (* newNodes = append(newNodes, nodes[index+1:]...) *)
    rewrite decide_True; last word.
    wp_auto.
    wp_apply (wp_slice_append with "[Hsl2 Hsl2cap Hsl_suf]"); first (iFrame "Hsl2 Hsl2cap Hsl_suf").
    iIntros (newSl) "(HnewNodes & HnewCap & Hsl_suf)".
    wp_auto.
    have HnkB : sint.nat (w64_word_instance.(word.add) idx (W64 1)) = (kw + 1)%nat.
    { move: Hslklen Hslklen0 Hkwlt2 Hidxsint => ? ? ? ?. word. }
    have Esrc : subslice (sint.nat (w64_word_instance.(word.add) idx (W64 1))) (sint.nat slk.(slice.len)) (ic_loc <$> client_run types kc) = drop (kw + 1) (ic_loc <$> client_run types kc).
    { rewrite HnkB -Hslklen /subslice take_ge; [reflexivity | rewrite length_fmap; clear -Hkwlt2; lia]. }
    have Elit : <[sint.nat (W64 0) := rs]> ([null] : list loc) = [rs].
    { have -> : sint.nat (W64 0) = 0%nat by word. reflexivity. }
    have Eall : (([] ++ take (sint.nat (w64_word_instance.(word.add) idx (W64 1))) (ic_loc <$> client_run types kc)) ++ <[sint.nat (W64 0) := rs]> ([null] : list loc)) ++ subslice (sint.nat (w64_word_instance.(word.add) idx (W64 1))) (sint.nat slk.(slice.len)) (ic_loc <$> client_run types kc) = take (kw + 1) (ic_loc <$> client_run types kc) ++ rs :: drop (kw + 1) (ic_loc <$> client_run types kc).
    { rewrite Esrc Elit HnkB app_nil_l -app_assoc /=. reflexivity. }
    iEval (rewrite Eall) in "HnewNodes".
    iAssert (slk ↦* (ic_loc <$> client_run types kc))%I with "[Hsl_pre Hsl_suf Hsl_tail]" as "Hslice".
    { rewrite (own_slice_slice (w64_word_instance.(word.add) idx (W64 1)) slk.(slice.len) slk (DfracOwn 1) (ic_loc <$> client_run types kc) Hsplitbnd). iFrame. }
    (* s.items[client] = newNodes: the key read borrows cl's node back from types2 *)
    have Hklt : (k < length cells)%nat by (apply lookup_lt_Some in Hcellk).
    have Hsck : split_cells cells k o rs !! k = Some leftCell.
    { rewrite Hsc /pre lookup_app_r; last (rewrite length_take; clear -Hklt; lia).
      rewrite length_take Nat.min_l; last (clear -Hklt; lia).
      have -> : (k - k)%nat = 0%nat by (clear -k; lia).
      reflexivity. }
    have Hlk2 : (<[parent:={| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) !! parent = Some {| ty_cells := split_cells cells k o rs; ty_arr := arr |} by apply lookup_insert_eq.
    iDestruct (big_sepM_lookup_acc _ _ parent {| ty_cells := split_cells cells k o rs; ty_arr := arr |} Hlk2 with "Htypes2") as "[(Hpc2 & %Harrinv2) Hclose2]".
    iDestruct "Hpc2" as (yt2 tl2) "(Hparent2 & Hdll3 & %Hlen2 & %Hrepr2 & %Hcpar2)".
    iDestruct (own_dll_acc (DfracOwn 1) (split_cells cells k o rs) yt2.(yjs.yType.start') tl2 k leftCell Hsck with "Hdll3") as (iv2 olid2 orid2) "(%Hcloc2 & %Hcl2 & %Hcr2 & %Hid2 & %Hcontent2 & %Holid2 & %Horid2 & %Hflags2 & %Hrun2 & %Hpar2 & Hcval2 & Hcol2 & Hcor2 & Hback2)".
    iEval (rewrite Hclloc) in "Hcval2".
    have Hkey : iv2.(yjs.item.id').(yjs.id.clientId') = kc.
    { move: Hid2. rewrite Hrhcl' Hid /toYjsId /=. move=> Heq.
      have Hc1 := f_equal clientId Heq. simpl in Hc1. rewrite /kc.
      clear -Hc1. word. }
    wp_auto.
    wp_apply (wp_map_insert with "Hmap").
    iIntros "Hmap".
    iEval (rewrite Hkey) in "Hmap".
    iEval (rewrite -Hclloc) in "Hcval2".
    iDestruct ("Hback2" with "Hcval2") as "Hdll3".
    iAssert (own_ytype_cells parent (DfracOwn 1) (split_cells cells k o rs) arr) with "[Hparent2 Hdll3]" as "Hyt2b".
    { iExists yt2, tl2. iFrame "Hparent2 Hdll3". iPureIntro.
      split_and!; [exact Hlen2 | exact Hrepr2 | exact Hcpar2]. }
    iDestruct ("Hclose2" with "[Hyt2b]") as "Htypes2"; first (iFrame "Hyt2b"; iPureIntro; exact Harrinv2).
    (* the item-map model surgery: the right half's loc lands at position kw+1 *)
    have Hkpcl : cell_kp leftCell = cell_kp cw.
    { rewrite /cell_kp /cell_pr Hcccl Hclcl Hclloc. reflexivity. }
    have Hkp : cell_kp <$> all_cells (<[parent:={| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) ≡ₚ (cell_kp <$> all_cells types) ++ [cell_kp rightCell].
    { etransitivity.
      { apply Permutation_map.
        exact (all_cells_insert types parent {| ty_cells := cells; ty_arr := arr |} {| ty_cells := split_cells cells k o rs; ty_arr := arr |} Htypes). }
      simpl. rewrite Hsc.
      etransitivity; last first.
      { apply Permutation_app_tail. apply Permutation_map. symmetry.
        exact (all_cells_lookup types parent {| ty_cells := cells; ty_arr := arr |} Htypes). }
      simpl. rewrite -Hsplit !map_app /= Hkpcl -!app_assoc /=.
      apply Permutation_app_head. apply perm_skip.
      etransitivity; [apply Permutation_cons_append |].
      simpl. rewrite -!app_assoc. reflexivity. }
    have Hbef : forall y, y ∈ take (kw + 1) (client_run types (cell_client rightCell)) -> ((cell_pr y).1 < (cell_pr rightCell).1)%Z.
    { move=> y Hy.
      rewrite Hcccr Hcwcc in Hy.
      apply list_elem_of_lookup_1 in Hy as [j Hj].
      apply lookup_take_Some in Hj as [Hj Hjlt].
      have Hple : (uint.Z (cell_clock y) <= uint.Z (cell_clock cw))%Z.
      { destruct (decide (j = kw)) as [-> | Hne].
        - rewrite Hkw in Hj. injection Hj as <-. lia.
        - exact (StronglySorted_lookup_le cell_le (client_run types kc) j kw y cw (client_run_sorted types kc) Hj Hkw ltac:(clear -Hjlt Hne; lia)). }
      rewrite /cell_pr /= Hccr_clock. clear -Hple Hopos. lia. }
    have Haft : forall y, y ∈ drop (kw + 1) (client_run types (cell_client rightCell)) -> ((cell_pr rightCell).1 < (cell_pr y).1)%Z.
    { move=> y Hy.
      rewrite Hcccr Hcwcc in Hy.
      apply list_elem_of_lookup_1 in Hy as [j Hj].
      rewrite lookup_drop in Hj.
      have HyCR : y ∈ client_run types kc := list_elem_of_lookup_2 _ _ _ Hj.
      have Hyall : y ∈ all_cells types := proj1 (proj1 (client_run_mem types kc y) HyCR).
      have Hycc : cell_client y = cell_client cw.
      { rewrite (proj2 (proj1 (client_run_mem types kc y) HyCR)) Hcwcc //. }
      have Hyne : y ≠ cw.
      { move=> Heq. rewrite Heq in Hj.
        have := NoDup_lookup _ _ _ _ Hndrun Hkw Hj. clear -k. lia. }
      have Hylocne : y.(ic_loc) ≠ cw.(ic_loc).
      { move=> Heq. apply Hyne. exact (Hinj y cw HyCR (list_elem_of_lookup_2 _ _ _ Hkw) Heq). }
      have Hle : (uint.Z (cell_clock cw) <= uint.Z (cell_clock y))%Z.
      { exact (StronglySorted_lookup_le cell_le (client_run types kc) kw (kw + 1 + j) cw y (client_run_sorted types kc) Hkw Hj ltac:(clear -k; lia)). }
      rewrite /cell_pr /= Hccr_clock.
      destruct (Hdisj y Hyall Hycc Hylocne) as [Hd | Hd].
      - exfalso.
        have Hyeq : uint.Z (cell_clock y) = uint.Z (cell_clock cw) by (clear -Hd Hle; lia).
        apply Hylocne. apply (Hclkloc y cw Hyall Hcwmem Hycc).
        rewrite /cell_pr /=. exact Hyeq.
      - clear -Hd Hoinrun. lia. }
    have Hrun_eq := client_run_loc_insert types (<[parent:={| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) rightCell (kw + 1) Hkp Hclkloc Hbef Haft.
    rewrite Hcccr Hcwcc Hcrloc in Hrun_eq.
    iEval (rewrite -Hrun_eq) in "HnewNodes".
    (* re-establish the own_item_map side conditions over types2 *)
    have HinjAll : forall x y, x ∈ all_cells types -> y ∈ all_cells types -> x.(ic_loc) = y.(ic_loc) -> x = y.
    { move=> x y Hx Hy Hxy.
      apply list_elem_of_lookup_1 in Hx as [ix Hix]. apply list_elem_of_lookup_1 in Hy as [iy Hiy].
      have Hlix : (ic_loc <$> all_cells types) !! ix = Some (y.(ic_loc)) by (rewrite list_lookup_fmap Hix /= Hxy //).
      have Hliy : (ic_loc <$> all_cells types) !! iy = Some (y.(ic_loc)) by (rewrite list_lookup_fmap Hiy //).
      have Hijeq : ix = iy := NoDup_lookup _ _ _ _ Hnodup Hlix Hliy.
      congruence. }
    have Hdecomp : forall c0, c0 ∈ all_cells (<[parent:={| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) -> c0 ∈ all_cells types \/ c0 = leftCell \/ c0 = rightCell.
    { move=> c0 Hc0.
      have Hp := all_cells_insert types parent {| ty_cells := cells; ty_arr := arr |} {| ty_cells := split_cells cells k o rs; ty_arr := arr |} Htypes.
      rewrite Hp /= Hsc in Hc0.
      apply elem_of_app in Hc0 as [Hc0 | Hc0].
      - apply elem_of_app in Hc0 as [Hc0 | Hc0].
        + left. apply all_cells_elem_of. exists parent, {| ty_cells := cells; ty_arr := arr |}.
          split; [exact Htypes |]. simpl. rewrite -Hsplit. apply elem_of_app. by left.
        + apply elem_of_cons in Hc0 as [-> | Hc0]; [by right; left |].
          apply elem_of_cons in Hc0 as [-> | Hc0]; [by right; right |].
          left. apply all_cells_elem_of. exists parent, {| ty_cells := cells; ty_arr := arr |}.
          split; [exact Htypes |]. simpl. rewrite -Hsplit. apply elem_of_app. right.
          apply elem_of_cons. by right.
      - left.
        have Hq := all_cells_lookup types parent {| ty_cells := cells; ty_arr := arr |} Htypes.
        rewrite Hq /=. apply elem_of_app. by right. }
    have Hcomplete2 : forall c0 : w64, c0 ∈ cell_client <$> all_cells (<[parent:={| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) -> is_Some (<[kc := newSl]> gm !! c0).
    { move=> c0 Hc0. apply list_elem_of_fmap in Hc0 as (cc & -> & Hcc0).
      destruct (Hdecomp cc Hcc0) as [Hin | [-> | ->]].
      - destruct (decide (cell_client cc = kc)) as [He | Hne].
        + rewrite He lookup_insert_eq. eauto.
        + rewrite lookup_insert_ne; [| congruence]. apply Hcomplete. apply list_elem_of_fmap_2. exact Hin.
      - rewrite Hcccl Hcwcc lookup_insert_eq. eauto.
      - rewrite Hcccr Hcwcc lookup_insert_eq. eauto. }
    have HF2 : forall c, c ∈ all_cells types -> cell_client c = cell_client cw -> (cell_pr c).1 = (cell_pr rightCell).1 -> False.
    { move=> c Hc Hcc Hpr.
      rewrite /cell_pr /= Hccr_clock in Hpr.
      destruct (decide (c.(ic_loc) = cw.(ic_loc))) as [He | Hne].
      - have Heq : c = cw := HinjAll c cw Hc Hcwmem He.
        rewrite Heq in Hpr. clear -Hpr Hopos. lia.
      - destruct (Hdisj c Hc Hcc Hne) as [Hd | Hd].
        + clear -Hd Hpr Hopos. lia.
        + clear -Hd Hpr Hoinrun. lia. }
    have Hprcl : (cell_pr leftCell).1 = (cell_pr cw).1 by (rewrite /cell_pr /= Hclcl //).
    have Hclkloc2 : forall c1 c2, c1 ∈ all_cells (<[parent:={| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) -> c2 ∈ all_cells (<[parent:={| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) -> cell_client c1 = cell_client c2 -> (cell_pr c1).1 = (cell_pr c2).1 -> c1.(ic_loc) = c2.(ic_loc).
    { move=> c1 c2 Hc1 Hc2 Hcc Hpr.
      destruct (Hdecomp c1 Hc1) as [Hin1 | [-> | ->]]; destruct (Hdecomp c2 Hc2) as [Hin2 | [-> | ->]].
      - exact (Hclkloc c1 c2 Hin1 Hin2 Hcc Hpr).
      - rewrite Hclloc.
        apply (Hclkloc c1 cw Hin1 Hcwmem); [rewrite Hcc Hcccl // | rewrite Hpr Hprcl //].
      - exfalso. apply (HF2 c1 Hin1); [rewrite Hcc Hcccr // | exact Hpr].
      - rewrite Hclloc. symmetry.
        apply (Hclkloc c2 cw Hin2 Hcwmem); [rewrite -Hcc Hcccl // | rewrite -Hpr Hprcl //].
      - reflexivity.
      - exfalso. rewrite /cell_pr /= Hclcl Hccr_clock in Hpr. clear -Hpr Hopos. lia.
      - exfalso. apply (HF2 c2 Hin2); [rewrite -Hcc Hcccr // | rewrite -Hpr //].
      - exfalso. rewrite /cell_pr /= Hclcl Hccr_clock in Hpr. clear -Hpr Hopos. lia.
      - reflexivity. }
    iDestruct ("Hrunsback" with "[$Hslice $Hcap]") as "Hruns".
    iAssert (own_item_map mref (DfracOwn 1) (<[parent:={| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types)) with "[Hmap HnewNodes HnewCap Hruns]" as "Hitemmap2".
    { iExists (<[kc := newSl]> gm). iFrame "Hmap".
      iSplitL "HnewNodes HnewCap Hruns".
      - rewrite big_sepM_insert_delete. iSplitL "HnewNodes HnewCap"; [iFrame |].
        iDestruct (big_sepM_delete _ _ kc slk Hslk with "Hruns") as "[_ Hrest2]".
        iApply (big_sepM_impl with "Hrest2").
        iIntros "!#" (client s0 Hcs) "H". iNamed "H".
        have Hne2 : client ≠ cell_client rightCell.
        { rewrite Hcccr Hcwcc. move=> Heqc. rewrite Heqc lookup_delete_eq in Hcs. discriminate. }
        rewrite (client_run_loc_other types (<[parent:={| ty_cells := split_cells cells k o rs; ty_arr := arr |}]> types) rightCell client Hkp Hclkloc Hne2). iFrame.
      - iPureIntro. split; [exact Hcomplete2 | exact Hclkloc2]. }
    wp_auto.
    iApply ("HΦ" $! rs).
    iFrame "Hitemsf Hitemmap2 Htypes2".
    iPureIntro. split; [exact Hrsnn | exact Hrsfresh].
Qed.

(** [store.splitAtAndGetLeft], general splitting form (issue #28 stage D1b):
    the id may address ANY char of the witness cell's run. When it is the
    run's LAST char the node already ends there and nothing changes;
    otherwise the node is split just after the id ([splitNode] at offset+1)
    and the truncated-in-place left half comes back (same location). Either
    way the returned node's run ends exactly at [idv]: the clean-end
    boundary the C2 flip feeds to Integrate as the left cursor. Mutates the
    item map, hence [DfracOwn 1]; needs the pool invariants (run-fits,
    loc-NoDup, range disjointness). *)
Lemma wp_store__splitAtAndGetLeft_range (s mref : loc) (idv : yjs.id.t)
    (types : gmap loc type_state) (parent : loc)
    (cells : list item_cell) (arr : list (YjsItem A)) (k : nat) (cw : item_cell) :
  types !! parent = Some (MkTypeState cells arr) ->
  cells !! k = Some cw ->
  cell_client cw = idv.(yjs.id.clientId') ->
  (uint.Z (cell_clock cw) <= uint.Z idv.(yjs.id.clock'))%Z ->
  (uint.Z idv.(yjs.id.clock') < uint.Z (cell_clock cw) + Z.of_nat (length (ic_run cw)))%Z ->
  (∀ c, c ∈ all_cells types -> (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) < 2^64)%Z) ->
  NoDup (ic_loc <$> all_cells types) ->
  cells_range_disjoint (all_cells types) ->
  {{{ is_pkg_init yjs ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types ∗
      ([∗ map] p ↦ ts ∈ types,
          own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) }}}
    s @! (go.PointerType yjs.store) @! "splitAtAndGetLeft" #idv
  {{{ (types' : gmap loc type_state), RET (#(ic_loc cw), #true);
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types' ∗
      ([∗ map] p ↦ ts ∈ types',
          own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) ∗
      ⌜((uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw))%nat = (length (ic_run cw) - 1)%nat ∧
        types' = types)
       ∨ (((uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) < length (ic_run cw) - 1)%nat ∧
          ∃ rloc : loc, rloc ≠ null ∧ rloc ∉ (ic_loc <$> all_cells types) ∧
            types' = <[parent := MkTypeState
              (split_cells cells k ((uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) + 1) rloc)
              arr]> types)⌝ }}}.
Proof using Type*.
  move=> Htypes Hcellk Hcwcc Hcwle Hcwlt Hrunfits Hnodup Hrangedisj.
  iIntros (Φ) "(#Hpkg & Hitemsf & Hitemmap & Htypes) HΦ".
  have Hcwmem : cw ∈ all_cells types.
  { apply all_cells_elem_of. exists parent, (MkTypeState cells arr).
    split; [exact Htypes | exact (list_elem_of_lookup_2 _ _ _ Hcellk)]. }
  wp_method_call. wp_call. wp_call. wp_auto.
  wp_apply (wp_store__GetNode_range s mref (DfracOwn 1) idv types cw
              Hcwmem Hcwcc Hcwle Hcwlt Hrunfits Hnodup Hrangedisj
              with "[$Hitemsf $Hitemmap $Htypes]").
  iIntros "(Hitemsf & Hitemmap & Htypes)".
  wp_auto.
  iDestruct (types_cell_acc_gen types cw Hcwmem with "Htypes") as "Hacc".
  iNamed "Hacc".
  have Hnwcw := Hrunfits cw Hcwmem.
  have Hcwck : cell_clock cw = itemVal.(yjs.item.id').(yjs.id.clock')
    by (rewrite /cell_clock Hid /toYjsId /=; word).
  have HlenEq : length (itemVal.(yjs.item.content').(yjs.content.content')) = length (ic_run cw).
  { have H := f_equal length Hcontent.
    rewrite length_fmap explode_length /toContent in H. lia. }
  have Hlenpos : (1 <= Z.of_nat (length (ic_run cw)))%Z.
  { have [Hne0 _] := Hrun. destruct (ic_run cw) as [|? ?]; [done | simpl; lia]. }
  have Hosub : uint.Z (w64_word_instance.(word.sub) idv.(yjs.id.clock') itemVal.(yjs.item.id').(yjs.id.clock'))
             = Z.of_nat (uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw))%nat.
  { rewrite -Hcwck. clear -Hcwle. word. }
  have Holt : ((uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) < length (ic_run cw))%nat.
  { clear -Hcwle Hcwlt. word. }
  wp_auto.
  wp_apply (wp_item__Len (ic_loc cw) (DfracOwn 1) itemVal with "[$Hval]"). iIntros "Hval".
  rewrite HlenEq.
  wp_auto.
  wp_if_destruct.
  - (* offset = Len-1: the run already ends at [idv]; no split *)
    iDestruct ("Hback" with "Hval") as "Htypes".
    iApply ("HΦ" $! types).
    iFrame "Hitemsf Hitemmap Htypes".
    iPureIntro. left. split; [| reflexivity].
    word.
  - (* the id sits strictly inside the run: split just after it *)
    iDestruct ("Hback" with "Hval") as "Htypes".
    have Hnlt : ((uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) < length (ic_run cw) - 1)%nat.
    { word. }
    have Hdiffnat : uint.nat (w64_word_instance.(word.add)
                      (w64_word_instance.(word.sub) idv.(yjs.id.clock') itemVal.(yjs.item.id').(yjs.id.clock'))
                      (W64 1))
                  = ((uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) + 1)%nat.
    { clear -Hosub Hnlt Hnwcw Hlenpos. word. }
    have Hdiffb : (0 < uint.nat (w64_word_instance.(word.add)
                      (w64_word_instance.(word.sub) idv.(yjs.id.clock') itemVal.(yjs.item.id').(yjs.id.clock'))
                      (W64 1)) < length (ic_run cw))%nat.
    { rewrite Hdiffnat. clear -Hnlt. lia. }
    have Hdisjcw : ∀ c, c ∈ all_cells types -> cell_client c = cell_client cw -> ic_loc c ≠ ic_loc cw ->
       (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) <= uint.Z (cell_clock cw))%Z ∨
       (uint.Z (cell_clock cw) + Z.of_nat (length (ic_run cw)) <= uint.Z (cell_clock c))%Z.
    { move=> c Hc Hcc Hlocne. exact (Hrangedisj c cw Hc Hcwmem Hcc Hlocne). }
    wp_apply (wp_store__splitNode s mref types parent cells arr k cw
                (w64_word_instance.(word.add)
                   (w64_word_instance.(word.sub) idv.(yjs.id.clock') itemVal.(yjs.item.id').(yjs.id.clock'))
                   (W64 1))
                Htypes Hcellk Hdiffb Hrunfits Hnodup Hdisjcw
                with "[$Hpkg $Hitemsf $Hitemmap $Htypes]").
    iIntros (rloc) "(%Hrlocnn & %Hrlocfresh & Hitemsf & Hitemmap & Htypes)".
    wp_auto.
    iApply ("HΦ" $! (<[parent := MkTypeState (split_cells cells k (uint.nat (w64_word_instance.(word.add)
                   (w64_word_instance.(word.sub) idv.(yjs.id.clock') itemVal.(yjs.item.id').(yjs.id.clock'))
                   (W64 1))) rloc) arr]> types)).
    iFrame "Hitemsf Hitemmap Htypes".
    iPureIntro. right. split.
    { exact Hnlt. }
    exists rloc. split_and!; [exact Hrlocnn | exact Hrlocfresh |].
    rewrite Hdiffnat //.
Qed.

(** [store.splitAtAndGetRight], general splitting form (issue #28 stage
    D1b): when the id addresses the HEAD of the witness cell's run nothing
    changes and the node itself comes back; otherwise the node is split at
    the id's offset and the fresh right half comes back. Either way the
    returned node's run STARTS exactly at [idv]: the clean-start boundary
    the C2 flip feeds to Integrate as the right cursor. *)
Lemma wp_store__splitAtAndGetRight_range (s mref : loc) (idv : yjs.id.t)
    (types : gmap loc type_state) (parent : loc)
    (cells : list item_cell) (arr : list (YjsItem A)) (k : nat) (cw : item_cell) :
  types !! parent = Some (MkTypeState cells arr) ->
  cells !! k = Some cw ->
  cell_client cw = idv.(yjs.id.clientId') ->
  (uint.Z (cell_clock cw) <= uint.Z idv.(yjs.id.clock'))%Z ->
  (uint.Z idv.(yjs.id.clock') < uint.Z (cell_clock cw) + Z.of_nat (length (ic_run cw)))%Z ->
  (∀ c, c ∈ all_cells types -> (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) < 2^64)%Z) ->
  NoDup (ic_loc <$> all_cells types) ->
  cells_range_disjoint (all_cells types) ->
  {{{ is_pkg_init yjs ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types ∗
      ([∗ map] p ↦ ts ∈ types,
          own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) }}}
    s @! (go.PointerType yjs.store) @! "splitAtAndGetRight" #idv
  {{{ (rl : loc) (types' : gmap loc type_state), RET (#rl, #true);
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types' ∗
      ([∗ map] p ↦ ts ∈ types',
          own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) ∗
      ⌜((uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw))%nat = 0%nat ∧
        rl = ic_loc cw ∧ types' = types)
       ∨ ((0 < (uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)))%nat ∧
          rl ≠ null ∧ rl ∉ (ic_loc <$> all_cells types) ∧
          types' = <[parent := MkTypeState
            (split_cells cells k (uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) rl)
            arr]> types)⌝ }}}.
Proof using Type*.
  move=> Htypes Hcellk Hcwcc Hcwle Hcwlt Hrunfits Hnodup Hrangedisj.
  iIntros (Φ) "(#Hpkg & Hitemsf & Hitemmap & Htypes) HΦ".
  have Hcwmem : cw ∈ all_cells types.
  { apply all_cells_elem_of. exists parent, (MkTypeState cells arr).
    split; [exact Htypes | exact (list_elem_of_lookup_2 _ _ _ Hcellk)]. }
  wp_method_call. wp_call. wp_call. wp_auto.
  wp_apply (wp_store__GetNode_range s mref (DfracOwn 1) idv types cw
              Hcwmem Hcwcc Hcwle Hcwlt Hrunfits Hnodup Hrangedisj
              with "[$Hitemsf $Hitemmap $Htypes]").
  iIntros "(Hitemsf & Hitemmap & Htypes)".
  wp_auto.
  iDestruct (types_cell_acc_gen types cw Hcwmem with "Htypes") as "Hacc".
  iNamed "Hacc".
  have Hnwcw := Hrunfits cw Hcwmem.
  have Hcwck : cell_clock cw = itemVal.(yjs.item.id').(yjs.id.clock')
    by (rewrite /cell_clock Hid /toYjsId /=; word).
  have Hlenpos : (1 <= Z.of_nat (length (ic_run cw)))%Z.
  { have [Hne0 _] := Hrun. destruct (ic_run cw) as [|? ?]; [done | simpl; lia]. }
  have Hosub : uint.Z (w64_word_instance.(word.sub) idv.(yjs.id.clock') itemVal.(yjs.item.id').(yjs.id.clock'))
             = Z.of_nat (uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw))%nat.
  { rewrite -Hcwck. clear -Hcwle. word. }
  have Holt : ((uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) < length (ic_run cw))%nat.
  { clear -Hcwle Hcwlt. word. }
  wp_auto.
  wp_if_destruct.
  - (* offset > 0: split at the offset, return the fresh right half *)
    iDestruct ("Hback" with "Hval") as "Htypes".
    have Hopos : (0 < (uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)))%nat.
    { word. }
    have Hdiffnat : uint.nat (w64_word_instance.(word.sub) idv.(yjs.id.clock') itemVal.(yjs.item.id').(yjs.id.clock'))
                  = (uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw))%nat.
    { clear -Hosub. word. }
    have Hdiffb : (0 < uint.nat (w64_word_instance.(word.sub) idv.(yjs.id.clock') itemVal.(yjs.item.id').(yjs.id.clock'))
                   < length (ic_run cw))%nat.
    { rewrite Hdiffnat. clear -Hopos Holt. lia. }
    have Hdisjcw : ∀ c, c ∈ all_cells types -> cell_client c = cell_client cw -> ic_loc c ≠ ic_loc cw ->
       (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) <= uint.Z (cell_clock cw))%Z ∨
       (uint.Z (cell_clock cw) + Z.of_nat (length (ic_run cw)) <= uint.Z (cell_clock c))%Z.
    { move=> c Hc Hcc Hlocne. exact (Hrangedisj c cw Hc Hcwmem Hcc Hlocne). }
    wp_apply (wp_store__splitNode s mref types parent cells arr k cw
                (w64_word_instance.(word.sub) idv.(yjs.id.clock') itemVal.(yjs.item.id').(yjs.id.clock'))
                Htypes Hcellk Hdiffb Hrunfits Hnodup Hdisjcw
                with "[$Hpkg $Hitemsf $Hitemmap $Htypes]").
    iIntros (rloc) "(%Hrlocnn & %Hrlocfresh & Hitemsf & Hitemmap & Htypes)".
    wp_auto.
    iApply ("HΦ" $! rloc (<[parent := MkTypeState (split_cells cells k
                (uint.nat (w64_word_instance.(word.sub) idv.(yjs.id.clock') itemVal.(yjs.item.id').(yjs.id.clock')))
                rloc) arr]> types)).
    iFrame "Hitemsf Hitemmap Htypes".
    iPureIntro. right. split.
    { exact Hopos. }
    split_and!; [exact Hrlocnn | exact Hrlocfresh |].
    rewrite Hdiffnat //.
  - (* offset = 0: the run already starts at [idv]; no split *)
    iDestruct ("Hback" with "Hval") as "Htypes".
    iApply ("HΦ" $! (ic_loc cw) types).
    iFrame "Hitemsf Hitemmap Htypes".
    iPureIntro. left. split_and!; [| reflexivity | reflexivity].
    word.
Qed.

(* ----- split_cells pool bookkeeping (issue #28 stage D1c) -----------------
   The pool effect of a split: the covering cell [cw] is replaced by its two
   halves, everything else untouched ([split_pool_perm]). On top of it, the
   pointwise preservation of the store pool invariants: run-fits, range
   disjointness, origin-clock (the right half's origin telescopes inside
   [cw]'s own run), and loc-NoDup (given the right half's location is fresh).
   These are what the general [repair] uses to re-establish [store_inv]
   across its clean-end / clean-start splits at the C2 flip. *)

(** The two halves' head / length / client / clock facts, in one bundle. *)
Lemma split_cell_facts (cw : item_cell) (o : nat) (rloc : loc) :
  run_wf (ic_run cw) ->
  (0 < o < length (ic_run cw))%nat ->
  run_head (split_cell_left cw o) = run_head cw ∧
  length (ic_run (split_cell_left cw o)) = o ∧
  length (ic_run (split_cell_right cw o rloc)) = (length (ic_run cw) - o)%nat ∧
  cell_client (split_cell_left cw o) = cell_client cw ∧
  cell_client (split_cell_right cw o rloc) = cell_client cw ∧
  cell_clock (split_cell_left cw o) = cell_clock cw ∧
  cell_clock (split_cell_right cw o rloc) = W64 (Z.of_nat (clock (item_id (run_head cw)) + o)%nat).
Proof.
  move=> Hrunwf [Hopos Holt].
  have Hrun0 : ic_run cw !! 0%nat = Some (run_head cw).
  { rewrite /run_head. destruct Hrunwf as [Hne _].
    destruct (ic_run cw) as [|a r']; [done | reflexivity]. }
  destruct (ic_run cw !! o) as [yo|] eqn:Hyo; last by (apply lookup_ge_None in Hyo; lia).
  have Hidy := run_wf_lookup_clock (ic_run cw) o (run_head cw) yo Hrunwf Hrun0 Hyo.
  have Hheadl : run_head (split_cell_left cw o) = run_head cw.
  { rewrite /run_head /split_cell_left /=. apply hd_inhabitant_take. lia. }
  have Hheadr : run_head (split_cell_right cw o rloc) = yo.
  { rewrite /run_head /split_cell_right /=. exact (hd_inhabitant_drop _ o yo Hyo). }
  split_and!.
  - exact Hheadl.
  - rewrite /split_cell_left /= length_take. lia.
  - rewrite /split_cell_right /= length_drop //.
  - rewrite /cell_client Hheadl //.
  - rewrite /cell_client Hheadr Hidy //=.
  - rewrite /cell_clock Hheadl //.
  - rewrite /cell_clock Hheadr Hidy //=.
Qed.

(** The pool permutation of a split: [cw] out, its two halves in. *)
Lemma split_pool_perm (types : gmap loc type_state) (parent : loc)
    (cells : list item_cell) (arr : list (YjsItem A)) (k : nat) (cw : item_cell)
    (o : nat) (rloc : loc) :
  types !! parent = Some (MkTypeState cells arr) ->
  cells !! k = Some cw ->
  ∃ rest : list item_cell,
    all_cells types ≡ₚ cw :: rest ∧
    all_cells (<[parent := MkTypeState (split_cells cells k o rloc) arr]> types)
      ≡ₚ split_cell_left cw o :: split_cell_right cw o rloc :: rest.
Proof.
  move=> Htypes Hck.
  exists (take k cells ++ drop (S k) cells ++ all_cells (delete parent types)).
  split.
  - rewrite (all_cells_lookup types parent _ Htypes) /=.
    rewrite -{1}(take_drop_middle cells k cw Hck).
    rewrite -app_assoc /=.
    rewrite -Permutation_middle //.
  - rewrite (all_cells_insert types parent _ _ Htypes) /= /split_cells Hck.
    rewrite -!app_assoc /=.
    rewrite -Permutation_middle.
    rewrite -Permutation_middle //.
Qed.

(** Run-fits survives a split: each half's range is a sub-range of [cw]'s.
    [Hckbnd] (the head clock fits as a NAT, from [types_cells_id_bounds2])
    makes the right half's [W64] clock exact. *)
Lemma split_pool_fits (types : gmap loc type_state) (parent : loc)
    (cells : list item_cell) (arr : list (YjsItem A)) (k : nat) (cw : item_cell)
    (o : nat) (rloc : loc) :
  types !! parent = Some (MkTypeState cells arr) ->
  cells !! k = Some cw ->
  run_wf (ic_run cw) ->
  (0 < o < length (ic_run cw))%nat ->
  (Z.of_nat (clock (item_id (run_head cw))) < 2^64)%Z ->
  (∀ c, c ∈ all_cells types -> (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) < 2^64)%Z) ->
  (∀ c, c ∈ all_cells (<[parent := MkTypeState (split_cells cells k o rloc) arr]> types) ->
     (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) < 2^64)%Z).
Proof.
  move=> Htypes Hck Hrunwf Ho Hckbnd Hfits c Hc.
  destruct (split_pool_perm types parent cells arr k cw o rloc Htypes Hck) as (rest & Hold & Hnew).
  have Hcwmem : cw ∈ all_cells types by (rewrite Hold; apply list_elem_of_here).
  have Hfitscw := Hfits cw Hcwmem.
  destruct (split_cell_facts cw o rloc Hrunwf Ho)
    as (Hheadl & Hlenl & Hlenr & Hclientl & Hclientr & Hclockl & Hclockr).
  have HclkZ : uint.Z (cell_clock cw) = Z.of_nat (clock (item_id (run_head cw))).
  { rewrite /cell_clock. word. }
  rewrite Hnew in Hc.
  apply elem_of_cons in Hc as [-> | Hc].
  - rewrite Hclockl Hlenl. lia.
  - apply elem_of_cons in Hc as [-> | Hc].
    + rewrite Hclockr Hlenr.
      have Hbo : (Z.of_nat (clock (item_id (run_head cw)) + o) < 2^64)%Z by lia.
      have -> : uint.Z (W64 (Z.of_nat (clock (item_id (run_head cw)) + o)%nat))
              = Z.of_nat (clock (item_id (run_head cw)) + o)%nat by word.
      lia.
    + apply Hfits. rewrite Hold. apply elem_of_cons. by right.
Qed.

(** Origin-clock survives a split: the left half keeps [cw]'s head (and so
    its origin fact); the right half's head is [cw]'s char at offset [o],
    whose origin is the previous char of the SAME run ([run_wf] chaining):
    same client, clock exactly one below. *)
Lemma split_pool_originclk (types : gmap loc type_state) (parent : loc)
    (cells : list item_cell) (arr : list (YjsItem A)) (k : nat) (cw : item_cell)
    (o : nat) (rloc : loc) :
  types !! parent = Some (MkTypeState cells arr) ->
  cells !! k = Some cw ->
  run_wf (ic_run cw) ->
  (0 < o < length (ic_run cw))%nat ->
  (∀ c, c ∈ all_cells types -> cell_origin_clk c) ->
  (∀ c, c ∈ all_cells (<[parent := MkTypeState (split_cells cells k o rloc) arr]> types) ->
     cell_origin_clk c).
Proof.
  move=> Htypes Hck Hrunwf Ho Hoclk c Hc.
  destruct (split_pool_perm types parent cells arr k cw o rloc Htypes Hck) as (rest & Hold & Hnew).
  have Hcwmem : cw ∈ all_cells types by (rewrite Hold; apply list_elem_of_here).
  destruct (split_cell_facts cw o rloc Hrunwf Ho)
    as (Hheadl & Hlenl & Hlenr & Hclientl & Hclientr & Hclockl & Hclockr).
  rewrite Hnew in Hc.
  apply elem_of_cons in Hc as [-> | Hc].
  - rewrite /cell_origin_clk Hheadl. exact (Hoclk cw Hcwmem).
  - apply elem_of_cons in Hc as [-> | Hc].
    + (* the right half: its head's origin is the previous char of the run *)
      rewrite /cell_origin_clk.
      have Hrun0 : ic_run cw !! 0%nat = Some (run_head cw).
      { rewrite /run_head. destruct Hrunwf as [Hne _].
        destruct (ic_run cw) as [|a r']; [done | reflexivity]. }
      destruct (ic_run cw !! o) as [yo|] eqn:Hyo; last by (apply lookup_ge_None in Hyo; lia).
      destruct (ic_run cw !! (o - 1)%nat) as [yp|] eqn:Hyp; last by (apply lookup_ge_None in Hyp; lia).
      have Hheadr : run_head (split_cell_right cw o rloc) = yo.
      { rewrite /run_head /split_cell_right /=. exact (hd_inhabitant_drop _ o yo Hyo). }
      have Hso : S (o - 1)%nat = o by lia.
      have Hstep := proj2 Hrunwf (o - 1)%nat yp yo Hyp ltac:(rewrite Hso //).
      destruct Hstep as (Hidyo & Horigyo & _).
      have Hidyp := run_wf_lookup_clock (ic_run cw) (o - 1)%nat (run_head cw) yp Hrunwf Hrun0 Hyp.
      move=> originId Hoid Hcl.
      rewrite Hheadr Horigyo /= in Hoid.
      injection Hoid as <-.
      rewrite Hheadr Hidyo Hidyp /=. lia.
    + apply (Hoclk c). rewrite Hold. apply elem_of_cons. by right.
Qed.

(** Range disjointness survives a split: the halves' ranges partition [cw]'s,
    so any old cell disjoint from [cw] is disjoint from both halves, and the
    halves are disjoint from each other by construction. Needs loc-NoDup so
    an old cell at [cw]'s own location cannot survive into [rest]. *)
Lemma split_pool_rangedisj (types : gmap loc type_state) (parent : loc)
    (cells : list item_cell) (arr : list (YjsItem A)) (k : nat) (cw : item_cell)
    (o : nat) (rloc : loc) :
  types !! parent = Some (MkTypeState cells arr) ->
  cells !! k = Some cw ->
  run_wf (ic_run cw) ->
  (0 < o < length (ic_run cw))%nat ->
  (Z.of_nat (clock (item_id (run_head cw))) < 2^64)%Z ->
  (uint.Z (cell_clock cw) + Z.of_nat (length (ic_run cw)) < 2^64)%Z ->
  NoDup (ic_loc <$> all_cells types) ->
  cells_range_disjoint (all_cells types) ->
  cells_range_disjoint (all_cells (<[parent := MkTypeState (split_cells cells k o rloc) arr]> types)).
Proof.
  move=> Htypes Hck Hrunwf Ho Hckbnd Hfitscw Hnodup Hdisj.
  destruct (split_pool_perm types parent cells arr k cw o rloc Htypes Hck) as (rest & Hold & Hnew).
  have Hcwmem : cw ∈ all_cells types by (rewrite Hold; apply list_elem_of_here).
  destruct (split_cell_facts cw o rloc Hrunwf Ho)
    as (Hheadl & Hlenl & Hlenr & Hclientl & Hclientr & Hclockl & Hclockr).
  have HclkZ : uint.Z (cell_clock cw) = Z.of_nat (clock (item_id (run_head cw))).
  { rewrite /cell_clock. word. }
  have Hbo : (Z.of_nat (clock (item_id (run_head cw)) + o) < 2^64)%Z by lia.
  have HclkrZ : uint.Z (cell_clock (split_cell_right cw o rloc))
              = (uint.Z (cell_clock cw) + Z.of_nat o)%Z.
  { rewrite Hclockr HclkZ. word. }
  (* an old cell in [rest] never sits at [cw]'s location (loc-NoDup) *)
  have Hrestloc : ∀ c, c ∈ rest -> ic_loc c ≠ ic_loc cw.
  { move=> c Hc Heq.
    have Hperm : ic_loc <$> all_cells types ≡ₚ ic_loc cw :: (ic_loc <$> rest)
      by rewrite Hold //.
    have Hnd2 : NoDup (ic_loc cw :: (ic_loc <$> rest)) by rewrite -Hperm //.
    apply NoDup_cons in Hnd2 as [Hnotin _].
    apply Hnotin. rewrite -Heq. apply list_elem_of_fmap_2. exact Hc.
  }
  (* disjointness of an old cell against [cw] transfers to both halves *)
  have Holdcase : ∀ c, c ∈ rest -> cell_client c = cell_client cw ->
    (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) <= uint.Z (cell_clock cw))%Z ∨
    (uint.Z (cell_clock cw) + Z.of_nat (length (ic_run cw)) <= uint.Z (cell_clock c))%Z.
  { move=> c Hc Hcc.
    apply (Hdisj c cw); [rewrite Hold; apply elem_of_cons; by right | exact Hcwmem | exact Hcc |].
    exact (Hrestloc c Hc). }
  move=> c1 c2 Hc1 Hc2 Hcc Hlocne.
  rewrite Hnew in Hc1 Hc2.
  apply elem_of_cons in Hc1 as [-> | Hc1];
    [| apply elem_of_cons in Hc1 as [-> | Hc1]];
    apply elem_of_cons in Hc2 as [-> | Hc2];
    try (apply elem_of_cons in Hc2 as [-> | Hc2]).
  - (* leftCell vs leftCell: same loc, guard is false *)
    exfalso. exact (Hlocne eq_refl).
  - (* leftCell vs rightCell: left half strictly below the right half *)
    left. rewrite Hclockl Hlenl HclkrZ. lia.
  - (* leftCell vs old *)
    have Hcc' : cell_client c2 = cell_client cw by rewrite -Hcc Hclientl //.
    destruct (Holdcase c2 Hc2 Hcc') as [Hd | Hd].
    + right. rewrite Hclockl. lia.
    + left. rewrite Hclockl Hlenl. lia.
  - (* rightCell vs leftCell *)
    right. rewrite Hclockl Hlenl HclkrZ. lia.
  - (* rightCell vs rightCell: same loc *)
    exfalso. exact (Hlocne eq_refl).
  - (* rightCell vs old *)
    have Hcc' : cell_client c2 = cell_client cw by rewrite -Hcc Hclientr //.
    destruct (Holdcase c2 Hc2 Hcc') as [Hd | Hd].
    + right. rewrite HclkrZ. lia.
    + left. rewrite HclkrZ Hlenr. lia.
  - (* old vs leftCell *)
    have Hcc' : cell_client c1 = cell_client cw by rewrite Hcc Hclientl //.
    destruct (Holdcase c1 Hc1 Hcc') as [Hd | Hd].
    + left. rewrite Hclockl. lia.
    + right. rewrite Hclockl Hlenl. lia.
  - (* old vs rightCell *)
    have Hcc' : cell_client c1 = cell_client cw by rewrite Hcc Hclientr //.
    destruct (Holdcase c1 Hc1 Hcc') as [Hd | Hd].
    + left. rewrite HclkrZ. lia.
    + right. rewrite HclkrZ Hlenr. lia.
  - (* old vs old *)
    apply (Hdisj c1 c2); [rewrite Hold; apply elem_of_cons; by right
                         | rewrite Hold; apply elem_of_cons; by right
                         | exact Hcc | exact Hlocne].
Qed.

(** Loc-NoDup survives a split, given the fresh right location: the pool's
    location multiset gains exactly [rloc]. *)
Lemma split_pool_locdup (types : gmap loc type_state) (parent : loc)
    (cells : list item_cell) (arr : list (YjsItem A)) (k : nat) (cw : item_cell)
    (o : nat) (rloc : loc) :
  types !! parent = Some (MkTypeState cells arr) ->
  cells !! k = Some cw ->
  rloc ∉ (ic_loc <$> all_cells types) ->
  NoDup (ic_loc <$> all_cells types) ->
  NoDup (ic_loc <$> all_cells (<[parent := MkTypeState (split_cells cells k o rloc) arr]> types)).
Proof.
  move=> Htypes Hck Hfresh Hnodup.
  destruct (split_pool_perm types parent cells arr k cw o rloc Htypes Hck) as (rest & Hold & Hnew).
  have Hpermnew : ic_loc <$> all_cells (<[parent := MkTypeState (split_cells cells k o rloc) arr]> types)
                ≡ₚ ic_loc cw :: rloc :: (ic_loc <$> rest)
    by rewrite Hnew //.
  have Hpermold : ic_loc <$> all_cells types ≡ₚ ic_loc cw :: (ic_loc <$> rest)
    by rewrite Hold //.
  rewrite Hpermnew.
  have Hndold : NoDup (ic_loc cw :: (ic_loc <$> rest)) by rewrite -Hpermold //.
  apply NoDup_cons in Hndold as [Hcwnotin Hndrest].
  have Hrfresh2 : rloc ∉ ic_loc cw :: (ic_loc <$> rest) by rewrite -Hpermold //.
  apply not_elem_of_cons in Hrfresh2 as [Hrnecw Hrnotin].
  apply NoDup_cons. split.
  { apply not_elem_of_cons. split; [congruence | exact Hcwnotin]. }
  apply NoDup_cons. split; [exact Hrnotin | exact Hndrest].
Qed.

(** [split_cells] index bookkeeping (issue #28 stage D2b prep): length and
    the four lookup regions. The general [repair] uses these to relocate its
    second (clean-start) witness after the first (clean-end) split touched
    the same type. *)
Lemma split_cells_length (cells : list item_cell) (k o : nat) (rloc : loc) (cw : item_cell) :
  cells !! k = Some cw ->
  length (split_cells cells k o rloc) = S (length cells).
Proof.
  move=> Hck. rewrite /split_cells Hck !length_app /= length_take length_drop.
  have := lookup_lt_Some _ _ _ Hck. lia.
Qed.

Lemma split_cells_lookup_left (cells : list item_cell) (k o : nat) (rloc : loc) (cw : item_cell) :
  cells !! k = Some cw ->
  split_cells cells k o rloc !! k = Some (split_cell_left cw o).
Proof.
  move=> Hck. rewrite /split_cells Hck.
  have Hklen : (k < length cells)%nat := lookup_lt_Some _ _ _ Hck.
  have Htk : length (take k cells) = k by (rewrite length_take_le; lia).
  rewrite lookup_app_r; last lia.
  rewrite Htk Nat.sub_diag //.
Qed.

Lemma split_cells_lookup_right (cells : list item_cell) (k o : nat) (rloc : loc) (cw : item_cell) :
  cells !! k = Some cw ->
  split_cells cells k o rloc !! (S k) = Some (split_cell_right cw o rloc).
Proof.
  move=> Hck. rewrite /split_cells Hck.
  have Hklen : (k < length cells)%nat := lookup_lt_Some _ _ _ Hck.
  have Htk : length (take k cells) = k by (rewrite length_take_le; lia).
  rewrite lookup_app_r; last lia.
  rewrite Htk.
  have -> : (S k - k)%nat = 1%nat by lia.
  done.
Qed.

Lemma split_cells_lookup_before (cells : list item_cell) (k o : nat) (rloc : loc)
    (cw : item_cell) (j : nat) :
  cells !! k = Some cw -> (j < k)%nat ->
  split_cells cells k o rloc !! j = cells !! j.
Proof.
  move=> Hck Hj. rewrite /split_cells Hck.
  have Hklen : (k < length cells)%nat := lookup_lt_Some _ _ _ Hck.
  have Htk : length (take k cells) = k by (rewrite length_take_le; lia).
  rewrite lookup_app_l; last lia.
  rewrite lookup_take_lt; [done | lia].
Qed.

Lemma split_cells_lookup_after (cells : list item_cell) (k o : nat) (rloc : loc)
    (cw : item_cell) (j : nat) :
  cells !! k = Some cw -> (k < j)%nat ->
  split_cells cells k o rloc !! (S j) = cells !! j.
Proof.
  move=> Hck Hj. rewrite /split_cells Hck.
  have Hklen : (k < length cells)%nat := lookup_lt_Some _ _ _ Hck.
  have Htk : length (take k cells) = k by (rewrite length_take_le; lia).
  rewrite lookup_app_r; last lia.
  rewrite Htk /=.
  have -> : (S j - k)%nat = S (S (j - S k)) by lia.
  simpl. rewrite lookup_drop. f_equal. lia.
Qed.

(** A clock covered by [cw]'s range is covered by exactly one of the two
    halves; the dispatch is [clkZ < clock cw + o]. Relocates a covering
    witness across a split when both origins land in the same run. *)
Lemma split_cell_cover (cw : item_cell) (o : nat) (rloc : loc) (clkZ : Z) :
  run_wf (ic_run cw) ->
  (0 < o < length (ic_run cw))%nat ->
  (Z.of_nat (clock (item_id (run_head cw))) < 2^64)%Z ->
  (uint.Z (cell_clock cw) + Z.of_nat (length (ic_run cw)) < 2^64)%Z ->
  (uint.Z (cell_clock cw) <= clkZ)%Z ->
  (clkZ < uint.Z (cell_clock cw) + Z.of_nat (length (ic_run cw)))%Z ->
  ((clkZ < uint.Z (cell_clock cw) + Z.of_nat o)%Z ∧
   (uint.Z (cell_clock (split_cell_left cw o)) <= clkZ)%Z ∧
   (clkZ < uint.Z (cell_clock (split_cell_left cw o))
           + Z.of_nat (length (ic_run (split_cell_left cw o))))%Z)
  ∨ ((uint.Z (cell_clock cw) + Z.of_nat o <= clkZ)%Z ∧
     (uint.Z (cell_clock (split_cell_right cw o rloc)) <= clkZ)%Z ∧
     (clkZ < uint.Z (cell_clock (split_cell_right cw o rloc))
             + Z.of_nat (length (ic_run (split_cell_right cw o rloc))))%Z).
Proof.
  move=> Hrunwf Ho Hckbnd Hfitscw Hle Hlt.
  destruct (split_cell_facts cw o rloc Hrunwf Ho)
    as (Hheadl & Hlenl & Hlenr & Hclientl & Hclientr & Hclockl & Hclockr).
  have HclkZ : uint.Z (cell_clock cw) = Z.of_nat (clock (item_id (run_head cw))).
  { rewrite /cell_clock. word. }
  have Hbo : (Z.of_nat (clock (item_id (run_head cw)) + o) < 2^64)%Z by lia.
  have HclkrZ : uint.Z (cell_clock (split_cell_right cw o rloc))
              = (uint.Z (cell_clock cw) + Z.of_nat o)%Z.
  { rewrite Hclockr HclkZ. word. }
  destruct (decide (clkZ < uint.Z (cell_clock cw) + Z.of_nat o)%Z) as [Hd | Hd].
  - left. rewrite Hclockl Hlenl. split_and!; lia.
  - right. rewrite HclkrZ Hlenr. split_and!; lia.
Qed.

(** Every pool cell's id components round-trip through [w64] heap fields
    ([own_dll_id_bounds], lifted over the big-sep): the glue from nat-level
    replay facts to W64 comparisons (issue #28 stage D). *)
Lemma types_cells_id_bounds2 (types : gmap loc type_state) :
  ([∗ map] parent ↦ ts ∈ types,
      own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
      ⌜YjsArrInvariant (ty_arr ts)⌝) -∗
  ⌜∀ c, c ∈ all_cells types ->
     (Z.of_nat (clientId (item_id (run_head c))) < 2^64)%Z ∧
     (Z.of_nat (clock (item_id (run_head c))) < 2^64)%Z⌝.
Proof.
  iIntros "Htypes".
  iAssert ([∗ map] p ↦ ts ∈ types,
      ⌜∀ c, c ∈ ty_cells ts ->
         (Z.of_nat (clientId (item_id (run_head c))) < 2^64)%Z ∧
         (Z.of_nat (clock (item_id (run_head c))) < 2^64)%Z⌝)%I
    with "[Htypes]" as "H".
  { iApply (big_sepM_impl with "Htypes").
    iIntros "!#" (p ts Hp) "[Hyt _]".
    iDestruct "Hyt" as (yt tl) "(Hparent & Hdll & %Hlen & %Hrepr & %Hcpar)".
    iApply (own_dll_id_bounds with "Hdll"). }
  iDestruct (big_sepM_pure with "H") as %Hall.
  iPureIntro. move=> c Hc.
  apply all_cells_elem_of in Hc. destruct Hc as (p & ts & Hp & Hcts).
  exact (Hall p ts Hp c Hcts).
Qed.

(** A split preserves each type's model document, and the map's domain. *)
Lemma split_types_preserve (types : gmap loc type_state) (parent : loc)
    (cells : list item_cell) (arr : list (YjsItem A)) (k o : nat) (rloc : loc)
    (cw : item_cell) :
  types !! parent = Some (MkTypeState cells arr) ->
  cells !! k = Some cw ->
  ∀ p ts', <[parent := MkTypeState (split_cells cells k o rloc) arr]> types !! p = Some ts' ->
    ∃ ts, types !! p = Some ts ∧ ty_arr ts' = ty_arr ts ∧
          run_flatten (ty_cells ts') = run_flatten (ty_cells ts).
Proof.
  move=> Htypes Hck p ts' Hp.
  destruct (decide (p = parent)) as [-> | Hne].
  - rewrite lookup_insert_eq in Hp. injection Hp as <-.
    exists (MkTypeState cells arr). split_and!; [exact Htypes | done |].
    rewrite /= (split_cells_flatten cells k o rloc cw Hck) //.
  - rewrite lookup_insert_ne in Hp; last congruence.
    exists ts'. split_and!; done.
Qed.

(** Coverage transport across a split: a pool cell covering a clock is
    replaced by a covering pool cell of the split map (one of the halves
    when the covered cell IS the split one). *)
Lemma split_pool_cover (types : gmap loc type_state) (parent : loc)
    (cells : list item_cell) (arr : list (YjsItem A)) (k : nat) (cw : item_cell)
    (o : nat) (rloc : loc) (ccl : w64) (clkZ : Z) :
  types !! parent = Some (MkTypeState cells arr) ->
  cells !! k = Some cw ->
  run_wf (ic_run cw) ->
  (0 < o < length (ic_run cw))%nat ->
  (Z.of_nat (clock (item_id (run_head cw))) < 2^64)%Z ->
  (uint.Z (cell_clock cw) + Z.of_nat (length (ic_run cw)) < 2^64)%Z ->
  rloc ∉ (ic_loc <$> all_cells types) ->
  ∀ c, c ∈ all_cells types ->
    cell_client c = ccl ->
    (uint.Z (cell_clock c) <= clkZ)%Z ->
    (clkZ < uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)))%Z ->
    ∃ c', c' ∈ all_cells (<[parent := MkTypeState (split_cells cells k o rloc) arr]> types) ∧
          cell_client c' = ccl ∧
          (uint.Z (cell_clock c') <= clkZ)%Z ∧
          (clkZ < uint.Z (cell_clock c') + Z.of_nat (length (ic_run c')))%Z ∧
          ic_parent c' = ic_parent c ∧
          (c' = c ∨ (c = cw ∧ (1 < length (ic_run cw))%nat ∧
                     (ic_loc c' = ic_loc cw ∨
                      ic_loc c' ∉ (ic_loc <$> all_cells types)))).
Proof.
  move=> Htypes Hck Hrunwf Ho Hckbnd Hfitscw Hfresh c Hc Hccl Hle Hlt.
  destruct (split_pool_perm types parent cells arr k cw o rloc Htypes Hck) as (rest & Hold & Hnew).
  destruct (split_cell_facts cw o rloc Hrunwf Ho)
    as (Hheadl & Hlenl & Hlenr & Hclientl & Hclientr & Hclockl & Hclockr).
  rewrite Hold in Hc. apply elem_of_cons in Hc as [-> | Hc].
  - destruct (split_cell_cover cw o rloc clkZ Hrunwf Ho Hckbnd Hfitscw Hle Hlt)
      as [(Hd & Hle' & Hlt') | (Hd & Hle' & Hlt')].
    + exists (split_cell_left cw o). split_and!;
        [rewrite Hnew; apply list_elem_of_here | rewrite Hclientl; exact Hccl | exact Hle' | exact Hlt' | done |].
      right. split_and!; [done | lia | by left].
    + exists (split_cell_right cw o rloc). split_and!;
        [rewrite Hnew; apply elem_of_cons; right; apply list_elem_of_here
        | rewrite Hclientr; exact Hccl | exact Hle' | exact Hlt' | done |].
      right. split_and!; [done | lia | by right].
  - exists c. split_and!;
      [rewrite Hnew; apply elem_of_cons; right; apply elem_of_cons; by right
      | exact Hccl | exact Hle | exact Hlt | done | by left].
Qed.

(** Cells away from the split location survive a split verbatim. *)
Lemma split_pool_stable (types : gmap loc type_state) (parent : loc)
    (cells : list item_cell) (arr : list (YjsItem A)) (k o : nat) (rloc : loc)
    (cw : item_cell) :
  types !! parent = Some (MkTypeState cells arr) ->
  cells !! k = Some cw ->
  ∀ c, c ∈ all_cells types -> ic_loc c ≠ ic_loc cw ->
    c ∈ all_cells (<[parent := MkTypeState (split_cells cells k o rloc) arr]> types).
Proof.
  move=> Htypes Hck c Hc Hlocne.
  destruct (split_pool_perm types parent cells arr k cw o rloc Htypes Hck) as (rest & Hold & Hnew).
  rewrite Hold in Hc. apply elem_of_cons in Hc as [-> | Hc].
  { exfalso. exact (Hlocne eq_refl). }
  rewrite Hnew. apply elem_of_cons; right. apply elem_of_cons; by right.
Qed.

(** A split grows only the split client's run list, by one. *)
Lemma split_pool_client_run_len (types : gmap loc type_state) (parent : loc)
    (cells : list item_cell) (arr : list (YjsItem A)) (k : nat) (cw : item_cell)
    (o : nat) (rloc : loc) (kc : w64) :
  types !! parent = Some (MkTypeState cells arr) ->
  cells !! k = Some cw ->
  run_wf (ic_run cw) ->
  (0 < o < length (ic_run cw))%nat ->
  (length (client_run (<[parent := MkTypeState (split_cells cells k o rloc) arr]> types) kc)
   <= S (length (client_run types kc)))%nat.
Proof.
  move=> Htypes Hck Hrunwf Ho.
  destruct (split_pool_perm types parent cells arr k cw o rloc Htypes Hck) as (rest & Hold & Hnew).
  destruct (split_cell_facts cw o rloc Hrunwf Ho)
    as (Hheadl & Hlenl & Hlenr & Hclientl & Hclientr & Hclockl & Hclockr).
  rewrite /client_run.
  have Hmsl : ∀ l : list item_cell, length (merge_sort cell_le l) = length l.
  { move=> l. apply Permutation_length. apply merge_sort_Permutation. }
  rewrite !Hmsl.
  have -> : length (filter (λ c, cell_client c = kc)
              (all_cells (<[parent := MkTypeState (split_cells cells k o rloc) arr]> types)))
          = length (filter (λ c, cell_client c = kc)
              (split_cell_left cw o :: split_cell_right cw o rloc :: rest)).
  { apply Permutation_length. by rewrite Hnew. }
  have -> : length (filter (λ c, cell_client c = kc) (all_cells types))
          = length (filter (λ c, cell_client c = kc) (cw :: rest)).
  { apply Permutation_length. by rewrite Hold. }
  rewrite !filter_cons Hclientl Hclientr.
  case_decide; simpl; lia.
Qed.

(* ----- invariant-carrying split wrappers (issue #28 stage D2b) ------------
   The D1b heap specs packaged with the D1c/D2a pool bookkeeping: pool
   invariants out for pool invariants in, plus the transport facts [repair]
   needs to sequence two splits (document/domain preservation, coverage
   transport with provenance, stability away from the split location, run
   list growth) and the boundary cell itself. *)

Definition pool_invs (types : gmap loc type_state) : Prop :=
  (∀ c, c ∈ all_cells types -> (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) < 2^64)%Z) ∧
  NoDup (ic_loc <$> all_cells types) ∧
  cells_range_disjoint (all_cells types) ∧
  (∀ c, c ∈ all_cells types -> cell_origin_clk c).

Definition split_step_facts (types types' : gmap loc type_state) (w : item_cell) : Prop :=
  (∀ p ts', types' !! p = Some ts' ->
     ∃ ts, types !! p = Some ts ∧ ty_arr ts' = ty_arr ts ∧
           run_flatten (ty_cells ts') = run_flatten (ty_cells ts)) ∧
  (∀ p, is_Some (types !! p) -> is_Some (types' !! p)) ∧
  (∀ kc, (length (client_run types' kc) <= S (length (client_run types kc)))%nat) ∧
  (∀ c, c ∈ all_cells types -> ic_loc c ≠ ic_loc w -> c ∈ all_cells types') ∧
  (∀ (ccl : w64) (clkZ : Z) (c : item_cell), c ∈ all_cells types ->
     cell_client c = ccl -> (uint.Z (cell_clock c) <= clkZ)%Z ->
     (clkZ < uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)))%Z ->
     ∃ c', c' ∈ all_cells types' ∧ cell_client c' = ccl ∧
           (uint.Z (cell_clock c') <= clkZ)%Z ∧
           (clkZ < uint.Z (cell_clock c') + Z.of_nat (length (ic_run c')))%Z ∧
           ic_parent c' = ic_parent c ∧
           (c' = c ∨ (c = w ∧ (1 < length (ic_run w))%nat ∧
                      (ic_loc c' = ic_loc w ∨
                       ic_loc c' ∉ (ic_loc <$> all_cells types))))) ∧
  (∀ p ts ts', types !! p = Some ts -> types' !! p = Some ts' ->
     Forall cell_unit (ty_cells ts) -> ts' = ts) ∧
  (∀ c', c' ∈ all_cells types' -> ∃ c, c ∈ all_cells types ∧
     cell_client c' = cell_client c ∧
     (uint.Z (cell_clock c) <= uint.Z (cell_clock c'))%Z ∧
     (uint.Z (cell_clock c') + Z.of_nat (length (ic_run c')) <=
      uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)))%Z).

(** Every post-split cell's clock range sits inside a same-client cell of the
    original pool (the halves inside the split cell, the rest inside itself);
    this is what transports the range-form freshness facts across a split. *)
Lemma split_pool_subrange (types : gmap loc type_state) (parent : loc)
    (cells : list item_cell) (arr : list (YjsItem A)) (k : nat) (cw : item_cell)
    (o : nat) (rloc : loc) :
  types !! parent = Some (MkTypeState cells arr) ->
  cells !! k = Some cw ->
  run_wf (ic_run cw) ->
  (0 < o < length (ic_run cw))%nat ->
  (Z.of_nat (clock (item_id (run_head cw))) < 2^64)%Z ->
  cell_fits cw ->
  ∀ c', c' ∈ all_cells (<[parent := MkTypeState (split_cells cells k o rloc) arr]> types) ->
    ∃ c, c ∈ all_cells types ∧ cell_client c' = cell_client c ∧
      (uint.Z (cell_clock c) <= uint.Z (cell_clock c'))%Z ∧
      (uint.Z (cell_clock c') + Z.of_nat (length (ic_run c')) <=
       uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)))%Z.
Proof.
  move=> Htypes Hck Hrunwf Ho Hckbnd Hfitscw c' Hc'.
  destruct (split_pool_perm types parent cells arr k cw o rloc Htypes Hck)
    as (rest & Hold & Hnew).
  destruct (split_cell_facts cw o rloc Hrunwf Ho)
    as (Hheadl & Hlenl & Hlenr & Hclientl & Hclientr & Hclockl & Hclockr).
  have HclkZ : uint.Z (cell_clock cw) = Z.of_nat (clock (item_id (run_head cw))).
  { rewrite /cell_clock. word. }
  rewrite Hnew in Hc'.
  apply elem_of_cons in Hc' as [-> | Hc'].
  { exists cw. split_and!.
    - rewrite Hold. apply list_elem_of_here.
    - exact Hclientl.
    - rewrite Hclockl. lia.
    - rewrite Hclockl Hlenl. lia. }
  apply elem_of_cons in Hc' as [-> | Hc'].
  { have Hzr : (uint.Z (cell_clock (split_cell_right cw o rloc))
               = Z.of_nat (clock (item_id (run_head cw)) + o))%Z.
    { rewrite Hclockr.
      have Hbo : (Z.of_nat (clock (item_id (run_head cw)) + o) < 2^64)%Z.
      { rewrite /cell_fits in Hfitscw. clear -HclkZ Hfitscw Ho Hckbnd. lia. }
      clear -Hbo. word. }
    exists cw. split_and!.
    - rewrite Hold. apply list_elem_of_here.
    - exact Hclientr.
    - rewrite Hzr. lia.
    - rewrite Hzr Hlenr. lia. }
  { exists c'. split_and!.
    - rewrite Hold. apply elem_of_cons. by right.
    - done.
    - lia.
    - lia. }
Qed.

Lemma wp_store__splitAtAndGetLeft_inv (s mref : loc) (idv : yjs.id.t)
    (types : gmap loc type_state) (cw : item_cell) :
  cw ∈ all_cells types ->
  cell_client cw = idv.(yjs.id.clientId') ->
  (uint.Z (cell_clock cw) <= uint.Z idv.(yjs.id.clock'))%Z ->
  (uint.Z idv.(yjs.id.clock') < uint.Z (cell_clock cw) + Z.of_nat (length (ic_run cw)))%Z ->
  pool_invs types ->
  {{{ is_pkg_init yjs ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types ∗
      ([∗ map] p ↦ ts ∈ types,
          own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) }}}
    s @! (go.PointerType yjs.store) @! "splitAtAndGetLeft" #idv
  {{{ (types' : gmap loc type_state), RET (#(ic_loc cw), #true);
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types' ∗
      ([∗ map] p ↦ ts ∈ types',
          own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) ∗
      ⌜pool_invs types'⌝ ∗ ⌜split_step_facts types types' cw⌝ ∗
      ⌜∃ cL, cL ∈ all_cells types' ∧ ic_loc cL = ic_loc cw ∧
             cell_client cL = idv.(yjs.id.clientId') ∧
             (uint.Z (cell_clock cL) + Z.of_nat (length (ic_run cL))
              = uint.Z idv.(yjs.id.clock') + 1)%Z ∧
             ic_parent cL = ic_parent cw⌝ }}}.
Proof using Type*.
  move=> Hcwmem Hcwcc Hcwle Hcwlt [Hfits [Hnodup [Hrangedisj Horiginclk]]].
  iIntros (Φ) "(#Hpkg & Hitemsf & Hitemmap & Htypes) HΦ".
  have Hcoords := Hcwmem.
  apply all_cells_elem_of in Hcoords.
  destruct Hcoords as (parent & ts & Htypes0 & Hcts).
  destruct ts as [cells arr]. simpl in Hcts.
  apply list_elem_of_lookup_1 in Hcts as [k Hck].
  iDestruct (types_cells_id_bounds2 with "Htypes") as %Hbnds.
  have Hckbnd : (Z.of_nat (clock (item_id (run_head cw))) < 2^64)%Z := proj2 (Hbnds cw Hcwmem).
  iDestruct (types_cell_acc_gen types cw Hcwmem with "Htypes") as "Hacc".
  iNamed "Hacc".
  iDestruct ("Hback" with "Hval") as "Htypes".
  have Hrunwf := Hrun.
  have Hfitscw := Hfits cw Hcwmem.
  have Hlenpos : (1 <= Z.of_nat (length (ic_run cw)))%Z.
  { destruct Hrunwf as [Hne0 _]. destruct (ic_run cw) as [|? ?]; [done | simpl; lia]. }
  wp_apply (wp_store__splitAtAndGetLeft_range s mref idv types parent cells arr k cw
              Htypes0 Hck Hcwcc Hcwle Hcwlt Hfits Hnodup Hrangedisj
              with "[$Hpkg $Hitemsf $Hitemmap $Htypes]").
  iIntros (types') "(Hitemsf & Hitemmap & Htypes & %Hbranch)".
  destruct Hbranch as [[Hoeq ->] | [Holt2 (rloc & Hrnn & Hrfresh & ->)]].
  - (* no split: the run already ends at the id *)
    iApply ("HΦ" $! types).
    iFrame "Hitemsf Hitemmap Htypes".
    iPureIntro. split_and!.
    + split_and!; [exact Hfits | exact Hnodup | exact Hrangedisj | exact Horiginclk].
    + split_and!.
      * move=> p ts' Hp. exists ts'. split_and!; done.
      * move=> p Hp. exact Hp.
      * move=> kc. lia.
      * move=> c Hc _. exact Hc.
      * move=> ccl clkZ c Hc Hccl Hle2 Hlt2. exists c. split_and!; try done. by left.
      * move=> p ts0 ts0' Hp Hp' _. congruence.
      * move=> c1 Hc1. exists c1. split_and!; [exact Hc1 | done | lia | lia].
    + exists cw. split_and!; [exact Hcwmem | done | exact Hcwcc | | done].
      clear -Hoeq Hcwle Hcwlt Hlenpos. word.
  - (* split just after the id *)
    have Ho2 : (0 < (uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) + 1
                < length (ic_run cw))%nat by lia.
    iApply ("HΦ" $! (<[parent := MkTypeState
        (split_cells cells k ((uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) + 1) rloc)
        arr]> types)).
    iFrame "Hitemsf Hitemmap Htypes".
    iPureIntro. split_and!.
    + split_and!.
      * exact (split_pool_fits types parent cells arr k cw _ rloc Htypes0 Hck Hrunwf Ho2 Hckbnd Hfits).
      * exact (split_pool_locdup types parent cells arr k cw _ rloc Htypes0 Hck Hrfresh Hnodup).
      * exact (split_pool_rangedisj types parent cells arr k cw _ rloc Htypes0 Hck Hrunwf Ho2 Hckbnd Hfitscw Hnodup Hrangedisj).
      * exact (split_pool_originclk types parent cells arr k cw _ rloc Htypes0 Hck Hrunwf Ho2 Horiginclk).
    + split_and!.
      * exact (split_types_preserve types parent cells arr k _ rloc cw Htypes0 Hck).
      * move=> p Hp. destruct (decide (p = parent)) as [-> | Hne].
        { rewrite lookup_insert_eq. eauto. }
        { rewrite lookup_insert_ne; [exact Hp | congruence]. }
      * move=> kc. exact (split_pool_client_run_len types parent cells arr k cw _ rloc kc Htypes0 Hck Hrunwf Ho2).
      * move=> c Hc Hlocne. exact (split_pool_stable types parent cells arr k _ rloc cw Htypes0 Hck c Hc Hlocne).
      * move=> ccl clkZ c Hc Hccl Hle2 Hlt2.
        exact (split_pool_cover types parent cells arr k cw _ rloc ccl clkZ Htypes0 Hck Hrunwf Ho2 Hckbnd Hfitscw Hrfresh c Hc Hccl Hle2 Hlt2).
      * move=> p ts0 ts0' Hp Hp' Hunit0.
        destruct (decide (p = parent)) as [-> | Hnep].
        { rewrite Htypes0 in Hp. injection Hp as <-.
          rewrite lookup_insert_eq in Hp'. injection Hp' as <-.
          exfalso. simpl in Hunit0.
          have Hu := Forall_lookup_1 _ _ _ _ Hunit0 Hck.
          rewrite /cell_unit in Hu. lia. }
        { rewrite lookup_insert_ne in Hp'; last congruence. congruence. }
      * exact (split_pool_subrange types parent cells arr k cw _ rloc Htypes0 Hck Hrunwf Ho2 Hckbnd Hfitscw).
    + destruct (split_pool_perm types parent cells arr k cw
                  ((uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) + 1) rloc Htypes0 Hck)
        as (rest & Hold & Hnew).
      destruct (split_cell_facts cw
                  ((uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) + 1) rloc Hrunwf Ho2)
        as (Hheadl & Hlenl & Hlenr & Hclientl & Hclientr & Hclockl & Hclockr).
      exists (split_cell_left cw ((uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) + 1)).
      split_and!.
      * rewrite Hnew. apply list_elem_of_here.
      * done.
      * rewrite Hclientl. exact Hcwcc.
      * rewrite Hclockl Hlenl. clear -Hcwle Hcwlt Hlenpos. word.
      * done.
Qed.

Lemma wp_store__splitAtAndGetRight_inv (s mref : loc) (idv : yjs.id.t)
    (types : gmap loc type_state) (cw : item_cell) :
  cw ∈ all_cells types ->
  cell_client cw = idv.(yjs.id.clientId') ->
  (uint.Z (cell_clock cw) <= uint.Z idv.(yjs.id.clock'))%Z ->
  (uint.Z idv.(yjs.id.clock') < uint.Z (cell_clock cw) + Z.of_nat (length (ic_run cw)))%Z ->
  pool_invs types ->
  {{{ is_pkg_init yjs ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types ∗
      ([∗ map] p ↦ ts ∈ types,
          own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) }}}
    s @! (go.PointerType yjs.store) @! "splitAtAndGetRight" #idv
  {{{ (rl : loc) (types' : gmap loc type_state), RET (#rl, #true);
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types' ∗
      ([∗ map] p ↦ ts ∈ types',
          own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) ∗
      ⌜pool_invs types'⌝ ∗ ⌜split_step_facts types types' cw⌝ ∗
      ⌜∃ cR, cR ∈ all_cells types' ∧ ic_loc cR = rl ∧
             cell_client cR = idv.(yjs.id.clientId') ∧
             (uint.Z (cell_clock cR) = uint.Z idv.(yjs.id.clock'))%Z ∧
             ic_parent cR = ic_parent cw⌝ }}}.
Proof using Type*.
  move=> Hcwmem Hcwcc Hcwle Hcwlt [Hfits [Hnodup [Hrangedisj Horiginclk]]].
  iIntros (Φ) "(#Hpkg & Hitemsf & Hitemmap & Htypes) HΦ".
  have Hcoords := Hcwmem.
  apply all_cells_elem_of in Hcoords.
  destruct Hcoords as (parent & ts & Htypes0 & Hcts).
  destruct ts as [cells arr]. simpl in Hcts.
  apply list_elem_of_lookup_1 in Hcts as [k Hck].
  iDestruct (types_cells_id_bounds2 with "Htypes") as %Hbnds.
  have Hckbnd : (Z.of_nat (clock (item_id (run_head cw))) < 2^64)%Z := proj2 (Hbnds cw Hcwmem).
  iDestruct (types_cell_acc_gen types cw Hcwmem with "Htypes") as "Hacc".
  iNamed "Hacc".
  iDestruct ("Hback" with "Hval") as "Htypes".
  have Hrunwf := Hrun.
  have Hfitscw := Hfits cw Hcwmem.
  have Hlenpos : (1 <= Z.of_nat (length (ic_run cw)))%Z.
  { destruct Hrunwf as [Hne0 _]. destruct (ic_run cw) as [|? ?]; [done | simpl; lia]. }
  wp_apply (wp_store__splitAtAndGetRight_range s mref idv types parent cells arr k cw
              Htypes0 Hck Hcwcc Hcwle Hcwlt Hfits Hnodup Hrangedisj
              with "[$Hpkg $Hitemsf $Hitemmap $Htypes]").
  iIntros (rl types') "(Hitemsf & Hitemmap & Htypes & %Hbranch)".
  destruct Hbranch as [[Hoeq [-> ->]] | [Hopos (Hrlnn & Hrlfresh & ->)]].
  - (* no split: the run already starts at the id *)
    iApply ("HΦ" $! (ic_loc cw) types).
    iFrame "Hitemsf Hitemmap Htypes".
    iPureIntro. split_and!.
    + split_and!; [exact Hfits | exact Hnodup | exact Hrangedisj | exact Horiginclk].
    + split_and!.
      * move=> p ts' Hp. exists ts'. split_and!; done.
      * move=> p Hp. exact Hp.
      * move=> kc. lia.
      * move=> c Hc _. exact Hc.
      * move=> ccl clkZ c Hc Hccl Hle2 Hlt2. exists c. split_and!; try done. by left.
      * move=> p ts0 ts0' Hp Hp' _. congruence.
      * move=> c1 Hc1. exists c1. split_and!; [exact Hc1 | done | lia | lia].
    + exists cw. split_and!; [exact Hcwmem | done | exact Hcwcc | | done].
      clear -Hoeq Hcwle. word.
  - (* split at the offset: the fresh right half starts at the id *)
    have Ho2 : (0 < (uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw))
                < length (ic_run cw))%nat.
    { split; [exact Hopos |]. clear -Hcwle Hcwlt. word. }
    iApply ("HΦ" $! rl (<[parent := MkTypeState
        (split_cells cells k (uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) rl)
        arr]> types)).
    iFrame "Hitemsf Hitemmap Htypes".
    iPureIntro. split_and!.
    + split_and!.
      * exact (split_pool_fits types parent cells arr k cw _ rl Htypes0 Hck Hrunwf Ho2 Hckbnd Hfits).
      * exact (split_pool_locdup types parent cells arr k cw _ rl Htypes0 Hck Hrlfresh Hnodup).
      * exact (split_pool_rangedisj types parent cells arr k cw _ rl Htypes0 Hck Hrunwf Ho2 Hckbnd Hfitscw Hnodup Hrangedisj).
      * exact (split_pool_originclk types parent cells arr k cw _ rl Htypes0 Hck Hrunwf Ho2 Horiginclk).
    + split_and!.
      * exact (split_types_preserve types parent cells arr k _ rl cw Htypes0 Hck).
      * move=> p Hp. destruct (decide (p = parent)) as [-> | Hne].
        { rewrite lookup_insert_eq. eauto. }
        { rewrite lookup_insert_ne; [exact Hp | congruence]. }
      * move=> kc. exact (split_pool_client_run_len types parent cells arr k cw _ rl kc Htypes0 Hck Hrunwf Ho2).
      * move=> c Hc Hlocne. exact (split_pool_stable types parent cells arr k _ rl cw Htypes0 Hck c Hc Hlocne).
      * move=> ccl clkZ c Hc Hccl Hle2 Hlt2.
        exact (split_pool_cover types parent cells arr k cw _ rl ccl clkZ Htypes0 Hck Hrunwf Ho2 Hckbnd Hfitscw Hrlfresh c Hc Hccl Hle2 Hlt2).
      * move=> p ts0 ts0' Hp Hp' Hunit0.
        destruct (decide (p = parent)) as [-> | Hnep].
        { rewrite Htypes0 in Hp. injection Hp as <-.
          rewrite lookup_insert_eq in Hp'. injection Hp' as <-.
          exfalso. simpl in Hunit0.
          have Hu := Forall_lookup_1 _ _ _ _ Hunit0 Hck.
          rewrite /cell_unit in Hu. lia. }
        { rewrite lookup_insert_ne in Hp'; last congruence. congruence. }
      * exact (split_pool_subrange types parent cells arr k cw _ rl Htypes0 Hck Hrunwf Ho2 Hckbnd Hfitscw).
    + destruct (split_pool_perm types parent cells arr k cw
                  (uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) rl Htypes0 Hck)
        as (rest & Hold & Hnew).
      destruct (split_cell_facts cw
                  (uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) rl Hrunwf Ho2)
        as (Hheadl & Hlenl & Hlenr & Hclientl & Hclientr & Hclockl & Hclockr).
      have HclkZ : uint.Z (cell_clock cw) = Z.of_nat (clock (item_id (run_head cw))).
      { rewrite /cell_clock. word. }
      exists (split_cell_right cw (uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw)) rl).
      split_and!.
      * rewrite Hnew. apply elem_of_cons; right. apply list_elem_of_here.
      * done.
      * rewrite Hclientr. exact Hcwcc.
      * rewrite Hclockr.
        have Hbo : (Z.of_nat (clock (item_id (run_head cw))
                    + (uint.nat idv.(yjs.id.clock') - uint.nat (cell_clock cw))) < 2^64)%Z.
        { clear -HclkZ Hfitscw Hcwlt Hcwle. lia. }
        clear -HclkZ Hbo Hcwle. word.
      * done.
Qed.

(** [store.getOrCreateYType], lookup-hit case: the name is already bound in
    the registry, so the creation branch is dead and the bound type comes
    back. This is the only case the verified update path needs — see
    [wp_store__applyUpdate]'s bound-names precondition (the on-the-fly type
    creation of y-octo's update path is outside the verified subset for now:
    it would grow [types]/[bind]/[m] with a fresh empty type mid-batch). *)
Lemma wp_store__getOrCreateYType (s tref : loc) (dq : dfrac) (bind : gmap P loc)
    (nm : go_string) (p : loc) :
  bind !! nm = Some p ->
  {{{ is_pkg_init yjs ∗ (s .[(yjs.store.t), "types"]) ↦ tref ∗ own_map tref dq bind }}}
    s @! (go.PointerType yjs.store) @! "getOrCreateYType" #nm
  {{{ RET #p; (s .[(yjs.store.t), "types"]) ↦ tref ∗ own_map tref dq bind }}}.
Proof using Type*.
  move=> Hp.
  iIntros (Φ) "(#Hpkg & Htypesf & Hmap) HΦ".
  wp_method_call. wp_call. wp_call. wp_auto.
  wp_apply (wp_map_lookup2 with "Hmap"). iIntros "Hmap".
  rewrite Hp /=.
  wp_auto.
  iApply "HΦ". iFrame "Htypesf Hmap".
Qed.

(* ----- the general repair (issue #28 stage D2b) ---------------------------
   [store.repair] over the invariant-carrying split wrappers: the origin ids
   may address ANY char of their covering cells' runs; the clean-end /
   clean-start splits put them on run boundaries. The two splits are
   sequenced by the wrappers' transport records. *)

(** Loc-NoDup makes the location injective on the pool. *)
Lemma pool_loc_inj (pool : list item_cell) :
  NoDup (ic_loc <$> pool) ->
  ∀ x y, x ∈ pool → y ∈ pool → ic_loc x = ic_loc y → x = y.
Proof.
  move=> Hnd x y Hx Hy Hxy.
  apply list_elem_of_lookup_1 in Hx as [ix Hix].
  apply list_elem_of_lookup_1 in Hy as [iy Hiy].
  have Hlix : (ic_loc <$> pool) !! ix = Some (ic_loc y) by (rewrite list_lookup_fmap Hix /= Hxy //).
  have Hliy : (ic_loc <$> pool) !! iy = Some (ic_loc y) by (rewrite list_lookup_fmap Hiy //).
  have Hijeq : ix = iy := NoDup_lookup _ _ _ _ Hnd Hlix Hliy.
  congruence.
Qed.

(** What [repair] guarantees about the type map: per-type model documents and
    the domain survive, and each client's run list grows by at most the two
    possible splits. *)
Definition repair_types_facts (types types2 : gmap loc type_state) : Prop :=
  (∀ p ts', types2 !! p = Some ts' ->
     ∃ ts, types !! p = Some ts ∧ ty_arr ts' = ty_arr ts ∧
           run_flatten (ty_cells ts') = run_flatten (ty_cells ts)) ∧
  (∀ p, is_Some (types !! p) -> is_Some (types2 !! p)) ∧
  (∀ kc, (length (client_run types2 kc) <= 2 + length (client_run types kc))%nat) ∧
  (∀ p ts ts', types !! p = Some ts -> types2 !! p = Some ts' ->
     Forall cell_unit (ty_cells ts) -> ts' = ts) ∧
  (∀ c', c' ∈ all_cells types2 -> ∃ c, c ∈ all_cells types ∧
     cell_client c' = cell_client c ∧
     (uint.Z (cell_clock c) <= uint.Z (cell_clock c'))%Z ∧
     (uint.Z (cell_clock c') + Z.of_nat (length (ic_run c')) <=
      uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)))%Z).

Lemma repair_types_facts_refl (types : gmap loc type_state) :
  repair_types_facts types types.
Proof.
  split_and!.
  - move=> p ts' Hp. exists ts'. split_and!; done.
  - move=> p Hp. exact Hp.
  - move=> kc. lia.
  - move=> p ts ts' Hp Hp' _. congruence.
  - move=> c' Hc'. exists c'. split_and!; [exact Hc' | done | lia | lia].
Qed.

Lemma split_step_facts_single (types types1 : gmap loc type_state) (w : item_cell) :
  split_step_facts types types1 w -> repair_types_facts types types1.
Proof.
  move=> H. destruct H as (Hp & Hd & Hr & _ & _ & Hu & Hsub).
  split_and!; [exact Hp | exact Hd | move=> kc; have := Hr kc; lia | exact Hu | exact Hsub].
Qed.

Lemma split_step_facts_compose (types types1 types2 : gmap loc type_state) (w1 w2 : item_cell) :
  split_step_facts types types1 w1 -> split_step_facts types1 types2 w2 ->
  repair_types_facts types types2.
Proof.
  move=> H1 H2.
  destruct H1 as (Hp1 & Hd1 & Hr1 & _ & _ & Hu1 & Hsub1).
  destruct H2 as (Hp2 & Hd2 & Hr2 & _ & _ & Hu2 & Hsub2).
  split_and!.
  - move=> p ts2 Hp.
    destruct (Hp2 p ts2 Hp) as (ts1 & Hp1' & Ha2 & Hf2).
    destruct (Hp1 p ts1 Hp1') as (ts0 & Hp0 & Ha1 & Hf1).
    exists ts0. split_and!; [exact Hp0 | congruence | congruence].
  - move=> p Hp. exact (Hd2 p (Hd1 p Hp)).
  - move=> kc. have := Hr1 kc. have := Hr2 kc. lia.
  - move=> p ts ts2 Hpa Hpb Hunit.
    destruct (Hd1 p (mk_is_Some _ _ Hpa)) as [ts1 Hpm].
    have Hts1 : ts1 = ts := Hu1 p ts ts1 Hpa Hpm Hunit.
    subst ts1.
    exact (Hu2 p ts ts2 Hpm Hpb Hunit).
  - move=> c2 Hc2.
    destruct (Hsub2 c2 Hc2) as (c1 & Hc1 & Hcl2 & Hlo2 & Hhi2).
    destruct (Hsub1 c1 Hc1) as (c0 & Hc0 & Hcl1 & Hlo1 & Hhi1).
    exists c0. split_and!; [exact Hc0 | congruence | lia | lia].
Qed.

(** [store.repair], general splitting form (issue #28 stage D2b): the origin
    ids address arbitrary chars of their covering witness cells; repair puts
    both on run boundaries by splitting, and the item comes back linked to
    the boundary cells. The same-run premise (equal witnesses force the left
    origin strictly below the right one in clock) is what item validity
    provides: within one run, doc order is clock order, and an item's origin
    precedes its right origin. *)
Lemma wp_store__repair_split (s mref tref item_l pname : loc)
    (input : IntegrateInput (A := A)) (opn : option go_string)
    (types : gmap loc type_state) (bind : gmap P loc)
    (ocL ocR : option item_cell) (p_t : loc) :
  match in_originId input, ocL with
  | Some originId, Some c => c ∈ all_cells types ∧
      clientId (item_id (run_head c)) = clientId originId ∧
      (clock (item_id (run_head c)) <= clock originId)%nat ∧
      (clock originId < clock (item_id (run_head c)) + length (ic_run c))%nat
  | None, None => True
  | _, _ => False
  end ->
  match in_rightOriginId input, ocR with
  | Some originId, Some c => c ∈ all_cells types ∧
      clientId (item_id (run_head c)) = clientId originId ∧
      (clock (item_id (run_head c)) <= clock originId)%nat ∧
      (clock originId < clock (item_id (run_head c)) + length (ic_run c))%nat
  | None, None => True
  | _, _ => False
  end ->
  match in_originId input, in_rightOriginId input, ocL, ocR with
  | Some a, Some b, Some cL0, Some cR0 => cL0 = cR0 -> (clock a < clock b)%nat
  | _, _, _, _ => True
  end ->
  match opn with
  | Some nm => bind !! nm = Some p_t
  | None => match ocL with
            | Some c => p_t = ic_parent c
            | None => match ocR with
                      | Some c => p_t = ic_parent c
                      | None => False
                      end
            end
  end ->
  (∀ c, c ∈ all_cells types -> (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) < 2^64)%Z) ->
  NoDup (ic_loc <$> all_cells types) ->
  cells_range_disjoint (all_cells types) ->
  (∀ c, c ∈ all_cells types -> cell_origin_clk c) ->
  {{{ is_pkg_init yjs ∗
      own_linked_item_run item_l input null null null ∗
      is_parent_name pname opn ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types ∗
      (s .[(yjs.store.t), "types"]) ↦ tref ∗ own_map tref (DfracOwn 1) bind ∗
      ([∗ map] p ↦ ts ∈ types,
          own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) }}}
    s @! (go.PointerType yjs.store) @! "repair" #item_l #pname
  {{{ (lft rgt : loc) (types2 : gmap loc type_state), RET #();
      own_linked_item_run item_l input p_t lft rgt ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types2 ∗
      (s .[(yjs.store.t), "types"]) ↦ tref ∗ own_map tref (DfracOwn 1) bind ∗
      ([∗ map] p ↦ ts ∈ types2,
          own_ytype_cells p (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) ∗
      ⌜pool_invs types2⌝ ∗
      ⌜repair_types_facts types types2⌝ ∗
      ⌜match in_originId input, ocL with
       | Some originId, Some c0 => lft = ic_loc c0 ∧
           ∃ cL', cL' ∈ all_cells types2 ∧ ic_loc cL' = lft ∧
             cell_client cL' = W64 (clientId originId) ∧
             (uint.Z (cell_clock cL') + Z.of_nat (length (ic_run cL'))
              = Z.of_nat (clock originId) + 1)%Z ∧
             ic_parent cL' = ic_parent c0
       | None, None => lft = null
       | _, _ => False
       end⌝ ∗
      ⌜match in_rightOriginId input, ocR with
       | Some originId, Some c0 =>
           ∃ cR', cR' ∈ all_cells types2 ∧ ic_loc cR' = rgt ∧
             cell_client cR' = W64 (clientId originId) ∧
             (uint.Z (cell_clock cR') = Z.of_nat (clock originId))%Z ∧
             ic_parent cR' = ic_parent c0
       | None, None => rgt = null
       | _, _ => False
       end⌝ }}}.
Proof using Type*.
  move=> HwL HwR Hsame Hwpar Hfits Hnodup Hrangedisj Horiginclk.
  iIntros (Φ) "(#Hpkg & Hlinked & #HisPN & Hitemsf & Hitemmap & Htypesf & Htypesmap & Htypes) HΦ".
  iDestruct "Hlinked" as (itemVal oleft oright) "(Hraw & %Hfl & %Hfr & %Hfpar & %Hflags & %Hrunc)".
  iNamed "Hraw".
  iDestruct (types_cells_id_bounds2 with "Htypes") as %Hbnds0.
  have Hpinvs : pool_invs types by (split_and!; assumption).

  wp_method_call. wp_call. wp_call. wp_auto.
  destruct oleft as [idvL|].
  - (* left origin present: clean-end split *)
    have HinlS : input.(in_originId) = Some (toYjsId idvL) by rewrite -Hin_l //.
    rewrite HinlS in HwL. destruct ocL as [cL|]; last done.
    destruct HwL as (HcLmem & HcLcl & HcLle & HcLlt).
    iDestruct "Holeft" as "[%HnnL #HolC]".
    rewrite (bool_decide_eq_false_2 (itemVal.(yjs.item.originLeftId') = null) HnnL) /=.
    wp_auto.
    have HcLbnd := proj2 (Hbnds0 cL HcLmem).
    have HcLccw : cell_client cL = idvL.(yjs.id.clientId').
    { rewrite /cell_client. move: HcLcl. rewrite /toYjsId /=. move=> ->. word. }
    have HcLleZ : (uint.Z (cell_clock cL) <= uint.Z idvL.(yjs.id.clock'))%Z.
    { move: HcLle. rewrite /toYjsId /= /cell_clock. move=> H. word. }
    have HcLltZ : (uint.Z idvL.(yjs.id.clock') < uint.Z (cell_clock cL) + Z.of_nat (length (ic_run cL)))%Z.
    { move: HcLlt. rewrite /toYjsId /= /cell_clock. move=> H. word. }
    wp_apply (wp_store__splitAtAndGetLeft_inv s mref idvL types cL
                HcLmem HcLccw HcLleZ HcLltZ Hpinvs
                with "[$Hpkg $Hitemsf $Hitemmap $Htypes]").
    iIntros (types1) "(Hitemsf & Hitemmap & Htypes & %Hpinvs1 & %Hstep1 & %HbdL)".
    destruct HbdL as (cL1 & HcL1mem & HcL1loc & HcL1cl & HcL1end & HcL1par).
    wp_auto.
    destruct oright as [idvR|].
    + (* right origin present: relocate the witness, clean-start split *)
      have HinrS : input.(in_rightOriginId) = Some (toYjsId idvR) by rewrite -Hin_r //.
      rewrite HinrS in HwR. destruct ocR as [cR|]; last done.
      destruct HwR as (HcRmem & HcRcl & HcRle & HcRlt).
      rewrite HinlS HinrS in Hsame.
      have Hsame' : cL = cR -> (clock (toYjsId idvL) < clock (toYjsId idvR))%nat := Hsame.
      iDestruct "Horight" as "[%HnnR #HorC]".
      rewrite (bool_decide_eq_false_2 (itemVal.(yjs.item.originRightId') = null) HnnR) /=.
      wp_auto.
      have HcRbnd := proj2 (Hbnds0 cR HcRmem).
      have HcRccw : cell_client cR = idvR.(yjs.id.clientId').
      { rewrite /cell_client. move: HcRcl. rewrite /toYjsId /=. move=> ->. word. }
      have HcRleZ : (uint.Z (cell_clock cR) <= uint.Z idvR.(yjs.id.clock'))%Z.
      { move: HcRle. rewrite /toYjsId /= /cell_clock. move=> H. word. }
      have HcRltZ : (uint.Z idvR.(yjs.id.clock') < uint.Z (cell_clock cR) + Z.of_nat (length (ic_run cR)))%Z.
      { move: HcRlt. rewrite /toYjsId /= /cell_clock. move=> H. word. }
      have Hstep1' := Hstep1.
      destruct Hstep1' as (Hpres1 & Hdom1 & Hrl1 & Hstable1 & Hcover1 & Hunitp1).
      destruct (Hcover1 idvR.(yjs.id.clientId') (uint.Z idvR.(yjs.id.clock')) cR HcRmem HcRccw HcRleZ HcRltZ)
        as (cR1 & HcR1mem & HcR1cc & HcR1le & HcR1lt & HcR1parw & Hprov).
      destruct Hpinvs1 as (Hfits1 & Hnodup1 & Hrangedisj1 & Horiginclk1).
      have Hlocne : ic_loc cL1 ≠ ic_loc cR1.
      { move=> Heqloc.
        have Hceq : cL1 = cR1 := pool_loc_inj (all_cells types1) Hnodup1 _ _ HcL1mem HcR1mem Heqloc.
        have HleRL : (uint.Z idvR.(yjs.id.clock') <= uint.Z idvL.(yjs.id.clock'))%Z.
        { rewrite -Hceq in HcR1lt. clear -HcR1lt HcL1end. lia. }
        have Hfire : cL = cR -> False.
        { move=> HeqLR. have := Hsame' HeqLR. rewrite /toYjsId /=. move=> H.
          clear -H HleRL. word. }
        destruct Hprov as [Hc'c | [HcRcw _]].
        - have HlocRL : ic_loc cR = ic_loc cL.
          { rewrite -Hc'c -Hceq HcL1loc //. }
          exact (Hfire (eq_sym (pool_loc_inj (all_cells types) Hnodup _ _ HcRmem HcLmem HlocRL))).
        - exact (Hfire (eq_sym HcRcw)). }
      have Hpinvs1' : pool_invs types1 by (split_and!; assumption).
      wp_apply (wp_store__splitAtAndGetRight_inv s mref idvR types1 cR1
                  HcR1mem HcR1cc HcR1le HcR1lt Hpinvs1'
                  with "[$Hpkg $Hitemsf $Hitemmap $Htypes]").
      iIntros (rl types2) "(Hitemsf & Hitemmap & Htypes & %Hpinvs2 & %Hstep2 & %HbdR)".
      destruct HbdR as (cR2 & HcR2mem & HcR2loc & HcR2cl & HcR2clk & HcR2par).
      wp_auto.
      have Hstep2' := Hstep2.
      destruct Hstep2' as (Hpres2 & Hdom2 & Hrl2 & Hstable2 & Hcover2 & Hunitp2).
      have HcL2mem : cL1 ∈ all_cells types2 := Hstable2 cL1 HcL1mem Hlocne.
      have HparR : ic_parent cR2 = ic_parent cR by rewrite HcR2par HcR1parw //.
      destruct opn as [nm|].
      * (* Parent::String *)
        iDestruct "HisPN" as "[%HnnP #HpnC]".
        rewrite (bool_decide_eq_false_2 (pname = null) HnnP) /=.
        wp_auto.
        wp_apply (wp_store__getOrCreateYType s tref (DfracOwn 1) bind nm p_t Hwpar
                    with "[$Htypesf $Htypesmap]").
        iIntros "(Htypesf & Htypesmap)".
        wp_auto.
        iApply ("HΦ" $! (ic_loc cL) rl types2).
        iFrame "Hitemsf Hitemmap Htypesf Htypesmap Htypes".
        iSplitL "Hitem".
        { iExists _, (Some idvL), (Some idvR). rewrite /own_fresh_item_raw. simpl.
          iFrame "Hitem". iFrame "HolC HorC".
          iPureIntro. split_and!; try done. }
        iPureIntro. split_and!.
        { destruct Hpinvs2 as (?&?&?&?). split_and!; assumption. }
        { exact (split_step_facts_compose types types1 types2 cL cR1 Hstep1 Hstep2). }
        { rewrite HinlS /=. split; [done |].
          exists cL1. split_and!;
            [exact HcL2mem | rewrite HcL1loc // | | | rewrite HcL1par //].
          - rewrite HcL1cl /toYjsId /=. word.
          - move: HcL1end. rewrite /toYjsId /=. move=> H. word. }
        { rewrite HinrS /=.
          exists cR2. split_and!;
            [exact HcR2mem | exact HcR2loc | | | exact HparR].
          - rewrite HcR2cl /toYjsId /=. word.
          - move: HcR2clk. rewrite /toYjsId /=. move=> H. word. }
      * (* Parent::None: borrow from the resolved left neighbour *)
        iDestruct "HisPN" as "%HpN".
        rewrite (bool_decide_eq_true_2 (pname = null) HpN) /=.
        iDestruct (types_cell_acc_gen types2 cL1 HcL2mem with "Htypes") as "Hacc".
        iNamed "Hacc".
        iDestruct (typed_pointsto_not_null with "Hval") as %HnnCL.
        iEval (rewrite HcL1loc) in "Hval".
        wp_auto.
        rewrite (bool_decide_eq_false_2 (cL.(ic_loc) = null) ltac:(rewrite -HcL1loc; exact HnnCL)) /=.
        wp_auto.
        iEval (rewrite -HcL1loc) in "Hval".
        iDestruct ("Hback" with "Hval") as "Htypes".
        rewrite Hpar HcL1par Hwpar.
        iApply ("HΦ" $! (ic_loc cL) rl types2).
        iFrame "Hitemsf Hitemmap Htypesf Htypesmap Htypes".
        iSplitL "Hitem".
        { iExists _, (Some idvL), (Some idvR). rewrite /own_fresh_item_raw. simpl.
          iFrame "Hitem". iFrame "HolC HorC".
          iPureIntro. split_and!; try done. }
        iPureIntro. split_and!.
        { destruct Hpinvs2 as (?&?&?&?). split_and!; assumption. }
        { exact (split_step_facts_compose types types1 types2 cL cR1 Hstep1 Hstep2). }
        { rewrite HinlS /=. split; [done |].
          exists cL1. split_and!;
            [exact HcL2mem | rewrite HcL1loc // | | | rewrite HcL1par //].
          - rewrite HcL1cl /toYjsId /=. word.
          - move: HcL1end. rewrite /toYjsId /=. move=> H. word. }
        { rewrite HinrS /=.
          exists cR2. split_and!;
            [exact HcR2mem | exact HcR2loc | | | exact HparR].
          - rewrite HcR2cl /toYjsId /=. word.
          - move: HcR2clk. rewrite /toYjsId /=. move=> H. word. }
    + (* no right origin *)
      have HinrN : input.(in_rightOriginId) = None by rewrite -Hin_r //.
      rewrite HinrN in HwR. destruct ocR as [cR|]; first done.
      iDestruct "Horight" as "%HnR".
      rewrite (bool_decide_eq_true_2 (itemVal.(yjs.item.originRightId') = null) HnR) /=.
      wp_auto.
      destruct opn as [nm|].
      * (* Parent::String *)
        iDestruct "HisPN" as "[%HnnP #HpnC]".
        rewrite (bool_decide_eq_false_2 (pname = null) HnnP) /=.
        wp_auto.
        wp_apply (wp_store__getOrCreateYType s tref (DfracOwn 1) bind nm p_t Hwpar
                    with "[$Htypesf $Htypesmap]").
        iIntros "(Htypesf & Htypesmap)".
        wp_auto.
        iApply ("HΦ" $! (ic_loc cL) null types1).
        iFrame "Hitemsf Hitemmap Htypesf Htypesmap Htypes".
        iSplitL "Hitem".
        { iExists _, (Some idvL), None. rewrite /own_fresh_item_raw. simpl.
          iFrame "Hitem". iFrame "HolC".
          iPureIntro. split_and!; try done. }
        iPureIntro. split_and!.
        { destruct Hpinvs1 as (?&?&?&?). split_and!; assumption. }
        { exact (split_step_facts_single types types1 cL Hstep1). }
        { rewrite HinlS /=. split; [done |].
          exists cL1. split_and!;
            [exact HcL1mem | rewrite HcL1loc // | | | rewrite HcL1par //].
          - rewrite HcL1cl /toYjsId /=. word.
          - move: HcL1end. rewrite /toYjsId /=. move=> H. word. }
        { rewrite HinrN //. }
      * (* Parent::None: borrow from the resolved left neighbour *)
        iDestruct "HisPN" as "%HpN".
        rewrite (bool_decide_eq_true_2 (pname = null) HpN) /=.
        iDestruct (types_cell_acc_gen types1 cL1 HcL1mem with "Htypes") as "Hacc".
        iNamed "Hacc".
        iDestruct (typed_pointsto_not_null with "Hval") as %HnnCL.
        iEval (rewrite HcL1loc) in "Hval".
        wp_auto.
        rewrite (bool_decide_eq_false_2 (cL.(ic_loc) = null) ltac:(rewrite -HcL1loc; exact HnnCL)) /=.
        wp_auto.
        iEval (rewrite -HcL1loc) in "Hval".
        iDestruct ("Hback" with "Hval") as "Htypes".
        rewrite Hpar HcL1par Hwpar.
        iApply ("HΦ" $! (ic_loc cL) null types1).
        iFrame "Hitemsf Hitemmap Htypesf Htypesmap Htypes".
        iSplitL "Hitem".
        { iExists _, (Some idvL), None. rewrite /own_fresh_item_raw. simpl.
          iFrame "Hitem". iFrame "HolC".
          iPureIntro. split_and!; try done. }
        iPureIntro. split_and!.
        { destruct Hpinvs1 as (?&?&?&?). split_and!; assumption. }
        { exact (split_step_facts_single types types1 cL Hstep1). }
        { rewrite HinlS /=. split; [done |].
          exists cL1. split_and!;
            [exact HcL1mem | rewrite HcL1loc // | | | rewrite HcL1par //].
          - rewrite HcL1cl /toYjsId /=. word.
          - move: HcL1end. rewrite /toYjsId /=. move=> H. word. }
        { rewrite HinrN //. }
  - (* no left origin *)
    have HinlN : input.(in_originId) = None by rewrite -Hin_l //.
    rewrite HinlN in HwL. destruct ocL as [cL|]; first done.
    iDestruct "Holeft" as "%HnL".
    rewrite (bool_decide_eq_true_2 (itemVal.(yjs.item.originLeftId') = null) HnL) /=.
    wp_auto.
    destruct oright as [idvR|].
    + (* right origin present: clean-start split, no relocation *)
      have HinrS : input.(in_rightOriginId) = Some (toYjsId idvR) by rewrite -Hin_r //.
      rewrite HinrS in HwR. destruct ocR as [cR|]; last done.
      destruct HwR as (HcRmem & HcRcl & HcRle & HcRlt).
      iDestruct "Horight" as "[%HnnR #HorC]".
      rewrite (bool_decide_eq_false_2 (itemVal.(yjs.item.originRightId') = null) HnnR) /=.
      wp_auto.
      have HcRbnd := proj2 (Hbnds0 cR HcRmem).
      have HcRccw : cell_client cR = idvR.(yjs.id.clientId').
      { rewrite /cell_client. move: HcRcl. rewrite /toYjsId /=. move=> ->. word. }
      have HcRleZ : (uint.Z (cell_clock cR) <= uint.Z idvR.(yjs.id.clock'))%Z.
      { move: HcRle. rewrite /toYjsId /= /cell_clock. move=> H. word. }
      have HcRltZ : (uint.Z idvR.(yjs.id.clock') < uint.Z (cell_clock cR) + Z.of_nat (length (ic_run cR)))%Z.
      { move: HcRlt. rewrite /toYjsId /= /cell_clock. move=> H. word. }
      wp_apply (wp_store__splitAtAndGetRight_inv s mref idvR types cR
                  HcRmem HcRccw HcRleZ HcRltZ Hpinvs
                  with "[$Hpkg $Hitemsf $Hitemmap $Htypes]").
      iIntros (rl types2) "(Hitemsf & Hitemmap & Htypes & %Hpinvs2 & %Hstep2 & %HbdR)".
      destruct HbdR as (cR2 & HcR2mem & HcR2loc & HcR2cl & HcR2clk & HcR2par).
      wp_auto.
      destruct opn as [nm|].
      * (* Parent::String *)
        iDestruct "HisPN" as "[%HnnP #HpnC]".
        rewrite (bool_decide_eq_false_2 (pname = null) HnnP) /=.
        wp_auto.
        wp_apply (wp_store__getOrCreateYType s tref (DfracOwn 1) bind nm p_t Hwpar
                    with "[$Htypesf $Htypesmap]").
        iIntros "(Htypesf & Htypesmap)".
        wp_auto.
        iApply ("HΦ" $! null rl types2).
        iFrame "Hitemsf Hitemmap Htypesf Htypesmap Htypes".
        iSplitL "Hitem".
        { iExists _, None, (Some idvR). rewrite /own_fresh_item_raw. simpl.
          iFrame "Hitem". iFrame "HorC".
          iPureIntro. split_and!; try done. }
        iPureIntro. split_and!.
        { destruct Hpinvs2 as (?&?&?&?). split_and!; assumption. }
        { exact (split_step_facts_single types types2 cR Hstep2). }
        { rewrite HinlN //. }
        { rewrite HinrS /=.
          exists cR2. split_and!;
            [exact HcR2mem | exact HcR2loc | | | exact HcR2par].
          - rewrite HcR2cl /toYjsId /=. word.
          - move: HcR2clk. rewrite /toYjsId /=. move=> H. word. }
      * (* Parent::None: borrow from the resolved right neighbour *)
        iDestruct "HisPN" as "%HpN".
        rewrite (bool_decide_eq_true_2 (pname = null) HpN) /=.
        have Hfl' : (itemVal <| yjs.item.right' := rl |>).(yjs.item.left') = null
          by simpl; exact Hfl.
        iDestruct (types_cell_acc_gen types2 cR2 HcR2mem with "Htypes") as "Hacc".
        iNamed "Hacc".
        iDestruct (typed_pointsto_not_null with "Hval") as %HnnCR.
        iEval (rewrite HcR2loc) in "Hval".
        wp_auto.
        rewrite (bool_decide_eq_true_2 _ Hfl') /=.
        wp_auto.
        rewrite (bool_decide_eq_false_2 (rl = null) ltac:(rewrite -HcR2loc; exact HnnCR)) /=.
        wp_auto.
        iEval (rewrite -HcR2loc) in "Hval".
        iDestruct ("Hback" with "Hval") as "Htypes".
        rewrite Hpar HcR2par Hwpar.
        iApply ("HΦ" $! null rl types2).
        iFrame "Hitemsf Hitemmap Htypesf Htypesmap Htypes".
        iSplitL "Hitem".
        { iExists _, None, (Some idvR). rewrite /own_fresh_item_raw. simpl.
          iFrame "Hitem". iFrame "HorC".
          iPureIntro. split_and!; try done. }
        iPureIntro. split_and!.
        { destruct Hpinvs2 as (?&?&?&?). split_and!; assumption. }
        { exact (split_step_facts_single types types2 cR Hstep2). }
        { rewrite HinlN //. }
        { rewrite HinrS /=.
          exists cR2. split_and!;
            [exact HcR2mem | exact HcR2loc | | | exact HcR2par].
          - rewrite HcR2cl /toYjsId /=. word.
          - move: HcR2clk. rewrite /toYjsId /=. move=> H. word. }
    + (* no origins at all: Parent::None is ruled out by the premise *)
      have HinrN : input.(in_rightOriginId) = None by rewrite -Hin_r //.
      rewrite HinrN in HwR. destruct ocR as [cR|]; first done.
      iDestruct "Horight" as "%HnR".
      rewrite (bool_decide_eq_true_2 (itemVal.(yjs.item.originRightId') = null) HnR) /=.
      wp_auto.
      destruct opn as [nm|]; last done.
      iDestruct "HisPN" as "[%HnnP #HpnC]".
      rewrite (bool_decide_eq_false_2 (pname = null) HnnP) /=.
      wp_auto.
      wp_apply (wp_store__getOrCreateYType s tref (DfracOwn 1) bind nm p_t Hwpar
                  with "[$Htypesf $Htypesmap]").
      iIntros "(Htypesf & Htypesmap)".
      wp_auto.
      iApply ("HΦ" $! null null types).
      iFrame "Hitemsf Hitemmap Htypesf Htypesmap Htypes".
      iSplitL "Hitem".
      { iExists _, None, None. rewrite /own_fresh_item_raw. simpl.
        iFrame "Hitem".
        iPureIntro. split_and!; try done. }
      iPureIntro. split_and!.
      { split_and!; assumption. }
      { exact (repair_types_facts_refl types). }
      { rewrite HinlN //. }
      { rewrite HinrN //. }
Qed.

(* ===== applyUpdate (doc-level, #49) ====================================== *)

(** Both origin indices of a successful [integrate], off its bind chain. *)
Lemma integrate_finds (input : IntegrateInput (A := A)) (arr arr2 : list (YjsItem A)) :
  integrate input arr = Some arr2 ->
  ∃ leftIdx rightIdx, findLeftIdx (in_originId input) arr = Some leftIdx /\
                      findRightIdx (in_rightOriginId input) arr = Some rightIdx.
Proof.
  rewrite /integrate.
  move=> /bind_Some [leftIdx [HfindLeft Hr1]].
  move: Hr1 => /bind_Some [rightIdx [HfindRight Hr2]].
  by exists leftIdx, rightIdx.
Qed.

(** A present origin's [find*Idx] hit names the origin item's exact index. *)
Lemma findLeftIdx_inv (originId : YjsId) (arr : list (YjsItem A)) (k : Z) :
  findLeftIdx (Some originId) arr = Some k ->
  ∃ (kn : nat) (it : YjsItem A), k = Z.of_nat kn /\ arr !! kn = Some it /\ item_id it = originId.
Proof.
  rewrite /findLeftIdx.
  destruct (list_find (fun item => item_id item = originId) arr) as [[kn it]|] eqn:Hf; last done.
  simpl. move=> [= <-]. apply list_find_Some in Hf. destruct Hf as (Hlk & Hidf & _).
  by exists kn, it.
Qed.

Lemma findRightIdx_inv (originId : YjsId) (arr : list (YjsItem A)) (k : Z) :
  findRightIdx (Some originId) arr = Some k ->
  ∃ (kn : nat) (it : YjsItem A), k = Z.of_nat kn /\ arr !! kn = Some it /\ item_id it = originId.
Proof.
  rewrite /findRightIdx.
  destruct (list_find (fun item => item_id item = originId) arr) as [[kn it]|] eqn:Hf; last done.
  simpl. move=> [= <-]. apply list_find_Some in Hf. destruct Hf as (Hlk & Hidf & _).
  by exists kn, it.
Qed.

(** ---- boundary-cell / cursor bridges (issue #28 U2): locating a flattened
    char inside its cell, and the id arithmetic along a well-formed run.
    These replace the unit-scaffold identifications (cell index = model
    index) once runs can be longer than one char. ---- *)

(** The id of the [o]-th char of a chained run: same client, head clock + o. *)
Lemma run_wf_char_id (r : list (YjsItem A)) (o : nat) (x : YjsItem A) :
  run_wf r -> r !! o = Some x ->
  item_id x = MkYjsId (clientId (item_id (hd inhabitant r)))
                      (clock (item_id (hd inhabitant r)) + o).
Proof.
  move=> [Hne Hstep].
  elim: o x => [| o IH] x Hx.
  - destruct r as [| h t]; first done.
    move: Hx => /= [= <-]. rewrite Nat.add_0_r. by destruct (item_id h).
  - have Hprev : is_Some (r !! o).
    { apply lookup_lt_is_Some. apply lookup_lt_Some in Hx. lia. }
    destruct Hprev as [y Hy].
    have [Hid _] := Hstep o y x Hy Hx.
    rewrite Hid (IH y Hy) /=. f_equal. lia.
Qed.

(** The char of a chained run carrying a covered id: at offset
    clock originId - head clock. *)
Lemma run_wf_char_at_clock (r : list (YjsItem A)) (originId : YjsId) :
  run_wf r ->
  clientId (item_id (hd inhabitant r)) = clientId originId ->
  (clock (item_id (hd inhabitant r)) <= clock originId)%nat ->
  (clock originId < clock (item_id (hd inhabitant r)) + length r)%nat ->
  ∃ ch, r !! (clock originId - clock (item_id (hd inhabitant r)))%nat = Some ch ∧
        item_id ch = originId.
Proof.
  move=> Hwf Hcl Hle Hlt.
  have Hlt3 : ((clock originId - clock (item_id (hd inhabitant r))) < length r)%nat by lia.
  destruct (lookup_lt_is_Some_2 _ _ Hlt3) as [ch Hch].
  exists ch. split; [exact Hch |].
  rewrite (run_wf_char_id _ _ _ Hwf Hch).
  destruct originId as [oc ok]. simpl in *.
  f_equal; [exact Hcl | lia].
Qed.

(** A flattened index decomposes into (containing cell, offset, prefix sum). *)
Lemma run_flatten_lookup_cell (cells : list item_cell) (kn : nat) (it : YjsItem A) :
  run_flatten cells !! kn = Some it ->
  ∃ (ci off : nat) (c : item_cell), cells !! ci = Some c ∧ ic_run c !! off = Some it ∧
    kn = (length (run_flatten (take ci cells)) + off)%nat.
Proof.
  elim: cells kn => [| c0 cs IH] kn.
  { rewrite /run_flatten /= lookup_nil //. }
  rewrite run_flatten_cons => /lookup_app_Some [Hin | [Hge Hlk]].
  - exists 0%nat, kn, c0. split_and!; [done | done | rewrite take_0 /run_flatten //=].
  - destruct (IH _ Hlk) as (ci & off & c & Hci & Hoff & Hkn).
    exists (S ci), off, c. split_and!; [done | done |].
    rewrite /= run_flatten_cons length_app. lia.
Qed.

(** Converse: the [off]-th char of cell [ci] sits at prefix-sum + [off]. *)
Lemma run_flatten_lookup_of_cell (cells : list item_cell) (ci off : nat)
    (c : item_cell) (it : YjsItem A) :
  cells !! ci = Some c -> ic_run c !! off = Some it ->
  run_flatten cells !! (length (run_flatten (take ci cells)) + off)%nat = Some it.
Proof.
  move=> Hci Hoff.
  have Hsplit := take_drop_middle cells ci c Hci.
  have Hdec : run_flatten cells
            = run_flatten (take ci cells) ++ ic_run c ++ run_flatten (drop (S ci) cells).
  { transitivity (run_flatten (take ci cells ++ c :: drop (S ci) cells)).
    - by rewrite Hsplit.
    - by rewrite run_flatten_app run_flatten_cons. }
  rewrite Hdec lookup_app_r; last lia.
  replace (length (run_flatten (take ci cells)) + off -
           length (run_flatten (take ci cells)))%nat with off by lia.
  rewrite lookup_app_l; [exact Hoff | by apply lookup_lt_Some in Hoff].
Qed.

(** Under [uniqueId] the flattened position of a char is unique: any index
    holding the [off]-th char of cell [ci] IS prefix-sum + [off]. *)
Lemma uniqueId_flatten_char_index (cells : list item_cell)
    (ci off : nat) (c : item_cell) (x : YjsItem A) (kn : nat) :
  uniqueId (run_flatten cells) ->
  cells !! ci = Some c -> ic_run c !! off = Some x ->
  run_flatten cells !! kn = Some x ->
  kn = (length (run_flatten (take ci cells)) + off)%nat.
Proof.
  move=> Huniq Hci Hoff Hkn.
  have Hpos := run_flatten_lookup_of_cell cells ci off c x Hci Hoff.
  set pos := (length (run_flatten (take ci cells)) + off)%nat in Hpos |- *.
  destruct (Nat.lt_trichotomy kn pos) as [Hlt | [Heq | Hgt]]; [| exact Heq |].
  - exact (False_ind _ (uniqueId_lookup_ne _ kn pos x x Huniq Hkn Hpos Hlt eq_refl)).
  - exact (False_ind _ (uniqueId_lookup_ne _ pos kn x x Huniq Hpos Hkn Hgt eq_refl)).
Qed.

(** Every cell of a DLL segment carries a well-formed run (pure extraction;
    the run-aware counterpart of the unit scaffold's per-cell length pin). *)
Lemma own_dll_runs_wf (dq : dfrac) (l last prev next : loc) (cells : list item_cell) :
  own_dll dq l last prev next cells -∗
  ⌜∀ c, c ∈ cells → run_wf (ic_run c)⌝.
Proof.
  iInduction cells as [|c0 cells] "IH" forall (l prev).
  - iIntros "_". iPureIntro. move=> c Hc. rewrite elem_of_nil in Hc. done.
  - iIntros "H". iNamed "H".
    iDestruct ("IH" with "Hrest") as %Hrest.
    iPureIntro. move=> c Hc.
    apply elem_of_cons in Hc as [-> | Hc]; last exact (Hrest c Hc).
    exact Hrun.
Qed.

(** Pure extractions read off the types big-sep: pool-wide run
    well-formedness, parent discipline, the per-entry document invariant,
    and the cells/model isomorphism. *)
Lemma types_runs_wf2 (types : gmap loc type_state) :
  ([∗ map] parent ↦ ts ∈ types,
      own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
      ⌜YjsArrInvariant (ty_arr ts)⌝) -∗
  ⌜∀ c, c ∈ all_cells types → run_wf (ic_run c)⌝.
Proof.
  iIntros "Htypes".
  iAssert ([∗ map] p ↦ ts ∈ types, ⌜∀ c, c ∈ ty_cells ts → run_wf (ic_run c)⌝)%I
    with "[Htypes]" as "H".
  { iApply (big_sepM_impl with "Htypes").
    iIntros "!#" (p ts Hp) "(Hyt & _)".
    iDestruct "Hyt" as (yt tl) "(Hp' & Hdll & %Hlen & %Hrepr & %Hcpar)".
    iApply (own_dll_runs_wf with "Hdll"). }
  iDestruct (big_sepM_pure with "H") as %Hall.
  iPureIntro. move=> c Hc.
  apply all_cells_elem_of in Hc. destruct Hc as (p & ts & Hp & Hcts).
  exact (Hall p ts Hp c Hcts).
Qed.

Lemma types_parents_all2 (types : gmap loc type_state) :
  ([∗ map] parent ↦ ts ∈ types,
      own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
      ⌜YjsArrInvariant (ty_arr ts)⌝) -∗
  ⌜∀ p ts c, types !! p = Some ts → c ∈ ty_cells ts → ic_parent c = p⌝.
Proof.
  iIntros "Htypes".
  iAssert ([∗ map] p ↦ ts ∈ types, ⌜∀ c, c ∈ ty_cells ts → ic_parent c = p⌝)%I
    with "[Htypes]" as "H".
  { iApply (big_sepM_impl with "Htypes").
    iIntros "!#" (p ts Hp) "(Hyt & _)".
    iDestruct "Hyt" as (yt tl) "(Hp' & Hdll & %Hlen & %Hrepr & %Hcpar)".
    by iPureIntro. }
  iDestruct (big_sepM_pure with "H") as %Hall.
  iPureIntro. move=> p ts c Hp Hc. exact (Hall p ts Hp c Hc).
Qed.

Lemma types_arr_inv2 (types : gmap loc type_state) :
  ([∗ map] parent ↦ ts ∈ types,
      own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
      ⌜YjsArrInvariant (ty_arr ts)⌝) -∗
  ⌜∀ p ts, types !! p = Some ts -> YjsArrInvariant (ty_arr ts)⌝.
Proof.
  iIntros "Htypes".
  iAssert ([∗ map] p ↦ ts ∈ types, ⌜YjsArrInvariant (ty_arr ts)⌝)%I
    with "[Htypes]" as "H".
  { iApply (big_sepM_impl with "Htypes").
    iIntros "!#" (p ts Hp) "(_ & %Hi)". by iPureIntro. }
  iDestruct (big_sepM_pure with "H") as %Hall.
  iPureIntro. move=> p ts Hp. exact (Hall p ts Hp).
Qed.

Lemma types_repr_all2 (types : gmap loc type_state) :
  ([∗ map] parent ↦ ts ∈ types,
      own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
      ⌜YjsArrInvariant (ty_arr ts)⌝) -∗
  ⌜∀ p ts, types !! p = Some ts -> cells_repr (ty_arr ts) (ty_cells ts) (ty_arr ts)⌝.
Proof.
  iIntros "Htypes".
  iAssert ([∗ map] p ↦ ts ∈ types,
      ⌜cells_repr (ty_arr ts) (ty_cells ts) (ty_arr ts)⌝)%I
    with "[Htypes]" as "H".
  { iApply (big_sepM_impl with "Htypes").
    iIntros "!#" (p ts Hp) "(Hyt & _)".
    iDestruct "Hyt" as (yt tl) "(Hp' & Hdll & %Hlen & %Hrepr & %Hcpar)".
    by iPureIntro. }
  iDestruct (big_sepM_pure with "H") as %Hall.
  iPureIntro. move=> p ts Hp. exact (Hall p ts Hp).
Qed.

Lemma types_entry_pures2 (types : gmap loc type_state) (p : loc) (ts : type_state) :
  types !! p = Some ts ->
  ([∗ map] parent ↦ ts0 ∈ types,
      own_ytype_cells parent (DfracOwn 1) (ty_cells ts0) (ty_arr ts0) ∗
      ⌜YjsArrInvariant (ty_arr ts0)⌝) -∗
  ⌜cells_repr (ty_arr ts) (ty_cells ts) (ty_arr ts) ∧
   (∀ c, c ∈ ty_cells ts -> ic_parent c = p)⌝.
Proof.
  move=> Hp. iIntros "Htypes".
  iDestruct (big_sepM_lookup_acc _ _ p ts Hp with "Htypes") as "[(Hyt & _) _]".
  iDestruct "Hyt" as (yt tl) "(Hp' & Hdll & %Hlen & %Hrepr & %Hcpar)".
  iPureIntro. split; [exact Hrepr | exact Hcpar].
Qed.
(** [store_inv] is exactly [own_store] with the model existentially closed.
    The forward direction restates the per-client counter clause at the
    model; the backward direction re-derives the [types]-level and the W64
    cell-level counter bounds from the model-level one, via the registry
    coherence and the DLL id-bound pins. A lock-holding caller uses this to
    trade the lock body for [own_store] (feeding a store-state spec such as
    [wp_store__applyUpdate_certs]) and back. The pending buffer (issue #40) is
    threaded through unchanged. *)
Lemma store_inv_own_store (s_loc : loc) (γs : store_names) (γh : history_names) :
  store_inv s_loc γs γh ⊣⊢
  ∃ (c : ClientId) (h : list Ev) (m : DocModel)
    (pend : list (TId * IntegrateInput (A := A))),
    own_store s_loc γs γh c h m pend.
Proof.
  iSplit.
  - iIntros "H". iNamed "H". iNamed "Hexcl". iNamed "Hro".
    iExists (uint.nat client), h, m, pend.
    iExists client, k, items_mref, types_mref, dset, pend_sl, types, bind.
    iFrame "∗#".
    iPureIntro. split_and!.
    + reflexivity.
    + exact Hpendbnd.
    + rewrite /doc_registry_coh. split_and!; assumption.
    + exact Hhcoh.
    + (* the model-level counter from the [types]-level one *)
      move=> t x Hx Hcx.
      have Hne : doc_model_get m t ≠ [].
      { move=> Heq. move: Hx. rewrite Heq elem_of_nil. done. }
      destruct (Hmdom t Hne) as (nm & p & -> & Hbnm).
      destruct (Hbindtypes nm p Hbnm) as [ts Hts].
      have Hdg : doc_model_get m (RootId nm) = ty_arr ts := Hmtypes nm p ts Hbnm Hts.
      rewrite Hdg in Hx.
      exact (Hctr p ts x Hts Hx Hcx).
    + exact Hlocdup.
    + exact Hrangedisj.
    + exact Hrunfits.
    + exact Horiginclk.
  - iIntros "H". iDestruct "H" as (c h m pend) "H". iNamed "H". subst c.
    iDestruct (types_repr_all2 with "Htypes") as %Hreprall.
    iDestruct (types_cells_id_bounds2 with "Htypes") as %Hcellbnd.
    destruct Hregcoh as (Hbindtypes & Hbindinj & Htypesbound & Hmtypes & Hmdom).
    (* the [types]-level counter from the model-level one *)
    have Hctrt : ∀ parent ts x, types !! parent = Some ts -> x ∈ ty_arr ts ->
        clientId (item_id x) = uint.nat client -> (clock (item_id x) < uint.nat k)%nat.
    { move=> parent ts x Hts Hx Hcx.
      destruct (Htypesbound parent (ex_intro _ ts Hts)) as [nm Hbnm].
      have Hdg : doc_model_get m (RootId nm) = ty_arr ts := Hmtypes nm parent ts Hbnm Hts.
      apply (Hctr (RootId nm) x); [by rewrite Hdg | exact Hcx]. }
    (* the W64 cell-level shadow, via the id-bound pins *)
    iDestruct (types_runs_wf2 with "Htypes") as %Hrunwfall0.
    have Hcellctr : ∀ c0, c0 ∈ all_cells types -> cell_client c0 = client ->
        (uint.Z (cell_clock c0) + Z.of_nat (length (ic_run c0)) <= uint.Z k)%Z.
    { move=> c0 Hc0 Hcc.
      have Hc0m := Hc0. apply all_cells_elem_of in Hc0m.
      destruct Hc0m as (p & ts & Hts & Hcts).
      have Hwf : run_wf (ic_run c0) := Hrunwfall0 c0 Hc0.
      have Hlen1 : (1 <= length (ic_run c0))%nat.
      { destruct (ic_run c0) eqn:Hrc; [exact (False_ind _ (proj1 Hwf eq_refl)) | simpl; lia]. }
      destruct (lookup_lt_is_Some_2 (ic_run c0) (length (ic_run c0) - 1)%nat ltac:(lia)) as [xl Hxl].
      have Hxlid := run_wf_char_id _ _ _ Hwf Hxl.
      apply list_elem_of_lookup_1 in Hcts as [ci Hci].
      have Hxlmem : xl ∈ ty_arr ts.
      { rewrite (Hreprall p ts Hts).
        apply (list_elem_of_lookup_2 _
                 (length (run_flatten (take ci (ty_cells ts))) + (length (ic_run c0) - 1))%nat).
        exact (run_flatten_lookup_of_cell (ty_cells ts) ci _ c0 xl Hci Hxl). }
      have [Hcb Hkb] := Hcellbnd c0 Hc0.
      have Hceq : clientId (item_id xl) = uint.nat client.
      { move: Hcc. rewrite /cell_client /run_head. move=> Hcc.
        have Hz : uint.Z (W64 (clientId (item_id (hd inhabitant (ic_run c0))))) = uint.Z client
          by rewrite Hcc.
        have Hcb' : (Z.of_nat (clientId (item_id (hd inhabitant (ic_run c0)))) < 2^64)%Z := Hcb.
        have Hcl2 : clientId (item_id (hd inhabitant (ic_run c0))) = uint.nat client.
        { clear -Hz Hcb'. word. }
        rewrite Hxlid. exact Hcl2. }
      have Hlt := Hctrt p ts xl Hts Hxlmem Hceq.
      rewrite Hxlid in Hlt.
      have Hlt2 : (clock (item_id (hd inhabitant (ic_run c0))) + (length (ic_run c0) - 1)
                   < uint.nat k)%nat := Hlt.
      rewrite /run_head in Hkb.
      have Hlt3 : (clock (item_id (hd inhabitant (ic_run c0))) + length (ic_run c0)
                   <= uint.nat k)%nat.
      { clear -Hlt2 Hlen1. lia. }
      rewrite /cell_clock /run_head. clear -Hlt3 Hkb. word. }
    iExists client, k, items_mref, types_mref, dset, pend_sl, types, bind, h, m, pend.
    iSplitR "Hseq Htypes"; last by iFrame "Hseq Htypes".
    iFrame "Hclient Hclock Hitemsf Hitemmap Htypesf Htypesmap Hdset Hpendf Hpend Hpendcert Hpendroot HtypesAuth Hbinds Hhist".
    iPureIntro. split_and!;
      [exact Hpendbnd | exact Hctrt | exact Hcellctr | exact Hlocdup | exact Hrangedisj
      | exact Hrunfits | exact Horiginclk | exact Hbindtypes | exact Hbindinj
      | exact Htypesbound | exact Hhcoh | exact Hmtypes | exact Hmdom].
Qed.

(* ===== #40 gate toolkit (getNodeIndex/GetNode covering-total, hasNode) =====
   The pending gate probes ids that may address ANY char of a run cell (a
   mid-run origin) and that may be absent, so the total form returns a found
   bool over the COVERING relation (issue #40 x issue #28 U7c): [ok] iff some
   run cell's clock range [cell_clock, cell_clock + len) covers [clk]. Index-
   wise range-disjointness of the run ([Hidisj], from the pool's
   [cells_range_disjoint] + loc-NoDup at the call site) makes the covering cell
   unique so the binary search corners it; the empty-window exit certifies that
   no run cell covers [clk]. *)
Lemma wp_getNodeIndex_total (sl : slice.t) (dq : dfrac) (types : gmap loc type_state)
    (run : list item_cell) (clk : w64) :
  StronglySorted cell_le run ->
  (∀ c, c ∈ run -> c ∈ all_cells types) ->
  (∀ c, c ∈ run -> (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) < 2^64)%Z) ->
  (∀ (k1 k2 : nat) (c1 c2 : item_cell),
     run !! k1 = Some c1 -> run !! k2 = Some c2 -> k1 ≠ k2 ->
     (uint.Z (cell_clock c1) + Z.of_nat (length (ic_run c1)) <= uint.Z (cell_clock c2))%Z ∨
     (uint.Z (cell_clock c2) + Z.of_nat (length (ic_run c2)) <= uint.Z (cell_clock c1))%Z) ->
  {{{ is_pkg_init yjs ∗ sl ↦*{dq} (ic_loc <$> run) ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) }}}
    @! yjs.getNodeIndex #sl #clk
  {{{ (i : w64) (ok : bool), RET (#i, #ok);
      sl ↦*{dq} (ic_loc <$> run) ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) ∗
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
    "Htypes" ∷ ([∗ map] parent ↦ ts ∈ types,
        own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
        ⌜YjsArrInvariant (ty_arr ts)⌝) ∗
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
    iDestruct (types_cell_acc_gen types cmid Hcmemall with "Htypes") as "Hacc".
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

(** [cell_covers c d]: the model id [d] addresses a char of cell [c]'s run
    (issue #28 U7c): same client as the run head, and clock inside the run's
    range [head clock, head clock + run length). The per-char [run_wf] id law
    ([run_wf_char_id]) makes this exactly "[d] is the id of some [ic_run c]
    char". Replaces the all-singleton head-only [item_id (run_head c) = d]. *)
Definition cell_covers (c : item_cell) (d : YjsId) : Prop :=
  clientId (item_id (run_head c)) = clientId d ∧
  (clock (item_id (run_head c)) <= clock d)%nat ∧
  (clock d < clock (item_id (run_head c)) + length (ic_run c))%nat.

(** [store.GetNode], covering-TOTAL (issue #40 x issue #28 U7c): the pending
    gate probes ids that may address ANY char of a run cell and that may be
    absent, so both miss paths (unknown client, clock not covered by any run)
    are live. [ok = true] pins the returned loc to a store cell whose run
    covers the probed id; [ok = false] certifies no store cell's run covers it.
    Range-disjointness + loc-NoDup make the covering cell unique. *)
Lemma wp_store__GetNode_total (s mref : loc) (dq : dfrac) (idv : yjs.id.t)
    (types : gmap loc type_state) :
  (∀ c, c ∈ all_cells types -> (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) < 2^64)%Z) ->
  NoDup (ic_loc <$> all_cells types) ->
  cells_range_disjoint (all_cells types) ->
  {{{ is_pkg_init yjs ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref dq types ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) }}}
    s @! (go.PointerType yjs.store) @! "GetNode" #idv
  {{{ (l : loc) (ok : bool), RET (#l, #ok);
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref dq types ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) ∗
      ⌜if ok
       then ∃ c, c ∈ all_cells types ∧ cell_client c = idv.(yjs.id.clientId') ∧
                 (uint.Z (cell_clock c) <= uint.Z idv.(yjs.id.clock'))%Z ∧
                 (uint.Z idv.(yjs.id.clock') < uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)))%Z ∧
                 ic_loc c = l
       else ∀ c, c ∈ all_cells types -> cell_client c = idv.(yjs.id.clientId') ->
                 (uint.Z (cell_clock c) <= uint.Z idv.(yjs.id.clock'))%Z ->
                 (uint.Z idv.(yjs.id.clock') < uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)))%Z -> False⌝ }}}.
Proof using Type*.
  move=> Hrunfits Hnodup Hrangedisj.
  iIntros (Φ) "(#Hpkg & Hitemsf & Hitemmap & Htypes) HΦ".
  set (kc := idv.(yjs.id.clientId')).
  iNamed "Hitemmap".
  wp_method_call. wp_call. wp_call. wp_auto.
  wp_apply (wp_map_lookup2 with "Hmap"). iIntros "Hmap".
  destruct (gm !! kc) as [slk |] eqn:Hslk; rewrite Hslk /=.
  - (* known client: run the binary search *)
    wp_auto.
    iDestruct (big_sepM_lookup_acc _ _ kc slk Hslk with "Hruns") as "[Hrun Hrunsback]".
    iNamed "Hrun".
    (* index-wise clock-range disjointness of the client's run *)
    have Hrunfits' : ∀ c, c ∈ client_run types kc ->
        (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) < 2^64)%Z.
    { move=> c Hc. exact (Hrunfits c (proj1 (proj1 (client_run_mem types kc c) Hc))). }
    have HndAll : NoDup (all_cells types) := NoDup_fmap_1 ic_loc _ Hnodup.
    have Hndrun : NoDup (client_run types kc).
    { rewrite /client_run (merge_sort_Permutation cell_le _). apply NoDup_filter. exact HndAll. }
    have Hinj : ∀ x y, x ∈ client_run types kc → y ∈ client_run types kc → ic_loc x = ic_loc y → x = y.
    { move=> x y Hx Hy Hxy.
      have Hxa : x ∈ all_cells types := proj1 (proj1 (client_run_mem types kc x) Hx).
      have Hya : y ∈ all_cells types := proj1 (proj1 (client_run_mem types kc y) Hy).
      apply list_elem_of_lookup_1 in Hxa as [ix Hix]. apply list_elem_of_lookup_1 in Hya as [iy Hiy].
      have Hlix : (ic_loc <$> all_cells types) !! ix = Some (ic_loc y) by (rewrite list_lookup_fmap Hix /= Hxy //).
      have Hliy : (ic_loc <$> all_cells types) !! iy = Some (ic_loc y) by (rewrite list_lookup_fmap Hiy //).
      have Hijeq : ix = iy := NoDup_lookup _ _ _ _ Hnodup Hlix Hliy.
      congruence. }
    have Hidisj : ∀ (k1 k2 : nat) (c1 c2 : item_cell),
        client_run types kc !! k1 = Some c1 -> client_run types kc !! k2 = Some c2 -> k1 ≠ k2 ->
        (uint.Z (cell_clock c1) + Z.of_nat (length (ic_run c1)) <= uint.Z (cell_clock c2))%Z ∨
        (uint.Z (cell_clock c2) + Z.of_nat (length (ic_run c2)) <= uint.Z (cell_clock c1))%Z.
    { move=> k1 k2 c1 c2 Hk1 Hk2 Hkne.
      have Hc1r : c1 ∈ client_run types kc := list_elem_of_lookup_2 _ _ _ Hk1.
      have Hc2r : c2 ∈ client_run types kc := list_elem_of_lookup_2 _ _ _ Hk2.
      have Hlocne : ic_loc c1 ≠ ic_loc c2.
      { move=> Heq. have Hceq : c1 = c2 := Hinj c1 c2 Hc1r Hc2r Heq.
        rewrite Hceq in Hk1. exact (Hkne (NoDup_lookup _ _ _ _ Hndrun Hk1 Hk2)). }
      apply (Hrangedisj c1 c2
               (proj1 (proj1 (client_run_mem types kc c1) Hc1r))
               (proj1 (proj1 (client_run_mem types kc c2) Hc2r)));
        [| exact Hlocne].
      rewrite (proj2 (proj1 (client_run_mem types kc c1) Hc1r))
              (proj2 (proj1 (client_run_mem types kc c2) Hc2r)) //. }
    wp_apply (wp_getNodeIndex_total slk dq types (client_run types kc) idv.(yjs.id.clock')
                (client_run_sorted types kc)
                (fun c Hc => proj1 (proj1 (client_run_mem types kc c) Hc))
                Hrunfits' Hidisj
                with "[$Hslice $Htypes]").
    iIntros (i ok) "(Hslice & Htypes & %Hires)".
    destruct ok.
    + (* hit: the probe covers the id *)
      destruct Hires as (cres & Hcres & Hcresle & Hcreslt).
      wp_auto.
      iDestruct (own_slice_len with "Hslice") as %[Hsllen Hsllen0].
      rewrite length_fmap in Hsllen Hsllen0.
      have Hilt : (uint.nat i < length (client_run types kc))%nat
        by (apply lookup_lt_Some in Hcres; lia).
      rewrite decide_True; last word.
      have Hlocres : (ic_loc <$> client_run types kc) !! uint.nat i = Some cres.(ic_loc)
        by rewrite list_lookup_fmap Hcres //.
      iDestruct (own_slice_elem_acc (sint.Z i) (ic_loc cres) slk dq (ic_loc <$> client_run types kc) with "Hslice") as "[Hel Hgive]".
      { word. }
      { replace (Z.to_nat (sint.Z i)) with (uint.nat i) by word. exact Hlocres. }
      wp_auto.
      iDestruct ("Hgive" $! cres.(ic_loc) with "Hel") as "Hslice".
      have Hinsid : (<[sint.nat i := cres.(ic_loc)]> (ic_loc <$> client_run types kc)) = (ic_loc <$> client_run types kc).
      { apply list_insert_id. replace (sint.nat i) with (uint.nat i) by word. exact Hlocres. }
      iEval (rewrite Hinsid) in "Hslice".
      have Hcresmem : cres ∈ all_cells types /\ cell_client cres = kc.
      { apply client_run_mem. exact (list_elem_of_lookup_2 _ _ _ Hcres). }
      iApply ("HΦ" $! (ic_loc cres) true).
      iFrame "Hitemsf".
      iDestruct ("Hrunsback" with "[$Hslice $Hcap]") as "Hruns".
      iSplitL "Hmap Hruns".
      { iExists gm. iFrame "Hmap Hruns". iPureIntro. split; [exact Hcomplete | exact Hclkloc]. }
      iFrame "Htypes".
      iPureIntro. exists cres.
      split_and!; [exact (proj1 Hcresmem) | exact (proj2 Hcresmem) | exact Hcresle | exact Hcreslt | done].
    + (* clock miss within a known client: no run of this client covers the id *)
      wp_auto.
      iApply ("HΦ" $! null false).
      iFrame "Hitemsf".
      iDestruct ("Hrunsback" with "[$Hslice $Hcap]") as "Hruns".
      iSplitL "Hmap Hruns".
      { iExists gm. iFrame "Hmap Hruns". iPureIntro. split; [exact Hcomplete | exact Hclkloc]. }
      iFrame "Htypes".
      iPureIntro. move=> c Hc Hcc Hcov1 Hcov2.
      have Hcrun : c ∈ client_run types kc by (apply client_run_mem; split; [exact Hc | exact Hcc]).
      apply list_elem_of_lookup_1 in Hcrun. destruct Hcrun as [kx Hkx].
      exact (Hires kx c Hkx Hcov1 Hcov2).
  - (* unknown client: no cell of this author at all *)
    wp_auto.
    iApply ("HΦ" $! null false).
    iFrame "Hitemsf".
    iSplitL "Hmap Hruns".
    { iExists gm. iFrame "Hmap Hruns". iPureIntro. split; [exact Hcomplete | exact Hclkloc]. }
    iFrame "Htypes".
    iPureIntro. move=> c Hc Hcc Hcov1 Hcov2.
    have Hkcin : kc ∈ (cell_client <$> all_cells types).
    { rewrite -Hcc. apply list_elem_of_fmap_2. exact Hc. }
    destruct (Hcomplete kc Hkcin) as [slk Hslk'].
    rewrite Hslk in Hslk'. discriminate.
Qed.

(** [store.hasNode] (issue #40 x issue #28 U7c): the arrival test the pending
    gate runs. Its result IS the model presence [doc_model_has m (toYjsId idv)]: the
    covering GetNode (W64 clock range) is bridged to the model per-char
    covering ([cell_covers], nat) through the cell id-bounds, then to
    [doc_model_has] through the store's model/cell agreement ([Hagree]). *)
Lemma wp_store__hasNode (s mref : loc) (dq : dfrac) (idv : yjs.id.t)
    (m : DocModel) (types : gmap loc type_state) :
  (∀ d : YjsId, doc_model_has m d = true <-> ∃ c, c ∈ all_cells types ∧ cell_covers c d) ->
  (∀ c, c ∈ all_cells types -> (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) < 2^64)%Z) ->
  NoDup (ic_loc <$> all_cells types) ->
  cells_range_disjoint (all_cells types) ->
  {{{ is_pkg_init yjs ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref dq types ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) }}}
    s @! (go.PointerType yjs.store) @! "hasNode" #idv
  {{{ (ok : bool), RET #ok;
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref dq types ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) ∗
      ⌜ok = true <-> doc_model_has m (toYjsId idv) = true⌝ }}}.
Proof using Type*.
  move=> Hagree Hrunfits Hnodup Hrangedisj.
  iIntros (Φ) "(#Hpkg & Hitemsf & Hitemmap & Htypes) HΦ".
  iDestruct (types_cells_id_bounds2 with "Htypes") as %Hcellbnd.
  (* the per-cell W64 <-> nat covering bridge *)
  have Hbridge : ∀ c, c ∈ all_cells types ->
      ((cell_client c = idv.(yjs.id.clientId') ∧
        (uint.Z (cell_clock c) <= uint.Z idv.(yjs.id.clock'))%Z ∧
        (uint.Z idv.(yjs.id.clock') < uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)))%Z)
       <-> cell_covers c (toYjsId idv)).
  { move=> c Hc. have [Hcb1 Hcb2] := Hcellbnd c Hc.
    rewrite /cell_covers /cell_client /cell_clock /toYjsId /=. split.
    - move=> [Ha [Hb Hd]]. split_and!.
      + have Hz : uint.Z (W64 (clientId (item_id (run_head c)))) = uint.Z idv.(yjs.id.clientId')
          by rewrite Ha. word.
      + word.
      + word.
    - move=> [Ha [Hb Hd]]. split_and!.
      + apply word.unsigned_inj. word.
      + word.
      + word. }
  wp_method_call. wp_call. wp_call. wp_auto.
  wp_apply (wp_store__GetNode_total s mref dq idv types Hrunfits Hnodup Hrangedisj
              with "[$Hitemsf $Hitemmap $Htypes]").
  iIntros (l ok) "(Hitemsf & Hitemmap & Htypes & %Hres)".
  wp_auto.
  iApply ("HΦ" $! ok).
  iFrame "Hitemsf Hitemmap Htypes".
  iPureIntro. destruct ok.
  - split; [move=> _ | done].
    destruct Hres as (c & Hc & Hcc & Hle & Hlt & _).
    apply Hagree. exists c. split; [exact Hc |].
    apply (proj1 (Hbridge c Hc)). done.
  - split; [done | move=> Hdh].
    exfalso. apply Hagree in Hdh. destruct Hdh as (c & Hc & Hcov).
    have [Hcc [Hle Hlt]] := proj2 (Hbridge c Hc) Hcov.
    exact (Hres c Hc Hcc Hle Hlt).
Qed.

(** [store.splitAtAndGetLeft] / [store.splitAtAndGetRight], unit fast path
    (issue #28 M2): with every run 1-char (the M1 all-singleton invariant) the
    found node already ends (resp. starts) at the requested id — the offset is
    0 and [Len() - 1] is 0 — so the split branch is dead and each helper
    coincides with [GetNode]. The general (actually splitting) specs arrive
    with the run-integrate milestone (M4), where runs become reachable. *)

(* ===== #40 pending stack (issue #40) ===== *)
Lemma own_update_id_bounds (sl : slice.t) (dq : dfrac)
    (inputs : list (TId * IntegrateInput (A := A))) :
  own_update_structs sl dq inputs -∗
  ⌜∀ (i : nat) (typedInput : TId * IntegrateInput (A := A)), inputs !! i = Some typedInput →
     (Z.of_nat (clientId (in_id typedInput.2)) < 2^64)%Z ∧
     (Z.of_nat (clock (in_id typedInput.2)) < 2^64)%Z⌝.
Proof.
  iIntros "Hupd". iDestruct "Hupd" as (uivs) "(Hsl & Hcap & #Hitems)".
  iDestruct (big_sepL2_impl _ (λ _ updateItemVal typedInput,
      ⌜(Z.of_nat (clientId (in_id typedInput.2)) < 2^64)%Z ∧
       (Z.of_nat (clock (in_id typedInput.2)) < 2^64)%Z⌝)%I
    with "Hitems []") as "Hpure".
  { iIntros "!>" (i updateItemVal typedInput Hu Hi) "Hui".
    iDestruct "Hui" as (oleft oright opn)
      "(HisL & HisR & HisPN & %Hin_l & %Hin_r & %Hin_id & %Hin_c & %Hulen & %Htid & %Hborrow)".
    iPureIntro. rewrite -Hin_id /toYjsId /=. split; word. }
  iDestruct (big_sepL2_length with "Hitems") as %Hlen2.
  iDestruct (big_sepL2_pure_1 with "Hpure") as %Hb.
  iPureIntro. move=> i typedInput Hi.
  have [updateItemVal Huiv] : is_Some (uivs !! i).
  { apply lookup_lt_is_Some_2. rewrite Hlen2. exact (lookup_lt_Some _ _ _ Hi). }
  exact (Hb i updateItemVal typedInput Huiv Hi).
Qed.

(* ===== the pending gate, heap side (issue #40) ============================ *)

(** [containsUpdateItemId] (the in-pending dedup probe): scans a decoded pending
    slice for a struct carrying [idv]. *)
Lemma wp_containsUpdateItemId (sl : slice.t) (dq : dfrac)
    (inputs : list (TId * IntegrateInput (A := A))) (idv : yjs.id.t) :
  {{{ is_pkg_init yjs ∗ own_update_structs sl dq inputs }}}
    @! yjs.containsUpdateItemId #sl #idv
  {{{ RET #(existsb (λ typedInput2, bool_decide (in_id typedInput2.2 = toYjsId idv)) inputs);
      own_update_structs sl dq inputs }}}.
Proof using Type*.
  wp_start as "Hupd".
  iDestruct "Hupd" as (uivs) "(Hsl & Hcap & #Hitems)".
  iDestruct (big_sepL2_length with "Hitems") as %Hlen2.
  iDestruct (own_slice_len with "Hsl") as %[Hsllen Hsllen0].
  wp_auto.
  iAssert (∃ (j : nat),
    "Hi" ∷ i_ptr ↦ W64 j ∗ "Hitemsp" ∷ items_ptr ↦ sl ∗ "Hid" ∷ id_ptr ↦ idv ∗
    "Hsl" ∷ sl ↦*{dq} uivs ∗
    "Hcap" ∷ own_slice_cap yjs.updateItem.t sl dq ∗
    "%Hjbnd" ∷ ⌜(j <= length uivs)%nat⌝ ∗
    "%Hnomatch" ∷ ⌜existsb (λ typedInput2, bool_decide (in_id typedInput2.2 = toYjsId idv))
                    (take j inputs) = false⌝)%I
    with "[i items id Hsl Hcap]" as "IH".
  { iExists 0%nat. iFrame "i items id Hsl Hcap". iPureIntro.
    split; [lia | rewrite take_0 //]. }
  wp_for "IH".
  case_bool_decide as Hcond.
  - (* probe element j *)
    have Hjlt : (j < length uivs)%nat.
    { move: Hcond. rewrite Hsllen. word. }
    destruct (uivs !! j) as [updateItemVal|] eqn:Huiv;
      last by (apply lookup_ge_None in Huiv; lia).
    have [typedInput Hti] : is_Some (inputs !! j).
    { apply lookup_lt_is_Some_2. rewrite -Hlen2. exact Hjlt. }
    iDestruct (big_sepL2_lookup _ _ _ j with "Hitems") as "Hui";
      [exact Huiv | exact Hti |].
    iDestruct "Hui" as (oleft oright opn)
      "(HisL & HisR & HisPN & %Hin_l & %Hin_r & %Hin_id & %Hin_c & %Hulen & %Htid & %Hborrow)".
    wp_auto.
    rewrite decide_True; last by word.
    iDestruct (own_slice_elem_acc (sint.Z (W64 j)) updateItemVal sl dq uivs with "Hsl") as "[Hel Hgive]".
    { word. }
    { replace (Z.to_nat (sint.Z (W64 j))) with j by word. exact Huiv. }
    wp_auto.
    wp_method_call. wp_call. wp_auto.
    wp_apply (wp_Id__Equal updateItemVal.(yjs.updateItem.id') idv).
    iDestruct ("Hgive" $! updateItemVal with "Hel") as "Hsl".
    have Hinsid : (<[sint.nat (W64 j) := updateItemVal]> uivs) = uivs.
    { apply list_insert_id. replace (sint.nat (W64 j)) with j by word. exact Huiv. }
    iEval (rewrite Hinsid) in "Hsl".
    case_bool_decide as Heqid.
    + (* match: the whole scan is true *)
      wp_auto. wp_for_post.
      have -> : existsb (λ typedInput2, bool_decide (in_id typedInput2.2 = toYjsId idv)) inputs = true.
      { apply existsb_exists. exists typedInput.
        split; [by apply list_elem_of_In, (list_elem_of_lookup_2 _ j) |].
        apply bool_decide_eq_true_2. rewrite -Hin_id //. }
      iApply ("HΦ" with "[Hsl Hcap]").
      iExists uivs. iFrame "Hsl Hcap Hitems".
    + (* no match at j: advance *)
      wp_auto. wp_for_post.
      iFrame "HΦ".
      iExists (S j).
      replace (word.add (W64 j) (W64 1)) with (W64 (S j)) by word.
      iFrame "Hi Hitemsp Hid Hsl Hcap".
      iPureIntro. split; [lia |].
      erewrite take_S_r; last exact Hti.
      rewrite existsb_app Hnomatch /=.
      rewrite bool_decide_eq_false_2; first done.
      rewrite -Hin_id //.
  - (* scanned everything: the scan is false *)
    wp_auto.
    have Hjall : (j >= length uivs)%nat.
    { move: Hcond. rewrite Hsllen. rewrite Hsllen in Hjbnd. word. }
    have -> : existsb (λ typedInput2, bool_decide (in_id typedInput2.2 = toYjsId idv)) inputs = false.
    { rewrite -(take_ge inputs j); [exact Hnomatch | rewrite -Hlen2; lia]. }
    iApply ("HΦ" with "[Hsl Hcap]").
    iExists uivs. iFrame "Hsl Hcap Hitems".
Qed.


Lemma docm_cells_agree (m : DocModel) (bind : gmap P loc)
    (types : gmap loc type_state) (d : YjsId) :
  (∀ name p ts, bind !! name = Some p -> types !! p = Some ts ->
     doc_model_get m (RootId name) = ty_arr ts) ->
  (∀ t, doc_model_get m t ≠ [] -> ∃ name p, t = RootId name ∧ bind !! name = Some p) ->
  (∀ name p, bind !! name = Some p -> is_Some (types !! p)) ->
  (∀ p, is_Some (types !! p) -> ∃ name, bind !! name = Some p) ->
  (∀ p ts, types !! p = Some ts -> cells_repr (ty_arr ts) (ty_cells ts) (ty_arr ts)) ->
  (∀ c, c ∈ all_cells types -> run_wf (ic_run c)) ->
  (doc_model_has m d = true <-> ∃ c, c ∈ all_cells types ∧ cell_covers c d).
Proof.
  move=> Hmtypes Hmdom Hbindtypes Htypesbound Hreprall Hrunwf. split.
  - move=> /docm_has_spec [t [x [Hx Hid]]].
    have Hne : doc_model_get m t ≠ [].
    { move=> Heq. move: Hx. rewrite Heq elem_of_nil //. }
    destruct (Hmdom t Hne) as (nm & p & -> & Hbnm).
    destruct (Hbindtypes nm p Hbnm) as [ts Hts].
    have Hdg : doc_model_get m (RootId nm) = ty_arr ts := Hmtypes nm p ts Hbnm Hts.
    have Hrep : ty_arr ts = run_flatten (ty_cells ts) := Hreprall p ts Hts.
    rewrite Hdg Hrep in Hx.
    apply list_elem_of_lookup_1 in Hx as [kn Hkn].
    destruct (run_flatten_lookup_cell (ty_cells ts) kn x Hkn) as (ci & off & c & Hci & Hoff & _).
    have Hcin : c ∈ ty_cells ts := list_elem_of_lookup_2 _ _ _ Hci.
    have Hcall : c ∈ all_cells types by (apply all_cells_elem_of; exists p, ts; by split).
    have Hwf : run_wf (ic_run c) := Hrunwf c Hcall.
    have Hofflt : (off < length (ic_run c))%nat := lookup_lt_Some _ _ _ Hoff.
    have Hxid := run_wf_char_id (ic_run c) off x Hwf Hoff.
    rewrite Hid in Hxid.
    exists c. split; [exact Hcall |].
    rewrite /cell_covers /run_head. rewrite Hxid /=.
    split_and!; [done | lia | lia].
  - move=> [c [Hc [Hcl [Hle Hlt]]]].
    apply docm_has_spec.
    have Hwf : run_wf (ic_run c) := Hrunwf c Hc.
    apply all_cells_elem_of in Hc. destruct Hc as (p & ts & Hts & Hcts).
    destruct (Htypesbound p (ex_intro _ ts Hts)) as [nm Hbnm].
    have Hdg : doc_model_get m (RootId nm) = ty_arr ts := Hmtypes nm p ts Hbnm Hts.
    have Hrep : ty_arr ts = run_flatten (ty_cells ts) := Hreprall p ts Hts.
    destruct (run_wf_char_at_clock (ic_run c) d Hwf Hcl Hle Hlt) as (ch & Hch & Hchid).
    exists (RootId nm), ch. split; [| exact Hchid].
    rewrite Hdg Hrep.
    apply list_elem_of_lookup_1 in Hcts as [ci Hci].
    apply (list_elem_of_lookup_2 _
             (length (run_flatten (take ci (ty_cells ts))) +
              (clock d - clock (item_id (run_head c))))%nat).
    exact (run_flatten_lookup_of_cell (ty_cells ts) ci _ c ch Hci Hch).
Qed.

(* ----- the arrival gate ----- *)
(* (the pure gate lemmas [input_ready_false_of_dep] / [input_ready_true_of] /
   [input_deps_*] live in [yjs_network_model] with the pending theory) *)

(** [store.originArrived] (issue #40): the per-origin arrival check; a nil
    origin imposes no dependency. Its result is the model presence of the
    origin id (via [hasNode]). *)
Lemma wp_store__originArrived (s mref : loc) (dq : dfrac) (p : loc)
    (originId : option yjs.id.t) (m : DocModel) (types : gmap loc type_state) :
  (∀ d : YjsId, doc_model_has m d = true <-> ∃ c, c ∈ all_cells types ∧ cell_covers c d) ->
  (∀ c, c ∈ all_cells types -> (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) < 2^64)%Z) ->
  NoDup (ic_loc <$> all_cells types) ->
  cells_range_disjoint (all_cells types) ->
  {{{ is_pkg_init yjs ∗ is_origin_id p originId ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref dq types ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) }}}
    s @! (go.PointerType yjs.store) @! "originArrived" #p
  {{{ (ok : bool), RET #ok;
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref dq types ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) ∗
      ⌜ok = true <-> match originId with
                     | None => True
                     | Some idv => doc_model_has m (toYjsId idv) = true
                     end⌝ }}}.
Proof using Type*.
  move=> Hagree Hrunfits Hnodup Hrangedisj.
  iIntros (Φ) "(#Hpkg & #HisP & Hitemsf & Hitemmap & Htypes) HΦ".
  wp_method_call. wp_call. wp_call. wp_auto.
  destruct originId as [idv |]; simpl.
  - (* a real origin: dereference and probe *)
    iDestruct "HisP" as "[%Hpne #Hpid]".
    rewrite bool_decide_eq_false_2; last first.
    { move=> Heq. exact (Hpne Heq). }
    wp_auto.
    wp_apply (wp_store__hasNode s mref dq idv m types Hagree Hrunfits Hnodup Hrangedisj
                with "[$Hitemsf $Hitemmap $Htypes]").
    iIntros (ok) "(Hitemsf & Hitemmap & Htypes & %Hok)".
    wp_auto.
    iApply ("HΦ" $! ok).
    iFrame "Hitemsf Hitemmap Htypes".
    iPureIntro. exact Hok.
  - (* nil origin: no dependency *)
    iDestruct "HisP" as %->.
    rewrite bool_decide_eq_true_2 //.
    wp_auto.
    iApply ("HΦ" $! true).
    iFrame "Hitemsf Hitemmap Htypes".
    iPureIntro. done.
Qed.

(** [store.depsArrived] (issue #40): the structural gate, as arrival checks.
    The return value IS the pure gate [input_ready] of the decoded struct; each
    arrival check ([originArrived] / [hasNode]) returns the model presence of a
    dependency, so the gate composes them by [input_ready_true_of] /
    [input_ready_false_of_dep]. *)
Lemma wp_store__depsArrived (s mref : loc) (dq : dfrac) (updateItemVal : yjs.updateItem.t)
    (typedInput : TId * IntegrateInput (A := A)) (m : DocModel) (types : gmap loc type_state) :
  (∀ d : YjsId, doc_model_has m d = true <-> ∃ c, c ∈ all_cells types ∧ cell_covers c d) ->
  (∀ c, c ∈ all_cells types -> (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) < 2^64)%Z) ->
  NoDup (ic_loc <$> all_cells types) ->
  cells_range_disjoint (all_cells types) ->
  {{{ is_pkg_init yjs ∗ is_update_item updateItemVal typedInput ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref dq types ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) }}}
    s @! (go.PointerType yjs.store) @! "depsArrived" #updateItemVal
  {{{ RET #(input_ready m typedInput.2);
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref dq types ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) }}}.
Proof using Type*.
  move=> Hagree Hrunfits Hnodup Hrangedisj.
  iIntros (Φ) "(#Hpkg & #Hui & Hitemsf & Hitemmap & Htypes) HΦ".
  iDestruct "Hui" as (oleft oright opn)
    "(HisL & HisR & HisPN & %Hin_l & %Hin_r & %Hin_id & %Hin_c & %Hunonempty & %Htid & %Hborrow)".
  have Hcid : clientId (in_id typedInput.2) = uint.nat updateItemVal.(yjs.updateItem.id').(yjs.id.clientId').
  { rewrite -Hin_id /toYjsId //. }
  have Hck : clock (in_id typedInput.2) = uint.nat updateItemVal.(yjs.updateItem.id').(yjs.id.clock').
  { rewrite -Hin_id /toYjsId //. }
  wp_method_call. wp_call. wp_call. wp_auto.
  (* ---- left origin ---- *)
  wp_apply (wp_store__originArrived s mref dq _ oleft m types Hagree Hrunfits Hnodup Hrangedisj
              with "[$HisL $Hitemsf $Hitemmap $Htypes]").
  iIntros (okL) "(Hitemsf & Hitemmap & Htypes & %HokL)".
  wp_auto.
  destruct okL; last first.
  { (* left origin missing *)
    wp_auto.
    have Hready : input_ready m typedInput.2 = false.
    { destruct oleft as [idL |]; simpl in Hin_l; last first.
      { exfalso. destruct HokL as [_ H2]. have := H2 I. discriminate. }
      apply (input_ready_false_of_dep m typedInput.2 (toYjsId idL)).
      - apply input_deps_originL. rewrite -Hin_l //.
      - apply not_true_iff_false => Hd.
        destruct HokL as [_ H2]. have := H2 Hd. discriminate. }
    iEval (rewrite Hready) in "HΦ".
    iApply ("HΦ" with "[$Hitemsf $Hitemmap $Htypes]"). }
  wp_auto.
  (* ---- right origin ---- *)
  wp_apply (wp_store__originArrived s mref dq _ oright m types Hagree Hrunfits Hnodup Hrangedisj
              with "[$HisR $Hitemsf $Hitemmap $Htypes]").
  iIntros (okR) "(Hitemsf & Hitemmap & Htypes & %HokR)".
  wp_auto.
  destruct okR; last first.
  { (* right origin missing *)
    wp_auto.
    have Hready : input_ready m typedInput.2 = false.
    { destruct oright as [idR |]; simpl in Hin_r; last first.
      { exfalso. destruct HokR as [_ H2]. have := H2 I. discriminate. }
      apply (input_ready_false_of_dep m typedInput.2 (toYjsId idR)).
      - apply input_deps_originR. rewrite -Hin_r //.
      - apply not_true_iff_false => Hd.
        destruct HokR as [_ H2]. have := H2 Hd. discriminate. }
    iEval (rewrite Hready) in "HΦ".
    iApply ("HΦ" with "[$Hitemsf $Hitemmap $Htypes]"). }
  wp_auto.
  (* the origin facts carried into the tail *)
  have HLarr : ∀ originId, in_originId typedInput.2 = Some originId -> doc_model_has m originId = true.
  { move=> originId Hoid.
    destruct oleft as [idL |]; simpl in Hin_l; last by rewrite -Hin_l in Hoid.
    rewrite -Hin_l in Hoid. injection Hoid as <-.
    exact (proj1 HokL eq_refl). }
  have HRarr : ∀ originId, in_rightOriginId typedInput.2 = Some originId -> doc_model_has m originId = true.
  { move=> originId Hoid.
    destruct oright as [idR |]; simpl in Hin_r; last by rewrite -Hin_r in Hoid.
    rewrite -Hin_r in Hoid. injection Hoid as <-.
    exact (proj1 HokR eq_refl). }
  (* ---- the own-predecessor gate ---- *)
  destruct (bool_decide
      (uint.Z (W64 0) < uint.Z updateItemVal.(yjs.updateItem.id').(yjs.id.clock'))) eqn:Hckpos.
  - (* clock > 0: probe (client, clock-1) *)
    apply bool_decide_eq_true_1 in Hckpos.
    wp_auto.
    wp_apply (wp_NewId updateItemVal.(yjs.updateItem.id').(yjs.id.clientId')
                (word.sub updateItemVal.(yjs.updateItem.id').(yjs.id.clock') (W64 1))).
    wp_apply (wp_store__hasNode s mref dq _ m types Hagree Hrunfits Hnodup Hrangedisj
                with "[$Hitemsf $Hitemmap $Htypes]").
    iIntros (okP) "(Hitemsf & Hitemmap & Htypes & %HokP)".
    wp_auto.
    have Hpredid : toYjsId (yjs.id.mk updateItemVal.(yjs.updateItem.id').(yjs.id.clientId')
                     (word.sub updateItemVal.(yjs.updateItem.id').(yjs.id.clock') (W64 1)))
                 = MkYjsId (clientId (in_id typedInput.2)) (clock (in_id typedInput.2) - 1)%nat.
    { rewrite /toYjsId /= Hcid Hck. f_equal. word. }
    have Hckform : ∃ k, clock (in_id typedInput.2) = S k ∧ (k = clock (in_id typedInput.2) - 1)%nat.
    { exists (clock (in_id typedInput.2) - 1)%nat. rewrite Hck. split; [word | done]. }
    destruct Hckform as (k & HckS & Hkval).
    destruct okP; last first.
    + (* predecessor missing *)
      wp_auto.
      have Hready : input_ready m typedInput.2 = false.
      { apply (input_ready_false_of_dep m typedInput.2 (MkYjsId (clientId (in_id typedInput.2)) k)).
        - exact (input_deps_pred typedInput.2 k HckS).
        - apply not_true_iff_false => Hd.
          destruct HokP as [_ H2].
          rewrite Hpredid -Hkval in H2.
          have := H2 Hd. discriminate. }
      iEval (rewrite Hready) in "HΦ".
      iApply ("HΦ" with "[$Hitemsf $Hitemmap $Htypes]").
    + (* everything arrived *)
      wp_auto.
      have Hready : input_ready m typedInput.2 = true.
      { apply input_ready_true_of; [exact HLarr | exact HRarr |].
        move=> k' Hk'.
        have Hkk : k' = k by lia.
        rewrite Hkk Hkval.
        have HP := proj1 HokP eq_refl. rewrite Hpredid in HP. exact HP. }
      iEval (rewrite Hready) in "HΦ".
      iApply ("HΦ" with "[$Hitemsf $Hitemmap $Htypes]").
  - (* clock 0: no predecessor *)
    apply bool_decide_eq_false_1 in Hckpos.
    wp_auto.
    have Hready : input_ready m typedInput.2 = true.
    { apply input_ready_true_of; [exact HLarr | exact HRarr |].
      move=> k' Hk'. exfalso. rewrite Hck in Hk'. word. }
    iEval (rewrite Hready) in "HΦ".
    iApply ("HΦ" with "[$Hitemsf $Hitemmap $Htypes]").
Qed.

(* ----- the ready step: one decoded struct, repaired and integrated ----- *)

(** [store.integrateDecoded] (issue #40 x issue #28 U7c): the ready branch of
    the drain, as a per-struct contract -- the loop-free core of the batch
    loop. The struct's target root must be bound ([Hbnm]; the #49 pre-bound-
    roots restriction), its chained per-char op chunk realizes the run fold
    [Hall = integrate_all (ops_of_input ...)], its head-op scan facts hold at
    the current model, and the heap advances to the model spliced at [typedInput.1]
    with the four store-lock pool invariants maintained. Mirrors one iteration
    of main's whole-batch [wp_store__applyUpdate] body. *)
Lemma wp_store__integrateDecoded (s mref tref : loc)
    (updateItemVal : yjs.updateItem.t) (typedInput : TId * IntegrateInput (A := A))
    (m : DocModel) (types : gmap loc type_state) (bind : gmap P loc)
    (newItem : YjsItem A) (arr2 : list (YjsItem A)) (nm : P) (p : loc) :
  typedInput.1 = RootId nm ->
  bind !! nm = Some p ->
  toItem typedInput.2 (doc_model_get m typedInput.1) = Some newItem ->
  IsItemValid newItem ->
  maximalId newItem (doc_model_get m typedInput.1) ->
  integrate_all (ops_of_input typedInput.2 (explode (in_content typedInput.2))) (doc_model_get m typedInput.1) = Some arr2 ->
  (∀ c0, c0 ∈ all_cells types -> cell_client c0 = W64 (clientId (in_id typedInput.2)) ->
     (uint.Z (cell_clock c0) < uint.Z (W64 (clock (in_id typedInput.2))))%Z ∧
     (uint.Z (cell_clock c0) + Z.of_nat (length (ic_run c0)) <= uint.Z (W64 (clock (in_id typedInput.2))))%Z) ->
  (∀ name p', bind !! name = Some p' -> is_Some (types !! p')) ->
  (∀ n1 n2 p', bind !! n1 = Some p' -> bind !! n2 = Some p' -> n1 = n2) ->
  (∀ name p' ts, bind !! name = Some p' -> types !! p' = Some ts ->
     doc_model_get m (RootId name) = ty_arr ts) ->
  (Z.of_nat (clock (in_id typedInput.2)) + Z.of_nat (length (in_content typedInput.2)) < 2^64)%Z ->
  NoDup (ic_loc <$> all_cells types) ->
  cells_range_disjoint (all_cells types) ->
  (∀ c, c ∈ all_cells types -> cell_fits c) ->
  (∀ c, c ∈ all_cells types -> cell_origin_clk c) ->
  {{{ is_pkg_init yjs ∗ is_update_item updateItemVal typedInput ∗
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types ∗
      (s .[(yjs.store.t), "types"]) ↦ tref ∗ own_map tref (DfracOwn 1) bind ∗
      ([∗ map] parent ↦ ts ∈ types,
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) }}}
    s @! (go.PointerType yjs.store) @! "integrateDecoded" #updateItemVal
  {{{ (types' : gmap loc type_state), RET #();
      (s .[(yjs.store.t), "items"]) ↦ mref ∗ own_item_map mref (DfracOwn 1) types' ∗
      (s .[(yjs.store.t), "types"]) ↦ tref ∗ own_map tref (DfracOwn 1) bind ∗
      ([∗ map] parent ↦ ts ∈ types',
          own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
          ⌜YjsArrInvariant (ty_arr ts)⌝) ∗
      ⌜dom types' = dom types⌝ ∗
      ⌜∀ name p' ts', bind !! name = Some p' -> types' !! p' = Some ts' ->
         doc_model_get (<[typedInput.1 := arr2]> m) (RootId name) = ty_arr ts'⌝ ∗
      ⌜∀ c, c ∈ all_cells types' ->
         (∃ c0, c0 ∈ all_cells types ∧ cell_client c = cell_client c0 ∧
            (uint.Z (cell_clock c0) <= uint.Z (cell_clock c))%Z ∧
            (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) <=
             uint.Z (cell_clock c0) + Z.of_nat (length (ic_run c0)))%Z) ∨
         (cell_client c = W64 (clientId (in_id typedInput.2)) ∧
          (uint.Z (W64 (clock (in_id typedInput.2))) <= uint.Z (cell_clock c))%Z ∧
          (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) <=
           uint.Z (W64 (clock (in_id typedInput.2))) + Z.of_nat (length (in_content typedInput.2)))%Z)⌝ ∗
      ⌜NoDup (ic_loc <$> all_cells types')⌝ ∗
      ⌜cells_range_disjoint (all_cells types')⌝ ∗
      ⌜∀ c, c ∈ all_cells types' -> cell_fits c⌝ ∗
      ⌜∀ c, c ∈ all_cells types' -> cell_origin_clk c⌝ }}}.
Proof using Type*.
  move=> Htieq Hbnm Htoit Hvld Hmax Hall Hgmax0 Hbindtypes Hbindinj Hmtypes
         Hnowrapc Hlocdup Hrangedisj Hfits Horiginclk.
  iIntros (Φ) "(#Hpkg & #Hui & Hitemsf & Hitemmap & Htypesf & Htypesmap & Htypes) HΦ".
  iDestruct "Hui" as (oleft oright opn)
    "(HisL & HisR & HisPN & %Hin_l & %Hin_r & %Hin_id & %Hin_c & %Hunonempty & %Htid & %Hborrow)".
  destruct typedInput as [typedInput2 input]. simpl in *. subst typedInput2.
  have Hts0 : is_Some (types !! p) := Hbindtypes nm p Hbnm.
  destruct Hts0 as [[cellsj arrj0] Htsj].
  have Hdgj : doc_model_get m (RootId nm) = arrj0 := Hmtypes nm p _ Hbnm Htsj.
  set (arrj := doc_model_get m (RootId nm)) in *.
  rewrite -Hdgj in Htsj.
  iDestruct (types_arr_inv2 with "Htypes") as %Harrinvs.
  have Hinvj : YjsArrInvariant arrj := Harrinvs p _ Htsj.
  destruct (integrate_some input arrj newItem Hinvj Htoit) as [arrinput Hintginput].
  destruct (integrate_finds input arrj arrinput Hintginput) as (leftIdx & rightIdx & HfindL & HfindR).
  iDestruct (types_entry_pures2 types p _ Htsj with "Htypes") as %(Hreprj & Hcparj).
  simpl in Hreprj, Hcparj.
  iDestruct (types_runs_wf2 with "Htypes") as %Hrunwfall.
  iDestruct (types_parents_all2 with "Htypes") as %Hparall.
  (* uniform repair witnesses: present origins resolve to the covering cell in
     this type's own cells (that is where [toItem]'s find landed) *)
  have Hwits : ∃ (ocL ocR : option item_cell),
    ((match in_originId input, ocL with
      | Some originId, Some c => c ∈ all_cells types ∧
          clientId (item_id (run_head c)) = clientId originId ∧
          (clock (item_id (run_head c)) <= clock originId)%nat ∧
          (clock originId < clock (item_id (run_head c)) + length (ic_run c))%nat
      | None, None => True | _, _ => False end : Prop)) /\
    ((match in_rightOriginId input, ocR with
      | Some originId, Some c => c ∈ all_cells types ∧
          clientId (item_id (run_head c)) = clientId originId ∧
          (clock (item_id (run_head c)) <= clock originId)%nat ∧
          (clock originId < clock (item_id (run_head c)) + length (ic_run c))%nat
      | None, None => True | _, _ => False end : Prop)) /\
    (match opn with
     | Some nm' => bind !! nm' = Some p
     | None => match ocL with
               | Some c => p = ic_parent c
               | None => match ocR with
                         | Some c => p = ic_parent c
                         | None => False
                         end
               end
     end) /\
    (match ocL with Some c => c ∈ cellsj | None => True end) /\
    (match ocR with Some c => c ∈ cellsj | None => True end).
  { have Hcellsw : ∀ (kn : nat) (it : YjsItem A), arrj !! kn = Some it ->
      ∃ (ci off : nat) (c : item_cell), cellsj !! ci = Some c ∧ ic_run c !! off = Some it ∧
        kn = (length (run_flatten (take ci cellsj)) + off)%nat ∧
        clientId (item_id (run_head c)) = clientId (item_id it) ∧
        (clock (item_id (run_head c)) <= clock (item_id it))%nat ∧
        (clock (item_id it) < clock (item_id (run_head c)) + length (ic_run c))%nat.
    { move=> kn it Hkn. rewrite /cells_repr in Hreprj. rewrite Hreprj in Hkn.
      destruct (run_flatten_lookup_cell cellsj kn it Hkn) as (ci & off & c & Hci & Hoff & Hpos).
      have Hwf : run_wf (ic_run c).
      { apply Hrunwfall. rewrite (all_cells_lookup _ _ _ Htsj). apply elem_of_app.
        left. exact (list_elem_of_lookup_2 _ _ _ Hci). }
      have Hcid := run_wf_char_id (ic_run c) off it Hwf Hoff.
      have Hlen := lookup_lt_Some _ _ _ Hoff.
      exists ci, off, c. split_and!.
      - exact Hci.
      - exact Hoff.
      - exact Hpos.
      - rewrite Hcid /run_head //=.
      - rewrite Hcid /run_head /=. lia.
      - rewrite Hcid /run_head /=. lia. }
    have HocL : ∃ ocL,
      ((match in_originId input, ocL with
        | Some originId, Some c => c ∈ all_cells types ∧
            clientId (item_id (run_head c)) = clientId originId ∧
            (clock (item_id (run_head c)) <= clock originId)%nat ∧
            (clock originId < clock (item_id (run_head c)) + length (ic_run c))%nat
        | None, None => True | _, _ => False end : Prop)) /\
      (match ocL with Some c => ic_parent c = p | None => True end) /\
      (match ocL with Some c => c ∈ cellsj | None => True end).
    { destruct (in_originId input) as [originIdLeft|] eqn:HoinL.
      - destruct (findLeftIdx_inv originIdLeft arrj leftIdx HfindL) as (kn & it & -> & Hkn & HidL).
        destruct (Hcellsw kn it Hkn) as (ci & off & cL & HcLk & Hoff & Hpos & Hcl & Hle & Hlt).
        have HcLmem : cL ∈ cellsj := list_elem_of_lookup_2 _ _ _ HcLk.
        exists (Some cL). split_and!.
        + apply all_cells_elem_of. exists p, (MkTypeState cellsj arrj).
          split; [exact Htsj | exact HcLmem].
        + rewrite HidL in Hcl. exact Hcl.
        + rewrite HidL in Hle. exact Hle.
        + rewrite HidL in Hlt. exact Hlt.
        + exact (Hcparj cL HcLmem).
        + exact HcLmem.
      - exists None. split_and!; done. }
    have HocR : ∃ ocR,
      ((match in_rightOriginId input, ocR with
        | Some originId, Some c => c ∈ all_cells types ∧
            clientId (item_id (run_head c)) = clientId originId ∧
            (clock (item_id (run_head c)) <= clock originId)%nat ∧
            (clock originId < clock (item_id (run_head c)) + length (ic_run c))%nat
        | None, None => True | _, _ => False end : Prop)) /\
      (match ocR with Some c => ic_parent c = p | None => True end) /\
      (match ocR with Some c => c ∈ cellsj | None => True end).
    { destruct (in_rightOriginId input) as [originIdRight|] eqn:HoinR.
      - destruct (findRightIdx_inv originIdRight arrj rightIdx HfindR) as (kn & it & -> & Hkn & HidR).
        destruct (Hcellsw kn it Hkn) as (ci & off & cR & HcRk & Hoff & Hpos & Hcl & Hle & Hlt).
        have HcRmem2 : cR ∈ cellsj := list_elem_of_lookup_2 _ _ _ HcRk.
        exists (Some cR). split_and!.
        + apply all_cells_elem_of. exists p, (MkTypeState cellsj arrj).
          split; [exact Htsj | exact HcRmem2].
        + rewrite HidR in Hcl. exact Hcl.
        + rewrite HidR in Hle. exact Hle.
        + rewrite HidR in Hlt. exact Hlt.
        + exact (Hcparj cR HcRmem2).
        + exact HcRmem2.
      - exists None. split_and!; done. }
    destruct HocL as (ocL & HwL & HparL & HmemL).
    destruct HocR as (ocR & HwR & HparR & HmemR).
    exists ocL, ocR. split_and!; try done.
    destruct opn as [nm'|].
    - have Hnmeq : RootId nm = RootId nm' := Htid nm' eq_refl.
      injection Hnmeq as <-. exact Hbnm.
    - destruct ocL as [cL|]; [by rewrite -(HparL) |].
      destruct ocR as [cR|]; [by rewrite -(HparR) |].
      destruct (Hborrow eq_refl) as [HL | HR].
      + move: HwL. by destruct (in_originId input).
      + move: HwR. by destruct (in_rightOriginId input). }
  destruct Hwits as (ocL & ocR & HwLc & HwRc & Hwpar & HmemLc & HmemRc).
  wp_method_call. wp_call. wp_call. wp_auto.
  wp_func_call. wp_call. wp_auto.
  wp_alloc itv as "Hitv". wp_auto.
  set (itemVal := {| yjs.item.id' := updateItemVal.(yjs.updateItem.id');
                yjs.item.originLeftId' := updateItemVal.(yjs.updateItem.originLeftId');
                yjs.item.originRightId' := updateItemVal.(yjs.updateItem.originRightId');
                yjs.item.left' := null; yjs.item.right' := null;
                yjs.item.parent' := null;
                yjs.item.content' := {| yjs.content.content' := updateItemVal.(yjs.updateItem.content') |};
                yjs.item.flags' := W8 2 |}).
  iAssert (own_linked_item_run itv input null null null) with "[Hitv]" as "Hfresh".
  { iExists itemVal, oleft, oright. rewrite /own_fresh_item_raw.
    iFrame "Hitv HisL HisR". iPureIntro.
    split_and!;
      [exact Hin_l | exact Hin_r | exact Hin_id | exact Hin_c
      | reflexivity | reflexivity | reflexivity | reflexivity
      | exact Hunonempty]. }
  (* general-repair premises (issue #28 U1) *)
  iDestruct (types_cells_id_bounds2 with "Htypes") as %Hbnds0.
  have Huniqj := yai_unique _ Hinvj.
  have HfLpj : findPtrIdx (origin newItem) arrj = Some leftIdx.
  { rewrite -(toitem_lemmas.findLeftIdx_findPtrIdx_eq input newItem arrj Huniqj Htoit). exact HfindL. }
  have HfRpj : findPtrIdx (rightOrigin newItem) arrj = Some rightIdx.
  { rewrite -(toitem_lemmas.findRightIdx_findPtrIdx_eq input newItem arrj Huniqj Htoit). exact HfindR. }
  have HorigAj := findptridx_getelem.findPtrIdx_ArrSet arrj (origin newItem) leftIdx HfLpj.
  have HrorAj := findptridx_getelem.findPtrIdx_ArrSet arrj (rightOrigin newItem) rightIdx HfRpj.
  have Hlrj := findptridx_order2.YjsLt'_findPtrIdx_lt arrj (origin newItem) (rightOrigin newItem)
                leftIdx rightIdx Hinvj HorigAj HrorAj (iiv_origin_lt _ Hvld) HfLpj HfRpj.
  have Hsameg : ((match in_originId input, in_rightOriginId input, ocL, ocR with
    | Some a, Some b, Some cL0, Some cR0 => cL0 = cR0 -> (clock a < clock b)%nat
    | _, _, _, _ => True end : Prop)).
  { move: HwLc HwRc HmemLc HmemRc HfindL HfindR.
    destruct (in_originId input) as [originIdLeft|] eqn:HoinL2; try done.
    destruct (in_rightOriginId input) as [originIdRight|] eqn:HoinR2; try done.
    destruct ocL as [cL0|]; try done. destruct ocR as [cR0|]; try done.
    move=> [_ [HclL [HleL HltL]]] [_ [HclR [HleR HltR]]] HmemL2 HmemR2 HfindL2 HfindR2 Heq.
    subst cR0.
    destruct (list_elem_of_lookup_1 _ _ HmemL2) as [ciw Hciw].
    have Hwf : run_wf (ic_run cL0).
    { apply Hrunwfall. rewrite (all_cells_lookup _ _ _ Htsj). apply elem_of_app.
      by left. }
    destruct (run_wf_char_at_clock (ic_run cL0) originIdLeft Hwf HclL HleL HltL)
      as (chL & HchL & HidchL).
    destruct (run_wf_char_at_clock (ic_run cL0) originIdRight Hwf HclR HleR HltR)
      as (chR & HchR & HidchR).
    have HposL := run_flatten_lookup_of_cell cellsj ciw _ cL0 chL Hciw HchL.
    have HposR := run_flatten_lookup_of_cell cellsj ciw _ cL0 chR Hciw HchR.
    rewrite /cells_repr in Hreprj. rewrite -Hreprj in HposL HposR.
    destruct (findLeftIdx_inv originIdLeft arrj leftIdx HfindL2) as (knL & itL & HeqL & HknL & HidL2).
    destruct (findRightIdx_inv originIdRight arrj rightIdx HfindR2) as (knR & itR & HeqR & HknR & HidR2).
    set prefw := length (run_flatten (take ciw cellsj)) in HposL HposR.
    have HknLp : knL = (prefw + (clock originIdLeft - clock (item_id (run_head cL0))))%nat.
    { set posL := (prefw + (clock originIdLeft - clock (item_id (run_head cL0))))%nat in HposL |- *.
      destruct (Nat.lt_trichotomy knL posL) as [Hlt2 | [Heq2 | Hgt2]]; [| exact Heq2 |]; exfalso.
      - have := uniqueId_lookup_ne arrj knL posL itL chL Huniqj HknL HposL Hlt2.
        rewrite HidL2 HidchL //.
      - have := uniqueId_lookup_ne arrj posL knL chL itL Huniqj HposL HknL Hgt2.
        rewrite HidL2 HidchL //. }
    have HknRp : knR = (prefw + (clock originIdRight - clock (item_id (run_head cL0))))%nat.
    { set posR := (prefw + (clock originIdRight - clock (item_id (run_head cL0))))%nat in HposR |- *.
      destruct (Nat.lt_trichotomy knR posR) as [Hlt2 | [Heq2 | Hgt2]]; [| exact Heq2 |]; exfalso.
      - have := uniqueId_lookup_ne arrj knR posR itR chR Huniqj HknR HposR Hlt2.
        rewrite HidR2 HidchR //.
      - have := uniqueId_lookup_ne arrj posR knR chR itR Huniqj HposR HknR Hgt2.
        rewrite HidR2 HidchR //. }
    have Hklt : (knL < knR)%nat by lia.
    lia. }
  wp_apply (wp_store__repair_split s mref tref itv (updateItemVal.(yjs.updateItem.parentName'))
              input opn types bind ocL ocR p
              HwLc HwRc Hsameg Hwpar Hfits Hlocdup Hrangedisj Horiginclk
              with "[$Hfresh $HisPN $Hitemsf $Hitemmap $Htypesf $Htypesmap $Htypes]").
  iIntros (lft rgt types2) "(Hlinked & Hitemsf & Hitemmap & Htypesf & Htypesmap & Htypes & %Hpinv2 & %Hrtf & %HbdL & %HbdR)".
  destruct Hpinv2 as (Hfits2 & Hnodup2 & Hrangedisj2 & Horiginclk2).
  destruct Hrtf as (Hpres2 & Hdom2 & Hrl2 & Hunitpres2 & Hsub2).
  destruct (Hdom2 p (mk_is_Some _ _ Htsj)) as [ts2e Htsj2].
  destruct (Hpres2 p ts2e Htsj2) as (ts0e & Htsj0e & Harr2p & Hflat2p).
  have Hts0eq2 : ts0e = MkTypeState cellsj arrj by congruence.
  rewrite Hts0eq2 /= in Harr2p Hflat2p.
  destruct ts2e as [cellsj2 arrj2]. simpl in Harr2p, Hflat2p. subst arrj2.
  iDestruct (types_runs_wf2 with "Htypes") as %Hrunwfall2.
  iDestruct (types_parents_all2 with "Htypes") as %Hparall2.
  iDestruct (types_cells_id_bounds2 with "Htypes") as %Hbnds2.
  have Hcparj2 : ∀ c, c ∈ cellsj2 -> ic_parent c = p.
  { move=> c Hc. exact (Hparall2 p _ c Htsj2 Hc). }
  (* the range-form freshness transports through sub-range provenance *)
  have Hbndj2 : ∀ c0, c0 ∈ all_cells types2 ->
      cell_client c0 = W64 (clientId (in_id input)) ->
      (uint.Z (cell_clock c0) < uint.Z (W64 (clock (in_id input))))%Z ∧
      (uint.Z (cell_clock c0) + Z.of_nat (length (ic_run c0)) <= uint.Z (W64 (clock (in_id input))))%Z.
  { move=> c0 Hc0 Hcc.
    destruct (Hsub2 c0 Hc0) as (cold & Hcold & Hcl & Hlo & Hhi).
    have Hccold : cell_client cold = W64 (clientId (in_id input)) by rewrite -Hcl Hcc.
    have Hh := Hgmax0 cold Hcold Hccold.
    have Hlen1 : (1 <= length (ic_run c0))%nat.
    { have Hwf := Hrunwfall2 c0 Hc0.
      destruct (ic_run c0) eqn:Hrc; [exact (False_ind _ (proj1 Hwf eq_refl)) | simpl; lia]. }
    split; lia. }
  have Hreprj' : arrj = run_flatten cellsj2.
  { move: Hreprj. rewrite /cells_repr. move=> ->. by rewrite Hflat2p. }
  have HcurLpack : ∃ curL2 : nat,
      (curL2 <= length cellsj2)%nat ∧
      (Z.of_nat (length (run_flatten (take curL2 cellsj2))) = leftIdx + 1)%Z ∧
      lft = node_loc cellsj2 (Z.of_nat curL2 - 1).
  { move: HbdL HwLc HmemLc HfindL.
    destruct (in_originId input) as [originIdLeft|] eqn:HoinL3; destruct ocL as [c0|]; try done.
    - move=> [Hlft0 [cL' [HcL'mem [HcL'loc [HcL'cl [HcL'clk HcL'par]]]]]]
             [_ [Hclw [Hlew Hltw]]] Hmem0 HfindL3.
      have HparL0 : ic_parent c0 = p := Hcparj c0 Hmem0.
      have Hmem0a : c0 ∈ all_cells types
        by (rewrite (all_cells_lookup _ _ _ Htsj); apply elem_of_app; by left).
      have HcL'cells : cL' ∈ cellsj2.
      { have HcL'm := HcL'mem. apply all_cells_elem_of in HcL'm.
        destruct HcL'm as (p0 & ts0 & Hp0 & Hcts0).
        have Hpar0 : ic_parent cL' = p0 := Hparall2 p0 ts0 cL' Hp0 Hcts0.
        have Hpeq : p0 = p by rewrite -Hpar0 HcL'par HparL0.
        rewrite Hpeq in Hp0.
        have Hts0eq : ts0 = MkTypeState cellsj2 arrj by congruence.
        rewrite Hts0eq /= in Hcts0. exact Hcts0. }
      destruct (list_elem_of_lookup_1 _ _ HcL'cells) as [ciL Hciw].
      have Hwf' : run_wf (ic_run cL') := Hrunwfall2 cL' HcL'mem.
      have Hlen1 : (1 <= length (ic_run cL'))%nat.
      { destruct (ic_run cL') eqn:Hrc; [exact (False_ind _ (proj1 Hwf' eq_refl)) | simpl; lia]. }
      have HbL' := Hbnds2 cL' HcL'mem.
      have Hzck : (uint.Z (cell_clock cL') = Z.of_nat (clock (item_id (run_head cL'))))%Z
        by (rewrite /cell_clock; destruct HbL'; word).
      have Hpin : (clock (item_id (run_head cL')) + length (ic_run cL') = clock originIdLeft + 1)%nat.
      { move: HcL'clk. rewrite Hzck. lia. }
      have HclL' : clientId (item_id (run_head cL')) = clientId originIdLeft.
      { have Hb1 := proj1 (Hbnds2 cL' HcL'mem).
        have Hb2 := proj1 (Hbnds0 c0 Hmem0a).
        move: HcL'cl. rewrite /cell_client -Hclw. move=> Hcc.
        have Hz : uint.Z (W64 (clientId (item_id (run_head cL'))))
                = uint.Z (W64 (clientId (item_id (run_head c0)))) by rewrite Hcc.
        word. }
      destruct (lookup_lt_is_Some_2 (ic_run cL') (length (ic_run cL') - 1)%nat
                  ltac:(lia)) as [chL HchL].
      have HidchL : item_id chL = originIdLeft.
      { rewrite (run_wf_char_id _ _ _ Hwf' HchL).
        rewrite /run_head in Hpin.
        destruct originIdLeft as [oc ok].
        have Hpin' : ((item_id (hd inhabitant (ic_run cL'))).(clock)
                      + length (ic_run cL'))%nat = (ok + 1)%nat := Hpin.
        f_equal; [exact HclL' | lia]. }
      have HposL := run_flatten_lookup_of_cell cellsj2 ciL _ cL' chL Hciw HchL.
      rewrite -Hreprj' in HposL.
      destruct (findLeftIdx_inv originIdLeft arrj leftIdx HfindL3) as (knL & itL & HeqL & HknL & HidL2).
      have HknLp : knL = (length (run_flatten (take ciL cellsj2)) + (length (ic_run cL') - 1))%nat.
      { set posL := (length (run_flatten (take ciL cellsj2)) + (length (ic_run cL') - 1))%nat
          in HposL |- *.
        destruct (Nat.lt_trichotomy knL posL) as [Hlt2 | [Heq2 | Hgt2]]; [| exact Heq2 |]; exfalso.
        - have := uniqueId_lookup_ne arrj knL posL itL chL Huniqj HknL HposL Hlt2.
          rewrite HidL2 HidchL //.
        - have := uniqueId_lookup_ne arrj posL knL chL itL Huniqj HposL HknL Hgt2.
          rewrite HidL2 HidchL //. }
      exists (S ciL). split_and!.
      + apply lookup_lt_Some in Hciw. lia.
      + rewrite (run_flatten_take_S cellsj2 ciL cL' Hciw) length_app. lia.
      + replace (Z.of_nat (S ciL) - 1)%Z with (Z.of_nat ciL) by lia.
        rewrite /node_loc decide_True; last lia.
        rewrite Nat2Z.id Hciw /= HcL'loc //.
    - move=> Hlftnull _ _ HfindL3.
      move: HfindL3. rewrite /findLeftIdx. move=> [= <-].
      exists 0%nat. split_and!.
      + lia.
      + rewrite take_0 /run_flatten /=. lia.
      + rewrite Hlftnull /node_loc. case_decide; [lia | done]. }
  have HcurRpack : ∃ curR2 : nat,
      (curR2 <= length cellsj2)%nat ∧
      (Z.of_nat (length (run_flatten (take curR2 cellsj2))) = rightIdx)%Z ∧
      rgt = node_loc cellsj2 (Z.of_nat curR2).
  { move: HbdR HwRc HmemRc HfindR.
    destruct (in_rightOriginId input) as [originIdRight|] eqn:HoinR3; destruct ocR as [c0|]; try done.
    - move=> [cR' [HcR'mem [HcR'loc [HcR'cl [HcR'clk HcR'par]]]]]
             [_ [Hclw [Hlew Hltw]]] Hmem0 HfindR3.
      have HparR0 : ic_parent c0 = p := Hcparj c0 Hmem0.
      have Hmem0a : c0 ∈ all_cells types
        by (rewrite (all_cells_lookup _ _ _ Htsj); apply elem_of_app; by left).
      have HcR'cells : cR' ∈ cellsj2.
      { have HcR'm := HcR'mem. apply all_cells_elem_of in HcR'm.
        destruct HcR'm as (p0 & ts0 & Hp0 & Hcts0).
        have Hpar0 : ic_parent cR' = p0 := Hparall2 p0 ts0 cR' Hp0 Hcts0.
        have Hpeq : p0 = p by rewrite -Hpar0 HcR'par HparR0.
        rewrite Hpeq in Hp0.
        have Hts0eq : ts0 = MkTypeState cellsj2 arrj by congruence.
        rewrite Hts0eq /= in Hcts0. exact Hcts0. }
      destruct (list_elem_of_lookup_1 _ _ HcR'cells) as [ciR Hciw].
      have Hwf' : run_wf (ic_run cR') := Hrunwfall2 cR' HcR'mem.
      have Hlen1 : (1 <= length (ic_run cR'))%nat.
      { destruct (ic_run cR') eqn:Hrc; [exact (False_ind _ (proj1 Hwf' eq_refl)) | simpl; lia]. }
      have HbR' := Hbnds2 cR' HcR'mem.
      have Hzck : (uint.Z (cell_clock cR') = Z.of_nat (clock (item_id (run_head cR'))))%Z
        by (rewrite /cell_clock; destruct HbR'; word).
      have Hpin : (clock (item_id (run_head cR')) = clock originIdRight)%nat.
      { move: HcR'clk. rewrite Hzck. lia. }
      have HclR' : clientId (item_id (run_head cR')) = clientId originIdRight.
      { have Hb1 := proj1 (Hbnds2 cR' HcR'mem).
        have Hb2 := proj1 (Hbnds0 c0 Hmem0a).
        move: HcR'cl. rewrite /cell_client -Hclw. move=> Hcc.
        have Hz : uint.Z (W64 (clientId (item_id (run_head cR'))))
                = uint.Z (W64 (clientId (item_id (run_head c0)))) by rewrite Hcc.
        word. }
      destruct (lookup_lt_is_Some_2 (ic_run cR') 0%nat ltac:(lia)) as [chR HchR].
      have HidchR : item_id chR = originIdRight.
      { rewrite (run_wf_char_id _ _ _ Hwf' HchR).
        rewrite /run_head in Hpin.
        destruct originIdRight as [oc ok].
        have Hpin' : (item_id (hd inhabitant (ic_run cR'))).(clock) = ok := Hpin.
        f_equal; [exact HclR' | lia]. }
      have HposR := run_flatten_lookup_of_cell cellsj2 ciR _ cR' chR Hciw HchR.
      rewrite -Hreprj' in HposR.
      destruct (findRightIdx_inv originIdRight arrj rightIdx HfindR3) as (knR & itR & HeqR & HknR & HidR2).
      have HknRp : knR = (length (run_flatten (take ciR cellsj2)) + 0)%nat.
      { set posR := (length (run_flatten (take ciR cellsj2)) + 0)%nat in HposR |- *.
        destruct (Nat.lt_trichotomy knR posR) as [Hlt2 | [Heq2 | Hgt2]]; [| exact Heq2 |]; exfalso.
        - have := uniqueId_lookup_ne arrj knR posR itR chR Huniqj HknR HposR Hlt2.
          rewrite HidR2 HidchR //.
        - have := uniqueId_lookup_ne arrj posR knR chR itR Huniqj HposR HknR Hgt2.
          rewrite HidR2 HidchR //. }
      exists ciR. split_and!.
      + apply lookup_lt_Some in Hciw. lia.
      + lia.
      + rewrite /node_loc decide_True; last lia.
        rewrite Nat2Z.id Hciw /= HcR'loc //.
    - move=> Hrgtnull _ _ HfindR3.
      move: HfindR3. rewrite /findRightIdx. move=> [= <-].
      exists (length cellsj2). split_and!.
      + lia.
      + rewrite take_ge; last lia. rewrite -Hreprj'. lia.
      + rewrite Hrgtnull /node_loc. case_decide; [| lia].
        rewrite Nat2Z.id lookup_ge_None_2 //. }
  iDestruct (linked_item_run_fresh2 with "Hlinked Htypes") as %Hfreshloc.
  iDestruct (types_repr_all2 with "Htypes") as %Hreprallj.
  wp_auto.
  have Hidnit : item_id newItem = in_id input := commutativity.toItem_id input arrj newItem Htoit.
  have Hgmaxj : ∀ c0, c0 ∈ all_cells types2 → cell_client c0 = W64 (clientId (item_id newItem)) →
                  (uint.Z (cell_clock c0) < uint.Z (W64 (clock (item_id newItem))))%Z ∧
                  (uint.Z (cell_clock c0) + Z.of_nat (length (ic_run c0)) <= uint.Z (W64 (clock (item_id newItem))))%Z.
  { intros c0 Hc0 Hcc0. rewrite Hidnit in Hcc0 |- *.
    exact (Hbndj2 c0 Hc0 Hcc0). }
  iDestruct (big_sepM_delete _ _ p _ Htsj2 with "Htypes") as "[[Hyt _] Htypesrest]".
  have Hfitscj : ∀ c0, c0 ∈ cellsj2 -> cell_fits c0.
  { move=> c0 Hc0. apply Hfits2.
    rewrite (all_cells_lookup _ _ _ Htsj2). apply elem_of_app. by left. }
  have Hoclkcj : ∀ c0, c0 ∈ cellsj2 -> cell_origin_clk c0.
  { move=> c0 Hc0. apply Horiginclk2.
    rewrite (all_cells_lookup _ _ _ Htsj2). apply elem_of_app. by left. }
  have Hreprj2 : cells_repr arrj cellsj2 arrj := Hreprallj p _ Htsj2.
  have Hnecj2 : Forall (λ c, ic_run c ≠ []) cellsj2.
  { apply Forall_forall. move=> c Hc.
    have Hwf : run_wf (ic_run c).
    { apply Hrunwfall2. rewrite (all_cells_lookup _ _ _ Htsj2). apply elem_of_app. by left. }
    exact (proj1 Hwf). }
  destruct HcurLpack as (curL2 & HcurL2b & HcurL2 & HlftND).
  destruct HcurRpack as (curR2 & HcurR2b & HcurR2 & HrgtND).
  iEval (rewrite HlftND HrgtND) in "Hlinked".
  wp_apply (wp_Store__Integrate_nil_run s p itv arrj arr2 input newItem cellsj2 types2 mref leftIdx rightIdx
              curL2 curR2
              Hinvj Htoit Hvld Hmax HfindL HfindR Htsj2 Hgmaxj Hnecj2 Hfitscj Hoclkcj
              HcurL2 HcurL2b HcurR2 HcurR2b Hall
              with "[$Hyt $Hlinked $Hitemsf $Hitemmap]").
  iIntros (idx2 iidx2 cells'' c2)
    "(%Hinv2 & Htext2 & Hitemsf & Hitemmap & %Hperm2 & %Hsplice2 & %Hidx2b & %Hcoup2 & %Hile2 & %Harrsp2 & %Hc2look & %Hc2loc & %Hc2id & %Hc2del & %Hc2orig & %Hc2rorig & %Hc2len)".
  have Hac_step : all_cells (<[p := MkTypeState cells'' arr2]> types2)
                ≡ₚ all_cells types2 ++ [c2]
    by apply (all_cells_insert_snoc types2 p cellsj2 arrj cells'' arr2 c2 Htsj2 Hperm2).
  have Hcc2 : cell_client c2 = W64 (clientId (in_id input))
    by rewrite /cell_client Hc2id //.
  have Hclk2 : cell_clock c2 = W64 (clock (in_id input))
    by rewrite /cell_clock Hc2id //.
  have Hlocdup' : NoDup (ic_loc <$> all_cells (<[p := MkTypeState cells'' arr2]> types2)).
  { apply (nodup_locs_snoc (all_cells types2) _ c2 Hac_step);
      [rewrite Hc2loc; exact Hfreshloc | exact Hnodup2]. }
  have Hrangedisj' : cells_range_disjoint (all_cells (<[p := MkTypeState cells'' arr2]> types2)).
  { apply (rangedisj_snoc (all_cells types2) _ c2 Hac_step); [| exact Hrangedisj2].
    move=> c0 Hc0 Hcc0.
    have Hccnit : cell_client c0 = W64 (clientId (item_id newItem)).
    { rewrite Hcc0 Hcc2 Hidnit //. }
    have Hle := proj2 (Hgmaxj c0 Hc0 Hccnit).
    rewrite Hidnit in Hle.
    rewrite Hclk2. clear -Hle. lia. }
  have Horiginclk' : ∀ c0, c0 ∈ all_cells (<[p := MkTypeState cells'' arr2]> types2) ->
      cell_origin_clk c0.
  { apply (originclk_snoc (all_cells types2) _ c2 Hac_step); [| exact Horiginclk2].
    move=> originId Hoid Hcl.
    rewrite Hc2orig in Hoid.
    rewrite Hc2id -Hidnit in Hcl.
    rewrite Hc2id -Hidnit.
    rewrite (in_originId_origin_id arrj newItem input Htoit) in Hoid.
    have [o0 [r0 [id0 [c0x [Hnitdef [HoLp [_ [_ _]]]]]]]]
      := proj1 (toItem_ok_iff input arrj newItem) Htoit.
    rewrite Hoid /isLeftIdPtr in HoLp.
    destruct HoLp as (x & Ho & Hfind).
    have Hxid : item_id x = originId by apply (find_by_id_id originId arrj x Hfind).
    have Hxmem : x ∈ arrj by apply (find_by_id_mem originId arrj x Hfind).
    have Hxmem2 := Hxmem. rewrite Hreprj' in Hxmem2.
    apply list_elem_of_lookup_1 in Hxmem2 as [kx Hkx].
    destruct (run_flatten_lookup_cell cellsj2 kx x Hkx) as (cix & offx & c0' & Hcix & Hoffx & _).
    have Hc0'mem : c0' ∈ cellsj2 := list_elem_of_lookup_2 _ _ _ Hcix.
    have Hc0'all : c0' ∈ all_cells types2.
    { rewrite (all_cells_lookup _ _ _ Htsj2). apply elem_of_app. by left. }
    have Hwfx : run_wf (ic_run c0') := Hrunwfall2 c0' Hc0'all.
    have Hxid2 := run_wf_char_id _ _ _ Hwfx Hoffx.
    have Hoffb := lookup_lt_Some _ _ _ Hoffx.
    have Hcl' : cell_client c0' = W64 (clientId (in_id input)).
    { rewrite /cell_client /run_head.
      have Hclx : clientId (item_id x) = clientId (item_id (hd inhabitant (ic_run c0')))
        by rewrite Hxid2 //.
      rewrite -Hclx Hxid Hcl Hidnit //. }
    have Hbnd := proj2 (Hbndj2 c0' Hc0'all Hcl').
    have Hclkx : clock originId = (clock (item_id (hd inhabitant (ic_run c0'))) + offx)%nat
      by rewrite -Hxid Hxid2 //.
    have [_ Hkb] := Hbnds2 c0' Hc0'all.
    have Hzc0 : (uint.Z (cell_clock c0') = Z.of_nat (clock (item_id (run_head c0'))))%Z
      by (rewrite /cell_clock; word).
    rewrite /run_head in Hzc0.
    have Hb : uint.Z (W64 (clock (in_id input))) = Z.of_nat (clock (in_id input))
      := uint_W64_nat_bound (clock (in_id input)) (length (in_content input)) Hnowrapc.
    rewrite Hb in Hbnd.
    rewrite Hidnit. lia. }
  iAssert ([∗ map] p0 ↦ ts ∈ <[p := MkTypeState cells'' arr2]> types2,
      own_ytype_cells p0 (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
      ⌜YjsArrInvariant (ty_arr ts)⌝)%I
    with "[Htext2 Htypesrest]" as "Htypes".
  { rewrite -insert_delete_eq.
    rewrite big_sepM_insert; last apply lookup_delete_eq.
    iFrame "Htypesrest". simpl. iFrame "Htext2".
    iPureIntro. exact Hinv2. }
  wp_auto.
  iApply ("HΦ" $! (<[p := MkTypeState cells'' arr2]> types2)).
  iFrame "Hitemsf Hitemmap Htypesf Htypesmap Htypes".
  iPureIntro. split_and!.
  - (* dom eq *)
    have Hdomeq2 : dom types2 = dom types.
    { apply set_eq => p0. rewrite !elem_of_dom. split.
      - move=> [ts0 Hp0]. destruct (Hpres2 p0 ts0 Hp0) as (tsold & Hpold & _). eauto.
      - move=> Hp0. exact (Hdom2 p0 Hp0). }
    rewrite dom_insert_lookup_L; [rewrite Hdomeq2; reflexivity | eauto].
  - (* per-name coherence at <[RootId nm := arr2]> m *)
    move=> nm0 p0 ts Hbnm0.
    destruct (decide (p0 = p)) as [-> | Hne].
    + have Hnm0 : nm0 = nm := Hbindinj nm0 nm p Hbnm0 Hbnm.
      subst nm0. rewrite lookup_insert_eq. move=> [= <-].
      rewrite docm_get_insert_eq //.
    + rewrite lookup_insert_ne; last congruence.
      move=> Hts.
      have Hnenm : RootId nm0 ≠ RootId nm.
      { move=> [= Heqnm]. subst nm0. apply Hne.
        have : Some p0 = Some p by rewrite -Hbnm0 -Hbnm //.
        by move=> [=]. }
      rewrite docm_get_insert_ne //.
      destruct (Hpres2 p0 ts Hts) as (tsold & Hpold & Harrp & _).
      rewrite Harrp.
      exact (Hmtypes nm0 p0 tsold Hbnm0 Hpold).
  - (* provenance: old cell (transported) or the new cell *)
    move=> c0 Hc0.
    rewrite Hac_step in Hc0. apply elem_of_app in Hc0 as [Hold | Hnew].
    + destruct (Hsub2 c0 Hold) as (cold & Hcold & Hcl & Hlo & Hhi).
      left. exists cold. split_and!; [exact Hcold | congruence | lia | lia].
    + apply list_elem_of_singleton in Hnew as ->.
      have Hlen2 : length (ic_run c2) = length (in_content input) by rewrite Hc2len explode_length.
      right. split_and!.
      * exact Hcc2.
      * rewrite Hclk2. lia.
      * rewrite Hclk2 Hlen2. lia.
  - exact Hlocdup'.
  - exact Hrangedisj'.
  - (* fits for the grown pool *)
    move=> c0 Hc0.
    rewrite Hac_step in Hc0. apply elem_of_app in Hc0 as [Hold | Hnew].
    + exact (Hfits2 c0 Hold).
    + apply list_elem_of_singleton in Hnew as ->.
      have Hlen2 : length (ic_run c2) = length (in_content input) by rewrite Hc2len explode_length.
      rewrite /cell_fits Hclk2 Hlen2.
      exact (uint_W64_nat_add_bound (clock (in_id input)) (length (in_content input)) Hnowrapc).
  - exact Horiginclk'.
Qed.

(* ===== the total applyUpdate loop (issue #40) ============================= *)

(** A [toItem] success with a present origin resolved that origin inside the
    target array, so the array is nonempty. This is how the drain derives the
    target root's binding for origin-carrying structs: a nonempty model entry
    is a registered root by [Hmdom] (origin-less structs instead carry a
    [pending_item_rooted]-style witness). *)
Lemma toItem_nonempty_of_origin (input : IntegrateInput (A := A))
    (arr : list (YjsItem A)) (newItem : YjsItem A) :
  toItem input arr = Some newItem ->
  in_originId input ≠ None ∨ in_rightOriginId input ≠ None ->
  arr ≠ [].
Proof.
  move=> Htoit Hor Heq. subst arr.
  have [o [r [idx [cx [_ [HoL [HoR _]]]]]]] :=
    proj1 (toItem_ok_iff input [] newItem) Htoit.
  destruct Hor as [Ho | Ho].
  - destruct (in_originId input) as [originId|]; last by apply Ho.
    destruct HoL as (it & _ & Hf).
    rewrite /find_by_id /= in Hf. discriminate.
  - destruct (in_rightOriginId input) as [originId|]; last by apply Ho.
    destruct HoR as (it & _ & Hf).
    rewrite /find_by_id /= in Hf. discriminate.
Qed.


(* ===== wire-level drain (issue #40 x issue #28 U7c) =======================
   The Go [applyUpdate] loop drains WIRE items (whole [updateItem] structs),
   integrating each ready one as ONE run cell -- a whole [expand_input] chunk of
   [integrate_all]. [wire_pass] / [wire_drain] mirror the per-char [pending_pass]
   / [pending_drain] ([yjs_network_model]) but step by [integrate_all] over a
   wire item's ops, so the drain loop refines them 1:1. The bridge to the
   per-char model (for the certificate [ValidReplay]) is
   [WireReplay_to_PendingReplay] in [yjs_store_update]: it turns a [WireReplay]
   into a [PendingReplay] of the [expand_inputs], re-deriving each chunk's
   freshness from head-freshness via [delivered_clock_bound]. Reuses
   [pending_keep] / [doc_model_has] / [input_ready] (a wire item's readiness is its
   head op's, since [typedInput.2]'s origins are the head's). *)

Definition wire_integrate (m : DocModel) (typedInput : TId * IntegrateInput (A := A))
    : option (list (YjsItem A)) :=
  integrate_all (ops_of_input typedInput.2 (explode (in_content typedInput.2))) (doc_model_get m typedInput.1).

Fixpoint wire_pass (m : DocModel) (pending kept : list (TId * IntegrateInput (A := A)))
    : list (TId * IntegrateInput (A := A)) * list (TId * IntegrateInput (A := A)) * DocModel :=
  match pending with
  | [] => ([], kept, m)
  | typedInput :: tl =>
      if doc_model_has m (in_id typedInput.2) then wire_pass m tl kept
      else if input_ready m typedInput.2 then
        match wire_integrate m typedInput with
        | Some arr' =>
            let '(app, kept', m') := wire_pass (<[typedInput.1 := arr']> m) tl kept in
            (typedInput :: app, kept', m')
        | None => wire_pass m tl (pending_keep kept typedInput)
        end
      else wire_pass m tl (pending_keep kept typedInput)
  end.

Fixpoint wire_drain_aux (fuel : nat) (m : DocModel)
    (pending : list (TId * IntegrateInput (A := A)))
    : list (TId * IntegrateInput (A := A)) * list (TId * IntegrateInput (A := A)) * DocModel :=
  match fuel with
  | 0%nat => ([], pending, m)
  | S f =>
      let '(app, kept, m') := wire_pass m pending [] in
      match app with
      | [] => ([], kept, m')
      | _ :: _ =>
          let '(app2, rest, m'') := wire_drain_aux f m' kept in
          (app ++ app2, rest, m'')
      end
  end.

Definition wire_drain (m : DocModel) (pending : list (TId * IntegrateInput (A := A)))
    : list (TId * IntegrateInput (A := A)) * list (TId * IntegrateInput (A := A)) * DocModel :=
  wire_drain_aux (S (length pending)) m pending.

Lemma wire_pass_kept_le (pending : list (TId * IntegrateInput (A := A))) :
  ∀ m kept app kept' m',
    wire_pass m pending kept = (app, kept', m') ->
    (length kept' + length app <= length kept + length pending)%nat.
Proof.
  elim: pending => [| typedInput tl IH] m kept app kept' m'.
  - move=> [= <- <- _] /=. lia.
  - have Hcl : length (typedInput :: tl) = S (length tl) by done.
    simpl. destruct (doc_model_has m (in_id typedInput.2)).
    { move=> Hwp. have Hle := IH _ _ _ _ _ Hwp. lia. }
    destruct (input_ready m typedInput.2); last first.
    { move=> Hwp. have Hle := IH _ _ _ _ _ Hwp.
      have Hkl : (length (pending_keep kept typedInput) <= S (length kept))%nat by apply pending_keep_length. lia. }
    destruct (wire_integrate m typedInput) as [arr' |]; last first.
    { move=> Hwp. have Hle := IH _ _ _ _ _ Hwp.
      have Hkl : (length (pending_keep kept typedInput) <= S (length kept))%nat by apply pending_keep_length. lia. }
    destruct (wire_pass (<[typedInput.1 := arr']> m) tl kept) as [[app0 kept0] m0] eqn:Hrec.
    move=> [= <- <- _]. have Hle := IH _ _ _ _ _ Hrec. simpl. lia.
Qed.

Lemma wire_pass_kept_lt (pending app kept' : list (TId * IntegrateInput (A := A)))
    (m m' : DocModel) :
  wire_pass m pending [] = (app, kept', m') ->
  app ≠ [] ->
  (length kept' < length pending)%nat.
Proof.
  move=> Hpass Hne.
  move: (wire_pass_kept_le pending m [] app kept' m' Hpass) => /=.
  destruct app; [done | simpl; lia].
Qed.

Lemma wire_drain_aux_fuel_agree (f1 : nat) :
  ∀ (f2 : nat) (m : DocModel) (pending : list (TId * IntegrateInput (A := A))),
    (length pending < f1)%nat -> (length pending < f2)%nat ->
    wire_drain_aux f1 m pending = wire_drain_aux f2 m pending.
Proof.
  elim: f1 => [| f1 IH] f2 m pending Hlt1 Hlt2; first lia.
  destruct f2 as [| f2]; first lia.
  simpl.
  destruct (wire_pass m pending []) as [[app kept] m'] eqn:Hpass.
  destruct app as [| a app0]; first done.
  have Hklt : (length kept < length pending)%nat
    by exact (wire_pass_kept_lt pending (a :: app0) kept m m' Hpass ltac:(done)).
  rewrite (IH f2 m' kept ltac:(lia) ltac:(lia)) //.
Qed.

Lemma wire_drain_aux_fuel_ge (fuel : nat) (m : DocModel)
    (pending : list (TId * IntegrateInput (A := A))) :
  (length pending < fuel)%nat ->
  wire_drain_aux fuel m pending = wire_drain_aux (S (length pending)) m pending.
Proof.
  move=> Hlt. exact (wire_drain_aux_fuel_agree fuel (S (length pending)) m pending Hlt ltac:(lia)).
Qed.

Lemma wire_drain_unfold (m : DocModel) (pending : list (TId * IntegrateInput (A := A))) :
  wire_drain m pending =
    let '(app, kept, m') := wire_pass m pending [] in
    match app with
    | [] => ([], kept, m')
    | _ :: _ =>
        let '(app2, rest, m'') := wire_drain m' kept in (app ++ app2, rest, m'')
    end.
Proof.
  rewrite {1}/wire_drain /=.
  destruct (wire_pass m pending []) as [[app kept] m'] eqn:Hpass.
  destruct app as [| a app0]; first done.
  have Hklt : (length kept < length pending)%nat
    by exact (wire_pass_kept_lt pending (a :: app0) kept m m' Hpass ltac:(done)).
  rewrite (wire_drain_aux_fuel_ge (length pending) m' kept Hklt) //.
Qed.

Lemma wire_pass_no_progress (pending : list (TId * IntegrateInput (A := A))) :
  ∀ m kept kept' m',
    wire_pass m pending kept = ([], kept', m') ->
    m' = m.
Proof.
  elim: pending => [| typedInput tl IH] m kept kept' m' /=.
  - move=> [= _ <-] //.
  - destruct (doc_model_has m (in_id typedInput.2)).
    { move=> /IH //. }
    destruct (input_ready m typedInput.2); last first.
    { move=> /IH //. }
    destruct (wire_integrate m typedInput) as [arr' |]; last first.
    { move=> /IH //. }
    destruct (wire_pass (<[typedInput.1 := arr']> m) tl kept) as [[app0 kept0] m0] eqn:Hrec.
    move=> [= Happ _ _]. discriminate.
Qed.

Lemma wire_drain_step_nil (m : DocModel)
    (pending kept : list (TId * IntegrateInput (A := A))) (m1 : DocModel) :
  wire_pass m pending [] = ([], kept, m1) ->
  wire_drain m pending = ([], kept, m1).
Proof. move=> Hpass. rewrite wire_drain_unfold Hpass //. Qed.

Lemma wire_drain_step_cons (m : DocModel)
    (pending : list (TId * IntegrateInput (A := A)))
    (a : TId * IntegrateInput (A := A))
    (app kept app2 rest2 : list (TId * IntegrateInput (A := A))) (m1 m2 : DocModel) :
  wire_pass m pending [] = (a :: app, kept, m1) ->
  wire_drain m1 kept = (app2, rest2, m2) ->
  wire_drain m pending = ((a :: app) ++ app2, rest2, m2).
Proof. move=> Hpass Hdrec. rewrite wire_drain_unfold Hpass Hdrec //. Qed.

(** The wire-level replay view of a drain: each applied wire item was fresh and
    ready and its whole op chunk integrated ([wire_integrate]). Mirrors
    [PendingReplay] with [integrate] replaced by [wire_integrate]. *)
Inductive WireReplay : DocModel -> list (TId * IntegrateInput (A := A)) -> DocModel -> Prop :=
  | WireReplay_nil m : WireReplay m [] m
  | WireReplay_cons m typedInput arr' rest m' :
      doc_model_has m (in_id typedInput.2) = false ->
      input_ready m typedInput.2 = true ->
      wire_integrate m typedInput = Some arr' ->
      WireReplay (<[typedInput.1 := arr']> m) rest m' ->
      WireReplay m (typedInput :: rest) m'.

Lemma WireReplay_app (m m1 m2 : DocModel)
    (a1 a2 : list (TId * IntegrateInput (A := A))) :
  WireReplay m a1 m1 -> WireReplay m1 a2 m2 -> WireReplay m (a1 ++ a2) m2.
Proof.
  move=> H1. elim: H1 a2 m2 => [m0 | m0 typedInput arr' rest m0' Hdup Hready Hint Hrest IH] a2 m2 H2 /=.
  - exact H2.
  - apply (WireReplay_cons m0 typedInput arr' (rest ++ a2) m2 Hdup Hready Hint).
    exact (IH a2 m2 H2).
Qed.

Lemma wire_pass_replay (pending : list (TId * IntegrateInput (A := A))) :
  ∀ m kept app kept' m',
    wire_pass m pending kept = (app, kept', m') ->
    WireReplay m app m'.
Proof.
  elim: pending => [| typedInput tl IH] m kept app kept' m' /=.
  - move=> [= <- _ <-]. constructor.
  - destruct (doc_model_has m (in_id typedInput.2)) eqn:Hdup.
    { move=> /IH //. }
    destruct (input_ready m typedInput.2) eqn:Hready; last first.
    { move=> /IH //. }
    destruct (wire_integrate m typedInput) as [arr' |] eqn:Hint; last first.
    { move=> /IH //. }
    destruct (wire_pass (<[typedInput.1 := arr']> m) tl kept) as [[app0 kept0] m0] eqn:Hrec.
    move=> [= <- _ <-].
    exact (WireReplay_cons m typedInput arr' app0 m0 Hdup Hready Hint (IH _ _ _ _ _ Hrec)).
Qed.

(** [wire_ready_total]: along the wire drain, a fresh, ready pending wire item
    always integrates its whole chunk (the exclusion of the ready-but-stuck
    branch: the Go loop integrates on [depsArrived], so its applied set is the
    ready set, which coincides with [wire_pass]'s only when this holds). The
    certificate layer supplies it (a ready certified chunk always folds). *)
Definition wire_ready_total (m : DocModel)
    (pending applied : list (TId * IntegrateInput (A := A))) : Prop :=
  ∀ pre suf mx (typedInput : TId * IntegrateInput (A := A)),
    applied = pre ++ suf -> WireReplay m pre mx ->
    typedInput ∈ pending ->
    doc_model_has mx (in_id typedInput.2) = false ->
    input_ready mx typedInput.2 = true ->
    is_Some (wire_integrate mx typedInput).

End store_update.
