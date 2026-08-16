(** The [store] VALUE layer, part 4: ID RANGES, WIRE SPANS and the by-id
    search. Independent of the cell bookkeeping; it only needs the [item]
    layer.

    Definitions
    - [range_ids] / [range_no_overflow]: the ids a clock range denotes and the
      [w64] honesty of its end, the one notion of "a range of ids" in the
      store.
    - its two runtime carriers: [span_ids] / [span_no_overflow] for the
      conflict scan's [idSpan], and the pure wire record [delete_span] with
      [delete_span_of_val] / [delete_span_ids] / [delete_batch_ids] /
      [delete_span_no_overflow] for the wire's [deleteSpan].
    - [cell_has_id] / [findById_res], the by-id search, and [cell_covers]: the
      model id [d] addresses a char of cell [c]'s run.

    Laws
    - [span_ids] is exactly the clock-interval test ([span_ids_elem] at the
      heap level, [range_ids_elem] / [span_ids_elem_nat] at the model level),
      is the singleton on a length-1 span, splits at any interior point
      ([span_ids_split]), and matches a run's char ids ([span_ids_char_ids]).
    - a batch covers each of its spans ([delete_span_ids_subseteq_batch]) and
      is monotone in them ([delete_batch_ids_mono]).

    The rest of the value layer: [store/value_cells.v], [store/value_live.v],
    [store/value_split.v]. *)

From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core prelude network_model.
From iris.algebra Require Import auth gmap gset.
From stdpp Require Import sorting.
Local Open Scope Z_scope.
From New.proof.store Require Import model.
From New.proof.id Require Import value heap.
From New.proof.item Require Import run_theory model value heap.
From New.proof.ytype Require Import model value heap.

Section store_value_span.

Set Default Proof Using "Type*".

Notation A := go_string.

Notation P := go_string.

Local Notation TId := (TypeId P).

Local Notation Op := (TId * @YjsOperation A)%type.

Local Notation Ev := (@Event Op).

Local Notation DocModel := (gmap TId (list (YjsItem A))).

(* ===== definitions ======================================================== *)

(** [cell_covers c d]: the model id [d] addresses a char of cell [c]'s run
    (issue #28 U7c): same client as the run head, and clock inside the run's
    range [head clock, head clock + run length). The per-char [run_wf] id law
    ([run_wf_char_id]) makes this exactly "[d] is the id of some [ic_run c]
    char". Replaces the all-singleton head-only [item_id (run_head c) = d]. *)
Definition cell_covers (c : item_cell) (d : YjsId) : Prop :=
  clientId (item_id (run_head c)) = clientId d ∧
  (clock (item_id (run_head c)) <= clock d)%nat ∧
  (clock d < clock (item_id (run_head c)) + length (ic_run c))%nat.

(* ===== wire-level drain (issue #40 x issue #28 U7c) =======================
   The Go [applyUpdate] loop drains WIRE items (whole [updateItem] structs),
   integrating each ready one as ONE run cell -- a whole [expand_input] chunk of
   [integrate_all]. [wire_pass] / [wire_drain] mirror the per-char [pending_pass]
   / [pending_drain] ([network_model]) but step by [integrate_all] over a
   wire item's ops, so the drain loop refines them 1:1. The bridge to the
   per-char model (for the certificate [ValidReplay]) is
   [WireReplay_to_PendingReplay] in [store/applyUpdate]: it turns a [WireReplay]
   into a [PendingReplay] of the [expand_inputs], re-deriving each chunk's
   freshness from head-freshness via [delivered_clock_bound]. Reuses
   [pending_keep] / [doc_model_has] / [input_ready] (a wire item's readiness is its
   head op's, since [typedInput.2]'s origins are the head's). *)

(* ----- id-span-slice abstraction to a gset ------------------------------ *)

(** The ids a CLOCK RANGE denotes: [len] consecutive clocks of [client]'s
    space starting at [start].

    Used as: the one notion of "a range of ids" in the store. Every runtime
    record that carries such a range is a thin layer over it ([span_ids] for
    the conflict scan's [idSpan], [delete_span_ids] for the wire's
    [deleteSpan]), and a spec that has the three words in hand states itself
    over this directly rather than assembling a heap record just to name a
    set ([wp_store__deleteRange], whose arguments are the three words). *)
Definition range_ids (client start len : w64) : gset YjsId :=
  list_to_set
    ((λ o, MkYjsId (uint.nat client) (uint.nat start + o)%nat)
       <$> seq 0 (uint.nat len)).

(** The range's end [start + len] does not OVERFLOW [w64].

    Used as: the side condition under which the Go tests agree with
    [range_ids], since they compute that sum in machine arithmetic
    ([containsId]'s range test, [deleteRange]'s loop bound). [span_no_overflow]
    and [delete_span_no_overflow] are its two runtime-record forms.

    A range that overflows is a broken request, not a smaller one: the wire
    carries the three words unchecked, so a peer can send one, and the Go
    tests then read the wrapped sum and agree with nothing. Rather than
    pretend, every statement about what a delete covered is GUARDED by this,
    so an overflowing span is claimed to do nothing, which is also what the
    loop does (its bound fails on the first iteration). *)
Definition range_no_overflow (start len : w64) : Prop :=
  (uint.Z start + uint.Z len < 2^64)%Z.

#[global] Instance range_no_overflow_dec start len : Decision (range_no_overflow start len).
Proof. rewrite /range_no_overflow. apply _. Defined.

(** The two runtime carriers, as the ranges they denote. *)
Definition span_ids (v : yjs.idSpan.t) : gset YjsId :=
  range_ids v.(yjs.idSpan.id').(yjs.id.clientId')
            v.(yjs.idSpan.id').(yjs.id.clock')
            v.(yjs.idSpan.len').

(** A WIRE delete span, as a PURE value: the three machine words the format
    carries, with no goose record in sight. Specs quantify over this, never
    over [yjs.deleteSpan.t], so that a caller reasoning about a delete batch
    never has to know the layout of a decoded struct.

    The fields stay [w64] rather than [nat] on purpose: overflow is a property
    of the 64-bit encoding, and [delete_span_no_overflow] is exactly what
    guards every statement about what a delete covered. Widening to [nat]
    would push that condition back onto the runtime records and undo the
    separation. *)
Record delete_span := MkDeleteSpan {
  delete_span_client : w64;
  delete_span_start : w64;
  delete_span_length : w64;
}.

#[global] Instance delete_span_eq_dec : EqDecision delete_span.
Proof. solve_decision. Defined.

(** What a decoded struct denotes. Injective, since it only renames fields,
    which is what lets a statement about the pure spans transport to the
    records the loop actually walks. *)
Definition delete_span_of_val (v : yjs.deleteSpan.t) : delete_span :=
  MkDeleteSpan v.(yjs.deleteSpan.client') v.(yjs.deleteSpan.clock')
               v.(yjs.deleteSpan.length').

#[global] Instance delete_span_of_val_inj : Inj (=) (=) delete_span_of_val.
Proof.
  move=> [c1 k1 l1] [c2 k2 l2] [= -> -> ->]. reflexivity.
Qed.

(** The ids a span denotes: its whole clock interval. The batch is their
    union, which is the right model because deletes are STATE, not operations:
    a batch means exactly the set of ids it tombstones, with no order and no
    multiplicity, so two batches with the same union are the same request.

    Used as: the pure model a public spec speaks about ([own_delete_ids],
    [codec_spec], [wp_Doc__ApplySyncUpdate]) and the currency of
    [wp_store__applyDeleteSpans]'s coverage report. *)
Definition delete_span_ids (sp : delete_span) : gset YjsId :=
  range_ids sp.(delete_span_client) sp.(delete_span_start) sp.(delete_span_length).

Definition delete_batch_ids (spans : list delete_span) : gset YjsId :=
  ⋃ (delete_span_ids <$> spans).

(** The [delete_span] form of [range_no_overflow]. *)
Definition delete_span_no_overflow (sp : delete_span) : Prop :=
  range_no_overflow sp.(delete_span_start) sp.(delete_span_length).

#[global] Instance delete_span_no_overflow_dec sp : Decision (delete_span_no_overflow sp).
Proof. rewrite /delete_span_no_overflow. apply _. Defined.

(** The [idSpan] form of [range_no_overflow]: [containsId]'s Go range test
    computes [clock + len] in [w64], so this is what makes the test decide
    [span_ids] membership. Sourced from the store's run-fits pool invariant. *)
Definition span_no_overflow (v : yjs.idSpan.t) : Prop :=
  range_no_overflow v.(yjs.idSpan.id').(yjs.id.clock') v.(yjs.idSpan.len').

(* ----- findById: locate a node by id in the DLL ------------------------- *)

(** The cell predicate [findById] decides: a cell whose model id is [toYjsId idv].
    [findById] returns the first matching node's location, or [null]. *)
Definition cell_has_id (idv : yjs.id.t) (c : item_cell) : Prop :=
  item_id (run_head c) = toYjsId idv.

#[local] Instance cell_has_id_dec idv c : Decision (cell_has_id idv c).
Proof. rewrite /cell_has_id. apply _. Defined.

(** Result location of [findById] over a cell list: first match, else [null]. *)
Definition findById_res (cells : list item_cell) (idv : yjs.id.t) : loc :=
  match list_find (cell_has_id idv) cells with
  | Some (_, c) => ic_loc c
  | None => null
  end.

(* ===== lemmas ============================================================= *)

Lemma delete_span_ids_subseteq_batch (sp : delete_span) (spans : list delete_span) :
  sp ∈ spans -> delete_span_ids sp ⊆ delete_batch_ids spans.
Proof.
  move=> Hsp i Hi. rewrite /delete_batch_ids elem_of_union_list.
  exists (delete_span_ids sp). split; last exact Hi.
  apply list_elem_of_fmap. by exists sp.
Qed.

Lemma delete_batch_ids_mono (l1 l2 : list delete_span) :
  (∀ sp, sp ∈ l1 -> sp ∈ l2) -> delete_batch_ids l1 ⊆ delete_batch_ids l2.
Proof.
  move=> Hsub i. rewrite /delete_batch_ids !elem_of_union_list.
  move=> [X [HX Hi]]. apply list_elem_of_fmap in HX as (sp & -> & Hsp).
  exists (delete_span_ids sp). split; last exact Hi.
  apply list_elem_of_fmap. exists sp. split; [done | exact (Hsub sp Hsp)].
Qed.

(** Membership in [span_ids] is exactly the (mathematical) range test. *)
Lemma span_ids_elem (v : yjs.idSpan.t) (idv : yjs.id.t) :
  toYjsId idv ∈ span_ids v ↔
    (v.(yjs.idSpan.id').(yjs.id.clientId') = idv.(yjs.id.clientId') ∧
     (uint.Z v.(yjs.idSpan.id').(yjs.id.clock') ≤ uint.Z idv.(yjs.id.clock'))%Z ∧
     (uint.Z idv.(yjs.id.clock') <
        uint.Z v.(yjs.idSpan.id').(yjs.id.clock') + uint.Z v.(yjs.idSpan.len'))%Z).
Proof.
  have HZn : ∀ w : w64, Z.of_nat (uint.nat w) = uint.Z w by move=> w; word.
  rewrite /span_ids /range_ids elem_of_list_to_set list_elem_of_fmap /toYjsId.
  split.
  - move=> [o [Hid Ho]]. apply elem_of_seq in Ho.
    injection Hid => Hclk Hcid.
    split_and!.
    + word.
    + have := f_equal Z.of_nat Hclk. rewrite Nat2Z.inj_add !HZn. lia.
    + have := f_equal Z.of_nat Hclk. rewrite Nat2Z.inj_add !HZn.
      have : (Z.of_nat o < uint.Z v.(yjs.idSpan.len'))%Z by rewrite -(HZn v.(yjs.idSpan.len')); lia.
      lia.
  - move=> [Hcid [Hle Hlt]].
    exists (uint.nat idv.(yjs.id.clock') - uint.nat v.(yjs.idSpan.id').(yjs.id.clock'))%nat.
    have Hlen : (uint.nat idv.(yjs.id.clock') - uint.nat v.(yjs.idSpan.id').(yjs.id.clock')
                 < uint.nat v.(yjs.idSpan.len'))%nat.
    { have H1 := HZn idv.(yjs.id.clock'). have H2 := HZn v.(yjs.idSpan.id').(yjs.id.clock').
      have H3 := HZn v.(yjs.idSpan.len'). lia. }
    have Hge : (uint.nat v.(yjs.idSpan.id').(yjs.id.clock') <= uint.nat idv.(yjs.id.clock'))%nat.
    { have H1 := HZn idv.(yjs.id.clock'). have H2 := HZn v.(yjs.idSpan.id').(yjs.id.clock'). lia. }
    split.
    + f_equal; [by rewrite Hcid | lia].
    + apply elem_of_seq. lia.
Qed.

(** Membership in a range, at the [nat] level the model ids live at. *)
Lemma range_ids_elem (client start len : w64) (i : YjsId) :
  i ∈ range_ids client start len ↔
    (clientId i = uint.nat client ∧
     (uint.nat start <= clock i)%nat ∧
     (clock i < uint.nat start + uint.nat len)%nat).
Proof.
  rewrite /range_ids elem_of_list_to_set list_elem_of_fmap. split.
  - move=> [o [-> Ho]]. apply elem_of_seq in Ho. simpl. split_and!; [done | lia | lia].
  - move=> [Hcid [Hle Hlt]].
    exists (clock i - uint.nat start)%nat. split.
    + destruct i as [ci ki]. simpl in *. f_equal; [done | lia].
    + apply elem_of_seq. lia.
Qed.

(** The same test on the runtime carrier, for callers that hold a model id
    rather than a heap one. *)
Lemma span_ids_elem_nat (v : yjs.idSpan.t) (i : YjsId) :
  i ∈ span_ids v ↔
    (clientId i = uint.nat v.(yjs.idSpan.id').(yjs.id.clientId') ∧
     (uint.nat v.(yjs.idSpan.id').(yjs.id.clock') <= clock i)%nat ∧
     (clock i < uint.nat v.(yjs.idSpan.id').(yjs.id.clock')
                + uint.nat v.(yjs.idSpan.len'))%nat).
Proof. rewrite /span_ids range_ids_elem //. Qed.

(** A span splits at any interior point, which is how a delete loop grows its
    "covered so far" record one node at a time. The no-wrap premise is the
    same [w64] honesty the store's [cell_fits] provides. *)
Lemma span_ids_split (cl clk l1 l2 : w64) :
  (uint.Z clk + uint.Z l1 + uint.Z l2 < 2^64)%Z ->
  span_ids (yjs.idSpan.mk (yjs.id.mk cl clk) (word.add l1 l2))
  = span_ids (yjs.idSpan.mk (yjs.id.mk cl clk) l1)
    ∪ span_ids (yjs.idSpan.mk (yjs.id.mk cl (word.add clk l1)) l2).
Proof.
  move=> Hnw. apply set_eq => i.
  rewrite elem_of_union !span_ids_elem_nat /=.
  have Hs : uint.Z (word.add l1 l2) = uint.Z l1 + uint.Z l2 by word.
  have Hc : uint.Z (word.add clk l1) = uint.Z clk + uint.Z l1 by word.
  have Hn : ∀ w : w64, Z.of_nat (uint.nat w) = uint.Z w by move=> w; word.
  split.
  - move=> [Hcid [Hle Hlt]].
    destruct (decide (clock i < uint.nat clk + uint.nat l1)%nat) as [Hin | Hin].
    + left. split_and!; [exact Hcid | exact Hle | exact Hin].
    + right. split_and!; [exact Hcid | | ].
      * have := Hn clk. have := Hn l1. lia.
      * have := Hn clk. have := Hn l1. have := Hn l2. have := Hn (word.add l1 l2).
        have := Hn (word.add clk l1). lia.
  - move=> [[Hcid [Hle Hlt]] | [Hcid [Hle Hlt]]].
    + split_and!; [exact Hcid | exact Hle |].
      have := Hn clk. have := Hn l1. have := Hn l2. have := Hn (word.add l1 l2). lia.
    + split_and!; [exact Hcid | |].
      * have := Hn clk. have := Hn l1. have := Hn (word.add clk l1). lia.
      * have := Hn clk. have := Hn l1. have := Hn l2. have := Hn (word.add l1 l2).
        have := Hn (word.add clk l1). lia.
Qed.

(** A length-1 span denotes exactly its head id (the pre-#28 singleton case). *)
Lemma span_ids_singleton (v : yjs.idSpan.t) :
  v.(yjs.idSpan.len') = W64 1 ->
  span_ids v = {[ toYjsId v.(yjs.idSpan.id') ]}.
Proof.
  move=> Hlen. rewrite /span_ids /range_ids Hlen.
  have -> : uint.nat (W64 1) = 1%nat by word.
  rewrite /= Nat.add_0_r /toYjsId.
  by rewrite (right_id_L ∅ (∪)).
Qed.

(** Appending one span adds its char ids in accumulator order. *)
Lemma span_union_snoc (vs : list yjs.idSpan.t) (v : yjs.idSpan.t) :
  ⋃ (span_ids <$> (vs ++ [v])) = span_ids v ∪ ⋃ (span_ids <$> vs).
Proof.
  rewrite fmap_app union_list_app_L /= (right_id_L ∅ (∪)).
  apply union_comm_L.
Qed.

(* ----- span <-> run-char bridge (issue #28 M4, stage C1a) ---------------- *)

(** A scanned node's span denotes exactly its run's char ids: the run's chars
    sit at the head's client with consecutive clocks from the head
    ([run_step]), which is what [span_ids] enumerates. Pure nat arithmetic on
    both sides, so no no-wrap premise is needed here (the [w64] no-wrap only
    matters for [containsId]'s range test). *)
Lemma span_ids_char_ids (idv : yjs.id.t) (len : w64)
    (h : YjsItem A) (tail : list (YjsItem A)) :
  item_id h = toYjsId idv ->
  run_step (h :: tail) ->
  length (h :: tail) = uint.nat len ->
  span_ids (yjs.idSpan.mk idv len) = char_ids (h :: tail).
Proof.
  move=> Hid Hstep Hlen.
  have Heta : forall i : YjsId, i = MkYjsId (clientId i) (clock i) by move=> [] //.
  apply set_eq => x.
  rewrite /span_ids /range_ids /char_ids !elem_of_list_to_set !list_elem_of_fmap.
  split.
  - move=> [o [-> Ho]]. apply elem_of_seq in Ho. simpl in Ho.
    destruct o as [|k].
    + exists h. split; [| apply elem_of_cons; by left].
      rewrite Hid /toYjsId /= Nat.add_0_r //.
    + have Hk : (k < length tail)%nat by (simpl in Hlen; lia).
      destruct (lookup_lt_is_Some_2 tail k Hk) as [y Hy].
      exists y. split; [| apply elem_of_cons; right; by eapply list_elem_of_lookup_2].
      destruct (run_step_tail_ids h tail Hstep k y Hy) as [Hcl Hck].
      rewrite (Heta (item_id y)) Hcl Hck Hid /toYjsId /=.
      f_equal. lia.
  - move=> [y [-> Hy]]. apply elem_of_cons in Hy as [-> | Hy].
    + exists 0%nat. split.
      * rewrite Hid /toYjsId /= Nat.add_0_r //.
      * apply elem_of_seq. simpl. simpl in Hlen. lia.
    + apply list_elem_of_lookup_1 in Hy as [k Hk].
      have Hklt : (k < length tail)%nat by (eapply lookup_lt_Some; exact Hk).
      exists (S k). split.
      * destruct (run_step_tail_ids h tail Hstep k y Hk) as [Hcl Hck].
        rewrite (Heta (item_id y)) Hcl Hck Hid /toYjsId /=.
        f_equal. lia.
      * apply elem_of_seq. simpl. simpl in Hlen. lia.
Qed.

End store_value_span.
