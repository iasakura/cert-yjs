(** Common definitions shared across the cert-yjs proof modules.

    Split out of the original single-file invariant development so the
    per-module proof files ([yjs_item], [yjs_proof], [yjs_store], [yjs_text])
    can share one base layer:

    - scalar abstractions [toYjsId] / [toContent] (heap [w64] ids/content to
      the model);
    - the heap-node record [item_cell] and the cursor helper [node_loc];
    - the persistent origin-pointer predicate [is_origin_id];
    - the item-pointer helpers [oid_of] / [item_or_null];
    - the id-span-slice abstraction [own_id_set] (a heap [[]idSpan] as a
      [gset YjsId] of char ids, issue #28).

    Naming convention (issue #47): [is_X] predicates are Persistent (duplicable
    handles / read-only facts); [own_X] predicates are ownership, parameterized
    by a [dfrac] where the data is plain heap state ([DfracOwn 1] = exclusive /
    writable, [DfracDiscarded] = frozen read-only, fractions = shared reads).

    None of these depend on the item DLL spine or the heap<->model isomorphism,
    so every other module imports this one. The goose package-init instances
    live here too (declared once and inherited via [Require]). *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import yjs_core.
From New.proof Require Import yjs_run_theory.
(* The Go package now imports sync (store.mu : sync.Mutex), so the generated yjs
   package imports sync; building [IsPkgInit yjs] below needs [IsPkgInit sync]
   (and [GetIsPkgInitWf sync]) in scope, provided by the sync proof base. The
   required [sync.Assumptions] comes from [yjs.Assumptions] (its
   [import_sync_Assumption ::] field). *)
From New.proof.sync_proof Require Import base.

(* ===== Countable (YjsItem A) ============================================== *)

(** [YjsItem]/[YjsPtr] are mutually inductive, so [solve_decision]-style
    derivation can't break the cycle (rocq-yjs derives only [EqDecision] this
    way). We get [Countable] by encoding the item tree into stdpp's [gen_tree]
    (leaves carry an id or a content character) and back, with the round-trip
    proved by the mutual induction scheme [YjsItem_mut]. This is what lets the
    store's grow-only item-set ghost use [gset (YjsItem A)] (pinning each known
    item to a genuine document item), rather than the weaker [gset YjsId] (which
    only pins ids and cannot witness a subsequence/[sublist] lower bound). *)
Section item_countable.
Context {A : Type} `{Countable A}.

Notation leaf := (YjsId + A)%type.

Fixpoint YjsItem_enc (i : YjsItem A) : gen_tree leaf :=
  match i with
  | Item o r id c => GenNode 0 [YjsPtr_enc o; YjsPtr_enc r; GenLeaf (inl id); GenLeaf (inr c)]
  end
with YjsPtr_enc (p : YjsPtr A) : gen_tree leaf :=
  match p with
  | itemPtr i => GenNode 1 [YjsItem_enc i]
  | First => GenNode 2 []
  | Last => GenNode 3 []
  end.

Fixpoint YjsItem_dec (t : gen_tree leaf) : option (YjsItem A) :=
  match t with
  | GenNode 0 [to; tr; GenLeaf (inl id); GenLeaf (inr c)] =>
      match YjsPtr_dec to, YjsPtr_dec tr with
      | Some o, Some r => Some (Item o r id c)
      | _, _ => None
      end
  | _ => None
  end
with YjsPtr_dec (t : gen_tree leaf) : option (YjsPtr A) :=
  match t with
  | GenNode 1 [ti] => match YjsItem_dec ti with Some i => Some (itemPtr i) | None => None end
  | GenNode 2 [] => Some First
  | GenNode 3 [] => Some Last
  | _ => None
  end.

Lemma YjsItem_dec_enc (i : YjsItem A) : YjsItem_dec (YjsItem_enc i) = Some i.
Proof.
  apply (YjsItem_mut A
    (fun p => YjsPtr_dec (YjsPtr_enc p) = Some p)
    (fun i => YjsItem_dec (YjsItem_enc i) = Some i)).
  - intros i0 IH. simpl. rewrite IH. reflexivity.
  - reflexivity.
  - reflexivity.
  - intros o IHo r IHr id c. simpl. rewrite IHo IHr. reflexivity.
Qed.

Global Instance YjsItem_countable : Countable (YjsItem A) :=
  inj_countable YjsItem_enc YjsItem_dec YjsItem_dec_enc.
End item_countable.

Section common.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

#[global] Instance : IsPkgInit (iProp Σ) yjs := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) yjs := build_get_is_pkg_init_wf.

Set Default Proof Using "Type*".

(** Document content type. *)
Notation A := go_string.

(* ===== abstraction of scalar fields ====================================== *)

(** Heap id (two [w64]s) to model id (two [nat]s). *)
Definition toYjsId (i : yjs.id.t) : YjsId :=
  MkYjsId (uint.nat i.(yjs.id.clientId')) (uint.nat i.(yjs.id.clock')).

Definition toContent (c : yjs.content.t) : A := c.(yjs.content.content').

(** One node of the heap DLL: its location and the *model* items it carries.

    A node covers a RUN of consecutive per-char model items ([ic_run], issue
    #28): the heap item's content of clock-length n denotes n model items with
    consecutive clocks, each chained to the previous one by its left origin and
    all sharing the run's right origin ([run_wf] below). Every current creator
    mints runs of length 1, but the representation layer is stated for any
    length so splitting (and later multi-element content, #25) is pure cell
    surgery with the flattened model unchanged.

    The cell holds only stable, model-relevant data — the heap struct
    ([yjs.item.t]) with its volatile [left']/[right'] links, its [w64] id /
    content / origin-id pointers, and its flags is *not* stored here; it is
    existentially quantified inside [own_dll] (see [yjs_item]) and constrained to
    *translate* to the run's HEAD item (heap id [toYjsId]-maps to
    [item_id (run_head c)], the content explodes to the per-char contents,
    etc.); the non-head items carry no heap data of their own — [run_wf]
    reconstructs their ids and origins from the head. This keeps the abstract
    cell list invariant under [Store.Integrate]'s neighbour relinking —
    relinking changes only the existential heap struct, not [ic_run], so the
    abstract [cells] is unchanged across the splice. Origins live in the model
    items (they are order-defining model data), so order recovery
    ([YjsLt'] / [YjsArrInvariant.yai_sorted]) is intact.

    One non-link flag is promoted out of the existential heap struct: [ic_deleted]
    mirrors the heap node's Deleted bit (y-octo ITEM_DELETED). [own_dll] pins the
    existential struct's flags to [ic_deleted] (Countable, Deleted = [ic_deleted]),
    so the visible-character count is a pure function of the abstract cells
    ([num_visible], the source of truth for [yType.len]). [Text.Delete] tombstones
    a cell by flipping [ic_deleted]; [ic_item] (hence the abstract document list)
    is untouched, so deletion never reorders or removes a document item.

    [ic_parent] mirrors the heap node's [parent] pointer (issue #49: items carry
    their resolved parent type, y-octo [Some (Parent::Type)]). Like [ic_deleted]
    it is promoted out of the existential struct — [own_dll] pins the struct's
    [parent'] field to it — so [store.repair]'s borrow-from-neighbour reads it
    through the abstract cells; [own_ytype_cells] pins every cell of a type's
    DLL to that type's own loc. *)
Record item_cell := MkItemCell {
  ic_loc : loc;
  ic_run : list (YjsItem A);
  ic_deleted : bool;
  ic_parent : loc;
}.

(** Model items are inhabited (needed to make [run_head] total; [run_wf]
    guarantees the run is nonempty wherever the head matters). *)
#[global] Instance YjsItem_inhabited : Inhabited (YjsItem A) :=
  populate (Item First Last (MkYjsId O O) inhabitant).

(** The head model item of a cell's run: the one the heap struct's id /
    origin-id fields translate to. *)
Definition run_head (c : item_cell) : YjsItem A := hd inhabitant (ic_run c).

(** Run well-formedness: the model shadow of the reference implementations'
    split/merge invariant (yjs [splitItem] / y-octo [split_node_at] / yrs
    [ItemPtr::splice]): nonempty, consecutive clocks from the head, each
    non-head item's left origin is exactly the previous item, and every item
    shares the head's right origin. Everything about a non-head item is thus
    a function of the head, which is why the heap stores one id/origin pair
    per node. *)
Definition run_wf (r : list (YjsItem A)) : Prop :=
  r ≠ [] ∧
  ∀ (k : nat) (x y : YjsItem A), r !! k = Some x → r !! S k = Some y →
    item_id y = MkYjsId (clientId (item_id x)) (S (clock (item_id x))) ∧
    origin y = itemPtr x ∧
    rightOrigin y = rightOrigin x.

(** A singleton run is trivially well-formed; every current creator mints
    these. *)
Lemma run_wf_singleton (y : YjsItem A) : run_wf [y].
Proof.
  split; first done.
  intros k x y' Hx Hy'. destruct k; simpl in *; [done | by destruct k].
Qed.

(** The head model item survives a nonempty left truncation ([take]) — used by
    the split's LEFT half ([ic_run = take o (ic_run c)]), which keeps the node's
    location and head. Stated over the raw run list ([run_head c = hd inhabitant
    (ic_run c)]); [split_cell_left] lives in [yjs_store_base]. *)
Lemma hd_inhabitant_take (r : list (YjsItem A)) (o : nat) :
  (0 < o)%nat -> hd inhabitant (take o r) = hd inhabitant r.
Proof.
  move=> Ho. destruct r as [|a r']; first by rewrite take_nil.
  destruct o; [lia | done].
Qed.

(** The head of a right drop is the element at the drop offset — the split's
    RIGHT half heads at [ic_run c !! o]. *)
Lemma hd_inhabitant_drop (r : list (YjsItem A)) (o : nat) (y : YjsItem A) :
  r !! o = Some y -> hd inhabitant (drop o r) = y.
Proof. move=> Ho. rewrite (drop_S r y o Ho) //=. Qed.

(** [run_wf] telescoping: the [o]-th char's id sits exactly [o] clocks past the
    head's (same client). Feeds the RIGHT half's [id] field condition, where
    [splitNode] sets [right.id = (client, head_clock + diff)]. *)
Lemma run_wf_lookup_clock (r : list (YjsItem A)) (o : nat) (x y : YjsItem A) :
  run_wf r -> r !! 0%nat = Some x -> r !! o = Some y ->
  item_id y = MkYjsId (clientId (item_id x)) (clock (item_id x) + o).
Proof.
  move=> [_ Hstep] Hx. revert y. induction o as [|o IH] => y Hy.
  - rewrite Hx in Hy. injection Hy as <-. rewrite Nat.add_0_r.
    destruct (item_id x) as [cl ck]; done.
  - have [z Hz] : is_Some (r !! o).
    { apply lookup_lt_is_Some. apply lookup_lt_Some in Hy. lia. }
    have [Hidy _] := Hstep o z y Hz Hy.
    rewrite Hidy (IH z Hz) /= Nat.add_succ_r //.
Qed.

(** [run_wf] telescoping: every char shares the run's right origin. Feeds the
    RIGHT half's [rightOrigin] condition ([splitNode] keeps [n.originRightId]). *)
Lemma run_wf_lookup_rightOrigin (r : list (YjsItem A)) (o : nat) (x y : YjsItem A) :
  run_wf r -> r !! 0%nat = Some x -> r !! o = Some y ->
  rightOrigin y = rightOrigin x.
Proof.
  move=> [_ Hstep] Hx. revert y. induction o as [|o IH] => y Hy.
  - rewrite Hx in Hy. by injection Hy as <-.
  - have [z Hz] : is_Some (r !! o).
    { apply lookup_lt_is_Some. apply lookup_lt_Some in Hy. lia. }
    have [_ [_ Hro]] := Hstep o z y Hz Hy.
    rewrite Hro (IH z Hz) //.
Qed.

(** Per-char explosion of a heap content string: byte k becomes the content of
    the run's k-th model item. (For future non-string content types, this is
    the per-content-type element decomposition.) *)
Definition explode (s : go_string) : list A := (λ b, [b]) <$> s.

Lemma explode_length (s : go_string) : length (explode s) = length s.
Proof. by rewrite /explode length_fmap. Qed.

Lemma explode_singleton (s : go_string) :
  length s = 1%nat → explode s = [s].
Proof.
  destruct s as [|b s']; first done.
  destruct s' as [|b' s'']; [done | done].
Qed.

(** The flattened per-char document list a cell list denotes. *)
Definition run_flatten (cells : list item_cell) : list (YjsItem A) :=
  mjoin (ic_run <$> cells).

Lemma run_flatten_nil : run_flatten [] = [].
Proof. done. Qed.

Lemma run_flatten_cons (c : item_cell) (cells : list item_cell) :
  run_flatten (c :: cells) = ic_run c ++ run_flatten cells.
Proof. done. Qed.

Lemma run_flatten_app (cs1 cs2 : list item_cell) :
  run_flatten (cs1 ++ cs2) = run_flatten cs1 ++ run_flatten cs2.
Proof. by rewrite /run_flatten fmap_app join_app. Qed.

(** Under the all-singleton invariant (every creator today mints 1-char runs;
    temporary until the run-scan bridge of issue #28 M4), the flatten is a
    plain head map, recovering the pre-#28 cell/model 1:1 correspondence. *)
Definition cell_unit (c : item_cell) : Prop := length (ic_run c) = 1%nat.

Lemma run_flatten_singletons (cells : list item_cell) :
  Forall cell_unit cells →
  run_flatten cells = run_head <$> cells.
Proof.
  induction 1 as [|c cells Hc Hcells IH]; first done.
  rewrite run_flatten_cons IH fmap_cons /run_head.
  rewrite /cell_unit in Hc.
  destruct (ic_run c) as [|y [|y' r']]; simpl in Hc; [lia | done | lia].
Qed.

(* ----- cell-cursor prefix sums (issue #28 M4, stage C1c) ----------------- *)

(** Advancing the cell cursor by one appends that cell's whole run to the
    flattened prefix. The scan steps NODE by node while the model steps CHAR
    by char, so a cursor over cells couples to a [setfii_loop] offset over
    chars via these prefix sums. *)
Lemma run_flatten_take_S (cells : list item_cell) (cur : nat) (ci : item_cell) :
  cells !! cur = Some ci ->
  run_flatten (take (S cur) cells) = run_flatten (take cur cells) ++ ic_run ci.
Proof.
  move=> Hcur.
  rewrite (take_S_r _ _ ci Hcur) run_flatten_app run_flatten_cons run_flatten_nil app_nil_r //.
Qed.

(** The chars of the cell at the cursor sit at consecutive model indices
    starting at the flattened-prefix length — [setfii_block_step]'s [Hlook]
    premise, read off [cells_repr]'s [arr = run_flatten cells]. *)
Lemma run_flatten_take_lookup (cells : list item_cell) (cur : nat) (ci : item_cell)
    (k : nat) (y : YjsItem A) :
  cells !! cur = Some ci ->
  ic_run ci !! k = Some y ->
  run_flatten cells !! (length (run_flatten (take cur cells)) + k)%nat = Some y.
Proof.
  move=> Hcur Hk.
  have Hdec : run_flatten cells
            = run_flatten (take cur cells) ++ (ic_run ci ++ run_flatten (drop (S cur) cells)).
  { rewrite -{1}(take_drop_middle cells cur ci Hcur) run_flatten_app run_flatten_cons //. }
  rewrite Hdec lookup_app_r; last lia.
  have -> : (length (run_flatten (take cur cells)) + k
             - length (run_flatten (take cur cells)))%nat = k by lia.
  rewrite lookup_app_l; last (apply lookup_lt_Some in Hk; lia).
  exact Hk.
Qed.

(** Under the unit scaffold the cell cursor and the model offset coincide:
    each cell contributes exactly one char, so the flattened prefix length is
    the cursor (clamped to the cell count). *)
Lemma run_flatten_take_length_unit (cells : list item_cell) (cur : nat) :
  Forall cell_unit cells ->
  length (run_flatten (take cur cells)) = (cur `min` length cells)%nat.
Proof.
  move=> Hunit.
  have Hunit' : Forall cell_unit (take cur cells) := Forall_take _ _ _ Hunit.
  rewrite (run_flatten_singletons _ Hunit') length_fmap length_take //.
Qed.

(** The loc of the node at index [k] of [cells] ([null] outside [0, len)).
    Used to place the heap [conflict] / [left] pointers within the DLL. *)
Definition node_loc (cells : list item_cell) (k : Z) : loc :=
  if decide (0 <= k)%Z then default null (ic_loc <$> cells !! Z.to_nat k) else null.

(** An origin pointer is either null (no origin) or a read-only [Id] cell.
    Origins are immutable once integrated, hence persistent ([↦□]). *)
Definition is_origin_id (p : loc) (oid : option yjs.id.t) : iProp Σ :=
  match oid with
  | None => ⌜p = null⌝
  | Some idv => ⌜p ≠ null⌝ ∗ p ↦□ idv
  end.

(** Origins are read-only, hence the predicate is persistent. *)
Global Instance is_origin_id_persistent p oid : Persistent (is_origin_id p oid).
Proof. rewrite /is_origin_id. by destruct oid; apply _. Qed.

(* ----- item-pointer helpers --------------------------------------------- *)

(** A heap item pointer is null or owns a node; [oid_of] is its model id. *)
Definition oid_of (ov : option yjs.item.t) : option YjsId :=
  (λ v, toYjsId v.(yjs.item.id')) <$> ov.

Definition item_or_null (p : loc) (ov : option yjs.item.t) (dq : dfrac) : iProp Σ :=
  match ov with
  | None => ⌜p = null⌝
  | Some v => ⌜p ≠ null⌝ ∗ p ↦{dq} v
  end.

(* ----- id-span-slice abstraction to a gset ------------------------------ *)

(** The char ids one [idSpan] covers: the [len] consecutive clocks from the
    head id, at the span's client. An id addresses ANY char of a scanned run
    (yjs getItem semantics, issue #28), so the scan's id sets are CHAR-id sets
    and a span denotes its whole clock interval. *)
Definition span_ids (v : yjs.idSpan.t) : gset YjsId :=
  list_to_set
    ((λ o, MkYjsId (uint.nat v.(yjs.idSpan.id').(yjs.id.clientId'))
                   (uint.nat v.(yjs.idSpan.id').(yjs.id.clock') + o)%nat)
       <$> seq 0 (uint.nat v.(yjs.idSpan.len'))).

(** A span's clock interval does not wrap: [containsId]'s Go range test
    computes [clock + len] in [w64], so this is what makes the test decide
    [span_ids] membership. Sourced from the store's run-fits pool invariant. *)
Definition span_wf (v : yjs.idSpan.t) : Prop :=
  (uint.Z v.(yjs.idSpan.id').(yjs.id.clock') + uint.Z v.(yjs.idSpan.len') < 2^64)%Z.

(** Membership in [span_ids] is exactly the (mathematical) range test. *)
Lemma span_ids_elem (v : yjs.idSpan.t) (idv : yjs.id.t) :
  toYjsId idv ∈ span_ids v ↔
    (v.(yjs.idSpan.id').(yjs.id.clientId') = idv.(yjs.id.clientId') ∧
     (uint.Z v.(yjs.idSpan.id').(yjs.id.clock') ≤ uint.Z idv.(yjs.id.clock'))%Z ∧
     (uint.Z idv.(yjs.id.clock') <
        uint.Z v.(yjs.idSpan.id').(yjs.id.clock') + uint.Z v.(yjs.idSpan.len'))%Z).
Proof.
  have HZn : ∀ w : w64, Z.of_nat (uint.nat w) = uint.Z w by move=> w; word.
  rewrite /span_ids elem_of_list_to_set list_elem_of_fmap /toYjsId.
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

(** A length-1 span denotes exactly its head id (the pre-#28 singleton case). *)
Lemma span_ids_singleton (v : yjs.idSpan.t) :
  v.(yjs.idSpan.len') = W64 1 ->
  span_ids v = {[ toYjsId v.(yjs.idSpan.id') ]}.
Proof.
  move=> Hlen. rewrite /span_ids Hlen.
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

(** A heap [[]idSpan] abstracts to a [gset YjsId]: the union of its spans'
    char ids is exactly [gs]. The Go set ops are [containsId] / [append] /
    reset to [[]]; the union makes membership (not order/duplicates) the
    observable, matching the pure [gset] with [∪] / [∈]. The representation
    carries [span_wf] for every span so [containsId]'s [w64] range test is
    exact. Owning heap data, it takes a [dfrac] (appending needs
    [DfracOwn 1]). *)
Definition own_id_set (s : slice.t) (dq : dfrac) (gs : gset YjsId) : iProp Σ :=
  ∃ (vs : list yjs.idSpan.t),
    "Hsl" ∷ s ↦*{dq} vs ∗
    "Hcap" ∷ own_slice_cap yjs.idSpan.t s dq ∗
    "%Hwf" ∷ ⌜Forall span_wf vs⌝ ∗
    "%Hset" ∷ ⌜⋃ (span_ids <$> vs) = gs⌝.

(* ----- span <-> run-char bridge (issue #28 M4, stage C1a) ---------------- *)

(** [run_wf]'s chaining clause is [yjs_run_theory]'s [run_step]. *)
Lemma run_wf_run_step (r : list (YjsItem A)) : run_wf r -> run_step r.
Proof. move=> [_ Hstep]. exact Hstep. Qed.

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
  rewrite /span_ids /char_ids !elem_of_list_to_set !list_elem_of_fmap.
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

End common.
