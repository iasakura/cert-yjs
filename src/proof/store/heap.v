(** The [store], Iris layer: ghost state, the lock body, and the public store
    predicate.

    Definitions
    - [store_names]: the per-store ghost names (item-set authority, root-type
      registry, write-lock witness, the RWMutex reader accounting, the accepted
      set).
    - [own_item_map_key_pairs]: the heap [map[Client][]*item] over a
      (client, clock, address) key list, which [own_item_map] is over a
      state's entries.
    - the type pool and the store predicate:
      [own_type_pool dq locs p] (over [store/value_cells]'s [locs_wf]);
      the PRIMITIVE [own_store_state s state], the store at a
      [store_state] (every field,
      [own_store_fields] / [own_items_field], with
      [store_invs]), which every store spec is stated over, and what it
      reads back ([own_store_state_run_pool_invs] /
      [own_store_state_run_wf] / [own_store_state_arr_inv] /
      [own_store_state_registry_coh], the document reader also on the pool,
      [own_type_pool_arr_inv]), the node borrows
      ([own_type_pool_node_acc] / [own_store_state_node_acc], with the
      neighbour addresses and the flag byte in the [_links] forms; a whole
      type as its run view for a read, [own_store_state_ytype_acc]; the
      clock and client fields, [own_store_state_clock_acc] /
      [own_store_state_client_acc]) and
      covering-slot uniqueness ([own_store_state_covers_unique]).
      [own_store] is the lock layer's closure of [own_store_state] over the
      public model.
    - the ghost delete set: [is_delete_set_lb] (the persistent lower bound a delete
      hands out) and [own_delete_set] (its authority, with the domain
      bound and the tombstone-bit coherence that make the bound mean
      something), with its transports ([own_delete_set_mono] / [_refine] /
      [_perm] / [_snoc] / [_apply] / [_insert] / [_ValidReplay]).
    - the lock body, at [(locs, pool)]: [store_inv_ro] (the fractional,
      reader-visible part: the item-set authority and [own_type_pool]),
      [store_inv_excl] (the exclusive part) and [store_inv], carrying the
      client's ghost history; [tie_body] and [types_frag] / [frac_of] are the
      RWMutex reader-count accounting (issue #22).
    - the public state predicate [own_store s c h m pend]: the WHOLE
      lock-protected state as one exclusive predicate over its model.
    - the persistent witnesses [is_Store], [is_type_binding], [is_root],
      [is_type_lb], [is_root_lb], [is_applied_root_lb] / [is_applied_certs],
      [is_accepted],
      [is_update_item], and the read capability [own_read_cap].
    - the Integrate-side predicates [own_fresh_item_raw], [own_linked_item]
      ([own_linked_item_as_node]: it is [item/heap]'s [own_item_node] at
      [DfracOwn 1], live, with a nonempty content) and the loop invariant
      [integrate_loop_inv].

    Laws
    - [store_inv_init]: how to build the invariant from the raw points-tos, and
      [store_inv_bridge] / [store_inv_own_store] / [own_store_hist_coh] /
      [own_store_accepted_sound] / [store_inv_excl_hist_root]: what you may
      read back out of it.
    - the pool's laws: borrow one node ([own_type_pool_node_acc], with
      its links [_node_acc_links]), read its pure content off
      ([own_type_pool_run_wf] / [_id_bounds] / [_arr] / [_arr_inv]), a
      fresh node or type is absent from it ([own_type_pool_fresh] /
      [_fresh_concat] / [_fresh_type]).
    - [own_store_accept_batch]: the state-transition law for accepting a
      delivered batch.
    - the reader fractions form a chain: [frac_of_0] and [frac_of_split].
    - [pool_frag] splits and agrees ([pool_frag_split], [pool_frag_agree]);
      [is_type_binding] is functional ([is_type_binding_agree]).
    - the item index only sees its key list up to permutation
      ([own_item_map_key_pairs_keys_perm]).

    The lock wrappers are [store/wp_private.v]; the method proofs are
    [store/Integrate], [store/GetNode], [store/splitNode], [store/repair] and
    [store/applyUpdate], each reopening the same [Section] boilerplate.
    Downstream files Require the [store/store] facade. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core.
From New.proof Require Import algebra.
From New.proof Require Import prelude.
From New.proof Require Import history.
From New.proof.sync_proof Require Import base mutex rwmutex rwmutex_guard.
                                                      (* store lock: rwmutex.is_RWMutex + LP Lock/Unlock
                                                         (y-octo Arc<RwLock<DocStore>>); the
                                                         guard's rfrac + tok_set reader accounting *)
From New.proof Require Import tok_set.
From iris.algebra Require Import auth gmap gset.
From iris.algebra.lib Require Import dfrac_agree.
From iris.bi.lib Require Import fractional.
From stdpp Require Import sorting.
(* iris.algebra / stdpp.sorting push [nat_scope], retuning the default [<] / [≤].
   The verified WP proofs write [Z] comparisons (e.g. [sint.Z i < …]) unannotated
   and annotate [nat] ones with [%nat], so restore [Z_scope] as the default. *)
Local Open Scope Z_scope.
From New.proof.store Require Import model value.
From New.proof.id Require Import value heap.
From New.proof.item Require Import run_theory model value heap.
From New.proof.ytype Require Import model value heap.

Section store_heap.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.

(* The ghost op-history types ([history] / [network_model]) at the
   document content type; type names are Go strings (issue #49). *)
Notation P := go_string.

Local Notation TId := (TypeId P).

Local Notation Op := (TId * @YjsOperation A)%type.

Local Notation Ev := (@Event Op).

Local Notation DocModel := (gmap TId (list (YjsItem A))).

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

    We track full ITEMS, not just ids: a membership bound [x ∈ S ⊆ tm_arr tm]
    then pins [x] to a *genuine* document item (same structure, not merely the
    same id), which is what lets [Text.Insert] expose the post as a real
    [sublist L L'] rather than only an id-set inclusion. [gset (YjsItem A)] needs
    [Countable (YjsItem A)] (derived in [prelude] via [gen_tree]). Order is not
    tracked in the ghost (recoverable from origins / from [YjsArrInvariant]). *)

Notation seqUR := (authR (gmapUR loc (gsetUR (YjsItem A)))).

Context {seq_inG : inG Σ seqUR}.

(** Accepted-id RA (this branch): a GROW-ONLY set of ids the store has
    "accepted", i.e. promised not to lose. [authR (gsetUR YjsId)] — the
    authority [● acc] sits in [store_inv], and a persistent lower-bound
    fragment [◯ {[i]}] (gset elements are core-id) is the [is_accepted]
    receipt every applyUpdate hands back per input. The store invariant ties
    [acc ⊆ delivered_ids h ∪ pending ids], so an accepted id is forever
    delivered-or-buffered: this is what makes "no input is lost" an
    ENFORCEABLE guarantee (a discarding implementation could not mint the
    receipt), unlike a bare existential over the pending list. *)

Notation accUR := (authR (gsetUR YjsId)).

Context {acc_inG : inG Σ accUR}.

Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO addressed_pool))}.

(* The [∷] (named) wrapper blocks [Timeless] TC resolution; unfold it (as
   [New.proof.sync_proof.rwmutex] does) so the [Timeless] instances below go
   through the named conjuncts of [own_item_map_key_pairs] / [store_inv]. *)

#[local] Hint Extern 100 (Timeless (?n ∷ ?P)) =>
  (change (n ∷ P) with P) : typeclass_instances.

(* ===== definitions ======================================================== *)


(** ---------- reader-count accounting (concurrent read API) ----------------
    The tie invariant carries [rwmutex_guard]-style accounting so multiple readers
    can each hold a fractional [store_inv_ro] share:
    - [own_tok_auth γs.(sn_rrlocked) n]: the active reader count [n];
    - [own_toks γs.(sn_rmax) n] bounded by the persistent
      [own_tok_auth_dfrac γs.(sn_rmax) □ (max)]: [n ≤ actualMaxReaders], so the
      per-reader fraction stays positive;
    - [types_frag] ([dfrac_agree] on the [types] map) ties the readers' share to
      the store's current [types] (needed to recombine at RUnlock, since the
      item-set auth alone does not determine the type pool);
    - the mutable-exclusive [store_inv_excl] whole + the shared [store_inv_ro] at
      the remaining fraction [frac_of n]. The write [Lock] linearizes at
      [RLocked 0] (fraction 1 = the whole [store_inv] via [store_inv_bridge]);
      each read [RLock] peels off one [rfrac] share. The fraction arithmetic
      mirrors [rwmutex_guard.rfrac]. ------------------------------------------ *)

Definition frac_of (n : nat) : Qp :=
  (pos_to_Qp (Z.to_pos (rwmutex.actualMaxReaders + 1 - Z.of_nat n)) * rwmutex_guard.rfrac)%Qp.


(** Needed to commute [▷ ∃ st : rwmutex, …] when opening the tie invariant. *)
#[local] Instance rwmutex_inhabited : Inhabited rwmutex := populate Locked.


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

(* [own_slice_cap] (a sealed disjunction of pure facts and a [↦{dq}] array) is
   timeless, but the New.golang slice library ships no such instance; provide it
   here (candidate upstream addition) so [own_item_map_key_pairs] / [store_inv] are
   timeless. *)
#[global] Instance own_slice_cap_timeless (V : Type) `{!ZeroVal V} `{!TypedPointsto V} (s : slice.t) (dq : dfrac) :
  Timeless (own_slice_cap V s dq).
Proof. rewrite own_slice_cap_unseal /own_slice_cap_def. apply _. Qed.

(** [own_item_map_key_pairs mref dq key_pairs]: the item index over a (client, clock,
    address) key list: the map header at [mref] (Go [store.items]) and, per
    client, the backing slice holding [key_pair_client_locs client key_pairs] (+ cap);
    every client with a key has a slice, and the keys are [key_pairs_clock_unique].
    [own_item_map] is this over a state's entries. *)
Definition own_item_map_key_pairs (mref : loc) (dq : dfrac) (key_pairs : list (w64 * (Z * loc))) : iProp Σ :=
  ∃ (gm : gmap w64 slice.t),
    "Hmap" ∷ own_map mref dq gm ∗
    "Hruns" ∷ ([∗ map] client ↦ s ∈ gm,
        "Hslice" ∷ s ↦*{dq} key_pair_client_locs client key_pairs ∗
        "Hcap"   ∷ own_slice_cap loc s dq) ∗
    "%Hcomplete" ∷ ⌜∀ c, c ∈ key_pairs.*1 → is_Some (gm !! c)⌝ ∗
    "%Hclockunique" ∷ ⌜key_pairs_clock_unique key_pairs⌝.

#[global] Instance own_item_map_key_pairs_timeless mref dq key_pairs : Timeless (own_item_map_key_pairs mref dq key_pairs).
Proof. rewrite /own_item_map_key_pairs. apply _. Qed.

(** The index only sees the key multiset. *)
Lemma own_item_map_key_pairs_keys_perm (mref : loc) (dq : dfrac) (key_pairs1 key_pairs2 : list (w64 * (Z * loc))) :
  key_pairs1 ≡ₚ key_pairs2 -> own_item_map_key_pairs mref dq key_pairs1 -∗ own_item_map_key_pairs mref dq key_pairs2.
Proof.
  iIntros (Hperm) "H". iNamed "H". iExists gm. iFrame "Hmap". iSplitL "Hruns".
  - iApply (big_sepM_impl with "Hruns"). iIntros "!>" (client s Hgm) "H". iNamed "H".
    rewrite (key_pair_client_locs_perm client key_pairs1 key_pairs2 Hclockunique Hperm). iFrame "Hslice Hcap".
  - iPureIntro. split.
    + move=> c Hc. apply Hcomplete. by rewrite Hperm.
    + move=> a b Ha Hb. apply Hclockunique; by rewrite Hperm.
Qed.

(** [own_item_map mref dq locs p]: the store's item index,
    [own_item_map_key_pairs] over the pool's entries. *)
Definition own_item_map (mref : loc) (dq : dfrac) (locs : gmap loc (list loc)) (p : pool) : iProp Σ :=
  own_item_map_key_pairs mref dq (entry_key_pair <$> pool_entries locs p).

(* The DLL predicate stack is timeless too (heap points-to + pure + persistent
   origin handles); register the instances so [store_inv] is timeless. *)
#[global] Instance is_origin_id_timeless p originId : Timeless (is_origin_id p originId).
Proof. rewrite /is_origin_id. by destruct originId; apply _. Qed.

#[global] Instance own_item_node_timeless l dq input deleted parent prev nxt :
  Timeless (own_item_node l dq input deleted parent prev nxt).
Proof. rewrite /own_item_node. apply _. Qed.

#[global] Instance own_dll_timeless dq parent l last prev next ls runs :
  Timeless (own_dll dq parent l last prev next ls runs).
Proof.
  revert runs l prev.
  induction ls as [|lc ls IH]; intros [|r runs] l prev; simpl; apply _.
Qed.

#[global] Instance own_ytype_timeless parent dq ls tm :
  Timeless (own_ytype parent dq ls tm).
Proof. rewrite /own_ytype. apply _. Qed.

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
  sn_accepted : gname; (* authR (gsetUR YjsId): grow-only accepted-id set (no-loss) *)
  sn_client : gname; (* agreeR (leibnizO ClientId): the store's client pin, [is_store_client] *)
  sn_delete_set : gname;     (* authR (gsetUR YjsId): the monotone delete set (plan-delete-set.md D1) *)
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

(* ----- the lock invariant ----------------------------------------------- *)

(** [store_inv_ro γs types q]: the read-only-shareable slice of [store_inv] that a
    concurrent reader needs: the per-type DLLs (from which [Text.String]/[Len]
    read visible content / length) and the item-set authority (combined with a
    reader's [is_type_lb] to locate its type). Fractional in [q]: the read lock
    hands each of up to [rwmutexMaxReaders] readers a share, and the write lock
    reassembles the whole ([q = 1]). The store's mutable-exclusive parts (the
    struct fields, the item index, the registry [ghost_map_auth], the ghost
    history) are NOT here; they stay whole in the lock invariant while readers
    hold shares, since no writer runs concurrently with readers. *)
(* ----- the decoded update buffer (issue #40) --------------------------------
   [own_update_structs] abstracts a heap slice of decoded structs to the model list of
   type-tagged integrate inputs. It lives here (moved from the update proofs)
   because the lock invariant now owns the store's pending buffer through it. *)

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

(** [is_update_item updateItemVal typedInput]: the decoded heap struct [updateItemVal] (a [updateItem])
    translates to the model doc-op payload [typedInput = (tid, input)] -- its id /
    content / both origin pointers map across (origins via [is_origin_id],
    persistent), its content is a nonempty run (issue #28 U7c: the single-char
    [Hulen = 1] restriction is dropped so a wire item can carry a whole run of
    chained per-char ops), and its decoded parent name
    (when present) is the name of the root type [tid] (issue #49; when absent
    the batch-level well-formedness pins [tid] through the origins). *)
Definition is_update_item (updateItemVal : yjs.updateItem.t)
    (typedInput : TId * IntegrateInput (A := A)) : iProp Σ :=
  ∃ (oleft oright : option yjs.id.t) (opn : option go_string),
    "HisL" ∷ is_origin_id updateItemVal.(yjs.updateItem.originLeftId') oleft ∗
    "HisR" ∷ is_origin_id updateItemVal.(yjs.updateItem.originRightId') oright ∗
    "HisPN" ∷ is_parent_name updateItemVal.(yjs.updateItem.parentName') opn ∗
    "%Hin_l" ∷ ⌜(toYjsId <$> oleft) = in_originId typedInput.2⌝ ∗
    "%Hin_r" ∷ ⌜(toYjsId <$> oright) = in_rightOriginId typedInput.2⌝ ∗
    "%Hin_id" ∷ ⌜toYjsId updateItemVal.(yjs.updateItem.id') = in_id typedInput.2⌝ ∗
    "%Hin_c" ∷ ⌜updateItemVal.(yjs.updateItem.content') = in_content typedInput.2⌝ ∗
    "%Hunonempty" ∷ ⌜(1 <= length updateItemVal.(yjs.updateItem.content'))%nat⌝ ∗
    "%Htid" ∷ ⌜∀ nm, opn = Some nm -> typedInput.1 = RootId nm⌝ ∗
    "%Hborrow" ∷ ⌜opn = None -> in_originId typedInput.2 ≠ None ∨ in_rightOriginId typedInput.2 ≠ None⌝.

#[global] Instance is_update_item_persistent updateItemVal typedInput : Persistent (is_update_item updateItemVal typedInput).
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
    "Hitems" ∷ ([∗ list] updateItemVal;typedInput ∈ uivs;inputs, is_update_item updateItemVal typedInput).

(** [own_delete_spans sl dq spans]: the heap slice of decoded delete spans at
    [sl] (the store's [pendingDeletes] buffer, and the batch [applyDeleteSpans]
    is handed). A span is a plain triple of machine words with no heap
    references, so unlike [own_update_structs] the model IS the value list;
    the capacity comes along because the buffer is appended to. *)
(** [own_delete_spans sl dq spans]: the delete-span slice over its PURE model,
    a list of [delete_span]. The decoded structs the slice actually holds are
    existentially quantified: nothing outside this proof file needs to know
    that a span is a goose record, and a spec that mentioned one would be
    mixing the model with the representation.

    Used as: the store's [pendingDeletes] buffer in [store_inv_excl], the
    argument and the leftover of [wp_store__applyDeleteSpans], and (through
    [own_delete_ids], which forgets down to the union of the ids) every public
    spec that takes a delete batch. *)
Definition own_delete_spans (sl : slice.t) (dq : dfrac)
    (spans : list delete_span) : iProp Σ :=
  ∃ vs : list yjs.deleteSpan.t,
    "Hspsl" ∷ sl ↦*{dq} vs ∗
    "Hspcap" ∷ own_slice_cap yjs.deleteSpan.t sl dq ∗
    "%Hspmodel" ∷ ⌜delete_span_of_val <$> vs = spans⌝.

#[global] Instance own_delete_spans_timeless sl dq spans :
  Timeless (own_delete_spans sl dq spans).
Proof. rewrite /own_delete_spans. apply _. Qed.

(** [own_delete_ids sl dq D]: the same slice over its PURE model, the set of
    ids the batch denotes ([delete_batch_ids]). This is the form public specs
    take: [own_delete_spans] exposes the wire records, which are internal
    data, and a caller of [Doc.ApplySyncUpdate] has no business reasoning
    about the layout of a [deleteSpan]. It is also the form the eventual
    certificate will line up with, since [is_delete_set_lb] speaks about a set of ids
    too. *)
Definition own_delete_ids (sl : slice.t) (dq : dfrac) (D : gset YjsId) : iProp Σ :=
  ∃ spans : list delete_span,
    own_delete_spans sl dq spans ∗ ⌜delete_batch_ids spans = D⌝.

#[global] Instance own_delete_ids_timeless sl dq D :
  Timeless (own_delete_ids sl dq D).
Proof. rewrite /own_delete_ids. apply _. Qed.

Lemma own_delete_ids_intro (sl : slice.t) (dq : dfrac)
    (spans : list delete_span) :
  own_delete_spans sl dq spans -∗ own_delete_ids sl dq (delete_batch_ids spans).
Proof. iIntros "H". iExists spans. by iFrame "H". Qed.


(** [is_root γs name]: persistent witness that the root type [name] is
    registered in the store (bound in the registry to SOME type loc, which
    stays hidden). This is what the [applyUpdate] certificate spec asks for
    per target root, in place of a raw registry lookup; any holder of the
    binding (a [Text] handle, [getOrCreateYType]'s hit path) can mint it. *)
Definition is_root (γs : store_names) (name : P) : iProp Σ :=
  ∃ p : loc, is_type_binding γs.(sn_types) name p.

#[global] Instance is_root_persistent γs name : Persistent (is_root γs name).
Proof. apply _. Qed.


(** [is_accepted γs i]: the persistent receipt that id [i] has been accepted by
    the store (a lower bound on the grow-only accepted set). Combined with the
    store invariant it proves [i] is forever delivered-or-buffered. *)
Definition is_accepted (γs : store_names) (i : YjsId) : iProp Σ :=
  own γs.(sn_accepted) (◯ ({[i]} : gset YjsId) : accUR).

#[global] Instance is_accepted_persistent γs i : Persistent (is_accepted γs i).
Proof. rewrite /is_accepted. apply _. Qed.

#[global] Instance is_accepted_timeless γs i : Timeless (is_accepted γs i).
Proof. rewrite /is_accepted. apply _. Qed.

(** [is_delete_set_lb γs S]: the persistent lower bound on the store-global monotone
    delete set (docs/plan-delete-set.md, D1): the ids in [S] are (and stay)
    tombstoned. Same RA and idiom as [is_accepted]; [Text.Delete] mints these,
    and (with D2) the wire delete path will too. *)
Definition is_delete_set_lb (γs : store_names) (S : gset YjsId) : iProp Σ :=
  own γs.(sn_delete_set) (◯ S : accUR).

#[global] Instance is_delete_set_lb_persistent γs S : Persistent (is_delete_set_lb γs S).
Proof. rewrite /is_delete_set_lb. apply _. Qed.

#[global] Instance is_delete_set_lb_timeless γs S : Timeless (is_delete_set_lb γs S).
Proof. rewrite /is_delete_set_lb. apply _. Qed.

Lemma is_delete_set_lb_union (γs : store_names) (S T : gset YjsId) :
  is_delete_set_lb γs S -∗ is_delete_set_lb γs T -∗ is_delete_set_lb γs (S ∪ T).
Proof. iApply auth_gset_frag_union. Qed.

Lemma is_delete_set_lb_empty (γs : store_names) : ⊢ |==> is_delete_set_lb γs ∅.
Proof. iApply auth_gset_frag_empty. Qed.

(** [own_delete_set γs m runs]: the delete-set authority, its
    tombstone clause ([delete_set_tombstoned]). *)
Definition own_delete_set (γs : store_names) (m : DocModel) (runs : list ItemRun) : iProp Σ :=
  ∃ delete_set : gset YjsId,
    "Hdelete_set_auth" ∷ own γs.(sn_delete_set) (● delete_set : accUR) ∗
    "%Hdelete_set_dom" ∷ ⌜delete_set_dom delete_set m⌝ ∗
    "%Hdelete_set_tomb" ∷ ⌜delete_set_tombstoned delete_set runs⌝.

#[global] Instance own_delete_set_timeless γs m runs : Timeless (own_delete_set γs m runs).
Proof. rewrite /own_delete_set. apply _. Qed.

(** The transports of the delete set, at runs: along model growth, along
    [live_refine] (a split, a flip, a registry insert), along a
    permutation, along an integrate (a fresh live run), along the remote
    apply ([apply_live_refine]), and along one type's list growing or a
    whole valid replay. *)
Lemma own_delete_set_mono (γs : store_names) (m m' : DocModel) (runs : list ItemRun) :
  (∀ i, doc_model_has m i = true -> doc_model_has m' i = true) ->
  own_delete_set γs m runs -∗ own_delete_set γs m' runs.
Proof.
  iIntros (Hmono) "H". iNamed "H". iExists delete_set. iFrame "Hdelete_set_auth".
  iPureIntro. split; [exact (delete_set_dom_mono delete_set m m' Hmono Hdelete_set_dom) | exact Hdelete_set_tomb].
Qed.

Lemma own_delete_set_refine (γs : store_names) (m : DocModel) (p p' : pool) :
  live_refine p p' ->
  own_delete_set γs m (all_runs p) -∗ own_delete_set γs m (all_runs p').
Proof.
  iIntros (Hlr) "H". iNamed "H". iExists delete_set. iFrame "Hdelete_set_auth".
  iPureIntro. split; [exact Hdelete_set_dom | exact (delete_set_tombstoned_refine delete_set p p' Hlr Hdelete_set_tomb)].
Qed.

Lemma own_delete_set_perm (γs : store_names) (m : DocModel) (runs runs' : list ItemRun) :
  runs' ≡ₚ runs -> own_delete_set γs m runs -∗ own_delete_set γs m runs'.
Proof.
  iIntros (Hperm) "H". iNamed "H". iExists delete_set. iFrame "Hdelete_set_auth".
  iPureIntro. split; [exact Hdelete_set_dom | exact (delete_set_tombstoned_perm delete_set runs runs' Hperm Hdelete_set_tomb)].
Qed.

Lemma own_delete_set_snoc (γs : store_names) (m : DocModel) (runs runs' : list ItemRun) (r : ItemRun) :
  runs' ≡ₚ runs ++ [r] ->
  (∀ y, y ∈ run_items r -> doc_model_has m (item_id y) = false) ->
  own_delete_set γs m runs -∗ own_delete_set γs m runs'.
Proof.
  iIntros (Hperm Hfresh) "H". iNamed "H". iExists delete_set. iFrame "Hdelete_set_auth".
  iPureIntro. split; [exact Hdelete_set_dom |].
  apply (delete_set_tombstoned_snoc delete_set runs runs' r Hperm); [| exact Hdelete_set_tomb].
  move=> y Hy Hin. have Ht := Hdelete_set_dom _ Hin. have Hf := Hfresh y Hy. congruence.
Qed.

Lemma own_delete_set_apply (γs : store_names) (m m' : DocModel) (runs runs' : list ItemRun) :
  (∀ i, doc_model_has m i = true -> doc_model_has m' i = true) ->
  apply_live_refine m runs runs' ->
  own_delete_set γs m runs -∗ own_delete_set γs m' runs'.
Proof.
  iIntros (Hmono Halr) "H". iNamed "H". iExists delete_set. iFrame "Hdelete_set_auth".
  iPureIntro. split; [exact (delete_set_dom_mono delete_set m m' Hmono Hdelete_set_dom) |].
  move=> r' Hr' y Hy Hin.
  destruct (run_deleted r') eqn:Hlive; first done. exfalso.
  destruct (Halr r' Hr' Hlive y Hy) as [(r & Hr & Hliver & Hy') | Hfresh].
  - by rewrite (Hdelete_set_tomb r Hr y Hy' Hin) in Hliver.
  - by rewrite (Hdelete_set_dom _ Hin) in Hfresh.
Qed.

Lemma own_delete_set_insert (γs : store_names) (m : DocModel) (runs : list ItemRun)
    (t : TId) (arr' : list (YjsItem A)) :
  (∀ x, x ∈ doc_model_get m t -> x ∈ arr') ->
  own_delete_set γs m runs -∗ own_delete_set γs (<[t := arr']> m) runs.
Proof.
  iIntros (Hgrow) "H". iNamed "H". iExists delete_set. iFrame "Hdelete_set_auth".
  iPureIntro. split; [exact (delete_set_dom_insert delete_set m t arr' Hgrow Hdelete_set_dom) | exact Hdelete_set_tomb].
Qed.

Lemma own_delete_set_ValidReplay (γs : store_names)
    (inputs : list (TId * IntegrateInput (A := A))) (m m' : DocModel)
    (runs : list ItemRun) :
  ValidReplay inputs m m' -> own_delete_set γs m runs -∗ own_delete_set γs m' runs.
Proof.
  iIntros (Hvr) "H". iNamed "H". iExists delete_set. iFrame "Hdelete_set_auth".
  iPureIntro. split; [exact (delete_set_dom_ValidReplay delete_set inputs m m' Hvr Hdelete_set_dom) | exact Hdelete_set_tomb].
Qed.

(** [is_store_client γs c]: the persistent witness that this store IS client
    [c] (the [store.client] field, set once at [newStore] and never written).
    An [agree] ghost: any two witnesses agree, and [own_store] carries one, so
    a spec over a store it only holds handles to can name the store's client
    instead of leaving it existential (the server proofs pin the server
    replica's [ClientId] this way, issue #107). *)
Definition is_store_client (γs : store_names) (c : ClientId) : iProp Σ :=
  own γs.(sn_client) (to_agree (c : leibnizO ClientId)).

#[global] Instance is_store_client_persistent γs c : Persistent (is_store_client γs c).
Proof. rewrite /is_store_client. apply _. Qed.

#[global] Instance is_store_client_timeless γs c : Timeless (is_store_client γs c).
Proof. rewrite /is_store_client. apply _. Qed.

Lemma is_store_client_agree γs c1 c2 :
  is_store_client γs c1 -∗ is_store_client γs c2 -∗ ⌜c1 = c2⌝.
Proof.
  iIntros "H1 H2". iCombine "H1 H2" gives %Hv.
  iPureIntro. by apply to_agree_op_valid_L in Hv.
Qed.

(** [own_type_pool dq locs p]: the whole type pool: every registered
    type's [own_ytype] at its address list, over the address map
    [locs_wf]. The [(locs, p)] pair is what every store spec carries. *)
Definition own_type_pool (dq : dfrac)
    (locs : gmap loc (list loc)) (p : pool) : iProp Σ :=
  "%Hlocswf" ∷ ⌜locs_wf locs p⌝ ∗
  "Hpool" ∷ [∗ map] parent ↦ tm ∈ p,
    ∃ ls, ⌜locs !! parent = Some ls⌝ ∗
          own_ytype parent dq ls tm ∗ ⌜YjsArrInvariant (tm_arr tm)⌝.

(** The type and pool are fractional: the read path holds a
    share of the pool ([store_inv_ro]) while the write path holds it whole. *)
#[global] Instance own_ytype_fractional parent ls tm :
  Fractional (λ q, own_ytype parent (DfracOwn q) ls tm).
Proof.
  intros q1 q2. iSplit.
  - iIntros "H". iDestruct "H" as (yt tl) "(Hpar & Hdll & %Hlen)".
    iDestruct "Hpar" as "[Hp1 Hp2]".
    iDestruct (own_dll_fractional with "Hdll") as "[Hd1 Hd2]".
    iSplitL "Hp1 Hd1"; iExists yt, tl; iFrame; done.
  - iIntros "[H1 H2]".
    iDestruct "H1" as (yt1 tl1) "(Hp1 & Hd1 & %Hlen)".
    iDestruct "H2" as (yt2 tl2) "(Hp2 & Hd2 & _)".
    iCombine "Hp1 Hp2" gives %Hyt. subst yt2.
    iDestruct (own_dll_lastptr with "Hd1") as "[%Htl1 Hd1]".
    iDestruct (own_dll_lastptr with "Hd2") as "[%Htl2 Hd2]".
    have Htl : tl2 = tl1 by rewrite Htl1 Htl2.
    rewrite Htl.
    iCombine "Hp1 Hp2" as "Hp".
    iDestruct (own_dll_fractional with "[$Hd1 $Hd2]") as "Hdll".
    iExists yt1, tl1. iFrame "Hp Hdll". done.
Qed.

#[global] Instance own_type_pool_fractional locs p :
  Fractional (λ q, own_type_pool (DfracOwn q) locs p).
Proof.
  intros q1 q2. rewrite /own_type_pool /named. iSplit.
  - iIntros "(%Hwf & Hpool)".
    iAssert ([∗ map] parent ↦ tm ∈ p,
        (∃ ls, ⌜locs !! parent = Some ls⌝ ∗ own_ytype parent (DfracOwn q1) ls tm ∗ ⌜YjsArrInvariant (tm_arr tm)⌝) ∗
        (∃ ls, ⌜locs !! parent = Some ls⌝ ∗ own_ytype parent (DfracOwn q2) ls tm ∗ ⌜YjsArrInvariant (tm_arr tm)⌝))%I
      with "[Hpool]" as "Hpool".
    { iApply (big_sepM_impl with "Hpool"). iIntros "!>" (parent tm Hp) "H".
      iDestruct "H" as (ls) "(%Hls & Hyt & %Hinv)".
      iDestruct (own_ytype_fractional parent ls tm q1 q2 with "Hyt") as "[H1 H2]".
      iSplitL "H1"; iExists ls; iFrame; by iSplit; iPureIntro. }
    rewrite big_sepM_sep. iDestruct "Hpool" as "[H1 H2]".
    iSplitL "H1"; iFrame; by iPureIntro.
  - iIntros "[(%Hwf & H1) (_ & H2)]". iSplitR; first by iPureIntro.
    iCombine "H1 H2" as "H". rewrite -big_sepM_sep.
    iApply (big_sepM_impl with "H"). iIntros "!>" (parent tm Hp) "[Ha Hb]".
    iDestruct "Ha" as (ls1) "(%Hls1 & Hyt1 & %Hinv)". iDestruct "Hb" as (ls2) "(%Hls2 & Hyt2 & _)".
    rewrite Hls1 in Hls2. injection Hls2 as <-.
    iExists ls1. iSplitR; first by iPureIntro. iSplitL; last by iPureIntro.
    iApply (own_ytype_fractional parent ls1 tm q1 q2). iFrame "Hyt1 Hyt2".
Qed.

(* ----- laws of the type pool --------------------------------------------- *)

(** Every run head's id components round-trip through [w64] heap fields:
    [own_type_pool_id_bounds], off the run spine. *)
Lemma own_type_pool_id_bounds (locs : gmap loc (list loc)) (p : pool) :
  own_type_pool (DfracOwn 1) locs p -∗
  ⌜∀ r, r ∈ all_runs p ->
     (Z.of_nat (run_client r) < 2^64)%Z ∧ (Z.of_nat (run_clock r) < 2^64)%Z⌝.
Proof.
  iIntros "(_ & Hpool)".
  iAssert ([∗ map] parent ↦ tm ∈ p,
      ⌜∀ r, r ∈ tm_runs tm -> (Z.of_nat (run_client r) < 2^64)%Z ∧
                              (Z.of_nat (run_clock r) < 2^64)%Z⌝)%I with "[Hpool]" as "H".
  { iApply (big_sepM_impl with "Hpool").
    iIntros "!#" (parent tm Hp) "H".
    iDestruct "H" as (ls) "(_ & Hyt & _)".
    iDestruct "Hyt" as (yt tl) "(_ & Hdll & _)".
    iApply (own_dll_id_bounds with "Hdll"). }
  iDestruct (big_sepM_pure with "H") as %Hall.
  iPureIntro. move=> r Hr.
  apply elem_of_all_runs in Hr as (parent & tm & Hp & Hr).
  exact (Hall parent tm Hp r Hr).
Qed.

(** Every run of the pool is chained ([run_wf]), off the run
    spine. *)
Lemma own_type_pool_run_wf (locs : gmap loc (list loc)) (p : pool) :
  own_type_pool (DfracOwn 1) locs p -∗
  ⌜∀ r, r ∈ all_runs p -> run_wf (run_items r)⌝.
Proof.
  iIntros "(_ & Hpool)".
  iAssert ([∗ map] parent ↦ tm ∈ p, ⌜∀ r, r ∈ tm_runs tm -> run_wf (run_items r)⌝)%I
    with "[Hpool]" as "H".
  { iApply (big_sepM_impl with "Hpool").
    iIntros "!#" (parent tm Hp) "H".
    iDestruct "H" as (ls) "(_ & Hyt & _)".
    iDestruct "Hyt" as (yt tl) "(_ & Hdll & _)".
    iApply (own_dll_run_wf with "Hdll"). }
  iDestruct (big_sepM_pure with "H") as %Hall.
  iPureIntro. move=> r Hr.
  apply elem_of_all_runs in Hr as (parent & tm & Hp & Hr).
  exact (Hall parent tm Hp r Hr).
Qed.

(** A fully owned node struct's address is not an address of a type, nor
    of any type of the pool: the source of [locs_wf]'s
    [NoDup] when a freshly allocated node is spliced in. *)
Lemma own_ytype_fresh (q : loc) (v : yjs.item.t) (parent : loc) (dq : dfrac)
    (ls : list loc) (tm : type_model) :
  q ↦ v -∗ own_ytype parent dq ls tm -∗ ⌜q ∉ ls⌝.
Proof.
  iIntros "Hq Hyt". iDestruct "Hyt" as (yt tl) "(_ & Hdll & _)".
  iApply (own_dll_fresh with "Hq Hdll").
Qed.

Lemma own_type_pool_fresh (q : loc) (v : yjs.item.t) (dq : dfrac)
    (locs : gmap loc (list loc)) (p : pool) :
  q ↦ v -∗
  ([∗ map] parent ↦ tm ∈ p,
     ∃ ls, ⌜locs !! parent = Some ls⌝ ∗ own_ytype parent dq ls tm ∗ ⌜YjsArrInvariant (tm_arr tm)⌝) -∗
  ⌜∀ parent ls tm, locs !! parent = Some ls -> p !! parent = Some tm -> q ∉ ls⌝.
Proof.
  iIntros "Hq Hpool". iIntros (parent ls tm Hls Hp).
  iDestruct (big_sepM_lookup _ _ parent tm Hp with "Hpool") as (ls0) "(%Hls0 & Hyt & _)".
  rewrite Hls in Hls0. injection Hls0 as <-.
  iApply (own_ytype_fresh with "Hq Hyt").
Qed.

(** The same, over the whole pool: an owned node address is absent from
    every address list of the map. *)
Lemma own_type_pool_fresh_concat (q : loc) (v : yjs.item.t) (dq : dfrac)
    (locs : gmap loc (list loc)) (p : pool) :
  q ↦ v -∗ own_type_pool dq locs p -∗ ⌜q ∉ concat ((map_to_list locs).*2)⌝.
Proof.
  iIntros "Hq (%Hlocswf & Hpool)".
  iDestruct (own_type_pool_fresh with "Hq Hpool") as %Hfr.
  iPureIntro. destruct Hlocswf as (Hdom & _ & _).
  move=> Hin. apply list_elem_of_concat in Hin as (lsq & Hin & Hlsq).
  apply list_elem_of_fmap in Hlsq as ([parent lsq'] & -> & Hq). simpl in Hin.
  apply elem_of_map_to_list in Hq.
  have Hqp : is_Some (p !! parent).
  { apply elem_of_dom. rewrite -Hdom. apply elem_of_dom. by exists lsq'. }
  destruct Hqp as [tmq Htmq].
  exact (Hfr parent lsq' tmq Hq Htmq Hin).
Qed.

(** A separately owned type is not in the pool: the run form of
    the cell-level freshness law, what [getOrCreateYType]'s miss branch
    registers a fresh [newYType] with. *)
Lemma own_type_pool_fresh_type (q : loc) (ls0 : list loc) (tm0 : type_model)
    (locs : gmap loc (list loc)) (p : pool) :
  own_ytype q (DfracOwn 1) ls0 tm0 -∗
  own_type_pool (DfracOwn 1) locs p -∗
  own_ytype q (DfracOwn 1) ls0 tm0 ∗
  own_type_pool (DfracOwn 1) locs p ∗
  ⌜p !! q = None⌝.
Proof.
  iIntros "Hnew (%Hlocswf & Hpool)".
  destruct (p !! q) as [tm|] eqn:Hq; last by iFrame.
  iExFalso.
  iDestruct (big_sepM_lookup_acc _ _ q _ Hq with "Hpool") as "[Hc _]".
  iDestruct "Hc" as (ls) "(_ & Hc & _)".
  iDestruct "Hnew" as (yt tl) "(Hpp & _)".
  iDestruct "Hc" as (yt' tl') "(Hpp' & _)".
  iDestruct (typed_pointsto_split with "Hpp") as "(Hs1 & _)".
  iDestruct (typed_pointsto_split with "Hpp'") as "(Hs2 & _)".
  iEval (rewrite typed_pointsto_unseal_eq /=) in "Hs1".
  iEval (rewrite typed_pointsto_unseal_eq /=) in "Hs2".
  iDestruct "Hs1" as "[Hs1 _]". iDestruct "Hs2" as "[Hs2 _]".
  iCombine "Hs1 Hs2" gives %[Hvalid _].
  by destruct (exclusive_l (DfracOwn 1) (DfracOwn 1) Hvalid).
Qed.

(* ----- the store's heap state --------------------------------------------- *)

Definition own_registry_field (l : loc) (bind : gmap P loc) : iProp Σ :=
  ∃ types_mref : loc,
    "Htypesf" ∷ l ↦ types_mref ∗
    "Htypesmap" ∷ own_map types_mref (DfracOwn 1) bind.

Definition own_pending_field (l : loc)
    (pend : list (TId * IntegrateInput (A := A))) : iProp Σ :=
  ∃ pend_sl : slice.t,
    "Hpendf" ∷ l ↦ pend_sl ∗
    "Hpend"  ∷ own_update_structs pend_sl (DfracOwn 1) pend.

Definition own_pending_deletes_field (l : loc) (pdel : list delete_span) : iProp Σ :=
  ∃ pdel_sl : slice.t,
    "Hpddelf" ∷ l ↦ pdel_sl ∗
    "Hpddel"  ∷ own_delete_spans pdel_sl (DfracOwn 1) pdel.

Definition own_deleted_set_field (l : loc) : iProp Σ :=
  ∃ deletedSetVal : yjs.deletedSet.t, l ↦ deletedSetVal.

(** The store's fields: the client id and clock, the deleted-set struct
    (not modeled: no verified method reads it through the field; the delete
    set's ghost model is [own_delete_set]), the item index
    ([store.items] and the per-client run map it points to), the root registry
    ([store.types] and its name -> type-loc map), the type pool, and the two
    buffers ([store.pending], [store.pendingDeletes]) over their model lists.
    The field pointers and buffer slices are existential: no spec names them,
    and no field has a predicate of its own, so a spec can only take the
    store whole ([own_store_state]). *)

(** [own_items_field l locs p]: the [items] field, the index over the
    pool's entries ([own_item_map]). *)
Definition own_items_field (l : loc) (locs : gmap loc (list loc)) (p : pool) : iProp Σ :=
  ∃ items_mref : loc,
    "Hitemsf" ∷ l ↦ items_mref ∗
    "Hitemmap" ∷ own_item_map items_mref (DfracOwn 1) locs p.

(** [own_store_fields s state]: every field of the store at its
    state: the item index over the pool's entries and the type
    pool as [own_type_pool]. *)
Definition own_store_fields (s : loc) (state : store_state) : iProp Σ :=
  "Hclient" ∷ (s .[(yjs.store.t), "client"]) ↦ ss_client state ∗
  "Hclock" ∷ (s .[(yjs.store.t), "clock"]) ↦ ss_clock state ∗
  "HdeletedSet" ∷ own_deleted_set_field (s .[(yjs.store.t), "deletedSet"]) ∗
  "Hitems" ∷ own_items_field (s .[(yjs.store.t), "items"]) (ss_locs state) (ss_pool state) ∗
  "Hregistry" ∷ own_registry_field (s .[(yjs.store.t), "types"]) (ss_bind state) ∗
  "Htypes" ∷ own_type_pool (DfracOwn 1) (ss_locs state) (ss_pool state) ∗
  "Hpending" ∷ own_pending_field (s .[(yjs.store.t), "pending"]) (ss_pending state) ∗
  "Hpdeletes" ∷ own_pending_deletes_field (s .[(yjs.store.t), "pendingDeletes"]) (ss_pending_deletes state).

(** [store_invs state]: the invariants every store method preserves: the
    pure pool invariants ([pool_invs]) and the registry's coherence. The
    address [NoDup] is not here; it is [own_type_pool]'s [locs_wf]. *)
Definition store_invs (state : store_state) : Prop :=
  pool_invs (ss_pool state) ∧ pool_registry_coh (ss_bind state) (ss_pool state).

(** [own_store_state s state]: THE store at its state, the
    PRIMITIVE store predicate: every field of the struct at [state], with
    the invariants every method preserves. *)
Definition own_store_state (s : loc) (state : store_state) : iProp Σ :=
  "Hfields" ∷ own_store_fields s state ∗
  "%Hinvs" ∷ ⌜store_invs state⌝.

(** The pool invariants, read off the store. *)
Lemma own_store_state_run_pool_invs (s : loc) (state : store_state) :
  own_store_state s state -∗ ⌜pool_invs (ss_pool state)⌝.
Proof.
  iIntros "(_ & %Hinvs)". iPureIntro. exact (proj1 Hinvs).
Qed.

(** The address map is aligned with the pool: read off the store. *)
Lemma own_store_state_aligned (s : loc) (state : store_state) :
  own_store_state s state -∗ ⌜locs_aligned (ss_locs state) (ss_pool state)⌝.
Proof.
  iIntros "(Hfields & _)".
  iDestruct "Hfields" as "(_ & _ & _ & _ & _ & Htypes & _ & _)".
  iDestruct "Htypes" as "(%Hlocswf & _)".
  iPureIntro. destruct Hlocswf as (Hdom & _ & Hlens). split; [exact Hdom | exact Hlens].
Qed.

(** Every run of the store is chained ([run_wf]): the heap pin of the run
    spine, read off the store. *)
Lemma own_store_state_run_wf (s : loc) (state : store_state) :
  own_store_state s state -∗ ⌜∀ r, r ∈ all_runs (ss_pool state) -> run_wf (run_items r)⌝.
Proof.
  iIntros "(Hfields & _)".
  iDestruct "Hfields" as "(_ & _ & _ & _ & _ & Htypes & _ & _)".
  iApply (own_type_pool_run_wf with "Htypes").
Qed.


(** Every registered type's document is a valid document: the yType body's
    invariant, read off the pool and off the whole store. *)
Lemma own_type_pool_arr_inv (dq : dfrac) (locs : gmap loc (list loc)) (p : pool) :
  own_type_pool dq locs p -∗
  ⌜∀ parent tm, p !! parent = Some tm -> YjsArrInvariant (tm_arr tm)⌝.
Proof.
  iIntros "(%Hlocswf & Hpool)".
  iAssert ([∗ map] parent ↦ tm ∈ p, ⌜YjsArrInvariant (tm_arr tm)⌝)%I
    with "[Hpool]" as "H".
  { iApply (big_sepM_impl with "Hpool").
    iIntros "!#" (parent tm Hp) "H".
    iDestruct "H" as (ls) "(_ & _ & %Hinv)". by iPureIntro. }
  iDestruct (big_sepM_pure with "H") as %Hall.
  iPureIntro. move=> parent tm Hp. exact (Hall parent tm Hp).
Qed.

(** Every registered type's document satisfies the array invariant, and the
    registry is coherent with the pool: read off the store. *)
Lemma own_store_state_arr_inv (s : loc) (state : store_state) :
  own_store_state s state -∗
  ⌜∀ parent tm, ss_pool state !! parent = Some tm -> YjsArrInvariant (tm_arr tm)⌝.
Proof.
  iIntros "(Hfields & _)".
  iDestruct "Hfields" as "(_ & _ & _ & _ & _ & Htypes & _ & _)".
  iApply (own_type_pool_arr_inv with "Htypes").
Qed.

Lemma own_store_state_registry_coh (s : loc) (state : store_state) :
  own_store_state s state -∗ ⌜pool_registry_coh (ss_bind state) (ss_pool state)⌝.
Proof.
  iIntros "(_ & %Hinvs)". iPureIntro. exact (proj2 Hinvs).
Qed.

(** Borrow the [k]-th node of the type at [parent] out of a
    pool, exposing its heap struct with the id and content length the
    loop reads (the cell borrow). *)
Lemma own_type_pool_node_acc (locs : gmap loc (list loc)) (p : pool) (parent : loc)
    (ls : list loc) (tm : type_model) (k : nat) (lc : loc) (r : ItemRun) :
  locs !! parent = Some ls ->
  p !! parent = Some tm ->
  ls !! k = Some lc ->
  tm_runs tm !! k = Some r ->
  own_type_pool (DfracOwn 1) locs p -∗
  ∃ itemVal : yjs.item.t,
    "%Haccid" ∷ ⌜item_id (run_head_item r) = toYjsId itemVal.(yjs.item.id')⌝ ∗
    "%Haccle" ∷ ⌜length (itemVal.(yjs.item.content').(yjs.content.content')) = length (run_items r)⌝ ∗
    "%Haccpar" ∷ ⌜itemVal.(yjs.item.parent') = parent⌝ ∗
    "Haccval" ∷ lc ↦ itemVal ∗
    "Haccback" ∷ (lc ↦ itemVal -∗ own_type_pool (DfracOwn 1) locs p).
Proof.
  move=> Hls Hp Hlk Hrk. iIntros "(%Hlocswf & Hpool)".
  iDestruct (big_sepM_delete _ _ parent _ Hp with "Hpool") as "[Hpc Hrest]".
  iDestruct "Hpc" as (ls0) "(%Hls0 & Hyt & %Harrinv)".
  rewrite Hls in Hls0. injection Hls0 as <-.
  iDestruct "Hyt" as (yt tl) "(Hparent & Hdll & %Hlen)".
  iDestruct (own_dll_acc (DfracOwn 1) parent _ tl ls (tm_runs tm) k lc r Hlk Hrk
               with "Hdll")
    as (prev' nxt') "(%Hcl & %Hcr & %Hrun & %Hperchar & %Hclen & Hnode & Hback)".
  iDestruct "Hnode" as (itemVal olid orid)
    "(Hval & Hol & Hor & %Hinl & %Hinr & %Hid & %Hcont & %Hparf & %Hprevf & %Hnextf & %Hflags)".
  have Haccid : item_id (run_head_item r) = toYjsId itemVal.(yjs.item.id').
  { symmetry. exact Hid. }
  have Haccle : length (itemVal.(yjs.item.content').(yjs.content.content')) = length (run_items r).
  { have Hstr : itemVal.(yjs.item.content').(yjs.content.content')
              = in_content (input_of_run r) := Hcont.
    rewrite Hstr. exact Hclen. }
  iExists itemVal. iFrame "Hval".
  iSplitR; first (iPureIntro; exact Haccid).
  iSplitR; first (iPureIntro; exact Haccle).
  iSplitR; first (iPureIntro; exact Hparf).
  iIntros "Hval".
  iAssert (own_item_node lc (DfracOwn 1) (input_of_run r) (run_deleted r) parent prev' nxt')
    with "[Hval Hol Hor]" as "Hnode".
  { iExists itemVal, olid, orid. iFrame "Hval Hol Hor".
    iPureIntro. split_and!;
      [exact Hinl | exact Hinr | exact Hid | exact Hcont | exact Hparf
      | exact Hprevf | exact Hnextf | exact Hflags]. }
  iDestruct ("Hback" with "Hnode") as "Hdll".
  iSplitR; first (iPureIntro; exact Hlocswf).
  iApply big_sepM_delete; first exact Hp.
  iFrame "Hrest". iExists ls. iSplitR; first (iPureIntro; exact Hls).
  iSplitL; last (iPureIntro; exact Harrinv).
  iExists yt, tl. iFrame "Hparent Hdll". iPureIntro. exact Hlen.
Qed.

(** Borrow the [k]-th node of the type at [parent] out of the store, exposing
    its heap struct with the id and content length the delete loop reads
    ([own_type_pool_node_acc] behind the store's lift and lower). *)
Lemma own_store_state_node_acc (s : loc) (state : store_state)
    (parent : loc) (ls : list loc) (tm : type_model) (k : nat) (lc : loc) (r : ItemRun) :
  ss_locs state !! parent = Some ls ->
  ss_pool state !! parent = Some tm ->
  ls !! k = Some lc ->
  tm_runs tm !! k = Some r ->
  own_store_state s state -∗
  ∃ itemVal : yjs.item.t,
    "%Haccid" ∷ ⌜item_id (run_head_item r) = toYjsId itemVal.(yjs.item.id')⌝ ∗
    "%Haccle" ∷ ⌜length (itemVal.(yjs.item.content').(yjs.content.content')) = length (run_items r)⌝ ∗
    "%Haccpar" ∷ ⌜itemVal.(yjs.item.parent') = parent⌝ ∗
    "Haccval" ∷ lc ↦ itemVal ∗
    "Haccback" ∷ (lc ↦ itemVal -∗ own_store_state s state).
Proof.
  move=> Hls Hp Hlk Hrk.
  destruct state as [client0 k0 locs p bind pend pdel]. simpl in *.
  iIntros "(Hfields & %Hinvs)".
  iDestruct "Hfields" as "(Hclient & Hclock & HdeletedSet & Hitems & Hregistry & Htypes & Hpending & Hpdeletes)".
  iEval (simpl) in "Htypes".
  iDestruct (own_type_pool_node_acc locs p parent ls tm k lc r Hls Hp Hlk Hrk with "Htypes") as (itemVal) "H".
  iNamed "H".
  iExists itemVal. iFrame "Haccval".
  iSplitR; first (iPureIntro; exact Haccid).
  iSplitR; first (iPureIntro; exact Haccle).
  iSplitR; first (iPureIntro; exact Haccpar).
  iIntros "Haccval".
  iDestruct ("Haccback" with "Haccval") as "Htypes".
  iSplitL; last (iPureIntro; exact Hinvs).
  rewrite /own_store_fields /=.
  iFrame "Hclient Hclock HdeletedSet Hitems Hregistry Htypes Hpending Hpdeletes".
Qed.

(** Borrow the [k]-th node of the type at [parent] out of the
    pool with its links: [own_type_pool_node_acc] plus the neighbour
    addresses read off the address list and the flag byte read off the
    run's tombstone bit. What a cursor walk ([Text.Delete]) reads. *)
Lemma own_type_pool_node_acc_links (locs : gmap loc (list loc)) (p : pool) (parent : loc)
    (ls : list loc) (tm : type_model) (k : nat) (lc : loc) (r : ItemRun) :
  locs !! parent = Some ls ->
  p !! parent = Some tm ->
  ls !! k = Some lc ->
  tm_runs tm !! k = Some r ->
  own_type_pool (DfracOwn 1) locs p -∗
  ∃ itemVal : yjs.item.t,
    "%Haccid" ∷ ⌜item_id (run_head_item r) = toYjsId itemVal.(yjs.item.id')⌝ ∗
    "%Haccle" ∷ ⌜length (itemVal.(yjs.item.content').(yjs.content.content')) = length (run_items r)⌝ ∗
    "%Haccpar" ∷ ⌜itemVal.(yjs.item.parent') = parent⌝ ∗
    "%Haccleft" ∷ ⌜itemVal.(yjs.item.left') = loc_at ls (Z.of_nat k - 1)⌝ ∗
    "%Haccright" ∷ ⌜itemVal.(yjs.item.right') = loc_at ls (Z.of_nat k + 1)⌝ ∗
    "%Haccflags" ∷ ⌜itemVal.(yjs.item.flags') = (if run_deleted r then W8 6 else W8 2)⌝ ∗
    "Haccval" ∷ lc ↦ itemVal ∗
    "Haccback" ∷ (lc ↦ itemVal -∗ own_type_pool (DfracOwn 1) locs p).
Proof.
  move=> Hls Hp Hlk Hrk. iIntros "(%Hlocswf & Hpool)".
  iDestruct (big_sepM_delete _ _ parent _ Hp with "Hpool") as "[Hpc Hrest]".
  iDestruct "Hpc" as (ls0) "(%Hls0 & Hyt & %Harrinv)".
  rewrite Hls in Hls0. injection Hls0 as <-.
  iDestruct "Hyt" as (yt tl) "(Hparent & Hdll & %Hlen)".
  iDestruct (own_dll_acc (DfracOwn 1) parent _ tl ls (tm_runs tm) k lc r Hlk Hrk
               with "Hdll")
    as (prev' nxt') "(%Hcl & %Hcr & %Hrun & %Hperchar & %Hclen & Hnode & Hback)".
  iDestruct "Hnode" as (itemVal olid orid)
    "(Hval & Hol & Hor & %Hinl & %Hinr & %Hid & %Hcont & %Hparf & %Hprevf & %Hnextf & %Hflags)".
  have Haccid : item_id (run_head_item r) = toYjsId itemVal.(yjs.item.id').
  { symmetry. exact Hid. }
  have Haccle : length (itemVal.(yjs.item.content').(yjs.content.content')) = length (run_items r).
  { have Hstr : itemVal.(yjs.item.content').(yjs.content.content')
              = in_content (input_of_run r) := Hcont.
    rewrite Hstr. exact Hclen. }
  iExists itemVal. iFrame "Hval".
  iSplitR; first (iPureIntro; exact Haccid).
  iSplitR; first (iPureIntro; exact Haccle).
  iSplitR; first (iPureIntro; exact Hparf).
  iSplitR; first (iPureIntro; rewrite Hprevf Hcl //).
  iSplitR; first (iPureIntro; rewrite Hnextf Hcr //).
  iSplitR; first (iPureIntro; exact Hflags).
  iIntros "Hval".
  iAssert (own_item_node lc (DfracOwn 1) (input_of_run r) (run_deleted r) parent prev' nxt')
    with "[Hval Hol Hor]" as "Hnode".
  { iExists itemVal, olid, orid. iFrame "Hval Hol Hor".
    iPureIntro. split_and!;
      [exact Hinl | exact Hinr | exact Hid | exact Hcont | exact Hparf
      | exact Hprevf | exact Hnextf | exact Hflags]. }
  iDestruct ("Hback" with "Hnode") as "Hdll".
  iSplitR; first (iPureIntro; exact Hlocswf).
  iApply big_sepM_delete; first exact Hp.
  iFrame "Hrest". iExists ls. iSplitR; first (iPureIntro; exact Hls).
  iSplitL; last (iPureIntro; exact Harrinv).
  iExists yt, tl. iFrame "Hparent Hdll". iPureIntro. exact Hlen.
Qed.

(** [own_type_pool_node_acc_links] behind the store's lift and lower. *)
Lemma own_store_state_node_acc_links (s : loc) (state : store_state)
    (parent : loc) (ls : list loc) (tm : type_model) (k : nat) (lc : loc) (r : ItemRun) :
  ss_locs state !! parent = Some ls ->
  ss_pool state !! parent = Some tm ->
  ls !! k = Some lc ->
  tm_runs tm !! k = Some r ->
  own_store_state s state -∗
  ∃ itemVal : yjs.item.t,
    "%Haccid" ∷ ⌜item_id (run_head_item r) = toYjsId itemVal.(yjs.item.id')⌝ ∗
    "%Haccle" ∷ ⌜length (itemVal.(yjs.item.content').(yjs.content.content')) = length (run_items r)⌝ ∗
    "%Haccpar" ∷ ⌜itemVal.(yjs.item.parent') = parent⌝ ∗
    "%Haccleft" ∷ ⌜itemVal.(yjs.item.left') = loc_at ls (Z.of_nat k - 1)⌝ ∗
    "%Haccright" ∷ ⌜itemVal.(yjs.item.right') = loc_at ls (Z.of_nat k + 1)⌝ ∗
    "%Haccflags" ∷ ⌜itemVal.(yjs.item.flags') = (if run_deleted r then W8 6 else W8 2)⌝ ∗
    "Haccval" ∷ lc ↦ itemVal ∗
    "Haccback" ∷ (lc ↦ itemVal -∗ own_store_state s state).
Proof.
  move=> Hls Hp Hlk Hrk.
  destruct state as [client0 k0 locs p bind pend pdel]. simpl in *.
  iIntros "(Hfields & %Hinvs)".
  iDestruct "Hfields" as "(Hclient & Hclock & HdeletedSet & Hitems & Hregistry & Htypes & Hpending & Hpdeletes)".
  iEval (simpl) in "Htypes".
  iDestruct (own_type_pool_node_acc_links locs p parent ls tm k lc r Hls Hp Hlk Hrk with "Htypes") as (itemVal) "H".
  iNamed "H".
  iExists itemVal. iFrame "Haccval".
  iSplitR; first (iPureIntro; exact Haccid).
  iSplitR; first (iPureIntro; exact Haccle).
  iSplitR; first (iPureIntro; exact Haccpar).
  iSplitR; first (iPureIntro; exact Haccleft).
  iSplitR; first (iPureIntro; exact Haccright).
  iSplitR; first (iPureIntro; exact Haccflags).
  iIntros "Haccval".
  iDestruct ("Haccback" with "Haccval") as "Htypes".
  iSplitL; last (iPureIntro; exact Hinvs).
  rewrite /own_store_fields /=.
  iFrame "Hclient Hclock HdeletedSet Hitems Hregistry Htypes Hpending Hpdeletes".
Qed.

(** Borrow the type at [parent] out of the store as its run view, for a
    read that leaves it as it is ([yType.findPos], the [len] field). *)
Lemma own_store_state_ytype_acc (s : loc) (state : store_state)
    (parent : loc) (ls : list loc) (tm : type_model) :
  ss_locs state !! parent = Some ls ->
  ss_pool state !! parent = Some tm ->
  own_store_state s state -∗
  own_ytype parent (DfracOwn 1) ls tm ∗
  (own_ytype parent (DfracOwn 1) ls tm -∗ own_store_state s state).
Proof.
  move=> Hls Hp.
  destruct state as [client0 k0 locs p bind pend pdel]. simpl in *.
  iIntros "(Hfields & %Hinvs)".
  iDestruct "Hfields" as "(Hclient & Hclock & HdeletedSet & Hitems & Hregistry & Htypes & Hpending & Hpdeletes)".
  iEval (simpl) in "Htypes".
  iDestruct "Htypes" as "(%Hlocswf & Hpool)".
  iDestruct (big_sepM_lookup_acc _ _ parent _ Hp with "Hpool") as "[Hpc Hclose]".
  iDestruct "Hpc" as (ls0) "(%Hls0 & Hyt & %Hinv)".
  rewrite Hls in Hls0. injection Hls0 as <-.
  iFrame "Hyt".
  iIntros "Hyt".
  iDestruct ("Hclose" with "[Hyt]") as "Hpool".
  { iExists ls. iFrame "Hyt". iPureIntro. split; [exact Hls | exact Hinv]. }
  iSplitL; last (iPureIntro; exact Hinvs).
  rewrite /own_store_fields /=.
  iFrame "Hclient Hclock HdeletedSet Hitems Hregistry Hpending Hpdeletes Hpool".
  by iPureIntro.
Qed.

(** The store's clock and client fields, borrowed out of the
    store: the clock may be rewritten (the store invariants say nothing
    about it; [Text.Insert] bumps it per inserted item), the client is
    read. *)
Lemma own_store_state_clock_acc (s : loc) (state : store_state) :
  own_store_state s state -∗
  (s .[(yjs.store.t), "clock"]) ↦ ss_clock state ∗
  (∀ k' : w64, (s .[(yjs.store.t), "clock"]) ↦ k' -∗ own_store_state s (state <| ss_clock := k' |>)).
Proof.
  destruct state as [client0 k0 locs p bind pend pdel]. simpl.
  iIntros "(Hfields & %Hinvs)".
  iDestruct "Hfields" as "(Hclient & Hclock & HdeletedSet & Hitems & Hregistry & Htypes & Hpending & Hpdeletes)".
  iFrame "Hclock".
  iIntros (k') "Hclock".
  iSplitL; last (iPureIntro; exact Hinvs).
  rewrite /own_store_fields /=.
  iFrame "Hclient Hclock HdeletedSet Hitems Hregistry Htypes Hpending Hpdeletes".
Qed.

Lemma own_store_state_client_acc (s : loc) (state : store_state) :
  own_store_state s state -∗
  (s .[(yjs.store.t), "client"]) ↦ ss_client state ∗
  ((s .[(yjs.store.t), "client"]) ↦ ss_client state -∗ own_store_state s state).
Proof.
  destruct state as [client0 k0 locs p bind pend pdel]. simpl.
  iIntros "(Hfields & %Hinvs)".
  iDestruct "Hfields" as "(Hclient & Hclock & HdeletedSet & Hitems & Hregistry & Htypes & Hpending & Hpdeletes)".
  iFrame "Hclient".
  iIntros "Hclient".
  iSplitL; last (iPureIntro; exact Hinvs).
  rewrite /own_store_fields /=.
  iFrame "Hclient Hclock HdeletedSet Hitems Hregistry Htypes Hpending Hpdeletes".
Qed.

(** One id lives in one slot: two covering slots of the store's pool are
    the same slot ([pool_covers_unique] off the pool invariants). What
    lets a split helper's caller identify the node [GetNode] returned with
    the slot it holds. *)
Lemma own_store_state_covers_unique (s : loc) (state : store_state) :
  own_store_state s state -∗
  ⌜∀ (d : YjsId) (q1 q2 : loc) (k1 k2 : nat),
     pool_covers (ss_pool state) q1 k1 d ->
     pool_covers (ss_pool state) q2 k2 d ->
     q1 = q2 ∧ k1 = k2⌝.
Proof.
  iIntros "H".
  iDestruct (own_store_state_run_pool_invs with "H") as %Hrpi.
  iPureIntro. move=> d q1 q2 k1 k2 Hcov1 Hcov2.
  exact (pool_covers_unique (ss_pool state) d q1 q2 k1 k2 Hrpi Hcov1 Hcov2).
Qed.

Definition store_inv_ro (γs : store_names) (locs : gmap loc (list loc)) (p : pool) (q : Qp) : iProp Σ :=
  "Hseq" ∷ own γs.(sn_seq) (●{DfracOwn q} ((λ tm, (list_to_set (tm_arr tm) : gset (YjsItem A))) <$> p) : seqUR) ∗
  "Htypes" ∷ own_type_pool (DfracOwn q) locs p.

#[global] Instance store_inv_ro_fractional γs locs p : Fractional (store_inv_ro γs locs p).
Proof.
  rewrite /store_inv_ro /named. apply fractional_sep.
  - intros q1 q2. rewrite -own_op -auth_auth_dfrac_op dfrac_op_own //.
  - apply own_type_pool_fractional.
Qed.

(** [store_inv_excl]: the complement of [store_inv_ro] within [store_inv], the
    mutable-exclusive state the read lock does NOT share (struct fields, the
    per-client item map, the registry [ghost_map_auth], the ghost history, and
    the counter / registry side conditions). It stays whole in the lock
    invariant while readers hold fractional shares of [store_inv_ro]. *)
Definition store_inv_excl (s_loc : loc) (γs : store_names) (γh : history_names)
    (client k : w64) (items_mref types_mref : loc) (deletedSetVal : yjs.deletedSet.t)
    (pend_sl pdel_sl : slice.t)
    (locs : gmap loc (list loc)) (p : pool) (bind : gmap P loc) (h : list Ev) (m : DocModel)
    (pend : list (TId * IntegrateInput (A := A)))
    (pdel : list delete_span) : iProp Σ :=
    ∃ (acc : gset YjsId),
    "Hclient" ∷ (s_loc .[(yjs.store.t), "client"]) ↦ client ∗
    "#Hclientpin" ∷ is_store_client γs (uint.nat client) ∗
    "Hclock"  ∷ (s_loc .[(yjs.store.t), "clock"]) ↦ k ∗
    "Hitemsf" ∷ (s_loc .[(yjs.store.t), "items"]) ↦ items_mref ∗
    "Hitemmap" ∷ own_item_map items_mref (DfracOwn 1) locs p ∗
    "Htypesf" ∷ (s_loc .[(yjs.store.t), "types"]) ↦ types_mref ∗
    "Htypesmap" ∷ own_map types_mref (DfracOwn 1) bind ∗
    "HdeletedSet"   ∷ (s_loc .[(yjs.store.t), "deletedSet"]) ↦ deletedSetVal ∗
    (* the pending buffer (issue #40): the buffered structs whose dependencies
       have not arrived, with their certificates (persistent), so the next
       applyUpdate can re-certify the whole drained buffer without the caller
       knowing what is buffered. *)
    "Hpendf"  ∷ (s_loc .[(yjs.store.t), "pending"]) ↦ pend_sl ∗
    "Hpend"   ∷ own_update_structs pend_sl (DfracOwn 1) pend ∗
    "Hpddelf" ∷ (s_loc .[(yjs.store.t), "pendingDeletes"]) ↦ pdel_sl ∗
    "Hpddel"  ∷ own_delete_spans pdel_sl (DfracOwn 1) pdel ∗
    "#Hpendcert" ∷ is_pending_certified γh (expand_inputs pend) ∗
    "%Hpendroot" ∷ ⌜is_pending_rooted pend⌝ ∗
    "%Hpendbnd" ∷ ⌜∀ typedInput : TId * IntegrateInput (A := A), typedInput ∈ pend ->
                    (Z.of_nat (clock (in_id typedInput.2)) + Z.of_nat (length (in_content typedInput.2)) < 2^64)%Z⌝ ∗
    "%Hctr"   ∷ ⌜∀ parent tm x, p !! parent = Some tm → x ∈ tm_arr tm →
                   clientId (item_id x) = uint.nat client →
                   (clock (item_id x) < uint.nat k)%nat⌝ ∗
    (* the pool invariants (issue #28): every run
       satisfies [run_invs] and the clock ranges are disjoint (the address
       [NoDup] is [own_type_pool]'s [locs_wf], in the read-shareable
       half) *)
    "%Hpool" ∷ ⌜pool_invs p⌝ ∗
    "HtypesAuth" ∷ ghost_map_auth γs.(sn_types) 1 bind ∗
    "#Hbinds" ∷ ([∗ map] name ↦ q ∈ bind, is_type_binding γs.(sn_types) name q) ∗
    "Hhist"   ∷ own_client_history γh (uint.nat client) h ∗
    "%Hhcoh"  ∷ ⌜history_state_coh h m⌝ ∗
    (* the registry coherence: [bind] / the pool / the replayed model [m] fit *)
    "%Hregcoh" ∷ ⌜pool_doc_registry_coh m bind p⌝ ∗
    (* no-loss accepted-id layer (this branch): the grow-only accepted set and
       its coherence [acc ⊆ delivered_ids h ∪ pending ids] *)
    "Hacc" ∷ own γs.(sn_accepted) (● acc : accUR) ∗
    (* the monotone delete set with its model-domain bound (plan-delete-set D1) *)
    "Hdelete_set" ∷ own_delete_set γs m (all_runs p) ∗
    "%Hacccoh" ∷ ⌜accepted_coh acc h pend⌝.

#[global] Instance store_inv_ro_timeless γs locs p q : Timeless (store_inv_ro γs locs p q).
Proof. rewrite /store_inv_ro. apply _. Qed.

#[global] Instance store_inv_excl_timeless s_loc γs γh client k im tm deletedSetVal psl pdsl locs p bind h m pend pdel :
  Timeless (store_inv_excl s_loc γs γh client k im tm deletedSetVal psl pdsl locs p bind h m pend pdel).
Proof. rewrite /store_inv_excl /own_update_structs /own_delete_spans /is_update_item. apply _. Qed.

(** [store_inv s_loc γs γh]: everything the store lock protects.
    - store struct NON-mu fields (client/clock/items/types/deletedSet field ptrs;
      [mu] is owned by the [sync.RWMutex] ([rwmutex.is_RWMutex] in [is_Store]), not here);
    - the item-set authority [own γ (●…)] per type loc (id-set), whose fragments
      are the [is_type_lb] lower bounds / registration witnesses [Text] holds;
    - each registered type's DLL (keyed by [parent]) + [YjsArrInvariant];
    - the store's per-client item set ([store.items] holds every
      integrated item's loc, clock-sorted — maintained by Integrate's [AddNode]);
    - the global per-client counter [Hctr] (source of [maximalId]) and its
      pool-wide shadow [Hcellctr] (every same-local-client run across ALL types
      has heap clock [< k]), what lets [Text.Insert] discharge the wrapper's
      global-max side condition for the OTHER types, whose runs are sealed
      in the [big_sepM] accumulator once THIS type is borrowed; re-established at
      each [Unlock] from the loop's carried bound (no [W64] round-trip).
    [client]/[k]/[types] etc. are existential; the fixed lock invariant hides
    the per-operation state. The item index and [Htypes] share the SAME state, so
    Insert grows both consistently (DLL splice + [AddNode] tail-append).

    Network layer (issues #42 / #49): the lock also holds this replica's
    exclusive ghost-history element [own_client_history] for the store's
    client. The history's replayed *doc model* [m] is coherent with the whole
    registry, not a single governed type ([history_state_coh h m], plus
    [Hmtypes]: each registered type's [tm_arr] equals [doc_model_get m] at its
    bound name).

    The body is [store_inv_excl] (the mutable-exclusive clauses, documented
    there) next to [store_inv_ro] at full fraction: exactly the two halves
    the RWMutex tie invariant tracks separately while readers hold shares,
    so [store_inv_bridge] is definitional. *)
Definition store_inv (s_loc : loc) (γs : store_names) (γh : history_names) : iProp Σ :=
  ∃ (client k : w64) (items_mref types_mref : loc) (deletedSetVal : yjs.deletedSet.t)
    (pend_sl pdel_sl : slice.t)
    (locs : gmap loc (list loc)) (p : pool) (bind : gmap P loc) (h : list Ev) (m : DocModel)
    (pend : list (TId * IntegrateInput (A := A))) (pdel : list delete_span),
    "Hexcl" ∷ store_inv_excl s_loc γs γh client k items_mref types_mref deletedSetVal pend_sl pdel_sl locs p bind h m pend pdel ∗
    "Hro"   ∷ store_inv_ro γs locs p 1.

(** [store_inv] is timeless (heap points-to + ghost state over discrete cameras +
    pure facts), so the write [Lock] wrapper hands it back WITHOUT a [▷] even
    though it is extracted from the tie invariant — the Insert/Delete proofs use
    it immediately (no intervening program step to strip a later). *)
#[global] Instance store_inv_timeless s_loc γs γh : Timeless (store_inv s_loc γs γh).
Proof. rewrite /store_inv. apply _. Qed.

(** ---------------------------------------------------------------------------
    Store lock = a [sync.RWMutex] (y-octo's [Arc<RwLock<DocStore>>]).

    Writers (Insert/Delete/GetOrCreateText/applyUpdate) take the write lock; the pure
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

(** Fractional agreement on the store's addresses and pool between a
    reader's share and the lock invariant. *)
Definition pool_frag (γs : store_names) (q : Qp) (locs : gmap loc (list loc)) (p : pool) : iProp Σ :=
  own γs.(sn_types_agree) (to_frac_agree q ((locs, p) : leibnizO addressed_pool)).

Definition storeN : namespace := nroot .@ "yjs_store".

Definition tie_body (s_loc : loc) (γs : store_names) (γh : history_names) (st : rwmutex) : iProp Σ :=
  match st with
  | Locked => ∃ locs p, own_tok_auth γs.(sn_rrlocked) 0 ∗ pool_frag γs 1 locs p
  | RLocked n =>
      own_tok_auth γs.(sn_rrlocked) n ∗ own_toks γs.(sn_rmax) n ∗ own_wlock γs ∗
      (∃ client k items_mref types_mref deletedSetVal pend_sl pdel_sl locs p bind h m pend pdel,
         pool_frag γs (frac_of n) locs p ∗
         store_inv_excl s_loc γs γh client k items_mref types_mref deletedSetVal pend_sl pdel_sl locs p bind h m pend pdel ∗
         store_inv_ro γs locs p (frac_of n))
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

Definition own_read_locked (γs : store_names) (locs : gmap loc (list loc)) (p : pool) : iProp Σ :=
  own_toks γs.(sn_rrlocked) 1 ∗ pool_frag γs rwmutex_guard.rfrac locs p.

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

(** [is_applied_root_lb γs applied m]: one monotone content certificate per
    applied wire item (issue #97 names the [applyUpdate] postcondition). Each
    applied tagged input targets a root [RootId name], and [name]'s full item
    set in the post-delivery model [m] is a lower bound of the store's grow-only
    content for that root. This is what [applyUpdate] hands back so the caller
    learns "the store now contains at least this" per delivered root. *)
Definition is_applied_root_lb (γs : store_names)
    (applied : list (TId * IntegrateInput (A := A))) (m : DocModel) : iProp Σ :=
  [∗ list] typedInput ∈ applied, ∃ name : P, ⌜typedInput.1 = RootId name⌝ ∗
    is_root_lb γs name (list_to_set (doc_model_get m typedInput.1)).

#[global] Instance is_applied_root_lb_persistent γs applied m :
  Persistent (is_applied_root_lb γs applied m).
Proof. rewrite /is_applied_root_lb. apply _. Qed.

(** [is_applied_certs γs applied m]: what applying a batch leaves behind for
    the applied wire items: the root content certificates
    ([is_applied_root_lb]) and the fact that every applied char is in the
    model [m] under its root. The postcondition of [applyUpdate],
    [Doc.ApplySyncUpdate] and [Doc.ApplyEncodedUpdate]. *)
Definition is_applied_certs (γs : store_names)
    (applied : list (TId * IntegrateInput (A := A))) (m : DocModel) : iProp Σ :=
  is_applied_root_lb γs applied m ∗
  ⌜∀ x, x ∈ expand_inputs applied -> ∃ it, item_id it = in_id x.2 ∧ it ∈ doc_model_get m x.1⌝.

#[global] Instance is_applied_certs_persistent γs applied m :
  Persistent (is_applied_certs γs applied m).
Proof. rewrite /is_applied_certs. apply _. Qed.

(** [own_store s γs γh c h m pend]: the WHOLE lock-protected store state, as
    one exclusive predicate over its public model: this replica is client
    [c] with ghost op history [h], whose replayed doc model is [m], and
    [pend] buffered wire items. Everything else (the state
    [own_store_state] with its addresses and pool, [bind], [pdel], the local
    clock) is existential. [store_inv] is exactly its model-existential closure
    ([store_inv_own_store] below), so the write lock hands out [own_store]
    ([wp_Store__wlock]) and takes it back ([wp_Store__wunlock]); every spec
    over store state is stated [own_store] in, [own_store] out.

    The pool invariants and the registry coherence live inside
    [own_store_state]. *)
Definition own_store (s_loc : loc) (γs : store_names) (γh : history_names)
    (c : ClientId) (h : list Ev) (m : DocModel)
    (pend : list (TId * IntegrateInput (A := A))) : iProp Σ :=
  ∃ (client k : w64) (pdel : list delete_span)
    (locs : gmap loc (list loc)) (p : pool) (bind : gmap P loc) (acc : gset YjsId),
    "%Hclientc" ∷ ⌜uint.nat client = c⌝ ∗
    "#Hclientpin" ∷ is_store_client γs c ∗
    "Hstate" ∷ own_store_state s_loc (MkStoreState client k locs p bind pend pdel) ∗
    "#Hpendcert" ∷ is_pending_certified γh (expand_inputs pend) ∗
    "%Hpendroot" ∷ ⌜is_pending_rooted pend⌝ ∗
    "%Hpendbnd" ∷ ⌜∀ typedInput : TId * IntegrateInput (A := A), typedInput ∈ pend ->
                    (Z.of_nat (clock (in_id typedInput.2)) + Z.of_nat (length (in_content typedInput.2)) < 2^64)%Z⌝ ∗
    "Hseq"    ∷ own γs.(sn_seq) (● ((λ tm, (list_to_set (tm_arr tm) : gset (YjsItem A))) <$> p) : seqUR) ∗
    "HtypesAuth" ∷ ghost_map_auth γs.(sn_types) 1 bind ∗
    "#Hbinds" ∷ ([∗ map] name ↦ q ∈ bind, is_type_binding γs.(sn_types) name q) ∗
    "Hhist"   ∷ own_client_history γh c h ∗
    "%Hregmodel" ∷ ⌜pool_registry_models m bind p⌝ ∗
    "%Hhcoh"  ∷ ⌜history_state_coh h m⌝ ∗
    "%Hctr"   ∷ ⌜∀ parent tm x, p !! parent = Some tm -> x ∈ tm_arr tm ->
                   clientId (item_id x) = c -> (clock (item_id x) < uint.nat k)%nat⌝ ∗
    (* no-loss accepted-id layer: matches [store_inv_excl] *)
    "Hacc" ∷ own γs.(sn_accepted) (● acc : accUR) ∗
    "Hdelete_set" ∷ own_delete_set γs m (all_runs p) ∗
    "%Hacccoh" ∷ ⌜accepted_coh acc h pend⌝.

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
#[global] Instance pool_frag_timeless γs q locs p : Timeless (pool_frag γs q locs p).
Proof. rewrite /pool_frag. apply _. Qed.

#[local] Instance tie_body_timeless s_loc γs γh st : Timeless (tie_body s_loc γs γh st).
Proof.
  destruct st; rewrite /tie_body;
    repeat first [ apply sep_timeless | apply exist_timeless; intros ? ]; apply _.
Qed.

#[global] Typeclasses Opaque tie_body.

(** A heap [[]idSpan] abstracts to a [gset YjsId]: the union of its spans'
    char ids is exactly [gs]. The Go set ops are [containsId] / [append] /
    reset to [[]]; the union makes membership (not order/duplicates) the
    observable, matching the pure [gset] with [∪] / [∈]. The representation
    carries [span_no_overflow] for every span so [containsId]'s [w64] range test is
    exact. Owning heap data, it takes a [dfrac] (appending needs
    [DfracOwn 1]). *)
Definition own_id_set (s : slice.t) (dq : dfrac) (gs : gset YjsId) : iProp Σ :=
  ∃ (vs : list yjs.idSpan.t),
    "Hsl" ∷ s ↦*{dq} vs ∗
    "Hcap" ∷ own_slice_cap yjs.idSpan.t s dq ∗
    "%Hwf" ∷ ⌜Forall span_no_overflow vs⌝ ∗
    "%Hset" ∷ ⌜⋃ (span_ids <$> vs) = gs⌝.

(** [integrate_loop_inv parent dq ls runs arr leftIdx rightIdx curR
    originLeftId originRightId newItemId loopResult conflict_l left_l
    right_l idsBeforeOrigin_l conflictIds_l offset cur curD idsBeforeOrigin
    conflictIds destIdx]: the loop invariant of [scanConflicts] (what
    [store/Integrate]'s [wp_scanConflicts] walks), coupling the Go loop
    state to a [set_find_integration_loop] run over the type at
    [(ls, runs, arr)], the anchor pointers read off the address list
    ([loc_at]) and the cursors coupled to model indices by the run prefix
    sum:
    - [conflict_l] (Go [conflict]) sits at the cursor RUN [cur], whose run
      starts at model index [leftIdx+offset] (the coupling [Hcur]);
    - [left_l] (Go [left]) is the anchor: the run just left of the insert
      boundary [curD], whose model boundary is [destIdx] ([HcurD]), so
      [item] is spliced after run [curD - 1];
    - [right_l] (Go [right]) is loop-constant at RUN [curR] (the right
      origin / [Last]), whose model boundary is [rightIdx] (a spec premise);
      the [conflict == right] break compares addresses, i.e. [cur = curR],
      which the prefix-sum injectivity turns into [leftIdx+offset = rightIdx];
    - [Hloop]: from the current accumulators, the remaining
      [Z.to_nat (rightIdx - leftIdx) - offset] steps of
      [set_find_integration_loop] still compute [loopResult]. With [Hbound] /
      [Hdest] this makes the Go [for conflict ≠ nil] test (with the
      [== right] break) consume exactly the loop's fuel.
    [own_fresh_item_raw] and the [parent.len] field are loop-constant, framed
    outside. *)
Definition integrate_loop_inv
    (parent : loc) (dq : dfrac) (ls : list loc) (runs : list ItemRun) (arr : list (YjsItem A))
    (leftIdx rightIdx : Z) (curR : nat)
    (originLeftId originRightId : option YjsId) (newItemId : YjsId)
    (loopResult : option Z)
    (conflict_l left_l right_l idsBeforeOrigin_l conflictIds_l : loc)
    (offset cur curD : nat) (idsBeforeOrigin conflictIds : gset YjsId) (destIdx : Z) : iProp Σ :=
  "Htext" ∷ own_ytype parent dq ls (MkTypeModel runs) ∗
  "Hconflict" ∷ conflict_l ↦ loc_at ls (Z.of_nat cur) ∗
  "Hleft" ∷ left_l ↦ loc_at ls (Z.of_nat curD - 1) ∗
  "Hright" ∷ right_l ↦ loc_at ls (Z.of_nat curR) ∗
  "Hids_before" ∷ (∃ s : slice.t, "Hids_before_ref" ∷ idsBeforeOrigin_l ↦ s ∗
                     "Hids_before_set" ∷ own_id_set s (DfracOwn 1) idsBeforeOrigin) ∗
  "Hconflict_ids" ∷ (∃ s : slice.t, "Hconflict_ids_ref" ∷ conflictIds_l ↦ s ∗
                     "Hconflict_ids_set" ∷ own_id_set s (DfracOwn 1) conflictIds) ∗
  "%Hoff" ∷ ⌜(1 <= offset)%nat⌝ ∗
  "%Hcur" ∷ ⌜(Z.of_nat (length (runs_flatten (take cur runs))) = leftIdx + Z.of_nat offset)%Z⌝ ∗
  "%Hcurb" ∷ ⌜(cur <= length runs)%nat⌝ ∗
  "%HcurD" ∷ ⌜(Z.of_nat (length (runs_flatten (take curD runs))) = destIdx)%Z⌝ ∗
  "%HcurDb" ∷ ⌜(curD <= length runs)%nat⌝ ∗
  "%Hdest" ∷ ⌜(leftIdx + 1 <= destIdx <= leftIdx + Z.of_nat offset)%Z⌝ ∗
  "%Hbound" ∷ ⌜(leftIdx + Z.of_nat offset <= rightIdx)%Z⌝ ∗
  "%Hloop" ∷ ⌜set_find_integration_loop (Z.to_nat (rightIdx - leftIdx) - offset) offset leftIdx rightIdx
                 originLeftId originRightId newItemId arr idsBeforeOrigin conflictIds destIdx
               = loopResult⌝.

(* ----- the fresh / linked item predicates [Store.Integrate] is stated over --- *)

(** [own_fresh_item_raw item_l input itemVal oleft oright]: [item_l] is a heap [Item] whose
    id / content and origin-id cells carry the integration [input]. Its abstract
    model item is [newItem = toItem input arr] — that link is a side condition of
    the spec (a fresh item's resolved origins depend on the current document
    [arr]), so it is *not* restated here. The [left']/[right'] fields are *not*
    constrained: the scan / entry-guard never read them, and [Store.Integrate]
    has already repaired (set) them by the time it calls the scan. *)
Definition own_fresh_item_raw (item_l : loc) (input : IntegrateInput (A := A))
    (itemVal : yjs.item.t) (oleft oright : option yjs.id.t) : iProp Σ :=
  "Hitem" ∷ item_l ↦ itemVal ∗
  "Holeft" ∷ is_origin_id itemVal.(yjs.item.originLeftId') oleft ∗
  "Horight" ∷ is_origin_id itemVal.(yjs.item.originRightId') oright ∗
  "%Hin_l" ∷ ⌜(toYjsId <$> oleft) = in_originId input⌝ ∗   (* heap ids = input ids *)
  "%Hin_r" ∷ ⌜(toYjsId <$> oright) = in_rightOriginId input⌝ ∗
  "%Hid" ∷ ⌜toYjsId itemVal.(yjs.item.id') = in_id input⌝ ∗
  "%Hcontent" ∷ ⌜toContent itemVal.(yjs.item.content') = in_content input⌝.

(** [own_linked_item item_l input parent leftNode rightNode]: the not-yet-integrated heap
    [Item] that [Store.Integrate] is about to splice in; everything about the
    caller's item is encapsulated here (its struct value and origin pointers
    are existentially hidden). On top of [own_fresh_item_raw] it records that
    the item is already linked to its resolved origin neighbours ([left'] =
    [leftNode], [right'] = [rightNode], set by [store.repair] on the update path or by
    the local-edit creator, issue #49), carries its parent, and is a countable
    insert of a nonempty run ([flags'] = ItemCountable; an [n]-char wire item
    denotes [n] chained per-char model ops, issue #28 U7). This is the
    item-side half of the Integrate spec. *)
Definition own_linked_item (item_l : loc) (input : IntegrateInput (A := A))
    (parent leftNode rightNode : loc) : iProp Σ :=
  ∃ (itemVal : yjs.item.t) (oleft oright : option yjs.id.t),
    own_fresh_item_raw item_l input itemVal oleft oright ∗
    ⌜itemVal.(yjs.item.left') = leftNode⌝ ∗
    ⌜itemVal.(yjs.item.right') = rightNode⌝ ∗
    ⌜itemVal.(yjs.item.parent') = parent⌝ ∗
    ⌜itemVal.(yjs.item.flags') = W8 2⌝ ∗
    ⌜(1 <= length (itemVal.(yjs.item.content').(yjs.content.content')))%nat⌝.

(** [own_linked_item] IS [own_item_node] at [DfracOwn 1], live, with a
    nonempty content: the fold/unfold between the two. *)
Lemma own_linked_item_as_node (item_l : loc) (input : IntegrateInput (A := A))
    (parent leftNode rightNode : loc) :
  own_linked_item item_l input parent leftNode rightNode ⊣⊢
  own_item_node item_l (DfracOwn 1) input false parent leftNode rightNode ∗
  ⌜(1 <= length (in_content input))%nat⌝.
Proof.
  rewrite /own_linked_item /own_fresh_item_raw /own_item_node.
  iSplit.
  - iIntros "H".
    iDestruct "H" as (v olid orid) "(H & %Hfl & %Hfr & %Hfpar & %Hflags & %Hlen)".
    iNamed "H".
    have Hc' : v.(yjs.item.content').(yjs.content.content') = in_content input
      := Hcontent.
    iSplitL; last first.
    { iPureIntro. rewrite -Hc'. exact Hlen. }
    iExists v, olid, orid.
    iFrame "Hitem Holeft Horight".
    iPureIntro.
    split_and!; [exact Hin_l | exact Hin_r | exact Hid | exact Hcontent
                | exact Hfpar | exact Hfl | exact Hfr | exact Hflags].
  - iIntros "[H %Hlen]". iDestruct "H" as (v olid orid) "H". iNamed "H".
    have Hc' : v.(yjs.item.content').(yjs.content.content') = in_content input
      := Hcontent.
    iExists v, olid, orid.
    iFrame "Hval Holeft Horight".
    iPureIntro.
    split_and!; [exact Hin_l | exact Hin_r | exact Hid | exact Hcontent
                | exact Hprev | exact Hnext | exact Hpar | exact Hflags
                | rewrite Hc' //].
Qed.

(** A linked item's address is new to the whole address map of the pool
    (the item is owned separately). *)
Lemma own_linked_item_fresh (item_l parent leftNode rightNode : loc)
    (input : IntegrateInput (A := A)) (dq : dfrac)
    (locs : gmap loc (list loc)) (p : pool) :
  own_linked_item item_l input parent leftNode rightNode -∗
  own_type_pool dq locs p -∗
  ⌜item_l ∉ concat ((map_to_list locs).*2)⌝.
Proof.
  iIntros "Hlinked Htypes".
  iDestruct "Hlinked" as (itemVal oleft oright) "(Hraw & _)".
  iDestruct "Hraw" as "(Hitem & _)".
  iApply (own_type_pool_fresh_concat with "Hitem Htypes").
Qed.

Lemma is_type_binding_agree (γ : gname) (name : P) (p q : loc) :
  is_type_binding γ name p -∗ is_type_binding γ name q -∗ ⌜p = q⌝.
Proof.
  iIntros "H1 H2". iDestruct (ghost_map_elem_agree with "H1 H2") as %Heq.
  iPureIntro. exact Heq.
Qed.

(** [store_inv] partitions into its exclusive part and the read-shareable part
    at full fraction; since the body IS that split, the bridge is definitional
    (kept as a lemma for the lock-layer proofs that rewrite with it). *)
Lemma store_inv_bridge (s_loc : loc) (γs : store_names) (γh : history_names) :
  store_inv s_loc γs γh ⊣⊢
  ∃ client k items_mref types_mref deletedSetVal pend_sl pdel_sl locs p bind h m pend pdel,
    store_inv_excl s_loc γs γh client k items_mref types_mref deletedSetVal pend_sl pdel_sl locs p bind h m pend pdel ∗
    store_inv_ro γs locs p 1.
Proof. rewrite /store_inv /named //. Qed.

(** What a reader's certificates read back out of the exclusive slice at a
    lock transition (issue #125): the client pin identifies the caller's
    history certificate with THIS replica's history, the registry binding
    routes a root name to its type slot, and [history_state_coh] turns every
    delivered insert of the certified prefix into an item of that type's
    CURRENT list ([delivered_ops_prefix] + [delivered_docm_mem]). The slice
    comes back untouched; [wp_Store__rlock] applies this at the read
    lock's linearization point, which is the only moment a reader sees the
    exclusive slice. *)
Lemma store_inv_excl_hist_root (s_loc : loc) (γs : store_names) (γh : history_names)
    (client k : w64) (items_mref types_mref : loc) (deletedSetVal : yjs.deletedSet.t)
    (pend_sl pdel_sl : slice.t) (locs : gmap loc (list loc)) (p : pool) (bind : gmap P loc)
    (h : list Ev) (m : DocModel) (pend : list (TId * IntegrateInput (A := A)))
    (pdel : list delete_span)
    (c : ClientId) (h0 : list Ev) (name : P) (parent : loc) :
  store_inv_excl s_loc γs γh client k items_mref types_mref deletedSetVal pend_sl pdel_sl locs p bind h m pend pdel -∗
  is_store_client γs c -∗
  is_history_lb γh c h0 -∗
  is_type_binding γs.(sn_types) name parent -∗
  store_inv_excl s_loc γs γh client k items_mref types_mref deletedSetVal pend_sl pdel_sl locs p bind h m pend pdel ∗
  ⌜∀ input : IntegrateInput (A := A),
     (RootId name, OpInsert input) ∈ delivered_ops h0 ->
     ∃ tm it, p !! parent = Some tm ∧ item_id it = in_id input ∧ it ∈ tm_arr tm⌝.
Proof.
  iIntros "Hexcl #Hpin #Hlb #Hbind". iNamed "Hexcl".
  iDestruct (is_store_client_agree with "Hclientpin Hpin") as %Heqc. subst c.
  iDestruct (is_history_lb_prefix with "Hhist Hlb") as %Hpref.
  iDestruct (ghost_map_lookup with "HtypesAuth Hbind") as %Hbindlk.
  have Hfact : ∀ input : IntegrateInput (A := A),
      (RootId name, OpInsert input) ∈ delivered_ops h0 ->
      ∃ tm it, p !! parent = Some tm ∧ item_id it = in_id input ∧ it ∈ tm_arr tm.
  { move=> input Hin.
    destruct Hregcoh as ((Hbindtypes & _ & _) & Hmtypes & _).
    destruct (Hbindtypes name parent Hbindlk) as [tm Htm].
    have Hdg : doc_model_get m (RootId name) = tm_arr tm := Hmtypes name parent tm Hbindlk Htm.
    have Hin' : (RootId name, OpInsert input) ∈ delivered_ops h.
    { destruct (delivered_ops_prefix h0 h Hpref) as [rest ->].
      rewrite elem_of_app. by left. }
    destruct (delivered_docm_mem h m (RootId name) input Hhcoh Hin') as (it & Hitid & Hitmem).
    exists tm, it. rewrite Hdg in Hitmem.
    split_and!; [exact Htm | exact Hitid | exact Hitmem]. }
  iSplitR ""; last (iPureIntro; exact Hfact).
  iExists acc.
  iFrame "∗#". iPureIntro. split_and!;
    [exact Hpendroot | exact Hpendbnd | exact Hctr | exact Hpool
    | exact Hhcoh | exact Hregcoh | exact Hacccoh].
Qed.

Lemma pool_frag_split γs q1 q2 locs p :
  pool_frag γs (q1 + q2) locs p ⊣⊢ pool_frag γs q1 locs p ∗ pool_frag γs q2 locs p.
Proof. rewrite /pool_frag -own_op -frac_agree_op //. Qed.

Lemma pool_frag_agree γs q1 q2 locs1 p1 locs2 p2 :
  pool_frag γs q1 locs1 p1 -∗ pool_frag γs q2 locs2 p2 -∗ ⌜locs1 = locs2 ∧ p1 = p2⌝.
Proof.
  iIntros "H1 H2". iCombine "H1 H2" gives %Hv.
  iPureIntro. apply frac_agree_op_valid_L in Hv as [_ Heq]. by injection Heq.
Qed.

(** No-loss SOUNDNESS: a receipt [is_accepted γs i] held together with the
    store proves [i] is delivered-or-buffered right now. A client re-acquires
    the lock and applies this: the accepted id it was handed cannot have been
    silently dropped. *)
Lemma own_store_accepted_sound (s_loc : loc) (γs : store_names) (γh : history_names)
    (c : ClientId) (h : list Ev) (m : DocModel)
    (pend : list (TId * IntegrateInput (A := A))) (i : YjsId) :
  own_store s_loc γs γh c h m pend -∗ is_accepted γs i -∗
  own_store s_loc γs γh c h m pend ∗ ⌜i ∈ delivered_ids h ∪ pending_id_set pend⌝.
Proof.
  iIntros "H #Hi". iNamed "H".
  iDestruct (auth_gset_frag_sub with "Hacc Hi") as %Hsub.
  have Hin : i ∈ acc.
  { apply Hsub. by apply elem_of_singleton. }
  iSplitR ""; last (iPureIntro; exact (elem_of_weaken _ _ _ Hin Hacccoh)).
  iExists client, k, pdel, locs, p, bind, acc.
  iFrame "∗#". iPureIntro. split_and!;
    [exact Hclientc | exact Hpendroot | exact Hpendbnd | exact Hregmodel | exact Hhcoh | exact Hctr
    | exact Hacccoh].
Qed.

(** The client pin comes out of the store without consuming it (the clause is
    persistent): how a caller that reveals a store state learns the client it
    already holds a pin for is THIS store's. *)
Lemma own_store_client_pin (s_loc : loc) (γs : store_names) (γh : history_names)
    (c : ClientId) (h : list Ev) (m : DocModel)
    (pend : list (TId * IntegrateInput (A := A))) :
  own_store s_loc γs γh c h m pend -∗
  own_store s_loc γs γh c h m pend ∗ is_store_client γs c.
Proof.
  iIntros "H". iNamed "H".
  iSplitR ""; last by iFrame "Hclientpin".
  iExists client, k, pdel, locs, p, bind, acc.
  iFrame "∗#". iPureIntro. split_and!;
    [exact Hclientc | exact Hpendroot | exact Hpendbnd | exact Hregmodel | exact Hhcoh | exact Hctr
    | exact Hacccoh].
Qed.

(** No-loss MINT: given the store and a proof that each id in [L] is already
    delivered-or-buffered, grow the accepted set and hand back a receipt per
    element. This is what [applyUpdate] calls (with [L = inputs]) so a
    discarding implementation, which delivers/buffers nothing, could not
    produce the receipts its postcondition promises. *)
Lemma own_store_accept_batch (s_loc : loc) (γs : store_names) (γh : history_names)
    (c : ClientId) (h : list Ev) (m : DocModel)
    (pend : list (TId * IntegrateInput (A := A)))
    (L : list (TId * IntegrateInput (A := A))) :
  (∀ x, x ∈ L -> in_id x.2 ∈ delivered_ids h ∪ pending_id_set pend) ->
  own_store s_loc γs γh c h m pend ==∗
  own_store s_loc γs γh c h m pend ∗ [∗ list] x ∈ L, is_accepted γs (in_id x.2).
Proof.
  iIntros (HL) "H". iNamed "H".
  set (T := list_to_set ((λ x, in_id x.2) <$> L) : gset YjsId).
  have HTsub : T ⊆ delivered_ids h ∪ pending_id_set pend.
  { subst T. move=> i. rewrite elem_of_list_to_set list_elem_of_fmap.
    move=> [x [-> Hx]]. exact (HL x Hx). }
  iMod (auth_gset_grow γs.(sn_accepted) acc T with "Hacc") as "[Hacc Hfrag]".
  iDestruct "Hfrag" as "#Hfrag".
  iAssert ([∗ list] x ∈ L, is_accepted γs (in_id x.2))%I as "#Haccepts".
  { iApply big_sepL_intro. iIntros "!#" (idx x Hx). rewrite /is_accepted.
    iApply (auth_gset_frag_mono γs.(sn_accepted) (acc ∪ T) {[in_id x.2]}); [| iApply "Hfrag"].
    apply singleton_subseteq_l, elem_of_union_r. subst T.
    rewrite elem_of_list_to_set list_elem_of_fmap.
    exists x. split; [done | exact (list_elem_of_lookup_2 _ _ _ Hx)]. }
  iModIntro. iFrame "Haccepts".
  iExists client, k, pdel, locs, p, bind, (acc ∪ T).
  iFrame "∗#". iPureIntro. split_and!;
    [exact Hclientc | exact Hpendroot | exact Hpendbnd | exact Hregmodel | exact Hhcoh | exact Hctr |].
  rewrite /accepted_coh. apply union_least; [exact Hacccoh | exact HTsub].
Qed.

(** The [wp_NewDoc] seam: a fresh store's heap fields and this client's
    (empty) history element assemble into the lock layer's tie payload at
    [RLocked 0], over caller-provided RWMutex names (the physical lock is set
    up by [init_RWMutex] at the call site), allocating the store's ghost
    names for real: the write-lock witness, the reader count at zero, the
    DISCARDED reader-bound authority ([is_Store]'s [Hmax]) and the types
    agreement all go into the payload rather than being dropped. The caller
    wraps the result in the tie invariant next to [own_RWMutex (RLocked 0)]
    and has [is_Store]. The reader-bound TOKENS come back too (issue #125):
    zipped with [init_RWMutex]'s RLock tokens they are the document's
    [own_read_cap] read capabilities, one per reader slot. *)
Lemma store_tie_init (s_loc : loc) (γh : history_names) (client k : w64)
    (items_mref types_mref : loc) (deletedSetVal : yjs.deletedSet.t)
    (γrw : RWMutex_names) :
  "Hclient" ∷ (s_loc .[(yjs.store.t), "client"]) ↦ client -∗
  "Hclock"  ∷ (s_loc .[(yjs.store.t), "clock"]) ↦ k -∗
  "Hitemsf" ∷ (s_loc .[(yjs.store.t), "items"]) ↦ items_mref -∗
  "Hmap"    ∷ own_map items_mref (DfracOwn 1) (∅ : gmap w64 slice.t) -∗
  "Htypesf" ∷ (s_loc .[(yjs.store.t), "types"]) ↦ types_mref -∗
  "Htypesmap" ∷ own_map types_mref (DfracOwn 1) (∅ : gmap P loc) -∗
  "HdeletedSet"   ∷ (s_loc .[(yjs.store.t), "deletedSet"]) ↦ deletedSetVal -∗
  "Hpendf"  ∷ (s_loc .[(yjs.store.t), "pending"]) ↦ slice.nil -∗
  "Hpddelf" ∷ (s_loc .[(yjs.store.t), "pendingDeletes"]) ↦ slice.nil -∗
  "Hhist"   ∷ own_client_history γh (uint.nat client) ([] : list Ev) ==∗
  ∃ γs : store_names,
    "%Hrw"        ∷ ⌜γs.(sn_rw) = γrw⌝ ∗
    "#Hmax"       ∷ own_tok_auth_dfrac γs.(sn_rmax) DfracDiscarded
                      (Z.to_nat rwmutex.actualMaxReaders) ∗
    "Hrtoks"      ∷ own_toks γs.(sn_rmax) (Z.to_nat rwmutex.actualMaxReaders) ∗
    "Htie"        ∷ tie_body s_loc γs γh (RLocked 0) ∗
    "#Hclientpin" ∷ is_store_client γs (uint.nat client).
Proof.
  iIntros "Hclient Hclock Hitemsf Hmap Htypesf Htypesmap HdeletedSet Hpendf Hpddelf Hhist".
  set (p := ∅ : pool). set (locs := ∅ : gmap loc (list loc)).
  iMod (own_alloc (● ((λ tm, (list_to_set (tm_arr tm) : gset (YjsItem A))) <$> p) : seqUR))
    as (γseq) "Hseq".
  { apply auth_auth_valid. rewrite /p fmap_empty //. }
  iMod (ghost_map_alloc_empty (K := P) (V := loc)) as (γtypes) "HtypesAuth".
  (* the lock-layer ghosts, for real: the write-lock witness, the reader
     count at zero, the reader bound (discarded, so it can sit in [is_Store]
     persistently; its tokens are the read capabilities, handed back to the
     caller) and the pool agreement at the empty store *)
  iMod (ghost_var_alloc ()) as (γwl) "Hwl".
  iMod (own_tok_auth_alloc) as (γrrlocked) "Hrrlocked".
  iMod (own_tok_auth_alloc) as (γrmax) "Hrmax".
  iMod (own_tok_auth_add (Z.to_nat rwmutex.actualMaxReaders) with "Hrmax")
    as "[Hrmax Hrtoks]".
  iPersist "Hrmax".
  iMod (own_toks_0 γrmax) as "Hrtoks0".
  iMod (own_alloc (to_frac_agree 1 ((locs, p) : leibnizO addressed_pool))) as (γta) "Hta".
  { done. }
  (* the grow-only accepted-id set starts empty *)
  iMod (own_alloc (● (∅ : gset YjsId) : accUR)) as (γacc) "Hacc0".
  { apply auth_auth_valid. done. }
  (* the monotone delete set starts empty (plan-delete-set D1) *)
  iMod (own_alloc (● (∅ : gset YjsId) : accUR)) as (γds) "Hdelete_set0".
  { apply auth_auth_valid. done. }
  (* the client pin (issue #107): one agree, fixed at birth *)
  iMod (own_alloc (to_agree ((uint.nat client) : leibnizO ClientId))) as (γcl) "#Hclpin".
  { done. }
  set (γs := {| sn_seq := γseq; sn_types := γtypes; sn_wl := γwl;
                sn_rw := γrw; sn_rmax := γrmax; sn_rrlocked := γrrlocked;
                sn_types_agree := γta; sn_accepted := γacc; sn_client := γcl;
                sn_delete_set := γds |}).
  iModIntro. iExists γs.
  iSplitR; first done.
  iFrame "Hrmax". iFrame "Hrtoks".
  iSplitL; last by iFrame "Hclpin".
  rewrite /tie_body.
  iFrame "Hrrlocked Hrtoks0 Hwl".
  iExists client, k, items_mref, types_mref, deletedSetVal, slice.nil, slice.nil, locs, p,
    (∅ : gmap P loc), ([] : list Ev), (∅ : DocModel),
    ([] : list (TId * IntegrateInput (A := A))), ([] : list delete_span).
  rewrite frac_of_0.
  iSplitL "Hta"; first by iFrame "Hta".
  iSplitR "Hseq"; last first.
  { (* store_inv_ro over the empty pool *)
    iFrame "Hseq". rewrite /own_type_pool /p big_sepM_empty.
    iSplit; last done. iPureIntro. rewrite /locs_wf /locs /p. split_and!.
    - rewrite !dom_empty_L //.
    - rewrite map_to_list_empty /=. constructor.
    - move=> parent ls tm Hls. rewrite lookup_empty // in Hls. }
  (* store_inv_excl *)
  iAssert (own_delete_set γs (∅ : DocModel) (all_runs p))
    with "[Hdelete_set0]" as "Hdelete_set".
  { iExists (∅ : gset YjsId). iFrame "Hdelete_set0". iPureIntro. split.
    - move=> i Hi. exfalso. set_solver.
    - move=> r Hr y _ Hin. exfalso. set_solver. }
  iExists (∅ : gset YjsId).
  iFrame "Hclient Hclock Hitemsf Htypesf Htypesmap HdeletedSet Hpendf Hpddelf Hhist HtypesAuth Hacc0 Hdelete_set".
  iSplitR; first by iFrame "Hclpin".
  iSplitL "Hmap".
  { (* the item index over the empty pool *)
    iExists (∅ : gmap w64 slice.t). iFrame "Hmap".
    rewrite big_sepM_empty. iSplit; [done |].
    iPureIntro. rewrite /pool_entries /p map_to_list_empty /=. split.
    - move=> c Hc. exfalso. move: Hc. rewrite elem_of_nil //.
    - move=> a b Ha. exfalso. move: Ha. rewrite elem_of_nil //. }
  iSplitR.
  { (* the empty pending buffer over the nil slice *)
    iExists []. iSplitR; [iApply own_slice_nil |].
    iSplitR; [iApply own_slice_cap_nil |]. rewrite big_sepL2_nil //. }
  iSplitR.
  { (* the empty delete-span buffer over the nil slice *)
    iExists []. iSplitR; [iApply own_slice_nil |].
    iSplitR; [iApply own_slice_cap_nil | done]. }
  iSplitR.
  { have He : expand_inputs [] = [] by done.
    rewrite /is_pending_certified He big_sepL_nil //. }
  iSplitR.
  { iPureIntro. move=> typedInput Hin. by apply elem_of_nil in Hin. }
  iSplitR.
  { iPureIntro. move=> typedInput Hin. by apply elem_of_nil in Hin. }
  iSplitR. { iPureIntro. move=> parent' tm' x Hlk. rewrite /p lookup_empty // in Hlk. }
  iSplitR.
  { iPureIntro. rewrite /pool_invs /all_runs /p map_to_list_empty /=.
    split; first by move=> r /elem_of_nil.
    move=> i j r1 r2 Hi. rewrite lookup_nil // in Hi. }
  iSplitR. { rewrite big_sepM_empty //. }
  iPureIntro. split_and!.
  - exact history_state_coh_nil.
  - rewrite /pool_doc_registry_coh /pool_registry_coh /pool_registry_models. split_and!.
    + move=> name q Hlk. rewrite lookup_empty // in Hlk.
    + move=> n1 n2 q Hlk. rewrite lookup_empty // in Hlk.
    + move=> q [tm Hlk]. rewrite /p lookup_empty // in Hlk.
    + move=> name q tm Hlk. rewrite lookup_empty // in Hlk.
    + move=> t Hne. exfalso. apply Hne. rewrite /doc_model_get lookup_empty //.
  - rewrite /accepted_coh. apply empty_subseteq.
Qed.

(** Peek [own_store]'s coherence fact while keeping the resource: the replayed
    doc model [m] is coherent with the store's current history [h]. Used to
    instantiate the receiver-side obligation of [wp_Doc__ApplySyncUpdate] at
    the history the lock reveals. *)
Lemma own_store_hist_coh (s_loc : loc) (γs : store_names) (γh : history_names)
    (c : ClientId) (h : list Ev) (m : DocModel)
    (pend : list (TId * IntegrateInput (A := A))) :
  own_store s_loc γs γh c h m pend -∗
  own_store s_loc γs γh c h m pend ∗ ⌜history_state_coh h m⌝.
Proof.
  iIntros "H". iNamed "H".
  iSplitL "Hstate Hseq HtypesAuth Hhist Hacc Hdelete_set".
  - iExists client, k, pdel, locs, p, bind, acc.
    iFrame "∗#".
    iPureIntro. split_and!;
      [exact Hclientc | exact Hpendroot | exact Hpendbnd | exact Hregmodel | exact Hhcoh | exact Hctr
      | exact Hacccoh].
  - iPureIntro. exact Hhcoh.
Qed.

(** [store_inv] is exactly [own_store] with the model existentially closed.
    The forward direction assembles [own_store_state] from the exclusive
    slice's fields and the read-shareable pool. The write lock uses this to
    hand out [own_store] ([wp_Store__wlock]) and to take it back. *)
Lemma store_inv_own_store (s_loc : loc) (γs : store_names) (γh : history_names) :
  store_inv s_loc γs γh ⊣⊢
  ∃ (c : ClientId) (h : list Ev) (m : DocModel)
    (pend : list (TId * IntegrateInput (A := A))),
    own_store s_loc γs γh c h m pend.
Proof.
  iSplit.
  - iIntros "H". iNamed "H". iNamed "Hexcl". iNamed "Hro".
    have [Hreg Hregmodel] := Hregcoh.
    iAssert (own_store_state s_loc (MkStoreState client k locs p bind pend pdel))
      with "[Hclient Hclock HdeletedSet Hitemsf Hitemmap Htypesf Htypesmap Hpendf Hpend Hpddelf Hpddel Htypes]"
      as "Hstate".
    { iSplitL; last by (iPureIntro; split; [exact Hpool | exact Hreg]).
      rewrite /own_store_fields /=.
      iFrame "Hclient Hclock Htypes".
      iSplitL "HdeletedSet"; first (iExists deletedSetVal; iFrame "HdeletedSet").
      iSplitL "Hitemsf Hitemmap"; first (iExists items_mref; iFrame).
      iSplitL "Htypesf Htypesmap"; first (iExists types_mref; iFrame).
      iSplitL "Hpendf Hpend"; first (iExists pend_sl; iFrame).
      iExists pdel_sl. iFrame. }
    iExists (uint.nat client), h, m, pend.
    iExists client, k, pdel, locs, p, bind, acc.
    iFrame "∗#".
    iPureIntro. split_and!;
      [reflexivity | exact Hpendroot | exact Hpendbnd | exact Hregmodel | exact Hhcoh
      | exact Hctr | exact Hacccoh].
  - iIntros "H". iDestruct "H" as (c h m pend) "H". iNamed "H". subst c. iNamed "Hstate".
    have [Hpool Hreg] := Hinvs.
    iNamed "Hfields". simpl in *.
    iDestruct "HdeletedSet" as (deletedSetVal) "HdeletedSet".
    iNamed "Hitems". iNamed "Hregistry". iNamed "Hpending". iNamed "Hpdeletes".
    iExists client, k, items_mref, types_mref, deletedSetVal, pend_sl, pdel_sl, locs, p, bind, h, m, pend, pdel.
    iSplitR "Hseq Htypes"; last by iFrame "Hseq Htypes".
    iExists acc.
    iFrame "Hclient Hclientpin Hclock Hitemsf Hitemmap Htypesf Htypesmap HdeletedSet Hpendf Hpend Hpddelf Hpddel Hpendcert HtypesAuth Hbinds Hhist Hacc Hdelete_set".
    iPureIntro. split_and!;
      [exact Hpendroot | exact Hpendbnd | exact Hctr | exact Hpool
      | exact Hhcoh | (split; [exact Hreg | exact Hregmodel]) | exact Hacccoh].
Qed.

End store_heap.
