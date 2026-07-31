(** The [store], Iris layer: ghost state, the lock body, and the public store
    predicate.

    Definitions
    - [store_names]: the per-store ghost names (item-set authority, root-type
      registry, write-lock witness, the RWMutex reader accounting, the accepted
      set).
    - [own_item_map]: the heap [map[Client][]*item] at the cell level.
    - the lock body: [store_inv_ro] (the fractional, reader-visible part),
      [store_inv_excl] (the exclusive part) and [store_inv], carrying the
      client's ghost history; [tie_body] and [types_frag] / [frac_of] are the
      RWMutex reader-count accounting (issue #22).
    - the public state predicate [own_store s c h m pend]: the WHOLE
      lock-protected state as one exclusive predicate over its model.
    - the persistent witnesses [is_Store], [is_type_binding], [is_root],
      [is_type_lb], [is_root_lb], [is_applied_root_lb], [is_accepted],
      [is_update_item], and the read capability [own_read_cap].
    - the Integrate-side predicates [own_fresh_item_raw], [own_linked_item(_run)]
      and the loop invariant [integrate_loop_inv].

    Laws
    - [store_inv_init]: how to build the invariant from the raw points-tos, and
      [store_inv_bridge] / [own_store_hist_coh] / [own_store_accepted_sound]:
      what you may read back out of it.
    - [own_store_accept_batch]: the state-transition law for accepting a
      delivered batch.
    - the reader fractions form a chain: [frac_of_0] and [frac_of_split].
    - [types_frag] splits and agrees ([tf_split], [tf_agree]);
      [is_type_binding] is functional ([is_type_binding_agree]).
    - [own_item_map] only sees cells up to [cell_kp] permutation
      ([own_item_map_kp_perm]), and a fresh node is fresh for the whole
      registry ([all_cells_fresh]).

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

    We track full ITEMS, not just ids: a membership bound [x ∈ S ⊆ ty_arr ts]
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

Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO (gmap loc type_state)))}.

(* The [∷] (named) wrapper blocks [Timeless] TC resolution; unfold it (as
   [New.proof.sync_proof.rwmutex] does) so the [Timeless] instances below go
   through the named conjuncts of [own_item_map] / [store_inv]. *)

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
      item-set auth alone does not determine the [type_state] map);
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
#[global] Instance is_origin_id_timeless p originId : Timeless (is_origin_id p originId).
Proof. rewrite /is_origin_id. by destruct originId; apply _. Qed.

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
   [⊣⊢]-backward direction needs the existential heap struct ([itemVal] / [yt]) and
   the DLL tail loc ([tl]) to AGREE across the two shares; [own_dll_last_agree]
   supplies the [tl] agreement (both DLLs over the same cells end at the same
   node); [itemVal]/[yt] agree by [pointsto] agreement. *)
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
      * iExists itemVal, olid, orid. iFrame "Hv1 Holeft Horight Hr1". done.
      * iExists itemVal, olid, orid. iFrame "Hv2 Holeft Horight Hr2". done.
    + iIntros "[H1 H2]".
      iDestruct "H1" as (iv1 olid1 orid1) "H1". iNamedSuffix "H1" "1".
      iDestruct "H2" as (iv2 olid2 orid2) "H2". iNamedSuffix "H2" "2".
      iCombine "Hval1 Hval2" gives %Hiv. subst iv2.
      iCombine "Hval1 Hval2" as "Hval".
      iDestruct (IH with "[$Hrest1 $Hrest2]") as "Hrest".
      iExists iv1, olid1, orid1. iFrame "Hval Hrest Holeft1 Horight1". done.
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
    struct fields, [own_item_map], the registry [ghost_map_auth], the ghost
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

(** [is_root γs name]: persistent witness that the root type [name] is
    registered in the store (bound in the registry to SOME type loc, which
    stays hidden). This is what the [applyUpdate] certificate spec asks for
    per target root, in place of a raw registry lookup; any holder of the
    binding (a [Text] handle, [getOrCreateYType]'s hit path) can mint it. *)
Definition is_root (γs : store_names) (name : P) : iProp Σ :=
  ∃ p : loc, is_type_binding γs.(sn_types) name p.

#[global] Instance is_root_persistent γs name : Persistent (is_root γs name).
Proof. apply _. Qed.

(** [pending_item_rooted]/[is_pending_rooted] (issue #40, weakened in #54):
    every HEAD struct of a decoded buffer (both origins absent, so it carries
    its root's name on the wire) targets a named root [RootId nm]. Issue #49
    additionally required that root to be ALREADY REGISTERED ([is_root γs nm]);
    issue #54 LIFTS that pre-bound-roots restriction now that
    [getOrCreateYType]'s miss branch is verified -- a head struct may target a
    not-yet-created root, which [applyUpdate]'s drain registers on first use.
    All that remains is that the target is a root and not an [AnchorId]
    (Parent::Id / type-as-item is out of the verified subset, #43). With the
    registration ([is_root], the only resource-bearing conjunct) gone, this is
    now a pure syntactic fact about the batch, so it is a [Prop] (carried as
    [⌜..⌝] where an [iProp] is expected); the [γs] argument is retained only for
    signature stability. Structs WITH an origin derive their binding from the
    origin's arrival at integration time, so carry no obligation here. *)
Definition pending_item_rooted (γs : store_names)
    (typedInput : TId * IntegrateInput (A := A)) : Prop :=
  if decide (in_originId typedInput.2 = None ∧ in_rightOriginId typedInput.2 = None)
  then (∃ nm : P, typedInput.1 = RootId nm)
  else True.

Definition is_pending_rooted (γs : store_names)
    (pending : list (TId * IntegrateInput (A := A))) : Prop :=
  ∀ typedInput, typedInput ∈ pending -> pending_item_rooted γs typedInput.

(** [is_accepted γs i]: the persistent receipt that id [i] has been accepted by
    the store (a lower bound on the grow-only accepted set). Combined with the
    store invariant it proves [i] is forever delivered-or-buffered. *)
Definition is_accepted (γs : store_names) (i : YjsId) : iProp Σ :=
  own γs.(sn_accepted) (◯ ({[i]} : gset YjsId) : accUR).

#[global] Instance is_accepted_persistent γs i : Persistent (is_accepted γs i).
Proof. rewrite /is_accepted. apply _. Qed.

#[global] Instance is_accepted_timeless γs i : Timeless (is_accepted γs i).
Proof. rewrite /is_accepted. apply _. Qed.

Definition store_inv_ro (γs : store_names) (types : gmap loc type_state) (q : Qp) : iProp Σ :=
  "Hseq" ∷ own γs.(sn_seq) (●{DfracOwn q} ((λ ts, (list_to_set (ty_arr ts) : gset (YjsItem A))) <$> types) : seqUR) ∗
  "Htypes" ∷ ([∗ map] parent ↦ ts ∈ types,
                own_ytype_cells parent (DfracOwn q) (ty_cells ts) (ty_arr ts) ∗
                ⌜YjsArrInvariant (ty_arr ts)⌝).

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
    (types : gmap loc type_state) (bind : gmap P loc) (h : list Ev) (m : DocModel)
    (pend : list (TId * IntegrateInput (A := A))) : iProp Σ :=
    ∃ (acc : gset YjsId),
    "Hclient" ∷ (s_loc .[(yjs.store.t), "client"]) ↦ client ∗
    "Hclock"  ∷ (s_loc .[(yjs.store.t), "clock"]) ↦ k ∗
    "Hitemsf" ∷ (s_loc .[(yjs.store.t), "items"]) ↦ items_mref ∗
    "Hitemmap" ∷ own_item_map items_mref (DfracOwn 1) types ∗
    "Htypesf" ∷ (s_loc .[(yjs.store.t), "types"]) ↦ types_mref ∗
    "Htypesmap" ∷ own_map types_mref (DfracOwn 1) bind ∗
    "Hdset"   ∷ (s_loc .[(yjs.store.t), "deletedSet"]) ↦ dset ∗
    (* the pending buffer (issue #40): the buffered structs whose dependencies
       have not arrived, with their certificates (persistent), so the next
       applyUpdate can re-certify the whole drained buffer without the caller
       knowing what is buffered. *)
    "Hpendf"  ∷ (s_loc .[(yjs.store.t), "pending"]) ↦ pend_sl ∗
    "Hpend"   ∷ own_update_structs pend_sl (DfracOwn 1) pend ∗
    "#Hpendcert" ∷ is_pending_certified γh (expand_inputs pend) ∗
    "%Hpendroot" ∷ ⌜is_pending_rooted γs pend⌝ ∗
    "%Hpendbnd" ∷ ⌜∀ typedInput : TId * IntegrateInput (A := A), typedInput ∈ pend ->
                    (Z.of_nat (clock (in_id typedInput.2)) + Z.of_nat (length (in_content typedInput.2)) < 2^64)%Z⌝ ∗
    "%Hctr"   ∷ ⌜∀ parent ts x, types !! parent = Some ts → x ∈ ty_arr ts →
                   clientId (item_id x) = uint.nat client →
                   (clock (item_id x) < uint.nat k)%nat⌝ ∗
    "%Hcellctr" ∷ ⌜∀ c, c ∈ all_cells types → cell_client c = client →
                   (uint.Z (cell_clock c) + Z.of_nat (length (ic_run c)) <= uint.Z k)%Z⌝ ∗
    (* part-6 pool invariants (issue #28): the split branches' index pin *)
    "%Hlocdup" ∷ ⌜NoDup (ic_loc <$> all_cells types)⌝ ∗
    "%Hrangedisj" ∷ ⌜cells_range_disjoint (all_cells types)⌝ ∗
    "%Hrunfits" ∷ ⌜∀ c, c ∈ all_cells types → cell_fits c⌝ ∗
    "%Horiginclk" ∷ ⌜∀ c, c ∈ all_cells types → cell_origin_clk c⌝ ∗
    "HtypesAuth" ∷ ghost_map_auth γs.(sn_types) 1 bind ∗
    "#Hbinds" ∷ ([∗ map] name ↦ p ∈ bind, is_type_binding γs.(sn_types) name p) ∗
    "%Hbindtypes" ∷ ⌜∀ name p, bind !! name = Some p → is_Some (types !! p)⌝ ∗
    "%Hbindinj" ∷ ⌜∀ n1 n2 p, bind !! n1 = Some p → bind !! n2 = Some p → n1 = n2⌝ ∗
    "%Htypesbound" ∷ ⌜∀ p, is_Some (types !! p) → ∃ name, bind !! name = Some p⌝ ∗
    "Hhist"   ∷ own_client_history γh (uint.nat client) h ∗
    "%Hhcoh"  ∷ ⌜history_state_coh h m⌝ ∗
    "%Hmtypes" ∷ ⌜∀ name p ts, bind !! name = Some p → types !! p = Some ts →
                    doc_model_get m (RootId name) = ty_arr ts⌝ ∗
    "%Hmdom" ∷ ⌜∀ t, doc_model_get m t ≠ [] →
                  ∃ name p, t = RootId name ∧ bind !! name = Some p⌝ ∗
    (* no-loss accepted-id layer (this branch): the grow-only accepted set and
       its coherence [acc ⊆ delivered_ids h ∪ pending ids] *)
    "Hacc" ∷ own γs.(sn_accepted) (● acc : accUR) ∗
    "%Hacccoh" ∷ ⌜accepted_coh acc h pend⌝.

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
    [Hmtypes]: each registered type's [ty_arr] equals [doc_model_get m] at its
    bound name).

    The body is [store_inv_excl] (the mutable-exclusive clauses, documented
    there) next to [store_inv_ro] at full fraction: exactly the two halves
    the RWMutex tie invariant tracks separately while readers hold shares,
    so [store_inv_bridge] is definitional. *)
Definition store_inv (s_loc : loc) (γs : store_names) (γh : history_names) : iProp Σ :=
  ∃ (client k : w64) (items_mref types_mref : loc) (dset : yjs.deletedSet.t)
    (pend_sl : slice.t)
    (types : gmap loc type_state) (bind : gmap P loc) (h : list Ev) (m : DocModel)
    (pend : list (TId * IntegrateInput (A := A))),
    "Hexcl" ∷ store_inv_excl s_loc γs γh client k items_mref types_mref dset pend_sl types bind h m pend ∗
    "Hro"   ∷ store_inv_ro γs types 1.

(** [store_inv] is timeless (heap points-to + ghost state over discrete cameras +
    pure facts), so the write [Lock] wrapper hands it back WITHOUT a [▷] even
    though it is extracted from the tie invariant — the Insert/Delete proofs use
    it immediately (no intervening program step to strip a later). *)
#[global] Instance store_inv_timeless s_loc γs γh : Timeless (store_inv s_loc γs γh).
Proof. rewrite /store_inv. apply _. Qed.

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

(** Fractional agreement on the [types] map between a reader's share and the
    lock invariant. *)
Definition types_frag (γs : store_names) (q : Qp) (types : gmap loc type_state) : iProp Σ :=
  own γs.(sn_types_agree) (to_frac_agree q (types : leibnizO (gmap loc type_state))).

Definition storeN : namespace := nroot .@ "yjs_store".

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
    (c : ClientId) (h : list Ev) (m : DocModel)
    (pend : list (TId * IntegrateInput (A := A))) : iProp Σ :=
  ∃ (client k : w64) (items_mref types_mref : loc) (dset : yjs.deletedSet.t)
    (pend_sl : slice.t)
    (types : gmap loc type_state) (bind : gmap P loc) (acc : gset YjsId),
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
    "#Hpendcert" ∷ is_pending_certified γh (expand_inputs pend) ∗
    "%Hpendroot" ∷ ⌜is_pending_rooted γs pend⌝ ∗
    "%Hpendbnd" ∷ ⌜∀ typedInput : TId * IntegrateInput (A := A), typedInput ∈ pend ->
                    (Z.of_nat (clock (in_id typedInput.2)) + Z.of_nat (length (in_content typedInput.2)) < 2^64)%Z⌝ ∗
    "Hseq"    ∷ own γs.(sn_seq) (● ((λ ts, (list_to_set (ty_arr ts) : gset (YjsItem A))) <$> types) : seqUR) ∗
    "Htypes"  ∷ ([∗ map] parent ↦ ts ∈ types,
                  own_ytype_cells parent (DfracOwn 1) (ty_cells ts) (ty_arr ts) ∗
                  ⌜YjsArrInvariant (ty_arr ts)⌝) ∗
    "HtypesAuth" ∷ ghost_map_auth γs.(sn_types) 1 bind ∗
    "#Hbinds" ∷ ([∗ map] name ↦ p ∈ bind, is_type_binding γs.(sn_types) name p) ∗
    "Hhist"   ∷ own_client_history γh c h ∗
    "%Hregcoh" ∷ ⌜doc_registry_coh m bind types⌝ ∗
    "%Hhcoh"  ∷ ⌜history_state_coh h m⌝ ∗
    "%Hctr"   ∷ ⌜∀ (t : TId) x, x ∈ doc_model_get m t -> clientId (item_id x) = c ->
                   (clock (item_id x) < uint.nat k)%nat⌝ ∗
    (* part-6 pool invariants (issue #28): heap-level facts the model does not
       determine, so [own_store] carries them (store_inv ⊣⊢ ∃ own_store) *)
    "%Hlocdup" ∷ ⌜NoDup (ic_loc <$> all_cells types)⌝ ∗
    "%Hrangedisj" ∷ ⌜cells_range_disjoint (all_cells types)⌝ ∗
    "%Hrunfits" ∷ ⌜∀ c, c ∈ all_cells types → cell_fits c⌝ ∗
    "%Horiginclk" ∷ ⌜∀ c, c ∈ all_cells types → cell_origin_clk c⌝ ∗
    (* no-loss accepted-id layer (this branch): matches [store_inv_excl] *)
    "Hacc" ∷ own γs.(sn_accepted) (● acc : accUR) ∗
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
#[global] Instance types_frag_timeless γs q types : Timeless (types_frag γs q types).
Proof. rewrite /types_frag. apply _. Qed.

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
    carries [span_wf] for every span so [containsId]'s [w64] range test is
    exact. Owning heap data, it takes a [dfrac] (appending needs
    [DfracOwn 1]). *)
Definition own_id_set (s : slice.t) (dq : dfrac) (gs : gset YjsId) : iProp Σ :=
  ∃ (vs : list yjs.idSpan.t),
    "Hsl" ∷ s ↦*{dq} vs ∗
    "Hcap" ∷ own_slice_cap yjs.idSpan.t s dq ∗
    "%Hwf" ∷ ⌜Forall span_wf vs⌝ ∗
    "%Hset" ∷ ⌜⋃ (span_ids <$> vs) = gs⌝.

(** Loop invariant for the conflict scan in [Integrate]. The heap loop refines
    the pure set-based loop [set_find_integration_loop] *directly*: the heap slices
    [itemsBeforeOrigin] / [conflictingItems] literally carry the [set_find_integration_loop]
    accumulators [idsBeforeOrigin] / [conflictIds] (as [gset]s), and the loop's
    progress is tracked by a fuel equation — the remaining run from the current
    state equals the fixed overall result [loopResult]. (The
    [set_find_integration_loop ↔ fii_loop] equivalence is a separate, already-proved fact used
    only to inherit [YjsArrInvariant].)

    - [conflict_l] (Go [conflict]) sits at the cursor CELL [cur], whose run
      starts at model index [leftIdx+offset] (the coupling [Hcur]);
    - [left_l] (Go [left]) is the anchor: the cell just left of the insert
      boundary [curD], whose model boundary is [destIdx] ([HcurD]), so [item]
      is spliced after cell [curD - 1];
    - [right_l] (Go [right]) is loop-constant at CELL [curR] (the right
      origin / [Last]), whose model boundary is [rightIdx] (a spec premise);
      the [conflict == right] break compares cell locs, i.e. [cur = curR],
      which the prefix-sum injectivity turns into [leftIdx+offset = rightIdx];
    - [Hloop]: from the current accumulators, the remaining
      [Z.to_nat (rightIdx - leftIdx) - offset] steps of [set_find_integration_loop] still
      compute [loopResult]. With [Hbound] / [Hdest] this makes the Go
      [for conflict ≠ nil] test (with the [== right] break) consume exactly the
      loop's fuel.
    [own_fresh_item_raw] and the [parent.len] field are loop-constant, framed outside. *)
Definition integrate_loop_inv
    (parent : loc) (dq : dfrac) (cells : list item_cell) (arr : list (YjsItem A))
    (leftIdx rightIdx : Z) (curR : nat)
    (originLeftId originRightId : option YjsId) (newItemId : YjsId)
    (loopResult : option Z)
    (conflict_l left_l right_l idsBeforeOrigin_l conflictIds_l : loc)
    (offset cur curD : nat) (idsBeforeOrigin conflictIds : gset YjsId) (destIdx : Z) : iProp Σ :=
  "Htext" ∷ own_ytype_cells parent dq cells arr ∗
  "Hconflict" ∷ conflict_l ↦ node_loc cells (Z.of_nat cur) ∗
  "Hleft" ∷ left_l ↦ node_loc cells (Z.of_nat curD - 1) ∗
  "Hright" ∷ right_l ↦ node_loc cells (Z.of_nat curR) ∗
  "Hids_before" ∷ (∃ s : slice.t, "Hids_before_ref" ∷ idsBeforeOrigin_l ↦ s ∗
                     "Hids_before_set" ∷ own_id_set s (DfracOwn 1) idsBeforeOrigin) ∗
  "Hconflict_ids" ∷ (∃ s : slice.t, "Hconflict_ids_ref" ∷ conflictIds_l ↦ s ∗
                     "Hconflict_ids_set" ∷ own_id_set s (DfracOwn 1) conflictIds) ∗
  "%Hoff" ∷ ⌜(1 <= offset)%nat⌝ ∗
  "%Hcur" ∷ ⌜(Z.of_nat (length (run_flatten (take cur cells))) = leftIdx + Z.of_nat offset)%Z⌝ ∗
  "%Hcurb" ∷ ⌜(cur <= length cells)%nat⌝ ∗
  "%HcurD" ∷ ⌜(Z.of_nat (length (run_flatten (take curD cells))) = destIdx)%Z⌝ ∗
  "%HcurDb" ∷ ⌜(curD <= length cells)%nat⌝ ∗
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

(** [own_linked_item item_l input parent lft rgt]: the not-yet-integrated heap
    [Item] that [Store.Integrate] is about to splice in — everything about the
    caller's item is encapsulated here (its model value [itemVal] and origin
    pointers are existentially hidden). On top of [own_fresh_item_raw] it
    records that the item is already linked to its resolved origin neighbours
    ([left'] = [lft], [right'] = [rgt] — set by [store.repair] on the update
    path or by the local-edit creator, issue #49), carries its parent, and is
    a countable, single-char insert ([flags'] = ItemCountable, content length
    1) — exactly what [newItem] + linking produces. This is the item-side half
    of the Integrate spec. *)
Definition own_linked_item (item_l : loc) (input : IntegrateInput (A := A))
    (parent lft rgt : loc) : iProp Σ :=
  ∃ (itemVal : yjs.item.t) (oleft oright : option yjs.id.t),
    own_fresh_item_raw item_l input itemVal oleft oright ∗
    ⌜itemVal.(yjs.item.left') = lft⌝ ∗
    ⌜itemVal.(yjs.item.right') = rgt⌝ ∗
    ⌜itemVal.(yjs.item.parent') = parent⌝ ∗
    ⌜itemVal.(yjs.item.flags') = W8 2⌝ ∗
    ⌜length (itemVal.(yjs.item.content').(yjs.content.content')) = 1%nat⌝.

(** [own_linked_item_run]: the multi-char (run) variant of [own_linked_item]
    (issue #28 U7). Identical except the content is a nonempty run
    ([1 <= length], not [= 1]) — an [n]-char wire item denoting [n] chained
    per-char model ops. Used by the update path ([applyUpdate]), where a decoded
    wire struct can carry a whole run; the single-char [own_linked_item] stays
    for the local-edit [Text.Insert] path. *)
Definition own_linked_item_run (item_l : loc) (input : IntegrateInput (A := A))
    (parent lft rgt : loc) : iProp Σ :=
  ∃ (itemVal : yjs.item.t) (oleft oright : option yjs.id.t),
    own_fresh_item_raw item_l input itemVal oleft oright ∗
    ⌜itemVal.(yjs.item.left') = lft⌝ ∗
    ⌜itemVal.(yjs.item.right') = rgt⌝ ∗
    ⌜itemVal.(yjs.item.parent') = parent⌝ ∗
    ⌜itemVal.(yjs.item.flags') = W8 2⌝ ∗
    ⌜(1 <= length (itemVal.(yjs.item.content').(yjs.content.content')))%nat⌝.

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

(** [own_item_map] is a function of the document-global (client, clock, loc)
    projection [cell_kp <$> all_cells] alone: two [types] with the same [cell_kp]
    multiset carry the same run-map. [Text.Delete] flips [ic_deleted] bits, which
    leaves every cell's [cell_kp] untouched, so the store's item set is preserved
    verbatim across a delete — this lemma converts the item map from the
    pre-delete [types] to the flipped-cells [types]. *)
(* [Proof using Type] (statement variables only) instead of the file default
   [Type*]: this pure heap/list reshuffle uses neither [seq_inG] nor
   [ftypes_inG], so trimming them makes the lemma usable in the [store/GetNode]
   section, which does not carry those instances (issue #54's
   [integrateDecoded]-fresh path converts the item map across a fresh empty
   type). *)
Lemma own_item_map_kp_perm (mref : loc) (dq : dfrac) (M1 M2 : gmap loc type_state) :
  cell_kp <$> all_cells M2 ≡ₚ cell_kp <$> all_cells M1 ->
  own_item_map mref dq M1 -∗ own_item_map mref dq M2.
Proof using Type.
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
  ∃ client k items_mref types_mref dset pend_sl types bind h m pend,
    store_inv_excl s_loc γs γh client k items_mref types_mref dset pend_sl types bind h m pend ∗
    store_inv_ro γs types 1.
Proof. rewrite /store_inv /named //. Qed.

Lemma tf_split γs q1 q2 types :
  types_frag γs (q1 + q2) types ⊣⊢ types_frag γs q1 types ∗ types_frag γs q2 types.
Proof. rewrite /types_frag -own_op -frac_agree_op //. Qed.

Lemma tf_agree γs q1 q2 t1 t2 : types_frag γs q1 t1 -∗ types_frag γs q2 t2 -∗ ⌜t1 = t2⌝.
Proof.
  iIntros "H1 H2". iCombine "H1 H2" gives %Hv.
  iPureIntro. by apply frac_agree_op_valid_L in Hv as [_ ->].
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
  iExists client, k, items_mref, types_mref, dset, pend_sl, types, bind, acc.
  iFrame "∗#". iPureIntro. split_and!;
    [exact Hclientc | exact Hpendroot | exact Hpendbnd | exact Hregcoh | exact Hhcoh | exact Hctr
    | exact Hlocdup | exact Hrangedisj | exact Hrunfits | exact Horiginclk | exact Hacccoh].
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
  iExists client, k, items_mref, types_mref, dset, pend_sl, types, bind, (acc ∪ T).
  iFrame "∗#". iPureIntro. split_and!;
    [exact Hclientc | exact Hpendroot | exact Hpendbnd | exact Hregcoh | exact Hhcoh | exact Hctr
    | exact Hlocdup | exact Hrangedisj | exact Hrunfits | exact Horiginclk |].
  rewrite /accepted_coh. apply union_least; [exact Hacccoh | exact HTsub].
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
  (* the grow-only accepted-id set starts empty *)
  iMod (own_alloc (● (∅ : gset YjsId) : accUR)) as (γacc) "Hacc0".
  { apply auth_auth_valid. done. }
  set (γrw := {| prot_gn := {| read_wait_gn := γd; rlock_overflow_gn := γd;
                               wlock_gn := γd; writer_sem_tok_gn := γd; state_gn := γd |};
                 reader_sem_gn := γd; writer_sem_gn := γd |} : RWMutex_names).
  set (γs := {| sn_seq := γseq; sn_types := γtypes; sn_wl := γwl;
                sn_rw := γrw; sn_rmax := γrmax; sn_rrlocked := γrrlocked;
                sn_types_agree := γta; sn_accepted := γacc |}).
  iModIntro. iExists γs.
  iExists client, k, items_mref, types_mref, dset, slice.nil, types, (∅ : gmap P loc),
    ([] : list Ev), (∅ : DocModel), ([] : list (TId * IntegrateInput (A := A))).
  iSplitR "Hseq"; last first.
  { (* store_inv_ro over the empty types map *)
    iFrame "Hseq". rewrite /types big_sepM_empty //. }
  (* store_inv_excl *)
  iExists (∅ : gset YjsId).
  iFrame "Hclient Hclock Hitemsf Htypesf Htypesmap Hdset Hpendf Hhist HtypesAuth Hacc0".
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
  { (* the empty pending buffer over the nil slice *)
    iExists []. iSplitR; [iApply own_slice_nil |].
    iSplitR; [iApply own_slice_cap_nil |]. rewrite big_sepL2_nil //. }
  iSplitR.
  { have He : expand_inputs [] = [] by done.
    rewrite /is_pending_certified He big_sepL_nil //. }
  iSplitR.
  { iPureIntro. move=> typedInput Hin. by apply elem_of_nil in Hin. }
  iSplitR.
  { iPureIntro. move=> typedInput Hin. by apply elem_of_nil in Hin. }
  iSplitR. { iPureIntro. move=> parent' ts' x Hlk. rewrite /types lookup_empty // in Hlk. }
  iSplitR. { iPureIntro. move=> c Hc. exfalso. move: Hc.
    rewrite /types /all_cells map_to_list_empty /= elem_of_nil //. }
  iSplitR. { iPureIntro. rewrite /types /all_cells map_to_list_empty /=. constructor. }
  iSplitR. { iPureIntro. move=> c1 c2 Hc1. exfalso. move: Hc1.
    rewrite /types /all_cells map_to_list_empty /= elem_of_nil //. }
  iSplitR. { iPureIntro. move=> c Hc. exfalso. move: Hc.
    rewrite /types /all_cells map_to_list_empty /= elem_of_nil //. }
  iSplitR. { iPureIntro. move=> c Hc. exfalso. move: Hc.
    rewrite /types /all_cells map_to_list_empty /= elem_of_nil //. }
  iSplitR. { rewrite big_sepM_empty //. }
  iPureIntro. split_and!.
  - move=> name p' Hlk. rewrite lookup_empty // in Hlk.
  - move=> n1 n2 p' Hlk. rewrite lookup_empty // in Hlk.
  - move=> p' [ts' Hlk]. rewrite /types lookup_empty // in Hlk.
  - exact history_state_coh_nil.
  - move=> name p' ts' Hlk. rewrite lookup_empty // in Hlk.
  - move=> t Hne. exfalso. apply Hne. rewrite /doc_model_get lookup_empty //.
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
  iSplitL "Hclient Hclock Hitemsf Hitemmap Htypesf Htypesmap Hdset Hpendf Hpend Hseq Htypes HtypesAuth Hhist Hacc".
  - iExists client, k, items_mref, types_mref, dset, pend_sl, types, bind, acc.
    iFrame "∗#".
    iPureIntro. split_and!;
      [exact Hclientc | exact Hpendroot | exact Hpendbnd | exact Hregcoh | exact Hhcoh | exact Hctr
      | exact Hlocdup | exact Hrangedisj | exact Hrunfits | exact Horiginclk | exact Hacccoh].
  - iPureIntro. exact Hhcoh.
Qed.

End store_heap.
