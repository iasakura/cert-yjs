(** The [Text] handle, Iris layer.

    Definitions
    - [is_Text t γs γh name L]: the handle is a [Text] on the store [γs] whose
      root type is called [name] and whose item list contains at least [L].
      Persistent, and grow-only in [L].
    - what a read ([Text.Len] / [Text.String]) sees: [text_snapshot L marr]
      (a valid document holding [L]) and [history_reflected h0 name marr]
      (every insert a history prefix delivered is in it).

    Laws
    - [is_Text_root] / [is_Text_root_lb]: the root witnesses a reader may
      project out of the handle, which is all the store layer exposes about it.

    The [Text] handle has no model of its own: the sequence it exposes is the
    [yType] model, so its list-level theory is [ytype/model.v]. The method
    proofs are [text/Insert.v], [text/Delete.v] and [text/Len.v]. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core.
From New.proof Require Import algebra.
From New.proof Require Import prelude.
From New.proof Require Import history.
From New.proof.sync_proof Require Import mutex.
From iris.algebra Require Import auth gmap gset.
From iris.algebra.lib Require Import dfrac_agree.
From stdpp Require Import sorting.
From New.proof.id Require Import value heap.
From New.proof.item Require Import run_theory model value heap.
From New.proof.ytype Require Import model value heap.
From New.proof.store Require Import model value heap.
From New.proof.text Require Import model.
(* iris.algebra / stdpp.sorting push [nat_scope], retuning the default [<] / [≤];
   the verified word-arithmetic proofs write [Z] comparisons unannotated, so
   restore [Z_scope] as the default. *)
Local Open Scope Z_scope.

Section text_heap.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

(** Store lock = a [sync.RWMutex] (write path here, via [wp_Store__wlock] /
    [wp_Store__wunlock]); the per-text item set lives in a grow-only auth
    (the same RA as [store/store], used by [is_type_lb]). *)
Context {sync_pkg : sync.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.

Context {seq_inG : inG Σ (authR (gmapUR loc (gsetUR (YjsItem A))))}.

(* [is_Store]'s reader-count accounting ties the readers' share to the store's
   [types] map via a [dfrac_agree]; threaded here so [is_Text]/[is_Store] uses
   in this file (Insert/Delete/Len) can discharge the instance. *)
Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO addressed_pool))}.

(* The ghost op-history types at the document content type; type names are Go
   strings (issue #49). *)
Local Notation P := go_string.

Local Notation TId := (TypeId P).

Local Notation Op := (TId * @YjsOperation A)%type.

Local Notation Ev := (@Event Op).

Local Notation DocModel := (gmap TId (list (YjsItem A))).

(* ===== definitions ======================================================== *)

(* ----- the Text handle invariant ----------------------------------------
   [is_Text] lives here; the Doc-layer predicate [is_Doc] lives in doc/heap.v
   (mirrors doc.go). [is_Text] delegates straight to the store invariants
   ([is_Store] / [is_type_lb]) in store/heap, referencing only Text's own fields.
   [wp_Text__Insert] is proved (Lock → store_inv → findPos/Integrate loop → grow
   the item-set auth → Unlock). *)

(** Text handle (persistent), parameterized by a SORTED list [L] of known items:
    reads ONLY its OWN fields ([store]/[inner], immutable ⇒ [↦□]) and delegates
    straight to [is_Store] (no Doc hop — Text holds [store] directly). The ghost
    is fed the item-SET of [L] ([is_type_lb] over [gset (YjsItem A)], a subset
    lower bound — grow-only, no [mra] needed), while [L] is required
    [StronglySorted] by the document order [YjsLt'] (the order
    [YjsArrInvariant.yai_sorted] uses). Tracking full items (not just ids) pins
    each [x ∈ L] to a genuine document item, so [L] is a real CRDT-ordered
    sub-sequence of the current content (a directly-readable [sublist]/string
    lower bound). Says NOTHING about store fields. Persistent ⇒ the [Insert] spec
    is pre/post in the same predicate (with [L] growing).

    Network layer (issues #42/#49): the handle also carries the (persistent)
    ghost op-history handle [is_history γh] and its root-type binding
    [is_type_binding] — the handle's text is the one the store's registry
    binds to [name], which is what ties the store's per-type history view to
    THIS text under the lock. *)
Definition is_Text (t : loc) (γs : store_names) (γh : history_names) (name : P) (L : list (YjsItem A)) : iProp Σ :=
  ∃ (tv : yjs.Text.t) (s_loc parent : loc),
    "Ht" ∷ t ↦□ tv ∗
    "%Hstore" ∷ ⌜tv.(yjs.Text.store') = s_loc⌝ ∗
    "%Hinner" ∷ ⌜tv.(yjs.Text.inner') = parent⌝ ∗
    "His_store" ∷ is_Store s_loc γs γh ∗
    "#His_hist" ∷ is_history (A := A) (P := P) γh ∗
    "#Hbind" ∷ is_type_binding γs.(sn_types) name parent ∗
    "His_lb" ∷ is_type_lb γs.(sn_seq) parent (list_to_set L) ∗
    "%Hsorted" ∷ ⌜StronglySorted (λ x y : YjsItem A, YjsLt' (itemPtr x) (itemPtr y)) L⌝.

#[global] Instance is_Text_persistent t γs γh name L : Persistent (is_Text t γs γh name L).
Proof. apply _. Qed.

(* ===== lemmas ============================================================= *)

(** A Text handle certifies its root at the store level: the name is
    registered ([is_root]) and the handle's known content is a lower bound
    of the root's item set ([is_root_lb]), with the handle's inner pointer
    as the hidden binding witness. These are the projections that let a
    Text-handle holder feed the [applyUpdate] certificate spec (its
    [is_root] precondition) and compare its content bound against the
    [is_root_lb] certificates the spec returns. [is_Text] itself keeps the
    binding and the lower bound as separate conjuncts because it must also
    pin the binding's loc to the handle's [inner] field. *)
Lemma is_Text_root (t : loc) (γs : store_names) (γh : history_names)
    (name : P) (L : list (YjsItem A)) :
  is_Text t γs γh name L -∗ is_root γs name.
Proof. iIntros "H". iNamed "H". iExists _. iFrame "Hbind". Qed.

Lemma is_Text_root_lb (t : loc) (γs : store_names) (γh : history_names)
    (name : P) (L : list (YjsItem A)) :
  is_Text t γs γh name L -∗ is_root_lb γs name (list_to_set L).
Proof. iIntros "H". iNamed "H". iExists _. iFrame "Hbind His_lb". Qed.

(** [Text.Insert] preserves the (persistent) document handle, grows the known
    content ([L ⊑ L']), AND exposes the inserted run [ins]: one fresh item per
    byte of [content], each now known ([∈ L'], and [∉ L] since its id is fresh),
    carrying that byte as content, with a fresh id [(client, k0+i)] (one local
    [client], consecutive clocks from some [k0]), the run's shared right origin
    [originRight], and its left origin chained (item 0 from [originLeft], item i+1 from item i).
    This says exactly "the characters you inserted are in [L'−L], with these
    content / id / left / right".

    Proof shape: peel [is_Text → is_Store] and take the RWMutex write lock
    ([wp_Store__wlock]), which yields [store_inv]; combine [is_type_lb] with
    [Hseq] (auth) via
    [auth_gmap_gset_lookup] to learn [parent ∈ dom types] and extract THIS text's
    [type_state] / DLL from [Htypes]; run the findPos/Integrate loop, whose
    invariant accumulates [ins] with the per-byte facts (content/id/origins) plus
    [ty_arr ts ⊆ arr]; at exit grow the auth item-set ([ty_arr ts → arr]) with
    [auth_gmap_gset_grow] and mint the new [is_type_lb]; reinsert the grown text
    into [Htypes] ([big_sepM_insert_acc]); rebuild [store_inv] (clock bumped,
    counter [Hctr] preserved); [Unlock]; return with [L' = arr]. The post's
    [sublist L L'] follows from [sorted_subseteq_sublist] (both sorted, [L ⊆ L']
    as items via the item-set ghost), and [it ∉ L] from the fresh clocks vs the
    initial [Hctr]. Overflow is ruled out by a Go-side guard in [Text.Insert]
    (its early return takes the [ins = []] disjunct); [k] stays hidden in the
    lock. Axiom-clean ([Print Assumptions] shows only goose/Perennial axioms). *)

End text_heap.
