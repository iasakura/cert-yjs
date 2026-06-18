(* Proofs about yjs/yjs.go.

   Phase 1 foundation: the goose-translated model of the core CRDT data
   structures (Id, Content, Item, Store, ...) is in
   New.code.github_com.iasakura.cert_yjs.yjs; here we establish the
   verification scaffold by proving specs for the basic operations and one
   functional-correctness round-trip property. Later phases extend this with
   the integrate algorithm. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

#[global] Instance : IsPkgInit (iProp Σ) yjs := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) yjs := build_get_is_pkg_init_wf.

(* ----- Id ----------------------------------------------------------------- *)

(* NewId builds the expected struct value. *)
Lemma wp_NewId (client clock : w64) :
  {{{ is_pkg_init yjs }}}
    @! yjs.newId #client #clock
  {{{ RET #(yjs.id.mk client clock); True }}}.
Proof.
  wp_start. wp_auto. iApply "HΦ". done.
Qed.

(* Add advances the clock; the client is untouched. *)
Lemma wp_Id__Add (id : yjs.id.t) (n : w64) :
  {{{ is_pkg_init yjs }}}
    id @! yjs.id @! "Add" #n
  {{{ RET #(yjs.id.mk id.(yjs.id.clientId') (word.add id.(yjs.id.clock') n)); True }}}.
Proof.
  wp_start. wp_auto. iApply "HΦ". done.
Qed.

(* Sub rewinds the clock; the client is untouched. *)
Lemma wp_Id__Sub (id : yjs.id.t) (n : w64) :
  {{{ is_pkg_init yjs }}}
    id @! yjs.id @! "Sub" #n
  {{{ RET #(yjs.id.mk id.(yjs.id.clientId') (word.sub id.(yjs.id.clock') n)); True }}}.
Proof.
  wp_start. wp_auto. iApply "HΦ". done.
Qed.

(* Functional-correctness round-trip: Sub undoes Add (machine-word level,
   holds unconditionally because subtraction is the inverse of addition mod
   2^64). This is the kind of property the foundation lets us state. *)
Lemma id_add_sub_roundtrip (id : yjs.id.t) (n : w64) :
  yjs.id.mk
    (yjs.id.mk id.(yjs.id.clientId') (word.add id.(yjs.id.clock') n)).(yjs.id.clientId')
    (word.sub (yjs.id.mk id.(yjs.id.clientId') (word.add id.(yjs.id.clock') n)).(yjs.id.clock') n)
  = id.
Proof.
  destruct id as [c k]. simpl. f_equal. word.
Qed.

(* ----- Node interface impls ----------------------------------------------- *)

(* The Node accessors read out of the embedded NodeLen / Item; here we pin down
   the GC-node projections, which the store's binary search relies on. *)
Lemma wp_GCNode__clock (n : yjs.gcNode.t) :
  {{{ is_pkg_init yjs }}}
    n @! yjs.gcNode @! "clock" #()
  {{{ RET #(n.(yjs.gcNode.nodeLen').(yjs.nodeLen.id').(yjs.id.clock')); True }}}.
Proof.
  wp_start. wp_auto. iApply "HΦ". done.
Qed.

Lemma wp_GCNode__length (n : yjs.gcNode.t) :
  {{{ is_pkg_init yjs }}}
    n @! yjs.gcNode @! "length" #()
  {{{ RET #(n.(yjs.gcNode.nodeLen').(yjs.nodeLen.len')); True }}}.
Proof.
  wp_start. wp_auto. iApply "HΦ". done.
Qed.

End proof.
