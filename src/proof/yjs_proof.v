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
    @! yjs.NewId #client #clock
  {{{ RET #(yjs.Id.mk client clock); True }}}.
Proof.
  wp_start. wp_auto. iApply "HΦ". done.
Qed.

(* Add advances the clock; the client is untouched. *)
Lemma wp_Id__Add (id : yjs.Id.t) (n : w64) :
  {{{ is_pkg_init yjs }}}
    id @! yjs.Id @! "Add" #n
  {{{ RET #(yjs.Id.mk id.(yjs.Id.clientId') (word.add id.(yjs.Id.clock') n)); True }}}.
Proof.
  wp_start. wp_auto. iApply "HΦ". done.
Qed.

(* Sub rewinds the clock; the client is untouched. *)
Lemma wp_Id__Sub (id : yjs.Id.t) (n : w64) :
  {{{ is_pkg_init yjs }}}
    id @! yjs.Id @! "Sub" #n
  {{{ RET #(yjs.Id.mk id.(yjs.Id.clientId') (word.sub id.(yjs.Id.clock') n)); True }}}.
Proof.
  wp_start. wp_auto. iApply "HΦ". done.
Qed.

(* Functional-correctness round-trip: Sub undoes Add (machine-word level,
   holds unconditionally because subtraction is the inverse of addition mod
   2^64). This is the kind of property the foundation lets us state. *)
Lemma id_add_sub_roundtrip (id : yjs.Id.t) (n : w64) :
  yjs.Id.mk
    (yjs.Id.mk id.(yjs.Id.clientId') (word.add id.(yjs.Id.clock') n)).(yjs.Id.clientId')
    (word.sub (yjs.Id.mk id.(yjs.Id.clientId') (word.add id.(yjs.Id.clock') n)).(yjs.Id.clock') n)
  = id.
Proof.
  destruct id as [c k]. simpl. f_equal. word.
Qed.

(* ----- Node interface impls ----------------------------------------------- *)

(* The Node accessors read out of the embedded NodeLen / Item; here we pin down
   the GC-node projections, which the store's binary search relies on. *)
Lemma wp_GCNode__clock (n : yjs.GCNode.t) :
  {{{ is_pkg_init yjs }}}
    n @! yjs.GCNode @! "clock" #()
  {{{ RET #(n.(yjs.GCNode.nodeLen').(yjs.NodeLen.id').(yjs.Id.clock')); True }}}.
Proof.
  wp_start. wp_auto. iApply "HΦ". done.
Qed.

Lemma wp_GCNode__length (n : yjs.GCNode.t) :
  {{{ is_pkg_init yjs }}}
    n @! yjs.GCNode @! "length" #()
  {{{ RET #(n.(yjs.GCNode.nodeLen').(yjs.NodeLen.len')); True }}}.
Proof.
  wp_start. wp_auto. iApply "HΦ". done.
Qed.

End proof.
