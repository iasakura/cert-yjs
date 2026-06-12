(* Proofs about yjs/yjs.go. Counter is a pipeline-smoke-test placeholder;
   real CRDT proofs go here. *)
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

Definition own_counter (c : loc) (n : w64) : iProp Σ :=
  "Hvalue" ∷ c.[yjs.Counter.t, "value"] ↦ n.

Lemma wp_Get (c : loc) (n : w64) :
  {{{ is_pkg_init yjs ∗ own_counter c n }}}
    c @! (go.PointerType yjs.Counter) @! "Get" #()
  {{{ RET #n; own_counter c n }}}.
Proof.
  wp_start as "Hown". iNamed "Hown".
  wp_auto.
  iApply "HΦ". iFrame.
Qed.

Lemma wp_Inc (c : loc) (n : w64) :
  {{{ is_pkg_init yjs ∗ own_counter c n }}}
    c @! (go.PointerType yjs.Counter) @! "Inc" #()
  {{{ RET #(); own_counter c (word.add n (W64 1)) }}}.
Proof.
  wp_start as "Hown". iNamed "Hown".
  wp_auto.
  iApply "HΦ". iFrame.
Qed.

End proof.
