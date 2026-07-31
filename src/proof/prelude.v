(** The shared base every cert-yjs proof file sits on.

    Deliberately tiny, and it holds no definitions on purpose: its whole job is
    to declare the goose package-init instances once, so that every WP file
    inherits [is_pkg_init yjs] via [Require] instead of redeclaring it. Anything
    that belongs to a Go type lives in that type's directory: its pure model in
    [model.v], its representation and invariants in [heap.v]. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core.
(* The Go package now imports sync (store.mu : sync.RWMutex), so the generated
   yjs package imports sync; building [IsPkgInit yjs] below needs
   [IsPkgInit sync] (and [GetIsPkgInitWf sync]) in scope, provided by the sync
   proof base. The required [sync.Assumptions] comes from [yjs.Assumptions] (its
   [import_sync_Assumption ::] field). *)
From New.proof.sync_proof Require Import base.

Section prelude.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

#[global] Instance : IsPkgInit (iProp Σ) yjs := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) yjs := build_get_is_pkg_init_wf.

Set Default Proof Using "Type*".

(** Document content type. *)
Notation A := go_string.

End prelude.
