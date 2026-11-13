(** The deployment's protocols on the ws FFI (issue #107, issue #131): what
    the verified server (ws_relay.v) and the verified client (ws_client.v)
    both take about the FFI's global state, and the package initialization
    predicate of the FFI's Go package, which both import.

    API
    - [deployment_protocols decode γh]: the FFI's wire protocol is
      [yjs_prot decode γh] and its trace protocol is [is_report γh].
    - [wp_wsnet_initialize'] / [wp_yjs_initialize']: the initialization of
      the two packages every node imports, for the nodes' boot lemmas. *)
From New.proof Require Import proof_prelude.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import wsnet.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import prelude.
From New.proof.sync_proof Require Import base mutex rwmutex.
From New.goose_lang.ffi.ws_ffi Require Import ws_ffi.
From New.proof Require Import core.
From New.proof Require Import history.
From New.proof Require Import yjs_prot.
From New.proof.report Require Import report.

Section deployment.
Context {Σ : gFunctors} {hG : heapGS Σ}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.
Context {sync_pkg : sync.Assumptions}.
Context {wsnet_pkg : wsnet.Assumptions}.

#[global] Instance : IsPkgInit (iProp Σ) wsnet := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) wsnet := build_get_is_pkg_init_wf.

Set Default Proof Using "Type*".

Notation A := (list w16).
Notation P := go_string.
Local Notation TId := (TypeId P).
Local Notation Input := (TId * IntegrateInput (A := A))%type.

(** The abstract codec the deployment runs under (see yjs_prot.v). *)
Context (decode : list u8 -> option (list Input)).

(* ===== definitions ======================================================== *)

(** The deployment's protocols on the FFI's global state: the wire protocol
    is [yjs_prot] (receives convert their [ws_prot] payload into
    certificates, sends convert them back) and the trace protocol is
    [is_report] (what every report a node traces must satisfy). *)
Definition deployment_protocols (γh : history_names) : Prop :=
  (∀ d, ws_prot d = yjs_prot decode γh d) ∧ (∀ d, trace_prot d = is_report γh d).

(* ===== lemmas ============================================================= *)

Lemma wp_wsnet_initialize' get_is_pkg_init :
  get_is_pkg_init_prop wsnet get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init }}}
    wsnet.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init wsnet }}}.
Proof.
  intros Hinit. wp_start as "Hown".
  wp_apply (wp_package_init with "[$Hown] HΦ").
  { destruct Hinit as (-> & ?); done. }
  iIntros "Hown". wp_auto.
  iEval (rewrite is_pkg_init_unfold /=). iFrame "∗#". done.
Qed.

Lemma wp_yjs_initialize' get_is_pkg_init :
  get_is_pkg_init_prop yjs get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init }}}
    yjs.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init yjs }}}.
Proof.
  intros Hinit. wp_start as "Hown".
  wp_apply (wp_package_init with "[$Hown] HΦ").
  { destruct Hinit as (-> & ?); done. }
  iIntros "Hown". wp_auto.
  wp_apply (sync.wp_initialize' with "[$Hown]") as "(Hown & #?)".
  { naive_solver. }
  iEval (rewrite is_pkg_init_unfold /=). iFrame "∗#". done.
Qed.

End deployment.
