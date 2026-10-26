(** The report, Iris layer (issue #239): the slice an encoder returns and
    what a trace entry certifies.

    Definitions
    - [own_report sl dq name chars]: ownership of a slice holding a report
      of root [name] with characters [chars]: bytes that decode to them
      ([decode_report]), with the slice's capacity. What [EncodeReport]
      returns.
    - [is_report γh d]: the bytes [d] are a report a replica wrote: they
      decode to a root's name and the characters of an exact read
      certificate of that root ([is_text_state], history.v), whose ids fit
      the machine words ([item_fits]). Made to be chosen as the trace
      protocol ([trace_prot], the ws FFI) by a deployment that traces
      reports; the server's closed theorem does.

    Laws
    - [is_report_pair_converge]: two reports about one root holding the
      same ids spell the same text, by the exact certificates' convergence
      ([is_text_state_convergence]).
    - [is_report_trace_converge]: the same over a whole trace
      ([reports_converge]); what the closed theorem exports. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core.
From New.proof Require Import prelude.
From New.proof Require Import history.
From New.proof.item Require Import model.
From New.proof.ytype Require Import model value.
From New.proof.report Require Import value.

Section report_slice.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

(* ===== definitions ======================================================== *)

Definition own_report (sl : slice.t) (dq : dfrac) (name : go_string)
    (chars : list yjs.SnapshotChar.t) : iProp Σ :=
  ∃ bytes : list u8,
    "Hreport_bytes" ∷ sl ↦*{dq} bytes ∗
    "Hreport_cap" ∷ own_slice_cap w8 sl dq ∗
    "%Hreport_decode" ∷ ⌜decode_report bytes = Some (name, chars)⌝.

End report_slice.

Section report_heap.

(* [allG] only (no [heapGS]), as [yjs_prot]: the trace protocol must be
   nameable inside an adequacy theorem's initial fancy update, before any
   node exists. *)
Context {Σ : gFunctors} `{!allG Σ}.

Set Default Proof Using "Type*".

Notation A := (list w16).
Notation P := go_string.
Local Notation TId := (TypeId P).
Local Notation Op := (TId * @YjsOperation A)%type.
Local Notation Ev := (@Event Op).

(* ===== definitions ======================================================== *)

Definition is_report (γh : history_names) (d : list u8) : iProp Σ :=
  ∃ (c : ClientId) (h : list Ev) (name : P) (s : list (YjsItem A * bool)),
    "#Hreport_state" ∷ is_text_state γh c h name s ∗
    "%Hreport_fits" ∷ ⌜Forall item_fits s.*1⌝ ∗
    "%Hreport_decode" ∷ ⌜decode_report d = Some (name, snapshot_chars s)⌝.

#[global] Instance is_report_persistent γh d : Persistent (is_report γh d).
Proof. rewrite /is_report. apply _. Qed.

End report_heap.

Section report_heap_laws.

(* The laws open the history invariant, so they need [invGS] besides
   [allG]; the definition above does not, and so stays nameable before any
   node exists. *)
Context {Σ : gFunctors} `{!allG Σ, !invGS Σ}.

Set Default Proof Using "Type*".

Notation A := (list w16).
Notation P := go_string.
Local Notation TId := (TypeId P).
Local Notation Op := (TId * @YjsOperation A)%type.
Local Notation Ev := (@Event Op).

(* ===== lemmas ============================================================= *)

Lemma is_report_pair_converge (γh : history_names) (d1 d2 : list u8) (E : coPset) :
  ↑histN ⊆ E ->
  is_history (A := A) (P := P) γh -∗ is_report γh d1 -∗ is_report γh d2 -∗
  |={E}=> ⌜∀ (name : P) (chars1 chars2 : list yjs.SnapshotChar.t),
      decode_report d1 = Some (name, chars1) -> decode_report d2 = Some (name, chars2) ->
      report_ids chars1 = report_ids chars2 -> report_text chars1 = report_text chars2⌝.
Proof.
  iIntros (HE) "#Hhist #H1 #H2".
  iDestruct "H1" as (c1 h1 name1 s1) "(#Hst1 & %Hfit1 & %Hdec1)".
  iDestruct "H2" as (c2 h2 name2 s2) "(#Hst2 & %Hfit2 & %Hdec2)".
  destruct (decide (name1 = name2 ∧ report_ids (snapshot_chars s1) = report_ids (snapshot_chars s2)))
    as [[-> Hids] | Hno].
  - (* same root, same ids: the certified items coincide *)
    iMod (is_text_state_convergence γh c1 c2 h1 h2 name2 s1 s2 E HE with "Hhist Hst1 Hst2 []")
      as %Heq.
    { iPureIntro. exact (report_ids_snapshot_chars s1 s2 Hfit1 Hfit2 Hids). }
    iPureIntro. move=> name chars1 chars2 Hd1 Hd2 _.
    rewrite Hdec1 in Hd1. injection Hd1 as _ <-.
    rewrite Hdec2 in Hd2. injection Hd2 as _ <-.
    exact (report_text_snapshot_chars s1 s2 Heq).
  - (* different roots or different ids: nothing to show *)
    iPureIntro. move=> name chars1 chars2 Hd1 Hd2 Hids. exfalso. apply Hno.
    rewrite Hdec1 in Hd1. injection Hd1 as <- <-.
    rewrite Hdec2 in Hd2. injection Hd2 as <- <-.
    done.
Qed.

Lemma is_report_trace_converge (γh : history_names) (T : list (list u8)) (E : coPset) :
  ↑histN ⊆ E ->
  is_history (A := A) (P := P) γh -∗ ([∗ list] d ∈ T, is_report γh d) -∗
  |={E}=> ⌜reports_converge T⌝.
Proof.
  iIntros (HE) "#Hhist #HT".
  iAssert (|={E}=> [∗ list] d1 ∈ T,
      ⌜∀ (d2 : list u8) (name : P) (chars1 chars2 : list yjs.SnapshotChar.t), d2 ∈ T ->
         decode_report d1 = Some (name, chars1) -> decode_report d2 = Some (name, chars2) ->
         report_ids chars1 = report_ids chars2 -> report_text chars1 = report_text chars2⌝)%I
    with "[]" as ">Hall".
  { iApply big_sepL_fupd. iApply big_sepL_intro. iIntros "!>" (k1 d1 Hd1).
    iDestruct (big_sepL_lookup _ _ k1 d1 Hd1 with "HT") as "#H1".
    iAssert (|={E}=> [∗ list] d2 ∈ T,
        ⌜∀ (name : P) (chars1 chars2 : list yjs.SnapshotChar.t),
           decode_report d1 = Some (name, chars1) -> decode_report d2 = Some (name, chars2) ->
           report_ids chars1 = report_ids chars2 -> report_text chars1 = report_text chars2⌝)%I
      with "[]" as ">Hd1".
    { iApply big_sepL_fupd. iApply big_sepL_intro. iIntros "!>" (k2 d2 Hd2).
      iDestruct (big_sepL_lookup _ _ k2 d2 Hd2 with "HT") as "#H2".
      iApply (is_report_pair_converge γh d1 d2 E HE with "Hhist H1 H2"). }
    iDestruct (big_sepL_pure_1 with "Hd1") as %Hd1all.
    iPureIntro. move=> d2 name chars1 chars2 Hd2.
    destruct (list_elem_of_lookup_1 _ _ Hd2) as [k2 Hk2].
    exact (Hd1all k2 d2 Hk2 name chars1 chars2). }
  iDestruct (big_sepL_pure_1 with "Hall") as %Hall.
  iPureIntro. move=> d1 d2 name chars1 chars2 Hd1 Hd2.
  destruct (list_elem_of_lookup_1 _ _ Hd1) as [k1 Hk1].
  exact (Hall k1 d1 Hk1 d2 name chars1 chars2 Hd2).
Qed.

End report_heap_laws.
