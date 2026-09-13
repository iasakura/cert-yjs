(** The [TextObserver], VALUE layer: what the Go values of the observer
    denote. Go values, no Iris.

    Definitions
    - [delta_op_denotes v op]: the [DeltaOp] struct value [v] is the entry
      [op]: its kind byte, and its count as a machine word or its content.
      The count is the model's [nat] taken modulo [2^64] ([W64]), the way
      [yType.len] denotes [runs_visible]: a walk adds [uint64] counts, and
      nothing bounds a text below [2^64] chars; [delta_fits] is the bound
      under which the word is the count.
    - [state_vector_denotes m sv]: the [map[Client]Clock] contents [m] are
      the state vector [sv] (per client word, the next clock).
    - [span_covers client sp d] / [spans_cover spans d]: a [span[uint64]] of
      [client] covers the id [d]; some span of the per-client span lists
      does. What the observer's deleted-spans map means.

    Laws
    - [spans_cover_insert]: appending one span to a client's list covers
      what was covered, plus the span.
    - [state_vector_denotes_run]: raising a client's entry to a run's end
      when that is larger (what the walk does per node) denotes the join
      with the run's state vector. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core network_model.
From New.proof.item Require Import model.
From New.proof.ytype Require Import model.
From New.proof.textobserver Require Import model.

Section text_observer_value.

Set Default Proof Using "Type*".

Notation A := go_string.

(* ===== definitions ======================================================== *)

(** The kind bytes of the Go [DeltaKind]: retain 0, insert 1, delete 2. *)
Definition delta_op_denotes (v : yjs.DeltaOp.t) (op : DeltaOp) : Prop :=
  match op with
  | Retain n => v.(yjs.DeltaOp.Kind') = W8 0 ∧ v.(yjs.DeltaOp.Length') = W64 (Z.of_nat n)
  | Insert t => v.(yjs.DeltaOp.Kind') = W8 1 ∧ v.(yjs.DeltaOp.Content') = t
  | Delete n => v.(yjs.DeltaOp.Kind') = W8 2 ∧ v.(yjs.DeltaOp.Length') = W64 (Z.of_nat n)
  end.

(** Per client word, the map holds the next clock (absent = 0). *)
Definition state_vector_denotes (m : gmap w64 w64) (sv : gmap ClientId nat) : Prop :=
  ∀ client : w64, uint.nat (default (W64 0) (m !! client)) = sv_get sv (uint.nat client).

Definition span_covers (client : w64) (sp : yjs.span.t w64) (d : YjsId) : Prop :=
  clientId d = uint.nat client ∧
  (uint.nat sp.(yjs.span.start') <= clock d)%nat ∧
  (clock d < uint.nat sp.(yjs.span.end'))%nat.

Definition spans_cover (spans : gmap w64 (list (yjs.span.t w64))) (d : YjsId) : Prop :=
  ∃ client sps sp, spans !! client = Some sps ∧ sp ∈ sps ∧ span_covers client sp d.

(* ===== lemmas ============================================================= *)

Lemma spans_cover_insert (spans : gmap w64 (list (yjs.span.t w64)))
    (client : w64) (sp : yjs.span.t w64) (d : YjsId) :
  spans_cover (<[client := default [] (spans !! client) ++ [sp]]> spans) d <->
  spans_cover spans d ∨ span_covers client sp d.
Proof.
  split.
  - intros (client' & sps' & sp' & Hlk & Hin & Hcov).
    destruct (decide (client' = client)) as [-> | Hne].
    + rewrite lookup_insert_eq in Hlk. injection Hlk as <-.
      apply elem_of_app in Hin as [Hin | Hin].
      * left. destruct (spans !! client) as [sps |] eqn:Hsps; last by apply elem_of_nil in Hin.
        exists client, sps, sp'. split_and!; [exact Hsps | exact Hin | exact Hcov].
      * right. apply list_elem_of_singleton in Hin. subst sp'. exact Hcov.
    + rewrite lookup_insert_ne in Hlk; last done.
      left. exists client', sps', sp'. split_and!; [exact Hlk | exact Hin | exact Hcov].
  - intros [(client' & sps' & sp' & Hlk & Hin & Hcov) | Hcov].
    + destruct (decide (client' = client)) as [-> | Hne].
      * exists client, (default [] (spans !! client) ++ [sp]), sp'.
        split_and!; [rewrite lookup_insert_eq // | | exact Hcov].
        rewrite Hlk /=. apply elem_of_app. by left.
      * exists client', sps', sp'.
        split_and!; [rewrite lookup_insert_ne // | exact Hin | exact Hcov].
    + exists client, (default [] (spans !! client) ++ [sp]), sp.
      split_and!; [rewrite lookup_insert_eq // | | exact Hcov].
      apply elem_of_app. right. apply list_elem_of_singleton. reflexivity.
Qed.

(** One run's contribution to the state-vector map: the Go raises the
    client's entry to the run's end when that is larger; the model joins the
    run's state vector. *)
Lemma state_vector_denotes_run (svm : gmap w64 w64) (sv : gmap ClientId nat)
    (client end_ : w64) (r : ItemRun) :
  run_wf (run_items r) ->
  uint.nat client = run_client r ->
  uint.nat end_ = (run_clock r + length (run_items r))%nat ->
  state_vector_denotes svm sv ->
  state_vector_denotes
    (if decide (uint.Z (default (W64 0) (svm !! client)) < uint.Z end_)%Z
     then <[client := end_]> svm else svm)
    (sv_join sv (snapshot_state_vector (run_models r))).
Proof.
  move=> Hwf Hclient Hend Hden cl.
  rewrite sv_get_join (snapshot_state_vector_run_models r _ Hwf).
  have Hcl := Hden cl.
  destruct (decide (cl = client)) as [-> | Hne].
  - case_decide as Hlt.
    + have Hlt' : (uint.nat (default (W64 0) (svm !! client)) < uint.nat end_)%nat by word.
      rewrite lookup_insert_eq /= decide_True; last exact Hclient. lia.
    + have Hge : (uint.nat end_ <= uint.nat (default (W64 0) (svm !! client)))%nat by word.
      rewrite decide_True; last exact Hclient. lia.
  - have Hne' : uint.nat cl ≠ run_client r.
    { move=> Heq. apply Hne. rewrite -Hclient in Heq. word. }
    case_decide as Hlt.
    + rewrite lookup_insert_ne; last done. rewrite decide_False; last exact Hne'. lia.
    + rewrite decide_False; last exact Hne'. lia.
Qed.

End text_observer_value.
