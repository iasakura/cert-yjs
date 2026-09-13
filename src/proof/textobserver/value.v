(** The [TextObserver], VALUE layer: what the Go values of the observer
    denote. Go values, no Iris.

    Definitions
    - [delta_op_denotes v op]: the [DeltaOp] struct value [v] is the entry
      [op] (its kind byte, its length or its content).
    - [state_vector_denotes m sv]: the [map[Client]Clock] contents [m] are
      the state vector [sv] (per client word, the next clock).
    - [span_covers client sp d] / [spans_cover spans d]: a [span[uint64]] of
      [client] covers the id [d]; some span of the per-client span lists
      does. What the observer's deleted-spans map means.

    Laws: none; [heap.v]'s predicates state the observer's fields over
    these directly. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core network_model.
From New.proof.textobserver Require Import model.

Section text_observer_value.

Set Default Proof Using "Type*".

Notation A := go_string.

(* ===== definitions ======================================================== *)

(** The kind bytes of the Go [DeltaKind]: retain 0, insert 1, delete 2. *)
Definition delta_op_denotes (v : yjs.DeltaOp.t) (op : DeltaOp) : Prop :=
  match op with
  | Retain n => v.(yjs.DeltaOp.Kind') = W8 0 ∧ uint.nat v.(yjs.DeltaOp.Length') = n
  | Insert t => v.(yjs.DeltaOp.Kind') = W8 1 ∧ v.(yjs.DeltaOp.Content') = t
  | Delete n => v.(yjs.DeltaOp.Kind') = W8 2 ∧ uint.nat v.(yjs.DeltaOp.Length') = n
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

End text_observer_value.
