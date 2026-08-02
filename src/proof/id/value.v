(** The [id] type, VALUE layer: what a heap [Id] means in the model. No Iris.

    Definitions
    - [toYjsId]: a heap [Id] (two [w64]s) as a model [YjsId] (two [nat]s).

    Laws
    - [toYjsId] is injective, and [Id.Equal]'s field-wise boolean is exactly
      [bool_decide] of model id equality ([toYjsId_inj], [Id_eqb_toYjsId]).
      This is the bridge between the Go id operations and the pure [gset] tests.
    - [Id.Sub] undoes [Id.Add] at the machine-word level
      ([id_add_sub_roundtrip]). *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core.
From New.proof Require Import prelude.

Section id_value.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Set Default Proof Using "Type*".

(* ===== definitions ======================================================== *)

(** Heap id (two [w64]s) to model id (two [nat]s). *)
Definition toYjsId (i : yjs.id.t) : YjsId :=
  MkYjsId (uint.nat i.(yjs.id.clientId')) (uint.nat i.(yjs.id.clock')).

(* ===== lemmas ============================================================= *)

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

(* ----- Id / set helper specs (model-id equality bridge) ------------------ *)

(** [toYjsId] is injective (it is [uint.nat] on both [w64] fields), so heap id
    equality matches model id equality — the bridge between the Go id ops and
    the pure [gset] tests. *)
Lemma toYjsId_inj (a b : yjs.id.t) : toYjsId a = toYjsId b -> a = b.
Proof.
  destruct a as [ca ka], b as [cb kb]. rewrite /toYjsId /=.
  injection 1 as Hc Hk. f_equal; word.
Qed.

(** [Id.Equal] computes the conjunction of the two field equalities; this is
    exactly [bool_decide] of the model id equality. *)
Lemma Id_eqb_toYjsId (a b : yjs.id.t) :
  (bool_decide (a.(yjs.id.clientId') = b.(yjs.id.clientId'))
   && bool_decide (a.(yjs.id.clock') = b.(yjs.id.clock')))%bool
  = bool_decide (toYjsId a = toYjsId b).
Proof.
  rewrite -bool_decide_and. apply bool_decide_ext. rewrite /toYjsId. split.
  - move=> [Hc Hk]. by rewrite Hc Hk.
  - move=> H. injection H => Hk Hc. split; word.
Qed.

End id_value.
