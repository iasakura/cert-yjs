(** The [item] type, VALUE layer: the heap node as the proofs see it, and what
    it denotes. Go values but no Iris.

    Definitions
    - [loc_at ls k]: the node address at cursor [k] of an address list
      ([null] outside the list), how a spec reads [ss_locs].
    - the flag accessors [is_deleted_flag] / [is_countable_flag] reading the
      heap struct's bits, and [set_deleted] setting the tombstone.
    - [toContent] and [originId_of], the remaining scalar readings.

    Laws
    - [loc_at_splice_ge]: a splice at [idx] leaves the addresses before [idx]
      where they were.
    - the heap flags pin the tombstone bit exactly ([flags_if_deleted],
      [flags_if_countable]).

    The Iris layer over the nodes is [item/heap.v]. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core prelude.
From New.proof.item Require Import run_theory model.
From New.proof.id Require Import value heap.

Section item_value.

Set Default Proof Using "Type*".

Notation A := go_string.

(* ===== definitions ======================================================== *)

(** [loc_at ls k]: the address at cursor [k] of an address list ([null]
    outside [0, len)), how a spec reads a node address off the
    [ss_locs] half of the store state. *)
Definition loc_at (ls : list loc) (k : Z) : loc :=
  if decide (0 <= k)%Z then default null (ls !! Z.to_nat k) else null.

(* ----- per-node accessors read by yType.findPos -------------------------- *)

(** The Deleted bit (y-octo ITEM_DELETED = 0x04) of a heap item's [flags], read
    exactly as [item.Deleted] computes it ([flags & 0x04 ≠ 0]). This boolean is
    the heap source of truth for visibility (a tombstoned node has it set). *)
Definition is_deleted_flag (v : yjs.item.t) : bool :=
  negb (bool_decide (w8_word_instance.(word.and) v.(yjs.item.flags') (W8 4) = W8 0)).

(** The Countable bit (ITEM_COUNTABLE = 0x02), read as [item.Countable] does.
    Every string item NewItem builds is countable, so this is [true] of every
    integrated node; it is what [item.Indexable] gates visibility on. *)
Definition is_countable_flag (v : yjs.item.t) : bool :=
  negb (bool_decide (w8_word_instance.(word.and) v.(yjs.item.flags') (W8 2) = W8 0)).

(** The heap effect of [item.flags |= itemDeleted]: set the Deleted bit. *)
Definition set_deleted (v : yjs.item.t) : yjs.item.t :=
  v <| yjs.item.flags' := w8_word_instance.(word.or) v.(yjs.item.flags') (W8 4) |>.

Definition toContent (c : yjs.content.t) : A := c.(yjs.content.content').

(* ----- item-pointer helpers --------------------------------------------- *)

(** A heap item pointer is null or owns a node; [originId_of] is its model id. *)
Definition originId_of (ov : option yjs.item.t) : option YjsId :=
  (λ v, toYjsId v.(yjs.item.id')) <$> ov.

Lemma loc_at_splice_ge (ls : list loc) (l : loc) (idx : nat) (k : Z) :
  (Z.of_nat idx <= k)%Z -> (idx <= length ls)%nat ->
  loc_at (take idx ls ++ l :: drop idx ls) (k + 1) = loc_at ls k.
Proof.
  move=> Hk Hle. rewrite /loc_at.
  rewrite decide_True; last lia. rewrite decide_True; last lia.
  rewrite lookup_app_r; last (rewrite length_take_le; [lia | exact Hle]).
  rewrite length_take_le; last exact Hle.
  have -> : (Z.to_nat (k + 1) - idx)%nat = S (Z.to_nat k - idx)%nat by lia.
  simpl. rewrite lookup_drop.
  have -> : (idx + (Z.to_nat k - idx))%nat = Z.to_nat k by lia.
  done.
Qed.

(** Read the tombstone bit back off the [own_item_node] flag pin
    ([flags'] = [if d then W8 6 else W8 2]): the struct is always Countable, and
    its Deleted bit is exactly [d]. Used by [findPos] / [Delete] after opening a
    node, to learn its visibility from the run's [run_deleted]. *)
Lemma flags_if_deleted (v : yjs.item.t) (d : bool) :
  v.(yjs.item.flags') = (if d then W8 6 else W8 2) -> is_deleted_flag v = d.
Proof. rewrite /is_deleted_flag => ->. by destruct d. Qed.

Lemma flags_if_countable (v : yjs.item.t) (d : bool) :
  v.(yjs.item.flags') = (if d then W8 6 else W8 2) -> is_countable_flag v = true.
Proof. rewrite /is_countable_flag => ->. by destruct d. Qed.

(* ----- the deletion layer: tombstoning a cell ---------------------------- *)

(* ===== lemmas ============================================================= *)

End item_value.
