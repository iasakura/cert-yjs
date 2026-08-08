(** [wp_NewDoc]: creating a document creates its store AND its lock layer.
    This is the living witness that [is_Store] is satisfiable: the physical
    RWMutex is initialized ([init_RWMutex]), the store's ghost names are
    allocated for real by [store_tie_init] (write-lock witness, reader count,
    discarded reader bound, types agreement, content authorities, client
    pin), and the tie invariant is allocated at [RLocked 0]. The caller
    supplies the client's (empty) history element, which the lock body owns
    from then on; back come the persistent [is_Doc] handle and the client
    pin. *)
From New.proof Require Import proof_prelude.
From New.code.github_com.iasakura.cert_yjs Require Import yjs.
From New.generatedproof.github_com.iasakura.cert_yjs Require Import yjs.
From New.proof Require Import core.
From New.proof Require Import prelude.
From New.proof Require Import history.
From New.proof.id Require Import id.
From New.proof.item Require Import item.
From New.proof.ytype Require Import ytype.
From New.proof.store Require Import store.
From New.proof.sync_proof Require Import base mutex rwmutex.
From iris.algebra Require Import auth gmap gset.
From iris.algebra.lib Require Import dfrac_agree.
From New.proof.doc Require Import model heap.

Section doc_NewDoc.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Context {sem : go.Semantics} {package_sem : yjs.Assumptions}.

Context {sync_pkg : sync.Assumptions}.

Set Default Proof Using "Type*".

Notation A := go_string.

Notation P := go_string.

Local Notation TId := (TypeId P).

Local Notation Ev := (@Event (TId * @YjsOperation A)).

Context {seq_inG : inG Σ (authR (gmapUR loc (gsetUR (YjsItem A))))}.

Context {acc_inG : inG Σ (authR (gsetUR YjsId))}.

Context {ftypes_inG : inG Σ (dfrac_agreeR (leibnizO (gmap loc type_state)))}.

Lemma wp_NewDoc (γh : history_names) (client : w64) :
  {{{ is_pkg_init yjs ∗
      own_client_history γh (uint.nat client) ([] : list Ev) }}}
    @! yjs.NewDoc #client
  {{{ (dv s_loc : loc) (γs : store_names), RET #dv;
      is_Doc dv s_loc γs γh ∗ is_store_client γs (uint.nat client) }}}.
Proof.
  wp_start as "Hhist".
  wp_auto.
  wp_func_call.
  wp_call.
  wp_auto.
  wp_apply wp_map_make1. iIntros (items_mref) "Hitemsmap".
  wp_auto.
  wp_apply wp_map_make1. iIntros (types_mref) "Htypesmap".
  wp_auto.
  wp_apply wp_map_make1. iIntros (ds_mref) "Hdsmap".
  wp_auto.
  wp_alloc s_loc as "Hs".
  wp_auto.
  wp_alloc dv as "Hd".
  iPersist "Hd".
  iApply wp_fupd.
  wp_auto.
  (* the physical lock: the mu field starts at the RWMutex zero value *)
  iStructNamed "Hs". simpl.
  iMod (init_RWMutex (storeN .@ "rw") with "mu") as (γrw) "(#Hrw & Hst & Hrtoks)".
  iClear "Hrtoks".
  (* the ghost layer, at the real lock names *)
  iMod (store_tie_init s_loc γh client (W64 0) items_mref types_mref _ γrw
          with "client clock items [Hitemsmap] types [Htypesmap] deletedSet
                pending Hhist") as (γs) "(%Hγrw & #Hmax & Htie & #Hpin)".
  { iFrame "Hitemsmap". }
  { iFrame "Htypesmap". }
  (* the tie invariant, at RLocked 0 *)
  iMod (inv_alloc (storeN .@ "tie") _
          (∃ st, rwmutex.own_RWMutex γs.(sn_rw) st ∗ tie_body s_loc γs γh st)
          with "[Hst Htie]") as "#Htieinv".
  { iNext. iExists (RLocked 0). rewrite Hγrw. iFrame "Hst Htie". }
  iModIntro.
  iApply ("HΦ" $! dv s_loc γs).
  iFrame "Hpin".
  iExists _. iFrame "Hd".
  iSplitR; first done.
  rewrite /is_Store Hγrw. iFrame "Hrw Hmax Htieinv".
Qed.

End doc_NewDoc.
