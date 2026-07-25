(** [yjs_text] facade: re-exports the Text handle proofs, split across
    [yjs_text_base] (is_Text + helpers), [yjs_text_insert] (Insert), and
    [yjs_text_delete] (Delete + Len) so the two heavy WP proofs check in
    parallel. Downstream files Require only [yjs_text]. *)
From New.proof Require Export yjs_text_base yjs_text_insert yjs_text_delete.
