(** The [TextObserver] facade: the only name downstream files Require. The
    delta it returns is [delta/delta], re-exported here. *)
From New.proof.delta Require Export delta.
From New.proof.textobserver Require Export model value heap wp_private NewObserver Poll.
