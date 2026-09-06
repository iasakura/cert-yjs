(** Facade for the [yType] proofs, in dependency order: the pure model ([model]:
    the document sequence and its validity theory, [runs_model]), the value
    layer ([value]: [visible_items] / [visible_string] / [find_pos]), the
    Iris layer ([heap]: [own_ytype]) and the method proofs ([newYType],
    [findPos], [Text]). Downstream files Require only this. *)
From New.proof.ytype Require Export model value heap newYType findPos Text.
