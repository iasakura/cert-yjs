(** Facade for the [yType] proofs, in dependency order: the pure model ([model]:
    the document sequence and its validity theory), the value layer ([value]:
    [cells_model]), the Iris layer ([heap]: [own_ytype] / [own_ytype_cells]) and
    the method proofs ([newYType], [findPos], [Text]). Downstream files Require
    only this. *)
From New.proof.ytype Require Export model value heap newYType findPos Text.
