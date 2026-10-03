(** The [Transaction] facade: the only name downstream files Require. One Go
    file ([yjs/transaction.go]), layered: the pure model ([model]: the start
    relation), the Iris layer ([heap]: the record, [own_transaction]), the
    unexported steps ([wp_private]: the record steps, [integrate],
    [deleteNode]) and one file per method proof ([deleteRange],
    [applyUpdate], [notify], [transact]). *)
From New.proof.transaction Require Export model heap wp_private deleteRange applyUpdate notify transact.
