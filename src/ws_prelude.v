(** Code-level prelude for the ws FFI, imported by every goose-translated
    package that uses it (goose emits [From New Require Import ws_prelude.] for
    packages mapped to the "ws" ffi; see goose/interface.go).

    Staging note: this file belongs in the perennial fork at
    [new/ws_prelude.v], whose logical path is [New.ws_prelude] -- the same as
    here, since cert-yjs maps [src] to [New]. Only the [impl] require below
    changes on the move. Modeled on perennial's [new/grove_prelude.v]. *)
From New.goose_lang.ffi.ws_ffi Require Import impl.
#[global]
Existing Instances ws_op ws_model.
