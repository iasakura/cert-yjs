(** Facade for the report proofs, in dependency order: the value layer
    ([value]: [encode_report] / [decode_report] and their roundtrip,
    [report_ids] / [report_text] / [reports_converge]), the Iris layer
    ([heap]: [own_report], the encoder's result; [is_report], the trace
    protocol) and the encoder's WP ([EncodeReport]). Downstream files
    Require only this. *)
From New.proof.report Require Export value heap EncodeReport.
