package yjs

// Wire-level entry point of the sync protocol over the verified subset
// (issue #107, W3b): applying one encoded update as received from the
// network.
//
// The byte codec stays outside the verified core (codec.go, //go:build
// !goose), so verified code takes it as a VALUE: a Codec is the decoding
// half, handed in by the deployment (WireCodec, codec.go). The server's
// proofs assume only its specification (codec_spec, src/proof/yjs_prot.v),
// stated against the abstract decode function the wire protocol [yjs_prot]
// is defined over; the real codec is trusted to meet it, the same trust
// boundary codec.go already is.

// Codec is the decoding half of the update codec: data decodes to a batch
// of insert structs, ok reports whether it decoded at all. The struct type
// is unexported, so a Codec can only be built inside this package; the
// deployment's is WireCodec (codec.go).
type Codec = func(data []byte) (bool, []updateItem)

// ApplyEncodedUpdate decodes one wire update with decode and applies the
// batch to the document with the verified total apply path
// (ApplySyncUpdate, under the store's write lock). It reports whether the
// update decoded; an applied update is one the caller may relay
// (y-websocket relays exactly what it applied).
func (d *Doc) ApplyEncodedUpdate(decode Codec, data []byte) bool {
	ok, structs := decode(data)
	if !ok {
		return false
	}
	d.ApplySyncUpdate(structs)
	return true
}
