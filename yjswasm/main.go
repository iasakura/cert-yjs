//go:build js && wasm

// Command yjswasm exposes the yjs package to JavaScript: compiled with
// GOOS=js GOARCH=wasm, it installs one global, __certYjs, whose newDocument
// builds a document binding. The Yjs-shaped API (Doc, Text, applyUpdate,
// encodeStateAsUpdate) is the JavaScript facade cert-yjs.mjs, which is the
// only intended caller of this file.
//
// Nothing here is verified: this is glue between the JavaScript values and
// the Go API, outside goose (the js && wasm constraint excludes it from the
// translation, as it does from the ordinary go build).
//
// The lock discipline of the yjs package is the facade's job, because a
// second lock on the document from the single wasm thread is a fatal Go
// deadlock, not an error: getText, observe and applyUpdate are not called
// inside transact, and the observer callback passed to observe only queues its
// delta (it runs under the store's write lock).
package main

import (
	"encoding/binary"
	"syscall/js"

	"github.com/iasakura/cert-yjs/yjs"
)

// Text crosses the boundary as UTF-16 code units, which is what both sides
// hold: a JavaScript string is a sequence of code units and the yjs package
// counts and stores them (yjs/content.go), so nothing is re-encoded here. The
// facade (cert-yjs.mjs) hands a string over as a Uint8Array holding its
// charCodeAt values, two little-endian bytes each, and reads one back with
// fromCharCode; these two helpers only read and write that byte layout.

// codeUnitsFromJS copies the code units in array (two little-endian bytes
// each) into a fresh slice of the Go side's own.
func codeUnitsFromJS(array js.Value) []uint16 {
	bytes := make([]byte, array.Length())
	js.CopyBytesToGo(bytes, array)
	units := make([]uint16, len(bytes)/2)
	for i := range units {
		units[i] = binary.LittleEndian.Uint16(bytes[2*i:])
	}
	return units
}

// codeUnitsToJS returns a fresh Uint8Array holding units, two little-endian
// bytes each.
func codeUnitsToJS(units []uint16) js.Value {
	bytes := make([]byte, 2*len(units))
	for i, unit := range units {
		binary.LittleEndian.PutUint16(bytes[2*i:], unit)
	}
	array := js.Global().Get("Uint8Array").New(len(bytes))
	js.CopyBytesToJS(array, bytes)
	return array
}

// documentBinding is one document with the transaction the JavaScript side
// has open on it, nil outside transact. Go has no goroutine identity and the
// yjs package cannot recognise a nested lock (yjs.Doc.Transact), so the
// binding routes every call made inside transact to the In-variant.
type documentBinding struct {
	document    *yjs.Doc
	transaction *yjs.Transaction
}

// newDocument(client) returns the binding object of a fresh document owned
// by client. The functions it holds are never released: a binding lives as
// long as the page.
func newDocument(this js.Value, arguments []js.Value) any {
	binding := &documentBinding{document: yjs.NewDoc(uint64(arguments[0].Float()))}
	return map[string]any{
		"getText":             js.FuncOf(binding.getText),
		"transact":            js.FuncOf(binding.transact),
		"encodeStateAsUpdate": js.FuncOf(binding.encodeStateAsUpdate),
		"applyUpdate":         js.FuncOf(binding.applyUpdate),
	}
}

// transact(body) runs the JavaScript function body as one transaction. body
// must not throw (a JavaScript exception crossing into Go is a panic that
// ends the wasm instance); the facade catches and rethrows on its side.
func (binding *documentBinding) transact(this js.Value, arguments []js.Value) any {
	body := arguments[0]
	binding.document.Transact(func(transaction *yjs.Transaction) {
		binding.transaction = transaction
		body.Invoke()
		binding.transaction = nil
	})
	return nil
}

// encodeStateAsUpdate() returns the whole document state as a Yjs v1 update
// in a fresh Uint8Array.
func (binding *documentBinding) encodeStateAsUpdate(this js.Value, arguments []js.Value) any {
	update := binding.document.EncodeUpdate()
	array := js.Global().Get("Uint8Array").New(len(update))
	js.CopyBytesToJS(array, update)
	return array
}

// applyUpdate(update) decodes the Uint8Array update and applies it, and
// reports whether it decoded. It opens a transaction of its own, so it is
// not callable inside transact.
func (binding *documentBinding) applyUpdate(this js.Value, arguments []js.Value) any {
	update := make([]byte, arguments[0].Length())
	js.CopyBytesToGo(update, arguments[0])
	return binding.document.ApplyEncodedUpdate(yjs.WireCodec(), update)
}

// getText(name) returns the binding object of the root text named name.
// Creating the root type locks the document, so it is not callable inside
// transact.
func (binding *documentBinding) getText(this js.Value, arguments []js.Value) any {
	text := binding.document.GetOrCreateText(arguments[0].String())
	return map[string]any{
		// insert(index, units) inserts the code units units (a Uint8Array,
		// see codeUnitsFromJS) at the visible index, counted in code units.
		"insert": js.FuncOf(func(this js.Value, arguments []js.Value) any {
			index := uint64(arguments[0].Float())
			content := codeUnitsFromJS(arguments[1])
			if binding.transaction != nil {
				text.InsertIn(binding.transaction, index, content)
			} else {
				text.Insert(index, content)
			}
			return nil
		}),
		"delete": js.FuncOf(func(this js.Value, arguments []js.Value) any {
			index := uint64(arguments[0].Float())
			length := uint64(arguments[1].Float())
			if binding.transaction != nil {
				text.DeleteIn(binding.transaction, index, length)
			} else {
				text.Delete(index, length)
			}
			return nil
		}),
		// toString() returns the visible text as code units (a Uint8Array,
		// see codeUnitsToJS); the facade makes the string.
		"toString": js.FuncOf(func(this js.Value, arguments []js.Value) any {
			if binding.transaction != nil {
				return codeUnitsToJS(text.CodeUnitsIn(binding.transaction))
			}
			return codeUnitsToJS(text.CodeUnits())
		}),
		// length() is the visible length in code units, as Yjs's
		// ytext.length. The yjs package has no length read for inside a
		// transaction, so there it is the length of the visible text.
		"length": js.FuncOf(func(this js.Value, arguments []js.Value) any {
			if binding.transaction != nil {
				return len(text.CodeUnitsIn(binding.transaction))
			}
			return float64(text.Len())
		}),
		// observe(callback) registers callback for the delta of every
		// transaction that changes the text. yjs.Text.Observe also calls it
		// once at registration with the whole text; Yjs's observe does not
		// (Yjs v14.0.0-rc.18 YType.observe, src/ytype.js:779, only adds the
		// handler), so that first call is dropped here.
		"observe": js.FuncOf(func(this js.Value, arguments []js.Value) any {
			callback := arguments[0]
			registered := false
			text.Observe(func(delta []yjs.DeltaOp) {
				if !registered {
					return
				}
				callback.Invoke(deltaValue(delta))
			})
			registered = true
			return nil
		}),
	}
}

// deltaValue renders a delta in the shape of Yjs's event.delta: an array of
// {retain: n}, {insert: units} and {delete: n} objects, the inserted text as
// code units (a Uint8Array, see codeUnitsToJS) that the facade turns into
// the string.
func deltaValue(delta []yjs.DeltaOp) []any {
	entries := make([]any, 0, len(delta))
	for _, operation := range delta {
		switch operation.Kind {
		case yjs.DeltaRetain:
			entries = append(entries, map[string]any{"retain": float64(operation.Length)})
		case yjs.DeltaInsert:
			entries = append(entries, map[string]any{"insert": codeUnitsToJS(operation.Content)})
		case yjs.DeltaDelete:
			entries = append(entries, map[string]any{"delete": float64(operation.Length)})
		}
	}
	return entries
}

func main() {
	js.Global().Set("__certYjs", map[string]any{
		"newDocument": js.FuncOf(newDocument),
	})
	// Keep the instance alive: the exported functions are served for as long
	// as the page holds them.
	select {}
}
