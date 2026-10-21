// A Yjs-shaped JavaScript API over the Go CRDT of this repository, compiled
// to WebAssembly (main.go). The names follow Yjs v13, the API applications
// are written against today:
//
//   import * as Y from './cert-yjs.mjs'
//   await Y.init()
//   const doc = new Y.Doc()
//   const text = doc.getText('note')
//   text.observe(event => console.log(event.delta))
//   doc.on('update', update => Y.applyUpdate(otherDoc, update))
//   text.insert(0, 'hello')
//
// What is here: Doc (getText, transact, on / off 'update'), Text (insert,
// delete, toString, length, observe, unobserve), applyUpdate,
// encodeStateAsUpdate. What is not: every other shared type, state vectors
// and differential updates, undo, relative positions.
//
// Text is UTF-16 code units on both sides: a JavaScript string is one, and
// so is the Go document (yjs/content.go), so indices, lengths and deltas
// mean the same as in Yjs and nothing is re-encoded on the way. Lone
// surrogates, the halves of a pair an edit separates included, are not
// supported (issue #233): replicas can read different text around them.
//
// Differences from Yjs a caller can observe:
//   - an 'update' event carries the WHOLE document state, not the
//     transaction's own changes (the Go has no differential encoder yet).
//     Applying it is still correct, updates being idempotent;
//   - observers and 'update' handlers run right after the transaction, when
//     the document is unlocked, not inside it. They may read and write the
//     document; what they write is a transaction of its own;
//   - applyUpdate, the first getText of a name and the first observe of a
//     text throw inside transact.

let binding = null;

// init loads the wasm module. source is the URL (browser) or the path or URL
// (Node) of cert-yjs.wasm, by default the file next to this module. wasm_exec.js
// is Go's own loader, copied next to this module by build.sh.
export async function init (source = new URL('./cert-yjs.wasm', import.meta.url)) {
  if (binding !== null) {
    return;
  }
  await import('./wasm_exec.js');
  const go = new globalThis.Go();
  let result;
  if (typeof process !== 'undefined' && process.versions?.node) {
    const { readFile } = await import('node:fs/promises');
    result = await WebAssembly.instantiate(await readFile(source), go.importObject);
  } else {
    result = await WebAssembly.instantiateStreaming(fetch(source), go.importObject);
  }
  // Never resolves: the Go program serves calls until the page goes away. It
  // has installed its global by the time run returns its promise.
  go.run(result.instance);
  binding = globalThis.__certYjs;
  if (binding === undefined) {
    binding = null;
    throw new Error('cert-yjs: the wasm module did not start');
  }
}

// The binding takes and returns text as a Uint8Array holding the string's
// code units (charCodeAt), two little-endian bytes each; these two write and
// read that layout, without touching the units themselves.
const encodeCodeUnits = (string) => {
  const bytes = new Uint8Array(2 * string.length);
  const view = new DataView(bytes.buffer);
  for (let i = 0; i < string.length; i++) {
    view.setUint16(2 * i, string.charCodeAt(i), true);
  }
  return bytes;
};

const decodeCodeUnits = (bytes) => {
  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  const count = bytes.byteLength / 2;
  let string = '';
  // fromCharCode is applied to bounded chunks: a very long argument list
  // overflows the call stack.
  for (let start = 0; start < count; start += 4096) {
    const units = [];
    for (let i = start; i < Math.min(start + 4096, count); i++) {
      units.push(view.getUint16(2 * i, true));
    }
    string += String.fromCharCode(...units);
  }
  return string;
};

// deltaEntry turns one entry of a binding delta into Yjs's shape, the
// inserted code units decoded into a string.
const deltaEntry = (entry) =>
  entry.insert !== undefined ? { insert: decodeCodeUnits(entry.insert) } : entry;

const isIndex = (value) => Number.isInteger(value) && value >= 0;

const equalBytes = (left, right) =>
  left.length === right.length && left.every((byte, index) => byte === right[index]);

export class Doc {
  constructor ({ clientID = crypto.getRandomValues(new Uint32Array(1))[0] } = {}) {
    if (binding === null) {
      throw new Error('cert-yjs: await init() before creating a Doc');
    }
    this.clientID = clientID;
    this._binding = binding.newDocument(clientID);
    this._texts = new Map();
    this._updateHandlers = new Set();
    // The state the last 'update' event carried, to tell whether a
    // transaction changed anything.
    this._lastState = null;
    this._inTransaction = false;
    this._settling = false;
    // Observer deliveries queued by the Go callbacks, which run under the
    // document lock and so cannot call the handlers themselves.
    this._deliveries = [];
  }

  getText (name = '') {
    let text = this._texts.get(name);
    if (text === undefined) {
      // Creating a root type takes the document lock on the Go side.
      if (this._inTransaction) {
        throw new Error(`cert-yjs: the first getText('${name}') cannot be inside transact`);
      }
      text = new Text(this, this._binding.getText(name));
      this._texts.set(name, text);
    }
    return text;
  }

  // transact runs body as one transaction: its observers are called once,
  // after it. A transact inside body joins the transaction already open.
  transact (body, origin = null) {
    return this._run(origin, () => {
      let result;
      let failure = null;
      // An exception must not cross into Go (main.go transact).
      this._binding.transact(() => {
        try {
          result = body();
        } catch (error) {
          failure = { error };
        }
      });
      if (failure !== null) {
        throw failure.error;
      }
      return result;
    });
  }

  on (eventName, handler) {
    if (eventName !== 'update') {
      throw new Error(`cert-yjs: no '${eventName}' event, only 'update'`);
    }
    if (this._lastState === null) {
      this._lastState = this._binding.encodeStateAsUpdate();
    }
    this._updateHandlers.add(handler);
  }

  off (eventName, handler) {
    if (eventName === 'update') {
      this._updateHandlers.delete(handler);
    }
  }

  // _run runs operation, which locks the document on the Go side, then
  // delivers what it caused. Inside a transaction the operation joins it.
  _run (origin, operation) {
    if (this._inTransaction) {
      return operation();
    }
    this._inTransaction = true;
    try {
      return operation();
    } finally {
      this._inTransaction = false;
      this._settle(origin);
    }
  }

  // _settle calls the observers of the transactions that just ended, then
  // the 'update' handlers if the document changed. A handler that writes the
  // document re-enters here; the loop of the outer call delivers for it.
  _settle (origin) {
    if (this._settling) {
      return;
    }
    this._settling = true;
    try {
      do {
        while (this._deliveries.length > 0) {
          const { text, delta } = this._deliveries.shift();
          const transaction = { origin, doc: this };
          for (const handler of [...text._handlers]) {
            handler({ target: text, delta, transaction }, transaction);
          }
        }
        if (this._updateHandlers.size > 0) {
          const state = this._binding.encodeStateAsUpdate();
          if (!equalBytes(state, this._lastState)) {
            this._lastState = state;
            for (const handler of [...this._updateHandlers]) {
              handler(state, origin, this);
            }
          }
        }
      } while (this._deliveries.length > 0);
    } finally {
      this._settling = false;
    }
  }
}

export class Text {
  constructor (doc, textBinding) {
    this.doc = doc;
    this._binding = textBinding;
    this._handlers = new Set();
    this._observing = false;
  }

  get length () {
    return this._binding.length();
  }

  toString () {
    return decodeCodeUnits(this._binding.toString());
  }

  insert (index, content) {
    if (!isIndex(index) || index > this.length) {
      throw new RangeError(`cert-yjs: insert index ${index} out of range`);
    }
    if (typeof content !== 'string') {
      throw new TypeError('cert-yjs: content must be a string');
    }
    this.doc._run(null, () => this._binding.insert(index, encodeCodeUnits(content)));
  }

  delete (index, length) {
    if (!isIndex(index) || !isIndex(length)) {
      throw new RangeError(`cert-yjs: delete range ${index}, ${length} out of range`);
    }
    this.doc._run(null, () => this._binding.delete(index, length));
  }

  // observe registers handler, called after every transaction that changed
  // this text with event.delta, an array of {retain}, {insert} and {delete}
  // entries that patches the text before the transaction into the text
  // after it.
  observe (handler) {
    if (!this._observing) {
      if (this.doc._inTransaction) {
        throw new Error('cert-yjs: the first observe of a text cannot be inside transact');
      }
      this._binding.observe((delta) => {
        this.doc._deliveries.push({ text: this, delta: delta.map(deltaEntry) });
      });
      this._observing = true;
    }
    this._handlers.add(handler);
  }

  unobserve (handler) {
    this._handlers.delete(handler);
  }
}

// applyUpdate integrates a Yjs v1 update into doc, as one transaction.
export function applyUpdate (doc, update, origin = null) {
  if (doc._inTransaction) {
    throw new Error('cert-yjs: applyUpdate cannot be called inside transact');
  }
  const decoded = doc._run(origin, () => doc._binding.applyUpdate(update));
  if (!decoded) {
    throw new Error('cert-yjs: malformed update');
  }
}

// encodeStateAsUpdate returns the whole document state as a Yjs v1 update.
export function encodeStateAsUpdate (doc) {
  return doc._binding.encodeStateAsUpdate();
}
