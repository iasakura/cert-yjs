// The moving parts of the demo page (index.html), kept apart from it so that
// the tests can drive them without a browser. A replica is
// { library, doc, text }: library is a module with Yjs's API, either Yjs
// itself or the Cert-Yjs facade (cert-yjs.mjs), doc one of its documents and
// text a shared text of doc. Nothing here depends on which library it is.

// The origin the network applies updates with, so that a replica tells an
// update it received from an edit of its own and does not send it back.
export const NETWORK = 'network'

// positionAfter moves a caret position in the old text through delta.
export const positionAfter = (delta, position) => {
  let index = 0
  let shift = 0
  for (const operation of delta) {
    if (index >= position) {
      break
    }
    if (operation.retain !== undefined) {
      index += operation.retain
    } else if (operation.insert !== undefined) {
      shift += operation.insert.length
    } else {
      shift -= Math.min(operation.delete, position - index)
      index += operation.delete
    }
  }
  return position + shift
}

// bindTextarea keeps textarea and text equal: an edit of the textarea becomes
// one delete and one insert in a transaction, and a change of the text (local
// or received) is written back with the caret moved through its delta. Each
// delta is shown in deltaLog.
export const bindTextarea = (textarea, text, deltaLog) => {
  textarea.value = text.toString()

  const pushEdit = () => {
    const before = text.toString()
    const after = textarea.value
    let prefix = 0
    while (prefix < before.length && prefix < after.length && before[prefix] === after[prefix]) {
      prefix++
    }
    let suffix = 0
    while (suffix < before.length - prefix && suffix < after.length - prefix &&
           before[before.length - 1 - suffix] === after[after.length - 1 - suffix]) {
      suffix++
    }
    text.doc.transact(() => {
      text.delete(prefix, before.length - prefix - suffix)
      text.insert(prefix, after.slice(prefix, after.length - suffix))
    }, textarea)
    if (textarea.value !== after) {
      const caret = textarea.selectionStart
      textarea.value = after
      textarea.setSelectionRange(caret, caret)
    }
  }
  textarea.addEventListener('input', (event) => {
    // An input method's composition is pushed once, when it ends.
    if (!event.isComposing) {
      pushEdit()
    }
  })
  textarea.addEventListener('compositionend', pushEdit)

  text.observe((event) => {
    const origin = event.transaction.origin === NETWORK ? 'received' : 'local'
    deltaLog.textContent = `last ${origin} delta: ${JSON.stringify(event.delta)}`
    const next = text.toString()
    if (textarea.value !== next) {
      const start = positionAfter(event.delta, textarea.selectionStart)
      const end = positionAfter(event.delta, textarea.selectionEnd)
      textarea.value = next
      textarea.setSelectionRange(start, end)
    }
  })
}

// connect links two replicas by a simulated network and calls onChange after
// every update either of them has. While the network is up, each update of a
// replica's own is applied to the other at once: Yjs sends the changes of the
// transaction, the Cert-Yjs facade its whole state. While it is down nothing
// is sent, and when it comes back each replica sends its whole state to the
// other, as a Yjs provider resynchronizes after a reconnection.
export const connect = (replicas, onChange) => {
  let online = true
  const peerOf = (replica) => replicas.find((other) => other !== replica)
  for (const replica of replicas) {
    replica.doc.on('update', (update, origin) => {
      if (online && origin !== NETWORK) {
        const peer = peerOf(replica)
        peer.library.applyUpdate(peer.doc, update, NETWORK)
      }
      onChange()
    })
  }
  return {
    get online () {
      return online
    },
    setOnline (value) {
      online = value
      if (online) {
        for (const replica of replicas) {
          const peer = peerOf(replica)
          peer.library.applyUpdate(peer.doc, replica.library.encodeStateAsUpdate(replica.doc), NETWORK)
        }
      }
      onChange()
    }
  }
}
