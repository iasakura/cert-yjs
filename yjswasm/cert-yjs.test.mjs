// Tests of the JavaScript facade over the wasm module, and of the wire format
// against the real Yjs (the yjs devDependency). Run with `npm test` after
// `./build.sh` and `npm install`.

import { test } from 'node:test'
import assert from 'node:assert/strict'
import * as Yjs from 'yjs'
import * as CertYjs from './cert-yjs.mjs'

await CertYjs.init()

// applyDelta patches string with a Yjs text delta.
const applyDelta = (string, delta) => {
  let result = ''
  let index = 0
  for (const operation of delta) {
    if (operation.retain !== undefined) {
      result += string.slice(index, index + operation.retain)
      index += operation.retain
    } else if (operation.insert !== undefined) {
      result += operation.insert
    } else {
      index += operation.delete
    }
  }
  return result + string.slice(index)
}

test('insert, delete, toString, length', () => {
  const text = new CertYjs.Doc({ clientID: 1 }).getText('note')
  text.insert(0, 'hello world')
  text.delete(5, 6)
  text.insert(5, '!')
  assert.equal(text.toString(), 'hello!')
  assert.equal(text.length, 6)
})

test('getText returns the same text for the same name', () => {
  const doc = new CertYjs.Doc({ clientID: 1 })
  assert.equal(doc.getText('note'), doc.getText('note'))
  assert.notEqual(doc.getText('note'), doc.getText('other'))
})

test('insert rejects non-string content and out-of-range indices', () => {
  const text = new CertYjs.Doc({ clientID: 1 }).getText('note')
  assert.throws(() => text.insert(0, 42), TypeError)
  assert.throws(() => text.insert(1, 'a'), RangeError)
  assert.throws(() => text.insert(-1, 'a'), RangeError)
  assert.equal(text.toString(), '')
})

// Text is UTF-16 code units, as in Yjs: indices and lengths count them, and
// a character outside the Basic Multilingual Plane is two of them.
test('non-ASCII text round-trips and is counted in UTF-16 code units', () => {
  const text = new CertYjs.Doc({ clientID: 1 }).getText('note')
  text.insert(0, 'こんにちは')
  assert.equal(text.toString(), 'こんにちは')
  assert.equal(text.length, 5)
  text.insert(5, ' 😀!')
  assert.equal(text.toString(), 'こんにちは 😀!')
  assert.equal(text.length, 9)
  // deleting one code unit of the pair leaves its other half in place
  text.delete(6, 1)
  assert.equal(text.length, 8)
  assert.equal(text.toString().charCodeAt(6), 0xDE00)
  text.delete(6, 1)
  assert.equal(text.toString(), 'こんにちは !')
})

test('deltas carry non-ASCII inserts, surrogate pairs included', () => {
  const doc = new CertYjs.Doc({ clientID: 1 })
  const text = doc.getText('note')
  const deltas = []
  text.observe((event) => deltas.push(event.delta))
  text.insert(0, 'é😀')
  text.insert(1, 'ü')
  assert.deepEqual(deltas, [[{ insert: 'é😀' }], [{ retain: 1 }, { insert: 'ü' }]])
  assert.equal(text.toString(), 'éü😀')
  assert.equal(applyDelta(applyDelta('', deltas[0]), deltas[1]), 'éü😀')
})

test('non-ASCII concurrent edits converge between two Cert-Yjs replicas', () => {
  const left = new CertYjs.Doc({ clientID: 1 })
  const right = new CertYjs.Doc({ clientID: 2 })
  left.getText('note').insert(0, '日本語の文章 ')
  CertYjs.applyUpdate(right, CertYjs.encodeStateAsUpdate(left))
  left.getText('note').insert(7, '😀')
  right.getText('note').insert(7, 'ñ')
  right.getText('note').delete(0, 1)
  const fromLeft = CertYjs.encodeStateAsUpdate(left)
  const fromRight = CertYjs.encodeStateAsUpdate(right)
  CertYjs.applyUpdate(left, fromRight)
  CertYjs.applyUpdate(right, fromLeft)
  const merged = left.getText('note').toString()
  assert.equal(right.getText('note').toString(), merged)
  assert.ok(merged.includes('😀') && merged.includes('ñ'))
  assert.equal(merged.length, '本語の文章 '.length + 3)
})

test('observe gets one delta per transaction, none at registration', () => {
  const doc = new CertYjs.Doc({ clientID: 1 })
  const text = doc.getText('note')
  text.insert(0, 'abc')
  const deltas = []
  text.observe((event) => deltas.push(event.delta))
  assert.deepEqual(deltas, [])
  doc.transact(() => {
    text.insert(3, 'def')
    text.delete(0, 1)
    assert.equal(text.toString(), 'bcdef')
    assert.equal(text.length, 5)
  })
  assert.deepEqual(deltas, [[{ delete: 1 }, { retain: 2 }, { insert: 'def' }]])
})

test('an observer may read and write the document', () => {
  const doc = new CertYjs.Doc({ clientID: 1 })
  const text = doc.getText('note')
  const seen = []
  text.observe(() => {
    seen.push(text.toString())
    if (text.length === 1) {
      text.insert(1, 'b')
    }
  })
  text.insert(0, 'a')
  assert.deepEqual(seen, ['a', 'ab'])
})

test('unobserve stops the deliveries', () => {
  const text = new CertYjs.Doc({ clientID: 1 }).getText('note')
  let calls = 0
  const handler = () => calls++
  text.observe(handler)
  text.insert(0, 'a')
  text.unobserve(handler)
  text.insert(1, 'b')
  assert.equal(calls, 1)
})

test('an exception in transact reaches the caller and leaves the document usable', () => {
  const doc = new CertYjs.Doc({ clientID: 1 })
  const text = doc.getText('note')
  assert.throws(() => doc.transact(() => {
    text.insert(0, 'a')
    throw new Error('stop')
  }), /stop/)
  text.insert(1, 'b')
  assert.equal(text.toString(), 'ab')
})

test('observe, applyUpdate and a new getText throw inside transact', () => {
  const doc = new CertYjs.Doc({ clientID: 1 })
  const text = doc.getText('note')
  assert.throws(() => doc.transact(() => doc.getText('other')), /inside transact/)
  doc.transact(() => assert.equal(doc.getText('note'), text))
  assert.throws(() => doc.transact(() => text.observe(() => {})), /inside transact/)
  assert.throws(() => doc.transact(() => CertYjs.applyUpdate(doc, new Uint8Array([0, 0]))), /inside transact/)
  text.insert(0, 'a')
  assert.equal(text.toString(), 'a')
})

test('a malformed update throws', () => {
  const doc = new CertYjs.Doc({ clientID: 1 })
  assert.throws(() => CertYjs.applyUpdate(doc, new Uint8Array([5, 1])), /malformed/)
})

test("'update' events carry the origin and stop once the replicas agree", () => {
  const left = new CertYjs.Doc({ clientID: 1 })
  const right = new CertYjs.Doc({ clientID: 2 })
  const origins = []
  // No origin filter: each replica forwards everything it is told. The
  // exchange ends because an update that changes nothing raises no event.
  left.on('update', (update, origin) => {
    origins.push(origin)
    CertYjs.applyUpdate(right, update, 'from left')
  })
  right.on('update', (update) => CertYjs.applyUpdate(left, update, 'from right'))
  const leftText = left.getText('note')
  left.transact(() => leftText.insert(0, 'abc'), 'typing')
  right.getText('note').insert(3, 'def')
  assert.equal(left.getText('note').toString(), 'abcdef')
  assert.equal(right.getText('note').toString(), 'abcdef')
  assert.deepEqual(origins, ['typing', 'from right'])
})

test('concurrent edits converge, and the deltas patch each view', () => {
  const left = new CertYjs.Doc({ clientID: 1 })
  const right = new CertYjs.Doc({ clientID: 2 })
  const views = new Map([[left, ''], [right, '']])
  for (const doc of [left, right]) {
    doc.getText('note').observe((event) => views.set(doc, applyDelta(views.get(doc), event.delta)))
  }
  left.getText('note').insert(0, 'shared ')
  CertYjs.applyUpdate(right, CertYjs.encodeStateAsUpdate(left))

  // offline: both edit the same places
  left.getText('note').insert(7, 'left')
  left.getText('note').delete(0, 2)
  right.getText('note').insert(7, 'right')
  right.getText('note').insert(0, '> ')

  const fromLeft = CertYjs.encodeStateAsUpdate(left)
  const fromRight = CertYjs.encodeStateAsUpdate(right)
  CertYjs.applyUpdate(left, fromRight)
  CertYjs.applyUpdate(right, fromLeft)

  const merged = left.getText('note').toString()
  assert.equal(right.getText('note').toString(), merged)
  assert.equal(views.get(left), merged)
  assert.equal(views.get(right), merged)
  assert.ok(merged.includes('left') && merged.includes('right'))
})

// The wire format against the real Yjs, both directions.

test('Yjs reads a Cert-Yjs update', () => {
  const ours = new CertYjs.Doc({ clientID: 1 })
  ours.getText('note').insert(0, 'hello world')
  ours.getText('note').delete(5, 6)
  const theirs = new Yjs.Doc()
  Yjs.applyUpdate(theirs, CertYjs.encodeStateAsUpdate(ours))
  assert.equal(theirs.getText('note').toString(), 'hello')
})

test('Cert-Yjs reads a Yjs update of inserts', () => {
  const theirs = new Yjs.Doc()
  theirs.getText('note').insert(0, 'hello')
  theirs.getText('note').insert(5, ' world')
  theirs.getText('note').insert(5, ',')
  const ours = new CertYjs.Doc({ clientID: 1 })
  CertYjs.applyUpdate(ours, Yjs.encodeStateAsUpdate(theirs))
  assert.equal(ours.getText('note').toString(), 'hello, world')
})

test('Cert-Yjs reads a Yjs update with deletes (gc off)', () => {
  const theirs = new Yjs.Doc({ gc: false })
  theirs.getText('note').insert(0, 'hello world')
  theirs.getText('note').delete(5, 6)
  const ours = new CertYjs.Doc({ clientID: 1 })
  CertYjs.applyUpdate(ours, Yjs.encodeStateAsUpdate(theirs))
  assert.equal(ours.getText('note').toString(), 'hello')
})

// Known gap: with gc on, Yjs replaces the content of a deleted item by
// ContentDeleted (content tag 1), and the Go codec reads every content as a
// String (yjs/codec.go readStruct), so the update comes back as malformed.
test('Cert-Yjs reads a Yjs update with deletes (gc on, the Yjs default)', { todo: 'ContentDeleted is not decoded' }, () => {
  const theirs = new Yjs.Doc()
  theirs.getText('note').insert(0, 'hello world')
  theirs.getText('note').delete(5, 6)
  const ours = new CertYjs.Doc({ clientID: 1 })
  CertYjs.applyUpdate(ours, Yjs.encodeStateAsUpdate(theirs))
  assert.equal(ours.getText('note').toString(), 'hello')
})

test('Yjs reads a Cert-Yjs update with non-ASCII text and a surrogate pair', () => {
  const ours = new CertYjs.Doc({ clientID: 1 })
  ours.getText('note').insert(0, 'héllo 😀 wörld')
  ours.getText('note').delete(6, 2)
  const theirs = new Yjs.Doc()
  Yjs.applyUpdate(theirs, CertYjs.encodeStateAsUpdate(ours))
  assert.equal(theirs.getText('note').toString(), 'héllo  wörld')
  assert.equal(theirs.getText('note').length, ours.getText('note').length)
})

test('Cert-Yjs reads a Yjs update with non-ASCII text and a surrogate pair', () => {
  const theirs = new Yjs.Doc()
  theirs.getText('note').insert(0, 'héllo')
  theirs.getText('note').insert(5, ' 😀 wörld')
  theirs.getText('note').insert(6, '→')
  const ours = new CertYjs.Doc({ clientID: 1 })
  CertYjs.applyUpdate(ours, Yjs.encodeStateAsUpdate(theirs))
  assert.equal(ours.getText('note').toString(), 'héllo →😀 wörld')
  assert.equal(ours.getText('note').length, theirs.getText('note').length)
})

test('Cert-Yjs and Yjs converge on concurrent edits', () => {
  const ours = new CertYjs.Doc({ clientID: 1 })
  const theirs = new Yjs.Doc({ gc: false })
  theirs.clientID = 2
  ours.getText('note').insert(0, 'shared ')
  Yjs.applyUpdate(theirs, CertYjs.encodeStateAsUpdate(ours))

  ours.getText('note').insert(7, 'ours')
  ours.getText('note').insert(0, '> ')
  theirs.getText('note').insert(7, 'theirs')
  theirs.getText('note').delete(0, 2)

  const fromOurs = CertYjs.encodeStateAsUpdate(ours)
  const fromTheirs = Yjs.encodeStateAsUpdate(theirs)
  CertYjs.applyUpdate(ours, fromTheirs)
  Yjs.applyUpdate(theirs, fromOurs)

  assert.equal(ours.getText('note').toString(), theirs.getText('note').toString())
})
