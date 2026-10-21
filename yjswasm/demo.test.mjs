// Tests of the demo page's logic (demo.mjs) on a Yjs replica and a Cert-Yjs
// replica wired as index.html wires them, with stand-ins for the textareas.
// Run with `npm test` after `./build.sh` and `npm install`.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import * as Yjs from 'yjs';
import * as CertYjs from './cert-yjs.mjs';
import { bindTextarea, connect } from './demo.mjs';

await CertYjs.init();

// A stand-in for a textarea, with what bindTextarea uses of one.
class TextareaStandIn {
  constructor () {
    this.value = '';
    this.selectionStart = 0;
    this.selectionEnd = 0;
    this.listeners = [];
  }

  addEventListener (type, listener) {
    this.listeners.push({ type, listener });
  }

  setSelectionRange (start, end) {
    this.selectionStart = start;
    this.selectionEnd = end;
  }

  // type sets the content as a user's edit does, the caret at caret, and
  // fires the input event.
  type (value, caret = value.length) {
    this.value = value;
    this.setSelectionRange(caret, caret);
    for (const { type, listener } of this.listeners) {
      if (type === 'input') {
        listener({ isComposing: false });
      }
    }
  }
}

// page builds the two replicas of index.html, connected and bound.
const page = () => {
  const replicas = [
    { library: Yjs, doc: new Yjs.Doc({ gc: false }) },
    { library: CertYjs, doc: new CertYjs.Doc() }
  ];
  for (const replica of replicas) {
    replica.text = replica.doc.getText('note');
    replica.textarea = new TextareaStandIn();
    replica.deltaLog = { textContent: '' };
  }
  const network = connect(replicas, () => {});
  for (const replica of replicas) {
    bindTextarea(replica.textarea, replica.text, replica.deltaLog);
  }
  const [yjs, certYjs] = replicas;
  return { yjs, certYjs, network };
};

// agree asserts that both texts and both textareas read expected.
const agree = ({ yjs, certYjs }, expected) => {
  assert.equal(yjs.text.toString(), expected);
  assert.equal(certYjs.text.toString(), expected);
  assert.equal(yjs.textarea.value, expected);
  assert.equal(certYjs.textarea.value, expected);
};

test('an edit on either side shows on the other while connected', () => {
  const demo = page();
  demo.yjs.textarea.type('hello');
  agree(demo, 'hello');
  demo.certYjs.textarea.type('hello world');
  agree(demo, 'hello world');
  demo.yjs.textarea.type('héllo 😀 world', 7);
  agree(demo, 'héllo 😀 world');
});

test('deletions travel both ways', () => {
  const demo = page();
  demo.yjs.textarea.type('hello wide world');
  demo.certYjs.textarea.type('hello world', 6);
  agree(demo, 'hello world');
  demo.yjs.textarea.type('hello', 5);
  agree(demo, 'hello');
});

test('edits made offline on both sides merge when the network is back', () => {
  const demo = page();
  demo.yjs.textarea.type('one two three');
  demo.network.setOnline(false);
  demo.yjs.textarea.type('zero one two three', 5);
  demo.certYjs.textarea.type('one three four');
  assert.equal(demo.yjs.text.toString(), 'zero one two three');
  assert.equal(demo.certYjs.text.toString(), 'one three four');
  demo.network.setOnline(true);
  agree(demo, 'zero one three four');
});

test('concurrent inserts at one position merge the same way on both sides', () => {
  const demo = page();
  demo.yjs.textarea.type('ab');
  demo.network.setOnline(false);
  demo.yjs.textarea.type('aXb', 2);
  demo.certYjs.textarea.type('aYb', 2);
  demo.network.setOnline(true);
  assert.equal(demo.yjs.text.toString(), demo.certYjs.text.toString());
  assert.ok(['aXYb', 'aYXb'].includes(demo.yjs.text.toString()));
  agree(demo, demo.yjs.text.toString());
});

test('the caret moves through a received edit', () => {
  const demo = page();
  demo.yjs.textarea.type('abcdef');
  demo.certYjs.textarea.setSelectionRange(3, 3);
  demo.yjs.textarea.type('XYabcdef', 2);
  assert.equal(demo.certYjs.textarea.value, 'XYabcdef');
  assert.equal(demo.certYjs.textarea.selectionStart, 5);
  assert.match(demo.certYjs.deltaLog.textContent, /^last received delta: /);
});
