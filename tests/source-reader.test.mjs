import test from 'node:test';
import assert from 'node:assert/strict';
import {validateSourceDocument,sourceHTML} from '../reader/source.mjs';

const definition=()=>({schemaVersion:1,id:'positive',title:'Positive',kind:'definition',key:'positive',
  source:String.raw`For every \(x\in\mathbb{R}\), \(\positive(x)\iff 0<x\).`,proofSource:'',
  syntax:{kind:'all'},certificate:'Example.definition',target:'forall x, P x <-> 0 < x',axioms:[],
  modelIdentity:'Example.model',languageIdentity:'Example.language',
  dependencies:['real'],terms:[{spelling:'\\positive',key:'positive'}],domains:[{phrase:'positive real number',key:'positive'}]});
const theorem=()=>({...definition(),id:'result',kind:'theorem',key:'',certificate:'Example.theorem',dependencies:['positive'],
  source:String.raw`If \(x\) is a positive real number, then \(\positive(x)\).`});
const doc=()=>({schemaVersion:1,entries:[definition(),theorem()]});

test('complete precise definitions resolve and source prose is retained',()=>{
  assert.equal(validateSourceDocument(doc()).entries.length,2);
  const e=theorem(),html=sourceHTML(e.source,e);
  assert.match(html,/If /);assert.match(html,/then /);assert.match(html,/href="#def-positive"/);
  assert.match(html,/positive real number/);
});
test('missing, duplicate, circular and forged primitive definition cards fail',()=>{
  assert.throws(()=>validateSourceDocument({schemaVersion:1,entries:[theorem()]}),/Missing checked definition/);
  const duplicate=doc();duplicate.entries.push({...definition(),id:'second'});
  assert.throws(()=>validateSourceDocument(duplicate),/Duplicate/);
  const cyclic=doc();cyclic.entries[0].dependencies=['positive'];
  assert.throws(()=>validateSourceDocument(cyclic),/Cyclic/);
  const primitive=doc();primitive.entries[0].key='real';
  assert.throws(()=>validateSourceDocument(primitive),/reserved|invalid definition/);
  const collision=doc();collision.entries[1].id='def-positive';
  assert.throws(()=>validateSourceDocument(collision),/definition anchor/);
  const reserved=doc();reserved.entries[1].id='about';
  assert.throws(()=>validateSourceDocument(reserved),/reserved/);
});
test('proof claims, extra axioms and unsupported rendering cannot silently pass',()=>{
  const proof=doc();proof.entries[1].kind='proof';
  assert.throws(()=>validateSourceDocument(proof),/Proof source/);
  const axiom=doc();axiom.entries[1].axioms=['sorryAx'];
  assert.throws(()=>validateSourceDocument(axiom),/Nonstandard/);
  const model=doc();model.entries[1].modelIdentity='Different.model';
  assert.throws(()=>validateSourceDocument(model),/share their compiled model/);
  assert.throws(()=>sourceHTML('\\unknown{ignore this}',theorem()),/Unsupported TeX/);
});
test('all math delimiters render and source text is HTML escaped',()=>{
  const e=theorem();
  const html=sourceHTML(String.raw`A < B. \(1=1\) \[2=2\] $3=3$`,e);
  assert.match(html,/A &lt; B/);assert.match(html,/katex-display/);
  assert.equal((html.match(/class="katex"/g)??[]).length,3);
});
