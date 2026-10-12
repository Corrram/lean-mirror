import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import {math, sourceHTML, validateDocument, render, formulaProse, proofHTML} from '../reader/render.mjs';

const doc = JSON.parse(await fs.readFile(new URL('../examples/analysis/document.mirror.json',import.meta.url),'utf8'));
const source = JSON.parse(await fs.readFile(new URL('../examples/analysis/source.json',import.meta.url),'utf8'));
const excerpts={};
for(const p of source.passages) excerpts[p.id]=await fs.readFile(new URL('../examples/analysis/'+p.file,import.meta.url),'utf8');

test('validates the document and rejects duplicate identifiers and missing certificates',()=>{
  validateDocument(doc);
  const duplicate=structuredClone(doc);duplicate.results[0].id=duplicate.definitions[0].id;
  assert.throws(()=>validateDocument(duplicate),/Duplicate/);
  const uncertified=structuredClone(doc);delete uncertified.results[0].certificate;
  assert.throws(()=>validateDocument(uncertified),/verification/);
});
test('rejects an unsupported proof node',()=>{
  const changed=structuredClone(doc);changed.results[0].checked.proof.kind='prose';
  assert.throws(()=>validateDocument(changed),/proof node/);
});
test('math rejects broken TeX and unknown or external definition links',()=>{
  assert.throws(()=>math('\\frac{1}'),/parse error/);
  assert.throws(()=>math('\\href{https://example.com}{x}'),/Unknown/);
  assert.throws(()=>math('\\href{#def-missing}{x}'),/Unknown/);
  assert.match(math('\\href{#def-sequence}{x}',false,['sequence']),/href="#def-sequence"/);
});
test('source comparison preserves nested math in footnotes and original proof text',()=>{
  const html=sourceHTML(excerpts.sequence,math);
  assert.match(html,/It is common to use/);
  assert.match(html,/for brevity/);
  assert.match(html,/bounded below/);
  assert.match(sourceHTML(excerpts.unique,math),/As /);
  assert.throws(()=>sourceHTML('\\unknown{silent omission}',math),/Unsupported/);
  assert.throws(()=>sourceHTML('\\footnote{unfinished',math),/Unbalanced/);
});
test('offline reader retains both calculations and verification boundaries',async()=>{
  const out=await fs.mkdtemp(path.join(os.tmpdir(),'lean-mirror-reader-'));
  try {
    await render(doc,source,excerpts,out,{toolchain:'test',executable:'Analysis.lean',example:'examples/analysis'});
    const html=await fs.readFile(path.join(out,'index.html'),'utf8');
    assert.match(html,/4 checked steps/);
    assert.equal((html.match(/aria-label="End of proof"/g)||[]).length,2);
    assert.match(html,/3 checked steps/);
    assert.equal((html.match(/Proof checked by Lean/g)||[]).length,2);
    assert.match(html,/not independently a Lean proof certificate/);
    assert.match(html,/for brevity/);
    assert.match(html,/generated-statement/);
    assert.doesNotMatch(html,/[Ââ]/);
    assert.doesNotMatch(html,/<(?:script|link)[^>]+(?:src|href)="https?:/);
    await fs.access(path.join(out,'assets/fonts/KaTeX_Main-Regular.woff2'));
  } finally {await fs.rm(out,{recursive:true,force:true});}
});

test('embeddable reader preserves conjunctions and resolves only declared source references',()=>{
  const f={kind:'and',left:{kind:'formula',latex:'P'},right:{kind:'formula',latex:'Q'}};
  assert.equal(formulaProse(f,x=>x),'P; and Q');
  assert.match(proofHTML({kind:'finish',claim:'P \\land Q',formula:f},x=>x),/Hence P; and Q/);
  const tex=String.raw`\begin{corollary}[A result] See Theorem~\ref{previous} and \eqref{identity}. \end{corollary}`;
  assert.match(sourceHTML(tex,math,{previous:'1.1',identity:'4'}),/A result.*Theorem 1.1 and \(4\)/);
  assert.throws(()=>sourceHTML(tex,math),/Unknown source reference/);
});
