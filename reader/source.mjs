import fs from 'node:fs/promises';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import katex from 'katex';

const escape = s => String(s).replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const safeID = s => typeof s === 'string' && /^[a-z][a-z0-9-]*$/.test(s);
const foundations = new Set(['real', 'unit-interval']);
const allowedAxioms = new Set(['propext', 'Classical.choice', 'Quot.sound']);

export function validateSourceDocument(doc) {
  if (doc.schemaVersion !== 1 || !Array.isArray(doc.entries) || !doc.entries.length) throw new Error('Invalid source document');
  const ids = new Set(), anchors = new Set(['definitions','def-real','def-unit-interval','about']), definitions = new Map();
  for (const e of doc.entries) {
    if (!e.modelIdentity || !e.languageIdentity || e.modelIdentity !== doc.entries[0].modelIdentity || e.languageIdentity !== doc.entries[0].languageIdentity) throw new Error('Definitions and results must share their compiled model and language');
    if (!safeID(e.id) || ids.has(e.id)) throw new Error('Duplicate or unsafe source identifier');
    ids.add(e.id);
    const anchor = e.kind === 'definition' ? 'def-' + e.key : e.id;
    if (anchors.has(anchor)) throw new Error('Duplicate or reserved definition anchor');
    anchors.add(anchor);
    if (!['definition','theorem','proof'].includes(e.kind) || !e.source || !e.syntax || !e.certificate || !e.target) throw new Error('Missing compiled source evidence');
    if (!Array.isArray(e.axioms) || e.axioms.some(a => !allowedAxioms.has(a))) throw new Error('Nonstandard source axiom');
    if (!Array.isArray(e.dependencies) || !Array.isArray(e.terms) || !Array.isArray(e.domains)) throw new Error('Missing compiled vocabulary');
    if ((e.kind === 'proof') !== !!e.proofSource) throw new Error('Proof source does not match its certificate kind');
    if (e.kind === 'definition') {
      if (!safeID(e.key) || foundations.has(e.key) || definitions.has(e.key)) throw new Error('Duplicate or invalid definition');
      definitions.set(e.key, e);
    }
  }
  const done = new Set(foundations), active = new Set();
  function visit(key) {
    if (done.has(key)) return;
    if (active.has(key)) throw new Error(`Cyclic source definition: ${key}`);
    const definition = definitions.get(key);
    if (!definition) throw new Error(`Missing checked definition: ${key}`);
    active.add(key);
    definition.dependencies.forEach(visit);
    active.delete(key); done.add(key);
  }
  doc.entries.forEach(e => e.dependencies.forEach(visit));
  return doc;
}

function math(tex, entry, display) {
  const keys = new Set([...entry.dependencies, entry.key, ...foundations]);
  // Fixed built-in notation. No author-supplied rendering callbacks or macros.
  // Custom control words display their literal name when KaTeX has no meaning
  // for them; the clickable defining equation supplies their mathematics.
  const terms = new Map(entry.terms.map(t => [t.spelling, t.key]));
  let linked = tex.replace(/\\[A-Za-z]+/g, spelling => {
    const key = terms.get(spelling);
    if (!key || !keys.has(key)) return spelling;
    let display = spelling;
    try { katex.renderToString(spelling, {throwOnError:true}); }
    catch { display = `\\operatorname{${spelling.slice(1)}}`; }
    return `\\href{#def-${key}}{${display}}`;
  });
  return katex.renderToString(linked, {displayMode:display, throwOnError:true, strict:'error',
    macros:{'\\abs':'\\left|#1\\right|', '\\real':'#1'},
    trust:ctx => ctx.command === '\\href' && [...keys].some(k => ctx.url === `#def-${k}`)});
}

function prose(text, entry) {
  if (/\\/.test(text)) throw new Error('Unsupported TeX outside a mathematical delimiter');
  const phrases = [...entry.domains, {phrase:'real number',key:'real'}, {phrase:'unit interval element',key:'unit-interval'}]
    .sort((a,b) => b.phrase.length-a.phrase.length);
  // Match on the source, then escape each text span. Never replace inside HTML.
  let out='', i=0;
  while (i < text.length) {
    const d = phrases.find(d => text.startsWith(d.phrase,i) && (i===0 || !/[A-Za-z]/.test(text[i-1])) && !/[A-Za-z]/.test(text[i+d.phrase.length]??''));
    if (d) { out += `<a class="definition-term" href="#def-${escape(d.key)}">${escape(d.phrase)}</a>`; i += d.phrase.length; }
    else { out += escape(text[i]); i++; }
  }
  return out;
}

/** Render the certified source, preserving its prose and formulas. No unrelated
    theorem title or custom expression renderer can replace the checked body. */
export function sourceHTML(source, entry) {
  source = source.replace(/(?<!\\)%[^\n]*/g, '');
  const re = /\\\(([\s\S]*?)\\\)|\\\[([\s\S]*?)\\\]|\$([^$]*)\$/g;
  let out='', at=0;
  for (const m of source.matchAll(re)) {
    out += prose(source.slice(at,m.index),entry);
    out += math(m[1]??m[2]??m[3],entry,m[2]!==undefined);
    at=m.index+m[0].length;
  }
  return '<div class="source-prose">'+out+prose(source.slice(at),entry)+'</div>';
}

export async function renderSourceDocument(doc, out) {
  validateSourceDocument(doc);
  const entries=doc.entries.map((e,i)=>`<section class="entry" id="${e.kind==='definition'?'def-'+e.key:e.id}">
    <div class="entry-heading"><span>${e.kind==='definition'?'Definition':'Theorem'} ${i+1}</span><span class="status">${e.kind==='proof'?'Source, theorem and proof steps checked':'Source and correspondence checked'}</span></div>
    <h2>${escape(e.title)}</h2>${sourceHTML(e.source,e)}
    ${e.proofSource?'<div class="proof"><h3>Proof</h3>'+sourceHTML(e.proofSource,e)+'</div>':''}
    <div class="definition-links">Definitions: ${e.dependencies.map(k=>`<a href="#def-${escape(k)}">${escape(k)}</a>`).join(' · ')||'built-in operations'}</div>
    <details><summary>Inspect the source and Lean certificate</summary><pre>${escape(e.source)}</pre>
      <p>Certificate: <code>${escape(e.certificate)}</code></p><p>Corresponding Lean statement:</p><pre>${escape(e.target)}</pre>
      <p>The certificate checks compilation of this source and its equivalence to the Lean statement.${e.proofSource?' It also checks every step of the displayed proof.':''}</p>
      <a href="source/${escape(e.sourceFile)}" download>Download this LaTeX source</a></details></section>`).join('');
  const html=`<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
    <title>${escape(doc.title)} · LeanMirror</title><link rel="stylesheet" href="assets/katex.min.css"><link rel="stylesheet" href="assets/source.css"></head>
    <body><header><a href="#">LeanMirror</a><nav><a href="#definitions">Definitions</a><a href="#about">How it is checked</a></nav></header>
    <main><div class="intro"><p class="eyebrow">Executable mathematical companion</p><h1>${escape(doc.title)}</h1>
    <p>The prose and formulas below are the source Lean checks. Follow a term to its precise definition.</p>
    <p><a href="lean-mirror-source.zip" download>Download the executable companion</a> · <a href="document.json">Compiled document</a></p></div>
    <section id="definitions" class="foundations"><h2>Foundations</h2><p id="def-real"><strong>Real numbers.</strong> ${katex.renderToString('\\mathbb{R}')} denotes Lean’s real numbers.</p>
    <p id="def-unit-interval"><strong>Unit interval.</strong> ${katex.renderToString('[0,1]=\\{x\\in\\mathbb{R}:0\\le x\\le1\\}')}.
    Interval elements are included in the reals when used in real arithmetic.</p></section>${entries}
    <section id="about"><h2>How it is checked</h2><p>The compiler parses the complete mathematical source, resolves names and scopes, and checks a Lean proof of its equivalence to the target statement. Definition entries must supply checked defining equations. Proof entries additionally justify every displayed step.</p>
    <p>The exact source string occurs in each certificate. Parsing and elaboration are total Lean functions, evaluated by the kernel when checking the compilation equation. Unknown clauses and missing definitions stop the build.</p>
    <p>This verifies the specified companion language. Human comparison with an original article and browser typesetting remain outside the mathematical proof. The allowed Lean axioms are propext, Classical.choice and Quot.sound.</p>
    <p>To reproduce this example after extracting the bundle:</p><pre>npm ci\npython scripts/source.py check examples/source</pre>
    <p><a href="verification.json">Build inputs</a>. Titles are editorial labels; the source bodies are the certified statements.</p></section></main></body></html>`;
  await fs.mkdir(path.join(out,'assets'),{recursive:true});
  await fs.writeFile(path.join(out,'index.html'),html);
  await fs.copyFile(new URL('./source.css',import.meta.url),path.join(out,'assets/source.css'));
  const dist=path.resolve(path.dirname(fileURLToPath(import.meta.url)),'../node_modules/katex/dist');
  await fs.copyFile(path.join(dist,'katex.min.css'),path.join(out,'assets/katex.min.css'));
  await fs.copyFile(path.resolve(dist,'../LICENSE'),path.join(out,'assets/KATEX-LICENSE'));
  await fs.cp(path.join(dist,'fonts'),path.join(out,'assets/fonts'),{recursive:true});
}

if (process.argv[1] && path.resolve(process.argv[1])===fileURLToPath(import.meta.url)) {
  const [input,out]=process.argv.slice(2);
  await renderSourceDocument(JSON.parse(await fs.readFile(input,'utf8')),out);
}
