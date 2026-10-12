import fs from 'node:fs/promises';
import path from 'node:path';
import katex from 'katex';
import {fileURLToPath} from 'node:url';

export const escape = s => String(s).replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const macros = {"\\N":"\\mathbb{N}","\\R":"\\mathbb{R}","\\sabs":"\\lvert #1\\rvert","\\babs":"\\bigl\\lvert #1\\bigr\\rvert","\\abs":"\\left\\lvert #1\\right\\rvert","\\nicefrac":"\\frac{#1}{#2}"};
export function math(tex, display = false, keys = []) {
  const allowed = new Set(keys.map(k => `#def-${k}`));
  for (const match of tex.matchAll(/\\href\{([^}]+)\}/g)) if (!allowed.has(match[1])) throw new Error(`Unknown definition link: ${match[1]}`);
  return katex.renderToString(tex, {displayMode: display, throwOnError: true, strict:'error', macros,
    trust: context => context.command === '\\href' && allowed.has(context.url), output:'htmlAndMathml'});
}
export function validateDocument(doc) {
  if (doc.schemaVersion !== 1 || !Array.isArray(doc.results) || !Array.isArray(doc.definitions)) throw new Error('Unsupported document schema');
  const ids = [...doc.definitions, ...doc.results].map(x => x.id);
  if (new Set(ids).size !== ids.length || ids.some(x=>!/^[-a-z0-9]+$/.test(x))) throw new Error('Duplicate or unsafe document identifier');
  const walk = (n, depth=0) => {
    if (!n || depth>200 || !['finish','have','fix','assume','choose','suffices'].includes(n.kind)) throw new Error('Invalid proof node');
    if (n.kind!=='fix' && typeof n.claim !== 'string') throw new Error('Missing mathematical claim');
    if (n.kind!=='finish') walk(n.next,depth+1);
  };
  for (const r of doc.results) {
    if (!r.certificate || !r.correspondence || !r.checked?.statement) throw new Error('Missing verification reference');
    walk(r.checked.proof);
  }
  return doc;
}
function children(n) {return n?.next ? [n,...children(n.next)] : n ? [n] : [];}
function relation(formula) {
  const prefix=[]; let f=formula;
  while(f && ['forall','imp'].includes(f.kind)) {
    prefix.push(f.kind==='forall' ? {kind:f.kind,name:f.name,binding:f.binding,type:f.type} : {kind:f.kind,premise:f.premise}); f=f.body;
  }
  return f?.kind==='relation' ? {prefix, ...f} : null;
}
// Natural descriptions are determined by formula constructors. Free prose never
// enters the proof tree. The original source is displayed in its own column.
function formulaProse(f, m) {
  if (f.kind==='forall') {
    const variable=m(`${f.binding??f.name}\\in ${f.type}`);
    return f.body.kind==='imp' ? `for every ${variable} satisfying ${m(f.body.premise.latex)}, ${formulaProse(f.body.body,m)}` : `for every ${variable}, ${formulaProse(f.body,m)}`;
  }
  if (f.kind==='exists') return `there exists ${m(`${f.binding??f.name}\\in ${f.type}`)} such that ${formulaProse(f.body,m)}`;
  if (f.kind==='imp') return `if ${m(f.premise.latex)}, then ${formulaProse(f.body,m)}`;
  return m(f.latex);
}
function chain(nodes, m) {
  const rs=nodes.map(n=>relation(n.formula));
  const prefix=rs[0].prefix;
  let lead='Estimate';
  for(const p of prefix) lead+= p.kind==='forall' ? `, for every ${m(`${p.binding??p.name}\\in ${p.type}`)}` : ` satisfying ${m(p.premise.latex)}`;
  let rows=rs[0].left+' &'+rs[0].operator+' '+rs[0].right;
  for(const r of rs.slice(1)) rows+=' \\\\ &'+r.operator+' '+r.right;
  return `<div class="calculation"><p>${lead}:</p>${m('\\begin{aligned}'+rows+'\\end{aligned}',true)}<span class="step-count">${nodes.length} checked steps</span></div>`;
}
function proofHTML(root, m) {
  let html=''; let n=root;
  while(n) {
    if(n.kind==='have' && relation(n.formula)) {
      const group=[n]; const first=relation(n.formula); let last=first;
      let next=n.next;
      while(next?.kind==='have') {
        const r=relation(next.formula);
        if(!r || JSON.stringify(r.prefix)!==JSON.stringify(first.prefix) || r.left!==last.right) break;
        group.push(next);last=r;next=next.next;
      }
      if(group.length>1){html+=chain(group,m); n=next;continue;}
    }
    const detail=n.claim?`<details class="node-detail"><summary>Exact obligation</summary>${m(n.claim,true)}</details>`:'';
    if(n.kind==='fix') html+=`<p>Let ${n.type==='\\mathbb{R}^{\\mathbb{N}}' ? m(`\\{${n.name}_n\\}_{n=1}^{\\infty}`)+' be a sequence' : m(`${n.binding??n.name}\\in ${n.type}`)}.</p>`;
    if(n.kind==='assume') html+=`<div class="proof-step"><p>Suppose ${formulaProse(n.formula,m)}.</p>${detail}</div>`;
    if(n.kind==='choose') html+=`<div class="proof-step"><p>Choose ${m(`${n.binding??n.name}\\in ${n.type}`)} such that ${formulaProse(n.formula,m)}.</p>${detail}</div>`;
    if(n.kind==='have') html+=`<div class="proof-step"><p>Then ${formulaProse(n.formula,m)}.</p>${detail}</div>`;
    if(n.kind==='suffices') {
      html+=`<div class="proof-step"><p>It suffices to show that ${formulaProse(n.formula,m)}.</p>${detail}<div class="subproof">${proofHTML(n.next,m)}</div><p>Consequently, ${m(n.goal)}.</p></div>`;
      return html;
    }
    if(n.kind==='finish') html+=`<p>Hence ${formulaProse(n.formula,m)}.</p>`;
    n=n.next;
  }
  return html;
}
// Small TeX reader for source comparison. Reject unsupported commands instead of
// quietly dropping them. It deliberately does not determine verification status.
function texArgumentCommands(text, command, transform) {
  const marker='\\'+command+'{'; let at=0, out='';
  for (;;) {
    const start=text.indexOf(marker,at);
    if(start<0) return out+text.slice(at);
    out+=text.slice(at,start); let end=start+marker.length, depth=1;
    const content=end;
    for(;end<text.length && depth;end++) {
      if(text[end]==='\\') {end++;continue;}
      if(text[end]==='{') depth++;
      if(text[end]==='}') depth--;
    }
    if(depth) throw new Error(`Unbalanced source command: ${command}`);
    out+=transform(text.slice(content,end-1)); at=end;
  }
}
export function sourceHTML(tex,m) {
  let t=tex.replace(/(?<!\\)%[^\n]*\n/g,'');
  for(const cmd of ['label','glsadd','index']) t=texArgumentCommands(t,cmd,()=> '');
  for(const cmd of ['myindex','emph']) t=texArgumentCommands(t,cmd,s=>s);
  t=texArgumentCommands(t,'footnote',s=>' (Footnote: '+s+')');
  t=t.replace(/\\qedhere/g,'')
    .replace(/\\begin\{(?:defn|prop)\}/g,'').replace(/\\end\{(?:defn|prop)\}/g,'\n\n')
    .replace(/\\begin\{proof\}/g,'\n\nProof. ').replace(/\\end\{proof\}/g,' □\n\n');
  const parts=[];const re=/\\begin\{equation\*\}([\s\S]*?)\\end\{equation\*\}|\$([^$]+)\$/g;let at=0;
  const plain=s=>{
    if(/\\[A-Za-z]/.test(s)) throw new Error(`Unsupported source prose TeX: ${s.slice(0,100)}`);
    return escape(s).replace(/\n\s*\n/g,'</p><p>').replace(/\n/g,' ');
  };
  for(const match of t.matchAll(re)) {
    parts.push(plain(t.slice(at,match.index)));
    parts.push(m((match[1]??match[2]).replace(/\\begin\{split\}/g,'\\begin{aligned}').replace(/\\end\{split\}/g,'\\end{aligned}'),!!match[1]));
    at=match.index+match[0].length;
  }
  parts.push(plain(t.slice(at)));
  return '<p>'+parts.join('')+'</p>';
}
export async function render(doc, source, excerpts, out, build) {
  validateDocument(doc);
  const keys=doc.definitions.map(x=>x.id);
  const m=(s,d=false)=>math(s,d,keys);
  const stepCount=doc.results.reduce((a,r)=>a+children(r.checked.proof).filter(n=>n.kind!=='fix').length,0);
  const sourceLink=p=>`${source.repository}/blob/${source.revision}/${source.file}#L${p.startLine}-L${p.endLine}`;
  const original=(id)=>{const p=source.passages.find(p=>p.id===id);return p?`<aside class="original"><div class="column-label">Original · ${escape(source.author)} <a href="${escape(sourceLink(p))}">lines ${p.startLine}–${p.endLine} ↗</a></div>${sourceHTML(excerpts[id],m)}</aside>`:'';};
  const defs=doc.definitions.map(d=>`<section class="definition" id="def-${d.id}"><div class="comparison"><div><h3>${escape(d.title)}</h3><p>${escape(d.text)}</p>${d.structured?`<p>${formulaProse(d.structured,m)}.</p><details><summary>Symbolic definition</summary>${m(d.formula,true)}</details>`:m(d.formula,true)}<details><summary>${d.status==='checked'?'Definition correspondence':'Mathematical convention'}</summary><p>${escape(d.bridge)}</p>${d.target?`<code>${escape(d.target)}</code>`:''}</details></div>${original(d.id)}</div></section>`).join('');
  const results=doc.results.map((r,i)=>`<section class="theorem" id="${r.id}"><div class="theorem-heading"><span class="eyebrow">Proposition ${i+1}</span><span class="checked">✓ Proof checked by Lean</span></div><h2>${escape(r.title)}</h2><div class="comparison"><div class="companion"><div class="column-label">Precise companion</div><p class="generated-statement">${formulaProse(r.checked.statement,m).replace(/^for every/,'For every')}.</p><details class="statement"><summary>Symbolic statement</summary>${m(r.checked.statement.latex,true)}</details><h4>Proof.</h4><div class="proof-flow">${proofHTML(r.checked.proof,m)}<span class="qed" aria-label="End of proof">□</span></div><details class="evidence"><summary>Lean certificate and library correspondence</summary><p>Every step in this proof tree is checked, including the existence of chosen objects.</p><code>${escape(r.certificate)}</code><p>Statement equivalence: <code>${escape(r.correspondence)}</code></p><p>Mathlib counterpart: <code>${escape(r.target)}</code></p><p><a href="${escape(build.executable)}">Inspect the executable source</a></p></details></div>${original(r.id)}</div></section>`).join('');
  const document=`<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>${escape(doc.title)} · LeanMirror</title><link rel="stylesheet" href="assets/katex.min.css"><link rel="stylesheet" href="assets/reader.css"></head><body class="comparing"><header class="topbar"><a class="brand" href="#">Lean<span>Mirror</span></a><nav><a href="#definitions">Definitions</a><a href="#${escape(doc.results[0]?.id??'definitions')}">Proofs</a><a href="#about">About this edition</a></nav></header><main><section class="intro"><p class="eyebrow">A readable, executable analysis companion</p><h1>${escape(doc.title)}</h1><p class="subtitle">${escape(doc.subtitle)}</p><p class="attribution">Adapted from ${escape(source.author)}’s <a href="${escape(source.repository)}">${escape(source.title)}</a>, ${escape(source.section)}. <a href="${escape(source.licenseUrl)}">CC BY-SA 4.0</a>.</p><div class="facts"><span><strong>${doc.results.length}</strong> complete proofs</span><span><strong>${stepCount}</strong> checked proof nodes</span></div><div class="toolbar"><label><input id="compare" type="checkbox" checked> Compare with the original</label><label><input id="detail" type="checkbox"> Show proof obligations</label><a href="companion.tex" download>LaTeX</a><a href="lean-mirror-source.zip" download>Executable bundle</a></div><p class="scope">${escape(source.scope)}</p></section><section id="definitions"><p class="eyebrow">The objects in these proofs</p><h2>Definitions and notation</h2>${defs}</section>${results}<section id="about" class="about"><h2>About this edition</h2><p>The comparison column preserves the selected source passages. The companion is generated from typed mathematical expressions and a scoped proof tree. Explanatory prose and mathematical notation remain an inspectable presentation boundary; Lean checks their formal interpretation.</p><p>This is a derivative companion, not an edition endorsed by the source author. The original book is not certified by this page.</p><h3>Precision and presentation changes</h3><ul>${source.changes.map(s=>`<li>${escape(s)}</li>`).join('')}</ul><h3>Reproduce the check</h3><p>Download and extract the executable bundle, or clone <a href="https://github.com/Corrram/lean-mirror">LeanMirror on GitHub</a>. From the project directory:</p><pre>lake exe cache get\nnpm ci\npython scripts/mirror.py check ${escape(build.example)}</pre><p>Lean ${escape(build.toolchain)}. Source revision <code>${escape(source.revision)}</code>.</p><details><summary>What the certificate guarantees</summary><p>The generic theorem <code>Argument.sound</code> derives the document’s conclusion from a proof of <code>Argument.Valid</code>. That validity condition checks every intermediate assertion, assumption scope, existential choice, and sufficient condition. Certificates reject unfinished proofs and additional axioms. The allowed axioms are propext, Classical.choice and Quot.sound.</p><p>The parser, vocabulary, typesetting and editorial alignment with the source have not themselves been formally verified. The source comparison helps readers review that boundary.</p><p>Displayed status records the local build that generated this artifact; downloaded JSON is not independently a Lean proof certificate. Run the command above to verify the executable sources.</p></details><p><a href="document.mirror.json" download>Document data</a> · <a href="verification.json" download>Build manifest</a> · <a href="source/${escape(source.file)}" download>Original source file</a> · <a href="${escape(build.executable)}" download>Executable companion</a></p></section></main><footer>LeanMirror · Mathematics you can read and check.</footer><script src="assets/reader.js"></script></body></html>`;
  await fs.mkdir(path.join(out,'assets'),{recursive:true});
  await fs.writeFile(path.join(out,'index.html'),document);
  await fs.copyFile(new URL('./reader.css',import.meta.url),path.join(out,'assets/reader.css'));
  await fs.copyFile(new URL('./reader.js',import.meta.url),path.join(out,'assets/reader.js'));
  const dist=path.resolve(path.dirname(fileURLToPath(import.meta.url)),'../node_modules/katex/dist');
  await fs.copyFile(path.join(dist,'katex.min.css'),path.join(out,'assets/katex.min.css'));
  await fs.cp(path.join(dist,'fonts'),path.join(out,'assets/fonts'),{recursive:true});
  await fs.copyFile(path.resolve(dist,'../LICENSE'),path.join(out,'assets/KATEX-LICENSE'));
  return {results:doc.results.length,proofNodes:stepCount};
}
if(process.argv[1] && path.resolve(process.argv[1])===fileURLToPath(import.meta.url)) {
  const [docFile,sourceFile,excerptsFile,out,buildFile]=process.argv.slice(2);
  const read=async f=>JSON.parse(await fs.readFile(f,'utf8'));
  console.log(JSON.stringify(await render(await read(docFile),await read(sourceFile),await read(excerptsFile),out,await read(buildFile))));
}
