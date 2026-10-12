import test from 'node:test';
import assert from 'node:assert/strict';
import {parseArticle,articleBlocks,resolveBindings,renderArticle} from '../reader/article.mjs';

const manuscript=String.raw`\title{A classical calculation}
\author{A mathematician}
\begin{document}
\maketitle
\section{Real numbers}\label{sec:reals}
For $x\in\mathbb R$, put
\begin{equation}\label{eq:alpha}\alpha(x)=x^2.\end{equation}
\begin{theorem}[Nonnegativity]\label{thm:positive}
Every $x\in\mathbb R$ satisfies $\alpha(x)\ge0$.
\end{theorem}
\begin{proof}
Since $x^2\ge0$, the assertion follows from \eqref{eq:alpha}.
\end{proof}
\begin{remark}\label{rem:zero} Equality holds at zero.\end{remark}
\end{document}`;

test('retains exact source spans, original result order and references',()=>{
  const article=parseArticle(manuscript);
  for(const b of articleBlocks(article))assert.equal(manuscript.slice(b.start,b.end),b.latex);
  assert.equal(article.references['thm:positive'].number,'1.1');
  assert.equal(article.references['rem:zero'].number,'1.2');
  const html=renderArticle(article);
  assert.match(html,/Nonnegativity/);
  assert.match(html,/Equality holds at zero/);
  assert.match(html,/data-result-kind="remark"/);
  assert.match(html,/href="#article-eq-alpha">\(1\)/);
  assert.doesNotMatch(html,/Open verification|checked mathematical/i);
});

test('bindings must identify exactly one original source passage',()=>{
  const article=parseArticle(manuscript);
  const bindings=[{label:'thm:positive',declarations:['Example.square_nonneg']}];
  assert.equal(Object.values(resolveBindings(article,bindings))[0][0].declaration,'Example.square_nonneg');
  assert.throws(()=>resolveBindings(article,[{label:'missing',declarations:[]}]),/exactly once/);
  assert.throws(()=>resolveBindings(article,[{quote:'x',kind:'paragraph',declarations:[]}]),/exactly once/);
});

test('duplicate labels and anchor collisions cannot hide a passage',()=>{
  assert.throws(()=>parseArticle(manuscript.replace('rem:zero','thm:positive')),/Duplicate/);
  assert.throws(()=>parseArticle(manuscript.replace('rem:zero','thm-positive')),/Colliding/);
});

test('notation links resolve only to definitions actually present in the article',()=>{
  const article=parseArticle(manuscript);
  assert.match(renderArticle(article,{definitions:{'\\alpha':{label:'eq:alpha'}}}),/href="#article-eq-alpha"/);
  assert.throws(()=>renderArticle(article,{definitions:{'\\alpha':{label:'missing'}}}),/Unknown definition/);
  assert.throws(()=>renderArticle(parseArticle(manuscript.replace('x^2.',String.raw`\href{https://example.com}{x}.`))),/presentation links/);
});

test('unsupported content, missing references, and missing evidence fail visibly',()=>{
  assert.throws(()=>parseArticle(manuscript.replace('begin{remark}','begin{unknown}').replace('end{remark}','end{unknown}')),/Unsupported/);
  assert.throws(()=>renderArticle(parseArticle(manuscript.replace('eqref{eq:alpha}','eqref{missing}'))),/Unknown reference/);
  const article=parseArticle(manuscript),annotations=resolveBindings(article,[{label:'thm:positive',declarations:['Missing.proof']}]);
  assert.throws(()=>renderArticle(article,{annotations}),/Missing compiled evidence/);
});
