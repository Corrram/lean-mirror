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
  assert.throws(()=>resolveBindings(article,[{label:'thm:positive',role:'certified-original',declarations:[]}]),/Unknown source binding role/);
});

test('a compiled counterexample is visibly distinguished from a source theorem link',()=>{
  const article=parseArticle(manuscript);
  const annotations=resolveBindings(article,[{label:'thm:positive',role:'refutation',declarations:['Example.counterexample']}]);
  const html=renderArticle(article,{annotations,evidence:{'Example.counterexample':{declaration:'Example.counterexample',type:'¬ PrintedClaim'}}});
  assert.match(html,/class="article-evidence article-refutation"/);assert.match(html,/Printed claim refuted · Open checked correction/);
});

test('a readable checked proof precedes folded native theorem types',()=>{
  const article=parseArticle(manuscript);
  const annotations=resolveBindings(article,[{label:'thm:positive',declarations:['Example.proof']}]);
  const html=renderArticle(article,{annotations,evidence:{'Example.proof':{declaration:'Example.proof',type:'NativeProposition'}},proofDetails:()=>'<p>Readable checked proof</p>'});
  assert(html.indexOf('Readable checked proof')<html.indexOf('NativeProposition'));
  assert.match(html,/class="article-native-types"/);
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

const document=body=>String.raw`\title{Source fidelity}\begin{document}`+body+String.raw`\end{document}`;

test('comments and inline environments preserve real proof text and source offsets',()=>{
  const source=document(String.raw`\begin{proof}
% \begin{invalid}
A matrix $\begin{pmatrix}1&0\\0&1\end{pmatrix}$ is invertible.
\begin{comment}\begin{unclosed}This is not published.\end{comment}
The conclusion remains visible.\end{proof}`);
  const article=parseArticle(source),html=renderArticle(article);
  for(const b of articleBlocks(article))assert.equal(source.slice(b.start,b.end),b.latex);
  assert.match(html,/invertible/);assert.match(html,/conclusion remains visible/);
  assert.doesNotMatch(html,/not published|unclosed|invalid/);
});

test('nested lists retain all items and explicit labels without moving source spans',()=>{
  const source=document(String.raw`\begin{enumerate}[label=(\roman*)]
\item[(A)] First outer claim.\begin{itemize}\item Inner one.\item Inner two.\end{itemize}
\item Second outer claim.\end{enumerate}`);
  const article=parseArticle(source),lists=articleBlocks(article).filter(b=>b.kind==='list');
  assert.equal(lists.length,2);assert.equal(lists[0].items.length,2);assert.equal(lists[1].items.length,2);
  for(const b of articleBlocks(article))assert.equal(source.slice(b.start,b.end),b.latex);
  const html=renderArticle(article);assert.match(html,/>\(A\)<\/span>/);assert.match(html,/Inner two/);assert.match(html,/Second outer claim/);
});

test('all figure panels and numerical table cells remain visible',()=>{
  const article=parseArticle(document(String.raw`\begin{figure}
\includegraphics[width=.32\textwidth]{left.png}\includegraphics[width=.32\textwidth]{right.png}
\caption{Both panels.}\label{fig:panels}\end{figure}
\begin{table}\begin{tabular}{lrr}\toprule Name & $x$ & $x^2$\\\midrule
A & $2$ & $4$\\\multicolumn{3}{c}{A spanning row}\\\bottomrule\end{tabular}
\caption{Exact entries.}\label{tab:entries}\end{table}`));
  const html=renderArticle(article);
  assert.equal((html.match(/<img /g)??[]).length,2);assert.match(html,/left.png/);assert.match(html,/right.png/);
  assert.match(html,/width:32%/);assert.match(html,/colspan="3"/);assert.match(html,/spanning row/);
  assert.equal(article.references['fig:panels'].number,'1');assert.equal(article.references['tab:entries'].number,'1');
});

test('declared theorem counters, parameterized notation and embedded bibliography are retained',()=>{
  const source=String.raw`\title{Counters}\newtheorem{theorem}{Theorem}[section]
\newtheorem{lemma}[theorem]{Lemma}\newtheorem{example}{Example}[subsection]
\newcommand{\square}[1]{#1^2}\DeclareMathOperator{\rank}{rank}
\begin{document}\section{First}\subsection{Subsection}
\begin{theorem}\label{thm:first}$\square{x}\ge0$.\end{theorem}
\begin{lemma}\label{lem:next}The next result.\end{lemma}
\begin{example}\label{ex:first}An example.\end{example}
See \cite{classic}.
\begin{thebibliography}{1}\bibitem{classic} A. Author. A classic theorem.\end{thebibliography}
\end{document}`;
  const article=parseArticle(source);
  assert.equal(article.references['thm:first'].number,'1.1');assert.equal(article.references['lem:next'].number,'1.2');
  assert.equal(article.references['ex:first'].number,'1.1.1');
  assert.match(renderArticle(article),/href="#bib-classic"/);assert.equal(article.bibliography.length,1);
});

test('starred headings, appendix headings and double-dollar mathematics are not discarded',()=>{
  const article=parseArticle(document(String.raw`\section{First}Text $$x^2\ge0$$ continues.
\section*{Acknowledgments}Thanks.\appendix\section{Calculation}$$1+1=2$$`));
  const headings=article.blocks.filter(b=>b.kind==='heading');
  assert.deepEqual(headings.map(b=>b.number),['1','','A']);
  const html=renderArticle(article);assert.match(html,/Acknowledgments/);assert.match(html,/A\. Calculation/);
  assert.equal((html.match(/class="katex-display"/g)??[]).length,2);
});

test('numbered outer rows count even without labels; nested cases and notag do not add numbers',()=>{
  const article=parseArticle(document(String.raw`\begin{align}
x &= \begin{cases}0&x<0\\1&x\ge0\end{cases}\label{eq:first}\\
y &= 2\\
z &= 3\notag\\
w &= 4\label{eq:last}\end{align}
\begin{equation}\label{eq:next}1=1\end{equation}`));
  assert.equal(article.references['eq:first'].number,'1');assert.equal(article.references['eq:last'].number,'3');
  assert.equal(article.references['eq:next'].number,'4');
});

test('a two-column title wrapper retains its content, source spans and pinned date',()=>{
  const source=document(String.raw`\twocolumn[{%
\begin{center}{\LARGE\bfseries A readable title\par}
An Author\textsuperscript{1}\par
An affiliation\par\today\end{center}
\begin{minipage}{.8\textwidth}An abstract with $x^2\ge0$.\end{minipage}
}]\section{The result}Original body. A citation dated 1980{\natexlab{a}}.`);
  const article=parseArticle(source);
  for(const b of articleBlocks(article))assert.equal(source.slice(b.start,b.end),b.latex);
  assert.throws(()=>renderArticle(article),/pinned sourceDate/);
  assert.throws(()=>renderArticle(article,{sourceDate:'2026-02-31'}),/pinned sourceDate/);
  const html=renderArticle(article,{sourceDate:'2026-09-29'});
  assert.match(html,/A readable title/);assert.match(html,/<sup>1<\/sup>/);
  assert.match(html,/29 September 2026/);assert.match(html,/An abstract/);assert.match(html,/Original body/);
  assert.match(html,/1980<span>a<\/span>/);
  assert.doesNotMatch(html,/\}\]/);
});

test('section equation numbering resets and appendix prefixes are preserved',()=>{
  const source=String.raw`\numberwithin{equation}{section}\begin{document}
\section{One}\begin{equation}\label{eq:first}1=1\end{equation}
\section*{Aside}\begin{equation}\label{eq:aside}2=2\end{equation}
\section{Two}\begin{equation}\label{eq:second}3=3\end{equation}
\appendix\section{Appendix}\begin{equation}\label{eq:appendix}4=4\end{equation}
\end{document}`;
  const article=parseArticle(source);
  assert.deepEqual(['eq:first','eq:aside','eq:second','eq:appendix'].map(k=>article.references[k].number),['1.1','1.2','2.1','A.1']);
});

test('ordinary subscripted names link to definitions in both TeX spellings',()=>{
  const article=parseArticle(document(String.raw`\begin{equation}\label{eq:L}L_b(x)=x\end{equation}
Use $L_b(u)$ and $L_{b}(v)$; $XL_b$ is a different name.`));
  const html=renderArticle(article,{definitions:{L_b:{label:'eq:L'}}});
  assert.equal((html.match(/<a href="#article-eq-L"/g)??[]).length,3);
  assert.throws(()=>renderArticle(article,{definitions:{'L+X':{label:'eq:L'}}}),/Unsupported definition notation/);
});


test('definition links preserve unbraced accents and single-token operands',()=>{
  const source=String.raw`\documentclass{article}
\begin{document}
\begin{equation}\label{def:L}L_b(u,v)=uv\end{equation}
$\check L_b$, $\hat{L_b}$, $x^{L_b}$ and $x^\xi$.
\begin{equation}\label{def:xi}\xi(C)=0\end{equation}
\end{document}`;
  const article=parseArticle(source);
  const html=renderArticle(article,{definitions:{L_b:{label:'def:L'},'\\xi':{label:'def:xi'}}});
  assert.match(html,/href="#article-def-L"/);
  assert.match(html,/href="#article-def-xi"/);
  assert.match(html,/class="accent/);
});


test('dsfont blackboard notation remains readable without editing the original source',()=>{
  const source=String.raw`\newcommand{\1}{\mathds{1}}\begin{document}
$\1_{\{x\le y\}}$ and $\mathds{R}$.\end{document}`;
  const article=parseArticle(source),html=renderArticle(article);
  assert.match(html,/mathvariant="double-struck"/);
  assert.match(html,/class="katex"/);
  assert.equal(article.macros['\\1'],String.raw`\mathds{1}`);
});


test('mathtools multiline subexpressions retain each original mathematical row',()=>{
  const source=String.raw`\begin{document}\begin{equation}\label{eq:split}
\begin{multlined}f(x)=x^2+1\\+x^3\end{multlined}\end{equation}\end{document}`;
  const article=parseArticle(source),html=renderArticle(article);
  assert.equal(article.references['eq:split'].number,'1');
  assert.equal(article.blocks[0].body.includes('\\begin{multlined}'),true);
  assert.match(html,/class="mtable"/);assert.match(html,/>3</);
});


test('quoted proof directions retain their mathematical content and quotation marks',()=>{
  const source=String.raw`\begin{document}\enquote{\emph{$\Rightarrow$}}. An argument.\end{document}`;
  const html=renderArticle(parseArticle(source));
  assert.match(html,/“<em>/);assert.match(html,/<\/em>”/);
  assert.match(html,/An argument/);assert.match(html,/⇒/);
});
