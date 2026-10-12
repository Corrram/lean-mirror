// A source-preserving LaTeX article reader. Mathematical evidence is an overlay,
// never a replacement for the manuscript, and unchecked spans stay visible.
import katex from 'katex';
import {escape} from './render.mjs';

const envPattern = /\\(begin|end)\{([^}]+)\}/g;
const mathEnvs = new Set(['equation','equation*','align','align*','gather','gather*','gathering','multline','multline*']);
const results = new Set(['theorem','lemma','proposition','corollary','remark','definition']);
export function brace(text, offset) {
  if(text[offset] !== '{') throw new Error(`Expected brace at ${offset}`);
  let depth=1, at=offset+1;
  for(; at<text.length; at++) {
    if(text[at]==='\\') {at++;continue;}
    if(text[at]==='{') depth++;
    else if(text[at]==='}' && --depth===0) return {value:text.slice(offset+1,at),end:at+1};
  }
  throw new Error('Unclosed LaTeX argument');
}

function argument(text,at) {
  while(/\s/.test(text[at]??'') && at<text.length) at++;
  return brace(text,at);
}
function optional(text,at) {
  if(text[at]!=='[') return {value:'',end:at};
  let depth=0;
  for(let i=at+1;i<text.length;i++) {
    if(text[i]==='{') depth++;
    else if(text[i]==='}') depth--;
    else if(text[i]===']' && depth===0) return {value:text.slice(at+1,i),end:i+1};
  }
  throw new Error('Unclosed LaTeX option');
}
const labels = text => [...text.matchAll(/\\label\{([^}]+)\}/g)].map(m=>m[1]);
const anchor = label => 'article-'+label.replace(/[^a-zA-Z0-9-]/g,'-');

export function articleBlocks(article) {
  const all=[];
  function walk(blocks){for(const b of blocks){all.push(b);if(b.children)walk(b.children);if(b.items)b.items.forEach(walk);}}
  walk(article.blocks);return all;
}

/** Bind by exact labels or a unique literal quotation; fuzzy matching is rejected. */
export function resolveBindings(article,bindings) {
  const blocks=articleBlocks(article),annotations={};
  for(const binding of bindings) {
    const candidates=blocks.filter(b=>binding.label?b.labels.includes(binding.label):b.kind===binding.kind&&b.latex.includes(binding.quote));
    if(candidates.length!==1)throw new Error(`Source binding must match exactly once: ${binding.label??binding.quote} (${candidates.length})`);
    const b=candidates[0];
    annotations[b.id]??=[];
    for(const declaration of binding.declarations)annotations[b.id].push({declaration,title:binding.title,note:binding.note});
  }
  return annotations;
}

function environment(text,at) {
  envPattern.lastIndex=at;
  const first=envPattern.exec(text);
  if(first?.index!==at || first[1]!=='begin') throw new Error('Expected environment');
  const title=optional(text,envPattern.lastIndex);
  const contentStart=title.end;
  const stack=[first[2]];
  envPattern.lastIndex=contentStart;
  for(let token; (token=envPattern.exec(text));) {
    if(token[1]==='begin') stack.push(token[2]);
    else if(stack.pop()!==token[2]) throw new Error(`Mismatched environment: ${token[2]}`);
    if(!stack.length) return {kind:first[2],title:title.value,body:text.slice(contentStart,token.index),end:envPattern.lastIndex};
  }
  throw new Error(`Unclosed environment ${first[2]}`);
}

export function parseArticle(source,bibliography='') {
  const begin=source.indexOf('\\begin{document}'),end=source.lastIndexOf('\\end{document}');
  if(begin<0||end<begin) throw new Error('Missing article document');
  const macros={};
  for(const match of source.slice(0,begin).matchAll(/\\newcommand\{(\\[A-Za-z]+|\\\d)\}(?!\[)/g)) {
    macros[match[1]]=argument(source,match.index+match[0].length).value;
  }
  const getMeta=command=>{const m=source.match(new RegExp('\\\\'+command+'\\{'));return m?brace(source,m.index+m[0].length-1).value:'';};
  const article={title:getMeta('title'),author:getMeta('author'),macros,blocks:[],references:{},bibliography:[]};
  let section=0,subsection=0,result=0,equation=0,figure=0,serial=0;
  function parse(text,base=0) {
    let at=0; const blocks=[];
    while(at<text.length) {
      if(/\s/.test(text[at])) {at++;continue;}
      if(text[at]==='%') {at=text.indexOf('\n',at);if(at<0)break;continue;}
      const start=at;
      const sectionMatch=text.slice(at).match(/^\\(section|subsection)\{/);
      let block;
      if(sectionMatch) {
        const arg=brace(text,at+sectionMatch[0].length-1); at=arg.end;
        const labelMatch=text.slice(at).match(/^\s*\\label\{[^}]+\}/);
        if(labelMatch)at+=labelMatch[0].length;
        if(sectionMatch[1]==='section'){section++;subsection=0;result=0;}else subsection++;
        block={kind:'heading',level:sectionMatch[1]==='section'?2:3,number:sectionMatch[1]==='section'?`${section}`:`${section}.${subsection}`,title:arg.value};
      } else if(text.startsWith('\\begin{',at)) {
        const env=environment(text,at);at=env.end;
        if(mathEnvs.has(env.kind)) {
          const count=env.kind==='align'?Math.max(1,labels(env.body).length):env.kind.endsWith('*')?0:1;
          const numbers=Array.from({length:count},()=>String(++equation));
          block={kind:'math',environment:env.kind,body:env.body,numbers};
        } else if(results.has(env.kind)) {
          const prefix=env.body.match(/^\s*(?:\\label\{[^}]+\}\s*)*/)[0];
          block={kind:env.kind,title:env.title,number:`${section}.${++result}`,ownLabels:labels(prefix),children:parse(env.body.slice(prefix.length),base+start+text.slice(start,at).indexOf(env.body)+prefix.length)};
        } else if(env.kind==='proof'||env.kind==='abstract'||env.kind==='center') {
          block={kind:env.kind,title:env.title,children:parse(env.body,base+start+text.slice(start,at).indexOf(env.body))};
        } else if(env.kind==='figure') {
          const image=env.body.match(/\\includegraphics(?:\[[^\]]*\])?\{([^}]+)\}/);
          const caption=env.body.match(/\\caption\{/);
          if(!image||!caption)throw new Error('Incomplete figure');
          block={kind:'figure',number:String(++figure),image:image[1],caption:brace(env.body,caption.index+caption[0].length-1).value};
        } else if(env.kind==='enumerate'||env.kind==='itemize') {
          const parts=env.body.split(/\\item\s*/).slice(1);
          block={kind:'list',style:env.kind==='itemize'?'bullet':env.title.includes('alph')?'alpha':env.title.includes('Q')?'question':'decimal',items:parts.map(p=>parse(p,base+start+text.slice(start,at).indexOf(p)))};
        } else throw new Error(`Unsupported article environment ${env.kind}`);
      } else if(text.startsWith('\\[',at)) {
        const close=text.indexOf('\\]',at+2);if(close<0)throw new Error('Unclosed display');
        at=close+2;block={kind:'math',body:text.slice(start+2,close),numbers:[]};
      } else {
        const next=text.slice(at).search(/\n\s*\n|\\begin\{|\\\[|\\(?:sub)?section\{/);
        at=next<0?text.length:at+Math.max(next,1);
        block={kind:'paragraph',body:text.slice(start,at)};
      }
      block.id=`passage-${++serial}`;
      block.start=base+start;block.end=base+at;
      block.latex=text.slice(start,at);block.labels=block.ownLabels??((block.children||block.items)?[]:labels(block.latex));
      blocks.push(block);
    }
    return blocks;
  }
  article.blocks=parse(source.slice(begin+16,end),begin+16);
  function putReference(label,number) {
    if(article.references[label])throw new Error(`Duplicate source label ${label}`);
    const id=anchor(label);
    if(Object.values(article.references).some(r=>r.id===id))throw new Error(`Colliding source anchor ${label}`);
    article.references[label]={id,number};
  }
  function referenceWalk(blocks) {
    for(const b of blocks) {
      // Label equations within results separately from their containing result.
      if(b.kind==='math') b.labels.forEach((l,i)=>putReference(l,b.numbers[i]??''));
      else if(b.number) for(const l of b.labels.filter(l=>!b.children?.some(c=>c.labels.includes(l))))putReference(l,b.number);
      if(b.kind==='list')b.items.forEach((item,i)=>{for(const p of item)if(p.kind==='paragraph')for(const l of p.labels)putReference(l,b.style==='question'?`(Q${i+1})`:b.style==='alpha'?`(${String.fromCharCode(97+i)})`:String(i+1));referenceWalk(item);});
      if(b.children)referenceWalk(b.children);
    }
  }
  referenceWalk(article.blocks);
  const bibStart=/\\bibitem(?:\[[\s\S]*?\])?\{([^}]+)\}/g;
  const matches=[...bibliography.matchAll(bibStart)];
  article.bibliography=matches.map((m,i)=>({key:m[1],number:i+1,body:bibliography.slice(m.index+m[0].length,matches[i+1]?.index??bibliography.length).replace(/\\end\{thebibliography\}[\s\S]*/,'')}));
  return article;
}

export function renderArticle(article,{annotations={},evidence={},definitions={},figureURL=x=>x,sourceURL='',proofDetails=()=>'',certificateURL=()=>''}={}) {
  const knownAnchors=new Set(Object.values(article.references).map(r=>r.id));
  for(const d of Object.values(definitions)) {
    if(!article.references[d.label])throw new Error(`Unknown definition label ${d.label}`);
  }
  function m(tex,display=false) {
    tex=tex.replace(/\\label\{[^}]+\}/g,'');
    if(/\\(?:href|url|html[A-Za-z]*|includegraphics)\b/.test(tex))throw new Error('Source math cannot supply presentation links or HTML');
    // Link lexical symbols; never nest links around their arguments.
    const commandMap=Object.entries(definitions).filter(([key])=>key.startsWith('\\')).sort((a,b)=>b[0].length-a[0].length);
    const re=commandMap.length?new RegExp(commandMap.map(([k])=>k.replace(/[.*+?^${}()|[\]\\]/g,'\\$&')).join('|'),'g'):null;
    if(re)tex=tex.replace(re,(symbol,offset,input)=>{
      if(/[A-Za-z]/.test(input[offset+symbol.length]??''))return symbol;
      const def=definitions[symbol],id=article.references[def.label]?.id??def.id;
      return `\\href{#${id}}{${symbol}}`;
    });
    return katex.renderToString(tex,{displayMode:display,throwOnError:true,strict:'ignore',macros:article.macros,trust:ctx=>ctx.command==='\\href'&&knownAnchors.has(ctx.url?.slice(1))});
  }
  function inline(tex) {
    let out='',at=0;
    const simple={'maketitle':'','centering':'','small':'','itshape':'','upshape':'','par':'','noindent':'','smallskip':'','leavevmode':'','qedhere':'','newblock':' '};
    while(at<tex.length) {
      if(tex[at]==='$') {const end=tex.indexOf('$',at+1);if(end<0)throw new Error('Unclosed inline math');out+=m(tex.slice(at+1,end));at=end+1;continue;}
      if(tex[at]==='%'&&(at===0||tex[at-1]!=='\\')){const end=tex.indexOf('\n',at);at=end<0?tex.length:end+1;continue;}
      if(tex[at]==='\\') {
        const match=tex.slice(at).match(/^\\([A-Za-z]+\*?|[^A-Za-z])/);const cmd=match[1];at+=match[0].length;
        if(Object.hasOwn(simple,cmd)){out+=simple[cmd];continue;}
        if(cmd==='\\'){out+='<br>';continue;}
        if(cmd==='quad'||cmd==='qquad'){out+=' ';continue;}
        if(cmd==='penalty'){const number=tex.slice(at).match(/^[+-]?\d+/);if(!number)throw new Error('Invalid penalty');at+=number[0].length;continue;}
        if(['Needspace','vspace','hspace','bibliographystyle'].includes(cmd)){at=argument(tex,at).end;continue;}
        if(cmd==='label'){at=argument(tex,at).end;continue;}
        if(cmd==='ref'||cmd==='eqref'){const arg=argument(tex,at),r=article.references[arg.value];if(!r)throw new Error(`Unknown reference ${arg.value}`);out+=`<a href="#${r.id}">${cmd==='eqref'?'('+escape(r.number)+')':escape(r.number)}</a>`;at=arg.end;continue;}
        if(['emph','textbf','textit','textup','textnormal','mbox','mathrm','nolinkurl'].includes(cmd)){const arg=argument(tex,at);const tag=cmd==='emph'||cmd==='textit'?'em':cmd==='textbf'?'strong':'span';out+=`<${tag}>${inline(arg.value)}</${tag}>`;at=arg.end;continue;}
        if(cmd==='texorpdfstring'){const first=argument(tex,at),second=argument(tex,first.end);out+=inline(first.value);at=second.end;continue;}
        if(cmd==='href'){const href=argument(tex,at),label=argument(tex,href.end);if(!/^(https?:|mailto:)/.test(href.value))throw new Error('Invalid source hyperlink');out+=`<a href="${escape(href.value)}">${inline(label.value)}</a>`;at=label.end;continue;}
        if(cmd==='url'){const arg=argument(tex,at);if(!/^https?:/.test(arg.value))throw new Error('Invalid source URL');out+=`<a href="${escape(arg.value)}">${escape(arg.value)}</a>`;at=arg.end;continue;}
        if(cmd==='doi'){const arg=argument(tex,at);out+=`<a href="https://doi.org/${escape(arg.value)}">doi: ${escape(arg.value)}</a>`;at=arg.end;continue;}
        if(cmd.startsWith('cite')){const first=optional(tex,at),second=optional(tex,first.end),arg=argument(tex,second.end);out+='['+arg.value.split(',').map(key=>{const b=article.bibliography.find(b=>b.key===key.trim());if(!b)throw new Error(`Missing citation ${key}`);return `<a href="#bib-${escape(b.key)}">${b.number}</a>`;}).join(', ')+(first.value?', '+inline(first.value):'')+(second.value?', '+inline(second.value):'')+']';at=arg.end;continue;}
        if(cmd==='bibliography'){at=argument(tex,at).end;continue;}
        if(cmd==='keywords'){const arg=argument(tex,at);out+='<strong>Keywords:</strong> '+inline(arg.value);at=arg.end;continue;}
        if(cmd==='footnote'){const arg=argument(tex,at);out+=`<span class="article-footnote">(${inline(arg.value)})</span>`;at=arg.end;continue;}
        if(['%','&','_','#','$','{','}'].includes(cmd)){out+=escape(cmd);continue;}
        if(['\'','`','"','^','~','c','v','H'].includes(cmd)){const arg=tex[at]==='{'?brace(tex,at):{value:tex[at],end:at+1};const marks={"'":'\u0301','`':'\u0300','"':'\u0308','^':'\u0302','~':'\u0303',c:'\u0327',v:'\u030c',H:'\u030b'};out+=escape((arg.value+marks[cmd]).normalize('NFC'));at=arg.end;continue;}
        if(cmd==='textendash'||cmd==='textemdash'){out+=cmd==='textendash'?'–':'—';continue;}
        if(cmd==='and'){out+=' and ';continue;}
        throw new Error(`Unsupported article prose command \\${cmd}: ${tex.slice(at-30,at+45)}`);
      }
      const char=tex[at++];if(char==='{'||char==='}')continue;
      out+=char==='~'?'&nbsp;':escape(char);
    }
    return out.replace(/---/g,'—').replace(/--/g,'–').replace(/``/g,'“').replace(/''/g,'”').replace(/\s+/g,' ');
  }
  function checked(b) {
    const items=annotations[b.id]??b.labels.flatMap(l=>annotations[l]??[]);
    if(!items.length)return '';
    return `<details class="article-evidence"><summary>Open verification (${items.length})</summary>${items.map(item=>{
      const record=evidence[item.declaration];if(!record)throw new Error(`Missing compiled evidence ${item.declaration}`);
      return `<section><h4>${escape(item.title??'Checked mathematical counterpart')}</h4><p><a href="${escape(certificateURL(record))}">${escape(record.declaration)}</a></p><pre><code>${escape(record.type)}</code></pre>${item.note?`<p>${escape(item.note)}</p>`:''}</section>`;
    }).join('')}${proofDetails(b,items,m)}</details>`;
  }
  function blocksHTML(blocks) {return blocks.map(b=>{
    const contentId=b.labels.find(l=>article.references[l])??b.id;
    const attrs=`id="${contentId===b.id?b.id:anchor(contentId)}" data-passage="${b.id}"`;
    const extraAnchors=b.labels.filter(l=>l!==contentId&&!b.children?.some(c=>c.labels.includes(l))).map(l=>`<span id="${anchor(l)}"></span>`).join('');
    if(b.kind==='heading')return `<h${b.level} ${attrs}>${b.number}. ${inline(b.title)}</h${b.level}>${extraAnchors}`;
    if(b.kind==='paragraph')return `<div class="article-paragraph" ${attrs}><p>${inline(b.body)}</p>${checked(b)}</div>`;
    if(b.kind==='math') {
      let tex=b.body;
      if(b.environment?.startsWith('align'))tex=`\\begin{aligned}${tex}\\end{aligned}`;
      if(b.environment?.startsWith('gather'))tex=`\\begin{gathered}${tex}\\end{gathered}`;
      if(b.environment?.startsWith('multline'))tex=`\\begin{gathered}${tex}\\end{gathered}`;
      return `<div class="article-equation" ${attrs}>${extraAnchors}<div class="article-math">${m(tex,true)}</div>${b.numbers.length?`<span class="equation-number">(${b.numbers.join(', ')})</span>`:''}${checked(b)}</div>`;
    }
    if(results.has(b.kind))return `<section class="article-result" data-result-kind="${b.kind}" ${attrs}>${extraAnchors}<h3>${b.kind[0].toUpperCase()+b.kind.slice(1)} ${b.number}${b.title?' ('+inline(b.title)+')':''}.</h3>${blocksHTML(b.children)}${checked(b)}</section>`;
    if(b.kind==='proof')return `<section class="article-proof" ${attrs}><h4>${b.title?inline(b.title):'Proof.'}</h4>${blocksHTML(b.children)}<span class="article-qed">□</span>${checked(b)}</section>`;
    if(b.kind==='abstract')return `<section class="article-abstract" ${attrs}><h2>Abstract</h2>${blocksHTML(b.children)}</section>`;
    if(b.kind==='center')return `<div class="article-affiliation" ${attrs}>${blocksHTML(b.children)}</div>`;
    if(b.kind==='figure')return `<figure ${attrs}>${extraAnchors}<img src="${escape(figureURL(b.image))}" alt="Figure ${b.number}" loading="lazy"><figcaption><strong>Figure ${b.number}.</strong> ${inline(b.caption)}</figcaption>${checked(b)}</figure>`;
    if(b.kind==='list')return `<${b.style==='bullet'?'ul':'ol'} class="article-list ${b.style}" ${attrs}>${b.items.map(item=>`<li>${blocksHTML(item)}</li>`).join('')}</${b.style==='bullet'?'ul':'ol'}>`;
    throw new Error(`Unsupported block ${b.kind}`);
  }).join('\n');}
  const toc=article.blocks.filter(b=>b.kind==='heading').map(b=>`<li class="level-${b.level}"><a href="#${b.labels[0]?anchor(b.labels[0]):b.id}">${b.number}. ${inline(b.title)}</a></li>`).join('');
  return `<article class="mirror-full-article"><header class="article-title"><h1>${inline(article.title)}</h1><p class="article-author">${inline(article.author)}</p><p><a href="${escape(sourceURL)}">Published source</a> · <a href="#article-verification">Verification map</a></p></header><details class="article-contents"><summary>Contents</summary><ol>${toc}</ol></details>${blocksHTML(article.blocks)}<section class="article-bibliography"><h2>References</h2><ol>${article.bibliography.map(b=>`<li id="bib-${escape(b.key)}">${inline(b.body)}</li>`).join('')}</ol></section></article>`;
}
