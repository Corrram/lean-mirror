#!/usr/bin/env python3
"""Build, check, or serve a LeanMirror companion from a pinned Lean project."""
import argparse
import hashlib
import http.server
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import zipfile

ROOT = Path(__file__).resolve().parents[1]

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def inside(path, root=ROOT):
    path = path.resolve()
    path.relative_to(root.resolve())
    return path

def lake_executable():
    if os.environ.get('LAKE'):
        return os.environ['LAKE']
    toolchain = (ROOT/'lean-toolchain').read_text().strip().replace('/', '--').replace(':', '---')
    direct = Path.home()/'.elan'/'toolchains'/toolchain/'bin'/('lake.exe' if os.name=='nt' else 'lake')
    return str(direct) if direct.exists() else 'lake'

def load_source(example, source):
    original = inside(example/'source'/source['file'], example/'source')
    if digest(original) != source['sourceSha256']:
        raise ValueError('Original source hash changed; review and update source.json explicitly.')
    lines = original.read_text(encoding='utf-8').splitlines()
    excerpts = {}
    for entry in source['passages']:
        file = inside(example/entry['file'], example)
        if digest(file) != entry['sha256']:
            raise ValueError('Source excerpt changed: '+entry['id'])
        text = file.read_text(encoding='utf-8')
        expected = '\n'.join(lines[entry['startLine']-1:entry['endLine']])+'\n'
        if text != expected:
            raise ValueError('Excerpt no longer matches the original: '+entry['id'])
        excerpts[entry['id']] = text
    return excerpts

def tex_escape(s):
    return ''.join({'\\':r'\textbackslash{}','&':r'\&','%':r'\%','$':r'\$','#':r'\#','_':r'\_','{':r'\{','}':r'\}'}.get(c,c) for c in s)

def clean_math(s):
    import re
    s = re.sub(r'\\href\{#def-([^}]+)\}',r'\\hyperlink{def-\1}',s)
    return s.replace('ε',r'\epsilon')

def formula_prose(f):
    math=lambda s:'$'+clean_math(s)+'$'
    kind=f['kind']
    if kind=='and': return formula_prose(f['left'])+'; and '+formula_prose(f['right'])
    if kind=='forall':
        variable=math(f.get('binding',f['name'])+r'\in '+f['type'])
        if f['body']['kind']=='imp':
            return 'for every '+variable+' satisfying '+math(f['body']['premise']['latex'])+', '+formula_prose(f['body']['body'])
        return 'for every '+variable+', '+formula_prose(f['body'])
    if kind=='exists': return 'there exists '+math(f.get('binding',f['name'])+r'\in '+f['type'])+' such that '+formula_prose(f['body'])
    if kind=='imp': return 'if '+math(f['premise']['latex'])+', then '+formula_prose(f['body'])
    return math(f['latex'])


def relation(f):
    prefix=[]
    while f['kind'] in ('forall','imp'):
        prefix.append({k:v for k,v in f.items() if k not in ('body','latex')})
        f=f['body']
    return (prefix,f) if f['kind']=='relation' else None


def latex_proof(n):
    math=lambda s:'$'+clean_math(s)+'$'
    display=lambda s:'\n\\[ '+clean_math(s)+r'. \]'+'\n'
    if n['kind']=='have' and relation(n['formula']):
        prefix,first=relation(n['formula']); group=[first]; following=n['next']
        while following['kind']=='have':
            r=relation(following['formula'])
            if not r or r[0]!=prefix or r[1]['left']!=group[-1]['right']: break
            group.append(r[1]);following=following['next']
        if len(group)>1:
            lead='Estimate'
            for p in prefix:
                lead+=(', for every '+math(p.get('binding',p['name'])+r'\in '+p['type'])) if p['kind']=='forall' else ' satisfying '+math(p['premise']['latex'])
            rows=first['left']+' &'+first['operator']+' '+first['right']
            for r in group[1:]:rows+=r' \\ &'+r['operator']+' '+r['right']
            return lead+':'+display(r'\begin{aligned}'+rows+r'\end{aligned}')+latex_proof(following)
    if n['kind']=='fix':
        value=(r'\{'+n['name']+r'_n\}_{n=1}^{\infty}') if n['type']==r'\mathbb{R}^{\mathbb{N}}' else n.get('binding',n['name'])+r'\in '+n['type']
        here='Let '+math(value)+'.\n'
    elif n['kind']=='assume': here='Suppose '+formula_prose(n['formula'])+'.\n'
    elif n['kind']=='choose': here='Choose '+math(n.get('binding',n['name'])+r'\in '+n['type'])+' such that '+formula_prose(n['formula'])+'.\n'
    elif n['kind']=='have': here='Then '+formula_prose(n['formula'])+'.\n'
    elif n['kind']=='suffices':
        return 'It suffices to show that '+formula_prose(n['formula'])+'.\n'+latex_proof(n['next'])+'Consequently, '+math(n['goal'])+'.\n'
    else: return 'Hence '+formula_prose(n['formula'])+'.\n'
    return here+latex_proof(n['next'])


def latex_document(doc, source):
    text=r'''\documentclass[11pt]{article}
\usepackage[a4paper,margin=25mm]{geometry}
\usepackage[T1]{fontenc}
\usepackage[utf8]{inputenc}
\usepackage{amsmath,amssymb,amsthm}
\usepackage[hidelinks]{hyperref}
\newtheorem{proposition}{Proposition}
\begin{document}
\title{''' + tex_escape(doc['title']) + r'''\\\large A LeanMirror companion}
\author{A companion adapted from ''' + tex_escape(source['author']) + r'''}
\date{}
\maketitle
'''
    text+='Adapted from '+tex_escape(source['title'])+'. '+tex_escape(source['scope'])+' Distributed under '+tex_escape(source['license'])+'.\n\n'
    text+='Original source: \\url{'+source['repository']+'}.\\par\nRevision: \\texttt{'+source['revision']+'}.\n'
    text+=r'\section*{Definitions and notation}'+'\n'
    for d in doc['definitions']:
        text+=r'\hypertarget{def-'+d['id']+r'}{}\paragraph{'+tex_escape(d['title'])+'}\n'
        text+=tex_escape(d['text'].replace('ε > 0','epsilon > 0').replace('n ≥ M','n at least M').replace('ε','epsilon'))+'\n'
        text+=(formula_prose(d['structured'])+'.\n') if 'structured' in d else '\\[ '+clean_math(d['formula'])+r'. \]'+'\n'
    for r in doc['results']:
        text+=r'\begin{proposition}'+tex_escape(r['title'])+'\n\n'+formula_prose(r['checked']['statement']).replace('for every','For every',1)+'.'+r'\end{proposition}'+'\n'
        text+=r'\begin{proof}'+latex_proof(r['checked']['proof'])+r'\end{proof}'+'\n'
    text+=r'\section*{Verification and scope}'+'\n'
    text+='The formal interpretation of every proof node is checked by Lean. The argument structure and all displayed formulas are generated from the checked expressions. The original wording can be compared in the interactive companion. Rendering, vocabulary and editorial alignment remain inspectable software and human review boundaries.\n'
    text+=r'\end{document}'+'\n'
    return text

def source_bundle(destination, overrides=None):
    overrides=overrides or {}
    files=[ROOT/name for name in ('LeanMirror.lean','lakefile.toml','lake-manifest.json',
        'lean-toolchain','.gitattributes','package.json','package-lock.json','LICENSE','README.md')]
    for folder in ('LeanMirror','reader','scripts','examples','tests','docs'):
        files.extend(p for p in (ROOT/folder).rglob('*') if p.is_file() and '__pycache__' not in p.parts)
    with zipfile.ZipFile(destination,'w',compression=zipfile.ZIP_DEFLATED) as bundle:
        for file in sorted(set(files)|set(overrides)):
            info=zipfile.ZipInfo('lean-mirror/'+file.relative_to(ROOT).as_posix(),date_time=(2020,1,1,0,0,0))
            info.compress_type=zipfile.ZIP_DEFLATED
            bundle.writestr(info,overrides[file] if file in overrides else file.read_bytes())


def check_generated(example, generated):
    for name,text in generated.items():
        saved=example/name
        if not saved.exists() or saved.read_text(encoding='utf-8')!=text:
            raise ValueError('Stale generated companion: '+str(saved)+'. Run the build command.')


def build(example, check=False):
    config=json.loads((example/'mirror.json').read_text(encoding='utf-8'))
    source_file=inside(example/config['source'], example)
    source=json.loads(source_file.read_text(encoding='utf-8'))
    excerpts=load_source(example,source)
    if not (ROOT/'node_modules/katex').exists(): raise ValueError('Run npm ci once to install the pinned renderer.')
    subprocess.run([lake_executable(),'build',config['module']],cwd=ROOT,check=True)
    temporary=ROOT/'.lake/mirror-export';temporary.mkdir(parents=True,exist_ok=True)
    with tempfile.TemporaryDirectory(dir=temporary) as directory:
        work=inside(Path(directory),temporary)
        fresh=work/'document.mirror.json'
        subprocess.run([lake_executable(),'env','lean','--run',str(inside(ROOT/config['exporter'])),str(fresh)],cwd=ROOT,check=True)
        doc=json.loads(fresh.read_text(encoding='utf-8'))
        tex=latex_document(doc,source)
        generated={'document.mirror.json':fresh.read_text(encoding='utf-8'),'companion.tex':tex}
        if check: check_generated(example,generated)
        out=work/'rendered'
        out.mkdir(parents=True,exist_ok=True)
        for name,text in generated.items():(out/name).write_text(text,encoding='utf-8',newline='\n')
        manifest={'toolchain':(ROOT/'lean-toolchain').read_text().strip(),'sourceRevision':source['revision'],
          'documentSha256':digest(fresh),'example':example.relative_to(ROOT).as_posix(),
          'executable':Path(config['executable']).name,'inputs':{}}
        for f in sorted([*ROOT.glob('LeanMirror/**/*.lean'),ROOT/'LeanMirror.lean',ROOT/'lake-manifest.json',ROOT/'lean-toolchain',ROOT/'lakefile.toml',ROOT/'package-lock.json',
            *ROOT.glob('reader/*'),*ROOT.glob('scripts/*.py'),*ROOT.glob('scripts/*.lean'),
            example/'mirror.json', source_file, *example.glob('source/*')]):
            manifest['inputs'][f.relative_to(ROOT).as_posix()]=digest(f)
        build_file=out/'verification.json';build_file.write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
        ex_file=work/'excerpts.json';ex_file.write_text(json.dumps(excerpts,ensure_ascii=False),encoding='utf-8')
        subprocess.run(['node',str(ROOT/'reader/render.mjs'),str(fresh),str(source_file),str(ex_file),str(out),str(build_file)],cwd=ROOT,check=True)
        shutil.copytree(example/'source',out/'source',dirs_exist_ok=True)
        shutil.copy2(inside(ROOT/config['executable']),out/manifest['executable'])
        source_bundle(out/'lean-mirror-source.zip',{example/name:text.encode('utf-8') for name,text in generated.items()})
        if check: print('PASS: Lean proofs, source fidelity, generated artifacts, and HTML rendering.')
        else:
            destination=inside(ROOT/config['output'])
            if destination == ROOT or ROOT/'build' not in destination.parents:
                raise ValueError('Output must be a subdirectory of build/.')
            destination.mkdir(parents=True,exist_ok=True)
            for name,text in generated.items():
                (example/name).write_text(text,encoding='utf-8',newline='\n')
            shutil.copytree(out,destination,dirs_exist_ok=True)
            print('Built '+str(destination/'index.html'))
    return inside(ROOT/config['output'])

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('command',choices=['build','check','serve'])
    p.add_argument('example',nargs='?',default='examples/analysis')
    p.add_argument('--port',type=int,default=8766)
    args=p.parse_args()
    example=inside(ROOT/args.example)
    try: out=build(example,args.command=='check')
    except (ValueError,OSError,KeyError,subprocess.CalledProcessError) as error:p.exit(1,str(error)+'\n')
    if args.command=='serve':
        from functools import partial
        handler=partial(http.server.SimpleHTTPRequestHandler,directory=str(out))
        server=http.server.ThreadingHTTPServer(('127.0.0.1',args.port),handler)
        print(f'Reader: http://127.0.0.1:{args.port}',flush=True)
        try:server.serve_forever()
        except KeyboardInterrupt:server.server_close()

if __name__=='__main__': main()
