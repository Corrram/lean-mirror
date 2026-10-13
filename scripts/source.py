#!/usr/bin/env python3
"""Compile the editable TeX companion and publish only freshly checked source."""
import argparse
import hashlib
import http.server
import json
from pathlib import Path
import shutil
import subprocess
import tempfile

from mirror import ROOT, inside, lake_executable, source_bundle


def reconcile(config, checked, example):
    """Neither config metadata nor an old export may replace certificate source."""
    if checked.get('schemaVersion') != 1:
        raise ValueError('Unsupported source certificate schema')
    records = checked['entries']
    names = [record['certificate'] for record in records]
    if len(set(names)) != len(names):
        raise ValueError('Duplicate source certificate')
    entries = config['entries']
    if len(entries) != len(records) or {e['certificate'] for e in entries} != set(names):
        raise ValueError('Configured entries must match all compiled certificates exactly')
    result = []
    for entry in entries:
        record = next(r for r in records if r['certificate'] == entry['certificate'])
        for field, file_field in [('source', 'source'), ('proofSource', 'proof')]:
            expected = inside(example / entry[file_field], example).read_bytes().decode('utf-8') if file_field in entry else ''
            if record[field] != expected:
                raise ValueError(f'Compiled {field} differs from editable source: {entry["id"]}')
        result.append({**record, 'id': entry['id'], 'title': entry['title'],
                       'sourceFile': entry['source'], 'proofFile': entry.get('proof')})
    return {'schemaVersion': 1, 'title': config['title'], 'entries': result}


def build(example, check=False):
    example = inside(example)
    config = json.loads((example / 'source.json').read_text(encoding='utf-8'))
    compiler = inside(example / config['compiler'], example)
    subprocess.run([lake_executable(), 'build', 'LeanMirror.Source.Export'], cwd=ROOT, check=True)
    with tempfile.TemporaryDirectory(prefix='source-', dir=ROOT / '.lake') as tmp:
        tmp = Path(tmp)
        raw = tmp / 'checked.json'
        # Run the authoring module directly: include_str inputs must be reread
        # even when Lake's cached .olean is otherwise up to date.
        subprocess.run([lake_executable(), 'env', 'lean', '--run', str(compiler), str(raw)], cwd=ROOT, check=True)
        doc = reconcile(config, json.loads(raw.read_text(encoding='utf-8')), example)
        export = tmp / 'document.json'
        export.write_text(json.dumps(doc, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
        # Validate and render to staging first; failed builds leave no new badge.
        staging = tmp / 'reader'
        subprocess.run(['node', str(ROOT / 'reader/source.mjs'), str(export), str(staging)], cwd=ROOT, check=True)
        if check:
            print(f'Checked {len(doc["entries"])} source certificates, definitions, and reader.')
            return None
        out = ROOT / 'build' / ('source-' + example.name)
        out.mkdir(parents=True, exist_ok=True)
        shutil.copytree(staging, out, dirs_exist_ok=True)
        shutil.copyfile(export, out / 'document.json')
        paths = {compiler, example / 'source.json'}
        paths.update(inside(example / e['source'], example) for e in config['entries'])
        paths.update(inside(example / e['proof'], example) for e in config['entries'] if e.get('proof'))
        for path in paths:
            destination = out / 'source' / path.relative_to(example)
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(path, destination)
        manifest = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(paths)}
        (out / 'verification.json').write_text(json.dumps({'inputs': manifest}, indent=2) + '\n', encoding='utf-8')
        source_bundle(out / 'lean-mirror-source.zip')
        print(f'Built {out / "index.html"}')
        return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=['build', 'check', 'serve'])
    parser.add_argument('example', nargs='?', default='examples/source')
    parser.add_argument('--port', type=int, default=8767)
    args = parser.parse_args()
    out = build(ROOT / args.example, args.command == 'check')
    if args.command == 'serve':
        from functools import partial
        server = http.server.ThreadingHTTPServer(('127.0.0.1', args.port), partial(http.server.SimpleHTTPRequestHandler, directory=str(out)))
        print(f'http://127.0.0.1:{args.port}', flush=True)
        server.serve_forever()


if __name__ == '__main__':
    main()
