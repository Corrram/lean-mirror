"""Source fidelity and filesystem boundary regression tests (no Lean rebuild)."""
import importlib.util
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
import zipfile

spec=importlib.util.spec_from_file_location('mirror',Path(__file__).resolve().parents[1]/'scripts/mirror.py')
mirror=importlib.util.module_from_spec(spec);spec.loader.exec_module(mirror)

class SourceIntegrity(unittest.TestCase):
    def test_checked_source(self):
        example=mirror.ROOT/'examples/analysis'
        source=json.loads((example/'source.json').read_text(encoding='utf-8'))
        self.assertEqual(set(mirror.load_source(example,source)),{'sequence','convergence','unique','bounded'})

    def test_source_and_excerpt_tampering(self):
        with tempfile.TemporaryDirectory(dir=mirror.ROOT/'.lake') as directory:
            example=Path(directory);(example/'source').mkdir()
            original=example/'source/original.tex';original.write_bytes(b'first\nsecond\n')
            excerpt=example/'source/part.tex';excerpt.write_bytes(b'first\n')
            source={'file':'original.tex','sourceSha256':mirror.digest(original),'passages':[
                {'id':'part','file':'source/part.tex','sha256':mirror.digest(excerpt),'startLine':1,'endLine':1}]}
            self.assertEqual(mirror.load_source(example,source),{'part':'first\n'})
            original.write_bytes(b'changed\nsecond\n')
            with self.assertRaisesRegex(ValueError,'Original source hash'):mirror.load_source(example,source)
            original.write_bytes(b'first\nsecond\n');excerpt.write_bytes(b'different\n')
            with self.assertRaisesRegex(ValueError,'Source excerpt changed'):mirror.load_source(example,source)
            source['passages'][0]['sha256']=mirror.digest(excerpt)
            with self.assertRaisesRegex(ValueError,'no longer matches'):mirror.load_source(example,source)

    def test_generated_statement_cannot_be_edited_without_rechecking(self):
        with tempfile.TemporaryDirectory(dir=mirror.ROOT/'.lake') as directory:
            example=Path(directory)
            saved=example/'document.mirror.json';saved.write_text('checked',encoding='utf-8')
            mirror.check_generated(example,{'document.mirror.json':'checked'})
            saved.write_text('edited inequality',encoding='utf-8')
            with self.assertRaisesRegex(ValueError,'Stale generated companion'):
                mirror.check_generated(example,{'document.mirror.json':'checked'})

    def test_executable_bundle_has_pins_and_no_local_runtime(self):
        with tempfile.TemporaryDirectory(dir=mirror.ROOT/'.lake') as directory:
            path=Path(directory)/'source.zip'
            fresh=mirror.ROOT/'examples/analysis/document.mirror.json'
            mirror.source_bundle(path,{fresh:b'freshly checked output'})
            with zipfile.ZipFile(path) as bundle:
                names=bundle.namelist()
                self.assertIn('lean-mirror/lean-toolchain',names)
                self.assertEqual(bundle.read('lean-mirror/examples/analysis/document.mirror.json'),b'freshly checked output')
                self.assertIn('lean-mirror/LeanMirror/Document.lean',names)
                self.assertIn('lean-mirror/examples/analysis/source/LICENSE.md',names)
                self.assertFalse(any('/.lake/' in n or '/node_modules/' in n for n in names))

    def test_paths_cannot_escape_project(self):
        with self.assertRaises(ValueError):mirror.inside(mirror.ROOT/'..'/'outside')

if __name__=='__main__':unittest.main()
