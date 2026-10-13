import importlib.util
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
spec = importlib.util.spec_from_file_location('source_companion', ROOT / 'scripts/source.py')
source = importlib.util.module_from_spec(spec)
spec.loader.exec_module(source)


class CheckedSource(unittest.TestCase):
    def test_certificate_is_bound_to_editable_source_and_proof(self):
        with tempfile.TemporaryDirectory(dir=ROOT / '.lake') as directory:
            example = Path(directory)
            (example / 'claim.tex').write_text('1=1.', encoding='utf-8')
            (example / 'proof.tex').write_text('Hence 1=1.', encoding='utf-8')
            config = {'title':'Test', 'entries':[{'id':'claim','title':'Claim','source':'claim.tex','proof':'proof.tex','certificate':'Checked.claim'}]}
            checked = {'schemaVersion':1,'entries':[{'source':'1=1.','proofSource':'Hence 1=1.','certificate':'Checked.claim'}]}
            result = source.reconcile(config, checked, example)
            self.assertEqual(result['entries'][0]['source'], '1=1.')
            (example / 'claim.tex').write_text('1=2.', encoding='utf-8')
            with self.assertRaisesRegex(ValueError, 'differs from editable source'):
                source.reconcile(config, checked, example)
            (example / 'claim.tex').write_text('1=1.', encoding='utf-8')
            (example / 'proof.tex').write_text('Have 0=1. Hence 1=1.', encoding='utf-8')
            with self.assertRaisesRegex(ValueError, 'proofSource differs'):
                source.reconcile(config, checked, example)

    def test_missing_and_duplicate_certificates_are_rejected(self):
        config = {'title':'Test', 'entries':[]}
        record = {'source':'1=1.','proofSource':'','certificate':'Checked.claim'}
        with self.assertRaisesRegex(ValueError, 'match all compiled'):
            source.reconcile(config, {'schemaVersion':1,'entries':[record]}, ROOT)
        with self.assertRaisesRegex(ValueError, 'Duplicate'):
            source.reconcile(config, {'schemaVersion':1,'entries':[record,record]}, ROOT)


if __name__ == '__main__':
    unittest.main()
