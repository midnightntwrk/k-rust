"""Exercise conformance outcome classification through the actual kast/krun handlers."""
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
sys.path.insert(0, sys.argv.pop(1))
import run

REFERENCE_KAST = '[Error] Inner Parser: Could not find start symbol: Foo provided to kast CLI --sort\n'
RUST_KAST = 'error: could not parse program as Foo with module "TEST": Parse error: unexpected end of file.\n'
REFERENCE_KRUN = '[Error] krun: Configuration variable missing: $Foo. Use -cFoo=<Value> in the command line to set.\n'
RUST_KRUN = 'error: definition has no configuration variable `$A`; available variables: $Foo\n'

def result(rc=0, out='', err='', timeout=False):
    return rc, out, err, 0.01, timeout

class ExpectedErrors(unittest.TestCase):
    def exercise(self, tool, expected, rust, reference=None, recipe=None):
        with tempfile.TemporaryDirectory() as directory:
            case = run.Case('fixture')
            case.dir = directory
            case.log = str(Path(directory) / 'logs')
            case.ref_kompiled = directory
            case.def_file = 'test.k'
            case.main_module = case.syntax_module = 'TEST'
            case.pgm_sort = 'Foo'
            if expected is not None:
                Path(directory, 'input.out').write_text(expected)
            rec = run.split_recipe(f'{run.KBIN}/{tool} input --sort Foo 2>&1 | diff - input.out' if tool == 'kast' else f'{run.KBIN}/{tool} input 2>&1 | diff - input.out')
            def execute(args, *unused, **kw):
                if args[0] == run.KRUST:
                    return rust
                if args[0] == 'bash':
                    return recipe if recipe is not None else result()
                return reference if reference is not None else result(1, err=expected or '')
            with patch.object(run, 'sh', side_effect=execute), patch.object(run, 'run_krust_program', return_value=([run.KRUST], *rust)), patch.object(run, 'compare_execution', return_value=True):
                return run.do_kast(case, rec) if tool == 'kast' else run.do_krun(case, rec)

    def test_expected_rejections_match_the_confirmed_reference_family(self):
        for tool, expected, actual in [('kast', REFERENCE_KAST, RUST_KAST), ('krun', REFERENCE_KRUN, RUST_KRUN)]:
            with self.subTest(tool=tool):
                row = self.exercise(tool, expected, result(1, err=actual))
                self.assertEqual(row['verdict'], 'match', row)
                self.assertEqual(row['reference_tool_rc'], 1)
                self.assertEqual(row['reference_recipe_rc'], 0)

    def test_expected_rejection_is_not_any_nonzero_exit(self):
        for actual in ['compiler failed', 'error: could not load file missing.k', 'thread main panicked', RUST_KRUN]:
            with self.subTest(actual=actual):
                row = self.exercise('kast', REFERENCE_KAST, result(1, err=actual))
                self.assertNotEqual(row['verdict'], 'match', row)

    def test_unknown_reference_diagnostic_is_not_a_match(self):
        row = self.exercise('kast', '[Error] Compiler: unspecified failure\n', result(1, err='compiler failed'))
        self.assertNotEqual(row['verdict'], 'match', row)

    def test_reference_failure_cannot_confirm_rejection(self):
        for reference in [result(-9), result(127, err='not found'), result(1, err='OutOfMemoryError'), result(0), result(1, timeout=True)]:
            with self.subTest(reference=reference):
                row = self.exercise('kast', REFERENCE_KAST, result(1, err=RUST_KAST), reference=reference)
                self.assertEqual(row['verdict'], 'reference-error', row)
        row = self.exercise('kast', REFERENCE_KAST, result(1, err=RUST_KAST), recipe=result(1))
        self.assertEqual(row['verdict'], 'reference-error', row)

    def test_acceptance_is_not_expected_rejection(self):
        row = self.exercise('kast', REFERENCE_KAST, result(0, out='1'))
        self.assertEqual(row['verdict'], 'mismatch', row)

    def test_timeout_and_signal_are_not_rejection(self):
        for rust in [result(1, err=RUST_KAST, timeout=True), result(-9, err=RUST_KAST)]:
            row = self.exercise('kast', REFERENCE_KAST, rust)
            self.assertNotEqual(row['verdict'], 'match', row)

    def test_unexpected_rejection_and_missing_oracle_do_not_match(self):
        for expected in ['1\n', None]:
            row = self.exercise('kast', expected, result(1, err=RUST_KAST))
            self.assertNotEqual(row['verdict'], 'match', row)

    def test_successful_nonzero_program_status_needs_reference_agreement(self):
        row = self.exercise('krun', '1\n', result(111, out='valid kore'), reference=result(111, out='1\n'))
        self.assertEqual(row['verdict'], 'match', row)
        self.assertEqual(row['reference_tool_rc'], 111)
        row = self.exercise('krun', '1\n', result(111, out='valid kore'), reference=result(0, out='1\n'))
        self.assertNotEqual(row['verdict'], 'match', row)

    def test_successful_zero_status_still_matches(self):
        self.assertEqual(self.exercise('kast', '1\n', result(0, out='1\n'))['verdict'], 'match')
        self.assertEqual(self.exercise('krun', '1\n', result(0, out='valid kore'))['verdict'], 'match')

if __name__ == '__main__':
    unittest.main()
