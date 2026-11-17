#!/usr/bin/env python3
"""Tests of check.py's pass rule on hand-built entries: python3 tools/test_check.py
(needs no K and no krust: kore.k's result is given, not computed)."""
import contextlib
import hashlib
import io
import json
import os
import sys
import tempfile
import tomllib
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import check  # noqa: E402

B0, B1, C0 = 'b(0)', 'b(1)', 'c(0)'

HEAD = '''id = "{id}"
kind = "{kind}"
subject = "A hand-built entry."
{rests}
[text]
files = [{files}]
kompile = "accepts"
'''
BASIS = '''
[[ruling.basis]]
source = "manual"
locator = "docs/user_manual.md:1"
quote = "A sentence."
'''
SETTLED = '''
[ruling]
status = "settled"
finals = ["b(1)"]
reason = "The rule of the least priority number gives b(1), by the sentence quoted."
''' + BASIS
UNSETTLED = '''
[ruling]
status = "unsettled"
reason = "The sentence quoted does not say whether an empty result is an application."
interpreter = "{interpreter}"
''' + BASIS + '''
[[reading]]
name = "blocks"
statement = "An empty result is an application."
finals = ["b(1)"]
consequence = "a(0) has no successor."

[[reading]]
name = "passes"
statement = "An empty result is a failure."
finals = ["b(1)", "c(0)"]
consequence = "a(0) steps to c(0)."
'''
PENDING = '''
[ruling]
status = "pending"
'''
TEXT_RULING = '''
[ruling]
status = "settled"
form = "means"
statement = "The sentence denotes a rewrite at the top."
reason = "By the sentence quoted."
''' + BASIS


def rewrite(path, text):
    with open(path, 'w') as f:
        f.write(text)


def disposition(impl, how='difference'):
    return f'\n[[disposition]]\nimplementation = "{impl}"\nis = "{how}"\nreason = "Why it differs."\n'


def finals(*fs):
    return {'finals': sorted(fs)}


class Package:
    """A package directory of hand-built entries."""

    def __init__(self, root):
        self.root = root

    def entry(self, cid, body, implementations=None, kind='case', rests='', evidence=True, canon=None):
        d = os.path.join(self.root, check.KIND_DIR[kind], cid)
        os.makedirs(d)
        names = ['def.k', 'pgm'] if kind == 'case' else [cid + '.k']
        for n in names:
            with open(os.path.join(d, n), 'w') as f:
                f.write(f'// {n} of {cid}\n')
        head = HEAD.format(id=cid, kind=kind, rests=rests, files=', '.join(f'"{n}"' for n in names))
        with open(os.path.join(d, 'entry.toml'), 'w') as f:
            f.write(head + body)
        if evidence:
            self.evidence(d, implementations or {}, canon)
        return d

    def evidence(self, d, implementations, canon=None):
        """evidence.json as tools/case.py is to write it: the present hashes, the ruling's finals as
        their own canonical text."""
        with open(os.path.join(d, 'entry.toml'), 'rb') as f:
            entry = tomllib.load(f)
        with open(os.path.join(d, 'kore.txt'), 'w') as f:
            f.write('axiom{} \\rewrites{SortS{}}(a, b)\n')
        inputs = {n: check.sha(os.path.join(d, n)) for n in entry['text']['files']}
        inputs['answer'] = check.answer_hash(entry)
        if canon is None:
            canon = {}
            if 'finals' in entry['ruling']:
                canon['settled'] = sorted(entry['ruling']['finals'])
            if entry.get('reading'):
                canon['readings'] = {r['name']: sorted(r['finals']) for r in entry['reading'] if 'finals' in r}
        ev = {'inputs': inputs,
              'kompile': {'release': 'K', 'command': 'kompile', 'exit': 0, 'message': None,
                          'kore.txt': check.sha(os.path.join(d, 'kore.txt'))},
              'ruling_canonical': canon, 'implementations': implementations}
        with open(os.path.join(d, 'evidence.json'), 'w') as f:
            json.dump(ev, f)

    def check(self, d, live=None):
        ok, line, _, differing = check.check_entry(d, check.index_of(self.root), live)
        return ok, line, differing


class PassRule(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.p = Package(tmp.name)

    def passes(self, d, text='', **kw):
        ok, line, differing = self.p.check(d, **kw)
        self.assertTrue(ok, line)
        self.assertIn(text, line)
        return differing

    def fails(self, d, cause, text='', **kw):
        ok, line, _ = self.p.check(d, **kw)
        self.assertFalse(ok, line)
        self.assertIn(f'FAIL {cause}: ', line)
        self.assertIn(text, line)

    # the two passing forms

    def test_pass_every_result_is_the_ruling(self):
        d = self.p.entry('c01-x', SETTLED, {'haskell': finals(B1), 'llvm': finals(B1)})
        self.assertEqual(self.passes(d, 'ok settled haskell:= kore.k:= llvm:=', live=finals(B1)), [])

    def test_pass_a_difference_with_its_disposition(self):
        d = self.p.entry('c01-x', SETTLED + disposition('llvm') + disposition('kore.k'),
                         {'haskell': finals(B1), 'llvm': {'error': 'abort'}})
        self.assertEqual(self.passes(d, 'haskell:= kore.k:differs llvm:differs', live=finals(B0)),
                         ['kore.k', 'llvm'])

    def test_pass_no_run_checks_the_stored_results(self):
        d = self.p.entry('c01-x', SETTLED + disposition('kore.k'), {'haskell': finals(B1)})
        self.passes(d, 'ok settled haskell:=')

    # cause 1: schema fault

    def test_schema_does_not_parse(self):
        d = self.p.entry('c01-x', SETTLED + '\n[ruling\n', evidence=False)
        self.fails(d, 'schema', 'does not parse')

    def test_schema_required_field(self):
        d = self.p.entry('c01-x', SETTLED.replace('finals = ["b(1)"]\n', ''), {})
        self.fails(d, 'schema', 'a settled case needs finals')

    def test_schema_no_basis(self):
        d = self.p.entry('c01-x', SETTLED.replace(BASIS, ''), {})
        self.fails(d, 'schema', 'ruling: no basis')

    def test_schema_basis_source(self):
        d = self.p.entry('c01-x', SETTLED.replace('source = "manual"', 'source = "tutorial"'), {'haskell': finals(B1)})
        self.passes(d, 'ok settled')
        d = self.p.entry('c02-x', SETTLED.replace('source = "manual"', 'source = "lecture"'), {})
        self.fails(d, 'schema', 'source is not one of')

    def test_schema_basis_without_quote(self):
        d = self.p.entry('c01-x', SETTLED.replace('quote = "A sentence."\n', ''), {})
        self.fails(d, 'schema', 'no locator or no quote')

    def test_schema_reason_names_an_implementation(self):
        words = ('Haskell', 'llvm', 'krust', 'KCore', 'backend', 'docs/compatibility.md')
        for i, word in enumerate(words):
            with self.subTest(word=word):
                d = self.p.entry(f'c1{i}-x', SETTLED.replace('by the sentence', f'as {word} has it, by the sentence'), {})
                self.fails(d, 'schema', 'ruling.reason names an implementation')

    def test_schema_unsettled_with_one_reading(self):
        body = UNSETTLED.format(interpreter='blocks')
        d = self.p.entry('c01-x', body[:body.index('[[reading]]\nname = "passes"')], {})
        self.fails(d, 'schema', 'at least two readings')

    def test_schema_reading_without_consequence(self):
        d = self.p.entry('c01-x', UNSETTLED.format(interpreter='blocks').replace('consequence = "a(0) steps to c(0)."\n', ''), {})
        self.fails(d, 'schema', 'reading[1] needs a consequence')

    def test_schema_reading_without_answer(self):
        d = self.p.entry('c01-x', UNSETTLED.format(interpreter='blocks').replace('finals = ["b(1)", "c(0)"]\n', ''), {})
        self.fails(d, 'schema', 'reading[1] needs one answer')

    def test_schema_unsettled_case_without_interpreter(self):
        d = self.p.entry('c01-x', UNSETTLED.replace('interpreter = "{interpreter}"\n', ''), {})
        self.fails(d, 'schema', 'an unsettled case needs interpreter')

    def test_schema_outside_without_disposition(self):
        d = self.p.entry('c01-x', UNSETTLED.format(interpreter='outside'), {})
        self.fails(d, 'schema', 'needs a disposition for kore.k')

    def test_schema_settled_rests_on_unsettled(self):
        self.p.entry('c02-y', UNSETTLED.format(interpreter='blocks'), {})
        d = self.p.entry('c01-x', SETTLED, {}, rests='rests_on = ["kk:c02-y"]')
        self.fails(d, 'schema', 'a settled entry rests on kk:c02-y, which is unsettled')

    def test_schema_rests_on_no_entry(self):
        d = self.p.entry('c01-x', SETTLED, {}, rests='rests_on = ["kk:t09-absent"]')
        self.fails(d, 'schema', 'kk:t09-absent names no entry')

    def test_schema_kompile_against_the_evidence(self):
        d = self.p.entry('c01-x', SETTLED, {})
        path = os.path.join(d, 'entry.toml')
        text = check.read_text(path).replace('kompile = "accepts"', 'kompile = "rejects"')
        rewrite(path, text)
        self.p.evidence(d, {})
        self.fails(d, 'schema', 'text.kompile is rejects and kompile exited 0')

    def test_schema_pending_is_no_status(self):
        d = self.p.entry('c01-x', PENDING, {'haskell': finals(B1)})
        self.fails(d, 'schema', 'ruling.status is not one of settled, unsettled', live=finals(B1))

    def test_schema_observe_pointer(self):
        seen = '\n[[observe]]\nfile = "kore.txt"\ncontains = "\\\\rewrites"\n'
        gone = '\n[[observe]]\nfile = "kore.txt"\nabsent = "\\\\rewrites"\n'
        self.passes(self.p.entry('t01-x', TEXT_RULING + seen, kind='text'), 'ok settled')
        self.fails(self.p.entry('t02-x', TEXT_RULING + gone, kind='text'), 'schema', 'observe: kore.txt contains')

    # cause 2: stale

    def test_stale_text_changed(self):
        d = self.p.entry('c01-x', SETTLED, {'haskell': finals(B1)})
        with open(os.path.join(d, 'def.k'), 'a') as f:
            f.write('// changed\n')
        self.fails(d, 'stale', 'def.k changed since evidence.json')

    def test_stale_answer_changed(self):
        d = self.p.entry('c01-x', SETTLED, {'haskell': finals(B1)})
        path = os.path.join(d, 'entry.toml')
        text = check.read_text(path)
        rewrite(path, text.replace('finals = ["b(1)"]', 'finals = ["b(0)"]'))
        self.fails(d, 'stale', 'answer changed since evidence.json')

    def test_not_stale_when_a_reason_or_a_disposition_changes(self):
        d = self.p.entry('c01-x', SETTLED, {'haskell': finals(B1), 'llvm': finals(B0)})
        path = os.path.join(d, 'entry.toml')
        text = check.read_text(path).replace('by the sentence quoted', 'by the sentence quoted below')
        rewrite(path, text + disposition('llvm'))
        self.passes(d, 'haskell:= llvm:differs')

    def test_stale_kore_txt_changed(self):
        d = self.p.entry('c01-x', SETTLED, {'haskell': finals(B1)})
        with open(os.path.join(d, 'kore.txt'), 'a') as f:
            f.write('axiom{} \\top{}()\n')
        self.fails(d, 'stale', 'kore.txt changed since evidence.json')

    def test_stale_no_evidence(self):
        d = self.p.entry('c01-x', SETTLED, evidence=False)
        self.fails(d, 'stale', 'no evidence.json')

    def test_stale_no_kompile_record(self):
        d = self.p.entry('c01-x', SETTLED, {'haskell': finals(B1)})
        path = os.path.join(d, 'evidence.json')
        ev = json.loads(check.read_text(path))
        del ev['kompile']
        rewrite(path, json.dumps(ev))
        self.fails(d, 'stale', 'evidence.json records no kompile run', live=finals(B1))

    # cause 3: an unrecorded or an outlived difference

    def test_differs_unrecorded(self):
        d = self.p.entry('c01-x', SETTLED, {'haskell': finals(B1), 'llvm': finals(B0, B1)})
        self.fails(d, 'differs', 'is not the ruling and no disposition names llvm')

    def test_differs_unrecorded_error(self):
        d = self.p.entry('c01-x', SETTLED, {'llvm': {'error': 'abort'}})
        self.fails(d, 'differs', 'llvm=error: abort is not the ruling')

    def test_differs_unrecorded_interpreter(self):
        d = self.p.entry('c01-x', SETTLED, {'haskell': finals(B1)})
        self.fails(d, 'differs', 'no disposition names kore.k', live=finals())

    def test_differs_outlived(self):
        d = self.p.entry('c01-x', SETTLED + disposition('llvm'), {'haskell': finals(B1), 'llvm': finals(B1)})
        self.fails(d, 'differs', 'a disposition names llvm, whose result is the ruling')

    def test_differs_disposition_without_result(self):
        d = self.p.entry('c01-x', SETTLED + disposition('llvm'), {'haskell': finals(B1)})
        self.fails(d, 'differs', 'a disposition names llvm, of which no result is recorded')

    # an unsettled entry

    def unsettled(self, extra='', interpreter='blocks', **implementations):
        return self.p.entry('c01-x', UNSETTLED.format(interpreter=interpreter) + extra, implementations)

    def test_unsettled_pass_each_result_a_reading(self):
        d = self.unsettled(haskell=finals(B1), other=finals(B1, C0))
        self.assertEqual(self.passes(d, 'ok unsettled haskell:reading:blocks kore.k:reading:blocks other:reading:passes',
                                     live=finals(B1)), [])

    def test_unsettled_no_reading_unrecorded(self):
        d = self.unsettled(llvm=finals(B0, B1))
        self.fails(d, 'differs', 'is no reading and no disposition names llvm')

    def test_unsettled_difference_recorded(self):
        d = self.unsettled(disposition('llvm'), llvm=finals(B0, B1))
        self.assertEqual(self.passes(d, 'llvm:differs'), ['llvm'])

    def test_unsettled_difference_outlived(self):
        d = self.unsettled(disposition('llvm'), llvm=finals(B1, C0))
        self.fails(d, 'differs', 'its result is the reading passes')

    def test_unsettled_interpreter_not_its_reading(self):
        d = self.unsettled(haskell=finals(B1))
        self.fails(d, 'differs', 'is not the reading blocks, which interpreter names', live=finals(B1, C0))

    def test_unsettled_outside_coincides(self):
        d = self.unsettled(disposition('kore.k', 'coincides:passes'), interpreter='outside', haskell=finals(B1))
        self.assertEqual(self.passes(d, 'kore.k:coincides:passes', live=finals(B1, C0)), ['kore.k'])
        self.fails(d, 'differs', 'does not equal the finals of passes', live=finals(B1))

    def test_unsettled_reading_form_is_not_compared(self):
        d = self.unsettled(disposition('haskell', 'reading:blocks'), haskell=finals('b(1) if defined(x)'))
        self.assertEqual(self.passes(d, 'haskell:reading:blocks'), [])

    def test_unsettled_disposition_names_no_reading(self):
        d = self.unsettled(disposition('llvm', 'coincides:absent'), llvm=finals(B1))
        self.fails(d, 'schema', 'names no reading')

    # the command, without a run

    def test_command_no_run(self):
        self.p.entry('c01-x', SETTLED + disposition('llvm'), {'haskell': finals(B1), 'llvm': finals(B0)})
        self.p.entry('c02-y', UNSETTLED.format(interpreter='blocks'), {'haskell': finals(B1)})
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = check.main(['--no-run'], package=self.p.root)
        self.assertEqual(code, 0, out.getvalue())
        self.assertIn('PASS kore-in-k: 2 of 2 entries pass (1 settled, 1 unsettled); '
                      'recorded differences: llvm 1;', out.getvalue())
        with self.assertRaises(SystemExit):
            check.main(['--no-run', '--allow-pending'], package=self.p.root)

    def test_answer_hash_reads_the_answer_fields_only(self):
        d = self.p.entry('c01-x', SETTLED, {})
        with open(os.path.join(d, 'entry.toml'), 'rb') as f:
            entry = tomllib.load(f)
        text = '{"finals":["b(1)"],"finals_canonical":null,"kompile":"accepts","readings":[]}'
        self.assertEqual(check.answer_hash(entry), hashlib.sha256(text.encode()).hexdigest())

    # the ruling hash a rows.toml row of kcore-spec cites (check.py --ruling-sha)

    def test_ruling_hash_reads_the_ruling_and_the_readings_only(self):
        d = self.p.entry('c01-x', UNSETTLED.format(interpreter='blocks'), {})
        with open(os.path.join(d, 'entry.toml'), 'rb') as f:
            entry = tomllib.load(f)
        text = json.dumps({'ruling': entry['ruling'], 'reading': entry['reading']}, sort_keys=True,
                          separators=(',', ':'), ensure_ascii=False)
        h = check.ruling_hash(entry)
        self.assertEqual(h, hashlib.sha256(text.encode()).hexdigest())
        # a disposition, a note or the subject leaves it; a basis or a reading's consequence moves it
        same = dict(entry, subject='Another subject.', disposition=[{'implementation': 'llvm'}],
                    note=[{'implementation': 'llvm', 'text': 'x'}])
        self.assertEqual(check.ruling_hash(same), h)
        moved = json.loads(json.dumps(entry))
        moved['ruling']['basis'][0]['quote'] = 'Another sentence.'
        self.assertNotEqual(check.ruling_hash(moved), h)
        moved = json.loads(json.dumps(entry))
        moved['reading'][1]['consequence'] = 'Another consequence.'
        self.assertNotEqual(check.ruling_hash(moved), h)

    def test_command_ruling_sha(self):
        d = self.p.entry('t01-x', TEXT_RULING, {}, kind='text')
        with open(os.path.join(d, 'entry.toml'), 'rb') as f:
            h = check.ruling_hash(tomllib.load(f))
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = check.main(['--ruling-sha', 'kk:t01-x', 't01-x'], package=self.p.root)
        self.assertEqual(code, 0)
        self.assertEqual(out.getvalue(), f't01-x {h}\nt01-x {h}\n')
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(check.main(['--ruling-sha', 't02-none'], package=self.p.root), 1)


if __name__ == '__main__':
    unittest.main()
