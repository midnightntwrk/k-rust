#!/usr/bin/env python3
"""Tests of case.py that need no K: python3 tools/test_case.py. kompile and kast are stood in for
by a runner that writes a given kompiled text or refuses, as kompile does."""
import json
import os
import shutil
import sys
import tempfile
import unittest
import unittest.mock

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import case  # noqa: E402
import check  # noqa: E402

SRC = "org'Stop'kframework'Stop'attributes'Stop'Source"
LOC = "org'Stop'kframework'Stop'attributes'Stop'Location"
KOMPILED = f'''[topCellInitializer{{}}(LblinitGeneratedTopCell{{}}())]

module BASIC-K
endmodule []

module MAIN
// sorts
  sort SortFoo{{}} [{LOC}{{}}("Location(3,3,3,20)"), {SRC}{{}}("Source(/abs/src/t.k)")]
  hooked-sort SortInt{{}} [hook{{}}("INT.Int"), {SRC}{{}}("Source(/nix/store/x/include/kframework/builtin/domains.md)")]
  symbol LblisFoo{{}}(SortK{{}}) : SortBool{{}} [function{{}}()]

// rules
// rule f(_Gen7)=>_Gen7 [UNIQUE_ID(1), org.kframework.attributes.Location(Location(4,3,4,20)), org.kframework.attributes.Source(Source(/abs/src/t.k))]
  axiom{{}} \\equals{{SortFoo{{}}, R}} (
    Lblf{{}}(Var'Unds'Gen7:SortFoo{{}}),
    Var'Unds'Gen7:SortFoo{{}}) [UNIQUE'Unds'ID{{}}("1"), {SRC}{{}}("Source(/abs/src/t.k)")]
  symbol LblShared{{}}() : SortK{{}} []
endmodule []
'''
EMPTY = '''[]

module EMPTY-MODULE
  symbol LblShared{}() : SortK{} []
endmodule []
'''
ADDED = '''//@ 1
  sort SortFoo{} []
//@ 3
  symbol LblisFoo{}(SortK{}) : SortBool{} [function{}()]
//@ 4
// rule f(_Gen0)=>_Gen0 [UNIQUE_ID(1)]
  axiom{} \\equals{SortFoo{}, R} (
    Lblf{}(Var'Unds'Gen0:SortFoo{}),
    Var'Unds'Gen0:SortFoo{}) [UNIQUE'Unds'ID{}("1")]
'''

TEXT_ENTRY = '''id = "{id}"
kind = "text"
subject = "A hand-built text entry."

[text]
files = ["{id}.k"]
kompile = "{kompile}"

[ruling]
status = "settled"
form = "means"
statement = "A hand-built statement."
reason = "By the sentence quoted."

[[ruling.basis]]
source = "manual"
locator = "docs/manual.md:1 (K 7.1.337)"
quote = "one"
'''


class FakeRunner:
    """kompile writes KOMPILED (EMPTY for the empty module) or refuses with a message naming the
    absolute path of the text; it counts its runs."""

    def __init__(self, refuse=False):
        self.refuse = refuse
        self.kompiles = 0

    def tool(self, name):
        return '/k/bin/' + name

    def installation(self):
        return '/k/bin/kompile'

    def release(self):
        return 'K v0'

    def kompile(self, args, cwd):
        self.kompiles += 1
        if 'empty-module.k' in args:
            text = EMPTY
        elif self.refuse:
            return 113, f'[Error] Compiler: refused.\n\tSource({cwd}/{args[2]})\n'
        else:
            text = KOMPILED
        os.makedirs(os.path.join(cwd, 'out'), exist_ok=True)
        with open(os.path.join(cwd, 'out', 'definition.kore'), 'w') as f:
            f.write(text)
        return 0, '[Warning] Compiler: a warning.\n'


class Base(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = tmp.name
        self.build_dir = os.path.join(self.root, 'build')
        self.saved, case.BUILD = case.BUILD, self.build_dir
        self.addCleanup(setattr, case, 'BUILD', self.saved)

    def text_entry(self, tid, kompile='accepts', entry=True):
        d = os.path.join(self.root, 'texts', tid)
        os.makedirs(d)
        with open(os.path.join(d, tid + '.k'), 'w') as f:
            f.write('module T\nendmodule\n')
        if entry:
            with open(os.path.join(d, 'entry.toml'), 'w') as f:
                f.write(TEXT_ENTRY.format(id=tid, kompile=kompile))
        return d

    def build(self, d, runner, imported=None):
        return case.build(d, runner, {'refresh': False, 'no_backends': False}, imported or {})

    def files(self, d):
        return sorted(os.listdir(d))


class Kore(Base):
    def test_added_sentences(self):
        n, added = case.added_sentences(KOMPILED, EMPTY)
        self.assertEqual(n, 7)
        self.assertEqual(''.join(s + '\n' for s in added), ADDED)

    def test_renumbered_each_spelling_from_zero(self):
        self.assertEqual(case.renumbered("_Gen4 Var'Unds'Gen9 _Gen2 _Gen4 Var'Unds'Gen3"),
                         "_Gen0 Var'Unds'Gen0 _Gen1 _Gen0 Var'Unds'Gen1")


class Build(Base):
    def test_refuses_without_entry_toml(self):
        d = self.text_entry('t01-x', entry=False)
        with self.assertRaises(case.Refused) as err:
            self.build(d, FakeRunner())
        self.assertIn('no entry.toml', str(err.exception))
        self.assertEqual(self.files(d), ['t01-x.k'])

    def test_text_accepted(self):
        d = self.text_entry('t01-x')
        with open(os.path.join(d, 'entry.toml'), 'rb') as f:
            before = f.read()
        _, ev, notes = self.build(d, FakeRunner())
        self.assertEqual(notes, [])
        with open(os.path.join(d, 'entry.toml'), 'rb') as f:
            self.assertEqual(f.read(), before)
        self.assertEqual(self.files(d), ['entry.toml', 'evidence.json', 'kompile.txt', 'kore.txt', 't01-x.k'])
        with open(os.path.join(d, 'kore.txt')) as f:
            self.assertEqual(f.read(), ADDED)
        self.assertEqual(ev['kompile'], {'release': 'K v0', 'exit': 0, 'message': None,
                                         'command': "kompile --backend haskell t01-x.k -o out  "
                                                    "(cwd: a copy of the entry's directory)",
                                         'kore.txt': check.sha(os.path.join(d, 'kore.txt'))})
        self.assertNotIn('ruling_canonical', ev)
        ok, line, _, _ = check.check_entry(d, {'t01-x': 'settled'}, None)
        self.assertTrue(ok, line)

    def test_text_refused_is_a_result(self):
        d = self.text_entry('t01-x', kompile='rejects')
        with open(os.path.join(d, 'kore.txt'), 'w') as f:
            f.write('left from an earlier build\n')
        _, ev, notes = self.build(d, FakeRunner(refuse=True))
        self.assertEqual(notes, [])
        self.assertNotIn('kore.txt', self.files(d))
        self.assertEqual(ev['kompile']['exit'], 113)
        self.assertEqual(ev['kompile']['message'], '[Error] Compiler: refused.\n\tSource(t01-x.k)')
        with open(os.path.join(d, 'kompile.txt')) as f:
            text = f.read()
        self.assertIn('exit: 113\n', text)
        self.assertNotIn(self.root, text + json.dumps(ev))
        ok, line, _, _ = check.check_entry(d, {'t01-x': 'settled'}, None)
        self.assertTrue(ok, line)

    def test_unexpected_kompile_result_is_written_and_reported(self):
        d = self.text_entry('t01-x', kompile='accepts')
        _, ev, notes = self.build(d, FakeRunner(refuse=True))
        self.assertEqual(notes, ['UNEXPECTED: text.kompile is accepts and kompile exited 113'])
        self.assertEqual(ev['kompile']['exit'], 113)
        ok, line, _, _ = check.check_entry(d, {'t01-x': 'settled'}, None)
        self.assertFalse(ok)
        self.assertIn('text.kompile is accepts and kompile exited 113', line)

    def test_kompile_cached_by_the_text(self):
        d = self.text_entry('t01-x')
        runner = FakeRunner()
        self.build(d, runner)
        self.build(d, runner)
        self.assertEqual(runner.kompiles, 2)  # the empty module, then the text once
        with open(os.path.join(d, 't01-x.k'), 'a') as f:
            f.write('// changed\n')
        self.build(d, runner)
        self.assertEqual(runner.kompiles, 3)

    def test_import_kcore_and_keep_while_current(self):
        d = self.text_entry('t01-x')
        path = os.path.join(self.root, 'kcore.json')
        with open(path, 'w') as f:
            json.dump({'version': 'kcore-spec abc, kcore oracle', 'results': {'t01-x': {'finals': ['b', 'a']}}}, f)
        rows = case.read_import('kcore=' + path)
        _, ev, _ = self.build(d, FakeRunner(), rows)
        self.assertEqual(ev['implementations']['kcore'],
                         {'version': 'kcore-spec abc, kcore oracle', 'finals': ['a', 'b'],
                          'imported_from': check.sha(path)})
        _, ev, _ = self.build(d, FakeRunner())
        self.assertIn('kcore', ev['implementations'])
        with open(os.path.join(d, 't01-x.k'), 'a') as f:
            f.write('// changed\n')
        _, ev, _ = self.build(d, FakeRunner())
        self.assertEqual(ev['implementations'], {})


class Canonical(unittest.TestCase):
    ARITIES = {'inj': 1, 'kseq': 2, 'dotk': 0, "Lbl'-LT-'t'-GT-'": 2, "Lbl'-LT-'k'-GT-'": 1,
               "Lbl'-LT-'n'-GT-'": 1, 'Lblb': 1}

    def canon(self, text, top='SortKCell'):
        return case.canonical_of_kast(text, top, self.ARITIES, {})

    def test_one_cell(self):
        self.assertEqual(self.canon('inj{SortS{}, SortKItem{}}(Lblb{}(\\dv{SortInt{}}("1")))'),
                         'inj{SortS,SortKItem}(Lblb(1))')

    def test_several_cells(self):
        text = ("kseq{}(inj{SortTCell{}, SortKItem{}}(Lbl'-LT-'t'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}("
                "inj{SortS{}, SortKItem{}}(Lblb{}(\\dv{SortInt{}}(\"1\"))),dotk{}())),"
                "Lbl'-LT-'n'-GT-'{}(\\dv{SortInt{}}(\"2\")))),dotk{}())")
        self.assertEqual(self.canon(text, 'SortTCell'),
                         "Lbl'-LT-'t'-GT-'(Lbl'-LT-'k'-GT-'(kseq(inj{SortS,SortKItem}(Lblb(1)),dotk())),"
                         "Lbl'-LT-'n'-GT-'(2))")

    def test_variable_refused(self):
        with self.assertRaisesRegex(ValueError, 'variable VarX'):
            self.canon('inj{SortS{}, SortKItem{}}(Lblb{}(VarX:SortInt{}))')

    def test_arity_refused(self):
        text = "kseq{}(inj{SortTCell{}, SortKItem{}}(Lbl'-LT-'t'-GT-'{}(Lbl'-LT-'k'-GT-'{}(dotk{}()))),dotk{}())"
        with self.assertRaisesRegex(ValueError, "applied to 1 arguments, declared with 2"):
            self.canon(text, 'SortTCell')


class Quotes(Base):
    def setUp(self):
        super().setUp()
        self.k = os.path.join(self.root, 'k')
        for rel, text in (('package/version', '7.1.337\n'),
                          ('docs/manual.md', 'one\nA sentence that\nruns over  two lines.\nfour\n'),
                          ('haskell-backend/src/main/native/haskell-backend/docs/kore.md', 'x\nKORE line\n')):
            os.makedirs(os.path.dirname(os.path.join(self.k, rel)), exist_ok=True)
            with open(os.path.join(self.k, rel), 'w') as f:
                f.write(text)

    def entry(self, *bases):
        d = self.text_entry('t01-x')
        with open(os.path.join(d, 'kore.txt'), 'w') as f:
            f.write('//@ 0\n  axiom{} a\n')
        with open(os.path.join(d, 'entry.toml'), 'a') as f:
            for source, locator, quote in bases:
                f.write(f'\n[[ruling.basis]]\nsource = "{source}"\nlocator = "{locator}"\nquote = "{quote}"\n')
        return d

    def verify(self, *bases):
        d = self.entry(*bases)
        out = []
        with unittest.mock.patch('builtins.print', lambda s: out.append(s)):
            code = case.verify_quotes([d], self.k)
        return code, '\n'.join(out)

    def test_quotes_at_their_locators(self):
        code, out = self.verify(('manual', 'docs/manual.md:2-3 (K 7.1.337)', 'A sentence that runs over two lines.'),
                                ('manual', 'docs/manual.md:1, 4', 'one ... four'),
                                ('kore-syntax', 'haskell-backend/docs/kore.md:2', 'KORE line'),
                                ('kompiled', 'kore.txt:2', 'axiom{} a'))
        self.assertEqual(code, 0, out)
        self.assertIn('t01-x: ok, 5 quote(s)', out)

    def test_quote_not_at_its_locator(self):
        for basis, why in ((('manual', 'docs/manual.md:3', 'A sentence that'), 'not at docs/manual.md:3'),
                           (('manual', 'docs/manual.md:1, 4', 'four ... one'), 'not at'),
                           (('manual', 'docs/manual.md:2 (K 7.1.336)', 'A sentence'), 'names K 7.1.336'),
                           (('manual', 'docs/none.md:2', 'A sentence'), 'no file docs/none.md'),
                           (('manual', 'docs/manual.md:9', 'A sentence'), 'has 5 lines'),
                           (('manual', 'docs/manual.md', 'A sentence'), 'the locator is not')):
            with self.subTest(basis=basis):
                self.tearDown_entry()
                code, out = self.verify(basis)
                self.assertEqual(code, 1, out)
                self.assertIn(why, out)

    def tearDown_entry(self):
        shutil.rmtree(os.path.join(self.root, 'texts'), ignore_errors=True)


if __name__ == '__main__':
    unittest.main()
