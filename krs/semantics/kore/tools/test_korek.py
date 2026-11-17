#!/usr/bin/env python3
"""Tests of the encoder's attribute checks and of its refusals of a rule or an equation whose
shape kore.k does not hold: python3 tools/test_korek.py (needs no K)."""
import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import korek  # noqa: E402

SRC = '/case/def.k'
# half(X0) = \and(X0 /Int 2, \top) for every X0, as kompile writes an equation
EQ = korek.read_pattern(
    "\\implies{R}(\\and{R}(\\top{R}(), \\and{R}(\\in{SortInt{}, R}(X0:SortInt{}, VarN:SortInt{}), \\top{R}())),"
    " \\equals{SortInt{}, R}(Lblhalf{}(X0:SortInt{}),"
    " \\and{SortInt{}}(Lbl'UndsSlsh'Int'Unds'{}(VarN:SortInt{}, \\dv{SortInt{}}(\"2\")), \\top{SortInt{}}())))")


def encoder(axiom_attrs, half_attrs=None):
    half = (('symbol', ('Lblhalf', (('SortInt', ()),), ('SortInt', ())),
             dict(half_attrs or {'function': True, korek.SOURCE: f'Source({SRC})'})))
    div = (('symbol', ("Lbl'UndsSlsh'Int'Unds'", (('SortInt', ()), ('SortInt', ())), ('SortInt', ())),
            {'function': True, 'hook': 'INT.tdiv', korek.SOURCE: 'Source(/k/int.md)'}))
    ax = ('axiom', EQ, dict(axiom_attrs, **{korek.SOURCE: f'Source({SRC})'}))
    return korek.Encoder([('CASE', [half, div, ax])], SRC)


class AttributeChecks(unittest.TestCase):
    def refused(self, e, text):
        with self.assertRaises(korek.Unsupported) as r:
            e.encode(None)
        self.assertIn(text, str(r.exception))

    def test_simplification_refused(self):
        self.refused(encoder({'simplification': True}),
                     'simplification axiom: not an equation of the definition')

    def test_non_executable_refused(self):
        self.refused(encoder({'non-executable': True}), 'non-executable')

    def test_unknown_axiom_attribute_refused(self):
        self.refused(encoder({'concrete': True}), 'attribute concrete')

    def test_macro_symbol_refused(self):
        e = encoder({}, {'function': True, 'macro': True, korek.SOURCE: f'Source({SRC})'})
        with self.assertRaises(korek.Unsupported) as r:
            e.term(korek.read_pattern('Lblhalf{}(\\dv{SortInt{}}("1"))'))
        self.assertIn('macro: a symbol kompile expands', str(r.exception))

    def test_plain_equation_encoded(self):
        f, c = encoder({}).equation(EQ, {})
        self.assertEqual(f, 'Lblhalf')
        self.assertTrue(c.startswith('cl(50, false, vr(0) ; .Ts, bv(true), hk(4, '))


def source(**attrs):
    return dict(attrs, **{korek.SOURCE: f'Source({SRC})'})


def symbol(name, args, result, **attrs):
    return ('symbol', (name, tuple((a, ()) for a in args), (result, ())), source(**attrs))


SYMBOLS = [symbol('Lblf', (), 'SortT', function=True), symbol('Lblg', ('SortEmpty',), 'SortT', constructor=True),
           symbol('Lblhalf', ('SortInt',), 'SortInt', function=True),
           symbol('Lblpos', ('SortInt',), 'SortBool', function=True),
           symbol('Lbla', (), 'SortS', constructor=True), symbol('Lblb', ('SortInt',), 'SortS', constructor=True),
           symbol("Lbl'-LT-'generatedTop'-GT-'", ('SortKCell', 'SortGeneratedCounterCell'), 'SortGeneratedTopCell',
                  constructor=True),
           symbol("Lbl'-LT-'k'-GT-'", ('SortK',), 'SortKCell', constructor=True)]

# rule f() => g(Y:Empty) [unboundVariables(Y)] as kompile writes it (K 7.1.337): Y stands in the
# right side alone
RIGHT_ONLY = r"""\implies{R} (
    \and{R}(
      \top{R}(),
          \top{R} ()
        ),
    \equals{SortT{},R} (
      Lblf{}(),
     \and{SortT{}} (
       Lblg{}(VarY:SortEmpty{}),
        \top{SortT{}}())))"""


def half(requires='\\top{R}()', right='VarN:SortInt{}', ensures='\\top{SortInt{}}()'):
    """half(X0) = \\and(right, ensures) where X0 is in VarN and the requires holds."""
    return ("\\implies{R}(\\and{R}(" + requires + ", \\and{R}(\\in{SortInt{}, R}(X0:SortInt{}, VarN:SortInt{}), "
            "\\top{R}())), \\equals{SortInt{}, R}(Lblhalf{}(X0:SortInt{}), \\and{SortInt{}}(" + right + ", "
            + ensures + ")))")


def holds(term, sort):
    return "\\equals{SortBool{}, " + sort + "}(" + term + ", \\dv{SortBool{}}(\"true\"))"


def top(item):
    return ("Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortS{}, SortKItem{}}(" + item
            + "), dotk{}())), Var'Unds'DotVar0:SortGeneratedCounterCell{})")


def rewrite(requires='\\top{SortGeneratedTopCell{}}()', item='Lblb{}(\\dv{SortInt{}}("1"))',
            ensures='\\top{SortGeneratedTopCell{}}()', right=None):
    """<k> a() => item </k> with a requires and an ensures, in the shape kompile writes."""
    g = 'SortGeneratedTopCell{}'
    right = right or "\\and{" + g + "}(" + top(item) + ", " + ensures + ")"
    return "\\rewrites{" + g + "}(\\and{" + g + "}(" + top('Lbla{}()') + ", " + requires + "), " + right + ")"


class ShapeChecks(unittest.TestCase):
    """A variable the left side does not bind, a right side under \\exists and a predicate that is
    not `term = true` are refused by name."""

    def refused(self, axiom, *texts):
        e = korek.Encoder([('CASE', SYMBOLS + [('axiom', korek.read_pattern(axiom), source())])], SRC)
        with self.assertRaises(korek.Unsupported) as r:
            e.encode(None)
        for text in texts:
            self.assertIn(text, str(r.exception))

    def test_equation_right_only_variable_refused(self):
        self.refused(RIGHT_ONLY, 'variable VarY of an equation of Lblf: the left side does not bind it')

    def test_equation_requires_variable_refused(self):
        self.refused(half(requires=holds('Lblpos{}(VarM:SortInt{})', 'R')),
                     'variable VarM of an equation of Lblhalf: the left side does not bind it')

    def test_equation_ensures_variable_refused(self):
        self.refused(half(ensures=holds('Lblpos{}(VarM:SortInt{})', 'SortInt{}')),
                     'variable VarM of an equation of Lblhalf: the left side does not bind it')

    def test_rule_requires_variable_refused(self):
        self.refused(rewrite(requires=holds('Lblpos{}(VarX:SortInt{})', 'SortGeneratedTopCell{}')),
                     'variable VarX of a rule: the left side does not bind it')

    def test_rule_ensures_variable_refused(self):
        self.refused(rewrite(ensures=holds('Lblpos{}(VarX:SortInt{})', 'SortGeneratedTopCell{}')),
                     'variable VarX of a rule: the left side does not bind it')

    def test_rule_right_variable_refused(self):
        self.refused(rewrite(item='Lblb{}(VarX:SortInt{})'), 'variable VarX of a rule: the left side does not bind it')

    def test_rule_right_side_under_exists_refused(self):
        g = 'SortGeneratedTopCell{}'
        body = "\\and{" + g + "}(" + top("Lblb{}(Var'Ques'X:SortInt{})") + ", \\top{" + g + "}())"
        self.refused(rewrite(right="\\exists{" + g + "}(Var'Ques'X:SortInt{}, " + body + ")"),
                     'right side of a rule under \\exists')

    def test_equation_right_side_under_exists_refused(self):
        ax = half().replace("\\and{SortInt{}}(VarN:SortInt{}, \\top{SortInt{}}())",
                            "\\exists{SortInt{}}(VarM:SortInt{}, \\and{SortInt{}}(VarM:SortInt{}, \\top{SortInt{}}()))")
        self.refused(ax, 'right side of an equation of Lblhalf under \\exists')

    def test_requires_predicate_refused(self):
        self.refused(half(requires='\\ceil{SortInt{}, R}(VarN:SortInt{})'), 'requires shape')

    def test_ensures_predicate_refused(self):
        self.refused(half(ensures='\\ceil{SortInt{}, SortInt{}}(VarN:SortInt{})'), 'ensures shape')

    def test_bound_variables_encoded(self):
        e = korek.Encoder([('CASE', SYMBOLS)], SRC)
        ax = half(requires=holds('Lblpos{}(VarN:SortInt{})', 'R'),
                  ensures=holds('Lblpos{}(VarN:SortInt{})', 'SortInt{}'))
        f, c = e.equation(korek.read_pattern(ax), {})
        self.assertEqual((f, c), ('Lblhalf', 'cl(50, false, vr(0) ; .Ts, ap(1, vr(0) ; .Ts), '
                                  'en(vr(0), ap(1, vr(0) ; .Ts)), '))
        r = e.rule(korek.read_pattern(rewrite()), {})
        self.assertTrue(r.startswith('rl(50, false, ij('), r)


if __name__ == '__main__':
    unittest.main()
