#!/usr/bin/env python3
"""Tests of the encoder's attribute checks: python3 tools/test_korek.py (needs no K)."""
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


if __name__ == '__main__':
    unittest.main()
