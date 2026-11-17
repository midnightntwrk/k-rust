#!/usr/bin/env python3
"""Tests of MUTATIONS.toml as a record: python3 tools/test_mutations.py (needs no K and no kink).

Every mutation is killed (kill-matrix.json, kink.lock) or marked equivalent with its argument, and
every one names the premises of kore.k's reading it breaks."""
import json
import os
import re
import sys
import tomllib
import unittest

PACKAGE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PREMISE_LINE = re.compile(r'#   ([a-z-]+): \S')
PREMISE_TAG = re.compile(r' \[premise: ([a-z-]+(?:, [a-z-]+)*)\]\Z')
# premises without a rule of their own in kore.k (MUTATIONS.toml's header says why)
UNMUTATED = {'total'}


def read(name):
    with open(os.path.join(PACKAGE, name), 'rb') as f:
        return f.read().decode()


class Mutations(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        text = read('MUTATIONS.toml')
        header = text[:text.index('[[mutation]]')]
        cls.premises = [m.group(1) for m in map(PREMISE_LINE.match, header.split('\n')) if m]
        cls.mutations = tomllib.loads(text)['mutation']
        cls.matrix = json.loads(read('kill-matrix.json'))
        cls.lock = {m['id']: m for m in tomllib.loads(read('kink.lock'))['run']['mutation']}

    def premises_of(self, mutation):
        tag = PREMISE_TAG.search(mutation['misunderstanding'])
        self.assertIsNotNone(tag, f'{mutation["id"]}: no [premise: ...] at the end of its misunderstanding')
        return tag.group(1).split(', ')

    def test_premises_listed(self):
        self.assertEqual(len(self.premises), 16)
        self.assertEqual(len(set(self.premises)), 16)

    def test_each_mutation_names_its_premises(self):
        for m in self.mutations:
            for p in self.premises_of(m):
                self.assertIn(p, self.premises, f'{m["id"]}: {p} is no premise of the header')

    def test_each_premise_has_a_mutation(self):
        broken = {p for m in self.mutations for p in self.premises_of(m)}
        self.assertEqual(set(self.premises) - broken, UNMUTATED)

    def test_each_mutation_killed_or_marked_equivalent(self):
        self.assertEqual(sorted(self.matrix), sorted(m['id'] for m in self.mutations))
        self.assertEqual(sorted(self.lock), sorted(self.matrix))
        for m in self.mutations:
            row, locked = self.matrix[m['id']], self.lock[m['id']]
            self.assertEqual(row['status'], locked['status'], m['id'])
            if row['status'] == 'killed':
                self.assertTrue(row['killed_by'], m['id'])
                self.assertIn(locked['killer'].split('/')[1], row['killed_by'], m['id'])
                self.assertNotEqual(m.get('expect'), 'survive', m['id'])
            else:
                self.assertEqual((row['status'], m.get('expect')), ('survived', 'survive'), m['id'])
                self.assertIn('Equivalent on every consistent object definition, by this argument: ',
                              m['misunderstanding'], m['id'])


if __name__ == '__main__':
    unittest.main()
