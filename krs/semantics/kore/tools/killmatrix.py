#!/usr/bin/env python3
"""Reduce `kink-flow run FLOW.toml MUTATIONS.toml --full` (its JSON document) to the kill matrix.

  kink-flow run FLOW.toml MUTATIONS.toml --full | python3 tools/killmatrix.py > kill-matrix.json

For each mutation, by id: `status` (killed, survived, ...), `killed_by` (every case whose result
on the mutant differs from kore.k's) and `undecided` (the cases on which the mutant's run gave no
comparable result, so that case neither kills nor clears it), each a sorted list of case ids
(the directory names under cases/).
"""
import json
import sys


def case_id(program):
    """cases/<id>/kore.pgm -> <id>"""
    parts = program.split('/')
    return parts[1] if len(parts) == 3 and parts[0] == 'cases' else program


def main():
    run = json.load(sys.stdin)
    undecided = {}
    for program in run['matrix']['programs']:
        for mutation in program['undecided']:
            undecided.setdefault(mutation, []).append(case_id(program['id']))
    matrix = {
        m['id']: {
            'status': m['status'],
            'killed_by': sorted(case_id(p) for p in m['killed_by'] or []),
            'undecided': sorted(undecided.get(m['id'], [])),
        }
        for m in run['mutations']
    }
    json.dump(matrix, sys.stdout, indent=1, sort_keys=True)
    sys.stdout.write('\n')


if __name__ == '__main__':
    main()
