#!/usr/bin/env python3
"""SIMPLE acceptance table (k2lean/tests/gate.sh heavy).

Inputs: the output of the generated `ksimple-test` (`lake test`), which prints one `FINAL name: …`
line per final configuration (`toK` notation) and one PASS/FAIL line per case comparing the Lean
result with krust's (configuration equality); the tests' `.out` files; krust itself, for its
captured standard output under `--io off`.

For each case it reports:
  lean_vs_krust  the Lean driver's verdict (final configuration(s) equal to krust's)
  lean_vs_out    the program output in Lean's final configuration(s) (the `<output>` cell's
                 buffer) against the `.out` file (exact text for one-schedule tests, the set of
                 `S:String` alternatives for search tests, the listed buffers for threads_05)
  krust_vs_out   krust's captured output (`--output captured`, `--io off`) against `.out`

usage: simple-acceptance.py TEST_OUTPUT TESTS_DIR KRUST DEFINITION OUT_TOML
"""
import re
import subprocess
import sys
from pathlib import Path

OUTPUT_RE = re.compile(
    r'<output>\(ListItem\(#ostream\(_\)_K-IO_Stream_Int\(1\)\) ListItem\("off"\) '
    r'ListItem\(#buffer\(_\)_K-IO_Stream_K\(("(?:[^"\\]|\\.)*") ~> \.K\)\) \.List\)'
)


def unquote(s):
    """A Lean `String.quote` literal (or a K string literal) to its text."""
    assert s[0] == '"' and s[-1] == '"'
    out, i, body = [], 0, s[1:-1]
    while i < len(body):
        c = body[i]
        if c != '\\':
            out.append(c)
            i += 1
            continue
        n = body[i + 1]
        if n in 'nrt"\\':
            out.append({'n': '\n', 'r': '\r', 't': '\t', '"': '"', '\\': '\\'}[n])
            i += 2
        elif n == 'x':
            out.append(chr(int(body[i + 2:i + 4], 16)))
            i += 4
        elif n == 'u':
            if body[i + 2] == '{':
                j = body.index('}', i)
                out.append(chr(int(body[i + 3:j], 16)))
                i = j + 1
            else:
                out.append(chr(int(body[i + 2:i + 6], 16)))
                i += 6
        else:
            out.append(n)
            i += 2
    return ''.join(out)


def expected_outputs(out_text):
    """`.out` of a search test: the `S:String #Equals "…"` alternatives, or listed buffers."""
    alts = re.findall(r'#Equals\s*\n\s*("(?:[^"\\]|\\.)*")', out_text)
    if alts:
        return {unquote(a) for a in alts}
    bufs = re.findall(r'<output>.*?#buffer \( ("(?:[^"\\]|\\.)*") ~> \.K \)', out_text, re.S)
    return {unquote(b) for b in bufs}


def main():
    test_out, tests_dir, krust, definition, out_toml = sys.argv[1:6]
    lines = Path(test_out).read_text().splitlines()
    finals, verdict = {}, {}
    for l in lines:
        m = re.match(r'FINAL (\S+): (.*)$', l)
        if m:
            finals.setdefault(m.group(1), []).append(m.group(2))
            continue
        m = re.match(r'(PASS|FAIL) (\S+) \((run|search)\): (.*)$', l)
        if m:
            verdict[m.group(2)] = (m.group(1), m.group(3), m.group(4))
    progs = {p.stem: p for p in Path(tests_dir).glob('*/*.simple')}
    rows = []
    for name, (v, mode, detail) in verdict.items():
        prog = progs[name]
        out_file = prog.with_suffix('.simple.out')
        out_text = out_file.read_text() if out_file.exists() else None
        lean_bufs = []
        for f in finals.get(name, []):
            m = OUTPUT_RE.search(f)
            lean_bufs.append(unquote(m.group(1)) if m else None)
        stdin = prog.with_suffix('.simple.in')
        if mode == 'run':
            lean_vs_out = 'n/a'
            if out_text is not None and lean_bufs and lean_bufs[0] is not None:
                lean_vs_out = 'pass' if lean_bufs[0] == out_text else 'fail'
            elif out_text is not None:
                lean_vs_out = 'no output (undefined step)' if 'undefined' in detail else 'fail'
            p = subprocess.run([krust, 'krun', '--definition', definition, '--sort', 'Stmt', '--output', 'captured', str(prog)],
                               stdin=open(stdin) if stdin.exists() else subprocess.DEVNULL, capture_output=True, text=True)
            krust_vs_out = ('pass' if p.stdout == out_text else 'fail') if p.returncode == 0 else 'krust: ' + p.stderr.strip().splitlines()[-1][:120]
        else:
            exp = expected_outputs(out_text)
            got = {b for b in lean_bufs if b is not None}
            if name == 'threads_05':
                lean_vs_out = 'pass' if exp <= got else f'fail (missing {sorted(exp - got)})'
            else:
                lean_vs_out = 'pass' if exp == got else f'fail (lean {sorted(got)}, .out {sorted(exp)})'
            krust_vs_out = 'via lean (equal configurations)' if v == 'PASS' else 'n/a'
        rows.append((name, mode, v.lower(), lean_vs_out, krust_vs_out, detail))
    with open(out_toml, 'w') as f:
        for r in rows:
            f.write('[[case]]\n')
            for k, val in zip(['name', 'mode', 'lean_vs_krust', 'lean_vs_out', 'krust_vs_out', 'detail'], r):
                f.write(f'{k} = {val!r}\n'.replace("'", '"') if '"' not in str(val) else f'{k} = """{val}"""\n')
            f.write('\n')
    print('| case | mode | Lean = krust | Lean output = .out | krust output = .out | detail |')
    print('|---|---|---|---|---|---|')
    for r in rows:
        print('| ' + ' | '.join(str(x) for x in r) + ' |')


if __name__ == '__main__':
    main()
