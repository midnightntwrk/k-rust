#!/usr/bin/env python3
"""Build the encoded program and the reference expected result of one case of kore-in-k, or all.

  case.py [--refresh] --all
  case.py [--refresh] cases/<id> [...]      (relative to the package directory, or absolute)

A case directory holds def.k (module CASE, syntax module CASE-SYNTAX, the term in a closed cell,
`configuration <k> $PGM:S </k>`, rules `<k> L => R </k>`) and pgm (the initial term in
CASE-SYNTAX). For each case this writes, into the case directory:

  pgm.kore       kast pgm --output kore against the haskell-kompiled def.k: the initial term
  kore.pgm       the encoded program for kore.k (tools/korek.py encode)
  symbols.json   the encoder's numbering of symbols and sorts
  expected.json  the reference result: for the haskell backend and for the llvm backend
                 (kompiled with --enable-search), the final configurations of krun --search as
                 canonical text (tools/korek.py ref), or the backend's error; which K release and
                 backends produced them; and the SHA-256 of def.k and pgm they were computed from

The kompiled definition (def.k's definition.kore, whose Source attributes name the absolute path
of def.k) stays in the build directory and is not part of the package; it is rebuilt from def.k.
expected.json is a cache of the reference runs: it is recomputed only when the SHA-256 of def.k or
pgm differs from its `inputs`, or under --refresh.

Tools: the K toolchain is found as the repository's gates find it, beside $K_KOMPILE, else on
PATH; without it the script exits 2. Every K run is under a 120 s timeout and a memory bound: a
transient systemd user scope (MemoryMax=12G, no swap) where one can be started, else an address
space limit of 24 GiB. $K_OPTS overrides the JVM options. The build directory is
$KORE_IN_K_BUILD, by default kore-in-k under the system temporary directory.
"""
import hashlib
import json
import os
import re
import resource
import shutil
import subprocess
import sys
import tempfile
import time

PACKAGE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(PACKAGE, 'tools'))
import korek  # noqa: E402

BUILD = os.environ.get('KORE_IN_K_BUILD', os.path.join(tempfile.gettempdir(), 'kore-in-k'))
TIMEOUT_S = 120
K_OPTS = os.environ.get('K_OPTS', '-Xmx2048m -Xss8m -XX:+UseSerialGC')
SCOPE = ['systemd-run', '--user', '--scope', '-q', '-p', 'MemoryMax=12G', '-p', 'MemorySwapMax=0']
FALLBACK_AS_BYTES = 24 << 30


def k_bin():
    kompile = os.environ.get('K_KOMPILE') or shutil.which('kompile')
    if not kompile or not os.path.exists(kompile):
        print('error: no K toolchain: set K_KOMPILE to its kompile, or put kompile on PATH', file=sys.stderr)
        sys.exit(2)
    return os.path.dirname(os.path.abspath(kompile))


def scope_available():
    try:
        return subprocess.run(SCOPE + ['true'], capture_output=True, timeout=30).returncode == 0
    except (OSError, subprocess.TimeoutExpired):
        return False


class Runner:
    def __init__(self):
        self.bin = k_bin()
        self.scoped = scope_available()

    def tool(self, name):
        return os.path.join(self.bin, name)

    def run(self, cmd, out=None):
        """Run a K tool; its stdout goes to `out`. Returns (exit code, stderr, wall ms)."""
        env = dict(os.environ, K_OPTS=K_OPTS)
        prefix = (SCOPE if self.scoped else []) + ['timeout', str(TIMEOUT_S)]

        def limit():
            if not self.scoped:
                resource.setrlimit(resource.RLIMIT_AS, (FALLBACK_AS_BYTES, FALLBACK_AS_BYTES))

        os.makedirs(BUILD, exist_ok=True)
        start = time.monotonic()
        r = subprocess.run(prefix + cmd, capture_output=True, text=True, env=env, cwd=BUILD,
                           preexec_fn=limit)
        ms = int((time.monotonic() - start) * 1000)
        if out:
            with open(out, 'w') as f:
                f.write(r.stdout)
        return r.returncode, r.stderr + r.stdout, ms

    def must(self, cmd, out=None):
        code, text, ms = self.run(cmd, out)
        if code != 0:
            raise RuntimeError(f'{os.path.basename(cmd[0])}: exit {code}\n{text[-3000:]}')
        return ms

    def versions(self):
        k = subprocess.run([self.tool('kompile'), '--version'], capture_output=True, text=True,
                           env=dict(os.environ, K_OPTS=K_OPTS)).stdout
        k = re.search(r'K version:\s*(\S+)', k).group(1)
        hs = subprocess.run([self.tool('kore-exec'), '--version'], capture_output=True, text=True).stdout.split()[0]
        llvm = subprocess.run([self.tool('llvm-backend-version')], capture_output=True, text=True).stdout.strip()
        return {
            'haskell': f'K {k}: kompile --backend haskell; krun --search (kore-exec {hs})',
            'llvm': f'K {k}: kompile --backend llvm --enable-search; krun --search (llvm backend {llvm})',
        }


def error_class(text):
    """A backend failure as stable text: the hook's message and the failing K tool, without the
    temporary paths and times krun prints."""
    def unpath(s):
        return ' '.join(re.sub(r'\S*/(\S+)', r'\1', s).split())

    found = []
    for pattern in (r'\[hook_[A-Za-z_]+\][^\n]*', r'what\(\):[^\n]*', r'\[Error\][^\n]*'):
        m = re.search(pattern, text)
        if m and not any(f in unpath(m.group(0)) for f in found):
            found.append(unpath(m.group(0)))
    if found:
        return '; '.join(found)
    last = [ln for ln in text.splitlines() if ln.strip()][-1:] or ['(no output)']
    return unpath(last[0])


def sha(path):
    with open(path, 'rb') as f:
        return hashlib.sha256(f.read()).hexdigest()


def write_json(path, value):
    with open(path, 'w') as f:
        json.dump(value, f, indent=1, sort_keys=True)
        f.write('\n')


def build(case, runner, refresh, versions):
    case = os.path.abspath(case)
    cid = os.path.basename(case)
    b = os.path.join(BUILD, cid)
    os.makedirs(b, exist_ok=True)
    defk, pgm = os.path.join(case, 'def.k'), os.path.join(case, 'pgm')
    key = {'def.k': sha(defk), 'pgm': sha(pgm)}
    exp_path = os.path.join(case, 'expected.json')
    old = json.load(open(exp_path)) if os.path.exists(exp_path) else None
    hs, kompiled = os.path.join(b, 'hs'), os.path.join(b, 'hs', 'definition.kore')
    stamp = os.path.join(b, 'inputs.json')
    times = {}
    if not (os.path.exists(kompiled) and os.path.exists(stamp) and json.load(open(stamp)) == key):
        shutil.rmtree(hs, ignore_errors=True)
        times['kompile_haskell_ms'] = runner.must(
            [runner.tool('kompile'), defk, '--main-module', 'CASE', '--syntax-module', 'CASE-SYNTAX',
             '--backend', 'haskell', '-o', hs])
        write_json(stamp, key)
    runner.must([runner.tool('kast'), pgm, '-d', hs, '--output', 'kore'], out=os.path.join(case, 'pgm.kore'))
    pgm_sort = re.search(r'\$PGM:(\w+)', open(defk).read()).group(1)
    syms = os.path.join(case, 'symbols.json')
    korek.cmd_encode(kompiled, os.path.join(case, 'pgm.kore'), os.path.join(case, 'kore.pgm'), syms, pgm_sort)
    if old is not None and old.get('inputs') == key and not refresh:
        return cid, old, times
    exp = {'inputs': key, 'reference': versions, 'backends': {}}
    hs_out = os.path.join(b, 'haskell.out')
    code, text, times['krun_haskell_ms'] = runner.run(
        [runner.tool('krun'), pgm, '-d', hs, '--search', '--output', 'kore'], out=hs_out)
    exp['backends']['haskell'] = ({'finals': korek.cmd_ref(syms, hs_out)} if code == 0
                                  else {'error': error_class(text)})
    llvm, llvm_out = os.path.join(b, 'llvm'), os.path.join(b, 'llvm.out')
    shutil.rmtree(llvm, ignore_errors=True)
    code, text, times['kompile_llvm_ms'] = runner.run(
        [runner.tool('kompile'), defk, '--main-module', 'CASE', '--syntax-module', 'CASE-SYNTAX',
         '--backend', 'llvm', '--enable-search', '-o', llvm])
    if code == 0:
        code, text, times['krun_llvm_ms'] = runner.run(
            [runner.tool('krun'), pgm, '-d', llvm, '--search', '--output', 'kore'], out=llvm_out)
    exp['backends']['llvm'] = ({'finals': korek.cmd_ref(syms, llvm_out)} if code == 0
                               else {'error': error_class(text)})
    finals = [v.get('finals') for v in exp['backends'].values()]
    exp['backends_agree'] = all(f is not None and f == finals[0] for f in finals)
    write_json(exp_path, exp)
    return cid, exp, times


def main(args):
    refresh = '--refresh' in args
    args = [a for a in args if a != '--refresh']
    if args == ['--all']:
        root = os.path.join(PACKAGE, 'cases')
        args = [os.path.join(root, d) for d in sorted(os.listdir(root))
                if os.path.isdir(os.path.join(root, d))]
    if not args:
        sys.exit(__doc__)
    runner = Runner()
    versions = runner.versions()
    bad = 0
    for c in args:
        if not os.path.isabs(c) and not os.path.exists(c):
            c = os.path.join(PACKAGE, c)
        try:
            cid, exp, times = build(c, runner, refresh, versions)
        except Exception as err:  # noqa: BLE001 - one failed case does not stop the others
            print(f'{os.path.basename(c)}: ERROR {err}')
            bad += 1
            continue
        res = {k: v.get('finals', 'error: ' + v.get('error', '')) for k, v in exp['backends'].items()}
        agree = 'backends agree' if exp['backends_agree'] else 'backends disagree'
        print(f'{cid}: {agree} {json.dumps(res)} {json.dumps(times)}')
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
