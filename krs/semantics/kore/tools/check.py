#!/usr/bin/env python3
"""Run kore.k on every case (or the named ones) and compare its result with the case's expected result.

  check.py [cases/<id> ...]      (relative to the package directory, or absolute)

kore.k is kompiled once with `krust kcompile` (cached in the build directory by the SHA-256 of
kore.k and of the krust executable); each case's kore.pgm is run with `krust krun --sort Pgm`,
and its result, decoded with the case's symbols.json (tools/korek.py korek), is compared with each
backend's result in the case's expected.json (its finals; a backend's error differs from every
result). No K reference tool runs: expected.json is the cached reference result, which
tools/case.py computes.

A case passes when, for each backend, kore.k's finals equal the backend's result and
differences.toml lists no difference of the case from that backend, or they differ and it lists
one (so an entry cannot outlive its difference). A case whose def.k or pgm no longer has the
SHA-256 its expected.json was computed from fails as stale: rebuild it with tools/case.py.
Exit 0 when every case passes, 1 otherwise, 2 when no krust executable is found.

krust is $KRUST, else release/krust under $CARGO_TARGET_DIR, else the repository's
target/release/krust. Each krust run has a 60 s timeout. The build directory is
$KORE_IN_K_BUILD, by default kore-in-k under the system temporary directory.
"""
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time
import tomllib

PACKAGE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
REPOSITORY = os.path.dirname(os.path.dirname(os.path.dirname(PACKAGE)))
sys.path.insert(0, os.path.join(PACKAGE, 'tools'))
import korek  # noqa: E402

BUILD = os.environ.get('KORE_IN_K_BUILD', os.path.join(tempfile.gettempdir(), 'kore-in-k'))
TIMEOUT_S = 60


def krust():
    candidates = [os.environ.get('KRUST')]
    if os.environ.get('CARGO_TARGET_DIR'):
        candidates.append(os.path.join(os.environ['CARGO_TARGET_DIR'], 'release', 'krust'))
    candidates.append(os.path.join(REPOSITORY, 'target', 'release', 'krust'))
    for c in candidates:
        if c and os.access(c, os.X_OK):
            return os.path.abspath(c)
    print('error: no krust executable: set KRUST, or build it with '
          '`cargo build --release -p k-rust` (see README.md)', file=sys.stderr)
    sys.exit(2)


def sha(path):
    with open(path, 'rb') as f:
        return hashlib.sha256(f.read()).hexdigest()


def kompiled(exe):
    """kore.k kompiled by krust, rebuilt when kore.k or the krust executable changes."""
    kc = os.path.join(BUILD, 'kore-k')
    stamp = os.path.join(kc, 'stamp.json')
    key = {'kore.k': sha(os.path.join(PACKAGE, 'kore.k')), 'krust': sha(exe)}
    if os.path.exists(stamp) and json.load(open(stamp)) == key:
        return kc, 0
    shutil.rmtree(kc, ignore_errors=True)
    os.makedirs(BUILD, exist_ok=True)
    start = time.monotonic()
    subprocess.run([exe, 'kcompile', os.path.join(PACKAGE, 'kore.k'), '--main-module', 'KORE',
                    '--syntax-module', 'KORE-SYNTAX', '-o', kc], check=True, timeout=TIMEOUT_S * 5)
    with open(stamp, 'w') as f:
        json.dump(key, f)
    return kc, int((time.monotonic() - start) * 1000)


def check(case, exe, kc, differences):
    cid = os.path.basename(case)
    exp = json.load(open(os.path.join(case, 'expected.json')))
    inputs = {'def.k': sha(os.path.join(case, 'def.k')), 'pgm': sha(os.path.join(case, 'pgm'))}
    if exp.get('inputs') != inputs:
        return False, f'{cid}: FAIL stale: def.k or pgm changed since expected.json; run tools/case.py {cid}', 0
    out = os.path.join(BUILD, f'{cid}.kore-k.out')
    start = time.monotonic()
    r = subprocess.run([exe, 'krun', '--definition', kc, '--sort', 'Pgm', os.path.join(case, 'kore.pgm')],
                       capture_output=True, text=True, timeout=TIMEOUT_S)
    ms = int((time.monotonic() - start) * 1000)
    with open(out, 'w') as f:
        f.write(r.stdout)
    try:
        finals = korek.cmd_korek(os.path.join(case, 'symbols.json'), out)
    except Exception as err:  # noqa: BLE001 - reported as this case's failure
        return False, f'{cid}: FAIL no result from kore.k ({err}; exit {r.returncode}: {r.stderr[-300:]})', ms
    bad, listed = [], []
    for backend, res in sorted(exp['backends'].items()):
        equal = finals == res.get('finals')
        shown = json.dumps(res['finals']) if 'finals' in res else 'error: ' + res.get('error', '')
        if (cid, backend) in differences:
            if equal:
                bad.append(f'listed in differences.toml but now equal to the {backend} backend')
            else:
                listed.append(backend)
        elif not equal:
            bad.append(f'{backend}={shown}')
    if bad:
        return False, f'{cid}: FAIL kore.k={json.dumps(finals)} ' + '; '.join(bad), ms
    if listed:
        return True, f'{cid}: ok ({ms} ms) {len(finals)} final(s); differs as listed from {", ".join(listed)}', ms
    return True, f'{cid}: ok ({ms} ms) {len(finals)} final(s)', ms


def main(args):
    with open(os.path.join(PACKAGE, 'differences.toml'), 'rb') as f:
        differences = {(d['case'], d['backend']): d['reason'] for d in tomllib.load(f).get('difference', [])}
    root = os.path.join(PACKAGE, 'cases')
    if args:
        cases = [a if os.path.isabs(a) or os.path.exists(a) else os.path.join(PACKAGE, a) for a in args]
    else:
        cases = [os.path.join(root, d) for d in sorted(os.listdir(root)) if os.path.isdir(os.path.join(root, d))]
    cases = [os.path.abspath(c) for c in cases]
    unknown = sorted({c for c, _ in differences} - {os.path.basename(c) for c in cases}) if not args else []
    exe = krust()
    kc, kompile_ms = kompiled(exe)
    passed, total_ms = 0, 0
    for case in cases:
        ok, line, ms = check(case, exe, kc, differences)
        passed += ok
        total_ms += ms
        print(line)
    for cid in unknown:
        print(f'{cid}: FAIL listed in differences.toml but no such case')
    fine = passed == len(cases) and not unknown
    kompile = f'kcompile {kompile_ms} ms' if kompile_ms else 'kcompile cached'
    print(f'{"PASS" if fine else "FAIL"} kore-in-k: {passed} of {len(cases)} cases pass '
          f'({len(differences)} listed difference(s)); krun {total_ms} ms in all, {kompile}')
    return 0 if fine else 1


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
