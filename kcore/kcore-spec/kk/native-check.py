"""The native check of kore.k's `succs` against KCore's executable step (`kcore kk-native`).

Usage: python3 -I kk/native-check.py [--record] [ID...]   (from anywhere)

For each case of kk/agree-kore-in-k.jsonl (the Kore-in-K catalogue's cases: the case's kompiled text
under .lake/kore-in-k/build, its initial configuration) and of kk/native-extra.jsonl, `kcore
kk-native` reads the case's text with KCore's reader and, where `KK.encDef` gives it a form, compares
at every configuration reachable from the input at `d₀` the executable step's successors
(`CExec.successorsN (d₀ d)`) with kore.k's `succs` at `[embD E, emb (enc x)]`, evaluated by
`CExec` at `K₀`, kore.k's semantics read from examples/ref-kk/RefKk/definition.kore (the text
test/kk-kompile.toml records, whose SHA-256 is checked here). The encodings are Lean's
(`KK.enc`, `KK.encDef`); no Python encoder is involved. `kcore kk-native-hooks` checks the table of
operation codes (`KK.hookCodes`) against kore.k's `hookOp`.

Each case runs in its own process under a 12 GiB memory scope with a time limit; its wall time and
peak memory are recorded. The `case` lines (without their times) are compared with
kk/native-check.expected; `--record` writes that file instead. A difference there, a `differ`
verdict or a failing hook check is a failure (exit 1). Exit 2 without kcore or the kompiled texts.

The work directory is .lake/kk-native: cases.jsonl, one log per case, report.txt.
"""
import hashlib, json, os, re, subprocess, sys, tomllib
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
SPEC = os.path.dirname(HERE)
WORK = os.path.join(SPEC, '.lake', 'kk-native')
KCORE = os.path.join(SPEC, '.lake', 'build', 'bin', 'kcore')
KK = os.path.join(SPEC, 'examples', 'ref-kk', 'RefKk', 'definition.kore')
EXPECTED = os.path.join(HERE, 'native-check.expected')
SCOPE = ['systemd-run', '--user', '--scope', '-q', '-p', 'MemoryMax=12G', '-p', 'MemorySwapMax=0']
TIMEOUT_S = 900


def rtime():
    d = SPEC
    while d != os.path.dirname(d):
        d = os.path.dirname(d)
        p = os.path.join(d, 'k2lean', 'tests', 'rtime.py')
        if os.path.isfile(p):
            return p
    return None


def mem_available_gib():
    for line in open('/proc/meminfo'):
        if line.startswith('MemAvailable:'):
            return int(line.split()[1]) / 2**20
    return 0


def run(argv, log):
    rt = rtime()
    cmd = [*SCOPE, 'timeout', str(TIMEOUT_S)] + (['python3', rt] if rt else []) + argv
    r = subprocess.run(cmd, capture_output=True, text=True, cwd=SPEC)
    open(log, 'w').write(r.stdout + r.stderr)
    m = re.search(r'rtime: (wall [0-9.]+ s).*?max child rss ([0-9]+ MiB)', r.stderr)
    res = f'{m.group(1)}, peak {m.group(2)}' if m else f'exit {r.returncode} (no rtime line)'
    return r.returncode, r.stdout, res


def cases():
    out = []
    seen = set()
    for f in ('agree-kore-in-k.jsonl', 'native-extra.jsonl'):
        for line in open(os.path.join(HERE, f)):
            if not line.strip():
                continue
            j = json.loads(line)
            cid = j['id'].split('/')[0]
            if cid in seen:
                continue
            seen.add(cid)
            out.append({'id': cid, 'definition': os.path.normpath(os.path.join(HERE, j['definition'])),
                        'input': j['input'], **({'reaches': j['reaches']} if 'reaches' in j else {})})
    return out


def main(argv):
    record = '--record' in argv
    only = [a for a in argv if not a.startswith('--')]
    if not os.access(KCORE, os.X_OK):
        print('native-check: no kcore: run `lake build kcore` in kcore-spec', file=sys.stderr)
        return 2
    pin = tomllib.load(open(os.path.join(SPEC, 'test', 'kk-kompile.toml'), 'rb'))
    if hashlib.sha256(open(KK, 'rb').read()).hexdigest() != pin['sha256']:
        print(f'native-check: {os.path.relpath(KK, SPEC)} is not the text test/kk-kompile.toml records', file=sys.stderr)
        return 1
    cs = [c for c in cases() if not only or c['id'] in only]
    missing = [c['id'] for c in cs if not os.path.isfile(c['definition'])]
    if missing:
        print(f'native-check: no kompiled text for {", ".join(missing)} (kk/agree-kore-in-k.py builds them, '
              'with $K_KOMPILE set)', file=sys.stderr)
        return 2
    os.makedirs(WORK, exist_ok=True)
    jl = os.path.join(WORK, 'cases.jsonl')
    with open(jl, 'w') as f:
        for c in cs:
            f.write(json.dumps(c) + '\n')

    rc, hooks_out, hooks_res = run([KCORE, 'kk-native-hooks', KK], os.path.join(WORK, 'hooks.log'))
    jobs = max(1, min((os.cpu_count() or 1) // 4, int((mem_available_gib() - 16) // 2)))

    def one(c):
        return (c['id'],) + run([KCORE, 'kk-native', KK, jl, c['id']], os.path.join(WORK, c['id'] + '.log'))

    with ThreadPoolExecutor(jobs) as ex:
        results = list(ex.map(one, cs))

    report, lines, faults = [], [], []
    kkline = next((l for _, _, out, _ in results for l in out.splitlines() if l.startswith('kk: ')), None)
    report.append(kkline or 'kk: no line')
    if not kkline or not kkline.endswith('execReady K₀ true'):
        faults.append('kore.k\'s semantics is not read, or CExec.execReady fails at K₀')
    report.append(f'hooks: {hooks_res}')
    report += ['  ' + l for l in hooks_out.splitlines()]
    if rc != 0:
        faults.append('kk-native-hooks fails')
    for cid, code, out, res in results:
        case = [l for l in out.splitlines() if l.startswith('case ')]
        if not case:
            case = [f'case {cid} no-result ({res})']
        lines += [re.sub(r' ms=\d+', '', l) for l in case]
        report.append(f'{cid}: {res}')
        report += ['  ' + l for l in out.splitlines() if not l.startswith('kk: ')]
        if code not in (0, 1) and case[0].find('no-result') < 0:
            faults.append(f'{cid}: exit {code}')
    open(os.path.join(WORK, 'report.txt'), 'w').write('\n'.join(report) + '\n')
    print('\n'.join(report))
    differ = sum(int(m.group(1)) for l in lines for m in [re.search(r' differ=(\d+)', l)] if m)
    unreached = [l.split()[1] for l in lines if 'reaches=no' in l]
    if record:
        if not only:
            open(EXPECTED, 'w').write('\n'.join(lines) + '\n')
        print(f'recorded {len(lines)} case lines in {os.path.relpath(EXPECTED, SPEC)}')
    else:
        want = [l for l in open(EXPECTED).read().splitlines() if l.strip()]
        if only:
            want = [l for l in want if l.split()[1] in only]
        if want != lines:
            faults.append('the case lines are not kk/native-check.expected\'s: ' +
                          '; '.join(f'{a!r} vs {b!r}' for a, b in zip(want, lines) if a != b)[:2000])
    for cid in unreached:
        faults.append(f'{cid}: the configuration it names is not reached at an agreeing step')
    for f in faults:
        print('FAULT ' + f)
    ok = not faults and differ == 0
    print(f'{"PASS" if ok else "FAIL"} kk-native: {len(lines)} cases, {differ} configuration(s) differ; '
          f'details in {os.path.relpath(os.path.join(WORK, "report.txt"), SPEC)}')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
