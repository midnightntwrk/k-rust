"""Compare kk.k with KCore's oracle, and both with the rulings of the Kore-in-K catalogue.

Usage: python3 -I kk/compare.py CATALOGUE   (from anywhere; CATALOGUE is krs/semantics/kore of a
       k-rust checkout, else $KORE_IN_K)

kk.k is the interpreter the statement kk_step is about: a copy of the catalogue's kore.k (its first
line records the commit it was copied at). The catalogue is read and never written; it reads nothing
of this directory. Two comparisons are made over the catalogue's cases, and kept apart:

1. kk.k against KCore. kk.k's finals (kk.k kompiled by `krust kcompile`, the case's kore.pgm run by
   `krust krun --sort Pgm`, the result decoded with the case's symbols.json by the catalogue's
   tools/korek.py) are given to `kcore oracle` as the expected result of the case's kompiled text
   and initial configuration (built as agree-kore-in-k.py builds them). The oracle's verdict:
   `=` (agree, or agree at the interpretation of the parameters), a defect (differ: kk.k or KCore
   changes), or `no-oracle` with the oracle's reason (the text is outside what KCore reads or runs).
2. kk.k and KCore against the catalogue's ruling: for a settled case, whether each one's finals are
   the ruling's; for an unsettled one, which readings' finals they are (a reading whose answer is
   prose is not compared). kk.k's finals are compared as canonical texts; KCore's by the oracle, with
   each ruling's (or reading's) finals as the expected result. A side whose finals are no ruling and
   no reading is a difference, and each difference is a line of catalogue-differences.toml (case,
   side, reason). A line there is never a failure, and it cannot outlive its difference.

A difference is never a reason to change a ruling of the catalogue: a line is a KCore ticket, a kk.k
ticket, or a challenge of the ruling from the K text.

Also checked: kk.k has the SHA-256 PIN.toml records, and the kompiled fixture PIN.toml names
(test/constructs/fixtures/kore-k) kompiles kk.k (its fixture.toml's `main` and `external`) and its
kompile.txt records that SHA-256 for it; whether kk.k without its first line is the catalogue's
kore.k is printed.

One line per case: `ID STATUS cmp1:V1 vs-ruling: kk.k:V2 kcore:V3`, followed by the catalogue's
disposition of its own kore.k where it has one (the finals are compared, not the route: at c42 the
catalogue records that kore.k reaches the finals of a reading by a route the text excludes). Exit 0 when comparison 1 has no
defect and catalogue-differences.toml lists exactly the differences of comparison 2; 1 otherwise;
2 without krust, kcore or the kompiled texts.

Tools: krust is $KRUST, else release/krust under $CARGO_TARGET_DIR, else target/release/krust of
the k-rust checkout above; kcore is .lake/build/bin/kcore (`lake build kcore`). The kompiled texts
of the cases are .lake/kore-in-k/build (agree-kore-in-k.py builds a missing one when $K_KOMPILE is
set). The work directory is .lake/kk-compare. kcore and krust run under a 12 GiB memory scope.
"""
import hashlib, importlib.util, json, os, re, shutil, subprocess, sys, tomllib

HERE = os.path.dirname(os.path.abspath(__file__))
SPEC = os.path.dirname(HERE)
WORK = os.path.join(SPEC, '.lake', 'kk-compare')
KK = os.path.join(HERE, 'kk.k')
KCORE = os.path.join(SPEC, '.lake', 'build', 'bin', 'kcore')
SCOPE = ['systemd-run', '--user', '--scope', '-q', '-p', 'MemoryMax=12G', '-p', 'MemorySwapMax=0']
TIMEOUT_S = 60


def sha(path):
    with open(path, 'rb') as f:
        return hashlib.sha256(f.read()).hexdigest()


def pin_faults(pin):
    """The faults of PIN.toml's kompiled fixture: it must kompile kk.k (fixture.toml `main` kk.k,
    `external` this kk.k by its path in the k-rust checkout) and its kompile.txt must record kk_sha256
    for that file."""
    fx = os.path.join(SPEC, 'test', 'constructs', 'fixtures', pin['kompiled_fixture'])
    rel = os.path.relpath(KK, os.path.dirname(os.path.dirname(SPEC)))
    out = []
    try:
        conf = tomllib.load(open(os.path.join(fx, 'fixture.toml'), 'rb'))
        record = open(os.path.join(fx, 'kompile.txt')).read()
    except OSError as err:
        return [f'kompiled fixture {pin["kompiled_fixture"]}: {err}']
    if conf.get('main') != 'kk.k' or rel not in conf.get('external', []):
        out.append(f'fixture {pin["kompiled_fixture"]} does not kompile {rel}')
    if f'external {rel}: sha256 {pin["kk_sha256"]}' not in record.split('\n'):
        out.append(f'fixture {pin["kompiled_fixture"]}: kompile.txt does not record kk_sha256 for {rel}')
    return out


def load_agree():
    spec = importlib.util.spec_from_file_location('agree_kore_in_k', os.path.join(HERE, 'agree-kore-in-k.py'))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def krust():
    candidates = [os.environ.get('KRUST')]
    if os.environ.get('CARGO_TARGET_DIR'):
        candidates.append(os.path.join(os.environ['CARGO_TARGET_DIR'], 'release', 'krust'))
    d = SPEC
    while d != os.path.dirname(d):
        d = os.path.dirname(d)
        candidates.append(os.path.join(d, 'target', 'release', 'krust'))
    for c in candidates:
        if c and os.access(c, os.X_OK):
            return os.path.abspath(c)
    print('compare: no krust executable: set KRUST', file=sys.stderr)
    sys.exit(2)


def kompiled_kk(exe):
    """kk.k kompiled by krust, rebuilt when kk.k or the krust executable changes."""
    kc = os.path.join(WORK, 'kk')
    stamp = os.path.join(WORK, 'kk.stamp.json')
    key = {'kk.k': sha(KK), 'krust': sha(exe)}
    if os.path.exists(stamp) and json.load(open(stamp)) == key:
        return kc
    shutil.rmtree(kc, ignore_errors=True)
    os.makedirs(WORK, exist_ok=True)
    subprocess.run([exe, 'kcompile', KK, '--main-module', 'KORE', '--syntax-module', 'KORE-SYNTAX', '-o', kc],
                   check=True, timeout=TIMEOUT_S * 5)
    json.dump(key, open(stamp, 'w'))
    return kc


def run_kk(korek, case, exe, kc):
    """kk.k's finals on a case, as canonical texts ({'finals': [...]} or {'error': ...})."""
    out = os.path.join(WORK, os.path.basename(case) + '.kk.out')
    r = subprocess.run([exe, 'krun', '--definition', kc, '--sort', 'Pgm', os.path.join(case, 'kore.pgm')],
                       capture_output=True, text=True, timeout=TIMEOUT_S)
    open(out, 'w').write(r.stdout)
    try:
        return {'finals': korek.cmd_korek(os.path.join(case, 'symbols.json'), out)}
    except Exception as err:  # noqa: BLE001 - kk.k's failure on a case is its result
        return {'error': f'no result from kk.k ({err}; exit {r.returncode})'}


def expected_kore(agree, finals, colls, defn):
    fs = [agree.final(t, colls, defn) for t in finals]
    return ('\\bottom{SortGeneratedTopCell{}}()' if not fs else fs[0] if len(fs) == 1
            else '\\or{SortGeneratedTopCell{}}(' + ', '.join(fs) + ')')


def main(argv):
    corpus = argv[0] if argv else os.environ.get('KORE_IN_K')
    if not corpus or not os.path.isfile(os.path.join(corpus or '', 'kore.k')):
        sys.exit('usage: compare.py CATALOGUE (or $KORE_IN_K): krs/semantics/kore of a k-rust checkout')
    corpus = os.path.abspath(corpus)
    sys.dont_write_bytecode = True  # the catalogue is read, not written
    sys.path.insert(0, os.path.join(corpus, 'tools'))
    import korek
    agree = load_agree()
    pin = tomllib.load(open(os.path.join(HERE, 'PIN.toml'), 'rb'))
    listed = tomllib.load(open(os.path.join(HERE, 'catalogue-differences.toml'), 'rb')).get('difference', [])
    faults = []
    if sha(KK) != pin['kk_sha256']:
        faults.append(f'kk.k does not have the SHA-256 PIN.toml records ({pin["kk_sha256"]})')
    faults += pin_faults(pin)
    body = open(KK, 'rb').read().split(b'\n', 1)[1]
    same = body == open(os.path.join(corpus, 'kore.k'), 'rb').read()
    print('kk.k without its first line ' + ('is' if same else 'is NOT') + " the catalogue's kore.k")
    if not os.access(KCORE, os.X_OK):
        print('compare: no kcore: run `lake build kcore` in kcore-spec', file=sys.stderr)
        sys.exit(2)
    exe = krust()
    os.makedirs(WORK, exist_ok=True)
    kc = kompiled_kk(exe)

    ids = sorted(d for d in os.listdir(os.path.join(corpus, 'cases'))
                 if os.path.isfile(os.path.join(corpus, 'cases', d, 'kore.pgm')))
    lines, info = [], {}
    for cid in ids:
        src = os.path.join(corpus, 'cases', cid)
        agree.build(corpus, cid)
        entry = tomllib.load(open(os.path.join(src, 'entry.toml'), 'rb'))
        ev = json.load(open(os.path.join(src, 'evidence.json')))
        canon = ev.get('ruling_canonical') or {}
        defk = open(os.path.join(src, 'def.k')).read()
        sort = re.search(r'\$PGM:(\w+)', defk).group(1)
        pgm = open(os.path.join(src, 'pgm.kore')).read().strip()
        colls = json.load(open(os.path.join(src, 'symbols.json'))).get('collections', {})
        defn = open(os.path.join(agree.BUILD, cid, 'hs', 'definition.kore')).read()
        init = agree.initial(corpus, defn, sort, pgm)
        kk = run_kk(korek, src, exe, kc)
        status = entry['ruling']['status']
        targets = {'ruling': canon['settled']} if status == 'settled' else dict(canon.get('readings') or {})
        own = [d['is'] for d in entry.get('disposition', []) if d.get('implementation') == 'kore.k']
        info[cid] = {'status': status, 'kk': kk, 'targets': targets, 'own': own}
        base = {'definition': os.path.join(agree.BUILD, cid, 'hs', 'definition.kore'), 'input': init, 'mode': 'search-final'}
        if 'finals' in kk:
            lines.append({'id': f'{cid}/kk', **base, 'expected': expected_kore(agree, kk['finals'], colls, defn)})
        for name, fs in targets.items():
            lines.append({'id': f'{cid}/{name}', **base, 'expected': expected_kore(agree, fs, colls, defn)})
    cases = os.path.join(WORK, 'cases.jsonl')
    with open(cases, 'w') as f:
        for line in lines:
            f.write(json.dumps(line) + '\n')
    out = os.path.join(WORK, 'oracle.jsonl')
    with open(out, 'w') as f:
        subprocess.run([*SCOPE, 'timeout', '1800', KCORE, 'oracle', cases], stdout=f, stderr=subprocess.STDOUT, cwd=WORK)
    oracle = {}
    for line in open(out):
        try:
            j = json.loads(line)
        except ValueError:
            continue
        if 'id' in j:
            oracle[j['id']] = j

    def verdict(lid):
        j = oracle.get(lid)
        if j is None:
            return 'missing', 'no oracle line'
        if not j.get('oracle'):
            if j.get('reason', '').startswith('no text'):
                return 'missing', j['reason']
            return 'no-oracle', j.get('reason', '')
        v = j.get('vs_expected', '-')
        return ('=' if v in ('agree', 'agree-at-none') else v), v

    defects, actual = [], {}
    for cid in ids:
        i = info[cid]
        kk, targets = i['kk'], i['targets']
        if 'finals' in kk:
            c1, why = verdict(f'{cid}/kk')
            if c1 == 'missing':
                faults.append(f'{cid}/kk: {why}')
            elif c1 not in ('=', 'no-oracle'):
                defects.append(f'{cid}: kk.k and KCore differ ({why})')
        else:
            c1 = 'kk-error'
        kk_at = [n for n, fs in targets.items() if 'finals' in kk and sorted(kk['finals']) == sorted(fs)]
        kcv = [(n, verdict(f'{cid}/{n}')) for n in targets]
        kc_at = [n for n, (v, _) in kcv if v == '=']
        no_oracle = any(v == 'no-oracle' for _, (v, _) in kcv)
        faults += [f'{cid}/{n}: no oracle line' for n, (v, _) in kcv if v == 'missing']
        mark = lambda at, settled: ('=' if at else 'differs') if settled else (
            ','.join(f'reading:{n}' for n in at) or 'differs')
        settled = i['status'] == 'settled'
        kk_mark = mark(kk_at, settled)
        kc_mark = 'no-oracle' if no_oracle and not kc_at else mark(kc_at, settled)
        if kk_mark == 'differs':
            actual[(cid, 'kk.k')] = kk.get('error', 'finals ' + json.dumps(kk.get('finals')))
        if kc_mark == 'differs':
            actual[(cid, 'kcore')] = 'its finals are no ' + ('ruling' if settled else 'reading')
        note = f' (the catalogue on its kore.k: {i["own"][0]})' if i['own'] else ''
        print(f'{cid} {i["status"]} cmp1:{c1} vs-ruling: kk.k:{kk_mark} kcore:{kc_mark}{note}')

    keys = set()
    for d in listed:
        k = (d.get('case'), d.get('side'))
        keys.add(k)
        if not d.get('reason'):
            faults.append(f'catalogue-differences.toml: {k} has no reason')
        if k not in actual:
            faults.append(f'catalogue-differences.toml lists {k[1]} at {k[0]}, which is at the ruling now')
    for k, what in sorted(actual.items()):
        if k not in keys:
            faults.append(f'{k[1]} at {k[0]} is not the ruling ({what}) and catalogue-differences.toml does not list it')
    for d in defects:
        print('DEFECT ' + d)
    for f in faults:
        print('FAULT ' + f)
    print(f'{"PASS" if not defects and not faults else "FAIL"} kk-compare: {len(ids)} cases; '
          f'comparison 1: {len(defects)} defect(s); comparison 2: {len(actual)} difference(s), '
          f'{len(listed)} listed; details in {os.path.relpath(out, SPEC)}')
    return 0 if not defects and not faults else 1


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
