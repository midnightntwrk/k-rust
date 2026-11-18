"""The corpus read natively: every distinct `definition.kore` of the reference cache's kompile
entries (K-rust's reference-outputs cache, `~/.cache/k-rust/reference-outputs/v1/entries/*/*`,
whose `files.tar.zst` archive holds the kompiled directory), each given to
`kcore gen TEXT PKG Cov --core`, which prints the account's classes and stops at the reader's
refusals, the unaccounted sentences, the account's refusals, or a failing `coreOK`.

A text is `clean` when its log names none of those refusals, and `coreOK` when `kcore gen` succeeds
(`coreOK` holds and the package is written). One line per text, `SHA16 clean|unclean coreOK|no`,
sorted, compared with an expected file; then the counts.

The texts are extracted once into .lake/corpus/defs (named by the first 16 hex digits of their
sha256, with .lake/corpus/index.json saying which cache entries hold each); a text added to the
cache is extracted on the next run. Logs per text in .lake/corpus/log, the packages in
.lake/corpus/pkg/N (one directory a worker; `kcore gen` replaces its own `Cov` directory).
Each `kcore gen` runs under a 12 GiB memory scope, JOBS at once.

Usage (from kcore-spec, `kcore` built): python3 -I test/corpus.py [-j JOBS] [--expected FILE]
  [--write-expected FILE]. Exit 1 when the lines differ from the expected file."""
import concurrent.futures, hashlib, io, json, os, subprocess, sys, tarfile, threading, time

K = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CACHE = os.environ.get('KCORE_REFERENCE_CACHE', os.path.expanduser('~/.cache/k-rust/reference-outputs/v1'))
OUT = os.path.join(K, '.lake/corpus')
DEFS = os.path.join(OUT, 'defs')
CAP = ['systemd-run', '--user', '--scope', '-q', '-p', 'MemoryMax=12G', '-p', 'MemorySwapMax=0', 'timeout', '300']
REFUSALS = ('refuses it', 'does not account', 'refusals of the account', 'KORE read error')


def extract():
    """Every kompile entry's definition.kore (not syntaxDefinition.kore) into DEFS, once per entry."""
    os.makedirs(DEFS, exist_ok=True)
    ip = os.path.join(OUT, 'index.json')
    idx = json.load(open(ip)) if os.path.exists(ip) else {}
    done = {e['entry'] for v in idx.values() for e in v}
    root = os.path.join(CACHE, 'entries')
    for d1 in sorted(os.listdir(root)):
        for e in sorted(os.listdir(os.path.join(root, d1))):
            if e in done:
                continue
            p = os.path.join(root, d1, e)
            try:
                res = json.load(open(os.path.join(p, 'result.json')))
            except (OSError, ValueError):
                continue
            if not res.get('archive'):
                continue
            files = [f for fs in res.get('changed', {}).values() for f in fs]
            if not any(f.endswith('definition.kore') and not f.endswith('syntaxDefinition.kore') for f in files):
                continue
            meta = json.load(open(os.path.join(p, 'meta.json')))
            data = subprocess.run(['zstd', '-dc', os.path.join(p, res['archive'])], capture_output=True, check=True).stdout
            with tarfile.open(fileobj=io.BytesIO(data)) as tf:
                for m in tf.getmembers():
                    if not m.isfile() or not m.name.endswith('/definition.kore') or m.name.endswith('syntaxDefinition.kore'):
                        continue
                    b = tf.extractfile(m).read()
                    h = hashlib.sha256(b).hexdigest()[:16]
                    fn = os.path.join(DEFS, h + '.kore')
                    if not os.path.exists(fn):
                        with open(fn + '.part', 'wb') as f:
                            f.write(b)
                        os.replace(fn + '.part', fn)
                    idx.setdefault(h, []).append({'entry': e, 'member': m.name, 'label': meta.get('label'),
                                                  'tool': meta.get('tool'), 'size': len(b)})
    json.dump(idx, open(ip, 'w'), indent=1, sort_keys=True)
    return idx


def main():
    args = sys.argv[1:]
    jobs, expected, write = 1, None, None
    while args:
        a = args.pop(0)
        if a == '-j': jobs = int(args.pop(0))
        elif a == '--expected': expected = args.pop(0)
        elif a == '--write-expected': write = args.pop(0)
        else: sys.exit(f'unknown argument {a}')
    t0 = time.time()
    idx = extract()
    texts = sorted(idx, key=lambda h: os.path.getsize(os.path.join(DEFS, h + '.kore')), reverse=True)
    os.makedirs(os.path.join(OUT, 'log'), exist_ok=True)
    exe = os.path.join(K, '.lake/build/bin/kcore')
    local = threading.local()
    slots = iter(range(jobs))
    lock = threading.Lock()

    def run(h):
        if not hasattr(local, 'pkg'):
            with lock:
                local.pkg = os.path.join(OUT, 'pkg', str(next(slots)))
        r = subprocess.run(CAP + [exe, 'gen', os.path.join(DEFS, h + '.kore'), local.pkg, 'Cov', '--core'],
                           capture_output=True, text=True)
        log = r.stdout + r.stderr
        open(os.path.join(OUT, 'log', h + '.gen'), 'w').write(log)
        clean = not any(s in log for s in REFUSALS)
        return f"{h} {'clean' if clean else 'unclean'} {'coreOK' if r.returncode == 0 else 'no'}"

    with concurrent.futures.ThreadPoolExecutor(jobs) as ex:
        lines = sorted(ex.map(run, texts))
    open(os.path.join(OUT, 'results.txt'), 'w').write('\n'.join(lines) + '\n')
    n = len(lines)
    nc = sum(' clean ' in l for l in lines)
    nk = sum(l.endswith(' coreOK') for l in lines)
    print(f'corpus: {n} texts, read clean {nc}, coreOK {nk} ({time.time() - t0:.0f} s)')
    if write:
        open(write, 'w').write('\n'.join(lines) + '\n')
    if expected:
        want = [l for l in open(expected).read().split('\n') if l]
        if want != lines:
            w, g = set(want), set(lines)
            for l in sorted(w - g): print('  expected:', l)
            for l in sorted(g - w): print('  now:     ', l)
            print(f'corpus: differs from {os.path.relpath(expected, K)} (expected read clean '
                  f"{sum(' clean ' in l for l in want)}, coreOK {sum(l.endswith(' coreOK') for l in want)})")
            sys.exit(1)
        print(f'corpus: as expected ({os.path.relpath(expected, K)})')


if __name__ == "__main__":
    main()
