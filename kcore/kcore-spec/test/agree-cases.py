"""Build the agreement cases (test/agree.jsonl, read by `kcore agree`) from the reference backends'
cached outputs (K-rust's reference-outputs cache, ~/.cache/k-rust/reference-outputs/v1, or
$KCORE_REFERENCE_CACHE). The expected results are only those cached outputs.

Two kompiled texts are the same definition when their `definition.kore` texts are equal once the
comments and the `Source` and `Location` attributes (where the text was compiled from) are removed.

- kore-exec (`DEF --module M --pattern P --output O [--depth N]`): the input is the pattern P, a
  fixture of the K-rust repository (read from the path in the entry when its sha256 matches, otherwise
  from $KRUST_CHECKOUT at the same path below `crates/`), the expected result the file O in the
  entry's archive, the mode `execute` (to depth N when given). One case per (definition, pattern,
  module, depth, result), the entries of one case listed in its source.
- krun: a program text is parsed by K inside the run, so a KORE input exists only where a
  `--depth 0` run of the same program, `-c` options and definition is cached: its output is the input
  of the group's other runs (`--depth N`: execute; `--search-final`, `--search-all`: search;
  `--search-one-step`: step). The definition of a run is found by recomputing the tree digest of each
  kompile entry's archive (scripts/reference_cache.py, `tree_digest`) and matching it with the run's
  `--definition` input.

A definition is named by the path of its text in the corpus extraction (test/corpus.py writes
.lake/corpus/defs/SHA16.kore), relative to this file's directory. The runs not usable (a group without
a depth-0 run, a definition whose kompile entry is not cached) are counted on stderr; `--wanted`
lists them.

Usage: python3 -I test/agree-cases.py [--wanted] > test/agree.jsonl"""
import collections, hashlib, io, json, os, re, subprocess, sys, tarfile

CACHE = os.environ.get('KCORE_REFERENCE_CACHE', os.path.expanduser('~/.cache/k-rust/reference-outputs/v1'))
ENTRIES = os.path.join(CACHE, 'entries')
DEFDIR = '../.lake/corpus/defs'


def entries():
    for d1 in sorted(os.listdir(ENTRIES)):
        for e in sorted(os.listdir(os.path.join(ENTRIES, d1))):
            p = os.path.join(ENTRIES, d1, e)
            try:
                key = json.load(open(os.path.join(p, 'key.json')))
                meta = json.load(open(os.path.join(p, 'meta.json')))
                res = json.load(open(os.path.join(p, 'result.json')))
            except (OSError, ValueError):
                continue
            yield e, p, key, meta, res


def members(p, res):
    if not res.get('archive'):
        return []
    data = subprocess.run(['zstd', '-dc', os.path.join(p, res['archive'])], capture_output=True, check=True).stdout
    tf = tarfile.open(fileobj=io.BytesIO(data))
    out = []
    for m in tf.getmembers():
        b = tf.extractfile(m).read() if m.isfile() else None
        out.append((m, b))
    return out


def tree_digest(ms, root):
    """The digest scripts/reference_cache.py's tree_digest gives the directory restored from the
    archive members below `root`: a record per directory, file and link, sorted by relative path."""
    recs = {}
    for m, b in ms:
        if not m.name.startswith(root + '/'):
            continue
        rel = m.name[len(root) + 1:]
        parts = rel.split('/')
        for i in range(1, len(parts)):
            recs.setdefault('/'.join(parts[:i]), 'D ' + '/'.join(parts[:i]))
        if m.isdir():
            recs[rel] = f'D {rel}'
        elif m.issym():
            recs[rel] = f'L {rel}\0{m.linkname}'
        elif m.isfile():
            recs[rel] = f'F {rel}\0{m.mode & 0o111:o}\0{hashlib.sha256(b).hexdigest()}'
    h = hashlib.sha256()
    for rel in sorted(recs):
        h.update(recs[rel].encode('utf-8', 'surrogateescape') + b'\n')
    return h.hexdigest()


ATTR = re.compile(rb'(Source|Location)\{\}\((?:"(?:[^"\\]|\\.)*"\s*,?\s*)*\)\s*,?\s*')
COMMENT = re.compile(rb'^\s*//.*$', re.M)


def normal(b):
    """The text without its comments and its Source and Location attributes."""
    return hashlib.sha256(ATTR.sub(b'', COMMENT.sub(b'', b))).hexdigest()


def main():
    wanted = '--wanted' in sys.argv
    trees = {}          # tree digest -> (sha16 of definition.kore, normalized hash)
    normals = {}        # sha16 of definition.kore -> normalized hash
    kexec, krun = [], []
    for e, p, key, meta, res in entries():
        tool = meta.get('tool')
        if tool == 'kompile' and res.get('rc') == 0:
            ms = members(p, res)
            for root in sorted({m.name.split('/')[0] for m, _ in ms}):
                d = [b for m, b in ms if m.name == root + '/definition.kore']
                if d:
                    trees['tree:' + tree_digest(ms, root)] = (hashlib.sha256(d[0]).hexdigest()[:16], normal(d[0]))
                    normals[hashlib.sha256(d[0]).hexdigest()[:16]] = normal(d[0])
        elif tool == 'kore-exec':
            kexec.append((e, p, key, meta, res))
        elif tool == 'krun':
            krun.append((e, p, key, meta, res))
    cases, missing = [], collections.Counter()
    want = []
    seen = {}
    for e, p, key, meta, res in kexec:
        a = key['argv']
        af = dict((k, v) for k, v in key['argument_files'])
        pat = a[a.index('--pattern') + 1]
        dsha = af[a[1]]
        depth = int(a[a.index('--depth') + 1]) if '--depth' in a else None
        module = a[a.index('--module') + 1]
        text = None
        for cand in [pat] + ([os.path.join(os.environ['KRUST_CHECKOUT'], 'crates', pat.split('/crates/', 1)[1])]
                             if 'KRUST_CHECKOUT' in os.environ and '/crates/' in pat else []):
            if os.path.exists(cand) and hashlib.sha256(open(cand, 'rb').read()).hexdigest() == af[pat]:
                text = open(cand).read()
                break
        if text is None:
            missing['kore-exec: pattern not found'] += 1
            want.append(f'kore-exec {e[:12]} {meta.get("label")}: pattern {pat} not found (set KRUST_CHECKOUT)')
            continue
        out = [b for m, b in members(p, res) if b is not None]
        if res.get('rc') != 0 or len(out) != 1:
            missing['kore-exec: no output'] += 1
            continue
        k = (normals.get(dsha[:16], dsha), af[pat], module, depth, hashlib.sha256(out[0]).hexdigest())
        if k in seen:
            seen[k]['source'] += f', {e[:12]}'
            continue
        case = {'id': f'kore-exec/{meta.get("label")}/{dsha[:8]}', 'definition': f'{DEFDIR}/{dsha[:16]}.kore',
                'module': module, 'input': text.strip(), 'mode': 'execute', 'expected': out[0].decode().strip(),
                'source': f'kore-exec {e[:12]} ({meta.get("label")}, K {key["pins"]["k"]["version"]})'}
        if depth is not None:
            case['depth'] = depth
        cases.append(case)
        seen[k] = case
    groups = collections.defaultdict(list)
    for e, p, key, meta, res in krun:
        a = key['argv']
        ins = dict((k, v) for k, v in key.get('inputs', []))
        d = a[a.index('--definition') + 1]
        tr = ins.get(d)
        if tr not in trees:
            missing['krun: definition not cached'] += 1
            want.append(f'krun {e[:12]} {meta.get("label")}: no kompile entry with the definition {str(tr)[:20]}')
            continue
        sha16, nh = trees[tr]
        prog = key['argument_files'][0][1] if key.get('argument_files') else ('term:' + a[a.index('--term') + 1] if '--term' in a else '')
        co = tuple(x for x in a if x.startswith('-c'))
        groups[(prog, co, nh)].append((e, p, key, meta, res, sha16))
    for (prog, co, nh), runs in sorted(groups.items()):
        zero = [r for r in runs if '--depth' in r[2]['argv'] and r[2]['argv'][r[2]['argv'].index('--depth') + 1] == '0'
                and not any(x.startswith('--search') for x in r[2]['argv']) and r[4].get('rc') == 0]
        if not zero:
            for e, p, key, meta, res, sha16 in runs:
                missing['krun: no depth-0 run of its program'] += 1
                want.append(f'krun {e[:12]} {meta.get("label")}: no cached --depth 0 run of the program '
                            f'{key["argv"][1]} with {" ".join(co) or "no -c"} on this definition')
            continue
        e0, p0, key0, meta0, res0, sha0 = zero[0]
        inp = open(os.path.join(p0, 'stdout')).read().strip()
        done = set()
        for e, p, key, meta, res, sha16 in runs:
            a = key['argv']
            if res.get('rc') != 0:
                continue
            depth = int(a[a.index('--depth') + 1]) if '--depth' in a else None
            flags = [x for x in a if x.startswith('--search')]
            mode = {'--search-final': 'search-final', '--search': 'search-final', '--search-all': 'search-all',
                    '--search-one-step': 'step'}.get(flags[0], flags[0]) if flags else 'execute'
            k = (mode, depth)
            if k in done:
                continue
            done.add(k)
            case = {'id': f'krun/{meta.get("label")}/{mode}{"" if depth is None else depth}/{sha16[:8]}',
                    'definition': f'{DEFDIR}/{sha16}.kore', 'input': inp, 'mode': mode,
                    'expected': open(os.path.join(p, 'stdout')).read().strip(),
                    'source': f'krun {e[:12]} ({meta.get("label")}, K {key["pins"]["k"]["version"]}); '
                              f'input: krun --depth 0 {e0[:12]} ({meta0.get("label")})'}
            if depth is not None:
                case['depth'] = depth
            cases.append(case)
    for c in cases:
        print(json.dumps(c))
    print(f'{len(cases)} cases ({sum(c["id"].startswith("kore-exec") for c in cases)} kore-exec, '
          f'{sum(c["id"].startswith("krun") for c in cases)} krun); not usable: {dict(missing)}', file=sys.stderr)
    if wanted:
        for w in want:
            print(w, file=sys.stderr)


main()
