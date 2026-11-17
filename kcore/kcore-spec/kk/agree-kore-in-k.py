"""Build the agreement cases of the kore-in-k corpus (kk/agree-kore-in-k.jsonl, read by `kcore agree`)
from that corpus's directory: the argument, else $KORE_IN_K (krs/semantics/kore of a checkout of the
kore-in-k branch). The expected results are only the corpus's recorded ones: the haskell and llvm
rows of each case's `evidence.json` (`implementations`).

A corpus case `cases/<id>/` is an object definition `def.k` (`configuration <k> $PGM:S </k>`, or a
top cell holding `<k> $PGM:S </k>` and other cells), its initial term `pgm.kore` (KORE of sort S)
and, per backend (haskell, llvm), the final configurations of `krun --search` in the corpus's
canonical text (its README, "A case"), or the backend's error. Each (case, backend) is one line:

- `definition`: the case's kompiled text, `../.lake/kore-in-k/build/<id>/hs/definition.kore`, built
  here by the corpus's own `tools/case.py` (needs $K_KOMPILE) on a copy of the case in
  `.lake/kore-in-k/cases/<id>/`, so the corpus is not written; case.py runs with `--no-backends`,
  so no reference backend runs. A case whose `def.k` or `pgm` differs from the `inputs` its
  `evidence.json` records is refused here before case.py runs, and the copy's `inputs` and
  `implementations` must be the corpus's after it. The texts case.py regenerates in the copy
  (`pgm.kore`, `kore.pgm`, `symbols.json`) are compared with the corpus's, a difference reported on
  stderr. A kompiled text whose `inputs.json` stamp (case.py's) matches is not rebuilt.
- `input`: the initial configuration, kompile's `initGeneratedTopCell` at `$PGM |-> PGM` with PGM the
  corpus's `pgm.kore`, its initializer equations unfolded by the corpus's own encoder
  (`tools/korek.py`, `Encoder.unfold`, reading them from the kompiled text) and printed as KORE; for
  the one cell `<k>` that is `<generatedTop>(<k>(kseq(inj{S,KItem}(PGM), dotk())),
  <generatedCounter>(0))`, written so (and checked equal to the unfolding).
- `mode`: `search-final` without a depth: every configuration reachable from the input that has no
  successor.
- `expected`: the backend's finals as KORE: each canonical item put back in the `<k>` cell of the
  one-cell configuration above, or, for several cells (the canonical text keeps the whole top cell
  `Lbl'-LT-'…'-GT-'(…)` then), that cell under `<generatedTop>` (no corpus definition uses `!X`, so
  the counter stays 0); an integer as a `SortInt` domain value, `true`/`false` as `SortBool` ones,
  `#token("t",SortX)` as `\\dv{SortX{}}("t")`, `inj{A,B}(v)` as written, a collection
  `SortX{...}`/`SortX[...]` as the concatenation of its element symbols applied to its elements (the
  symbols named by the case's `symbols.json`; a `Map` cell collection's sort too), the unit for none.
  A final under conditions ` if C and C'…` is `\\and(CONFIG, φ)`, φ the condition (the conditions
  joined by `\\and`): `defined(Q)` as `\\ceil(Q)`, `A=B` as `\\equals(A, B)`, `not(C)` as
  `\\not(C)`, the operand sort read from the value (a domain value's or an injection's sort, else
  the kompiled text's declaration of its head). A backend's error gives no `expected` and
  `no_reference` its text: verdict `no-reference`.

Usage: python3 -I kk/agree-kore-in-k.py [DIR] > kk/agree-kore-in-k.jsonl"""
import hashlib, json, os, re, shutil, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
SPEC = os.path.dirname(HERE)
WORK = os.path.join(SPEC, '.lake', 'kore-in-k')
BUILD = os.path.join(WORK, 'build')
COPIES = os.path.join(WORK, 'cases')
DEFREL = '../.lake/kore-in-k/build'
BACKENDS = ('haskell', 'llvm')
COPIED = ('def.k', 'pgm', 'entry.toml', 'evidence.json', 'pgm.kore', 'kore.pgm', 'symbols.json')
REGENERATED = ('pgm.kore', 'kore.pgm', 'symbols.json')


def sha(path):
    with open(path, 'rb') as f:
        return hashlib.sha256(f.read()).hexdigest()


def kompiled(cid, key):
    """The case's kompiled text, building it with case.py where its stamp does not match `key`."""
    out = os.path.join(BUILD, cid, 'hs', 'definition.kore')
    stamp = os.path.join(BUILD, cid, 'inputs.json')
    if os.path.exists(out) and os.path.exists(stamp) and json.load(open(stamp)) == key:
        return out
    return None


def recorded(ev):
    """What case.py must leave as it is in a copy of the case: the hashes of def.k and pgm, and the
    implementations' results."""
    inputs = ev.get('inputs') or {}
    return {'def.k': inputs.get('def.k'), 'pgm': inputs.get('pgm')}, ev.get('implementations')


def build(corpus, cid):
    src = os.path.join(corpus, 'cases', cid)
    ev = json.load(open(os.path.join(src, 'evidence.json')))
    key = {'def.k': sha(os.path.join(src, 'def.k')), 'pgm': sha(os.path.join(src, 'pgm'))}
    if recorded(ev)[0] != key:
        sys.exit(f'{cid}: def.k or pgm differs from the inputs evidence.json records; its recorded '
                 'results are not of this text')
    if kompiled(cid, key):
        return
    if not os.environ.get('K_KOMPILE'):
        sys.exit(f'{cid}: no kompiled text at {BUILD}/{cid}; set K_KOMPILE to build it with case.py')
    copy = os.path.join(COPIES, cid)
    shutil.rmtree(copy, ignore_errors=True)
    os.makedirs(copy)
    for f in COPIED:
        shutil.copy(os.path.join(src, f), copy)
    env = dict(os.environ, KORE_IN_K_BUILD=BUILD)
    r = subprocess.run([sys.executable, '-I', os.path.join(corpus, 'tools', 'case.py'), '--no-backends', copy],
                       env=env, capture_output=True, text=True)
    print(f'{cid}: case.py: {r.stdout.strip()[:300]}', file=sys.stderr)
    if r.returncode != 0 or not kompiled(cid, key):
        sys.exit(f'{cid}: case.py failed (exit {r.returncode}): {r.stderr[-2000:]}')
    if recorded(json.load(open(os.path.join(copy, 'evidence.json')))) != recorded(ev):
        sys.exit(f'{cid}: case.py changed the inputs or the implementations of evidence.json')
    for f in REGENERATED:
        if sha(os.path.join(copy, f)) != sha(os.path.join(src, f)):
            print(f'{cid}: the regenerated {f} differs from the corpus\'s', file=sys.stderr)


TOKEN = re.compile(r"\s*(#token\(\"(?:[^\"\\]|\\.)*\",Sort\w+\)|\|->|[(){}\[\],=]|-?[0-9]+|[A-Za-z][A-Za-z0-9'\-]*)")
TOKLIT = re.compile(r'#token\(("(?:[^"\\]|\\.)*"),(Sort\w+)\)')


def tokens(text):
    out, i = [], 0
    text = text.strip()
    while i < len(text):
        m = TOKEN.match(text, i)
        if not m:
            raise ValueError(f'canonical text: cannot read at {text[i:i + 40]!r}')
        out.append(m.group(1))
        i = m.end()
    return out


class Canon:
    """The corpus's canonical text of a value, read back as KORE."""

    def __init__(self, text, colls):
        self.toks, self.i = tokens(text), 0
        self.colls = colls

    def peek(self):
        return self.toks[self.i] if self.i < len(self.toks) else None

    def next(self):
        t = self.peek()
        if t is None:
            raise ValueError('canonical text: unexpected end')
        self.i += 1
        return t

    def expect(self, t):
        if self.next() != t:
            raise ValueError(f'canonical text: expected {t} at token {self.i}')

    def args(self, close):
        out = []
        if self.peek() == close:
            self.next()
            return out
        while True:
            out.append(self.term())
            t = self.next()
            if t == close:
                return out
            if t != ',':
                raise ValueError(f'canonical text: expected , or {close}, got {t}')

    def term(self):
        t = self.next()
        m = TOKLIT.fullmatch(t)
        if m:
            return f'\\dv{{{m.group(2)}{{}}}}({m.group(1)})'
        if re.fullmatch(r'-?[0-9]+', t):
            return f'\\dv{{SortInt{{}}}}("{t}")'
        if t in ('true', 'false'):
            return f'\\dv{{SortBool{{}}}}("{t}")'
        if t == 'inj':
            self.expect('{')
            a = self.next()
            self.expect(',')
            b = self.next()
            self.expect('}')
            self.expect('(')
            (v,) = self.args(')')
            return f'inj{{{a}{{}}, {b}{{}}}}({v})'
        if t in self.colls and self.peek() in ('{', '['):
            c = self.colls[t]
            close = '}' if self.next() == '{' else ']'
            elems = []
            if self.peek() == close:
                self.next()
            else:
                while True:
                    k = self.term()
                    if c['kind'] == 'map':
                        self.expect('|->')
                        elems.append(f"{c['element']}{{}}({k}, {self.term()})")
                    else:
                        elems.append(f"{c['element']}{{}}({k})")
                    s = self.next()
                    if s == close:
                        break
                    if s != ',':
                        raise ValueError(f'canonical text: expected , or {close}, got {s}')
            if not elems:
                return f"{c['unit']}{{}}()"
            acc = elems[0]
            for e in elems[1:]:
                acc = f"{c['concat']}{{}}({acc}, {e})"
            return acc
        self.expect('(')
        return f'{t}{{}}(' + ', '.join(self.args(')')) + ')'

    def whole(self):
        v = self.term()
        if self.peek() is not None:
            raise ValueError(f'canonical text: trailing {self.toks[self.i:][:5]}')
        return v


TOP = 'SortGeneratedTopCell{}'


def top(cell):
    """The configuration `<generatedTop>(CELL, <generatedCounter>(0))`."""
    return ("Lbl'-LT-'generatedTop'-GT-'{}(" + cell + ", "
            "Lbl'-LT-'generatedCounter'-GT-'{}(\\dv{SortInt{}}(\"0\")))")


def config(item):
    """The configuration of one cell `<k>` holding `item`, or, for a top cell `Lbl'-LT-'…'-GT-'(…)`
    of several cells (the canonical text keeps the whole top cell then), that cell."""
    if item.startswith("Lbl'-LT-'"):
        return top(item)
    return top("Lbl'-LT-'k'-GT-'{}(kseq{}(" + item + ", dotk{}()))")


def result_sort(defn, sym):
    m = re.search(r'\bsymbol\s+' + re.escape(sym) + r'\{\}\([^)]*\)\s*:\s*(Sort[A-Za-z0-9]*)\{\}', defn)
    if not m:
        raise ValueError(f'no declaration of {sym} in the kompiled text')
    return m.group(1)


def sort_of(q, defn):
    """The sort of a value's KORE as the canonical reader writes it."""
    head = q.split('{', 1)[0]
    if head == '\\dv':
        return re.match(r'\\dv\{(Sort\w+)\{\}\}', q).group(1)
    if head == 'inj':
        return re.match(r'inj\{\S+, (Sort\w+)\{\}\}', q).group(1)
    return result_sort(defn, head)


def condition(text, colls, defn):
    """A condition of the canonical text as a KORE predicate of the configuration's sort:
    `defined(Q)` as `\\ceil(Q)`, `A=B` as `\\equals(A, B)`, `not(C)` as `\\not(C)`."""
    text = text.strip()
    m = re.fullmatch(r'(defined|not)\((.*)\)', text)
    if m and m.group(1) == 'defined':
        q = Canon(m.group(2), colls).whole()
        return f'\\ceil{{{sort_of(q, defn)}{{}}, {TOP}}}({q})'
    if m:
        return f'\\not{{{TOP}}}({condition(m.group(2), colls, defn)})'
    r = Canon(text, colls)
    a = r.term()
    r.expect('=')
    b = r.term()
    if r.peek() is not None:
        raise ValueError(f'a condition other than defined(Q), A=B, not(C): {text}')
    return f'\\equals{{{sort_of(a, defn)}{{}}, {TOP}}}({a}, {b})'


def final(text, colls, defn):
    """A canonical final, possibly under conditions ` if C [and C'...]`, as a KORE configuration:
    `\\and(CONFIG, C)`, the conditions joined by `\\and`."""
    item, _, cond = text.partition(' if ')
    c = config(Canon(item, colls).whole())
    cs = [condition(part, colls, defn) for part in cond.split(' and ')] if cond else []
    if not cs:
        return c
    phi = cs[0] if len(cs) == 1 else '\\and{' + TOP + '}(' + ', '.join(cs) + ')'
    return '\\and{' + TOP + '}(' + c + ', ' + phi + ')'


def kore_of(p):
    """A pattern as the corpus's KORE reader (`tools/korek.py`) holds it, printed as KORE."""
    def srt(s):
        return s[0] if s[1] is None else s[0] + '{' + ', '.join(srt(a) for a in s[1]) + '}'
    if p[0] == 'str':
        return json.dumps(p[1])
    if p[0] == 'var':
        raise ValueError(f'a variable in the initial configuration: {p[1]}')
    _, name, sorts, args = p
    return name + '{' + ', '.join(srt(s) for s in sorts) + '}(' + ', '.join(kore_of(a) for a in args) + ')'


def initial(corpus, defn, sort, pgm):
    """The initial configuration: kompile's `initGeneratedTopCell` at the map `$PGM |-> PGM`, its
    initializer equations unfolded by the corpus's own encoder (`korek.Encoder.unfold`, which reads
    them from the kompiled text). For the one cell `<k>` it is written as before,
    `<generatedTop>(<k>(kseq(inj{S,KItem}(PGM), dotk())), <generatedCounter>(0))` (checked)."""
    sys.dont_write_bytecode = True  # the corpus is read, not written
    sys.path.insert(0, os.path.join(corpus, 'tools'))
    import korek
    head = defn.split('\n', 1)[0]
    src = re.search(r'Source\{\}\("Source\(([^)]*)\)"\)', head).group(1)
    ti = re.search(r'topCellInitializer\{\}\((\S+?)\{\}\(\)\)', head).group(1)
    e = korek.Encoder(korek.read_definition(defn), src, ti)
    t = e.unfold(('app', ti, (), (('var', 'Init', None),)), {'Init': None}, korek.read_pattern(pgm))
    if t[0] != 'app' or t[1] != "Lbl'-LT-'generatedTop'-GT-'" or kore_of(t[3][1]) != \
            "Lbl'-LT-'generatedCounter'-GT-'{}(\\dv{SortInt{}}(\"0\"))":
        raise ValueError(f'initial configuration of another shape: {kore_of(t)[:200]}')
    one = config(f'inj{{Sort{sort}{{}}, SortKItem{{}}}}({pgm})')
    if t[3][0][1] == "Lbl'-LT-'k'-GT-'":
        k = korek.read_pattern(one)
        if kore_of(k) != kore_of(t):
            raise ValueError(f'the one-cell initial configuration is not the one unfolded: {kore_of(t)[:200]}')
        return one
    return kore_of(t)


def main(argv):
    corpus = argv[0] if argv else os.environ.get('KORE_IN_K')
    if not corpus or not os.path.isdir(os.path.join(corpus, 'cases')):
        sys.exit('usage: agree-kore-in-k.py DIR (or $KORE_IN_K): the kore-in-k corpus directory, with cases/')
    corpus = os.path.abspath(corpus)
    ids = sorted(d for d in os.listdir(os.path.join(corpus, 'cases'))
                 if os.path.isfile(os.path.join(corpus, 'cases', d, 'def.k')))
    for cid in ids:
        build(corpus, cid)
    for cid in ids:
        src = os.path.join(corpus, 'cases', cid)
        defk = open(os.path.join(src, 'def.k')).read()
        sort = re.search(r'\$PGM:(\w+)', defk).group(1)
        what = defk.splitlines()[0].lstrip('/ ').strip()
        pgm = open(os.path.join(src, 'pgm.kore')).read().strip()
        colls = {s: c for s, c in json.load(open(os.path.join(src, 'symbols.json'))).get('collections', {}).items()}
        rows = json.load(open(os.path.join(src, 'evidence.json')))['implementations']
        defn = open(os.path.join(BUILD, cid, 'hs', 'definition.kore')).read()
        init = initial(corpus, defn, sort, pgm)
        for b in BACKENDS:
            r = rows[b]
            case = {'id': f'{cid}/{b}', 'definition': f'{DEFREL}/{cid}/hs/definition.kore',
                    'input': init, 'mode': 'search-final'}
            if 'finals' in r:
                fs = [final(t, colls, defn) for t in r['finals']]
                case['expected'] = ('\\bottom{SortGeneratedTopCell{}}()' if not fs else fs[0] if len(fs) == 1
                                    else '\\or{SortGeneratedTopCell{}}(' + ', '.join(fs) + ')')
            else:
                case['no_reference'] = f"{b} backend error: {r.get('error', '')}"
            case['source'] = {'case': f'cases/{cid}', 'tests': what, 'backend': b,
                              'reference': r['version'], 'canonical': r.get('finals', r.get('error'))}
            print(json.dumps(case))


if __name__ == '__main__':
    main(sys.argv[1:])
