#!/usr/bin/env python3
"""Write the tool-written files of entries of kore-in-k (SCHEMA.md), or check their quotes.

  case.py [--refresh] [--no-backends] [--import kcore=FILE] (--all | ENTRY...)
  case.py --verify-quotes K_CHECKOUT (--all | ENTRY...)

ENTRY is cases/<id> or texts/<id>, relative to the package directory, or absolute. --all names
every case under cases/ (a text entry is named), and under --verify-quotes, which writes nothing,
every entry under cases/ and texts/.

An entry's entry.toml is written by hand. This script reads it and never creates or changes it: it
stops at an entry that has none. For each entry it writes, into the entry's directory:

  evidence.json  inputs: the SHA-256 of each file of [text].files and of the answer fields
                 (check.answer_hash); kompile: the release, the command, the exit code, the hash
                 of kore.txt and, where kompile refused the text, its message; for a case,
                 ruling_canonical: the finals of the ruling and of each reading in the canonical
                 text of tools/korek.py; implementations: each implementation's result
  kompile.txt    kompile's command, release, exit code and messages, with the entry's and the
                 build's directories and the store paths of the K installation replaced by names,
                 and the process numbers kore-exec prints replaced by PID
  kore.txt       where kompile accepted the text: the sentences of the main module that come from
                 no builtin file of K and that an empty module's main module does not hold (the
                 sentences the text adds to an empty module), in their order, each after a line
                 `//@ N`, N its index among the main module's sentences (a `// rule` comment
                 belongs to the axiom after it); their Source and Location attributes removed and
                 the variables kompile generates renumbered by first occurrence in each sentence,
                 since kompile numbers them differently from run to run
and, for a case whose text kompile accepts:
  pgm.kore       kast pgm --output kore against the haskell-kompiled def.k: the initial term
  kore.pgm       the encoded program for kore.k (tools/korek.py encode)
  symbols.json   the encoder's numbering of symbols and sorts

A case is def.k (module CASE, syntax module CASE-SYNTAX) and pgm; it is kompiled with
`kompile def.k --main-module CASE --syntax-module CASE-SYNTAX --backend haskell`. A text entry's
one K file is kompiled with `kompile --backend haskell FILE` in a copy of the entry's directory. A
KORE text and a quoted declaration are not kompiled. kompile's refusal of a text is a result: it
is recorded (exit code and message, no kore.txt) whatever [text].kompile says; an exit code other
than the one [text].kompile states is reported here (exit 1) and is a schema fault for
tools/check.py.

ruling_canonical. Each term of `finals` (of [ruling], and of each [[reading]]) is written in the
syntax of def.k and parsed by kast against the kompiled def.k, in module CASE: for a configuration
of the one cell <k>, the term the cell holds, by the program parser at sort KItem; for a
configuration of several cells, the top cell, by the rule parser with no compilation step. A term
that kast does not parse, or whose parse holds a variable or applies a symbol to another number of
arguments than its declaration's, stops the entry with an error naming the term. kast's rule
parser refuses a cell collection of two or more instances, and gives one of none an application
of the wrong arity: such finals are written as finals_canonical, the canonical text itself, which
is taken as written. A reading whose answer is prose has no key.

implementations. The haskell backend (krun --search) and the llvm backend (kompiled with
--enable-search) are run on a case, and their final configurations written as canonical text
(tools/korek.py ref), sorted, or the backend's error. They are a cache: they are rerun only when
the SHA-256 of def.k or pgm differs from evidence.json's inputs, or under --refresh. A row of
evidence.json whose inputs are not current is not kept.

--no-backends     runs kompile, kast and the encoder only; the recorded backend rows are kept while
                  their inputs are current.
--import kcore=FILE
                  adds the kcore row. FILE is JSON: {"version": TEXT, "results": {ID: {"finals":
                  [canonical texts]} or {"error": TEXT}}}. The row of an entry FILE names is
                  {"version", "finals" or "error", "imported_from": the SHA-256 of FILE}; an entry
                  FILE does not name keeps its kcore row while its inputs are current.
--verify-quotes K_CHECKOUT
                  writes nothing and runs no K tool: checks that the quote of each basis
                  ([[ruling.basis]], [[ruling.kore.basis]], [text].declaration) stands at its
                  locator. A locator is `PATH:LINES`, LINES a line, a range A-B, or several
                  separated by commas, optionally followed by `(K RELEASE)`, which must be the
                  checkout's (package/version). PATH is relative to K_CHECKOUT, or to the entry's
                  directory for source = "kompiled"; `haskell-backend/P` (`llvm-backend/P`) that is
                  no file of the checkout is P in the backend's sources as the release pins them,
                  `haskell-backend/src/main/native/haskell-backend/P`. The quote, whitespace
                  collapsed, must occur in the lines, joined by a space and whitespace collapsed;
                  a quote with ` ... ` must hold its parts in that order there. Exit 1 when a
                  quote is not at its locator.

Tools: the K toolchain is found as the repository's gates find it, beside $K_KOMPILE, else on
PATH; without it the script exits 2. Every K run is under a 120 s timeout and a memory bound: a
transient systemd user scope (MemoryMax=12G, no swap) where one can be started, else an address
space limit of 24 GiB. $K_OPTS overrides the JVM options. The build directory, which holds the
kompiled texts (not part of the package: their Source attributes name absolute paths), is
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
import check  # noqa: E402
import korek  # noqa: E402

BUILD = os.environ.get('KORE_IN_K_BUILD', os.path.join(tempfile.gettempdir(), 'kore-in-k'))
TIMEOUT_S = 120
K_OPTS = os.environ.get('K_OPTS', '-Xmx2048m -Xss8m -XX:+UseSerialGC')
SCOPE = ['systemd-run', '--user', '--scope', '-q', '-p', 'MemoryMax=12G', '-p', 'MemorySwapMax=0']
FALLBACK_AS_BYTES = 24 << 30
BACKENDS = ('haskell', 'llvm')
BUILTIN = '/include/kframework/builtin/'
EMPTY_MODULE = 'module EMPTY-MODULE\nendmodule\n'


class Refused(Exception):
    """An entry this script does not build, with the reason."""


# ------------------------------------------------------------------ running K


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
        self.cached = {}

    def tool(self, name):
        return os.path.join(self.bin, name)

    def installation(self):
        """The K installation, by the real path of its kompile."""
        return os.path.realpath(self.tool('kompile'))

    def run(self, cmd, out=None, cwd=None):
        """Run a K tool; its stdout goes to `out`. Returns (exit code, stderr then stdout, wall ms)."""
        env = dict(os.environ, K_OPTS=K_OPTS)
        prefix = (SCOPE if self.scoped else []) + ['timeout', str(TIMEOUT_S)]

        def limit():
            if not self.scoped:
                resource.setrlimit(resource.RLIMIT_AS, (FALLBACK_AS_BYTES, FALLBACK_AS_BYTES))

        os.makedirs(BUILD, exist_ok=True)
        start = time.monotonic()
        r = subprocess.run(prefix + cmd, capture_output=True, text=True, env=env, cwd=cwd or BUILD,
                           preexec_fn=limit)
        ms = int((time.monotonic() - start) * 1000)
        if out:
            with open(out, 'w') as f:
                f.write(r.stdout)
        return r.returncode, r.stderr + r.stdout, ms

    def must(self, cmd, out=None, cwd=None):
        code, text, ms = self.run(cmd, out, cwd)
        if code != 0:
            raise RuntimeError(f'{os.path.basename(cmd[0])}: exit {code}\n{text[-3000:]}')
        return ms

    def kompile(self, args, cwd):
        """kompile ARGS in cwd: (exit code, output). A timeout or a kill is no result of kompile."""
        code, text, _ = self.run([self.tool('kompile')] + args, cwd=cwd)
        if code in (124, 137, -9):
            raise RuntimeError(f'kompile did not finish (exit {code}): {text[-1000:]}')
        return code, text

    def kast(self, args):
        """kast ARGS: (exit code, stdout, stderr then stdout)."""
        out = os.path.join(BUILD, f'kast.{os.getpid()}.out')
        code, text, _ = self.run([self.tool('kast')] + args, out=out)
        with open(out) as f:
            stdout = f.read()
        os.remove(out)
        return code, stdout, text

    def release(self):
        if 'release' not in self.cached:
            k = subprocess.run([self.tool('kompile'), '--version'], capture_output=True, text=True,
                               env=dict(os.environ, K_OPTS=K_OPTS)).stdout
            self.cached['release'] = 'K ' + re.search(r'K version:\s*(\S+)', k).group(1)
        return self.cached['release']

    def versions(self):
        if 'versions' not in self.cached:
            k = self.release()
            hs = subprocess.run([self.tool('kore-exec'), '--version'], capture_output=True,
                                text=True).stdout.split()[0]
            llvm = subprocess.run([self.tool('llvm-backend-version')], capture_output=True,
                                  text=True).stdout.strip()
            self.cached['versions'] = {
                'haskell': f'{k}: kompile --backend haskell; krun --search (kore-exec {hs})',
                'llvm': f'{k}: kompile --backend llvm --enable-search; krun --search (llvm backend {llvm})',
            }
        return self.cached['versions']


def error_class(text):
    """A backend failure as stable text: the hook's message and the failing K tool, without the
    temporary paths and times krun prints."""
    def unpath(s):
        return ' '.join(re.sub(r'\S*/(\S+)', r'\1', s).split())

    found = []
    for pattern in (r'\[hook_[A-Za-z_]+\][^\n]*', r'what\(\):[^\n]*', r'Error \([A-Za-z]+\)',
                    r'Unable to instantiate semantic rule[^\n]*', r'\[Error\][^\n]*'):
        m = re.search(pattern, text)
        if m and not any(f in unpath(m.group(0)) for f in found):
            found.append(unpath(m.group(0)))
    if found:
        return '; '.join(found)
    last = [ln for ln in text.splitlines() if ln.strip()][-1:] or ['(no output)']
    return unpath(last[0])


def unpath(text, names):
    """text with each directory of `names` (path -> name; the name '' drops the directory) replaced,
    and the store paths of the K installation by NIXSTORE, so that it names no absolute path."""
    for path, name in sorted(names.items(), key=lambda pn: -len(pn[0])):
        text = text.replace(path + '/', name + '/' if name else '').replace(path, name or '.')
    return re.sub(r'/nix/store/[a-z0-9]{32}-[^/\s"]*', 'NIXSTORE', text)


def unpid(text):
    """text with the process numbers kore-exec prints in its messages replaced by PID, so that a
    rebuild of the same text writes the same file."""
    return re.sub(r'(kore-exec: )\[\d+\]', r'\1[PID]', text)


def sha(path):
    with open(path, 'rb') as f:
        return hashlib.sha256(f.read()).hexdigest()


def read_json(path):
    with open(path) as f:
        return json.load(f)


def write_json(path, value):
    with open(path, 'w') as f:
        json.dump(value, f, indent=1, sort_keys=True)
        f.write('\n')


def write_text(path, text):
    with open(path, 'w') as f:
        f.write(text)


# ------------------------------------------------------------------ kore.txt

ATTR = re.compile(r",? ?org'Stop'kframework'Stop'attributes'Stop'(?:Source|Location)\{\}\(\"[^\"]*\"\)"
                  r"|,? ?org\.kframework\.attributes\.(?:Source|Location)\((?:Source|Location)\([^)]*\)\)")
SENT = re.compile(r'^(  (axiom|symbol|sort|hooked-symbol|hooked-sort|import|alias|claim)\b|module |endmodule)')
GEN = re.compile(r"(Var'Unds'Gen|_Gen)(\d+)")


def main_module(kore):
    """The lines of the last module of a kompiled text (kompile writes the main module last)."""
    lines = kore.split('\n')
    start = max(i for i, ln in enumerate(lines) if ln.startswith('module '))
    end = next(i for i in range(start, len(lines)) if lines[i].startswith('endmodule'))
    return lines[start:end + 1]


def sentences(lines):
    """The main module's lines grouped into sentences, a `// rule` or `// claim` comment line with
    the sentence after it; the other comment lines and the blank lines are dropped."""
    out, cur, after_comment = [], None, False
    for ln in lines:
        if not ln.strip() or (ln.startswith('// ') and not ln.startswith(('// rule ', '// claim '))):
            continue
        if ln.startswith('// '):
            cur = [ln]
            out.append(cur)
            after_comment = True
            continue
        if (SENT.match(ln) and not after_comment) or cur is None:
            cur = [ln]
            out.append(cur)
        else:
            cur.append(ln)
        after_comment = False
    return ['\n'.join(g) for g in out]


def renumbered(text):
    """text with the variables kompile generates (Var'Unds'GenN, and _GenN in its `// rule`
    comments) renumbered by first occurrence, each spelling from 0."""
    seen, count = {}, {}

    def one(m):
        if m[0] not in seen:
            seen[m[0]] = m[1] + str(count.get(m[1], 0))
            count[m[1]] = count.get(m[1], 0) + 1
        return seen[m[0]]
    return GEN.sub(one, text)


def unattributed(text):
    """text without Source and Location attributes."""
    return ATTR.sub('', text).replace('[, ', '[').replace('[,', '[')


def added_sentences(kore, empty_kore):
    """(the number of sentences of `kore`'s main module, those of them that come from no builtin
    file and are not sentences of `empty_kore`'s main module, each `//@ I` and the sentence
    without Source and Location and with its generated variables renumbered)."""
    def key(g):
        return renumbered(unattributed(g))

    base = {key(g) for g in sentences(main_module(empty_kore))}
    ss = sentences(main_module(kore))
    out = []
    for i, g in enumerate(ss):
        if g.startswith(('module ', 'endmodule')) or BUILTIN in g or key(g) in base:
            continue
        out.append(f'//@ {i}\n{key(g)}')
    return len(ss), out


# ------------------------------------------------------------------ kompile


def empty_module(runner):
    """The kompiled text of an empty module, cached in the build directory by the K installation."""
    d = os.path.join(BUILD, 'empty-module')
    stamp, kore = os.path.join(d, 'stamp.json'), os.path.join(d, 'out', 'definition.kore')
    key = {'kompile': runner.installation(), 'text': EMPTY_MODULE}
    if not (os.path.exists(kore) and os.path.exists(stamp) and read_json(stamp) == key):
        shutil.rmtree(d, ignore_errors=True)
        os.makedirs(d)
        write_text(os.path.join(d, 'empty-module.k'), EMPTY_MODULE)
        code, text = runner.kompile(['--backend', 'haskell', 'empty-module.k', '-o', 'out'], d)
        if code != 0:
            raise RuntimeError(f'kompile of an empty module: exit {code}\n{text[-2000:]}')
        write_json(stamp, key)
    with open(kore) as f:
        return f.read()


def kompile_entry(runner, entry, directory, b):
    """Kompile the entry's K text in its build directory `b`, cached there by the SHA-256 of its
    files (inputs.json) and the K installation (kompile.json). Returns (the command as recorded,
    exit code, output with paths replaced, the kompiled directory or None)."""
    files = entry['text']['files']
    key = {f: sha(os.path.join(directory, f)) for f in files}
    stamp, record = os.path.join(b, 'inputs.json'), os.path.join(b, 'kompile.json')
    if entry['kind'] == 'case':
        out = os.path.join(b, 'hs')
        args = [os.path.join(directory, 'def.k'), '--main-module', 'CASE', '--syntax-module', 'CASE-SYNTAX',
                '--backend', 'haskell', '-o', out]
        shown = 'kompile def.k --main-module CASE --syntax-module CASE-SYNTAX --backend haskell -o hs'
        cwd, names = b, {directory: '', b: 'BUILD'}
    else:
        src = os.path.join(b, 'src')
        out = os.path.join(src, 'out')
        args = ['--backend', 'haskell', files[0], '-o', 'out']
        shown = ' '.join(['kompile'] + args) + "  (cwd: a copy of the entry's directory)"
        cwd, names = src, {src: '', directory: '', b: 'BUILD'}
    if os.path.exists(stamp) and os.path.exists(record) and read_json(stamp) == key \
            and read_json(record).get('kompile') == runner.installation():
        rec = read_json(record)
    else:
        for p in (stamp, record):
            if os.path.exists(p):
                os.remove(p)
        shutil.rmtree(out, ignore_errors=True)
        if entry['kind'] != 'case':
            shutil.rmtree(src, ignore_errors=True)
            os.makedirs(src)
            shutil.copy(os.path.join(directory, files[0]), src)
        code, text = runner.kompile(args, cwd)
        rec = {'exit': code, 'output': unpath(text, names).strip(), 'kompile': runner.installation()}
        write_json(record, rec)
        write_json(stamp, key)
    kompiled = out if rec['exit'] == 0 and os.path.exists(os.path.join(out, 'definition.kore')) else None
    return shown, rec['exit'], unpid(rec['output']), kompiled


# ------------------------------------------------------------------ ruling_canonical


def symbol_arities(modules):
    out = {}
    for _, sents in modules:
        for kind, data, _ in sents:
            if kind in ('symbol', 'hooked-symbol'):
                out[data[0]] = len(data[1])
    return out


def top_cell_sort(modules):
    """The sort of the configuration's top cell: the first argument of <generatedTop>."""
    for _, sents in modules:
        for kind, data, _ in sents:
            if kind == 'symbol' and data[0] == "Lbl'-LT-'generatedTop'-GT-'":
                return data[1][0][0]
    raise ValueError('the kompiled text declares no <generatedTop>')


def term_faults(p, arities):
    """The variables of a parsed term, and its applications of a symbol to another number of
    arguments than its declaration's."""
    if p[0] == 'var':
        return [f'variable {p[1]}']
    if p[0] != 'app' or p[1] == '\\dv':
        return []
    _, name, _, args = p
    out = []
    if name not in arities:
        out.append(f'{name} is no declared symbol')
    elif arities[name] != len(args):
        out.append(f'{name} applied to {len(args)} arguments, declared with {arities[name]}')
    for a in args:
        out += term_faults(a, arities)
    return out


def canonical_of_kast(kore_text, top_sort, arities, csyms):
    """The canonical text of a final configuration from kast's KORE of the term written for it.
    One cell <k> (top_sort SortKCell): the item the cell holds, as parsed. Several cells: kast's
    rule parser gives kseq(inj{T,KItem}(TOP), dotk()), TOP the top cell of sort T = top_sort."""
    p = korek.read_pattern(kore_text)
    faults = term_faults(p, arities)
    if faults:
        raise ValueError('; '.join(faults))
    if top_sort == 'SortKCell':
        return korek.canon(p, csyms)
    item = korek.unseq(p)
    if not (item[0] == 'app' and item[1] == 'inj' and item[2][0][0] == top_sort):
        raise ValueError(f'not a top cell of sort {top_sort}')
    return korek.canon(item[3][0], csyms)


def canonical_finals(runner, b, hs, terms, top_sort, arities, csyms):
    out = []
    os.makedirs(os.path.join(b, 'finals'), exist_ok=True)
    for i, term in enumerate(terms):
        path = os.path.join(b, 'finals', f'{i}.k')
        write_text(path, term + '\n')
        if top_sort == 'SortKCell':
            args = [path, '-d', hs, '--module', 'CASE', '--sort', 'KItem', '--output', 'kore']
        else:
            args = [path, '-d', hs, '--module', 'CASE', '--input', 'rule', '--steps', ',', '--output', 'kore']
        code, stdout, text = runner.kast(args)
        try:
            if code != 0:
                raise ValueError(f'kast exit {code}: {error_class(text)}')
            out.append(canonical_of_kast(stdout, top_sort, arities, csyms))
        except ValueError as err:
            raise Refused(f'the final {term!r} is not parsed from the syntax of def.k ({err}); '
                          'write these finals as finals_canonical') from err
    return sorted(out)


def ruling_canonical(runner, entry, b, hs, csyms):
    """ruling_canonical of a case: the ruling's finals and each reading's, as canonical text."""
    ruling = entry['ruling']
    wanted = []
    if ruling.get('status') == 'settled':
        wanted.append(('settled', ruling))
    elif ruling.get('status') == 'unsettled':
        wanted += [(r.get('name'), r) for r in entry.get('reading', [])]
    wanted = [(n, h) for n, h in wanted if 'finals' in h or 'finals_canonical' in h]
    if not wanted:
        return {}
    with open(os.path.join(hs, 'definition.kore')) as f:
        modules = korek.read_definition(f.read())
    top_sort, arities = top_cell_sort(modules), symbol_arities(modules)
    out = {}
    for name, holder in wanted:
        if 'finals_canonical' in holder:
            terms = sorted(holder['finals_canonical'])
        else:
            terms = canonical_finals(runner, b, hs, holder['finals'], top_sort, arities, csyms)
        if name == 'settled':
            out['settled'] = terms
        else:
            out.setdefault('readings', {})[name] = terms
    return out


# ------------------------------------------------------------------ implementations


def run_backends(runner, case, b, hs, syms):
    defk, pgm = os.path.join(case, 'def.k'), os.path.join(case, 'pgm')
    rows, times = {}, {}
    hs_out = os.path.join(b, 'haskell.out')
    code, text, times['krun_haskell_ms'] = runner.run(
        [runner.tool('krun'), pgm, '-d', hs, '--search', '--output', 'kore'], out=hs_out)
    rows['haskell'] = {'finals': korek.cmd_ref(syms, hs_out)} if code == 0 else {'error': error_class(text)}
    llvm, llvm_out = os.path.join(b, 'llvm'), os.path.join(b, 'llvm.out')
    shutil.rmtree(llvm, ignore_errors=True)
    code, text, times['kompile_llvm_ms'] = runner.run(
        [runner.tool('kompile'), defk, '--main-module', 'CASE', '--syntax-module', 'CASE-SYNTAX',
         '--backend', 'llvm', '--enable-search', '-o', llvm])
    if code == 0:
        code, text, times['krun_llvm_ms'] = runner.run(
            [runner.tool('krun'), pgm, '-d', llvm, '--search', '--output', 'kore'], out=llvm_out)
    rows['llvm'] = {'finals': korek.cmd_ref(syms, llvm_out)} if code == 0 else {'error': error_class(text)}
    for impl, v in runner.versions().items():
        rows[impl]['version'] = v
    return rows, times


def read_import(spec):
    """--import kcore=FILE: the kcore row of each entry id FILE names."""
    impl, _, path = spec.partition('=')
    if impl != 'kcore' or not path:
        sys.exit('--import takes kcore=FILE')
    doc = read_json(path)
    if not isinstance(doc, dict) or not isinstance(doc.get('version'), str) \
            or not isinstance(doc.get('results'), dict):
        sys.exit(f'{path}: not {{"version": TEXT, "results": {{ID: {{"finals": [...]}} or {{"error": TEXT}}}}}}')
    digest = sha(path)
    rows = {}
    for cid, r in doc['results'].items():
        if isinstance(r, dict) and check.is_texts(r.get('finals')):
            rows[cid] = {'version': doc['version'], 'finals': sorted(r['finals']), 'imported_from': digest}
        elif isinstance(r, dict) and isinstance(r.get('error'), str):
            rows[cid] = {'version': doc['version'], 'error': r['error'], 'imported_from': digest}
        else:
            sys.exit(f'{path}: the result of {cid} has neither finals (a list of texts) nor error')
    return rows


# ------------------------------------------------------------------ one entry


def load_entry(directory):
    """The entry.toml of an entry, refused where there is none or it lacks what this script reads."""
    if not os.path.exists(os.path.join(directory, 'entry.toml')):
        raise Refused(f'no entry.toml in {directory}: it is written by hand (SCHEMA.md), never by this script')
    entry, fault = check.load(directory)
    if entry is None:
        raise Refused(fault)
    text = entry.get('text')
    if entry.get('kind') not in check.KIND_DIR or not isinstance(text, dict) \
            or not isinstance(entry.get('ruling'), dict):
        raise Refused('entry.toml has no kind, [text] or [ruling] (SCHEMA.md); tools/check.py names the fault')
    files = text.get('files')
    if files is not None and (not check.is_texts(files)
                              or any(not os.path.isfile(os.path.join(directory, f)) for f in files)):
        raise Refused('text.files names no file of the entry')
    if entry['kind'] == 'case' and files != ['def.k', 'pgm']:
        raise Refused('the files of a case are def.k and pgm')
    if entry['kind'] == 'text' and files is not None and len(files) != 1:
        raise Refused('a text entry has one K or KORE file')
    return entry


def build(directory, runner, opts, imported):
    """Write the tool-written files of one entry. Returns (id, evidence, notes)."""
    directory = os.path.abspath(directory)
    cid = os.path.basename(directory)
    toml = os.path.join(directory, 'entry.toml')
    entry = load_entry(directory)
    before = sha(toml)
    files = entry['text'].get('files') or []
    inputs = {f: sha(os.path.join(directory, f)) for f in files}
    inputs['answer'] = check.answer_hash(entry)
    ev_path = os.path.join(directory, 'evidence.json')
    old = read_json(ev_path) if os.path.exists(ev_path) else {}
    current = all((old.get('inputs') or {}).get(f) == inputs[f] for f in files)
    kept = dict(old.get('implementations') or {}) if current else {}
    ev = {'inputs': inputs, 'implementations': {}}
    notes = []
    b = os.path.join(BUILD, cid)
    os.makedirs(b, exist_ok=True)
    kore_txt, kompile_txt = os.path.join(directory, 'kore.txt'), os.path.join(directory, 'kompile.txt')
    hs = None
    if entry['kind'] == 'case' or (files and files[0].endswith('.k')):
        command, code, output, hs = kompile_entry(runner, entry, directory, b)
        release = runner.release()
        declared = entry['text'].get('kompile')
        if (code == 0) != (declared == 'accepts'):
            notes.append(f'UNEXPECTED: text.kompile is {declared} and kompile exited {code}')
        ev['kompile'] = {'release': release, 'command': command, 'exit': code,
                         'message': None if code == 0 else output}
        report = [f'command: {command}', f'release: {release}', f'exit: {code}']
        if hs:
            with open(os.path.join(hs, 'definition.kore')) as f:
                n, added = added_sentences(f.read(), empty_module(runner))
            write_text(kore_txt, ''.join(s + '\n' for s in added))
            ev['kompile']['kore.txt'] = sha(kore_txt)
            report.append(f"kore.txt: {len(added)} of the main module's {n} sentences: those that come from "
                          "no builtin file of K and that the main module of an empty module does not hold")
        else:
            if os.path.exists(kore_txt):
                os.remove(kore_txt)
            report.append('kore.txt: none, kompile wrote no definition')
        report.append('messages:')
        report += ['  ' + ln for ln in output.split('\n')] if output else ['  (none)']
        write_text(kompile_txt, '\n'.join(report) + '\n')
    else:
        for p in (kore_txt, kompile_txt):
            if os.path.exists(p):
                os.remove(p)

    if entry['kind'] == 'case':
        ev['ruling_canonical'] = {}
    if entry['kind'] == 'case' and hs:
        pgm_kore, syms = os.path.join(directory, 'pgm.kore'), os.path.join(directory, 'symbols.json')
        runner.must([runner.tool('kast'), os.path.join(directory, 'pgm'), '-d', hs, '--output', 'kore'], out=pgm_kore)
        korek.cmd_encode(os.path.join(hs, 'definition.kore'), pgm_kore, os.path.join(directory, 'kore.pgm'), syms)
        csyms = korek.coll_symbols(read_json(syms).get('collections'))
        ev['ruling_canonical'] = ruling_canonical(runner, entry, b, hs, csyms)
        rows = {k: v for k, v in kept.items() if k in BACKENDS}
        if not opts['no_backends'] and (opts['refresh'] or set(rows) != set(BACKENDS)):
            rows, times = run_backends(runner, directory, b, hs, syms)
            notes.append(json.dumps(times))
        ev['implementations'].update(rows)
    ev['implementations'].update({k: v for k, v in kept.items() if k not in BACKENDS})
    if cid in imported:
        ev['implementations']['kcore'] = imported[cid]
    write_json(ev_path, ev)
    if sha(toml) != before:
        raise RuntimeError(f'{toml} changed while the entry was built')
    return cid, ev, notes


# ------------------------------------------------------------------ --verify-quotes

LOCATOR = re.compile(r'(?P<path>[^:\s]+):(?P<lines>[0-9][0-9 ,\-]*?)\s*(?:\((?P<release>K [^)]*)\))?\Z')


def collapse(text):
    return ' '.join(text.split())


def quote_fault(basis, directory, checkout, release):
    """None when the quote of `basis` stands at its locator, else why not."""
    m = LOCATOR.match(str(basis.get('locator', '')).strip())
    if not m:
        return 'the locator is not PATH:LINES [(K RELEASE)]'
    if m['release'] and m['release'] != f'K {release}':
        return f'the locator names {m["release"]} and the checkout is K {release}'
    rel = m['path']
    if basis.get('source') == 'kompiled':
        path = os.path.join(directory, rel)
    else:
        path = os.path.join(checkout, rel)
        head, _, rest = rel.partition('/')
        if not os.path.isfile(path) and head in ('haskell-backend', 'llvm-backend'):
            path = os.path.join(checkout, head, 'src', 'main', 'native', head, rest)
    if not os.path.isfile(path):
        return f'no file {rel}'
    with open(path, encoding='utf-8', errors='replace') as f:
        lines = f.read().split('\n')
    numbers = []
    for part in m['lines'].split(','):
        a, _, z = part.strip().partition('-')
        numbers += range(int(a), int(z or a) + 1)
    if not numbers or max(numbers) > len(lines):
        return f'{rel} has {len(lines)} lines'
    text, at = collapse(' '.join(lines[n - 1] for n in numbers)), 0
    for piece in collapse(str(basis.get('quote', ''))).split(' ... '):
        found = text.find(piece, at)
        if found < 0:
            return f'not at {rel}:{m["lines"].strip()}: {piece[:80]!r}'
        at = found + len(piece)
    return None


def verify_quotes(directories, checkout):
    version = os.path.join(checkout, 'package', 'version')
    if not os.path.isfile(version):
        sys.exit(f'{checkout}: not a K checkout (no package/version)')
    with open(version) as f:
        release = f.read().strip()
    bad = total = 0
    for d in directories:
        cid = os.path.basename(d)
        try:
            entry = load_entry(d)
        except Refused as err:
            print(f'{cid}: REFUSED {err}')
            bad += 1
            continue
        ruling = entry['ruling']
        bases = [('ruling.basis', b) for b in ruling.get('basis') or []]
        bases += [('ruling.kore.basis', b) for b in (ruling.get('kore') or {}).get('basis') or []]
        if isinstance(entry['text'].get('declaration'), dict):
            bases.append(('text.declaration', entry['text']['declaration']))
        faults = []
        for where, b in bases:
            fault = quote_fault(b, d, checkout, release) if isinstance(b, dict) else 'not a table'
            if fault:
                faults.append(f'{where} ({b.get("locator") if isinstance(b, dict) else b}): {fault}')
        total += len(bases)
        bad += bool(faults)
        print(f'{cid}: ' + ('FAIL ' + '; '.join(faults) if faults else f'ok, {len(bases)} quote(s) at their locators'))
    print(f'{"PASS" if not bad else "FAIL"} quotes: {total} checked against K {release}; '
          f'{bad} entr{"y" if bad == 1 else "ies"} with a quote not at its locator')
    return 1 if bad else 0


# ------------------------------------------------------------------ command


def main(args):
    opts = {'refresh': False, 'no_backends': False}
    imports, checkout, named = [], None, []
    it = iter(args)
    for a in it:
        if a in ('--refresh', '--no-backends'):
            opts[a[2:].replace('-', '_')] = True
        elif a == '--import':
            imports.append(next(it, ''))
        elif a.startswith('--import='):
            imports.append(a[len('--import='):])
        elif a == '--verify-quotes':
            checkout = next(it, '')
        elif a.startswith('--') and a != '--all':
            sys.exit(__doc__)
        else:
            named.append(a)
    if named == ['--all']:
        named = []
        for sub in ('cases', 'texts') if checkout else ('cases',):
            root = os.path.join(PACKAGE, sub)
            if os.path.isdir(root):
                named += [os.path.join(root, d) for d in sorted(os.listdir(root)) if os.path.isdir(os.path.join(root, d))]
    if not named or '--all' in named or checkout == '':
        sys.exit(__doc__)
    named = [os.path.abspath(c if os.path.isabs(c) or os.path.exists(c) else os.path.join(PACKAGE, c))
             for c in named]
    if checkout:
        return verify_quotes(named, os.path.abspath(checkout))
    imported = {}
    for spec in imports:
        imported.update(read_import(spec))
    runner = Runner()
    bad = 0
    for c in named:
        try:
            cid, ev, notes = build(c, runner, opts, imported)
        except Refused as err:
            print(f'{os.path.basename(c)}: REFUSED {err}')
            bad += 1
            continue
        except Exception as err:  # noqa: BLE001 - one failed entry does not stop the others
            print(f'{os.path.basename(c)}: ERROR {err}')
            bad += 1
            continue
        k = ev.get('kompile')
        res = {i: v.get('finals', 'error: ' + str(v.get('error', ''))) for i, v in ev['implementations'].items()}
        print(f'{cid}: ' + (f'kompile exit {k["exit"]}' if k else 'not kompiled')
              + (f' ruling_canonical {json.dumps(ev["ruling_canonical"])}' if ev.get('ruling_canonical') else '')
              + f' {json.dumps(res)}' + ''.join(' ' + n for n in notes))
        bad += any(n.startswith('UNEXPECTED') for n in notes)
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
