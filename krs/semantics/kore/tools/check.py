#!/usr/bin/env python3
"""Check that the record of every entry (or of the named ones) is consistent with itself.

  check.py [--no-run] [cases/<id> | texts/<id> ...]
                                         (relative to the package directory, or absolute)
  check.py --ruling-sha ID...            print `ID SHA` per entry id (kk:ID or ID): the SHA-256 of
                                         its ruling (SCHEMA.md, "The ruling hash"); writes nothing

An entry is a directory with a hand-written entry.toml (SCHEMA.md) and tool-written evidence.
This script writes neither. An entry fails for one of three causes, and for nothing else:

  schema   entry.toml does not parse or does not have the form SCHEMA.md states;
  stale    a hash the evidence records is not the present one (the answer fields of entry.toml,
           the K text, kore.txt), or the entry has no evidence;
  differs  an implementation's result is not the ruling (or, at an unsettled entry, no reading)
           and no disposition names the implementation; or a disposition names one whose result
           is the ruling (a disposition does not outlive its difference).

An implementation that differs from the ruling under a disposition is not a failure, whichever
implementation it is. The implementations are the rows of evidence.json and, for a case, kore.k
as krust runs it now: kore.k is kompiled once with `krust kcompile` (cached in the build directory
by the SHA-256 of kore.k and of the krust executable), the case's kore.pgm is run with
`krust krun --sort Pgm`, and the result is decoded with the case's symbols.json
(tools/korek.py korek). No K reference tool runs.

--no-run         does not run kore.k: the schema, the hashes and the stored results only. Needs
                 nothing but Python.

One line per entry: its status and, per implementation, `=` (the ruling), `reading:<name>`,
`coincides:<name>`, or `differs`. The summary counts the entries, settled and unsettled, and per
implementation the recorded differences, kore.k's apart. Exit 0 when no entry fails, 1 otherwise, 2 when
kore.k is to be run and no krust executable is found.

krust is $KRUST, else release/krust under $CARGO_TARGET_DIR, else the repository's
target/release/krust. Each krust run has a 60 s timeout. The build directory is
$KORE_IN_K_BUILD, by default kore-in-k under the system temporary directory.
"""
import hashlib
import json
import os
import re
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

KIND_DIR = {'case': 'cases', 'text': 'texts'}
ID_FORM = {'case': re.compile(r'c\d\d+-[a-z0-9-]+\Z'), 'text': re.compile(r't\d\d+-[a-z0-9-]+\Z')}
STATUSES = ('settled', 'unsettled')
KOMPILE = ('accepts', 'rejects', 'not-run')
SOURCES = ('manual', 'tutorial', 'domains', 'builtin-module', 'kore-syntax', 'prelude', 'kompiled', 'matching-logic')
FRONTEND = ('as-ruled', 'differs', 'manual-silent')
# form -> the further fields a text ruling of that form carries
FORMS = {'means': (), 'same-text': ('other',), 'differs-in': ('other', 'sentences'), 'no-sentence': (),
         'rejected': (), 'no-model': (), 'hook-value': ('hook', 'points')}
OBSERVED = ('kore.txt', 'kompile.txt')
# a reason is a derivation from sentences: it names none of these
IMPLEMENTATION_WORDS = re.compile(r'\b(haskell|llvm|krust|kcore|backends?)\b|compatibility\.md', re.I)
INTERPRETER = 'kore.k'

TOP_KEYS = {'id', 'kind', 'subject', 'retro', 'rests_on', 'origin', 'text', 'ruling', 'reading',
            'disposition', 'observe', 'note'}
TEXT_KEYS = {'files', 'declaration', 'kompile', 'frontend', 'frontend_difference'}
RULING_KEYS = {'status', 'reason', 'basis', 'kore', 'finals', 'finals_canonical', 'statement', 'form',
               'other', 'sentences', 'hook', 'points', 'interpreter', 'separates'}
READING_KEYS = {'name', 'statement', 'finals', 'finals_canonical', 'answer', 'consequence'}


def sha(path):
    with open(path, 'rb') as f:
        return hashlib.sha256(f.read()).hexdigest()


def answer_hash(entry):
    """The SHA-256 of the answer fields of an entry (SCHEMA.md, "evidence.json"): a change of any
    other field leaves the evidence current."""
    ruling = entry.get('ruling', {})
    answer = {'kompile': entry.get('text', {}).get('kompile'),
              'finals': ruling.get('finals'),
              'finals_canonical': ruling.get('finals_canonical'),
              'readings': [{'name': r.get('name'), 'finals': r.get('finals'),
                            'finals_canonical': r.get('finals_canonical')}
                           for r in entry.get('reading', [])]}
    text = json.dumps(answer, sort_keys=True, separators=(',', ':'), ensure_ascii=False)
    return hashlib.sha256(text.encode()).hexdigest()


def ruling_hash(entry):
    """The SHA-256 of an entry's ruling (SCHEMA.md, "The ruling hash"): its [ruling] table, which
    holds [ruling.kore] and [[ruling.basis]], and its [[reading]] blocks, serialized as
    answer_hash serializes the answer. Dispositions, notes, observe pointers and the other fields
    are outside it, so a row that cites the entry stays current when only they change."""
    ruling = {'ruling': entry.get('ruling', {}), 'reading': entry.get('reading', [])}
    text = json.dumps(ruling, sort_keys=True, separators=(',', ':'), ensure_ascii=False)
    return hashlib.sha256(text.encode()).hexdigest()


def read_json(path):
    with open(path) as f:
        return json.load(f)


def read_text(path):
    with open(path) as f:
        return f.read()


def is_text(v):
    return isinstance(v, str) and v.strip() != ''


def is_texts(v):
    return isinstance(v, list) and all(isinstance(x, str) for x in v)


def basis_faults(basis, where):
    if not isinstance(basis, list) or not basis:
        return [f'{where}: no basis']
    out = []
    for i, b in enumerate(basis):
        if not isinstance(b, dict) or b.get('source') not in SOURCES:
            out.append(f'{where}.basis[{i}]: source is not one of {", ".join(SOURCES)}')
        elif not is_text(b.get('locator')) or not is_text(b.get('quote')):
            out.append(f'{where}.basis[{i}]: no locator or no quote')
    return out


def schema_faults(entry, directory, index):
    """The schema faults of a parsed entry.toml; `index` gives the status of every entry by id."""
    out = []
    cid = os.path.basename(directory)
    kind = entry.get('kind')
    for k in sorted(set(entry) - TOP_KEYS):
        out.append(f'unknown field {k}')
    if kind not in KIND_DIR:
        return out + ['kind is not case or text']
    if entry.get('id') != cid:
        out.append(f'id is not the directory name {cid}')
    if not ID_FORM[kind].match(cid):
        out.append(f'the id of a {kind} has the form {"cNN-name" if kind == "case" else "tNN-name"}')
    if os.path.basename(os.path.dirname(directory)) != KIND_DIR[kind]:
        out.append(f'a {kind} entry stands under {KIND_DIR[kind]}/')
    if not is_text(entry.get('subject')):
        out.append('no subject')
    if 'retro' in entry and not is_texts(entry['retro']):
        out.append('retro is not a list of row ids')
    if 'origin' in entry and not is_text(entry['origin']):
        out.append('origin is not a text')

    text = entry.get('text')
    if not isinstance(text, dict):
        return out + ['no [text]']
    for k in sorted(set(text) - TEXT_KEYS):
        out.append(f'unknown field text.{k}')
    if text.get('kompile') not in KOMPILE:
        out.append(f'text.kompile is not one of {", ".join(KOMPILE)}')
    files, decl = text.get('files'), text.get('declaration')
    if (files is None) == (decl is None):
        out.append('[text] has exactly one of files and declaration')
    elif decl is not None:
        if kind != 'text':
            out.append('only a text entry quotes a declaration')
        if not isinstance(decl, dict) or decl.get('source') not in SOURCES \
                or not is_text(decl.get('locator')) or not is_text(decl.get('quote')):
            out.append('text.declaration needs source, locator and quote')
        if text.get('kompile') in ('accepts', 'rejects'):
            out.append('a declaration quoted alone is not kompiled: text.kompile is not-run')
    elif not is_texts(files) or not files:
        out.append('text.files is not a list of file names')
    else:
        if kind == 'case' and files != ['def.k', 'pgm']:
            out.append('the files of a case are def.k and pgm')
        if kind == 'text' and len(files) != 1:
            out.append('a text entry has one K or KORE file')
        for f in files:
            if os.path.basename(f) != f or not os.path.isfile(os.path.join(directory, f)):
                out.append(f'text.files: no file {f} in the entry')
    if 'frontend' in text and text['frontend'] not in FRONTEND:
        out.append(f'text.frontend is not one of {", ".join(FRONTEND)}')
    if text.get('frontend') == 'differs' and not is_text(text.get('frontend_difference')):
        out.append('text.frontend = "differs" needs frontend_difference')

    ruling = entry.get('ruling')
    if not isinstance(ruling, dict):
        return out + ['no [ruling]']
    for k in sorted(set(ruling) - RULING_KEYS):
        out.append(f'unknown field ruling.{k}')
    status = ruling.get('status')
    if status not in STATUSES:
        return out + [f'ruling.status is not one of {", ".join(STATUSES)}']
    readings = entry.get('reading', [])
    dispositions = entry.get('disposition', [])
    if not isinstance(readings, list) or not isinstance(dispositions, list):
        return out + ['reading and disposition are arrays of tables']
    names = [r.get('name') for r in readings]

    seen = set()
    for i, d in enumerate(dispositions):
        impl, how = d.get('implementation'), d.get('is')
        if not is_text(impl) or not is_text(d.get('reason')) or not is_text(how):
            out.append(f'disposition[{i}] needs implementation, is and reason')
            continue
        if impl in seen:
            out.append(f'two dispositions name {impl}')
        seen.add(impl)
        form, _, name = how.partition(':')
        if status == 'unsettled' and form in ('reading', 'coincides'):
            if name not in names:
                out.append(f'disposition[{i}]: is = "{how}" names no reading')
        elif how != 'difference':
            allowed = '"difference", "reading:<name>" or "coincides:<name>"' if status == 'unsettled' \
                else '"difference"'
            out.append(f'disposition[{i}]: at a {status} entry is = {allowed}')
    for i, o in enumerate(entry.get('observe', [])):
        if o.get('file') not in OBSERVED or ('contains' in o) == ('absent' in o) \
                or not is_text(o.get('contains', o.get('absent'))):
            out.append(f'observe[{i}] needs file ({" or ".join(OBSERVED)}) and one of contains and absent')
    for i, n in enumerate(entry.get('note', [])):
        if not is_text(n.get('implementation')) or not is_text(n.get('text')):
            out.append(f'note[{i}] needs implementation and text')

    rests = entry.get('rests_on', [])
    if not is_texts(rests):
        out.append('rests_on is not a list of entries')
        rests = []
    for r in rests:
        if not r.startswith('kk:') or r[3:] not in index:
            out.append(f'rests_on: {r} names no entry')
        elif status == 'settled' and index[r[3:]] != 'settled':
            out.append(f'a settled entry rests on {r}, which is {index[r[3:]]}')

    if not is_text(ruling.get('reason')):
        out.append('ruling: no reason')
    else:
        m = IMPLEMENTATION_WORDS.search(ruling['reason'])
        if m:
            out.append(f'ruling.reason names an implementation ({m.group(0)})')
    out += basis_faults(ruling.get('basis'), 'ruling')
    kore = ruling.get('kore')
    if kore is not None:
        if not isinstance(kore, dict) or not is_text(kore.get('statement')):
            out.append('ruling.kore: no statement')
        else:
            out += basis_faults(kore.get('basis'), 'ruling.kore')

    answers = [k for k in ('finals', 'finals_canonical', 'statement') if k in ruling]
    if status == 'settled':
        for k in ('interpreter', 'separates'):
            if k in ruling:
                out.append(f'ruling.{k} belongs to an unsettled case')
        if readings:
            out.append('a settled entry has no reading')
        if kind == 'case':
            if 'statement' in ruling or 'form' in ruling:
                out.append('the ruling of a case is its finals, not a statement')
            if not any(is_texts(ruling.get(k)) for k in ('finals', 'finals_canonical')):
                out.append('a settled case needs finals (a list of terms; [] for no final configuration)')
        else:
            if 'finals' in ruling or 'finals_canonical' in ruling:
                out.append('the ruling of a text entry is a statement, not finals')
            if not is_text(ruling.get('statement')):
                out.append('a settled text entry needs a statement')
            form = ruling.get('form')
            if form not in FORMS:
                out.append(f'ruling.form is not one of {", ".join(FORMS)}')
            else:
                for k in FORMS[form]:
                    if k not in ruling:
                        out.append(f'form = "{form}" needs {k}')
                other = ruling.get('other')
                if 'other' in FORMS[form] and is_text(other) \
                        and (not other.startswith('kk:') or other[3:] not in index):
                    out.append(f'ruling.other: {other} names no entry')
    else:
        if answers:
            out.append(f'an unsettled entry has no answer of its own ({", ".join(answers)}): '
                       'its readings carry one each')
        if len(readings) < 2:
            out.append('an unsettled entry needs at least two readings')
        if len(set(names)) != len(names):
            out.append('two readings have one name')
        for i, r in enumerate(readings):
            for k in sorted(set(r) - READING_KEYS):
                out.append(f'unknown field reading[{i}].{k}')
            if not is_text(r.get('name')) or not is_text(r.get('statement')):
                out.append(f'reading[{i}] needs name and statement')
            has_finals = any(is_texts(r.get(k)) for k in ('finals', 'finals_canonical'))
            if has_finals == is_text(r.get('answer')):
                out.append(f'reading[{i}] needs one answer: finals, or answer in prose')
            if not is_text(r.get('consequence')):
                out.append(f'reading[{i}] needs a consequence')
        if kind == 'case':
            interp = ruling.get('interpreter')
            if interp != 'outside' and interp not in names:
                out.append('an unsettled case needs interpreter: a reading\'s name, or "outside"')
            elif interp == 'outside' and INTERPRETER not in seen:
                out.append(f'interpreter = "outside" needs a disposition for {INTERPRETER}')
            elif interp != 'outside' and INTERPRETER in seen:
                out.append(f'a disposition names {INTERPRETER}, whose reading interpreter gives: '
                           'only interpreter = "outside" has one')
            if 'separates' in ruling:
                known = mutation_ids(os.path.dirname(os.path.dirname(directory)))
                if not is_texts(ruling['separates']):
                    out.append('ruling.separates is not a list of mutation ids')
                elif known is not None:
                    for m in ruling['separates']:
                        if m not in known:
                            out.append(f'ruling.separates: no mutation {m} in MUTATIONS.toml')
        else:
            for k in ('interpreter', 'separates'):
                if k in ruling:
                    out.append(f'ruling.{k} belongs to an unsettled case')
    return out


def mutation_ids(package):
    path = os.path.join(package, 'MUTATIONS.toml')
    if not os.path.exists(path):
        return None
    with open(path, 'rb') as f:
        return {m.get('id') for m in tomllib.load(f).get('mutation', [])}


def evidence_of(directory):
    """The entry's evidence.json, or None."""
    path = os.path.join(directory, 'evidence.json')
    return read_json(path) if os.path.exists(path) else None


def record_faults(entry, directory, ev):
    """(schema faults, stale hashes) of the evidence against entry.toml and the entry's files."""
    schema, stale = [], []
    status = entry['ruling']['status']
    files = entry['text'].get('files', [])
    inputs = {f: sha(os.path.join(directory, f)) for f in files}
    inputs['answer'] = answer_hash(entry)
    recorded = ev.get('inputs') or {}
    for k in sorted(set(inputs) | set(recorded)):
        if inputs.get(k) != recorded.get(k):
            stale.append(f'{k} changed since evidence.json')
    kompile, declared = ev.get('kompile'), entry['text']['kompile']
    if declared == 'not-run':
        if kompile is not None:
            schema.append('text.kompile is not-run and evidence.json records a kompile run')
    elif kompile is None:
        stale.append('evidence.json records no kompile run')
    else:
        if (kompile.get('exit') == 0) != (declared == 'accepts'):
            schema.append(f'text.kompile is {declared} and kompile exited {kompile.get("exit")}')
        if kompile.get('kore.txt') is not None:
            path = os.path.join(directory, 'kore.txt')
            if not os.path.exists(path) or sha(path) != kompile['kore.txt']:
                stale.append('kore.txt changed since evidence.json')
    if entry['kind'] == 'case':
        canon = ev.get('ruling_canonical') or {}
        if status == 'settled' and not is_texts(canon.get('settled')):
            stale.append('evidence.json has no canonical text of the ruling')
        if status == 'unsettled':
            for r in entry['reading']:
                if 'answer' not in r and not is_texts((canon.get('readings') or {}).get(r['name'])):
                    stale.append(f'evidence.json has no canonical text of reading {r["name"]}')
    return schema, stale


def observe_faults(entry, directory):
    out = []
    for o in entry.get('observe', []):
        path = os.path.join(directory, o['file'])
        content = read_text(path) if os.path.exists(path) else None
        if content is None:
            out.append(f'observe: no {o["file"]}')
        elif 'contains' in o and o['contains'] not in content:
            out.append(f'observe: {o["file"]} does not contain {o["contains"]!r}')
        elif 'absent' in o and o['absent'] in content:
            out.append(f'observe: {o["file"]} contains {o["absent"]!r}')
    return out


def shown(res):
    return json.dumps(res['finals']) if 'finals' in res else 'error: ' + str(res.get('error', ''))


def compare(entry, ev, live):
    """(failures, marks, the implementations that differ as recorded) of each implementation's
    result against the ruling. `live` is kore.k's result of now ({'finals': [...]} or
    {'error': ...}), or None when it was not run."""
    status = entry['ruling']['status']
    dispositions = {d['implementation']: d['is'] for d in entry.get('disposition', [])}
    results = dict(ev.get('implementations') or {})
    bad, marks, differing = [], [], []

    if live is not None:
        results[INTERPRETER] = live
    for impl in sorted(set(dispositions) - set(results)):
        if impl != INTERPRETER or live is not None:
            bad.append(f'a disposition names {impl}, of which no result is recorded')
    canon = ev.get('ruling_canonical') or {}
    if status == 'settled':
        ruled = sorted(canon['settled'])
        for impl, res in sorted(results.items()):
            equal = 'finals' in res and sorted(res['finals']) == ruled
            if impl in dispositions:
                if equal:
                    bad.append(f'a disposition names {impl}, whose result is the ruling')
                else:
                    marks.append(f'{impl}:differs')
                    differing.append(impl)
            elif equal:
                marks.append(f'{impl}:=')
            else:
                bad.append(f'{impl}={shown(res)} is not the ruling and no disposition names {impl}')
        return bad, marks, differing

    readings = {n: sorted(f) for n, f in (canon.get('readings') or {}).items()}
    interp = entry['ruling'].get('interpreter')
    for impl, res in sorted(results.items()):
        finals = sorted(res['finals']) if 'finals' in res else None
        equal_to = [n for n, f in readings.items() if finals == f]
        how = dispositions.get(impl)
        if how is None and impl == INTERPRETER:
            if interp in readings and finals != readings[interp]:
                bad.append(f'{impl}={shown(res)} is not the reading {interp}, which interpreter names')
            else:
                marks.append(f'{impl}:reading:{interp}')
        elif how is None:
            if equal_to:
                marks.append(f'{impl}:reading:{equal_to[0]}')
            else:
                bad.append(f'{impl}={shown(res)} is no reading and no disposition names {impl}')
        elif how == 'difference':
            if equal_to:
                bad.append(f'a disposition names {impl} a difference, and its result is the reading {equal_to[0]}')
            else:
                marks.append(f'{impl}:differs')
                differing.append(impl)
        elif how.startswith('coincides:'):
            name = how.partition(':')[2]
            if name in readings and finals == readings[name]:
                marks.append(f'{impl}:{how}')
                differing.append(impl)
            else:
                bad.append(f'{impl}={shown(res)} does not equal the finals of {name}, with which its '
                           'disposition says it coincides')
        else:
            marks.append(f'{impl}:{how}')
    return bad, marks, differing


def load(directory):
    """(entry, None) or (None, the parse fault)."""
    path = os.path.join(directory, 'entry.toml')
    if not os.path.exists(path):
        return None, 'no entry.toml'
    try:
        with open(path, 'rb') as f:
            return tomllib.load(f), None
    except tomllib.TOMLDecodeError as err:
        return None, f'entry.toml does not parse: {err}'


def check_entry(directory, index, live=None):
    """Judge one entry. Returns (passes, line, status, the implementations that differ as recorded)."""
    cid = os.path.basename(directory)
    entry, fault = load(directory)
    if entry is None:
        return False, f'{cid}: FAIL schema: {fault}', None, []
    faults = schema_faults(entry, directory, index)
    if faults:
        return False, f'{cid}: FAIL schema: ' + '; '.join(faults), None, []
    status = entry['ruling']['status']
    ev = evidence_of(directory)
    if ev is None:
        return False, f'{cid}: FAIL stale: no evidence.json; run tools/case.py {cid}', status, []
    schema, stale = record_faults(entry, directory, ev)
    schema += observe_faults(entry, directory)
    if schema:
        return False, f'{cid}: FAIL schema: ' + '; '.join(schema), status, []
    if stale:
        return False, f'{cid}: FAIL stale: ' + '; '.join(stale) + f'; run tools/case.py {cid}', status, []
    if entry['kind'] != 'case':
        return True, f'{cid}: ok {status}', status, []
    bad, marks, differing = compare(entry, ev, live)
    if bad:
        return False, f'{cid}: FAIL differs: ' + '; '.join(bad), status, differing
    return True, f'{cid}: ok {status}' + ''.join(' ' + m for m in marks), status, differing


def entries_of(package):
    out = []
    for sub in KIND_DIR.values():
        root = os.path.join(package, sub)
        if os.path.isdir(root):
            out += [os.path.join(root, d) for d in sorted(os.listdir(root)) if os.path.isdir(os.path.join(root, d))]
    return out


def index_of(package):
    """The status of every entry of the package by id (None where entry.toml gives none)."""
    index = {}
    for d in entries_of(package):
        entry, _ = load(d)
        ruling = (entry or {}).get('ruling')
        index[os.path.basename(d)] = ruling.get('status') if isinstance(ruling, dict) else None
    return index


def krust():
    candidates = [os.environ.get('KRUST')]
    if os.environ.get('CARGO_TARGET_DIR'):
        candidates.append(os.path.join(os.environ['CARGO_TARGET_DIR'], 'release', 'krust'))
    candidates.append(os.path.join(REPOSITORY, 'target', 'release', 'krust'))
    for c in candidates:
        if c and os.access(c, os.X_OK):
            return os.path.abspath(c)
    print('error: no krust executable: set KRUST, or build it with '
          '`cargo build --release -p k-rust` (see README.md); --no-run needs none', file=sys.stderr)
    sys.exit(2)


def kompiled(exe):
    """kore.k kompiled by krust, rebuilt when kore.k or the krust executable changes."""
    kc = os.path.join(BUILD, 'kore-k')
    stamp = os.path.join(kc, 'stamp.json')
    key = {'kore.k': sha(os.path.join(PACKAGE, 'kore.k')), 'krust': sha(exe)}
    if os.path.exists(stamp) and read_json(stamp) == key:
        return kc, 0
    shutil.rmtree(kc, ignore_errors=True)
    os.makedirs(BUILD, exist_ok=True)
    start = time.monotonic()
    subprocess.run([exe, 'kcompile', os.path.join(PACKAGE, 'kore.k'), '--main-module', 'KORE',
                    '--syntax-module', 'KORE-SYNTAX', '-o', kc], check=True, timeout=TIMEOUT_S * 5)
    with open(stamp, 'w') as f:
        json.dump(key, f)
    return kc, int((time.monotonic() - start) * 1000)


def run_interpreter(case, exe, kc):
    """kore.k's result on a case's kore.pgm: ({'finals': [...]} or {'error': ...}, ms)."""
    cid = os.path.basename(case)
    out = os.path.join(BUILD, f'{cid}.kore-k.out')
    start = time.monotonic()
    r = subprocess.run([exe, 'krun', '--definition', kc, '--sort', 'Pgm', os.path.join(case, 'kore.pgm')],
                       capture_output=True, text=True, timeout=TIMEOUT_S)
    ms = int((time.monotonic() - start) * 1000)
    with open(out, 'w') as f:
        f.write(r.stdout)
    try:
        return {'finals': korek.cmd_korek(os.path.join(case, 'symbols.json'), out)}, ms
    except Exception as err:  # noqa: BLE001 - kore.k's failure on this case is its result
        return {'error': f'no result from kore.k ({err}; exit {r.returncode}: {r.stderr[-300:]})'}, ms


def print_ruling_hashes(ids, package):
    """One line per id: `ID SHA`, the ruling hash of the entry kk:ID; exit 1 when an id names no entry
    or its entry.toml does not parse."""
    known = {os.path.basename(d): d for d in entries_of(package)}
    bad = 0
    for i in ids:
        i = i[3:] if i.startswith('kk:') else i
        entry, fault = load(known[i]) if i in known else (None, 'names no entry')
        if entry is None:
            print(f'{i}: {fault}', file=sys.stderr)
            bad += 1
        else:
            print(f'{i} {ruling_hash(entry)}')
    return 1 if bad else 0


def main(args, package=PACKAGE):
    if args[:1] == ['--ruling-sha']:
        if len(args) < 2:
            sys.exit(__doc__)
        return print_ruling_hashes(args[1:], package)
    flags = {a for a in args if a.startswith('--')}
    if flags - {'--no-run'}:
        sys.exit(__doc__)
    run = '--no-run' not in flags
    named = [a for a in args if not a.startswith('--')]
    if named:
        entries = [a if os.path.isabs(a) or os.path.exists(a) else os.path.join(package, a) for a in named]
    else:
        entries = entries_of(package)
    entries = [os.path.abspath(e) for e in entries]
    index = index_of(package)
    exe = kc = None
    kompile_ms = 0
    if run:
        exe = krust()
        kc, kompile_ms = kompiled(exe)
    passed, total_ms = 0, 0
    statuses = dict.fromkeys(STATUSES, 0)
    differences = {}
    for e in entries:
        live = None
        if run and os.path.exists(os.path.join(e, 'kore.pgm')):
            live, ms = run_interpreter(e, exe, kc)
            total_ms += ms
        ok, line, status, differing = check_entry(e, index, live)
        passed += ok
        if status:
            statuses[status] += 1
        for impl in differing:
            differences[impl] = differences.get(impl, 0) + 1
        print(line)
    fine = passed == len(entries)
    own = differences.pop(INTERPRETER, 0)
    counted = ', '.join(f'{n} {s}' for s, n in statuses.items())
    recorded = ', '.join(f'{impl} {n}' for impl, n in sorted(differences.items())) or 'none'
    if not run:
        ran = 'kore.k not run'
    else:
        ran = f'krun {total_ms} ms in all, ' + (f'kcompile {kompile_ms} ms' if kompile_ms else 'kcompile cached')
    print(f'{"PASS" if fine else "FAIL"} kore-in-k: {passed} of {len(entries)} entries pass ({counted}); '
          f'recorded differences: {recorded}; {INTERPRETER} is not the ruling, or is outside the readings, '
          f'at {own}; {ran}')
    return 0 if fine else 1


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
