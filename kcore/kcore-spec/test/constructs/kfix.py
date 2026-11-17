"""The K-level fixtures of rows.toml (lists E1, E2, E3, E7, E8): small K texts, their kompiled KORE
and `kcore account` of it, under test/constructs/fixtures/NAME/.

Usage (from kcore-spec):
  python3 -I test/constructs/kfix.py run [NAME...]   kompile the named fixtures (all without names)
  python3 -I test/constructs/kfix.py check [LIST...]  check rows.toml's pointers (lists E1 E2 E3 E7 E8
                                                     by default) against the files
  python3 -I test/constructs/kfix.py rehash [NAME...] rewrite kompile.txt's stripped sha256 and
                                                     verdicts from the cached text of the same run

A fixture directory holds its K text(s) and fixture.toml:
  main     the file kompiled (default NAME.k)
  extra    options after `--backend haskell` (default none: R-12's option set)
  expect   "ok" (default) or "error": an error fixture records kompile's message and nothing else
  same_as  another fixture whose kompiled text this one's must equal after removing the Source and
           Location attributes and the main module's name, putting each disjunction's disjuncts in a
           fixed order (kompile's order changes from run to run; \\or is commutative and associative)
           and renumbering the variables kompile generates (their numbers change from run to run)
           (`stripped`) (an option or a construct that changes no
           sentence); differs_from: the same, must differ
  text_from  another fixture whose text files are copied beside this one's (an option fixture
           kompiles another fixture's text); kore.txt then holds the sentences not in that
           fixture's main module instead of base's
  external files of the k-rust checkout (K_RUST, paths relative to it) copied beside the text
           before kompiling; kompile.txt records each one's sha256
  kore_txt false: write no kore.txt (a large text no row points into, such as kore.k's)
  keep     regular expressions: when the sentences for kore.txt exceed 200 KB, only those with a
           Source in the fixture or matching one of these are written
  args     the whole command line after kompile instead of `--backend haskell EXTRA MAIN -o out`
           (an option that writes no definition, such as --help)
  kore     a KORE text (path relative to kcore-spec) that kompile 7.1.337 does not write, such as
           krust's text of a K file: `run` kompiles nothing and writes account.txt, `kcore account`
           of that text, and kompile.txt, the text's path and sha256; no kore.txt

`run` copies the directory to .lake/kfix/NAME/src, kompiles there one fixture at a time under the
memory wrapper, and writes into the fixture directory:
  kompile.txt  the command, exit code, seconds, size and sha256 of definition.kore with paths
               replaced (FIXTURE/ for the fixture's directory, BUILTIN/ for K's builtin directory),
               the sha256 with Source, Location and module names removed, the same_as / differs_from
               verdict, and kompile's output (paths replaced)
  kore.txt     the sentences of the main module that come from no builtin file (no Source under
               BUILTIN/) and are not sentences of fixture `base`'s main module: what the text adds
               to an empty module (compared with generated variables renumbered); each after a line `//@ N`, N its index among the main module's
               sentences (a `// rule` comment kompile writes counts with the axiom it precedes).
               The whole text is not committed (80 to 650 KB each); kompile.txt's command
               regenerates it. Kompile numbers its generated variables differently from run to
               run, so the text's sha256 can change; the stripped sha256 (Source, Location and
               module names removed, disjunctions in a fixed order, generated variables
               renumbered: `stripped`) is the one to compare.
  account.txt  `kcore account out/definition.kore` (the workspace's .lake/build/bin/kcore)

A row of rows.toml names its fixture (`fixture`) and either the sentences that carry it (`sentence`,
substrings of that fixture's kore.txt, or of kompile.txt for an error fixture) or why no sentence of
a kompiled text carries it (`no_sentence`, "CLASS: reason", with `fixture` the evidence, or "none"
when the reason is a place in K's sources). Classes: erased (the fixture's same_as pair is equal),
rejected (kompile's error in the fixture), and the others named where they are used. `check` fails
unless every row of E1, E2, E3, E7, E8 has a fixture that exists, every `sentence` occurs in it,
every row has exactly one of `sentence` and `no_sentence`, and every same_as / differs_from verdict
recorded holds.

A row or a `cases` entry of any list E1 to E8 may carry `notes`, a table from a constructor of
`ReadingNote` (KcoreSpec/Parse.lean) to a fixture directory whose account.txt prints the note: a
line `N read NOTE [...]` or `sentence I: ... NOTE ...` (the per-sentence readings), or a count line
`... (NOTE): N`, with N > 0. `check` also fails unless each `notes` entry is so, and every
constructor of ReadingNote is a key of some `notes` table.
"""
import hashlib, os, re, shutil, subprocess, sys, time, tomllib

K = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(K, "test"))
sys.dont_write_bytecode = True  # no __pycache__ in the tree
import relsource
FX = os.path.join(K, "test/constructs/fixtures")
WORK = os.path.join(K, ".lake/kfix")
# the k-rust checkout: $K_RUST, or the nearest directory above holding Cargo.toml and crates/k-rust
KR = relsource.krust_root() or "K_RUST-unset"
KOMPILE = os.environ.get("K_KOMPILE", os.path.join(KR, "k/result/bin/kompile"))
KCORE = os.path.join(K, ".lake/build/bin/kcore")
LISTS = ["E1", "E2", "E3", "E7", "E8"]
LIMIT = 200_000
WRAP = ["systemd-run", "--user", "--scope", "-q", "-p", "MemoryMax=12G", "-p", "MemorySwapMax=0"]
ATTR = re.compile(r",? ?org'Stop'kframework'Stop'attributes'Stop'(?:Source|Location)\{\}\(\"[^\"]*\"\)"
                  r"|,? ?org\.kframework\.attributes\.(?:Source|Location)\((?:Source|Location)\([^)]*\)\)")


def builtin_dir():
    return os.path.join(os.path.dirname(os.path.dirname(os.path.realpath(KOMPILE))),
                        "include/kframework/builtin")


def norm(text, src):
    text = text.replace(src + "/", "FIXTURE/").replace(src, "FIXTURE")
    text = text.replace(builtin_dir() + "/", "BUILTIN/")
    return re.sub(r"/nix/store/[a-z0-9]{32}-[^/\s\"]*", "NIXSTORE", text)


def main_module(kore):
    """The lines of the last module of a kompiled text (kompile writes the main module last)."""
    lines = kore.split("\n")
    start = max(i for i, l in enumerate(lines) if l.startswith("module "))
    end = next(i for i in range(start, len(lines)) if lines[i].startswith("endmodule"))
    return lines[start:end + 1]


SENT = re.compile(r"^(  (axiom|symbol|sort|hooked-symbol|hooked-sort|import|alias|claim)\b|module |endmodule)")


def sentences(lines):
    """The main module's lines grouped into sentences, a `// rule ...` comment line with the sentence
    that follows it; the section comments (`// sorts`, ...) and blank lines are dropped."""
    out, cur, after_comment = [], None, False
    for l in lines:
        if l.startswith("// ") and not l.startswith("// rule") and not l.startswith("// claim"):
            continue
        if not l.strip():
            continue
        if l.startswith("// "):
            cur = [l]; out.append(cur); after_comment = True; continue
        if SENT.match(l) and not after_comment:
            cur = [l]; out.append(cur)
        elif cur is None:
            cur = [l]; out.append(cur)
        else:
            cur.append(l)
        after_comment = False
    return ["\n".join(g) for g in out]


GEN = re.compile(r"(Var'Unds'Gen|_Gen)(\d+)")
CHUNK = re.compile(r"^(?=  (?:axiom|symbol|sort|hooked-symbol|hooked-sort|import|alias|claim)\b|// rule|// claim|module |endmodule)", re.M)


def alpha(text):
    """The variables kompile generates (Var'Unds'GenN, and _GenN in its `// rule` comments) renumbered
    by first occurrence within each sentence: kompile numbers them differently from run to run."""
    def one(chunk):
        seen = {}
        return GEN.sub(lambda m: m[1] + str(seen.setdefault(m[0], len([k for k in seen if k.startswith(m[1])]))), chunk)
    return "".join(one(c) for c in CHUNK.split(text))


def _string_end(t, i):
    """The index after the KORE string literal that starts at t[i] == '"'."""
    i += 1
    while i < len(t):
        if t[i] == "\\":
            i += 2; continue
        if t[i] == '"':
            return i + 1
        i += 1
    raise ValueError("kfix: unterminated string literal")


def _close(t, i):
    """The index of the bracket closing the one at t[i] ('(' or '{'), string literals skipped."""
    depth = 0
    while i < len(t):
        ch = t[i]
        if ch == '"':
            i = _string_end(t, i); continue
        if ch in "({":
            depth += 1
        elif ch in ")}":
            depth -= 1
            if depth == 0:
                return i
        i += 1
    raise ValueError("kfix: unbalanced brackets in a disjunction")


def _args(t, i):
    """The arguments of the application whose '(' is t[i], split at top-level commas, and the index
    after its ')'."""
    end, out, depth, start, j = _close(t, i), [], 0, i + 1, i + 1
    while j < end:
        ch = t[j]
        if ch == '"':
            j = _string_end(t, j); continue
        if ch in "({":
            depth += 1
        elif ch in ")}":
            depth -= 1
        elif ch == "," and depth == 0:
            out.append(t[start:j]); start = j + 1
        j += 1
    out.append(t[start:end])
    return out, end + 1


OR = "\\or{"


def _or_app(t, i):
    """For the \\or application at t[i]: its sort (whitespace removed), arguments, and end index."""
    s_end = _close(t, i + len(OR) - 1)
    sort = re.sub(r"\s+", "", t[i + len(OR) - 1:s_end + 1])
    j = s_end + 1
    while j < len(t) and t[j].isspace():
        j += 1
    if j >= len(t) or t[j] != "(":
        raise ValueError("kfix: \\or without arguments")
    args, end = _args(t, j)
    return sort, args, end


def _ws(t):
    """Whitespace runs outside string literals collapsed to one space."""
    out, i = [], 0
    while i < len(t):
        if t[i] == '"':
            e = _string_end(t, i); out.append(t[i:e]); i = e; continue
        if t[i].isspace():
            while i < len(t) and t[i].isspace():
                i += 1
            out.append(" "); continue
        out.append(t[i]); i += 1
    return "".join(out).strip()


def disjunctions_sorted(t):
    """Every maximal chain of \\or applications of one sort, \\or{S}(A, \\or{S}(B, ...)) nested
    either way, rebuilt as the right-nested chain of its disjuncts in a fixed order: the order of
    their texts with the generated variables renumbered within each disjunct (kompile numbers them
    by position, so their numbers cannot order the disjuncts). \\or is commutative and associative,
    so every arrangement of one set of disjuncts denotes the same pattern; kompile writes some
    disjunctions (the negated left sides of an [owise] equation's siblings, for one) in an order
    that changes from run to run, so the stripped text fixes one arrangement. Disjuncts are
    themselves rewritten first; `// rule` / `// claim` comment lines and string literals are left
    as they are."""
    out, i, n = [], 0, len(t)
    while i < n:
        if t.startswith("// ", i) and (i == 0 or t[i - 1] == "\n"):
            e = t.find("\n", i); e = n if e < 0 else e
            out.append(t[i:e]); i = e; continue
        if t[i] == '"':
            e = _string_end(t, i); out.append(t[i:e]); i = e; continue
        if t.startswith(OR, i):
            sort, args, end = _or_app(t, i)
            leaves, todo = [], list(reversed(args))
            while todo:
                a = todo.pop().strip()
                if a.startswith(OR):
                    s2, a2, e2 = _or_app(a, 0)
                    if s2 == sort and not a[e2:].strip():
                        todo.extend(reversed(a2)); continue
                leaves.append(_ws(disjunctions_sorted(a)))
            leaves.sort(key=lambda d: (alpha(d), d))
            chain = leaves[-1]
            for d in reversed(leaves[:-1]):
                chain = f"\\or{sort}({d}, {chain})"
            out.append(chain); i = end; continue
        out.append(t[i]); i += 1
    return "".join(out)


def main_name(kore):
    """The name of the text's last module (kompile writes the main module last), or None."""
    names = re.findall(r"^module (\S+)", kore, re.M)
    return names[-1] if names else None


def unmodule(t, name):
    """t with the main module's name `name` replaced by MAIN where a symbol's label holds it: K's
    label `..._NAME_Sort...` is written `...Unds'NAME'Unds'Sort...`, the `_` before the name being
    the end of the mangled run before it (`'Unds'NAME` after a letter, `'LParUndsRParUnds'NAME`
    after `(_)`). Only that name: another token in that place (a sort such as K, a library
    module's name) is kept, so that two texts differing there are not made equal."""
    if not name:
        return t
    return re.sub(r"(?<=Unds)'" + re.escape(name) + r"'(?=Unds')", "'MAIN'", t)


def stripped(kore):
    """The text compared by same_as / differs_from and hashed as `stripped sha256`: Source and
    Location attributes removed, module names replaced (each `module` line's, and the main
    module's where a label holds it: unmodule), disjunctions in a fixed order
    (disjunctions_sorted), and generated variables renumbered (alpha), in that order so that
    neither the module names nor the generated variables' numbers fix a disjunct's place."""
    t = ATTR.sub("", kore).replace("[, ", "[").replace("[,", "[")
    t = unmodule(t, main_name(t))
    t = re.sub(r"^module \S+", "module MAIN", t, flags=re.M)
    return alpha(disjunctions_sorted(t))


def sha(s):
    return hashlib.sha256(s.encode()).hexdigest()


def conf(name):
    p = os.path.join(FX, name, "fixture.toml")
    c = tomllib.load(open(p, "rb")) if os.path.exists(p) else {}
    c.setdefault("main", name + ".k")
    c.setdefault("extra", [])
    c.setdefault("expect", "ok")
    return c


def run_kore(name, c):
    """A fixture of a KORE text kompile does not write (fixture.toml `kore`): its account only."""
    for f in ("kore.txt", "account.txt"):
        if os.path.exists(os.path.join(FX, name, f)):
            os.remove(os.path.join(FX, name, f))
    t0 = time.time()
    a = subprocess.run([*WRAP, "timeout", "300", KCORE, "account", c["kore"]], cwd=K,
                       capture_output=True, text=True, env={**os.environ, "LEAN_NUM_THREADS": "1"})
    secs = time.time() - t0
    open(os.path.join(FX, name, "account.txt"), "w").write(a.stdout + a.stderr + f"(exit {a.returncode})\n")
    text = open(os.path.join(K, c["kore"])).read()
    open(os.path.join(FX, name, "kompile.txt"), "w").write("\n".join([
        f"command: none: fixture.toml kore = {c['kore']!r}, a KORE text kompile does not write; "
        f"account.txt is `kcore account {c['kore']}` (cwd: kcore-spec)",
        f"definition.kore bytes: {len(text.encode())}", f"definition.kore sha256: {sha(text)}"]) + "\n")
    print(f"kfix {name}: kcore account exit {a.returncode}, {secs:.1f}s")
    return secs


def run(name):
    c = conf(name)
    if "kore" in c:
        return run_kore(name, c)
    w = os.path.join(WORK, name)
    src = os.path.join(w, "src")
    shutil.rmtree(w, ignore_errors=True)
    shutil.copytree(os.path.join(FX, name), src,
                    ignore=shutil.ignore_patterns("kompile.txt", "kore.txt", "account.txt"))
    # each file of src: the file of the tree (or of the k-rust checkout) it is a copy of
    origin = {f: os.path.relpath(os.path.join(FX, name, f), relsource.TREE) for f in os.listdir(src)}
    if "text_from" in c:
        for f in os.listdir(os.path.join(FX, c["text_from"])):
            if f not in ("kompile.txt", "kore.txt", "account.txt", "fixture.toml"):
                shutil.copy(os.path.join(FX, c["text_from"], f), src)
                origin[f] = os.path.relpath(os.path.join(FX, c["text_from"], f), relsource.TREE)
    ext = []
    for rel in c.get("external", []):
        shutil.copy(os.path.join(KR, rel), src)
        origin[os.path.basename(rel)] = rel
        ext.append(f"external {rel}: sha256 {hashlib.sha256(open(os.path.join(KR, rel), 'rb').read()).hexdigest()}")
    args = c["args"] if "args" in c else ["--backend", "haskell", *c["extra"], c["main"], "-o", "out"]
    cmd = ["kompile", *args]
    t0 = time.time()
    p = subprocess.run([*WRAP, "timeout", "900", KOMPILE, *args], cwd=src, capture_output=True,
                       text=True, env={**os.environ, "LEAN_NUM_THREADS": "1"})
    secs = time.time() - t0
    out = norm(p.stdout + p.stderr, src)
    rep = [f"command: {' '.join(cmd)}  (cwd: the fixture directory)", f"exit: {p.returncode}",
           f"seconds: {secs:.1f}", *ext]
    kp = os.path.join(src, "out/definition.kore")
    for f in ("kore.txt", "account.txt"):
        if os.path.exists(os.path.join(FX, name, f)):
            os.remove(os.path.join(FX, name, f))
    ok = p.returncode == 0
    if ok and os.path.exists(kp):
        kore = norm(open(kp).read(), src)
        rep += [f"definition.kore bytes: {len(kore.encode())}", f"definition.kore sha256: {sha(kore)}",
                f"stripped sha256: {sha(stripped(kore))}"]
        open(os.path.join(w, "definition.norm.kore"), "w").write(kore)
        ss = sentences(main_module(kore))
        ref = c.get("text_from", "base")
        if name == "base":
            keep = set()
        else:
            bp = os.path.join(WORK, ref, "definition.norm.kore")
            if not os.path.exists(bp):
                raise SystemExit(f"kfix: run fixture {ref} before {name}")
            keep = {alpha(g) for g in sentences(main_module(open(bp).read()))}
        delta = [f"//@ {i}\n{g}" for i, g in enumerate(ss)
                 if alpha(g) not in keep and "Source(BUILTIN/" not in g]
        size = sum(len(g) for g in delta)
        if size > LIMIT:
            keep_re = [re.compile(x) for x in c.get("keep", [])]
            full = len(delta)
            delta = [g for g in delta if "Source(FIXTURE" in g or any(r.search(g) for r in keep_re)]
            rep.append(f"main module: {len(ss)} sentences, {full} not in {ref}'s ({size} bytes, over "
                       f"{LIMIT}): kore.txt holds the {len(delta)} with a Source in the fixture"
                       + (f" or matching keep {c['keep']}" if keep_re else ""))
        else:
            rep.append(f"main module: {len(ss)} sentences, {len(delta)} not in {ref}'s, in kore.txt")
        if c.get("kore_txt", True):
            open(os.path.join(FX, name, "kore.txt"), "w").write("\n".join(delta) + "\n")
        else:
            rep.append("kore.txt: not written (fixture.toml kore_txt = false); the command regenerates the text")
        a = subprocess.run([KCORE, "account", "out/definition.kore"], cwd=src, capture_output=True,
                           text=True)
        open(os.path.join(FX, name, "account.txt"), "w").write(
            norm(a.stdout + a.stderr, src) + f"(exit {a.returncode})\n")
        for rel in ("same_as", "differs_from"):
            if rel in c:
                op = os.path.join(WORK, c[rel], "definition.norm.kore")
                if not os.path.exists(op):
                    raise SystemExit(f"kfix: run fixture {c[rel]} before {name}")
                eq = stripped(open(op).read()) == stripped(kore)
                rep.append(f"{rel} {c[rel]}: {'equal' if eq else 'different'} after stripping")
        # the text left in .lake (the one copied into the tree) names each source by the file it
        # is a copy of, relative (test/relsource.py); the outputs above were computed before
        kr = relsource.krust_root()
        relsource.rewrite_file(kp, lambda p: origin.get(p[len(src) + 1:], os.path.relpath(p, relsource.TREE))
                               if p.startswith(src + "/") else relsource.relative(p, kr))
    elif ok:
        rep.append("definition.kore: none written")
    if (c["expect"] == "ok") != ok:
        rep.append(f"UNEXPECTED: expect {c['expect']}")
    lines = out.strip().split("\n")
    rep += ["output:"] + ["  " + l for l in lines[:80]] + (
        [f"  ... {len(lines) - 80} more lines"] if len(lines) > 80 else [])
    open(os.path.join(FX, name, "kompile.txt"), "w").write("\n".join(rep) + "\n")
    print(f"kfix {name}: exit {p.returncode}, {secs:.1f}s" + (
        "" if (c["expect"] == "ok") == ok else "  UNEXPECTED"))
    return secs


def rehash(names):
    """Rewrite kompile.txt's `stripped sha256` and same_as / differs_from lines from the cached
    .lake/kfix/NAME/definition.norm.kore when its sha256 is the recorded definition.kore sha256 (the
    same run's text), after a change to `stripped`; the fixtures with no such cache are listed, to
    be run."""
    stale, done = [], 0
    for name in names:
        kt = os.path.join(FX, name, "kompile.txt")
        t = open(kt).read() if os.path.exists(kt) else ""
        if "\nstripped sha256: " not in t:
            continue
        cp = os.path.join(WORK, name, "definition.norm.kore")
        m = re.search(r"^definition\.kore sha256: (\w+)$", t, re.M)
        if not (m and os.path.exists(cp) and sha(open(cp).read()) == m[1]):
            stale.append(name); continue
        kore = open(cp).read()
        t = re.sub(r"^stripped sha256: \w+$", f"stripped sha256: {sha(stripped(kore))}", t, flags=re.M)
        c = conf(name)
        for rel in ("same_as", "differs_from"):
            if rel in c:
                op = os.path.join(WORK, c[rel], "definition.norm.kore")
                if not os.path.exists(op):
                    stale.append(name); break
                eq = stripped(open(op).read()) == stripped(kore)
                t = re.sub(rf"^{rel} \S+: \w+ after stripping$",
                           f"{rel} {c[rel]}: {'equal' if eq else 'different'} after stripping", t, flags=re.M)
        else:
            open(kt, "w").write(t); done += 1
    print(f"kfix rehash: {done} rewritten, {len(stale)} with no cache of their run"
          + (": " + " ".join(stale) if stale else ""))
    return 1 if stale else 0


def reading_notes():
    """The constructors of Parse.ReadingNote, in the order of KcoreSpec/Parse.lean."""
    src = open(os.path.join(K, "KcoreSpec/Parse.lean")).read()
    block = src.split("\ninductive ReadingNote where\n", 1)[1].split("\n  deriving", 1)[0]
    return re.findall(r"^  \| (\w+)", block, re.M)


def prints_note(account, note):
    """account.txt prints the note: a read class, a per-sentence reading, or a count above 0."""
    w = re.escape(note)
    return bool(re.search(rf"^\s*[1-9]\d* read {w} \[|^\s*sentence \d+: .*\b{w}\b"
                          rf"|\({w}\): [1-9]", account, re.M))


def check_notes(rows):
    """Each `notes` entry of a row or case (any list) names a fixture whose account prints the note,
    and every ReadingNote constructor has one."""
    notes, bad, seen = reading_notes(), [], {}

    def entries(where, e):
        yield where, e
        for i, c in enumerate(e.get("cases", [])):
            if isinstance(c, dict):
                yield from entries(f"{where} cases[{i}]", c)
    for l in (f"E{i}" for i in range(1, 9)):
        for key, r in rows.get(l, {}).items():
            for where, e in entries(f"{l} {key}", r):
                for note, f in e.get("notes", {}).items():
                    if note not in notes:
                        bad.append(f"{where}: notes {note}: no constructor of ReadingNote"); continue
                    a = os.path.join(FX, f, "account.txt")
                    if not os.path.exists(a):
                        bad.append(f"{where}: notes {note}: no fixtures/{f}/account.txt"); continue
                    if not prints_note(open(a).read(), note):
                        bad.append(f"{where}: notes {note}: fixtures/{f}/account.txt does not print it"); continue
                    seen.setdefault(note, set()).add(f)
    for note in notes:
        if note not in seen:
            bad.append(f"ReadingNote.{note}: no `notes` entry names a fixture")
    print(f"kfix notes: {len(seen)} of {len(notes)} ReadingNote constructors with a fixture printing them"
          + "".join(f"; {x}: {', '.join(sorted(seen[x]))}" for x in notes if x in seen))
    return bad


def check(lists):
    rows = tomllib.load(open(os.path.join(K, "test/constructs/rows.toml"), "rb"))
    bad, n, cache = [], {}, {}
    for l in lists:
        for key, r in rows[l].items():
            f = r.get("fixture")
            n.setdefault(l, [0, 0])
            if not f:
                bad.append(f"{l} {key}: no fixture"); continue
            if ("sentence" in r) == ("no_sentence" in r):
                bad.append(f"{l} {key}: needs exactly one of sentence, no_sentence"); continue
            if f == "none":
                if "no_sentence" not in r:
                    bad.append(f"{l} {key}: fixture none without no_sentence")
                n[l][1] += 1; continue
            d = os.path.join(FX, f)
            if not os.path.isdir(d):
                bad.append(f"{l} {key}: no fixture directory {f}"); continue
            if f not in cache:
                cache[f] = "".join(open(os.path.join(d, x)).read() for x in ("kore.txt", "kompile.txt")
                                   if os.path.exists(os.path.join(d, x)))
            for s in r.get("sentence", []):
                if s not in cache[f]:
                    bad.append(f"{l} {key}: {s!r} not in {f}")
            n[l][0 if "sentence" in r else 1] += 1
    for f in sorted(os.listdir(FX)):
        kt = os.path.join(FX, f, "kompile.txt")
        if not os.path.exists(kt):
            bad.append(f"fixture {f}: not run"); continue
        t = open(kt).read()
        if "UNEXPECTED" in t:
            bad.append(f"fixture {f}: unexpected exit")
        for m in re.finditer(r"^(same_as|differs_from) (\S+): (\w+)", t, re.M):
            if (m[1] == "same_as") != (m[3] == "equal"):
                bad.append(f"fixture {f}: {m[1]} {m[2]} is {m[3]}")
        c = conf(f)
        for rel in ("same_as", "differs_from"):
            if rel in c and f"{rel} {c[rel]}:" not in t:
                bad.append(f"fixture {f}: {rel} not recorded")
    bad += check_notes(rows)
    for l in lists:
        n.setdefault(l, [0, 0])
        print(f"kfix {l}: {n[l][0]} rows with sentences, {n[l][1]} rows with no_sentence")
    nofx = [b for b in bad if b.endswith(": no fixture")]
    for l in lists:
        c = sum(1 for b in nofx if b.startswith(l + " "))
        if c:
            print(f"kfix {l}: {c} rows without a fixture")
    rest = [b for b in bad if not b.endswith(": no fixture")]
    for b in rest[:60]:
        print("kfix: " + b)
    if len(rest) > 60:
        print(f"kfix: ... {len(rest) - 60} more")
    return 1 if bad else 0


if __name__ == "__main__":
    if sys.argv[1:2] == ["check"]:
        sys.exit(check(sys.argv[2:] or LISTS))
    if sys.argv[1:2] == ["rehash"]:
        sys.exit(rehash(sys.argv[2:] or sorted(os.listdir(FX))))
    if sys.argv[1:2] != ["run"]:
        raise SystemExit(__doc__)
    names = sys.argv[2:] or sorted(os.listdir(FX))
    # base first, then every fixture before those that compare with it
    order, seen = [], set()

    def visit(x):
        if x in seen: return
        seen.add(x)
        c = conf(x)
        for rel in ("same_as", "differs_from", "text_from"):
            if rel in c and c[rel] in names: visit(c[rel])
        order.append(x)
    if "base" in names: visit("base")
    for x in names: visit(x)
    names = order
    t = sum(run(x) for x in names)
    print(f"kfix: {len(names)} kompiles, {t:.0f}s")
