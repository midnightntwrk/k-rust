"""DONE-0 C3: the meaning-carrying modifiers, computed from the kompiled texts, and the pair table
[C3] of rows.toml checked.

A fixture with `same_as` or `differs_from` in its fixture.toml (test/constructs/kfix.py) is a text
and the same text without one modifier (its companion). For each such pair `run` compares
  text       the user module's sentences of the two kompiled texts (kfix.py's `stripped`: Source and
             Location removed, comments removed (a `// rule` comment is whitespace to the KORE
             parser and no sentence), module names replaced (in rule labels too), disjunctions
             and their disjuncts' existential binders ordered, generated variables renumbered), as
             sets;
  Semantics  the lines `kcore sem-fields` prints of each (every field of `Fn`, `Clause` and `Rule`,
             and one line per sort, constructor and parameter symbol, the symbols read with no
             clause, with the registry hook that interprets each or none; symbols and sorts by
             name), the main module's name replaced where a label holds it (kfix.py's `unmodule`),
             as sets; a text the reader refuses prints its refusal. A Semantics difference is
             printed with its count per kind of line (fn, clause, rule, sort, ctor, param).
The modifier is a modifier when either differs; where the reader refuses one of the two texts the
Semantics are not compared and the text alone decides. `run` prints, per pair, the counts on each side and
the entries of rows.toml (rows of E1 to E8 and of C3, and their `cases`) whose fixture is the
pair's text, or one of their `also_fixtures` (further fixtures whose texts the entry's evidence
cites as showing the same thing, so that a pair of such a text is printed with the entry); then the modifier set (the entries of a pair that differs); then every pair whose text
differs and whose Semantics does not ("text difference with no Semantics difference": such an
entry is inert with a reason, or a finding); then the count of entries whose fixture has no
companion (not computable here). It needs each fixture's kompiled text under .lake/kfix/NAME/src/out
(kfix.py run NAME) and the built kcore; a pair without them is printed as not computable.

[C3] has one entry per unordered pair of modifiers, keyed "A x B". An entry has status (rows.toml's
statuses, or `independent`), and either fixture and sentence (or no_sentence) as a row of E2 has, or,
for `independent`, `declarations`: the two declarations that read A and B. `core = true` marks the
pairs DONE-0 C3 names (CORE below): each is present, has a fixture other than "none", and is never
`independent`. `check` fails on a missing core pair, a core entry without a fixture or marked
independent, an independent entry without two declarations, a key that is not "A x B", two keys of
one unordered pair, a status outside the vocabulary, or a sentence (of an entry or of its `cases`)
that is not in its fixture's kore.txt or kompile.txt; and, for an entry of any list, a name of
`also_fixtures` that is no fixture directory or that the entry's evidence does not name.

Usage (from kcore-spec):
  python3 -I test/constructs/modifiers.py run [FIXTURE...]   compute (all pairs without names)
  python3 -I test/constructs/modifiers.py check [ROWS.toml]  check [C3] (default test/constructs/rows.toml)
"""
import importlib.util, os, subprocess, sys, tomllib

sys.dont_write_bytecode = True

K = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
_spec = importlib.util.spec_from_file_location("kfix", os.path.join(K, "test/constructs/kfix.py"))
kfix = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(kfix)
FX, ROWS = kfix.FX, os.path.join(K, "test/constructs/rows.toml")
CACHE = os.path.join(K, ".lake/modifiers")
ST = {"supported", "parameter", "inert", "erased", "refused", "pending-fixture", "not-handled",
      "independent"}
# DONE-0 C3's core pairs: the ten among requires, ensures, priority, [owise], [total] for
# equations, the same five for rules where they exist ([total] on a rule: kompile rejects it,
# fixture c3-rule-total), and four more.
_EQ = ["requires", "ensures", "priority", "owise", "total"]
CORE = ([f"equation {a} x equation {b}" for i, a in enumerate(_EQ) for b in _EQ[i + 1:]]
        + [f"rule {a} x rule {b}" for i, a in enumerate(_EQ[:4]) for b in _EQ[i + 1:4]]
        + ["hook x equation", "owise x simplification", "simplification x priority",
           "anywhere rule x constructor"])


def kompiled(name):
    p = os.path.join(kfix.WORK, name, "src/out/definition.kore")
    return p if os.path.exists(p) else None


def text_of(name):
    """The user module's sentences of the fixture's kompiled text, stripped, as a set."""
    kore = open(kompiled(name)).read()
    return set(kfix.sentences(kfix.stripped("\n".join(kfix.main_module(kore))).split("\n"))[1:-1])


def sem_of(name):
    """`kcore sem-fields` of the fixture's kompiled text, the main module's name replaced where a
    label holds it (kfix.unmodule), as a set of lines (cached as printed, by the text's size and
    modification time)."""
    p = kompiled(name)
    os.makedirs(CACHE, exist_ok=True)
    key = f"{os.path.getsize(p)}-{int(os.path.getmtime(p))}-{int(os.path.getmtime(kfix.KCORE))}"
    c = os.path.join(CACHE, name + ".sem")
    mn = kfix.main_name(open(p).read())
    if os.path.exists(c) and open(c).readline().strip() == key:
        return set(kfix.unmodule(open(c).read(), mn).split("\n")[1:]) - {""}
    r = subprocess.run([*kfix.WRAP, "timeout", "300", kfix.KCORE, "sem-fields", p], capture_output=True,
                       text=True, env={**os.environ, "LEAN_NUM_THREADS": "1"})
    out = r.stdout if r.returncode == 0 else f"refused-or-failed\t{r.returncode}\t{r.stderr.strip()}\n"
    open(c, "w").write(key + "\n" + out)
    return set(kfix.unmodule(out, mn).split("\n")) - {""}


def per_kind(sf, sg):
    """The lines only in sf and only in sg, counted by their kind (the first field), as " (k +n -m, ...)"."""
    kind = lambda l: l.split("\t", 1)[0]
    ks = sorted({kind(l) for l in sf ^ sg})
    if not ks:
        return ""
    return " (" + ", ".join(f"{k} +{sum(kind(l) == k for l in sf - sg)} -{sum(kind(l) == k for l in sg - sf)}"
                            for k in ks) + ")"


def entries(rows):
    """(where, entry) for every row of every list and every table of its `cases`, recursively."""
    def walk(where, e):
        yield where, e
        for i, c in enumerate(e.get("cases", [])):
            if isinstance(c, dict):
                yield from walk(f"{where}, case {c.get('case', i)!r}"[:160], c)
    for l, tab in rows.items():
        for key, r in tab.items():
            if isinstance(r, dict):
                yield from walk(f"{l} {key}", r)


def companions(names=None):
    out = []
    for f in sorted(os.listdir(FX)):
        c = kfix.conf(f)
        for rel in ("same_as", "differs_from"):
            if rel in c and (not names or f in names):
                out.append((f, c[rel], rel))
    return out


def run(names):
    rows = tomllib.load(open(ROWS, "rb"))
    by_fx = {}
    for w, e in entries(rows):
        for f in [e.get("fixture"), *e.get("also_fixtures", [])]:
            by_fx.setdefault(f, []).append(w)
    mods, visible, nocomp, pairs = [], [], [], companions(names)
    for f, g, rel in pairs:
        if not (kompiled(f) and kompiled(g)):
            nocomp.append(f); print(f"pair {f} / {g}: not computable (no kompiled text; kfix.py run)"); continue
        tf, tg, sf, sg = text_of(f), text_of(g), sem_of(f), sem_of(g)
        td, sd = (len(tf - tg), len(tg - tf)), (len(sf - sg), len(sg - sf))
        verdict = "modifier" if td != (0, 0) or sd != (0, 0) else "no difference"
        refused = [x for x, sx in ((f, sf), (g, sg)) if any(l.startswith("refused-or-failed") for l in sx)]
        sem = f"Semantics +{sd[0]} -{sd[1]}{per_kind(sf, sg)}" if not refused else "Semantics not compared (the reader refuses " + " and ".join(refused) + ")"
        print(f"pair {f} / {g} ({rel}): text +{td[0]} -{td[1]}, {sem}: {verdict}")
        for w in by_fx.get(f, []):
            print(f"    {w}")
        if verdict == "modifier":
            mods += by_fx.get(f, []) or [f"(fixture {f}: no entry)"]
        if td != (0, 0) and sd == (0, 0) and not refused:
            visible.append((f, g, by_fx.get(f, [])))
    unnamed = [w for w in mods if w.startswith("(fixture ")]
    mods = list(dict.fromkeys(w for w in mods if not w.startswith("(fixture ")))
    print(f"modifier set: {len(mods)} entries; {len(unnamed)} differing fixtures that no entry names")
    for w in mods + unnamed:
        print(f"  {w}")
    print(f"text difference with no Semantics difference: {len(visible)}")
    for f, g, ws in visible:
        print(f"  {f} / {g}: " + ("; ".join(ws) if ws else "no entry"))
    paired = {f for f, _, _ in companions()}
    lone = [w for w, e in entries(rows) if e.get("fixture") not in paired | {None, "none"}
            and not paired & set(e.get("also_fixtures", []))]
    print(f"entries whose fixture has no companion (not computable here): {len(lone)}; pairs not computable: {len(nocomp)}")
    return 0


def check(path=ROWS):
    rows = tomllib.load(open(path, "rb"))
    t, bad, seen, cache = rows.get("C3", {}), [], {}, {}

    def has(f, s):
        if f not in cache:
            d = os.path.join(FX, f)
            cache[f] = "".join(open(os.path.join(d, x)).read() for x in ("kore.txt", "kompile.txt")
                               if os.path.exists(os.path.join(d, x)))
        return s in cache[f]

    def sentences(where, e):
        f = e.get("fixture")
        if f and f != "none":
            if not os.path.isdir(os.path.join(FX, f)):
                bad.append(f"{where}: no fixture directory {f}")
            else:
                bad.extend(f"{where}: {s!r} not in {f}" for s in e.get("sentence", []) if not has(f, s))
        for c in e.get("cases", []):
            if isinstance(c, dict):
                sentences(f"{where}, case {c.get('case', '')[:50]!r}", c)

    for key, e in t.items():
        parts = key.split(" x ")
        if len(parts) != 2 or not all(p.strip() for p in parts):
            bad.append(f"C3 {key!r}: not \"A x B\""); continue
        u = frozenset(p.strip() for p in parts)
        if u in seen:
            bad.append(f"C3 {key!r}: the pair of {seen[u]!r}")
        seen[u] = key
        st = e.get("status")
        if st not in ST:
            bad.append(f"C3 {key!r}: status {st!r}")
        if e.get("core") is True or key in CORE:
            if key in CORE and e.get("core") is not True:
                bad.append(f"C3 {key!r}: a core pair without core = true")
            if key not in CORE:
                bad.append(f"C3 {key!r}: core = true, not a pair of DONE-0 C3")
            if st == "independent":
                bad.append(f"C3 {key!r}: a core pair cannot be independent")
            if e.get("fixture") in (None, "none"):
                bad.append(f"C3 {key!r}: a core pair without a fixture")
        if st == "independent":
            d = e.get("declarations")
            if not (isinstance(d, list) and len(d) == 2 and all(isinstance(x, str) and x for x in d)):
                bad.append(f"C3 {key!r}: independent without the two declarations")
        elif ("sentence" in e) == ("no_sentence" in e):
            bad.append(f"C3 {key!r}: needs exactly one of sentence, no_sentence")
        sentences(f"C3 {key!r}", e)
    bad += [f"C3: core pair {k!r} has no entry" for k in CORE if k not in t]
    for w, e in entries(rows):
        for f in e.get("also_fixtures", []):
            if not os.path.isdir(os.path.join(FX, f)):
                bad.append(f"{w}: also_fixtures {f}: no fixture directory")
            elif f not in e.get("evidence", ""):
                bad.append(f"{w}: also_fixtures {f}: not named in its evidence")
    by = {}
    for e in t.values():
        by[e.get("status")] = by.get(e.get("status"), 0) + 1
    print(f"C3: {len(t)} pairs, {sum(1 for k in t if k in CORE)} of {len(CORE)} core; by status: "
          + ", ".join(f"{s} {n}" for s, n in sorted(by.items(), key=str)))
    for b in bad:
        print("C3: " + b)
    return 1 if bad else 0


if __name__ == "__main__":
    if sys.argv[1:2] == ["run"]:
        sys.exit(run(sys.argv[2:]))
    if sys.argv[1:2] == ["check"]:
        sys.exit(check(*sys.argv[2:3]))
    raise SystemExit(__doc__)
