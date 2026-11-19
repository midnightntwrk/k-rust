"""KPROV.scope-corpus-count: `kcore scope-count` over the parsed texts of the fixtures and of the
corpus, counting, outside the prelude's modules, the forms findings/KPROV-scope.md calls never
written: Pattern.iff, mu, nu, next, leftAssoc, rightAssoc; Pattern.string in a sentence's pattern
(never an attribute's, never a domain value's); Sentence.alias; axioms without `simplification`
of the form \\equals(f(...), _), under an \\implies or not, with a set variable under f's
application (svarEqn); axioms without `simplification` or `symbol-overload` of the form
\\equals(c(...), r), under an \\implies or not, c a symbol the text declares `constructor` and r
(the first conjunct of an \\and) no application of one (ctorEqn: an equation headed by a
constructor, rows.toml E5 convertRule:axiom#1's H1 case with a function right side); axioms
\\exists B. (phi_1 and ... and phi_n), n >= 2, a conjunct equating an application to B (existEqn,
the reader's existentialAxiom? shape: the H8 case); and axioms carrying smt-lemma whose pattern
holds a \\rewrites (smtRewrites: E2 SMT_LEMMA(smt-lemma)@rule's case).

Texts, in three groups printed apart:
  kompiled  the kompiled text of every fixture kompile wrote one for (.lake/kfix/NAME/src/out/
            definition.kore, `kfix.py run NAME`; where this tree has no run of it, the text
            kompile.txt records from kfix.py's cache, kfix.recorded_text);
  hand      the hand-written texts (`kore = ...` in a fixture.toml), which are written to hold
            such forms and are no evidence of what kompile writes;
  corpus    .lake/corpus/defs/*.kore (unpacked from ~/.cache/k-rust/reference-outputs/v1 by
            test/corpus.py's extract when the directory is absent).
Each run serially under a 12 GiB scope. Prints, per group, the number of texts, the totals, and
every text with a non-zero count. Expected 0 for every count in kompiled and corpus, except alias in
e8-enable-kore-antileft (written under --enable-kore-antileft).

Usage (from kcore-spec, kcore built): python3 -I test/constructs/scope-count.py [KCORE]
"""
import os, subprocess, sys, tomllib

sys.dont_write_bytecode = True
K = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
FX = os.path.join(K, "test/constructs/fixtures")
WORK = os.path.join(K, ".lake/kfix")
CORPUS = os.path.join(K, ".lake/corpus/defs")
KCORE = sys.argv[1] if len(sys.argv) > 1 else os.path.join(K, ".lake/build/bin/kcore")
WRAP = ["systemd-run", "--user", "--scope", "-q", "-p", "MemoryMax=12G", "-p", "MemorySwapMax=0",
        "timeout", "600"]
KEYS = ["iff", "mu", "nu", "next", "leftAssoc", "rightAssoc", "string", "alias", "svarEqn",
        "ctorEqn", "existEqn", "smtRewrites"]


def count(path):
    r = subprocess.run([*WRAP, KCORE, "scope-count", path], cwd=K, capture_output=True, text=True,
                       env={**os.environ, "LEAN_NUM_THREADS": "1"})
    if r.returncode != 0:
        return None, (r.stdout + r.stderr).strip()
    f = dict(x.split("=", 1) for x in r.stdout.strip().split("\t"))
    return {k: int(f[k]) for k in KEYS}, f["modules"]


def groups():
    sys.path.insert(0, os.path.join(K, "test/constructs"))
    sys.path.insert(0, os.path.join(K, "test"))
    import corpus as corpus_mod, kfix
    kompiled, hand = [], []
    for name in sorted(os.listdir(FX)):
        t = os.path.join(FX, name, "fixture.toml")
        conf = tomllib.load(open(t, "rb")) if os.path.exists(t) else {}
        if "kore" in conf:
            hand.append((name, os.path.join(K, conf["kore"])))
        else:
            p = os.path.join(WORK, name, "src/out/definition.kore")
            h = kfix.recorded_sha(name)
            if os.path.exists(p):
                kompiled.append((name, p))
            elif h and kfix.recorded_text(name) is not None:
                kompiled.append((name, os.path.join(kfix.CACHE, h + ".kore")))
    if not os.path.isdir(CORPUS):
        corpus_mod.extract()
    corpus = [(f[:-5], os.path.join(CORPUS, f)) for f in sorted(os.listdir(CORPUS)) if f.endswith(".kore")]
    return [("kompiled", kompiled), ("hand", hand), ("corpus", corpus)]


def main():
    for g, texts in groups():
        tot = {k: 0 for k in KEYS}
        hits, fails = [], []
        for name, p in texts:
            c, mods = count(p)
            if c is None:
                fails.append((name, mods))
                continue
            for k in KEYS:
                tot[k] += c[k]
            nz = {k: v for k, v in c.items() if v}
            if nz:
                hits.append((name, nz))
        print(f"{g}: {len(texts)} texts, {len(fails)} unreadable; " + ", ".join(f"{k} {tot[k]}" for k in KEYS))
        for name, nz in hits:
            print(f"  {name}: " + ", ".join(f"{k} {v}" for k, v in nz.items()))
        for name, why in fails:
            print(f"  UNREADABLE {name}: {why[:200]}")


main()
