#!/usr/bin/env bash
# Row KORE in K, the kompile command: test/kk-kompile.toml records the command that produced
# ref-kk's definition.kore from krs/semantics/kore/kore.k; this script checks the record against the
# option set the rows are stated for (DONE-0 reading R-12: kompile 7.1.337, default options,
# `--backend haskell`), as test/imp-kompile.sh does for row imp, and against the committed text.
#
# The record meets the option set when its argv is `kompile FILE --backend haskell` and every other
# option is one of those below, each of which selects nothing a default would not:
#   --main-module M, --syntax-module S   only with the names kompile takes by default for FILE
#                                        (the file's name in capitals, and that name with -SYNTAX)
#   --output-definition DIR              where the kompiled directory is written
#   -I DIR                               where `requires` finds files
#   --warnings none                      which diagnostics are printed
# Any other option, another backend, or module names that are not the defaults: exit 1.
#
# Against the source and the text: kore.k, where the checkout holds it, has the recorded SHA-256;
# the text has its recorded SHA-256; its definition attribute names the
# source as `Source`, and its builtin sentences name an installation of the recorded K version.
#
# With --rerun the command is run (kompile: $K_KOMPILE, or k/result/bin/kompile of the k-rust
# checkout) and its definition.kore compared with the committed text, the user `Source` paths made
# relative as the committed ones are and the hash of the K installation's store path left out:
# sentence by sentence, each byte for byte, except that an [owise] equation's axiom may differ in
# the order of its lines and the numbering of its generated variables (`Var'Unds'GenN`). kompile
# 7.1.337 writes the disjuncts of the negated competing left sides of an [owise] axiom in an order
# that depends on the absolute path of the source file (two runs from one path agree; runs from
# different checkouts do not); the disjuncts form an \or, whose meaning their order does not change.
# The JVM under a 12 GiB memory scope. Without --rerun nothing is kompiled.
# Usage: test/kk-kompile.sh [--rerun]   (from anywhere)
set -u
K=$(cd "$(dirname "$0")/.." && pwd); cd "$K"
rerun=0; [ "${1:-}" = --rerun ] && rerun=1
if [ -n "${K_RUST:-}" ]; then KR=$K_RUST
else KR=; d=$K; while [ "$d" != / ]; do d=$(dirname "$d")
  [ -d "$d/krs/semantics/kore" ] && { KR=$d; break; }; done; fi
out=$(mktemp -d); trap 'rm -rf "$out"' EXIT
RERUN=$rerun KR=$KR OUT=$out KOMPILE=${K_KOMPILE:-} python3 -I - <<'PY'
import hashlib, os, re, subprocess, sys, tomllib

def fail(msg):
    print("kk-kompile: " + msg); print("kk-kompile: FAIL"); sys.exit(1)

rec = tomllib.load(open("test/kk-kompile.toml", "rb"))
argv = rec["argv"]
if len(argv) < 2 or argv[0] != "kompile" or argv[1].startswith("-"):
    fail("argv is not `kompile FILE ...`")
src = argv[1]
stem = os.path.splitext(os.path.basename(src))[0].upper()
seen, i = {}, 2
arity = {"--backend": 1, "--main-module": 1, "--syntax-module": 1, "--output-definition": 1,
         "-I": 1, "--warnings": 1}
while i < len(argv):
    o = argv[i]
    if o not in arity:
        fail(f"option {o} is outside the option set (default options and --backend haskell)")
    if o in seen and o != "-I":
        fail(f"option {o} given twice")
    if i + 1 >= len(argv):
        fail(f"option {o} has no value")
    seen.setdefault(o, []).append(argv[i + 1]); i += 2
if seen.get("--backend") != ["haskell"]:
    fail(f"--backend is {seen.get('--backend')}, not haskell")
if seen.get("--main-module", [stem]) != [stem]:
    fail(f"--main-module is not the default {stem}")
if seen.get("--syntax-module", [stem + "-SYNTAX"]) != [stem + "-SYNTAX"]:
    fail(f"--syntax-module is not the default {stem}-SYNTAX")
if seen.get("--warnings", ["none"]) != ["none"]:
    fail("--warnings is not none")
if seen.get("--output-definition") != ["${out}"]:
    fail("--output-definition is not ${out}")
rel = src.replace("${kk}", "krs/semantics/kore")
if rel != rec["source"]:
    fail(f"argv's file is {rel}, not the recorded source {rec['source']}")

text = open(rec["text"], "rb").read()
if hashlib.sha256(text).hexdigest() != rec["sha256"]:
    fail(f"{rec['text']} does not have the recorded SHA-256")
head = text.split(b"\n", 1)[0].decode()
if f'Source{{}}("Source({rel})")' not in head:
    fail(f"the definition attribute does not name {rel} as Source")
stores = set(re.findall(rb"Source\((/[^)\"]*)/include/kframework/builtin/[^/)]+\)", text))
if not stores or any(not re.search(rb"-k-" + re.escape(rec["k_version"].encode()) + rb"-[0-9a-f]+$", s) for s in stores):
    fail(f"a builtin Source names no installation of K {rec['k_version']}: {sorted(stores)[:2]}")
print(f"kk-kompile: the record is within the option set and {rec['text']} has its SHA-256")

kr = os.environ["KR"]
kk = os.path.join(kr, "krs/semantics/kore") if kr else ""
have = bool(kk) and os.path.isfile(os.path.join(kk, "kore.k"))
if not have:
    print("kk-kompile: no krs/semantics/kore/kore.k above kcore-spec (set K_RUST): the source is not checked")
    if os.environ["RERUN"] == "1":
        sys.exit(2)
elif hashlib.sha256(open(os.path.join(kk, "kore.k"), "rb").read()).hexdigest() != rec["source_sha256"]:
    fail(f"{rec['source']} does not have the recorded SHA-256: the text is of another kore.k")
else:
    print(f"kk-kompile: {rec['source']} has its SHA-256")

if os.environ["RERUN"] != "1":
    print("kk-kompile: ok (not re-run)"); sys.exit(0)
kompile = os.environ["KOMPILE"] or os.path.join(kr, "k/result/bin/kompile")
if not os.path.isfile(kompile):
    print(f"kk-kompile: no kompile at {kompile}"); sys.exit(2)
ver = subprocess.run([kompile, "--version"], capture_output=True, text=True).stdout
if rec["k_version"] not in ver:
    fail(f"kompile is not {rec['k_version']}: {ver.strip()[:80]}")
od = os.path.join(os.environ["OUT"], "kompiled")
cmd = [kompile] + [a.replace("${kk}", kk).replace("${out}", od) for a in argv[1:]]
env = dict(os.environ, K_OPTS=os.environ.get("K_OPTS", "-Xmx4g"))
r = subprocess.run(["systemd-run", "--user", "--scope", "-q", "-p", "MemoryMax=12G", "-p",
                    "MemorySwapMax=0", "timeout", "900"] + cmd, env=env, capture_output=True, text=True)
if r.returncode != 0:
    fail(f"kompile exit {r.returncode}: {(r.stdout + r.stderr).strip()[-300:]}")
new = open(os.path.join(od, "definition.kore"), "rb").read()
store = re.compile(rb"/nix/store/[a-z0-9]{32}-")
norm = lambda t: store.sub(b"/nix/store/-", t)
new = new.replace(os.path.realpath(kk).encode() + b"/", b"krs/semantics/kore/").replace(kk.encode() + b"/", b"krs/semantics/kore/")
sent = re.compile(rb"\n(?=\s*(?:axiom|symbol|hooked-symbol|sort|hooked-sort|import|alias|endmodule|module|claim)\b)")
a, b = sent.split(norm(new)), sent.split(norm(text))
if len(a) != len(b):
    fail(f"the command's definition.kore has {len(a)} sentences, {rec['text']} {len(b)}")
gen = re.compile(rb"Var'Unds'Gen[0-9]+")
up = lambda x: sorted(gen.sub(b"Var'Unds'Gen", x).split(b"\n"))
bad = [i for i, (x, y) in enumerate(zip(a, b)) if x != y and not (b"owise{}()" in y and up(x) == up(y))]
if bad:
    fail(f"the command's definition.kore differs from {rec['text']} in {len(bad)} sentences (the first: {bad[0]})")
n = sum(1 for x, y in zip(a, b) if x != y)
print(f"kk-kompile: ok (re-run: the command gives the committed text, Source paths relative, the store hash left out; {n} [owise] axioms equal up to the order of lines and the numbering of generated variables)")
PY
