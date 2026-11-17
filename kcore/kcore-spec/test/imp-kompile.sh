#!/usr/bin/env bash
# Row imp, the kompile command (DONE-0 C9 part 1): test/imp-kompile.toml records the command that
# produced ref-kimp's definition.kore; this script checks the record against the option set the rows
# are stated for (DONE-0 reading R-12: kompile 7.1.337, default options, `--backend haskell`) and
# against the committed text.
#
# The record meets R-12 when its argv is `kompile FILE --backend haskell` and every other option is
# one of those below, each of which selects nothing a default would not:
#   --main-module M, --syntax-module S   only with the names kompile takes by default for FILE
#                                        (the file's name in capitals, and that name with -SYNTAX)
#   --output-definition DIR              where the kompiled directory is written
#   -I DIR                               where `requires` finds files
#   --warnings none                      which diagnostics are printed
# Any other option, another backend, or module names that are not the defaults: exit 1.
#
# Against the text: its SHA-256 is the recorded one; it is f2-examples/ref-kimp.kore byte for byte;
# its definition attribute names FILE as `Source`, and its builtin sentences name an installation
# of the recorded K version.
#
# With --rerun the command is run (kompile: $K_KOMPILE, or k/result/bin/kompile of the k-rust
# checkout; ${imp}: $IMP_SEMANTICS_CHECKOUT, or imp-semantics of the checkout, which must be at the
# recorded revision) and its definition.kore compared with the committed text, the user `Source`
# paths made relative as the committed ones are and the hash of the K installation's store path
# left out. The JVM under a 12 GiB memory scope. Without --rerun nothing is kompiled.
# Usage: test/imp-kompile.sh [--rerun]   (from anywhere)
set -u
K=$(cd "$(dirname "$0")/.." && pwd); cd "$K"
rerun=0; [ "${1:-}" = --rerun ] && rerun=1
if [ -n "${K_RUST:-}" ]; then KR=$K_RUST
else KR=; d=$K; while [ "$d" != / ]; do d=$(dirname "$d")
  [ -f "$d/Cargo.toml" ] && [ -d "$d/crates/k-rust" ] && { KR=$d; break; }; done; fi
out=$(mktemp -d); trap 'rm -rf "$out"' EXIT
RERUN=$rerun KR=$KR OUT=$out KOMPILE=${K_KOMPILE:-} IMP=${IMP_SEMANTICS_CHECKOUT:-} python3 -I - <<'PY'
import hashlib, os, re, subprocess, sys, tomllib

def fail(msg):
    print("imp-kompile: " + msg); print("imp-kompile: FAIL"); sys.exit(1)

rec = tomllib.load(open("test/imp-kompile.toml", "rb"))
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
        fail(f"option {o} is outside R-12 (default options and --backend haskell)")
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

text = open(rec["text"], "rb").read()
if hashlib.sha256(text).hexdigest() != rec["sha256"]:
    fail(f"{rec['text']} does not have the recorded SHA-256")
if text != open("f2-examples/ref-kimp.kore", "rb").read():
    fail(f"{rec['text']} is not f2-examples/ref-kimp.kore")
rel = src.replace("${imp}", "imp-semantics")
head = text.split(b"\n", 1)[0].decode()
if f'Source{{}}("Source({rel})")' not in head:
    fail(f"the definition attribute does not name {rel} as Source")
stores = set(re.findall(rb"Source\((/[^)\"]*)/include/kframework/builtin/[^/)]+\)", text))
if not stores or any(not re.search(rb"-k-" + re.escape(rec["k_version"].encode()) + rb"-[0-9a-f]+$", s) for s in stores):
    fail(f"a builtin Source names no installation of K {rec['k_version']}: {sorted(stores)[:2]}")
print(f"imp-kompile: the record is within R-12 and {rec['text']} has its SHA-256")

if os.environ["RERUN"] != "1":
    print("imp-kompile: ok (not re-run)"); sys.exit(0)
kr = os.environ["KR"]
kompile = os.environ["KOMPILE"] or os.path.join(kr, "k/result/bin/kompile")
imp = os.environ["IMP"] or os.path.join(kr, "imp-semantics")
if not os.path.isfile(kompile) or not os.path.isdir(imp):
    print(f"imp-kompile: no kompile at {kompile} or no checkout at {imp}"); sys.exit(2)
ver = subprocess.run([kompile, "--version"], capture_output=True, text=True).stdout
if rec["k_version"] not in ver:
    fail(f"kompile is not {rec['k_version']}: {ver.strip()[:80]}")
rev = subprocess.run(["git", "-C", imp, "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
if rev != rec["revision"]:
    fail(f"the imp-semantics checkout is at {rev}, not {rec['revision']}")
od = os.path.join(os.environ["OUT"], "kompiled")
cmd = [kompile] + [a.replace("${imp}", imp).replace("${out}", od) for a in argv[1:]]
env = dict(os.environ, K_OPTS=os.environ.get("K_OPTS", "-Xmx4g"))
r = subprocess.run(["systemd-run", "--user", "--scope", "-q", "-p", "MemoryMax=12G", "-p",
                    "MemorySwapMax=0", "timeout", "900"] + cmd, env=env, capture_output=True, text=True)
if r.returncode != 0:
    fail(f"kompile exit {r.returncode}: {(r.stdout + r.stderr).strip()[-300:]}")
new = open(os.path.join(od, "definition.kore"), "rb").read()
store = re.compile(rb"/nix/store/[a-z0-9]{32}-")
norm = lambda t: store.sub(b"/nix/store/-", t)
new = new.replace(imp.encode() + b"/", b"imp-semantics/")
if norm(new) != norm(text):
    a, b = norm(new).split(b"\n"), norm(text).split(b"\n")
    n = sum(1 for x, y in zip(a, b) if x != y) + abs(len(a) - len(b))
    fail(f"the command's definition.kore differs from {rec['text']} in {n} lines")
print("imp-kompile: ok (re-run: the command gives the committed text, Source paths relative, the store hash left out)")
PY
