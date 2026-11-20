#!/usr/bin/env bash
# DONE-0 C8 part 1: the reader mutants of test/constructs/mutants.toml, run. For each mutant (all,
# or those named):
# 1. a scratch copy of kcore-spec under .lake/mutants/NAME (the sources and .lake/build; the sibling
#    packages aml-port and kore-lean linked, read only), the mutant's patch applied (`patch -p1`);
#    only the reader's files may change;
# 2. `lake build --old kcore` there (this tree's build must be current, `lake build --no-build
#    kcore`; the copy's sources are dated before its build): the patched modules are rebuilt and
#    `kcore` relinked; the modules importing them are not rebuilt (`--old`), so `kcore` and the
#    elaborator commands (`definition_of`) run the mutant's reader with the rest of the library as
#    built;
# 3. the row's fixture regenerated: `kcore account` of its text by the mutant (a fixture directory:
#    `kfix.py accounts NAME` with the mutant's binary, against the committed account.txt, which
#    needs K_RUST or K_KOMPILE to name a K installation, kfix.py's rule; a KORE
#    text: against this tree's `kcore account` of it). A difference kills the mutant;
# 4. otherwise the row's theorem module, `lake env lean` in the scratch copy: it reads the text with
#    the mutant's reader, and must fail; the declarations at which Lean reports an error are recorded.
# A mutant whose patch does not apply or which does not build is an error, neither killed nor not.
# Prints one line per mutant (`killed by account`, `killed by theorems: FILE: DECL, ...`,
# `survives`) and the account's first differing lines. Exit 1 when a mutant's outcome is not its
# `expect`, or on an error. The scratch copy is removed unless --keep. Every lean and lake run is
# under a 12 GiB scope, one thread.
#
# Usage (from anywhere; the library and kcore built in this tree):
#   test/mutants.sh [--keep] [--list] [--par] [NAME...]   ($KCORE_MUTANTS: another mutants file)
#     --par   the mutants run several at once, as many as free memory admits (KCORE_RESERVE_GIB,
#             default 16, kept free; KCORE_JOBS an upper bound), each in its own scratch copy
#   test/mutants.sh --kernel    the kernel mutants ([kernel.*]: a change of Eval or Step, shown by
#                               argument, not run): each listed, each refutation's theorem found
set -u
K=$(cd "$(dirname "$0")/.." && pwd); cd "$K"
exec python3 -I - "$K" "$@" <<'PY'
import os, re, shutil, subprocess, sys, tomllib

K = sys.argv[1]
args = sys.argv[2:]
keep = "--keep" in args
listing = "--list" in args
names = [a for a in args if not a.startswith("--")]
CAP = ["systemd-run", "--user", "--scope", "-q", "-p", "MemoryMax=12G", "-p", "MemorySwapMax=0"]
READER = re.compile(r"KcoreSpec/(Parse[A-Za-z]*|Account|ReadFns|Kore/Read)\.lean$")
DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*"
                  r"(theorem|lemma|def|abbrev|example|instance|structure|inductive|kernel_rfl|[a-z_]+_of|kore_term|user_axioms)\b\s*(\S*)")

ms = tomllib.load(open(os.environ.get("KCORE_MUTANTS") or os.path.join(K, "test/constructs/mutants.toml"), "rb")).get("mutant", {})
rows = tomllib.load(open(os.path.join(K, "test/constructs/rows.toml"), "rb"))
if "--kernel" in args:
    # the kernel mutants: listed, and each refutation's file checked to hold its theorem
    ks = tomllib.load(open(os.environ.get("KCORE_MUTANTS") or os.path.join(K, "test/constructs/mutants.toml"), "rb")).get("kernel", {})
    bad = 0
    for n, m in ks.items():
        print(f"{n}: {m.get('summary', '')}")
        print(f"  at: {m.get('at', '')}")
        refs = m.get("refutation", [])
        if not refs or not m.get("argument") or not m.get("breaks") or not m.get("at"):
            print("  error: an entry names its refutation, at, breaks and argument"); bad += 1
        for ref in refs:
            f, _, d = ref.partition(": ")
            fp = os.path.join(K, f)
            ok = os.path.isfile(fp) and re.search(rf"^(?:private )?theorem {re.escape(d.split('.')[-1])}\b", open(fp, encoding="utf-8").read(), re.M)
            print(f"  {'refuted by' if ok else 'error: no theorem'} {d} ({f})")
            bad += 0 if ok else 1
    print(f"mutants: {len(ks)} kernel mutants listed, " + ("each refutation found" if not bad else f"{bad} errors"))
    sys.exit(1 if bad else 0)
if listing:
    for n, m in ms.items():
        print(f"{n}: {m.get('summary', '')} (row {m.get('row')}; fixture {m.get('fixture')}; expect {m.get('expect')})")
    sys.exit(0)
for n in names:
    if n not in ms:
        sys.exit(f"mutants: no mutant {n} in test/constructs/mutants.toml")
todo = names or list(ms)


def env1():
    e = dict(os.environ)
    e["LEAN_NUM_THREADS"] = "1"
    return e


def run(cmd, cwd, timeout, env=None):
    return subprocess.run(CAP + ["timeout", str(timeout)] + cmd, cwd=cwd, capture_output=True, text=True, env=env or env1())


def scratch_copy(name):
    root = os.path.join(K, ".lake/mutants", name)
    shutil.rmtree(root, ignore_errors=True)
    spec = os.path.join(root, "kcore/kcore-spec")
    shutil.copytree(K, spec, symlinks=True, ignore=lambda d, fs: [f for f in fs if f == ".lake"])
    shutil.copytree(os.path.join(K, ".lake/build"), os.path.join(spec, ".lake/build"), symlinks=True)
    for sib in ("aml-port", "kore-lean"):
        os.symlink(os.path.realpath(os.path.join(K, "..", sib)), os.path.join(root, "kcore", sib))
    # `--old` rebuilds a module whose source is newer than its build: the tree's build is current
    # (checked below), so every source is dated before every artifact, and only what the patch
    # writes is newer
    for d, _, fs in os.walk(spec):
        if "/.lake" in d[len(spec):] or d[len(spec):].startswith("/.lake"):
            continue
        for f in fs:
            fp = os.path.join(d, f)
            if not os.path.islink(fp):
                os.utime(fp, (946684800, 946684800))
    return root, spec


def decl_at(lines, ln):
    """The declaration (or command) of the source line ln (1-based): the last one starting at or above it."""
    for i in range(min(ln, len(lines)) - 1, -1, -1):
        m = DECL.match(lines[i])
        if m and not lines[i].startswith((" ", "\t")):
            return f"{m.group(1)} {m.group(2)}".strip()
    return f"line {ln}"


def check_row(ref):
    m = re.match(r"(\S+) (.+)$", ref or "")
    return bool(m) and m.group(2) in rows.get(m.group(1), {})


nb = subprocess.run(["lake", "build", "--no-build", "kcore"], cwd=K, capture_output=True, text=True)
if nb.returncode:
    sys.exit("mutants: this tree's build is not current (`lake build --no-build kcore` fails): run test/lake-par.py and `lake build kcore` first")


def parallel(todo):
    """--par: each mutant run by its own `test/mutants.sh NAME` (its own scratch copy), several at
    once. A run is started only when MemAvailable leaves RESERVE GiB free beyond the expected peak of
    every run already started and of the new one: a run's peak is its build (about 2 GiB) or, when
    the mutant names a theorem module, that module's recorded peak (test/lake-par.py's table), the
    whole peak charged for as long as the run lasts. The outputs are printed as the runs end."""
    import json, time
    reserve = float(os.environ.get("KCORE_RESERVE_GIB", "16"))
    cap = int(os.environ.get("KCORE_JOBS", "0")) or os.cpu_count()
    try:
        peaks = json.load(open(os.path.expanduser("~/.cache/kcore-lake-peaks.json")))
    except Exception:
        peaks = {}

    def est(n):
        t = ms[n].get("theorems")
        return max(2.5, min(12.0, peaks.get(t, 9.0) * 1.15)) if t else 2.5

    def avail():
        for l in open("/proc/meminfo"):
            if l.startswith("MemAvailable:"):
                return int(l.split()[1]) / 1048576
        return 0.0
    # the heaviest first, so that the light runs fill the room the heavy ones leave
    queue = sorted(todo, key=lambda n: -est(n))
    running, outs, nbad = {}, {}, 0
    while queue or running:
        for n, p in list(running.items()):
            if p.poll() is not None:
                o = open(outs[n]).read(); os.unlink(outs[n])
                print(o.rstrip("\n").split("\nmutants: ")[0], flush=True)
                nbad += 1 if p.returncode else 0
                del running[n]
        started = False
        if queue and len(running) < cap and (not running or
                avail() - sum(est(n) for n in running) - est(queue[0]) >= reserve):
            n = queue.pop(0)
            outs[n] = os.path.join(K, ".lake", f"mutants-{n}.out")
            running[n] = subprocess.Popen(["bash", os.path.join(K, "test/mutants.sh")] + (["--keep"] if keep else []) + [n],
                                          stdout=open(outs[n], "w"), stderr=subprocess.STDOUT)
            started = True
        # a run reaches its build's size within seconds: the next one is weighed against it
        time.sleep(15 if started else 5)
    print(f"mutants: {len(todo)} run, " + ("each as expected" if not nbad else f"{nbad} not as expected or in error"))
    return 1 if nbad else 0


if "--par" in args and len(todo) > 1:
    sys.exit(parallel(todo))
bad = 0
for name in todo:
    m = ms[name]
    expect = m.get("expect")
    print(f"{name}: {m.get('summary', '')}")
    if not check_row(m.get("row")):
        print(f"  error: row {m.get('row')!r} is no entry of rows.toml"); bad += 1; continue
    if expect not in ("killed", "survives") or (expect == "survives" and not m.get("why")):
        print(f"  error: expect {expect!r} (killed, or survives with why)"); bad += 1; continue
    patch = m.get("patch", "")
    files = re.findall(r"^\+\+\+ b/(\S+)", patch, re.M)
    if not files or any(not READER.search(f) for f in files):
        print(f"  error: the patch changes {files}, not the reader's files only"); bad += 1; continue
    fx, thm = m.get("fixture"), m.get("theorems")
    root, spec = scratch_copy(name)
    try:
        p = subprocess.run(["patch", "-p1", "--forward", "--no-backup-if-mismatch", "-r", "-"], cwd=spec,
                           input=patch.lstrip("\n"), capture_output=True, text=True)
        if p.returncode:
            print(f"  error: the patch does not apply: {(p.stdout + p.stderr).strip()[:400]}"); bad += 1; continue
        b = run(["lake", "build", "--old", "kcore"], spec, 3600)
        if b.returncode:
            print(f"  error: the mutant does not build: {(b.stdout + b.stderr).strip()[-800:]}"); bad += 1; continue
        mk = os.path.join(spec, ".lake/build/bin/kcore")
        # 3. the account of the row's fixture by the mutant
        if os.path.isdir(os.path.join(K, "test/constructs/fixtures", fx)):
            e = env1(); e["KCORE_BIN"] = mk
            a = subprocess.run(["python3", "-I", "test/constructs/kfix.py", "accounts", fx], cwd=K,
                               capture_output=True, text=True, env=e)
            detail = (a.stdout + a.stderr).strip().splitlines()
            sm = re.search(r"kfix accounts: (\d+) equal, (\d+) differ(?:: [^,]*)?, (\d+) not in the cache", a.stdout)
            if not sm or sm.group(3) != "0" or int(sm.group(1)) + int(sm.group(2)) != 1:
                print(f"  error: kfix.py accounts {fx} did not compare the fixture's account: {' '.join(detail[-2:])[:400]}")
                bad += 1; continue
            changed = sm.group(2) != "0"
        else:
            text = os.path.join(K, fx)
            mine = run([os.path.join(K, ".lake/build/bin/kcore"), "account", text], K, 600)
            theirs = run([mk, "account", text], K, 600)
            ml, tl = mine.stdout.splitlines(), theirs.stdout.splitlines()
            changed = ml != tl or mine.returncode != theirs.returncode
            detail = [f"- {l}" for l in ml if l not in tl][:5] + [f"+ {l}" for l in tl if l not in ml][:5]
        if changed:
            outcome = "killed by account"
            print(f"  {outcome}")
            for l in detail[:10]:
                print(f"    {l}")
        elif not thm:
            outcome = "survives"
            print(f"  survives: the account of {fx} is unchanged, and the mutant names no theorem module")
        else:
            t = run(["lake", "env", "lean", "-j1", thm], spec, 1800)
            if t.returncode == 0:
                outcome = "survives"
                print(f"  survives: the account of {fx} is unchanged and {thm} checks")
            else:
                src = open(os.path.join(spec, thm), encoding="utf-8").read().splitlines()
                errs = re.findall(rf"^{re.escape(thm)}:(\d+):\d+: error", t.stdout + t.stderr, re.M)
                decls = []
                for ln in errs:
                    d = decl_at(src, int(ln))
                    if d not in decls:
                        decls.append(d)
                if not decls:
                    print(f"  error: {thm} fails with no error at a line (rc {t.returncode}): {(t.stdout + t.stderr).strip()[-400:]}")
                    bad += 1; continue
                outcome = "killed by theorems"
                print(f"  killed by theorems: the account of {fx} is unchanged; {thm} fails at {len(errs)} errors: {', '.join(decls)}")
                first = re.search(rf"^{re.escape(thm)}:\d+:\d+: error.*$", t.stdout + t.stderr, re.M)
                if first:
                    print(f"    {first.group(0)[:300]}")
        if (outcome != "survives") != (expect == "killed"):
            print(f"  not as expected ({expect})"); bad += 1
    finally:
        if not keep:
            shutil.rmtree(root, ignore_errors=True)
print(f"mutants: {len(todo)} run, " + ("each as expected" if not bad else f"{bad} not as expected or in error"))
sys.exit(1 if bad else 0)
PY
