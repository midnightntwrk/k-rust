#!/usr/bin/env python3
"""Conformance driver: K regression-new cases through the pinned reference toolchain and krust.

For every leaf case (a directory whose Makefile includes ktest.mak or ktest-fail.mak, expanding
ktest-group.mak SUBDIRS recursively) the driver:
  1. copies the case tree to a scratch directory (never writes into k/),
  2. asks GNU make for the exact reference recipes (`make -n all` with K_BIN pointed at k/result/bin),
  3. runs the reference kompile recipe(s) verbatim (and every recipe of a ktest-fail case, which are
     self-checking against their .out), skipping reference test runs whose checked-in .out exists,
  4. runs the krust equivalent of each recipe, converts krust's KORE output to K surface syntax with
     the reference `kprint` against the reference-kompiled definition, and diffs against the .out,
  5. on a mismatch re-runs the reference recipe verbatim to confirm the .out is still the oracle.
Results go to the requested results.toml (rewritten after every case) and per-case logs directory.
"""
import argparse, json, math, os, re, shlex, shutil, subprocess, sys, threading, time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import tomllib

HERE = Path(__file__).resolve().parent
KR = str(HERE.parents[1])
K_CHECKOUT = os.environ.get("K_CHECKOUT", f"{KR}/k")
KBIN = os.path.dirname(os.environ["K_KOMPILE"]) if os.environ.get("K_KOMPILE") else f"{K_CHECKOUT}/result/bin"
BUILTIN = f"{K_CHECKOUT}/k-distribution/include/kframework/builtin"
KRUST = os.environ.get("CONFORMANCE_KRUST", f"{KR}/target/release/krust")
SRC_TREE = f"{K_CHECKOUT}/k-distribution"
WORK_TREE = "/tmp/k-rust-conformance/k-distribution"
REG = "tests/regression-new"
LOGS = "/tmp/k-rust-conformance/logs"
RESULTS = "/tmp/k-rust-conformance/results.toml"
K_OPTS = os.environ.get("REFERENCE_DIFFERENTIAL_K_OPTS", "")
KORE_PARSER = os.environ.get("K_KORE_PARSER", f"{KBIN}/kore-parser")
TEST_BINARY = os.environ.get("CONFORMANCE_TEST_BINARY")
EXPECTATIONS = str(HERE / "expectations.toml")
IGNORE_UNIQUE_ID = False
CASE_BUDGET = 300.0
CASE_BUDGETS = {}
DIFF_LINES = 20

TOOLS = {"kompile", "krun", "kast", "kprove", "kparse", "kdep", "kore-print", "k-rule-find", "llvm-krun", "kprint", "kserver"}
KOMPILE_VALUE_OPTS = {"--backend", "--main-module", "--syntax-module", "--output-definition", "--md-selector", "-I",
    "--hook-namespaces", "--type-inference-mode", "--post-process", "--top-cell", "--profile-rule-parsing",
    "--bison-stack-max-depth", "--llvm-kompile-type", "--llvm-kompile-output", "-ccopt", "-w", "-W", "-Wno",
    "--warnings", "-d", "--directory", "--definition", "-O", "--concrete-rules", "--smt-prelude", "--llvm-kompile-flags"}
KRUN_VALUE_OPTS = {"--definition", "-d", "--depth", "--bound", "--pattern", "--parser", "--output", "-o", "--output-file",
    "-c", "-p", "--io", "--smt", "--smt-prelude", "--smt-timeout", "--term", "--search-pattern", "--md-selector", "-I", "--warnings", "-w"}
KAST_VALUE_OPTS = {"--definition", "-d", "--sort", "-s", "--module", "-m", "--input", "-i", "--output", "-o", "--output-file",
    "--expression", "-e", "--md-selector", "-I", "--warnings", "-w", "--gen-parser-only"}
KPROVE_VALUE_OPTS = {"--definition", "-d", "--spec-module", "--def-module", "--md-selector", "--smt", "--smt-prelude",
    "--smt-timeout", "--branching-allowing", "--branching-allowed", "--depth", "--claim", "--claims", "--exclude",
    "--trusted", "--debug-script", "--profile-rule-parsing", "--warnings", "-w", "--type-inference-mode", "-I",
    "--max-counterexamples", "--output", "-o", "--output-file", "--save-directory", "--haskell-backend-command",
    "--kore-exec-command", "--log-level"}

lock = threading.Lock()


def reference_default_k_opts(workspace):
    """Read N20's one JVM-options authority without duplicating the option string."""
    guard = os.path.join(workspace, "scripts", "reference-memory-guard.sh")
    completed = subprocess.run(
        [
            "bash",
            "-c",
            'source "$1"; printf "%s" "$reference_default_k_opts"',
            "conformance-k-opts",
            guard,
        ],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    if completed.returncode != 0 or not completed.stdout:
        raise RuntimeError(
            f"could not read reference_default_k_opts from {guard}: {completed.stderr.strip()}"
        )
    return completed.stdout


def load_expectations(path):
    with open(path, "rb") as source:
        document = tomllib.load(source)
    rows = document.get("case", [])
    budgets = {
        row["name"]: float(row["budget"])
        for row in rows
        if "budget" in row
    }
    return document, budgets


def load_reference_normalisations(workspace, k_checkout):
    """Read the manifest through its renderer, which owns placeholder expansion."""
    renderer = os.path.join(workspace, "scripts", "reference-manifest.py")
    environment = dict(os.environ)
    environment.update(WORKSPACE=workspace, K_CHECKOUT=k_checkout)
    completed = subprocess.run(
        [sys.executable, renderer],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        env=environment,
    )
    if completed.returncode != 0:
        raise RuntimeError(
            f"could not read reference normalisations through {renderer}: "
            f"{completed.stderr.strip()}"
        )
    try:
        manifest = json.loads(completed.stdout)
    except json.JSONDecodeError as error:
        raise RuntimeError(f"invalid manifest JSON from {renderer}: {error}") from error
    return manifest.get("normalisations", {})


def sh(cmd, cwd, timeout, stdin_path=None, env=None, shell=False):
    """Run a command, return (rc, stdout, stderr, seconds, timed_out)."""
    e = dict(os.environ); e["K_OPTS"] = K_OPTS
    if env: e.update(env)
    stdin = open(stdin_path, "rb") if stdin_path and os.path.exists(stdin_path) else subprocess.DEVNULL
    t0 = time.monotonic()
    try:
        p = subprocess.Popen(cmd, cwd=cwd, stdin=stdin, stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=e,
                             shell=shell, start_new_session=True)
        try:
            out, err = p.communicate(timeout=max(1.0, timeout))
            to = False
        except subprocess.TimeoutExpired:
            os.killpg(p.pid, 9); out, err = p.communicate(); to = True
        rc = p.returncode
    except FileNotFoundError as ex:
        rc, out, err, to = 127, b"", str(ex).encode(), False
    finally:
        if stdin is not subprocess.DEVNULL: stdin.close()
    return rc, out.decode("utf-8", "replace"), err.decode("utf-8", "replace"), time.monotonic() - t0, to


def first_diff(expected, actual, n=DIFF_LINES):
    import difflib
    a = [l.rstrip() for l in expected.splitlines()]
    b = [l.rstrip() for l in actual.splitlines()]
    if a == b: return None
    d = list(difflib.unified_diff(a, b, "expected", "krust", lineterm="", n=1))
    return "\n".join(d[:n]) + ("\n..." if len(d) > n else "")


def split_surface_disjunction(text):
    """Return sorted kprint #Or branches, or None when text is not a disjunction."""
    lines = text.splitlines()
    if not any(line.rstrip() == "#Or" and not line.startswith((" ", "\t")) for line in lines):
        return None
    branches = []
    current = []
    for line in lines:
        if line.rstrip() == "#Or" and not line.startswith((" ", "\t")):
            branches.append("\n".join(current).strip("\n"))
            current = []
            continue
        current.append((line[2:] if line.startswith("  ") else line).rstrip())
    branches.append("\n".join(current).strip("\n"))
    return sorted(branches)


def execution_text_diff(expected, actual):
    expected_disjuncts = split_surface_disjunction(expected)
    actual_disjuncts = split_surface_disjunction(actual)
    if expected_disjuncts is None and actual_disjuncts is None:
        return first_diff(expected, actual), False
    expected_disjuncts = expected_disjuncts or [expected.rstrip()]
    actual_disjuncts = actual_disjuncts or [actual.rstrip()]
    expected_sorted = "\n#Or\n".join(sorted(expected_disjuncts))
    actual_sorted = "\n#Or\n".join(sorted(actual_disjuncts))
    return first_diff(expected_sorted, actual_sorted), True


def toml_str(s):
    return json.dumps(s, ensure_ascii=False)


def toml_ml(s):
    s = "".join(ch if ch in "\n\t" or ord(ch) >= 32 else "?" for ch in s)
    return '"""\n' + s.replace("\\", "\\\\").replace('"""', '\\"\\"\\"') + '\n"""'


class Case:
    def __init__(self, rel):
        self.rel = rel
        self.name = rel
        self.src = f"{SRC_TREE}/{REG}/{rel}"
        self.dir = f"{WORK_TREE}/{REG}/{rel}"
        self.log = f"{LOGS}/{rel.replace('/', '__')}"
        self.steps = []
        self.notes = []
        self.kind = "unknown"
        self.backend = "llvm"
        self.vars = {}
        self.t0 = time.monotonic()
        self.budget = CASE_BUDGETS.get(rel, CASE_BUDGET)
        self.deadline = self.t0 + self.budget
        self.ref_kompiled = None
        self.main_module = None
        self.syntax_module = None
        self.pgm_sort = None
        self.config_sorts = {}
        self.def_file = None
        self.custom_targets = []

    def remaining(self):
        return self.deadline - time.monotonic()

    def out_of_budget(self):
        return self.remaining() <= 1

    def note(self, s):
        self.notes.append(s)

    def logfile(self, name, text):
        os.makedirs(self.log, exist_ok=True)
        with open(f"{self.log}/{name}", "w") as f: f.write(text)


def enumerate_cases(rel=""):
    d = f"{SRC_TREE}/{REG}/{rel}" if rel else f"{SRC_TREE}/{REG}"
    mk = f"{d}/Makefile"
    if not os.path.exists(mk):
        return [(rel, "no-makefile")]
    text = open(mk).read()
    if "ktest-group.mak" in text or (rel == ""):
        m = re.search(r"^SUBDIRS\s*=\s*(.*)$", text, re.M)
        subs = []
        if m and "$(" not in m.group(1):
            subs = m.group(1).split()
        else:
            subs = sorted(x for x in os.listdir(d) if os.path.isdir(f"{d}/{x}"))
        out = []
        for s in subs:
            sub = f"{rel}/{s}" if rel else s
            if os.path.isdir(f"{SRC_TREE}/{REG}/{sub}"):
                out += enumerate_cases(sub)
        return out
    if "ktest-fail.mak" in text: return [(rel, "fail")]
    if "ktest-kdep.mak" in text: return [(rel, "kdep")]
    if "ktest.mak" in text: return [(rel, "ktest")]
    return [(rel, "custom")]


def make_vars(case):
    rc, out, err, _, _ = sh(["make", "-pn", "clean", f"K_BIN={KBIN}", f"BUILTIN_DIR={BUILTIN}", "KDEP=true"], case.dir, 60)
    v = {}
    for m in re.finditer(r"^([A-Z_0-9]+) :?= (.*)$", out, re.M):
        v[m.group(1)] = m.group(2)
    return v


def make_recipes(case):
    rc, out, err, secs, to = sh(["make", "-n", "all", f"K_BIN={KBIN}", f"BUILTIN_DIR={BUILTIN}", "KDEP=true"], case.dir, 120)
    lines = [l for l in out.splitlines() if l.strip() and not l.startswith("make")]
    case.logfile("make-n.txt", out + "\n--- stderr ---\n" + err)
    return rc, lines, err


def split_recipe(line):
    """Return dict(tool, args, out, stdin, discard, raw, tokens) or None for lines without a K tool."""
    try:
        toks = shlex.split(line)
    except ValueError:
        toks = line.split()
    tool_i = None
    for i, t in enumerate(toks):
        if t.startswith(KBIN + "/") and os.path.basename(t) in TOOLS:
            tool_i = i; break
    if tool_i is None:
        return None
    stops = {"|", "2>&1", ">", "&&", "||", ";", "1>/dev/null", "2>/dev/null"}
    args = []
    for t in toks[tool_i + 1:]:
        if t in stops: break
        args.append(t)
    out = None; actual_file = None
    for j, t in enumerate(toks):
        if t == "diff" and j + 1 < len(toks):
            if toks[j + 1] == "-" and j + 2 < len(toks): out = toks[j + 2]
            elif j + 2 < len(toks) and toks[j + 2] != "-": out = toks[j + 1]; actual_file = toks[j + 2]
            else: out = toks[j + 1]
    m = re.search(r"cat (\S+\.in) 2>/dev/null", line)
    stdin = m.group(1) if m else None
    discard = "1>/dev/null" in line
    filters = " | sed" in line
    return dict(tool=os.path.basename(toks[tool_i]), args=args, out=out, actual_file=actual_file, stdin=stdin,
                discard=discard, filters=filters, raw=line)


def parse_opts(args, value_opts):
    """Split args into (positionals, opts dict(list), flags list)."""
    pos, opts, flags = [], {}, []
    i = 0
    while i < len(args):
        a = args[i]
        if a.startswith("-"):
            if "=" in a and a.startswith("--"):
                k, v = a.split("=", 1); opts.setdefault(k, []).append(v); i += 1; continue
            if a in value_opts and i + 1 < len(args):
                opts.setdefault(a, []).append(args[i + 1]); i += 2; continue
            if a.startswith("-c") and not a.startswith("--") and len(a) > 2:
                opts.setdefault("-c", []).append(a[2:]); i += 1; continue
            if a.startswith("-p") and not a.startswith("--") and len(a) > 2:
                opts.setdefault("-p", []).append(a[2:]); i += 1; continue
            if a.startswith("-I") and len(a) > 2:
                opts.setdefault("-I", []).append(a[2:]); i += 1; continue
            flags.append(a); i += 1
        else:
            pos.append(a); i += 1
    return pos, opts, flags


def read_kompiled(case, kompiled):
    try:
        case.main_module = open(f"{kompiled}/mainModule.txt").read().strip()
        case.syntax_module = open(f"{kompiled}/mainSyntaxModule.txt").read().strip()
        cv = open(f"{kompiled}/configVars.sh").read()
        for m in re.finditer(r"declaredConfigVar_(\w+)='([^']*)'", cv):
            case.config_sorts[m.group(1)] = m.group(2)
        case.pgm_sort = case.config_sorts.get("PGM")
        case.ref_kompiled = kompiled
    except OSError as ex:
        case.note(f"could not read reference kompiled metadata: {ex}")


def guess_modules(case, src, main):
    text = open(f"{case.dir}/{src}", errors="replace").read() if os.path.exists(f"{case.dir}/{src}") else ""
    mods = re.findall(r"^\s*module\s+([A-Z][A-Z0-9-]*)", text, re.M)
    if not main:
        main = os.path.basename(src).rsplit(".", 1)[0].upper()
    syn = f"{main}-SYNTAX" if f"{main}-SYNTAX" in mods else main
    m = re.search(r"\$PGM:([A-Za-z][A-Za-z0-9]*)", text)
    return main, syn, (m.group(1) if m else "KItem")


def classify_error(err):
    e = err.lower()
    if re.search(r"could not parse (program|input|rule|claim|context|configuration|sentence|term)|has \d+ parses|ambigu|could not infer|inference|sort inference", e): return "inner-parse"
    if re.search(r"outer|unexpected (token|character|end)|unterminated|imports missing|missing module|unknown module|duplicate module|could not (read|load|find) (file|module)|failed to extract k code|no such file|requires", e): return "outer-parse"
    return "kompile"


def reference_message_class(text):
    match = re.search(r"\[Error\]\s+([^:\n]+):", text)
    if not match:
        return ""
    heading = match.group(1).strip().lower()
    for name in ("outer", "inner", "compiler", "prover", "critical"):
        if name in heading:
            return name
    return "other"


def krust_message_class(text):
    if not text.strip():
        return ""
    classified = reference_message_class(text)
    if classified:
        return classified
    lowered = text.lower()
    if re.search(r"proof|prover|claim", lowered):
        return "prover"
    if re.search(r"has excluded attribute|not defined|duplicate", lowered):
        return "compiler"
    return {
        "outer-parse": "outer",
        "inner-parse": "inner",
        "kompile": "compiler",
    }[classify_error(text)]


def postprocess(path):
    """Re-read results.toml, reclassify error stages from the recorded text, trim long lines, recompute case fields."""
    import tomllib
    data = tomllib.load(open(path, "rb"))
    cases = []
    for d in data.get("case", []):
        c = Case(d["name"]); c.kind = d["kind"]; c.backend = d["backend"]; c.notes = d.get("notes", []); c.custom_targets = d.get("undriven_recipes", [])
        c.main_module = d.get("main_module"); c.syntax_module = d.get("syntax_module"); c.pgm_sort = d.get("pgm_sort"); c.seconds = d.get("seconds", 0)
        c.steps = [dict(s) for s in d.get("step", [])]
        for s in c.steps:
            for k in ("divergence", "fallback_divergence", "oracle_output"):
                if k in s: s[k] = "\n".join(l[:300] for l in s[k].splitlines()[:DIFF_LINES])
            if s.get("verdict") == "krust-error" and s.get("divergence") and "timed out" not in (s.get("reason") or ""):
                s["stage"] = classify_error(s["divergence"])
            if s.get("fallback_verdict") == "krust-error" and s.get("fallback_divergence"):
                s["fallback_stage"] = classify_error(s["fallback_divergence"])
            if s.get("step") == "kprove" and "krust_rc" in s and s.get("out") and s.get("test"):
                outp = f"{WORK_TREE}/{REG}/{c.name}/{s['out']}"; logp = f"{c.log}/{os.path.basename(s['test'])}.krust.log"
                if os.path.exists(outp) and os.path.exists(logp):
                    expected = open(outp, errors="replace").read(); lg = open(logp, errors="replace").read()
                    kout, _, kerr = lg.partition("\n--- stderr ---\n")
                    exp, got, v, note, claims = kprove_verdicts(expected, kout, kerr, s["krust_rc"])
                    old_v = s.get("verdict")
                    s["expected_verdict"] = exp; s["krust_verdict"] = got
                    s["stage"] = "kprove" if (claims or got == "not-proven") else classify_error(kerr)
                    s["comparison"] = "verdict-only (proven / not-proven / error; counterexample and message text not compared)"
                    if old_v == "reference-error" and v != "match": pass  # keep the stale-oracle verdict
                    elif old_v == "reference-error" and v == "match": s["verdict"] = "match"; s["reason"] = note + " (oracle re-run differed only in log lines; see oracle_output)"
                    else: s["verdict"] = v; s["reason"] = note
                    if v == "match": s.pop("divergence", None)
        if d["verdict"] == "skipped-with-reason" and not c.steps:
            finish(c, d["verdict"], d.get("reason"))
        else:
            finish(c)
        c.seconds = d.get("seconds", 0)
        cases.append(c)
    write_results(cases, path)
    print(f"postprocessed {len(cases)} cases -> {path}")


def run_test_binary(name, env, cwd):
    """Run one ignored comparison test of crates/k-rust/tests/reference_differential.rs directly."""
    binary = TEST_BINARY
    if not binary:
        dependency_dir = os.path.join(KR, "target", "debug", "deps")
        if not os.path.isdir(dependency_dir):
            return 1, "", f"no reference_differential test binary directory: {dependency_dir}"
        bins = sorted((os.path.getmtime(path), path) for path in
                      (os.path.join(dependency_dir, entry) for entry in os.listdir(dependency_dir)
                       if entry.startswith("reference_differential-") and not entry.endswith(".d"))
                      if os.access(path, os.X_OK))
        if not bins:
            return 1, "", "no reference_differential test binary in target/debug/deps"
        binary = bins[-1][1]
    rc, out, err, _, _ = sh(
        [binary, "--ignored", "--exact", name, "--nocapture", "--test-threads=1"],
        cwd,
        120,
        env=env,
    )
    return rc, out, err


def kprint(case, kore_path):
    rc, out, err, _, _ = sh([f"{KBIN}/kprint", case.ref_kompiled, kore_path, "false"], case.dir, 60)
    return rc, out, err


def step_record(case, **kw):
    kw.setdefault("verdict", "skipped-with-reason")
    case.steps.append(kw)
    return kw


def krust_kompile_args(case, rec, force_syntax_module=False):
    pos, opts, flags = parse_opts(rec["args"], KOMPILE_VALUE_OPTS)
    src = next((p for p in pos if re.search(r"\.(k|md|json)$", p)), None)
    if src is None:
        return None, "no source file in kompile recipe", None
    backend = (opts.get("--backend") or ["llvm"])[-1]
    main = (opts.get("--main-module") or [None])[-1]
    syn = (opts.get("--syntax-module") or [None])[-1]
    gm, gs, gp = guess_modules(case, src, main)
    main = main or gm
    args = [KRUST, "kcompile", src, "--main-module", main, "--backend", "llvm" if backend == "llvm" else "rust",
            "--output-directory", "krust-kompiled", "-I", ".", "--builtin-directory", BUILTIN]
    if syn or force_syntax_module:
        args += ["--syntax-module", syn or gs]
    for s in opts.get("--md-selector", []): args += ["--md-selector", s]
    for d in opts.get("-I", []): args += ["-I", d]
    if "--no-prelude" in flags: args.append("--no-prelude")
    if "--emit-json" in flags: args.append("--emit-json")
    dropped = [f for f in flags if f not in ("--no-prelude", "--emit-json", "--no-exc-wrap")]
    inference_mode = (opts.get("--type-inference-mode") or [None])[-1]
    for k in opts:
        if k not in ("--backend", "--main-module", "--syntax-module", "--output-definition", "--md-selector", "-I", "--type-inference-mode"):
            dropped.append(f"{k} {' '.join(opts[k])}")
    if inference_mode not in (None, "simplesub", "checked"):
        dropped.append(f"--type-inference-mode {inference_mode}")
    if src.endswith(".json"): return None, "--outer-parsed-json input has no krust equivalent", None
    info = dict(src=src, backend=backend, main=main, syn=syn or gs, dropped=dropped,
                inference_mode=inference_mode)
    return args, None, info


def do_kompile(case, rec, expect_fail):
    """Reference kompile (verbatim recipe) + krust kcompile + KORE comparison."""
    step = dict(step="kompile", ref_cmd=rec["raw"], out=rec["out"])
    rc, out, err, secs, to = sh(["bash", "-c", rec["raw"]], case.dir, case.remaining())
    case.logfile("kompile.ref.log", out + "\n--- stderr ---\n" + err)
    step["ref_rc"] = rc; step["ref_seconds"] = round(secs, 1)
    if to:
        step.update(verdict="reference-error", reason="reference kompile timed out"); return step_record(case, **step)
    pos, opts, flags = parse_opts(rec["args"], KOMPILE_VALUE_OPTS)
    kompiled = (opts.get("--output-definition") or [None])[-1]
    if not expect_fail:
        if rc != 0:
            step.update(verdict="reference-error", reason=f"reference kompile exit {rc}", divergence=(out + err)[-1500:])
            return step_record(case, **step)
        if kompiled and os.path.isdir(f"{case.dir}/{kompiled}"): read_kompiled(case, f"{case.dir}/{kompiled}")
    args, why, info = krust_kompile_args(case, rec, force_syntax_module=expect_fail)
    if args is None:
        step.update(verdict="krust-unsupported", reason=why); return step_record(case, **step)
    krust_env = ({"KRUST_TYPE_INFERENCE_MODE": "checked"}
                 if info["inference_mode"] == "checked" else None)
    env_prefix = "KRUST_TYPE_INFERENCE_MODE=checked " if krust_env else ""
    step["krust_cmd"] = env_prefix + " ".join(shlex.quote(a) for a in args)
    if info["dropped"]: step["dropped_flags"] = info["dropped"]
    if os.path.exists(f"{case.dir}/krust-kompiled"): shutil.rmtree(f"{case.dir}/krust-kompiled")
    krc, kout, kerr, ksecs, kto = sh(args, case.dir, case.remaining(), env=krust_env)
    case.logfile("kompile.krust.log", kout + "\n--- stderr ---\n" + kerr)
    step["krust_rc"] = krc; step["krust_seconds"] = round(ksecs, 1)
    if kto:
        step.update(verdict="krust-error", stage="kompile", reason="krust kcompile timed out"); return step_record(case, **step)
    if expect_fail:
        expected = open(f"{case.dir}/{rec['out']}", errors="replace").read() if rec["out"] and os.path.exists(f"{case.dir}/{rec['out']}") else ""
        ref_rejects = "[Error]" in expected or rc != 0
        step["oracle_confirmed"] = (rc == 0)
        step["expected_first_lines"] = "\n".join(expected.splitlines()[:6])
        step["krust_first_lines"] = "\n".join((kerr or kout).splitlines()[:6])
        step["message_class_expected"] = reference_message_class(expected or err)
        step["message_class_krust"] = krust_message_class(kerr or kout) if krc != 0 else ""
        step["message_class_match"] = (
            step["message_class_expected"] == step["message_class_krust"]
        )
        if krc != 0:
            step["stage"] = classify_error(kerr)
            step.update(verdict="match" if ref_rejects else "mismatch", reason=("both reject (message class reported separately)" if ref_rejects else "krust rejects a definition the reference accepts"))
        else:
            step["stage"] = "kompile"
            step.update(verdict="mismatch" if ref_rejects else "match", reason=("krust accepts a definition the reference rejects" if ref_rejects else "both accept"))
        if not ref_rejects and rc != 0: step["reason"] += "; reference recipe diff failed"
        return step_record(case, **step)
    if krc != 0:
        step.update(verdict="krust-error", stage=classify_error(kerr), divergence=(kerr or kout)[-1500:])
        return step_record(case, **step)
    step["stage"] = "kompile"
    ref_kore = f"{case.dir}/{kompiled}/definition.kore" if kompiled else None
    rust_kore = f"{case.dir}/krust-kompiled/definition.kore"
    if ref_kore and os.path.exists(ref_kore) and os.path.exists(rust_kore):
        vrc, vout, verr, vsecs, vto = sh(
            [KORE_PARSER, ref_kore], case.dir, case.remaining(), env={"GHCRTS": ""}
        )
        case.logfile("kompile.reference-verify.log", vout + "\n--- stderr ---\n" + verr)
        step["reference_verify_rc"] = vrc
        step["reference_verify_seconds"] = round(vsecs, 1)
        if vto or vrc != 0:
            step.update(
                verdict="reference-error",
                reason="reference definition.kore rejected by kore-parser --verify",
                verification="kore-parser --verify",
                divergence="\n".join((verr or vout).splitlines()[:DIFF_LINES]),
            )
            return step_record(case, **step)
        vrc, vout, verr, vsecs, vto = sh(
            [KORE_PARSER, rust_kore], case.dir, case.remaining(), env={"GHCRTS": ""}
        )
        case.logfile("kompile.krust-verify.log", vout + "\n--- stderr ---\n" + verr)
        step["krust_verify_rc"] = vrc
        step["krust_verify_seconds"] = round(vsecs, 1)
        step["verification"] = "kore-parser --verify"
        if vto or vrc != 0:
            step.update(
                verdict="mismatch",
                reason="krust definition.kore rejected by kore-parser --verify",
                divergence="\n".join((verr or vout).splitlines()[:DIFF_LINES]),
            )
            return step_record(case, **step)
        comparison_environment = {
            "K_REFERENCE_KORE": ref_kore,
            "K_RUST_KORE": rust_kore,
        }
        if IGNORE_UNIQUE_ID:
            comparison_environment["K_DIFFERENTIAL_IGNORE_UNIQUE_ID"] = "1"
        trc, tout, terr = run_test_binary("emitted_kore_matches_the_reference_frontend",
                                          comparison_environment, case.dir)
        case.logfile("kompile.kore-compare.log", tout + "\n--- stderr ---\n" + terr)
        unique_id = re.search(r"^unique-id divergences: ([0-9]+)$", tout, re.M)
        if unique_id:
            step["unique_id_divergences"] = int(unique_id.group(1))
        if trc == 0:
            step.update(verdict="match", comparison="definition.kore multiset (reference_differential::emitted_kore_matches_the_reference_frontend)")
        else:
            msg = re.search(r"panicked at[^\n]*\n(.*)", tout + terr, re.S)
            text = (msg.group(1) if msg else (tout + terr)).strip()
            step.update(verdict="mismatch", comparison="definition.kore multiset", divergence="\n".join(text.splitlines()[:DIFF_LINES]))
    else:
        step.update(verdict="match", comparison="both kompile succeeded; no definition.kore to compare")
    return step_record(case, **step)


def program_sort_fallback(case, prog_path, stdin_path):
    """Ask the reference kast for the KORE of the program to learn its actual sort."""
    if not case.ref_kompiled: return None
    args = [f"{KBIN}/kast", "--definition", case.ref_kompiled, "--output", "kore"]
    args += [prog_path] if prog_path else ["-"]
    rc, out, err, _, _ = sh(args, case.dir, min(120, case.remaining()), stdin_path=stdin_path)
    m = re.match(r"\s*inj\{Sort(\w+)\{\}, ?Sort(\w+)\{\}\}", out)
    if m: return m.group(1)
    m = re.match(r"\s*\\dv\{Sort(\w+)\{\}\}", out)
    if m: return m.group(1)
    return None


def run_krust_program(case, kind, prog, stdin_path, extra, sort, syntax_module, step):
    args = [KRUST, "krun", case.def_file, "--main-module", case.main_module, "--syntax-module", syntax_module,
            "--sort", sort, "-I", ".", "--builtin-directory", BUILTIN] + extra
    if prog: args.insert(3, prog)
    elif stdin_path: args.insert(3, "-")
    rc, out, err, secs, to = sh(args, case.dir, case.remaining(), stdin_path=stdin_path)
    return args, rc, out, err, secs, to


def compare_execution(case, rec, step, kout, kore_output, tag):
    """Compare krust KORE output with the checked-in .out (pretty via kprint, or structurally for --output kore)."""
    outp = f"{case.dir}/{rec['out']}" if rec["out"] else None
    kore_path = f"{case.log}/{tag}.krust.kore"
    case.logfile(f"{tag}.krust.kore", kout)
    if not outp or not os.path.exists(outp):
        return None
    expected = open(outp, errors="replace").read()
    if kore_output:
        comparison_environment = {
            "K_REFERENCE_EXECUTION": outp,
            "K_RUST_EXECUTION": kore_path,
            "K_DIFFERENTIAL_MODULE": case.main_module or "MAIN",
            "K_RUST_KRUST": KRUST,
        }
        definition = (
            f"{case.ref_kompiled}/definition.kore" if case.ref_kompiled else None
        )
        if definition and os.path.exists(definition):
            comparison_environment["K_DIFFERENTIAL_DEFINITION"] = definition
        trc, tout, terr = run_test_binary("executed_kore_matches_the_reference_backend",
                                          comparison_environment, case.dir)
        step["comparison"] = "KORE disjunct multiset and constraints (reference_differential::executed_kore_matches_the_reference_backend)"
        if trc == 0: return True
        msg = re.search(r"panicked at[^\n]*\n(.*)", tout + terr, re.S)
        step["divergence"] = "\n".join(((msg.group(1) if msg else tout + terr).strip()).splitlines()[:DIFF_LINES])
        return False
    prc, pout, perr = kprint(case, kore_path)
    step["comparison"] = "kprint(reference kompiled, krust KORE) text vs .out"
    if prc != 0:
        step["divergence"] = "kprint failed on krust output: " + (perr or pout)[:800]
        return False
    case.logfile(f"{tag}.krust.pretty", pout)
    d, compared_as_set = execution_text_diff(expected, pout)
    if compared_as_set:
        step["comparison"] = "kprint #Or disjunct multiset vs .out (arbiter row 12)"
    if d is None: return True
    step["divergence"] = d
    return False


def confirm_oracle(case, rec, step):
    if case.out_of_budget():
        step["oracle_confirmed"] = "not-run (budget)"; return
    rc, out, err, secs, to = sh(["bash", "-c", rec["raw"]], case.dir, case.remaining())
    step["oracle_confirmed"] = (rc == 0 and not to)
    step["oracle_seconds"] = round(secs, 1)
    if rc != 0 or to:
        step["oracle_output"] = "\n".join((out + err).splitlines()[:DIFF_LINES])
        if step.get("verdict") == "mismatch":
            step["verdict"] = "reference-error"
            step["reason"] = "checked-in .out is not reproduced by the pinned reference toolchain; krust mismatch recorded against a stale oracle"


def do_krun(case, rec, search_file=False):
    pos, opts, flags = parse_opts(rec["args"], KRUN_VALUE_OPTS)
    prog = next((p for p in pos if p not in ("print",)), None)
    tag = os.path.basename(prog) if prog else "krun.nopgm"
    step = dict(step="search" if search_file else "krun", test=prog or "(stdin)", ref_cmd=rec["raw"], out=rec["out"])
    if rec["discard"]:
        step.update(verdict="skipped-with-reason", reason="reference recipe discards krun output (1>/dev/null)"); return step_record(case, **step)
    if not case.ref_kompiled:
        step.update(verdict="skipped-with-reason", reason="no reference kompiled definition (reference kompile failed or unsupported)"); return step_record(case, **step)
    unsupported = []
    extra = []
    kore_output = False
    completion_only = False
    for f in flags:
        if f in ("--search",): extra.append("--search-final")
        elif f in ("--search-all", "--search-final", "--search-one-step", "--search-one-or-more-steps"): extra.append(f)
        elif f in ("--no-exc-wrap", "--no-pattern", "--profile", "--debug", "--no-expand-macros"): pass
        elif f in ("--help", "--version", "--dry-run", "--proof-hint", "--term"): unsupported.append(f)
        else: unsupported.append(f)
    for k, vs in opts.items():
        v = vs[-1]
        if k in ("--definition", "-d", "--smt", "--smt-prelude", "--warnings", "-w", "--md-selector"): continue
        if k == "--depth": extra += ["--depth", v]
        elif k == "--bound": extra += ["--search-bound", v]
        elif k == "--io": extra += ["--io", v]
        elif k == "-c":
            for c in vs: extra += ["-c", c]
        elif k in ("--output", "-o"):
            if v == "kore": kore_output = True
            elif v == "pretty": pass
            elif v == "none": completion_only = True
            else: unsupported.append(f"{k} {v}")
        elif k == "-I":
            for d in vs: extra += ["-I", d]
        else: unsupported.append(f"{k} {v}")
    if search_file: extra.append("--search-all")
    if unsupported:
        step.update(verdict="krust-unsupported", reason="reference krun flags with no krust equivalent: " + " ".join(unsupported))
        return step_record(case, **step)
    stdin_path = f"{case.dir}/{rec['stdin']}" if rec["stdin"] and os.path.exists(f"{case.dir}/{rec['stdin']}") else None
    if stdin_path: step["stdin"] = rec["stdin"]
    sort = case.pgm_sort or "KItem"
    args, rc, out, err, secs, to = run_krust_program(case, "krun", prog, stdin_path, extra, sort, case.syntax_module, step)
    step["krust_cmd"] = " ".join(shlex.quote(a) for a in args); step["krust_rc"] = rc; step["krust_seconds"] = round(secs, 1)
    case.logfile(f"{tag}.krust.log", out + "\n--- stderr ---\n" + err)
    if to:
        step.update(verdict="krust-error", stage="krun", reason="krust krun timed out"); return step_record(case, **step)
    if rc != 0 or not out.strip():
        stage = classify_error(err)
        step.update(verdict="krust-error", stage=stage, divergence=(err or out)[-1200:])
        if stage == "inner-parse" and sort in ("K", "KItem"):
            fb = program_sort_fallback(case, prog, stdin_path)
            if fb and fb != sort:
                step["fallback_sort"] = fb
                args2, rc2, out2, err2, secs2, to2 = run_krust_program(case, "krun", prog, stdin_path, extra, fb, case.syntax_module, step)
                step["fallback_krust_cmd"] = " ".join(shlex.quote(a) for a in args2)
                case.logfile(f"{tag}.krust.fallback.log", out2 + "\n--- stderr ---\n" + err2)
                if to2: step["fallback_verdict"] = "krust-error"; step["fallback_stage"] = "krun"; step["fallback_reason"] = "timed out"
                elif rc2 != 0 or not out2.strip():
                    step["fallback_verdict"] = "krust-error"; step["fallback_stage"] = classify_error(err2)
                    step["fallback_divergence"] = (err2 or out2)[-800:]
                else:
                    sub = {k: v for k, v in step.items() if k != "divergence"}
                    ok = compare_execution(case, rec, sub, out2, kore_output, tag + ".fallback")
                    step["fallback_stage"] = "search" if "--search" in " ".join(extra) else "krun"
                    step["fallback_verdict"] = "match" if ok else ("mismatch" if ok is False else "skipped-with-reason")
                    if ok is False and sub.get("divergence"): step["fallback_divergence"] = sub["divergence"]
                    if sub.get("comparison"): step["comparison"] = sub["comparison"]
        return step_record(case, **step)
    step["stage"] = "search" if any(x.startswith("--search") for x in extra) else "krun"
    if completion_only:
        case.logfile(f"{tag}.krust.kore", out)
        step.update(verdict="match", comparison="completion only: the reference recipe runs with --output none, so only successful termination is compared")
        return step_record(case, **step)
    ok = compare_execution(case, rec, step, out, kore_output, tag)
    if ok is None:
        step.update(verdict="skipped-with-reason", reason="no checked-in .out for this test")
    elif ok:
        step["verdict"] = "match"
    else:
        step["verdict"] = "mismatch"
        confirm_oracle(case, rec, step)
    return step_record(case, **step)


def do_kast(case, rec):
    pos, opts, flags = parse_opts(rec["args"], KAST_VALUE_OPTS)
    prog = pos[0] if pos else None
    tag = os.path.basename(prog) if prog else "kast"
    step = dict(step="kast", test=prog, ref_cmd=rec["raw"], out=rec["out"])
    if not case.ref_kompiled:
        step.update(verdict="skipped-with-reason", reason="no reference kompiled definition"); return step_record(case, **step)
    unsupported = [f for f in flags if f not in ("--no-exc-wrap", "--debug")]
    inp = (opts.get("--input") or opts.get("-i") or ["program"])[-1]
    outfmt = (opts.get("--output") or opts.get("-o") or ["kast"])[-1]
    if inp != "program": unsupported.append(f"--input {inp}")
    if outfmt not in ("kast", "json"): unsupported.append(f"--output {outfmt}")
    for k in opts:
        if k not in ("--definition", "-d", "--sort", "-s", "--module", "-m", "--input", "-i", "--output", "-o", "--expression", "-e", "--warnings", "-w"):
            unsupported.append(f"{k} {' '.join(opts[k])}")
    expand = "--expand-macros" in flags
    unsupported = [u for u in unsupported if u not in ("--expand-macros", "--no-substitution-filtering")]
    sort = (opts.get("--sort") or opts.get("-s") or [case.pgm_sort or "KItem"])[-1]
    module = (opts.get("--module") or opts.get("-m") or [case.syntax_module])[-1]
    args = [KRUST, "kast", case.def_file, "--module", module, "--sort", sort, "-I", ".", "--builtin-directory", BUILTIN,
            "-o", "json" if outfmt == "json" else "text"]
    expr = (opts.get("--expression") or opts.get("-e") or [None])[-1]
    if expr is not None: args += ["-e", expr]
    elif prog: args.append(prog)
    step["krust_cmd"] = " ".join(shlex.quote(a) for a in args)
    if unsupported:
        step.update(verdict="krust-unsupported", reason="reference kast flags with no krust equivalent: " + " ".join(unsupported))
        return step_record(case, **step)
    rc, out, err, secs, to = sh(args, case.dir, case.remaining())
    case.logfile(f"{tag}.krust.log", out + "\n--- stderr ---\n" + err)
    step["krust_rc"] = rc; step["krust_seconds"] = round(secs, 1)
    if to: step.update(verdict="krust-error", stage="kast", reason="timed out"); return step_record(case, **step)
    if rc != 0:
        step.update(verdict="krust-error", stage="inner-parse", divergence=(err or out)[-1200:])
        if sort in ("K", "KItem"):
            fb = program_sort_fallback(case, prog, None)
            if fb and fb != sort:
                step["fallback_sort"] = fb
                a2 = [x if x != sort else fb for x in args]
                rc2, out2, err2, _, _ = sh(a2, case.dir, case.remaining())
                step["fallback_krust_cmd"] = " ".join(shlex.quote(a) for a in a2)
                if rc2 != 0: step["fallback_verdict"] = "krust-error"; step["fallback_divergence"] = (err2 or out2)[-800:]
                else:
                    expected = open(f"{case.dir}/{rec['out']}", errors="replace").read() if rec["out"] and os.path.exists(f"{case.dir}/{rec['out']}") else None
                    d = first_diff(expected, out2) if expected is not None else None
                    step["fallback_stage"] = "kast"
                    step["fallback_verdict"] = "match" if (expected is not None and d is None) else ("mismatch" if expected is not None else "skipped-with-reason")
                    if d: step["fallback_divergence"] = d
        return step_record(case, **step)
    step["stage"] = "kast"
    outp = f"{case.dir}/{rec['out']}" if rec["out"] else None
    if not outp or not os.path.exists(outp):
        step.update(verdict="skipped-with-reason", reason="no checked-in .out"); return step_record(case, **step)
    expected = open(outp, errors="replace").read()
    d = first_diff(expected, out)
    step["comparison"] = "kast text vs .out" + (" (reference expanded macros; krust kast cannot)" if expand else "")
    if d is None:
        step["verdict"] = "match"; return step_record(case, **step)
    step["divergence"] = d
    if expand:
        step["verdict"] = "krust-unsupported"; step["reason"] = "--expand-macros has no krust kast equivalent; text differs"
        # secondary parse-only comparison against reference kast --output json without macro expansion
        rargs = [f"{KBIN}/kast", "--definition", case.ref_kompiled, "--sort", sort, "--module", module, "--output", "json", prog]
        rrc, rout, rerr, _, _ = sh(rargs, case.dir, min(120, case.remaining()))
        case.logfile(f"{tag}.reference-json.log", rout + "\n--- stderr ---\n" + rerr)
        if rrc != 0: step["secondary_parse_only_json"] = "reference kast --output json failed: " + rerr.strip()[:200]
        if rrc == 0:
            a2 = [x if x != "text" else "json" for x in args]
            krc, kout, kerr, _, _ = sh(a2, case.dir, case.remaining())
            try:
                rj = json.loads(rout); kj = json.loads(kout)
                step["secondary_parse_only_json"] = "match" if rj.get("term") == kj.get("term") else "mismatch"
            except Exception as ex:
                step["secondary_parse_only_json"] = f"error: {ex}"
        return step_record(case, **step)
    step["verdict"] = "mismatch"
    confirm_oracle(case, rec, step)
    return step_record(case, **step)


def kprove_verdicts(expected, out, err, rc):
    """Return (expected_kind, krust_kind, verdict, note, claims). Kinds: proven | not-proven | error."""
    body = "\n".join(l for l in expected.splitlines() if not re.match(r"\s*(kore-exec: \[|\s*$)", l) and not l.startswith("    ")).strip()
    if body == "#Top" or (body == "" and "#Top" in expected): exp = "proven"
    elif re.search(r"\[Error\] Prover|#Not|#Ceil|#Equals|<generatedTop>|<k>", expected): exp = "not-proven"
    elif "[Error]" in expected: exp = "error"
    elif body == "": exp = "empty"
    else: exp = "not-proven"
    claims = re.findall(r"^claim [^:\n]+: (\w[\w-]*)", out, re.M)
    if claims and rc == 0 and all(c == "proven" for c in claims): got = "proven"
    elif claims or "claims were not proven" in err: got = "not-proven"
    elif rc != 0: got = "error"
    else: got = "unknown"
    if exp == got: v, note = "match", "verdicts agree"
    elif exp == "not-proven" and got == "error": v, note = "krust-error", "reference reports a failed proof; krust errored before producing claim verdicts"
    elif exp == "error" and got == "not-proven": v, note = "mismatch", "reference rejects the specification before proving; krust ran the proof"
    elif exp == "error" and got == "proven": v, note = "mismatch", "reference rejects the specification before proving; krust proves it"
    elif got == "error": v, note = "krust-error", "krust errored"
    else: v, note = "mismatch", f"expected {exp}, krust {got}"
    return exp, got, v, note, claims


def do_kprove(case, rec):
    pos, opts, flags = parse_opts(rec["args"], KPROVE_VALUE_OPTS)
    spec = pos[0] if pos else None
    tag = os.path.basename(spec) if spec else "kprove"
    step = dict(step="kprove", test=spec, ref_cmd=rec["raw"], out=rec["out"])
    if not case.ref_kompiled or not spec:
        step.update(verdict="skipped-with-reason", reason="no reference kompiled definition"); return step_record(case, **step)
    unsupported = [f for f in flags if f not in ("--no-exc-wrap", "--debug")]
    extra = []
    for k, vs in opts.items():
        v = vs[-1]
        if k in ("--definition", "-d", "--smt", "--smt-prelude", "--warnings", "-w", "--type-inference-mode", "--profile-rule-parsing", "--log-level"): continue
        if k == "--md-selector": extra += ["--md-selector", v]
        elif k == "--depth": extra += ["--depth", v]
        elif k in ("--claim", "--claims"):
            for value in vs:
                for claim in value.split(","): extra += ["--claim", claim]
        elif k in ("--exclude", "--trusted"):
            for value in vs:
                for claim in value.split(","): extra += [k, claim]
        elif k in ("--spec-module", "--def-module"): continue
        else: unsupported.append(f"{k} {v}")
    spec_module = (opts.get("--spec-module") or [os.path.basename(spec).rsplit(".", 1)[0].upper()])[-1]
    def_module = (opts.get("--def-module") or [case.main_module])[-1]
    wrapped = spec.rsplit(".", 1)[0] + ".krust-wrapped." + spec.rsplit(".", 1)[1]
    rel_def = os.path.relpath(f"{case.dir}/{case.def_file}", os.path.dirname(f"{case.dir}/{spec}"))
    with open(f"{case.dir}/{wrapped}", "w") as f:
        f.write(f'requires "{rel_def}"\n' + open(f"{case.dir}/{spec}", errors="replace").read())
    args = [KRUST, "kprove", wrapped, "--main-module", spec_module, "--definition-module", def_module, "-I", ".",
            "--builtin-directory", BUILTIN] + extra
    inference_mode = (opts.get("--type-inference-mode") or [None])[-1]
    krust_env = ({"KRUST_TYPE_INFERENCE_MODE": "checked"}
                 if inference_mode == "checked" else None)
    env_prefix = "KRUST_TYPE_INFERENCE_MODE=checked " if krust_env else ""
    step["krust_cmd"] = env_prefix + " ".join(shlex.quote(a) for a in args) + f"   # {wrapped} = spec with `requires \"{rel_def}\"` prepended"
    if unsupported:
        step.update(verdict="krust-unsupported", reason="reference kprove flags with no krust equivalent: " + " ".join(unsupported))
        return step_record(case, **step)
    outp = f"{case.dir}/{rec['out']}" if rec["out"] else None
    expected = open(outp, errors="replace").read() if outp and os.path.exists(outp) else None
    if expected is None:
        step.update(verdict="skipped-with-reason", reason="no checked-in .out"); return step_record(case, **step)
    rc, out, err, secs, to = sh(args, case.dir, case.remaining(), env=krust_env)
    case.logfile(f"{tag}.krust.log", out + "\n--- stderr ---\n" + err)
    step["krust_rc"] = rc; step["krust_seconds"] = round(secs, 1)
    if to: step.update(verdict="krust-error", stage="kprove", reason="krust kprove timed out (case budget)"); return step_record(case, **step)
    exp, got, v, note, claims = kprove_verdicts(expected, out, err, rc)
    step["expected_verdict"] = exp; step["krust_verdict"] = got
    step["stage"] = "kprove" if (claims or got == "not-proven") else classify_error(err)
    step["comparison"] = "verdict-only (proven / not-proven / error; counterexample and message text not compared)"
    step["expected_first_lines"] = "\n".join(expected.splitlines()[:5])
    step["krust_first_lines"] = "\n".join((out + err).strip().splitlines()[:5])
    step["verdict"] = v; step["reason"] = note
    if v == "krust-error": step["divergence"] = (err or out)[-1200:]
    elif v == "mismatch":
        step["divergence"] = f"expected {exp}, krust {got}\n" + (out + err)[-800:]
        confirm_oracle(case, rec, step)
    return step_record(case, **step)


def run_case(rel, kind):
    case = Case(rel); case.kind = kind
    if os.path.exists(case.log): shutil.rmtree(case.log)
    os.makedirs(case.log, exist_ok=True)
    if kind in ("no-makefile", "custom", "kdep"):
        case.note(f"case kind {kind}: not driven"); return finish(case, "skipped-with-reason", f"case kind {kind}")
    for entry in os.listdir(case.dir):
        if entry.endswith("-kompiled") and os.path.isdir(f"{case.dir}/{entry}"): shutil.rmtree(f"{case.dir}/{entry}")
        if entry in (".depend", ".depend-tmp"): os.remove(f"{case.dir}/{entry}")
    case.vars = make_vars(case)
    case.backend = case.vars.get("KOMPILE_BACKEND", "llvm").strip() or "llvm"
    rc, lines, err = make_recipes(case)
    if rc != 0 and not lines:
        case.note("make -n all failed: " + err.strip()[:300]); return finish(case, "skipped-with-reason", "make -n all failed")
    recs = []
    custom = []
    for l in lines:
        r = split_recipe(l)
        if r is None: custom.append(l)
        else: recs.append(r)
    if custom:
        case.custom_targets = custom[:8]
        case.note(f"{len(custom)} recipe line(s) without a K tool were not driven")
    kompiles = [r for r in recs if r["tool"] == "kompile"]
    tests = [r for r in recs if r["tool"] != "kompile"]
    if kind == "fail":
        case.deadline = case.t0 + max(case.budget, 12.0 * len(kompiles))
        case.note(f"ktest-fail case: budget {int(case.deadline - case.t0)} s for {len(kompiles)} kompile recipes")
        for r in kompiles:
            if case.out_of_budget(): step_record(case, step="kompile", reason="case budget exhausted", ref_cmd=r["raw"]); continue
            do_kompile(case, r, expect_fail=True)
    else:
        if not kompiles:
            case.note("no kompile recipe in `make -n all`")
        else:
            if len(kompiles) > 1: case.note(f"{len(kompiles)} kompile recipes; only the first is driven for krust")
            k = kompiles[0]
            pos, opts, flags = parse_opts(k["args"], KOMPILE_VALUE_OPTS)
            case.def_file = next((p for p in pos if re.search(r"\.(k|md|json)$", p)), None)
            do_kompile(case, k, expect_fail=False)
            for extra_k in kompiles[1:]:
                sh(["bash", "-c", extra_k["raw"]], case.dir, case.remaining())
            if not case.main_module and case.def_file:
                case.main_module, case.syntax_module, case.pgm_sort = guess_modules(case, case.def_file, (opts.get("--main-module") or [None])[-1])
                if (opts.get("--syntax-module") or [None])[-1]: case.syntax_module = opts["--syntax-module"][-1]
    for r in tests:
        if case.out_of_budget():
            step_record(case, step=r["tool"], test=" ".join(r["args"][:1]), reason=f"case budget exhausted ({case.budget:g} s)", ref_cmd=r["raw"]); continue
        if kind == "fail" and r["tool"] == "kast":
            do_kast(case, r) if case.ref_kompiled else step_record(case, step="kast", ref_cmd=r["raw"], reason="ktest-fail kast test without a kompiled definition")
        elif r["tool"] == "krun":
            pos, _, _ = parse_opts(r["args"], KRUN_VALUE_OPTS)
            do_krun(case, r, search_file=any(p.endswith(".search") for p in pos))
        elif r["tool"] == "kast": do_kast(case, r)
        elif r["tool"] == "kprove": do_kprove(case, r)
        elif r["tool"] == "kparse": step_record(case, step="kparse", test=" ".join(r["args"][:1]), ref_cmd=r["raw"], verdict="krust-unsupported", reason="kparse (program -> KORE) has no krust equivalent; krust kast emits KAST text/JSON only")
        else: step_record(case, step=r["tool"], ref_cmd=r["raw"], verdict="krust-unsupported", reason=f"{r['tool']} has no krust equivalent")
    return finish(case)


VERDICT_RANK = {
    "reference-error": -1,
    "krust-error": 0,
    "mismatch": 1,
    "krust-unsupported": 2,
    "skipped-with-reason": 2,
    "match": 3,
}
STAGE_RANK = ["outer-parse", "inner-parse", "kompile", "kast", "krun", "search", "kprove"]


def finish(case, verdict=None, reason=None):
    case.seconds = round(time.monotonic() - case.t0, 1)
    if verdict is None:
        vs = [s.get("verdict", "skipped-with-reason") for s in case.steps]
        if not vs: verdict, reason = "skipped-with-reason", "no driven steps"
        else:
            verdict = min(vs, key=VERDICT_RANK.__getitem__)
            first = next(s for s in case.steps if s.get("verdict") == verdict)
            reason = first.get("reason") or (f"{first.get('step')} {first.get('test', '')}".strip() + f": {verdict}")
    stages = [s.get("stage") for s in case.steps if s.get("stage")]
    stage = max(stages, key=STAGE_RANK.index) if stages else "none"
    case.verdict, case.reason, case.stage = verdict, reason, stage
    case.fallback_verdict = case.fallback_stage = None
    if any("fallback_sort" in s for s in case.steps):
        vs = [s.get("fallback_verdict", s.get("verdict", "skipped-with-reason")) for s in case.steps]
        case.fallback_verdict = min(vs, key=VERDICT_RANK.__getitem__)
        st = [s.get("fallback_stage", s.get("stage")) for s in case.steps if s.get("fallback_stage", s.get("stage"))]
        case.fallback_stage = max(st, key=STAGE_RANK.index) if st else stage
    return case


def write_results(cases, path=RESULTS):
    lines = ["# Conformance of krust against K's regression-new suite (pinned K v7.1.337 at k/result, krust target/release/krust).",
             "# One [[case]] per leaf Makefile; [[case.step]] per reference recipe. See summary.md for the method and verdict vocabulary.",
             f"# generated {time.strftime('%Y-%m-%d %H:%M:%S')}", ""]
    for c in sorted(cases, key=lambda c: c.name):
        lines += ["[[case]]", f"name = {toml_str(c.name)}", f"kind = {toml_str(c.kind)}", f"backend = {toml_str(c.backend)}",
                  f"verdict = {toml_str(c.verdict)}", f"stage = {toml_str(c.stage)}", f"reason = {toml_str(c.reason or '')}",
                  f"seconds = {getattr(c, 'seconds', 0)}", f"steps = {len(c.steps)}"]
        if getattr(c, "fallback_verdict", None):
            lines.append(f"fallback_verdict = {toml_str(c.fallback_verdict)}  # after re-parsing K/KItem programs with the sort the reference kast assigns")
            lines.append(f"fallback_stage = {toml_str(c.fallback_stage)}")
        if c.main_module: lines.append(f"main_module = {toml_str(c.main_module)}")
        if c.syntax_module: lines.append(f"syntax_module = {toml_str(c.syntax_module)}")
        if c.pgm_sort: lines.append(f"pgm_sort = {toml_str(c.pgm_sort)}")
        if c.notes: lines.append("notes = [" + ", ".join(toml_str(n) for n in c.notes) + "]")
        if c.custom_targets: lines.append("undriven_recipes = [" + ", ".join(toml_str(n) for n in c.custom_targets) + "]")
        lines.append(f"log_dir = {toml_str(os.path.relpath(c.log, HERE))}")
        lines.append("")
        for s in c.steps:
            lines.append("[[case.step]]")
            for k, v in s.items():
                if v is None: continue
                if isinstance(v, bool): lines.append(f"{k} = {'true' if v else 'false'}")
                elif isinstance(v, (int, float)): lines.append(f"{k} = {v}")
                elif isinstance(v, list): lines.append(f"{k} = [" + ", ".join(toml_str(str(x)) for x in v) + "]")
                elif "\n" in str(v): lines.append(f"{k} = {toml_ml(str(v))}")
                else: lines.append(f"{k} = {toml_str(str(v))}")
            lines.append("")
    tmp = path + ".tmp"
    with open(tmp, "w") as f: f.write("\n".join(lines))
    os.replace(tmp, path)


def positive_integer(value):
    try:
        parsed = int(value)
    except ValueError as error:
        raise argparse.ArgumentTypeError("must be an integer") from error
    if parsed <= 0:
        raise argparse.ArgumentTypeError("must be positive")
    return parsed


def positive_seconds(value):
    try:
        parsed = float(value)
    except ValueError as error:
        raise argparse.ArgumentTypeError("must be a number") from error
    if not math.isfinite(parsed) or parsed <= 0:
        raise argparse.ArgumentTypeError("must be a positive finite number")
    return parsed


def case_budget_override(value):
    name, separator, seconds = value.partition("=")
    if not separator or not name or not seconds:
        raise argparse.ArgumentTypeError("must have the form NAME=SECONDS")
    return name, positive_seconds(seconds)


def validate_work_tree_target(path, workspace, source_tree):
    """Reject broad or source-tree scratch targets before any recursive removal."""
    target = Path(path).resolve()
    workspace = Path(workspace).resolve()
    source_tree = Path(source_tree).resolve()
    protected = {
        Path("/").resolve(),
        Path("/tmp").resolve(),
        Path("/var/tmp").resolve(),
        Path.home().resolve(),
        workspace,
        source_tree,
    }
    if target in protected or len(target.parts) < 3:
        raise ValueError(f"refusing unsafe conformance work tree: {target}")
    if workspace.is_relative_to(target) or source_tree.is_relative_to(target):
        raise ValueError(f"work tree would contain a protected checkout: {target}")
    if target.is_relative_to(source_tree):
        raise ValueError(f"work tree must not be inside the pinned K source tree: {target}")
    return str(target)


def main():
    global BUILTIN, CASE_BUDGET, CASE_BUDGETS, EXPECTATIONS, IGNORE_UNIQUE_ID
    global KBIN, K_CHECKOUT, K_OPTS, KORE_PARSER, KR, KRUST, LOGS
    global RESULTS, SRC_TREE, TEST_BINARY, WORK_TREE

    ap = argparse.ArgumentParser()
    ap.add_argument("--workspace", help="repository root; defaults to the parent of scripts/")
    ap.add_argument("--k-bin", help="directory containing the pinned K executables")
    ap.add_argument("--krust", help="krust executable")
    ap.add_argument("--test-binary", help="reference_differential test executable")
    ap.add_argument("--work-tree", default=WORK_TREE, help="scratch k-distribution copy")
    ap.add_argument("--results", default=RESULTS)
    ap.add_argument("--logs", default=LOGS)
    ap.add_argument("--k-opts", help="bounded K JVM options")
    ap.add_argument("--budget", type=positive_seconds, default=CASE_BUDGET)
    ap.add_argument(
        "--case-budget",
        type=case_budget_override,
        action="append",
        default=[],
        metavar="NAME=SECONDS",
    )
    ap.add_argument("--ticket", action="append", default=[], help="select cases owned by ID")
    ap.add_argument("--stage", action="append", default=[], help="select baseline stage")
    ap.add_argument("--cases", nargs="*", default=[], help="case names relative to regression-new")
    ap.add_argument("--all", action="store_true", help="select every regression-new leaf")
    ap.add_argument("--kore-parser", help="matching pinned kore-parser executable")
    ap.add_argument("--expectations", help="case ownership and budget TOML")
    ap.add_argument("--jobs", type=positive_integer, default=2)
    ap.add_argument("--rank", choices=sorted(VERDICT_RANK), help="print a verdict rank and exit")
    ap.add_argument("--list", action="store_true")
    ap.add_argument("--fresh-copy", action="store_true", help="re-copy the regression tree to the scratch directory")
    ap.add_argument("--postprocess", action="store_true", help="only reclassify/trim an existing results file")
    ap.add_argument("--merge", help="replace the cases of --results by the cases found in this results file, then postprocess")
    a = ap.parse_args()

    if a.rank:
        print(VERDICT_RANK[a.rank])
        return 0

    workspace = Path(a.workspace or KR).resolve()
    KR = str(workspace)
    K_CHECKOUT = str(Path(os.environ.get("K_CHECKOUT", workspace / "k")).resolve())
    if a.k_bin:
        KBIN = str(Path(a.k_bin).resolve())
    elif os.environ.get("K_KOMPILE"):
        KBIN = str(Path(os.environ["K_KOMPILE"]).resolve().parent)
    else:
        KBIN = str(Path(K_CHECKOUT) / "result" / "bin")
    BUILTIN = str(Path(K_CHECKOUT) / "k-distribution" / "include" / "kframework" / "builtin")
    SRC_TREE = str(Path(K_CHECKOUT) / "k-distribution")
    KRUST = str(Path(a.krust or os.environ.get("CONFORMANCE_KRUST", workspace / "target" / "release" / "krust")).resolve())
    selected_test_binary = a.test_binary or os.environ.get("CONFORMANCE_TEST_BINARY")
    TEST_BINARY = str(Path(selected_test_binary).resolve()) if selected_test_binary else None
    KORE_PARSER = str(Path(a.kore_parser or os.environ.get("K_KORE_PARSER", Path(KBIN) / "kore-parser")).resolve())
    EXPECTATIONS = str(Path(a.expectations or workspace / "scripts" / "conformance" / "expectations.toml").resolve())
    RESULTS = str(Path(a.results).resolve())
    LOGS = str(Path(a.logs).resolve())
    try:
        WORK_TREE = validate_work_tree_target(a.work_tree, workspace, SRC_TREE)
    except ValueError as error:
        ap.error(str(error))
    CASE_BUDGET = a.budget
    CASE_BUDGETS = {}
    a.results = RESULTS

    os.makedirs(os.path.dirname(RESULTS), exist_ok=True)

    if a.merge:
        with open(a.results, "rb") as source:
            base = tomllib.load(source)
        with open(a.merge, "rb") as source:
            extra = tomllib.load(source)
        names = {c["name"] for c in extra.get("case", [])}
        merged = [c for c in base.get("case", []) if c["name"] not in names] + extra.get("case", [])
        tmp = a.results + ".merge"
        with open(tmp, "w") as f:
            f.write("# merged\n")
            for c in merged:
                f.write("[[case]]\n")
                for k, v in c.items():
                    if k == "step": continue
                    f.write(f"{k} = {toml_ml(v) if isinstance(v, str) and chr(10) in v else (toml_str(v) if isinstance(v, str) else ('true' if v is True else 'false' if v is False else (json.dumps(v) if isinstance(v, list) else v)))}\n")
                f.write("\n")
                for st in c.get("step", []):
                    f.write("[[case.step]]\n")
                    for k, v in st.items():
                        if isinstance(v, bool): f.write(f"{k} = {'true' if v else 'false'}\n")
                        elif isinstance(v, (int, float)): f.write(f"{k} = {v}\n")
                        elif isinstance(v, list): f.write(f"{k} = [" + ", ".join(toml_str(str(x)) for x in v) + "]\n")
                        elif chr(10) in str(v): f.write(f"{k} = {toml_ml(str(v))}\n")
                        else: f.write(f"{k} = {toml_str(str(v))}\n")
                    f.write("\n")
        os.replace(tmp, a.results)
        postprocess(a.results)
        return 0
    if a.postprocess:
        postprocess(a.results)
        return 0

    try:
        cases = enumerate_cases()
    except OSError as error:
        ap.error(f"cannot enumerate {SRC_TREE}/{REG}: {error}")
    if a.list:
        for rel, kind in cases: print(kind, rel)
        return 0

    try:
        expectations_document, expectation_budgets = load_expectations(EXPECTATIONS)
    except (OSError, tomllib.TOMLDecodeError, KeyError, TypeError, ValueError) as error:
        ap.error(f"cannot load expectations {EXPECTATIONS}: {error}")
    expectations = {}
    for row in expectations_document.get("case", []):
        name = row.get("name")
        if name in expectations:
            ap.error(f"duplicate expectation case: {name}")
        expectations[name] = row
    for name, budget in expectation_budgets.items():
        if not math.isfinite(budget) or budget <= 0:
            ap.error(f"expectation budget for {name} must be positive and finite")
    CASE_BUDGETS.update(expectation_budgets)
    for name, budget in a.case_budget:
        CASE_BUDGETS[name] = budget

    available = {name for name, _ in cases}
    unknown_overrides = sorted(CASE_BUDGETS.keys() - available)
    if unknown_overrides:
        ap.error(f"unknown --case-budget case(s): {', '.join(unknown_overrides)}")

    selectors_given = bool(a.cases or a.ticket or a.stage)
    selected = set(a.cases)
    for ticket in a.ticket:
        selected.update(
            name for name, row in expectations.items()
            if ticket in row.get("tickets", [])
        )
    for stage in a.stage:
        selected.update(
            name for name, row in expectations.items()
            if row.get("baseline_stage") == stage
        )
    if a.all or not selectors_given:
        selected.update(available)
    unknown = sorted(selected - available)
    if unknown:
        ap.error(f"unknown conformance case(s): {', '.join(unknown)}")
    cases = [(name, kind) for name, kind in cases if name in selected]
    if not cases:
        ap.error("the selection contains no conformance cases")

    if a.k_opts is not None:
        K_OPTS = a.k_opts
    elif os.environ.get("REFERENCE_DIFFERENTIAL_K_OPTS"):
        K_OPTS = os.environ["REFERENCE_DIFFERENTIAL_K_OPTS"]
    else:
        try:
            K_OPTS = reference_default_k_opts(KR)
        except RuntimeError as error:
            ap.error(str(error))
    try:
        normalisations = load_reference_normalisations(KR, K_CHECKOUT)
    except RuntimeError as error:
        ap.error(str(error))
    IGNORE_UNIQUE_ID = bool(normalisations.get("ignore_unique_id"))

    if a.fresh_copy or not os.path.isdir(WORK_TREE):
        if os.path.lexists(WORK_TREE):
            if os.path.islink(WORK_TREE) or not os.path.isdir(WORK_TREE):
                ap.error(f"work tree exists but is not a directory: {WORK_TREE}")
            shutil.rmtree(WORK_TREE)
        os.makedirs(os.path.dirname(WORK_TREE), exist_ok=True)
        try:
            shutil.copytree(f"{SRC_TREE}/include", f"{WORK_TREE}/include", symlinks=True)
            shutil.copytree(f"{SRC_TREE}/{REG}", f"{WORK_TREE}/{REG}", symlinks=True)
        except OSError as error:
            ap.error(f"cannot populate work tree {WORK_TREE}: {error}")
    os.makedirs(LOGS, exist_ok=True)

    done = []
    t0 = time.monotonic()
    def work(item):
        rel, kind = item
        try:
            c = run_case(rel, kind)
        except Exception as ex:
            import traceback
            c = Case(rel); c.kind = kind; c.note("driver exception: " + traceback.format_exc()[-800:]); finish(c, "skipped-with-reason", f"driver exception: {ex}")
        with lock:
            done.append(c); write_results(done, a.results)
            print(f"[{len(done)}/{len(cases)}] {c.verdict:22s} {c.stage:12s} {c.seconds:6.1f}s  {rel}", flush=True)
    with ThreadPoolExecutor(max_workers=a.jobs) as ex:
        list(ex.map(work, cases))
    print(f"done: {len(done)} cases in {time.monotonic() - t0:.0f}s")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
