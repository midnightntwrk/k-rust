#!/usr/bin/env python3
"""Conformance driver: K regression-new cases through the pinned reference toolchain and krust.

For every leaf case (a directory whose Makefile includes ktest.mak or ktest-fail.mak, expanding
ktest-group.mak SUBDIRS recursively) the driver:
  1. copies the case tree to a scratch directory (never writes into k/),
  2. asks GNU make for the exact reference recipes (`make -n all` with K_BIN pointed at k/result/bin;
     reviewed manifest rows supply consumer chains hidden behind fixture-specific default goals),
  3. runs the reference kompile recipe(s) verbatim (and every recipe of a ktest-fail case, which are
     self-checking against their .out), skipping reference test runs whose checked-in .out exists,
  4. runs the krust equivalent of each recipe, converts krust's KORE output to K surface syntax with
     the reference `kprint` against the reference-kompiled definition, and diffs against the .out,
  5. when the texts differ, re-runs the reference recipe with --output kore, simplifies that result
     and krust's with `krust kore-simplify` against the reference-kompiled definition, and compares
     the two simplified patterns structurally (C8); a step that matches only this way says so,
  6. on a remaining mismatch re-runs the reference recipe verbatim to confirm the .out is still the oracle.
Every case runs under a budget (--budget, or `budget` in expectations.toml); a program execution may
additionally be capped by the case's `step_budget`, so one divergent program is reported as its own
krust-error instead of consuming the budget of every program behind it.
Results go to the requested results.toml (rewritten after every case) and per-case logs directory.
"""
import argparse, json, math, os, re, shlex, shutil, subprocess, sys, tempfile, threading, time
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
BISON_PARSER_MANIFEST = str(HERE / "bison-parsers.toml")
BISON_PARSER_ONLY = False
IGNORE_UNIQUE_ID = False
CASE_BUDGET = 300.0
CASE_BUDGETS = {}
# Per-program ceiling inside the case budget (expectations `step_budget`); absent means the case
# budget alone bounds a program, so one divergent program hides every program behind it.
STEP_BUDGETS = {}
DIFF_LINES = 20
WORK_TREE_MARKER = ".krust-conformance-source.json"
REFERENCE_ERROR = object()

TOOLS = {"kompile", "krun", "kast", "kprove", "kparse", "kdep", "kore-print", "k-rule-find", "llvm-krun", "kprint", "kserver"}
KOMPILE_VALUE_OPTS = {"--backend", "--main-module", "--syntax-module", "--output-definition", "--md-selector", "-I",
    "--hook-namespaces", "--type-inference-mode", "--post-process", "--top-cell", "--profile-rule-parsing",
    "--bison-stack-max-depth", "--llvm-kompile-type", "--llvm-kompile-output", "-ccopt", "-w", "-W", "-Wno",
    "--warnings", "-d", "--directory", "--definition", "-O", "--concrete-rules", "--smt-prelude", "--llvm-kompile-flags"}
KRUN_VALUE_OPTS = {"--definition", "-d", "--depth", "--bound", "--pattern", "--parser", "--output", "-o", "--output-file",
    "-c", "-p", "--io", "--smt", "--smt-prelude", "--smt-timeout", "--term", "--search-pattern", "--md-selector", "-I", "--warnings", "-w"}
KAST_VALUE_OPTS = {"--definition", "-d", "--sort", "-s", "--module", "-m", "--input", "-i", "--output", "-o", "--output-file",
    "--expression", "-e", "--md-selector", "-I", "--warnings", "-w", "--gen-parser-only", "--bison-stack-max-depth"}
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
    step_budgets = {
        row["name"]: float(row["step_budget"])
        for row in rows
        if "step_budget" in row
    }
    return document, budgets, step_budgets


def load_bison_parsers(path):
    with open(path, "rb") as source:
        document = tomllib.load(source)
    if document.get("schema") != 1:
        raise ValueError("bison parser manifest schema must be 1")
    allowed = {"name", "artifact", "inputs", "makefile", "comparison", "reason", "consumer", "library"}
    rows = {}
    for index, row in enumerate(document.get("case", [])):
        unknown = set(row) - allowed
        if unknown:
            raise ValueError(f"bison parser row {index} has unknown fields: {sorted(unknown)}")
        missing = {"name", "artifact", "inputs"} - set(row)
        if missing:
            raise ValueError(f"bison parser row {index} is missing: {sorted(missing)}")
        name = row["name"]
        if not isinstance(name, str) or not name or name in rows:
            raise ValueError(f"invalid or duplicate bison parser case: {name!r}")
        name_path = Path(name)
        if name_path.is_absolute() or any(part in (".", "..") for part in name_path.parts):
            raise ValueError(f"unsafe bison parser case path: {name!r}")
        if row["artifact"] not in ("executable", "shared-library"):
            raise ValueError(f"invalid bison parser artifact for {name}: {row['artifact']!r}")
        if row.get("comparison", "exact") not in ("exact", "amb"):
            raise ValueError(f"invalid bison parser comparison for {name}")
        inputs = row["inputs"]
        if (not isinstance(inputs, list) or not inputs or
                any(not isinstance(item, str) or not item for item in inputs) or
                inputs != sorted(set(inputs))):
            raise ValueError(f"bison parser inputs for {name} must be nonempty, unique, and sorted")
        if any(Path(item).is_absolute() or any(part in (".", "..") for part in Path(item).parts)
               for item in inputs):
            raise ValueError(f"unsafe bison parser input path for {name}")
        for optional in ("makefile", "reason", "consumer", "library"):
            if optional in row and not isinstance(row[optional], str):
                raise ValueError(f"bison parser {optional} for {name} must be a string")
        if "makefile" in row:
            makefile = Path(row["makefile"])
            if makefile.is_absolute() or len(makefile.parts) != 1 or makefile.parts[0] in (".", ".."):
                raise ValueError(f"unsafe bison parser makefile for {name}")
        if row["artifact"] == "shared-library":
            missing_library_fields = {"consumer", "library"} - set(row)
            if missing_library_fields:
                raise ValueError(
                    f"shared-library bison parser row {name} is missing: "
                    f"{sorted(missing_library_fields)}"
                )
            consumer = Path(row["consumer"])
            if (not row["consumer"] or consumer.is_absolute() or
                    any(part in (".", "..") for part in consumer.parts)):
                raise ValueError(f"unsafe bison parser consumer for {name}")
            if not re.fullmatch(r"[A-Za-z0-9_.+-]+", row["library"]):
                raise ValueError(f"unsafe bison parser library for {name}")
        rows[name] = dict(row, comparison=row.get("comparison", "exact"))
    return rows


BISON_PARSERS = load_bison_parsers(BISON_PARSER_MANIFEST)


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


def sh_bytes(cmd, cwd, timeout, stdin_path=None, env=None):
    """Run a command while preserving stdout as exact bytes."""
    e = dict(os.environ); e["K_OPTS"] = K_OPTS
    if env: e.update(env)
    stdin = open(stdin_path, "rb") if stdin_path and os.path.exists(stdin_path) else subprocess.DEVNULL
    t0 = time.monotonic()
    try:
        p = subprocess.Popen(cmd, cwd=cwd, stdin=stdin, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                             env=e, start_new_session=True)
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
    return rc, out, err.decode("utf-8", "replace"), time.monotonic() - t0, to


def sh_to_file(cmd, cwd, timeout, stdout_path, env=None):
    """Run a command with stdout connected directly to a binary file."""
    e = dict(os.environ); e["K_OPTS"] = K_OPTS
    if env: e.update(env)
    t0 = time.monotonic()
    os.makedirs(os.path.dirname(stdout_path), exist_ok=True)
    try:
        with open(stdout_path, "wb") as stdout:
            process = subprocess.Popen(
                cmd, cwd=cwd, stdin=subprocess.DEVNULL, stdout=stdout,
                stderr=subprocess.PIPE, env=e, start_new_session=True,
            )
            try:
                _, stderr = process.communicate(timeout=max(1.0, timeout))
                timed_out = False
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, 9)
                _, stderr = process.communicate()
                timed_out = True
            rc = process.returncode
    except FileNotFoundError as error:
        rc, stderr, timed_out = 127, str(error).encode(), False
    return rc, stderr.decode("utf-8", "replace"), time.monotonic() - t0, timed_out


def reference_process_env(tool=None, args=()):
    """Bound threaded Haskell tools without passing -N1 to non-threaded helpers."""
    configured = os.environ.get("GHCRTS")
    if configured is not None:
        return {"GHCRTS": configured}
    # The pinned kore-match-disjunction is not threaded. Reference krun delegates
    # --pattern matching to it, so the default threaded-runtime bound must not
    # leak through the wrapper to that child process.
    uses_match_disjunction = tool == "krun" and any(
        arg == "--pattern" or arg.startswith("--pattern=") for arg in args
    )
    if tool in ("kore-match-disjunction", "kore-parser") or uses_match_disjunction:
        return {"GHCRTS": ""}
    return {"GHCRTS": "-N1"}


def output_excerpt(text):
    return "\n".join(text.splitlines()[:DIFF_LINES])


def is_reference_crash(text):
    return re.search(
        r"panicked|outofmemory|out of memory|segmentation fault|stack overflow|"
        r"failed to create.*thread|cannot allocate memory|backend crashed",
        text,
        re.I,
    ) is not None


def memory_guard_suffix():
    guard = os.environ.get("REFERENCE_DIFFERENTIAL_JOB_GUARD_KIND", "").strip()
    return f" under the {guard} memory guard" if guard else ""


def reference_failure_reason(prefix, rc, timed_out, stderr, empty_output=False):
    if timed_out:
        outcome = "timed out"
    elif empty_output:
        outcome = f"exit {rc}, empty stdout"
    else:
        outcome = f"exit {rc}"
    excerpt = output_excerpt(stderr).strip()
    crash = " (reference crash)" if is_reference_crash(stderr) else ""
    detail = f": {excerpt}" if excerpt else ""
    return f"{prefix} ({outcome}){crash}{detail}{memory_guard_suffix()}"


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


# C7 (scripts/reference-normalisations.toml): kprint prints a rule existential (a Var'Ques' name) as
# `?Name:Sort`; both engines instantiate it through a fresh counter and keep an engine-chosen unification
# representative, so the names are compared modulo a bijective, sort-preserving renaming. A double-quoted
# string literal is matched first and left untouched. The canonical `?'KDiff<n>` names start with a
# quote, which the name class excludes, so they can never collide with a name either engine prints.
EXISTENTIAL_TOKEN = re.compile(r'"(?:[^"\\]|\\.)*"|\?([A-Za-z_][A-Za-z0-9_\']*)(:[A-Za-z][A-Za-z0-9]*)')
PATTERN_EXISTENTIAL = re.compile(r'"(?:[^"\\]|\\.)*"|\?([A-Za-z_][A-Za-z0-9_\']*)')


def pattern_existentials(pattern):
    """The `?` variable names a krun --pattern text declares (with or without a sort); C7 keeps them literal."""
    return frozenset(m.group(1) for m in PATTERN_EXISTENTIAL.finditer(pattern or "") if m.group(1))


def rename_existentials(text, fixed=frozenset()):
    """C7: rename every `?Name:Sort` outside string literals to `?'KDiff<n>:Sort` by first occurrence of Name."""
    indices = {}
    def sub(m):
        name = m.group(1)
        if name is None or name in fixed: return m.group(0)
        return f"?'KDiff{indices.setdefault(name, len(indices))}{m.group(2)}"
    return EXISTENTIAL_TOKEN.sub(sub, text)


def execution_text_diff(expected, actual, pattern=""):
    """Diff kprint text modulo C7 (existential renaming per disjunct) and C1 (sorted #Or branches).
    Returns (diff of the renamed texts or None, compared_as_set, renamed_existentials); the last is true
    only when the literal texts differ and the renamed texts match."""
    fixed = pattern_existentials(pattern)
    def normalize(text, rename):
        disjuncts = split_surface_disjunction(text)
        parts = [text] if disjuncts is None else disjuncts
        if rename: parts = [rename_existentials(part, fixed) for part in parts]
        return "\n#Or\n".join(sorted(parts)), disjuncts is not None
    (expected_text, expected_set), (actual_text, actual_set) = normalize(expected, True), normalize(actual, True)
    d = first_diff(expected_text, actual_text)
    renamed = d is None and first_diff(normalize(expected, False)[0], normalize(actual, False)[0]) is not None
    return d, expected_set or actual_set, renamed


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
        self.step_budget = STEP_BUDGETS.get(rel)
        self.deadline = self.t0 + self.budget
        self.ref_kompiled = None
        self.krust_runtime_definition = "krust-kompiled"
        self.needs_krust_runtime = False
        self.main_module = None
        self.syntax_module = None
        self.pgm_sort = None
        self.config_sorts = {}
        self.def_file = None
        self.md_selectors = []
        self.kompile_recipe = None
        self.proof_definition_ready = False
        self.proof_compile_attempted = False
        self.proof_compile_failure = None
        self.custom_targets = []
        self.bison_parser = BISON_PARSERS.get(rel)
        self.makefile = self.bison_parser.get("makefile", "Makefile") if self.bison_parser else "Makefile"

    def remaining(self):
        return self.deadline - time.monotonic()

    def out_of_budget(self):
        return self.remaining() <= 1

    def step_timeout(self):
        """Timeout for one program execution: the remaining case budget, capped by the step budget.

        Returns (seconds, capped); `capped` says the step budget, not the case budget, is the bound,
        so a kill can be reported as the program's own cost rather than as budget exhaustion.
        """
        remaining = self.remaining()
        if self.step_budget is not None and self.step_budget < remaining:
            return self.step_budget, True
        return remaining, False

    def note(self, s):
        self.notes.append(s)

    def logfile(self, name, text):
        os.makedirs(self.log, exist_ok=True)
        with open(f"{self.log}/{name}", "w") as f: f.write(text)

    def binary_logfile(self, name, data):
        os.makedirs(self.log, exist_ok=True)
        with open(f"{self.log}/{name}", "wb") as f: f.write(data)


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
    makefile = ["-f", case.makefile] if case.makefile != "Makefile" else []
    rc, out, err, _, _ = sh(["make", *makefile, "-pn", "clean", f"K_BIN={KBIN}", f"BUILTIN_DIR={BUILTIN}", "KDEP=true"], case.dir, 60)
    v = {}
    for m in re.finditer(r"^([A-Z_0-9]+) :?= (.*)$", out, re.M):
        v[m.group(1)] = m.group(2)
    return v


def make_recipes(case):
    makefile = ["-f", case.makefile] if case.makefile != "Makefile" else []
    rc, out, err, secs, to = sh(["make", *makefile, "-n", "all", f"K_BIN={KBIN}", f"BUILTIN_DIR={BUILTIN}", "KDEP=true"], case.dir, 120)
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
    if "in-process backend halted at depth" in e: return "krun"
    if re.search(r"could not parse (program|input|rule|claim|context|configuration|sentence|term)|has \d+ parses|ambigu|could not infer|inference|sort inference", e): return "inner-parse"
    if re.search(r"outer|unexpected (token|character|end)|unterminated|imports missing|missing module|unknown module|duplicate module|differs from previous declaration|could not (read|load|find) (file|module)|failed to extract k code|no such file|requires", e): return "outer-parse"
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


def run_test_binary_result(name, env, cwd, timeout=120):
    """Run one ignored comparison test of crates/k-rust/tests/reference_differential.rs directly."""
    binary = TEST_BINARY
    if not binary:
        dependency_dir = os.path.join(KR, "target", "debug", "deps")
        if not os.path.isdir(dependency_dir):
            return 1, "", f"no reference_differential test binary directory: {dependency_dir}", False
        bins = sorted((os.path.getmtime(path), path) for path in
                      (os.path.join(dependency_dir, entry) for entry in os.listdir(dependency_dir)
                       if entry.startswith("reference_differential-") and not entry.endswith(".d"))
                      if os.access(path, os.X_OK))
        if not bins:
            return 1, "", "no reference_differential test binary in target/debug/deps", False
        binary = bins[-1][1]
    rc, out, err, _, timed_out = sh(
        [binary, "--ignored", "--exact", name, "--nocapture", "--test-threads=1"],
        cwd,
        timeout,
        env=env,
    )
    return rc, out, err, timed_out


def run_test_binary(name, env, cwd, timeout=120):
    rc, out, err, _ = run_test_binary_result(name, env, cwd, timeout)
    return rc, out, err


def kprint(case, kore_path):
    rc, out, err, _, _ = sh(
        [f"{KBIN}/kprint", case.ref_kompiled, kore_path, "false"],
        case.dir,
        60,
        env=reference_process_env("kprint"),
    )
    return rc, out, err


def step_record(case, **kw):
    kw.setdefault("verdict", "skipped-with-reason")
    case.steps.append(kw)
    return kw


def krust_kompile_args(case, rec, expect_fail=False):
    """Translate a reference kompile recipe; `expect_fail` marks a ktest-fail recipe."""
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
    if syn or expect_fail:
        args += ["--syntax-module", syn or gs]
    # Preserve the selection in this compilation. Program runs consume the published runnable
    # artifact and therefore do not repeat source or Markdown parsing.
    case.md_selectors = list(opts.get("--md-selector", []))
    if case.def_file is None: case.def_file = src
    if not case.main_module: case.main_module = main
    if not case.syntax_module: case.syntax_module = syn or gs
    for s in case.md_selectors: args += ["--md-selector", s]
    for d in opts.get("-I", []): args += ["-I", d]
    if "--no-prelude" in flags: args.append("--no-prelude")
    if "--emit-json" in flags: args.append("--emit-json")
    for flag in flags:
        if flag in ("--gen-bison-parser", "--gen-glr-bison-parser", "--bison-lists", "--bison-parser-library"):
            args.append(flag)
    if opts.get("--bison-stack-max-depth"):
        args += ["--bison-stack-max-depth", opts["--bison-stack-max-depth"][-1]]
    # Warning policy for the -w/-w2e flags krust implements (`--warnings LEVEL`,
    # `--warnings-to-errors`). The contract is forwarded whole or not at all: `-w2e` reaches krust
    # only for a ktest-fail recipe (the reference's rejection depends on it) that carries no
    # per-category `-W`/`-Wno`, which krust cannot express. Forwarding it next to a dropped `-Wno`
    # promotes a warning the reference disabled (werrorCategory), and forwarding it on a recipe the
    # reference accepts promotes krust's extension warnings that K never emits (prelude-warnings,
    # UnadmittedHookNamespace); both are spurious krust-errors, not conformance divergences.
    warning_level = (opts.get("-w") or opts.get("--warnings") or [None])[-1]
    if warning_level in ("all", "normal", "none"): args += ["--warnings", warning_level]
    per_category = [f"{k} {v}" for k in ("-W", "-Wno") for v in opts.get(k, [])]
    w2e = [f for f in flags if f in ("-w2e", "--warnings-to-errors")]
    dropped = [f for f in flags if f not in ("--no-prelude", "--emit-json", "--no-exc-wrap", "-w2e", "--warnings-to-errors", "--gen-bison-parser", "--gen-glr-bison-parser", "--bison-lists", "--bison-parser-library")]
    if w2e and per_category:
        dropped.append(f"{w2e[-1]} (not forwarded next to {' '.join(per_category)}: krust has no per-category warning control, and a partial contract would promote warnings the reference disabled)")
    elif w2e and not expect_fail:
        dropped.append(f"{w2e[-1]} (not forwarded: the reference accepts this recipe, and krust's extension warnings would be promoted)")
    elif w2e:
        args.append("--warnings-to-errors")
    inference_mode = (opts.get("--type-inference-mode") or [None])[-1]
    for k in opts:
        if k in ("-w", "--warnings") and warning_level in ("all", "normal", "none"): continue
        if k not in ("--backend", "--main-module", "--syntax-module", "--output-definition", "--md-selector", "-I", "--type-inference-mode", "--bison-stack-max-depth"):
            dropped.append(f"{k} {' '.join(opts[k])}")
    if inference_mode not in (None, "simplesub", "checked"):
        dropped.append(f"--type-inference-mode {inference_mode}")
    if src.endswith(".json"): return None, "--outer-parsed-json input has no krust equivalent", None
    info = dict(src=src, backend=backend, main=main, syn=syn or gs, dropped=dropped,
                inference_mode=inference_mode)
    return args, None, info


def krust_proof_kompile_args(case, rec):
    """Translate the definition recipe into the proof-ready compilation used by kprove."""
    args, why, info = krust_kompile_args(case, rec)
    if args is None:
        return None, why, info
    for option, value in (("--backend", "rust"), ("--output-directory", "krust-kompiled-proof")):
        index = args.index(option)
        args[index + 1] = value
    if "--syntax-module" not in args:
        args += ["--syntax-module", info["syn"]]
    args.append("--for-proving")
    return args, None, info


def krust_runtime_kompile_args(args, info):
    """Return the separately accounted Rust compilation required by an LLVM comparison."""
    if info["backend"] != "llvm":
        return None
    runtime_args = list(args)
    runtime_args[runtime_args.index("--backend") + 1] = "rust"
    runtime_args[runtime_args.index("--output-directory") + 1] = "krust-kompiled-runtime"
    return runtime_args


def do_kompile(case, rec, expect_fail):
    """Reference kompile (verbatim recipe) + krust kcompile + KORE comparison."""
    step = dict(step="kompile", ref_cmd=rec["raw"], out=rec["out"])
    rc, out, err, secs, to = sh(
        ["bash", "-c", rec["raw"]],
        case.dir,
        case.remaining(),
        env=reference_process_env(rec["tool"], rec["args"]),
    )
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
    args, why, info = krust_kompile_args(case, rec, expect_fail=expect_fail)
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
    runtime_args = (krust_runtime_kompile_args(args, info)
                    if case.needs_krust_runtime else None)
    if runtime_args is not None:
        # The LLVM KORE is retained for the frontend comparison above. It is not a Rust runtime
        # payload: generate a distinct Rust artifact once and account for that work explicitly.
        case.krust_runtime_definition = "krust-kompiled-runtime"
        runtime_path = f"{case.dir}/{case.krust_runtime_definition}"
        if os.path.exists(runtime_path): shutil.rmtree(runtime_path)
        step["krust_runtime_compile_cmd"] = env_prefix + " ".join(shlex.quote(a) for a in runtime_args)
        rrc, rout, rerr, rsecs, rto = sh(
            runtime_args, case.dir, case.remaining(), env=krust_env
        )
        case.logfile("kompile.krust-runtime.log", rout + "\n--- stderr ---\n" + rerr)
        step["krust_runtime_compile_rc"] = rrc
        step["krust_runtime_compile_seconds"] = round(rsecs, 1)
        if rto or rrc != 0:
            step.update(
                verdict="krust-error",
                stage="kompile",
                reason=("Rust runnable artifact compilation timed out" if rto else
                        f"Rust runnable artifact compilation exited {rrc}"),
                divergence=(rerr or rout)[-1500:],
            )
            return step_record(case, **step)
    else:
        case.krust_runtime_definition = "krust-kompiled"
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


def bison_log_key(input_path):
    return re.sub(r"[^A-Za-z0-9_.-]+", "__", input_path).strip("_") or "input"


def compare_bison_parser_commands(case, row, input_path, reference_command, rust_command,
                                  reference_environment=None, rust_environment=None, **fields):
    """Run two generated-parser consumers and compare their stdout bytes."""
    reference_environment = {
        **reference_process_env(),
        **(reference_environment or {}),
    }
    step = dict(step="bison-parser", stage="bison-parser", test=input_path,
                comparison_policy=row["comparison"], **fields)
    if case.out_of_budget():
        step.update(verdict="reference-error", reason="case budget exhausted before reference parser")
        return step_record(case, **step)
    key = bison_log_key(input_path)
    reference_output = os.path.join(case.log, f"bison__{key}.reference.kore")
    rust_output = os.path.join(case.log, f"bison__{key}.krust.kore")
    reference_stderr = os.path.join(case.log, f"bison__{key}.reference.stderr")
    rust_stderr = os.path.join(case.log, f"bison__{key}.krust.stderr")

    rc, err, seconds, timed_out = sh_to_file(
        reference_command, case.dir, case.remaining(), reference_output,
        env=reference_environment)
    case.logfile(os.path.basename(reference_stderr), err)
    step["ref_rc"] = rc; step["ref_seconds"] = round(seconds, 1)
    if timed_out:
        step.update(verdict="reference-error", reason="reference parser timed out (case budget)")
        return step_record(case, **step)
    if rc != 0:
        step.update(verdict="reference-error", reason=f"reference parser exit {rc}", divergence=err[-1500:])
        return step_record(case, **step)

    if case.out_of_budget():
        step.update(verdict="krust-error", reason="case budget exhausted before krust parser")
        return step_record(case, **step)
    rc, err, seconds, timed_out = sh_to_file(
        rust_command, case.dir, case.remaining(), rust_output, env=rust_environment)
    case.logfile(os.path.basename(rust_stderr), err)
    step["krust_rc"] = rc; step["krust_seconds"] = round(seconds, 1)
    if timed_out:
        step.update(verdict="krust-error", reason="krust parser timed out (case budget)")
        return step_record(case, **step)
    if rc != 0:
        step.update(verdict="krust-error", reason=f"krust parser exit {rc}", divergence=err[-1500:])
        return step_record(case, **step)

    environment = {
        "K_REFERENCE_BISON_PARSER_OUTPUT": reference_output,
        "K_RUST_BISON_PARSER_OUTPUT": rust_output,
        "K_BISON_PARSER_INPUT": f"{case.name}/{input_path}",
        "K_BISON_PARSER_ALLOW_AMBIGUITY": "1" if row["comparison"] == "amb" else "0",
    }
    if case.out_of_budget():
        step.update(verdict="krust-error", reason="case budget exhausted before parser-output comparison")
        return step_record(case, **step)
    trc, tout, terr, comparator_timed_out = run_test_binary_result(
        "generated_bison_parser_outputs_match", environment, case.dir, case.remaining())
    case.logfile(f"bison__{key}.compare.log", tout + "\n--- stderr ---\n" + terr)
    # The comparison test emits simple machine-readable assignments; parse them separately
    # to keep diagnostics robust when libtest adds unrelated output.
    for name, quoted, number in re.findall(r"(bison-parser-[a-z-]+) = (?:'([^']*)'|([0-9]+))$", tout, re.M):
        step[name.replace("-", "_")] = quoted if quoted else int(number)
    if comparator_timed_out:
        step.update(verdict="krust-error", reason="parser-output comparator timed out (case budget)")
    elif trc == 0:
        step.update(verdict="match", comparison="parser stdout bytes" if row["comparison"] == "exact" else "parser KORE modulo same-sort Lblamb flattening and sorting")
    elif trc == 101:
        message = re.search(r"panicked at[^\n]*\n(.*)", tout + terr, re.S)
        text = (message.group(1) if message else (tout + terr)).strip()
        step.update(verdict="mismatch", comparison="generated parser stdout", divergence="\n".join(text.splitlines()[:DIFF_LINES]))
    else:
        step.update(verdict="krust-error", reason=f"parser-output comparator exit {trc}", divergence="\n".join((tout + terr).strip().splitlines()[:DIFF_LINES]))
    return step_record(case, **step)


def run_bison_parsers(case):
    """Execute and semantically compare the generated parser artifacts named by the manifest."""
    row = case.bison_parser
    if row is None:
        return
    if row["artifact"] == "shared-library":
        extension = ".dylib" if sys.platform == "darwin" else ".so"
        consumer = os.path.join(case.dir, row["consumer"])
        reference_directory = case.ref_kompiled or ""
        rust_directory = os.path.join(case.dir, "krust-kompiled")
        reference_library = os.path.join(reference_directory, f"lib{row['library']}{extension}")
        rust_library = os.path.join(rust_directory, f"lib{row['library']}{extension}")
        missing = None
        if not case.ref_kompiled or not os.path.exists(reference_library):
            missing = ("reference-error", "reference generator did not install the parser shared library")
        elif not os.path.exists(rust_library):
            missing = ("krust-error", "krust generator did not install the parser shared library")
        if missing:
            for input_path in row["inputs"]:
                step_record(case, step="bison-parser", stage="bison-parser", test=input_path,
                            comparison_policy=row["comparison"], verdict=missing[0], reason=missing[1])
            return
        consumers = {}
        for side, directory in (("reference", reference_directory), ("krust", rust_directory)):
            output = os.path.join(case.log, f"bison__consumer.{side}")
            command = [os.environ.get("CC", "cc"), consumer, f"-L{directory}",
                       f"-l{row['library']}", "-o", output]
            rc, out, err, seconds, timed_out = sh(command, case.dir, case.remaining())
            case.logfile(f"bison__consumer.{side}.log", out + "\n--- stderr ---\n" + err)
            if timed_out or rc != 0:
                verdict = "reference-error" if side == "reference" else "krust-error"
                reason = f"{side} parser consumer {'timed out' if timed_out else f'exit {rc}'}"
                for input_path in row["inputs"]:
                    step_record(case, step="bison-parser", stage="bison-parser", test=input_path,
                                comparison_policy=row["comparison"], verdict=verdict, reason=reason,
                                divergence=(err or out)[-1500:])
                return
            consumers[side] = (output, directory, command, seconds)
        loader_variable = "DYLD_LIBRARY_PATH" if sys.platform == "darwin" else "LD_LIBRARY_PATH"
        for input_path in row["inputs"]:
            compare_bison_parser_commands(
                case, row, input_path,
                [consumers["reference"][0], input_path],
                [consumers["krust"][0], input_path],
                reference_environment={loader_variable: reference_directory},
                rust_environment={loader_variable: rust_directory},
                ref_compile_cmd=" ".join(shlex.quote(word) for word in consumers["reference"][2]),
                krust_compile_cmd=" ".join(shlex.quote(word) for word in consumers["krust"][2]),
            )
        return

    reference_parser = os.path.join(case.ref_kompiled or "", "parser_PGM")
    rust_parser = os.path.join(case.dir, "krust-kompiled", "parser_PGM")
    for input_path in row["inputs"]:
        if not case.ref_kompiled or not os.path.exists(reference_parser):
            step_record(case, step="bison-parser", stage="bison-parser", test=input_path,
                        comparison_policy=row["comparison"], verdict="reference-error",
                        reason="reference generator did not install a resolvable parser_PGM")
            continue
        if not os.path.exists(rust_parser):
            step_record(case, step="bison-parser", stage="bison-parser", test=input_path,
                        comparison_policy=row["comparison"], verdict="krust-error",
                        reason="krust generator did not install a resolvable parser_PGM")
            continue
        compare_bison_parser_commands(
            case, row, input_path,
            [reference_parser, input_path], [rust_parser, input_path])


def program_sort_fallback(case, prog_path, stdin_path):
    """Ask the reference kast for the KORE of the program to learn its actual sort."""
    if not case.ref_kompiled: return None
    args = [f"{KBIN}/kast", "--definition", case.ref_kompiled, "--output", "kore"]
    args += [prog_path] if prog_path else ["-"]
    rc, out, err, _, _ = sh(
        args,
        case.dir,
        min(120, case.remaining()),
        stdin_path=stdin_path,
        env=reference_process_env("kast", args),
    )
    m = re.match(r"\s*inj\{Sort(\w+)\{\}, ?Sort(\w+)\{\}\}", out)
    if m: return m.group(1)
    m = re.match(r"\s*\\dv\{Sort(\w+)\{\}\}", out)
    if m: return m.group(1)
    return None


def md_selector_args(case, opts=None):
    """The kompile recipe's Markdown selection, unless the step's own recipe selects."""
    if opts and opts.get("--md-selector"): return []
    args = []
    for selector in case.md_selectors: args += ["--md-selector", selector]
    return args


def default_parser_script(case, value):
    """The note for a krun `--parser VALUE` that is K's default program parse, else None.

    krun hands the program file to the parser command and reads KORE (krun script,
    parser_PGM); the default is kparse on that file, and `kast` without --sort or --module
    parses it the same way: at the $PGM sort with the main syntax module. A script that is
    exactly that (optionally `cat "$1" |` into `kast -`, optionally `--output kore`) is what
    krust krun does by default. `cat` (a KORE program) and every other parser stay unsupported.
    """
    path = os.path.join(case.dir, value)
    if not os.path.isfile(path): return None
    lines = [l.strip() for l in open(path, errors="replace").read().splitlines()]
    commands = [l for l in lines if l and not l.startswith("#")]
    if len(commands) != 1: return None
    match = re.fullmatch(r'(?:cat\s+"?\$1"?\s*\|\s*)?kast\s+(.*)', commands[0])
    if not match: return None
    words = match.group(1).split()
    if words[:1] not in (["-"], ["$1"], ['"$1"']): return None
    if words[1:] not in ([], ["--output", "kore"], ["-o", "kore"]): return None
    return f"{value} is `{commands[0]}`, K's default program parse (kast at the $PGM sort with the main syntax module); krust krun parses the program the same way by default"


def krust_krun_args(case, prog, stdin_path, extra, sort, syntax_module):
    args = [KRUST, "krun", "--definition", case.krust_runtime_definition,
            "--sort", sort]
    if prog: args.append(prog)
    elif stdin_path: args.append("-")
    args += extra
    return args


def run_krust_program(case, kind, prog, stdin_path, extra, sort, syntax_module, step):
    args = krust_krun_args(case, prog, stdin_path, extra, sort, syntax_module)
    timeout, capped = case.step_timeout()
    if capped: step["step_budget"] = case.step_budget
    rc, out, err, secs, to = sh(args, case.dir, timeout, stdin_path=stdin_path)
    return args, rc, out, err, secs, to


def run_krust_program_bytes(case, prog, stdin_path, extra, sort, syntax_module, step):
    args = krust_krun_args(case, prog, stdin_path, extra, sort, syntax_module)
    timeout, capped = case.step_timeout()
    if capped: step["step_budget"] = case.step_budget
    rc, out, err, secs, to = sh_bytes(args, case.dir, timeout, stdin_path=stdin_path)
    return args, rc, out, err, secs, to


def krust_timeout_reason(step, tool):
    """The kill reason of a krust program run: its own step budget, or the case budget."""
    if step.get("step_budget"):
        return f"krust {tool} exceeded the step budget ({step['step_budget']:g} s)"
    return f"krust {tool} timed out"


def compare_execution(case, rec, step, kout, kore_output, tag, pattern=""):
    """Compare krust KORE output with the checked-in .out (pretty via kprint modulo C7 with the recipe's
    --pattern text fixing its own `?` variables, or structurally for --output kore)."""
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
    d, compared_as_set, renamed = execution_text_diff(expected, pout, pattern)
    step["comparison"] = "kprint(reference kompiled, krust KORE) text vs .out modulo C7 existential renaming"
    if compared_as_set:
        step["comparison"] = "kprint #Or disjunct multiset vs .out modulo C7 existential renaming (docs/compatibility.md#search-results)"
    if renamed: step["renamed_existentials"] = True
    if d is None: return True
    step["divergence"] = d
    return compare_simplified_kore(case, rec, step, kore_path, tag, expected, pattern)


# C8 (scripts/reference-normalisations.toml): the pinned reference prints a rewrite result that its own
# simplifier has not finished (a residual constraint its smt-lemma axioms make valid, a function
# application over a term whose definedness is open), and krust prints the same pattern simplified.
# Simplifying both results with krust's simplifier makes the represented patterns comparable; the
# evidence is supplementary because it depends on that simplifier, like N15.
SIMPLIFIED_KORE_COMPARISON = (
    "text differs; KORE equal after krust kore-simplify of the reference --output kore result and the krust "
    "result against the reference definition (C8; reference_differential::executed_kore_matches_the_reference_backend "
    "without K_DIFFERENTIAL_DEFINITION)")


C9_STDOUT_COMPARISON = "C9: stdout stream buffer under --io off vs .out"
LIVE_STDOUT_COMPARISON = "committed console stdout under --io on vs .out"
DEFAULT_STDIN_PARSE_DELIMITERS = " \n\t\r"
STDIN_EMPTY_SUCCESSOR = re.compile(
    r"^warning: execution ended with no successor at depth \d+: "
    r"rule (?P<label>STDIN-STREAM\.[^ ]+) applied with an undefined result; "
    r"refuted obligation (?P<obligation>.+)$",
    re.M,
)
PARSE_INPUT_DELIMITERS = re.compile(
    r"Lbl'Hash'parseInput[^\n]*\{\}\(\s*"
    r'\\dv\{SortString\{\}\}\("(?:\\.|[^"\\])*"\),\s*'
    r'\\dv\{SortString\{\}\}\("(?P<delimiters>(?:\\.|[^"\\])*)"\)',
    re.S,
)


def is_bottom_result(source):
    """Recognize the complete bottom pattern printed by krust, not an occurrence inside a result."""
    return re.fullmatch(
        r"\s*\\bottom\{(?:[^{}]|\{[^{}]*\})*\}\(\)\s*",
        source,
    ) is not None


def definition_stdin_delimiters(definition_path):
    """Return the stream parse delimiters generated into definition.kore."""
    try:
        source = Path(definition_path).read_text(errors="replace")
    except OSError:
        return [DEFAULT_STDIN_PARSE_DELIMITERS]
    delimiters = []
    for match in PARSE_INPUT_DELIMITERS.finditer(source):
        try:
            value = json.loads(f'"{match.group("delimiters")}"')
        except json.JSONDecodeError:
            continue
        if value not in delimiters:
            delimiters.append(value)
    return delimiters or [DEFAULT_STDIN_PARSE_DELIMITERS]


def input_has_delimiter_run(stdin_path, delimiter_sets):
    """Whether buffered stdin starts with a delimiter or contains adjacent delimiters."""
    try:
        source = Path(stdin_path).read_text(errors="replace")
    except OSError:
        return False
    for delimiters in delimiter_sets:
        if not delimiters:
            continue
        members = set(delimiters)
        if source[:1] and source[0] in members:
            return True
        if any(left in members and right in members for left, right in zip(source, source[1:])):
            return True
    return False


def c9_stdin_precondition_failure(stderr, stdin_path, definition_path):
    """Return the attributed STDIN-STREAM collapse when C9 cannot translate the input."""
    diagnostic = STDIN_EMPTY_SUCCESSOR.search(stderr)
    if not diagnostic:
        return None
    delimiters = definition_stdin_delimiters(definition_path)
    if not input_has_delimiter_run(stdin_path, delimiters):
        return None
    return diagnostic.group("label"), diagnostic.group("obligation").strip()


def stdout_bytes_divergence(expected, actual):
    limit = min(len(expected), len(actual))
    offset = next((index for index in range(limit) if expected[index] != actual[index]), limit)
    return (
        f"stdout bytes differ at offset {offset}: "
        f"expected {expected[max(0, offset - 24):offset + 80]!r}; "
        f"krust buffer {actual[max(0, offset - 24):offset + 80]!r}"
    )


def compare_stdout_buffer(case, step, kore_path, expected_path):
    """C9: structurally extract one unconstrained stdout buffer and compare its exact bytes."""
    rc, out, err, timed_out = run_test_binary_result(
        "conformance_stdout_stream_buffers",
        {"K_RUST_EXECUTION": kore_path},
        case.dir,
        case.remaining(),
    )
    step["comparison"] = C9_STDOUT_COMPARISON
    if timed_out:
        step.update(verdict="krust-error", reason="C9 KORE extraction timed out")
        return
    if rc != 0:
        message = re.search(r"panicked at[^\n]*\n(.*)", out + err, re.S)
        detail = (message.group(1) if message else out + err).strip()
        step.update(
            verdict="krust-error",
            reason="C9 could not structurally inspect the krust KORE result",
            divergence="\n".join(detail.splitlines()[:DIFF_LINES]),
        )
        return
    # libtest prefixes output written while a test is running with `test NAME ... `.
    match = re.search(r"c9-stdout-report = (.+)$", out, re.M)
    if not match:
        step.update(
            verdict="krust-error",
            reason="C9 structural comparator returned no stdout report",
            divergence=output_excerpt(out + err),
        )
        return
    try:
        report = json.loads(match.group(1))
        leaves = report["leaves"]
        terminal = [leaf for leaf in leaves if not leaf["constraints"]]
    except (json.JSONDecodeError, KeyError, TypeError) as error:
        step.update(
            verdict="krust-error",
            reason=f"C9 structural comparator returned an invalid stdout report: {error}",
            divergence=output_excerpt(match.group(1)),
        )
        return
    step["stdout_leaf_count"] = len(leaves)
    step["stdout_terminal_leaf_count"] = len(terminal)
    if len(leaves) != 1 or len(terminal) != 1 or len(terminal[0].get("buffers", [])) != 1:
        summary = [
            {
                "buffers": leaf.get("buffers", []),
                "constraints": leaf.get("constraints", []),
            }
            for leaf in leaves
        ]
        step.update(
            verdict="mismatch",
            reason="C9 requires exactly one execution leaf, unconstrained and with exactly one stdout stream buffer",
            divergence=output_excerpt(json.dumps(summary, ensure_ascii=False, indent=2)),
        )
        return
    expected = Path(expected_path).read_bytes()
    try:
        actual = bytes(terminal[0]["buffers"][0])
    except (TypeError, ValueError):
        step.update(
            verdict="krust-error",
            reason="C9 structural comparator returned an invalid byte buffer",
            divergence=output_excerpt(json.dumps(terminal[0]["buffers"][0])),
        )
        return
    step["stdout_buffer_bytes"] = len(actual)
    if expected == actual:
        step["verdict"] = "match"
    else:
        step.update(
            verdict="mismatch",
            reason="stdout stream buffer differs from the checked-in console output",
            divergence=stdout_bytes_divergence(expected, actual),
        )


def live_io_options(extra):
    """Select krust's pre-buffered committed live-IO mode for an ordinary recipe."""
    translated = []
    index = 0
    while index < len(extra):
        if extra[index] == "--io" and index + 1 < len(extra):
            index += 2
            continue
        translated.append(extra[index])
        index += 1
    translated += ["--io", "on", "--output", "none"]
    return translated


def compare_live_console_output(case, step, prog, stdin_path, extra, sort, syntax_module,
                                expected_path, tag, primary=False):
    """Run one ordinary committed trace and compare its console stdout byte for byte."""
    args, rc, out, err, secs, timed_out = run_krust_program_bytes(
        case, prog, stdin_path, live_io_options(extra), sort, syntax_module, step
    )
    prefix = "" if primary else "live_"
    step[f"{prefix}krust_cmd"] = " ".join(shlex.quote(argument) for argument in args)
    step[f"{prefix}krust_rc"] = rc
    step[f"{prefix}krust_seconds"] = round(secs, 1)
    case.binary_logfile(f"{tag}.krust.live.stdout", out)
    case.logfile(f"{tag}.krust.live.stderr", err)
    step["comparison"] = LIVE_STDOUT_COMPARISON
    if timed_out:
        step.update(verdict="krust-error", stage="krun", reason=krust_timeout_reason(step, "krun --io on"))
        return
    if rc != 0:
        step.update(
            verdict="krust-error",
            stage="krun",
            reason=f"krust krun --io on exited {rc} where the reference recipe requires successful completion",
            divergence=output_excerpt(err),
        )
        return
    expected = Path(expected_path).read_bytes()
    step["live_stdout_bytes"] = len(out)
    if out == expected:
        step["verdict"] = "match"
    else:
        step.update(
            verdict="mismatch",
            reason="committed console stdout differs from the checked-in console output",
            divergence=stdout_bytes_divergence(expected, out),
        )


def reference_kore_args(rec):
    """The recipe's tool argv with its output format replaced by --output kore, or None when the recipe
    needs a shell expansion or redirection the driver does not replay (as confirmed_reference_outcome)."""
    if any(re.search(r'\$|`|[<>]', arg) for arg in rec["args"]):
        return None
    args = []
    skip = False
    for arg in rec["args"]:
        if skip: skip = False; continue
        if arg in ("--output", "-o"): skip = True; continue
        if arg.startswith("--output="): continue
        args.append(arg)
    return [f"{KBIN}/{rec['tool']}", *args, "--output", "kore"]


def simplify_kore(case, source, target):
    """Run krust kore-simplify on `source` against the reference kompiled definition and main module."""
    args = [KRUST, "kore-simplify", f"{case.ref_kompiled}/definition.kore", "--module", case.main_module,
            "--pattern", source, "--output", target]
    rc, out, err, secs, to = sh(args, case.dir, case.remaining())
    if to: return False, "timed out", secs
    if rc != 0 or not os.path.exists(target):
        return False, f"exit {rc}: " + " ".join((err or out).strip().splitlines()[:3])[:600], secs
    return True, "", secs


def compare_simplified_kore(case, rec, step, kore_path, tag, expected, pattern=""):
    """C8: after the C7 text comparison failed, re-run the reference recipe with --output kore, simplify both
    that result and krust's with `krust kore-simplify` (reference kompiled definition, main module), and compare
    the simplified patterns with reference_differential::executed_kore_matches_the_reference_backend without
    K_DIFFERENTIAL_DEFINITION (N4 renaming applies, N15 does not). Returns True only when every stage succeeded
    and the comparator accepted the pair; the step then carries SIMPLIFIED_KORE_COMPARISON and keeps the text
    difference as text_divergence. A reference re-run that produces no result returns REFERENCE_ERROR. Every
    other unsuccessful comparison keeps the text mismatch. All unsuccessful outcomes record why in
    simplified_kore_divergence."""
    def not_compared(reason):
        step["simplified_kore_divergence"] = reason
        return False
    definition = f"{case.ref_kompiled}/definition.kore" if case.ref_kompiled else None
    if not definition or not os.path.exists(definition) or not case.main_module:
        return not_compared("not compared: no reference kompiled definition or main module")
    if case.out_of_budget():
        return not_compared("not compared: no remaining budget for the reference --output kore re-run")
    args = reference_kore_args(rec)
    if args is None:
        return not_compared("not compared: reference recipe needs an unsupported shell expansion or redirection")
    stdin_path = f"{case.dir}/{rec['stdin']}" if rec.get("stdin") else None
    rc, out, err, secs, to = sh(
        args,
        case.dir,
        case.remaining(),
        stdin_path=stdin_path,
        env=reference_process_env(rec["tool"], rec["args"]),
    )
    step["reference_kore_cmd"] = " ".join(shlex.quote(a) for a in args)
    step["reference_kore_rc"] = rc
    step["reference_kore_seconds"] = round(secs, 1)
    case.logfile(f"{tag}.reference-kore.log", out + "\n--- stderr ---\n" + err)
    if to or rc != 0 or not out.strip():
        divergence = "not compared: reference --output kore re-run " + (
            "timed out" if to else f"exited {rc}" + (" with empty stdout" if not out.strip() else "")
        )
        step["simplified_kore_divergence"] = divergence
        step["reference_kore_error"] = output_excerpt(err)
        step["reference_error_reason"] = reference_failure_reason(
            "reference --output kore re-run failed",
            rc,
            to,
            err,
            empty_output=(not to and rc == 0 and not out.strip()),
        )
        return REFERENCE_ERROR
    reference_kore = f"{case.log}/{tag}.reference.kore"
    case.logfile(f"{tag}.reference.kore", out)
    # The checked-in .out stays the oracle: the re-run's result must still print as the .out, otherwise the
    # oracle is stale and confirm_oracle reports it; port agreement with a stale oracle's live output is not a pass.
    prc, pout, perr = kprint(case, reference_kore)
    if prc != 0:
        return not_compared("not compared: kprint failed on the reference --output kore result: " + (perr or pout)[:800])
    reproduces, _, _ = execution_text_diff(expected, pout, pattern)
    step["reference_kore_reproduces_out"] = reproduces is None
    if reproduces is not None:
        return not_compared("not compared: kprint of the reference --output kore result does not reproduce the checked-in .out")
    simplified = {}
    for side, source in (("reference", reference_kore), ("krust", kore_path)):
        if case.out_of_budget():
            return not_compared(f"not compared: no remaining budget to simplify the {side} KORE")
        simplified[side] = f"{case.log}/{tag}.{side}.simplified.kore"
        ok, message, secs = simplify_kore(case, source, simplified[side])
        step[f"{side}_simplify_seconds"] = round(secs, 1)
        if not ok:
            return not_compared(f"not compared: krust kore-simplify failed on the {side} KORE: {message}")
    comparison_environment = {
        "K_REFERENCE_EXECUTION": simplified["reference"],
        "K_RUST_EXECUTION": simplified["krust"],
        "K_DIFFERENTIAL_MODULE": case.main_module,
    }
    trc, tout, terr, timed_out = run_test_binary_result(
        "executed_kore_matches_the_reference_backend", comparison_environment, case.dir)
    if trc == 0 and not timed_out:
        step["comparison"] = SIMPLIFIED_KORE_COMPARISON
        step["simplified_kore_equal"] = True
        step["text_divergence"] = step.pop("divergence")
        return True
    if timed_out:
        return not_compared("simplified KORE not compared: the comparator timed out")
    msg = re.search(r"panicked at[^\n]*\n(.*)", tout + terr, re.S)
    return not_compared("simplified KORE differ: " + "\n".join(
        ((msg.group(1) if msg else tout + terr).strip()).splitlines()[:DIFF_LINES]))


def confirm_oracle(case, rec, step):
    if case.out_of_budget():
        step["oracle_confirmed"] = "not-run (budget)"; return
    direct = not rec.get("filters") and not rec.get("actual_file") and not any(
        re.search(r'\$|`|[<>]', arg) for arg in rec["args"]
    )
    args = [f"{KBIN}/{rec['tool']}", *rec["args"]] if direct else ["bash", "-c", rec["raw"]]
    stdin_path = f"{case.dir}/{rec['stdin']}" if direct and rec.get("stdin") else None
    rc, out, err, secs, to = sh(
        args,
        case.dir,
        case.remaining(),
        stdin_path=stdin_path,
        env=reference_process_env(rec["tool"], rec["args"]),
    )
    step["oracle_cmd"] = " ".join(shlex.quote(a) for a in args)
    if direct:
        step["oracle_tool_rc"] = rc
    step["oracle_seconds"] = round(secs, 1)
    expected = expected_output(case, rec)
    tool_failed = to or (direct and rc != 0) or (
        not direct and rc != 0 and is_reference_crash(err)
    )
    if tool_failed:
        step["oracle_confirmed"] = "not-run (reference crash)"
        step["oracle_output"] = output_excerpt(err or out)
        if step.get("verdict") != "reference-error":
            step["verdict"] = "reference-error"
            step["reason"] = reference_failure_reason(
                "reference recipe failed to run", rc, to, err or out
            )
        return
    if not direct:
        step["oracle_confirmed"] = (rc == 0 and not to)
        if rc == 0:
            return
        difference = output_excerpt(out + err)
    elif expected is None:
        step["oracle_confirmed"] = False
        difference = "checked-in output is unavailable"
    else:
        difference = first_diff(expected, out)
        step["oracle_confirmed"] = difference is None
        if difference is None:
            return
    step["oracle_output"] = difference
    step["oracle_stale"] = True
    if step.get("verdict") != "reference-error":
        step["verdict"] = "reference-error"
        step["reason"] = "checked-in .out is not reproduced by the pinned reference toolchain; krust mismatch recorded against a stale oracle"


def expected_output(case, rec):
    path = Path(case.dir) / rec['out'] if rec.get('out') else None
    return path.read_text(errors='replace') if path and path.is_file() else None


def rejection_family(text, tool):
    # Only known tool failures establish a family. Generic compiler/error headings
    # and crashes must never be mistaken for an intended parser/config rejection.
    if is_reference_crash(text):
        return None
    if tool == 'krun' and re.search(
        r'Configuration variable missing:|missing required configuration variables? |definition has no configuration variable ', text):
        return 'configuration-variable'
    if tool == 'kast' and (re.search(r'^\[Error\] Inner Parser:', text, re.M)
                           or re.search(r'could not parse program as .+ with module .+:', text)):
        return 'program-parse'
    return None


def confirmed_reference_outcome(case, rec, step, tag):
    if case.out_of_budget():
        step.update(verdict='reference-error', reason='no remaining budget to confirm reference outcome')
        return None
    # The recipe verifies the checked-in expected output, including its filters;
    # its final status is not necessarily the status of the K tool in a pipeline.
    rc, out, err, secs, timed_out = sh(
        ['bash', '-c', rec['raw']], case.dir, case.remaining(),
        env=reference_process_env(rec['tool'], rec['args'])
    )
    step.update(reference_recipe_rc=rc, reference_recipe_seconds=round(secs, 1))
    case.logfile(f'{tag}.reference-recipe.log', out + '\n--- stderr ---\n' + err)
    if timed_out or rc != 0:
        step.update(verdict='reference-error', reason='reference recipe did not reproduce the expected outcome')
        return None
    if case.out_of_budget():
        step.update(verdict='reference-error', reason='no remaining budget to record reference tool status')
        return None
    # Only replay statically decoded argv. Shell expansions need an explicit
    # adapter rather than accidentally treating their spelling as a literal arg.
    if any(re.search(r'\$|`|[<>]', arg) for arg in rec['args']):
        step.update(verdict='reference-error', reason='reference tool status requires an unsupported shell expansion or redirection')
        return None
    args = [f"{KBIN}/{rec['tool']}", *rec['args']]
    stdin_path = str(Path(case.dir) / rec['stdin']) if rec.get('stdin') else None
    rc, out, err, secs, timed_out = sh(
        args,
        case.dir,
        case.remaining(),
        stdin_path=stdin_path,
        env=reference_process_env(rec['tool'], rec['args']),
    )
    step.update(reference_tool_cmd=' '.join(shlex.quote(a) for a in args),
                reference_tool_rc=rc, reference_tool_seconds=round(secs, 1))
    case.logfile(f'{tag}.reference-tool.log', out + '\n--- stderr ---\n' + err)
    if timed_out or rc < 0 or rc in (126, 127):
        step.update(verdict='reference-error', reason='reference tool failed to produce an ordinary outcome')
        return None
    return rc, out, err


def compare_expected_rejection(case, rec, step, rc, out, err, tag):
    expected = expected_output(case, rec)
    if expected is None or not re.search(r'^\[Error\]', expected, re.M):
        return False
    step['expected_outcome'] = 'rejection'
    step['stage'] = rec['tool']
    reference = confirmed_reference_outcome(case, rec, step, tag)
    if reference is None:
        return True
    ref_rc, ref_out, ref_err = reference
    expected_family = rejection_family(expected, rec['tool'])
    reference_family = rejection_family(ref_out + '\n' + ref_err, rec['tool'])
    actual_family = rejection_family(out + '\n' + err, rec['tool'])
    step['expected_rejection_family'] = expected_family or 'unrecognized'
    step['reference_rejection_family'] = reference_family or 'unrecognized'
    step['krust_rejection_family'] = actual_family or 'unrecognized'
    if ref_rc == 0 or not expected_family or reference_family != expected_family:
        step.update(verdict='reference-error', reason='reference tool did not confirm a recognized expected rejection')
    elif rc == 0:
        step.update(verdict='mismatch', reason='krust accepts an input the reference rejects')
    elif rc < 0 or rc in (126, 127):
        step.update(verdict='krust-error', reason='krust terminated without an ordinary rejection')
    elif actual_family != expected_family:
        step.update(verdict='mismatch', reason='krust failure is not the expected rejection family', divergence=(err or out)[-1200:])
    else:
        step.update(verdict='match', comparison='confirmed rejection and diagnostic family; raw diagnostics retained')
    return True


def compare_program_status(case, rec, step, rc, tag):
    # Zero is ordinary success. Nonzero can be a successful program's getExitCode
    # value, but needs a successful reference recipe and the same direct status.
    if rc == 0:
        return True
    if rc < 0 or rc in (126, 127):
        step.update(verdict='krust-error', reason='krust did not finish with an ordinary program status')
        return False
    reference = confirmed_reference_outcome(case, rec, step, tag)
    if reference is None:
        return False
    if reference[0] != rc:
        step.update(verdict='mismatch', reason=f'program exit status differs: krust {rc}, reference {reference[0]}')
        return False
    return True


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
    pattern_values = opts.get("--pattern", [])
    pattern_is_valid = len(pattern_values) == 1 and "--search-pattern" not in opts
    pattern = pattern_values[-1] if pattern_is_valid else ""
    if len(pattern_values) > 1:
        unsupported.append("repeated --pattern")
    if pattern_values and "--search-pattern" in opts:
        unsupported.append("--pattern conflicts with --search-pattern")
    search_mode = None
    for f in flags:
        if f in ("--search", "--search-all", "--search-final", "--search-one-step", "--search-one-or-more-steps"):
            # krust spells the bare --search default as --search-final. A mode repeated in one
            # recipe is the reference's idempotent boolean flag and collapses; two different
            # modes have no single krust equivalent.
            mode = "--search-final" if f == "--search" else f
            if search_mode is None: search_mode = mode; extra.append(mode)
            elif search_mode != mode: unsupported.append(f"{search_mode} conflicts with {mode}")
        elif f in ("--no-exc-wrap", "--no-pattern", "--profile", "--debug", "--no-expand-macros"): pass
        elif f in ("--help", "--version", "--dry-run", "--proof-hint", "--term"): unsupported.append(f)
        else: unsupported.append(f)
    for k, vs in opts.items():
        v = vs[-1]
        if k in ("--definition", "-d", "--smt", "--smt-prelude", "--warnings", "-w", "--md-selector"): continue
        if k == "--depth": extra += ["--depth", v]
        elif k == "--bound": extra += ["--search-bound", v]
        elif k == "--io": extra += ["--io", v]
        elif k == "--pattern":
            if pattern_is_valid: extra += ["--pattern", v]
        elif k == "-c":
            for c in vs: extra += ["-c", c]
        elif k in ("--output", "-o"):
            if v == "kore": kore_output = True
            elif v == "pretty": pass
            elif v == "none": completion_only = True
            else: unsupported.append(f"{k} {v}")
        elif k == "-I":
            for d in vs: extra += ["-I", d]
        elif k == "--parser":
            equivalent = default_parser_script(case, v)
            if equivalent: step["parser"] = equivalent
            else: unsupported.append(f"{k} {v}")
        else: unsupported.append(f"{k} {v}")
    # A .search recipe runs KSEARCH, which is `krun --search-all`
    # (k/k-distribution/include/kframework/ktest-common.mak:23), so the mode usually comes from
    # the recipe itself; supply the default only when the recipe selected none.
    if search_file and search_mode is None: search_mode = "--search-all"; extra.append(search_mode)
    if unsupported:
        step.update(verdict="krust-unsupported", reason="reference krun flags with no krust equivalent: " + " ".join(unsupported))
        return step_record(case, **step)
    expected_path = f"{case.dir}/{rec['out']}" if rec.get("out") else None
    nonempty_expected_output = bool(
        expected_path and os.path.isfile(expected_path) and os.path.getsize(expected_path) > 0
    )
    explicit_io = (opts.get("--io") or [None])[-1]
    c9_stdout = completion_only and nonempty_expected_output and explicit_io != "on"
    live_stdout = completion_only and nonempty_expected_output and explicit_io == "on"
    if c9_stdout and explicit_io is None:
        extra += ["--io", "off"]
    stdin_path = f"{case.dir}/{rec['stdin']}" if rec["stdin"] and os.path.exists(f"{case.dir}/{rec['stdin']}") else None
    if stdin_path: step["stdin"] = rec["stdin"]
    sort = case.pgm_sort or "KItem"
    if live_stdout:
        step["stage"] = "krun"
        compare_live_console_output(
            case, step, prog, stdin_path, extra, sort, case.syntax_module,
            expected_path, tag, primary=True,
        )
        return step_record(case, **step)
    args, rc, out, err, secs, to = run_krust_program(case, "krun", prog, stdin_path, extra, sort, case.syntax_module, step)
    step["krust_cmd"] = " ".join(shlex.quote(a) for a in args); step["krust_rc"] = rc; step["krust_seconds"] = round(secs, 1)
    case.logfile(f"{tag}.krust.log", out + "\n--- stderr ---\n" + err)
    if to:
        step.update(verdict="krust-error", stage="krun", reason=krust_timeout_reason(step, "krun")); return step_record(case, **step)
    if compare_expected_rejection(case, rec, step, rc, out, err, tag):
        return step_record(case, **step)
    if not out.strip():
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
                elif not out2.strip():
                    step["fallback_verdict"] = "krust-error"; step["fallback_stage"] = classify_error(err2)
                    step["fallback_divergence"] = (err2 or out2)[-800:]
                else:
                    sub = {k: v for k, v in step.items() if k != "divergence"}
                    ok = compare_execution(case, rec, sub, out2, kore_output, tag + ".fallback", pattern)
                    step["fallback_stage"] = "search" if "--search" in " ".join(extra) else "krun"
                    step["fallback_verdict"] = (
                        "reference-error" if ok is REFERENCE_ERROR else
                        "match" if ok else ("mismatch" if ok is False else "skipped-with-reason")
                    )
                    if ok is False and sub.get("divergence"): step["fallback_divergence"] = sub["divergence"]
                    if sub.get("renamed_existentials"): step["fallback_renamed_existentials"] = True
                    if sub.get("comparison"): step["comparison"] = sub["comparison"]
        return step_record(case, **step)
    step["stage"] = "search" if any(x.startswith("--search") for x in extra) else "krun"
    if completion_only:
        if rc != 0:
            step.update(verdict="krust-error", stage="krun", reason=f"krust krun exited {rc} where the reference recipe requires successful completion")
            return step_record(case, **step)
        case.logfile(f"{tag}.krust.kore", out)
        if is_bottom_result(out):
            stdin_precondition = None
            if c9_stdout and stdin_path:
                stdin_precondition = c9_stdin_precondition_failure(
                    err,
                    stdin_path,
                    os.path.join(case.dir, "krust-kompiled", "definition.kore"),
                )
            if stdin_precondition:
                label, obligation = stdin_precondition
                step["c9_stdin_precondition"] = (
                    f"{label} is undefined on the buffered input ({obligation})"
                )
                step["c9_result"] = out.strip()
                if explicit_io is None:
                    compare_live_console_output(
                        case, step, prog, stdin_path, extra, sort, case.syntax_module,
                        expected_path, tag,
                    )
                    return step_record(case, **step)
                step.update(
                    verdict="skipped-with-reason",
                    stage="krun",
                    reason=(
                        f"C9 stdin precondition: {label} is undefined on the buffered input "
                        f"({obligation}); the explicit --io off recipe supplies no live oracle"
                    ),
                    divergence=out,
                )
                return step_record(case, **step)
            step.update(
                verdict="krust-error",
                stage="krun",
                reason="krust execution produced bottom where the reference recipe requires successful completion",
                divergence=out,
            )
            return step_record(case, **step)
        if c9_stdout:
            compare_stdout_buffer(case, step, f"{case.log}/{tag}.krust.kore", expected_path)
            return step_record(case, **step)
        if nonempty_expected_output:
            step.update(
                verdict="krust-unsupported",
                reason="a non-empty .out cannot be accepted by completion only and explicit --io on is outside C9",
            )
            return step_record(case, **step)
        step.update(verdict="match", comparison="completion only: the reference recipe runs with --output none, so only successful termination is compared")
        return step_record(case, **step)
    if not compare_program_status(case, rec, step, rc, tag):
        return step_record(case, **step)
    ok = compare_execution(case, rec, step, out, kore_output, tag, pattern)
    if ok is None:
        step.update(verdict="skipped-with-reason", reason="no checked-in .out for this test")
    elif ok is REFERENCE_ERROR:
        step["verdict"] = "reference-error"
        step["reason"] = step["reference_error_reason"]
        confirm_oracle(case, rec, step)
    elif ok:
        step["verdict"] = "match"
    else:
        step["verdict"] = "mismatch"
        confirm_oracle(case, rec, step)
    return step_record(case, **step)


def krust_kast_args(case, module, sort, outfmt, expr, prog):
    args = [KRUST, "kast", case.def_file, "--module", module, "--sort", sort, "-I", ".", "--builtin-directory", BUILTIN,
            "-o", "json" if outfmt == "json" else "text"] + md_selector_args(case)
    if expr is not None: args += ["-e", expr]
    elif prog: args.append(prog)
    return args


def do_kast(case, rec):
    pos, opts, flags = parse_opts(rec["args"], KAST_VALUE_OPTS)
    prog = pos[0] if pos else None
    tag = os.path.basename(prog) if prog else "kast"
    step = dict(step="kast", test=prog, ref_cmd=rec["raw"], out=rec["out"])
    if not case.ref_kompiled:
        step.update(verdict="skipped-with-reason", reason="no reference kompiled definition"); return step_record(case, **step)
    generator_flags = [flag for flag in ("--gen-parser", "--gen-glr-parser") if flag in flags]
    unsupported = [f for f in flags if f not in ("--no-exc-wrap", "--debug", "--gen-parser", "--gen-glr-parser")]
    inp = (opts.get("--input") or opts.get("-i") or ["program"])[-1]
    outfmt = (opts.get("--output") or opts.get("-o") or ["kast"])[-1]
    if inp != "program": unsupported.append(f"--input {inp}")
    if outfmt not in ("kast", "json"): unsupported.append(f"--output {outfmt}")
    for k in opts:
        if k not in ("--definition", "-d", "--sort", "-s", "--module", "-m", "--input", "-i", "--output", "-o", "--expression", "-e", "--warnings", "-w", "--bison-stack-max-depth"):
            unsupported.append(f"{k} {' '.join(opts[k])}")
    expand = "--expand-macros" in flags
    unsupported = [u for u in unsupported if u not in ("--expand-macros", "--no-substitution-filtering")]
    sort = (opts.get("--sort") or opts.get("-s") or [case.pgm_sort or "KItem"])[-1]
    module = (opts.get("--module") or opts.get("-m") or [case.syntax_module])[-1]
    expr = (opts.get("--expression") or opts.get("-e") or [None])[-1]
    if generator_flags:
        if len(generator_flags) != 1:
            unsupported.append(" ".join(generator_flags))
        if not prog:
            unsupported.append("generated parser output path")
        rust_parser = os.path.join(case.log, "kast-bison.krust-parser")
        args = [KRUST, "kast", case.def_file, "--module", module, "--sort", sort,
                "-I", ".", "--builtin-directory", BUILTIN] + md_selector_args(case)
        args.append(generator_flags[0])
        if opts.get("--bison-stack-max-depth"):
            args += ["--bison-stack-max-depth", opts["--bison-stack-max-depth"][-1]]
        args.append(rust_parser)
        step["krust_cmd"] = " ".join(shlex.quote(a) for a in args)
        step["stage"] = "bison-parser"
        if unsupported:
            step.update(verdict="krust-unsupported", reason="reference kast flags with no krust equivalent: " + " ".join(unsupported))
            return step_record(case, **step)
        rc, out, err, secs, to = sh(["bash", "-c", rec["raw"]], case.dir, case.remaining())
        case.logfile("kast-bison.reference-generation.log", out + "\n--- stderr ---\n" + err)
        step["ref_rc"] = rc; step["ref_seconds"] = round(secs, 1)
        reference_parser = os.path.join(case.dir, prog)
        if to:
            step.update(verdict="reference-error", reason="reference parser generation timed out")
            return step_record(case, **step)
        if rc != 0:
            step.update(verdict="reference-error", reason=f"reference parser generation exit {rc}", divergence=(err or out)[-1500:])
            return step_record(case, **step)
        if not os.path.exists(reference_parser):
            step.update(verdict="reference-error", reason="reference kast did not write the generated parser")
            return step_record(case, **step)
        rc, out, err, secs, to = sh(args, case.dir, case.remaining())
        case.logfile("kast-bison.krust-generation.log", out + "\n--- stderr ---\n" + err)
        step["krust_rc"] = rc; step["krust_seconds"] = round(secs, 1)
        if to:
            step.update(verdict="krust-error", reason="krust parser generation timed out")
            return step_record(case, **step)
        if rc != 0:
            step.update(verdict="krust-error", reason=f"krust parser generation exit {rc}", divergence=(err or out)[-1500:])
            return step_record(case, **step)
        if not os.path.exists(rust_parser):
            step.update(verdict="krust-error", reason="krust kast did not write the generated parser")
            return step_record(case, **step)
        case.kast_reference_parser = reference_parser
        case.kast_rust_parser = rust_parser
        step.update(verdict="match", comparison="both kast commands generated a parser executable")
        return step_record(case, **step)
    args = krust_kast_args(case, module, sort, outfmt, expr, prog)
    step["krust_cmd"] = " ".join(shlex.quote(a) for a in args)
    if unsupported:
        step.update(verdict="krust-unsupported", reason="reference kast flags with no krust equivalent: " + " ".join(unsupported))
        return step_record(case, **step)
    rc, out, err, secs, to = sh(args, case.dir, case.remaining())
    case.logfile(f"{tag}.krust.log", out + "\n--- stderr ---\n" + err)
    step["krust_rc"] = rc; step["krust_seconds"] = round(secs, 1)
    if to: step.update(verdict="krust-error", stage="kast", reason="timed out"); return step_record(case, **step)
    if compare_expected_rejection(case, rec, step, rc, out, err, tag):
        return step_record(case, **step)
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
        rrc, rout, rerr, _, _ = sh(
            rargs,
            case.dir,
            min(120, case.remaining()),
            env=reference_process_env("kast", rargs),
        )
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
    # K prints the detail of a diagnostic (Source, Location, the quoted source line and its
    # caret) tab-indented under the [Error] line; a quoted rule may contain `<k>`, so the
    # verdict is read from the diagnostic lines alone.
    diagnostic = "\n".join(l for l in expected.splitlines() if not l.startswith("\t"))
    if body == "#Top" or (body == "" and "#Top" in expected): exp = "proven"
    elif re.search(r"\[Error\] Prover|#Not|#Ceil|#Equals|<generatedTop>|<k>", diagnostic): exp = "not-proven"
    elif "[Error]" in diagnostic: exp = "error"
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


def krust_kprove_args(case, rec):
    """Translate a kprove recipe against the separately prepared definition."""
    pos, opts, flags = parse_opts(rec["args"], KPROVE_VALUE_OPTS)
    spec = pos[0] if pos else None
    if not spec:
        return None, "no specification source in kprove recipe", None
    unsupported = [f for f in flags if f not in ("--no-exc-wrap", "--debug")]
    extra = []
    for k, vs in opts.items():
        v = vs[-1]
        if k in ("--definition", "-d", "--smt", "--smt-prelude", "--warnings", "-w", "--type-inference-mode", "--profile-rule-parsing", "--log-level"): continue
        if k == "--md-selector":
            for value in vs: extra += ["--md-selector", value]
        elif k == "--depth": extra += ["--depth", v]
        elif k in ("--claim", "--claims"):
            for value in vs:
                for claim in value.split(","): extra += ["--claim", claim]
        elif k in ("--exclude", "--trusted"):
            for value in vs:
                for claim in value.split(","): extra += [k, claim]
        elif k == "-I":
            for value in vs: extra += ["-I", value]
        elif k in ("--spec-module", "--def-module"): continue
        else: unsupported.append(f"{k} {v}")
    spec_module = (opts.get("--spec-module") or [os.path.basename(spec).rsplit(".", 1)[0].upper()])[-1]
    def_module = (opts.get("--def-module") or [case.main_module])[-1]
    args = [KRUST, "kprove", spec, "--compiled-definition", "krust-kompiled-proof",
            "--main-module", spec_module, "--definition-module", def_module, "-I", ".",
            "--builtin-directory", BUILTIN] + extra
    inference_mode = (opts.get("--type-inference-mode") or [None])[-1]
    info = dict(spec=spec, spec_module=spec_module, def_module=def_module,
                inference_mode=inference_mode, unsupported=unsupported)
    return args, None, info


def do_kprove(case, rec):
    args, why, info = krust_kprove_args(case, rec)
    spec = info["spec"] if info else None
    tag = os.path.basename(spec) if spec else "kprove"
    step = dict(step="kprove", test=spec, ref_cmd=rec["raw"], out=rec["out"])
    if not case.ref_kompiled or not spec:
        step.update(verdict="skipped-with-reason", reason=why or "no reference kompiled definition"); return step_record(case, **step)
    compile_args, compile_why, compile_info = krust_proof_kompile_args(case, case.kompile_recipe) if case.kompile_recipe else (None, "no kompile recipe", None)
    unsupported = info["unsupported"]
    krust_env = ({"KRUST_TYPE_INFERENCE_MODE": "checked"}
                 if info["inference_mode"] == "checked" else None)
    env_prefix = "KRUST_TYPE_INFERENCE_MODE=checked " if krust_env else ""
    if unsupported:
        step.update(verdict="krust-unsupported", reason="reference kprove flags with no krust equivalent: " + " ".join(unsupported))
        return step_record(case, **step)
    if compile_args is None:
        step.update(verdict="krust-unsupported", reason=f"proof-ready definition cannot be compiled: {compile_why}")
        return step_record(case, **step)
    outp = f"{case.dir}/{rec['out']}" if rec["out"] else None
    expected = open(outp, errors="replace").read() if outp and os.path.exists(outp) else None
    if expected is None:
        step.update(verdict="skipped-with-reason", reason="no checked-in .out"); return step_record(case, **step)
    commands = []
    if not case.proof_compile_attempted:
        compile_env = ({"KRUST_TYPE_INFERENCE_MODE": "checked"}
                       if compile_info["inference_mode"] == "checked" else None)
        compile_prefix = "KRUST_TYPE_INFERENCE_MODE=checked " if compile_env else ""
        commands.append(compile_prefix + " ".join(shlex.quote(a) for a in compile_args))
        case.proof_compile_attempted = True
        proof_directory = f"{case.dir}/krust-kompiled-proof"
        if os.path.exists(proof_directory): shutil.rmtree(proof_directory)
        crc, cout, cerr, csecs, cto = sh(compile_args, case.dir, case.remaining(), env=compile_env)
        case.logfile("proof-kompile.krust.log", cout + "\n--- stderr ---\n" + cerr)
        step["proof_kompile_rc"] = crc
        step["proof_kompile_seconds"] = round(csecs, 1)
        if cto:
            case.proof_compile_failure = "krust proof-ready kcompile timed out (case budget)"
        elif crc != 0:
            case.proof_compile_failure = (cerr or cout)[-1200:]
        else:
            case.proof_definition_ready = True
    commands.append(env_prefix + " ".join(shlex.quote(a) for a in args))
    step["krust_cmd"] = " && ".join(commands)
    if not case.proof_definition_ready:
        failure = case.proof_compile_failure or "proof-ready definition compilation failed"
        step.update(verdict="krust-error", stage=classify_error(failure), reason="krust proof-ready kcompile failed", divergence=failure)
        return step_record(case, **step)
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


def clean_case_artifacts(case):
    """Remove generated definitions anywhere below one scratch case before make expansion."""
    case_root = Path(case.dir).resolve()
    for current, directories, _ in os.walk(case.dir, topdown=True):
        for name in list(directories):
            if not name.endswith("-kompiled"):
                continue
            candidate = Path(current) / name
            directories.remove(name)
            if candidate.is_symlink():
                raise RuntimeError(f"refusing symlinked kompiled artifact: {candidate}")
            resolved = candidate.resolve()
            if not resolved.is_relative_to(case_root):
                raise RuntimeError(f"refusing kompiled artifact outside the case: {candidate}")
            shutil.rmtree(candidate)
    for name in (".depend", ".depend-tmp"):
        dependency = Path(case.dir) / name
        if dependency.exists():
            dependency.unlink()


def kast_bison_recipe_input(recipe):
    """Recognise the checked %.kast-bison parser invocation after its kast generation recipe."""
    match = re.search(
        r"(?:^|;\s*)\./bison_parser\s+([^\s|]+)\s*\|\s*diff\s+-\s+[^\s;]+\s*$",
        recipe,
    )
    return match.group(1) if match else None


def run_kast_bison_parsers(case, inputs):
    """Run the reference and krust parsers produced by a kast --gen-parser recipe."""
    row = {"comparison": "exact"}
    reference_parser = getattr(case, "kast_reference_parser", os.path.join(case.dir, "bison_parser"))
    rust_parser = getattr(case, "kast_rust_parser", os.path.join(case.log, "kast-bison.krust-parser"))
    for input_path in inputs:
        if not os.path.exists(reference_parser):
            step_record(case, step="bison-parser", stage="bison-parser", test=input_path,
                        comparison_policy="exact", verdict="reference-error",
                        reason="reference kast did not install the generated parser")
            continue
        if not os.path.exists(rust_parser):
            step_record(case, step="bison-parser", stage="bison-parser", test=input_path,
                        comparison_policy="exact", verdict="krust-error",
                        reason="krust kast did not install the generated parser")
            continue
        compare_bison_parser_commands(
            case, row, input_path,
            [reference_parser, input_path], [rust_parser, input_path])


def run_case(rel, kind):
    case = Case(rel); case.kind = kind
    if os.path.exists(case.log): shutil.rmtree(case.log)
    os.makedirs(case.log, exist_ok=True)
    if kind in ("no-makefile", "kdep") or (kind == "custom" and case.bison_parser is None):
        case.note(f"case kind {kind}: not driven"); return finish(case, "skipped-with-reason", f"case kind {kind}")
    clean_case_artifacts(case)
    case.vars = make_vars(case)
    case.backend = case.vars.get("KOMPILE_BACKEND", "llvm").strip() or "llvm"
    rc, lines, err = make_recipes(case)
    if rc != 0 and not lines:
        case.note("make -n all failed: " + err.strip()[:300])
        return finish(case, "reference-error", "driver could not enumerate recipes: make -n all failed")
    recs = []
    custom = []
    kast_bison_inputs = []
    for l in lines:
        r = split_recipe(l)
        if r is None:
            kast_bison_input = kast_bison_recipe_input(l)
            if kast_bison_input:
                kast_bison_inputs.append(kast_bison_input)
            else:
                custom.append(l)
        else: recs.append(r)
    if custom:
        case.custom_targets = custom[:8]
        case.note(f"{len(custom)} recipe line(s) without a K tool were not driven")
    kompiles = [r for r in recs if r["tool"] == "kompile"]
    tests = [] if BISON_PARSER_ONLY else [r for r in recs if r["tool"] != "kompile"]
    case.needs_krust_runtime = any(r["tool"] == "krun" for r in tests)
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
            case.kompile_recipe = k
            pos, opts, flags = parse_opts(k["args"], KOMPILE_VALUE_OPTS)
            case.def_file = next((p for p in pos if re.search(r"\.(k|md|json)$", p)), None)
            do_kompile(case, k, expect_fail=False)
            for extra_k in kompiles[1:]:
                sh(
                    ["bash", "-c", extra_k["raw"]],
                    case.dir,
                    case.remaining(),
                    env=reference_process_env(extra_k["tool"], extra_k["args"]),
                )
            if not case.main_module and case.def_file:
                case.main_module, case.syntax_module, case.pgm_sort = guess_modules(case, case.def_file, (opts.get("--main-module") or [None])[-1])
                if (opts.get("--syntax-module") or [None])[-1]: case.syntax_module = opts["--syntax-module"][-1]
        run_bison_parsers(case)
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
    run_kast_bison_parsers(case, kast_bison_inputs)
    return finish(case)


VERDICT_RANK = {
    "reference-error": -1,
    "krust-error": 0,
    "mismatch": 1,
    "krust-unsupported": 2,
    "skipped-with-reason": 2,
    "match": 3,
}
STAGE_RANK = ["outer-parse", "inner-parse", "kompile", "bison-parser", "kast", "krun", "search", "kprove"]


def finish(case, verdict=None, reason=None):
    case.seconds = round(time.monotonic() - case.t0, 1)
    if verdict is None:
        ranked_steps = case.steps
        if BISON_PARSER_ONLY:
            ranked_steps = [step for step in case.steps if step.get("step") == "bison-parser"]
        vs = [s.get("verdict", "skipped-with-reason") for s in ranked_steps]
        if not vs: verdict, reason = "skipped-with-reason", "no driven steps"
        else:
            verdict = min(vs, key=VERDICT_RANK.__getitem__)
            first = next(s for s in ranked_steps if s.get("verdict") == verdict)
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
    lexical_target = Path(path).absolute()
    if lexical_target.is_symlink():
        raise ValueError(f"refusing symlinked conformance work tree: {lexical_target}")
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


def source_tree_marker(source_tree):
    """Identify the immutable K source copied into the persistent driver work tree."""
    source_tree = Path(source_tree).resolve()
    completed = subprocess.run(
        ["git", "-C", str(source_tree.parent), "rev-parse", "HEAD"],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        text=True,
    )
    revision = completed.stdout.strip() if completed.returncode == 0 else ""
    return {"source_tree": str(source_tree), "revision": revision}


def selected_work_tree_files(cases):
    files = [Path("include/kframework/ktest.mak")]
    for rel, kind in cases:
        if kind == "no-makefile":
            continue
        makefile = BISON_PARSERS.get(rel, {}).get("makefile", "Makefile")
        files.append(Path(REG) / rel / makefile)
    return files


def work_tree_refresh_reason(work_tree, source_tree, cases):
    target = Path(work_tree)
    if not target.is_dir():
        return "work tree is missing"
    marker_path = target / WORK_TREE_MARKER
    try:
        marker = json.loads(marker_path.read_text())
    except (OSError, json.JSONDecodeError):
        return "source marker is missing or invalid"
    if marker != source_tree_marker(source_tree):
        return "source marker is stale"
    missing = [str(path) for path in selected_work_tree_files(cases) if not (target / path).is_file()]
    if missing:
        return "required files are missing: " + ", ".join(missing[:5])
    return None


def refresh_work_tree(work_tree, source_tree):
    """Stage a complete copy, then replace the persistent scratch tree."""
    target = Path(work_tree)
    target.parent.mkdir(parents=True, exist_ok=True)
    staging = Path(tempfile.mkdtemp(prefix=f".{target.name}.refresh-", dir=target.parent))
    try:
        shutil.copytree(Path(source_tree) / "include", staging / "include", symlinks=True)
        (staging / Path(REG).parent).mkdir(parents=True, exist_ok=True)
        shutil.copytree(Path(source_tree) / REG, staging / REG, symlinks=True)
        (staging / WORK_TREE_MARKER).write_text(
            json.dumps(source_tree_marker(source_tree), sort_keys=True) + "\n"
        )
        if os.path.lexists(target):
            if target.is_symlink() or not target.is_dir():
                raise ValueError(f"work tree exists but is not a directory: {target}")
            shutil.rmtree(target)
        os.replace(staging, target)
    finally:
        if staging.exists():
            shutil.rmtree(staging)


def ensure_work_tree(work_tree, source_tree, cases, force=False):
    reason = "--fresh-copy requested" if force else work_tree_refresh_reason(
        work_tree, source_tree, cases
    )
    if reason is not None:
        refresh_work_tree(work_tree, source_tree)
    remaining = work_tree_refresh_reason(work_tree, source_tree, cases)
    if remaining is not None:
        raise OSError(f"work tree validation failed after refresh: {remaining}")
    return reason


def main():
    global BISON_PARSER_ONLY, BUILTIN, CASE_BUDGET, CASE_BUDGETS, EXPECTATIONS, IGNORE_UNIQUE_ID
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
    ap.add_argument("--stage", action="append", default=[], help="select baseline stage")
    ap.add_argument("--cases", nargs="*", default=[], help="case names relative to regression-new")
    ap.add_argument("--all", action="store_true", help="select every regression-new leaf")
    ap.add_argument(
        "--bison-parsers",
        action="store_true",
        help="select the generated-parser manifest and run only its parser comparisons",
    )
    ap.add_argument("--kore-parser", help="matching pinned kore-parser executable")
    ap.add_argument("--expectations", help="case expectations and budget TOML")
    ap.add_argument("--jobs", type=positive_integer, default=2)
    ap.add_argument("--rank", choices=sorted(VERDICT_RANK), help="print a verdict rank and exit")
    ap.add_argument("--list", action="store_true")
    ap.add_argument("--fresh-copy", action="store_true", help="re-copy the regression tree to the scratch directory")
    ap.add_argument("--postprocess", action="store_true", help="only reclassify/trim an existing results file")
    ap.add_argument("--merge", help="replace the cases of --results by the cases found in this results file, then postprocess")
    a = ap.parse_args()
    BISON_PARSER_ONLY = a.bison_parsers

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
    STEP_BUDGETS.clear()
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
        for rel, kind in cases:
            if not BISON_PARSER_ONLY or rel in BISON_PARSERS:
                print(kind, rel)
        return 0

    try:
        expectations_document, expectation_budgets, expectation_step_budgets = load_expectations(EXPECTATIONS)
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
    for name, step_budget in expectation_step_budgets.items():
        if not math.isfinite(step_budget) or step_budget <= 0:
            ap.error(f"expectation step_budget for {name} must be positive and finite")
        if step_budget > CASE_BUDGETS.get(name, CASE_BUDGET):
            ap.error(f"expectation step_budget for {name} exceeds its case budget")
    STEP_BUDGETS.update(expectation_step_budgets)

    available = {name for name, _ in cases}
    unknown_overrides = sorted(CASE_BUDGETS.keys() - available)
    if unknown_overrides:
        ap.error(f"unknown --case-budget case(s): {', '.join(unknown_overrides)}")

    selectors_given = bool(a.cases or a.stage or BISON_PARSER_ONLY)
    selected = set(a.cases)
    if BISON_PARSER_ONLY:
        selected.update(BISON_PARSERS)
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

    try:
        refresh_reason = ensure_work_tree(
            WORK_TREE, SRC_TREE, cases, force=a.fresh_copy
        )
    except (OSError, ValueError) as error:
        ap.error(f"cannot populate work tree {WORK_TREE}: {error}")
    if refresh_reason is not None:
        print(f"refreshed conformance work tree: {refresh_reason}", file=sys.stderr)
    os.makedirs(LOGS, exist_ok=True)

    done = []
    t0 = time.monotonic()
    def work(item):
        rel, kind = item
        try:
            c = run_case(rel, kind)
        except Exception as ex:
            import traceback
            c = Case(rel); c.kind = kind; c.note("driver exception: " + traceback.format_exc()[-800:]); finish(c, "reference-error", f"driver exception: {ex}")
        with lock:
            done.append(c); write_results(done, a.results)
            print(f"[{len(done)}/{len(cases)}] {c.verdict:22s} {c.stage:12s} {c.seconds:6.1f}s  {rel}", flush=True)
    with ThreadPoolExecutor(max_workers=a.jobs) as ex:
        list(ex.map(work, cases))
    print(f"done: {len(done)} cases in {time.monotonic() - t0:.0f}s")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
