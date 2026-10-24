#!/usr/bin/env python3
"""Measure a gate run and compare it with the baseline (k2lean/tests/gate.sh calls this).

usage: gate-check.py check WORK BASELINE TIER   measure WORK, write WORK/measured/measured.toml,
                                                 compare with BASELINE; exit 1 on a regression
       gate-check.py accept WORK BASELINE        make WORK's last measurements the baseline, and
                                                 copy its expected outputs to expected/ beside it

What is compared (each entry of the baseline names its tier, light, heavy or arity; an arity run
compares its libraries with the arity entries, and kimp's goldens, SIMPLE's cases and their
recorded outputs with the default encoding's, which they must equal):
  status    every step of the run succeeded (generation, builds, axiom guards, tests)
  unit      generator tests: none fails, and no fewer pass
  lib.X     the open-obligation set of library X may only shrink (a new member fails, and is
            printed); fewer stated equations or fewer theorems under the axiom guard fail
  kimp      goldens passed and trace states: equal to the baseline
  demo.X    theorems under the guard may not decrease; each `k2l_preserve` call closes no fewer
            rules and has no new residual rule; Kind2Template is the skeleton that
            `k2lean new-invariant` writes for kimp (kind 2), built like a demo; SimpleEnv
            (heavy) is the kind 2 invariant of SIMPLE
  diff      `k2lean diff` of each library's last generation (the tree under test's generated/)
            against the regenerated one: a NOTE naming the changed rules and functions and the
            hand-written references to revisit (the sources check is what fails)
  inv.X     the kind 1 invariant of library X (`X/NS/Invariants.lean`) builds; its open rule cases
            (open-invariant-cases.txt) may only shrink, the cases proved by `k2l_preserve` may not
            decrease, nor the theorems under its axiom guard
  negative  KRS IMP with an ill-typed `assign`: the generated proof of the declared cell type must
            still fail, with exactly the baseline's open cases, and an error line naming each
  simple    cases and Lean = krust verdicts equal to the baseline
  claims    stated claims (kimp's, and kimpinv's under its invariant), induction obligations and theorems
            under the guard equal to the baseline
  outputs   recorded outputs (goldens.toml, kimp-test.out, acceptance tables, claims files)
            equal to expected/, after the normalization each one names (search times, replay
            seconds and the order of logged lines are not compared)
  sources   the sha256 of every regenerated source equals the baseline's (the last accepted
            generation); a difference fails until accepted. The hand inputs of a library (its
            open lists and kind 1 hand module `InvariantsHand.lean`) are not hashed: the build
            that uses them checks them
  banned    no `sorry` or `admit` token, and no `axiom` declaration outside the baseline's allowed
            set, in any Lean source of the work tree, and no "declaration uses 'sorry'" in a log
"""
import hashlib
import re
import shutil
import sys
import tomllib
from pathlib import Path

LIBS = {"kimp": ("KImp", "light"), "kimp-d2": ("KImp", "light"), "krsimp": ("KrsImp", "light"), "kmut": ("KMut", "light"),
        "imptypes": ("KImpTypes", "light"), "simple": ("KSimple", "heavy"), "kimpinv": ("KImpInv", "light"),
        "simpleinv": ("KSimpleInv", "heavy"), "kimp-ar": ("KImp", "arity"), "simple-ar": ("KSimple", "arity"),
        "kimpkeys": ("KImpKeys", "light"), "kimpkeys-hand": ("KImpKeys", "light"),
        "kimpfold": ("KImpInv", "light"), "kimptop": ("KImpInv", "light"), "nested": ("KNested", "light"),
        "simplestore": ("KSimpleInv", "heavy"), "simplet": ("KSimpleInv", "heavy")}
# libraries built only as far as their invariant needs: no `…Test.Axioms` guard
NO_GUARD = {"kimpinv", "simpleinv", "kimpkeys", "kimpkeys-hand", "kimpfold", "kimptop", "nested", "simplestore", "simplet"}
INVS = {"kimpinv": ("KImpInv", "light"), "krsimp": ("KrsImp", "light"), "simpleinv": ("KSimpleInv", "heavy"),
        "kimpkeys": ("KImpKeys", "light"), "kimpkeys-hand": ("KImpKeys", "light"),
        "kimpfold": ("KImpInv", "light"), "kimptop": ("KImpInv", "light"), "nested": ("KNested", "light"),
        "simplestore": ("KSimpleInv", "heavy"), "simplet": ("KSimpleInv", "heavy")}
DEMOS = {"ImpRel": "light", "ImpTypes": "light", "ImpMut": "light", "KrsImpTyping": "light",
         "Kind2Template": "light", "SimpleEnv": "heavy", "ImpWrites": "light", "ImpRelClaims": "heavy"}
OUTPUTS = {  # recorded output → (tier, normalization)
    "goldens.toml": ("light", "exact"),
    "kimp-test.out": ("light", "exact"),
    "simple-acceptance.toml": ("heavy", "strip-ms"),
    "simple-acceptance.md": ("heavy", "strip-ms"),
    "claims.toml": ("heavy", "exact"),
    "claims-inv.toml": ("heavy", "exact"),
    "kprove.txt": ("heavy", "exact"),
    "kc-auto-stats.txt": ("heavy", "sorted-lines"),  # Lake replays logs in build order
    "axioms.txt": ("heavy", "axiom-sets"),
    "replay/addition-2.toml": ("heavy", "strip-seconds"),
    "replay/branching.toml": ("heavy", "strip-seconds"),
    "replay/sum-loop.toml": ("heavy", "strip-seconds"),
}
# the recorded outputs an arity run produces, compared with the default encoding's
ARITY_OUTPUTS = {"goldens.toml", "kimp-test.out", "simple-acceptance.toml", "simple-acceptance.md"}
# the tracked inputs of a generated library, which a person writes and the generator only reads
# (the open lists, and the kind 1 hand module that `gen` writes once and never overwrites): not
# hashed, so an edit to them is checked by the build that uses them, not by the sources check
HAND_INPUTS = ("open-obligations.txt", "open-invariant-cases.txt", "InvariantsHand.lean")
# generated sources the gate does not regenerate (written by `k2lean configs`, which it skips)
NOT_REGENERATED = {"generated/kimp/KImpBench/Programs.lean", "generated/kimp-d2/KImpBench/Programs.lean",
                   "generated/kimp-ar/KImpBench/Programs.lean"}
SOURCE_DIRS = {"light": ["generated/kimp", "generated/kimp-d2", "generated/krsimp", "generated/kmut", "generated/imptypes", "generated/kimpinv",
                         "generated/kimpkeys", "generated/kimpkeys-hand",
                         "generated/kimpfold", "generated/kimptop", "generated/nested"],
               "heavy": ["generated/simple", "generated/kimp-claims", "generated/simpleinv", "generated/simplestore", "generated/simplet",
                         "generated/kimpinv-claims"],
               "arity": ["generated/kimp-ar", "generated/simple-ar"]}
DEMO_SOURCES = ["demos/ImpRel/ImpRel/Bisim.lean", "demos/ImpRel/correspondence.toml",
                "demos/ImpTypes/ImpTypes/Tr.lean", "demos/ImpTypes/correspondence.toml",
                "demos/ImpMut/ImpMut/Tr.lean", "demos/ImpMut/correspondence.toml"]


def tiers(tier):
    return {"light": ["light"], "heavy": ["light", "heavy"], "arity": ["arity"]}[tier]


# ---------------------------------------------------------------- measuring

def read(p):
    p = Path(p)
    return p.read_text(errors="replace") if p.exists() else None


def equations(path):
    """(stated, open set) of a generated Equations.lean."""
    text = read(path)
    if text is None:
        return None
    opened = re.findall(r"^def (\S+)\.statement : Prop", text, re.M)
    proved = re.findall(r"^theorem ((?:Eqn|Simp|Lemma)\.\S+)", text, re.M)
    return len(opened) + len(proved), sorted(opened)


def guarded(log):
    text = read(log)
    return None if text is None else len(re.findall(r"depends on axioms: ", text))


def lean_names(s):
    """The names of a printed Lean list body: `«…»` names may contain `,`, `]` and spaces."""
    out, i = [], 0
    while i < len(s):
        if s[i] in " ,":
            i += 1
        elif s[i] == "«":
            j = s.index("»", i)
            k = j + 1
            while k < len(s) and s[k] not in " ,":
                k += 1
            out.append(s[i:k])
            i = k
        else:
            k = i
            while k < len(s) and s[k] not in " ,":
                k += 1
            out.append(s[i:k])
            i = k
    return out


def preserve_lines(log):
    """Each `k2l_preserve` result, keyed by the file and line of its call (`where`), in that order:
    Lake replays module logs in build order, which is not fixed."""
    out = []
    pat = (r"(?:(\S+\.lean):(\d+):\d+: )?k2l_preserve: (\d+) of (\d+) rules closed"
           r"(?:; hand: \[(.*?)\](?=; open: |$))?(?:; open: \[(.*)\])?$")
    for m in re.finditer(pat, read(log) or "", re.M):
        opened = lean_names(m.group(6)) if m.group(6) else []
        e = {"where": f"{m.group(1)}:{m.group(2)}" if m.group(1) else "", "closed": int(m.group(3)),
             "total": int(m.group(4)), "open": opened}
        # the hand mode (kind 2): the rules whose cases come from hand-written theorems
        if m.group(5):
            e["hand"] = lean_names(m.group(5))
        out.append(e)
    out.sort(key=lambda x: x["where"])
    return out


def strip_lean(text):
    """Lean source without comments and string literals (so a `sorry` in a doc comment is not one)."""
    out, i, n, depth = [], 0, len(text), 0
    while i < n:
        if depth:
            if text.startswith("/-", i):
                depth, i = depth + 1, i + 2
            elif text.startswith("-/", i):
                depth, i = depth - 1, i + 2
            else:
                if text[i] == "\n":
                    out.append("\n")
                i += 1
        elif text.startswith("/-", i):
            depth, i = 1, i + 2
        elif text.startswith("--", i):
            while i < n and text[i] != "\n":
                i += 1
        elif text[i] == '"':
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
            i += 1
            out.append('""')
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


AXIOM_RE = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*axiom\s+(\S+)", re.M)


def banned(tree, logs):
    found, axioms = [], []
    for sub in ["lean", "generated", "demos"]:
        for f in sorted((tree / sub).rglob("*.lean")):
            if ".lake" in f.parts:
                continue
            rel = f.relative_to(tree).as_posix()
            src = strip_lean(f.read_text(errors="replace"))
            for k, line in enumerate(src.split("\n"), 1):
                for tok in re.findall(r"(?<![\w.'])(sorry|admit)(?![\w'])", line):
                    found.append(f"{rel}:{k}: {tok}")
            for m in AXIOM_RE.finditer(src):
                axioms.append(f"{rel}: {m.group(1)}")
    for log in sorted(logs.glob("*.log")):
        if "declaration uses 'sorry'" in log.read_text(errors="replace"):
            found.append(f"{log.name}: declaration uses 'sorry'")
    return found, axioms


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def sources(tree, tier):
    out = {}
    for t in tiers(tier):
        for d in SOURCE_DIRS[t]:
            for f in sorted((tree / d).rglob("*")):
                rel = f.relative_to(tree).as_posix()
                if (f.is_dir() or ".lake" in f.parts
                        or f.name in HAND_INPUTS or f.name in ("lake-manifest.json", ".gitignore")
                        or rel in NOT_REGENERATED):
                    continue
                out[rel] = (t, sha(f))
        if t == "light":
            for rel in DEMO_SOURCES:
                if (tree / rel).exists():
                    out[rel] = (t, sha(tree / rel))
    return out


def measure(work, tier):
    work = Path(work)
    tree, logs, meas = work / "k2lean", work / "logs", work / "measured"
    run = tomllib.loads(read(meas / "run.toml") or "")
    m = {"tier": tier, "run": run}
    status = {}
    for line in (read(meas / "status.tsv") or "").splitlines()[1:]:
        step, result, log = (line.split("\t") + ["", ""])[:3]
        status[step] = (result, log)
    m["status"] = status
    m["unit"] = {"passed": run.get("unit_passed"), "failed": run.get("unit_failed")}
    m["lib"] = {}
    for d, (ns, t) in LIBS.items():
        if t not in tiers(tier):
            continue
        eq = equations(tree / "generated" / d / ns / "Equations.lean") if f"build {d}" in status or f"build {ns}.Equations" in status else None
        g = guarded(logs / f"build-{d}-guard.log") if status.get(f"guard {d}", ("",))[0] == "ok" else None
        m["lib"][d] = {"tier": t, "stated": eq[0] if eq else None, "open": eq[1] if eq else None, "guarded": g}
    out = read(meas / "kimp-test.out") or ""
    gm = re.search(r"^goldens: (\d+)/(\d+) pass", out, re.M)
    m["kimp"] = {
        "tier": "light",
        "goldens_pass": int(gm.group(1)) if gm else None,
        "goldens_total": int(gm.group(2)) if gm else None,
        "trace_states": sum(int(x) for x in re.findall(r"^PASS trace .*?: (\d+) configurations equal", out, re.M)) if out else None,
        "trace_failures": len(re.findall(r"^FAIL trace", out, re.M)) if out else None,
    }
    m["inv"] = {}
    for d, (ns, t) in INVS.items():
        if t not in tiers(tier):
            continue
        src = read(tree / "generated" / d / ns / "Invariants.lean")
        if src is None:
            continue
        built = status.get(f"invariant {d}", ("",))[0] == "ok"
        auto = len(re.findall(r"^theorem \S.* := by k2l_inv$", src, re.M))
        hand = len(re.findall(r"^theorem \S.* := Invariant\.hand\.", src, re.M))
        opened = []
        for l in (read(tree / "generated" / d / "open-invariant-cases.txt") or "").splitlines():
            l = l.strip()
            if l and not l.startswith("#"):
                opened.append(l.split(" | ")[0])
        m["inv"][d] = {"tier": t, "cases": auto + hand, "auto": auto, "open": sorted(opened),
                       "guarded": guarded(logs / f"build-{d}-inv.log") if built else None}
    neg = read(meas / "negative.toml")
    m["negative"] = tomllib.loads(neg) if neg else {}
    for e in m["negative"].values():
        e["tier"] = "light"
    m["demo"] = {}
    for p, t in DEMOS.items():
        if t not in tiers(tier):
            continue
        ok = status.get(f"build {p}", ("",))[0] == "ok"
        # the `k2l_preserve` counts are logged before a failing proof's error, so a failed build
        # still says how many rules the tactic closed
        m["demo"][p] = {"tier": t, "guarded": guarded(logs / f"build-{p}.log") if ok else None,
                        "preserve": preserve_lines(logs / f"build-{p}.log")}
    if tier in ("heavy", "arity"):
        acc = read(meas / "simple-acceptance.toml")
        m["simple"] = {"tier": "heavy",
                       "cases": len(re.findall(r"^\[\[case\]\]", acc, re.M)) if acc else None,
                       "lean_eq_krust": len(re.findall(r'^lean_vs_krust = "pass"', acc, re.M)) if acc else None,
                       "lean_out_eq_out": len(re.findall(r'^lean_vs_out = "pass"', acc, re.M)) if acc else None}
    if tier == "heavy":
        ct = read(meas / "claims.toml")
        ci = read(meas / "claims-inv.toml")
        ax = read(meas / "axioms.txt")
        kc = read(meas / "kc-auto-stats.txt")
        m["claims"] = {"tier": "heavy",
                       "claims": len(re.findall(r"^\[\[claim\]\]", ct, re.M)) if ct else None,
                       "stated": len(re.findall(r"^stated = true", ct, re.M)) if ct else None,
                       "inv_stated": len(re.findall(r"^stated = true", ci, re.M)) if ci else None,
                       "induction_obligations": sum(int(x) for x in re.findall(r"^obligations = (\d+)", ct, re.M)) if ct else None,
                       "guarded": len([l for l in ax.splitlines() if l.strip()]) if ax else None,
                       "kc_auto": len([l for l in kc.splitlines() if "kc_auto" in l]) if kc else None,
                       "kc_auto_open": sum(int(x) for x in re.findall(r"(\d+) open", kc)) if kc else None}
    m["outputs"] = {k: (t, norm) for k, (t, norm) in OUTPUTS.items() if t in tiers(tier) or (tier == "arity" and k in ARITY_OUTPUTS)}
    m["sources"] = sources(tree, tier)
    m["banned"], m["axioms"] = banned(tree, logs)
    return m


# ---------------------------------------------------------------- TOML

def tv(v):
    if isinstance(v, bool):
        return "true" if v else "false"
    if isinstance(v, int):
        return str(v)
    if isinstance(v, str):
        return '"' + v.replace("\\", "\\\\").replace('"', '\\"') + '"'
    if isinstance(v, list):
        if all(isinstance(x, str) for x in v) and len(v) > 3:
            return "[\n" + "".join(f"  {tv(x)},\n" for x in v) + "]"
        return "[" + ", ".join(tv(x) for x in v) + "]"
    if isinstance(v, dict):
        return "{ " + ", ".join(f"{tk(k)} = {tv(x)}" for k, x in v.items()) + " }"
    raise TypeError(v)


def tk(k):
    return k if re.fullmatch(r"[A-Za-z0-9_-]+", k) else tv(k)


def to_baseline(m, old=None):
    """The baseline document for measurements m (keeping old's entries of tiers m did not run)."""
    old = old or {}
    run_t = tiers(m["tier"])
    keep = lambda e: isinstance(e, dict) and e.get("tier") not in run_t
    b = {"lib": {k: v for k, v in old.get("lib", {}).items() if keep(v)},
         "demo": {k: v for k, v in old.get("demo", {}).items() if keep(v)},
         "inv": {k: v for k, v in old.get("inv", {}).items() if keep(v)},
         "negative": {k: v for k, v in old.get("negative", {}).items() if keep(v)}}
    b["unit"] = {"tier": "light", "passed": m["unit"]["passed"]}
    for d, e in m["lib"].items():
        b["lib"][d] = e
    # an arity run records only its libraries and sources: its goldens, cases and outputs are
    # compared with the default encoding's entries, which it keeps
    arity = m["tier"] == "arity"
    b["kimp"] = old.get("kimp", m["kimp"]) if arity else m["kimp"]
    for p, e in m["demo"].items():
        b["demo"][p] = e
    for d, e in m["inv"].items():
        b["inv"][d] = e
    for d, e in m["negative"].items():
        b["negative"][d] = {k: v for k, v in e.items() if k != "first_error"}
    for k in ("simple", "claims"):
        if k in m and not arity:
            b[k] = m[k]
        elif k in old:
            b[k] = old[k]
    outs = {k: v for k, v in old.get("outputs", {}).items() if keep(v) or arity}
    if not arity:
        outs.update({k: {"tier": t, "compare": n} for k, (t, n) in m["outputs"].items()})
    b["outputs"] = outs
    srcs = {k: v for k, v in old.get("sources", {}).get("sha256", {}).items() if keep(v)}
    srcs.update({k: {"tier": t, "sha256": h} for k, (t, h) in m["sources"].items()})
    b["sources"] = {"allowed_axioms": old.get("sources", {}).get("allowed_axioms", []), "sha256": srcs}
    return b


def dump(b, header):
    o = [header]

    def table(name, d):
        o.append(f"\n[{name}]")
        for k, v in d.items():
            if v is None:
                o.append(f"# {tk(k)}: not measured")
            else:
                o.append(f"{tk(k)} = {tv(v)}")
    table("unit", b["unit"])
    for d, e in b["lib"].items():
        table(f"lib.{d}", e)
    table("kimp", b["kimp"])
    for p, e in b["demo"].items():
        table(f"demo.{p}", e)
    for d, e in b.get("inv", {}).items():
        table(f"inv.{d}", e)
    for d, e in b.get("negative", {}).items():
        table(f"negative.{tk(d)}", e)
    for k in ("simple", "claims"):
        if k in b:
            table(k, b[k])
    table("outputs", b["outputs"])
    o.append("\n[sources]")
    o.append(f"allowed_axioms = {tv(b['sources']['allowed_axioms'])}")
    o.append("\n[sources.sha256]")
    for k, v in sorted(b["sources"]["sha256"].items()):
        o.append(f"{tv(k)} = {tv(v)}")
    return "\n".join(o) + "\n"


HEADER = """# k2lean regression gate baseline (k2lean/tests/gate.sh, k2lean/tests/gate-check.py).
# Accept a new one after a deliberate change: run the tier, read its FAIL lines, then
#   k2lean/tests/gate.sh accept
# (with the same GATE_WORK/GATE_ROOT as the run); a light run replaces only the light entries.
# The recorded outputs that `outputs` names are in expected/ beside this file.
"""


# ---------------------------------------------------------------- comparing

def normalize(text, how):
    if how == "sorted-lines":
        return "\n".join(sorted(text.splitlines()))
    if how == "strip-ms":
        return re.sub(r", [0-9]* ms\b", "", text)
    if how == "strip-seconds":
        return "\n".join(l for l in text.splitlines() if not l.startswith("seconds = "))
    if how == "axiom-sets":
        rows = []
        for l in text.splitlines():
            name, _, axs = l.partition(" depends on axioms: ")
            rows.append(name + " " + " ".join(sorted(a.strip() for a in axs.strip("[]").split(",") if a.strip())))
        return "\n".join(sorted(rows))
    return text


def compare(m, base, expected, accept_cmd):
    fails, notes, passes = [], [], []
    F, N, P = fails.append, notes.append, passes.append
    run_t = tiers(m["tier"])
    lower = f"lower the baseline: {accept_cmd}"

    bad = [(s, log) for s, (r, log) in m["status"].items() if r != "ok"]
    for s, log in bad:
        F(f"step {s} failed (log {log})")
    if not bad:
        P(f"status: all {len(m['status'])} steps succeeded")

    u, bu = m["unit"], base.get("unit", {})
    if u["failed"] is None:
        F("unit: no test result (the generator did not build)")
    elif u["failed"] or (u["passed"] or 0) < bu.get("passed", 0):
        F(f"unit: {u['failed']} failed, {u['passed']} passed (baseline {bu.get('passed')} passed)")
    else:
        P(f"unit: {u['passed']} generator tests passed")
        if u["passed"] > bu.get("passed", 0):
            N(f"unit: {u['passed']} tests, baseline {bu.get('passed')}: {accept_cmd}")

    for d, e in m["lib"].items():
        b = base.get("lib", {}).get(d)
        if b is None:
            N(f"lib.{d}: not in the baseline")
            continue
        if e["open"] is None:
            F(f"lib.{d}: not measured (generation or build failed)")
            continue
        now, was = set(e["open"]), set(b["open"])
        new, gone = sorted(now - was), sorted(was - now)
        if new:
            F(f"lib.{d}: open obligations {len(was)} -> {len(now)}; new open: {', '.join(new)}")
        elif gone:
            P(f"lib.{d}: open obligations {len(was)} -> {len(now)}; closed: {', '.join(gone)}")
            N(f"lib.{d}: {len(gone)} fewer open obligations; {lower}")
        else:
            P(f"lib.{d}: open obligations {len(now)}, the same set")
        if e["stated"] < b["stated"]:
            F(f"lib.{d}: stated equations {b['stated']} -> {e['stated']}")
        elif e["stated"] > b["stated"]:
            N(f"lib.{d}: stated equations {b['stated']} -> {e['stated']}")
        if d in NO_GUARD:
            pass
        elif e["guarded"] is None:
            F(f"lib.{d}: axiom guard not run")
        elif e["guarded"] < b["guarded"]:
            F(f"lib.{d}: theorems under the axiom guard {b['guarded']} -> {e['guarded']}")
        else:
            P(f"lib.{d}: {e['guarded']} theorems under the axiom guard (baseline {b.get('guarded')})")

    k, bk = m["kimp"], base.get("kimp", {})
    for f in ("goldens_pass", "goldens_total", "trace_states", "trace_failures"):
        if k[f] != bk.get(f):
            F(f"kimp: {f} {bk.get(f)} -> {k[f]}")
    if all(k[f] == bk.get(f) for f in ("goldens_pass", "goldens_total", "trace_states", "trace_failures")):
        P(f"kimp: goldens {k['goldens_pass']}/{k['goldens_total']}, {k['trace_states']} trace states equal")

    for p, e in m["demo"].items():
        b = base.get("demo", {}).get(p)
        if b is None:
            N(f"demo.{p}: not in the baseline")
            continue
        if e["guarded"] is None:
            F(f"demo.{p}: not built")
        elif e["guarded"] < b["guarded"]:
            F(f"demo.{p}: theorems under the axiom guard {b['guarded']} -> {e['guarded']}")
        bp, ep = b.get("preserve", []), e["preserve"]
        if len(ep) != len(bp):
            F(f"demo.{p}: {len(bp)} k2l_preserve results in the baseline, {len(ep)} now")
        # pair the results by call site when the baseline records it, else by position
        if all(x.get("where") for x in bp):
            by = {y["where"]: y for y in ep}
            pairs = [(x, by[x["where"]]) for x in bp if x["where"] in by]
            for x in bp:
                if x["where"] not in by:
                    F(f"demo.{p}: no k2l_preserve result at {x['where']} (baseline {x['closed']} of {x['total']})")
        else:
            pairs = list(zip(bp, ep))
        for i, (x, y) in enumerate(pairs):
            new = sorted(set(y["open"]) - set(x["open"]))
            if y["closed"] < x["closed"] or new:
                F(f"demo.{p}: k2l_preserve #{i + 1}: {x['closed']} of {x['total']} -> {y['closed']} of {y['total']} rules closed"
                  + (f"; new residual: {', '.join(new)}" if new else ""))
            elif y["closed"] > x["closed"]:
                N(f"demo.{p}: k2l_preserve #{i + 1} closes {y['closed']} of {y['total']} (baseline {x['closed']}); {lower}")
        if not [f for f in fails if f.startswith(f"demo.{p}:")]:
            pres = "; ".join(f"{y['closed']}/{y['total']}" for y in ep)
            P(f"demo.{p}: {e['guarded']} theorems under the guard; k2l_preserve {pres or 'none'}")

    for d, e in m["inv"].items():
        b = base.get("inv", {}).get(d)
        if b is None:
            N(f"inv.{d}: not in the baseline")
            continue
        now, was = set(e["open"]), set(b["open"])
        new, gone = sorted(now - was), sorted(was - now)
        bad = len(fails)
        if e["guarded"] is None:
            F(f"inv.{d}: Invariants.lean does not build")
        elif e["guarded"] < b["guarded"]:
            F(f"inv.{d}: theorems under the axiom guard {b['guarded']} -> {e['guarded']}")
        if new:
            F(f"inv.{d}: open invariant cases {len(was)} -> {len(now)}; new open: {', '.join(new)}")
        if e["auto"] < b["auto"]:
            F(f"inv.{d}: cases proved by k2l_preserve {b['auto']} -> {e['auto']} (of {e['cases']})")
        if len(fails) == bad:
            P(f"inv.{d}: {e['auto']} of {e['cases']} rule cases by k2l_preserve, open {sorted(now) or 'none'}, {e['guarded']} under the guard")
            if gone or e["auto"] > b["auto"]:
                N(f"inv.{d}: fewer open cases or more automatic ones; {lower}")
    for d, b in base.get("negative", {}).items():
        if b.get("tier") not in run_t:
            continue
        e = m["negative"].get(d)
        if e is None:
            F(f"negative.{d}: not measured")
            continue
        bad = len(fails)
        if e["builds"]:
            F(f"negative.{d}: the generated proof now succeeds on the ill-typed definition")
        if sorted(e["open"]) != sorted(b["open"]):
            F(f"negative.{d}: open cases {b['open']} -> {e['open']}")
        unnamed = [x for x in b["open"] if x not in e["error_names"]]
        if unnamed:
            F(f"negative.{d}: no build error names {', '.join(unnamed)} (first error: {e.get('first_error')!r})")
        if len(fails) == bad:
            P(f"negative.{d}: fails as expected at {', '.join(e['open'])} (error: {e.get('first_error')})")
    for d in m["negative"]:
        if d not in base.get("negative", {}):
            N(f"negative.{d}: not in the baseline")

    for sec in ("simple", "claims"):
        if "heavy" not in run_t and not (m["tier"] == "arity" and sec == "simple"):
            break
        e, b = m.get(sec, {}), base.get(sec)
        if b is None:
            N(f"{sec}: not in the baseline")
            continue
        diff = [f"{f} {b.get(f)} -> {e.get(f)}" for f in b if f != "tier" and e.get(f) != b.get(f)]
        if diff:
            F(f"{sec}: " + "; ".join(diff))
        else:
            P(f"{sec}: " + ", ".join(f"{f} {e[f]}" for f in b if f != "tier"))

    for name, entry in base.get("outputs", {}).items():
        if entry.get("tier") not in run_t and not (m["tier"] == "arity" and name in ARITY_OUTPUTS):
            continue
        got, exp = m["work"] / "measured" / name, expected / name
        if not got.exists():
            F(f"outputs: {name} not produced")
            continue
        if not exp.exists():
            F(f"outputs: {name} has no expected copy in {expected}")
            continue
        a, b2 = normalize(exp.read_text(), entry["compare"]), normalize(got.read_text(), entry["compare"])
        if a == b2:
            P(f"outputs: {name} equal ({entry['compare']})")
        else:
            al, bl = a.splitlines(), b2.splitlines()
            j = next((i for i, (x, y) in enumerate(zip(al, bl)) if x != y), min(len(al), len(bl)))
            F(f"outputs: {name} differs ({entry['compare']}) from line {j + 1}: expected {al[j] if j < len(al) else '<end>'!r}, got {bl[j] if j < len(bl) else '<end>'!r}")

    want = {k: v for k, v in base.get("sources", {}).get("sha256", {}).items() if v.get("tier") in run_t}
    got = m["sources"]
    changed = sorted(k for k in want if k in got and got[k][1] != want[k]["sha256"])
    missing = sorted(k for k in want if k not in got)
    added = sorted(k for k in got if k not in want)
    if changed or missing:
        F(f"sources: {len(changed)} regenerated files differ from the accepted generation, {len(missing)} missing: "
          + ", ".join(changed[:12] + [f"{x} (missing)" for x in missing[:6]]) + (" …" if len(changed) > 12 else ""))
    else:
        P(f"sources: {len(want)} regenerated files identical to the accepted generation")
    if added:
        N(f"sources: {len(added)} new generated files: {', '.join(added[:8])}")

    for f in sorted((m["work"] / "measured").glob("diff-*.toml")):
        try:
            d = tomllib.loads(f.read_text())
        except tomllib.TOMLDecodeError:
            N(f"diff {f.stem[5:]}: unreadable {f}")
            continue
        sm = d.get("summary", {})
        counts = {k: sm.get(k, 0) for k in ("changed", "added", "removed", "renamed", "renamed_changed", "context_changed",
                                            "functions_changed", "functions_added", "functions_removed")}
        if any(counts.values()):
            rules = [f"{r['name']} {r['status']}" for r in d.get("rule", [])]
            rules += [f"function {x['label']} {x['status']} ({len(x.get('rules', []))} calling rules)" for x in d.get("function", [])]
            revisit = sorted({r["rule"] for r in d.get("revisit", [])})
            N(f"diff {f.stem[5:]}: " + ", ".join(f"{k} {v}" for k, v in counts.items() if v) + f": {'; '.join(rules[:12])}"
              + (f"; hand-written cases to revisit: {', '.join(revisit)}" if revisit else "") + f" ({f.with_suffix('.txt')})")

    allowed = set(base.get("sources", {}).get("allowed_axioms", []))
    extra = [a for a in m["axioms"] if a.split(": ", 1)[1] not in allowed]
    if m["banned"]:
        F(f"banned: {len(m['banned'])} sorry/admit: " + "; ".join(m["banned"][:10]))
    if extra:
        F(f"banned: axiom declarations: " + "; ".join(extra[:10]))
    if not m["banned"] and not extra:
        P(f"banned: no sorry, admit or axiom declaration ({len(m['axioms'])} allowed axioms)")
    return fails, notes, passes


# ---------------------------------------------------------------- commands

def check(work, baseline, tier):
    work, baseline = Path(work), Path(baseline)
    m = measure(work, tier)
    m["work"] = work
    base = tomllib.loads(baseline.read_text())
    (work / "measured" / "measured.toml").write_text(dump(to_baseline(m), f"# measured by a {tier} gate run, {m['run'].get('started')}\ntier = \"{tier}\"\n"))
    accept = "k2lean/tests/gate.sh accept" + ("" if str(work).endswith("/work/main") else f"  (with GATE_WORK={work})")
    fails, notes, passes = compare(m, base, baseline.parent / "expected", accept)
    for p in passes:
        print(f"gate: PASS {p}")
    for n in notes:
        print(f"gate: NOTE {n}")
    for f in fails:
        print(f"gate: FAIL {f}")
    print(f"gate: {tier} {'FAILED, ' + str(len(fails)) + ' regressions' if fails else 'passed'}; logs in {work / 'logs'}, measurements in {work / 'measured'}")
    return 1 if fails else 0


def accept(work, baseline):
    work, baseline = Path(work), Path(baseline)
    meas = work / "measured"
    mt = meas / "measured.toml"
    if not mt.exists():
        print(f"gate: no measurements in {meas}; run a tier first", file=sys.stderr)
        return 2
    tier = tomllib.loads(mt.read_text())["tier"]
    m = measure(work, tier)
    bad = [s for s, (r, _) in m["status"].items() if r != "ok"]
    if bad or m["banned"] or m["unit"]["failed"]:
        print(f"gate: not accepted: failed steps {bad}, banned {m['banned'][:3]}, unit failures {m['unit']['failed']}", file=sys.stderr)
        return 1
    old = tomllib.loads(baseline.read_text()) if baseline.exists() else {}
    baseline.write_text(dump(to_baseline(m, old), HEADER))
    exp = baseline.parent / "expected"
    for name, (t, _) in OUTPUTS.items():
        if t in tiers(tier) and (meas / name).exists():
            (exp / name).parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(meas / name, exp / name)
    print(f"gate: accepted the {tier} measurements of {work} into {baseline} and {exp}/")
    return 0


if __name__ == "__main__":
    a = sys.argv[1:]
    if a[:1] == ["check"] and len(a) == 4:
        sys.exit(check(*a[1:]))
    if a[:1] == ["accept"] and len(a) == 3:
        sys.exit(accept(*a[1:]))
    print(__doc__, file=sys.stderr)
    sys.exit(2)
