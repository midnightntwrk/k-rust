#!/usr/bin/env python3
"""Measure a gate run and compare it with the baseline (k2lean/tests/gate.sh calls this).

usage: gate-check.py check WORK BASELINE TIER    measure WORK, write WORK/measured/measured.toml
                                                  (and one baseline/AREA.toml per area there),
                                                  compare with BASELINE; exit 1 on a regression
       gate-check.py accept WORK BASELINE [--area NAME]
                                                  make WORK's last measurements the baseline (of
                                                  every area, or of area NAME only), and copy its
                                                  expected outputs to expected/AREA/ beside it
       gate-check.py entries TIER                 the entries a TIER run measures, `KIND NAME` a line
       gate-check.py list [TIER]                  the registered entries by area (of a TIER run)

BASELINE is a directory with one AREA.toml per area; the recorded outputs of area AREA are in
expected/AREA/ beside it. The registries are tests/areas/AREA.py (GATE_AREAS=DIR overrides the
directory), for the areas of LIBS_AREAS in tests/libs.sh beside them. A registry defines any of:
  LIBS      name -> {ns, tier, encoding ("arity", the default, or "per-sort": a label;
            the `gen` arm of the area selects the encoding), guard (False: built only as far as
            its invariant, no `…Test.Axioms`), not_regenerated (files of generated/name that the gate
            does not regenerate)}; generated/name is hashed
  INVS      name -> {ns, tier}: the kind 1 invariant of library name
  DEMOS     name -> {tier, sources (files or directories under k2lean/ that the demo's phase
            generates, hashed), encoding (as LIBS': the encoding of the libraries it is built on)}
  NEGATIVE  name -> {tier}: an entry of measured/negative.toml
  RECORDS   name -> {tier, compare_in, measure (a function of the run, returning the record's
            fields), sources}
  OUTPUTS   path under measured/ -> {tier, compare (the normalization), compare_in, same_as (another
            output of the area whose recorded copy this one is compared with; it has none of its own)}
Every entry is measured, compared and accepted by a run of a tier that includes its own (heavy
includes light), and only measured and compared by a run of a tier in its compare_in.

What is compared:
  status    every step of the run succeeded (generation, builds, axiom guards, tests)
  unit      generator tests: none fails, and no fewer pass
  lib.X     the open-obligation set of library X may only shrink (a new member fails, and is
            printed); fewer stated equations or fewer theorems under the axiom guard fail; the
            number of overlapping pairs `gen` lists (determinism along the rule index) and of
            those without a witness equal the baseline's
  demo.X    theorems under the guard may not decrease; each `k2l_preserve` call closes no fewer
            rules and has no new residual rule
  diff      `k2lean diff` of each library's last generation (the tree under test's generated/)
            against the regenerated one: a NOTE naming the changed rules and functions and the
            hand-written references to revisit (the sources check is what fails)
  inv.X     the kind 1 invariant of library X (`X/NS/Invariants.lean`) builds; its open rule cases
            (open-invariant-cases.txt) may only shrink, the cases proved by `k2l_preserve` may not
            decrease, nor the theorems under its axiom guard
  negative  KRS IMP with an ill-typed `assign`: the generated proof of the declared cell type must
            still fail, with exactly the baseline's open cases, and an error line naming each
  records   every field equal to the baseline (kimp's goldens and traces, SIMPLE's cases, the claims)
  outputs   recorded outputs equal to expected/AREA/, after the normalization each one names
            (search times, replay seconds and the order of logged lines are not compared)
  sources   the sha256 of every regenerated source equals the baseline's (the last accepted
            generation); a difference fails until accepted. The hand inputs of a library (its
            open lists and kind 1 hand module `InvariantsHand.lean`) are not hashed: the build
            that uses them checks them
  banned    no `sorry` or `admit` token, and no `axiom` declaration outside the baseline's allowed
            set, in any Lean source of the work tree, and no "declaration uses 'sorry'" in a log
"""
import hashlib
import os
import re
import shutil
import sys
import tomllib
from pathlib import Path
from types import SimpleNamespace

TIERS = ("light", "heavy")
KINDS = ("lib", "inv", "demo", "negative", "record", "output")
# the tracked inputs of a generated library, which a person writes and the generator only reads
# (the open lists, and the kind 1 hand module that `gen` writes once and never overwrites): not
# hashed, so an edit to them is checked by the build that uses them, not by the sources check
HAND_INPUTS = ("open-obligations.txt", "open-invariant-cases.txt", "InvariantsHand.lean")


def tiers(tier):
    """The entry tiers a run of TIER measures, compares and accepts."""
    return {"light": ["light"], "heavy": ["light", "heavy"]}[tier]


def measured_in(e, tier):
    return e["tier"] in tiers(tier) or tier in e.get("compare_in", [])


def load_registry(adir=None):
    """The areas (in LIBS_AREAS order) and their entries: {area: {"LIBS": …, …}}, each entry with
    its defaults filled in; a name registered by two areas is an error. ADIR overrides GATE_AREAS."""
    adir = Path(adir or os.environ.get("GATE_AREAS") or Path(__file__).resolve().parent / "areas")
    libs_sh = (adir.parent / "libs.sh").read_text()
    order = re.search(r'^LIBS_AREAS="([^"]*)"', libs_sh, re.M).group(1).split()
    reg, seen = {}, {}
    for a in order:
        ns = {"re": re, "read": read, "guarded": guarded, "Path": Path}
        exec(compile((adir / f"{a}.py").read_text(), str(adir / f"{a}.py"), "exec"), ns)
        r = {k: dict(ns.get(k, {})) for k in ("LIBS", "INVS", "DEMOS", "NEGATIVE", "RECORDS", "OUTPUTS")}
        for k, d in r.items():
            for name, e in d.items():
                if e.get("tier") not in TIERS or any(t not in TIERS for t in e.get("compare_in", [])):
                    raise SystemExit(f"gate-check: {adir / a}.py: {k} {name}: tier must be one of {TIERS}")
                if (k, name) in seen:
                    raise SystemExit(f"gate-check: {k} {name} is registered by both {seen[k, name]} and {a}")
                seen[k, name] = a
                e.setdefault("compare_in", [])
                e["area"] = a
        for e in r["LIBS"].values():
            e.setdefault("encoding", "arity")
            e.setdefault("guard", True)
            e.setdefault("not_regenerated", [])
        reg[a] = r
    return reg


def same_as(reg, name):
    """The recorded output that output NAME is compared with: its own, or the one its `same_as` names."""
    for r in reg.values():
        if name in r["OUTPUTS"]:
            return r["OUTPUTS"][name].get("same_as", name)
    return name


def entries(reg):
    """(area, kind, name, entry) of every registered entry."""
    kind = {"LIBS": "lib", "INVS": "inv", "DEMOS": "demo", "NEGATIVE": "negative", "RECORDS": "record", "OUTPUTS": "output"}
    for a, r in reg.items():
        for k, d in r.items():
            for name, e in d.items():
                yield a, kind[k], name, e


def owned_sources(reg):
    """(area, tier, path, not_regenerated) of every hashed path (a file, or a directory hashed whole)."""
    for a, r in reg.items():
        for d, e in r["LIBS"].items():
            yield a, e["tier"], f"generated/{d}", {f"generated/{d}/{x}" for x in e["not_regenerated"]}
        for k in ("DEMOS", "RECORDS"):
            for e in r[k].values():
                for p in e.get("sources", []):
                    yield a, e["tier"], p, set()


# ---------------------------------------------------------------- measuring

def read(p):
    p = Path(p)
    return p.read_text(errors="replace") if p.exists() else None


def equations(path):
    """(stated, open set) of a generated Equations.lean, with the parts it imports when it is
    written in parts (`NS/Equations/PartK.lean`, `import NS.Equations.PartK`)."""
    text = read(path)
    if text is None:
        return None
    path = Path(path)
    ns = path.parent.name
    for m in re.findall(rf"^import {re.escape(ns)}\.Equations\.(Part\d+)$", text, re.M):
        part = read(path.parent / "Equations" / f"{m}.lean")
        if part is None:
            return None
        text += "\n" + part
    opened = re.findall(r"^def (\S+)\.statement : Prop", text, re.M)
    proved = re.findall(r"^theorem ((?:Eqn|Simp|Lemma)\.\S+)", text, re.M)
    return len(opened) + len(proved), sorted(opened)


def overlaps(log):
    """(listed overlapping pairs, of them without a witness) of a generation log with determinism
    along the rule index; (None, None) without it (a definition with several-match rules)."""
    text = read(log) or ""
    m = re.findall(r"^determinism: (\d+) overlapping pairs$", text, re.M)
    if not m:
        return None, None
    u = re.findall(r"^unwitnessed = (\d+)$", text, re.M)
    return int(m[-1]), int(u[-1]) if u else 0


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


def sources(tree, tier, reg):
    out = {}
    for a, t, p, skip in owned_sources(reg):
        if t not in tiers(tier):
            continue
        root = tree / p
        files = sorted(root.rglob("*")) if root.is_dir() else [root] if root.exists() else []
        for f in files:
            rel = f.relative_to(tree).as_posix()
            if (f.is_dir() or ".lake" in f.parts
                    or f.name in HAND_INPUTS or f.name in ("lake-manifest.json", ".gitignore")
                    or rel in skip):
                continue
            out[rel] = (a, t, sha(f))
    return out


def measure(work, tier, reg):
    work = Path(work)
    tree, logs, meas = work / "k2lean", work / "logs", work / "measured"
    run = tomllib.loads(read(meas / "run.toml") or "")
    m = {"tier": tier, "run": run, "work": work}
    status = {}
    for line in (read(meas / "status.tsv") or "").splitlines()[1:]:
        step, result, log = (line.split("\t") + ["", ""])[:3]
        status[step] = (result, log)
    m["status"] = status
    ctx = SimpleNamespace(tier=tier, run=run, status=status, tree=tree, logs=logs, meas=meas)
    m["lib"], m["inv"], m["demo"], m["negative"], m["record"], m["outputs"] = {}, {}, {}, {}, {}, {}
    neg_doc = tomllib.loads(read(meas / "negative.toml") or "")
    for a, kind, d, e in entries(reg):
        if not measured_in(e, tier):
            continue
        t = e["tier"]
        if kind == "lib":
            ns = e["ns"]
            eq = equations(tree / "generated" / d / ns / "Equations.lean") if f"build {d}" in status or f"build {ns}.Equations" in status else None
            g = guarded(logs / f"build-{d}-guard.log") if status.get(f"guard {d}", ("",))[0] == "ok" else None
            ov = overlaps(logs / f"gen-{d}.log")
            m["lib"][d] = {"tier": t, "stated": eq[0] if eq else None, "open": eq[1] if eq else None, "guarded": g,
                           "overlaps": ov[0], "unwitnessed": ov[1]}
        elif kind == "inv":
            src = read(tree / "generated" / d / e["ns"] / "Invariants.lean")
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
        elif kind == "demo":
            ok = status.get(f"build {d}", ("",))[0] == "ok"
            # the `k2l_preserve` counts are logged before a failing proof's error, so a failed build
            # still says how many rules the tactic closed
            m["demo"][d] = {"tier": t, "guarded": guarded(logs / f"build-{d}.log") if ok else None,
                            "preserve": preserve_lines(logs / f"build-{d}.log")}
        elif kind == "negative":
            if d in neg_doc:
                m["negative"][d] = dict(neg_doc[d], tier=t)
        elif kind == "record":
            m["record"][d] = {"tier": t, **e["measure"](ctx)}
        elif kind == "output":
            m["outputs"][d] = (a, t, e["compare"])
    m["sources"] = sources(tree, tier, reg)
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


def to_baseline(m, area, reg, old=None):
    """Area AREA's baseline document for measurements m: the entries of the tiers m's run accepts,
    and old's entries of the other tiers (an entry only compared by the run keeps old's). An old
    entry of a tier that is not in TIERS is dropped: no run can measure or accept it again."""
    old = old or {}
    run_t = tiers(m["tier"])
    keep = lambda e: isinstance(e, dict) and e.get("tier") in TIERS and e.get("tier") not in run_t
    owner = {(k, n): a for a, k, n, _ in entries(reg)}
    mine = lambda kind, n: owner.get((kind, n)) == area
    b = {}
    for sec, kind in (("lib", "lib"), ("inv", "inv"), ("demo", "demo"), ("negative", "negative")):
        b[sec] = {k: v for k, v in old.get(sec, {}).items() if keep(v)}
        for d, e in m[sec].items():
            if mine(kind, d) and e["tier"] in run_t:
                # a field not measured is left out (a kept entry, parsed back, has no trace of it)
                b[sec][d] = {k: v for k, v in e.items() if k != "first_error" and v is not None}
    b["record"] = {}
    orec = old.get("record", {})
    names = [n for (k, n), a in owner.items() if k == "record" and a == area]
    for name in names + [n for n in orec if n not in names]:
        e = m["record"].get(name)
        if e is not None and e["tier"] in run_t and mine("record", name):
            b["record"][name] = {k: v for k, v in e.items() if v is not None}
        elif name in orec and keep(orec[name]):
            b["record"][name] = orec[name]
    b["outputs"] = {k: v for k, v in old.get("outputs", {}).items() if keep(v)}
    for k, (a, t, n) in m["outputs"].items():
        if a == area and t in run_t:
            b["outputs"][k] = {"tier": t, "compare": n}
    # the registry's order, then entries no longer registered, so that an accept is byte-stable
    order = {}
    for i, (_, k, n, _) in enumerate(entries(reg)):
        order.setdefault(k, {})[n] = i
    for sec, kind in (("lib", "lib"), ("inv", "inv"), ("demo", "demo"), ("negative", "negative"),
                      ("record", "record"), ("outputs", "output")):
        o = order.get(kind, {})
        b[sec] = dict(sorted(b[sec].items(), key=lambda kv: o.get(kv[0], len(o))))
    srcs = {k: v for k, v in old.get("sources", {}).get("sha256", {}).items() if keep(v)}
    srcs.update({k: {"tier": t, "sha256": h} for k, (a, t, h) in m["sources"].items() if a == area})
    b["sources"] = {"sha256": srcs}
    if "allowed_axioms" in old.get("sources", {}):
        b["sources"]["allowed_axioms"] = old["sources"]["allowed_axioms"]
    return b


# the top-level tables of a baseline document that are not records
RESERVED = ("lib", "inv", "demo", "negative", "outputs", "sources", "tier")


def dump(b, header):
    o = [header]

    def table(name, d):
        o.append(f"\n[{name}]")
        for k, v in d.items():
            if v is None:
                o.append(f"# {tk(k)}: not measured")
            else:
                o.append(f"{tk(k)} = {tv(v)}")
    if "unit" in b["record"]:
        table("unit", b["record"]["unit"])
    for d, e in b["lib"].items():
        table(f"lib.{d}", e)
    for k, e in b["record"].items():
        if k != "unit":
            table(tk(k), e)
    for p, e in b["demo"].items():
        table(f"demo.{p}", e)
    for d, e in b["inv"].items():
        table(f"inv.{d}", e)
    for d, e in b["negative"].items():
        table(f"negative.{tk(d)}", e)
    if b["outputs"]:
        table("outputs", b["outputs"])
    o.append("\n[sources]")
    if "allowed_axioms" in b["sources"]:
        o.append(f"allowed_axioms = {tv(b['sources']['allowed_axioms'])}")
    o.append("\n[sources.sha256]")
    for k, v in sorted(b["sources"]["sha256"].items()):
        o.append(f"{tv(k)} = {tv(v)}")
    return "\n".join(o) + "\n"


def as_doc(text):
    """A baseline document parsed into to_baseline's shape (records under "record")."""
    raw = tomllib.loads(text)
    return {"lib": raw.get("lib", {}), "inv": raw.get("inv", {}), "demo": raw.get("demo", {}),
            "negative": raw.get("negative", {}), "outputs": raw.get("outputs", {}),
            "record": {k: v for k, v in raw.items() if k not in RESERVED},
            "sources": raw.get("sources", {})}


def header(area):
    return f"""# k2lean regression gate baseline of the {area} area (k2lean/tests/gate.sh, k2lean/tests/gate-check.py).
# Accept a new one after a deliberate change: run the tier, read its FAIL lines, then
#   k2lean/tests/gate.sh accept --area {area}
# (with the same GATE_WORK/GATE_ROOT as the run); a light run replaces only the light entries.
# The recorded outputs that `outputs` names are in expected/{area}/ beside this directory.
"""


def load_baseline(bdir, reg):
    """{area: document} of every registered area (an empty document when its file is missing)."""
    out = {}
    for a in reg:
        f = Path(bdir) / f"{a}.toml"
        out[a] = as_doc(f.read_text()) if f.exists() else as_doc("")
    return out


def merged(docs):
    """One document of every area's entries, for the comparison; each output knows its area."""
    b = {"lib": {}, "inv": {}, "demo": {}, "negative": {}, "record": {}, "outputs": {}, "sha256": {}, "allowed_axioms": []}
    for a, d in docs.items():
        for sec in ("lib", "inv", "demo", "negative", "record"):
            b[sec].update(d[sec])
        b["outputs"].update({k: dict(v, area=a) for k, v in d["outputs"].items()})
        b["sha256"].update(d["sources"].get("sha256", {}))
        b["allowed_axioms"] += d["sources"].get("allowed_axioms", [])
    return b


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


def compare(m, base, expected, accept_cmd, reg):
    """m's measurements against the merged baseline document base (merged()); EXPECTED is the
    directory of the recorded outputs, one subdirectory per area."""
    fails, notes, passes = [], [], []
    lib_reg = {d: e for r in reg.values() for d, e in r["LIBS"].items()}
    F, N, P = fails.append, notes.append, passes.append
    run_t = tiers(m["tier"])
    lower = f"lower the baseline: {accept_cmd}"

    bad = [(s, log) for s, (r, log) in m["status"].items() if r != "ok"]
    for s, log in bad:
        F(f"step {s} failed (log {log})")
    if not bad:
        P(f"status: all {len(m['status'])} steps succeeded")

    u, bu = m["record"].get("unit"), base["record"].get("unit", {})
    if u is not None:
        u = dict(u, failed=m["run"].get("unit_failed"))
    if u is None:
        F("unit: not registered (the core area's record `unit`)")
    elif u["failed"] is None:
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
        # determinism: the listed overlapping pairs are pinned (a library proved deterministic
        # unconditionally keeps an empty list), and none may lose its witness
        if e.get("overlaps") != b.get("overlaps"):
            F(f"lib.{d}: overlapping pairs {b.get('overlaps')} -> {e.get('overlaps')}")
        elif e.get("unwitnessed") != b.get("unwitnessed"):
            F(f"lib.{d}: overlapping pairs without a witness {b.get('unwitnessed')} -> {e.get('unwitnessed')}")
        elif e.get("overlaps") is not None:
            P(f"lib.{d}: {e['overlaps']} overlapping pairs, {e['unwitnessed']} without a witness")
        if not lib_reg.get(d, {}).get("guard", True):
            pass
        elif e["guarded"] is None:
            F(f"lib.{d}: axiom guard not run")
        elif e["guarded"] < b["guarded"]:
            F(f"lib.{d}: theorems under the axiom guard {b['guarded']} -> {e['guarded']}")
        else:
            P(f"lib.{d}: {e['guarded']} theorems under the axiom guard (baseline {b.get('guarded')})")

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

    # the records (kimp's goldens and traces, SIMPLE's cases, the claims): every field equal
    for sec, e in m["record"].items():
        if sec == "unit":
            continue
        b = base["record"].get(sec)
        if b is None:
            N(f"{sec}: not in the baseline")
            continue
        diff = [f"{f} {b.get(f)} -> {e.get(f)}" for f in b if f != "tier" and e.get(f) != b.get(f)]
        if diff:
            F(f"{sec}: " + "; ".join(diff))
        else:
            P(f"{sec}: " + ", ".join(f"{f} {e[f]}" for f in b if f != "tier"))

    for name in m["outputs"]:
        if name not in base["outputs"]:
            N(f"outputs: {name} not in the baseline")
    for name, entry in base["outputs"].items():
        if name not in m["outputs"]:
            continue
        got, exp = m["work"] / "measured" / name, expected / entry["area"] / same_as(reg, name)
        if not got.exists():
            F(f"outputs: {name} not produced")
            continue
        if not exp.exists():
            F(f"outputs: {name} has no expected copy in {expected / entry['area']}")
            continue
        a, b2 = normalize(exp.read_text(), entry["compare"]), normalize(got.read_text(), entry["compare"])
        if a == b2:
            P(f"outputs: {name} equal ({entry['compare']})")
        else:
            al, bl = a.splitlines(), b2.splitlines()
            j = next((i for i, (x, y) in enumerate(zip(al, bl)) if x != y), min(len(al), len(bl)))
            F(f"outputs: {name} differs ({entry['compare']}) from line {j + 1}: expected {al[j] if j < len(al) else '<end>'!r}, got {bl[j] if j < len(bl) else '<end>'!r}")

    want = {k: v for k, v in base["sha256"].items() if v.get("tier") in run_t}
    got = m["sources"]
    changed = sorted(k for k in want if k in got and got[k][2] != want[k]["sha256"])
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

    allowed = set(base["allowed_axioms"])
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
    reg = load_registry()
    m = measure(work, tier, reg)
    docs = load_baseline(baseline, reg)
    meas = work / "measured"
    (meas / "baseline").mkdir(parents=True, exist_ok=True)
    for a in reg:
        (meas / "baseline" / f"{a}.toml").write_text(dump(to_baseline(m, a, reg), header(a)))
    (meas / "measured.toml").write_text(f"# measured by a {tier} gate run, {m['run'].get('started')}; the entries by area are in baseline/\ntier = \"{tier}\"\n")
    accept = "k2lean/tests/gate.sh accept [--area NAME]" + ("" if str(work).endswith("/work/main") else f"  (with GATE_WORK={work})")
    fails, notes, passes = compare(m, merged(docs), baseline.parent / "expected", accept, reg)
    for p in passes:
        print(f"gate: PASS {p}")
    for n in notes:
        print(f"gate: NOTE {n}")
    for f in fails:
        print(f"gate: FAIL {f}")
    print(f"gate: {tier} {'FAILED, ' + str(len(fails)) + ' regressions' if fails else 'passed'}; logs in {work / 'logs'}, measurements in {work / 'measured'}")
    return 1 if fails else 0


def doc_diff(old, new):
    """The entries in which two documents of one area differ, as `section.name` labels."""
    out = []
    for sec in ("lib", "inv", "demo", "negative", "record", "outputs"):
        for k in sorted(set(old[sec]) | set(new[sec])):
            if old[sec].get(k) != new[sec].get(k):
                out.append(f"{'' if sec == 'record' else sec + '.'}{k}")
    os_, ns_ = old["sources"].get("sha256", {}), new["sources"].get("sha256", {})
    out += [f"sources {k}" for k in sorted(set(os_) | set(ns_)) if os_.get(k) != ns_.get(k)]
    if old["sources"].get("allowed_axioms") != new["sources"].get("allowed_axioms"):
        out.append("sources.allowed_axioms")
    return out


def accept(work, baseline, area=None):
    work, baseline = Path(work), Path(baseline)
    meas = work / "measured"
    mt = meas / "measured.toml"
    if not mt.exists():
        print(f"gate: no measurements in {meas}; run a tier first", file=sys.stderr)
        return 2
    reg = load_registry()
    if area is not None and area not in reg:
        print(f"gate: no area {area}; the areas are {', '.join(reg)}", file=sys.stderr)
        return 2
    tier = tomllib.loads(mt.read_text())["tier"]
    m = measure(work, tier, reg)
    bad = [s for s, (r, _) in m["status"].items() if r != "ok"]
    uf = m["run"].get("unit_failed")
    if bad or m["banned"] or uf:
        print(f"gate: not accepted: failed steps {bad}, banned {m['banned'][:3]}, unit failures {uf}", file=sys.stderr)
        return 1
    olds = load_baseline(baseline, reg)
    news, texts = {}, {}
    exp = baseline.parent / "expected"

    def changed_outputs(m, reg, expdir, a):
        # only a change the comparison sees rewrites a recorded copy, so the fields it normalizes
        # away (times, the order of logged lines) do not churn expected/
        out = []
        for name, (oa, t, how) in m["outputs"].items():
            if oa != a or t not in tiers(tier) or not (meas / name).exists() or same_as(reg, name) != name:
                continue
            e = expdir / a / name
            if not e.exists() or normalize(e.read_text(), how) != normalize((meas / name).read_text(), how):
                out.append(name)
        return out

    for a in reg:
        texts[a] = dump(to_baseline(m, a, reg, olds[a]), header(a))
        news[a] = as_doc(texts[a])
    outs = {a: changed_outputs(m, reg, exp, a) for a in reg}
    if area is not None:
        # the baseline the run started from (gate.sh copies it; a run from before that has none)
        against = meas / "against"
        start = None
        if (against / "baseline").is_dir() and (against / "registry" / "areas").is_dir():
            # the run measured with the registry it started with (main may have registered entries since)
            sreg = load_registry(against / "registry" / "areas")
            sm = measure(work, tier, sreg)
            start = load_baseline(against / "baseline", sreg)

        def as_started(b):
            # does the run measure area b exactly as the baseline it started from records it
            return (b in start
                    and not doc_diff(start[b], as_doc(dump(to_baseline(sm, b, sreg, start[b]), header(b))))
                    and not changed_outputs(sm, sreg, against / "expected", b))

        # another area's difference is that area's regression or acceptance, not this one's, unless
        # the run measured the area as its starting baseline records it: then the difference is that
        # baseline's own move since the run started (another landing), and the current one stays
        others, moved = {}, []
        for b in reg:
            d = [] if b == area else doc_diff(olds[b], news[b]) + [f"expected/{b}/{n}" for n in outs[b]]
            if d and start is not None and as_started(b):
                moved.append(b)
            elif d:
                others[b] = d
        if others:
            for b, d in others.items():
                print(f"gate: not accepted: area {b} measured entries that differ from its baseline: {', '.join(d[:12])}"
                      + (" …" if len(d) > 12 else ""), file=sys.stderr)
            print(f"gate: accept them with `accept --area` of their area, or all areas with `accept`", file=sys.stderr)
            return 1
        # the area's own baseline moved since the run started: the run was compared with a stale one
        # (unless what would be written is already the current text)
        since = doc_diff(start[area], olds[area]) if start is not None and area in start else []
        own = baseline / f"{area}.toml"
        if since and not (own.exists() and own.read_text() == texts[area]):
            print(f"gate: not accepted: area {area}'s baseline changed since this run started "
                  f"({', '.join(since[:12])}{' …' if len(since) > 12 else ''}); rerun the tier on the current tree",
                  file=sys.stderr)
            return 1
        if moved:
            print(f"gate: kept the current baseline of {', '.join(moved)}: it changed since this run started, which "
                  f"measured it as it was then; a change since then that reaches area {area} without moving "
                  f"its entries (the prelude, a tactic) still needs a rerun")
    written = []
    for a in ([area] if area is not None else list(reg)):
        f = baseline / f"{a}.toml"
        if not f.exists() or f.read_text() != texts[a]:
            baseline.mkdir(parents=True, exist_ok=True)
            f.write_text(texts[a])
            written.append(str(f))
        for name in outs[a]:
            (exp / a / name).parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(meas / name, exp / a / name)
            written.append(str(exp / a / name))
    print(f"gate: accepted the {tier} measurements of {work}" + (f" for area {area}" if area else "")
          + (": wrote " + ", ".join(written) if written else ": nothing changed"))
    return 0


def list_entries(tier=None):
    reg = load_registry()
    for a, kind, name, e in entries(reg):
        if tier is not None and not measured_in(e, tier):
            continue
        extra = []
        if e.get("compare_in"):
            extra.append(f"compared in {','.join(e['compare_in'])}")
        if e.get("same_as"):
            extra.append(f"compared with {e['same_as']}")
        if e.get("encoding", "arity") != "arity":
            extra.append(f"encoding {e['encoding']}")
        print(f"{a:16} {kind:9} {name:24} {e['tier']:6} {'; '.join(extra)}".rstrip())
    return 0


if __name__ == "__main__":
    a = sys.argv[1:]
    if a[:1] == ["check"] and len(a) == 4 and a[3] in TIERS:
        sys.exit(check(*a[1:]))
    if a[:1] == ["accept"] and len(a) == 3:
        sys.exit(accept(*a[1:]))
    if a[:1] == ["accept"] and len(a) == 5 and a[3] == "--area":
        sys.exit(accept(a[1], a[2], a[4]))
    if a[:1] == ["entries"] and len(a) == 2 and a[1] in TIERS:
        for _, kind, name, e in entries(load_registry()):
            if measured_in(e, a[1]):
                print(kind, name)
        sys.exit(0)
    if a[:1] == ["list"] and (len(a) == 1 or (len(a) == 2 and a[1] in TIERS)):
        sys.exit(list_entries(*a[1:]))
    print(__doc__, file=sys.stderr)
    sys.exit(2)
