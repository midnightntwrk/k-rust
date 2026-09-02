#!/usr/bin/env python3
"""Build summary.md from results.toml."""
import sys, tomllib, re, collections, time
path = sys.argv[1] if len(sys.argv) > 1 else "results.toml"
out = sys.argv[2] if len(sys.argv) > 2 else "summary.md"
data = tomllib.load(open(path, "rb"))
cases = data.get("case", [])

def subsystem(step, case):
    v = step.get("verdict"); st = step.get("stage", ""); kind = step.get("step"); div = (step.get("divergence") or "") + (step.get("reason") or "")
    if v == "krust-unsupported": return "CLI (flag or tool without krust equivalent)"
    if case.get("kind") == "fail" and kind == "kompile": return "kompile checks (definition checks / warnings-as-errors)"
    changing = [f for f in step.get("dropped_flags", []) if re.match(r"--coverage|--top-cell|-O\d|--enable-search|--allow-anywhere|--emit-json|--outer-parsed", f)]
    if v == "mismatch" and changing and kind == "kompile": return "CLI (reference kompile flag dropped for krust: " + ", ".join(changing)[:40] + ")"
    if "kprint failed" in div: return "KORE emission (kprint cannot unparse krust output)"
    if v == "reference-error": return "oracle (reference toolchain or stale .out)"
    if kind == "kompile":
        if case.get("kind") == "fail":
            return "kompile checks (definition checks / warnings-as-errors)"
        if v == "krust-error":
            return {"outer-parse": "outer", "inner-parse": "inner/disambiguation (rule parsing)"}.get(st, "kompile passes")
        if v == "mismatch":
            if re.search(r"inj\{|injection|Inj", div): return "injections/KORE emission"
            if re.search(r"attributes|module count|module name", div): return "module_to_kore/KORE emission"
            return "kompile passes / KORE emission"
    if kind in ("krun", "search"):
        if v == "krust-error":
            return {"inner-parse": "inner/disambiguation (program parsing)", "outer-parse": "outer"}.get(st, "backend execution")
        if v == "mismatch":
            if "kprint failed" in div: return "KORE emission (kprint cannot unparse krust output)"
            return "backend execution"
    if kind == "kast":
        return "inner/disambiguation (program parsing)" if v in ("krust-error", "mismatch") else "CLI"
    if kind == "kprove":
        if v == "krust-error" and st in ("outer-parse", "inner-parse"): return "inner/disambiguation (claim parsing)"
        return "backend proof"
    if kind == "kparse": return "CLI (kparse)"
    return "unclassified"

verdicts = collections.Counter(c["verdict"] for c in cases)
stages = collections.Counter(c["stage"] for c in cases)
fb = collections.Counter(c.get("fallback_verdict") for c in cases if c.get("fallback_verdict"))
kinds = collections.Counter(c["kind"] for c in cases)
backends = collections.Counter(c["backend"] for c in cases)
steps = [(c, s) for c in cases for s in c.get("step", [])]
step_verdicts = collections.Counter(s.get("verdict") for _, s in steps)
step_kinds = collections.Counter((s.get("step"), s.get("verdict")) for _, s in steps)
fb_steps = collections.Counter(s.get("fallback_verdict") for _, s in steps if s.get("fallback_sort"))
groups = collections.defaultdict(list)
for c, s in steps:
    if s.get("verdict") in ("mismatch", "krust-error", "reference-error"):
        groups[subsystem(s, c)].append((c, s))
unsupported = collections.Counter()
for c, s in steps:
    if s.get("verdict") == "krust-unsupported":
        unsupported[re.sub(r"^.*?: ", "", s.get("reason", ""))[:90]] += 1

L = ["# regression-new conformance summary", "", f"Generated {time.strftime('%Y-%m-%d %H:%M')} from `results.toml` ({len(cases)} leaf cases, {len(steps)} driven steps).",
     "Method: `run.py` (see its docstring); the invocation selects concurrency and per-case budgets.",
     "Verdict of a case is the worst verdict of its steps (reference-error < krust-error < mismatch < krust-unsupported = skipped-with-reason < match).",
     "`stage` is the furthest stage krust reached on the faithful command line; `fallback_*` fields re-parse `$PGM:K`/`KItem` programs with the sort the reference `kast --output kore` assigns, so backend stages can still be observed behind the K/KItem start-sort limitation.",
     "", "## Case verdicts", ""]
L += ["| verdict | cases |", "|---|---|"] + [f"| {k} | {v} |" for k, v in verdicts.most_common()]
L += ["", "Case verdicts after the K/KItem sort fallback (cases that used it):", "", "| fallback verdict | cases |", "|---|---|"] + [f"| {k} | {v} |" for k, v in fb.most_common()]
L += ["", "## Stage reached (per case, faithful command line)", "", "| stage | cases |", "|---|---|"] + [f"| {k} | {v} |" for k, v in stages.most_common()]
L += ["", "Cases by Makefile kind: " + ", ".join(f"{k}={v}" for k, v in kinds.items()) + "; by requested backend: " + ", ".join(f"{k}={v}" for k, v in backends.items()) + ".",
      "Backend requested `llvm` still gets its krust run with `--backend llvm` KORE for kompile and the in-process Rust backend for execution; the mismatch of backends is recorded in the case's `backend` field, never as a skip.",
      "", "## Step verdicts", "", "| step | verdict | count |", "|---|---|---|"]
L += [f"| {k[0]} | {k[1]} | {v} |" for k, v in sorted(step_kinds.items(), key=lambda x: (str(x[0][0]), str(x[0][1])))]
L += ["", f"Steps that used the sort fallback: {sum(fb_steps.values())} (" + ", ".join(f"{k}={v}" for k, v in fb_steps.most_common()) + ").", ""]
L += ["## Mismatches and errors grouped by the subsystem most likely responsible", ""]
for g, items in sorted(groups.items(), key=lambda x: -len(x[1])):
    L += [f"### {g} ({len(items)} steps in {len(set(c['name'] for c, _ in items))} cases)", ""]
    seen = collections.Counter()
    for c, s in items:
        key = (c["name"], s.get("step"))
        seen[c["name"]] += 1
        if seen[c["name"]] > 3: continue
        head = f"- `{c['name']}` {s.get('step')} {s.get('test', '') or ''} [{s.get('verdict')}, stage {s.get('stage', '-')}]"
        if s.get("fallback_sort"): head += f" (fallback sort {s['fallback_sort']}: {s.get('fallback_verdict')})"
        div = (s.get("divergence") or s.get("reason") or "").strip().splitlines()
        L.append(head)
        if div: L.append("  - `" + div[0][:160].replace("`", "'") + "`")
    extra = [n for n, k in seen.items() if k > 3]
    if extra: L.append(f"- (more steps elided for: {', '.join(extra)})")
    L.append("")
kore_mm = collections.Counter(c["backend"] for c, s in steps if s.get("step") == "kompile" and s.get("verdict") == "mismatch" and not s.get("dropped_flags") and c["kind"] != "fail")
kore_ok = collections.Counter(c["backend"] for c, s in steps if s.get("step") == "kompile" and s.get("verdict") == "match" and c["kind"] != "fail")
L += ["## definition.kore agreement by requested backend (kompile steps of ktest cases, no dropped flags)", "", "| backend | match | mismatch |", "|---|---|---|"]
L += [f"| {b} | {kore_ok[b]} | {kore_mm[b]} |" for b in sorted(set(kore_ok) | set(kore_mm))]
stale = [(c, s) for c, s in steps if s.get("oracle_confirmed") is False]
L += ["", f"## Stale or unreproduced oracles ({len(stale)} steps)", "", "Steps whose checked-in .out the pinned reference toolchain did not reproduce when re-run verbatim (verdict reference-error; krust's divergence is still recorded).", ""]
L += [f"- `{c['name']}` {s.get('step')} {s.get('test', '') or s.get('out', '')}: " + ((s.get('oracle_output') or '').strip().splitlines() or ['(no output)'])[0][:140].replace('`', "'") for c, s in stale[:60]]
L += [""]
L += ["## Unsupported reference flags/tools (krust-unsupported steps)", "", "| reason | steps |", "|---|---|"] + [f"| {k} | {v} |" for k, v in unsupported.most_common(30)]
L += ["", "## Coverage notes", ""]
for c in cases:
    if c["verdict"] == "skipped-with-reason" or c.get("notes"):
        L.append(f"- `{c['name']}` ({c['kind']}): {c['verdict']}; {c.get('reason', '')}; notes: {'; '.join(c.get('notes', []))}")
open(out, "w").write("\n".join(L) + "\n")
print(f"wrote {out}: {len(cases)} cases, verdicts {dict(verdicts)}")
