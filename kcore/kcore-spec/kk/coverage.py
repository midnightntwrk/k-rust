"""kk/COVERAGE.toml's rows table: for every row and `cases` entry of test/constructs/rows.toml whose
status is supported or parameter, whether kore.k's encoding of an object definition (`KK.encDef`,
KcoreSpec/KKEncDef.lean) has a place for what the reader makes of the row's construct. `encDef d` is
`some` exactly where `KK.encodable d`, the conjunction of eleven Bools (`encDef_isSome`); every verdict
below is computed from `kcore encodable`, which evaluates them, and none is written by hand.

Usage (from kcore-spec):
  python3 -I kk/coverage.py gen              rewrite COVERAGE.toml after its marker line
  python3 -I kk/coverage.py check [--report] exit 1 unless COVERAGE.toml is what gen writes, the
                                             floor holds, rows.toml's module rows carry the kimp
                                             computed below and every entry has a verdict (with
                                             --report the entries without evidence text are listed,
                                             not failed)
  python3 -I kk/coverage.py kimp [--write]   the kimp of each E6 module row (below); --write sets it
                                             in rows.toml
  python3 -I kk/coverage.py fixtures [--write]  for each entry with no evidence text, a fixture:
                                             for an E6 symbol or axiom row, of the fixtures whose
                                             kompiled text holds its sentence and is read by the
                                             reader, the one holding the fewest library modules,
                                             then the smallest, then by name (--write names it in
                                             rows.toml); for another entry, the first fixture its
                                             own `evidence` names that the reader reads, printed
                                             only (whether the evidence names it as the entry's
                                             own is read by hand)

An entry's key is the row's key, or "<row key>#cases[<i>]" for the i-th (from 0) of its `cases`; a
case of its row's status without `fixture` or `kimp` takes its row's. Its verdict, by the first rule that applies:
  1. A `fixture`: KK.encodable of the reader's semantics of the fixture's kompiled text (from
     test/constructs/kfix.py's cache, its paths restored, or the fixture's `kore` text): covered with
     `case` the text, or refused with `bool` the first false conjunct and `refused_on` the text. A
     refused verdict on a fixture holding several constructs may be caused by another construct of
     it; covered means the whole text has a form. A text the reader refuses fails gen (such a row is
     not supported).
  2. An E6 hook row (key hook:HOOK:DECL): `kcore encodable --library`'s tables. A hooked symbol is
     covered where KK.readApp gives an application of its registered hook a form (KK.libCollOf,
     KK.hookCodes, KK.derivedHook), else refused appsOK; a sort-parametric one (KEQUAL.ite), whose
     applications the reader reads as parameter symbols with the hook as `impl`, and a hook the
     registry does not interpret (a library parameter) are refused paramsOK. A hooked sort (DECL SortX) and an E6 token row (token:SortX)
     are covered where the registry sort X has a form (a collection whose unit has one; literals
     KK.encLit writes, at a sort KK.litsOK admits), else refused with the Bool the table names.
     A hook covered by KK.derivedHook (=/=Bool, as hk 22 BOOL.not [hk 23 BOOL.eq ARGS]) has as its
     case, beside the composition, the rewrite rules of ref-kimp's text whose right side applies DECL
     (`kimp_rules_applying`: their Source file and Location), so that the composition is shown at a
     rule kimp's semantics fires.
  3. `kimp = true`: KK.encodable of f2-examples/ref-kimp.kore's semantics (true: the floor).
  4. An E6 module row (key module:M): covered where every hook row of M (the declarations of M's
     library text with a hook attribute, `kcore encodable --library`) has a covered entry, else
     refused, naming the first that has none in `first_uncovered` and its `bool`.
  Any other entry has no evidence text: gen lists it in the file, with no verdict, and exits 1
  (`fixtures` proposes one).
The kimp of an E6 module row is whether ref-kimp's text holds a sentence of the module (the reader's
moduleAt of each builtin sentence, `kcore encodable`'s `modules`).
Floor (findings/work/decision-dec3.md section 2.4): KK.encodable of ref-kimp's text is true.
Results are cached in .lake/kk-coverage/results.json by the text's and the kcore binary's sha256.
"""
import concurrent.futures, hashlib, json, os, re, subprocess, sys, tomllib

K = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(K, "test/constructs"))
sys.dont_write_bytecode = True
import kfix  # noqa: E402

ROWS = os.path.join(K, "test/constructs/rows.toml")
COV = os.path.join(K, "kk/COVERAGE.toml")
KIMP = "f2-examples/ref-kimp.kore"
KCORE = os.environ.get("KCORE_BIN") or os.path.join(K, ".lake/build/bin/kcore")
WORK = os.path.join(K, ".lake/kk-coverage")
MARK = "# ---- generated by kk/coverage.py gen from rows.toml and `kcore encodable`; do not edit below ----"
PARTS = ["ovlsOK", "paramsOK", "appsOK", "headsOK", "litsOK", "subsortsOK", "colPatsOK", "asOK", "ensOK",
         "shapesOK", "collFormOK"]


def sha(b):
    return hashlib.sha256(b if isinstance(b, bytes) else b.encode()).hexdigest()


KSHA = sha(open(KCORE, "rb").read()) if os.path.exists(KCORE) else None


def load_cache():
    p = os.path.join(WORK, "results.json")
    try:
        return json.load(open(p))
    except (OSError, ValueError):
        return {}


def save_cache(c):
    os.makedirs(WORK, exist_ok=True)
    p = os.path.join(WORK, "results.json")
    tmp = f"{p}.{os.getpid()}"
    json.dump(c, open(tmp, "w"), sort_keys=True)
    os.replace(tmp, p)


def text_of(name):
    """(the path kcore reads, the cwd, the text's sha256) of fixture NAME's kompiled text, or
    (None, None, why)."""
    if name == KIMP:
        p = os.path.join(K, KIMP)
        return p, K, sha(open(p, "rb").read())
    if not os.path.isdir(os.path.join(kfix.FX, name)):
        return None, None, f"no fixture directory {name}"
    c = kfix.conf(name)
    if "kore" in c:
        p = os.path.join(K, c["kore"])
        return p, K, sha(open(p, "rb").read())
    h = kfix.recorded_sha(name)
    if not h:
        return None, None, f"fixture {name} has no kompiled text (an error fixture, or not run)"
    kore = kfix.cache_get(h)
    if kore is None:
        return None, None, f"fixture {name}: its text ({h[:12]}) is not in kfix.py's cache {kfix.CACHE}"
    src = os.path.join(WORK, "src", h)
    p = os.path.join(src, "out/definition.kore")
    if not os.path.exists(p):
        bd = kfix.FAKE_BUILTIN
        raw = kore.replace("BUILTIN/", bd + "/").replace("FIXTURE/", src + "/").replace("FIXTURE", src)
        os.makedirs(os.path.dirname(p), exist_ok=True)
        tmp = f"{p}.{os.getpid()}"
        open(tmp, "w").write(raw)
        os.replace(tmp, p)
    return p, src, h


def run_encodable(path, cwd):
    a = subprocess.run(["timeout", "600", KCORE, "encodable", path], cwd=cwd, capture_output=True, text=True,
                       env={**os.environ, "LEAN_NUM_THREADS": "1"})
    if a.returncode != 0:
        return {"error": (a.stderr.strip() or a.stdout.strip() or f"exit {a.returncode}").splitlines()[-1][:300]}
    return json.loads(a.stdout.strip().splitlines()[-1])


def encodable_of(names):
    """{text name: kcore encodable's object, or {"error": why}} for the named texts."""
    cache, out, todo = load_cache(), {}, []
    for n in sorted(set(names)):
        p, cwd, h = text_of(n)
        if p is None:
            out[n] = {"error": h}
        elif f"{h}:{KSHA}" in cache:
            out[n] = cache[f"{h}:{KSHA}"]
        else:
            todo.append((n, p, cwd, h))
    jobs = max(1, min(8, (os.cpu_count() or 2) // 4))
    with concurrent.futures.ThreadPoolExecutor(jobs) as ex:
        for (n, p, cwd, h), r in zip(todo, ex.map(lambda t: run_encodable(t[1], t[2]), todo)):
            out[n] = r
            if "error" not in r or r["error"].endswith("KORE read error") or ": refused: " in r["error"]:
                cache[f"{h}:{KSHA}"] = r
    if todo:
        save_cache(cache)
    return out


def library():
    a = subprocess.run([KCORE, "encodable", "--library"], capture_output=True, text=True)
    if a.returncode != 0:
        raise SystemExit(f"coverage: kcore encodable --library: {a.stderr.strip()}")
    hooks, sorts, mods, mhooks, msrc = {}, {}, [], {}, {}
    for line in a.stdout.splitlines():
        f = line.split("\t")
        if f[0] == "hook": hooks[f[1]] = (f[2], f[3])
        elif f[0] == "sort": sorts[f[1]] = (f[2], f[3])
        elif f[0] == "module": mods.append(f[1]); mhooks[f[1]] = []; msrc[f[1]] = f[2]
        elif f[0] == "mhook": mhooks[f[1]].append(f"hook:{f[2]}:{f[3]}")
    return hooks, sorts, mods, mhooks, msrc


def split_top(s, i):
    """The arguments of the application whose `(` is at s[i], split at its top-level commas, and the
    index after its `)`."""
    depth, start, args, q = 0, i + 1, [], False
    for j in range(i, len(s)):
        c = s[j]
        if q:
            if c == "\\": q = "esc"
            elif q == "esc": q = True
            elif c == '"': q = False
            continue
        if c == '"': q = True
        elif c == "(": depth += 1
        elif c == ")":
            depth -= 1
            if depth == 0:
                args.append(s[start:j]); return args, j + 1
        elif c == "," and depth == 1:
            args.append(s[start:j]); start = j + 1
    raise ValueError("unbalanced")


def kimp_rules_applying(decl):
    """FILE:LINE:COL (the Source file's name and the Location) of each rewrite axiom of ref-kimp's
    text whose right side (the second argument of \\rewrites) applies the symbol DECL."""
    text = open(os.path.join(K, KIMP)).read()
    out = []
    for blk in re.split(r"\n(?=\s*axiom\s*\{)", text):
        m = re.match(r"\s*axiom\s*\{\}\s*\\rewrites\{[^(]*\(", blk)
        if not m: continue
        args, end = split_top(blk, m.end() - 1)
        if len(args) != 2 or not re.search(r"(?<![\w'])" + re.escape(decl) + r"\{", args[1]): continue
        loc = re.search(r'Location\{\}\("Location\((\d+),(\d+),', blk[end:])
        src = re.search(r'Source\{\}\("Source\(([^)]*)\)', blk[end:])
        out.append(f"{os.path.basename(src[1]) if src else '?'}:{loc[1]}:{loc[2]}" if loc else "?")
    return out


def entries(rows):
    """(list, key, row, entry) for every supported or parameter row and `cases` entry, in file order;
    a case of its row's status takes the row's fixture and kimp where it has none (a case of another
    status is a shape the row's evidence does not show)."""
    for l, tab in rows.items():
        for k, r in tab.items():
            if r.get("status") in ("supported", "parameter"):
                yield l, k, r, r
            cs = r.get("cases")
            if isinstance(cs, list):
                for i, c in enumerate(cs):
                    if isinstance(c, dict) and c.get("status") in ("supported", "parameter"):
                        e = dict(c)
                        if c["status"] == r.get("status"):
                            for f in ("fixture", "kimp"):
                                if f not in e and f in r: e[f] = r[f]
                        yield l, f"{k}#cases[{i}]", r, e


def fixture_of(e):
    f = e.get("fixture")
    return f if isinstance(f, str) and f != "none" else None


def verdict_text(res, text):
    if "error" in res:
        return None, f"{text}: {res['error']}"
    if res["encodable"]:
        return {"verdict": "covered", "by": "fixture" if text != KIMP else "kimp", "case": text}, None
    b = next(p for p in PARTS if not res[p])
    return {"verdict": "refused", "by": "fixture" if text != KIMP else "kimp", "bool": b, "refused_on": text}, None


def compute(rows):
    """{(list, key): entry fields}, the failures, the library tables, ref-kimp's result."""
    hooks, sorts, mods, mhooks, msrc = library()
    ents = list(entries(rows))
    res = encodable_of([fixture_of(e) for _, _, _, e in ents if fixture_of(e)] + [KIMP])
    out, bad, modrows = {}, [], []
    for l, k, r, e in ents:
        fx = fixture_of(e)
        if fx:
            v, err = verdict_text(res[fx], fx)
            if err: bad.append(f"{l} {k}: {err}")
            else: out[(l, k)] = v
        elif l == "E6" and k.startswith("hook:"):
            _, h, decl = k.split(":", 2)
            if decl.startswith("Sort"):
                st, form = sorts.get(decl[4:], ("refused", None))
                if form is None:
                    bad.append(f"{l} {k}: {decl[4:]} is no registry sort"); continue
                out[(l, k)] = ({"verdict": "covered", "by": "sort table", "case": f"{decl[4:]}: {form}"} if st == "covered"
                               else {"verdict": "refused", "by": "sort table", "bool": form, "refused_on": decl[4:]})
            elif h in hooks:
                st, form = hooks[h]
                if st == "covered" and form.startswith("KK.derivedHook"):
                    rs = kimp_rules_applying(decl)
                    if rs: form += "; applied by ref-kimp's rule" + ("s" if len(rs) > 1 else "") + " at " + ", ".join(rs)
                out[(l, k)] = ({"verdict": "covered", "by": "hook table", "case": f"{h}: {form}"} if st == "covered"
                               else {"verdict": "refused", "by": "hook table", "bool": form, "refused_on": h})
            else:
                out[(l, k)] = {"verdict": "refused", "by": "hook table", "bool": "paramsOK",
                               "refused_on": f"{h}: no registry hook (a library parameter)"}
        elif l == "E6" and k.startswith("token:"):
            s = k.split(":", 1)[1][4:]
            if s not in sorts:
                bad.append(f"{l} {k}: {s} is no registry sort"); continue
            st, form = sorts[s]
            out[(l, k)] = ({"verdict": "covered", "by": "sort table", "case": f"{s}: {form}"} if st == "covered"
                           else {"verdict": "refused", "by": "sort table", "bool": form, "refused_on": s})
        elif e.get("kimp") is True:
            v, err = verdict_text(res[KIMP], KIMP)
            if err: bad.append(f"{l} {k}: {err}")
            else: out[(l, k)] = v
        elif l == "E6" and k.startswith("module:"):
            modrows.append((l, k))
        else:
            bad.append(f"{l} {k}: no evidence text (no fixture, kimp not true, not a hook, token or module row)")
            NOEV.append((l, k))
    for l, k in modrows:
        m = k.split(":", 1)[1]
        if m not in mhooks:
            bad.append(f"{l} {k}: {m} is no library module"); continue
        first = None
        for hk in mhooks[m]:
            if hk not in rows.get("E6", {}):
                bad.append(f"{l} {k}: its declaration {hk} is no E6 row"); first = first or (hk, "no row"); continue
            v = out.get(("E6", hk))
            if v is None:
                first = first or (hk, f"status {rows['E6'][hk].get('status')}")
            elif v["verdict"] != "covered":
                first = first or (hk, v["bool"])
            if first: break
        if first is None:
            n = len(mhooks[m])
            out[(l, k)] = {"verdict": "covered", "by": "module hooks",
                           "case": f"its {n} hook rows covered" if n else "no hook row"}
        else:
            out[(l, k)] = {"verdict": "refused", "by": "module hooks", "bool": first[1], "first_uncovered": first[0]}
    return out, bad, (hooks, sorts, mods, mhooks, msrc), res[KIMP]


NOEV = []


def bad_entries(bad):
    """(list, row key, case index or None) of the entries compute found no evidence text for."""
    for l, k in NOEV:
        m = re.match(r"^(.*)#cases\[(\d+)\]$", k)
        yield (l, m[1], int(m[2])) if m else (l, k, None)


def tq(s):
    return json.dumps(s, ensure_ascii=False)


def render(rows, out, noev):
    order = [(l, k) for l, k, _, _ in entries(rows) if (l, k) in out]
    cov = [x for x in order if out[x]["verdict"] == "covered"]
    ref = [x for x in order if out[x]["verdict"] == "refused"]
    per = {}
    for x in ref:
        if out[x]["bool"] in PARTS: per[out[x]["bool"]] = per.get(out[x]["bool"], 0) + 1
    by = {}
    for x in order: by[out[x]["by"]] = by.get(out[x]["by"], 0) + 1
    lines = [MARK, "#",
             "# One table per supported or parameter row (and `cases` entry, \"<row key>#cases[<i>]\") of",
             "# test/constructs/rows.toml, under [rows.LIST.\"KEY\"]; kk/coverage.py's docstring gives the rules.",
             "#   verdict  covered: KK.encDef has a form for the reader's semantics of the evidence; refused: it",
             "#            has none.",
             "#   by       the evidence: fixture (its kompiled text), kimp (f2-examples/ref-kimp.kore), hook table,",
             "#            sort table (`kcore encodable --library`), module hooks (the module's hook rows).",
             "#   case     for covered, the text or the table entry; bool, for refused, the first false conjunct",
             "#            of KK.encodable (a fixture's or ref-kimp's text), the table's Bool, or the first",
             "#            uncovered hook row's; refused_on, the text or table entry; first_uncovered, the hook",
             "#            row a module row is refused by.",
             f"# Entries: {len(order)}; covered {len(cov)}; refused {len(ref)}"
             + (" (" + ", ".join(f"{b} {n}" for b, n in sorted(per.items(), key=lambda t: (-t[1], t[0]))) + ")" if per else "")
             + ".",
             "# By evidence: " + ", ".join(f"{b} {n}" for b, n in sorted(by.items(), key=lambda t: (-t[1], t[0]))) + ".",
             f"# No evidence text, no verdict (a fixture is owed; check fails on them, check --report lists them): {len(noev)}"
             + (":" if noev else ".")]
    lines += [f"#   {x}" for x in noev]
    lines += [""]
    for l, k in order:
        v = out[(l, k)]
        lines.append(f"[rows.{l}.{tq(k)}]")
        for f in ("verdict", "by", "case", "bool", "refused_on", "first_uncovered"):
            if f in v: lines.append(f"{f} = {tq(v[f])}")
        lines.append("")
    return "\n".join(lines), len(cov), len(ref), per


def head_of_file():
    t = open(COV).read()
    i = t.find("\n" + MARK)
    return (t if i < 0 else t[:i]).rstrip("\n") + "\n\n"


def module_kimp(kimp_res, mods):
    held = set(kimp_res.get("modules", []))
    return {f"module:{m}": m in held for m in mods}


def kimp_lines(rows, mk):
    """rows.toml's module rows whose kimp differs from the computed one: (key, computed)."""
    return [(k, mk[k]) for k, r in rows.get("E6", {}).items() if k in mk and r.get("kimp") != mk[k]]


def set_fields(edits):
    """In rows.toml, add `FIELD = VALUE` (VALUE as TOML) to each entry (list, key, case index or None):
    a row's after its `status = "...", `, a case's at the start of its inline table. The entry must
    not have the field already; the file read back must differ from the one before by exactly these
    fields, else nothing is written."""
    old = open(ROWS).read()
    lines = old.split("\n")
    sec, done = None, set()
    for i, ln in enumerate(lines):
        m = re.match(r"^\[(\w+)\]$", ln)
        if m: sec = m[1]; continue
        # a line's cases from the last, so that an insertion leaves the earlier cases' starts as found
        for n, (l, k, ci, f, v) in sorted(enumerate(edits), key=lambda t: -1 if t[1][2] is None else -1 - t[1][2]):
            pre = tq(k) + " = { status = "
            if sec != l or not ln.startswith(pre): continue
            if ci is None:
                ln = re.sub(r"^(" + re.escape(pre) + r"\"[\w-]+\", )", lambda mm: mm[1] + f"{f} = {v}, ", ln, count=1)
            else:
                j = ln.index("cases = [")
                for _ in range(ci + 1):
                    j = ln.index("{ case = ", j + 1)
                ln = ln[:j + 2] + f"{f} = {v}, " + ln[j + 2:]
            done.add(n)
        lines[i] = ln
    new = "\n".join(lines)
    want = tomllib.loads(old)
    for l, k, ci, f, v in edits:
        e = want[l][k] if ci is None else want[l][k]["cases"][ci]
        if f in e: raise SystemExit(f"coverage: {l} {k} {ci}: already has {f}")
        e[f] = tomllib.loads(f"x = {v}")["x"]
    if len(done) != len(edits) or tomllib.loads(new) != want:
        raise SystemExit("coverage: rows.toml edit does not give exactly the fields asked; nothing written")
    open(ROWS, "w").write(new)
    return len(done)


def sentence_in(text, key, msrc):
    """Whether the kompiled text (paths restored) holds E6 row KEY's sentence: a symbol row's
    declaration, or an axiom row's axiom (its module's file and its line and column)."""
    kind, mod, rest = key.split(":", 2)
    if kind == "symbol":
        return re.search(r"^\s*(?:hooked-)?symbol " + re.escape(rest) + r"\{", text, re.M) is not None
    if kind == "axiom":
        f = msrc.get(mod, "").split("//")[-1]
        lc = rest.split("#")[0].split(":")
        if len(lc) != 2 or not f: return False
        pat = re.compile(r"Location\{\}\(\"Location\(" + lc[0] + "," + lc[1] + r",")
        for blk in re.split(r"\n(?=\s*axiom\s*\{)", text):
            if pat.search(blk) and ("/include/kframework/builtin/" + f + ")") in blk and blk.lstrip().startswith("axiom"):
                return True
    return False


def main():
    cmd = sys.argv[1:2]
    if not os.path.exists(KCORE):
        raise SystemExit(f"coverage: no kcore binary at {KCORE} (lake build kcore)")
    rows = tomllib.load(open(ROWS, "rb"))
    if cmd == ["kimp"]:
        hooks, sorts, mods, mhooks, msrc = library()
        mk = module_kimp(encodable_of([KIMP])[KIMP], mods)
        diff = kimp_lines(rows, mk)
        for k, v in diff: print(f"E6 {k}: kimp = {str(v).lower()}")
        if "--write" in sys.argv[2:] and diff:
            print(f"coverage: {set_fields([('E6', k, None, 'kimp', str(v).lower()) for k, v in diff])} rows set")
        return 0
    if cmd == ["fixtures"]:
        out, bad, lib, _ = compute(rows)
        msrc = lib[4]
        names = sorted(n for n in os.listdir(kfix.FX) if kfix.recorded_sha(n)
                       and os.path.exists(os.path.join(kfix.CACHE, kfix.recorded_sha(n) + ".kore")))
        texts, edits = {}, []
        for l, k, ci in bad_entries(bad):
            found, cands = None, []
            if l == "E6" and ci is None:
                for n in names:
                    if n not in texts:
                        p, _, _ = text_of(n)
                        texts[n] = open(p).read() if p else ""
                    if sentence_in(texts[n], k, msrc):
                        cands.append(n)
                res = encodable_of(cands)
                ok = [n for n in cands if "error" not in res[n]]
                if ok:
                    found = min(ok, key=lambda n: (len(res[n]["modules"]), len(texts[n]), n))
            else:
                e = rows[l][k] if ci is None else rows[l][k]["cases"][ci]
                ev = e.get("evidence", "")
                cands = [m for m in re.findall(r"fixtures/([a-z0-9][a-z0-9-]*)", json.dumps(ev))
                         if os.path.isdir(os.path.join(kfix.FX, m))]
                res = encodable_of(cands)
                found = next((n for n in cands if "error" not in res[n]), None)
            key = k if ci is None else f"{k}#cases[{ci}]"
            sentence = l == "E6" and ci is None
            print(f"{l} {key}\t{found or 'none'}\t{len(cands)} candidates" + ("" if sentence or not found else "\t(cited; not written)"))
            if found and sentence: edits.append((l, k, ci, "fixture", tq(found)))
        if "--write" in sys.argv[2:] and edits:
            print(f"coverage: {set_fields(edits)} entries given a fixture")
        return 0
    if cmd not in (["gen"], ["check"]):
        raise SystemExit(__doc__)
    report = "--report" in sys.argv[2:]
    out, bad, lib, kimp_res = compute(rows)
    noev = [f"{l} {k}" for l, k in NOEV]
    fail = [b for b in bad if "no evidence text" not in b]
    if "error" in kimp_res or not kimp_res.get("encodable"):
        fail.append(f"floor: KK.encodable of {KIMP} is not true: {kimp_res}")
    mk = module_kimp(kimp_res, lib[2])
    fail += [f"E6 {k}: kimp is not {str(v).lower()} (ref-kimp's modules; coverage.py kimp --write)"
             for k, v in kimp_lines(rows, mk)]
    if [b for b in bad if "no evidence text" not in b]:
        for f in fail: print("coverage: " + f)
        return 1
    body, nc, nr, per = render(rows, out, noev)
    text = head_of_file() + body
    tomllib.loads(text)
    print(f"coverage: {nc + nr + len(noev)} entries, covered {nc}, refused {nr}"
          + (" (" + ", ".join(f"{b} {n}" for b, n in sorted(per.items(), key=lambda t: (-t[1], t[0]))) + ")" if per else "")
          + f", no evidence text {len(noev)}")
    if cmd == ["gen"]:
        open(COV, "w").write(text)
        report = False
    elif open(COV).read() != text:
        fail.append("kk/COVERAGE.toml is not what kk/coverage.py gen writes")
    for x in noev: print(f"coverage: {x}: no evidence text, no verdict (a fixture is owed)")
    for f in fail: print("coverage: " + f)
    return 1 if fail or (noev and not report) else 0


if __name__ == "__main__":
    sys.exit(main())
