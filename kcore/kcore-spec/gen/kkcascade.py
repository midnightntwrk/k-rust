#!/usr/bin/env python3
"""kkcascade.py: the cascade text of kore.k's functions over sorted values, from the clauses of
RefKk.defn.sem.

Usage (from anywhere; the library built first):
  python3 -I gen/kkcascade.py facts SPEC [--print]
  python3 -I gen/kkcascade.py emit SPEC [--no-table] [--hb] [--out FILE] [--print]
  python3 -I gen/kkcascade.py check SPEC

SPEC (examples/ref-kk/User/cascade.toml) names the KORE text, the mirrors of kore.k's list sorts
(which constructors are a Lean list's `[]` and `::`, or an `Option`'s `none` and `some`, and the
Lean function that gives a value its term) and the functions to emit.

A probe (a Lean run that reads the KORE text as `definition_of` does) prints each function's
clauses, the constructors' signatures and the functions' symbols. From those alone:
- `facts` writes the table module: for every constructor of the text, `c₀.isCtor f = true`,
  `patternHooks.contains f = false`, its signature and its argument sorts; for every function,
  `c₀.isCtor g = false`, `isHook g = false`, `c₀.isParam g = false`; for the Int comparisons a
  `requires` reads, `c₀.isCtor h = false`, `isHook h = true`. Each is decided once, by the kernel.
- `emit` writes, per function, its clauses as literals (tied to `c₀.lookupFn` by `kernel_rfl`), the
  Lean function `F` (the cascade of its equations by priority, in the semantics' order, with an
  `Option` result) and `F.eval`, `F.eval_iff`; `--no-table` decides the symbol facts at each use
  instead of reading the table, `--hb` (or `hb = true` in SPEC) reports each `F.eval`'s heartbeats.
- `check` emits into a temporary file and compares with the committed module.

The proof of `F.eval` follows F: an induction on the list argument F recurses on, then per branch
of the cascade (a `split` per constructor pattern on a term argument, a `by_cases` per `requires`)
the equation that applies by `Eval.clause` (its place in the function's clause list by
`List.mem_cons_of_mem`), each equation of a smaller priority by `Fails` (the
pattern's constructor against the argument's, or the branch's negative hypothesis, or the
`requires` with the value `false`), and where no equation applies `Eval.rest`. Refused, with the
reason: a recursion that is not on one list argument with the other arguments unchanged, a pattern
below a constructor's arguments, a `requires` that is not an Int comparison of two variables, an
`ensures`, a premise or right-side predicate, existential variables, an aside clause, more than one
call in a right side, or a call below a constructor's argument.
"""
import json, os, re, subprocess, sys, tempfile, tomllib

KS = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
WRAP = ["systemd-run", "--user", "--scope", "-q", "-p", "MemoryMax=12G", "-p", "MemorySwapMax=0"]


class Refused(Exception):
    pass


PROBE = r'''import KcoreSpec
open KCore

partial def kcJ : Term → String
  | .var i => s!"[\"var\",{i}]"
  | .app f ts => s!"[\"app\",{f},[" ++ ",".intercalate (ts.map kcJ) ++ "]]"
  | .inj a b t => s!"[\"inj\",{a},{b},{kcJ t}]"
  | .as t i => s!"[\"as\",{kcJ t},{i}]"
  | .dv s (.int x) => s!"[\"dvi\",{s},{x}]"
  | .dv s (.bool b) => s!"[\"dvb\",{s},{b}]"
  | .dv s _ => s!"[\"dvo\",{s}]"
def kcO : Option Term → String
  | some t => kcJ t
  | none => "null"
def kcS (o : Option String) : String := match o with
  | some s => s.quote
  | none => "null"
def kcC : Cond → String
  | .top => "true"
  | _ => "false"

#eval show IO Unit from do
  let input ← IO.FS.readFile "@PATH@"
  let k ← match Kore.parseDefinition input with
    | .ok k => pure k
    | .error e => throw (IO.userError s!"KORE read error {e}")
  let d ← match Parse.parse k with
    | .ok d => pure d
    | .error r => throw (IO.userError s!"KCore's parse refuses it: {r.toText}")
  let c := d.sem
  for k in c.ctors do
    IO.println s!"C \{\"f\":{k.name},\"args\":{k.args},\"result\":{k.result}}"
  for f in c.allFns do
    IO.println s!"G {f.label}"
  for (f, fp) in withPres c.fns d.pres.fns do
    let cls := (withPres f.clauses fp.clauses).map fun (cl, cp) =>
      s!"\{\"vars\":{cl.vars},\"pats\":[" ++ ",".intercalate (cl.pats.map kcJ) ++ s!"],\"req\":{kcO cl.req}," ++
      s!"\"rhs\":{kcJ cl.rhs},\"ens\":{kcO cl.ens},\"prio\":{cl.prio},\"aside\":{cl.aside},\"exs\":{cl.exs}," ++
      s!"\"pre\":{kcC cl.pre},\"post\":{kcC cl.post},\"label\":{kcS cp.label},\"names\":[" ++
      ",".intercalate (cp.names.map (·.quote)) ++ "]}"
    IO.println (s!"F \{\"label\":{f.label},\"args\":{f.args},\"result\":{f.result},\"total\":{f.total},\"clauses\":[" ++
      ",".intercalate cls ++ "]}")
'''


def probe(kore):
    with tempfile.TemporaryDirectory(prefix="kkcascade-") as d:
        f = os.path.join(d, "Probe.lean")
        open(f, "w").write(PROBE.replace("@PATH@", os.path.abspath(kore)))
        env = dict(os.environ, LEAN_NUM_THREADS="1")
        r = subprocess.run(WRAP + ["timeout", "900", "lake", "env", "lean", "-j1", f], cwd=KS, env=env,
                           capture_output=True, text=True)
    if r.returncode != 0:
        raise Refused(f"the probe fails: {(r.stdout + r.stderr).strip()[-800:]}")
    ctors, fns, labels = {}, {}, []
    for l in r.stdout.split("\n"):
        if l.startswith("C "):
            k = json.loads(l[2:])
            ctors[k["f"]] = (k["args"], k["result"])
        elif l.startswith("G "):
            labels.append(int(l[2:]))
        elif l.startswith("F "):
            f = json.loads(l[2:])
            fns[f["label"]] = f
    return ctors, fns, labels


# ---------------------------------------------------------------------------------------------
# Terms: ("var", i) | ("app", f, [t]) | ("as", t, i) | ("dvi", s, x) | ("dvb", s, b) | ("inj", a, b, t)

def tm(j):
    if j[0] == "var":
        return ("var", j[1])
    if j[0] == "app":
        return ("app", j[1], [tm(x) for x in j[2]])
    if j[0] == "as":
        return ("as", tm(j[1]), j[2])
    if j[0] == "inj":
        return ("inj", j[1], j[2], tm(j[3]))
    if j[0] == "dvi":
        return ("dvi", j[1], j[2])
    if j[0] == "dvb":
        return ("dvb", j[1], j[2])
    return ("dvo", j[1])


def lit(t):
    """A term as a Lean literal of `KCore.Term`."""
    k = t[0]
    if k == "var":
        return f".var {t[1]}"
    if k == "app":
        return f".app {t[1]} [{', '.join(lit(x) for x in t[2])}]"
    if k == "as":
        return f".as ({lit(t[1])}) {t[2]}"
    if k == "inj":
        return f".inj {t[1]} {t[2]} ({lit(t[3])})"
    if k == "dvi":
        x = t[2]
        return f".dv {t[1]} (.int {x if x >= 0 else f'({x})'})"
    if k == "dvb":
        return f".dv {t[1]} (.bool {'true' if t[2] else 'false'})"
    raise Refused("a domain value other than an Int or a Bool")


def call_calls(t, fsyms):
    """The calls of functions in `fsyms` in a term."""
    if t[0] == "app":
        here = [t] if t[1] in fsyms else []
        return here + [c for x in t[2] for c in call_calls(x, fsyms)]
    if t[0] in ("as", "inj"):
        return call_calls(t[1] if t[0] == "as" else t[3], fsyms)
    return []


INT_HOOKS = {19: ("<", "hook_intLt"), 20: ("≤", "hook_intLe"), 21: (">", "hook_intGt"),
             22: ("≥", "hook_intGe"), 23: ("=", "hook_intEq"), 24: ("≠", "hook_intNe")}

# ---------------------------------------------------------------------------------------------
# Mirrors: how a value of a sort is a Lean value. "raw" (a GroundTerm of the sort), "int" (an Int,
# the term `.dv 3 (.int x)`), or a list or option mirror of the spec.


class Mirrors:
    def __init__(self, spec, ctors):
        self.ctors = ctors
        self.m = {}
        for k, v in spec.get("mirror", {}).items():
            s = int(k)
            v = dict(v)
            v["sort"] = s
            if v["kind"] == "list":
                args, res = ctors[v["cons"]]
                if res != s or ctors[v["nil"]] != ([], s):
                    raise Refused(f"mirror {s}: the constructors are not those of the sort")
                comps = [a for i, a in enumerate(args) if i != v["tail"]]
                if args[v["tail"]] != s:
                    raise Refused(f"mirror {s}: the tail is not of the sort")
                raws = [i for i, a in enumerate(comps) if a != 3]
                if len(comps) > 2 or len(raws) != 1:
                    raise Refused(f"mirror {s}: an element of more than two parts, or not one term part")
                v["comps"] = comps
                v["raw"] = raws[0]
            elif v["kind"] == "option":
                args, res = ctors[v["some"]]
                if res != s or ctors[v["none"]] != ([], s) or len(args) != 1 or args[0] == 3:
                    raise Refused(f"mirror {s}: the constructors are not an option's of one term")
                v["comps"] = args
            self.m[s] = v

    def of(self, s, raw=False):
        if raw:
            return "raw"
        if s == 3:
            return "int"
        return s if s in self.m else "raw"

    def ltype(self, mk):
        if mk == "raw":
            return "GroundTerm"
        if mk == "int":
            return "Int"
        v = self.m[mk]
        el = " × ".join("Int" if a == 3 else "GroundTerm" for a in v["comps"])
        if v["kind"] == "list":
            return f"List ({el})" if len(v["comps"]) > 1 else f"List {el}"
        return f"Option {el}"

    def emb(self, mk, e):
        """The term of a Lean value `e` of mirror `mk`."""
        if mk == "raw":
            return e
        if mk == "int":
            return f".dv 3 (.int {e})"
        return f"{self.m[mk]['emb']} {paren(e)}"


def paren(e):
    e = e.strip()
    if re.fullmatch(r"[\w'.₀-₉]+", e) or (e.startswith("(") and e.endswith(")") and balanced(e[1:-1])) \
            or (e.startswith("[") and e.endswith("]") and balanced(e[1:-1])):
        return e
    return f"({e})"


def balanced(s):
    d = 0
    for ch in s:
        if ch in "([⟨":
            d += 1
        elif ch in ")]⟩":
            d -= 1
            if d < 0:
                return False
    return d == 0


# ---------------------------------------------------------------------------------------------
# Values in a branch of the cascade.

class Val:
    """A value in a branch: its Lean expression in F (`f`), its term in the proof (`ge`), its
    mirror and sort, the proof of its sort (`sp`; for a list mirror, `eh` the elements' hypothesis),
    what is known of its constructor (`known`: (f, fields)) and the constructors it is not
    (`negs`: (f, arity, hypothesis))."""

    def __init__(self, f, ge, mk, sort, sp, eh=None, known=None, negs=()):
        self.f, self.ge, self.mk, self.sort, self.sp, self.eh = f, ge, mk, sort, sp, eh
        self.known, self.negs = known, list(negs)

    def copy(self, **kw):
        v = Val(self.f, self.ge, self.mk, self.sort, self.sp, self.eh, self.known, self.negs)
        for k, x in kw.items():
            setattr(v, k, x)
        return v


def core_pat(p):
    return p[1] if p[0] == "as" else p


class Gen:
    def __init__(self, spec, ctors, fns, fn_labels, table=True, hb=False):
        self.spec, self.ctors, self.fns, self.table, self.hb = spec, ctors, fns, table, hb
        self.mir = Mirrors(spec, ctors)
        self.specs = {f["sym"]: f for f in spec["fn"]}
        self.fn_labels = set(fn_labels)

    # the facts, from the table or decided at the use
    def fact(self, kind, f):
        if not self.table:
            return "(by decide +kernel)"
        if kind in ("ctor", "noHook", "sig", "args") and f not in self.ctors:
            raise Refused(f"symbol {f}: not a constructor of the text, no table row")
        if kind in ("notCtorF", "notHook", "notParam") and f not in self.fn_labels:
            raise Refused(f"symbol {f}: not a function of the text, no table row")
        return {"ctor": f"ctor_{f}", "noHook": f"noHook_{f}", "sig": f"sig_{f}", "args": f"args_{f}",
                "notCtorF": f"notCtor_{f}", "notHook": f"notHook_{f}", "notParam": f"notParam_{f}",
                "notCtorH": f"notCtor_{f}", "isHook": f"isHook_{f}"}[kind]

    # names
    def fname(self, sym):
        return self.specs[sym]["name"] + "F"

    def litname(self, sym):
        return self.specs[sym]["name"] + "Def"

    def clname(self, sym, j):
        cl = self.fns[sym]["clauses"][j]
        if cl["label"]:
            parts = re.split(r"[^A-Za-z0-9]+", self.label(cl))
            parts = [p for p in parts if p]
            return parts[0] + "".join(p[:1].upper() + p[1:] for p in parts[1:]) + "Cl"
        return f"{self.specs[sym]['name']}Cl{j}"

    @staticmethod
    def label(cl):
        """The rule's label without its module."""
        return cl["label"].rsplit(".", 1)[-1] if cl["label"] else None

    # ---------------------------------------------------------------- the shape of one function
    def setup(self, sym):
        sp = self.specs[sym]
        fn = self.fns.get(sym)
        if fn is None:
            raise Refused(f"symbol {sym}: not a function with clauses")
        name = sp["name"]
        raw = set(sp.get("raw", []))
        args = fn["args"]
        names = sp["args"]
        if len(names) != len(args):
            raise Refused(f"{name}: {len(args)} arguments, {len(names)} names")
        mks = [self.mir.of(s, i in raw) for i, s in enumerate(args)]
        clauses = [dict(cl, j=j, pats=[tm(p) for p in cl["pats"]], rhs=tm(cl["rhs"]),
                        req=tm(cl["req"]) if cl["req"] else None) for j, cl in enumerate(fn["clauses"])]
        for cl in clauses:
            lbl = self.label(cl) or f"clause {cl['j']}"
            if cl["ens"] is not None or not cl["pre"] or not cl["post"] or cl["exs"] or cl["aside"]:
                raise Refused(f"{name}: {lbl}: an ensures, a premise or right-side predicate, existential variables or aside")
            for p in cl["pats"]:
                self.check_pat(name, lbl, p, top=True)
            if cl["req"] is not None:
                r = cl["req"]
                if r[0] != "app" or r[1] not in INT_HOOKS or any(a[0] != "var" for a in r[2]):
                    raise Refused(f"{name}: {lbl}: a requires that is not an Int comparison of two variables")
        rec = [i for i, mk in enumerate(mks) if mk not in ("raw", "int")
               and any(core_pat(cl["pats"][i])[0] == "app" for cl in clauses)]
        if len(rec) > 1:
            raise Refused(f"{name}: constructor patterns on more than one list argument")
        for i, mk in enumerate(mks):
            if mk not in ("raw", "int") and self.mir.m[mk]["kind"] != "list":
                raise Refused(f"{name}: an argument of an option mirror")
        r = rec[0] if rec else None
        calls = [c for cl in clauses for c in call_calls(cl["rhs"], self.specs.keys())]
        for cl in clauses:
            cs = call_calls(cl["rhs"], self.specs.keys())
            if len(cs) > 1:
                raise Refused(f"{name}: more than one call in a right side")
        self_calls = [c for c in calls if c[1] == sym]
        if self_calls and r is None:
            raise Refused(f"{name}: recursive, but on no list argument")
        return dict(sym=sym, name=name, fn=fn, args=args, names=names, mks=mks, clauses=clauses, rec=r,
                    res=self.fn_res(sym))

    def check_pat(self, name, lbl, p, top):
        k = p[0]
        if k == "var":
            return
        if k == "as":
            if p[1][0] not in ("app",):
                raise Refused(f"{name}: {lbl}: an alias of a variable")
            return self.check_pat(name, lbl, p[1], top)
        if k == "app":
            if not top:
                raise Refused(f"{name}: {lbl}: a pattern below a constructor's arguments")
            if p[1] not in self.ctors:
                raise Refused(f"{name}: {lbl}: a pattern of a symbol that is not one of the text's constructors")
            for x in p[2]:
                if x[0] != "var":
                    raise Refused(f"{name}: {lbl}: a pattern below a constructor's arguments")
            return
        raise Refused(f"{name}: {lbl}: a pattern of kind {k}")

    # ---------------------------------------------------------------- binding a clause
    def bind(self, cl, vals):
        """The clause's variables against the branch's values: `None` where a pattern's constructor
        is not the value's; raises `Unknown` (the position) where the value's constructor is not
        known."""
        b = {}
        for k, (p, v) in enumerate(zip(cl["pats"], vals)):
            if p[0] == "as":
                b[p[2]] = v
                p = p[1]
            if p[0] == "var":
                b[p[1]] = v
                continue
            g = p[1]
            if v.known is not None:
                if v.known[0] != g:
                    return None
                for x, w in zip(p[2], v.known[1]):
                    b[x[1]] = w
                continue
            if any(n[0] == g for n in v.negs):
                return None
            raise Unknown(k)
        return b

    # ---------------------------------------------------------------- the cascade
    def cascade(self, sh, C, vals, guards, hn):
        """The tree of the cascade of clauses C (in priority order) at the branch's values."""
        if not C:
            return ("rest", vals, guards)
        cl = C[0]
        try:
            b = self.bind(cl, vals)
        except Unknown as u:
            k = u.args[0]
            p = core_pat(cl["pats"][k])
            g = p[1]
            v = vals[k]
            if v.mk != "raw":
                raise Refused(f"{sh['name']}: a constructor pattern on an argument that is not a term")
            fargs, _ = self.ctors[g]
            names = self.field_names(sh, cl, p, vals)
            fields = [Val(n, n, "raw", a, f"h{n}") for n, a in zip(names, fargs)]
            fpat = [n if x[1] in vars_of(cl["rhs"]) or (cl["req"] and x[1] in vars_of(cl["req"])) else "_"
                    for n, x in zip(names, p[2])]
            ge = f".ctor {g} [{', '.join(names)}]"
            vpos = vals[:k] + [v.copy(ge=ge, known=(g, fields), f=v.f)] + vals[k + 1:]
            n = hn[0] + 1
            hn[0] = n
            vneg = vals[:k] + [v.copy(negs=v.negs + [(g, len(fargs), f"hn{n}")])] + vals[k + 1:]
            pos = self.cascade(sh, C, vpos, guards, hn)
            neg = self.cascade(sh, C[1:], vneg, guards, hn)
            return ("split", k, g, names, fpat, fields, v, pos, neg, f"hn{n}")
        if b is None:
            return self.cascade(sh, C[1:], vals, guards, hn)
        if cl["req"] is None:
            return ("leaf", cl, b, vals, guards)
        key = self.guard_key(cl, b)
        n = hn[0] + 1
        hn[0] = n
        h = f"h{n}"
        pos = ("leaf", cl, b, vals, guards + [(key, h, True)])
        neg = self.cascade(sh, C[1:], vals, guards + [(key, h, False)], hn)
        return ("guard", key, h, pos, neg)

    def field_names(self, sh, cl, p, vals):
        taken = set(sh["names"]) | {"r", "h", "hr", "ih"}
        for v in vals:
            taken.add(v.f)
        out = []
        for x in p[2]:
            nm = None
            if x[1] < len(cl["names"]):
                raw = cl["names"][x[1]]
                m = re.fullmatch(r"(?:Var)?([A-Z][A-Za-z0-9]*)", raw)
                if m:
                    nm = m[1][0].lower() + m[1][1:]
            if not nm or not re.fullmatch(r"[a-z][A-Za-z0-9]*", nm):
                nm = f"v{x[1]}"
            base, i = nm, 1
            while nm in taken or nm in out:
                i += 1
                nm = f"{base}{i}"
            out.append(nm)
        return out

    def guard_key(self, cl, b):
        r = cl["req"]
        op, _ = INT_HOOKS[r[1]]
        xs = []
        for a in r[2]:
            v = b[a[1]]
            if v.mk != "int":
                raise Refused(f"a requires on a variable that is not an Int argument or part")
            xs.append(v.f)
        return (r[1], xs[0], xs[1])

    def guard_text(self, key):
        op, _ = INT_HOOKS[key[0]]
        return f"{key[1]} {op} {key[2]}"

    # ---------------------------------------------------------------- the right side, in F
    def rhs_f(self, sh, t, b, mk):
        """The right side as a Lean expression of `Option` of mirror mk."""
        calls = call_calls(t, self.specs.keys())
        if not calls:
            return f"some {paren(self.tr(t, b, mk))}"
        c = calls[0]
        cf = self.call_text(c, b)
        if t == c:
            if self.fn_res(c[1]) != mk:
                raise Refused(f"{sh['name']}: a call whose result mirror is not the function's")
            return cf
        if t[0] != "app" or c not in t[2]:
            raise Refused(f"{sh['name']}: a call below a constructor's argument")
        body = self.tr(t, b, mk, hole=(c, "r", self.fn_res(c[1])))
        return f"{paren(cf)}.bind fun r => some {paren(body)}"

    def fn_res(self, sym):
        """A function's result as a term, or as a value of its sort's list or option mirror."""
        return self.mir.of(self.fns[sym]["result"], self.fns[sym]["result"] == 3)

    def fn_mks(self, sym):
        sp = self.specs[sym]
        raw = set(sp.get("raw", []))
        return [self.mir.of(s, i in raw) for i, s in enumerate(self.fns[sym]["args"])]

    def call_text(self, c, b):
        mks = self.fn_mks(c[1])
        return f"{self.fname(c[1])} " + " ".join(paren(self.tr(a, b, m)) for a, m in zip(c[2], mks))

    def tr(self, t, b, mk, hole=None):
        """A call-free term (or one with the hole `hole` for its call) as a Lean value of mirror mk."""
        if hole is not None and t == hole[0]:
            hm = hole[2]
            return hole[1] if hm == mk else self.need(hm, mk, hole[1], self.mir.emb(hm, hole[1]))
        k = t[0]
        if k == "var":
            v = b[t[1]]
            if v.mk == mk:
                return v.f
            return self.need(v.mk, mk, v.f, self.mir.emb(v.mk, v.f))
        if k == "dvi":
            if mk == "int":
                return str(t[2]) if t[2] >= 0 else f"({t[2]})"
            if mk == "raw":
                return lit(t)
        if k == "dvb" and mk == "raw":
            return lit(t)
        if k == "app" and t[1] in self.ctors:
            g = t[1]
            fargs, res = self.ctors[g]
            if mk not in ("raw", "int"):
                m = self.mir.m[mk]
                if m["kind"] == "list":
                    if g == m["nil"]:
                        return "[]"
                    if g == m["cons"]:
                        comps = [a for i, a in enumerate(t[2]) if i != m["tail"]]
                        cm = ["int" if s == 3 else "raw" for s in m["comps"]]
                        hd = [self.tr(a, b, x, hole) for a, x in zip(comps, cm)]
                        tl = self.tr(t[2][m["tail"]], b, mk, hole)
                        h = hd[0] if len(hd) == 1 else f"({', '.join(hd)})"
                        return f"{paren(h) if len(hd) == 1 else h} :: {tl}"
                else:
                    if g == m["none"]:
                        return "none"
                    if g == m["some"]:
                        return f"some {paren(self.tr(t[2][0], b, 'raw', hole))}"
                raise Refused(f"a constructor {g} at a value of mirror {mk}")
            if mk == "raw":
                parts = []
                for a, s in zip(t[2], fargs):
                    am = self.mir.of(s)
                    if a[0] == "var" and b[a[1]].mk == "raw":
                        am = "raw"
                    e = self.tr(a, b, am, hole)
                    parts.append(self.mir.emb(am, e) if am != "raw" else e)
                return f".ctor {g} [{', '.join(parts)}]"
        if k == "app" and t[1] in self.specs:
            raise Refused("a call below a constructor's argument")
        if k == "app" and t[1] in self.fns:
            raise Refused(f"a call of symbol {t[1]}, a function SPEC does not name")
        raise Refused(f"a right side of kind {k} at mirror {mk}")

    def need(self, have, want, f, femb):
        if want == "raw":
            return femb
        raise Refused(f"a value of mirror {have} where mirror {want} is needed")

    # ---------------------------------------------------------------- F
    def f_text(self, sh, tree):
        name, mks, r = sh["name"], sh["mks"], sh["rec"]
        out = []
        doc = f"/-- kore.k's `{name}` as a cascade. -/"
        restype = f"Option {paren(self.mir.ltype(sh['res']))}"
        if r is None:
            bs = binders(sh["names"], [self.mir.ltype(m) for m in mks])
            out.append(doc)
            out.append(f"def {self.fname(sh['sym'])} {bs} : {restype} :=")
            out += ["  " + l for l in self.render(tree)]
        else:
            ty = " → ".join(self.mir.ltype(m) for m in mks)
            out.append(doc)
            out.append(f"def {self.fname(sh['sym'])} : {ty} → {restype}")
            for case, sub in tree:
                lines = self.render(sub)
                used = lambda n: any(re.search(rf"(?<![\w.']){re.escape(n)}(?![\w'])", l) for l in lines)
                pats = [n if used(n) else "_" for n in sh["names"]]
                pats[r] = case["fpat"]
                head = f"  | {', '.join(pats)} =>"
                if len(lines) == 1:
                    out.append(f"{head} {lines[0]}")
                else:
                    out.append(head)
                    out += ["    " + l for l in lines]
        return out

    def render(self, node):
        k = node[0]
        if k == "rest":
            return ["none"]
        if k == "leaf":
            _, cl, b, vals, _ = node
            return [self.rhs_f(self.cur, cl["rhs"], b, self.cur["res"])]
        if k == "guard":
            _, key, h, pos, neg = node
            p, n = self.render(pos), self.render(neg)
            if len(p) == 1 and len(n) == 1:
                return [f"if {self.guard_text(key)} then {p[0]} else {n[0]}"]
            out = [f"if {self.guard_text(key)} then"] + ["  " + l for l in p] + ["else"] + ["  " + l for l in n]
            return out
        if k == "split":
            _, kk, g, names, fpat, fields, v, pos, neg, hn = node
            p, n = self.render(pos), self.render(neg)
            out = [f"match {v.f} with"]
            alt = f"| .ctor {g} [{', '.join(fpat)}] =>"
            out += [f"{alt} {p[0]}"] if len(p) == 1 else [alt] + ["  " + l for l in p]
            out += [f"| _ => {n[0]}"] if len(n) == 1 else ["| _ =>"] + ["  " + l for l in n]
            return out
        raise AssertionError(k)

    # ---------------------------------------------------------------- the proof
    def eval_text(self, sh, tree):
        sym, name, mks, r = sh["sym"], sh["name"], sh["mks"], sh["rec"]
        F = self.fname(sym)
        hyps = []
        for n, m, s in zip(sh["names"], mks, sh["args"]):
            h = self.top_hyp(n, m, s)
            if h:
                hyps.append(h)
        bs = binders(sh["names"], [self.mir.ltype(m) for m in mks])
        hs = " ".join(f"({h} : {t})" for h, t in hyps)
        vs = "[" + ", ".join(self.mir.emb(m, n) for n, m in zip(sh["names"], mks)) + "]"
        call = f"{F} {' '.join(sh['names'])}"
        res = f"({call})" if sh["res"] == "raw" else f"(({call}).map {self.mir.m[sh['res']]['emb']})"
        out = []
        if self.hb:
            out.append("spike_hb in")
        sig = f"theorem {F}.eval {bs}{(' ' + hs) if hs else ''} :"
        out.append(sig)
        out.append(f"    Eval c₀ {sym} {vs} {res} := by")
        body = []
        if r is None:
            body += self.proof(sh, tree, unfolded=False, top=True)
        else:
            m = self.mir.m[mks[r]]
            body.append(f"induction {sh['names'][r]} with")
            for case, sub in tree:
                body.append(f"| {case['ind']} =>")
                inner = list(case["pre"])
                inner += self.proof(sh, sub, unfolded=False, top=True, ih=case.get("ih"))
                body += ["  " + l for l in inner]
        out += ["  " + l for l in body]
        iff_hs = " ".join(f"({h} : {t})" for h, t in hyps)
        hn = " ".join(h for h, _ in hyps)
        rr = res[1:-1] if res.startswith("(") else res
        out.append("")
        out.append(f"theorem {F}.eval_iff {bs}{(' ' + iff_hs) if iff_hs else ''} {{r : Option GroundTerm}} :")
        out.append(f"    Eval c₀ {sym} {vs} r ↔ r = {rr} :=")
        args = " ".join(sh["names"]) + (" " + hn if hn else "")
        out.append(f"  ⟨fun h => Eval.functional coherent h ({F}.eval {args}), fun e => e ▸ {F}.eval {args}⟩")
        return out

    def top_hyp(self, n, m, s):
        if m == "int":
            return None
        if m == "raw":
            return (f"h{n}", f"c₀.sortOf {n} = some {s}")
        mm = self.mir.m[m]
        es = mm["comps"][mm["raw"]]
        if len(mm["comps"]) == 1:
            return (f"h{n}", f"∀ u ∈ {n}, c₀.sortOf u = some {es}")
        return (f"h{n}", f"∀ p ∈ {n}, c₀.sortOf p.{mm['raw'] + 1} = some {es}")

    def top_vals(self, sh):
        vals = []
        for n, m, s in zip(sh["names"], sh["mks"], sh["args"]):
            if m == "int":
                vals.append(Val(n, f".dv 3 (.int {n})", "int", 3, f"sort_int {n}"))
            elif m == "raw":
                vals.append(Val(n, n, "raw", s, f"h{n}"))
            else:
                mm = self.mir.m[m]
                vals.append(Val(n, f"{mm['emb']} {n}", m, s, f"{mm['sorted']} h{n}", eh=f"h{n}"))
        return vals

    def rec_cases(self, sh):
        """Per constructor of the list argument F recurses on: its case of F and of the induction."""
        r = sh["rec"]
        n = sh["names"][r]
        mk = sh["mks"][r]
        mm = self.mir.m[mk]
        order = []
        for cl in sorted(sh["clauses"], key=lambda c: c["prio"]):
            p = core_pat(cl["pats"][r])
            if p[0] == "app" and p[1] not in order:
                order.append(p[1])
        for g in (mm["nil"], mm["cons"]):
            if g not in order:
                order.append(g)
        cases = []
        base = self.top_vals(sh)
        for g in order:
            if g == mm["nil"]:
                v = base[r].copy(f="[]", ge=f"{mm['emb']} []", known=(g, []))
                cases.append(dict(g=g, fpat="[]", ind="nil", pre=[], vals=base[:r] + [v] + base[r + 1:], ih=None))
                continue
            fields_s = self.ctors[g][0]
            fnames = mm["names"]
            taken = set(sh["names"])
            tl = fnames[mm["tail"]]
            comps_n = [x for i, x in enumerate(fnames) if i != mm["tail"]]
            fvals = []
            hd = comps_n[0] if len(comps_n) == 1 else f"({', '.join(comps_n)})"
            eh = f"h{tl}" if f"h{tl}" != f"h{n}" else f"h{tl}'"
            for i, s in enumerate(fields_s):
                fn_ = fnames[i]
                if i == mm["tail"]:
                    fvals.append(Val(fn_, f"{mm['emb']} {fn_}", mk, s, f"{mm['sorted']} {eh}", eh=eh))
                elif s == 3:
                    fvals.append(Val(fn_, f".dv 3 (.int {fn_})", "int", 3, f"sort_int {fn_}"))
                else:
                    fvals.append(Val(fn_, fn_, "raw", s, f"h{n} {hd} (List.mem_cons_self ..)"))
            whole = f"{hd} :: {tl}"
            v = base[r].copy(f=f"({whole})", ge=f"{mm['emb']} ({whole})", known=(g, fvals))
            es = mm["comps"][mm["raw"]]
            if len(comps_n) == 1:
                pre = [f"have {eh} : ∀ u ∈ {tl}, c₀.sortOf u = some {es} := fun u hu => h{n} u (List.mem_cons_of_mem _ hu)"]
                ind = f"cons {hd} {tl} ih"
            else:
                pre = [f"obtain ⟨{', '.join(comps_n)}⟩ := e₀",
                       f"have {eh} : ∀ p ∈ {tl}, c₀.sortOf p.{mm['raw'] + 1} = some {es} := fun p hp => h{n} p (List.mem_cons_of_mem _ hp)"]
                ind = f"cons e₀ {tl} ih"
            cases.append(dict(g=g, fpat=whole, ind=ind, pre=pre, vals=base[:r] + [v] + base[r + 1:], ih=eh, tail=tl))
        return cases

    def build(self, sh):
        C = sorted(sh["clauses"], key=lambda c: c["prio"])
        hn = [0]
        if sh["rec"] is None:
            return self.cascade(sh, C, self.top_vals(sh), [], hn)
        out = []
        for case in self.rec_cases(sh):
            hn = [0]
            sub = self.cascade(sh, C, case["vals"], [], hn)
            uses_ih = tree_calls(sub, sh["sym"])
            if uses_ih:
                case["pre"] = case["pre"] + [f"have ih := ih {case['ih']}"]
            out.append((case, sub))
        return out

    def proof(self, sh, node, unfolded, top=False, ih=None):
        k = node[0]
        F = self.fname(sh["sym"])
        unfold = []
        if k in ("guard", "split") and not unfolded:
            unfold = [f"rw [{F}]" if sh["rec"] is not None else f"unfold {F}"]
            unfolded = True
        if k == "rest":
            return self.rest_text(sh, node)
        if k == "leaf":
            return self.leaf_text(sh, node, unfolded)
        if k == "guard":
            _, key, h, pos, neg = node
            g = self.guard_text(key)
            out = unfold + [f"by_cases {h} : {g}"]
            out += ["· " + l if i == 0 else "  " + l
                    for i, l in enumerate([f"rw [ite_pos {h}]"] + self.proof(sh, pos, unfolded))]
            out += ["· " + l if i == 0 else "  " + l
                    for i, l in enumerate([f"rw [ite_neg {h}]"] + self.proof(sh, neg, unfolded))]
            return out
        if k == "split":
            _, kk, g, names, fpat, fields, v, pos, neg, hn = node
            out = unfold + ["split"]
            pre = []
            if fields:
                fa = self.fact("args", g)
                if not self.table:
                    fa = f"(as := [{', '.join(str(w.sort) for w in fields)}]) {fa}"
                src = f"(sort_args {v.sp} {fa})"
                for i, w in enumerate(fields):
                    last = i == len(fields) - 1
                    pre.append(f"obtain ⟨h{w.f}, {'-' if last else 'hr'}⟩ := sorts_cons_inv {src}")
                    src = "hr"
            pp = pre + self.proof(sh, pos, unfolded)
            head = f"· next {' '.join(names)} =>" if names else None
            if head:
                out.append(head)
                out += ["    " + l for l in pp]
            else:
                out += ["· " + l if i == 0 else "  " + l for i, l in enumerate(pp)]
            nn = self.proof(sh, neg, unfolded)
            out.append(f"· next {hn} =>")
            out += ["    " + l for l in nn]
            return out
        raise AssertionError(k)

    def leaf_text(self, sh, node, unfolded):
        _, cl, b, vals, guards = node
        sym, F = sh["sym"], self.fname(sh["sym"])
        n = len(cl["vars"])
        for i in range(n):
            if i not in b:
                raise Refused(f"{sh['name']}: a variable no pattern binds")
        sigma = f"enumFrom 0 [{', '.join(b[i].ge for i in range(n))}]"
        sorts = ".nil"
        for i in reversed(range(n)):
            sorts = f".cons {paren(b[i].sp)} {paren(sorts)}"
        pv = ".nil"
        for p, v in reversed(list(zip(cl["pats"], vals))):
            pv = f".cons {paren(self.patval(p))} {paren(pv)}"
        lbl = self.label(cl) or f"clause {cl['j']}"
        goals = []
        req = "(fun _ h => by cases h)"
        if cl["req"] is not None:
            req = "?_"
            key = self.guard_key(cl, b)
            h = [g[1] for g in guards if g[0] == key and g[2]]
            if not h:
                raise Refused(f"{sh['name']}: {lbl}: the requires has no hypothesis in its branch")
            op, hook = INT_HOOKS[key[0]]
            a, c = cl["req"][2]
            goals.append(["intro tq htq", "cases htq",
                          f"have hq := ev_int2 (σ := {sigma}) (P := (· {op} ·)) {hook} (ev_var (i := {a[1]}) rfl) "
                          f"(ev_var (i := {c[1]}) rfl) {self.fact('notCtorH', key[0])} {self.fact('isHook', key[0])}",
                          f"rwa [decide_eq_true {h[0]}] at hq"])
        goals.append(self.prio_text(sh, cl, vals, guards))
        rhs, rhs_goal = self.rhs_proof(sh, cl, b, sigma, unfolded)
        if rhs_goal is not None:
            goals.append(rhs_goal)
        mem = "List.mem_cons_self .."
        for _ in range(cl["j"]):
            mem = f"List.mem_cons_of_mem _ ({mem})"
        out = [f"-- {lbl}",
               f"refine Eval.clause (cl := {self.clname(sym, cl['j'])}) (σ := {sigma}) {self.litname(sym)}_lookup ({mem})",
               f"  (ws_enum ({sorts}))",
               f"  ({pv})",
               f"  {req} Holds.top ?_ rfl {rhs} (fun _ h => by cases h) Holds.top"]
        if len(goals) == 1:
            out += goals[0]
        else:
            for g in goals:
                out += ["· " + l if i == 0 else "  " + l for i, l in enumerate(g)]
        return out

    def patval(self, p):
        if p[0] == "var":
            return ".var rfl"
        if p[0] == "as":
            return f".as {paren(self.patval(p[1]))} rfl"
        if p[0] == "app":
            inner = ".nil"
            for x in reversed(p[2]):
                inner = f".cons {paren(self.patval(x))} {paren(inner)}"
            return f".ctor {self.fact('ctor', p[1])} {paren(inner)}"
        raise Refused("a pattern of a domain value")

    def clause_list(self, sh):
        n = len(sh["fn"]["clauses"])
        return " | ".join(["rfl"] * n)

    def prio_text(self, sh, cl, vals, guards):
        lit_ = self.litname(sh["sym"])
        out = ["intro cl' hm _ hp",
               f"simp only [{lit_}, List.mem_cons, List.not_mem_nil, or_false] at hm",
               f"rcases hm with {self.clause_list(sh)}"]
        for c2 in sh["clauses"]:
            if c2["prio"] >= cl["prio"]:
                out.append("· exact absurd hp (by decide)")
            else:
                f = self.fails(sh, c2, vals, guards)
                out += ["· " + l if i == 0 else "  " + l for i, l in enumerate(f)]
        return out

    def rest_text(self, sh, node):
        _, vals, guards = node
        lit_ = self.litname(sh["sym"])
        out = ["-- no equation applies",
               f"refine Eval.rest (fn := {lit_}) {lit_}_lookup ?_",
               "intro cl hm",
               f"simp only [{lit_}, List.mem_cons, List.not_mem_nil, or_false] at hm",
               f"rcases hm with {self.clause_list(sh)}"]
        for c2 in sh["clauses"]:
            f = self.fails(sh, c2, vals, guards)
            out += ["· " + l if i == 0 else "  " + l for i, l in enumerate(f)]
        return out

    def fails(self, sh, c2, vals, guards):
        """`Fails` of clause c2 at the branch's values."""
        lbl = self.label(c2) or f"clause {c2['j']}"
        n = len(vals)
        # a pattern's constructor against the argument's, or against a negative hypothesis
        for k, (p, v) in enumerate(zip(c2["pats"], vals)):
            via_as = p[0] == "as"
            q = core_pat(p)
            if q[0] != "app":
                continue
            g = q[1]
            src = f"(PatVal.as_inv hv{k}).1" if via_as else f"hv{k}"
            pvc = f"pv_ctor {src} {self.fact('ctor', g)} {self.fact('noHook', g)}"
            if v.known is not None and v.known[0] != g:
                return ["refine .intro fun σ _ hm => ?_",
                        f"rcases hm with {rc_names({k: f'hv{k}'}, n)}",
                        f"obtain ⟨xs, he, -⟩ := {pvc}",
                        "exact absurd (GroundTerm.ctor.inj he).1 (by decide)"]
            if v.known is None:
                ng = [x for x in v.negs if x[0] == g]
                if ng:
                    _, ar, hn = ng[0]
                    return ["refine .intro fun σ _ hm => ?_",
                            f"rcases hm with {rc_names({k: f'hv{k}'}, n)}",
                            f"obtain ⟨xs, he, hxs⟩ := {pvc}",
                            f"rcases hxs with {rc_full({}, ar)}",
                            f"exact ({hn}{' _' * ar} he).elim"]
        # the requires with the value false
        if c2["req"] is None:
            raise Refused(f"{sh['name']}: {lbl}: matches in a branch of an equation of a larger priority")
        try:
            b = self.bind(c2, vals)
        except Unknown:
            b = None
        if b is None:
            raise Refused(f"{sh['name']}: {lbl}: no refutation in a branch")
        key = self.guard_key(c2, b)
        hs = [g[1] for g in guards if g[0] == key and not g[2]]
        if not hs:
            raise Refused(f"{sh['name']}: {lbl}: its requires is not refuted in a branch where it matches")
        op, hook = INT_HOOKS[key[0]]
        # where each variable of the requires is bound: a position, or a field of a known constructor
        loc = {}
        for k, p in enumerate(c2["pats"]):
            if p[0] == "as":
                loc[p[2]] = ("as", k)
                p = p[1]
            if p[0] == "var":
                loc[p[1]] = ("top", k)
            elif p[0] == "app":
                for m, x in enumerate(p[2]):
                    loc[x[1]] = ("in", k, m)
        need = [a[1] for a in c2["req"][2]]
        tops, ins = {}, {}
        for x in need:
            l = loc[x]
            tops[l[1]] = f"hv{l[1]}"
            if l[0] == "in":
                ins.setdefault(l[1], {})[l[2]] = f"hx{l[1]}_{l[2]}"
        out = ["refine .intro fun σ _ hm => ?_", f"rcases hm with {rc_names(tops, n)}"]
        for k, ms in sorted(ins.items()):
            p = c2["pats"][k]
            via_as = p[0] == "as"
            q = core_pat(p)
            src = f"(PatVal.as_inv hv{k}).1" if via_as else f"hv{k}"
            out.append(f"obtain ⟨xs{k}, he{k}, hxs{k}⟩ := pv_ctor {src} {self.fact('ctor', q[1])} {self.fact('noHook', q[1])}")
            out.append(f"cases he{k}")
            out.append(f"rcases hxs{k} with {rc_full(ms, len(q[2]))}")

        def ev(x):
            l = loc[x]
            if l[0] == "top":
                return f"(ev_var (PatVal.var_inv hv{l[1]}))"
            if l[0] == "as":
                return f"(ev_var (PatVal.as_inv hv{l[1]}).2)"
            return f"(ev_var (PatVal.var_inv hx{l[1]}_{l[2]}))"
        a, c = need
        out.append(f"refine .intro rfl (ev_int2 (P := (· {op} ·)) {hook} {ev(a)} {ev(c)} "
                   f"{self.fact('notCtorH', key[0])} {self.fact('isHook', key[0])}) ?_")
        out.append(f"rw [decide_eq_false {hs[0]}]")
        out.append("exact fun e => absurd (bool_inj (Option.some.inj e)) (by decide)")
        return out

    def rhs_proof(self, sh, cl, b, sigma, unfolded):
        """The right side's evaluation: a term, or `?_` and the goal's text."""
        t = cl["rhs"]
        calls = call_calls(t, self.specs.keys())
        if not calls:
            return paren(self.ev(t, b)[0]), None
        c = calls[0]
        cp = self.call_proof(sh, c, b)
        g = c[1]
        evc = f"ev_call {paren(self.evargs(c[2], b))} {cp} {self.fact('notCtorF', g)} {self.fact('notHook', g)} {self.fact('notParam', g)}"
        if t == c:
            return f"({evc})", None
        # a call as an argument of the right side's constructor: the two cases of its value
        f = t[1]
        cf = self.call_text(c, b)
        lines = [] if unfolded else [f"simp only [{self.fname(sh['sym'])}]"]
        hname = "ih" if c[1] == sh["sym"] else "hc"
        if hname == "hc":
            lines.append(f"have hc := {cp}")
        evc_h = evc.replace(f" {cp} ", f" {hname} ", 1)
        lines.append(f"cases hr : {cf} with")
        rs, parts = [], []
        for a in t[2]:
            if a == c:
                rs.append("none")
                parts.append(evc_h)
            else:
                pf, ge = self.ev(a, b)
                rs.append(f"some {paren(ge)}")
                parts.append(pf)
        terms = ".nil"
        for p in reversed(parts):
            terms = f".cons {paren(p)} {paren(terms)}"
        lines += ["| none =>",
                  f"  rw [hr] at {hname}",
                  f"  exact EvalTerm.ctor (σ := {sigma}) (rs := [{', '.join(rs)}]) {self.fact('ctor', f)}",
                  f"    {paren(terms)}"]
        parts2 = []
        for a in t[2]:
            parts2.append(evc_h if a == c else self.ev(a, b)[0])
        ea = ".nil"
        for p in reversed(parts2):
            ea = f".cons {paren(p)} {paren(ea)}"
        lines += ["| some r =>",
                  f"  rw [hr] at {hname}",
                  f"  exact ev_ctor {paren(ea)} {self.fact('ctor', f)}"]
        return "?_", lines

    def call_proof(self, sh, c, b):
        g = c[1]
        if g == sh["sym"]:
            r = sh["rec"]
            for i, a in enumerate(c[2]):
                if a[0] != "var":
                    raise Refused(f"{sh['name']}: a recursive call at an argument that is not a variable")
            # the recursive call: at the tail, the other arguments unchanged
            args = [b[a[1]] for a in c[2]]
            top = self.top_vals(sh)
            for i, v in enumerate(args):
                if i == r:
                    if v.eh is None or v.known is not None:
                        raise Refused(f"{sh['name']}: a recursive call not at the list's tail")
                elif v.f != top[i].f:
                    raise Refused(f"{sh['name']}: a recursive call with another argument changed")
            return "ih"
        hs = []
        for a, m in zip(c[2], self.fn_mks(g)):
            if a[0] != "var":
                raise Refused(f"{sh['name']}: a call at an argument that is not a variable")
            v = b[a[1]]
            if v.mk != m:
                raise Refused(f"{sh['name']}: a call at a value of another mirror")
            if m == "raw":
                hs.append(v.sp)
            elif m != "int":
                hs.append(v.eh)
        args = " ".join(paren(b[a[1]].f) for a in c[2])
        return f"({self.fname(g)}.eval {args}{' ' + ' '.join(paren(h) for h in hs) if hs else ''})"

    def ev(self, t, b):
        """A call-free term's evaluation: its proof and its value's term."""
        k = t[0]
        if k == "var":
            return "ev_var rfl", b[t[1]].ge
        if k in ("dvi", "dvb"):
            return "EvalTerm.dv", lit(t)
        if k == "app" and t[1] in self.ctors:
            ps, gs = [], []
            for a in t[2]:
                p, g = self.ev(a, b)
                ps.append(p)
                gs.append(g)
            ea = ".nil"
            for p in reversed(ps):
                ea = f".cons {paren(p)} {paren(ea)}"
            return f"ev_ctor {paren(ea)} {self.fact('ctor', t[1])}", f".ctor {t[1]} [{', '.join(gs)}]"
        raise Refused(f"a right side of kind {k}")

    def evargs(self, ts, b):
        ea = ".nil"
        for a in reversed(ts):
            ea = f".cons {paren(self.ev(a, b)[0])} {paren(ea)}"
        return ea

    # ---------------------------------------------------------------- literals
    def literals(self, sh):
        sym, fn = sh["sym"], sh["fn"]
        out = []
        names = []
        for j, cl in enumerate(fn["clauses"]):
            nm = self.clname(sym, j)
            names.append(nm)
            lbl = self.label(cl)
            out.append(f"/-- The clause of `{sh['name']}`" + (f" from kore.k's rule `{lbl}`. -/" if lbl else f" number {j}. -/"))
            req = "none" if cl["req"] is None else f"some ({lit(tm(cl['req']))})"
            out += [f"def {nm} : Clause :=",
                    f"  {{ vars := {cl['vars']},",
                    f"    pats := [{', '.join(lit(tm(p)) for p in cl['pats'])}],",
                    f"    req := {req},",
                    f"    rhs := {lit(tm(cl['rhs']))},",
                    "    ens := none,",
                    f"    prio := {cl['prio']},",
                    "    aside := false,",
                    "    exs := [],",
                    "    pre := .top,",
                    "    post := .top }", ""]
        L = self.litname(sym)
        out += [f"/-- `{sh['name']}` (symbol {sym}) as the definition's semantics holds it. -/",
                f"def {L} : Fn :=",
                f"  {{ label := {sym}, args := {fn['args']}, result := {fn['result']},",
                f"    clauses := [{', '.join(names)}], total := {'true' if fn['total'] else 'false'} }}", "",
                f"theorem {L}_lookup : c₀.lookupFn {sym} = some {L} := by kernel_rfl", ""]
        return out

    def function(self, sym):
        sh = self.setup(sym)
        self.cur = sh
        tree = self.build(sh)
        out = [f"/-! ## `{sh['name']}` -/", ""]
        out += self.literals(sh)
        out += self.f_text(sh, tree)
        out.append("")
        out += self.eval_text(sh, tree)
        out.append("")
        return out


class Unknown(Exception):
    pass


def vars_of(t):
    if t is None:
        return set()
    k = t[0]
    if k == "var":
        return {t[1]}
    if k == "app":
        return set().union(*[vars_of(x) for x in t[2]]) if t[2] else set()
    if k == "as":
        return vars_of(t[1]) | {t[2]}
    if k == "inj":
        return vars_of(t[3])
    return set()


def tree_calls(node, sym):
    k = node[0]
    if k == "leaf":
        return any(c[1] == sym for c in call_calls(node[1]["rhs"], {sym}))
    if k == "guard":
        return tree_calls(node[3], sym) or tree_calls(node[4], sym)
    if k == "split":
        return tree_calls(node[7], sym) or tree_calls(node[8], sym)
    return False


def binders(names, types):
    out, i = [], 0
    while i < len(names):
        j = i
        while j + 1 < len(names) and types[j + 1] == types[i]:
            j += 1
        out.append(f"({' '.join(names[i:j + 1])} : {types[i]})")
        i = j + 1
    return " ".join(out)


def rc_names(named, n):
    """An `rcases` pattern of `PatVals` at n values naming the positions of `named`, `_` after the
    last named one."""
    last = max(named) if named else -1

    def go(i):
        if i > last:
            return "_"
        return f"_ | ⟨{named.get(i, '_')}, {go(i + 1)}⟩"
    return go(0)


def rc_full(named, n):
    """An `rcases` pattern of `PatVals` at exactly n values, naming the positions of `named`."""
    def go(i):
        if i == n:
            return "_ | _"
        return f"_ | ⟨{named.get(i, '_')}, {go(i + 1)}⟩"
    return go(0)


# ---------------------------------------------------------------------------------------------

def facts_text(spec, ctors, fn_labels):
    hooks = sorted(INT_HOOKS)
    out = ["/-", "  Generated by kcore-spec/gen/kkcascade.py from the KORE text; not edited by hand. The facts about",
           "  single symbols of kore.k's semantics at `c₀` that the cascade text reads, each decided once: for",
           "  every constructor, that it is one, that it is not a pattern hook, its signature and its argument",
           "  sorts; for every function, that it is not a constructor, a hook or a parameter; for the Int",
           "  comparisons, that they are hooks and not constructors.", "-/",
           "import User.Coherent", "", "set_option autoImplicit false", "set_option maxRecDepth 1000000", "",
           "namespace KK.Facts", "", "open KCore RefKk KK", ""]
    for f in sorted(ctors):
        args, res = ctors[f]
        out += [f"theorem ctor_{f} : c₀.isCtor {f} = true := by decide +kernel",
                f"theorem noHook_{f} : patternHooks.contains {f} = false := by decide +kernel",
                f"theorem sig_{f} : (lookupSig c₀.ctorSigs {f}).map (fun k => (k.args, k.result)) = some ({args}, {res}) := by decide +kernel",
                f"theorem args_{f} : (lookupSig c₀.ctorSigs {f}).map (·.args) = some {args} := by decide +kernel"]
    out.append("")
    for g in sorted(set(fn_labels)):
        out += [f"theorem notCtor_{g} : c₀.isCtor {g} = false := by decide +kernel",
                f"theorem notHook_{g} : isHook {g} = false := by decide +kernel",
                f"theorem notParam_{g} : c₀.isParam {g} = false := by decide +kernel"]
    out.append("")
    for h in hooks:
        out += [f"theorem notCtor_{h} : c₀.isCtor {h} = false := by decide +kernel",
                f"theorem isHook_{h} : isHook {h} = true := by decide +kernel"]
    out += ["", "end KK.Facts", ""]
    return "\n".join(out)


def emit_text(spec, ctors, fns, fn_labels, table, hb, spec_path):
    g = Gen(spec, ctors, fns, fn_labels, table=table, hb=hb)
    names = ", ".join(f"`{f['name']}`" for f in spec["fn"])
    out = ["/-", "  Generated by kcore-spec/gen/kkcascade.py from the KORE text and "
           f"{os.path.relpath(spec_path, KS)}; not edited", f"  by hand. `F.eval` and `F.eval_iff` for kore.k's {names}"
           " over sorted values: the clauses as literals,",
           "  the Lean function `F` as the cascade of the equations, and the proof along F's branches.", "-/",
           "import User.KkKit"]
    if table:
        out.append("import User.KkFacts")
    out += ["", "set_option autoImplicit false", "set_option maxRecDepth 1000000", "set_option Elab.async false", "",
            f"namespace {spec['namespace']}", "",
            "open KCore KCore.Det RefKk KK KK.Kit" + (" KK.Facts" if table else ""), ""]
    for f in spec["fn"]:
        out += g.function(f["sym"])
    out += [f"end {spec['namespace']}", ""]
    return "\n".join(out)


def main(argv):
    if len(argv) < 2 or argv[0] not in ("facts", "emit", "check"):
        print(__doc__)
        return 2
    cmd, spec_path = argv[0], os.path.abspath(argv[1])
    rest = argv[2:]
    spec = tomllib.load(open(spec_path, "rb"))
    base = os.path.dirname(spec_path)
    pkg = os.path.join(KS, spec["package"])
    kore = os.path.join(pkg, spec["kore"])
    try:
        ctors, fns, labels = probe(kore)
        if cmd == "facts":
            text = facts_text(spec, ctors, labels)
            out = os.path.join(pkg, spec["facts"])
        else:
            table = "--no-table" not in rest
            hb = "--hb" in rest or spec.get("hb", False)
            text = emit_text(spec, ctors, fns, labels, table, hb, spec_path)
            out = os.path.join(pkg, spec["module"])
            if "--out" in rest:
                out = os.path.abspath(rest[rest.index("--out") + 1])
    except Refused as e:
        print(f"kkcascade: refused: {e}", file=sys.stderr)
        return 1
    if cmd == "check":
        if "--no-table" in rest:
            print("kkcascade: check compares the table text", file=sys.stderr)
            return 2
        mods = [(os.path.join(pkg, spec["module"]), text),
                (os.path.join(pkg, spec["facts"]), facts_text(spec, ctors, labels))]
        bad = [p for p, t in mods if not os.path.exists(p) or open(p).read() != t]
        for p in bad:
            print(f"kkcascade: {os.path.relpath(p, KS)} is not what the script writes", file=sys.stderr)
        return 1 if bad else 0
    if "--print" in rest:
        sys.stdout.write(text)
        return 0
    open(out, "w").write(text)
    print(f"wrote {os.path.relpath(out, KS) if out.startswith(KS) else out}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
