#!/usr/bin/env python3
"""tiegen.py: the tie (C14) of a construct fixture's kompiled text, written as a Lean test.

Usage (from anywhere; the library and `kcore` built first):
  python3 -I test/constructs/tiegen.py FIXTURE [--sig-chunk N] [--decl-chunk N] [--print]
  (the probe, a run of the Lean definitions on the text, is stopped after $TIEGEN_PROBE_TIMEOUT seconds, 900 by default)

For FIXTURE (a directory of test/constructs/fixtures with a kompiled text), it writes
  f2-examples/FIXTURE.kompile.kore   the kompiled text kompile.txt records (from the cache kfix.py
                                     keeps), K's builtin directory restored for BUILTIN/ and the
                                     fixture's directory, relative to kcore-spec's parent, for FIXTURE/;
  test/Tie<Fixture>.lean             the tie on that text, on the literals `kore` and `defn`, for
                                     every interpretation H.

It refuses, with the reason, a fixture without a kompiled text, a text whose `kcore account` is not
the fixture's account.txt, a text the reader refuses, a text with an open generator parameter, a
text whose definition reads a confined sort (`readsConfined`), and a text with an owed fact (`kcore
gen --core` names one, or states its obligations otherwise than `FnObligations defn.sem callOrder []`).

What the test states (each a kernel decision or a proof from one):
- layer 1: `wf defn = true` (or `coreOK` with the failing conjuncts of `wf` named); the account (the
  class lists, in `tieClasses`' order, partition the user module's sentences); `account_absent` and
  `absent_closed`; `attrs_agree`; `sig_origin` and `decls_entailed` (by ranges of the lists);
- the acceptance conditions themselves: `noRaw`, `readsConfined_c`, the four obligation lists empty,
  `consistent` for every H;
- by class, the theorems of test/TieEns.lean over the sentences they hold of: the function
  equations (`fn_shape`, `fns_entailed`, `fns_from_text`, `fn_prios`), the constructor sentences
  (`cons_entailed`), the no-junk sentences (`nojunk_trivial_entailed`, `nojunk_items`,
  `nojunk_kitem_entailed`), set idempotence (`idem_refuted`) and the library sample `I -Int 0 = I`
  (`lib166`, `lib166_at_values`) where the text holds that sentence, and `gamma_origin` where
  every premise of Γ has its origin here.

The classes. A sentence whose text equals one of f2-examples/ens.kompile.kore's user module (up to
`Location`, `Source` and `UNIQUE'Unds'ID` attributes and whitespace) takes that sentence's class in
test/TieEns.lean's account. Any other sentence (`unmapped` in the test) takes its class from what a
probe evaluates of it (a run of the Lean definitions on the text: the symbols it applies against Γ's,
its place among Γ's function items, `tieConsB`, the constructor items) and from its form (kompile's
`// functional`, `// subsort`, `// no confusion` and `// no junk` comments, the `assoc`, `unit`, `idem`,
`priority` and `owise` attributes, set variables, a builtin `Source`); a sentence that neither gives a
class is refused by name. A mapped sentence whose probe class differs from ens's is refused too.
A sentence of a class with a theorem in test/TieEns.lean that no theorem here holds of is listed in
`uncovered`, with its class: the part of the tie that is left to write by hand.

What the kernel checks of the classes: that the lists partition the user module (`account`), that
the no-direction class is exactly the sentences applying a symbol Γ lacks (`account_absent`), and,
by each class theorem, that its list (`fnText`, `ruleText`, `consText`, the no-junk lists) is what
the theorem says. It does not check the other labels: which of the classes without a theorem here
(function functional, hooked functional, collection law, library, set-variable lemma) a sentence is
in, and which of the four constructor classes a sentence of `consText` is in, rest on ens's account
(for a mapped sentence) or on the form read above (for an unmapped one).
"""
import hashlib, json, os, re, subprocess, sys, tempfile, tomllib

HERE = os.path.dirname(os.path.abspath(__file__))
KS = os.path.dirname(os.path.dirname(HERE))          # kcore-spec
sys.path.insert(0, HERE)
sys.dont_write_bytecode = True
import kfix  # noqa: E402  (the cache of kompiled texts, kompile.txt's hashes)

FX = os.path.join(KS, "test/constructs/fixtures")
KCORE = os.environ.get("KCORE_BIN") or os.path.join(KS, ".lake/build/bin/kcore")
# K 7.1.337's builtin directory, as the f2-examples texts copied from the cache name it
BI = ("/nix/store/18pfm4wc0m4b8phf1x7nwla65iv2s44r-k-7.1.337-4a46d1231473b599c699160132fd6e76a5c46406"
      "/include/kframework/builtin")
ENS_TEXT = os.path.join(KS, "f2-examples/ens.kompile.kore")
ENS_TIE = os.path.join(KS, "test/TieEns.lean")
WRAP = ["systemd-run", "--user", "--scope", "-q", "-p", "MemoryMax=12G", "-p", "MemorySwapMax=0"]

CLASSES = ["function equation", "rewrite rule", "priority equation", "constructor functional", "subsort",
           "injectivity", "distinctness", "no junk", "function functional", "hooked functional",
           "collection law", "library", "set idempotence", "set-variable lemma", "function law",
           "open generator law", "open generator functional", "no direction"]
# the classes test/TieEns.lean states a theorem of, sentence by sentence
THEOREM_CLASSES = {"function equation", "rewrite rule", "priority equation", "constructor functional",
                   "subsort", "injectivity", "distinctness", "no junk", "set idempotence"}
CONS_CLASSES = ["constructor functional", "subsort", "injectivity", "distinctness"]


class Refused(Exception):
    pass


# ---------------------------------------------------------------------------------------------
# The sentences of a text, as findings/FIX-core-wave-A-axmap.py reads them

def axioms(text):
    """(index, module, normalised text) of each axiom, index counted from 1 over the whole text,
    the text with whitespace runs made one space and the Location, Source and UNIQUE'Unds'ID
    attributes dropped."""
    out, cur, mod = [], None, None
    for line in text.split("\n"):
        m = re.match(r"\s*module (\S+)", line)
        if m and not line.strip().startswith("//"):
            mod = m.group(1)
        if re.match(r"\s*axiom\s*\{", line):
            if cur:
                out.append(cur)
            cur = [mod, line]
        elif cur is not None:
            if line.strip() == "" or re.match(r"\s*(sort|symbol|hooked-sort|hooked-symbol|alias|endmodule|import|//)", line):
                out.append(cur)
                cur = None
            else:
                cur.append(line)
    if cur:
        out.append(cur)
    res = []
    for i, a in enumerate(out):
        s = re.sub(r"\s+", " ", " ".join(a[1:]))
        raw = s
        s = re.sub(r"org'Stop'kframework'Stop'attributes'Stop'(Location|Source)\{\}\(\"[^\"]*\"\)(, )?", "", s)
        s = re.sub(r"UNIQUE'Unds'ID\{\}\(\"[^\"]*\"\)(, )?", "", s)
        res.append((i + 1, a[0], s, raw))
    return res


def user_axioms(text):
    ax = axioms(text)
    um = ax[-1][1]
    return um, [a for a in ax if a[1] == um]


def ens_classes():
    """test/TieEns.lean's account: index -> class."""
    t = open(ENS_TIE).read()
    body = t[t.index("def classes : List (String × List Nat) :="):]
    body = body[:body.index("/-- The indices of a class. -/")]
    out = {}
    for name, nums in re.findall(r'\("([^"]+)", \[([^\]]*)\]\)', body):
        for n in re.findall(r"\d+", nums):
            out[int(n)] = name
    return out


# ---------------------------------------------------------------------------------------------
# The text, the account and the obligations, natively

def camel(name):
    return "".join(p[:1].upper() + p[1:] for p in re.split(r"[-_]", name))


def restored_text(name):
    h = kfix.recorded_sha(name)
    if not h:
        raise Refused(f"{name}: kompile.txt records no kompiled text (an error fixture, a kore fixture, or not run)")
    t = kfix.recorded_text(name)
    if t is None:
        raise Refused(f"{name}: the kompiled text of sha256 {h} is neither in .lake/kfix nor in the cache "
                      f"{kfix.CACHE} (`kfix.py run {name}` or `kfix.py cache-import`)")
    rel = f"kcore-spec/test/constructs/fixtures/{name}"
    out = t.replace("BUILTIN/", BI + "/").replace("FIXTURE/", rel + "/")
    back = out.replace(BI + "/", "BUILTIN/").replace(rel + "/", "FIXTURE/")
    if hashlib.sha256(back.encode()).hexdigest() != h:
        raise Refused(f"{name}: the text with its paths restored does not write back to sha256 {h}")
    return out


def run(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, **kw)


def account_check(name, path):
    a = run([KCORE, "account", path], cwd=KS)
    got = a.stdout + a.stderr
    want = open(os.path.join(FX, name, "account.txt")).read()
    cut = lambda s: [l for l in s[s.find("\nuser module"):].split("\n") if l and l != "(exit 0)"]
    if a.returncode != 0 or "\nuser module" not in "\n" + got:
        raise Refused(f"{name}: `kcore account` fails on the text: {got.strip()[-400:]}")
    if cut("\n" + got) != cut("\n" + want):
        raise Refused(f"{name}: `kcore account` of the text differs from the fixture's account.txt (stale fixture or binary)")
    m = re.search(r"^parse: ok; wf (\w+); failing: \[(.*)\]$", got, re.M)
    if not m:
        raise Refused(f"{name}: the account prints no `parse: ok` line")
    wf = m[1] == "true"
    failing = [x.strip() for x in m[2].split(",") if x.strip()]
    m2 = re.search(r"^coreOK: (\w+); failing: \[(.*)\]$", got, re.M)
    if not m2 or m2[1] != "true":
        raise Refused(f"{name}: coreOK fails ({m2[0] if m2 else 'no coreOK line'})")
    if re.search(r"^refused by the account: (\d+)$", got, re.M)[1] != "0":
        raise Refused(f"{name}: the account refuses sentences")
    return wf, failing


def obligations(name, path):
    with tempfile.TemporaryDirectory(prefix="tiegen-") as d:
        g = run([KCORE, "gen", path, d, "TieGenProbe", "--core"], cwd=KS)
        if g.returncode != 0:
            raise Refused(f"{name}: `kcore gen --core` fails: {(g.stdout + g.stderr).strip()[-400:]}")
        fh = open(os.path.join(d, "TieGenProbe/FnHyp.lean")).read()
        order = open(os.path.join(d, "TieGenProbe/FnHyp/Order.lean")).read()
    facts = re.search(r"^def namedFacts : List String := (\[.*?\])$", fh, re.M | re.S)
    if not facts or facts[1].strip() != "[]":
        raise Refused(f"{name}: an owed fact (`kcore gen --core`'s namedFacts: {facts[1] if facts else '?'})")
    if not re.search(r"^abbrev Obl : Prop := FnObligations defn\.sem callOrder \[\]$", fh, re.M):
        raise Refused(f"{name}: the obligations are not `FnObligations defn.sem callOrder []` (parameters or open laws)")
    co = re.search(r"def callOrder : List Nat := (\[[^\]]*\])", order)
    return re.sub(r"/-.*?-/", "", co[1]).replace(" ", "")


PROBE = r'''import KcoreSpec
open KCore ML Faithful KoreAML

def tgOrTopBot (S : P) : P := conjList [] ⇒ (sOr S (sTop S) (sBot S) ≡ inhOf S)
def tgRuleParts : Kore.Pattern → Option (Kore.KSort × Kore.Pattern × Kore.Pattern × Kore.Pattern × Kore.Pattern)
  | .rewrites C (.and _ [l, t, x]) r => some (C, l, t, x, r)
  | _ => none
def tgDropThird (p : Kore.Pattern) : Kore.Pattern :=
  match tgRuleParts p with
  | some (C, l, t, _, r) => .rewrites C (.and C [l, t]) r
  | none => p

#eval show IO Unit from do
  let input ← IO.FS.readFile "@PATH@"
  let k ← match Kore.parseDefinition input with
    | .ok k => pure k
    | .error e => throw (IO.userError s!"KORE read error {e}")
  let d ← match Parse.parse k with
    | .ok d => pure d
    | .error r => throw (IO.userError s!"KCore's parse refuses it: {r.toText}")
  let c := d.sem
  let trS := fun (ad : AxiomDecl) => trAxiom k.symbolDecls k.aliasNames ad
  let fis := fnItems c
  let ks := kernelSyms c
  let ci := consItemsK c
  let has := fun (n : String) => ks.any (fun g => c.symName g.name == n)
  let afs := c.allFns
  let css := c.ctorSigs
  let isFn := fun (n : String) => afs.any (c.symName ·.label == n)
  let isCtor := fun (n : String) => css.any (c.symName ·.name == n)
  let isHook := fun (n : String) => hookSigs.any (c.symName ·.name == n)
  let kind := fun (n : String) => if isFn n then "fn" else if isCtor n then "ctor" else if isHook n then "hook" else if has n then "other" else "absent"
  let kg := (gensInOrder c d.pres Srt.kitem).map (Gen.toK c)
  let kitemPat := (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) kg).pat
  let tsig := (Theory.ofDefinition k).signature
  let sigFrom := fun (it : Item) => tsig.any (·.pat == it.pat) || surplusItem k it
  let hasSym := has
  let plainSyms := k.symbolDecls.filter fun sd => sd.params.isEmpty && hasSym sd.name
  let plainSorts := k.sortDecls.filter (·.params.isEmpty)
  let si := sigItems c
  let declItems := plainSorts.map sortConstantItem ++ plainSyms.map arityItem
  IO.println s!"H readsConfined {c.readsConfined}"
  IO.println s!"H wf {wf d}"
  IO.println s!"H coreOK {c.coreOK}"
  IO.println s!"H attrsAgree {attrsAgree k d}"
  IO.println s!"H shapesOK {c.shapesOK}"
  IO.println s!"H rawParams {(c.params.filter (·.raw)).length}"
  IO.println s!"H nFnItems {fis.length}"
  IO.println s!"H nRuleItems {(ruleItems c).length}"
  IO.println s!"H nSig {si.length}"
  IO.println s!"H sigAll {si.all sigFrom}"
  IO.println s!"H sigBad {(si.zip (List.range si.length)).filter (!sigFrom ·.1) |>.map (·.2)}"
  let nextIt := (KoreAML.nextArityItem [] (srtOf c topCellSort)).pat
  IO.println s!"H sigBadNext {(si.filter (!sigFrom ·)).all (·.pat == nextIt)}"
  IO.println s!"H textNext {k.axiomDecls.any fun ad => !(nextSortsOf ad.ax.pattern).isEmpty}"
  IO.println s!"H nDecl {declItems.length}"
  IO.println s!"H declAll {declItems.all fun it => si.any (·.pat == it.pat)}"
  IO.println s!"H declCounts {k.sortDecls.length} {plainSorts.length} {k.symbolDecls.length} {plainSyms.length} {(k.symbolDecls.filter fun sd => !sd.params.isEmpty).length} {(k.symbolDecls.filter fun sd => sd.params.isEmpty && !hasSym sd.name).length}"
  IO.println s!"H kitemCons {decide (Srt.kitem ∈ consSorts c)} {(c.gens Srt.kitem).isEmpty}"
  IO.println s!"H kitemPerm {kg.isPerm ((c.gens Srt.kitem).map (Gen.toK c))} {decide ((c.gens Srt.kitem).map (Gen.toK c) ≠ kg)}"
  IO.println s!"H fnPrios {(c.allFns.flatMap (fun f => f.clauses.map (·.prio)))}"
  let us := k.axiomDecls.filter (·.module == "@MOD@")
  for (r, j) in c.rules.zip (List.range c.rules.length) do
    let p := prioRuleK c r
    let ok := (tgRuleParts p).isSome && decide (tableOf [] p = tableOf [] (tgDropThird p)) &&
      decide ((freeOf [] p).eraseDups = (freeOf [] (tgDropThird p)).eraseDups)
    let tgt := (trAxiom [] [] ⟨0, "kernel", ⟨[], tgDropThird p, []⟩⟩).pat
    let is := (us.filter (fun ad => (trS ad).pat == tgt)).map (·.index)
    IO.println s!"R {j}\t{ok}\t{is}"
  for ad in us do
    let p := (trS ad).pat
    let absent := !(symbolsOf ad.ax.pattern).all (fun n => n == "inj" || has n)
    let fnJ := ((fis.zip (List.range fis.length)).filter (fun (it, _) => it.pat == p)).map (·.2)
    let cons := tieConsB c ad.ax
    let plain := decide (p = (trAxiom [] [] ad).pat)
    let consItem := ci.any (·.pat == p)
    let triv := (k.sortDecls.filter fun sd => p == tgOrTopBot (sym (.sort sd.name))).map (·.name)
    let kitem := p == kitemPat
    let rw := AttrsAgree.isRewrite ad.ax.pattern
    let eh := (AttrsAgree.eqnHead ad.ax.pattern).getD ""
    let fh := match ad.ax.pattern with
      | .exist _ _ (.equals _ _ _ (.app h _ _)) => h.ident.name
      | _ => ""
    IO.println s!"S {ad.index}\t{absent}\t{fnJ}\t{cons}\t{plain}\t{consItem}\t{triv}\t{kitem}\t{rw}\t{eh}\t{kind eh}\t{fh}\t{kind fh}\t{AttrsAgree.prioOf ad.ax.attributes}"
'''


def probe(name, path, um):
    with tempfile.TemporaryDirectory(prefix="tiegen-") as d:
        f = os.path.join(d, "Probe.lean")
        open(f, "w").write(PROBE.replace("@PATH@", os.path.abspath(path)).replace("@MOD@", um))
        env = dict(os.environ, LEAN_NUM_THREADS="1")
        r = run(WRAP + ["timeout", os.environ.get("TIEGEN_PROBE_TIMEOUT", "900"), "lake", "env", "lean", "-j1", f], cwd=KS, env=env)
    if r.returncode != 0:
        raise Refused(f"{name}: the probe fails: {(r.stdout + r.stderr).strip()[-600:]}")
    head, sents = {}, {}
    head["rules"] = []
    for l in r.stdout.split("\n"):
        if l.startswith("H "):
            k, _, v = l[2:].partition(" ")
            head[k] = v
        elif l.startswith("R "):
            f = l[2:].split("\t")
            head["rules"].append((int(f[0]), f[1] == "true", [int(x) for x in re.findall(r"\d+", f[2])]))
        elif l.startswith("S "):
            f = l[2:].split("\t")
            nums = lambda s: [int(x) for x in re.findall(r"\d+", s)]
            sents[int(f[0])] = dict(absent=f[1] == "true", fnJ=nums(f[2]), cons=f[3] == "true", plain=f[4] == "true",
                                    consItem=f[5] == "true", triv=re.findall(r"Sort[^,\]\s]+", f[6]),
                                    kitem=f[7] == "true", rw=f[8] == "true", eh=f[9], ehk=f[10], fh=f[11],
                                    fhk=f[12], prio=int(f[13]))
    return head, sents


# ---------------------------------------------------------------------------------------------
# Classes

def form_class(s, raw, builtin):
    """The class a sentence's form and its probe give, or None."""
    if s["absent"]:
        return "no direction"
    if s["fnJ"]:
        return "function equation"
    if s["rw"]:
        return "rewrite rule"
    if s["triv"] or s["consItem"] or s["kitem"] or "// no junk" in raw:
        return "no junk"
    if "[subsort{" in raw:
        return "subsort"
    if "// no confusion same constructor" in raw:
        return "injectivity"
    if "// no confusion different constructors" in raw:
        return "distinctness"
    if "[functional{}()]" in raw and s["fh"]:
        return {"ctor": "constructor functional", "fn": "function functional", "hook": "hooked functional"}.get(s["fhk"])
    if s["ehk"] == "fn" and not builtin:
        return "priority equation" if (s["prio"] != 50 and s["prio"] != 200) else "function equation"
    if "[idem{}()]" in raw:
        return "set idempotence"
    if "[assoc{}()]" in raw or "[unit{}()]" in raw:
        return "collection law"
    if re.search(r"@Var\w*:", raw) and "simplification{}" in raw:
        return "set-variable lemma"
    if builtin:
        return "library"
    return None


def classify(name, text, sents):
    um, ua = user_axioms(text)
    if sorted(sents) != [a[0] for a in ua]:
        raise Refused(f"{name}: the probe's user-module sentences are not the text's (indices differ)")
    _, ea = user_axioms(open(ENS_TEXT).read())
    ecls = ens_classes()
    pool = {}
    for i, _, s, _ in ea:
        pool.setdefault(s, []).append(i)
    cls, mapped, unmapped = {}, {}, []
    for i, _, s, raw in ua:
        builtin = "/include/kframework/builtin/" in raw
        fc = form_class(sents[i], raw, builtin)
        if pool.get(s):
            j = pool[s].pop(0)
            mapped[i] = j
            ec = ecls[j]
            # where the probe decides the class (a symbol Γ lacks, an item of Γ), it must agree with ens's
            decided = fc if fc in ("no direction", "function equation", "rewrite rule") or (fc == "no junk" and ec == "no junk") else None
            if (ec == "no direction") != sents[i]["absent"]:
                raise Refused(f"{name}: sentence {i} is ens's {j} (class {ec}), but here it applies "
                              f"{'a symbol Γ lacks' if sents[i]['absent'] else 'only symbols Γ has'}")
            if decided and decided != ec:
                raise Refused(f"{name}: sentence {i} is ens's {j} (class {ec}), but the probe gives {decided}")
            cls[i] = ec
        else:
            if fc is None:
                raise Refused(f"{name}: sentence {i} has no ens counterpart and neither its form nor the probe gives its class: {raw[:200]}")
            cls[i] = fc
            unmapped.append(i)
    return um, cls, mapped, unmapped


# ---------------------------------------------------------------------------------------------
# The Lean text

def wrap_nums(nums, indent, width=100):
    lines, cur = [], ""
    for n in nums:
        piece = f"{n}, "
        if len(cur) + len(piece) + indent > width:
            lines.append(cur.rstrip())
            cur = ""
        cur += piece
    lines.append(cur.rstrip().rstrip(","))
    return ("\n" + " " * indent).join(lines)


def ax_list(nums, indent=3):
    return "[" + wrap_nums([f"U.ax{n}" for n in nums], indent) + "]"


def ranges(n, first, chunk):
    """[(a, len)] covering 0..n: one block of `first`, then blocks of `chunk`, the last open."""
    out, a = [], 0
    if first and first < n:
        out.append((a, first))
        a = first
    while a + chunk < n:
        out.append((a, chunk))
        a += chunk
    out.append((a, None))
    return out


def by_ranges(prefix, lst, pred, rs):
    thms, chain = [], []
    for a, ln in rs:
        if ln is None:
            thms.append(f"theorem {prefix}_{a} : (({lst}).drop {a}).all {pred} = true := by decide +kernel")
        else:
            thms.append(f"theorem {prefix}_{a} : ((({lst}).drop {a}).take {ln}).all {pred} = true := by decide +kernel")
    body = f"tieAllE_whole (p := {pred}) <|\n"
    for a, ln in rs[:-1]:
        body += f"    tieAllE_range (a := {a}) (n := {ln}) {prefix}_{a} <|\n"
    body += f"    {prefix}_{rs[-1][0]}"
    return "\n".join(thms), body


def generate(name, text_rel, um, cls, mapped, unmapped, sents, head, wf_ok, failing, call_order, chunks):
    ns = "Tie" + camel(name)
    idx = sorted(cls)
    by_class = {c: [i for i in idx if cls[i] == c] for c in CLASSES}
    nfn = int(head["nFnItems"])
    nrules = int(head["nRuleItems"])
    # function equations, in fnItems' order
    fn_order = {}
    for i in by_class["function equation"]:
        for j in sents[i]["fnJ"]:
            fn_order.setdefault(j, []).append(i)
    fn_full = (sorted(fn_order) == list(range(nfn)) and all(len(v) == 1 for v in fn_order.values())
               and sorted(v[0] for v in fn_order.values()) == by_class["function equation"])
    fn_text = [fn_order[j][0] for j in range(nfn)] if fn_full else []
    cons_text = [i for i in idx if cls[i] in CONS_CLASSES and sents[i]["cons"] and sents[i]["plain"]]
    nj = by_class["no junk"]
    nj_triv = [(i, sents[i]["triv"][0]) for i in nj if sents[i]["triv"]]
    nj_items = [i for i in nj if not sents[i]["triv"] and sents[i]["consItem"]]
    kc = head["kitemCons"].split()
    kp = head["kitemPerm"].split()
    kitem_ok = kc == ["true", "false"] and kp == ["true", "true"]
    nj_kitem = [i for i in nj if not sents[i]["triv"] and not sents[i]["consItem"] and sents[i]["kitem"] and kitem_ok]
    inv = {j: i for i, j in mapped.items()}
    idem = inv.get(61) if cls.get(inv.get(61)) == "set idempotence" else None
    lib166 = inv.get(166) if cls.get(inv.get(166)) == "library" else None
    rule_map = [(j, ix[0]) for j, ok, ix in head["rules"] if ok and len(ix) == 1]
    rules_full = (len(rule_map) == nrules and sorted(i for _, i in rule_map) == by_class["rewrite rule"])
    rule_text = [i for _, i in rule_map] if rules_full else []
    covered = set(fn_text) | set(rule_text) | set(cons_text) | {i for i, _ in nj_triv} | set(nj_items) | set(nj_kitem)
    if idem is not None:
        covered.add(idem)
    uncovered = [(i, cls[i]) for i in idx if cls[i] in THEOREM_CLASSES and i not in covered]
    gamma = fn_full and rules_full
    sig_rs = ranges(int(head["nSig"]), chunks[0], chunks[1])
    decl_rs = ranges(int(head["nDecl"]), 0, chunks[2])
    dc = head["declCounts"].split()

    L = []
    w = L.append
    # ---- header
    w("/-")
    w(f"  The tie (C14) on `{text_rel}`, the kompiled text of construct fixture {name}")
    w(f"  (`test/constructs/fixtures/{name}`), sentence by sentence, against the translation of the text as")
    w("  written (`trS ad := trAxiom k.symbolDecls k.aliasNames ad`), on the literals `kore` and `defn`, for")
    w("  every interpretation H. Nothing here reads `Parse.parse` or `emit`. Written by")
    w(f"  `test/constructs/tiegen.py {name}`; run from the package root: `lake env lean -j1 test/{ns}.lean`.")
    w("")
    w("  Layer 1.")
    if wf_ok:
        w("  - `wf_defn`: `wf defn = true`.")
    else:
        w(f"  - `coreOK`: `coreOK`; `wf` fails at the conjuncts {', '.join(failing)} (`wfFailing`).")
    w(f"  - The account: the class lists partition the {len(idx)} sentences of the user module {um}, in")
    w("    `tieClasses`' order (`account`, `account_sizes`, `account_classes`); the no-direction class holds")
    w("    exactly the sentences that apply a symbol Γ lacks (`account_absent`, `absent_closed`).")
    w("  - `attrs_agree`: the attributes the translation does not read agree with `defn`.")
    if head["sigAll"] == "true":
        w(f"  - `sig_origin`: each of the {head['nSig']} items of `sigItems c` is a declaration's item of the text or a")
        w("    surplus one; `decls_entailed`: Γ entails the item of each declaration without sort parameters")
        w("    of a symbol Γ has (both by ranges of the lists).")
    else:
        w(f"  - `sig_origin_but_next`: each of the {head['nSig']} items of `sigItems c` but one is a declaration's item")
        w("    of the text or a surplus one; the one is next's arity at the configuration sort, which Γ states")
        w("    and the text, having no `\\rewrites` (`text_nextless`), does not. `decls_entailed`: Γ entails")
        w("    the item of each declaration without sort parameters of a symbol Γ has (by ranges of the lists).")
    w("  - The definition reads no confined sort (`readsConfined_c`), has no open generator (`noRaw`) and")
    w("    owes no fact (`term_named`, `total_named`, `agree_named`, `match_named`), so Γ with the step's")
    w("    closure has a model for every H (`consistent`).")
    w("")
    w("  Layer 2, by class (indices are the text's axiom numbers, `AxiomDecl.index`).")
    if fn_full:
        w(f"  - Function equations ({len(fn_text)}): each of Γ's items is the translation of one sentence, in the")
        w("    order `fnText` lists them (`fn_shape`); `fns_entailed` (E), `fns_from_text` (the converse),")
        w("    `fn_prios` (the priorities the sentences state are the clauses').")
    if rules_full and nrules:
        w(f"  - Rewrite rules ({nrules}): each of Γ's rule items (with the premise `⌈rhs ∧ ens⌉`) is a consequence")
        w("    of its text sentence, `ruleText` in `ruleItems`' order (`rule_from_text`, W1, every H).")
    w(f"  - Constructor sentences ({len(cons_text)}): entailed by Γ (`cons_entailed`).")
    w(f"  - No junk ({len(nj_triv)} of a sort without generators, `nojunk_trivial_entailed`; {len(nj_items)} equal to")
    w(f"    one of Γ's constructor items, `nojunk_items`; {len(nj_kitem)} KItem's with its disjuncts in the text's")
    w("    order, `nojunk_kitem_entailed`).")
    if idem is not None:
        w(f"  - Set idempotence ({idem}): Γ with it has no model (`idem_refuted`).")
    if lib166 is not None:
        w(f"  - Library sample, {lib166} (`I -Int 0 = I`): holds at values (`lib166`, `lib166_at_values`).")
    if gamma:
        w("  - The converse over Γ's content: each premise is a function sentence's translation, one of the")
        w("    five parts Γ defines by predicates, or definedness (`gamma_origin`, `gamma_from`).")
    w("  - Hooked functional, collection law, library: at values (no theorem here); function functional:")
    w("    owed as `FnHyp` (no theorem); no direction: `absent_closed`.")
    w("")
    w(f"  The sentences with no counterpart in f2-examples/ens.kompile.kore are `unmapped` ({len(unmapped)});")
    w(f"  the sentences of a class with a theorem that no theorem here holds of are `uncovered` ({len(uncovered)}).")
    w("-/")
    w("import KcoreSpec")
    w("")
    w("set_option autoImplicit false")
    w("set_option maxRecDepth 1000000")
    w("")
    w(f"namespace KCore.{ns}")
    w("")
    w("open KCore ML Faithful KoreAML")
    w("")
    w(f'kore_term kore from "{text_rel}"')
    w(f'definition_of defn from "{text_rel}"')
    w(f'user_axioms U from "{text_rel}" module "{um}"')
    w("")
    w("noncomputable abbrev c : Semantics := defn.sem")
    w("noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H")
    w("")
    w("/-- No parameter of the definition is an open generator. -/")
    w("theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel")
    w("")
    w("/-- The definition reads no confined sort: its theory is Γ. -/")
    w("theorem readsConfined_c : c.readsConfined = false := by decide +kernel")
    w("")
    w("/-- The axioms of the user module, in text order. -/")
    w(f'noncomputable def userAxioms : List AxiomDecl := kore.axiomDecls.filter (·.module == "{um}")')
    w("")
    w("theorem userAxioms_eq : userAxioms = U.all := by kernel_rfl")
    w(f"theorem userAxioms_length : U.all.length = {len(idx)} := by decide +kernel")
    w("")
    w("/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/")
    w("noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad")
    w("")
    w("theorem trS_is_text : (Theory.ofDefinition kore).axioms = kore.axiomDecls.map trS := rfl")
    w("")
    w("/-! ## Layer 1 -/")
    w("")
    w("set_option maxHeartbeats 1000000 in")
    w("theorem coreOK : c.coreOK = true := by decide_cheap")
    w("theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK")
    w("")
    if wf_ok:
        w("set_option maxHeartbeats 1000000 in")
        w("theorem wf_defn : wf defn = true := by decide_cheap")
    else:
        w("/-- The conjuncts of `wf` that fail on this text (`kcore account`); `coreOK` holds. -/")
        w("def wfFailing : List String := [" + ", ".join(f'"{x}"' for x in failing) + "]")
    w("")
    # ---- account
    w("/-! ## The account: every sentence of the user module is in exactly one class -/")
    w("")
    w("/-- Per class of the tie (`tieClasses`), the indices (`AxiomDecl.index`) of its sentences. -/")
    w("def classes : List (String × List Nat) :=")
    rows = []
    for c_ in CLASSES:
        rows.append(f'("{c_}", [' + wrap_nums(by_class[c_], 6) + "])")
    w("  [" + ",\n   ".join(rows) + "]")
    w("")
    w("/-- The indices of a class. -/")
    w("def classOf (n : String) : List Nat := (classes.filter (·.1 == n)).flatMap (·.2)")
    w("")
    w("/-- **The account**: the class lists partition the user module's sentences. Their concatenation is")
    w("a permutation of the sentences' indices, which are distinct, so each sentence is in one class and")
    w("in it once. -/")
    w("theorem account : (classes.flatMap (·.2)).isPerm (userAxioms.map (·.index)) = true ∧")
    w("    (userAxioms.map (·.index)).Nodup := by")
    w("  rw [userAxioms_eq]; decide +kernel")
    w("")
    w("/-- The class sizes. -/")
    w("theorem account_sizes : classes.map (fun cl => (cl.1, cl.2.length)) =")
    w("    [" + ", ".join(f'("{c_}", {len(by_class[c_])})' for c_ in CLASSES) + "] := by")
    w("  decide +kernel")
    w("")
    w("/-- The classes are the tie's (`tieClasses`, which gives each its direction), in its order. -/")
    w("theorem account_classes : classes.map (·.1) = tieClasses.map (·.1) := by decide +kernel")
    w("")
    w("/-- **A sentence outside the no-direction class applies only symbols Γ has** (the injection `inj`")
    w("aside, which Γ's constructor items apply), and each sentence of that class applies one Γ lacks. -/")
    w("theorem account_absent : userAxioms.all (fun ad =>")
    w('    (classOf "no direction").contains ad.index !=')
    w('      (symbolsOf ad.ax.pattern).all (fun n => n == "inj" || (kernelSyms c).any (fun k => c.symName k.name == n))) = true := by')
    w("  rw [userAxioms_eq]; decide +kernel")
    w("")
    w("/-- **The no-direction class is closed**: every sentence outside it applies only symbols Γ has. -/")
    w("theorem absent_closed :")
    w('    (userAxioms.filter (fun ad => !(classOf "no direction").contains ad.index)).all')
    w("      (fun ad => (symbolsOf ad.ax.pattern).all")
    w('        (fun n => n == "inj" || (kernelSyms c).any (fun k => c.symName k.name == n))) = true :=')
    w("  tieAbsent_of_account userAxioms _ _ account_absent")
    w("")
    w("/-- The sentences whose text is none of f2-examples/ens.kompile.kore's user module, with their class. -/")
    w("def unmapped : List (Nat × String) :=")
    w("  [" + wrap_nums([f'({i}, "{cls[i]}")' for i in unmapped], 3) + "]")
    w("")
    w("/-- The sentences of a class with a theorem in the tie that no theorem of this file holds of: the")
    w("tie's remainder on this text. -/")
    w("def uncovered : List (Nat × String) :=")
    w("  [" + wrap_nums([f'({i}, "{c_}")' for i, c_ in uncovered], 3) + "]")
    w("")
    w("/-- Each listed sentence is in its class in the account. -/")
    w("theorem lists_in_account : (unmapped ++ uncovered).all (fun ic => (classOf ic.2).contains ic.1) = true := by")
    w("  decide +kernel")
    w("")
    w("/-! ## The attributes -/")
    w("")
    w("/-- **The attributes of the text agree with `defn`** (`attrsAgree`): constructors, functions,")
    w("hooks, collection symbols, priorities. -/")
    w("theorem attrs_agree : attrsAgree kore defn = true := by decide +kernel")
    w("")
    # ---- signature
    w("/-! ## The declarations: `sig_origin` and `decls_entailed`, by ranges -/")
    w("")
    w("/-- `p` holds from `a` on where it holds on the `n` members from `a` and from `a + n` on. -/")
    w("theorem tieAllE_range {α : Type} {l : List α} {p : α → Bool} {a n : Nat}")
    w("    (h : ((l.drop a).take n).all p = true) (ht : (l.drop (a + n)).all p = true) :")
    w("    (l.drop a).all p = true := by")
    w("  rw [← List.take_append_drop n (l.drop a), List.all_append, h, List.drop_drop, ht]; rfl")
    w("")
    w("/-- `p` holds of the whole list where it holds from `0` on. -/")
    w("theorem tieAllE_whole {α : Type} {l : List α} {p : α → Bool} (h : (l.drop 0).all p = true) :")
    w("    l.all p = true := h")
    w("")
    w("/-- The item of Γ's signature is a declaration's item of the text, or a surplus one. -/")
    w("noncomputable def sigFrom (it : Item) : Bool :=")
    w("  (Theory.ofDefinition kore).signature.any (·.pat == it.pat) || surplusItem kore it")
    w("")
    sig_next = head["sigAll"] != "true"
    if sig_next:
        w("/-- Next's arity at the configuration sort, which Γ states whatever the text. -/")
        w("noncomputable def nextItem : Item := KoreAML.nextArityItem [] (srtOf c topCellSort)")
        w("")
        w("/-- No sentence of the text has a `\\rewrites` or a `\\next`, so the text's signature states the")
        w("arity of next at no sort. -/")
        w("theorem text_nextless : kore.axiomDecls.all (fun ad => (nextSortsOf ad.ax.pattern).isEmpty) = true := by")
        w("  decide +kernel")
        w("")
        w("/-- The item has an origin in the text, or is next's arity at the configuration sort. -/")
        w("noncomputable def sigFromN (it : Item) : Bool := sigFrom it || it.pat == nextItem.pat")
        w("")
    pred = "sigFromN" if sig_next else "sigFrom"
    thms, body = by_ranges("sigE", "sigItems c", pred, sig_rs)
    w(thms)
    w("")
    w(f"theorem sig_sizes : (sigItems c).length = {head['nSig']} := by decide +kernel")
    w("")
    if sig_next:
        w("/-- **Every item of Γ's signature but next's arity has its origin**: the item of a declaration of")
        w("the text, or the sort constant of a registry sort or the arity of an interpreted hooked symbol that")
        w("the text does not declare at that shape. Next's arity at the configuration sort has none: the")
        w("text has no rule (`text_nextless`). -/")
        w("theorem sig_origin_but_next : (sigItems c).all (fun it =>")
        w("    (Theory.ofDefinition kore).signature.any (·.pat == it.pat) || surplusItem kore it ||")
        w("      it.pat == nextItem.pat) = true :=")
    else:
        w("/-- **Every item of Γ's signature has its origin**: the item of a declaration of the text, or the")
        w("sort constant of a registry sort or the arity of an interpreted hooked symbol that the text does not")
        w("declare at that shape. -/")
        w("theorem sig_origin : (sigItems c).all (fun it =>")
        w("    (Theory.ofDefinition kore).signature.any (·.pat == it.pat) || surplusItem kore it) = true :=")
    w("  " + body)
    w("")
    w("kernel_rfl sigItems_withHooks : ∀ (c : Semantics) (H : HookParams), sigItems (c.withHooks H) = sigItems c")
    w("")
    w("/-- Γ has a symbol under the name `n`. -/")
    w("noncomputable def hasSym (n : String) : Bool := (kernelSyms c).any fun k => c.symName k.name == n")
    w("")
    w("noncomputable def plainSorts : List SortDecl := kore.sortDecls.filter (·.params.isEmpty)")
    w("noncomputable def plainSyms : List SymbolDecl := kore.symbolDecls.filter fun sd => sd.params.isEmpty && hasSym sd.name")
    w("noncomputable def declItems : List Item := plainSorts.map sortConstantItem ++ plainSyms.map arityItem")
    w("")
    w("/-- The item is one of `sigItems c`, pattern for pattern. -/")
    w("noncomputable def inSigItems (it : Item) : Bool := (sigItems c).any (·.pat == it.pat)")
    w("")
    w("/-- The declarations of the text: sorts, sorts without parameters, symbols, symbols without")
    w("parameters that Γ has, symbols with parameters, symbols without parameters that Γ lacks. -/")
    w("theorem decl_counts :")
    w("    (kore.sortDecls.length, plainSorts.length, kore.symbolDecls.length, plainSyms.length,")
    w("      (kore.symbolDecls.filter fun sd => !sd.params.isEmpty).length,")
    w(f"      (kore.symbolDecls.filter fun sd => sd.params.isEmpty && !hasSym sd.name).length) = ({', '.join(dc)}) := by")
    w("  decide +kernel")
    w("")
    thms, body = by_ranges("declsE", "declItems", "inSigItems", decl_rs)
    w(thms)
    w("")
    w("theorem decls_in_sig : declItems.all inSigItems = true :=")
    w("  " + body)
    w("")
    w("/-- **E for the declarations**: Γ entails the item of each declaration without sort parameters of")
    w("a symbol Γ has, for every H. -/")
    w("theorem decls_entailed (H : HookParams) : ∀ it ∈ declItems, Γ (cH H) ⊧ it.pat := by")
    w("  intro it hit M _ I hI")
    w("  have h1 : (sigItems c).any (·.pat == it.pat) = true := List.all_eq_true.mp decls_in_sig it hit")
    w("  obtain ⟨it', hit', he⟩ := List.any_eq_true.mp h1")
    w("  rw [← of_decide_eq_true he]")
    w("  exact sat_sigItem hI (by rw [sigItems_withHooks]; exact hit')")
    w("")
    # ---- consistency
    w("/-! ## Consistency for every H -/")
    w("")
    w(f"def callOrder : List Nat := {call_order}")
    w("")
    w("theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel")
    w("theorem total_named : c.totalObligationsRP callOrder [] = [] := by decide +kernel")
    w("theorem agree_named : c.agreeObligationsI = [] := by decide +kernel")
    w("theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel")
    w("")
    w("theorem obl_nil (H : HookParams) : FnObligations (cH H) callOrder [] :=")
    w("  FnObligations.of_nil")
    w("    (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named)")
    w("    ((Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named)")
    w("    ((Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named)")
    w("    ((Det.Semantics.matchObligationsL_withHooks _ H).trans match_named)")
    w("")
    w("theorem fnHypH (H : HookParams) : FnHyp (cH H) := fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H")
    w("  ParamsTotal.nil (obl_nil H)")
    w("")
    w("/-- **Γ with the step's closure has a model, for every H.** -/")
    w("theorem consistent (H : HookParams) : Consistent (cH H) := consistent_of_fnHyp _ (coreOKH H) (fnHypH H)")
    w("")
    w("/-! ## Γ under every interpretation reads the same equations and rules -/")
    w("")
    w("kernel_rfl fnItems_withHooks : ∀ (c : Semantics) (H : HookParams), fnItems (c.withHooks H) = fnItems c")
    w("kernel_rfl ruleItems_withHooks : ∀ (c : Semantics) (H : HookParams), ruleItems (c.withHooks H) = ruleItems c")
    w("")
    w("theorem mem_Γ_fns {c : Semantics} {φ : P} (h : ΓFns c φ) : Γ c φ := Or.inl (Or.inl (Or.inr h))")
    w("")
    if fn_full:
        w(f"/-! ## Function equations ({len(fn_text)} sentences) -/")
        w("")
        w("/-- The axioms of Γ's equations, in `fnItems`'s order. -/")
        w("noncomputable def fnAxioms (c : Semantics) : List Kore.Axiom :=")
        w("  c.allFns.flatMap fun f => (fnEquationsK c f).filterMap fun")
        w("    | .axiom a => some a")
        w("    | _ => none")
        w("")
        w('theorem fnItems_eq : fnItems c = (fnAxioms c).map fun a => trAxiom [] [] ⟨0, "kernel", a⟩ := by kernel_rfl')
        w("")
        w(f"/-- The text sentences of Γ's {len(fn_text)} equations, in `fnItems`'s order. -/")
        w("noncomputable def fnText : List AxiomDecl :=")
        w("  " + ax_list(fn_text))
        w("")
        w("/-- **Γ's equations are the text's sentences' translations, pattern for pattern** (one kernel")
        w("decision). -/")
        w("theorem fn_shape : (fnItems c).map (·.pat) = fnText.map (trS · |>.pat) := by")
        w("  rw [fnItems_eq, List.map_map]")
        w("  exact (by decide +kernel :")
        w('    ((fnAxioms c).map fun a => (trAxiom [] [] ⟨0, "kernel", a⟩).pat) = fnText.map (trS · |>.pat))')
        w("")
        w("/-- **`fnText` is the account's function-equation class**: the same indices, each once. -/")
        w('theorem fns_account : (classOf "function equation").isPerm (fnText.map (·.index)) = true := by decide +kernel')
        w("")
        w("/-- **E for the equations**: Γ entails each, for every H. -/")
        w("theorem fns_entailed (H : HookParams) : ∀ ad ∈ fnText, Γ (cH H) ⊧ (trS ad).pat := by")
        w("  intro ad had M _ I hI")
        w("  have hmem : (trS ad).pat ∈ (fnItems c).map (·.pat) := by")
        w("    rw [fn_shape]; exact List.mem_map.mpr ⟨ad, had, rfl⟩")
        w("  obtain ⟨it, hit, he⟩ := List.mem_map.mp hmem")
        w("  exact hI _ (mem_Γ_fns (Or.inl ⟨it, by rw [fnItems_withHooks]; exact hit, he⟩))")
        w("")
        w("/-- **The converse for `fnItems`**: the j-th item is a consequence of `fnText[j]`. -/")
        w("theorem fns_from_text (H : HookParams) :")
        w("    ∀ (j : Nat) (it : Item), (fnItems (cH H))[j]? = some it →")
        w("      ∃ ad, fnText[j]? = some ad ∧ (itemsPremises [trS ad] ⊧ it.pat) := by")
        w("  intro j it hj")
        w("  rw [fnItems_withHooks] at hj")
        w("  have h1 : ((fnItems c).map (·.pat))[j]? = some it.pat := by rw [List.getElem?_map, hj]; rfl")
        w("  rw [fn_shape, List.getElem?_map] at h1")
        w("  cases hf : fnText[j]? with")
        w("  | none => rw [hf] at h1; cases h1")
        w("  | some ad =>")
        w("    rw [hf] at h1")
        w("    refine ⟨ad, rfl, fun {M} _ {I} hI => ?_⟩")
        w("    have he : (trS ad).pat = it.pat := Option.some.inj h1")
        w("    exact hI _ (Or.inl ⟨trS ad, List.mem_singleton_self _, he⟩)")
        w("")
        w("/-- The priority each function sentence's attributes state is the priority of the clause whose")
        w("item is the sentence's translation, item by item in `fnItems`'s order. -/")
        w("theorem fn_prios : fnText.map (fun ad => AttrsAgree.prioOf ad.ax.attributes) =")
        w("    c.allFns.flatMap (fun f => f.clauses.map (·.prio)) := by decide +kernel")
        w("")
    if rules_full and nrules:
        w(ens_section("/-! ## The rule (sentence 155): W1 -/", "noncomputable def r0 : Rule").replace(
            "/-! ## The rule (sentence 155): W1 -/", f"/-! ## The rules ({nrules} sentences): W1 -/"))
        for j, i in rule_map:
            w(f"noncomputable def r{j} : Rule := c.rules[{j}]'(by decide +kernel)")
        w("")
        w("theorem ruleItems_eq : ruleItems c = [" + ",\n    ".join(
            f"trAxiom [] [] (kAx (prioRuleK c r{j}))" for j, _ in rule_map) + "] := by kernel_rfl")
        w("")
        w("/-- The text sentences of Γ's rules, in `ruleItems`'s order. -/")
        w("noncomputable def ruleText : List AxiomDecl :=")
        w("  " + ax_list(rule_text))
        w("")
        w("/-- **`ruleText` is the account's rewrite-rule class**: the same indices, each once. -/")
        w('theorem rules_account : (classOf "rewrite rule").isPerm (ruleText.map (·.index)) = true := by decide +kernel')
        w("")
        for j, i in rule_map:
            w(f"theorem rule{j}_parts : (ruleParts (prioRuleK c r{j})).isSome = true := by decide +kernel")
            w(f"theorem rule{j}_table : tableOf [] (prioRuleK c r{j}) = tableOf [] (dropThird (prioRuleK c r{j})) := by decide +kernel")
            w(f"theorem rule{j}_free : (freeOf [] (prioRuleK c r{j})).eraseDups = (freeOf [] (dropThird (prioRuleK c r{j}))).eraseDups := by")
            w("  decide +kernel")
            w(f"/-- Γ's item of rule {j} without its premise `⌈rhs ∧ ens⌉` is the text's sentence {i}. -/")
            w(f"theorem rule{j}_text : (trS U.ax{i}).pat = (trAxiom [] [] (kAx (dropThird (prioRuleK c r{j})))).pat := by decide +kernel")
            w(f"/-- **W1 for rule {j}**: Γ's item is a consequence of sentence {i}. -/")
            w(f"theorem rule{j}_from_text : itemsPremises [trS U.ax{i}] ⊧ (trAxiom [] [] (kAx (prioRuleK c r{j}))).pat := by")
            w("  intro M _ I hI")
            w("  have hD : DefOK I := defOK_of fun x => hI _ (Or.inr ⟨x, rfl⟩)")
            w(f"  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp rule{j}_parts")
            w("  obtain ⟨C, l, t, x, r⟩ := q")
            w(f"  refine rewrite_weaken hD hq rule{j}_table rule{j}_free ?_")
            w(f"  rw [← rule{j}_text]")
            w(f"  exact hI _ (Or.inl ⟨trS U.ax{i}, List.mem_singleton_self _, rfl⟩)")
            w("")
        w("set_option maxHeartbeats 4000000 in")
        w("/-- **W1 for the rules, and the converse for `ruleItems`**: each of Γ's rule items is a")
        w("consequence of a text sentence of `ruleText`, for every H. -/")
        w("theorem rule_from_text (H : HookParams) : ∀ it ∈ ruleItems (cH H), ∃ ad ∈ ruleText, itemsPremises [trS ad] ⊧ it.pat := by")
        w("  intro it hit")
        w("  rw [ruleItems_withHooks, ruleItems_eq] at hit")
        w("  simp only [List.mem_cons, List.not_mem_nil, or_false] at hit")
        w("  rcases hit with " + " | ".join(["rfl"] * nrules))
        for k, (j, i) in enumerate(rule_map):
            mem = "List.mem_cons_self"
            for _ in range(k):
                mem = f"List.mem_cons_of_mem _ ({mem})"
            w(f"  · exact ⟨U.ax{i}, {mem}, rule{j}_from_text⟩")
        w("")
    # ---- no junk
    w("/-! ## No junk -/")
    w("")
    if nj_triv:
        w("/-- `\\or{S}(\\top{S}(), \\bottom{S}())` as an axiom: `⊤ ⇒ (⊤_S ∨ ⊥_S ≡ ⟦S⟧)`. -/")
        w("def orTopBot (S : P) : P := conjList [] ⇒ (sOr S (sTop S) (sBot S) ≡ inhOf S)")
        w("")
        w("theorem orTopBot_valid {M : Type} {I : Interpretation KoreAML.Sym M} (hD : DefOK I) {S : P}")
        w("    (hS : S.isFreeEvar topVar = false) : I ⊧ᴵ orTopBot S := by")
        w("  intro e m")
        w("  unfold orTopBot")
        w("  rw [interpret_impl]")
        w("  intro _")
        w("  rw [interp_equal hD]")
        w("  intro a")
        w("  rw [interp_sOr, interp_sTop hD hS]")
        w("  exact ⟨fun h => h.1, fun h => ⟨h, Or.inl h⟩⟩")
        w("")
        for i, s in nj_triv:
            w(f'theorem nj{i} : (trS U.ax{i}).pat = orTopBot (sym (.sort "{s}")) := by decide +kernel')
        w("")
        w("/-- **E for the no-junk sentences of the sorts without generators**: logical truths, entailed by")
        w("Γ for every H. -/")
        w("theorem nojunk_trivial_entailed (H : HookParams) :")
        w(f"    ∀ ad ∈ {ax_list([i for i, _ in nj_triv], 6)}, Γ (cH H) ⊧ (trS ad).pat := by")
        w("  intro ad had M _ I hI")
        w("  have hD := defOK hI")
        w("  simp only [List.mem_cons, List.not_mem_nil, or_false] at had")
        w("  rcases had with " + " | ".join(["rfl"] * len(nj_triv)))
        for i, _ in nj_triv:
            w(f"  · rw [nj{i}]; exact orTopBot_valid hD rfl")
        w("")
    if nj_items:
        w("/-- **No junk of the sorts with generators**: the translation of each sentence is the pattern of")
        w("one of Γ's constructor items. -/")
        w(f"theorem nojunk_items : ∀ ad ∈ {ax_list(nj_items, 6)},")
        w("    (consItemsK c).any (·.pat == (trS ad).pat) = true := by decide +kernel")
        w("")
        w("kernel_rfl consItemsK_withHooks : ∀ (c : Semantics) (H : HookParams), consItemsK (c.withHooks H) = consItemsK c")
        w("")
        w("/-- **E for those**: Γ entails each, for every H. -/")
        w(f"theorem nojunk_items_entailed (H : HookParams) : ∀ ad ∈ {ax_list(nj_items, 6)},")
        w("    Γ (cH H) ⊧ (trS ad).pat := by")
        w("  intro ad had M _ I hI")
        w("  obtain ⟨it, hit, he⟩ := List.any_eq_true.mp (nojunk_items ad had)")
        w("  rw [← of_decide_eq_true he]")
        w("  exact sat_cons hI (Or.inl ⟨it, by rw [consItemsK_withHooks]; exact hit, rfl⟩)")
        w("")
    for i in nj_kitem:
        w("/-- KItem's no-junk sentence is the item over KItem's generators in the text's order, the same")
        w("generators as `Semantics.gens` lists, in another order. -/")
        w(f"theorem nojunk_kitem_order : (trS U.ax{i}).pat =")
        w("    (KoreAML.Cons.noJunkItem (c.sortName Srt.kitem) ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c))).pat := by")
        w("  decide +kernel")
        w("theorem nojunk_kitem_members :")
        w("    ((gensInOrder c defn.pres Srt.kitem).map (Gen.toK c)).isPerm ((c.gens Srt.kitem).map (Gen.toK c)) = true := by")
        w("  decide +kernel")
        w("")
        w(f"/-- **E for KItem's no junk ({i})**, for every H (`noJunkItem_of_subset`). -/")
        w(f"theorem nojunk_kitem_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax{i}).pat := by")
        w("  intro M _ I hI")
        w("  rw [nojunk_kitem_order]")
        w("  refine noJunkItem_of_subset (defOK hI) (gs := (c.gens Srt.kitem).map (Gen.toK c))")
        w("    (fun g hg => (List.isPerm_iff.mp nojunk_kitem_members).mem_iff.mpr hg) ?_")
        w("  exact sat_cons hI (Or.inl ⟨_, noJunkItem_mem (c := cH H) (N := Srt.kitem)")
        w("    (show Srt.kitem ∈ consSorts c by decide +kernel) (show (c.gens Srt.kitem).isEmpty = false by decide +kernel), rfl⟩)")
        w("")
    # ---- cons
    if cons_text:
        w("/-! ## The constructor sentences: functional, subsort, injectivity, distinctness -/")
        w("")
        w("/-- The constructor sentences `tieConsB` decides, in text order. -/")
        w("noncomputable def consText : List AxiomDecl :=")
        w("  " + ax_list(cons_text))
        w("")
        w("theorem cons_checked : consText.all (fun ad => tieConsB c ad.ax) = true := by decide +kernel")
        w("")
        w("theorem cons_trS : consText.all (fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat)) = true := by")
        w("  decide +kernel")
        w("")
        w("/-- **E for the constructor sentences**: Γ entails each, for every H. -/")
        w("theorem cons_entailed (H : HookParams) : ∀ ad ∈ consText, Γ (cH H) ⊧ (trS ad).pat := by")
        w("  intro ad had M _ I hI")
        w("  rw [of_decide_eq_true (List.all_eq_true.mp cons_trS ad had)]")
        w("  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)")
        w("  exact tieCons_entailed (c := cH H) (a := ad.ax)")
        w("    ((tieConsB_withHooks c H ad.ax).trans (List.all_eq_true.mp cons_checked ad had)) ad.index ad.module hI")
        w("")
    # ---- idem
    if idem is not None:
        w(ens_section("/-! ## Set idempotence (61): refuted -/", "/-! ## Consistency for every H -/",
                      IDEM_DROP).replace("@I@", str(idem)))
    if lib166 is not None:
        w(ens_section("/-! ## Library sample: sentence 166", "/-! ## Symbols the text's sentences apply").replace("@I@", str(lib166)))
        w(ens_section("theorem shapesOK_c", "/-- The symbols the rule's sentence applies. -/").replace("@I@", str(lib166)))
    if gamma:
        w(GAMMA_RULES if nrules else GAMMA)
    w(f"end KCore.{ns}")
    w("")
    names = ["noRaw", "readsConfined_c", "userAxioms_eq", "coreOK"] + (["wf_defn"] if wf_ok else []) + \
        ["account", "account_sizes", "account_classes", "account_absent", "absent_closed", "lists_in_account",
         "attrs_agree", "sig_origin_but_next" if head["sigAll"] != "true" else "sig_origin", "decls_entailed",
         "consistent"] + (["text_nextless"] if head["sigAll"] != "true" else [])
    if fn_full:
        names += ["fn_shape", "fns_account", "fns_entailed", "fns_from_text", "fn_prios"]
    if nj_triv:
        names.append("nojunk_trivial_entailed")
    if nj_items:
        names.append("nojunk_items_entailed")
    if nj_kitem:
        names.append("nojunk_kitem_entailed")
    if cons_text:
        names.append("cons_entailed")
    if rules_full and nrules:
        names += ["rules_account", "rule_from_text"]
    if idem is not None:
        names.append("idem_refuted")
    if lib166 is not None:
        names += ["lib166", "lib166_at_values"]
    if gamma:
        names += ["gamma_origin", "gamma_from"]
    for n in names:
        w(f"#check @KCore.{ns}.{n}")
    for n in names:
        w(f"#print axioms KCore.{ns}.{n}")
    summary = dict(fixture=name, sentences=len(idx), mapped=len(mapped), unmapped=len(unmapped),
                   classes={c_: len(by_class[c_]) for c_ in CLASSES}, fn_full=fn_full, cons=len(cons_text),
                   nojunk=[len(nj_triv), len(nj_items), len(nj_kitem)], idem=idem, lib166=lib166, gamma=gamma,
                   uncovered=uncovered, theorems=names)
    return ns, "\n".join(L) + "\n", summary


def ens_section(start, end, drop=()):
    """The text of test/TieEns.lean from the line `start` up to the line `end`, each text of `drop`
    taken out, its sentences 61 and 166 made the placeholder @I@."""
    t = open(ENS_TIE).read()
    a = t.index("\n" + start) + 1
    b = t.index("\n" + end, a) + 1
    s = t[a:b]
    for d in drop:
        if d not in s:
            raise Refused(f"test/TieEns.lean has changed: no {d[:60]!r} in its section {start!r}")
        s = s.replace(d, "")
    return s.replace("U.ax61", "U.ax@I@").replace("U.ax166", "U.ax@I@").replace("Sentence 61", "Sentence @I@").replace(
        "sentence 166", "sentence @I@").replace("Sentence 166", "Sentence @I@")


IDEM_DROP = ("""set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

/-- No rule or clause has an open variable or a condition with a binder. -/
theorem readsConfined_c : c.readsConfined = false := by decide +kernel

""",)


GAMMA = r'''/-! ## The converse over Γ's content -/

theorem ruleItems_nil : ruleItems c = [] := by kernel_rfl

/-- The parts of Γ that are no sentence's translation: the families. -/
def Families (H : HookParams) : Premises KoreAML.Sym :=
  ΓSig (cH H) ∪ ΓCons (cH H) ∪ ΓDomains (cH H) ∪ ΓColls (cH H) ∪ ΓFallback (cH H)

/-- The function sentences as written, with definedness, and the families. -/
def Pre (H : HookParams) : Premises KoreAML.Sym :=
  (fun φ => (∃ ad ∈ fnText, (trS ad).pat = φ) ∨ ∃ x : EVar, φ = @definedness KoreAML.Sym _ x) ∪ Families H

/-- **The origin of each premise of Γ**: a function equation is the translation of a text
sentence; the text has no rule, so Γ has no rule item; everything else is one of the five parts
defined by predicates (`Families`), or definedness. -/
theorem gamma_origin (H : HookParams) : ∀ φ, Γ (cH H) φ →
    (∃ ad ∈ fnText, (trS ad).pat = φ) ∨ Families H φ ∨ (∃ x : EVar, φ = @definedness KoreAML.Sym _ x) := by
  intro φ h
  rcases h with ((((((h | h) | h) | h) | h) | h) | h)
  · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h)))))
  · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
  · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr h))))
  · exact Or.inr (Or.inl (Or.inl (Or.inr h)))
  · rcases h with ⟨it, hit, rfl⟩ | hx
    · rw [fnItems_withHooks] at hit
      have hmem : it.pat ∈ fnText.map (trS · |>.pat) := fn_shape ▸ List.mem_map.mpr ⟨it, hit, rfl⟩
      obtain ⟨ad, had, he⟩ := List.mem_map.mp hmem
      exact Or.inl ⟨ad, had, he⟩
    · exact Or.inr (Or.inr hx)
  · rcases h with ⟨it, hit, rfl⟩ | hx
    · rw [ruleItems_withHooks, ruleItems_nil] at hit; cases hit
    · exact Or.inr (Or.inr hx)
  · exact Or.inr (Or.inl (Or.inr h))

/-- Every premise of Γ is a consequence of `Pre`. -/
theorem gamma_from (H : HookParams) : ∀ φ, Γ (cH H) φ → Pre H ⊧ φ := by
  intro φ h M _ I hI
  rcases gamma_origin H φ h with ⟨ad, had, he⟩ | hf | hx
  · exact hI _ (Or.inl (Or.inl ⟨ad, had, he⟩))
  · exact hI _ (Or.inr hf)
  · exact hI _ (Or.inl (Or.inr hx))
'''

GAMMA_RULES = r'''/-! ## The converse over Γ's content -/

/-- The parts of Γ that are no sentence's translation: the families. -/
def Families (H : HookParams) : Premises KoreAML.Sym :=
  ΓSig (cH H) ∪ ΓCons (cH H) ∪ ΓDomains (cH H) ∪ ΓColls (cH H) ∪ ΓFallback (cH H)

/-- The function sentences as written, with definedness, Γ's rule items (each a consequence of its
text sentence, `rule_from_text`), and the families. -/
def Pre (H : HookParams) : Premises KoreAML.Sym :=
  (fun φ => (∃ ad ∈ fnText, (trS ad).pat = φ) ∨ ∃ x : EVar, φ = @definedness KoreAML.Sym _ x) ∪ ΓRules (cH H) ∪ Families H

/-- **The origin of each premise of Γ**: a function equation is the translation of a text
sentence; a rule item is a consequence of a text sentence of `ruleText`; everything else is one of
the five parts defined by predicates (`Families`), or definedness. -/
theorem gamma_origin (H : HookParams) : ∀ φ, Γ (cH H) φ →
    (∃ ad ∈ fnText, (trS ad).pat = φ) ∨ (ΓRules (cH H) φ ∧ ∃ ad ∈ ruleText, itemsPremises [trS ad] ⊧ φ) ∨
      Families H φ ∨ (∃ x : EVar, φ = @definedness KoreAML.Sym _ x) := by
  intro φ h
  rcases h with ((((((h | h) | h) | h) | h) | h) | h)
  · exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))
  · exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr h)))))
  · exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr h))))
  · rcases h with ⟨it, hit, rfl⟩ | hx
    · rw [fnItems_withHooks] at hit
      have hmem : it.pat ∈ fnText.map (trS · |>.pat) := fn_shape ▸ List.mem_map.mpr ⟨it, hit, rfl⟩
      obtain ⟨ad, had, he⟩ := List.mem_map.mp hmem
      exact Or.inl ⟨ad, had, he⟩
    · exact Or.inr (Or.inr (Or.inr hx))
  · rcases h with ⟨it, hit, rfl⟩ | hx
    · exact Or.inr (Or.inl ⟨Or.inl ⟨it, hit, rfl⟩, rule_from_text H it hit⟩)
    · exact Or.inr (Or.inr (Or.inr hx))
  · exact Or.inr (Or.inr (Or.inl (Or.inr h)))

/-- Every premise of Γ is a consequence of `Pre`. -/
theorem gamma_from (H : HookParams) : ∀ φ, Γ (cH H) φ → Pre H ⊧ φ := by
  intro φ h M _ I hI
  rcases gamma_origin H φ h with ⟨ad, had, he⟩ | ⟨hr, -⟩ | hf | hx
  · exact hI _ (Or.inl (Or.inl (Or.inl ⟨ad, had, he⟩)))
  · exact hI _ (Or.inl (Or.inr hr))
  · exact hI _ (Or.inr hf)
  · exact hI _ (Or.inl (Or.inl (Or.inr hx)))
'''


def main(argv):
    if not argv or argv[0].startswith("-"):
        raise SystemExit(__doc__)
    name = argv[0]
    opt = lambda f, d: int(argv[argv.index(f) + 1]) if f in argv else d
    chunks = (opt("--sig-chunk-first", 34), opt("--sig-chunk", 13), opt("--decl-chunk", 25))
    if not os.path.isdir(os.path.join(FX, name)):
        raise Refused(f"{name}: no such fixture")
    text = restored_text(name)
    text_rel = f"f2-examples/{name}.kompile.kore"
    final = os.path.join(KS, text_rel)
    tmpd = tempfile.TemporaryDirectory(prefix="tiegen-text-")
    path = os.path.join(tmpd.name, f"{name}.kompile.kore")
    open(path, "w").write(text)
    wf_ok, failing = account_check(name, path)
    head, sents = probe(name, path, user_axioms(text)[0])
    if head.get("rawParams") != "0":
        raise Refused(f"{name}: {head.get('rawParams')} parameter(s) are open generators (raw)")
    if head.get("readsConfined") != "false":
        raise Refused(f"{name}: the definition reads a confined sort (readsConfined = true): its theory is Γc")
    call_order = obligations(name, path)
    if head.get("attrsAgree") != "true":
        raise Refused(f"{name}: the attributes do not agree with the definition (attrsAgree false)")
    if head.get("wf") != ("true" if wf_ok else "false"):
        raise Refused(f"{name}: the probe's wf and the account's differ")
    next_only = head.get("sigBadNext") == "true" and head.get("textNext") == "false"
    if (head.get("sigAll") != "true" and not next_only) or head.get("declAll") != "true":
        raise Refused(f"{name}: an item of the signature has no origin (items {head.get('sigBad')}) or a declaration's item is not Γ's")
    um, cls, mapped, unmapped = classify(name, text, sents)
    ns, lean, summary = generate(name, text_rel, um, cls, mapped, unmapped, sents, head, wf_ok, failing,
                                 call_order, chunks)
    if not os.path.exists(final) or open(final).read() != text:
        open(final, "w").write(text)
    out = os.path.join(KS, "test", ns + ".lean")
    open(out, "w").write(lean)
    summary["file"] = os.path.relpath(out, KS)
    print(json.dumps(summary, indent=1) if "--print" in argv else
          f"tiegen: {summary['file']}: {summary['sentences']} sentences ({summary['mapped']} as ens's, "
          f"{summary['unmapped']} unmapped), {len(summary['uncovered'])} uncovered")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main(sys.argv[1:]))
    except Refused as e:
        print(f"tiegen: refused: {e}", file=sys.stderr)
        sys.exit(1)
