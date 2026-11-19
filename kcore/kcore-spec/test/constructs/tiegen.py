#!/usr/bin/env python3
"""tiegen.py: the tie (C14) of a construct fixture's kompiled text, written as a Lean test.

Usage (from anywhere; the library and `kcore` built first):
  python3 -I test/constructs/tiegen.py FIXTURE [--sig-chunk N] [--decl-chunk N] [--chunk N]
                                               [--hand consistency=FILE] [--at-values N,...] [--cons-head] [--wf-parts]
                                               [--out DIR] [--print]
  (the probe, a run of the Lean definitions on the text, is stopped after $TIEGEN_PROBE_TIMEOUT seconds, 900 by default)
  python3 -I test/constructs/tiegen.py --self-test   (the law search below, on three fixtures)

For FIXTURE (a directory of test/constructs/fixtures with a kompiled text), it writes
  f2-examples/FIXTURE.kompile.kore   the kompiled text kompile.txt records (from the cache kfix.py
                                     keeps), K's builtin directory restored for BUILTIN/ and the
                                     fixture's directory, relative to kcore-spec's parent, for FIXTURE/;
  test/Tie<Fixture>.lean             the tie on that text, on the literals `kore` and `defn`, for
                                     every interpretation H.
With --out DIR it writes the test into DIR and leaves f2-examples alone. --chunk N cuts the
decisions over the whole user module (`account_absent`) and over the constructor sentences
(`cons_checked`, `cons_trS`) into ranges of N, each its own kernel decision (default: one each).
--cons-head decides the constructor sentences with `tchConsB` (KcoreSpec/TieConsHd.lean), in the
probe and in the test (`cons_checked_hd`, and `cons_checked` from it by `tchConsB_all`), in place of
`tieConsB`, whose search over pairs of generators and scans of `consItemsK` are quadratic in a sort's
generators: for a text with a sort of many generators (KItem over the cell sorts of a deep
configuration). It accepts only what `tieConsB` accepts (`tchConsB_sound`); a sentence `tieConsB`
accepts and it does not is left to the classes the probe gives otherwise.
--wf-parts states `wf_defn` from its conjuncts (`wf_of_parts_all`), each a decision of its own, the
names' distinctness by their codes (`KoreAML.Distinct`): `namesOK`'s `nodup` over the emitted
declarations compares every pair of names, which for a text of many symbols exceeds a 12 GiB scope.
--hand consistency=FILE puts FILE in place of the consistency section, for a text that owes an
agreement, a clause's match independence, or a rule's or clause's condition (`owed_rules`,
`owed_clauses`): FILE proves the owed facts and states `consistent` for every H, with `facts` for an
agreement, and `owed_rules`, `owed_clauses` and `openDecidedH` (`OpenDecided` for every H) otherwise.
--at-values N,... names the user lemmas (by `AxiomDecl.index`) that are of the class `user lemma at
values` in place of `user lemma`; an index that is no user lemma of the text is refused.

It refuses, with the reason, a fixture without a kompiled text, a text whose `kcore account` is not
the fixture's account.txt, a text the reader refuses, a text whose obligations `kcore gen --core`
states in a form not in OBL_FORMS, or which owes termination, totality or a held-named function's
fact, or, without --hand consistency, a match independence or a rule's or clause's condition;
a text whose `attrsAgree` fails; a law of the reader or a law item of Γ that is not one sentence as
written; a text with a law of a function that the probe refutes at values (Function laws, below).

Function laws. A law of a function (`Definition.laws`) is owed as `FnLaws`: `LawAt` for each law,
under every well-sorted substitution its two sides have the same `EvalTerm` results. Where it fails
at every H the tie, which takes it as a hypothesis, states nothing, and the text is not tied: by the
owed-sentence rule (test/constructs/rows-header.toml, items 3 and 4) a fixture of it is a test of
the check (DONE-0 C8). That it fails at every H is not decidable from the text in general: `LawAt`
quantifies over all values of the law's variables (infinitely many of Int), so no finite evaluation
settles that it holds, and where it fails one valuation witnesses it, which a search can find but
whose absence it cannot show. What tiegen decides is such a witness. The probe evaluates both sides
with `Cert.evalTC` (fuel 4000) at the valuations of the law's variables drawn from 0, 1, 2, 3, -1,
-2, true, false and the nullary constructors of their sorts (4096 at most). A valuation at which both
sides have values (`some (some v)`) that differ (`Exec.same`) refutes the law at every H: `evalTC`
has no result where it would consult the interpretation, so with no open generator its result is
the one at every H (`Cert.evalTC_withHooks`) and the executable evaluation's (`Cert.evalTC_sound`),
hence the `EvalTerm` result (`Exec.evalT_sound`, from `ok`, `srReady`, `matchReady`, which no H
changes, and `lawSorted`); and `EvalTerm` is functional where `CoherentAll` holds
(`Det.coherentAll_of_nil`: `clausesFixed`, no agreement owed), so `LawAt` would give the right side
the left side's value. The search runs only where those conditions hold. Only values on both sides
count: where a side has no result `LawAt` can fail while the sentence holds (`Parse.fnLawEntry`), so
that is no witness. tiegen refuses such a text, naming the witness (test/FnLawFixtures.lean's
`Bad.not_lawAt` is the kernel's refutation for e2-fn-assoc-bad). A law the search does not refute
(no witness among those valuations, a side without a value or reading the interpretation there, or
the conditions not met) is not shown to hold: tiegen writes the tie with `FnLaws` owed (the
summary's `law_search`), and before the tie counts as a row's evidence the lane checks the law:
proves `FnLaws` at some H (as `FnLawFixtures.Assoc.fnLaws`), or refutes it at every H, which makes
the fixture a C8 test. `--self-test` runs the search on e2-fn-assoc-bad (refused, at var 2 = 1),
e2-fn-assoc and e2-fn-assoc-rest (both not refuted).

What it states where the text:
- owes an agreement (`agree_named` not empty): `facts` and `consistent` take it as a hypothesis
  (`AgreeOwed`), the proof owed (`owed` in the summary), unless `--hand consistency` gives it;
- has an open generator (`raw`; one at most): `params_raw`, `facts` and `consistent` for every H
  satisfying `OpenLaws`, at `lawHooks c H` for every H, for every H where it has no law
  (`openLaws_any`); its law sentence is Γ's law item (`openlaw_*`, the class `open generator law`),
  its functional sentence no item of Γ (`open_functional_not_item`, the class `open generator
  functional`);
- states a law of a function (`Definition.laws`): `law_text` (the sentence as written is `lawPattern`),
  `law_not_item`, `law_account` (the class `function law`);
- has a lemma applying a parameter symbol no hook implements (`isParamLemma`, the class `parameter
  lemma`, direction hypothesis): `paramlemma_account`, and `ParamLemmaWitnessAtValues`, one H at
  which `FnObligations` hold and every parameter lemma holds at values (`EntailsAtValues`), stated
  and owed (`owed` in the summary); and
  `paramlemma_heads`: every `simplification` equation of the user module whose left side's head is
  a parameter symbol without `impl` is in that class;
- has a lemma of a user's file that applies no such parameter symbol (the reader's class inert
  simplification, a `Source` outside K's installation): the class `user lemma` (direction entailed),
  or `user lemma at values` (direction atValues) for the indices `--at-values` names;
  `userlemma_account`, and the Props `UserLemmaEntailed` (Γ entails each for every H) and
  `UserLemmaAtValues` (`EntailsAtValues` of each for every H), stated and owed (`owed` in the
  summary). tiegen cannot decide which of the two holds: the default is the stronger class, whose
  proof fails where the lemma holds at values only, and the author then names the index. A user's
  equation of a symbol whose value the registry gives (`Parse.regLemmaEqn`, no `simplification`
  needed: the attribute does not change what an equation states) is out of Γ as well and rests on
  that symbol's graph, which Γ states at values: the class `user lemma at values` without
  `--at-values` (a parameter lemma where it applies a parameter symbol without `impl`);
- has a parameter symbol no hook implements (the H form): `total_named` and `obl_nil` at `[]`, which
  holds where no `[total]` function owes a parameter's totality; where one does, at
  `defn.totalParams` (the `[total]` functions are total under every H total on the parameters the
  text declares total), and `fnHypH` and `consistent` take `ParamsTotal c defn.totalParams H`, which
  one H meets (`paramsTotal_witness`, `consistent_witness`: `constH` at a value exhibited of the
  parameters' result sort); refused where that list is not empty, no one exhibited value is of every
  such parameter's result sort, or an open generator, agreement, match independence or condition is
  owed beside it;
- is not plain (`FnFacts`): `owed_rules`, `owed_clauses`, `openDecidedH`;
- reads a confined sort: `readsConfined_c` true, the theory `Γc`, the entailments
  over Γ restated over `Γc` (`entails_c`, the `_c` forms), `gamma_origin_c` (Bool holding only its
  literals, `Γcl` is `boolClosed`; otherwise refused);
- has `[owise]` equations whose items are their sentences up to a renaming of element variables:
  `fn_align` with test/NonExecOwiseTie.lean's `alphaB` section, `fn_shape_but_owise`,
  `owise_not_literal`, the converse up to the renaming;
- has one function equation whose item is not its sentence because Γ holds it with the premise that
  the clauses of a smaller priority that are not `aside` do not apply (`prioEquation`; the text
  neither confined nor with an open generator), every other item its sentence's translation up to a
  renaming of a free variable (`TiePair.sameB`): `fnText` by head symbol and priority
  (`TiePair.fnTextOf`), `fns_account` over the function-equation and priority-equation classes,
  `w_text` (the item without that premise is the sentence, `TiePair.minusNeg`), `w_differs`, `w1`
  (W1: the sentence entails the item), `shape`, `fns_entailed`, `fns_from_text`, `fn_prios`, and
  the converse over Γ's content `gamma_from` (`TiePair.Pre`). Two or more such items are left
  `uncovered`;
- has function items of Γ that no user sentence is and each one sentence of the text's prelude
  modules is, as written (KSEQ's `append`, which Γ holds where a rule or an equation applies it),
  every other item one user sentence's: `fnText` lists those sentences among the user ones (literals
  of the prelude module's axioms, `user_axioms Prelude<Module>`, which `prelude<Module>_eq` states
  are the text's), `fn_shape` as for user sentences only, and `fns_account`: `fnText`'s user-module
  sentences are the function-equation class, and its others those prelude sentences;
- has the no-junk sentence of a sort with generators other than KItem that is not Γ's item as
  written: the item over its generators in the text's order, a permutation of `Semantics.gens`
  (`<sort>TextGens`), `nojunk_<sort>_entailed` (for an open generator's sort also that it is open);
  the probe tries every permutation of a sort of at most 5 generators, and for a larger sort the
  one order the sentence's disjuncts apply the generators in (each disjunct's symbol, or `inj` from
  its sort), taken where the item over that order is the sentence;
- has the `functional` sentence of a parameter symbol no registry hook implements that the text
  declares total (`isParamFunctional`, the class `parameter functional`, direction hypothesis):
  `total_params` (`Definition.totalParams`), `paramfunctional_account`, `paramfunctional_heads`; it is
  owed as `ParamsTotal`, the hypothesis on H the statements take. The functional sentence of a
  parameter without `impl` the text does not declare total is refused.

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
  every premise of Γ has its origin here;
- the idempotence sentence of each other set collection (a definition's own, hooked to SET.concat):
  `own_idem_refuted_<i>` from `Faithful.setColl_idem_refuted_text`, its shape and the collection's
  key value one kernel decision (`own_idem_ok_<i>`).

The classes. A sentence whose text equals one of f2-examples/ens.kompile.kore's user module (up to
`Location`, `Source` and `UNIQUE'Unds'ID` attributes and whitespace) takes that sentence's class in
test/TieEns.lean's account. Any other sentence (`unmapped` in the test) takes its class from what a
probe evaluates of it (a run of the Lean definitions on the text: the heads it applies, each a symbol
with its sort arguments (`appHeadsOf`), against Γ's (`gammaHasHead`),
its place among Γ's function items, `tieConsB`, the constructor items; a symbol the registry interprets
is a registry hook or a parameter symbol a registry hook implements, `MtCellMap:in_keys` with
`MAP.in_keys`) and from its form (kompile's
`// functional`, `// subsort`, `// no confusion` and `// no junk` comments, the `assoc`, `unit`, `idem`,
`priority` and `owise` attributes, set variables, a builtin `Source`); a sentence that neither gives a
class is refused by name. A mapped sentence whose probe class differs from ens's is refused too.
Whether a sentence applies a head Γ lacks is a fact of the text's Γ, not of ens's: a sentence equal
to one of ens's that is in the no-direction class in one of the two texts and not in the other (a
projection that no read sentence of ens applies and a read sentence here does) is not mapped; it
takes its class from the probe and its form.
A sentence of a class with a theorem in test/TieEns.lean that no theorem here holds of is listed in
`uncovered`, with its class, and so is each user lemma: the part of the tie that is left to write by
hand.

What the kernel checks of the classes: that the lists partition the user module (`account`), that
the no-direction class is exactly the sentences applying a head Γ lacks (`account_absent`), and,
by each class theorem, that its list (`fnText`, `ruleText`, `consText`, the no-junk lists) is what
the theorem says. It does not check the other labels: which of the classes without a theorem here
(function functional, hooked functional, collection law, library, set-variable lemma, user lemma,
user lemma at values) a sentence is in, and which of the four constructor classes a sentence of
`consText` is in, rest on ens's account (for a mapped sentence) or on the form read above (for an
unmapped one).
"""
import hashlib, json, os, re, subprocess, sys, tempfile, textwrap, tomllib

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
           "open generator law", "open generator functional", "parameter functional", "parameter lemma",
           "user lemma", "user lemma at values", "no direction"]
# the classes test/TieEns.lean states a theorem of, sentence by sentence
THEOREM_CLASSES = {"function equation", "rewrite rule", "priority equation", "constructor functional",
                   "subsort", "injectivity", "distinctness", "no junk", "set idempotence"}
CONS_CLASSES = ["constructor functional", "subsort", "injectivity", "distinctness"]
# The classes of the sentences the reader reads as laws or Γ holds for an open generator: a law of
# a function (`Definition.laws`) is no item of Γ and is owed as `FnLaws` (direction hypothesis); an
# open generator's law is Γ's law item (`lawItemsK`, direction equal); an open generator's
# functional sentence is no item of Γ and is owed at values as `OpenTotal` (direction hypothesis).
LAW_FN_CLASS = "function law"
LAW_OPEN_CLASS = "open generator law"
OPEN_FUNCTIONAL_CLASS = "open generator functional"
# The class of the `functional` sentence of a parameter symbol no registry hook interprets that the
# text declares total (`isParamFunctional`, `Definition.totalParams`): the reader reads it as that
# declaration; Γ states the parameter's graph at values from the interpretation, so the sentence holds
# at values where H gives the parameter a value at every argument list of its sorts, which the
# statements take as the hypothesis `ParamsTotal` (direction hypothesis).
PARAM_FUNCTIONAL_CLASS = "parameter functional"
# The class of a lemma the reader leaves out of Γ that applies a parameter symbol no registry hook
# interprets (`isParamLemma`): its truth depends on the interpretation, so it is owed as a hypothesis
# on H (direction hypothesis), at values: Γ states the parameter's graph at values only (`ΓDomains`),
# so a model of Γ may hold an element of an unconfined sort that is no value's, at which no item of Γ
# constrains the parameter, and the sentence at every valuation can fail there at every H. The tie of
# a text with one owes one H at which `FnObligations` hold and every one of them holds at the
# valuations sending its variables to values (`ParamLemmaWitnessAtValues`, `EntailsAtValues`), since
# a hypothesis no H satisfies would tie a text without a model.
PARAM_LEMMA_CLASS = "parameter lemma"
# The classes of a lemma of a user's file that the reader leaves out of Γ (inert simplification) and
# that applies no parameter symbol without `impl`: Γ at every H either entails it or, with it, has
# no model. `user lemma` (direction entailed): Γ entails it at every valuation; `user lemma at
# values` (direction atValues): it holds at the valuations sending its variables to values, because
# it rests on an interpreted symbol's graph, which Γ states at values. Neither has a generated
# theorem: the tie states what is owed (`UserLemmaEntailed`, `UserLemmaAtValues`), proved by hand.
USER_LEMMA_CLASS = "user lemma"
USER_LEMMA_VALUES_CLASS = "user lemma at values"
USER_LEMMA_CLASSES = (USER_LEMMA_CLASS, USER_LEMMA_VALUES_CLASS)


class Refused(Exception):
    pass


def nested(s):
    """`[[1], [2, 3]]` as a list of lists of numbers."""
    s = s.strip()
    if s in ("", "[]"):
        return []
    return [[int(x) for x in re.findall(r"\d+", g)] for g in re.findall(r"\[([^\[\]]*)\]", s[1:-1])]


# names a generated file defines or reads, which a name made from the text must not take
RESERVED = {"c", "cH", "kore", "defn", "U", "trS", "fn", "f", "at", "by", "do", "fun", "let", "in", "if", "then",
            "else", "have", "show", "from", "end", "def", "theorem", "match", "with", "open", "namespace", "where",
            "instance", "structure", "class", "import", "names", "classes", "consText", "fnText", "ruleText",
            "lawText", "lawIdx", "callOrder", "Pre", "Families", "hasSym", "declItems", "plainSorts", "plainSyms"}


def short_sym(n):
    """A symbol's name without kompile's `Lbl` prefix, where that is a plain identifier."""
    s = n[3:] if n.startswith("Lbl") else n
    return s[:1].lower() + s[1:] if re.fullmatch(r"[A-Za-z][A-Za-z0-9]*", s) else None


def ident(base, fallback, taken):
    """`base` where it is free, else `fallback` (made free); the name is then taken."""
    n = base if base and base not in taken else fallback
    while n in taken:
        n += "'"
    taken.add(n)
    return n


def law_what(idx, raws, sents):
    """What the law sentences state, by their attributes: `the associativity of `f``, …"""
    seen = {}
    for i in idx:
        f = short_sym(sents[i]["eh"]) or sents[i]["eh"]
        r = raws.get(i, "")
        k = "associativity" if "assoc{}()" in r else "idempotence" if "idem{}()" in r else "unit" if "unit{}()" in r else ""
        seen[(k, f)] = seen.get((k, f), 0) + 1
    out = []
    for (k, f), n in seen.items():
        if k in ("associativity", "idempotence"):
            out.append(f"the {k} of `{f}`")
        else:
            out.append(f"{'a' if n == 1 else numword(n)} {k + ' ' if k else ''}law{'' if n == 1 else 's'} of `{f}`")
    return ", ".join(out)


NUMWORDS = ["no", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine"]


def numword(n):
    return NUMWORDS[n] if n < len(NUMWORDS) else str(n)


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


# The forms `kcore gen --core` states the obligations in (KcoreGen.genFnHyp): without a parameter
# symbol no hook implements, `Obl : Prop := K defn.sem callOrder []`; with one, the H form
# `Obl (H : HookParams) : Prop := K (defn.sem.withHooks H) callOrder defn.totalParams`, behind
# `OpenLaws (defn.sem.withHooks H) →` where a parameter is an open generator. K is `FnObligations`
# for a plain definition and `FnFacts` otherwise (`OpenDecided` then proved from `owed_rules` and
# `owed_clauses`).
OBL_FORMS = [
    (r"FnObligations defn\.sem callOrder \[\]", "FnObligations", False),
    (r"FnFacts defn\.sem callOrder \[\]", "FnFacts", False),
    (r"FnObligations \(defn\.sem\.withHooks H\) callOrder defn\.totalParams", "FnObligations", True),
    (r"FnFacts \(defn\.sem\.withHooks H\) callOrder defn\.totalParams", "FnFacts", True),
    (r"OpenLaws \(defn\.sem\.withHooks H\) → FnFacts \(defn\.sem\.withHooks H\) callOrder defn\.totalParams",
     "FnFacts", True),
]


def named_list(src, thm):
    """The numbers of the list a `theorem THM : … =\n    [..] :=` of `kcore gen`'s FnHyp modules
    states (its entries' comments and a type ascription dropped), or None without that theorem."""
    m = re.search(rf"^theorem {thm} : .*?=\s*(\(\[\] : [^)]*\)|\[.*?\])", src, re.M | re.S)
    if not m:
        return None
    return [] if m[1].startswith("(") else [int(x) for x in re.findall(r"\d+", re.sub(r"/-.*?-/", "", m[1]))]


def obligations(name, path, hand=False):
    """What `kcore gen --core` names of the text: the obligation form, the call order, the
    functions its agreement list names, whether it names a clause's match independence (`match`) and
    whether it owes a rule's or clause's condition (`owed`). Refused: a form not in OBL_FORMS,
    termination or totality named, a held-named function (`Held`); without `hand` (a consistency
    section written by hand that proves them), a match independence named or an owed condition
    (`Owed`)."""
    with tempfile.TemporaryDirectory(prefix="tiegen-") as d:
        g = run([KCORE, "gen", path, d, "TieGenProbe", "--core"], cwd=KS)
        if g.returncode != 0:
            raise Refused(f"{name}: `kcore gen --core` fails: {(g.stdout + g.stderr).strip()[-400:]}")
        fh = open(os.path.join(d, "TieGenProbe/FnHyp.lean")).read()
        order = open(os.path.join(d, "TieGenProbe/FnHyp/Order.lean")).read()
        mods = {}
        for m in ("Term", "Total", "Agree", "Match", "Owed"):
            p = os.path.join(d, f"TieGenProbe/FnHyp/{m}.lean")
            mods[m] = open(p).read() if os.path.exists(p) else ""
    form = None
    for rx, kind, hform in OBL_FORMS:
        if re.search(rf"^abbrev Obl(?: \(H : HookParams\))? : Prop := {rx}$", fh, re.M):
            form = dict(kind=kind, hform=hform)
    if form is None:
        m = re.search(r"^abbrev Obl.*$", fh, re.M)
        raise Refused(f"{name}: the obligations are in a form tiegen does not state ({m[0] if m else 'no Obl'})")
    if re.search(r"^abbrev Held\b", fh, re.M):
        raise Refused(f"{name}: a held-named function (`kcore gen --core` states `Held`)")
    if re.search(r"^abbrev Owed\b", fh, re.M) and not hand:
        raise Refused(f"{name}: an owed condition (`kcore gen --core` states `Owed`): its proof goes in "
                      f"--hand consistency")
    lists = {k: named_list(mods[m], k) for k, m in (("term_named", "Term"), ("total_named", "Total"),
                                                   ("agree_named", "Agree"), ("match_named", "Match"))}
    if any(v is None for v in lists.values()):
        raise Refused(f"{name}: `kcore gen --core` states no list of {[k for k, v in lists.items() if v is None]}")
    others = [k for k in ("term_named", "total_named") + (() if hand else ("match_named",)) if lists[k]]
    if others:
        raise Refused(f"{name}: an owed fact other than an agreement ({', '.join(others)} not empty)"
                      + ("" if hand or others != ["match_named"] else ": its proof goes in --hand consistency"))
    form["match"] = bool(lists["match_named"])
    form["agree"] = lists["agree_named"]
    am = re.search(r"^theorem agree_named : .*?=\s*(\[.*?\])", mods["Agree"], re.M | re.S)
    form["agree_names"] = re.findall(r"\d+ /- (.*?) -/", am[1]) if am else []
    form["owed"] = form["kind"] == "FnFacts" and (named_list(mods["Owed"], "owed_rules") != [] or
                                                  named_list(mods["Owed"], "owed_clauses") != [])
    if form["owed"] and not hand:
        raise Refused(f"{name}: a rule's or clause's condition is owed (owed_rules, owed_clauses): its proof goes "
                      f"in --hand consistency")
    co = re.search(r"def callOrder : List Nat := (\[[^\]]*\])", order)
    form["call_order"] = re.sub(r"/-.*?-/", "", co[1]).replace(" ", "")
    form["order_list"] = "[" + ", ".join(re.findall(r"\d+", form["call_order"])) + "]"
    return form


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
def tgVarRelB : List (EVar × EVar) → EVar → EVar → Bool
  | [], x, y => decide (x = y)
  | (a, b) :: env, x, y => if x = a then decide (y = b) else if y = b then false else tgVarRelB env x y
def tgAlphaB {𝕊 : Type} [DecidableEq 𝕊] : List (EVar × EVar) → Pattern 𝕊 → Pattern 𝕊 → Bool
  | env, .evar x, .evar y => tgVarRelB env x y
  | _, .svar X, .svar Y => decide (X = Y)
  | _, .bottom, .bottom => true
  | _, .symbol s, .symbol t => decide (s = t)
  | env, .application p q, .application p' q' => tgAlphaB env p p' && tgAlphaB env q q'
  | env, .implication p q, .implication p' q' => tgAlphaB env p p' && tgAlphaB env q q'
  | env, .existential x p, .existential y q => tgAlphaB ((x, y) :: env) p q
  | env, .mu X p, .mu Y q => decide (X = Y) && tgAlphaB env p q
  | _, _, _ => false
def tgFreeEV {𝕊 : Type} : List EVar → Pattern 𝕊 → List EVar
  | bound, .evar x => if x ∈ bound then [] else [x]
  | _, .svar _ => []
  | _, .bottom => []
  | _, .symbol _ => []
  | bound, .application p q => tgFreeEV bound p ++ tgFreeEV bound q
  | bound, .implication p q => tgFreeEV bound p ++ tgFreeEV bound q
  | bound, .existential x p => tgFreeEV (x :: bound) p
  | bound, .mu _ p => tgFreeEV bound p
partial def tgPerms : List Nat → List (List Nat)
  | [] => [[]]
  | l => l.flatMap fun x => (tgPerms (l.erase x)).map (x :: ·)
def tgFnAxioms (c : Semantics) : List Kore.Axiom :=
  c.allFns.flatMap fun f => (fnEquationsK c f).filterMap fun
    | .axiom a => some a
    | _ => none
def tgMinusNeg (a : Kore.Axiom) : P :=
  match TiePair.negParts a.pattern with
  | some (R, _, prem, concl) =>
    let t := tableOf a.sortVars a.pattern
    conjList (((a.sortVars.map sortVarKey ++ freeOf [] a.pattern).eraseDups).map (guardOf t)) ⇒
      (tr ⟨t, []⟩ (.implies R prem concl) ≡ inhOf (trSort t R))
  | none => (trAxiom [] [] ⟨0, "kernel", a⟩).pat
def tgNjBody : Kore.Pattern → Kore.Pattern
  | .exist _ _ b => tgNjBody b
  | p => p
/-- The generator a disjunct of a no-junk sentence applies: its symbol, or `inj` from its sort. -/
def tgNjIsGen (g : KoreAML.Gen) (d : Kore.Pattern) : Bool :=
  match g, tgNjBody d with
  | .ctor k, .app h _ _ => h.ident.name == k.name
  | .inj a, .app h (s0 :: _) _ => h.ident.name == "inj" && s0 == KoreAML.srt a
  | _, _ => false
/-- The positions in `gs` of the generators the disjuncts apply, in the disjuncts' order, the closing
`\bottom` dropped; none where a disjunct applies none of them. -/
def tgNjOrder (gs : List KoreAML.Gen) : List Kore.Pattern → Option (List Nat)
  | [] => some []
  | [.bottom _] => some []
  | d :: ds => do
    let j ← (List.range gs.length).find? fun j => (gs[j]?.map (tgNjIsGen · d)).getD false
    let rest ← tgNjOrder gs ds
    pure (j :: rest)

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
  let gh := gammaHeads c
  let hasHead := fun (h : String × List Kore.KSort) => gh.any fun g => decide (g = h)
  let afs := c.allFns
  let css := c.ctorSigs
  let isFn := fun (n : String) => afs.any (c.symName ·.label == n)
  let isCtor := fun (n : String) => css.any (c.symName ·.name == n)
  let isHook := fun (n : String) => hookSigs.any (c.symName ·.name == n)
  let isImplParam := fun (n : String) => c.params.any fun k => c.symName k.sig.name == n && k.impl.isSome && !k.raw
  let kind := fun (n : String) => if isFn n then "fn" else if isCtor n then "ctor" else if isHook n || isImplParam n then "hook" else if has n then "other" else "absent"
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
  IO.println s!"H fnPrios {(afs.flatMap (fun f => f.clauses.map (·.prio)))}"
  let us := k.axiomDecls.filter (·.module == "@MOD@")
  let usP := us.map fun ad => let q := (trS ad).pat; (ad, q, (tgFreeEV [] q).eraseDups)
  let nmK := Parse.namesOf k
  let scK := match k.modules.getLast? with
    | some m => Parse.scan m.sentences
    | none => Parse.scan []
  let ixOf := fun (q : P) => (usP.filter fun (_, p, _) => p == q).map (·.1.index)
  IO.println s!"H hasParams {c.params.any (·.impl.isNone)}"
  IO.println s!"H totalParams {d.totalParams.map c.symName}"
  IO.println s!"H noImplParams {(c.params.filter fun p => p.impl.isNone && !p.raw).map (c.symName ·.sig.name)}"
  IO.println s!"H totalNil {decide (c.totalObligationsRP @ORDER@ [] = [])}"
  IO.println s!"H totalTp {decide (c.totalObligationsRP @ORDER@ d.totalParams = [])}"
  let tgTotV := ((c.params.find? fun k => d.totalParams.contains k.sig.name).bind fun k =>
    Parse.exhibit? c k.sig.result).getD default
  IO.println s!"H totalWit {ParamSchema.constTotal c d.totalParams tgTotV}"
  IO.println s!"H attrsParts {AttrsAgree.ctors k c} {AttrsAgree.fns k c} {AttrsAgree.hooks k c} {AttrsAgree.colls k c} {AttrsAgree.prios k d}"
  let lawIx := d.laws.map fun l => ixOf (lawPattern c l)
  IO.println s!"H lawIx {lawIx}"
  IO.println s!"H openLawIx {(lawItemsK c).map fun it => ixOf it.pat}"
  let lawGate := c.params.all (!·.raw) && c.ok && c.srReady && c.matchReady && c.clausesFixed &&
    c.agreeObligations.isEmpty
  let tgShow := fun (v : GroundTerm) => match v with
    | .dv _ (.int i) => toString i
    | .dv _ (.bool b) => toString b
    | .ctor f [] => c.symName f
    | v => reprStr v
  let tgCands := fun (s : Srt) =>
    ((([0, 1, 2, 3, -1, -2] : List Int).map fun i => GroundTerm.dv Srt.int (.int i)) ++
      [GroundTerm.dv Srt.bool (.bool true), GroundTerm.dv Srt.bool (.bool false)] ++
      (c.ctorSigs.filter (·.args.isEmpty)).map (fun g => GroundTerm.ctor g.name [])).filter (c.sortOf · == some s)
  for (l, j) in d.laws.zipIdx do
    let gate := lawGate && lawSorted c l
    let σs : List Subst := (l.vars.zipIdx.foldr (fun (s, i) acc =>
      (tgCands s).flatMap fun v => acc.map ((i, v) :: ·)) [[]]).take 4096
    let wit : Option (Subst × GroundTerm × GroundTerm) := if !gate then none else σs.findSome? fun σ =>
      if !Exec.wellSorted c l.vars σ then none else
      match Cert.evalTC c 4000 σ l.lhs, Cert.evalTC c 4000 σ l.rhs with
      | some (some v), some (some w) => if Exec.same v w then none else some (σ, v, w)
      | _, _ => none
    let ws := match wit with
      | some (σ, v, w) => s!"{", ".intercalate (σ.map fun (p : Nat × GroundTerm) => s!"var {p.1} = {tgShow p.2}")}\t{tgShow v}\t{tgShow w}"
      | none => "none"
    IO.println s!"L {j}\t{gate}\t{σs.length}\t{ws}"
  IO.println s!"H litBool {c.litSort Srt.bool}"
  IO.println s!"H owedNil {c.owedRules.isEmpty && c.owedClauses.isEmpty}"
  IO.println s!"H fnClauses {afs.map fun f => c.symName f.label ++ "=" ++ toString f.clauses.length}"
  for kp in c.params.filter (·.raw) do
    IO.println s!"P {kp.sig.name}\t{c.symName kp.sig.name}\t{kp.sig.args}\t{kp.sig.result}\t{c.sortName kp.sig.result}\t{kp.assoc}\t{kp.idem}\t{c.isOpenGen (.ctor kp.sig)}"
  for (it, j) in fis.zip (List.range fis.length) do
    let fp := (tgFreeEV [] it.pat).eraseDups
    IO.println s!"F {j}\t{(usP.filter fun (_, q, fq) => tgAlphaB (fp.zip fq) it.pat q && tgAlphaB (fq.zip fp) q it.pat).map (·.1.index)}"
  -- the sentences of the text's other modules (the prelude: KSEQ, INJ) that are a function item as written
  for ad in k.axiomDecls.filter (·.module != "@MOD@") do
    let q := (trS ad).pat
    IO.println s!"Q {ad.index}\t{ad.module}\t{((fis.zip (List.range fis.length)).filter (fun (it, _) => it.pat == q)).map (·.2)}"
  let pairText := TiePair.fnTextOf c us
  let fax := tgFnAxioms c
  for (it, j) in fis.zip (List.range fis.length) do
    match pairText[j]?, fax[j]? with
    | some ad, some a =>
      let t := (trS ad).pat
      IO.println s!"W {j}\t{ad.index}\t{TiePair.sameB it.pat t}\t{(TiePair.negParts a.pattern).isSome}\t{TiePair.sameB (tgMinusNeg a) t}\t{decide (it.pat ≠ t)}"
    | _, _ => IO.println s!"W {j}\tnone\tfalse\tfalse\tfalse\tfalse"
  IO.println s!"H pairTextLen {pairText.length}"
  let njCands := ((consSorts c).filter fun s => s != Srt.kitem && !(c.gens s).isEmpty && (c.gens s).length ≤ 5).map fun s =>
    let gs := (c.gens s).map (Gen.toK c)
    (s, (KoreAML.Cons.noJunkItem (c.sortName s) ((gensInOrder c d.pres s).map (Gen.toK c))).pat,
      (tgPerms (List.range gs.length)).map fun pm => (pm, (KoreAML.Cons.noJunkItem (c.sortName s) (pm.filterMap (gs[·]?))).pat))
  for (r, j) in c.rules.zip (List.range c.rules.length) do
    let p := prioRuleK c r
    let ok := (tgRuleParts p).isSome && decide (tableOf [] p = tableOf [] (tgDropThird p)) &&
      decide ((freeOf [] p).eraseDups = (freeOf [] (tgDropThird p)).eraseDups)
    let tgt := (trAxiom [] [] ⟨0, "kernel", ⟨[], tgDropThird p, []⟩⟩).pat
    let is := (usP.filter (fun (_, q, _) => q == tgt)).map (·.1.index)
    IO.println s!"R {j}\t{ok}\t{is}"
  for (ad, p, _) in usP do
    let absent := !(appHeadsOf ad.ax.pattern).all hasHead
    let fnJ := ((fis.zip (List.range fis.length)).filter (fun (it, _) => it.pat == p)).map (·.2)
    let cons := @CONS@ c ad.ax
    let plain := decide (p = (trAxiom [] [] ad).pat)
    let consItem := ci.any (·.pat == p)
    let triv := (k.sortDecls.filter fun sd => p == tgOrTopBot (sym (.sort sd.name))).map (·.name)
    let kitem := p == kitemPat
    let rw := AttrsAgree.isRewrite ad.ax.pattern
    let eh := (AttrsAgree.eqnHead ad.ax.pattern).getD ""
    let fh := match ad.ax.pattern with
      | .exist _ _ (.equals _ _ _ (.app h _ _)) => h.ident.name
      | _ => ""
    -- a user's equation of a symbol whose value the registry gives (`Parse.regLemmaEqn`): out of Γ,
    -- a parameter lemma where it applies a parameter symbol without `impl`, else at values
    let rl := (Parse.rawEqn? ad.ax).any (Parse.regLemmaEqn scK ·)
    let pl := isParamLemma c (Parse.classify nmK (.axiom ad.ax)) (.axiom ad.ax) || (rl && appliesNoImplParam c ad.ax.pattern)
    let simp := Parse.classify nmK (.axiom ad.ax) == .inert .simplification
    let usrc := Parse.isUserSource ad.ax.attributes
    IO.println s!"S {ad.index}\t{absent}\t{fnJ}\t{cons}\t{plain}\t{consItem}\t{triv}\t{kitem}\t{rw}\t{eh}\t{kind eh}\t{fh}\t{kind fh}\t{AttrsAgree.prioOf ad.ax.attributes}\t{pl}\t{simp}\t{usrc}\t{rl}"
    if !consItem && triv.isEmpty && !kitem then
      match njCands.find? (fun (_, o, _) => o == p) with
      | some (s, _, _) => IO.println s!"N {ad.index}\t{s}\t{c.sortName s}\torder\t[]\t{(c.gens s).length}"
      | none =>
        for (s, _, pms) in njCands do
          match pms.find? (·.2 == p) with
          | some (pm, _) => IO.println s!"N {ad.index}\t{s}\t{c.sortName s}\tperm\t{pm}\t{(c.gens s).length}"
          | none => pure ()
        -- a sort of more than 5 generators: the text's order (`gensInOrder`), or the order its
        -- disjuncts apply the generators in, taken where the item over it is the sentence
        match ad.ax.pattern with
        | .or S ds =>
          for s in (consSorts c).filter fun s => s != Srt.kitem && (c.gens s).length > 5 && srtOf c s == S do
            let gs := (c.gens s).map (Gen.toK c)
            if (KoreAML.Cons.noJunkItem (c.sortName s) ((gensInOrder c d.pres s).map (Gen.toK c))).pat == p then
              IO.println s!"N {ad.index}\t{s}\t{c.sortName s}\torder\t[]\t{gs.length}"
            else match tgNjOrder gs ds with
              | some pm =>
                if pm.length == gs.length && pm.eraseDups.length == pm.length &&
                    (KoreAML.Cons.noJunkItem (c.sortName s) (pm.filterMap (gs[·]?))).pat == p then
                  IO.println s!"N {ad.index}\t{s}\t{c.sortName s}\tperm\t{pm}\t{gs.length}"
              | none => pure ()
        | _ => pure ()
'''


def probe(name, path, um, order="[]", cons_head=False):
    with tempfile.TemporaryDirectory(prefix="tiegen-") as d:
        f = os.path.join(d, "Probe.lean")
        open(f, "w").write(PROBE.replace("@PATH@", os.path.abspath(path)).replace("@MOD@", um)
                           .replace("@ORDER@", f"({order} : List Nat)")
                           .replace("@CONS@", "tchConsB" if cons_head else "tieConsB"))
        env = dict(os.environ, LEAN_NUM_THREADS="1")
        r = run(WRAP + ["timeout", os.environ.get("TIEGEN_PROBE_TIMEOUT", "900"), "lake", "env", "lean", "-j1", f], cwd=KS, env=env)
    if r.returncode != 0:
        raise Refused(f"{name}: the probe fails: {(r.stdout + r.stderr).strip()[-600:]}")
    head, sents = {}, {}
    head["rules"], head["raw"], head["fnA"], head["nj"], head["lawRef"], head["fnW"] = [], [], {}, {}, [], {}
    head["fnQ"] = {}
    nums = lambda s: [int(x) for x in re.findall(r"\d+", s)]
    for l in r.stdout.split("\n"):
        if l.startswith("H "):
            k, _, v = l[2:].partition(" ")
            head[k] = v
        elif l.startswith("L "):
            f = l[2:].split("\t")
            head["lawRef"].append(dict(j=int(f[0]), searched=f[1] == "true", tried=int(f[2]),
                                       wit=None if f[3] == "none" else dict(sigma=f[3], lhs=f[4], rhs=f[5])))
        elif l.startswith("R "):
            f = l[2:].split("\t")
            head["rules"].append((int(f[0]), f[1] == "true", [int(x) for x in re.findall(r"\d+", f[2])]))
        elif l.startswith("P "):
            f = l[2:].split("\t")
            head["raw"].append(dict(sym=int(f[0]), name=f[1], args=nums(f[2]), res=int(f[3]), sort=f[4],
                                    assoc=f[5], idem=f[6], openGen=f[7] == "true"))
        elif l.startswith("F "):
            f = l[2:].split("\t")
            head["fnA"][int(f[0])] = nums(f[1])
        elif l.startswith("Q "):
            f = l[2:].split("\t")
            head["fnQ"][int(f[0])] = (f[1], nums(f[2]))
        elif l.startswith("W "):
            f = l[2:].split("\t")
            head["fnW"][int(f[0])] = dict(idx=None if f[1] == "none" else int(f[1]), same=f[2] == "true",
                                          narrowed=f[3] == "true", wtext=f[4] == "true", differs=f[5] == "true")
        elif l.startswith("N "):
            f = l[2:].split("\t")
            head["nj"].setdefault(int(f[0]), []).append(dict(srt=int(f[1]), sort=f[2], form=f[3], perm=nums(f[4]),
                                                             ngens=int(f[5])))
        elif l.startswith("S "):
            f = l[2:].split("\t")
            nums = lambda s: [int(x) for x in re.findall(r"\d+", s)]
            sents[int(f[0])] = dict(idx=int(f[0]), absent=f[1] == "true", fnJ=nums(f[2]), cons=f[3] == "true", plain=f[4] == "true",
                                    consItem=f[5] == "true", triv=re.findall(r"Sort[^,\]\s]+", f[6]),
                                    kitem=f[7] == "true", rw=f[8] == "true", eh=f[9], ehk=f[10], fh=f[11],
                                    fhk=f[12], prio=int(f[13]), pl=f[14] == "true",
                                    simp=f[15] == "true", usrc=f[16] == "true", rl=f[17] == "true")
    return head, sents


# ---------------------------------------------------------------------------------------------
# Classes

def form_class(s, raw, builtin, laws=(), open_laws=(), raw_names=(), at_values=(), total_params=()):
    """The class a sentence's form and its probe give, or None. `laws`: the sentences that are, as
    written, the reader's laws of functions (`lawPattern`); `open_laws`: those that are Γ's law
    items of open generators (`lawItemsK`); `raw_names`: the open generators' symbol names;
    `at_values`: the user lemmas the caller names as holding at values only; `total_params`: the
    names of the parameter symbols without `impl` that the text declares total
    (`Definition.totalParams`)."""
    # a sentence applying a head Γ lacks: no item of Γ states anything of that head and H gives it
    # no value, so no class with a direction holds it. The class is not what the text owes: where
    # eliminating the head fixes a value of a symbol of Γ (findChar's equation, domains.md 1891,
    # applying `ite{SortInt}`: the condition `Semantics.findCharEq` on H), that is owed apart.
    if s["absent"]:
        return "no direction"
    if s["idx"] in laws:
        return LAW_FN_CLASS
    if s["idx"] in open_laws:
        return LAW_OPEN_CLASS
    if "[functional{}()]" in raw and s["fh"] in raw_names and not s["fnJ"] and not s["consItem"]:
        return OPEN_FUNCTIONAL_CLASS
    if "[functional{}()]" in raw and s["fh"] in total_params and not s["fnJ"] and not s["consItem"]:
        return PARAM_FUNCTIONAL_CLASS
    if s["fnJ"]:
        return "function equation"
    if s["rw"]:
        return "rewrite rule"
    if s["pl"]:
        return PARAM_LEMMA_CLASS
    # a lemma of a user's file (the reader's inert simplification, a `Source` outside K's
    # installation), whatever its form: with a set variable it is no library lemma
    if s["simp"] and s["usrc"] and not builtin:
        return USER_LEMMA_VALUES_CLASS if s["idx"] in at_values else USER_LEMMA_CLASS
    # a user's equation of a symbol whose value the registry gives (`Parse.regLemmaEqn`), applying no
    # parameter symbol without `impl`: it rests on an interpreted symbol's graph, at values
    if s["rl"] and not builtin:
        return USER_LEMMA_VALUES_CLASS
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


def classify(name, text, sents, laws=(), open_laws=(), raw_names=(), at_values=(), total_params=(), no_impl=()):
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
        fc = form_class(sents[i], raw, builtin, laws, open_laws, raw_names, at_values, total_params)
        # the functional sentence of a parameter without `impl` that the text does not declare total
        # has no class: the reader reads such a sentence only as the declaration (`totalParams`)
        if ("[functional{}()]" in raw and sents[i]["fh"] in no_impl and sents[i]["fh"] not in total_params
                and not sents[i]["absent"]):
            raise Refused(f"{name}: sentence {i} is the functional sentence of the parameter {sents[i]['fh']}, "
                          f"which the text does not declare total (`Definition.totalParams`)")
        # whether a sentence applies a head Γ lacks is a fact of this text's Γ: a sentence equal to one
        # of ens's that is in the no-direction class in one text and not in the other takes no class
        # from ens's and is unmapped
        if pool.get(s) and (ecls[pool[s][0]] == "no direction") == sents[i]["absent"]:
            j = pool[s].pop(0)
            mapped[i] = j
            # a lemma over a parameter symbol of this text's reading without `impl` is a parameter
            # lemma whatever ens's class of the same sentence (the parameters are the text's), and a
            # lemma of a user's file is a user lemma (the `Source` is this text's), and the functional
            # sentence of a parameter this text declares total is a parameter functional
            ec = fc if fc in (PARAM_LEMMA_CLASS, PARAM_FUNCTIONAL_CLASS) or fc in USER_LEMMA_CLASSES else ecls[j]
            # where the probe decides the class (a head Γ lacks, an item of Γ), it must agree with ens's
            decided = fc if fc in ("no direction", "function equation", "rewrite rule") or (fc == "no junk" and ec == "no junk") else None
            if decided and decided != ec:
                raise Refused(f"{name}: sentence {i} is ens's {j} (class {ec}), but the probe gives {decided}")
            cls[i] = ec
        else:
            if fc is None:
                raise Refused(f"{name}: sentence {i} has no ens counterpart and neither its form nor the probe gives its class: {raw[:200]}")
            cls[i] = fc
            unmapped.append(i)
    stray = sorted(i for i in at_values if cls.get(i) != USER_LEMMA_VALUES_CLASS)
    if stray:
        raise Refused(f"{name}: --at-values names {', '.join(map(str, stray))}, no user lemma of the text "
                      f"(a sentence of a user's file that the reader classes inert simplification and that "
                      f"applies no parameter symbol without `impl`)")
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


def ax_list(nums, indent=3, pre=None):
    """The literals of the axioms `nums`: `U.axN`, or `pre[N].axN` for an axiom of a prelude module."""
    pre = pre or {}
    return "[" + wrap_nums([f"{pre.get(n, 'U')}.ax{n}" for n in nums], indent) + "]"


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


def by_ranges(prefix, lst, pred, rs, lem="tieAllE", named=False):
    """The range theorems of `{lst}.all {pred} = true` over `rs`, each its own kernel decision, and
    the term that joins them. `named`: the join names the list and the predicate at every step, so
    each step's statement is fixed before its argument is elaborated, and the predicate's binder
    has the list's member type; the join is then instantiation and the `a + n` of `tieAll_range`
    against the next range's literal start, with nothing of the list or the predicate reduced."""
    thms, chain = [], []
    for a, ln in rs:
        if ln is None:
            thms.append(f"theorem {prefix}_{a} : (({lst}).drop {a}).all {pred} = true := by decide +kernel")
        else:
            thms.append(f"theorem {prefix}_{a} : ((({lst}).drop {a}).take {ln}).all {pred} = true := by decide +kernel")
    lp = f"(l := {lst}) (p := {pred}) " if named else ""
    body = f"{lem}_whole {lp or f'(p := {pred}) '}<|\n"
    for a, ln in rs[:-1]:
        body += f"    {lem}_range {lp}(a := {a}) (n := {ln}) {prefix}_{a} <|\n"
    body += f"    {prefix}_{rs[-1][0]}"
    return "\n".join(thms), body


def generate(name, text_rel, um, cls, mapped, unmapped, sents, head, wf_ok, failing, ob, chunks, raws=None,
             hand=None, chunk=0, at_values=(), cons_head=False, wf_parts=None):
    """The Lean text of the tie. `ob`: what `obligations` read; `raws`: each sentence's text as
    written; `hand`: hand-written sections by name (`consistency`), each in place of the generated
    one; `chunk`: the length of the ranges the decisions over the whole user module are cut into
    (0: one decision each)."""
    raws = raws or {}
    hand = hand or {}
    call_order = ob["call_order"]
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
    # otherwise the items no user sentence is may each be, as written, one sentence of the text's
    # prelude modules (KSEQ's `append`, which Γ holds where a rule or an equation applies it): every
    # other item one user sentence's, each function equation of the user module one item's
    fn_pre = {}
    if not fn_full and nfn and all(len(v) == 1 for v in fn_order.values()) and \
            sorted(v[0] for v in fn_order.values()) == by_class["function equation"]:
        rest = [j for j in range(nfn) if j not in fn_order]
        pre = {j: [i for i, (_, js) in head["fnQ"].items() if j in js] for j in rest}
        if all(len(v) == 1 for v in pre.values()) and len({v[0] for v in pre.values()}) == len(rest):
            fn_order.update(pre)
            fn_full = True
            fn_pre = {v[0]: head["fnQ"][v[0]][0] for v in pre.values()}
    fn_text = [fn_order[j][0] for j in range(nfn)] if fn_full else []
    # each prelude module of such a sentence, with the name of its axioms' literals (`user_axioms`)
    pre_mods = {m: "Prelude" + re.sub(r"[^A-Za-z0-9]", "", camel(m.lower())) for m in sorted(set(fn_pre.values()))}
    fn_user = [i for i in fn_text if i not in fn_pre]
    # otherwise each item may be its sentence up to a renaming of element variables (`alphaB`): an
    # `[owise]` equation's exclusion names its own bound variable
    fn_align, fn_nonlit = False, []
    if not fn_full and nfn:
        cand = [head["fnA"].get(j, []) for j in range(nfn)]
        if all(len(v) == 1 for v in cand) and sorted(v[0] for v in cand) == by_class["function equation"]:
            txt = [v[0] for v in cand]
            nonlit = [j for j in range(nfn) if j not in sents[txt[j]]["fnJ"]]
            if nonlit and all("owise{}()" in raws.get(txt[j], "") for j in nonlit):
                fn_align, fn_text, fn_nonlit = True, txt, nonlit
    raw = head["raw"]
    law_idx = [l[0] for l in nested(head["lawIx"])]
    open_law = [l[0] for l in nested(head["openLawIx"])]
    confined = head["readsConfined"] == "true"
    # otherwise each item may be its sentence's translation up to a renaming of one free variable
    # (`TiePair.sameB`) but one, a priority equation's: Γ's item is its sentence with the premise
    # that the clauses of a smaller priority that are not `aside` do not apply (`prioEquation`), and
    # without that premise it is the sentence (`TiePair.minusNeg`), which entails it (W1)
    fn_pair, pair_text, pair_w = False, [], None
    fw = head["fnW"]
    if not fn_full and not fn_align and nfn and not confined and not raw and \
            sorted(fw) == list(range(nfn)) and int(head.get("pairTextLen", -1)) == nfn and \
            all(fw[j]["idx"] is not None for j in range(nfn)):
        txt = [fw[j]["idx"] for j in range(nfn)]
        ws = [j for j in range(nfn) if not fw[j]["same"]]
        fn_prio_list = [int(x) for x in re.findall(r"\d+", head["fnPrios"])]
        if len(ws) == 1 and fw[ws[0]]["narrowed"] and fw[ws[0]]["wtext"] and fw[ws[0]]["differs"] and \
                sorted(txt) == sorted(by_class["function equation"] + by_class["priority equation"]) and \
                len(set(txt)) == nfn and [sents[i]["prio"] for i in txt] == fn_prio_list:
            fn_pair, pair_text, pair_w = True, txt, ws[0]
    agree = ob["agree"]
    facts_kind = ob["kind"]
    tp_params = ob["hform"] and head["totalNil"] != "true"
    # where a `[total]` function applies a parameter the text declares total, its totality holds
    # under the interpretations total on those parameters (`totalObligationsRP callOrder
    # defn.totalParams`): the statements take `ParamsTotal` as the hypothesis on H, and one H meets
    # it (`constH` at a value the search exhibits of the parameters' one result sort)
    tp_held = tp_params and head.get("totalTp") == "true" and head.get("totalWit") == "true"
    parts = dict(zip(["ctors", "fns", "hooks", "colls", "prios"], head["attrsParts"].split()))
    if head["attrsAgree"] != "true":
        bad = [k for k, v in parts.items() if v != "true"]
        raise Refused(f"{name}: the attributes do not agree with the definition (attrsAgree false; failing "
                      f"{', '.join(bad)})")
    taken = set(RESERVED)
    rn = [ident(short_sym(k["name"]), f"openGen{j}", taken) for j, k in enumerate(raw)]
    sn = {}
    for k in raw:
        if k["res"] not in sn:
            sn[k["res"]] = ident(k["sort"].lower() if k["sort"].isalpha() else None,
                                 f"srt{k['res']}", taken)
    cons_text = [i for i in idx if cls[i] in CONS_CLASSES and sents[i]["cons"] and sents[i]["plain"]]
    nj = by_class["no junk"]
    nj_triv = [(i, sents[i]["triv"][0]) for i in nj if sents[i]["triv"]]
    nj_items = [i for i in nj if not sents[i]["triv"] and sents[i]["consItem"]]
    kc = head["kitemCons"].split()
    kp = head["kitemPerm"].split()
    kitem_ok = kc == ["true", "false"] and kp == ["true", "true"]
    nj_kitem = [i for i in nj if not sents[i]["triv"] and not sents[i]["consItem"] and sents[i]["kitem"] and kitem_ok]
    # the no-junk sentence of another sort with generators that is not Γ's item as written: the item
    # over its generators in the text's order (`gensInOrder`) or in a permutation of
    # `Semantics.gens`, whatever the sort (`noJunkItem_of_subset` reads the generators as a set); the
    # sort of an open generator also states that generator open
    nj_sorts = [(i, head["nj"][i][0]) for i in nj
                if not sents[i]["triv"] and not sents[i]["consItem"] and i not in nj_kitem and head["nj"].get(i)]
    nj_sort_new = {}
    for i, e in nj_sorts:
        if e["srt"] not in sn:
            sn[e["srt"]] = ident(e["sort"].lower() if e["sort"].isalpha() else None, f"srt{e['srt']}", taken)
            nj_sort_new[e["srt"]] = e["sort"]
    inv = {j: i for i, j in mapped.items()}
    idem = inv.get(61) if cls.get(inv.get(61)) == "set idempotence" else None
    # the idempotence sentences of the other set collections (the definition's own, hooked to
    # SET.concat), each `(index, concatenation symbol, variable)`; refuted by
    # `setColl_idem_refuted_text`, which decides in the kernel that the collection is a set
    # collection with a value of its key sort and that the sentence is its idempotence sentence
    own_idem = [(i,) + m for i in by_class["set idempotence"] if i != idem
                for m in [own_idem_shape(raws.get(i, ""))] if m]
    lib166 = inv.get(166) if cls.get(inv.get(166)) == "library" else None
    rule_map = [(j, ix[0]) for j, ok, ix in head["rules"] if ok and len(ix) == 1]
    rules_full = (len(rule_map) == nrules and sorted(i for _, i in rule_map) == by_class["rewrite rule"])
    rule_text = [i for _, i in rule_map] if rules_full else []
    covered = set(fn_text) | set(rule_text) | set(cons_text) | {i for i, _ in nj_triv} | set(nj_items) | set(nj_kitem)
    covered |= {i for i, _ in nj_sorts}
    if fn_pair:
        covered |= set(pair_text)
    covered |= {i for i, _, _ in own_idem}
    if idem is not None:
        covered.add(idem)
    # a user lemma has no generated theorem: it is the tie's remainder, as an uncovered sentence of a
    # class with a theorem is
    uncovered = [(i, cls[i]) for i in idx
                 if (cls[i] in THEOREM_CLASSES and i not in covered) or cls[i] in USER_LEMMA_CLASSES]
    gamma = (fn_full and rules_full) or (fn_align and nrules == 0)
    fn_any = fn_full or fn_align
    open_fun = [i for i in idx if cls[i] == OPEN_FUNCTIONAL_CLASS and sents[i]["fh"] in {k["name"] for k in raw}]
    param_lem = by_class[PARAM_LEMMA_CLASS]
    param_fun = by_class[PARAM_FUNCTIONAL_CLASS]
    total_names = re.findall(r"[^\s\[\],]+", head.get("totalParams", ""))
    user_lem, user_lem_v = by_class[USER_LEMMA_CLASS], by_class[USER_LEMMA_VALUES_CLASS]
    if tp_params and (not tp_held or raw or agree or ob["match"] or ob["owed"]):
        raise Refused(f"{name}: a `[total]` function owes the totality of a parameter the text declares total "
                      f"(`totalObligationsRP callOrder []` not empty): tiegen states `ParamsTotal` as the hypothesis "
                      f"only where the totality holds under it (`totalObligationsRP callOrder defn.totalParams` empty), "
                      f"one value exhibited is of every such parameter's result sort (`constTotal`), and no open "
                      f"generator, agreement, match independence or condition is owed")
    if len(raw) > 1:
        raise Refused(f"{name}: {len(raw)} open generators: tiegen states one")
    if raw and (agree or confined or facts_kind != "FnFacts"):
        raise Refused(f"{name}: an open generator beside an owed agreement or a confined sort: tiegen states "
                      f"neither together")
    if agree and confined:
        raise Refused(f"{name}: an owed agreement beside a confined sort: tiegen states not both")
    if confined and head["litBool"] != "true":
        raise Refused(f"{name}: the definition reads a confined sort and Bool holds other than its literals (`Γcl` empty)")
    law_fns = sorted({sents[i]["eh"] for i in law_idx})
    rawd = [(k, rn[j], sn[k["res"]]) for j, k in enumerate(raw)]
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
    cmd = name + (f" --at-values {','.join(map(str, sorted(at_values)))}" if at_values else "")
    if hand:
        w(f"  `test/constructs/tiegen.py {cmd}`, its {', '.join(sorted(hand))} section by hand; run from the package root:")
        w(f"  `lake env lean -j1 test/{ns}.lean`.")
    else:
        w(f"  `test/constructs/tiegen.py {cmd}`; run from the package root: `lake env lean -j1 test/{ns}.lean`.")
    w("")
    if confined:
        w("  The definition reads a confined sort (`readsConfined_c`, `Semantics.readsConfined`), so its")
        w("  theory is `Γc = Γ ∪ Γcl`. Each statement of layers 1 and 2 is over Γ; `Γc` holds every premise")
        w("  of Γ, so each entailment holds over `Γc` too (`entails_c`, the `_c` forms at the end)" +
          (", and every\n  premise of `Γc` is a premise of Γ or `boolClosed`, the one item of `Γcl` here, which no sentence\n"
           "  states (`gamma_origin_c`)." if gamma else "."))
        w("")
    w("  Layer 1.")
    if wf_ok:
        w("  - `wf_defn`: `wf defn = true`.")
    else:
        w(f"  - `coreOK`: `coreOK`; `wf` fails at the conjuncts {', '.join(failing)} (`wfFailing`).")
    w(f"  - The account: the class lists partition the {len(idx)} sentences of the user module {um}, in")
    w("    `tieClasses`' order (`account`, `account_sizes`, `account_classes`); the no-direction class holds")
    w("    exactly the sentences that apply a symbol Γ lacks (`account_absent`, `absent_closed`).")
    il = ", ".join(map(str, law_idx))
    rnames = " and ".join(f"`{r}`" for _, r, _ in rawd)
    if law_idx:
        w("  - `attrs_agree`: the attributes the translation does not read agree with `defn`; the law")
        w(f"    sentences ({il}) are no equations of {', '.join(f'`{x}`' for x in law_fns)} (`AttrsAgree.isLaw`), so the priorities")
        w("    compared are those of its equations.")
    elif raw:
        gens = "generator" if len(raw) == 1 else "generators"
        w(f"  - `attrs_agree`: the attributes the translation does not read agree with `defn`; the open")
        w(f"    {gens} {rnames} {'is a parameter' if len(raw) == 1 else 'are parameters'} declared without `hook` and without `function`, of which the")
        w("    text states no equation.")
    else:
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
    no_law = raw and all(k["assoc"] == "false" and k["idem"] == "false" for k in raw)
    if raw:
        srts = sorted({s for _, _, s in rawd})
        w(f"  - The definition reads no confined sort (`readsConfined_c`); its {numword(len(raw))} open generator{'s' if len(raw) > 1 else ''} {'is' if len(raw) == 1 else 'are'} {rnames}")
        w(f"    (`params_raw`), of {', '.join(k['sort'] for k in raw)}. It owes no fact")
        w("    about its functions (`term_named`, `total_named`, `agree_named`, `match_named`), so Γ with the")
        w("    step's closure has a model for every H that satisfies the open generator's laws (`facts`,")
        if no_law:
            w(f"    `consistent`), at `lawHooks c H` for every H (`lawHooks_laws`, `consistent_lawHooks`); {rnames}")
            w("    has no law, so that is every H (`openLaws_any`, `consistent_any`).")
        else:
            w("    `consistent`), at `lawHooks c H` for every H (`lawHooks_laws`, `consistent_lawHooks`).")
    elif agree:
        an = " and ".join(f"`{x}`" for x in ob["agree_names"])
        w("  - The definition reads no confined sort (`readsConfined_c`) and has no open generator (`noRaw`).")
        w(f"    It owes {'one fact' if len(agree) == 1 else numword(len(agree)) + ' facts'}, the agreement of {an} (`agree_named`): no decider shows that its")
        w("    competing clauses give one result where more than one applies (`ClausesAgree`).")
        if "consistency" in hand:
            w("    The agreement holds for every H (`agree`), so Γ with the step's closure has a model for every")
            w("    H (`facts`, `consistent`).")
        else:
            w("    Under every H where it holds (`AgreeOwed`), Γ with the step's closure has a model (`facts`,")
            w("    `consistent`): the proof of `AgreeOwed` is owed.")
    elif ob["match"] or ob["owed"]:
        th = "`Γc`" if confined else "Γ"
        owes = (["the match independence of a clause (`match_named`)"] if ob["match"] else []) + \
            (["the condition of a rule or clause (`owed_rules`, `owed_clauses`)"] if ob["owed"] else [])
        w(f"  - The definition reads {'a' if confined else 'no'} confined sort (`readsConfined_c`) and has no open generator")
        w(f"    (`noRaw`). It owes {' and '.join(owes)}.")
        w("    The consistency section, written by hand, proves what it owes for every H"
          + (" (`openDecidedH`)" if facts_kind == "FnFacts" else "") + ",")
        w(f"    so {th} with the step's closure has a model for every H (`consistent`).")
    elif tp_held:
        th = "`Γc`" if confined else "Γ"
        w(f"  - The definition reads {'a' if confined else 'no'} confined sort (`readsConfined_c`) and has no open generator (`noRaw`).")
        w("    Its `[total]` functions are total under every H total on the parameters the text declares")
        w("    total (`total_named` at `defn.totalParams`), and it owes no other fact (`term_named`,")
        w(f"    `agree_named`, `match_named`), so {th} with the step's closure has a model for every H with")
        w("    `ParamsTotal c defn.totalParams H` (`consistent`); one H has it (`paramsTotal_witness`,")
        w("    `consistent_witness`).")
    elif facts_kind == "FnFacts":
        th = "`Γc`" if confined else "Γ"
        w(f"  - The definition reads {'a' if confined else 'no'} confined sort (`readsConfined_c`), has no open generator (`noRaw`), owes")
        w("    no fact (`term_named`, `total_named`, `agree_named`, `match_named`) and no rule's or clause's")
        w(f"    condition (`owed_rules`, `owed_clauses`), so {th} with the step's closure has a model for every")
        w("    H (`consistent`).")
    else:
        w("  - The definition reads no confined sort (`readsConfined_c`), has no open generator (`noRaw`) and")
        w("    owes no fact (`term_named`, `total_named`, `agree_named`, `match_named`), so Γ with the step's")
        w("    closure has a model for every H (`consistent`).")
    w("")
    w("  Layer 2, by class (indices are the text's axiom numbers, `AxiomDecl.index`).")
    if fn_align:
        ow = f"the {numword(len(fn_nonlit))} `[owise]` equations" if len(fn_nonlit) > 1 else "the `[owise]` equation"
        w(f"  - Function equations ({len(fn_text)}): each of Γ's items is the translation of one sentence up to a renaming")
        w("    of element variables, free and bound, both ways, in the order `fnText` lists them (`fn_align`;")
        w(f"    `alphaB`, `satisfies_of_alphaB`): pattern for pattern but for {ow}")
        w("    (`fn_shape_but_owise`), whose exclusion the text writes with its own bound variable")
        w("    (`owise_not_literal`). `fns_entailed` (E), `fns_from_text` (the converse), `fn_prios` (the")
        w("    priorities the sentences state are the clauses').")
    if fn_full and fn_pre:
        pl = ", ".join(f"{i} ({fn_pre[i]})" for i in sorted(fn_pre))
        w(textwrap.fill(
            f"Function equations ({len(fn_user)}, and {numword(len(fn_pre))} sentences of the text's prelude modules, "
            f"{pl}, which no user sentence is): each of Γ's items is the translation of one sentence, in the order "
            f"`fnText` lists them (`fn_shape`); its user-module sentences are the class, the others those prelude "
            f"sentences (`fns_account`, and `{'`, `'.join(n[:1].lower() + n[1:] + '_eq' for n in pre_mods.values())}`: "
            f"they are the text's); `fns_entailed` (E), `fns_from_text` (the converse), `fn_prios` (the priorities "
            f"the sentences state are the clauses').",
            width=100, initial_indent="  - ", subsequent_indent="    ", break_on_hyphens=False, break_long_words=False))
    elif fn_full:
        w(f"  - Function equations ({len(fn_text)}): each of Γ's items is the translation of one sentence, in the")
        w("    order `fnText` lists them (`fn_shape`); `fns_entailed` (E), `fns_from_text` (the converse),")
        w("    `fn_prios` (the priorities the sentences state are the clauses').")
    if fn_pair:
        wi, wj = pair_text[pair_w], pair_w
        nfe = len(by_class["function equation"])
        w(textwrap.fill(
            f"Function equations ({nfe}) and the priority equation ({wi}, of priority {sents[wi]['prio']}), in the "
            f"order `fnText` lists them (`fns_account`): each of Γ's items but item {wj} is the translation of "
            f"one sentence (`shape`), so Γ entails it (`fns_entailed`); item {wj} is the clause of {wi} under the "
            f"negation of the clauses of a smaller priority that are not `aside`, which sentence {wi} entails "
            f"(`w1`, W1) and is without that premise (`w_text`); `fns_from_text` (the converse), `fn_prios` "
            f"(the priorities the sentences state are the clauses').",
            width=100, initial_indent="  - ", subsequent_indent="    ", break_on_hyphens=False, break_long_words=False))
    if rules_full and nrules:
        w(f"  - Rewrite rules ({nrules}): each of Γ's rule items (with the premise `⌈rhs ∧ ens⌉`) is a consequence")
        w("    of its text sentence, `ruleText` in `ruleItems`' order (`rule_from_text`, W1, every H).")
    w(f"  - Constructor sentences ({len(cons_text)}): entailed by Γ (`cons_entailed`).")
    w(f"  - No junk ({len(nj_triv)} of a sort without generators, `nojunk_trivial_entailed`; {len(nj_items)} equal to")
    w(f"    one of Γ's constructor items, `nojunk_items`; {len(nj_kitem)} KItem's with its disjuncts in the text's")
    w("    order, `nojunk_kitem_entailed`).")
    if idem is not None:
        w(f"  - Set idempotence ({idem}): Γ with it has no model (`idem_refuted`).")
    for i, f, _ in own_idem:
        w(f"  - Set idempotence of the set collection of `{f}` ({i}): Γ with it has no model")
        w(f"    (`own_idem_refuted_{i}`, from `setColl_idem_refuted_text`).")
    if lib166 is not None:
        w(f"  - Library sample, {lib166} (`I -Int 0 = I`): holds at values (`lib166`, `lib166_at_values`).")
    if gamma and fn_align:
        w("  - The converse over Γ's content: each premise is a function sentence's translation up to a")
        w("    renaming, one of the five parts Γ defines by predicates, or definedness (`gamma_origin`,")
        w("    `gamma_from`).")
    elif gamma:
        w("  - The converse over Γ's content: each premise is a function sentence's translation, one of the")
        w("    five parts Γ defines by predicates, or definedness (`gamma_origin`, `gamma_from`).")
    if fn_pair:
        w(textwrap.fill(
            f"The converse over Γ's content: each premise is a consequence of the function sentences "
            f"({pair_text[pair_w]} through W1), Γ's rule items, the five parts Γ defines by predicates, or "
            f"definedness (`gamma_from`).",
            width=100, initial_indent="  - ", subsequent_indent="    ", break_on_hyphens=False, break_long_words=False))
    owed_more = ""
    if law_idx:
        owed_more += "; function law: owed as `FnLaws` (`law_account`)"
    if open_fun:
        owed_more += "; open generator functional: owed as `OpenTotal`\n    (`open_functional_not_item`)"
    if open_law:
        owed_more += "; open generator law: Γ's law item (`openlaw_item`,\n    `openlaw_account`)"
    if param_fun:
        owed_more += ("; parameter functional: owed as `ParamsTotal`\n    (`total_params`, `paramfunctional_account`, "
                      "`paramfunctional_heads`)")
    if param_lem:
        owed_more += ("; parameter lemma: owed as a hypothesis on H, at values\n    (`paramlemma_account`, "
                      "`paramlemma_heads`,\n    `ParamLemmaWitnessAtValues`)")
    if user_lem or user_lem_v:
        owed_more += ("; user lemma: owed, by hand\n    (`userlemma_account`, `UserLemmaEntailed`, "
                      "`UserLemmaAtValues`)")
    w("  - Hooked functional, collection law, library: at values (no theorem here); function functional:")
    w(f"    owed as `FnHyp` (no theorem){owed_more}; no direction: `absent_closed`.")
    w("")
    if law_idx:
        what = law_what(law_idx, raws, sents)
        w(f"  The law sentences ({il}; {what}) are neither a function equation's item nor a constructor item of Γ")
        w("  (`law_not_item`): the reader reads each as a")
        w("  law of the function stated at values (`Definition.laws`, `law_text`: the sentence as written is the")
        w(f"  law's `lawPattern`), owed as `FnLaws`. The account holds them in the class `{LAW_FN_CLASS}`, of the")
        w("  direction `hypothesis` (Γ does not hold the sentence; it is owed).")
        w("")
    if raw or nj_sorts:
        para = []
        for i, e in nj_sorts:
            gr = [r for k, r, s in rawd if k["res"] == e["srt"]]
            para.append(f"{e['sort']}'s no junk ({i}) is entailed (`nojunk_{sn[e['srt']]}_entailed`): its item lists {e['sort']}'s generators"
                        + (f", {' and '.join(f'`{g}`' for g in gr)} among them," if gr else "")
                        + (" in the text's order." if e["form"] == "order" else " in another order than `Semantics.gens`."))
        for i in open_law:
            para.append(f"The law sentence of {rnames} ({i}) is Γ's law item as written and entailed")
            para.append(f"(`openlaw_item`, `openlaw_entailed`); the account holds it in `{LAW_OPEN_CLASS}`, of the")
            para.append("direction `equal`.")
        if open_fun:
            para.append(f"{rnames}'s functional sentence{'s' if len(open_fun) > 1 else ''} ({', '.join(map(str, open_fun))}) {'is' if len(open_fun) == 1 else 'are'} no item of")
            para.append("Γ and is owed at values as `OpenTotal` (`open_functional_not_item`); the account holds it in")
            para.append(f"`{OPEN_FUNCTIONAL_CLASS}`, of the direction `hypothesis`.")
        if para:
            w(textwrap.fill(" ".join(para), width=100, initial_indent="  ", subsequent_indent="  ",
                            break_on_hyphens=False, break_long_words=False))
            w("")
    if param_fun:
        para = [f"The parameter functional sentence{'s' if len(param_fun) > 1 else ''} ({', '.join(map(str, param_fun))}) "
                f"{'are' if len(param_fun) > 1 else 'is'} the `functional` sentence of a parameter symbol no registry hook "
                "interprets that the text declares total (`Definition.totalParams`, `total_params`), which the reader "
                "reads as that declaration. Γ states the parameter's graph at values from the interpretation "
                "(`ΓDomains`: its application to values denotes `paramVal`'s value, or nothing), so the sentence "
                "holds at values where H gives the parameter a value of its sort at every argument list of its "
                "sorts: the hypothesis on H the statements take (`ParamsTotal`). The account holds "
                f"{'them' if len(param_fun) > 1 else 'it'} in the class `{PARAM_FUNCTIONAL_CLASS}`, of the direction "
                "`hypothesis` (`paramfunctional_account`), and every such sentence of the user module is in it "
                "(`paramfunctional_heads`)."]
        w(textwrap.fill(" ".join(para), width=100, initial_indent="  ", subsequent_indent="  ",
                        break_on_hyphens=False, break_long_words=False))
        w("")
    if param_lem:
        para = [f"The parameter lemmas ({', '.join(map(str, param_lem))}) apply a parameter symbol no registry hook "
                "interprets, whose value the interpretation gives: each is owed as a hypothesis on H, at the "
                "valuations sending its variables to values (`EntailsAtValues (cH H) ad (trS ad).pat`), since Γ "
                "states the parameter's graph at values only (`ΓDomains`). The account holds them in the class "
                f"`{PARAM_LEMMA_CLASS}`, of the direction `hypothesis`. A hypothesis no H satisfies would tie a text "
                "without a model, so the tie owes one H at which the functions' obligations hold and every "
                "parameter lemma holds at values (`ParamLemmaWitnessAtValues`, stated here and proved by hand: "
                "owed). Every `simplification` equation of the user module whose left side's head is a parameter "
                "symbol without `impl` is one of them (`paramlemma_heads`)."]
        w(textwrap.fill(" ".join(para), width=100, initial_indent="  ", subsequent_indent="  ",
                        break_on_hyphens=False, break_long_words=False))
        w("")
    if user_lem or user_lem_v:
        # the class at values holds the lemmas `--at-values` names and, named by no option, the user's
        # equations of a symbol whose value the registry gives (`Parse.regLemmaEqn`)
        v_named = [i for i in user_lem_v if i in at_values]
        v_reg = [i for i in user_lem_v if i not in at_values]
        if not v_reg:
            para = [f"The user lemmas ({', '.join(map(str, user_lem + user_lem_v))}) are sentences of a user's file "
                    "that the reader leaves out of Γ as lemmas (inert simplification) and that apply no parameter "
                    "symbol without `impl`."]
        else:
            para = [f"The user lemmas ({', '.join(map(str, user_lem + user_lem_v))}) are sentences of a user's file "
                    "that the reader leaves out of Γ and that apply no parameter symbol without `impl`."]
            if user_lem or v_named:
                para.append(f"Lemmas (inert simplification): {', '.join(map(str, user_lem + v_named))}.")
            para.append("Equations whose left side is headed by a symbol whose value the registry gives "
                        f"(`Parse.regLemmaEqn`): {', '.join(map(str, v_reg))}; each rests on that symbol's graph, "
                        "which Γ states at values.")
        if user_lem:
            para.append(f"Of the class `{USER_LEMMA_CLASS}` (direction `entailed`): {', '.join(map(str, user_lem))}, "
                        "each owed as `Γ (cH H) ⊧ (trS ad).pat` for every H (`UserLemmaEntailed`).")
        if user_lem_v:
            para.append(f"Of the class `{USER_LEMMA_VALUES_CLASS}` (direction `atValues`)"
                        + (", named by `--at-values`" if not v_reg else "") + f": {', '.join(map(str, user_lem_v))}, "
                        "each owed at the valuations sending its variables to values, for every H "
                        "(`UserLemmaAtValues`).")
        para.append("Both are stated here and proved by hand: owed. A lemma that is false has no proof, and its "
                    "text is not tied.")
        w(textwrap.fill(" ".join(para), width=100, initial_indent="  ", subsequent_indent="  ",
                        break_on_hyphens=False, break_long_words=False))
        w("")
    w(f"  The sentences with no counterpart in f2-examples/ens.kompile.kore are `unmapped` ({len(unmapped)});")
    if user_lem or user_lem_v:
        w(f"  the sentences of a class with a theorem that no theorem here holds of, and the user lemmas, are")
        w(f"  `uncovered` ({len(uncovered)}).")
    else:
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
    for m, pn in pre_mods.items():
        w(f'user_axioms {pn} from "{text_rel}" module "{m}"')
    w("")
    w("noncomputable abbrev c : Semantics := defn.sem")
    w("noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H")
    w("")
    if raw:
        one = len(raw) == 1
        sorts_of = sorted({k["res"] for k in raw})
        w(f"/-- {rnames}, the text's {numword(len(raw))} open generator{'' if one else 's'} (`raw`), and "
          f"{', '.join(k['sort'] for k in raw if k['res'] in sorts_of)}, {'its sort' if one else 'their sorts'}. -/")
        for k, r, _ in rawd:
            w(f"def {r} : Sym := {k['sym']}")
        for s in sorts_of:
            w(f"def {sn[s]} : Srt := {s}")
        w("")
        conj = [f'c.symName {r} = "{k["name"]}"' for k, r, _ in rawd] + \
            [f'c.sortName {sn[s]} = "{next(k["sort"] for k in raw if k["res"] == s)}"' for s in sorts_of]
        w(f"theorem names : {' ∧ '.join(conj)} := by decide +kernel")
        w("")
        srt = lambda s: sn.get(s, str(s))
        tup = [f"({r}, [{', '.join(srt(a) for a in k['args'])}], {s}, {k['assoc']}, {k['idem']})" for k, r, s in rawd]
        if one:
            k, r, s = rawd[0]
            w(f"/-- **The definition's one open generator is `{r}`**, of {k['sort']}, `assoc` {k['assoc']} and `idem` {k['idem']}. -/")
        else:
            w("/-- **The definition's open generators**, each with its sort, `assoc` and `idem`. -/")
        w("theorem params_raw : (c.params.filter (·.raw)).map (fun k => (k.sig.name, k.sig.args, k.sig.result, k.assoc, k.idem)) =")
        w(f"    [{', '.join(tup)}] := by decide +kernel")
    else:
        w("/-- No parameter of the definition is an open generator. -/")
        w("theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel")
    w("")
    if confined:
        w("/-- The definition reads a confined sort: its theory is `Γc`. -/")
        w("theorem readsConfined_c : c.readsConfined = true := by decide +kernel")
    else:
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
    if wf_ok and wf_parts:
        w("/-! `wf defn` conjunct by conjunct (`wf_of_parts_all`), each a decision of its own; the names")
        w("declared once by their codes (`KoreAML.Distinct.codesDistinct`), sorted in as many passes as the")
        w("bits of the text's number of declarations. -/")
        w(f"theorem sorts_distinct : KoreAML.Distinct.codesDistinct {wf_parts[0]} (defn.emit.sortDecls.map (·.name)) = true := by")
        w("  decide +kernel")
        w(f"theorem syms_distinct :")
        w(f"    KoreAML.Distinct.codesDistinct {wf_parts[1]} (defn.emit.symbolDecls.map (·.name) ++ defn.emit.aliasNames) = true := by")
        w("  decide +kernel")
        w("theorem names_rest : (c.hooksApart && c.predsApart && c.idsOK) = true := by decide_cheap")
        w("theorem okAll_c : c.okAll = true := by decide_cheap")
        w("theorem cert_ok : defn.cert.ok c = true := by decide +kernel")
        w("theorem pres_ok : defn.pres.ok c = true := by decide +kernel")
        w("theorem params_ok : defn.paramsOK = true := by decide +kernel")
        w("theorem faith_ok : c.faithOK = true := by unfold Semantics.faithOK; decide_cheap")
        w("theorem overloads_ok : c.overloadsOK = true := by decide +kernel")
        w("theorem wf_defn : wf defn = true :=")
        w("  wf_of_parts_all sorts_distinct syms_distinct names_rest okAll_c cert_ok pres_ok params_ok faith_ok overloads_ok")
    elif wf_ok:
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
    if chunk:
        w("/-- The sentence is in the no-direction class exactly where it applies a head Γ lacks. -/")
        w("noncomputable def absentP (ad : AxiomDecl) : Bool :=")
        w('  (classOf "no direction").contains ad.index != (appHeadsOf ad.ax.pattern).all (gammaHasHead c)')
        w("")
        thms, body = by_ranges("absentE", "U.all", "absentP", ranges(len(idx), 0, chunk), "tieAll", True)
        w(thms)
        w("")
    w("/-- **A sentence outside the no-direction class applies only symbols Γ has**, each a head with its")
    w("sort arguments (`appHeadsOf`) among Γ's (`gammaHeads`), and each sentence of that class applies one")
    w("Γ lacks. -/")
    w("theorem account_absent : userAxioms.all (fun ad =>")
    w('    (classOf "no direction").contains ad.index != (appHeadsOf ad.ax.pattern).all (gammaHasHead c)) = true := by')
    if chunk:
        w("  rw [userAxioms_eq]; exact")
        w("    " + body.replace("\n    ", "\n      "))
    else:
        w("  rw [userAxioms_eq]; decide +kernel")
    w("")
    w("/-- **The no-direction class is closed**: every sentence outside it applies only symbols Γ has,")
    w("so no sentence with a direction applies a symbol Γ lacks. The injection `inj` is no member of")
    w("`kernelSyms` and is Γ's all the same at each subsort pair, where the constructor items state it")
    w("(`gammaHeads`). -/")
    w("theorem absent_closed :")
    w('    (userAxioms.filter (fun ad => !(classOf "no direction").contains ad.index)).all')
    w("      (fun ad => (appHeadsOf ad.ax.pattern).all (gammaHasHead c)) = true :=")
    w("  tieAbsent_of_account userAxioms _ _ account_absent")
    w("")
    w("/-- The sentences whose text is none of f2-examples/ens.kompile.kore's user module, with their class. -/")
    w("def unmapped : List (Nat × String) :=")
    w("  [" + wrap_nums([f'({i}, "{cls[i]}")' for i in unmapped], 3) + "]")
    w("")
    if user_lem or user_lem_v:
        w("/-- The sentences of a class with a theorem in the tie that no theorem of this file holds of, and")
        w("the user lemmas, of which the tie has no generated theorem: the tie's remainder on this text. -/")
    else:
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
    if law_idx:
        what = law_what(law_idx, raws, sents)
        w(f"/-- The law sentences of the text: {what}. -/")
        w(f"def lawIdx : List Nat := [{il}]")
        w("")
        w("/-- **The attributes of the text agree with `defn`** (`attrsAgree`): constructors, functions,")
        w(f"hooks, collection symbols, priorities. The law sentences (`lawIdx`) are no equations of {', '.join(f'`{x}`' for x in law_fns)}")
        w("(`AttrsAgree.isLaw`, `AttrsAgree.eqnsOf`), so its priorities are those of its equations, which")
        w("`fn_prios` pairs with its clauses. -/")
    elif raw:
        w("/-- **The attributes of the text agree with `defn`** (`attrsAgree`): constructors, functions,")
        if len(raw) == 1:
            w(f"hooks, collection symbols, priorities. The open generator {rnames} is a parameter (`raw`) that no")
        else:
            w(f"hooks, collection symbols, priorities. The open generators {rnames} are parameters (`raw`) that no")
        w("registry hook interprets, declared without `hook` and without `function`, and the text states")
        w("no equation of it (`AttrsAgree.eqnsOf`), which `AttrsAgree.hooks` admits. -/")
    else:
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
    tp = "[]"
    if raw:
        w("/-! ## Consistency for every H satisfying the open generator's laws -/")
    elif agree:
        w(f"/-! ## Consistency for every H: the agreement of {' and '.join(f'`{x}`' for x in ob['agree_names'])} -/")
    else:
        w("/-! ## Consistency for every H -/")
    w("")
    w(f"def callOrder : List Nat := {call_order}")
    w("")
    w("theorem term_named : c.rankObligations callOrder ++ c.decObligationsL = [] := by decide +kernel")
    tpo = "defn.totalParams" if tp_held else tp
    w(f"theorem total_named : c.totalObligationsRP callOrder {tpo} = [] := by decide +kernel")
    if not agree:
        w("theorem agree_named : c.agreeObligationsI = [] := by decide +kernel")
    w("theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel")
    w("")
    of_nil = ["    (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named)",
              "    ((Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named)",
              "    ((Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named)",
              "    ((Det.Semantics.matchObligationsL_withHooks _ H).trans match_named)"]
    if raw:
        w("/-- No function's fact is named: under every interpretation that satisfies the open generator's")
        w("laws, `FnFacts` holds. -/")
        w("theorem facts (H : HookParams) (hop : OpenLaws (cH H)) : FnFacts (cH H) callOrder [] :=")
        w("  FnFacts.of_nil_laws")
        w("\n".join(of_nil) + " hop")
        w("")
        w("/-- **Γ with the step's closure has a model, for every H that satisfies the open generator's laws**")
        w("(`OpenLaws`). -/")
        w("theorem consistent (H : HookParams) (hop : OpenLaws (cH H)) : Consistent (cH H) :=")
        w("  consistent_of_fnFacts (coreOKH H) (Semantics.rightHeld_withHooks_of_valued (by decide +kernel) H) (facts H hop)")
        w("")
        vals = " and ".join(f"`{r}` a value at every {'pair' if len(k['args']) == 2 else 'list'} of "
                            f"{k['sort'] if len(set(k['args'])) == 1 and k['args'][0] == k['res'] else 'argument'} values"
                            for k, r, _ in rawd)
        w(f"/-- **`lawHooks c H` satisfies the laws and gives {vals}**,")
        w("for every H; so Γ with the step's closure has a model there. -/")
        w("theorem lawHooks_laws (H : HookParams) :")
        w("    OpenLaws (c.withHooks (lawHooks c H)) ∧ OpenTotal (c.withHooks (lawHooks c H)) :=")
        w("  ⟨openLaws_lawHooks c coreOK H, openTotal_lawHooks c coreOK H⟩")
        w("")
        w("theorem consistent_lawHooks (H : HookParams) : Consistent (c.withHooks (lawHooks c H)) :=")
        w("  consistent (lawHooks c H) (lawHooks_laws H).1")
        w("")
        if no_law and len(raw) == 1:
            w(f"/-- **{rnames} has no law: `OpenLaws` holds under every interpretation.** -/")
            w("theorem openLaws_any (H : HookParams) : OpenLaws (cH H) := fun k hk hr => by")
            w("  have hk' : k ∈ c.params.filter (·.raw) := List.mem_filter.mpr ⟨hk, hr⟩")
            w("  have hm := List.mem_map_of_mem (f := fun k : ParamSig => (k.sig.name, k.sig.args, k.sig.result, k.assoc, k.idem)) hk'")
            w("  rw [params_raw, List.mem_singleton] at hm")
            w("  simp only [Prod.mk.injEq] at hm")
            w("  exact ⟨fun h => (by rw [hm.2.2.2.1] at h; cases h), fun h => (by rw [hm.2.2.2.2] at h; cases h)⟩")
            w("")
            w("/-- **Γ with the step's closure has a model, for every H.** -/")
            w("theorem consistent_any (H : HookParams) : Consistent (cH H) := consistent H (openLaws_any H)")
            w("")
    elif agree:
        al = "[" + ", ".join(map(str, agree)) + "]"
        w("/-- The functions whose agreement no decider confirms, the same under every H. -/")
        w(f"theorem agree_named : c.agreeObligationsI = {al} := by decide +kernel")
        w(f"theorem agree_namedH (H : HookParams) : (cH H).agreeObligationsI = {al} :=")
        w("  (Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named")
        w("")
        w("/-- **The owed fact**: under H, the clauses of each function `agree_named` names agree")
        w("(`ClausesAgree`). -/")
        w("def AgreeOwed (H : HookParams) : Prop :=")
        w("  ∀ g ∈ (cH H).agreeObligationsI, ∀ fn, (cH H).lookupFn g = some fn → ClausesAgree (cH H) fn")
        w("")
        w("/-- **The facts the package names hold under every H where the agreement holds** (`FnFacts` at")
        w("the package's `callOrder`). -/")
        w("theorem facts (H : HookParams) (hag : AgreeOwed H) : FnFacts (cH H) callOrder [] :=")
        w("  ⟨fun g hg => by")
        w("    rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks, term_named] at hg")
        w("    exact absurd hg List.not_mem_nil,")
        w("   fun g hg => by")
        w("    rw [Semantics.totalObligationsRP_withHooks _ H _ _, total_named] at hg")
        w("    exact absurd hg List.not_mem_nil,")
        w("   hag,")
        w("   fun p hp => by")
        w("    rw [Det.Semantics.matchObligationsL_withHooks _ H, match_named] at hp")
        w("    exact absurd hp List.not_mem_nil,")
        w("   openLaws_of_plain fun k hk => by")
        w("    simpa using List.all_eq_true.mp (by decide +kernel : c.params.all (fun k => !k.raw) = true) k hk⟩")
        w("")
        w("/-- **Γ with the step's closure has a model, for every H where the agreement holds.** -/")
        w("theorem consistent (H : HookParams) (hag : AgreeOwed H) : Consistent (cH H) :=")
        w("  consistent_of_fnFacts (coreOKH H) (Semantics.rightHeld_withHooks_of_valued (by decide +kernel) H) (facts H hag)")
        w("")
    else:
        if facts_kind == "FnFacts":
            w("theorem owed_rules : c.owedRules = ([] : List Nat) := by decide +kernel")
            w("theorem owed_clauses : c.owedClauses = [] := by decide +kernel")
            w("")
            w("/-- No rule's or clause's condition is owed, under every H: `OpenDecided`. -/")
            w("theorem openDecidedH (H : HookParams) : OpenDecided (cH H) :=")
            w("  ⟨openRules_of_owed (by rw [Semantics.owedRules_withHooks, owed_rules]; intro i hi; cases hi),")
            w("   openClauses_of_owed (by rw [Semantics.owedClauses_withHooks, owed_clauses]; intro p hp; cases hp)⟩")
            w("")
            w(f"theorem obl_nil (H : HookParams) : FnObligations (cH H) callOrder {tpo} :=")
            w("  (FnFacts.of_nil")
            w("\n".join(of_nil))
            w("    (show c.params.all (fun k => !k.raw) = true by decide +kernel)).obligations (openDecidedH H)")
        else:
            w(f"theorem obl_nil (H : HookParams) : FnObligations (cH H) callOrder {tpo} :=")
            w("  FnObligations.of_nil")
            w("\n".join(of_nil))
        w("")
        if tp_held:
            w("theorem fnHypH (H : HookParams) (hH : ParamsTotal c defn.totalParams H) : FnHyp (cH H) :=")
            w("  fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H hH (obl_nil H)")
            w("")
            w(f"/-- **{'`Γc`' if confined else 'Γ'} with the step's closure has a model, for every H total on the parameters the")
            w("text declares total** (`ParamsTotal`). -/")
            w("theorem consistent (H : HookParams) (hH : ParamsTotal c defn.totalParams H) : Consistent (cH H) :=")
            w("  consistent_of_fnHyp _ (coreOKH H) (fnHypH H hH)")
            w("")
            w("/-- A value of the result sort of the parameters the text declares total, exhibited by the")
            w("search over the definition's data (`Parse.exhibit?`). -/")
            w("noncomputable def totalWitnessV : GroundTerm :=")
            w("  ((c.params.find? fun k => defn.totalParams.contains k.sig.name).bind fun k =>")
            w("    Parse.exhibit? c k.sig.result).getD default")
            w("")
            w("/-- **The hypothesis is met**: the interpretation answering `totalWitnessV` everywhere is total on")
            w("the parameters the text declares total. -/")
            w("theorem paramsTotal_witness : ParamsTotal c defn.totalParams (ParamSchema.constH totalWitnessV) :=")
            w("  ParamSchema.paramsTotal_constH (by decide +kernel)")
            w("")
            w("theorem consistent_witness : Consistent (cH (ParamSchema.constH totalWitnessV)) :=")
            w("  consistent _ paramsTotal_witness")
            w("")
        else:
            w("theorem fnHypH (H : HookParams) : FnHyp (cH H) := fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H")
            w("  ParamsTotal.nil (obl_nil H)")
            w("")
            w(f"/-- **{'`Γc`' if confined else 'Γ'} with the step's closure has a model, for every H.** -/")
            w("theorem consistent (H : HookParams) : Consistent (cH H) := consistent_of_fnHyp _ (coreOKH H) (fnHypH H)")
            w("")
    if fn_align:
        w(alpha_block())
    w("/-! ## Γ under every interpretation reads the same equations and rules -/")
    w("")
    w("kernel_rfl fnItems_withHooks : ∀ (c : Semantics) (H : HookParams), fnItems (c.withHooks H) = fnItems c")
    w("kernel_rfl ruleItems_withHooks : ∀ (c : Semantics) (H : HookParams), ruleItems (c.withHooks H) = ruleItems c")
    w("")
    w("theorem mem_Γ_fns {c : Semantics} {φ : P} (h : ΓFns c φ) : Γ c φ := Or.inl (Or.inl (Or.inr h))")
    w("")
    if fn_align:
        w(fn_align_section(fn_text, fn_nonlit))
    if fn_full:
        w(f"/-! ## Function equations ({len(fn_user)} sentences"
          + (f", and {numword(len(fn_pre))} of the prelude" if fn_pre else "") + ") -/")
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
        w("  " + ax_list(fn_text, pre={i: pre_mods[m] for i, m in fn_pre.items()}))
        w("")
        w("set_option maxHeartbeats 1000000 in")
        w("/-- **Γ's equations are the text's sentences' translations, pattern for pattern** (one kernel")
        w("decision). -/")
        w("theorem fn_shape : (fnItems c).map (·.pat) = fnText.map (trS · |>.pat) := by")
        w("  rw [fnItems_eq, List.map_map]")
        w("  exact (by decide +kernel :")
        w('    ((fnAxioms c).map fun a => (trAxiom [] [] ⟨0, "kernel", a⟩).pat) = fnText.map (trS · |>.pat))')
        w("")
        if fn_pre:
            for m, pn in pre_mods.items():
                w(f"/-- The axioms of the prelude module {m}, in text order. -/")
                w(f'theorem {pn[:1].lower() + pn[1:]}_eq : kore.axiomDecls.filter (·.module == "{m}") = {pn}.all := by kernel_rfl')
                w("")
            w("/-- **`fnText`'s user-module sentences are the account's function-equation class**: the same")
            w("indices, each once; its other sentences are the prelude's, which no user sentence is. -/")
            w("theorem fns_account :")
            w(f'    (classOf "function equation").isPerm ((fnText.filter (·.module == "{um}")).map (·.index)) = true ∧')
            w(f'    (fnText.filter (·.module != "{um}")).map (fun ad => (ad.index, ad.module)) =')
            w("      [" + ", ".join(f'({i}, "{fn_pre[i]}")' for i in fn_text if i in fn_pre) + "] := by decide +kernel")
        else:
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
        w("set_option maxHeartbeats 1000000 in")
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
    nj_names = []
    for i, e in nj_sorts:
        sec, nn = nojunk_sort_section(i, e, sn, rawd, e["srt"] in nj_sort_new)
        w(sec)
        nj_names += nn
    # ---- cons
    if cons_text:
        w("/-! ## The constructor sentences: functional, subsort, injectivity, distinctness -/")
        w("")
        dec = "tchConsB" if cons_head else "tieConsB"
        w(f"/-- The constructor sentences `{dec}` decides, in text order. -/")
        w("noncomputable def consText : List AxiomDecl :=")
        w("  " + ax_list(cons_text))
        w("")
        checked = "cons_checked_hd" if cons_head else "cons_checked"
        if chunk and len(cons_text) > chunk:
            thms, body = by_ranges("consE", "consText", f"(fun ad => {dec} c ad.ax)", ranges(len(cons_text), 0, chunk), "tieAll", True)
            w(thms)
            w(f"theorem {checked} : consText.all (fun ad => {dec} c ad.ax) = true :=")
            w("  " + body)
        else:
            w(f"theorem {checked} : consText.all (fun ad => {dec} c ad.ax) = true := by decide +kernel")
        if cons_head:
            w("")
            w("theorem cons_checked : consText.all (fun ad => tieConsB c ad.ax) = true := tchConsB_all cons_checked_hd")
        w("")
        if chunk and len(cons_text) > chunk:
            pr = "(fun ad => decide ((trS ad).pat = (trAxiom [] [] ad).pat))"
            thms, body = by_ranges("consT", "consText", pr, ranges(len(cons_text), 0, chunk), "tieAll", True)
            w(thms)
            w(f"theorem cons_trS : consText.all {pr} = true :=")
            w("  " + body)
        else:
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
        sec = ens_section("/-! ## Set idempotence (61): refuted -/", "/-! ## Consistency for every H -/",
                          IDEM_DROP).replace("@I@", str(idem))
        if raw:
            for a, b in IDEM_RAW:
                if a not in sec:
                    raise Refused(f"test/TieEns.lean has changed: no {a[:60]!r} in its idempotence section")
                sec = sec.replace(a, b)
        w(sec)
    if own_idem:
        w(own_idem_section(own_idem))
    if lib166 is not None:
        w(ens_section("/-! ## Library sample: sentence 166", "/-! ## Symbols the text's sentences apply").replace("@I@", str(lib166)))
        w(ens_section("theorem shapesOK_c", "/-- The symbols the rule's sentence applies. -/").replace("@I@", str(lib166)))
    if law_idx:
        w(law_section(law_idx))
    if open_law:
        w(openlaw_section(open_law, rnames, need_rfl=not nj_items))
    if open_fun:
        w(open_functional_section(open_fun, rnames))
    if param_fun:
        w(param_functional_section(param_fun, total_names, len(idx), chunk))
    if param_lem:
        w(param_lemma_section(param_lem))
    if user_lem or user_lem_v:
        w(user_lemma_section(user_lem, user_lem_v))
    if fn_pair:
        wi = pair_text[pair_w]
        w(pair_section(pair_w, wi, sents[wi]["prio"], "non-executable{}()" in raws.get(wi, ""),
                       len(by_class["function equation"])))
    if gamma:
        w(GAMMA_ALIGN if fn_align else GAMMA_RULES if nrules else GAMMA)
    cnames = []
    if confined:
        sec, cnames = gamma_c_section(gamma, fn_align, nrules, fn_any, nj_triv, nj_items, nj_kitem, cons_text, idem,
                                      own_idem)
        w(sec)
    w(f"end KCore.{ns}")
    w("")
    names = ["params_raw" if raw else "noRaw", "readsConfined_c", "userAxioms_eq", "coreOK"] + (["wf_defn"] if wf_ok else []) + \
        ["account", "account_sizes", "account_classes", "account_absent", "absent_closed", "lists_in_account"] + \
        ["attrs_agree"] + \
        ["sig_origin_but_next" if head["sigAll"] != "true" else "sig_origin", "decls_entailed",
         "consistent"] + (["text_nextless"] if head["sigAll"] != "true" else [])
    if fn_full:
        names += [n[:1].lower() + n[1:] + "_eq" for n in pre_mods.values()]
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
    names += [f"own_idem_refuted_{i}" for i, _, _ in own_idem]
    if lib166 is not None:
        names += ["lib166", "lib166_at_values"]
    if gamma and not fn_align:
        names += ["gamma_origin", "gamma_from"]
    after = []
    if agree:
        after += ["agree_named"] + (["agree"] if "consistency" in hand else []) + ["facts"]
    if tp_held:
        after += ["total_named", "paramsTotal_witness", "consistent_witness"]
    if fn_align:
        after += ["fn_shape_but_owise", "owise_not_literal", "fn_align", "fns_account", "fns_entailed",
                  "fns_from_text", "fn_prios"] + (["gamma_origin", "gamma_from"] if gamma else [])
    k = names.index("consistent") + 1
    names[k:k] = after
    if law_idx:
        names += ["law_indices", "law_text", "law_not_item", "law_account"]
    if raw:
        names += ["names", "facts", "lawHooks_laws", "consistent_lawHooks"] + (["openLaws_any", "consistent_any"] if no_law and len(raw) == 1 else [])
    names += nj_names
    if open_law:
        names += ["openlaw_item", "openlaw_cons", "openlaw_entailed", "openlaw_account"]
    if open_fun:
        names.append("open_functional_not_item")
    if param_fun:
        names += ["total_params", "paramfunctional_account", "paramfunctional_heads"]
    if param_lem:
        names += ["paramlemma_account", "paramlemma_heads", "ParamLemmaWitnessAtValues"]
    if user_lem or user_lem_v:
        names += ["userlemma_account", "UserLemmaEntailed", "UserLemmaAtValues"]
    if facts_kind == "FnFacts" and not agree and not raw:
        names += ["owed_rules", "owed_clauses", "openDecidedH"]
    names += cnames
    pair_names = ["fns_account", "aW_narrowed", "w_text", "w_differs", "w1", "shape", "fns_entailed",
                  "fns_from_text", "fn_prios", "gamma_from"] if fn_pair else []
    for block in (names, pair_names):
        for n in block:
            w(f"#check @KCore.{ns}.{n}")
        for n in block:
            w(f"#print axioms KCore.{ns}.{n}")
    names = names + pair_names
    lean = "\n".join(L) + "\n"
    for sec, text in hand.items():
        start = HAND_SECTIONS[sec]
        a = lean.index("\n" + start) + 1
        b = lean.index("\n/-! ## ", a) + 1
        lean = lean[:a] + text.rstrip("\n") + "\n\n" + lean[b:]
    owed = ([f"the agreement of {', '.join(ob['agree_names'])} (AgreeOwed)"] if agree and "consistency" not in hand else [])
    if param_lem:
        owed.append(f"one H at which FnObligations hold and the parameter lemmas {', '.join(map(str, param_lem))} "
                    f"hold at values (ParamLemmaWitnessAtValues)")
    if user_lem:
        owed.append(f"Γ entails the user lemmas {', '.join(map(str, user_lem))} for every H (UserLemmaEntailed)")
    if user_lem_v:
        owed.append(f"the user lemmas {', '.join(map(str, user_lem_v))} hold at values for every H (UserLemmaAtValues)")
    summary = dict(fixture=name, sentences=len(idx), mapped=len(mapped), unmapped=len(unmapped),
                   classes={c_: len(by_class[c_]) for c_ in CLASSES}, fn_full=fn_full, fn_prelude=sorted(fn_pre), fn_align=fn_align,
                   fn_pair=fn_pair,
                   cons=len(cons_text), nojunk=[len(nj_triv), len(nj_items), len(nj_kitem), len(nj_sorts)],
                   idem=idem, own_idem=[i for i, _, _ in own_idem], lib166=lib166, gamma=gamma, laws=law_idx, open_generators=[k["name"] for k in raw],
                   confined=confined, uncovered=uncovered, owed=owed, theorems=names,
                   law_search=[dict(law=law_idx[r["j"]], searched=r["searched"], valuations=r["tried"], refuted=False)
                               for r in head["lawRef"]])
    return ns, lean, summary


# the sections a hand-written text may take the place of (`--hand NAME=FILE`), by their first line
HAND_SECTIONS = {"consistency": "/-! ## Consistency for every H"}

NEX_TIE = os.path.join(KS, "test/NonExecOwiseTie.lean")


def pair_section(j, i, prio, nonexec, nfe):
    """The function equations where Γ's item `j` is sentence `i` with the premise that the clauses of
    a smaller priority that are not `aside` do not apply (W1), and every other item is its sentence's
    translation (`TiePair.shapeB`), with the converse over Γ's content (`TiePair.gamma_from`)."""
    nx = ", the `non-executable` one" if nonexec else ""
    intro = textwrap.fill(
        f"`fnItems`'s item {j} is the equation of the clause of priority {prio}{nx}: Γ holds it under the "
        f"negation of the clauses of a smaller priority that are not `aside` (`prioEquation`, "
        f"`competingEquation`), a premise the sentence does not state. Sentence {i} entails it (`w1`, the "
        f"direction of the class priority equation) and is the item without that premise (`w_text`); it "
        f"is not the item (`w_differs`). Every other item is the translation of its function sentence "
        f"(`shape`). -/", width=100, break_on_hyphens=False, break_long_words=False)
    return f'''/-! ## Function equations ({nfe} sentences) and the priority equation (sentence {i})

{intro}

/-- The text sentences of Γ's equations, in `fnItems`'s order: found by head symbol and priority
(`TiePair.fnTextOf`); `shape` is what makes them the equations' sentences. -/
noncomputable def fnText : List AxiomDecl := TiePair.fnTextOf c U.all

/-- **`fnText` is the account's function-equation and priority-equation classes**: the same
indices, each once. -/
theorem fns_account :
    (classOf "function equation" ++ classOf "priority equation").isPerm (fnText.map (·.index)) = true := by
  decide +kernel

/-- Γ's axiom of the narrowed equation. -/
noncomputable def aW : Kore.Axiom := ((TiePair.fnAxioms c)[{j}]?).getD ⟨[], .top KoreAML.R, []⟩

theorem aW_at : (TiePair.fnAxioms c)[{j}]? = some aW := by decide +kernel

/-- Γ's item of it. -/
noncomputable def gW : P := (trAxiom [] [] ⟨0, "kernel", aW⟩).pat

theorem gW_at : (TiePair.gammaPats c)[{j}]? = some gW := TiePair.gammaPats_at aW_at

kernel_rfl fnText_W : fnText[{j}]? = some U.ax{i}

/-- Its premise has the negated conjunct. -/
theorem aW_narrowed : (TiePair.negParts aW.pattern).isSome = true := by decide +kernel

/-- **Γ's item without the priority premise is the text's sentence {i}** (`TiePair.minusNeg`, up to
the indices of its variables: `TiePair.sameB`; kernel). -/
theorem w_text : TiePair.sameB (TiePair.minusNeg aW) (trS U.ax{i}).pat = true := by decide +kernel

/-- **Γ's item is not the sentence.** -/
theorem w_differs : gW ≠ (trS U.ax{i}).pat := by decide +kernel

/-- **W1**: the text's sentence {i} entails Γ's item, in every model of definedness. -/
theorem w1 : TiePair.Texts [(trS U.ax{i}).pat] ⊧ gW :=
  fun {{M}} _ {{I}} hI => TiePair.item_of_sentence (TiePair.defOK_texts hI) w_text
    (hI _ (Or.inl (List.mem_singleton_self _)))

/-- The premise set's equations, in `fnItems`'s order: each text sentence's translation, and for
sentence {i} Γ's item. -/
noncomputable def textPats : List P := (fnText.map (trS · |>.pat)).set {j} gW

/-- **Each of Γ's equations but item {j} is the translation of its text sentence** (kernel); item
{j} is `gW`. -/
theorem shape : TiePair.shapeB (TiePair.gammaPats c) textPats = true := by decide +kernel

theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) textPats = true := by
  rw [TiePair.gammaPats_withHooks]; exact shape

/-- **E for the function equations**: Γ entails each sentence of `fnText` but sentence {i}, for
every H. -/
theorem fns_entailed (H : HookParams) : ∀ (j : Nat) (ad : AxiomDecl), fnText[j]? = some ad → j ≠ {j} →
    Γ (cH H) ⊧ (trS ad).pat := by
  intro j ad hj hne
  refine TiePair.entailed (shapeH H) _ (List.mem_of_getElem? (i := j) ?_)
  unfold textPats
  rw [List.getElem?_set_ne (Ne.symm hne), List.getElem?_map, hj]; rfl

/-- **The converse for `fnItems`**: each item is a consequence of a text sentence, the j-th of
`fnText`; item {j} by W1, the others by their translation. -/
theorem fns_from_text (H : HookParams) :
    ∀ (j : Nat) (it : Item), (fnItems (cH H))[j]? = some it →
      ∃ ad, fnText[j]? = some ad ∧ (TiePair.Texts [(trS ad).pat] ⊧ it.pat) := by
  intro j it hj
  by_cases hJ : j = {j}
  · subst hJ
    refine ⟨U.ax{i}, fnText_W, ?_⟩
    have hg : (TiePair.gammaPats (cH H))[{j}]? = some it.pat := by
      unfold TiePair.gammaPats; rw [List.getElem?_map, hj]; rfl
    rw [TiePair.gammaPats_withHooks, gW_at] at hg
    rw [← Option.some.inj hg]
    intro M _ I hI
    exact w1 hI
  · obtain ⟨t, ht, hent⟩ := TiePair.from_text (shapeH H) j it hj
    unfold textPats at ht
    rw [List.getElem?_set_ne (Ne.symm hJ), List.getElem?_map] at ht
    cases hf : fnText[j]? with
    | none => rw [hf] at ht; cases ht
    | some ad => rw [hf] at ht; cases ht; exact ⟨ad, rfl, hent⟩

/-- The priority each function sentence's attributes state is the priority of the clause whose
item it gives, item by item in `fnItems`'s order. -/
theorem fn_prios : fnText.map (fun ad => AttrsAgree.prioOf ad.ax.attributes) =
    c.allFns.flatMap (fun f => f.clauses.map (·.prio)) := by decide +kernel

/-! ## The converse over Γ's content -/

/-- **Every premise of Γ is a consequence of the text's function sentences** (sentence {i} through
W1), Γ's rule items and the five parts Γ defines by predicates (`TiePair.Pre`), for every H. -/
theorem gamma_from (H : HookParams) : ∀ φ, Γ (cH H) φ → TiePair.Pre (cH H) textPats ⊧ φ :=
  TiePair.gamma_from (shapeH H)
'''


def alpha_block():
    """test/NonExecOwiseTie.lean's patterns equal up to a renaming of element variables (`alphaB`,
    `satisfies_of_alphaB`) and its alignment of items with sentences (`alignB`), as written there."""
    t = open(NEX_TIE).read()
    try:
        a = t.index("\n/-! ## Patterns equal up to the names of their element variables -/") + 1
        b = t.index("\nkernel_rfl fnItems_withHooks", a) + 1
    except ValueError:
        raise Refused("test/NonExecOwiseTie.lean has changed: no alphaB section to copy")
    s = t[a:b]
    if "/-! ## Shared -/\n\n" not in s or "def alignB" not in s or "theorem satisfies_of_alphaB" not in s:
        raise Refused("test/NonExecOwiseTie.lean has changed: its alphaB section lacks alignB or satisfies_of_alphaB")
    return s.replace("/-! ## Shared -/\n\n", "").rstrip("\n") + "\n"


def erase_chain(base, js, piped):
    """`base` without the members at the sorted indices `js`, each erased in turn (an index moves
    down by the members erased before it)."""
    es = [j - k for k, j in enumerate(js)]
    if piped:
        return f"({base}.eraseIdx {es[0]}" + "".join(f" |>.eraseIdx {e}" for e in es[1:]) + ")"
    s = f"{base}.eraseIdx {es[0]}"
    for e in es[1:]:
        s = f"({s}).eraseIdx {e}"
    return f"({s})"


def fn_align_section(fn_text, nonlit):
    a, n = nonlit[0], len(nonlit)
    if nonlit != list(range(a, a + n)):
        raise Refused("the [owise] equations whose items are not their sentences as written are not consecutive in fnItems")
    ow = f"the {numword(n)} `[owise]` equations" if n > 1 else "the `[owise]` equation"
    return f"""/-! ## Function equations ({len(fn_text)} sentences) -/

/-- The axioms of Γ's equations, in `fnItems`'s order. -/
noncomputable def fnAxioms (c : Semantics) : List Kore.Axiom :=
  c.allFns.flatMap fun f => (fnEquationsK c f).filterMap fun
    | .axiom a => some a
    | _ => none

theorem fnItems_eq : fnItems c = (fnAxioms c).map fun a => trAxiom [] [] ⟨0, "kernel", a⟩ := by kernel_rfl

/-- The text sentences of Γ's {len(fn_text)} equations, in `fnItems`'s order. -/
noncomputable def fnText : List AxiomDecl :=
  {ax_list(fn_text)}

/-- **The items of the other equations are their sentences' translations, pattern for pattern**
(one kernel decision). -/
theorem fn_shape_but_owise : {erase_chain("(fnItems c)", nonlit, True)}.map (·.pat) =
    {erase_chain("fnText", nonlit, False)}.map (trS · |>.pat) := by
  rw [fnItems_eq]; decide +kernel

/-- The items of {ow} are not their sentences' translations as written: the text
writes the exclusion's bound variable under its own name. -/
theorem owise_not_literal : ((fnItems c).drop {a} |>.take {n}).map (·.pat) ≠
    ((fnText.drop {a}).take {n}).map (trS · |>.pat) := by
  rw [fnItems_eq]; decide +kernel

/-- **Each of Γ's equations is the translation of its text sentence up to a renaming of element
variables, free and bound**, both ways (one kernel decision). -/
theorem fn_align : alignB trS (fnItems c) fnText = true := by
  rw [fnItems_eq]; decide +kernel

/-- **`fnText` is the account's function-equation class**: the same indices, each once. -/
theorem fns_account : (classOf "function equation").isPerm (fnText.map (·.index)) = true := by decide +kernel

/-- **E for the equations**: Γ entails each, for every H. -/
theorem fns_entailed (H : HookParams) : ∀ ad ∈ fnText, Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  obtain ⟨it, hit, _, hα⟩ := align_text fn_align had
  exact satisfies_of_alphaB hα (hI _ (mem_Γ_fns (Or.inl ⟨it, by rw [fnItems_withHooks]; exact hit, rfl⟩)))

/-- **The converse for `fnItems`**: the j-th item is a consequence of `fnText[j]`. -/
theorem fns_from_text (H : HookParams) :
    ∀ (j : Nat) (it : Item), (fnItems (cH H))[j]? = some it →
      ∃ ad, fnText[j]? = some ad ∧ (itemsPremises [trS ad] ⊧ it.pat) := by
  intro j it hj
  rw [fnItems_withHooks] at hj
  have hl : (fnItems c).length = fnText.length := by
    have := fn_align; simp only [alignB, Bool.and_eq_true, beq_iff_eq] at this; exact this.1
  obtain ⟨hjl, hjit⟩ := List.getElem?_eq_some_iff.mp hj
  have hjt : j < fnText.length := hl ▸ hjl
  refine ⟨fnText[j], List.getElem?_eq_getElem hjt, fun {{M}} _ {{I}} hI => ?_⟩
  have hα := (align_pair fn_align j hjl hjt).2
  rw [hjit] at hα
  exact satisfies_of_alphaB hα (hI _ (Or.inl ⟨trS fnText[j], List.mem_singleton_self _, rfl⟩))

/-- The priority each function sentence's attributes state is the priority of the clause whose
item is the sentence's translation, item by item in `fnItems`'s order. -/
theorem fn_prios : fnText.map (fun ad => AttrsAgree.prioOf ad.ax.attributes) =
    c.allFns.flatMap (fun f => f.clauses.map (·.prio)) := by decide +kernel
"""


def nojunk_sort_section(i, e, sn, rawd, new):
    """The no-junk sentence `i` of a sort with generators other than KItem (`e`: the probe's
    match): the item over the sort's generators in the text's order, entailed by Γ for every H."""
    s, S = sn[e["srt"]], e["sort"]
    gr = [(k, r) for k, r, _ in rawd if k["res"] == e["srt"]]
    srt = lambda x: sn.get(x, str(x))
    out = []
    if new:
        out += [f"/-- {S}, a sort with generators. -/", f"def {s} : Srt := {e['srt']}", "",
                f'theorem {s}_name : c.sortName {s} = "{S}" := by decide +kernel', ""]
    if e["form"] == "perm":
        pm = e["perm"]
        gs = ", ".join(f"g{j}" for j in range(len(pm)))
        # a list pattern of many elements is no pattern Lean takes: past 5 generators (the probe's
        # enumeration) the order is the generators' positions
        body = [f"  match (c.gens {s}).map (Gen.toK c) with",
                f"  | [{gs}] => [{', '.join(f'g{j}' for j in pm)}]",
                "  | gs => gs"] if len(pm) <= 5 else \
            [f"  ([{wrap_nums([str(j) for j in pm], 4)}] : List Nat).filterMap",
             f"    (((c.gens {s}).map (Gen.toK c))[·]?)"]
        out += [f"/-- {S}'s generators in the order the text's no-junk sentence ({i}) lists them, a permutation",
                "of those `Semantics.gens` lists. -/",
                f"noncomputable def {s}TextGens : List KoreAML.Gen :="] + body + ["",
                f"/-- {S}'s no-junk sentence ({i}) is the item over {S}'s generators in the text's order. -/",
                f"theorem nojunk_{s}_order : (trS U.ax{i}).pat = (KoreAML.Cons.noJunkItem (c.sortName {s}) {s}TextGens).pat := by",
                "  decide +kernel",
                f"theorem nojunk_{s}_members : {s}TextGens.isPerm ((c.gens {s}).map (Gen.toK c)) = true := by",
                "  decide +kernel"]
    else:
        out += [f"/-- {S}'s no-junk sentence ({i}) is the item over {S}'s generators in the text's order, the same",
                "generators as `Semantics.gens` lists. -/",
                f"theorem nojunk_{s}_order : (trS U.ax{i}).pat =",
                f"    (KoreAML.Cons.noJunkItem (c.sortName {s}) ((gensInOrder c defn.pres {s}).map (Gen.toK c))).pat := by",
                "  decide +kernel",
                f"theorem nojunk_{s}_members :",
                f"    ((gensInOrder c defn.pres {s}).map (Gen.toK c)).isPerm ((c.gens {s}).map (Gen.toK c)) = true := by",
                "  decide +kernel"]
    names = [f"nojunk_{s}_order", f"nojunk_{s}_members"]
    if gr:
        og = " ∧ ".join(f"c.isOpenGen (.ctor ⟨{r}, [{', '.join(srt(a) for a in k['args'])}], {s}⟩) = true" for k, r in gr)
        nm = f"nojunk_{s}_{gr[0][1]}" if len(gr) == 1 else f"nojunk_{s}_open"
        out += [f"theorem {nm} : ((c.gens {s}).map (Gen.toK c)).length = {e['ngens']} ∧ {og} := by",
                "  decide +kernel"]
        names.append(nm)
    members = ("(List.isPerm_iff.mp nojunk_" + s + "_members).mem_iff.mpr hg")
    out += ["",
            f"/-- **E for {S}'s no junk ({i})**, for every H (`noJunkItem_of_subset`). -/",
            f"theorem nojunk_{s}_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax{i}).pat := by",
            "  intro M _ I hI",
            f"  rw [nojunk_{s}_order]",
            f"  refine noJunkItem_of_subset (defOK hI) (gs := (c.gens {s}).map (Gen.toK c))",
            f"    (fun g hg => {members}) ?_",
            f"  exact sat_cons hI (Or.inl ⟨_, noJunkItem_mem (c := cH H) (N := {s})",
            f"    (show {s} ∈ consSorts c by decide +kernel) (show (c.gens {s}).isEmpty = false by decide +kernel), rfl⟩)",
            ""]
    names.append(f"nojunk_{s}_entailed")
    return "\n".join(out), names


IDEM_RAW = [
    ("theorem s1_sort : (cH H).sortOf s1 = some Srt.set := by rw [Semantics.sortOf_withHooks _ _ noRaw]; decide +kernel",
     "theorem s1_sort : (cH H).sortOf s1 = some Srt.set := by\n  rw [Semantics.sortOf_withHooks_rawFree c H (by decide +kernel)]; decide +kernel"),
    ("  rw [Semantics.sortsOf_withHooks _ _ noRaw]; decide +kernel", "  simp only [Semantics.sortsOf, s1_sort H]"),
]


def law_section(law_idx):
    il = ", ".join(map(str, law_idx))
    lt = ", ".join(f"U.ax{i}" for i in law_idx)
    return f"""/-! ## The law sentences ({il}): owed as `FnLaws` -/

/-- The text's law sentences of functions, in the order of the reader's laws (`Definition.laws`). -/
noncomputable def lawText : List AxiomDecl := [{lt}]

theorem law_indices : lawText.map (·.index) = lawIdx := by decide +kernel

/-- **Each law sentence is, as written, the sentence of the reader's law** (`lawPattern`), in
`Definition.laws`' order: what `consistent_with_laws` states in a model of Γ with the step's
closure, where the interpretation satisfies the laws at values (`FnLaws`). -/
theorem law_text : lawText.map (trS · |>.pat) = defn.laws.map (lawPattern c) := by decide +kernel

/-- **No law sentence is a function equation's item or a constructor item of Γ** (`fnItems`,
`consItemsK`). -/
theorem law_not_item : lawText.all (fun ad => !(fnItems c).any (·.pat == (trS ad).pat) &&
    !(consItemsK c).any (·.pat == (trS ad).pat)) = true := by decide +kernel

/-- The law sentences are the account's class `{LAW_FN_CLASS}`, of the direction `hypothesis` (Γ does
not hold the sentence; it is owed as `FnLaws`). -/
theorem law_account : lawText.map (·.index) = classOf "{LAW_FN_CLASS}" := by
  decide +kernel
"""


def param_functional_section(param_fun, total_names, n, chunk):
    il = ", ".join(map(str, param_fun))
    lt = ", ".join(f"U.ax{i}" for i in param_fun)
    tn = ", ".join(f'"{x}"' for x in total_names)
    pred = f'(fun ad => !functionalOfNamed [{tn}] ad.ax || (classOf "{PARAM_FUNCTIONAL_CLASS}").contains ad.index)'
    if chunk:
        thms, body = by_ranges("paramFunE", "U.all", "paramFunP", ranges(n, 0, chunk), "tieAll", True)
        heads = (f"""/-- The sentence is no parameter's functional sentence, or it is of the class
`{PARAM_FUNCTIONAL_CLASS}`. -/
noncomputable def paramFunP (ad : AxiomDecl) : Bool :=
  !functionalOfNamed [{tn}] ad.ax || (classOf "{PARAM_FUNCTIONAL_CLASS}").contains ad.index

{thms}

""", "  rw [userAxioms_eq]; exact\n    " + body.replace("\n    ", "\n      "))
    else:
        heads = ("", "  rw [userAxioms_eq]; decide +kernel")
    return f"""/-! ## The parameter functional sentences ({il}): owed as `ParamsTotal` -/

/-- The parameter symbols no registry hook interprets that the text declares total
(`Definition.totalParams`): the statements take `ParamsTotal c defn.totalParams H`, that `H` gives
each a value of its result sort at every argument list of its argument sorts. -/
theorem total_params : defn.totalParams.map c.symName = [{tn}] := by decide +kernel

/-- The text's `functional` sentences of those parameters (`isParamFunctional`). -/
noncomputable def paramFunctionalText : List AxiomDecl := [{lt}]

/-- The parameter functional sentences are the account's class `{PARAM_FUNCTIONAL_CLASS}`, of the
direction `hypothesis`: Γ states a parameter's graph at values from the interpretation (`ΓDomains`),
so it holds the sentence at values exactly where `H` gives the parameter a value at the values of its
argument sorts, which is `ParamsTotal` at that parameter. -/
theorem paramfunctional_account : paramFunctionalText.map (·.index) = classOf "{PARAM_FUNCTIONAL_CLASS}" ∧
    paramFunctionalText.all (fun ad => functionalOfNamed [{tn}] ad.ax) = true := by
  decide +kernel

{heads[0]}/-- Every `functional` sentence of the user module of a parameter the text declares total
(`total_params`) is of the class `{PARAM_FUNCTIONAL_CLASS}`. -/
theorem paramfunctional_heads : userAxioms.all {pred} = true := by
{heads[1]}
"""


def param_lemma_section(param_lem):
    il = ", ".join(map(str, param_lem))
    lt = ", ".join(f"U.ax{i}" for i in param_lem)
    return f"""/-! ## The parameter lemmas ({il}): owed as a hypothesis on H -/

/-- The text's lemmas that apply a parameter symbol no registry hook interprets (`isParamLemma`). -/
noncomputable def paramLemmaText : List AxiomDecl := [{lt}]

/-- The parameter lemmas are the account's class `{PARAM_LEMMA_CLASS}`, of the direction `hypothesis`
(Γ does not hold the sentence; at the member `cH H` it is owed at values). -/
theorem paramlemma_account : paramLemmaText.map (·.index) = classOf "{PARAM_LEMMA_CLASS}" := by
  decide +kernel

/-- **What the tie owes of the parameter lemmas**: one interpretation `H` at which the functions'
obligations hold and every parameter lemma holds in every model of Γ at the valuations sending its
free element variables to values (`EntailsAtValues`), so that the text with its hypotheses has a
model. Γ states a parameter's graph at values only (`ΓDomains`), so the lemma is owed there. Stated,
not proved here: the proof is owed. -/
def ParamLemmaWitnessAtValues : Prop :=
  ∃ H : HookParams, FnObligations (cH H) callOrder [] ∧
    ∀ ad ∈ paramLemmaText, EntailsAtValues (cH H) ad (trS ad).pat

/-- Every sentence of the user module that carries `simplification`, is an equation
(`AttrsAgree.eqnHead`) and has at the head of its left side a parameter symbol no registry hook
interprets (`impl = none`) is of the class `{PARAM_LEMMA_CLASS}`: the sentences `attrsAgree` does not
count as equations of such a parameter are held by the account as hypotheses on `H`. -/
theorem paramlemma_heads : userAxioms.all (fun ad =>
    !(AttrsAgree.has ad.ax.attributes "simplification" &&
      (AttrsAgree.eqnHead ad.ax.pattern).any (fun n =>
        c.params.any fun k => k.impl.isNone && c.symName k.sig.name == n)) ||
    (classOf "{PARAM_LEMMA_CLASS}").contains ad.index) = true := by
  rw [userAxioms_eq]; decide +kernel
"""


def user_lemma_section(user_lem, user_lem_v):
    il = ", ".join(map(str, user_lem + user_lem_v))
    lt = ", ".join(f"U.ax{i}" for i in user_lem)
    lv = ", ".join(f"U.ax{i}" for i in user_lem_v)
    return f"""/-! ## The user lemmas ({il}): owed, by hand -/

/-- The lemmas of a user's file that the reader leaves out of Γ and that apply no parameter symbol
without `impl`, of the class `{USER_LEMMA_CLASS}`. -/
noncomputable def userLemmaText : List AxiomDecl := [{lt}]

/-- Those of the class `{USER_LEMMA_VALUES_CLASS}`. -/
noncomputable def userLemmaValuesText : List AxiomDecl := [{lv}]

/-- The two lists are the account's classes `{USER_LEMMA_CLASS}`, of the direction `entailed`, and
`{USER_LEMMA_VALUES_CLASS}`, of the direction `atValues`. -/
theorem userlemma_account : userLemmaText.map (·.index) = classOf "{USER_LEMMA_CLASS}" ∧
    userLemmaValuesText.map (·.index) = classOf "{USER_LEMMA_VALUES_CLASS}" := by
  decide +kernel

/-- **What the tie owes of the user lemmas of the class `{USER_LEMMA_CLASS}`**: Γ entails each, for
every interpretation `H`. Stated, not proved here: the proof is owed. -/
def UserLemmaEntailed : Prop :=
  ∀ (H : HookParams), ∀ ad ∈ userLemmaText, Γ (cH H) ⊧ (trS ad).pat

/-- **What the tie owes of the user lemmas of the class `{USER_LEMMA_VALUES_CLASS}`**: each holds in
every model of Γ at the valuations sending its free element variables to values, for every
interpretation `H`. Stated, not proved here: the proof is owed. -/
def UserLemmaAtValues : Prop :=
  ∀ (H : HookParams), ∀ ad ∈ userLemmaValuesText, EntailsAtValues (cH H) ad (trS ad).pat
"""


def openlaw_section(open_law, rnames, need_rfl):
    i = open_law[0]
    rfl = ("kernel_rfl consItemsK_withHooks : ∀ (c : Semantics) (H : HookParams), consItemsK (c.withHooks H) = consItemsK c\n\n"
           if need_rfl else "")
    return f"""/-! ## The law sentence of {rnames} ({i}): an item of Γ -/

{rfl}/-- **Γ's one law item is the translation of sentence {i}, as written** (`lawItemsK`, a part of
the constructors' items). -/
theorem openlaw_item : (lawItemsK c).map (·.pat) = [(trS U.ax{i}).pat] := by decide +kernel
theorem openlaw_cons : (consItemsK c).any (·.pat == (trS U.ax{i}).pat) = true := by decide +kernel

/-- **E for the law sentence**: Γ entails it, for every H. -/
theorem openlaw_entailed (H : HookParams) : Γ (cH H) ⊧ (trS U.ax{i}).pat := by
  intro M _ I hI
  obtain ⟨it, hit, he⟩ := List.any_eq_true.mp openlaw_cons
  rw [← of_decide_eq_true he]
  exact sat_cons hI (Or.inl ⟨it, by rw [consItemsK_withHooks]; exact hit, rfl⟩)

/-- The law sentence is the account's class `{LAW_OPEN_CLASS}` (direction `equal`: Γ's law item is
its translation, `openlaw_item`, and Γ entails it, `openlaw_entailed`). -/
theorem openlaw_account : classOf "{LAW_OPEN_CLASS}" = [{i}] := by decide +kernel
"""


def open_functional_section(open_fun, rnames):
    if len(open_fun) == 1:
        i = open_fun[0]
        return f"""/-! ## The functional sentence of {rnames} ({i}): owed as `OpenTotal` -/

/-- **Γ holds no item for {rnames}'s functional sentence**: the constructors' items state the
functionality of the generators that are no open generator only. The sentence is owed, at values,
as `OpenTotal`, which `lawHooks c H` satisfies (`lawHooks_laws`). -/
theorem open_functional_not_item : !(consItemsK c).any (·.pat == (trS U.ax{i}).pat) &&
    !(fnItems c).any (·.pat == (trS U.ax{i}).pat) &&
    (classOf "{OPEN_FUNCTIONAL_CLASS}" == [{i}]) = true := by
  decide +kernel
"""
    return f"""/-! ## The functional sentences of {rnames} ({', '.join(map(str, open_fun))}): owed as `OpenTotal` -/

/-- **Γ holds no item for the open generators' functional sentences**: the constructors' items
state the functionality of the generators that are no open generator only. The sentences are owed,
at values, as `OpenTotal`, which `lawHooks c H` satisfies (`lawHooks_laws`). -/
theorem open_functional_not_item : {ax_list(open_fun, 4)}.all (fun ad => !(consItemsK c).any (·.pat == (trS ad).pat) &&
    !(fnItems c).any (·.pat == (trS ad).pat)) &&
    (classOf "{OPEN_FUNCTIONAL_CLASS}" == [{', '.join(map(str, open_fun))}]) = true := by
  decide +kernel
"""


def gamma_c_section(gamma, fn_align, nrules, fn_any, nj_triv, nj_items, nj_kitem, cons_text, idem, own_idem=()):
    """The statements over `Γc = Γ ∪ Γcl`, the theory of a definition that reads a confined sort: each
    entailment over Γ holds over `Γc`; `Γcl` holds `boolClosed` alone; the origin of `Γc`'s premises."""
    L = ["/-! ## Over `Γc`, the theory the statements are about -/", "",
         "/-- `Γc` holds every premise of Γ. -/",
         "theorem Γ_sub_Γc (c : Semantics) {φ : P} (h : Γ c φ) : Γc c φ := Or.inl h", "",
         "/-- What Γ entails, `Γc` entails. -/",
         "theorem entails_c {c : Semantics} {ψ : P} (h : Γ c ⊧ ψ) : Γc c ⊧ ψ :=",
         "  fun hI => h fun φ hφ => hI φ (Γ_sub_Γc c hφ)", "",
         "/-- Bool holds only its literals here, and the definition reads a confined sort: `Γcl` holds its",
         "one item, `boolClosed`. -/",
         "theorem gammaCl_eq (H : HookParams) (φ : P) : Γcl (cH H) φ ↔ φ = boolClosed (cH H) :=",
         "  ⟨fun h => h.2.2, fun h => ⟨readsConfined_c, (by decide +kernel : c.litSort Srt.bool = true), h⟩⟩", ""]
    names = ["gammaCl_eq"]
    if gamma:
        if fn_align:
            fnd = "(∃ ad ∈ fnText, ∃ env, alphaB env (trS ad).pat φ = true)"
        else:
            fnd = "(∃ ad ∈ fnText, (trS ad).pat = φ)"
        if nrules:
            body = (f"    ({fnd} ∨ (ΓRules (cH H) φ ∧ ∃ ad ∈ ruleText, itemsPremises [trS ad] ⊧ φ) ∨\n"
                    "      Families H φ ∨ (∃ x : EVar, φ = @definedness KoreAML.Sym _ x)) ∨ φ = boolClosed (cH H) := by")
        else:
            body = (f"    ({fnd} ∨ Families H φ ∨\n"
                    "      (∃ x : EVar, φ = @definedness KoreAML.Sym _ x)) ∨ φ = boolClosed (cH H) := by")
        L += ["/-- **The origin of each premise of `Γc`**: one of Γ's (`gamma_origin`), or `boolClosed`, the item",
              "of `Γcl`: every element of Bool is `true` or `false`, a family of the reading of a definition that",
              "reads a confined sort, which no sentence of the text states. -/",
              "theorem gamma_origin_c (H : HookParams) : ∀ φ, Γc (cH H) φ →", body,
              "  intro φ h", "  rcases h with h | h", "  · exact Or.inl (gamma_origin H φ h)",
              "  · exact Or.inr ((gammaCl_eq H φ).mp h)", "",
              "/-- Every premise of `Γc` is a consequence of `Pre` with `Γcl`. -/",
              "theorem gamma_from_c (H : HookParams) : ∀ φ, Γc (cH H) φ → (Pre H ∪ Γcl (cH H)) ⊧ φ := by",
              "  intro φ h M _ I hI", "  rcases h with h | h",
              "  · exact gamma_from H φ h (fun ψ hψ => hI ψ (Or.inl hψ))", "  · exact hI _ (Or.inr h)", ""]
        names += ["gamma_origin_c", "gamma_from_c"]
    L += ["theorem decls_entailed_c (H : HookParams) : ∀ it ∈ declItems, Γc (cH H) ⊧ it.pat :=",
          "  fun it hit => entails_c (decls_entailed H it hit)"]
    names.append("decls_entailed_c")
    if fn_any:
        L += ["theorem fns_entailed_c (H : HookParams) : ∀ ad ∈ fnText, Γc (cH H) ⊧ (trS ad).pat :=",
              "  fun ad had => entails_c (fns_entailed H ad had)"]
        names.append("fns_entailed_c")
    if nj_triv:
        L += ["theorem nojunk_trivial_entailed_c (H : HookParams) :",
              f"    ∀ ad ∈ {ax_list([i for i, _ in nj_triv], 6)}, Γc (cH H) ⊧ (trS ad).pat :=",
              "  fun ad had => entails_c (nojunk_trivial_entailed H ad had)"]
        names.append("nojunk_trivial_entailed_c")
    if nj_items:
        L += [f"theorem nojunk_items_entailed_c (H : HookParams) : ∀ ad ∈ {ax_list(nj_items, 6)},",
              "    Γc (cH H) ⊧ (trS ad).pat :=",
              "  fun ad had => entails_c (nojunk_items_entailed H ad had)"]
        names.append("nojunk_items_entailed_c")
    for i in nj_kitem:
        L += [f"theorem nojunk_kitem_entailed_c (H : HookParams) : Γc (cH H) ⊧ (trS U.ax{i}).pat :=",
              "  entails_c (nojunk_kitem_entailed H)"]
        names.append("nojunk_kitem_entailed_c")
    if cons_text:
        L += ["theorem cons_entailed_c (H : HookParams) : ∀ ad ∈ consText, Γc (cH H) ⊧ (trS ad).pat :=",
              "  fun ad had => entails_c (cons_entailed H ad had)"]
        names.append("cons_entailed_c")
    if idem is not None:
        L += [f"/-- **Sentence {idem} is refuted over `Γc`, for every H**: a model of `Γc` is one of Γ. -/",
              "theorem idem_refuted_c (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),",
              f"    I ⊧ᴵP Γc (cH H) → ¬ (I ⊧ᴵ (trS U.ax{idem}).pat) :=",
              "  fun M hM I hI => idem_refuted H M hM I fun φ hφ => hI φ (Γ_sub_Γc _ hφ)"]
        names.append("idem_refuted_c")
    for i, _, _ in own_idem:
        L += [f"/-- **Sentence {i} is refuted over `Γc`, for every H**: a model of `Γc` is one of Γ. -/",
              f"theorem own_idem_refuted_{i}_c (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),",
              f"    I ⊧ᴵP Γc (cH H) → ¬ (I ⊧ᴵ (trS U.ax{i}).pat) :=",
              f"  fun M hM I hI => own_idem_refuted_{i} H M hM I fun φ hφ => hI φ (Γ_sub_Γc _ hφ)"]
        names.append(f"own_idem_refuted_{i}_c")
    return "\n".join(L) + "\n", names


OWN_IDEM_RE = re.compile(r"axiom ?\{R\} ?\\equals\{Sort([\w']+)\{\}, ?R\} ?\(([^\s{}(),]+)\{\}\("
                         r"(\w+):Sort\1\{\}, ?\3:Sort\1\{\}\), ?\3:Sort\1\{\}\) ?\[idem\{\}\(\)\]")


def own_idem_shape(raw):
    """`(concatenation symbol, variable)` of an idempotence sentence `\\equals{S, R}(f(K, K), K)`
    with nothing but `idem` among its attributes, or None."""
    m = OWN_IDEM_RE.match(raw.strip())
    return (m.group(2), m.group(3)) if m else None


def own_idem_section(own_idem):
    """The refutation of each idempotence sentence of a set collection other than the library's
    `Set` (`Faithful.setColl_idem_refuted_text`)."""
    L = ["/-! ## Set idempotence of the definition's own set collections: refuted",
         "",
         "Each sentence is the idempotence sentence of a set collection of the definition, whose key sort",
         "has a value the search exhibits (`setIdemTextOK`, a kernel decision). At the element `x` of a",
         "one-member set `{w}` the sentence says `concat(x, x)` holds `x`; `ΓColls` (`setElemAtomAx`) then",
         "makes `x` the unit's, which `setElemNotUnitAx` denies (`Faithful.setColl_idem_refuted_text`). -/",
         ""]
    for i, f, v in own_idem:
        L += [f"theorem own_idem_ok_{i} : setIdemTextOK c \"{f}\" \"{v}\" U.ax{i} = true := by decide +kernel",
              f"theorem own_idem_trS_{i} : (trS U.ax{i}).pat = (trAxiom [] [] U.ax{i}).pat := by decide +kernel",
              "",
              f"/-- **Sentence {i} is refuted, for every H**: Γ with it has no model. -/",
              f"theorem own_idem_refuted_{i} (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),",
              f"    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS U.ax{i}).pat) := by",
              "  haveI : OvlOK (cH H) := ovlOK_of_core (coreOKH H)",
              "  intro M hM I hI hax",
              f"  rw [own_idem_trS_{i}] at hax",
              f"  exact setColl_idem_refuted_text c H own_idem_ok_{i} M hM I hI hax",
              ""]
    return "\n".join(L)



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

GAMMA_ALIGN = r'''/-! ## The converse over Γ's content -/

theorem ruleItems_nil : ruleItems c = [] := by kernel_rfl

/-- The parts of Γ that are no sentence's translation: the families. -/
def Families (H : HookParams) : Premises KoreAML.Sym :=
  ΓSig (cH H) ∪ ΓCons (cH H) ∪ ΓDomains (cH H) ∪ ΓColls (cH H) ∪ ΓFallback (cH H)

/-- The function sentences as written, with definedness, and the families. -/
def Pre (H : HookParams) : Premises KoreAML.Sym :=
  (fun φ => (∃ ad ∈ fnText, (trS ad).pat = φ) ∨ ∃ x : EVar, φ = @definedness KoreAML.Sym _ x) ∪ Families H

/-- **The origin of each premise of Γ**: a function equation is the translation of a text
sentence up to a renaming of element variables; the text has no rule, so Γ has no rule item;
everything else is one of the five parts defined by predicates (`Families`), or definedness. -/
theorem gamma_origin (H : HookParams) : ∀ φ, Γ (cH H) φ →
    (∃ ad ∈ fnText, ∃ env, alphaB env (trS ad).pat φ = true) ∨ Families H φ ∨
      (∃ x : EVar, φ = @definedness KoreAML.Sym _ x) := by
  intro φ h
  rcases h with ((((((h | h) | h) | h) | h) | h) | h)
  · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h)))))
  · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
  · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr h))))
  · exact Or.inr (Or.inl (Or.inl (Or.inr h)))
  · rcases h with ⟨it, hit, rfl⟩ | hx
    · rw [fnItems_withHooks] at hit
      exact Or.inl (align_item fn_align hit)
    · exact Or.inr (Or.inr hx)
  · rcases h with ⟨it, hit, rfl⟩ | hx
    · rw [ruleItems_withHooks, ruleItems_nil] at hit; cases hit
    · exact Or.inr (Or.inr hx)
  · exact Or.inr (Or.inl (Or.inr h))

/-- Every premise of Γ is a consequence of `Pre`. -/
theorem gamma_from (H : HookParams) : ∀ φ, Γ (cH H) φ → Pre H ⊧ φ := by
  intro φ h M _ I hI
  rcases gamma_origin H φ h with ⟨ad, had, _, hα⟩ | hf | hx
  · exact satisfies_of_alphaB hα (hI _ (Or.inl (Or.inl ⟨ad, had, rfl⟩)))
  · exact hI _ (Or.inr hf)
  · exact hI _ (Or.inl (Or.inr hx))
'''


def law_refuted(name, head, laws, raws, sents):
    """The refusal of a text with a law the probe refutes at values (the module's docstring,
    Function laws), or None. `laws`: the probe's `lawIx`, in `Definition.laws`' order."""
    for r in head["lawRef"]:
        if r["wit"]:
            i, w = laws[r["j"]][0], r["wit"]
            return (f"{name}: the law axiom {i} ({law_what([i], raws, sents)}) is false at values under every "
                    f"interpretation: at {w['sigma']} its left side's value is {w['lhs']} and its right side's "
                    f"{w['rhs']} (`Cert.evalTC`, which consults no interpretation); `FnLaws` fails at every H, so the "
                    "text is not tied and a fixture of it is a test of the check (DONE-0 C8; "
                    "test/constructs/rows-header.toml, owed-sentence rule items 3 and 4)")
    return None


# the law search's expected outcome on fixtures: the refusal's witness, or None where no law is refuted
SELF_TEST = {"e2-fn-assoc-bad": "at var 0 = 0, var 1 = 0, var 2 = 1 its left side's value is -1 and its right side's 1",
             "e2-fn-assoc": None, "e2-fn-assoc-rest": None}


def self_test():
    bad = []
    for name, want in SELF_TEST.items():
        text = restored_text(name)
        with tempfile.TemporaryDirectory(prefix="tiegen-self-") as d:
            path = os.path.join(d, f"{name}.kompile.kore")
            open(path, "w").write(text)
            account_check(name, path)
            ob = obligations(name, path)
            um0, ua = user_axioms(text)
            head, sents = probe(name, path, um0, ob["order_list"])
        laws, lr = nested(head["lawIx"]), head["lawRef"]
        got = law_refuted(name, head, laws, {i: raw for i, _, _, raw in ua}, sents) if len(lr) == len(laws) else None
        ok = len(laws) == len(lr) == 1 and lr[0]["searched"] and (got is None if want is None else want in got)
        print(f"tiegen self-test: {name}: " + (f"refused: {got}" if got else
              f"{len(lr)} laws, searched {[x['searched'] for x in lr]}, {[x['tried'] for x in lr]} valuations, no witness")
              + ("" if ok else "  FAILS"))
        if not ok:
            bad.append(name)
    print(f"tiegen self-test: {len(SELF_TEST)} fixtures, {len(bad)} failing")
    return 1 if bad else 0


def main(argv):
    if argv[:1] == ["--self-test"]:
        return self_test()
    if not argv or argv[0].startswith("-"):
        raise SystemExit(__doc__)
    name = argv[0]
    opt = lambda f, d: int(argv[argv.index(f) + 1]) if f in argv else d
    chunks = (opt("--sig-chunk-first", 34), opt("--sig-chunk", 13), opt("--decl-chunk", 25))
    chunk = opt("--chunk", 0)
    at_values = ()
    if "--at-values" in argv:
        v = argv[argv.index("--at-values") + 1] if argv.index("--at-values") + 1 < len(argv) else ""
        if not re.fullmatch(r"\d+(,\d+)*", v):
            raise Refused(f"--at-values {v!r}: a comma-separated list of sentence indices is expected")
        at_values = tuple(sorted({int(x) for x in v.split(",")}))
    hand = {}
    for j, a in enumerate(argv):
        if a == "--hand":
            sec, _, f = argv[j + 1].partition("=")
            if sec not in HAND_SECTIONS or not os.path.isfile(f):
                raise Refused(f"--hand {argv[j + 1]}: no section {sec!r} or no file {f!r} (sections: {', '.join(HAND_SECTIONS)})")
            hand[sec] = open(f).read()
    if not os.path.isdir(os.path.join(FX, name)):
        raise Refused(f"{name}: no such fixture")
    text = restored_text(name)
    text_rel = f"f2-examples/{name}.kompile.kore"
    final = os.path.join(KS, text_rel)
    tmpd = tempfile.TemporaryDirectory(prefix="tiegen-text-")
    path = os.path.join(tmpd.name, f"{name}.kompile.kore")
    open(path, "w").write(text)
    wf_ok, failing = account_check(name, path)
    ob = obligations(name, path, "consistency" in hand)
    um0, ua = user_axioms(text)
    cons_head = "--cons-head" in argv
    wf_parts = None
    if "--wf-parts" in argv:
        nsorts = len(re.findall(r"^\s*(?:hooked-)?sort ", text, re.M))
        nsyms = len(re.findall(r"^\s*(?:(?:hooked-)?symbol|alias) ", text, re.M))
        wf_parts = (nsorts.bit_length() + 1, nsyms.bit_length() + 1)
    head, sents = probe(name, path, um0, ob["order_list"], cons_head)
    if "consistency" in hand and not (ob["agree"] or ob["match"] or ob["owed"]):
        raise Refused(f"{name}: --hand consistency is for a text that owes an agreement, a match independence or a "
                      f"condition")
    laws, open_laws = nested(head["lawIx"]), nested(head["openLawIx"])
    if any(len(l) != 1 for l in laws) or len({l[0] for l in laws}) != len(laws):
        raise Refused(f"{name}: a law of the reader (`Definition.laws`) is not, as written, exactly one sentence of the user module")
    if any(len(l) != 1 for l in open_laws) or len(open_laws) > 1:
        raise Refused(f"{name}: Γ's law items (`lawItemsK`) are not one sentence of the user module, as written")
    if len(head["lawRef"]) != len(laws):
        raise Refused(f"{name}: the probe's law search does not list the reader's laws")
    refuted = law_refuted(name, head, laws, {i: raw for i, _, _, raw in ua}, sents)
    if refuted:
        raise Refused(refuted)
    if head.get("wf") != ("true" if wf_ok else "false"):
        raise Refused(f"{name}: the probe's wf and the account's differ")
    next_only = head.get("sigBadNext") == "true" and head.get("textNext") == "false"
    if (head.get("sigAll") != "true" and not next_only) or head.get("declAll") != "true":
        raise Refused(f"{name}: an item of the signature has no origin (items {head.get('sigBad')}) or a declaration's item is not Γ's")
    law_set, open_set = {l[0] for l in laws}, {l[0] for l in open_laws}
    names_of = lambda k: set(re.findall(r"[^\s\[\],]+", head.get(k, "")))
    um, cls, mapped, unmapped = classify(name, text, sents, law_set, open_set, {k["name"] for k in head["raw"]},
                                         at_values, names_of("totalParams"), names_of("noImplParams"))
    for i in law_set | open_set:
        if sents[i]["fnJ"] or (i in law_set and sents[i]["consItem"]):
            raise Refused(f"{name}: law sentence {i} is a function equation's item or a constructor item of Γ")
    ns, lean, summary = generate(name, text_rel, um, cls, mapped, unmapped, sents, head, wf_ok, failing,
                                 ob, chunks, {i: raw for i, _, _, raw in ua}, hand, chunk,
                                 at_values, cons_head, wf_parts)
    outdir = argv[argv.index("--out") + 1] if "--out" in argv else None
    if outdir is None and (not os.path.exists(final) or open(final).read() != text):
        open(final, "w").write(text)
    out = os.path.join(outdir or os.path.join(KS, "test"), ns + ".lean")
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
