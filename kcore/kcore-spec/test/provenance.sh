#!/usr/bin/env bash
# DONE-0 C7, check 1: the evidence theorems rows.toml names (field `derived`, rows-header.toml) carry
# their form and kind, are stated for every hook interpretation, and are none of the AtNone ones.
#
# An entry is any table of rows.toml with a key `derived`: a row of a list (E1 to E8, C3) or a table
# nested in one (`cases`, `also_refused`, `split`). `derived` is a list of tables, one per derivation:
#   form       "a", "b", "c" or "r" (C7: (a) a Lean proof from the translated text's sentences, Γ's
#              items of a W-class sentence with their W1 theorem, and named families; (b) a derivation
#              written step by step, by hand; (c) "the text's sentences entail no value here", with
#              the pair of models that shows it; (r) "the text's sentences have no model": a Lean
#              proof that the premise set form (a) would use, built the same way, has no model)
#   kind       form (a): "from sentences" (a defined value, a step that exists), "through the
#              reading" (no value where an `ensures` fails, no successor, an exact successor set) or
#              "in a model" (the sentences of a symbol Γ lacks, of the no-direction class, hold at
#              values in a model of Γ whose steps are Step's: owed-sentence rule item 7);
#              form (r), optional: "through the reading" (the refutation is of the reading's theory,
#              the sentence-level statement owed) or "sentence against the reading" (a text without a
#              model whose reading has one: for every H no model of the theory the statements are
#              about (`Γc (c.withHooks H)`; `Γ` where the proof reads no `boolClosed`, which is the
#              stronger form) satisfies the one sentence named first in `sentences`, as written; the
#              reading is consistent, `consistent`)
#   family     kind "through the reading": the family the expectation goes through (`Γstep`, the
#              premise ⌈rhs ∧ ens⌉, ...); form (r): the families of the reading the refutation uses
#              beside the sentences, each named (always required: no refutation is from sentences
#              alone where a family carries a fact no sentence states); a refutation stated over `Γc`
#              and not `Γ` names `Γcl` (`boolClosed`, which no sentence of the text states)
#   sentences  forms (a) and (r): the indices of the text's sentences that determine the
#              expectation (that the refutation uses); `[]` on a form (a) table, kind "through the
#              reading", of a supported E6 `hook:` row itself (not a nested table): a hook has no
#              defining sentence, its in-domain value is stated from the builtin prose at a
#              semantics, not at a text, and goes through Γ's graph of the symbol (its `family`)
#   theorem    the theorem's full name (namespaces included); required for forms (a), (c) and (r)
#   file       the Lean file holding it, relative to kcore-spec; required with `theorem`
#   derivation form (b): the file holding the derivation, relative to kcore-spec
#   owed_refuted  form (r) only, optional: the full name of a theorem of `file` refuting the fact
#              the package names as owed for the construct (it is false of this text)
#   consistent kind "sentence against the reading" only, required: the full name of a theorem of
#              `file` stating `Consistent` of the reading for every H (Γ has a model)
#   owed_statement  kind "sentence against the reading" only, required: in words, the sentence-level
#              statement left owed (no model of the translated sentences and the named families,
#              with no other item of Γ)
#   fixture    optional, on a table whose sentences are another fixture's text than the entry's (its
#              `fixture`): that fixture, a directory of test/constructs/fixtures/. The indices of
#              `sentences` are axioms of that fixture's kompiled text, and the entry is listed under
#              it where its tables are listed by fixture (the form (r) tables below, K-coverage.md).
#              Without it the table's sentences are taken to be the entry's fixture's (not checked).
# The checks, each on the text of the named file (no Lean is run):
# - `form` is one of the four, `kind` one of the three for form (a) and absent, "through the
#   reading" or "sentence against the reading" for form (r), `family` given for "through the
#   reading" and for form (r), `sentences` a non-empty list of indices for forms (a) and (r)
#   (`[]` admitted on the supported `hook:` row's own form (a) table of kind "through the reading"),
#   `derivation` an existing file for form (b), `theorem` and `file` given for forms (a), (c) and
#   (r), `owed_refuted` on form (r) only, `consistent` and `owed_statement` given for kind
#   "sentence against the reading" and on no other table;
# - the theorem (and `owed_refuted`) is declared in the file, once, under that full name
#   (`namespace`/`section`/`end` tracked; comments removed);
# - neither the file's path nor a namespace of the theorem's name contains `AtNone`: such a theorem
#   may exist (a statement at the interpretation `HookParams.none`), and is never a row's evidence;
# - its statement (the text from the name to the top-level `:=`) is for every H, and so is that of
#   `owed_refuted`: it mentions H (a name bound in it at type `HookParams`, by a binder, `∀` or `∃`,
#   and used past its binder, or a `variable` of that type in scope that the statement mentions);
#   or, naming no `HookParams` and no `withHooks`, it is over every Semantics (a name bound in it at
#   type `Semantics` and used past its binder; `c.withHooks H` is a Semantics, so the statement holds
#   at it for every H); or it reads no semantics at all (it names no `Semantics`, no `HookParams`,
#   no `withHooks`, no `⊧`, no judgement that takes a semantics: SEM_READERS below). Under the last two,
#   it names no semantics the file declares (`def`/`abbrev NAME : Semantics`, or `….sem`), which
#   would make it a statement at that semantics' own H;
# - a form (a) statement does not mention `FnShape` (C7: no form (a) theorem is stated under
#   `FnShape` or a hypothesis of that kind);
# - a form (r) statement, and that of `owed_refuted`, has no hypothesis `FnHyp`: it mentions `FnHyp`
#   only as its whole conclusion `¬ FnHyp …` (the refutation of that owed fact), and nowhere else; a
#   hypothesis on the hook interpretation makes it a statement at some H, not for every H;
# - a kind "in a model" statement states an interpretation satisfying the theory with Step's steps:
#   it has an `∃`, a satisfaction of a theory (`⊧ᴵP`, or `InitModel`, whose field `sat` is one) and
#   mentions `Step`;
# - kind "sentence against the reading": the theorem's statement mentions Γ or Γc, a satisfaction
#   of a theory (`⊧ᴵP`) and a negation (`¬`): no model of that theory satisfies the sentence; one
#   that mentions Γc and not Γ names `Γcl` in `family`; `consistent` is
#   declared once in `file`, mentions H and `Consistent` and negates nothing (`¬`); the entry claims
#   no inconsistency: none of its `tie_theorems` is named `inconsistent` or, declared in a file of its
#   `tie`, states `¬ Consistent`.
# - `silent_statement` (rows-header.toml), on a supported E6 `hook:` row only: a non-empty list of
#   tables { theorem, file }, each checked as a form (c) table's theorem (declared once, no AtNone,
#   for every H as above).
# - a table's `fixture`: a directory of test/constructs/fixtures/, not the entry's own `fixture`, on a
#   table with `file` and non-empty `sentences`; the file reads that fixture's text (a `from "PATH"`
#   with PATH f2-examples/FIXTURE.kompile.kore, or a text that carries the Source of the fixture's own
#   fixtures/FIXTURE/FIXTURE.k), and each index of `sentences` is an axiom of each such text (1 to
#   its number of axioms, as AxiomDecl.index counts them).
# Prints the entries by form and kind (the counts C7 asks for: forms (b), (r) and "through the
# reading" counted apart), the fixtures of the form (r) entries (texts without a model: the table's
# `fixture`, else the entry's), and every failure. Exit 1 on a failure.
#
# Usage (from anywhere): test/provenance.sh [ROWS.toml]   (default test/constructs/rows.toml)
#                        test/provenance.sh --self-test   (the checks on cases written to a scratch
#                                                          directory under .lake: each is accepted or
#                                                          refused as expected)
set -u
K=$(cd "$(dirname "$0")/.." && pwd); cd "$K"
exec python3 -I - "$K" "${1:-test/constructs/rows.toml}" <<'PY'
import os, re, sys, tempfile, tomllib

K, arg = sys.argv[1], sys.argv[2]
FORMS = {"a", "b", "c", "r"}
KINDS = {"from sentences", "through the reading", "in a model"}
AGAINST = "sentence against the reading"
R_KINDS = (None, "through the reading", AGAINST)
HP = r"(?:KCore\.)?HookParams"
SEMT = r"(?:KCore\.)?Semantics"
SEM_READERS = ("Γ", "Γc", "Γstep", "Γcl", "Eval", "EvalTerm", "Step", "Holds", "hookRes", "sortOf", "sortsOf",
               "Consistent", "coreOK", "shapesOK", "floatShapeOK", "params", "fns", "lib", "sem",
               "withHooks", "HookParams", "Semantics", "FnHyp", "InitModel", "Config")
IDENT = r"[^\s(){}\[\]:,.⟨⟩]+"


def strip_comments(src):
    """Lean source without `--` line comments and (nested) `/- -/` block comments, string literals kept."""
    out, i, n, depth = [], 0, len(src), 0
    while i < n:
        if depth == 0 and src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            out.append(src[i:j + 1]); i = j + 1
        elif src.startswith("/-", i):
            depth += 1; i += 2
        elif depth and src.startswith("-/", i):
            depth -= 1; i += 2
        elif depth:
            out.append("\n" if src[i] == "\n" else ""); i += 1
        elif src.startswith("--", i):
            while i < n and src[i] != "\n":
                i += 1
        else:
            out.append(src[i]); i += 1
    return "".join(out)


def statement(src, start):
    """The text from `start` to the first `:=` (or `where`, or a line starting `|`) at bracket depth 0."""
    depth, i = 0, start
    while i < len(src):
        ch = src[i]
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        elif depth == 0:
            if src.startswith(":=", i):
                return src[start:i]
            if re.match(r"\swhere\b", src[i:i + 7]) or (ch == "\n" and re.match(r"\n\s*\|", src[i:i + 40])):
                return src[start:i]
        i += 1
    return src[start:]


def hook_binders(text):
    """(names bound at type HookParams, the text with those binders removed)."""
    names, rest = [], text
    for pat in (rf"[({{]\s*((?:{IDENT}\s+)*{IDENT})\s*:\s*{HP}\s*[)}}]",
                rf"[∀∃]\s*((?:{IDENT}\s+)*{IDENT})\s*:\s*{HP}\s*,"):
        for m in re.finditer(pat, rest):
            names += m.group(1).split()
        rest = re.sub(pat, " ", rest)
    return names, rest


def sem_binders(text):
    """(names bound at type Semantics, the text with those binders removed)."""
    names, rest = [], text
    for pat in (rf"[({{]\s*((?:{IDENT}\s+)*{IDENT})\s*:\s*{SEMT}\s*[)}}]",
                rf"[∀∃]\s*((?:{IDENT}\s+)*{IDENT})\s*:\s*{SEMT}\s*,"):
        for m in re.finditer(pat, rest):
            names += m.group(1).split()
        rest = re.sub(pat, " ", rest)
    return names, rest


def reads(name, text):
    """Whether `text` names `name`, also as a field or method (`c.sortOf`)."""
    return re.search(rf"(?<![\w'₀-₉]){re.escape(name)}(?![\w'₀-₉!?])", text) is not None


def every_h(stmt, var, fixed):
    """How the statement is for every H: "H" (it mentions a HookParams name), "every Semantics",
    "reads no semantics", or None. `fixed`: the names the file declares at type Semantics."""
    names, rest = hook_binders(stmt)
    if any(mentions(h, rest) for h in names) or any(mentions(v, stmt) for v in var):
        return "H"
    sn, srest = sem_binders(stmt)
    if reads("HookParams", stmt) or reads("withHooks", stmt) or any(mentions(x, stmt) for x in fixed if x not in sn) \
            or re.search(r"\.sem(?![\w'₀-₉!?])", stmt):
        return None
    if any(mentions(x, srest) for x in sn):
        return "every Semantics"
    if "⊧" not in stmt and not any(reads(x, stmt) for x in SEM_READERS):
        return "reads no semantics"
    return None


def mentions(name, text):
    return re.search(rf"(?<![\w.'₀-₉]){re.escape(name)}(?![\w'₀-₉!?])", text) is not None


def split_type(text):
    """(binders, type) of a statement: the text before and after its first `:` at bracket depth 0."""
    depth = 0
    for i, ch in enumerate(text):
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        elif depth == 0 and ch == ":" and not text.startswith(":=", i):
            return text[:i], text[i + 1:]
    return text, ""


def fn_hyp(stmt):
    """Whether the statement has `FnHyp` as a hypothesis: it mentions FnHyp other than as the head of
    its whole conclusion `¬ FnHyp …`."""
    binders, typ = split_type(stmt)
    m = re.match(r"\s*¬\s*\(?\s*FnHyp(?![\w'₀-₉!?])", typ)
    if m:
        depth, top = 0, []
        for ch in typ[m.end():]:
            depth += ch in "([{⟨"
            depth -= ch in ")]}⟩"
            top.append(ch if depth <= 0 else " ")
        if "→" in "".join(top):
            m = None
    rest = typ[m.end():] if m else typ
    return mentions("FnHyp", binders) or mentions("FnHyp", rest)


def declarations(path):
    """{full name: (namespaces, statement, HookParams variables in scope)} of the file's theorems and lemmas."""
    src = strip_comments(open(path, encoding="utf-8").read())
    scopes = []          # (kind, name parts, HookParams variable names)
    decls = {}
    tok = re.compile(r"^[ \t]*(?:(namespace)\s+(\S+)|(section)(?:[ \t]+(\S+))?[ \t]*$|(end)(?:[ \t]+(\S+))?[ \t]*$|"
                     r"(variable)\b|(?:@\[[^\]\n]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*"
                     r"(?:open\s[^\n]*?\bin\s+)?(theorem|lemma)\s+(\S+))", re.M)
    for m in tok.finditer(src):
        if m.group(1):
            scopes.append(("namespace", m.group(2).split("."), []))
        elif m.group(3):
            scopes.append(("section", [], []))
        elif m.group(5):
            if scopes:
                scopes.pop()
        elif m.group(7):
            line = src[m.end():src.find("\n", m.end())]
            names, _ = hook_binders(line)
            if scopes:
                scopes[-1][2].extend(names)
            else:
                scopes.append(("file", [], names))
        elif m.group(8):
            name = m.group(9)
            ns = [p for s in scopes for p in s[1]]
            full = name[len("_root_."):] if name.startswith("_root_.") else ".".join(ns + [name])
            var = [v for s in scopes for v in s[2]]
            decls.setdefault(full, []).append((ns + name.split(".")[:-1], statement(src, m.end()), var))
    return decls


def entries(node, where):
    if isinstance(node, dict):
        if "derived" in node:
            yield where, node
        for k, v in node.items():
            if k != "derived":
                yield from entries(v, f"{where} {k}" if where else k)
    elif isinstance(node, list):
        for i, v in enumerate(node):
            yield from entries(v, f"{where}[{i}]")


def check(rows, base):
    t = tomllib.load(open(rows, "rb"))
    cache, fixed, bad, counts, nomodel = {}, {}, [], {}, []
    hookrows = {f"E6 {k}" for k, v in (t.get("E6") or {}).items()
                if k.startswith("hook:") and isinstance(v, dict) and v.get("status") == "supported"}

    def theorem_ok(at, th, fl, path, what, form, kind=None, family=None):
        """The checks on a named theorem of `fl`: declared once, in no AtNone namespace, its statement
        mentioning H (for form (a), not FnShape; for form (r), not FnHyp). Returns its statement, or None."""
        if path not in cache:
            cache[path] = declarations(path)
        found = cache[path].get(th, [])
        if len(found) != 1:
            bad.append(f"{at}: {len(found)} theorems named {th} in {fl}, not one"); return None
        ns, stmt, var = found[0]
        if any("AtNone" in p for p in ns):
            bad.append(f"{at}: {th} is in a namespace named AtNone: never a row's evidence")
        if path not in fixed:
            fixed[path] = re.findall(r"^[ \t]*(?:noncomputable\s+)?(?:abbrev|def)\s+(\S+)\s*:\s*" + SEMT + r"\b",
                                     strip_comments(open(path, encoding="utf-8").read()), re.M)
        if every_h(stmt, var, fixed[path]) is None:
            bad.append(f"{at}: the statement of {what}{th} is not for every H (no name of type HookParams it"
                       " uses; not over every Semantics; reads a semantics)")
        if form == "a" and mentions("FnShape", stmt):
            bad.append(f"{at}: the form (a) theorem {th} is stated under FnShape")
        if form == "r" and what != "consistent " and fn_hyp(stmt):
            bad.append(f"{at}: the form (r) statement of {what}{th} mentions FnHyp other than as its"
                       " conclusion ¬ FnHyp (a hypothesis on H)")
        if kind == "in a model" and not ("∃" in stmt and ("⊧ᴵP" in stmt or mentions("InitModel", stmt))
                                         and mentions("Step", stmt)):
            bad.append(f"{at}: the kind 'in a model' theorem {th} states no interpretation satisfying the"
                       " theory with Step's steps (an ∃, ⊧ᴵP or InitModel, and Step)")
        if kind == AGAINST:
            if not ((mentions("Γ", stmt) or mentions("Γc", stmt)) and "⊧ᴵP" in stmt and "¬" in stmt):
                bad.append(f"{at}: the kind '{AGAINST}' theorem {th} states no refutation against Γ or Γc"
                           " (Γ or Γc, ⊧ᴵP and ¬)")
            elif mentions("Γc", stmt) and not mentions("Γ", stmt) and not (isinstance(family, str) and mentions("Γcl", family)):
                bad.append(f"{at}: the kind '{AGAINST}' theorem {th} is a refutation against Γc: it names Γcl in `family`")
        return stmt

    def tie_statement(name, e):
        """The statement of the theorem `name` in a file of the entry's `tie`, where one declares it once."""
        ts = e.get("tie")
        for fl in (ts if isinstance(ts, list) else [ts] if isinstance(ts, str) else []):
            path = os.path.join(base, fl) if isinstance(fl, str) else ""
            if not os.path.isfile(path):
                continue
            if path not in cache:
                cache[path] = declarations(path)
            found = cache[path].get(name, [])
            if len(found) == 1:
                return found[0][1]
        return None

    def against(at, d, e, fl, path):
        """Kind "sentence against the reading": `consistent` and `owed_statement`, and no claim of
        inconsistency among the entry's `tie_theorems`."""
        ow = d.get("owed_statement")
        if not (isinstance(ow, str) and ow.strip()):
            bad.append(f"{at}: kind '{AGAINST}' names no `owed_statement`, the sentence-level statement left owed")
        cs = d.get("consistent")
        if not isinstance(cs, str):
            bad.append(f"{at}: kind '{AGAINST}' names no `consistent`, the theorem that the reading has a model")
        elif path is not None:
            st = theorem_ok(at, cs, fl, path, "consistent ", "r")
            if st is not None and not (mentions("Consistent", st) and "¬" not in st):
                bad.append(f"{at}: the statement of consistent {cs} does not state Consistent (it mentions no"
                           " Consistent, or negates)")
        for n in (e.get("tie_theorems") or []):
            if not isinstance(n, str):
                continue
            st = tie_statement(n, e)
            if n.split(".")[-1] == "inconsistent" or (st is not None and re.search(r"¬\s*\(?\s*Consistent\b", st)):
                bad.append(f"{at}: kind '{AGAINST}' beside tie_theorems {n}, which claims the reading inconsistent")

    def fixture_ok(at, d, e):
        """A table's `fixture`: another fixture than the entry's, whose text the table's `file` reads
        and whose axioms the indices of `sentences` are."""
        fx = d["fixture"]
        if not (isinstance(fx, str) and fx and "/" not in fx
                and os.path.isdir(os.path.join(base, "test/constructs/fixtures", fx))):
            bad.append(f"{at}: `fixture` {fx!r} names no directory of test/constructs/fixtures"); return
        if fx == e.get("fixture"):
            bad.append(f"{at}: `fixture` {fx} is the entry's own fixture; it names another"); return
        ss, fl = d.get("sentences"), d.get("file")
        if not (isinstance(fl, str) and isinstance(ss, list) and ss and all(isinstance(x, int) for x in ss)):
            bad.append(f"{at}: `fixture` on a table without `file` and non-empty `sentences`"); return
        path = os.path.join(base, fl)
        if not os.path.isfile(path):
            return  # reported as no file
        src = re.compile(r'Source\((?:[^()"]*/)?fixtures/' + re.escape(fx) + "/" + re.escape(fx) + r"\.k\)")
        texts = {}
        for p in sorted(set(re.findall(r'\bfrom\s+"([^"]+)"', strip_comments(open(path, encoding="utf-8").read())))):
            q = os.path.join(base, p)
            body = open(q, encoding="utf-8").read() if os.path.isfile(q) else None
            if body is not None and (p == f"f2-examples/{fx}.kompile.kore" or src.search(body)):
                texts[p] = sum(1 for l in body.split("\n") if re.match(r"\s*axiom\s*\{", l))
        if not texts:
            bad.append(f"{at}: `fixture` {fx}: {fl} reads no text of it (f2-examples/{fx}.kompile.kore, or a"
                       f" text carrying the Source of fixtures/{fx}/{fx}.k)"); return
        out = [(x, p, n) for p, n in texts.items() for x in ss if not 1 <= x <= n]
        if out:
            x, p, n = out[0]
            bad.append(f"{at}: `fixture` {fx}: sentence {x} is no axiom of {p} ({n} axioms)")

    for where, e in entries(t, ""):
        ds = e["derived"]
        if not isinstance(ds, list) or not ds:
            bad.append(f"{where}: `derived` is not a non-empty list of tables"); continue
        for i, d in enumerate(ds):
            at = f"{where}: derived[{i}]"
            if not isinstance(d, dict):
                bad.append(f"{at}: not a table"); continue
            form, kind = d.get("form"), d.get("kind")
            if form not in FORMS:
                bad.append(f"{at}: carries no form (form {form!r}, not one of a, b, c, r)"); continue
            key = f"({form})" + (f" {kind}" if form == "a" or (form == "r" and kind is not None) else "")
            counts[key] = counts.get(key, 0) + 1
            if form == "r":
                nomodel.append((where, d.get("fixture") or e.get("fixture"), d.get("theorem")))
            if "fixture" in d:
                fixture_ok(at, d, e)
            if form in ("a", "r"):
                if form == "a" and kind not in KINDS:
                    bad.append(f"{at}: form (a) with kind {kind!r}, not 'from sentences', 'through the reading' or 'in a model'")
                if form == "r" and kind not in R_KINDS:
                    bad.append(f"{at}: form (r) with kind {kind!r}, not absent, 'through the reading' or '{AGAINST}'")
                if (form == "r" or kind == "through the reading") and not (isinstance(d.get("family"), str) and d["family"].strip()):
                    bad.append(f"{at}: " + ("form (r)" if form == "r" else "kind 'through the reading'") + " names no family")
                ss = d.get("sentences")
                prose = form == "a" and kind == "through the reading" and where in hookrows and ss == []
                if not prose and not (isinstance(ss, list) and ss and all(isinstance(x, int) and x >= 0 for x in ss)):
                    bad.append(f"{at}: form ({form}) without `sentences`, the indices of the sentences that determine it")
            elif kind is not None:
                bad.append(f"{at}: kind {kind!r} on form ({form}); kinds are forms (a) and (r)'s")
            ow = d.get("owed_refuted")
            if ow is not None and form != "r":
                bad.append(f"{at}: `owed_refuted` on form ({form}); it is form (r)'s")
            for fld in ("consistent", "owed_statement"):
                if d.get(fld) is not None and (form, kind) != ("r", AGAINST):
                    bad.append(f"{at}: `{fld}` on form ({form})" + (f" kind {kind!r}" if kind else "")
                               + f"; it is kind '{AGAINST}''s")
            if form == "b":
                dv = d.get("derivation")
                if not (isinstance(dv, str) and os.path.isfile(os.path.join(base, dv))):
                    bad.append(f"{at}: form (b) without an existing `derivation` file ({dv!r})")
            th, fl = d.get("theorem"), d.get("file")
            if th is None and form in ("a", "c", "r"):
                bad.append(f"{at}: form ({form}) names no theorem"); continue
            if th is None:
                continue
            if not (isinstance(th, str) and isinstance(fl, str)):
                bad.append(f"{at}: `theorem` without `file`"); continue
            if "AtNone" in fl:
                bad.append(f"{at}: {th} is in the file {fl}, named AtNone: never a row's evidence")
            path = os.path.join(base, fl)
            if not os.path.isfile(path):
                bad.append(f"{at}: no file {fl}")
                if (form, kind) == ("r", AGAINST):
                    against(at, d, e, fl, None)
                continue
            theorem_ok(at, th, fl, path, "", form, kind if form == "a" or (form, kind) == ("r", AGAINST) else None,
                       d.get("family"))
            if (form, kind) == ("r", AGAINST):
                against(at, d, e, fl, path)
            if ow is not None and form == "r":
                if not isinstance(ow, str):
                    bad.append(f"{at}: `owed_refuted` is not a theorem's full name")
                else:
                    theorem_ok(at, ow, fl, path, "owed_refuted ", form)
    def silent_tables(node, where):
        if isinstance(node, dict):
            if "silent_statement" in node:
                yield where, node
            for k, v in node.items():
                yield from silent_tables(v, f"{where} {k}" if where else k)
        elif isinstance(node, list):
            for i, v in enumerate(node):
                yield from silent_tables(v, f"{where}[{i}]")

    for where, e in silent_tables(t, ""):
        ss = e["silent_statement"]
        if where not in hookrows:
            bad.append(f"{where}: `silent_statement` on an entry that is no supported E6 hook: row"); continue
        if not (isinstance(ss, list) and ss and all(isinstance(x, dict) for x in ss)):
            bad.append(f"{where}: `silent_statement` is not a non-empty list of tables"); continue
        for i, d in enumerate(ss):
            at = f"{where}: silent_statement[{i}]"
            th, fl = d.get("theorem"), d.get("file")
            if not (isinstance(th, str) and isinstance(fl, str)):
                bad.append(f"{at}: names no `theorem` and `file`"); continue
            path = os.path.join(base, fl)
            if "AtNone" in fl or not os.path.isfile(path):
                bad.append(f"{at}: no file {fl}, or one named AtNone"); continue
            theorem_ok(at, th, fl, path, "", "c")
    return counts, bad, nomodel


def report(rows, base):
    counts, bad, nomodel = check(rows, base)
    total = sum(counts.values())
    print(f"provenance: {total} derivations named" + (": " + ", ".join(f"{k} {v}" for k, v in sorted(counts.items())) if total else ""))
    if nomodel:
        print(f"provenance: {len(nomodel)} of form (r), texts without a model: "
              + "; ".join(f"{w} (fixture {fx or 'none'}, {th})" for w, fx, th in nomodel))
    for b in bad[:40]:
        print(f"  {b}")
    if len(bad) > 40:
        print(f"  ... {len(bad) - 40} more")
    return bad


def self_test():
    d = tempfile.mkdtemp(prefix="provenance-", dir=os.path.join(K, ".lake"))
    lean = """namespace KCore.ProvT
-- theorem commented (H : HookParams) : True
/-- a docstring holding theorem nested (H : HookParams) -/
theorem good (H : HookParams) : ∀ y, ¬ Step (cH H) (XH H) y := sorry
theorem unused (H : HookParams) : Pre ⊧ φ := sorry
theorem atNoneOnly : Eval (c.withHooks HookParams.none) e none := sorry
theorem shape (hs : FnShape) (H : HookParams) : Pre H ⊧ φ := sorry
theorem pair : ∃ H₁ H₂ : HookParams, Eval (cH H₁) e v ∧ Eval (cH H₂) e w := sorry
theorem noModel (H : HookParams) : ¬ ∃ (M : Type) (_ : Inhabited M) (I : Interpretation Sym M), I ⊧ᴵP Pre H := sorry
theorem refuted (H : HookParams) : ¬ MatchIndependent (cH H) cl := sorry
theorem model (H : HookParams) : ∃ I : Interpretation KoreAML.Sym Elem, (I ⊧ᴵP (Γc (cH H) ∪ Γstep (cH H))) ∧
    (∀ x y : Config (cH H), Step (cH H) x y ↔ ¬ (I ⊧ᴵ (den x ⇒ ∼ den y))) ∧ I ⊧ᴵ φ := sorry
theorem modelInit (H : HookParams) : ∃ I, InitModel (cH H) N ar G I ∧ ∀ x y, Step (cH H) x y ↔ R I x y := sorry
theorem modelNoStep (H : HookParams) : ∃ I : Interpretation KoreAML.Sym Elem, I ⊧ᴵP (Γc (cH H)) ∧ I ⊧ᴵ φ := sorry
theorem against (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS ax).pat) := sorry
theorem againstC (H : HookParams) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation Sym M),
    I ⊧ᴵP Γc (cH H) → ¬ (I ⊧ᴵ (trS ax).pat) := sorry
theorem againstFn (H : HookParams) (hf : FnHyp (cH H)) : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation Sym M),
    I ⊧ᴵP Γ (cH H) → ¬ (I ⊧ᴵ (trS ax).pat) := sorry
theorem noModelFn (H : HookParams) (hf : FnHyp (cH H)) : ¬ ∃ (M : Type) (_ : Inhabited M) (I : Interpretation Sym M), I ⊧ᴵP Pre H := sorry
theorem refutedFn (H : HookParams) (hf : FnHyp (cH H)) : ¬ MatchIndependent (cH H) cl := sorry
theorem notFn (H : HookParams) : ¬ FnHyp (cH H) := sorry
theorem notFnImp (H : HookParams) : ¬ FnHyp (cH H) → ¬ MatchIndependent (cH H) cl := sorry
theorem consistent (H : HookParams) : Consistent (cH H) := sorry
theorem inconsistent (H : HookParams) : ¬ Consistent (cH H) := sorry
theorem noCons (H : HookParams) : ¬Consistent (cH H) := sorry
theorem overSem (c : Semantics) (i : Int) : c.sortOf (int i) = some Srt.int := sorry
theorem overSemImpl {c : Semantics} (hs : c.shapesOK = true) : ∀ f ∈ fs, ∃ v, hook f vs = some (some v) := sorry
theorem atConst (c : Semantics) : (c.withHooks (constH v)).sortOf x = some s := sorry
theorem atFixed (c : Semantics) : Γ c φ ∧ Γ cFix ψ := sorry
theorem atFixedSem : cDef.sem.sortOf x = some s := sorry
theorem semUnused (c : Semantics) : Γ cFix ψ := sorry
theorem noSem : ∀ f ∈ fs, ∀ vs : List GroundTerm, silent f vs = false := sorry
theorem readsFixed : ∀ f ∈ fs, silent f vs = false ∧ cFix.sortOf x = some s := sorry
theorem readsAnon : silentKey f = false ∧ Γ cX φ := sorry
theorem readsTheory : Pre ⊧ φ := sorry
theorem shadows (cFix : Semantics) (i : Int) : cFix.sortOf (int i) = some Srt.int := sorry
noncomputable def cFix : Semantics := default
section S
variable (H : HookParams)
theorem viaVar : Eval (cH H) e v := sorry
end S
namespace AtNone
theorem hidden (H : HookParams) : Eval (cH H) e v := sorry
theorem hiddenModel (H : HookParams) : ∃ I, InitModel (cH H) N ar G I ∧ ∀ x y, Step (cH H) x y ↔ R I x y := sorry
end AtNone
end KCore.ProvT
"""
    open(os.path.join(d, "T.lean"), "w").write(lean)
    open(os.path.join(d, "AtNoneT.lean"), "w").write("theorem KCore.q (H : HookParams) : Eval (cH H) e v := sorry\n")
    open(os.path.join(d, "hand.txt"), "w").write("step 1\n")
    f = os.path.relpath(os.path.join(d, "T.lean"), K)
    cases = [  # (derived table, the failure expected, or None)
        ({"form": "a", "kind": "through the reading", "family": "Γstep", "sentences": [155], "theorem": "KCore.ProvT.good", "file": f}, None),
        ({"form": "a", "kind": "from sentences", "sentences": [211], "theorem": "KCore.ProvT.viaVar", "file": f}, None),
        ({"form": "c", "theorem": "KCore.ProvT.pair", "file": f}, None),
        ({"form": "b", "derivation": os.path.relpath(os.path.join(d, "hand.txt"), K)}, None),
        ({"kind": "from sentences", "sentences": [1], "theorem": "KCore.ProvT.good", "file": f}, "carries no form"),
        ({"form": "a", "kind": "by eye", "sentences": [1], "theorem": "KCore.ProvT.good", "file": f}, "not 'from sentences'"),
        ({"form": "a", "kind": "through the reading", "sentences": [1], "theorem": "KCore.ProvT.good", "file": f}, "names no family"),
        ({"form": "a", "kind": "from sentences", "theorem": "KCore.ProvT.good", "file": f}, "without `sentences`"),
        ({"form": "a", "kind": "from sentences", "sentences": [1], "theorem": "KCore.ProvT.unused", "file": f}, "not for every H"),
        ({"form": "a", "kind": "from sentences", "sentences": [1], "theorem": "KCore.ProvT.atNoneOnly", "file": f}, "not for every H"),
        ({"form": "a", "kind": "from sentences", "sentences": [1], "theorem": "KCore.ProvT.shape", "file": f}, "under FnShape"),
        ({"form": "a", "kind": "from sentences", "sentences": [1], "theorem": "KCore.ProvT.AtNone.hidden", "file": f}, "namespace named AtNone"),
        ({"form": "c", "theorem": "KCore.q", "file": os.path.relpath(os.path.join(d, "AtNoneT.lean"), K)}, "named AtNone"),
        ({"form": "c", "theorem": "KCore.ProvT.commented", "file": f}, "0 theorems named"),
        ({"form": "c", "theorem": "KCore.ProvT.nested", "file": f}, "0 theorems named"),
        ({"form": "b", "derivation": "no/such/file"}, "without an existing `derivation`"),
        ({"form": "r", "sentences": [216, 217, 344], "family": "ΓDomains", "theorem": "KCore.ProvT.noModel", "file": f,
          "owed_refuted": "KCore.ProvT.refuted"}, None),
        ({"form": "r", "kind": "through the reading", "sentences": [344], "family": "ΓCons", "theorem": "KCore.ProvT.noModel", "file": f}, None),
        ({"form": "r", "sentences": [344], "theorem": "KCore.ProvT.noModel", "file": f}, "form (r) names no family"),
        ({"form": "r", "family": "ΓCons", "theorem": "KCore.ProvT.noModel", "file": f}, "form (r) without `sentences`"),
        ({"form": "r", "kind": "from sentences", "sentences": [344], "family": "ΓCons", "theorem": "KCore.ProvT.noModel", "file": f}, "form (r) with kind"),
        ({"form": "r", "sentences": [344], "family": "ΓCons"}, "form (r) names no theorem"),
        ({"form": "r", "sentences": [344], "family": "ΓCons", "theorem": "KCore.ProvT.unused", "file": f}, "not for every H"),
        ({"form": "r", "sentences": [344], "family": "ΓCons", "theorem": "KCore.ProvT.noModel", "file": f,
          "owed_refuted": "KCore.ProvT.unused"}, "statement of owed_refuted"),
        ({"form": "r", "sentences": [344], "family": "ΓCons", "theorem": "KCore.ProvT.noModel", "file": f,
          "owed_refuted": "KCore.ProvT.missing"}, "0 theorems named KCore.ProvT.missing"),
        ({"form": "a", "kind": "from sentences", "sentences": [1], "theorem": "KCore.ProvT.good", "file": f,
          "owed_refuted": "KCore.ProvT.refuted"}, "`owed_refuted` on form (a)"),
        ({"form": "a", "kind": "in a model", "sentences": [281, 283], "theorem": "KCore.ProvT.model", "file": f}, None),
        ({"form": "a", "kind": "in a model", "sentences": [93], "theorem": "KCore.ProvT.modelInit", "file": f}, None),
        ({"form": "a", "kind": "in a model", "sentences": [93], "theorem": "KCore.ProvT.modelNoStep", "file": f},
         "states no interpretation satisfying"),
        ({"form": "a", "kind": "in a model", "sentences": [93], "theorem": "KCore.ProvT.good", "file": f},
         "states no interpretation satisfying"),
        ({"form": "a", "kind": "in a model", "theorem": "KCore.ProvT.model", "file": f}, "without `sentences`"),
        ({"form": "a", "kind": "in a model", "sentences": [1], "theorem": "KCore.ProvT.AtNone.hiddenModel", "file": f},
         "namespace named AtNone"),
        ({"form": "c", "kind": "in a model", "theorem": "KCore.ProvT.pair", "file": f}, "kinds are forms (a) and (r)'s"),
    ]
    ag = {"form": "r", "kind": "sentence against the reading", "sentences": [78, 86, 142], "family": "ΓDomains",
          "theorem": "KCore.ProvT.against", "file": f, "consistent": "KCore.ProvT.consistent",
          "owed_statement": "no model of sentences 78, 86, 142 and the families named, with no other item of Γ"}
    agw = lambda **kw: {k: v for k, v in dict(ag, **kw).items() if v is not None}
    tie = {"tie": [f], "tie_theorems": ["KCore.ProvT.consistent"]}
    cases += [  # kind "sentence against the reading" (third item: fields of the entry beside `derived`)
        (agw(), None),
        (agw(), None, tie),
        (agw(owed_refuted="KCore.ProvT.refuted"), None),
        (agw(family=None), "form (r) names no family"),
        (agw(consistent=None), "names no `consistent`"),
        (agw(owed_statement=None), "names no `owed_statement`"),
        (agw(consistent="KCore.ProvT.inconsistent"), "does not state Consistent"),
        (agw(consistent="KCore.ProvT.missing"), "0 theorems named KCore.ProvT.missing"),
        (agw(theorem="KCore.ProvT.noModel"), "states no refutation against Γ"),
        (agw(theorem="KCore.ProvT.againstC", family="ΓDomains, Γcl"), None),
        (agw(theorem="KCore.ProvT.againstC"), "names Γcl in `family`"),
        (agw(theorem="KCore.ProvT.againstC", family="ΓDomains, Γclosed"), "names Γcl in `family`"),
        (agw(theorem="KCore.ProvT.againstFn"), "mentions FnHyp"),
        (agw(owed_refuted="KCore.ProvT.refutedFn"), "statement of owed_refuted KCore.ProvT.refutedFn mentions FnHyp"),
        ({"form": "r", "sentences": [344], "family": "ΓCons", "theorem": "KCore.ProvT.noModelFn", "file": f}, "mentions FnHyp"),
        ({"form": "r", "sentences": [344], "family": "ΓCons", "theorem": "KCore.ProvT.noModel", "file": f,
          "owed_refuted": "KCore.ProvT.notFn"}, None),
        ({"form": "r", "sentences": [344], "family": "ΓCons", "theorem": "KCore.ProvT.noModel", "file": f,
          "owed_refuted": "KCore.ProvT.notFnImp"}, "mentions FnHyp"),
        (agw(), "claims the reading inconsistent", {"tie": [f], "tie_theorems": ["KCore.ProvT.inconsistent"]}),
        (agw(), "claims the reading inconsistent", {"tie": [f], "tie_theorems": ["KCore.ProvT.noCons"]}),
        ({"form": "r", "sentences": [344], "family": "ΓCons", "theorem": "KCore.ProvT.noModel", "file": f,
          "consistent": "KCore.ProvT.consistent"}, "`consistent` on form (r)"),
        ({"form": "r", "kind": "through the reading", "sentences": [344], "family": "ΓCons", "theorem": "KCore.ProvT.noModel",
          "file": f, "owed_statement": "x"}, "`owed_statement` on form (r) kind"),
    ]
    hk = ("E6", "hook:K.x:Lblx")
    pr = {"form": "a", "kind": "through the reading", "family": "ΓDomains", "sentences": [], "theorem": "KCore.ProvT.good", "file": f}
    cases += [  # a supported hook row's prose value (fourth item: the list and key of the row)
        (pr, None, {}, hk),
        (pr, "without `sentences`", {}),
        (pr, "cases[0]: derived[0]: form (a) without `sentences`", {"cases": [{"case": "n", "status": "supported", "derived": [pr]}]}, hk),
        (dict(pr, kind="from sentences"), "without `sentences`", {}, hk),
        (pr, "without `sentences`", {"status": "parameter"}, hk),
    ]
    sa = lambda th: {"form": "a", "kind": "from sentences", "sentences": [1], "theorem": f"KCore.ProvT.{th}", "file": f}
    cases += [  # statements for every H without a HookParams name
        (sa("overSem"), None),
        (sa("overSemImpl"), None),
        (sa("noSem"), None),
        (sa("atConst"), "not for every H"),
        (sa("atFixed"), "not for every H"),
        (sa("atFixedSem"), "not for every H"),
        (sa("semUnused"), "not for every H"),
        (sa("readsFixed"), "not for every H"),
        (sa("readsAnon"), "not for every H"),
        (sa("readsTheory"), "not for every H"),
        (sa("shadows"), None),
        (pr, None, {"silent_statement": [{"theorem": "KCore.ProvT.noSem", "file": f}]}, hk),
        (pr, None, {"silent_statement": [{"theorem": "KCore.ProvT.good", "file": f}]}, hk),
        (pr, "silent_statement[0]: the statement of KCore.ProvT.atFixed is not for every H",
         {"silent_statement": [{"theorem": "KCore.ProvT.atFixed", "file": f}]}, hk),
        (pr, "silent_statement[0]: 0 theorems named", {"silent_statement": [{"theorem": "KCore.ProvT.missing", "file": f}]}, hk),
        (pr, "not a non-empty list", {"silent_statement": []}, hk),
        (sa("good"), "no supported E6 hook: row", {"silent_statement": [{"theorem": "KCore.ProvT.noSem", "file": f}]}),
    ]
    # a table's `fixture` (fixtures of test/constructs/fixtures, read by name; the text by its Source in S.kore)
    sk = os.path.relpath(os.path.join(d, "S.kore"), K)
    src = "Source(kcore-spec/test/constructs/fixtures/e3-ml-eq-rhs-or-total/e3-ml-eq-rhs-or-total.k)"
    open(os.path.join(d, "S.kore"), "w").write(
        f"[org'Stop'kframework'Stop'attributes'Stop'Source{{}}(\"{src}\")]\nmodule M\n"
        "  axiom{R} \\top{R}() []\n  axiom{R} \\top{R}() []\n\n  axiom{R} \\top{R}() []\nendmodule []\n")
    open(os.path.join(d, "F.lean"), "w").write(
        'namespace KCore.ProvF\n-- kore_term k0 from "f2-examples/c3-anywhere-ctor.kompile.kore"\n'
        'kore_term kore from "f2-examples/e5-ovl-fun.kompile.kore"\n'
        "theorem lit (H : HookParams) : Eval (cH H) e v := sorry\n"
        "theorem noModel (H : HookParams) : ¬ ∃ (M : Type) (_ : Inhabited M) (I : Interpretation Sym M), I ⊧ᴵP Pre H := sorry\n"
        "end KCore.ProvF\n")
    open(os.path.join(d, "G.lean"), "w").write(
        f'namespace KCore.ProvG\ndefinition_of defn from "{sk}"\n'
        "theorem src (H : HookParams) : Eval (cH H) e v := sorry\nend KCore.ProvG\n")
    ff, fg = (os.path.relpath(os.path.join(d, x), K) for x in ("F.lean", "G.lean"))
    fa = lambda fx, ss, th="KCore.ProvF.lit", fl=ff: {"form": "a", "kind": "from sentences", "sentences": ss,
                                                     "theorem": th, "file": fl, "fixture": fx}
    own = {"fixture": "c3-anywhere-ctor"}
    cases += [
        (fa("e5-ovl-fun", [1, 2]), None, own),
        (fa("e5-ovl-fun", [1]), None),
        (fa("e3-ml-eq-rhs-or-total", [1, 3], "KCore.ProvG.src", fg), None, own),
        (fa("e3-ml-eq-rhs-or-total", [3, 4], "KCore.ProvG.src", fg), "sentence 4 is no axiom of", own),
        (fa("e5-ovl-fun", [1, 100000]), "sentence 100000 is no axiom of f2-examples/e5-ovl-fun.kompile.kore", own),
        (fa("c3-anywhere-ctor", [1]), "reads no text of it"),
        (fa("e5-ovl-fun", [1], "KCore.ProvG.src", fg), "reads no text of it", own),
        (fa("c3-anywhere-ctor", [1]), "is the entry's own fixture", own),
        (fa("no-such-fixture", [1]), "names no directory of test/constructs/fixtures", own),
        (fa("../constructs", [1]), "names no directory of test/constructs/fixtures", own),
        ({"form": "c", "theorem": "KCore.ProvT.pair", "file": f, "fixture": "e5-ovl-fun"},
         "`fixture` on a table without `file` and non-empty `sentences`", own),
        ({"form": "r", "sentences": [105], "family": "ΓCons", "theorem": "KCore.ProvF.noModel", "file": ff,
          "fixture": "e5-ovl-fun"}, None, own),
    ]
    ok = True
    val = lambda v: (f"{v!r}".replace("'", '"') if not isinstance(v, (list, dict)) else
                     "[" + ", ".join(val(x) for x in v) + "]" if isinstance(v, list) else
                     "{ " + ", ".join(f"{k} = {val(x)}" for k, x in v.items()) + " }")
    for i, (dt, want, *more) in enumerate(cases):
        rp = os.path.join(d, f"rows{i}.toml")
        fields = dict(more[0]) if more else {}
        st = fields.pop("status", "supported")
        lst, key = more[1] if len(more) > 1 else ("E2", "row")
        extra = "".join(f", {k} = {val(v)}" for k, v in fields.items())
        with open(rp, "w") as o:
            o.write(f"[{lst}]\n\"{key}\" = {{ status = \"{st}\"" + extra + ", derived = [{ "
                    + ", ".join(f"{k} = {val(v)}" for k, v in dt.items())
                    + " }] }\n")
        _, bad, nomodel = check(rp, K)
        if (want is None and bad) or (want is not None and (len(bad) != 1 or want not in bad[0])):
            ok = False
            print(f"self-test case {i}: expected {want!r}, got {bad}")
        # a form (r) table is listed under its own `fixture`, else under the entry's
        fx = [dt.get("fixture") or fields.get("fixture")] if dt.get("form") == "r" else []
        if [x for _, x, _ in nomodel] != fx:
            ok = False
            print(f"self-test case {i}: form (r) listed under {[x for _, x, _ in nomodel]}, expected {fx}")
    for x in os.listdir(d):
        os.remove(os.path.join(d, x))
    os.rmdir(d)
    print(f"provenance self-test: {len(cases)} cases, " + ("each as expected" if ok else "some not as expected"))
    return ok


if arg == "--self-test":
    sys.exit(0 if self_test() else 1)
sys.exit(1 if report(arg if os.path.isabs(arg) else os.path.join(K, arg), K) else 0)
PY
