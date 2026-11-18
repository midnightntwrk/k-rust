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
#              the sentence-level statement owed)
#   family     kind "through the reading": the family the expectation goes through (`Γstep`, the
#              premise ⌈rhs ∧ ens⌉, ...); form (r): the families of the reading the refutation uses
#              beside the sentences, each named (always required: no refutation is from sentences
#              alone where a family carries a fact no sentence states)
#   sentences  forms (a) and (r): the indices of the text's sentences that determine the
#              expectation (that the refutation uses)
#   theorem    the theorem's full name (namespaces included); required for forms (a), (c) and (r)
#   file       the Lean file holding it, relative to kcore-spec; required with `theorem`
#   derivation form (b): the file holding the derivation, relative to kcore-spec
#   owed_refuted  form (r) only, optional: the full name of a theorem of `file` refuting the fact
#              the package names as owed for the construct (it is false of this text)
# The checks, each on the text of the named file (no Lean is run):
# - `form` is one of the four, `kind` one of the three for form (a) and absent or "through the
#   reading" for form (r), `family` given for "through the reading" and for form (r), `sentences` a
#   non-empty list of indices for forms (a) and (r), `derivation` an existing file for form (b),
#   `theorem` and `file` given for forms (a), (c) and (r), `owed_refuted` on form (r) only;
# - the theorem (and `owed_refuted`) is declared in the file, once, under that full name
#   (`namespace`/`section`/`end` tracked; comments removed);
# - neither the file's path nor a namespace of the theorem's name contains `AtNone`: such a theorem
#   may exist (a statement at the interpretation `HookParams.none`), and is never a row's evidence;
# - its statement (the text from the name to the top-level `:=`) mentions H, and so does that of
#   `owed_refuted`: a name bound in it at
#   type `HookParams` (by a binder, `∀` or `∃`) and used past its binder, or a `variable` of that
#   type in scope that the statement mentions;
# - a form (a) statement does not mention `FnShape` (C7: no form (a) theorem is stated under
#   `FnShape` or a hypothesis of that kind);
# - a kind "in a model" statement states an interpretation satisfying the theory with Step's steps:
#   it has an `∃`, a satisfaction of a theory (`⊧ᴵP`, or `InitModel`, whose field `sat` is one) and
#   mentions `Step`.
# Prints the entries by form and kind (the counts C7 asks for: forms (b), (r) and "through the
# reading" counted apart), the fixtures of the form (r) entries (texts without a model), and every
# failure. Exit 1 on a failure.
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
HP = r"(?:KCore\.)?HookParams"
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


def mentions(name, text):
    return re.search(rf"(?<![\w.'₀-₉]){re.escape(name)}(?![\w'₀-₉!?])", text) is not None


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
    cache, bad, counts, nomodel = {}, [], {}, []

    def theorem_ok(at, th, fl, path, what, form, kind=None):
        """The checks on a named theorem of `fl`: declared once, in no AtNone namespace, its statement
        mentioning H (and, for form (a), not FnShape)."""
        if path not in cache:
            cache[path] = declarations(path)
        found = cache[path].get(th, [])
        if len(found) != 1:
            bad.append(f"{at}: {len(found)} theorems named {th} in {fl}, not one"); return
        ns, stmt, var = found[0]
        if any("AtNone" in p for p in ns):
            bad.append(f"{at}: {th} is in a namespace named AtNone: never a row's evidence")
        names, rest = hook_binders(stmt)
        if not (any(mentions(h, rest) for h in names) or any(mentions(v, stmt) for v in var)):
            bad.append(f"{at}: the statement of {what}{th} does not mention H (no name of type HookParams it uses)")
        if form == "a" and mentions("FnShape", stmt):
            bad.append(f"{at}: the form (a) theorem {th} is stated under FnShape")
        if kind == "in a model" and not ("∃" in stmt and ("⊧ᴵP" in stmt or mentions("InitModel", stmt))
                                         and mentions("Step", stmt)):
            bad.append(f"{at}: the kind 'in a model' theorem {th} states no interpretation satisfying the"
                       " theory with Step's steps (an ∃, ⊧ᴵP or InitModel, and Step)")

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
                nomodel.append((where, e.get("fixture"), d.get("theorem")))
            if form in ("a", "r"):
                if form == "a" and kind not in KINDS:
                    bad.append(f"{at}: form (a) with kind {kind!r}, not 'from sentences', 'through the reading' or 'in a model'")
                if form == "r" and kind not in (None, "through the reading"):
                    bad.append(f"{at}: form (r) with kind {kind!r}, not absent or 'through the reading'")
                if (form == "r" or kind == "through the reading") and not (isinstance(d.get("family"), str) and d["family"].strip()):
                    bad.append(f"{at}: " + ("form (r)" if form == "r" else "kind 'through the reading'") + " names no family")
                ss = d.get("sentences")
                if not (isinstance(ss, list) and ss and all(isinstance(x, int) and x >= 0 for x in ss)):
                    bad.append(f"{at}: form ({form}) without `sentences`, the indices of the sentences that determine it")
            elif kind is not None:
                bad.append(f"{at}: kind {kind!r} on form ({form}); kinds are forms (a) and (r)'s")
            ow = d.get("owed_refuted")
            if ow is not None and form != "r":
                bad.append(f"{at}: `owed_refuted` on form ({form}); it is form (r)'s")
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
                bad.append(f"{at}: no file {fl}"); continue
            theorem_ok(at, th, fl, path, "", form, kind if form == "a" else None)
            if ow is not None and form == "r":
                if not isinstance(ow, str):
                    bad.append(f"{at}: `owed_refuted` is not a theorem's full name")
                else:
                    theorem_ok(at, ow, fl, path, "owed_refuted ", form)
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
        ({"form": "a", "kind": "from sentences", "sentences": [1], "theorem": "KCore.ProvT.unused", "file": f}, "does not mention H"),
        ({"form": "a", "kind": "from sentences", "sentences": [1], "theorem": "KCore.ProvT.atNoneOnly", "file": f}, "does not mention H"),
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
        ({"form": "r", "sentences": [344], "family": "ΓCons", "theorem": "KCore.ProvT.unused", "file": f}, "does not mention H"),
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
    ok = True
    for i, (dt, want) in enumerate(cases):
        rp = os.path.join(d, f"rows{i}.toml")
        with open(rp, "w") as o:
            o.write("[E2]\n\"row\" = { status = \"supported\", derived = [{ "
                    + ", ".join(f"{k} = {v!r}".replace("'", '"') if not isinstance(v, list) else f"{k} = {v}" for k, v in dt.items())
                    + " }] }\n")
        _, bad, _ = check(rp, K)
        got = bad[0] if bad else None
        if (want is None and bad) or (want is not None and (len(bad) != 1 or want not in bad[0])):
            ok = False
            print(f"self-test case {i}: expected {want!r}, got {bad}")
    for x in os.listdir(d):
        os.remove(os.path.join(d, x))
    os.rmdir(d)
    print(f"provenance self-test: {len(cases)} cases, " + ("each as expected" if ok else "some not as expected"))
    return ok


if arg == "--self-test":
    sys.exit(0 if self_test() else 1)
sys.exit(1 if report(arg if os.path.isabs(arg) else os.path.join(K, arg), K) else 0)
PY
