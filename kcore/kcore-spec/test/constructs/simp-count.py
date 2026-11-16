"""SIMP (DONE-0 section 2.1; REVIEW-RN finding 4): the [simplification] axioms of a corpus of
kompiled texts that can state something where a function's equations leave the point open.

Usage: python3 -I simp-count.py DEFS_DIR INDEX_JSON [EXCLUDE_REGEX]

DEFS_DIR holds the corpus's distinct definition.kore files (test/corpus.py's .lake/corpus/defs),
INDEX_JSON says which cache entries (labels) hold each. Texts whose every label matches
EXCLUDE_REGEX (default: the upstream semantics, wasm, mir, evm-equivalence, kevm) are left out.

Counted: every axiom of a text's last module carrying `simplification`, whose Source is not K's
builtin directory (the library's lemmas are its own; E6 rows them). Its conclusion is the
`\\equals` under the axiom's `\\implies` (or the axiom itself); the left side classifies it:
  ceil      \\ceil(f(...)) with f a function symbol of the text;
  fn-req    f(...) with f a function symbol, the premise's first conjunct (the requires) not \\top;
  fn        f(...) with f a function symbol and no requires;
  other     anything else (an injection, a constructor, a predicate pattern).
f's kind: `eqs` (a function with equations in the text that are not simplifications), `hooked`
(declared hooked-symbol: the registry or a parameter gives its values), `none` (a function with no
equation: a parameter). A lemma of class ceil, fn-req or fn about an `eqs` function speaks at a
failing-clause point when some argument satisfying its premise makes every equation fail: this
script does not decide that (it needs the equations' evaluation); it counts the candidates.
"""
import json, os, re, sys
from collections import Counter, defaultdict

defs, index = sys.argv[1:3]
excl = re.compile(sys.argv[3] if len(sys.argv) > 3 else r"wasm|mir|evm|kevm")
idx = json.load(open(index))


def tokens(s):
    i, n = 0, len(s)
    while i < n:
        c = s[i]
        if c.isspace(): i += 1; continue
        if c in "{}(),:": yield c; i += 1; continue
        if c == '"':
            j = i + 1
            while s[j] != '"': j += 2 if s[j] == "\\" else 1
            yield s[i:j + 1]; i = j + 1; continue
        j = i
        while j < n and not s[j].isspace() and s[j] not in "{}(),:": j += 1
        yield s[i:j]; i = j


def parse(toks, pos=0):
    """pattern := name ('{' sorts '}')? ('(' patterns ')')? | name ':' sort | string. Returns (node, pos)."""
    t = toks[pos]
    if t.startswith('"'): return ("str", t), pos + 1
    name, pos = t, pos + 1
    if pos < len(toks) and toks[pos] == ":":
        depth, p = 0, pos + 1
        # the sort: name ('{' ... '}')?
        p += 1
        if p < len(toks) and toks[p] == "{":
            depth = 1; p += 1
            while depth:
                depth += toks[p] == "{"; depth -= toks[p] == "}"; p += 1
        return ("var", name), p
    if pos < len(toks) and toks[pos] == "{":
        depth = 1; pos += 1
        while depth:
            depth += toks[pos] == "{"; depth -= toks[pos] == "}"; pos += 1
    args = []
    if pos < len(toks) and toks[pos] == "(":
        pos += 1
        while toks[pos] != ")":
            a, pos = parse(toks, pos); args.append(a)
            if toks[pos] == ",": pos += 1
        pos += 1
    return ("app", name, args), pos


def sentences(text):
    mainmod = text[text.rindex("\nmodule "):]
    out, cur = [], None
    for l in mainmod.split("\n"):
        if l.lstrip().startswith("//"): continue
        if re.match(r"\s+(sort|hooked-sort|symbol|hooked-symbol|claim|alias|import) ", l) or re.match(r"\s+axiom\s*\{", l):
            if cur: out.append(cur)
            cur = l.strip()
        elif l.startswith("endmodule"):
            if cur: out.append(cur)
            cur = None
        elif cur is not None:
            cur += "\n" + l
    return out


def split_atts(s):
    """(body, attributes) of a sentence: the last top-level [...]."""
    depth, q = 0, False
    for i in range(len(s) - 1, -1, -1):
        c = s[i]
        if c == "]" and not q: depth += 1
        if c == "[" and not q:
            depth -= 1
            if depth == 0: return s[:i], s[i:]
    return s, ""


totals, per_text = Counter(), defaultdict(Counter)
examples = defaultdict(list)
texts = 0
for fn in sorted(os.listdir(defs)):
    h = fn[:-5]
    labels = {e.get("label", "") for e in idx.get(h, [])}
    if labels and all(excl.search(l) for l in labels): continue
    texts += 1
    sents = sentences(open(os.path.join(defs, fn)).read())
    fun, hooked, eqheads = set(), set(), Counter()
    parsed = []
    for s in sents:
        body, atts = split_atts(s)
        if body.startswith(("symbol", "hooked-symbol")):
            m = re.match(r"(hooked-)?symbol (\S+?)\{", body)
            if "function{}()" in atts: fun.add(m.group(2))
            if m.group(1): hooked.add(m.group(2))
        elif body.startswith("axiom"):
            b = body[body.index("}") + 1:].strip()
            try:
                node, _ = parse(list(tokens(b)))
            except (IndexError, ValueError):
                continue
            parsed.append((node, atts))
    def concl(node):
        if node[0] == "app" and node[1] == "\\implies":
            prem, c = node[2]
            req = prem[2][0] if prem[0] == "app" and prem[1] == "\\and" and prem[2] else prem
            return req, c
        return None, node
    for node, atts in parsed:
        if "simplification{}(" in atts: continue
        req, c = concl(node)
        if c[0] == "app" and c[1] == "\\equals" and c[2] and c[2][0][0] == "app":
            eqheads[c[2][0][1]] += 1
    for node, atts in parsed:
        if "simplification{}(" not in atts or "/include/kframework/builtin/" in atts: continue
        req, c = concl(node)
        lhs = c[2][0] if c[0] == "app" and c[1] == "\\equals" and c[2] else c
        cls, f = "other", None
        if lhs[0] == "app" and lhs[1] == "\\ceil" and lhs[2] and lhs[2][0][0] == "app" and lhs[2][0][1] in fun:
            cls, f = "ceil", lhs[2][0][1]
        elif lhs[0] == "app" and lhs[1] in fun:
            f = lhs[1]
            has_req = req is not None and not (req[0] == "app" and req[1] == "\\top")
            cls = "fn-req" if has_req else "fn"
        kind = "-" if f is None else ("hooked" if f in hooked else ("eqs" if eqheads[f] else "none"))
        totals[(cls, kind)] += 1
        per_text[h][(cls, kind)] += 1
        if cls != "other" and len(examples[(cls, kind)]) < 3:
            examples[(cls, kind)].append(f"{h} {f}")

print(f"texts read: {texts} (left out by label: {len(os.listdir(defs)) - texts})")
print("user [simplification] axioms by class and head kind (axioms / texts):")
for k in sorted(totals):
    nt = sum(1 for c in per_text.values() if c[k])
    print(f"  {k[0]:7} {k[1]:7} {totals[k]:6} / {nt}" + (f"   e.g. {'; '.join(examples[k])}" if examples[k] else ""))
cand = sum(v for (c, kd), v in totals.items() if c != "other" and kd == "eqs")
for k in sorted(totals):
    if k[0] != "other" and k[1] != "hooked":
        hs = [h for h, c in per_text.items() if c[k]]
        print(f"  {k[0]} {k[1]} labels: " + ", ".join(sorted({e.get("label", "?") for h in hs for e in idx.get(h, [])[:1]})))
print(f"candidates (ceil, fn-req or fn about a function with equations): {cand} axioms in "
      f"{sum(1 for c in per_text.values() if any(v for (cl, kd), v in c.items() if cl != 'other' and kd == 'eqs'))} texts")
