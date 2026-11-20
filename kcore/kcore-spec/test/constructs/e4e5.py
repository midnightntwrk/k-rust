"""The nodes of E4 (the KORE grammar's productions and the reader's syntax-tree constructors) and the
translation sites of E5 (ModuleToKORE's emit sites) that a fixture's text holds, by a parse of the
text (DONE-0 C2: a K-level row's KORE consists of E4/E5 rows; each supported E4 and E5 row names a
fixture whose text holds its node).

The text of a fixture: its kore.txt (the sentences its K text adds to an empty module, each after a
line `//@ N`, between the main module's `module` and `endmodule` lines), or, for a `kore` fixture
(fixture.toml `kore = PATH`: a hand-written KORE text), the whole definition at PATH. The parse
follows the grammar of haskell-backend/docs/kore-syntax.md as the rows of E4 spell it: a sentence,
pattern, sort and attribute list each records the productions it is an instance of (rows.toml E4
keys `grammar:...`) and the syntax-tree constructor it is (test/ConstructsE4.lean's keys
`tree:...`, the strings that file's functions return). A text that does not parse is reported, not
read. An E5 site is recognised by the form ModuleToKORE.java writes there:
  translateSorts:sort#1        a `sort` declaration
  translateSorts:hooked-#1     a `hooked-sort` whose hook is a collection's (SET.Set, MAP.Map,
                               LIST.List, RANGEMAP.RangeMap: ModuleToKORE.java:201-205)
  translateSorts:hooked-#2     a `hooked-sort` with another hook
  translateSymbol:symbol#1     a `symbol` declaration
  genOverloadedAxiom:axiom#1   an axiom with the attribute symbol-overload
  convertRule:axiom#1          an equation (ModuleToKORE.java:1127): an axiom with sort variables
                               whose attributes hold UNIQUE'Unds'ID (a rule's) and whose body is
                               no \\rewrites
  convertRule:axiom#2          a rewrite rule (ModuleToKORE.java:1333): `axiom{}` whose body is a
                               \\rewrites
  functionalPattern:axiom#1    an axiom with the attribute functional or subsort whose body is an
                               \\exists (ModuleToKORE.java:1588)
  genIdemAxiom:axiom#1         an axiom with the attribute idem whose body is an \\equals
                               (ModuleToKORE.java's genIdemAxiom: `f(K, K) = K` of a symbol with idem)
  genAssocAxiom:axiom#1        an axiom with the attribute assoc whose body is an \\equals
                               (`f(f(K1, K2), K3) = f(K1, f(K2, K3))` of a symbol with assoc)

An entry with `node_sentence` (rows-header.toml) is looked up in its fixture's kompiled definition
instead: the text kompile.txt's `definition.kore sha256` names, from kfix.py's cache (this tree's
.lake/kfix, else $KCORE_KFIX_CACHE), parsed whole; the node must be held by a sentence whose first
line contains the string. It is for a sentence kore.txt leaves out (a builtin file's, whose Source
is K's), and it locates the one sentence, since every kompiled definition holds the library's; or
for the definition's own productions (`<definition>`, `<modules>`), which no kore.txt holds: a
string in the definition's first line (its attribute list) locates those two and nothing else.

Usage (from kcore-spec):
  python3 -I test/constructs/e4e5.py find [--write] [ROWS.toml]
      for each supported E4 and E5 row, the fixture whose text holds its node: the first of the
      fixtures (the order below) whose account refuses nothing and whose text holds it; prints each
      row's fixture and sentence, and the rows no fixture holds; --write records them in rows.toml
      (fields fixture and sentence, the sentence the first line of the sentence holding the node)
  python3 -I test/constructs/e4e5.py check [ROWS.toml]
      each supported E4 and E5 row and `cases` entry naming a fixture: the fixture's text (or, with
      node_sentence, the sentence of its kompiled definition) holds the row's node; exit 1 otherwise
  python3 -I test/constructs/e4e5.py --self-test
      the parse of small texts, each node found or not as expected
The order of the fixtures for find: those the FIX-rest tie tickets tie first (PREFER, in that
order: their tie is the one these rows then name), then the kompiled fixtures by the size of their
kore.txt and name, then the `kore` fixtures by the size of their text and name (a node no kompiled
fixture's kore.txt holds: the definition's attributes and module list, a library sentence).
"""
import os, re, sys, tomllib

HERE = os.path.dirname(os.path.abspath(__file__))
K = os.path.dirname(os.path.dirname(HERE))
FXDIR = os.path.join(HERE, "fixtures")
PREFER = ["base", "e1-module", "e1-sentences", "e1-syntax", "e1-tag", "e8-main-module", "e8-md",
          "e2-module-att", "e2-symbol", "e2-collection", "e2-equation", "e2-simplification", "e2-token",
          "e2-macro", "e2-cells", "e3-ml", "e3-kseq", "e3-vars", "e3-kast", "e3-casts", "e3-fresh",
          "e3-reqens", "e3-k", "e3-fragment", "e3-userlist"]
COLLECTIONS = {"SET.Set", "MAP.Map", "LIST.List", "RANGEMAP.RangeMap"}

G = "grammar:"
ML = {
    "\\top": G + '<matching-logic-pattern>::="\\top" "{" <sort> "}" "(" ")"',
    "\\bottom": G + '<matching-logic-pattern>::="\\bottom" "{" <sort> "}" "(" ")"',
    "\\not": G + '<matching-logic-pattern>::="\\not" "{" <sort> "}" "(" <pattern> ")"',
    "\\and": G + '<matching-logic-pattern>::="\\and" "{" <sort> "}" "(" <patterns> ")"',
    "\\or": G + '<matching-logic-pattern>::="\\or" "{" <sort> "}" "(" <patterns> ")"',
    "\\implies": G + '<matching-logic-pattern>::="\\implies" "{" <sort> "}" "(" <pattern> "," <pattern> ")"',
    "\\iff": G + '<matching-logic-pattern>::="\\iff" "{" <sort> "}" "(" <pattern> "," <pattern> ")"',
    "\\exists": G + '<matching-logic-pattern>::="\\exists" "{" <sort> "}" "(" <element-variable> "," <pattern> ")"',
    "\\forall": G + '<matching-logic-pattern>::="\\forall" "{" <sort> "}" "(" <element-variable> "," <pattern> ")"',
    "\\mu": G + '<matching-logic-pattern>::="\\mu" "{" "}" "(" <set-variable> "," <pattern> ")"',
    "\\nu": G + '<matching-logic-pattern>::="\\nu" "{" "}" "(" <set-variable> "," <pattern> ")"',
    "\\ceil": G + '<matching-logic-pattern>::="\\ceil" "{" <sort> "," <sort> "}" "(" <pattern> ")"',
    "\\floor": G + '<matching-logic-pattern>::="\\floor" "{" <sort> "," <sort> "}" "(" <pattern> ")"',
    "\\equals": G + '<matching-logic-pattern>::="\\equals" "{" <sort> "," <sort> "}" "(" <pattern> "," <pattern> ")"',
    "\\in": G + '<matching-logic-pattern>::="\\in" "{" <sort> "," <sort> "}" "(" <pattern> "," <pattern> ")"',
    "\\next": G + '<matching-logic-pattern>::="\\next" "{" <sort> "}" "(" <pattern> ")"',
    "\\rewrites": G + '<matching-logic-pattern>::="\\rewrites" "{" <sort> "}" "(" <pattern> "," <pattern> ")"',
    "\\dv": G + '<matching-logic-pattern>::="\\dv" "{" <sort> "}" "(" <string-literal> ")"',
    "\\left-assoc": G + '<matching-logic-pattern>::="\\left-assoc" "{" "}" "(" <application-pattern> ")"',
    "\\right-assoc": G + '<matching-logic-pattern>::="\\right-assoc" "{" "}" "(" <application-pattern> ")"',
}
TREE_ML = {"\\top": "top", "\\bottom": "bottom", "\\not": "not", "\\and": "and", "\\or": "or",
           "\\implies": "implies", "\\iff": "iff", "\\exists": "exist", "\\forall": "forall", "\\mu": "mu",
           "\\nu": "nu", "\\ceil": "ceil", "\\floor": "floor", "\\equals": "equals", "\\in": "in",
           "\\next": "next", "\\rewrites": "rewrites", "\\dv": "dv", "\\left-assoc": "leftAssoc",
           "\\right-assoc": "rightAssoc"}
# the connectives' arguments: sorts in braces, then the argument forms ("p" a pattern, "ps" a
# pattern list, "v" a variable, "s" a string literal, "a" an application)
ARITY = {"\\top": (1, ()), "\\bottom": (1, ()), "\\not": (1, ("p",)), "\\and": (1, ("ps",)),
         "\\or": (1, ("ps",)), "\\implies": (1, ("p", "p")), "\\iff": (1, ("p", "p")),
         "\\exists": (1, ("v", "p")), "\\forall": (1, ("v", "p")), "\\mu": (0, ("v", "p")),
         "\\nu": (0, ("v", "p")), "\\ceil": (2, ("p",)), "\\floor": (2, ("p",)),
         "\\equals": (2, ("p", "p")), "\\in": (2, ("p", "p")), "\\next": (1, ("p",)),
         "\\rewrites": (1, ("p", "p")), "\\dv": (1, ("s",)), "\\left-assoc": (0, ("a",)),
         "\\right-assoc": (0, ("a",))}
SENT = {  # keyword: (the sentence production, the alternative of <sentence>, the tree constructor)
    "sort": (G + '<sentence-sort>::="sort" <sort-identifier> "{" <sort-variables> "}" "[" <attributes> "]"',
             G + "<sentence>::=<sentence-sort>", "sort"),
    "hooked-sort": (G + '<sentence-hooked-sort>::="hooked-sort" <sort-identifier> "{" <sort-variables> "}" "[" <attributes> "]"',
                    G + "<sentence>::=<sentence-hooked-sort>", "hookedSort"),
    "symbol": (G + '<sentence-symbol>::="symbol" <symbol> "(" <sorts> ")" ":" <sort> "[" <attributes> "]"',
               G + "<sentence>::=<sentence-symbol>", "symbol"),
    "hooked-symbol": (G + '<sentence-hooked-symbol>::="hooked-symbol" <symbol> "(" <sorts> ")" ":" <sort> "[" <attributes> "]"',
                      G + "<sentence>::=<sentence-hooked-symbol>", "hookedSymbol"),
    "axiom": (G + '<sentence-axiom>::="axiom" "{" <sort-variables> "}" <pattern> "[" <attributes> "]"',
              G + "<sentence>::=<sentence-axiom>", "axiom"),
    "claim": (G + '<sentence-claim>::="claim" "{" <sort-variables> "}" <pattern> "[" <attributes> "]"',
              G + "<sentence>::=<sentence-claim>", "claim"),
    "import": (G + '<sentence-import>::="import" <module-name> "[" <attributes> "]"',
               G + "<sentence>::=<sentence-import>", "import"),
    "alias": (G + '<sentence-alias>::="alias" <alias> "(" <sorts> ")" ":" <sort> "where" <application-pattern> ":=" <pattern> "[" <attributes> "]"',
              G + "<sentence>::=<sentence-alias>", "alias"),
}
K_ = {
    "string": G + "<string-literal>::=['\"'] <char>* ['\"']",
    "escape": G + "<char>::=<escape-sequence>",
    "printable-char": G + "<char>::=<printable-ascii-char> except ['\"', '\\']",
    "printable": G + "<printable-ascii-char>::=U+0020 through U+007E",
    "identifier": G + "<identifier>::=<identifier-first-char> <identifier-char>*",
    "idchar-first": G + "<identifier-char>::=<identifier-first-char>",
    "idchar-other": G + "<identifier-char>::=<identifier-other-char>",
    "idfirst": G + "<identifier-first-char>::=['A'..'Z', 'a'..'z']",
    "idother": G + "<identifier-other-char>::=['0'..'9', '\\'', '-']",
    "symbol-identifier": G + "<symbol-identifier>::=['\\']? <identifier>",
    "evar-identifier": G + "<element-variable-identifier>::=<identifier>",
    "svar-identifier": G + "<set-variable-identifier>::=['@'] <identifier>",
    "sort-identifier": G + "<sort-identifier>::=<identifier>",
    "module-name": G + "<module-name>::=<identifier>",
    "sep-empty": G + '<[$item]-sep-by-[$separator]>::=""',
    "sep-nonempty": G + "<[$item]-sep-by-[$separator]>::=<[$item]-sep-by-1-[$separator]>",
    "sep1-one": G + "<[$item]-sep-by-1-[$separator]>::=$item",
    "sep1-more": G + "<[$item]-sep-by-1-[$separator]>::=$item $separator <[$item]-sep-by-1-[$separator]>",
    "sort-var": G + "<sort>::=<sort-variable>",
    "sort-ctor": G + '<sort>::=<sort-identifier> "{" <sorts> "}"',
    "sorts": G + '<sorts>::=<[sort]-sep-by-[","]>',
    "sort-variable": G + "<sort-variable>::=<sort-identifier>",
    "sort-variables": G + '<sort-variables>::=<[sort-variable]-sep-by-[","]>',
    "pat-var": G + "<pattern>::=<variable-pattern>",
    "pat-ml": G + "<pattern>::=<matching-logic-pattern>",
    "pat-app": G + "<pattern>::=<application-pattern>",
    "pat-string": G + "<pattern>::=<string-literal>",
    "patterns": G + '<patterns>::=<[pattern]-sep-by-[","]>',
    "varpat-evar": G + "<variable-pattern>::=<element-variable>",
    "varpat-svar": G + "<variable-pattern>::=<set-variable>",
    "element-variable": G + '<element-variable>::=<element-variable-identifier> ":" <sort>',
    "set-variable": G + '<set-variable>::=<set-variable-identifier> ":" <sort>',
    "app": G + '<application-pattern>::=<symbol-identifier> "{" <sorts> "}" "(" <patterns> ")"',
    "attribute": G + "<attribute>::=<application-pattern>",
    "attributes": G + '<attributes>::=<[attribute]-sep-by-[","]>',
    "symbol": G + "<symbol>::=<symbol-or-alias>",
    "alias": G + "<alias>::=<symbol-or-alias>",
    "symbol-or-alias": G + '<symbol-or-alias>::=<symbol-identifier> "{" <sort-variables> "}"',
    "definition": G + '<definition>::="[" <attributes> "]" <modules>',
    "module": G + '<module>::="module" <module-name> <sentences> "endmodule" "[" <attributes> "]"',
    "modules": G + "<modules>::=<[module]-sep-by-1-[whitespace]>",
    "kw-module": G + '<keyword>::="module"',
    "kw-endmodule": G + '<keyword>::="endmodule"',
}
for kw in ("import", "sort", "hooked-sort", "symbol", "hooked-symbol", "axiom", "claim", "alias", "where"):
    K_["kw-" + kw] = G + f'<keyword>::="{kw}"'


class ParseError(Exception):
    pass


TOKEN = re.compile(r'\s+|//[^\n]*|/\*.*?\*/|"(?:[^"\\]|\\.)*"|[\\@]?[A-Za-z][A-Za-z0-9\'-]*|:=|[{}()\[\],:]',
                   re.S)


def tokens(text, offsets=None):
    """The tokens of a KORE text (whitespace and comments dropped); with a list `offsets`, each
    token's offset in the text is appended to it."""
    out, i = [], 0
    while i < len(text):
        m = TOKEN.match(text, i)
        if not m:
            raise ParseError(f"no token at {text[i:i + 30]!r}")
        s = m[0]
        if not (s.isspace() or s.startswith("//") or s.startswith("/*")):
            out.append(s)
            if offsets is not None:
                offsets.append(i)
        i = m.end()
    return out


def line_at(text, off):
    """The line of the text holding offset off, from off on."""
    end = text.find("\n", off)
    return text[off:end if end >= 0 else len(text)]


class Parser:
    """A recursive-descent parser over the tokens; `found` collects the E4 keys of what it reads."""

    def __init__(self, toks):
        self.t, self.i, self.found = toks, 0, set()

    def peek(self, k=0):
        return self.t[self.i + k] if self.i + k < len(self.t) else None

    def eat(self, want=None):
        tok = self.peek()
        if tok is None or (want is not None and tok != want):
            raise ParseError(f"expected {want!r}, found {tok!r} at token {self.i}")
        self.i += 1
        return tok

    def add(self, *ks):
        self.found.update(ks)

    def ident(self, role):
        tok = self.eat()
        if not re.match(r"[A-Za-z][A-Za-z0-9'-]*$", tok):
            raise ParseError(f"expected an identifier, found {tok!r}")
        self.add(K_["identifier"], K_["idfirst"], K_[role])
        if len(tok) > 1:
            if any(c.isalpha() for c in tok[1:]):
                self.add(K_["idchar-first"])
            if any(c.isdigit() or c in "'-" for c in tok[1:]):
                self.add(K_["idchar-other"], K_["idother"])
        return tok

    def string(self):
        tok = self.eat()
        if not tok.startswith('"'):
            raise ParseError(f"expected a string literal, found {tok!r}")
        self.add(K_["string"])
        body = tok[1:-1]
        if "\\" in body:
            self.add(K_["escape"])
        if re.search(r'[^"\\]', body.replace("\\\\", "").replace('\\"', "")):
            self.add(K_["printable-char"], K_["printable"])
        return tok

    def seplist(self, item, close, sep=","):
        """item(), separated by sep, up to close (not eaten); the sep-by keys."""
        n = 0
        if self.peek() == close:
            self.add(K_["sep-empty"])
            return 0
        while True:
            item(); n += 1
            if self.peek() == sep:
                self.eat(sep); continue
            break
        self.add(K_["sep-nonempty"], K_["sep1-one"])
        if n > 1:
            self.add(K_["sep1-more"])
        return n

    def sort(self):
        self.ident("sort-identifier")
        if self.peek() == "{":
            self.eat("{"); self.seplist(self.sort, "}"); self.eat("}")
            self.add(K_["sort-ctor"], K_["sorts"], "tree:KSort.ctor")
        else:
            self.add(K_["sort-var"], K_["sort-variable"], "tree:KSort.var")

    def sorts_braced(self):
        self.eat("{"); self.seplist(self.sort, "}"); self.eat("}")
        self.add(K_["sorts"])

    def sortvars(self):
        def sv():
            self.ident("sort-identifier"); self.add(K_["sort-variable"])
        self.eat("{"); self.seplist(sv, "}"); self.eat("}")
        self.add(K_["sort-variables"])

    def variable(self):
        """An element or set variable `X:S`; returns whether it was a set variable."""
        tok = self.peek()
        if tok.startswith("@"):
            self.eat(); self.add(K_["identifier"], K_["svar-identifier"], K_["set-variable"],
                                 K_["varpat-svar"], "tree:VarPattern.svar")
            self.eat(":"); self.sort()
            return True
        self.ident("evar-identifier")
        self.eat(":"); self.sort()
        self.add(K_["element-variable"], K_["varpat-evar"], "tree:VarPattern.evar")
        return False

    def app(self):
        tok = self.eat()
        if not re.match(r"\\?[A-Za-z][A-Za-z0-9'-]*$", tok):
            raise ParseError(f"expected a symbol, found {tok!r}")
        name = tok
        self.add(K_["symbol-identifier"], K_["identifier"], K_["idfirst"])
        self.sorts_braced()
        self.eat("("); self.seplist(self.pattern, ")"); self.eat(")")
        self.add(K_["patterns"], K_["app"])
        return name

    def pattern(self):
        tok = self.peek()
        if tok is None:
            raise ParseError("a pattern expected, end of text")
        if tok.startswith('"'):
            self.string(); self.add(K_["pat-string"], "tree:Pattern.string"); return
        if tok in ML:
            self.eat()
            nsorts, args = ARITY[tok]
            self.eat("{")
            for j in range(nsorts):
                if j:
                    self.eat(",")
                self.sort()
            self.eat("}")
            self.eat("(")
            for j, a in enumerate(args):
                if j:
                    self.eat(",")
                if a == "p":
                    self.pattern()
                elif a == "ps":
                    self.seplist(self.pattern, ")"); self.add(K_["patterns"])
                elif a == "v":
                    self.variable()
                elif a == "s":
                    self.string()
                elif a == "a":
                    self.app(); self.add(K_["pat-app"])
            self.eat(")")
            self.add(ML[tok], K_["pat-ml"], "tree:Pattern." + TREE_ML[tok])
            return
        if self.peek(1) == ":":
            self.variable()
            self.add(K_["pat-var"], "tree:Pattern.var")
            return
        self.app()
        self.add(K_["pat-app"], "tree:Pattern.app")

    def attributes(self):
        """`[ attr, ... ]`; returns the attributes' heads with their string arguments."""
        heads = []

        def attr():
            start = self.i
            name = self.app()
            heads.append((name, [t for t in self.t[start:self.i] if t.startswith('"')]))
            self.add(K_["attribute"])
        self.eat("["); self.seplist(attr, "]"); self.eat("]")
        self.add(K_["attributes"])
        return heads

    def sentence(self):
        """One sentence; returns (keyword, attribute heads, the body's head connective or None, has
        sort variables)."""
        kw = self.eat()
        if kw not in SENT:
            raise ParseError(f"no sentence keyword: {kw!r}")
        prod, alt, tree = SENT[kw]
        self.add(prod, alt, K_["kw-" + kw], "tree:Sentence." + tree)
        body, nvars = None, 0
        if kw == "import":
            self.ident("module-name")
        elif kw in ("sort", "hooked-sort"):
            self.ident("sort-identifier"); self.sortvars()
        elif kw in ("symbol", "hooked-symbol", "alias"):
            self.ident("symbol-identifier")
            self.add(K_["symbol-identifier"], K_["symbol-or-alias"], K_["symbol" if kw != "alias" else "alias"])
            self.sortvars()
            self.eat("("); self.seplist(self.sort, ")"); self.eat(")"); self.add(K_["sorts"])
            self.eat(":"); self.sort()
            if kw == "alias":
                self.eat("where"); self.add(K_["kw-where"]); self.app(); self.eat(":="); self.pattern()
        else:
            start = self.i
            self.sortvars()
            nvars = sum(1 for t in self.t[start:self.i] if t not in "{},")
            body = self.peek()
            self.pattern()
        heads = self.attributes()
        return kw, heads, body, nvars


def e5_sites(kw, heads, body, nvars):
    """The E5 sites a sentence is the form of (module docstring)."""
    names = {h for h, _ in heads}
    out = set()
    if kw == "sort":
        out.add("translateSorts:sort#1")
    elif kw == "hooked-sort":
        hook = next((a[0].strip('"') for h, a in heads if h == "hook" and a), None)
        out.add("translateSorts:hooked-#1" if hook in COLLECTIONS else "translateSorts:hooked-#2")
    elif kw == "symbol":
        out.add("translateSymbol:symbol#1")
    elif kw == "axiom":
        if "symbol-overload" in names:
            out.add("genOverloadedAxiom:axiom#1")
        elif body == "\\rewrites" and nvars == 0:
            out.add("convertRule:axiom#2")
        elif "UNIQUE'Unds'ID" in names and nvars > 0 and body != "\\rewrites":
            out.add("convertRule:axiom#1")
        elif body == "\\exists" and names & {"functional", "subsort"}:
            out.add("functionalPattern:axiom#1")
        elif body == "\\equals" and "idem" in names:
            out.add("genIdemAxiom:axiom#1")
        elif body == "\\equals" and "assoc" in names:
            out.add("genAssocAxiom:axiom#1")
    return out


def parse_kore_txt(text):
    """[(index, first line, keys)] of a kore.txt: its module line, its sentences, its endmodule."""
    out, chunks, cur = [], [], None
    for line in text.split("\n"):
        m = re.match(r"^//@ (\d+)$", line)
        if m:
            cur = [int(m[1]), []]; chunks.append(cur); continue
        if cur is not None:
            cur[1].append(line)
    for idx, lines in chunks:
        body = "\n".join(l for l in lines if not l.startswith("//"))
        first = next((l for l in lines if l.strip() and not l.startswith("//")), "")
        toks = tokens(body)
        if not toks:
            continue                      # a section comment kompile writes (`// rules`), no sentence
        p = Parser(toks)
        if toks[:1] == ["module"]:
            p.eat("module"); p.ident("module-name"); p.add(K_["kw-module"])
        elif toks[:1] == ["endmodule"]:
            p.eat("endmodule"); p.attributes(); p.add(K_["kw-endmodule"])
        else:
            kw, heads, b, nv = p.sentence()
            p.found |= e5_sites(kw, heads, b, nv)
        if p.i != len(toks):
            raise ParseError(f"sentence {idx}: tokens left after the sentence: {toks[p.i:p.i + 5]}")
        out.append((idx, first, p.found))
    kinds = [f.split()[0] if f.split() else "" for _, f, _ in out]
    if "module" in kinds and "endmodule" in kinds:
        out.append((None, "module", {K_["module"]}))
    return out


def parse_definition(text):
    """[(index, first line, keys)] of a whole definition: one entry per sentence (index its place
    in its module), and one for the definition's own productions."""
    offs = []
    toks = tokens(text, offs)
    p = Parser(toks)
    out = []
    p.attributes()
    nmod = 0
    while p.peek() == "module":
        p.eat("module"); p.ident("module-name"); p.add(K_["kw-module"])
        j = 0
        while p.peek() != "endmodule":
            before = p.found; p.found = set()
            start = p.i
            kw, heads, b, nv = p.sentence()
            keys = p.found | e5_sites(kw, heads, b, nv)
            out.append((j, line_at(text, offs[start]), keys))
            p.found = before | keys
            j += 1
        p.eat("endmodule"); p.attributes(); p.add(K_["kw-endmodule"], K_["module"])
        nmod += 1
    if p.i != len(toks):
        raise ParseError(f"tokens left after the modules: {toks[p.i:p.i + 5]}")
    p.add(K_["definition"], K_["modules"])
    out.append((None, line_at(text, offs[0]), p.found))
    return out


_cache = {}


def fixture_nodes(name, fxdir=FXDIR):
    """{key: (sentence index or None, first line)} of the fixture's text, the first sentence holding
    each key; or a string (why the text is not read)."""
    if (fxdir, name) in _cache:
        return _cache[(fxdir, name)]
    d = os.path.join(fxdir, name)
    c = tomllib.load(open(os.path.join(d, "fixture.toml"), "rb")) if os.path.isfile(os.path.join(d, "fixture.toml")) else {}
    try:
        if isinstance(c.get("kore"), str):
            p = os.path.join(K, c["kore"])
            res = parse_definition(open(p).read()) if os.path.isfile(p) else f"no text {c['kore']}"
        elif c.get("expect", "ok") != "ok" or not os.path.isfile(os.path.join(d, "kore.txt")):
            res = "no kore.txt of a kompiled text"
        else:
            res = parse_kore_txt(open(os.path.join(d, "kore.txt")).read())
    except ParseError as err:
        res = f"does not parse: {err}"
    if not isinstance(res, str):
        nodes = {}
        for idx, first, keys in res:
            for k in keys:
                nodes.setdefault(k, (idx, first))
        res = nodes
    _cache[(fxdir, name)] = res
    return res


def kompiled_text(name, fxdir=FXDIR):
    """(text, None): the kompiled definition fixture NAME's kompile.txt records (its
    `definition.kore sha256`), from kfix.py's cache; or (None, why there is none)."""
    sys.dont_write_bytecode = True  # no __pycache__ in the tree
    if HERE not in sys.path:
        sys.path.insert(0, HERE)
    import kfix
    kt = os.path.join(fxdir, name, "kompile.txt")
    m = re.search(r"^definition\.kore sha256: (\w+)$", open(kt).read() if os.path.isfile(kt) else "", re.M)
    if not m:
        return None, "no definition.kore sha256 in kompile.txt"
    p = os.path.join(kfix.WORK, name, "definition.norm.kore")
    if os.path.isfile(p):
        kore = open(p).read()
        if kfix.sha(kore) == m[1]:
            return kore, None
    kore = kfix.cache_get(m[1])
    return (kore, None) if kore is not None else (None, f"its kompiled text {m[1][:12]} is in no cache ({kfix.CACHE})")


DEFINITION_OWN = {K_["definition"], K_["modules"]}


def sentence_nodes(name, s, fxdir=FXDIR, text=None):
    """{key: (sentence index, first line)} of the sentences of fixture NAME's kompiled definition
    (or of TEXT) whose first line contains S, and, where the definition's first line (its attribute
    list) contains S, the productions of the definition itself (DEFINITION_OWN, index None); or a
    string (why there is none)."""
    given = text is not None
    if not given and (fxdir, name, s) in _cache:
        return _cache[(fxdir, name, s)]
    why = None
    if not given:
        text, why = kompiled_text(name, fxdir)
    if why is not None:
        res = why
    else:
        try:
            nodes = {}
            for idx, first, keys in parse_definition(text):
                if s in first:
                    # the definition's own entry (no index) holds every node of the text: only the
                    # productions of the definition itself are its own
                    for k in (keys if idx is not None else keys & DEFINITION_OWN):
                        nodes.setdefault(k, (idx, first))
            res = nodes or f"no sentence of its kompiled definition has {s!r} in its first line"
        except ParseError as err:
            res = f"its kompiled definition does not parse: {err}"
    if not given:
        _cache[(fxdir, name, s)] = res
    return res


def holds(fx, l, key, name, node_sentence=None):
    """(held, how) for rest.py: whether fixture NAME's text holds the E4/E5 row's node; with
    node_sentence, the sentence of its kompiled definition that the string locates."""
    if node_sentence is not None:
        n = sentence_nodes(name, node_sentence, fx.fx)
        if isinstance(n, str):
            return False, f"{name}: {n}"
        if key not in n:
            return False, f"{name}'s kompiled sentence {node_sentence!r} does not hold it (e4e5.py)"
        return True, f"{name}'s kompiled definition, sentence {node_sentence!r} (e4e5.py)"
    n = fixture_nodes(name, fx.fx)
    if isinstance(n, str):
        return False, f"{name}: {n}"
    if key not in n:
        return False, f"{name}'s text does not hold it (e4e5.py)"
    idx = n[key][0]
    return True, f"{name}" + (f" //@ {idx}" if idx is not None else "") + " (e4e5.py)"


# ---------------------------------------------------------------------------------------- modes

def clean(name):
    p = os.path.join(FXDIR, name, "account.txt")
    if not os.path.isfile(p):
        return False
    a = open(p).read()
    return (bool(re.search(r"^parse: ok\b", a, re.M))
            and not re.search(r"^\s+[1-9]\d* refused \w+ \[", a, re.M)
            and not re.search(r"(?:sentence \d+|the module) \(.*?\): \w+", a)
            and bool(re.search(r"^stage refusals \(of sentences classified read\): 0$", a, re.M))
            and bool(re.search(r"^refused by the account: 0$", a, re.M)))


def order():
    names = sorted(d for d in os.listdir(FXDIR) if os.path.isdir(os.path.join(FXDIR, d)))
    conf = {n: (tomllib.load(open(os.path.join(FXDIR, n, "fixture.toml"), "rb"))
                if os.path.isfile(os.path.join(FXDIR, n, "fixture.toml")) else {}) for n in names}
    kompiled = [n for n in names if "kore" not in conf[n] and os.path.isfile(os.path.join(FXDIR, n, "kore.txt"))]
    kore = [n for n in names if isinstance(conf[n].get("kore"), str)]
    size = lambda n: os.path.getsize(os.path.join(FXDIR, n, "kore.txt"))
    ksize = lambda n: os.path.getsize(os.path.join(K, conf[n]["kore"])) if os.path.isfile(os.path.join(K, conf[n]["kore"])) else 1 << 40
    pre = [n for n in PREFER if n in kompiled]
    return pre + sorted((n for n in kompiled if n not in pre), key=lambda n: (size(n), n)) \
        + sorted(kore, key=lambda n: (ksize(n), n))


def rows_of(t):
    return [(l, k, r) for l in ("E4", "E5") for k, r in t[l].items() if r.get("status") == "supported"]


def sentence_of(name, idx, first):
    """A substring of the fixture's text that locates the node: the first line of its sentence."""
    s = first.strip()
    return s[:110]


def find(rows, write):
    t = tomllib.load(open(rows, "rb"))
    cands = [n for n in order() if clean(n)]
    unparsed = [(n, fixture_nodes(n)) for n in cands if isinstance(fixture_nodes(n), str)]
    pick, none = {}, []
    for l, k, r in rows_of(t):
        x = next((n for n in cands if not isinstance(fixture_nodes(n), str) and k in fixture_nodes(n)), None)
        if x is None:
            none.append(f"{l} {k}"); continue
        idx, first = fixture_nodes(x)[k]
        pick[(l, k)] = (x, idx, sentence_of(x, idx, first))
    for (l, k), (x, idx, s) in pick.items():
        print(f"e4e5: {l} {k!r}: {x}" + (f" //@ {idx}" if idx is not None else "") + f": {s[:70]!r}")
    print(f"e4e5: {len(pick)} of {len(pick) + len(none)} supported E4 and E5 rows held by a fixture whose account"
          f" refuses nothing ({len(cands)} such fixtures, {len(unparsed)} of whose texts are not read"
          + (": " + ", ".join(f"{n} ({w[:60]})" for n, w in unparsed[:5]) if unparsed else "") + ")")
    for n in none:
        print(f"e4e5: no fixture holds {n}")
    if write and pick:
        src = open(rows).read()
        for (l, k), (x, idx, s) in pick.items():
            src = record(src, t, l, k, x, idx, s)
        open(rows, "w").write(src)
        tomllib.loads(src)
        print(f"e4e5: {len(pick)} rows written")
    return 1 if none else 0


def record(src, t, l, k, x, idx, s):
    """rows.toml's text with the row's fixture and sentence added at the end of its line."""
    import json
    lines = src.split("\n")
    sec = lines.index(f"[{l}]")
    head = json.dumps(k, ensure_ascii=False) + " = { "
    i = next(i for i in range(sec + 1, len(lines)) if lines[i].startswith(head))
    if "fixture" in t[l][k] or "sentence" in t[l][k] or not lines[i].endswith(" }"):
        raise SystemExit(f"e4e5: {l} {k!r} already has a fixture or sentence, or is not one line")
    lines[i] = lines[i][:-2] + f", fixture = {toml_inline(x)}, sentence = [{toml_inline(s)}] }}"
    r = tomllib.loads(lines[i])[k]
    assert r == {**t[l][k], "fixture": x, "sentence": [s]}
    d = os.path.join(FXDIR, x, "kore.txt")
    if s not in (open(d).read() if os.path.isfile(d) else text_of(x)):
        raise SystemExit(f"e4e5: {l} {k!r}: the sentence {s!r} is not in {x}'s text")
    return "\n".join(lines)


def text_of(x):
    c = tomllib.load(open(os.path.join(FXDIR, x, "fixture.toml"), "rb"))
    return open(os.path.join(K, c["kore"])).read()


def toml_inline(v):
    import json
    if isinstance(v, bool):
        return "true" if v else "false"
    if isinstance(v, int):
        return str(v)
    if isinstance(v, str):
        return json.dumps(v, ensure_ascii=False)
    if isinstance(v, list):
        return "[" + ", ".join(toml_inline(x) for x in v) + "]"
    if isinstance(v, dict):
        return "{ " + ", ".join(f"{json.dumps(a, ensure_ascii=False) if not re.match(r'^[A-Za-z0-9_-]+$', a) else a}"
                                f" = {toml_inline(b)}" for a, b in v.items()) + " }"
    raise TypeError(v)


def check(rows):
    t = tomllib.load(open(rows, "rb"))
    bad, n = [], 0
    for l in ("E4", "E5"):
        for k, row in t[l].items():
            entries = [(f"{l} {k!r}", row)] + [(f"{l} {k!r} cases[{i}]", c) for i, c in enumerate(row.get("cases") or [])
                                               if isinstance(c, dict)]
            for at, r in entries:
                x = r.get("fixture")
                if not isinstance(x, str) or x == "none" or r.get("status") != "supported":
                    continue
                n += 1
                if not os.path.isdir(os.path.join(FXDIR, x)):
                    bad.append(f"{at}: no fixture {x}"); continue
                ns = r.get("node_sentence")
                nodes = fixture_nodes(x) if ns is None else sentence_nodes(x, ns)
                if isinstance(nodes, str):
                    bad.append(f"{at}: {x}: {nodes}")
                elif k not in nodes:
                    bad.append(f"{at}: {x}'s " + ("text" if ns is None else f"kompiled sentence {ns!r}")
                               + " does not hold the node")
    print(f"e4e5 check: {n} supported E4 and E5 rows and cases naming a fixture, {len(bad)} failing")
    for b in bad:
        print(f"  {b}")
    return 1 if bad else 0


def self_test():
    tiny = ('[topCellInitializer{}()]\nmodule M\n  import K []\n  sort SortA{} []\n'
            '  hooked-sort SortS{} [hook{}("SET.Set")]\n  hooked-sort SortI{} [hook{}("INT.Int")]\n'
            '  symbol Lbla{}() : SortA{} [constructor{}()]\n'
            '  axiom{R} \\exists{R} (Val:SortA{}, \\equals{SortA{}, R} (Val:SortA{}, Lbla{}())) [functional{}()]\n'
            '  axiom{} \\rewrites{SortA{}} (Lbla{}(), \\and{SortA{}}(Lbla{}(), \\top{SortA{}}())) '
            '[UNIQUE\'Unds\'ID{}("x\\"y")]\n'
            '  axiom{R} \\equals{SortA{}, R} (Lbla{}(), Lbla{}()) [assoc{}()]\nendmodule []\n')
    bad = []
    try:
        res = parse_definition(tiny)
    except ParseError as err:
        res = None; bad.append(f"the tiny definition does not parse: {err}")
    if res:
        keys = res[-1][2]
        want = {K_["definition"], K_["modules"], K_["module"], K_["escape"], "tree:Sentence.hookedSort",
                "tree:Pattern.exist", "tree:Pattern.rewrites", "tree:KSort.var", ML["\\top"],
                "translateSorts:hooked-#1", "translateSorts:hooked-#2", "translateSorts:sort#1",
                "translateSymbol:symbol#1", "functionalPattern:axiom#1", "convertRule:axiom#2", K_["sep1-more"],
                "genAssocAxiom:axiom#1",
                K_["sep-empty"], "tree:Sentence.import"}
        not_want = {"tree:Pattern.or", "convertRule:axiom#1", "tree:Sentence.hookedSymbol", "tree:Pattern.dv"}
        bad += [f"not found: {k}" for k in sorted(want - keys)]
        bad += [f"found, not in the text: {k}" for k in sorted(not_want & keys)]
    # node_sentence: the sentence its string locates, not the definition's first holding the key
    for s, key, want_held in [('hooked-sort SortI{}', "translateSorts:hooked-#2", True),
                              ('hooked-sort SortI{}', "translateSorts:hooked-#1", False),
                              ('hooked-sort SortS{}', "translateSorts:hooked-#2", False),
                              ('symbol Lbla{}', "translateSorts:hooked-#2", False)]:
        n = sentence_nodes("tiny", s, text=tiny)
        if isinstance(n, str) or (key in n) != want_held:
            bad.append(f"node_sentence {s!r}: {key} " + ("not held" if want_held else "held"))
    # the definition's attribute list locates the definition's own productions and no sentence's
    n = sentence_nodes("tiny", "[topCellInitializer{}()]", text=tiny)
    if isinstance(n, str) or not DEFINITION_OWN <= set(n) or "translateSorts:hooked-#2" in n or K_["module"] in n:
        bad.append(f"node_sentence '[topCellInitializer{{}}()]': {n if isinstance(n, str) else sorted(n)}")
    if not isinstance(sentence_nodes("tiny", "hooked-sort SortZ{}", text=tiny), str):
        bad.append("node_sentence 'hooked-sort SortZ{}': a sentence found, the text has none")
    for txt in ["module M\n  axiom{R} \\and{R}(\n", "[] module M axiom{} \\top{S{}}() endmodule []"]:
        try:
            parse_definition(txt); bad.append(f"parses, should not: {txt!r}")
        except ParseError:
            pass
    kt = ('//@ 0\nmodule M\n//@ 3\n// rule f(X)=>X\n  axiom{R} \\implies{R} (\\top{R}(), \\equals{SortInt{},R} '
          '(Lblf{}(X:SortInt{}), \\and{SortInt{}} (X:SortInt{}, \\top{SortInt{}}()))) [UNIQUE\'Unds\'ID{}("a")]\n'
          '//@ 9\nendmodule []\n')
    try:
        r = parse_kore_txt(kt)
        allk = set().union(*[k for _, _, k in r])
        if "convertRule:axiom#1" not in allk or K_["module"] not in allk or "tree:Pattern.implies" not in allk:
            bad.append(f"kore.txt: {sorted(k for k in allk if not k.startswith('grammar:<id'))}")
        if r[1][0] != 3:
            bad.append(f"kore.txt: the axiom's index is {r[1][0]}, not 3")
    except ParseError as err:
        bad.append(f"the kore.txt does not parse: {err}")
    t = tomllib.load(open(os.path.join(HERE, "rows.toml"), "rb"))
    allkeys = set(t["E4"]) | set(t["E5"])
    ours = set(K_.values()) | set(ML.values()) | {a for v in SENT.values() for a in v[:2]}
    bad += [f"no row of E4 is the key {k!r}" for k in sorted(ours - allkeys)]
    for b in bad:
        print(f"e4e5 self-test: FAILS: {b}")
    print(f"e4e5 self-test: {len(bad)} failing")
    return 1 if bad else 0


if __name__ == "__main__":
    a = sys.argv[1:]
    if a[:1] == ["--self-test"]:
        sys.exit(self_test())
    mode = a.pop(0) if a[:1] in (["find"], ["check"]) else None
    w = "--write" in a
    a = [x for x in a if x != "--write"]
    rows = a[0] if a else os.path.join(HERE, "rows.toml")
    if mode == "find":
        sys.exit(find(rows, w))
    if mode == "check":
        sys.exit(check(rows))
    raise SystemExit(__doc__)
