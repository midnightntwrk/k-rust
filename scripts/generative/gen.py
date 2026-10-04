#!/usr/bin/env python3
"""Seeded generator of small K definitions for the generative compile test.

Usage: gen.py OUT_DIR [--count N] [--seed S]

Writes OUT_DIR/NNNN.k for i in 0..N, each a definition whose main module is MAIN. Case i is
generated from random.Random(S * 1_000_003 + i), so any single case is reproducible from the seed
alone and does not depend on PYTHONHASHSEED.

The generator keeps a model of the declared grammar (sorts, subsorts, productions, available
builtin modules) and produces mostly well-sorted sentences from it; a small, explicit fraction of
choices deliberately leaves the valid path (marked MUTATION below) so that rejection paths are
also exercised. scripts/generative/expected.toml lists the rejections that such invalid inputs
are expected to produce.

Not generated: several modules or `requires`, `#fun` and `#let`, `?X` existentials, MInt and
Float operations, binders.
"""
import os
import random
import sys
import time

USER_SORTS = ["Exp", "Stmt", "Val", "Pgm", "Ty", "Node", "Tree", "State", "Cmd", "Item", "Op", "Res"]
TERMINAL_WORDS = ["foo", "bar", "baz", "qux", "nil", "done", "skip", "halt", "go", "stop",
                  "tick", "zero", "one", "pair", "wrap", "mk", "leaf", "node", "inc", "dec"]
INFIX_OPS = ["+", "*", "-", "&", "|", "~", "<+>", "::", "^^", "@", "%%", "->"]
BUILTIN_MODULES = ["INT", "BOOL", "STRING", "MAP", "SET", "LIST", "K-EQUAL", "ID", "BYTES", "FLOAT"]
CELL_NAMES = ["k", "env", "store", "cnt", "out", "log", "mem", "stack", "flag", "acc"]

# Production attribute keys (attribute_keys.rs, PRODUCTION target), split by parameter rule.
PROD_FORBIDDEN = ["function", "total", "functional", "constructor", "injective", "assoc", "comm",
                  "idem", "left", "right", "non-assoc", "prefer", "avoid", "private", "public",
                  "macro", "macro-rec", "alias", "alias-rec", "memo", "impure", "deprecated",
                  "unused", "no-evaluators", "binder", "bracket", "token", "initializer",
                  "freshGenerator", "exit", "initial", "maincell", "internal", "unparseAvoid",
                  "returnsUnit", "mlBinder", "mlOp", "cell", "bag", "cellCollection"]
PROD_REQUIRED = ["symbol", "klabel", "hook", "format", "color", "colors", "latex", "smtlib",
                 "smt-hook", "unit", "element", "update", "priority", "prec", "overload", "group",
                 "result", "applyPriority", "index", "parser", "type", "terminator-symbol",
                 "wrapElement", "multiplicity", "cellName", "label", "unboundVariables"]
PROD_OPTIONAL = ["strict", "seqstrict", "concrete", "symbolic", "stream", "hybrid"]
RULE_KEYS_FORBIDDEN = ["owise", "anywhere", "preserves-definedness", "smt-lemma", "non-executable",
                       "cool", "heat", "comm", "initializer"]
RULE_KEYS_OPTIONAL = ["simplification", "concrete", "symbolic", "stream"]
RULE_KEYS_REQUIRED = ["priority", "label", "group", "syntactic", "result", "unboundVariables"]
SORT_KEYS = ["token", "hook", "locations", "cellCollection"]


class Fail(Exception):
    pass


HOOKED = {"Int", "Bool", "String", "Map", "Set", "List", "Float", "Bytes", "Id", "K"}


class Prod:
    def __init__(self, sort, kind, args, name, attrs, params=()):
        self.sort = sort          # result sort spelling
        self.kind = kind          # 'const' | 'prefix' | 'infix' | 'mixfix' | 'sub' | 'list' | 'token'
        self.args = args          # argument sorts
        self.name = name          # terminal / function name / operator
        self.attrs = attrs        # list of (key, value-or-None)
        self.params = params      # sort parameters ({S} ...)

    def has(self, key):
        return any(k == key for k, _ in self.attrs)

    @property
    def is_function(self):
        return self.has("function") or self.has("macro") or self.has("alias")


class Gen:
    def __init__(self, rng):
        self.r = rng
        self.sentences = []
        self.prods = []
        self.sorts = []            # user sorts (non-parametric names)
        self.subsorts = set()      # (sub, sup)
        self.synonyms = {}         # alias -> sort
        self.tokens = []           # token sorts
        self.list_sorts = {}       # list sort -> element sort
        self.counter = 0
        self.var_counter = 0
        self.cells = []            # (name, sort, multiplicity)
        self.has_config = False
        self.kresult = False
        self.need_kresult = False
        self.allow_fresh = False

    # ---------- helpers ----------
    def p(self, prob):
        return self.r.random() < prob

    def fresh(self, base):
        self.counter += 1
        return f"{base}{self.counter}"

    def fresh_var(self):
        self.var_counter += 1
        return f"V{self.var_counter}"

    def builtin_sorts(self):
        m = self.mods
        s = ["K", "KItem"] if m else []
        if "INT" in m: s.append("Int")
        if "BOOL" in m: s.append("Bool")
        if "STRING" in m: s.append("String")
        if "MAP" in m: s.append("Map")
        if "SET" in m: s.append("Set")
        if "LIST" in m: s.append("List")
        if "ID" in m: s.append("Id")
        if "BYTES" in m: s.append("Bytes")
        if "FLOAT" in m: s.append("Float")
        return s

    def all_sorts(self, include_k=True):
        s = list(self.sorts) + list(self.tokens) + list(self.list_sorts)
        b = self.builtin_sorts()
        if not include_k:
            b = [x for x in b if x not in ("K", "KItem")]
        return s + b

    def leq(self, a, b):
        """Is sort a a (reflexive, transitive) subsort of b?"""
        if a == b or b == "K" or (b == "KItem" and a != "K"):
            return True
        seen, stack = set(), [a]
        while stack:
            x = stack.pop()
            for (lo, hi) in self.subsorts:
                if lo == x and hi not in seen:
                    if hi == b:
                        return True
                    seen.add(hi)
                    stack.append(hi)
        return False

    def assoc_ok(self, prod, key):
        """Whether the associativity attribute `key` has an effect on `prod`, which the
        compiler requires of a production with exactly two non-terminals: `left` needs the
        result sort below the right argument, `right` below the left argument, `non-assoc`
        both."""
        if len(prod.args) != 2:
            return True
        left, right = (self.leq(prod.sort, a) for a in prod.args)
        return {"left": right, "right": left, "non-assoc": left and right}[key]

    def attr_text(self, attrs):
        if not attrs:
            return ""
        parts = []
        for k, v in attrs:
            parts.append(k if v is None else f"{k}({v})")
        return " [" + ", ".join(parts) + "]"

    # ---------- top level ----------
    def definition(self):
        r = self.r
        roll = r.random()
        if roll < 0.30:
            self.mods = {"INT", "BOOL", "STRING", "MAP", "SET", "LIST", "K-EQUAL", "ID", "DOMAINS"}
            imports = ["DOMAINS"]
        elif roll < 0.80:
            imports = sorted(r.sample(BUILTIN_MODULES, r.randint(1, 4)))
            self.mods = set(imports)
        else:
            imports = ["BASIC-K"] if self.p(0.5) else []
            self.mods = set(imports)
        if "K-EQUAL" in self.mods and "BOOL" not in self.mods and self.p(0.7):
            imports.append("BOOL")
            self.mods.add("BOOL")
        self.imports = imports

        # sorts
        n_sorts = r.randint(1, 4)
        self.sorts = r.sample(USER_SORTS, n_sorts)
        for s in self.sorts:
            if self.p(0.85):
                attrs = []
                if self.p(0.03):  # MUTATION: unusual sort attributes
                    k = r.choice(SORT_KEYS)
                    attrs.append((k, "FOO.Bar" if k == "hook" else None))
                self.sentences.append(f"syntax {s}{self.attr_text(attrs)}")

        self.gen_parametric()
        self.gen_subsorts()
        n_prod_sentences = r.randint(1, 6)
        for _ in range(n_prod_sentences):
            self.gen_production_sentence()
        if self.p(0.25):
            self.gen_list_sort()
        if self.p(0.12):
            self.gen_token_sort()
        if self.p(0.12):
            self.gen_synonym()
        if self.p(0.08):
            self.gen_user_collection()
        if self.p(0.12):
            self.gen_priority_assoc()
        if self.p(0.05):
            self.sentences.append(f'syntax lexical {r.choice(["Digit", "Alpha", "Ws"])} = r"[{r.choice(["0-9", "a-z", "A-Z"])}]"')
        if self.p(0.12):
            self.gen_strict()
        if self.need_kresult and not self.kresult and self.p(0.95):
            self.kresult = True
            v = self.r.choice([s for s in ("Int", "Bool") if s in self.builtin_sorts()] or self.sorts or ["KItem"])
            self.sentences.append(f"syntax KResult ::= {v}")
            self.subsorts.add((v, "KResult"))
        if self.p(0.55):
            self.gen_configuration()
        n_rules = r.randint(0, 6)
        for _ in range(n_rules):
            self.gen_rule()
        if self.p(0.02):  # MUTATION: claims belong in spec modules
            self.gen_claim()

        for srt in self.sorts:
            if not any(x.startswith(f"syntax {srt} ") or x == f"syntax {srt}" for x in self.sentences):
                self.sentences.insert(0, f"syntax {srt}")
        # Interleave sentence order a bit: K is declarative, order should not matter.
        if self.p(0.2):
            r.shuffle(self.sentences)
        lines = ["module MAIN" + (self.attr_text([(r.choice(["private", "not-lr1", "haskell", "symbolic"]), None)]) if self.p(0.03) else "")]
        for imp in imports:
            vis = ""
            if self.p(0.1):
                vis = r.choice(["public ", "private "])
            lines.append(f"  imports {vis}{imp}")
        for s in self.sentences:
            lines.append("  " + s.replace("\n", "\n  "))
        lines.append("endmodule")
        return "\n".join(lines) + "\n"

    # ---------- syntax ----------
    def gen_parametric(self):
        r = self.r
        if self.p(0.2):
            # parametric production: {S} S ::= name(S, ...)
            name = self.fresh(r.choice(["sel", "id", "wrap", "dup", "pick"]))
            if "BOOL" in self.mods and self.p(0.5):
                args = ["Bool", "S", "S"]
            else:
                args = ["S"] * r.randint(1, 2)
            attrs = [("function", None)] if self.p(0.7) else []
            if self.p(0.6):
                attrs.append(("symbol", name))
            prod = Prod("S", "prefix", args, name, attrs, params=("S",))
            self.prods.append(prod)
            self.sentences.append(f"syntax {{S}} S ::= {name}({', '.join(args)}){self.attr_text(attrs)}")
        if self.p(0.03) and self.sorts:
            # Parametric sort with explicit instances: mostly the builtin MInt{W}, otherwise a
            # user parametric sort (documented as unsupported). MInt is hooked (MINT.MInt), so
            # its values are fixed by the hook and its productions must be functions.
            base = "MInt" if self.p(0.85) else r.choice(["Box", "MW"])
            fun = "function, " if base == "MInt" else ""
            inst = r.sample(self.sorts, min(len(self.sorts), r.randint(1, 2)))
            if self.p(0.1):  # generic parametric sort declaration (documented as unsupported)
                self.sentences.append(f"syntax {{P}} {base}{{P}}")
            for i in inst:
                self.sentences.append(f"syntax {base}{{{i}}}")
            name = self.fresh("box")
            if self.p(0.5):
                self.sentences.append(f"syntax {{P}} {base}{{P}} ::= {name}(P) [{fun}symbol({name})]")
            else:  # instance-level productions (tests/fixtures/sort-check/result-instance.k shape)
                self.sentences.append(f'syntax {base}{{{inst[0]}}} ::= "{name}" [{fun}symbol({name})]')
            if self.p(0.6):
                sup = r.choice(self.sorts)
                self.sentences.append(f"syntax {sup} ::= {base}{{{inst[0]}}}")

    def gen_subsorts(self):
        r = self.r
        cands = self.all_sorts(include_k=False)
        for _ in range(r.randint(0, 3)):
            if len(cands) < 2:
                break
            sup = r.choice(self.sorts)
            sub = r.choice(cands)
            if sub == sup:
                continue
            if self.leq(sup, sub) and not self.p(0.1):  # avoid cycles except as a MUTATION
                continue
            if sup in ("Int", "Bool", "String"):
                continue
            self.subsorts.add((sub, sup))
            self.prods.append(Prod(sup, "sub", [sub], None, []))
            attrs = []
            if self.p(0.05):
                attrs.append((r.choice(["prefer", "avoid", "private"]), None))
            self.sentences.append(f"syntax {sup} ::= {sub}{self.attr_text(attrs)}")
        if "KResult" not in self.sorts and self.p(0.15) and self.sorts:
            self.kresult = True
            v = r.choice(self.sorts + [s for s in ("Int", "Bool") if s in self.builtin_sorts()])
            self.sentences.append(f"syntax KResult ::= {v}")
            self.subsorts.add((v, "KResult"))

    def prod_attrs(self, prod, function):
        r = self.r
        attrs = []
        if function:
            attrs.append(("function", None))
            if self.p(0.3):
                attrs.append(("total", None))
            elif self.p(0.05):
                attrs.append(("functional", None))
        if self.p(0.6):
            attrs.append(("symbol", prod.name_sym))
        elif self.p(0.1):
            attrs.append(("klabel", prod.name_sym))
        if prod.kind == "infix" and self.p(0.4) and (prod.args == [prod.sort, prod.sort] or self.p(0.1)):
            key = r.choice(["left", "right", "non-assoc"])
            if self.assoc_ok(prod, key):
                attrs.append((key, None))
        if not function and prod.args and self.p(0.06):
            attrs.append(("strict", None if self.p(0.6) else str(r.randint(1, len(prod.args)))))
            self.need_kresult = True
        if self.p(0.08):
            attrs.append(("format", " ".join(f"%{i + 1}" for i in range(prod.n_items))))
        if self.p(0.05):
            attrs.append(("color", r.choice(["red", "blue"])))
        if self.p(0.04):
            attrs.append(("latex", "{#1}"))
        if self.p(0.04):
            attrs.append(("group", r.choice(["g1", "g2"])))
        if function and self.p(0.05):
            attrs.append(("memo", None))
        if function and self.p(0.03):
            attrs.append(("smtlib", prod.name_sym))
        if function and self.p(0.03):
            attrs.append(("impure", None))
        if function and self.p(0.03):
            attrs.append(("no-evaluators", None))
        if not function and self.p(0.05):
            attrs.append(("injective", None))
        if self.p(0.03):
            attrs.append(("deprecated", None))
        if self.p(0.03):
            attrs.append(("unused", None))
        if self.p(0.03):
            attrs.append(("prefer" if self.p(0.5) else "avoid", None))
        if self.p(0.04):
            attrs.append(("private", None))
        # MUTATION: a random production key with a syntactically legal parameter.
        if self.p(0.025):
            k = r.choice(PROD_FORBIDDEN + PROD_REQUIRED + PROD_OPTIONAL)
            if k in PROD_REQUIRED:
                v = {"hook": r.choice(["INT.add", "BOOL.and", "STRING.concat", "FOO.bar", "MAP.element"]),
                     "priority": str(r.choice([10, 50, 200])),
                     "prec": "1", "applyPriority": "1", "index": "0",
                     "result": r.choice(self.all_sorts()),
                     "unit": "." + r.choice(self.sorts or ["X"]), "type": "Map",
                     "multiplicity": "*", "overload": "ov"}.get(k, prod.name_sym)
                attrs.append((k, v))
            elif k in PROD_OPTIONAL:
                attrs.append((k, None))
            else:
                attrs.append((k, None))
        # dedupe keys (duplicate keys are a fatal parse error; keep only first)
        seen, out = set(), []
        for k, v in attrs:
            if k not in seen:
                seen.add(k)
                out.append((k, v))
        return out

    def gen_production(self, sort):
        r = self.r
        cands = self.all_sorts(include_k=self.p(0.15))
        function = self.p(0.3) or (sort in HOOKED and not self.p(0.03))
        roll = r.random()
        if roll < 0.25:
            word = self.fresh(r.choice(TERMINAL_WORDS)) if self.p(0.95) else r.choice(TERMINAL_WORDS)
            prod = Prod(sort, "const", [], word, [])
            prod.n_items = 1
            text = f'"{word}"'
        elif roll < 0.6:
            name = self.fresh(r.choice(TERMINAL_WORDS)) if self.p(0.95) else r.choice(TERMINAL_WORDS)
            args = [r.choice(cands) for _ in range(r.randint(1, 3))]
            prod = Prod(sort, "prefix", args, name, [])
            prod.n_items = len(args)
            if self.p(0.2):
                names = [f"{c}{i}" for i, c in enumerate("abcd"[:len(args)])]
                text = f"{name}(" + ", ".join(f"{n}: {a}" for n, a in zip(names, args)) + ")"
            elif self.p(0.25):
                text = f'"{name}" "(" ' + ' "," '.join(args) + ' ")"'
            else:
                text = f"{name}(" + ", ".join(args) + ")"
        elif roll < 0.85:
            op = r.choice(INFIX_OPS)
            if self.p(0.3):
                op = op + str(self.counter + 1)
                self.counter += 1
            a = sort if self.p(0.7) else r.choice(cands)
            b = sort if self.p(0.7) else r.choice(cands)
            prod = Prod(sort, "infix", [a, b], op, [])
            prod.n_items = 3
            text = f'{a} "{op}" {b}'
        else:
            word = self.fresh(r.choice(TERMINAL_WORDS))
            args = [r.choice(cands) for _ in range(r.randint(1, 2))]
            prod = Prod(sort, "mixfix", args, word, [])
            prod.n_items = 1 + 2 * len(args)
            text = f'"{word}" ' + " ".join(f'{a} ";"' for a in args)
        prod.name_sym = self.fresh("s")
        prod.attrs = self.prod_attrs(prod, function)
        self.prods.append(prod)
        return text + self.attr_text(prod.attrs)

    def gen_production_sentence(self):
        r = self.r
        if self.sorts and self.p(0.75):
            sort = r.choice(self.sorts)
        else:
            sort = r.choice(self.all_sorts(include_k=self.p(0.3)))
        if sort == "K" and self.p(0.7):
            sort = "KItem"
        n_blocks = 1 if self.p(0.75) else 2
        blocks = []
        for _ in range(n_blocks):
            assoc = ""
            if n_blocks > 1 and self.p(0.4):
                # A block prefix relates the block's productions to each other; unlike the
                # production attribute, it is legal whatever their argument sorts.
                assoc = r.choice(["left", "right", "non-assoc"]) + ": "
            alts = [self.gen_production(sort) for _ in range(r.randint(1, 3))]
            blocks.append(assoc + "\n    | ".join(alts))
        self.sentences.append(f"syntax {sort} ::= " + "\n    > ".join(blocks))

    def gen_list_sort(self):
        r = self.r
        if not self.sorts:
            return
        elem = r.choice(self.all_sorts(include_k=False))
        lst = elem + "s" if elem + "s" not in self.all_sorts() else self.fresh("Lst")
        if not lst[0].isupper():
            lst = "L" + lst
        sep = r.choice([",", ";", ""])
        kind = "NeList" if self.p(0.25) else "List"
        attrs = []
        if self.p(0.5):
            attrs.append(("symbol", self.fresh("cons")))
        if self.p(0.3):
            attrs.append(("terminator-symbol", self.fresh("nil")))
        self.list_sorts[lst] = elem
        self.prods.append(Prod(lst, "list", [elem], sep, attrs))
        self.sentences.append(f'syntax {lst} ::= {kind}{{{elem}, "{sep}"}}{self.attr_text(attrs)}')
        if self.p(0.4):
            holder = r.choice(self.sorts)
            name = self.fresh("blk")
            self.prods.append(Prod(holder, "prefix", [lst], name, [("symbol", name)]))
            self.sentences.append(f"syntax {holder} ::= {name}({lst}) [symbol({name})]")

    def gen_token_sort(self):
        r = self.r
        t = r.choice(["Name", "Word", "Num"])
        if t in self.tokens:
            return
        self.tokens.append(t)
        regex = {"Name": "[a-z][a-z0-9]*", "Word": "[A-Z][a-z]+", "Num": "0x[0-9a-f]+"}[t]
        attrs = [("token", None)]
        if self.p(0.3):
            attrs.append(("prec", "2"))
        self.sentences.append(f'syntax {t} ::= r"{regex}"{self.attr_text(attrs)}')
        if self.sorts and self.p(0.6):
            sup = r.choice(self.sorts)
            self.subsorts.add((t, sup))
            self.prods.append(Prod(sup, "sub", [t], None, []))
            self.sentences.append(f"syntax {sup} ::= {t}")

    def gen_synonym(self):
        r = self.r
        target = r.choice(self.all_sorts(include_k=False) or ["K"])
        alias = r.choice(["Alias", "Syn", "Other"])
        if alias in self.synonyms:
            return
        self.synonyms[alias] = target
        self.sentences.append(f"syntax {alias} = {target}")
        if self.p(0.7):
            name = self.fresh("viaSyn")
            sort = r.choice(self.sorts) if self.sorts else target
            self.prods.append(Prod(sort, "prefix", [target], name, [("symbol", name)]))
            self.sentences.append(f"syntax {sort} ::= {name}({alias}) [symbol({name})]")

    def gen_user_collection(self):
        r = self.r
        kind = r.choice(["Map", "Set", "List"])
        if kind not in self.builtin_sorts():
            return
        s = "My" + kind
        u, e, c = self.fresh("unit"), self.fresh("elem"), self.fresh("cat")
        hk = kind.upper()
        lines = [f"syntax {s} [hook({hk}.{kind})]"]
        assoc = "assoc, comm" if kind != "List" else "assoc"
        if kind == "Map":
            lines.append(f'syntax {s} ::= {s} {s} [left, function, hook(MAP.concat), symbol({c}), {assoc}, unit({u}), element({e}), index(0)]')
            lines.append(f'syntax {s} ::= "{u}" [function, total, hook(MAP.unit), symbol({u})]')
            lines.append(f'syntax {s} ::= KItem "{e}" KItem [function, total, hook(MAP.element), symbol({e}), injective]')
        else:
            lines.append(f'syntax {s} ::= {s} {s} [left, function, total, hook({hk}.concat), symbol({c}), {assoc}, unit({u}), element({e})]')
            lines.append(f'syntax {s} ::= "{u}" [function, total, hook({hk}.unit), symbol({u})]')
            lines.append(f'syntax {s} ::= {e}(KItem) [function, total, hook({hk}.element), symbol({e})]')
        self.sentences.extend(lines)
        self.coll = (s, kind, u, e)

    def gen_priority_assoc(self):
        r = self.r
        syms = [p for p in self.prods if p.has("symbol") or p.has("group")]
        if len(syms) < 1:
            return
        def tag(p):
            for k, v in p.attrs:
                if k in ("symbol", "group"):
                    return v
        if len(syms) >= 2 and self.p(0.6):
            a, b = r.sample(syms, 2)
            self.sentences.append(f"syntax priority {tag(a)} > {tag(b)}")
        else:
            a = r.choice(syms)
            self.sentences.append(f"syntax {r.choice(['left', 'right', 'non-assoc'])} {tag(a)}")

    def gen_strict(self):
        r = self.r
        if not self.sorts:
            return
        sort = r.choice(self.sorts)
        name = self.fresh(r.choice(["add", "seq", "app", "cond"]))
        n = r.randint(1, 3)
        attr = r.choice(["strict", "seqstrict", "strict(1)", "seqstrict(1)", f"strict({n})"])
        k, _, v = attr.partition("(")
        attrs = [(k, v.rstrip(")") or None), ("symbol", name)]
        self.prods.append(Prod(sort, "prefix", [sort] * n, name, attrs))
        self.sentences.append(f"syntax {sort} ::= {name}({', '.join([sort] * n)}){self.attr_text(attrs)}")
        if not self.kresult and self.p(0.95):
            self.kresult = True
            res = "Int" if "Int" in self.builtin_sorts() else sort
            if res == sort:
                v = self.fresh("val")
                self.prods.append(Prod(sort, "const", [], v, [("symbol", v)]))
                self.sentences.append(f'syntax Val{self.counter} ::= "{v}" [symbol({v})]')
                res = f"Val{self.counter}"
                self.sorts.append(res)
                self.prods[-1].sort = res
                self.subsorts.add((res, sort))
                self.sentences.append(f"syntax {sort} ::= {res}")
            else:
                self.subsorts.add((res, sort))
                self.prods.append(Prod(sort, "sub", [res], None, []))
                self.sentences.append(f"syntax {sort} ::= {res}")
            self.sentences.append(f"syntax KResult ::= {res}")
        if self.p(0.3):
            hole_pos = r.randrange(n)
            args = ["HOLE" if i == hole_pos else "_" for i in range(n)]
            self.sentences.append(f"context {name}({', '.join(args)})")
        if self.p(0.1):
            self.sentences.append(f"context alias [{self.fresh('ca')}]: <k> HERE:K ... </k>")

    # ---------- configuration ----------
    def init_value(self, sort):
        """A configuration cell's sort is the (least) sort of its initial value, so the value
        must have exactly `sort`: a literal of that sort or a production whose result is it."""
        lit = self.lit(sort)
        exact = [p for p in self.prods if p.sort == sort and p.params == () and not p.is_function
                 and p.kind in ("const", "prefix", "mixfix", "infix")]
        if lit is not None and (not exact or self.p(0.5)):
            return lit
        if not exact:
            return None
        p = self.r.choice(exact)
        try:
            return self.render(p, 2, {}, False, True, None)
        except Fail:
            return None

    def gen_configuration(self):
        r = self.r
        self.has_config = True
        pgm_sort = r.choice(self.all_sorts(include_k=True))
        cells = [("k", f"$PGM:{pgm_sort}" if self.p(0.7) else ".K", "K")]
        self.cells.append(("k", "K", None))
        for _ in range(r.randint(0, 3)):
            name = r.choice(CELL_NAMES[1:])
            if any(c[0] == name for c in self.cells):
                continue
            sort = r.choice(self.all_sorts(include_k=False) or ["K"])
            exit_cell = self.p(0.05)
            if exit_cell and "Int" in self.builtin_sorts() and self.p(0.7):
                sort = "Int"
            init = None if self.p(0.15) else self.init_value(sort)
            if init is None:
                init = f"${name.upper()}:{sort}"
            attrs = ""
            mult = None
            if self.p(0.1):
                mult = "?"
                attrs = ' multiplicity="?"'
            if exit_cell:
                attrs += ' exit=""'
            if self.p(0.05):
                attrs += ' color="red"'
            self.cells.append((name, sort, mult))
            cells.append((name, init, sort, attrs))
        body = []
        for c in cells:
            if len(c) == 3:
                body.append(f"<{c[0]}> {c[1]} </{c[0]}>")
            else:
                body.append(f"<{c[0]}{c[3]}> {c[1]} </{c[0]}>")
        if self.p(0.12) and "MAP" in self.mods:
            # collection cell with multiplicity *
            typ = r.choice(["Map", "Set", "List"]) if self.p(0.9) else None
            ta = f' type="{typ}"' if typ else ""
            init_id = "0" if "INT" in self.mods else ".K"
            body.append(f'<threads> <thread multiplicity="*"{ta}> <tid> {init_id} </tid> <tk> .K </tk> </thread> </threads>')
            self.cells.append(("tid", "Int" if init_id == "0" else "K", "*"))
        if self.p(0.04) and "LIST" in self.mods and "STRING" in self.mods:
            body.append('<in stream="stdin"> .List </in>')
        wrap = self.p(0.5)
        inner = " ".join(body)
        if wrap:
            top = r.choice(["T", "top", "generatedTop0"])
            inner = f"<{top}> {inner} </{top}>"
        self.sentences.append("configuration " + inner)

    # ---------- terms ----------
    def lit(self, sort):
        r = self.r
        if sort == "Int":
            return str(r.choice([0, 1, 2, 7, 42, -3])) if self.p(0.9) else "123456789012345678901234567890"
        if sort == "Bool":
            return r.choice(["true", "false"])
        if sort == "String":
            return r.choice(['"a"', '""', '"hello world"', '"\\n"'])
        if sort == "Float":
            return r.choice(["1.0", "0.5", "2.5e3"])
        if sort == "Bytes":
            return 'b"ab"'
        if sort == "Map":
            return ".Map"
        if sort == "Set":
            return ".Set"
        if sort == "List":
            return ".List"
        if sort in ("K",):
            return ".K"
        return None

    def term(self, sort, depth, env, lhs, constructors_only=False, binders=None):
        """Generate a term of sort `sort` (or a subsort). env: name -> sort of bound vars.
        On the LHS, new variables are added to `binders`. Returns None if impossible."""
        r = self.r
        sort = self.synonyms.get(sort, sort)
        options = []
        # variables
        if not constructors_only:
            if lhs:
                options.append(("newvar", 3))
                options.append(("anon", 0.6))
            else:
                if any(self.leq(s, sort) for s in env.values()):
                    options.append(("var", 4))
        if self.lit(sort) is not None:
            options.append(("lit", 2))
        if self.allow_fresh and not lhs and not constructors_only and (
                (sort == "Int" and "INT" in self.mods) or (sort == "Id" and "ID" in self.mods)):
            options.append(("fresh", 0.7))
        cands = [p for p in self.prods if p.kind not in ("sub",) and p.params == ()
                 and self.leq(p.sort, sort)
                 and not ((lhs or constructors_only) and p.is_function)]
        if cands and depth > 0:
            options.append(("prod", 4))
        elif cands:
            consts = [p for p in cands if p.kind == "const"]
            if consts:
                options.append(("const", 3))
        if not lhs and not constructors_only and depth > 0:
            if sort in ("Int", "K", "KItem") and "INT" in self.mods:
                options.append(("intop", 1.5))
            if sort in ("Bool",) and "BOOL" in self.mods:
                options.append(("boolop", 1.5))
            if sort == "Bool" and "INT" in self.mods and "BOOL" in self.mods:
                options.append(("cmp", 1.5))
            if sort == "Bool" and "K-EQUAL" in self.mods:
                options.append(("keq", 1))
            if "K-EQUAL" in self.mods and "BOOL" in self.mods:
                options.append(("ite", 0.4))
            if sort in ("Map",) and "MAP" in self.mods:
                options.append(("mapop", 1))
            if sort in ("List",) and "LIST" in self.mods:
                options.append(("listop", 1))
            if sort in ("Set",) and "SET" in self.mods:
                options.append(("setop", 1))
            if sort in ("Int",) and ("MAP" in self.mods or "LIST" in self.mods) and "INT" in self.mods:
                options.append(("size", 0.5))
            par = [p for p in self.prods if p.params]
            if par:
                options.append(("param", 0.6))
            if sort in ("String",) and "STRING" in self.mods:
                options.append(("strop", 1))
        if depth > 0 and sort in ("K",):
            options.append(("seq", 0.8))
        if depth > 0 and sort in ("K", "KItem"):
            options.append(("anysort", 2))
        if depth > 0 and not constructors_only and self.p(0.5):
            options.append(("cast", 0.7))
        if lhs and depth > 0 and "MAP" in self.mods and sort == "Map":
            options.append(("mappat", 1))
        if lhs and depth > 0 and "LIST" in self.mods and sort == "List":
            options.append(("listpat", 1))
        if not options:
            return None
        total = sum(w for _, w in options)
        pick = r.random() * total
        for kind, w in options:
            pick -= w
            if pick <= 0:
                break
        if kind == "newvar":
            v = self.fresh_var()
            if binders is not None:
                binders[v] = sort
            if self.p(0.5) and sort not in ("K",):
                return f"{v}:{sort}"
            return f"{v}:{sort}" if self.p(0.6) else v
        if kind == "fresh":
            self.counter += 1
            return f"!F{self.counter}:{sort}"
        if kind == "anon":
            return "_" if self.p(0.6) else f"_:{sort}"
        if kind == "var":
            vs = [n for n, s in env.items() if self.leq(s, sort)]
            return r.choice(vs)
        if kind == "lit":
            return self.lit(sort)
        if kind in ("prod", "const"):
            if kind == "const":
                cands = [p for p in cands if p.kind == "const"]
            p = r.choice(cands)
            return self.render(p, depth, env, lhs, constructors_only, binders)
        def sub(s):
            t = self.term(s, depth - 1, env, lhs, constructors_only, binders)
            if t is None:
                raise Fail()
            return t
        if kind == "intop":
            a, b = sub("Int"), sub("Int")
            return f"({a} {r.choice(['+Int', '-Int', '*Int', '/Int', '%Int', 'maxInt'] if False else ['+Int', '-Int', '*Int', '/Int', '%Int'])} {b})"
        if kind == "boolop":
            if self.p(0.3):
                return f"(notBool {sub('Bool')})"
            return f"({sub('Bool')} {r.choice(['andBool', 'orBool', 'xorBool', 'impliesBool'])} {sub('Bool')})"
        if kind == "cmp":
            return f"({sub('Int')} {r.choice(['<Int', '<=Int', '==Int', '=/=Int', '>Int'])} {sub('Int')})"
        if kind == "keq":
            s = r.choice(self.all_sorts(include_k=False) or ["KItem"])
            return f"({sub(s)} {r.choice(['==K', '=/=K'])} {sub(s)})"
        if kind == "ite":
            return f"(#if {sub('Bool')} #then {sub(sort)} #else {sub(sort)} #fi)"
        if kind == "mapop":
            c = r.random()
            if c < 0.4:
                return f"(({sub('KItem')}) |-> ({sub('KItem')}))"
            if c < 0.7:
                return f"({sub('Map')}[{sub('KItem')} <- {sub('KItem')}])"
            return f"({sub('Map')} {sub('Map')})"
        if kind == "listop":
            return r.choice([f"ListItem({sub('KItem')})", f"({sub('List')} {sub('List')})"])
        if kind == "setop":
            return r.choice([f"SetItem({sub('KItem')})", f"({sub('Set')} {sub('Set')})"])
        if kind == "size":
            col = r.choice([c for c in ("Map", "List") if c in self.builtin_sorts()] or ["Map"])
            return f"size({sub(col)})"
        if kind == "strop":
            return f"({sub('String')} +String {sub('String')})"
        if kind == "param":
            p = r.choice([p for p in self.prods if p.params])
            args = []
            for a in p.args:
                args.append(sub(sort if a == "S" else a))
            if any(a is None for a in args):
                return None
            return f"{p.name}({', '.join(args)})"
        if kind == "seq":
            return f"{sub('KItem')} ~> {sub('K')}"
        if kind == "anysort":
            s = r.choice(self.all_sorts(include_k=False) or ["K"])
            return sub(s)
        if kind == "cast":
            c = r.random()
            if lhs:
                if c < 0.5:
                    v = self.fresh_var()
                    if binders is not None:
                        binders[v] = sort
                    return f"{v}::{sort}"
                inner = sub(sort)
                return None if inner is None else f"({inner}):{sort}"
            if c < 0.5:
                s2 = r.choice(self.all_sorts(include_k=False) or [sort])
                inner = sub("K") if self.p(0.3) else sub(s2)
                return None if inner is None else f"{{{inner}}}:>{sort}"
            inner = sub(sort)
            return None if inner is None else f"({inner}):{sort}"
        if kind == "mappat":
            return f"((({sub('KItem')}) |-> ({sub('KItem')})) {sub('Map')})"
        if kind == "listpat":
            return f"(ListItem({sub('KItem')}) {sub('List')})"
        return None

    def render(self, p, depth, env, lhs, constructors_only, binders):
        def sub(s):
            t = self.term(s, depth - 1, env, lhs, constructors_only, binders)
            if t is None:
                raise Fail()
            return t
        if p.kind == "const":
            return p.name
        if p.kind == "token":
            return p.name
        if p.kind == "list":
            n = self.r.randint(0, 2)
            if n == 0:
                return f".{p.sort}"
            items = [sub(p.args[0]) for _ in range(n)]
            if any(i is None for i in items):
                return None
            joiner = f" {p.name} " if p.name else " "
            return "(" + joiner.join(f"({i})" for i in items) + ")"
        args = [sub(a) for a in p.args]
        if any(a is None for a in args):
            return None
        if p.kind == "prefix":
            return f"{p.name}(" + ", ".join(args) + ")"
        if p.kind == "infix":
            return f"(({args[0]}) {p.name} ({args[1]}))"
        if p.kind == "mixfix":
            return f"({p.name} " + " ".join(f"({a}) ;" for a in args) + ")"
        return None

    # ---------- sentences ----------
    def rule_attrs(self, kind):
        r = self.r
        attrs = []
        simp = kind == "function" and self.p(0.1)
        if self.p(0.08) and not simp:
            attrs.append(("priority", str(r.choice([10, 49, 51, 200]))))
        if self.p(0.08):
            attrs.append(("label", self.fresh("lbl")))
        if kind == "function" and not simp and self.p(0.1):
            attrs.append(("owise", None))
        if simp:
            attrs.append(("simplification", None if self.p(0.6) else str(r.choice([10, 60]))))
            if self.p(0.3):
                attrs.append((r.choice(["concrete", "symbolic"]), None))
        if kind == "rewrite" and self.p(0.04):
            attrs.append(("anywhere", None))
        if self.p(0.03):
            attrs.append(("preserves-definedness", None))
        if self.p(0.003):
            attrs.append(("smt-lemma", None))
        if kind == "function" and self.p(0.03):
            attrs.append(("non-executable", None))
        # MUTATION: random rule key
        if self.p(0.04):
            k = r.choice(RULE_KEYS_FORBIDDEN + RULE_KEYS_OPTIONAL + RULE_KEYS_REQUIRED)
            if k in RULE_KEYS_REQUIRED:
                attrs.append((k, {"priority": "5", "result": r.choice(self.all_sorts())}.get(k, self.fresh("x"))))
            else:
                attrs.append((k, None))
        seen, out = set(), []
        for k, v in attrs:
            if k not in seen:
                seen.add(k)
                out.append((k, v))
        return out

    def condition(self, env):
        if "BOOL" not in self.mods or not self.p(0.35):
            return ""
        try:
            c = self.term("Bool", 2, env, lhs=False)
        except Fail:
            c = None
        if c is None:
            return ""
        if self.p(0.15):
            return f" ensures {c}"
        return f" requires {c}"

    def gen_rule(self):
        try:
            self._gen_rule()
        except Fail:
            pass
        finally:
            self.allow_fresh = False

    def _gen_rule(self):
        r = self.r
        funcs = [p for p in self.prods if p.is_function and p.kind != "sub" and not p.params]
        cons = [p for p in self.prods if not p.is_function and p.kind not in ("sub", "list") and not p.params]
        roll = r.random()
        label = f"[{self.fresh('r')}]: " if self.p(0.15) else ""
        if funcs and roll < 0.45:
            f = r.choice(funcs)
            binders = {}
            if f.kind == "const":
                lhs = f.name
            else:
                args = [self.term(a, 2, {}, lhs=True, binders=binders) for a in f.args]
                if any(a is None for a in args):
                    return
                lhs = self.render_with(f, args)
            rhs = self.term(f.sort, 3, binders, lhs=False)
            if rhs is None:
                return
            cond = self.condition(binders)
            self.sentences.append(f"rule {label}{lhs} => {rhs}{cond}{self.attr_text(self.rule_attrs('function'))}")
            return
        if self.has_config and roll < 0.75:
            self.allow_fresh = self.p(0.5)
            # cell rule
            binders = {}
            parts = []
            cells = [c for c in self.cells if c[2] != "*"]
            chosen = [c for c in cells if c[0] == "k" or self.p(0.4)]
            if not chosen:
                return
            pending = []
            for name, sort, mult in chosen:
                s = sort if sort != "K" else "KItem"
                lhs_t = self.term(s, 2, {}, lhs=True, binders=binders)
                if lhs_t is None:
                    return
                pending.append((name, s, lhs_t))
            must = self.r.randrange(len(pending))
            for i, (name, s, lhs_t) in enumerate(pending):
                if i == must or self.p(0.6):
                    rhs_t = self.term(s, 2, binders, lhs=False)
                    if rhs_t is None:
                        return
                    body = f"{lhs_t} => {rhs_t}"
                else:
                    body = lhs_t
                frame = " ..." if name == "k" and self.p(0.7) else ""
                parts.append(f"<{name}> {body}{frame} </{name}>")
            cond = self.condition(binders)
            self.sentences.append(f"rule {label}" + " ".join(parts) + cond + self.attr_text(self.rule_attrs("rewrite")))
            return
        if cons:
            self.allow_fresh = self.p(0.3)
            p = r.choice(cons)
            binders = {}
            lhs = self.render(p, 2, {}, True, False, binders)
            if lhs is None:
                return
            if self.p(0.2) and p.kind == "prefix" and len(p.args) >= 1:
                # local rewrite inside a constructor argument
                i = r.randrange(len(p.args))
                args = []
                binders2 = {}
                for j, a in enumerate(p.args):
                    t = self.term(a, 1, {}, lhs=True, binders=binders2)
                    if t is None:
                        return
                    args.append(t)
                rhs_i = self.term(p.args[i], 1, binders2, lhs=False)
                if rhs_i is None:
                    return
                args[i] = f"{args[i]} => {rhs_i}"
                self.sentences.append(f"rule {label}{p.name}(" + ", ".join(args) + ")" + self.attr_text(self.rule_attrs("rewrite")))
                return
            rhs = self.term(p.sort, 2, binders, lhs=False)
            if rhs is None:
                return
            cond = self.condition(binders)
            self.sentences.append(f"rule {label}{lhs} => {rhs}{cond}{self.attr_text(self.rule_attrs('rewrite'))}")
            return
        # macro / alias production with its defining rule
        if self.sorts:
            sort = r.choice(self.sorts)
            rhs = self.term(sort, 2, {}, lhs=False, constructors_only=True)
            if rhs is None:
                return
            name = self.fresh("m")
            kind = r.choice(["macro", "alias", "macro-rec"])
            self.sentences.append(f'syntax {sort} ::= "{name}" [{kind}]')
            self.sentences.append(f"rule {name} => {rhs}")

    def render_with(self, f, args):
        if f.kind == "prefix":
            return f"{f.name}(" + ", ".join(args) + ")"
        if f.kind == "infix":
            return f"(({args[0]}) {f.name} ({args[1]}))"
        if f.kind == "mixfix":
            return f"{f.name} " + " ".join(f"({a}) ;" for a in args)
        return f.name

    def gen_claim(self):
        try:
            self._gen_claim()
        except Fail:
            pass

    def _gen_claim(self):
        if not self.has_config:
            return
        binders = {}
        lhs = self.term("KItem", 1, {}, lhs=True, binders=binders)
        rhs = self.term("KItem", 1, binders, lhs=False)
        if lhs and rhs:
            self.sentences.append(f"claim <k> {lhs} => {rhs} </k>")


def usage():
    print("usage: gen.py OUT_DIR [--count N] [--seed S]", file=sys.stderr)
    sys.exit(2)


def main():
    args = sys.argv[1:]
    if not args or args[0].startswith("--"):
        usage()
    out = args.pop(0)
    count = 1000
    seed = 1
    try:
        while args:
            a = args.pop(0)
            if a == "--count":
                count = int(args.pop(0))
            elif a == "--seed":
                seed = int(args.pop(0))
            else:
                usage()
    except (IndexError, ValueError):
        usage()
    os.makedirs(out, exist_ok=True)
    width = max(4, len(str(count - 1)))
    started = time.time()
    for i in range(count):
        case_seed = seed * 1_000_003 + i
        g = Gen(random.Random(case_seed))
        text = g.definition()
        with open(os.path.join(out, f"{i:0{width}d}.k"), "w") as fh:
            fh.write(f"// generated by scripts/generative/gen.py, case seed {case_seed}\n" + text)
    print(f"generated {count} definitions in {time.time() - started:.2f}s", file=sys.stderr)


if __name__ == "__main__":
    main()
