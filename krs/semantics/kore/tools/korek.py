#!/usr/bin/env python3
"""KORE text reader, the encoder of an object definition for kore.k, and the decoders that put
kore.k's result and the reference backends' results in one canonical form.

  korek.py encode DEF.kompile.KORE PGM.KORE OUT.pgm SYMBOLS.json
      DEF.kompile.KORE: kompile's definition.kore of the object definition; PGM.KORE: the initial
      term as KORE (kast --output kore); writes kore.k's program and the numbering of symbols and
      sorts.
  korek.py ref SYMBOLS.json KRUN-OUTPUT.kore          -> JSON list of canonical final terms
  korek.py korek SYMBOLS.json KORE-K-OUTPUT.kore      -> JSON list of canonical final terms

KRUN-OUTPUT is `krun --search --output kore` on the object definition; KORE-K-OUTPUT is
`krust krun --definition <kore.k kompiled by krust kcompile> --sort Pgm` on the encoded program.

The encoder is mechanical: it reads the axioms whose Source is the object definition's file
(rewrite rules and function equations), the stated subsort axioms except those into KItem and K
and those between generated cell sorts, and the declarations of the symbols the axioms apply.
A configuration of the one cell <k> (<generatedTop>(<k>(kseq(inj{S,KItem}(X), dotk())), DotVar))
is stripped to the item inj{S,KItem}(X) the cell holds; a configuration of several cells to its top
cell (<generatedTop>(<T>(...), DotVar) -> <T>(...)), every cell an application of its constructor
and the <k> cell's content a K sequence (kseq, dotk). The initial configuration is the value of
the definition's topCellInitializer at the program: kompile's initializer equations unfolded, and
the projection of the configuration variable $PGM read as the program, stripped the same way.
"""
import json
import re
import sys

# ------------------------------------------------------------------ reading KORE text

TOKEN = re.compile(r'''\s+|//[^\n]*|/\*.*?\*/|"(?:[^"\\]|\\.)*"|:=|[{}()\[\],:]|[\\@]?[A-Za-z0-9'_\-#]+''', re.S)


def tokenize(text):
    pos = 0
    out = []
    while pos < len(text):
        m = TOKEN.match(text, pos)
        if not m:
            raise ValueError(f'bad KORE at {pos}: {text[pos:pos + 40]!r}')
        t = m.group(0)
        pos = m.end()
        if t[0].isspace() or t.startswith('//') or t.startswith('/*'):
            continue
        out.append(t)
    return out


class P:
    def __init__(self, toks):
        self.t = toks
        self.i = 0

    def peek(self, k=0):
        return self.t[self.i + k] if self.i + k < len(self.t) else None

    def next(self):
        x = self.t[self.i]
        self.i += 1
        return x

    def expect(self, x):
        y = self.next()
        if y != x:
            raise ValueError(f'expected {x!r}, got {y!r} at token {self.i}: {" ".join(self.t[self.i - 5:self.i + 5])}')

    def sort(self):
        name = self.next()
        if self.peek() == '{':
            self.next()
            args = self.list_until('}', self.sort)
            return (name, tuple(args))
        return (name, None)  # a sort variable

    def list_until(self, close, item):
        out = []
        if self.peek() == close:
            self.next()
            return out
        while True:
            out.append(item())
            x = self.next()
            if x == close:
                return out
            if x != ',':
                raise ValueError(f'expected , or {close}, got {x!r}')

    def pattern(self):
        t = self.next()
        if t.startswith('"'):
            return ('str', json.loads(t))
        if self.peek() == ':':
            self.next()
            return ('var', t, self.sort())
        self.expect('{')
        sorts = self.list_until('}', self.sort)
        self.expect('(')
        args = self.list_until(')', self.pattern)
        return ('app', t, tuple(sorts), tuple(args))

    def attrs(self):
        self.expect('[')
        return self.list_until(']', self.pattern)


def attr_map(attrs):
    m = {}
    for a in attrs:
        if a[0] == 'app':
            args = a[3]
            if a[1] == 'subsort':
                m['subsort'] = a[2]
                continue
            m[a[1]] = args[0][1] if args and args[0][0] == 'str' else (args if args else True)
    return m


def read_definition(text):
    """Sentences of the last module: (kind, data, attrs)."""
    p = P(tokenize(text))
    p.attrs()
    modules = []
    while p.peek() is not None:
        p.expect('module')
        name = p.next()
        sents = []
        while p.peek() != 'endmodule':
            kw = p.next()
            if kw == 'import':
                p.next()
                p.attrs()
            elif kw in ('sort', 'hooked-sort'):
                n = p.next()
                p.expect('{')
                p.list_until('}', p.next)
                sents.append((kw, n, attr_map(p.attrs())))
            elif kw in ('symbol', 'hooked-symbol'):
                n = p.next()
                p.expect('{')
                p.list_until('}', p.next)
                p.expect('(')
                args = p.list_until(')', p.sort)
                p.expect(':')
                res = p.sort()
                sents.append((kw, (n, args, res), attr_map(p.attrs())))
            elif kw in ('axiom', 'claim'):
                p.expect('{')
                p.list_until('}', p.next)
                pat = p.pattern()
                sents.append((kw, pat, attr_map(p.attrs())))
            elif kw == 'alias':
                p.next()
                p.expect('{')
                p.list_until('}', p.next)
                p.expect('(')
                p.list_until(')', p.sort)
                p.expect(':')
                p.sort()
                p.expect('where')
                p.pattern()
                p.expect(':=')
                p.pattern()
                p.attrs()
            else:
                raise ValueError(f'unknown sentence {kw!r}')
        p.next()
        p.attrs()
        modules.append((name, sents))
    return modules


def read_pattern(text):
    p = P(tokenize(text))
    return p.pattern()

# ------------------------------------------------------------------ encoding

HOOKS = {'INT.add': 1, 'INT.sub': 2, 'INT.mul': 3, 'INT.tdiv': 4, 'INT.tmod': 5,
         'INT.lt': 10, 'INT.le': 11, 'INT.gt': 12, 'INT.ge': 13, 'INT.eq': 14, 'INT.ne': 15,
         'BOOL.and': 20, 'BOOL.or': 21, 'BOOL.not': 22, 'KEQUAL.ite': 30,
         'MAP.lookup': 40, 'MAP.lookupOrDefault': 41, 'MAP.update': 42, 'MAP.remove': 43,
         'MAP.in_keys': 44, 'MAP.size': 45, 'SET.in': 50, 'SET.size': 51, 'SET.union': 52,
         'LIST.size': 60}
# the constructors of a collection sort: its concatenation, unit and element symbols
KINDS = {'MAP': 'map', 'SET': 'set', 'LIST': 'list'}
ROLES = ('concat', 'unit', 'element')


def collection_hook(attrs):
    """(kind, role) of a collection's concatenation, unit or element symbol, else None."""
    h = attrs.get('hook', '')
    if not isinstance(h, str) or '.' not in h:
        return None
    lib, op = h.split('.', 1)
    return (KINDS[lib], op) if lib in KINDS and op in ROLES else None
FIXED_SORTS = {'SortInt': 1, 'SortBool': 2}
SOURCE = "org'Stop'kframework'Stop'attributes'Stop'Source"


def unseq(x):
    """kseq(I, dotk()) -> I: the one item a closed <k> cell holds, inj{S,KItem}(X) where X is the
    configuration's term of sort S; anything else as is. The injection into KItem is kept: rules
    match configurations at sort KItem, where an Exp pattern matches a Val result through Val < Exp."""
    if x[0] == 'app' and x[1] == 'kseq' and x[3][1][0] == 'app' and x[3][1][1] == 'dotk':
        return x[3][0]
    return x


def config_of(top):
    """The configuration a backend's <generatedTop>(TOP, COUNTER) holds: the item of a one-cell
    configuration (TOP = <k>(kseq(I, dotk()))), else the top cell TOP itself."""
    if top[0] == 'app' and top[1].startswith("Lbl'-LT-'"):
        args = top[3]
        if len(args) == 1 and args[0][0] == 'app' and args[0][1] == 'kseq':
            return unseq(args[0])
        return top
    raise Unsupported(f'configuration shape {str(top)[:200]}')


class Unsupported(Exception):
    pass


class Encoder:
    def __init__(self, modules, source, top_init=None):
        self.decls = {}
        self.subsorts = []
        self.axioms = []
        self.source = source
        self.top_init = top_init
        self.initializers = {}
        for _, sents in modules:
            for kind, data, attrs in sents:
                if kind in ('symbol', 'hooked-symbol'):
                    self.decls[data[0]] = (data, attrs)
                elif kind == 'axiom':
                    if 'subsort' in attrs:
                        self.subsorts.append(attrs['subsort'])
                    src = attrs.get(SOURCE, '')
                    if src == f'Source({source})':
                        self.axioms.append((data, attrs))
                    elif data[1] == '\\implies' and data[3][1][1] == '\\equals':
                        head = data[3][1][3][0]
                        if head[0] == 'app' and re.match(r"Lblinit\w*Cell$", head[1]):
                            self.initializers.setdefault(head[1], []).append(data)
        self.sorts = dict(FIXED_SORTS)
        self.syms = {}
        self.vars = {}
        self.in_lhs = False

    def sort(self, s):
        name = s[0]
        if name not in self.sorts:
            self.sorts[name] = 10 + len([k for k in self.sorts if k not in FIXED_SORTS])
        return self.sorts[name]

    def sym(self, name):
        if name not in self.syms:
            self.syms[name] = 1 + len(self.syms)
        return self.syms[name]

    def var(self, name):
        if name not in self.vars:
            self.vars[name] = len(self.vars)
        return self.vars[name]

    def term(self, p):
        tag = p[0]
        if tag == 'var':
            return f'vr({self.var(p[1])})'
        if tag != 'app':
            raise Unsupported(f'pattern {p}')
        _, name, sorts, args = p
        if name == '\\dv':
            s, v = sorts[0][0], args[0][1]
            if s == 'SortInt':
                return f'iv({v})'
            if s == 'SortBool':
                return f'bv({v})'
            raise Unsupported(f'domain value of {s}')
        if name == 'inj':
            return f'ij({self.sort(sorts[0])}, {self.sort(sorts[1])}, {self.term(args[0])})'
        if name == '\\and' and len(args) == 2 and args[1][0] == 'var':
            return f'as({self.term(args[0])}, {self.var(args[1][1])})'
        if name == '\\bottom':
            return 'bot'
        if name.startswith('\\'):
            raise Unsupported(f'connective {name} in a term')
        decl = self.decls.get(name)
        if decl is None:
            raise Unsupported(f'undeclared symbol {name}')
        attrs = decl[1]
        coll = collection_hook(attrs)
        if coll is not None:
            return self.collection(coll[0], decl[0][2], p)
        ts = ' ; '.join(self.term(a) for a in args)
        ts = (ts + ' ; .Ts') if args else '.Ts'
        if 'hook' in attrs:
            h = attrs['hook']
            if h not in HOOKS:
                raise Unsupported(f'hook {h} of {name}')
            return f'hk({HOOKS[h]}, {ts})'
        if 'function' in attrs and 'constructor' not in attrs and attrs.get(SOURCE) != f'Source({self.source})':
            # its equations, if any, are in K's own modules, which the encoding leaves out
            raise Unsupported(f'function {name} declared outside the object definition')
        if 'constructor' in attrs or 'function' in attrs:
            return f'ap({self.sym(name)}, {ts})'
        raise Unsupported(f'symbol {name} is neither constructor nor function')

    def parts(self, kind, sort, p):
        """The parts of a collection term of `sort`: its elements and its other terms, the
        nested concatenations, units and elements of the same sort flattened."""
        if p[0] == 'app' and p[1] in self.decls:
            (_, _, res), attrs = self.decls[p[1]]
            coll = collection_hook(attrs)
            if coll is not None and coll[0] == kind and res == sort:
                role, args = coll[1], p[3]
                if role == 'unit':
                    return []
                if role == 'element':
                    if kind == 'map':
                        return [f'kv({self.term(args[0])}, {self.term(args[1])})']
                    return [f'el({self.term(args[0])})']
                return [x for a in args for x in self.parts(kind, sort, a)]
        return [self.term(p)]

    def collection(self, kind, sort, p):
        """cb(Kind, Sort, Parts). Map and Set concatenation is commutative: their element parts
        come first. A Map or Set pattern has at most one part that is not an element."""
        ps = self.parts(kind, sort, p)
        if kind != 'list':
            elems = [x for x in ps if x.startswith(('kv(', 'el('))]
            others = [x for x in ps if not x.startswith(('kv(', 'el('))]
            if self.in_lhs and len(others) > 1:
                raise Unsupported(f'a {kind} pattern with {len(others)} frames')
            ps = elems + others
        body = ' ; '.join(ps) + ' ; .Ts' if ps else '.Ts'
        return f'cb({kind}, {self.sort(sort)}, {body})'

    def collections(self):
        """For each collection sort the encoding numbers, its kind and its constructors' names."""
        out = {}
        for name, ((_, _, res), attrs) in self.decls.items():
            coll = collection_hook(attrs)
            if coll is not None and coll[1] == 'concat' and res[0] in self.sorts:
                out[res[0]] = {'kind': coll[0], 'concat': name,
                               'unit': attrs['unit'][0][1], 'element': attrs['element'][0][1]}
        return out

    def cell(self, p):
        """<generatedTop>(TOP, DotVar) -> config_of(TOP)"""
        if p[0] == 'app' and p[1] == "Lbl'-LT-'generatedTop'-GT-'" and p[3][1][0] == 'var':
            return config_of(p[3][0])
        raise Unsupported(f'configuration shape {str(p)[:200]}')

    def unfold(self, p, env, init):
        """The initial configuration: an application of an initializer replaced by its equation's
        right side (kompile writes one equation for each, of variable arguments and no requires),
        the projection of $PGM's lookup in the initial map replaced by the program `init`."""
        if p[0] == 'var':
            if p[1] not in env:
                raise Unsupported(f'initializer variable {p[1]}')
            return env[p[1]]
        if p[0] != 'app':
            return p
        _, name, sorts, args = p
        if (name.startswith("Lblproject'Coln'") and len(args) == 1 and args[0][1] == 'kseq'
                and args[0][3][0][1] == "LblMap'Coln'lookup"
                and args[0][3][0][3][1] == ('app', 'inj', (('SortKConfigVar', ()), ('SortKItem', ())),
                                            (('app', '\\dv', (('SortKConfigVar', ()),), (('str', '$PGM'),)),))):
            return init
        if name in self.initializers:
            eqs = self.initializers[name]
            if len(eqs) != 1:
                raise Unsupported(f'initializer {name} of {len(eqs)} equations')
            _, _, _, (pre, concl) = eqs[0]
            lhs, (rhs, _) = concl[3][0], concl[3][1][3]
            binds, a = {}, pre[3][1]
            while a[1] == '\\and':
                i, a = a[3]
                binds[i[3][0][1]] = i[3][1][1]
            inner = {}
            for x, v in zip(lhs[3], args):
                inner[binds.get(x[1], x[1])] = self.unfold(v, env, init)
            return self.unfold(rhs, inner, init)
        return ('app', name, sorts, tuple(self.unfold(a, env, init) for a in args))

    def initial(self, init):
        """The encoded initial configuration: for one cell <k>, inj{S,KItem}(PGM), the item the
        initializer places in it."""
        if self.top_init is None:
            raise Unsupported('a definition without a topCellInitializer')
        top = self.unfold(('app', self.top_init, (), (('var', 'Init', None),)), {'Init': None}, init)
        if top[1] != "Lbl'-LT-'generatedTop'-GT-'":
            raise Unsupported(f'initial configuration {str(top)[:200]}')
        return self.term(config_of(top[3][0]))

    @staticmethod
    def req(p):
        """\\equals{Bool,_}(R, true) -> R; \\top -> None"""
        if p[0] == 'app' and p[1] == '\\top':
            return None
        if p[0] == 'app' and p[1] == '\\equals' and p[3][1] == ('app', '\\dv', (('SortBool', ()),), (('str', 'true'),)):
            return p[3][0]
        raise Unsupported(f'requires shape {str(p)[:200]}')

    @staticmethod
    def priority(attrs):
        owise = 'owise' in attrs
        if 'priority' in attrs:
            return int(attrs['priority']), owise
        return 50, owise

    def rule(self, ax, attrs):
        # \rewrites(\and(LHS, REQ), \and(RHS, \top))
        _, _, _, (left, right) = ax
        lhs, req = left[3]
        rhs, top = right[3]
        if top[1] != '\\top':
            raise Unsupported('ensures')
        self.vars = {}
        prio, owise = self.priority(attrs)
        r = self.req(req)
        self.in_lhs = True
        left = self.term(self.cell(lhs))
        self.in_lhs = False
        enc = f'rl({prio}, {str(owise).lower()}, {left}, {self.term(r) if r else "bv(true)"}, {self.term(self.cell(rhs))}, '
        return enc

    def equation(self, ax, attrs):
        # \implies(\and(REQ-or-owise-negation, \and(\in(X0, P0), ... \top)), \equals(f(X0..), \and(RHS, \top)))
        _, _, _, (pre, concl) = ax
        if concl[1] != '\\equals':
            raise Unsupported('equation conclusion')
        lhs, rhsand = concl[3]
        rhs, top = rhsand[3]
        if top[1] != '\\top':
            raise Unsupported('ensures in equation')
        reqpart, argpart = pre[3]
        owise = 'owise' in attrs
        if owise:
            # \and(\not(...other equations...), \and(REQ-or-\top, ARGS)): the negation is the [owise]
            # premise, read through the attribute; the inner \and holds this equation's own parts.
            if reqpart[1] != '\\not':
                raise Unsupported('owise premise shape')
            reqpart, argpart = argpart[3]
        self.vars = {}
        pats = {}
        a = argpart
        while a[1] == '\\and':
            i, rest = a[3]
            if i[1] != '\\in':
                raise Unsupported('argument shape')
            pats[i[3][0][1]] = i[3][1]
            a = rest
        if a[1] != '\\top':
            raise Unsupported('argument list end')
        fname = lhs[1]
        argvars = [x[1] for x in lhs[3]]
        if any(x[0] != 'var' for x in lhs[3]):
            raise Unsupported('equation left side shape')
        self.in_lhs = True
        pat_terms = [self.term(pats[v]) if v in pats else self.term(('var', v, None)) for v in argvars]
        self.in_lhs = False
        prio, _ = self.priority(attrs)
        r = self.req(reqpart)
        ps = ' ; '.join(pat_terms) + ' ; .Ts' if pat_terms else '.Ts'
        return fname, f'cl({prio}, {str(owise).lower()}, {ps}, {self.term(r) if r else "bv(true)"}, {self.term(rhs)}, '

    def encode(self, init):
        rules, fns = [], {}
        for ax, attrs in self.axioms:
            if ax[1] == '\\rewrites':
                rules.append(self.rule(ax, attrs))
            elif ax[1] == '\\implies':
                f, c = self.equation(ax, attrs)
                fns.setdefault(f, []).append(c)
            else:
                raise Unsupported(f'axiom {ax[1]}')
        self.vars = {}
        t = self.initial(init)
        # the stated subsorts, but those into KItem and K and those of the generated configuration
        # cells, which no term of the single cell reaches
        def kept(a, b):
            return b[0] not in ('SortKItem', 'SortK') and not any(
                re.search(r'Cell(Opt|Fragment|Map|List|Set|Bag)?$', x[0]) for x in (a, b))
        sub_items = [(self.sort(a), self.sort(b)) for (a, b) in self.subsorts if kept(a, b)]
        sub_enc = ''.join(f'sub({x}, {y}, ' for x, y in sub_items) + '.Subs' + ')' * len(sub_items)
        fn_enc = ''
        for f, cls in fns.items():
            fn_enc += f'fn({self.sym(f)}, ' + ''.join(cls) + '.Cls' + ')' * len(cls) + ', '
        fn_enc += '.Fns' + ')' * len(fns)
        rule_enc = ''.join(rules) + '.Rules' + ')' * len(rules)
        return f'pgm(def({sub_enc}, {fn_enc}, {rule_enc}), {t})\n'


def cmd_encode(defn, pgm, out, syms):
    text = open(defn).read()
    mods = read_definition(text)
    head = text.split('\n', 1)[0]
    src = re.search(r'Source\{\}\("Source\(([^)]*)\)"\)', head).group(1)
    top = re.search(r'topCellInitializer\{\}\((\S+?)\{\}\(\)\)', head)
    e = Encoder(mods, src, top.group(1) if top else None)
    init = read_pattern(open(pgm).read())
    prog = e.encode(init)
    open(out, 'w').write(prog)
    out = {'symbols': e.syms, 'sorts': e.sorts}
    colls = e.collections()
    if colls:
        out['collections'] = colls
    json.dump(out, open(syms, 'w'), indent=1, sort_keys=True)
    open(syms, 'a').write('\n')

# ------------------------------------------------------------------ canonical form of results


def collection_text(kind, sort, elems):
    """A collection value as text: SortMap{K|->V,...} and SortSet{X,...} with their elements'
    texts sorted, SortList[X,...] in order. Each backend prints a collection's elements in an
    order of its own; this is the one order of the canonical text."""
    if kind == 'list':
        return f'{sort}[' + ','.join(elems) + ']'
    return f'{sort}{{' + ','.join(sorted(elems)) + '}'


def coll_symbols(colls):
    """symbol name -> (collection sort, its description, role)"""
    out = {}
    for sort, c in (colls or {}).items():
        for role in ROLES:
            out[c[role]] = (sort, c, role)
    return out


def canon(p, csyms=None):
    """A value of the object definition as text: name(args), int, bool, inj{A,B}(v), and the
    collection values of collection_text."""
    csyms = csyms or {}
    tag = p[0]
    if tag == 'app':
        _, name, sorts, args = p
        if name == '\\dv':
            return args[0][1]
        if name == 'inj':
            return f'inj{{{sorts[0][0]},{sorts[1][0]}}}({canon(args[0], csyms)})'
        if name in csyms:
            sort, c, _ = csyms[name]
            return collection_text(c['kind'], sort, coll_elems(p, sort, csyms))
        return f'{name}(' + ','.join(canon(a, csyms) for a in args) + ')'
    raise ValueError(f'not a value: {p}')


def coll_elems(p, sort, csyms):
    """The elements' texts of a collection value of `sort`, its concatenations flattened."""
    s, c, role = csyms.get(p[1], (None, None, None))
    if s != sort:
        raise ValueError(f'not a value of {sort}: {str(p)[:200]}')
    if role == 'unit':
        return []
    if role == 'element':
        args = p[3]
        if c['kind'] == 'map':
            return [f'{canon(args[0], csyms)}|->{canon(args[1], csyms)}']
        return [canon(args[0], csyms)]
    return [e for a in p[3] for e in coll_elems(a, sort, csyms)]


def constraint(p, csyms=None):
    if p[1] == '\\ceil':
        return f'defined({canon(p[3][0], csyms)})'
    return str(p)[:200]


def disjuncts(p):
    if p[0] == 'app' and p[1] == '\\or':
        out = []
        for a in p[3]:
            out += disjuncts(a)
        return out
    if p[0] == 'app' and p[1] == '\\bottom':
        return []
    return [p]


def cmd_ref(syms, outfile):
    text = open(outfile).read().strip()
    if not text:
        return []
    csyms = coll_symbols(json.load(open(syms)).get('collections'))
    res = []
    for d in disjuncts(read_pattern(text)):
        if d[1] == '\\equals':  # krun --search: \equals(VarResult, CONFIG)
            d = d[3][1]
        cond = ''
        if d[1] == '\\and':  # \and(CONSTRAINT, \equals(VarResult, CONFIG)): kept with its constraint
            cond = ' if ' + ' and '.join(constraint(c, csyms) for c in d[3] if c[1] != '\\equals')
            d = [c for c in d[3] if c[1] == '\\equals'][0][3][1]
        res.append(canon(config_of(d[3][0]), csyms) + cond)
    return sorted(set(res))


def korek_value(t, rsym, rsort):
    """kore.k's encoded value (KORE of a Term of KORE) -> canonical text."""
    _, name, _, args = t
    if name.startswith("Lblco'LPar"):
        kind = re.match(r"Lbl(\w+)'", args[0][1]).group(1)
        sort = rsort[int(args[1][3][0][1])]
        elems = []
        for e in korek_list(args[2]):
            if e[1].startswith("Lblkv'LPar"):
                elems.append(f'{korek_value(e[3][0], rsym, rsort)}|->{korek_value(e[3][1], rsym, rsort)}')
            elif e[1].startswith("Lblel'LPar"):
                elems.append(korek_value(e[3][0], rsym, rsort))
            else:
                elems.append(f'?{e[1]}')
        return collection_text(kind, sort, elems)
    if name == "Lblap'LParUndsCommUndsRParUnds'KORE-SYNTAX'Unds'Term'Unds'Int'Unds'Ts":
        f = int(args[0][3][0][1])
        return f'{rsym[f]}(' + ','.join(korek_value(a, rsym, rsort) for a in korek_list(args[1])) + ')'
    if name == "Lbliv'LParUndsRParUnds'KORE-SYNTAX'Unds'Term'Unds'Int":
        return args[0][3][0][1]
    if name == "Lblbv'LParUndsRParUnds'KORE-SYNTAX'Unds'Term'Unds'Bool":
        return args[0][3][0][1]
    if name == "Lblij'LParUndsCommUndsCommUndsRParUnds'KORE-SYNTAX'Unds'Term'Unds'Int'Unds'Int'Unds'Term":
        a, b = int(args[0][3][0][1]), int(args[1][3][0][1])
        return f'inj{{{rsort[a]},{rsort[b]}}}({korek_value(args[2], rsym, rsort)})'
    return f'?{name}'


def korek_list(t):
    out = []
    while t[1] != "Lbl'Stop'Ts'Unds'KORE-SYNTAX'Unds'Ts":
        out.append(t[3][0])
        t = t[3][1]
    return out


def find(p, pred):
    if pred(p):
        return p
    if p[0] == 'app':
        for a in p[3]:
            r = find(a, pred)
            if r is not None:
                return r
    return None


def cmd_korek(syms, outfile):
    s = json.load(open(syms))
    rsym = {v: k for k, v in s['symbols'].items()}
    rsort = {v: k for k, v in s['sorts'].items()}
    finals = []
    for d in disjuncts(read_pattern(open(outfile).read())):
        done = find(d, lambda p: p[0] == 'app' and p[1].startswith("Lbldone'"))
        if done is None:
            raise ValueError('no done(...) in the result')
        finals.append([korek_value(v, rsym, rsort) for v in korek_list(done[3][0])])
    if len(finals) != 1:
        raise ValueError(f'{len(finals)} results of kore.k')
    return sorted(set(finals[0]))


if __name__ == '__main__':
    a = sys.argv[1:]
    if a[0] == 'encode':
        cmd_encode(*a[1:])
    elif a[0] == 'ref':
        print(json.dumps(cmd_ref(*a[1:])))
    elif a[0] == 'korek':
        print(json.dumps(cmd_korek(*a[1:])))
    else:
        sys.exit('usage: korek.py encode|ref|korek ...')
