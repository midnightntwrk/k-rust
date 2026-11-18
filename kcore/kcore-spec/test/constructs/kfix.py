"""The K-level fixtures of rows.toml (lists E1, E2, E3, E7, E8): small K texts, their kompiled KORE
and `kcore account` of it, under test/constructs/fixtures/NAME/.

Usage (from kcore-spec):
  python3 -I test/constructs/kfix.py run [NAME...]   kompile the named fixtures (all without names)
  python3 -I test/constructs/kfix.py check [LIST...]  check rows.toml's pointers (lists E1 E2 E3 E7 E8
                                                     by default) against the files
  python3 -I test/constructs/kfix.py rehash [NAME...] rewrite kompile.txt's stripped sha256 and
                                                     verdicts from the text of the same run (this
                                                     tree's .lake/kfix or the cache: no kompile)
  python3 -I test/constructs/kfix.py accounts [--write] [NAME...]
                                                     `kcore account` of each fixture's text from the
                                                     cache below (no kompile) against account.txt;
                                                     --write re-records account.txt; each kompiled
                                                     text is also read with other paths restored
                                                     and must give the same account
  python3 -I test/constructs/kfix.py cache-import DIR...
                                                     put DIR/NAME/definition.norm.kore (DIR another
                                                     tree's .lake/kfix) into the cache when its sha256
                                                     is the one NAME's kompile.txt records

A fixture directory holds its K text(s) and fixture.toml:
  main     the file kompiled (default NAME.k)
  extra    options after `--backend haskell` (default none: R-12's option set)
  expect   "ok" (default) or "error": an error fixture records kompile's message and nothing else
  same_as  another fixture whose kompiled text this one's must equal after removing the Source and
           Location attributes, the comments (whitespace to the KORE lexer, so no sentence holds
           one) and the main module's name (its `module` line, symbol labels and rule labels
           holding it), putting each disjunction's disjuncts in a
           fixed order (kompile's order changes from run to run and with the text's path; \\or is
           commutative and associative), the binders of each disjunct's chain of existentials in a
           fixed order (kompile's order changes with the text's path; adjacent existentials commute)
           and renumbering the variables kompile generates (their numbers change from run to run)
           (`stripped`) (an option or a construct that changes no
           sentence); differs_from: the same, must differ
  text_from  another fixture whose text files are copied beside this one's (an option fixture
           kompiles another fixture's text); kore.txt then holds the sentences not in that
           fixture's main module instead of base's (base's still where that fixture is an error
           fixture, which has no main module)
  kk       the id of a Kore-in-K entry (krs/semantics/kore/texts/ID or cases/ID of this tree) whose
           K text is this fixture's: the files of its [text] are copied beside the fixture's, as
           text_from copies a fixture's, and main defaults to the first of them; kompile.txt records
           each one's path and sha256 (`kk FILE: sha256 ...`). The fixture directory then holds no K
           text of its own: the entry's is the one copy
  external files of the k-rust checkout (K_RUST, paths relative to it) copied beside the text
           before kompiling; kompile.txt records each one's sha256
  kore_txt false: write no kore.txt (a large text no row points into, such as kore.k's)
  params   true: `run` also writes params.txt, the `param` lines of `kcore sem-fields` of the text
           (each parameter symbol of the reading: its signature, `impl`, the registry hook that
           interprets it or none, and raw, assoc, idem), followed by `(exit N)`; `accounts`
           compares it as it compares account.txt
  keep     regular expressions: when the sentences for kore.txt exceed 200 KB, only those with a
           Source in the fixture or matching one of these are written
  args     the whole command line after kompile instead of `--backend haskell EXTRA MAIN -o out`
           (an option that writes no definition, such as --help)
  pre      a kompile command line run first in the same directory (its exit code and output are
           recorded); pre_copy [FROM, TO]: then FROM, a file it wrote, is copied to TO, which the
           main command reads (a definition given in another input form, such as the JSON
           `--emit-json` writes, read back under `--outer-parsed-json`)
  left_lines  [FIRST, LAST], for an error fixture: when kompile leaves out/definition.kore, its
           size and sha256 go into kompile.txt and kore.txt holds those lines of it (paths
           replaced), each after a line `//@ line N` (a text a backend rejects, such as at the
           line its message names)
  expectation, observed  prose read by no tool: what the text's sentences give, and kore.txt lines
           quoted with their line numbers
  kore     a KORE text (path relative to kcore-spec) that kompile 7.1.337 does not write, such as
           krust's text of a K file: `run` kompiles nothing and writes account.txt, `kcore account`
           of that text, and kompile.txt, the text's path and sha256; no kore.txt

`run` copies the directory to .lake/kfix/NAME/src, kompiles there one fixture at a time under the
memory wrapper, and writes into the fixture directory:
  kompile.txt  the command, exit code, seconds, size and sha256 of definition.kore with paths
               replaced (FIXTURE/ for the fixture's directory, BUILTIN/ for K's builtin directory),
               the sha256 with Source, Location, comments and module names removed, the same_as / differs_from
               verdict, and kompile's output (paths replaced)
  kore.txt     the sentences of the main module that come from no builtin file (no Source under
               BUILTIN/) and are not sentences of fixture `base`'s main module: what the text adds
               to an empty module (compared with generated variables renumbered); each after a line `//@ N`, N its index among the main module's
               sentences (a `// rule` comment kompile writes counts with the axiom it precedes).
               The whole text is not committed (80 to 650 KB each); kompile.txt's command
               regenerates it. Kompile numbers its generated variables differently from run to
               run, and orders some disjunctions and the binders of their existentials by the
               path of the text it kompiles, so the text's sha256 can change from run to run and
               from tree to tree; the stripped sha256 (Source, Location, comments and module names
               removed, disjunctions and existential binders in a fixed order, generated variables
               renumbered: `stripped`) absorbs those differences and reproduces in any tree: it is
               the one to compare. kore.txt keeps the
               `// rule` comment lines (rows quote them to locate a sentence); `stripped` does not.
  account.txt  `kcore account out/definition.kore` (the workspace's .lake/build/bin/kcore)

The kompiled texts are not committed. `run` also keeps each one, as kompile.txt hashes it (paths
replaced: definition.norm.kore), in a cache outside the tree keyed by that sha256:
CACHE/SHA.kore, CACHE = $KCORE_KFIX_CACHE, default $XDG_CACHE_HOME/kcore-kfix (~/.cache/kcore-kfix
when XDG_CACHE_HOME is unset): one per user, shared by every worktree of the user, never committed.
A fixture's text is found there by kompile.txt's `definition.kore sha256` alone, so a stale entry
cannot be read for another text. `run` reads fixture `base`'s (and a same_as / differs_from
fixture's) text from the cache when this tree's .lake/kfix has no run of it; `accounts` reads every
fixture's text from it (restoring BUILTIN/ as K's builtin directory, so K_RUST or K_KOMPILE must name
a K installation, and FIXTURE/ as .lake/kfix/NAME/account); `check` prints how many kompiled texts the
cache holds. A new tree is seeded with `cache-import` from another tree's .lake/kfix.

A row of rows.toml names its fixture (`fixture`) and either the sentences that carry it (`sentence`,
substrings of that fixture's kore.txt, or of kompile.txt for an error fixture) or why no sentence of
a kompiled text carries it (`no_sentence`, "CLASS: reason", with `fixture` the evidence, or "none"
when the reason is a place in K's sources). Classes: erased (the fixture's same_as pair is equal),
rejected (kompile's error in the fixture), and the others named where they are used. `check` fails
unless every row of E1, E2, E3, E7, E8 has a fixture that exists, every `sentence` occurs in it,
every row has exactly one of `sentence` and `no_sentence`, and every same_as / differs_from verdict
recorded holds.

A row or a `cases` entry of any list E1 to E8 may carry `notes`, a table from a constructor of
`ReadingNote` (KcoreSpec/Parse.lean) to a fixture directory whose account.txt prints the note: a
line `N read NOTE [...]` or `sentence I: ... NOTE ...` (the per-sentence readings), or a count line
`... (NOTE): N`, with N > 0. `check` also fails unless each `notes` entry is so, and every
constructor of ReadingNote is a key of some `notes` table.
"""
import difflib, hashlib, os, re, shutil, subprocess, sys, time, tomllib

K = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(K, "test"))
sys.dont_write_bytecode = True  # no __pycache__ in the tree
import relsource
FX = os.path.join(K, "test/constructs/fixtures")
WORK = os.path.join(K, ".lake/kfix")
# the k-rust checkout: $K_RUST, or the nearest directory above holding Cargo.toml and crates/k-rust
KR = relsource.krust_root() or "K_RUST-unset"
KOMPILE = os.environ.get("K_KOMPILE", os.path.join(KR, "k/result/bin/kompile"))
# the kcore binary `run` and `accounts` call: $KCORE_BIN (e.g. an older build, to show a check fails
# on it), else this workspace's
KCORE = os.environ.get("KCORE_BIN") or os.path.join(K, ".lake/build/bin/kcore")
# a made-up builtin directory (223 characters; K 7.1.337's in the nix store is 121): `accounts` and
# account-depth.py restore BUILTIN/ as it for the second account of a text (the reader tells a builtin
# Source by its /include/kframework/builtin/ suffix only)
FAKE_BUILTIN = "/" + "/".join(["made-up-k-installation-path"] * 7) + "/include/kframework/builtin"
LISTS = ["E1", "E2", "E3", "E7", "E8"]
LIMIT = 200_000
WRAP = ["systemd-run", "--user", "--scope", "-q", "-p", "MemoryMax=12G", "-p", "MemorySwapMax=0"]
ATTR = re.compile(r",? ?org'Stop'kframework'Stop'attributes'Stop'(?:Source|Location)\{\}\(\"[^\"]*\"\)"
                  r"|,? ?org\.kframework\.attributes\.(?:Source|Location)\((?:Source|Location)\([^)]*\)\)")


def builtin_dir():
    return os.path.join(os.path.dirname(os.path.dirname(os.path.realpath(KOMPILE))),
                        "include/kframework/builtin")


def norm(text, src):
    text = text.replace(src + "/", "FIXTURE/").replace(src, "FIXTURE")
    text = text.replace(builtin_dir() + "/", "BUILTIN/")
    return re.sub(r"/nix/store/[a-z0-9]{32}-[^/\s\"]*", "NIXSTORE", text)


def main_module(kore):
    """The lines of the last module of a kompiled text (kompile writes the main module last)."""
    lines = kore.split("\n")
    start = max(i for i, l in enumerate(lines) if l.startswith("module "))
    end = next(i for i in range(start, len(lines)) if lines[i].startswith("endmodule"))
    return lines[start:end + 1]


SENT = re.compile(r"^(  (axiom|symbol|sort|hooked-symbol|hooked-sort|import|alias|claim)\b|module |endmodule)")


def sentences(lines):
    """The main module's lines grouped into sentences, a `// rule ...` comment line with the sentence
    that follows it; the section comments (`// sorts`, ...) and blank lines are dropped."""
    out, cur, after_comment = [], None, False
    for l in lines:
        if l.startswith("// ") and not l.startswith("// rule") and not l.startswith("// claim"):
            continue
        if not l.strip():
            continue
        if l.startswith("// "):
            cur = [l]; out.append(cur); after_comment = True; continue
        if SENT.match(l) and not after_comment:
            cur = [l]; out.append(cur)
        elif cur is None:
            cur = [l]; out.append(cur)
        else:
            cur.append(l)
        after_comment = False
    return ["\n".join(g) for g in out]


GEN = re.compile(r"(Var'Unds'Gen|_Gen)(\d+)")
CHUNK = re.compile(r"^(?=  (?:axiom|symbol|sort|hooked-symbol|hooked-sort|import|alias|claim)\b|// rule|// claim|module |endmodule)", re.M)


def alpha(text):
    """The variables kompile generates (Var'Unds'GenN, and _GenN in its `// rule` comments) renumbered
    by first occurrence within each sentence: kompile numbers them differently from run to run."""
    def one(chunk):
        seen = {}
        return GEN.sub(lambda m: m[1] + str(seen.setdefault(m[0], len([k for k in seen if k.startswith(m[1])]))), chunk)
    return "".join(one(c) for c in CHUNK.split(text))


def _string_end(t, i):
    """The index after the KORE string literal that starts at t[i] == '"'."""
    i += 1
    while i < len(t):
        if t[i] == "\\":
            i += 2; continue
        if t[i] == '"':
            return i + 1
        i += 1
    raise ValueError("kfix: unterminated string literal")


def _close(t, i):
    """The index of the bracket closing the one at t[i] ('(' or '{'), string literals skipped."""
    depth = 0
    while i < len(t):
        ch = t[i]
        if ch == '"':
            i = _string_end(t, i); continue
        if ch in "({":
            depth += 1
        elif ch in ")}":
            depth -= 1
            if depth == 0:
                return i
        i += 1
    raise ValueError("kfix: unbalanced brackets in a disjunction")


def _args(t, i):
    """The arguments of the application whose '(' is t[i], split at top-level commas, and the index
    after its ')'."""
    end, out, depth, start, j = _close(t, i), [], 0, i + 1, i + 1
    while j < end:
        ch = t[j]
        if ch == '"':
            j = _string_end(t, j); continue
        if ch in "({":
            depth += 1
        elif ch in ")}":
            depth -= 1
        elif ch == "," and depth == 0:
            out.append(t[start:j]); start = j + 1
        j += 1
    out.append(t[start:end])
    return out, end + 1


OR = "\\or{"


def _or_app(t, i):
    """For the \\or application at t[i]: its sort (whitespace removed), arguments, and end index."""
    s_end = _close(t, i + len(OR) - 1)
    sort = re.sub(r"\s+", "", t[i + len(OR) - 1:s_end + 1])
    j = s_end + 1
    while j < len(t) and t[j].isspace():
        j += 1
    if j >= len(t) or t[j] != "(":
        raise ValueError("kfix: \\or without arguments")
    args, end = _args(t, j)
    return sort, args, end


def _ws(t):
    """Whitespace runs outside string literals collapsed to one space."""
    out, i = [], 0
    while i < len(t):
        if t[i] == '"':
            e = _string_end(t, i); out.append(t[i:e]); i = e; continue
        if t[i].isspace():
            while i < len(t) and t[i].isspace():
                i += 1
            out.append(" "); continue
        out.append(t[i]); i += 1
    return "".join(out).strip()


EXISTS = "\\exists{"


def _exists_app(t, i):
    """For the \\exists application at t[i]: its sort parameter (whitespace removed), its binder
    and body, and its end index; None where t[i:] is no such application."""
    if not t.startswith(EXISTS, i):
        return None
    s_end = _close(t, i + len(EXISTS) - 1)
    sort = re.sub(r"\s+", "", t[i + len(EXISTS) - 1:s_end + 1])
    j = s_end + 1
    while j < len(t) and t[j].isspace():
        j += 1
    if j >= len(t) or t[j] != "(":
        return None
    args, end = _args(t, j)
    if len(args) != 2:
        return None
    return sort, args[0].strip(), args[1].strip(), end


def exists_sorted(d):
    """d, a pattern whose text starts a chain of \\exists of one sort, \\exists{S}(x1, \\exists{S}(x2,
    ... BODY)), with the chain's binders in a fixed order: by the first occurrence of each bound
    variable in BODY, those that do not occur last in their order of sort and text. Two adjacent
    existential quantifiers commute (\\exists x . \\exists y . P and \\exists y . \\exists x . P denote
    the same set), so every order of one chain denotes the same pattern; kompile writes the binders
    of a generated chain (an [owise] equation's negated sibling) in an order that changes with the
    text's path, and `alpha` numbers the generated variables by first occurrence, the binders
    first, so the binders' order would fix their numbers. Applied to a disjunct of
    `disjunctions_sorted`; a text that starts no chain is returned as it is."""
    d = d.strip()
    first = _exists_app(d, 0)
    if first is None or first[3] != len(d):
        return d
    sort, binders, body = first[0], [first[1]], first[2]
    while True:
        nxt = _exists_app(body, 0)
        if nxt is None or nxt[0] != sort or nxt[3] != len(body):
            break
        binders.append(nxt[1]); body = nxt[2]
    def key(b):
        name = b.split(":", 1)[0].strip()
        m = re.search(re.escape(name) + r"(?![\w'])", body)
        return (0, m.start(), "") if m else (1, 0, b.split(":", 1)[-1] + b)
    binders.sort(key=key)
    out = body
    for b in reversed(binders):
        out = f"\\exists{sort} ({b}, {out})"
    return out


def disjunctions_sorted(t):
    """Every maximal chain of \\or applications of one sort, \\or{S}(A, \\or{S}(B, ...)) nested
    either way, rebuilt as the right-nested chain of its disjuncts in a fixed order: the order of
    their texts with the generated variables renumbered within each disjunct (kompile numbers them
    by position, so their numbers cannot order the disjuncts). \\or is commutative and associative,
    so every arrangement of one set of disjuncts denotes the same pattern; kompile writes some
    disjunctions (the negated left sides of an [owise] equation's siblings, for one) in an order
    that changes from run to run and with the text's path, so the stripped text fixes one
    arrangement. Disjuncts are themselves rewritten first, and each disjunct's chain of
    existentials has its binders in a fixed order (exists_sorted) before the disjuncts are
    ordered; string literals are left as they are. It is applied to a text without comments
    (`stripped` removes them first)."""
    out, i, n = [], 0, len(t)
    while i < n:
        if t[i] == '"':
            e = _string_end(t, i); out.append(t[i:e]); i = e; continue
        if t.startswith(OR, i):
            sort, args, end = _or_app(t, i)
            leaves, todo = [], list(reversed(args))
            while todo:
                a = todo.pop().strip()
                if a.startswith(OR):
                    s2, a2, e2 = _or_app(a, 0)
                    if s2 == sort and not a[e2:].strip():
                        todo.extend(reversed(a2)); continue
                leaves.append(exists_sorted(_ws(disjunctions_sorted(a))))
            leaves.sort(key=lambda d: (alpha(d), d))
            chain = leaves[-1]
            for d in reversed(leaves[:-1]):
                chain = f"\\or{sort}({d}, {chain})"
            out.append(chain); i = end; continue
        out.append(t[i]); i += 1
    return "".join(out)


def main_name(kore):
    """The name of the text's last module (kompile writes the main module last), or None."""
    names = re.findall(r"^module (\S+)", kore, re.M)
    return names[-1] if names else None


def unmodule(t, name):
    """t with the main module's name `name` replaced by MAIN where a symbol's label holds it, and
    where a sentence's `label` attribute starts with it. K's symbol label `..._NAME_Sort...` is
    written `...Unds'NAME'Unds'Sort...`, the `_` before the name being the end of the mangled run
    before it (`'Unds'NAME` after a letter, `'LParUndsRParUnds'NAME` after `(_)`). A rule's label is
    qualified by its module: kompile writes `label{}("NAME.neg1-cool")` on each heating and cooling
    axiom of a strict production (and `label(NAME.neg1-cool)` in the `// rule` comment over it),
    so two texts with strict productions in differently named main modules would never compare
    equal. Only that name: another token in that place (a sort such as K, a library module's name)
    is kept, so that two texts differing there are not made equal."""
    if not name:
        return t
    t = re.sub(r"(?<=Unds)'" + re.escape(name) + r"'(?=Unds')", "'MAIN'", t)
    return re.sub(r"(?<=label\{\}\(\")" + re.escape(name) + r"(?=\.)", "MAIN", t)


COMMENT = re.compile(r'"|//|/\*')


def uncommented(t):
    """t without its comments, as the KORE lexer reads it (KoreParser/Parser.lean, `ws`): `//` to
    the end of the line and `/* ... */`, outside string literals. A comment is whitespace there,
    so no sentence KCore reads holds one. A `//` comment that is a whole line goes with its line
    end (kompile writes its `// rule`, `// claim` and section comments as whole lines; the cached
    texts hold no other comment); another `//` comment goes up to its line end, and a `/* */`
    comment is replaced by one space where no whitespace or text boundary is beside it (it
    separates tokens as whitespace does), else by nothing. Whitespace is otherwise kept as it is."""
    out, i, n = [], 0, len(t)
    while True:
        m = COMMENT.search(t, i)
        if not m:
            out.append(t[i:]); break
        j = m.start()
        out.append(t[i:j])
        if m[0] == '"':
            e = _string_end(t, j); out.append(t[j:e]); i = e; continue
        if m[0] == "//":
            e = t.find("\n", j); e = n if e < 0 else e
            i = min(e + 1, n) if j == 0 or t[j - 1] == "\n" else e
            continue
        e = t.find("*/", j + 2)
        if e < 0:
            raise ValueError("kfix: unterminated /* comment")
        i = e + 2
        if 0 < j and not t[j - 1].isspace() and i < n and not t[i].isspace():
            out.append(" ")
    return "".join(out)


def stripped(kore):
    """The text compared by same_as / differs_from and hashed as `stripped sha256`: Source and
    Location attributes removed, comments removed (uncommented: KCore's KORE parser drops them, so
    no reading depends on one), module names replaced (each `module` line's, and the main
    module's where a label holds it: unmodule), disjunctions in a fixed order and each disjunct's
    chain of existential binders in a fixed order (disjunctions_sorted, exists_sorted), and
    generated variables renumbered (alpha), in that order so that neither the module names nor the
    generated variables' numbers fix a disjunct's or a binder's place. What it absorbs is what
    kompile changes between runs or between the directories it kompiles in without changing a
    sentence's meaning."""
    t = ATTR.sub("", kore).replace("[, ", "[").replace("[,", "[")
    t = uncommented(t)
    t = unmodule(t, main_name(t))
    t = re.sub(r"^module \S+", "module MAIN", t, flags=re.M)
    return alpha(disjunctions_sorted(t))


def sha(s):
    return hashlib.sha256(s.encode()).hexdigest()


# the Kore-in-K catalogue of this tree (krs/semantics/kore), whose entries a fixture's `kk` names
CATALOGUE = os.path.join(os.path.dirname(os.path.dirname(K)), "krs/semantics/kore")


def kk_files(entry_id):
    """The paths of the K text files of the Kore-in-K entry `entry_id`; SystemExit when it names no
    entry or the entry has no K text."""
    for sub in ("texts", "cases"):
        d = os.path.join(CATALOGUE, sub, entry_id)
        if os.path.isfile(os.path.join(d, "entry.toml")):
            files = tomllib.load(open(os.path.join(d, "entry.toml"), "rb")).get("text", {}).get("files")
            if not files:
                raise SystemExit(f"kfix: kk entry {entry_id} has no K text ([text].files)")
            return [os.path.join(d, f) for f in files]
    raise SystemExit(f"kfix: kk = {entry_id!r} names no entry of {os.path.relpath(CATALOGUE, K)}")


def conf(name):
    p = os.path.join(FX, name, "fixture.toml")
    c = tomllib.load(open(p, "rb")) if os.path.exists(p) else {}
    if "kk" in c and "main" not in c:
        c["main"] = os.path.basename(kk_files(c["kk"])[0])
    c.setdefault("main", name + ".k")
    c.setdefault("extra", [])
    c.setdefault("expect", "ok")
    return c


CACHE = os.environ.get("KCORE_KFIX_CACHE") or os.path.join(
    os.environ.get("XDG_CACHE_HOME") or os.path.expanduser("~/.cache"), "kcore-kfix")


def recorded_sha(name):
    """kompile.txt's `definition.kore sha256` of a kompiled fixture (one with a stripped sha256),
    else None (an error fixture, a `kore` fixture, a fixture not run)."""
    kt = os.path.join(FX, name, "kompile.txt")
    t = open(kt).read() if os.path.exists(kt) else ""
    m = re.search(r"^definition\.kore sha256: (\w+)$", t, re.M)
    return m[1] if m and "\nstripped sha256: " in t else None


def cache_put(kore):
    os.makedirs(CACHE, exist_ok=True)
    p = os.path.join(CACHE, sha(kore) + ".kore")
    if not os.path.exists(p):
        tmp = f"{p}.{os.getpid()}.tmp"
        open(tmp, "w").write(kore)
        os.replace(tmp, p)


def cache_get(h):
    """The cached text of sha256 h, or None; an entry whose content is not of sha256 h is not read."""
    p = os.path.join(CACHE, h + ".kore")
    if not os.path.exists(p):
        return None
    kore = open(p).read()
    return kore if sha(kore) == h else None


def norm_text(name):
    """Fixture NAME's text as kompile.txt hashes it: this tree's last run of it, else the cache's."""
    p = os.path.join(WORK, name, "definition.norm.kore")
    if os.path.exists(p):
        return open(p).read()
    h = recorded_sha(name)
    return cache_get(h) if h else None


def run_kore(name, c):
    """A fixture of a KORE text kompile does not write (fixture.toml `kore`): its account only."""
    for f in ("kore.txt", "account.txt"):
        if os.path.exists(os.path.join(FX, name, f)):
            os.remove(os.path.join(FX, name, f))
    t0 = time.time()
    a = subprocess.run([*WRAP, "timeout", "300", KCORE, "account", c["kore"]], cwd=K,
                       capture_output=True, text=True, env={**os.environ, "LEAN_NUM_THREADS": "1"})
    secs = time.time() - t0
    open(os.path.join(FX, name, "account.txt"), "w").write(a.stdout + a.stderr + f"(exit {a.returncode})\n")
    text = open(os.path.join(K, c["kore"])).read()
    open(os.path.join(FX, name, "kompile.txt"), "w").write("\n".join([
        f"command: none: fixture.toml kore = {c['kore']!r}, a KORE text kompile does not write; "
        f"account.txt is `kcore account {c['kore']}` (cwd: kcore-spec)",
        f"definition.kore bytes: {len(text.encode())}", f"definition.kore sha256: {sha(text)}"]) + "\n")
    print(f"kfix {name}: kcore account exit {a.returncode}, {secs:.1f}s")
    return secs


def run(name):
    c = conf(name)
    if "kore" in c:
        return run_kore(name, c)
    w = os.path.join(WORK, name)
    src = os.path.join(w, "src")
    shutil.rmtree(w, ignore_errors=True)
    shutil.copytree(os.path.join(FX, name), src,
                    ignore=shutil.ignore_patterns("kompile.txt", "kore.txt", "account.txt", "params.txt"))
    # each file of src: the file of the tree (or of the k-rust checkout) it is a copy of
    origin = {f: os.path.relpath(os.path.join(FX, name, f), relsource.TREE) for f in os.listdir(src)}
    if "text_from" in c:
        for f in os.listdir(os.path.join(FX, c["text_from"])):
            if f not in ("kompile.txt", "kore.txt", "account.txt", "params.txt", "fixture.toml"):
                shutil.copy(os.path.join(FX, c["text_from"], f), src)
                origin[f] = os.path.relpath(os.path.join(FX, c["text_from"], f), relsource.TREE)
    ext = []
    for f in kk_files(c["kk"]) if "kk" in c else []:
        shutil.copy(f, src)
        origin[os.path.basename(f)] = os.path.relpath(f, relsource.TREE)
        ext.append(f"kk {os.path.relpath(f, os.path.dirname(os.path.dirname(K)))}: sha256 "
                   f"{hashlib.sha256(open(f, 'rb').read()).hexdigest()}")
    for rel in c.get("external", []):
        shutil.copy(os.path.join(KR, rel), src)
        origin[os.path.basename(rel)] = rel
        ext.append(f"external {rel}: sha256 {hashlib.sha256(open(os.path.join(KR, rel), 'rb').read()).hexdigest()}")
    args = c["args"] if "args" in c else ["--backend", "haskell", *c["extra"], c["main"], "-o", "out"]
    cmd = ["kompile", *args]
    t0 = time.time()
    pre = []
    if "pre" in c:
        q = subprocess.run([*WRAP, "timeout", "900", KOMPILE, *c["pre"]], cwd=src, capture_output=True,
                           text=True, env={**os.environ, "LEAN_NUM_THREADS": "1"})
        pre = [f"pre: kompile {' '.join(c['pre'])}  (cwd: the fixture directory)", f"pre exit: {q.returncode}"]
        if "pre_copy" in c:
            fr, to = c["pre_copy"]
            ok_copy = os.path.exists(os.path.join(src, fr))
            if ok_copy:
                shutil.copy(os.path.join(src, fr), os.path.join(src, to))
            pre.append(f"pre_copy: {fr} -> {to}" + ("" if ok_copy else f": {fr} not written"))
        pre += ["pre output:"] + ["  " + l for l in norm(q.stdout + q.stderr, src).strip().split("\n")[:40]]
    p = subprocess.run([*WRAP, "timeout", "900", KOMPILE, *args], cwd=src, capture_output=True,
                       text=True, env={**os.environ, "LEAN_NUM_THREADS": "1"})
    secs = time.time() - t0
    out = norm(p.stdout + p.stderr, src)
    rep = [*pre, f"command: {' '.join(cmd)}  (cwd: the fixture directory)", f"exit: {p.returncode}",
           f"seconds: {secs:.1f}", *ext]
    kp = os.path.join(src, "out/definition.kore")
    for f in ("kore.txt", "account.txt", "params.txt"):
        if os.path.exists(os.path.join(FX, name, f)):
            os.remove(os.path.join(FX, name, f))
    ok = p.returncode == 0
    if ok and os.path.exists(kp):
        kore = norm(open(kp).read(), src)
        rep += [f"definition.kore bytes: {len(kore.encode())}", f"definition.kore sha256: {sha(kore)}",
                f"stripped sha256: {sha(stripped(kore))}"]
        open(os.path.join(w, "definition.norm.kore"), "w").write(kore)
        cache_put(kore)
        ss = sentences(main_module(kore))
        ref = c.get("text_from", "base")
        if conf(ref)["expect"] == "error":
            ref = "base"
        if name == "base":
            keep = set()
        else:
            bt = norm_text(ref)
            if bt is None:
                raise SystemExit(f"kfix: run fixture {ref} before {name}")
            keep = {alpha(g) for g in sentences(main_module(bt))}
        delta = [f"//@ {i}\n{g}" for i, g in enumerate(ss)
                 if alpha(g) not in keep and "Source(BUILTIN/" not in g]
        size = sum(len(g) for g in delta)
        if size > LIMIT:
            keep_re = [re.compile(x) for x in c.get("keep", [])]
            full = len(delta)
            delta = [g for g in delta if "Source(FIXTURE" in g or any(r.search(g) for r in keep_re)]
            rep.append(f"main module: {len(ss)} sentences, {full} not in {ref}'s ({size} bytes, over "
                       f"{LIMIT}): kore.txt holds the {len(delta)} with a Source in the fixture"
                       + (f" or matching keep {c['keep']}" if keep_re else ""))
        else:
            rep.append(f"main module: {len(ss)} sentences, {len(delta)} not in {ref}'s, in kore.txt")
        if c.get("kore_txt", True):
            open(os.path.join(FX, name, "kore.txt"), "w").write("\n".join(delta) + "\n")
        else:
            rep.append("kore.txt: not written (fixture.toml kore_txt = false); the command regenerates the text")
        a = subprocess.run([KCORE, "account", "out/definition.kore"], cwd=src, capture_output=True,
                           text=True)
        open(os.path.join(FX, name, "account.txt"), "w").write(
            norm(a.stdout + a.stderr, src) + f"(exit {a.returncode})\n")
        if c.get("params"):
            open(os.path.join(FX, name, "params.txt"), "w").write(sem_params(src))
        for rel in ("same_as", "differs_from"):
            if rel in c:
                ot = norm_text(c[rel])
                if ot is None:
                    raise SystemExit(f"kfix: run fixture {c[rel]} before {name}")
                eq = stripped(ot) == stripped(kore)
                rep.append(f"{rel} {c[rel]}: {'equal' if eq else 'different'} after stripping")
        # the text left in .lake (the one copied into the tree) names each source by the file it
        # is a copy of, relative (test/relsource.py); the outputs above were computed before
        kr = relsource.krust_root()
        relsource.rewrite_file(kp, lambda p: origin.get(p[len(src) + 1:], os.path.relpath(p, relsource.TREE))
                               if p.startswith(src + "/") else relsource.relative(p, kr))
    elif ok:
        rep.append("definition.kore: none written")
    elif "left_lines" in c and os.path.exists(kp):
        kore = norm(open(kp).read(), src)
        a, b = c["left_lines"]
        lines = kore.split("\n")
        rep += [f"definition.kore left: {len(kore.encode())} bytes, {len(lines)} lines, sha256 {sha(kore)}",
                f"kore.txt: its lines {a} to {b}"]
        open(os.path.join(FX, name, "kore.txt"), "w").write(
            "".join(f"//@ line {i}\n{lines[i - 1]}\n" for i in range(a, min(b, len(lines)) + 1)))
    elif "left_lines" in c:
        rep.append("definition.kore: none left")
    if (c["expect"] == "ok") != ok:
        rep.append(f"UNEXPECTED: expect {c['expect']}")
    lines = out.strip().split("\n")
    rep += ["output:"] + ["  " + l for l in lines[:80]] + (
        [f"  ... {len(lines) - 80} more lines"] if len(lines) > 80 else [])
    open(os.path.join(FX, name, "kompile.txt"), "w").write("\n".join(rep) + "\n")
    print(f"kfix {name}: exit {p.returncode}, {secs:.1f}s" + (
        "" if (c["expect"] == "ok") == ok else "  UNEXPECTED"))
    return secs


def recorded_text(name):
    """The text of the run kompile.txt records (its sha256 the recorded definition.kore sha256):
    this tree's .lake/kfix/NAME/definition.norm.kore when it is that text, else the cache's; None
    when neither holds it."""
    h = recorded_sha(name)
    if not h:
        return None
    p = os.path.join(WORK, name, "definition.norm.kore")
    if os.path.exists(p):
        kore = open(p).read()
        if sha(kore) == h:
            return kore
    return cache_get(h)


def rehash(names):
    """Rewrite kompile.txt's `stripped sha256` and same_as / differs_from lines from the text of the
    same run (recorded_text: no kompile), after a change to `stripped` or to fixture.toml's
    relation (a recorded same_as / differs_from line of the same pair is replaced by the relation
    fixture.toml names); the fixtures whose run, or whose pair's run, is held nowhere are listed,
    to be run."""
    stale, done = [], 0
    for name in names:
        kt = os.path.join(FX, name, "kompile.txt")
        t = open(kt).read() if os.path.exists(kt) else ""
        if "\nstripped sha256: " not in t:
            continue
        kore = recorded_text(name)
        if kore is None:
            stale.append(name); continue
        t = re.sub(r"^stripped sha256: \w+$", f"stripped sha256: {sha(stripped(kore))}", t, flags=re.M)
        c = conf(name)
        for rel in ("same_as", "differs_from"):
            if rel in c:
                other = recorded_text(c[rel])
                if other is None:
                    stale.append(name); break
                eq = stripped(other) == stripped(kore)
                line = f"{rel} {c[rel]}: {'equal' if eq else 'different'} after stripping"
                t, k = re.subn(rf"^(?:same_as|differs_from) {re.escape(c[rel])}: \w+ after stripping$",
                               line, t, flags=re.M)
                if k != 1:
                    stale.append(name); break
        else:
            open(kt, "w").write(t); done += 1
    print(f"kfix rehash: {done} rewritten, {len(stale)} with no cache of their run"
          + (": " + " ".join(stale) if stale else ""))
    return 1 if stale else 0


def account_of(name, c):
    """`kcore account` of fixture NAME's text as `run` writes account.txt, the text read from the
    cache (a kompiled fixture) or from kcore-spec (a `kore` fixture); None when the cache lacks it."""
    env = {**os.environ, "LEAN_NUM_THREADS": "1"}
    if "kore" in c:
        a = subprocess.run([*WRAP, "timeout", "300", KCORE, "account", c["kore"]], cwd=K,
                           capture_output=True, text=True, env=env)
        return a.stdout + a.stderr + f"(exit {a.returncode})\n"
    h = recorded_sha(name)
    kore = cache_get(h) if h else None
    if kore is None:
        return None
    return account_at(kore, os.path.join(WORK, name, "account"), builtin_dir())


def account_at(kore, src, bd):
    """`kcore account` of a text as kompile.txt hashes it (FIXTURE/, BUILTIN/) with its paths restored
    as the directory src and the builtin directory bd (any path ending in include/kframework/builtin),
    written to src/out/definition.kore and read from src as `run` does; the output with src and bd
    replaced back (norm, then bd)."""
    raw = kore.replace("BUILTIN/", bd + "/").replace("FIXTURE/", src + "/").replace("FIXTURE", src)
    if norm(raw, src).replace(bd + "/", "BUILTIN/") != kore:
        raise SystemExit(f"kfix: {src}: the cached text's paths cannot be restored")
    os.makedirs(os.path.join(src, "out"), exist_ok=True)
    open(os.path.join(src, "out/definition.kore"), "w").write(raw)
    a = subprocess.run([*WRAP, "timeout", "300", KCORE, "account", "out/definition.kore"], cwd=src,
                       capture_output=True, text=True, env={**os.environ, "LEAN_NUM_THREADS": "1"})
    return norm(a.stdout + a.stderr, src).replace(bd + "/", "BUILTIN/") + f"(exit {a.returncode})\n"


def sem_params(src):
    """The `param` lines of `kcore sem-fields out/definition.kore` read in src, then `(exit N)`
    (fixture.toml params)."""
    a = subprocess.run([*WRAP, "timeout", "300", KCORE, "sem-fields", "out/definition.kore"], cwd=src,
                       capture_output=True, text=True, env={**os.environ, "LEAN_NUM_THREADS": "1"})
    lines = [l for l in a.stdout.split("\n") if l.startswith("param\t")]
    return "".join(l + "\n" for l in lines) + norm(a.stderr, src) + f"(exit {a.returncode})\n"


def account_deep(kore, name):
    """`kcore account` of a cached text kompiled elsewhere: FIXTURE/ restored twelve directory levels
    below .lake/kfix/NAME/depth and BUILTIN/ as FAKE_BUILTIN, normalised back. It must equal the
    account at the usual place (FIX-core.account-trunc-path): an account line may not depend on where
    the text was kompiled or where K is installed."""
    return account_at(kore, os.path.join(WORK, name, "depth", *(["deeper"] * 12), "s"), FAKE_BUILTIN)


def accounts(names, write):
    """Each fixture's account from its cached text against account.txt, serially; with write, the
    differing ones re-recorded. Each kompiled fixture's text is also read a second time kompiled
    elsewhere (account_deep), which must give the same account (with or without write). Exit 1 when
    one differs (without write), a second account differs, or a text is not cached."""
    if not os.path.isdir(builtin_dir()):
        raise SystemExit(f"kfix accounts: no K builtin directory {builtin_dir()}: set K_RUST or K_KOMPILE")
    same, diff, missing, depth = [], [], [], []
    for name in names:
        acc = os.path.join(FX, name, "account.txt")
        c = conf(name)
        if not os.path.exists(acc) or not ("kore" in c or recorded_sha(name)):
            continue
        got = account_of(name, c)
        if got is None:
            missing.append(name); continue
        if "kore" not in c:
            deep = account_deep(cache_get(recorded_sha(name)), name)
            if deep != got:
                depth.append(name)
                sys.stdout.writelines(difflib.unified_diff(
                    got.splitlines(True), deep.splitlines(True), f"{name} (here)", f"{name} (deep)"))
        pdiff = False
        if c.get("params") and "kore" not in c:
            pp = os.path.join(FX, name, "params.txt")
            pg = sem_params(os.path.join(WORK, name, "account"))
            old = open(pp).read() if os.path.exists(pp) else ""
            if pg != old:
                pdiff = True
                if write:
                    open(pp, "w").write(pg)
                else:
                    sys.stdout.writelines(difflib.unified_diff(
                        old.splitlines(True), pg.splitlines(True), f"{name}/params.txt", f"{name} (now)", n=0))
        if got == open(acc).read() and not pdiff:
            same.append(name); continue
        diff.append(name)
        if got == open(acc).read():
            continue
        if write:
            open(acc, "w").write(got)
        else:
            sys.stdout.writelines(difflib.unified_diff(
                open(acc).read().splitlines(True), got.splitlines(True), f"{name}/account.txt", f"{name} (now)", n=0))
    print(f"kfix accounts: {len(same)} equal, {len(diff)} {'re-recorded' if write else 'differ'}"
          + (": " + " ".join(diff) if diff else "") + f", {len(missing)} not in the cache {CACHE}"
          + (": " + " ".join(missing) if missing else "")
          + f"; {len(depth)} whose account kompiled elsewhere differs"
          + (": " + " ".join(depth) if depth else ""))
    return 1 if missing or depth or (diff and not write) else 0


def cache_import(dirs):
    """Put DIR/NAME/definition.norm.kore into the cache when its sha256 is NAME's recorded one."""
    have, put, none = 0, 0, []
    for name in sorted(os.listdir(FX)):
        h = recorded_sha(name)
        if not h:
            continue
        if cache_get(h) is not None:
            have += 1; continue
        for d in dirs:
            p = os.path.join(d, name, "definition.norm.kore")
            if os.path.exists(p) and sha(open(p).read()) == h:
                cache_put(open(p).read()); put += 1; break
        else:
            none.append(name)
    print(f"kfix cache {CACHE}: {have} present, {put} imported, {len(none)} found nowhere"
          + (": " + " ".join(none) if none else ""))
    return 1 if none else 0


def reading_notes():
    """The constructors of Parse.ReadingNote, in the order of KcoreSpec/Parse.lean."""
    src = open(os.path.join(K, "KcoreSpec/Parse.lean")).read()
    block = src.split("\ninductive ReadingNote where\n", 1)[1].split("\n  deriving", 1)[0]
    return re.findall(r"^  \| (\w+)", block, re.M)


def prints_note(account, note):
    """account.txt prints the note: a read class, a per-sentence reading, or a count above 0."""
    w = re.escape(note)
    return bool(re.search(rf"^\s*[1-9]\d* read {w} \[|^\s*sentence \d+: .*\b{w}\b"
                          rf"|\({w}\): [1-9]", account, re.M))


def check_notes(rows):
    """Each `notes` entry of a row or case (any list) names a fixture whose account prints the note,
    and every ReadingNote constructor has one."""
    notes, bad, seen = reading_notes(), [], {}

    def entries(where, e):
        yield where, e
        for i, c in enumerate(e.get("cases", [])):
            if isinstance(c, dict):
                yield from entries(f"{where} cases[{i}]", c)
    for l in (f"E{i}" for i in range(1, 9)):
        for key, r in rows.get(l, {}).items():
            for where, e in entries(f"{l} {key}", r):
                for note, f in e.get("notes", {}).items():
                    if note not in notes:
                        bad.append(f"{where}: notes {note}: no constructor of ReadingNote"); continue
                    a = os.path.join(FX, f, "account.txt")
                    if not os.path.exists(a):
                        bad.append(f"{where}: notes {note}: no fixtures/{f}/account.txt"); continue
                    if not prints_note(open(a).read(), note):
                        bad.append(f"{where}: notes {note}: fixtures/{f}/account.txt does not print it"); continue
                    seen.setdefault(note, set()).add(f)
    for note in notes:
        if note not in seen:
            bad.append(f"ReadingNote.{note}: no `notes` entry names a fixture")
    print(f"kfix notes: {len(seen)} of {len(notes)} ReadingNote constructors with a fixture printing them"
          + "".join(f"; {x}: {', '.join(sorted(seen[x]))}" for x in notes if x in seen))
    return bad


D1_TEXT = """module A
  import B []
// rule f() => 1 requires true [label(A.r)]
  axiom{R} \\rewrites{S}(Lblf{}(), \\dv{S}("1 // one /* two */")) [label{}("A.r"), UNIQUE'Unds'ID{}("u1")]
endmodule []
"""
D1_STRICT = "c3-strict-base"
# the two disjuncts of a negated disjunction as kompile writes an [owise] equation's: a chain of two
# existentials, and one existential
D1_EX1 = ("\\exists{R} (Var'Unds'Gen0:SortA{}, \\exists{R} (Var'Unds'Gen1:SortB{}, \\and{R}(\\in{SortA{}, R}("
          "X0:SortA{}, Var'Unds'Gen0:SortA{}), \\in{SortB{}, R}(X1:SortB{}, Var'Unds'Gen1:SortB{}))))")
D1_EX2 = "\\exists{R} (Var'Unds'Gen2:SortA{}, \\in{SortA{}, R}(X0:SortA{}, Lblg{}(Var'Unds'Gen2:SortA{})))"


def d1_exists(x, y):
    return ("module A\n  axiom{R} \\implies{R}(\\not{R}(\\or{R}(\\bottom{R}(), \\or{R}(" + x + ", " + y
            + "))), \\top{R}()) []\nendmodule []\n")


def check_stripped():
    """D1 of `stripped` (findings/C3-unbound-rulings.md section 1, C3.kfix-stripped-comments): two
    texts differing only in a comment, or only in the main module's name, are equal; two texts
    differing in a sentence, in a string literal holding `//` or `/*`, or in a label naming
    another module are different. On D1_TEXT and, when cached, D1_STRICT's kompiled text (strict
    productions: a heating and a cooling label per argument). On the text of D1_EX1 and D1_EX2 (d1_exists): it with a chain's
    two binders in the other order, with the generated variables numbered by that order, and with
    its two disjuncts in the other order (numbered by position) are equal; the text with the two
    bound variables exchanged in the body, and with a binder of another sort, are different."""
    t = D1_TEXT
    equal = [
        t.replace("// rule f() => 1 requires true [label(A.r)]", "// rule something else"),
        t.replace("// rule f() => 1 requires true [label(A.r)]\n", ""),
        t.replace("  import B []", "  import B []// trailing").replace("endmodule []", "/* x */endmodule []"),
        t.replace("  axiom{R}", "  /* x\n y */axiom{R}"),
        t.replace("module A", "module A2").replace("label{}(\"A.r\")", "label{}(\"A2.r\")")
         .replace("label(A.r)", "label(A2.r)"),
    ]
    different = [
        t.replace("Lblf{}()", "Lblg{}()"),
        t.replace("1 // one /* two */", "1 // one /* three */"),
        t.replace("1 // one /* two */", "1 // won /* two */"),
        t.replace("label{}(\"A.r\")", "label{}(\"B.r\")"),
        t.replace("label{}(\"A.r\")", "label{}(\"A.s\")"),
    ]
    bad = [f"D1 of stripped: equal case {i} differs" for i, u in enumerate(equal) if stripped(u) != stripped(t)]
    bad += [f"D1 of stripped: different case {i} is equal" for i, u in enumerate(different)
            if stripped(u) == stripped(t)]
    e, a, b = d1_exists(D1_EX1, D1_EX2), "\\exists{R} (Var'Unds'Gen0:SortA{}, ", "\\exists{R} (Var'Unds'Gen1:SortB{}, "
    swap = e.replace(a + b, b + a)
    renum = swap.replace("Gen0", "GenT").replace("Gen1", "Gen0").replace("GenT", "Gen1")
    ex_equal = [swap, renum, d1_exists(D1_EX2.replace("Gen2", "Gen0"),
                                        D1_EX1.replace("Gen1", "Gen2").replace("Gen0", "Gen1"))]
    ex_different = [e.replace("(X0:SortA{}, Var'Unds'Gen0:SortA{})", "(X0:SortA{}, Var'Unds'Gen1:SortA{})")
                    .replace("(X1:SortB{}, Var'Unds'Gen1:SortB{})", "(X1:SortB{}, Var'Unds'Gen0:SortB{})"),
                    e.replace("Var'Unds'Gen1:SortB{}, \\and", "Var'Unds'Gen1:SortC{}, \\and")]
    bad += [f"D1 of stripped: exists equal case {i} differs" for i, u in enumerate(ex_equal)
            if u == e or stripped(u) != stripped(e)]
    bad += [f"D1 of stripped: exists different case {i} is equal" for i, u in enumerate(ex_different)
            if u == e or stripped(u) == stripped(e)]
    if '"1 // one /* two */"' not in stripped(t):
        bad.append("D1 of stripped: a string literal holding // or /* is cut")
    kore = recorded_text(D1_STRICT)
    if kore is not None:
        name = main_name(kore)
        renamed = re.sub(rf"(?<![\w-]){re.escape(name)}(?![\w-])", name + "-RENAMED", kore)
        if renamed == kore or stripped(renamed) != stripped(kore):
            bad.append(f"D1 of stripped: {D1_STRICT} with its main module renamed differs")
        lab = re.search(r'label\{\}\("' + re.escape(name) + r'\.([\w-]+)"\)', kore)
        if not lab or stripped(kore.replace(lab[0], lab[0].replace(lab[1], lab[1] + "x"), 1)) == stripped(kore):
            bad.append(f"D1 of stripped: {D1_STRICT} with one rule label changed is equal")
        if "// rule" not in kore or "// rule" in stripped(kore):
            bad.append(f"D1 of stripped: {D1_STRICT}'s // rule comments not removed")
    print(f"kfix stripped D1: {len(equal) + len(ex_equal)} equal and {len(different) + len(ex_different)}"
          " different cases on small texts"
          + (f", {D1_STRICT} renamed and relabelled" if kore is not None else f"; {D1_STRICT} not cached"))
    return bad


def check(lists):
    rows = tomllib.load(open(os.path.join(K, "test/constructs/rows.toml"), "rb"))
    bad, n, cache = [], {}, {}
    for l in lists:
        for key, r in rows[l].items():
            f = r.get("fixture")
            n.setdefault(l, [0, 0])
            if not f:
                bad.append(f"{l} {key}: no fixture"); continue
            if ("sentence" in r) == ("no_sentence" in r):
                bad.append(f"{l} {key}: needs exactly one of sentence, no_sentence"); continue
            if f == "none":
                if "no_sentence" not in r:
                    bad.append(f"{l} {key}: fixture none without no_sentence")
                n[l][1] += 1; continue
            d = os.path.join(FX, f)
            if not os.path.isdir(d):
                bad.append(f"{l} {key}: no fixture directory {f}"); continue
            if f not in cache:
                cache[f] = "".join(open(os.path.join(d, x)).read() for x in ("kore.txt", "kompile.txt")
                                   if os.path.exists(os.path.join(d, x)))
            for s in r.get("sentence", []):
                if s not in cache[f]:
                    bad.append(f"{l} {key}: {s!r} not in {f}")
            n[l][0 if "sentence" in r else 1] += 1
    for f in sorted(os.listdir(FX)):
        kt = os.path.join(FX, f, "kompile.txt")
        if not os.path.exists(kt):
            bad.append(f"fixture {f}: not run"); continue
        t = open(kt).read()
        if "UNEXPECTED" in t:
            bad.append(f"fixture {f}: unexpected exit")
        for m in re.finditer(r"^(same_as|differs_from) (\S+): (\w+)", t, re.M):
            if (m[1] == "same_as") != (m[3] == "equal"):
                bad.append(f"fixture {f}: {m[1]} {m[2]} is {m[3]}")
        try:
            c = conf(f)
        except SystemExit as err:
            bad.append(f"fixture {f}: {err}"); continue
        for rel in ("same_as", "differs_from"):
            if rel in c and f"{rel} {c[rel]}:" not in t:
                bad.append(f"fixture {f}: {rel} not recorded")
        for kf in kk_files(c["kk"]) if "kk" in c else []:
            line = (f"kk {os.path.relpath(kf, os.path.dirname(os.path.dirname(K)))}: sha256 "
                    f"{hashlib.sha256(open(kf, 'rb').read()).hexdigest()}")
            if line not in t:
                bad.append(f"fixture {f}: kompile.txt does not record the present text of kk {c['kk']} "
                           f"({os.path.basename(kf)}): kfix.py run {f}")
    bad += check_notes(rows)
    bad += check_stripped()
    ks =[f for f in sorted(os.listdir(FX)) if recorded_sha(f)]
    print(f"kfix cache {CACHE}: {sum(1 for f in ks if cache_get(recorded_sha(f)) is not None)} of "
          f"{len(ks)} kompiled texts")
    for l in lists:
        n.setdefault(l, [0, 0])
        print(f"kfix {l}: {n[l][0]} rows with sentences, {n[l][1]} rows with no_sentence")
    nofx = [b for b in bad if b.endswith(": no fixture")]
    for l in lists:
        c = sum(1 for b in nofx if b.startswith(l + " "))
        if c:
            print(f"kfix {l}: {c} rows without a fixture")
    rest = [b for b in bad if not b.endswith(": no fixture")]
    for b in rest[:60]:
        print("kfix: " + b)
    if len(rest) > 60:
        print(f"kfix: ... {len(rest) - 60} more")
    return 1 if bad else 0


if __name__ == "__main__":
    if sys.argv[1:2] == ["check"]:
        sys.exit(check(sys.argv[2:] or LISTS))
    if sys.argv[1:2] == ["rehash"]:
        sys.exit(rehash(sys.argv[2:] or sorted(os.listdir(FX))))
    if sys.argv[1:2] == ["accounts"]:
        w = "--write" in sys.argv[2:]
        sys.exit(accounts([x for x in sys.argv[2:] if x != "--write"] or sorted(os.listdir(FX)), w))
    if sys.argv[1:2] == ["cache-import"]:
        sys.exit(cache_import(sys.argv[2:]))
    if sys.argv[1:2] != ["run"]:
        raise SystemExit(__doc__)
    names = sys.argv[2:] or sorted(os.listdir(FX))
    # base first, then every fixture before those that compare with it
    order, seen = [], set()

    def visit(x):
        if x in seen: return
        seen.add(x)
        c = conf(x)
        for rel in ("same_as", "differs_from", "text_from"):
            if rel in c and c[rel] in names: visit(c[rel])
        order.append(x)
    if "base" in names: visit("base")
    for x in names: visit(x)
    names = order
    t = sum(run(x) for x in names)
    print(f"kfix: {len(names)} kompiles, {t:.0f}s")
