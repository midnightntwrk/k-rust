"""Relative `Source` attributes in a kompiled KORE text.

kompile writes each sentence's `Source(PATH)` with the absolute path of the K file it read. This
tool rewrites PATH in place, in the attribute (`Source{}("Source(PATH)")`) and in kompile's `// rule`
comments (`...attributes.Source(Source(PATH))`), to a path relative to a root of the checkout:

  - a file of the tree that holds kcore-spec (kcore-spec's parent directory): relative to that
    directory, e.g. `kcore-spec/f2-examples/ens.k`;
  - another file of the k-rust checkout: relative to the checkout, e.g. `kink/examples/imp/imp.k`,
    also when the path names it through one of the checkout's top-level symbolic links (`imp-semantics`);
  - a file of a K installation's builtin directory (`.../include/kframework/builtin/F`): unchanged,
    since the reader recognises a builtin sentence by that suffix (Parse.kBuiltinFile?).

Any other absolute path is an error: nothing absolute is written silently. The k-rust checkout is
$K_RUST, or the nearest directory above kcore-spec holding Cargo.toml and crates/k-rust.

What the reader takes from a Source: whether it is krust's builtin (`krust-builtin://`), a K
installation's builtin (the suffix above) or the user's (anything else); whether it equals the main
module's Source (`srcOver`); and the string itself, kept in the presentation for `emit`. A rewrite
that keeps every builtin Source and maps the user Sources of one text one-to-one keeps all three,
so the definition's core is the same; `rewrite` checks the one-to-one part on each text.

Usage (from anywhere): python3 -I kcore-spec/test/relsource.py FILE...   (rewrites each FILE)
"""
import os, re, sys

KS = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TREE = os.path.dirname(KS)
BUILTIN = re.compile(r"/include/kframework/builtin/[^/]+$")
PATH = re.compile(r'(?<=Source\()(/[^)"]*)(?=\))')


def krust_root():
    if os.environ.get("K_RUST"):
        return os.path.abspath(os.environ["K_RUST"])
    d = TREE
    while d != os.path.dirname(d):
        d = os.path.dirname(d)
        if os.path.isfile(os.path.join(d, "Cargo.toml")) and os.path.isdir(os.path.join(d, "crates/k-rust")):
            return d
    return None


def _under(p, root):
    return root is not None and (p == root or p.startswith(root.rstrip("/") + "/"))


def relative(p, kr=None):
    """PATH's relative form (see the module doc); raises ValueError for another absolute path."""
    if not p.startswith("/") or BUILTIN.search(p):
        return p
    if _under(p, TREE):
        return os.path.relpath(p, TREE)
    if _under(p, kr):
        return os.path.relpath(p, kr)
    if kr is not None:
        rp = os.path.realpath(p)
        for n in sorted(os.listdir(kr)):
            link = os.path.join(kr, n)
            if os.path.islink(link) and _under(rp, os.path.realpath(link)):
                return os.path.join(n, os.path.relpath(rp, os.path.realpath(link)))
    raise ValueError(f"no relative form for {p} (tree {TREE}, k-rust checkout {kr})")


def rewrite(text, mapper=None):
    """TEXT with every absolute Source path replaced by mapper(path) (default `relative`); raises
    ValueError when two distinct paths of the text would get one form."""
    kr = krust_root()
    mapper = mapper or (lambda p: relative(p, kr))
    forms = {}
    def one(m):
        p = m.group(1)
        if p not in forms:
            forms[p] = mapper(p)
        return forms[p]
    out = PATH.sub(one, text)
    seen = {}
    for p, r in forms.items():
        if seen.setdefault(r, p) != p:
            raise ValueError(f"{seen[r]} and {p} would both be written {r}")
    return out


def rewrite_file(path, mapper=None):
    t = open(path, encoding="utf-8").read()
    n = rewrite(t, mapper)
    if n != t:
        open(path, "w", encoding="utf-8").write(n)
    return n != t


if __name__ == "__main__":
    bad = 0
    for f in sys.argv[1:]:
        try:
            print(f"{f}: {'rewritten' if rewrite_file(f) else 'unchanged'}")
        except ValueError as e:
            print(f"{f}: {e}", file=sys.stderr); bad = 1
    sys.exit(bad)
