#!/usr/bin/env python3
"""The manifest's rows for silentTable against the table (DONE-0 C5, manifest prose).

../core-manifest.toml's entry whose declaration names silentTable lists, in `rows`, the rows.toml
entries of the table's keys, and says in `reason` how many keys there are. This check reads the
keys from the sources: the entries of `silentTable` (KcoreSpec/Hooks.lean), each key's registry
hook (`regHookNames`, KcoreSpec/FixedSignature.lean) and KORE name (`regSymNames` with
KcoreSpec/BuiltinNames.lean's `newSymNames`, by the number of its `def NAME : Sym := N`). A key with a registry hook H has the one E6 row `hook:H:…`; a key
without one has the one E6 row `symbol:MODULE:NAME` of its KORE name. It fails when `rows` is not
exactly those entries, when one of them is no entry of rows.toml, or when the counts in `reason`
("N keys", "(A hook rows and B rows of library symbols …") are not the table's.

Usage: python3 -I test/constructs/silentkeys.py [--rows]   (--rows prints the expected list)
"""
import os, re, sys, tomllib

K = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def read(rel):
    return open(os.path.join(K, rel), encoding="utf-8").read()


def body(src, head):
    """The text of the list literal that follows `head` (up to the first line ending the list)."""
    i = src.index(head)
    i = src.index(":=", i)
    j = src.index("\n\n", i)
    return src[i:j]


def expected():
    hooks, sig = read("KcoreSpec/Hooks.lean"), read("KcoreSpec/FixedSignature.lean")
    keys = re.findall(r"\((\w+), fun ", body(hooks, "def silentTable :"))
    if len(keys) != len(set(keys)) or not keys:
        sys.exit("silentkeys: could not read silentTable's keys")
    num = {m.group(1): int(m.group(2)) for m in re.finditer(r"def (\w+) : Sym := (\d+)\s*$", sig, re.M)}
    hook = dict(re.findall(r'\((\w+), "([A-Z-]+\.[A-Za-z0-9_]+)"\)', body(sig, "def regHookNames :")))
    strs = lambda t: re.findall(r'"((?:[^"\\]|\\.)*)"', t)
    reg = body(sig + "\n\n", "def regSymNames :")
    if "BuiltinNames.newSymNames" not in reg:
        sys.exit("silentkeys: regSymNames is no longer its own names ++ BuiltinNames.newSymNames ++ …")
    pre, post = reg.split("BuiltinNames.newSymNames")
    names = strs(pre) + strs(body(read("KcoreSpec/BuiltinNames.lean"), "def newSymNames :")) + strs(post)
    e6 = tomllib.load(open(os.path.join(K, "test/constructs/rows.toml"), "rb"))["E6"]
    rows, bad = [], []
    for k in keys:
        if k in hook:
            found = [r for r in e6 if r.startswith(f"hook:{hook[k]}:")]
        elif k in num and num[k] < len(names):
            found = [r for r in e6 if r.startswith("symbol:") and r.split(":", 2)[2] == names[num[k]]]
        else:
            found = []
        if len(found) != 1:
            bad.append(f"key {k}: {len(found)} E6 rows, not one")
        rows += [f"E6 {r}" for r in found]
    return keys, [k for k in keys if k in hook], rows, bad


def main():
    keys, hooked, rows, bad = expected()
    if "--rows" in sys.argv[1:]:
        for r in rows:
            print(r)
        return 1 if bad else 0
    man = tomllib.load(open(os.path.join(os.path.dirname(K), "core-manifest.toml"), "rb"))

    def entries(node):
        if isinstance(node, dict):
            if isinstance(node.get("declaration"), str):
                yield node
            for v in node.values():
                yield from entries(v)
        elif isinstance(node, list):
            for v in node:
                yield from entries(v)

    es = [e for e in entries(man) if re.search(r"\bsilentTable\b", e["declaration"]) and "rows" in e]
    if len(es) != 1:
        bad.append(f"{len(es)} manifest entries declare silentTable with `rows`, not one")
    else:
        e = es[0]
        have = e["rows"]
        for r in sorted(set(rows) - set(have)):
            bad.append(f"the manifest's rows lack {r}")
        for r in sorted(set(have) - set(rows)):
            bad.append(f"the manifest's rows name {r}, which is no key of silentTable")
        if len(have) != len(set(have)):
            bad.append("the manifest's rows repeat an entry")
        n, a, b = len(keys), len(hooked), len(keys) - len(hooked)
        reason = e.get("reason", "")
        if f"silentTable has {n} keys" not in reason:
            bad.append(f"the manifest's reason does not say `silentTable has {n} keys`")
        if f"({a} hook rows and {b} rows of library symbols" not in reason:
            bad.append(f"the manifest's reason does not say `({a} hook rows and {b} rows of library symbols`")
    for m in bad:
        print(f"silentkeys: {m}")
    if not bad:
        print(f"silentkeys: the manifest names silentTable's {len(keys)} keys "
              f"({len(hooked)} hook rows, {len(keys) - len(hooked)} library symbols)")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
