"""The links from rows.toml and the fixtures to the Kore-in-K catalogue (krs/semantics/kore of this
tree; findings/KK-redesign.md section 5.2).

Usage (from kcore-spec): python3 -I test/constructs/kklink.py

A row of rows.toml (of any list, or a `cases` entry) may carry
  kk       a list of entry ids of the catalogue ("t105-concrete-rule", or "kk:t105-concrete-rule"):
           the entries whose reading the row rests on;
  kk_sha   a table from each of those ids to the entry's ruling hash when the row was written, as
           `krs/semantics/kore/tools/check.py --ruling-sha ID` prints it (the SHA-256 of the entry's
           [ruling], [ruling.kore], [[ruling.basis]] and [[reading]] blocks).
A fixture.toml may carry `kk`, one entry id whose K text kfix.py copies (kfix.py's docstring).

Fails (exit 1) on an id that names no entry of the catalogue, on a row with kk and no kk_sha entry
for one of its ids, or with a kk_sha id that is not in its kk. Reports, and does not fail on, a row
whose recorded hash is not the entry's present one: the entry's ruling changed since the row was
written, and the row is stale until someone re-reads the entry and records the new hash.
"""
import os
import subprocess
import sys
import tomllib

K = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
ROWS = os.path.join(K, "test/constructs/rows.toml")
FX = os.path.join(K, "test/constructs/fixtures")
CATALOGUE = os.path.join(os.path.dirname(os.path.dirname(K)), "krs/semantics/kore")
CHECK = os.path.join(CATALOGUE, "tools/check.py")


def bare(i):
    return i[3:] if isinstance(i, str) and i.startswith("kk:") else i


def linked(rows):
    """(where, table) for every row or cases entry of rows.toml that carries kk or kk_sha."""
    for l, tab in rows.items():
        if not isinstance(tab, dict):
            continue
        for key, r in tab.items():
            if not isinstance(r, dict):
                continue
            for where, e in [(f"{l} {key}", r)] + [(f"{l} {key} case {c.get('case', i)}", c)
                                                    for i, c in enumerate(r.get("cases", []))
                                                    if isinstance(c, dict)]:
                if "kk" in e or "kk_sha" in e:
                    yield where, e


def ruling_hashes(ids):
    """The present ruling hash of each id that names an entry; the others are absent."""
    if not ids:
        return {}
    known = {d for sub in ("texts", "cases") if os.path.isdir(os.path.join(CATALOGUE, sub))
             for d in os.listdir(os.path.join(CATALOGUE, sub))}
    named = sorted(i for i in ids if i in known)
    if not named:
        return {}
    p = subprocess.run([sys.executable, "-I", CHECK, "--ruling-sha", *named], capture_output=True, text=True)
    if p.returncode != 0:
        raise SystemExit(f"kklink: check.py --ruling-sha failed: {p.stderr.strip()}")
    return dict(line.split(" ", 1) for line in p.stdout.split("\n") if line.strip())


def main():
    rows = tomllib.load(open(ROWS, "rb"))
    found = list(linked(rows))
    fixtures = []
    for f in sorted(os.listdir(FX)):
        p = os.path.join(FX, f, "fixture.toml")
        c = tomllib.load(open(p, "rb")) if os.path.exists(p) else {}
        if "kk" in c:
            fixtures.append((f, c["kk"]))
    ids = {bare(i) for _, e in found for i in (e.get("kk") if isinstance(e.get("kk"), list) else [])}
    ids |= {bare(i) for _, i in fixtures}
    present = ruling_hashes(ids)
    bad, stale, current = [], [], 0
    for where, e in found:
        kk, shas = e.get("kk"), e.get("kk_sha")
        if not isinstance(kk, list) or not kk or not all(isinstance(i, str) for i in kk):
            bad.append(f"{where}: kk is not a non-empty list of entry ids"); continue
        if not isinstance(shas, dict):
            bad.append(f"{where}: kk_sha is not a table from entry id to ruling hash"); continue
        ids = [bare(i) for i in kk]
        for i in sorted(set(map(bare, shas)) - set(ids)):
            bad.append(f"{where}: kk_sha names {i}, which kk does not")
        recorded = {bare(i): h for i, h in shas.items()}
        for i in ids:
            if i not in present:
                bad.append(f"{where}: kk {i} names no entry of krs/semantics/kore")
            elif i not in recorded:
                bad.append(f"{where}: kk_sha has no hash for {i} (check.py --ruling-sha {i})")
            elif recorded[i] != present[i]:
                stale.append(f"{where}: kk {i}: the ruling changed since the row was written "
                             f"(recorded {recorded[i][:12]}, now {present[i][:12]})")
            else:
                current += 1
    for f, i in fixtures:
        if not isinstance(i, str) or bare(i) not in present:
            bad.append(f"fixture {f}: kk {i!r} names no entry of krs/semantics/kore")
    print(f"kklink: {len(found)} rows with kk, {current} links current, {len(stale)} stale; "
          f"{len(fixtures)} fixtures with kk")
    for s in stale:
        print("kklink: stale: " + s)
    for b in bad:
        print("kklink: " + b)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
