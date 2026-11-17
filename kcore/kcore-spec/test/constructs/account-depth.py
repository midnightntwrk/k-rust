"""`kcore account` of one text kompiled in two places (FIX-core.account-trunc-path): each fixture's
cached text (kfix.py's cache, no kompile) with its paths restored twice, FIXTURE/ as a directory one
level under .lake/kfix/NAME/depth and as one twelve levels further down, BUILTIN/ as K's builtin
directory and as kfix.FAKE_BUILTIN (kfix.account_deep), each account normalised back (FIXTURE/,
BUILTIN/). The two accounts of a text must be equal: the account's lines may not depend on where a
text was kompiled. `kfix.py accounts` makes the same comparison for every text it checks (against its
account at .lake/kfix/NAME/account); this script is the comparison alone, without account.txt.
Known-bad: a `kcore` that cuts a line at a fixed number of characters of the raw sentence (Source
paths counted, before FIX-core.account-trunc-path) prints different lines for e2-registry-symbol-name
(a user Source before the cut) and e3-mint (a builtin Source and a user Source before the cut); with
such a binary as KCORE_BIN both this script and `kfix.py accounts` exit 1 there.

Usage (from kcore-spec, K_RUST or K_KOMPILE naming a K installation):
  python3 -I test/constructs/account-depth.py [NAME...]   (default: every kompiled fixture)
Exit 1 when some text's two accounts differ or a text is not in the cache."""
import difflib, os, sys

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import kfix



def main(names):
    if not os.path.isdir(kfix.builtin_dir()):
        raise SystemExit(f"account-depth: no K builtin directory {kfix.builtin_dir()}: set K_RUST or K_KOMPILE")
    same, diff, missing = [], [], []
    for name in names:
        h = kfix.recorded_sha(name)
        kore = kfix.cache_get(h) if h else None
        if kore is None:
            if h: missing.append(name)
            continue
        base = os.path.join(kfix.WORK, name, "depth")
        a = kfix.account_at(kore, os.path.join(base, "s"), kfix.builtin_dir())
        b = kfix.account_deep(kore, name)
        if a == b:
            same.append(name); continue
        diff.append(name)
        sys.stdout.writelines(difflib.unified_diff(a.splitlines(True), b.splitlines(True),
                                                   f"{name} (shallow)", f"{name} (deep)"))
    print(f"account-depth: {len(same)} equal at both depths, {len(diff)} differ"
          + (": " + " ".join(diff) if diff else "") + f", {len(missing)} not in the cache"
          + (": " + " ".join(missing) if missing else ""))
    return 1 if diff or missing else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:] or sorted(os.listdir(kfix.FX))))
