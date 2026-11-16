"""Compare a review cone written by `#review_cone` (KcoreSpec/ReviewCone.lean) with a committed one.

Compared:
- the declaration names (the `NNN-NNN kind name` rows under each `## module` header);
- the lines and declarations the module headers add up to;
- each declaration's own line count (its range in its module);
- each declaration's TEXT: the lines of its range in its module's source, with trailing blanks
  removed (for a theorem the range is its statement only, as `#review_cone` writes it), the
  committed cone read against the committed tree's sources and the new cone against the new
  tree's;
- the section `## roots, as elaborated` verbatim.

A declaration that only moves (a different range, the same text) is not a change. Neither file is
rewritten. Not compared: the lines outside every range that a declaration's meaning can depend on
(`variable`, `open`, `namespace`, `notation`, `set_option`); a change there shows only through a
declaration whose elaborated type changes text, or through the roots section.

Usage: python3 -I test/cone.py COMMITTED NEW (--old-rev REV | --old-src DIR) [--new-src DIR] [--diff]
       python3 -I test/cone.py COMMITTED NEW --names-only

Run from the package root (kcore-spec/). The source of module `A.B.C` is looked up as
`A/B/C.lean` under the package root, `../aml-port` and `../kore-lean`, in that order.
--old-rev REV reads the committed tree's sources with `jj file show -r REV` (the revision the
committed cone was computed at); --old-src DIR reads them from DIR, another package root.
--new-src defaults to `.`. --diff prints a unified diff of each changed declaration's text.
--names-only skips the text comparison and says so (exit 1 still on names and line counts).

Exit 1 when the names, the line count, a declaration's own line count, a declaration's text or
the roots section differ; exit 2 when a source cannot be read."""
import argparse, difflib, os, re, subprocess, sys

ROOTS = ['.', '../aml-port', '../kore-lean']


def parse(path):
    mod, decls, lines, ndecl = None, {}, 0, 0
    roots, in_roots = [], False
    for l in open(path).read().split('\n'):
        if l.startswith('## '):
            in_roots = l.startswith('## roots, as elaborated')
        elif in_roots:
            roots.append(l.rstrip())
        m = re.match(r'^## (\S+)\s+\((\d+) declarations?, (\d+) lines?\)', l)
        if m:
            mod = m.group(1); ndecl += int(m.group(2)); lines += int(m.group(3))
            continue
        if l.startswith('## '):
            mod = None
            continue
        m = re.match(r'^\s+(\d+)-(\d+)\s+(\S+)\s+(\S+)', l)
        if m and mod:
            a, b = int(m.group(1)), int(m.group(2))
            decls[m.group(4)] = (mod, b - a + 1, m.group(3), a, b)
    while roots and roots[-1] == '':
        roots.pop()
    return decls, lines, ndecl, roots


class Sources:
    def __init__(self, src=None, rev=None):
        self.src, self.rev, self.cache = src, rev, {}

    def read(self, rel):
        if self.rev is not None:
            r = subprocess.run(['jj', 'file', 'show', '--no-pager', '-r', self.rev, rel],
                               capture_output=True, text=True)
            return r.stdout if r.returncode == 0 else None
        p = os.path.join(self.src, rel)
        return open(p).read() if os.path.exists(p) else None

    def module(self, mod):
        if mod not in self.cache:
            rel = os.path.join(*mod.split('.')) + '.lean'
            text = None
            for root in ROOTS:
                text = self.read(os.path.normpath(os.path.join(root, rel)))
                if text is not None:
                    break
            if text is None:
                where = f'revision {self.rev}' if self.rev is not None else self.src
                print(f'cone: cannot read the source of {mod} ({rel}) at {where}')
                sys.exit(2)
            self.cache[mod] = text.split('\n')
        return self.cache[mod]

    def text(self, entry):
        mod, _, _, a, b = entry
        return [l.rstrip() for l in self.module(mod)[a - 1:b]]


ap = argparse.ArgumentParser()
ap.add_argument('committed'); ap.add_argument('new')
ap.add_argument('--old-rev'); ap.add_argument('--old-src')
ap.add_argument('--new-src', default='.')
ap.add_argument('--diff', action='store_true')
ap.add_argument('--names-only', action='store_true')
args = ap.parse_args()
if not args.names_only and (args.old_rev is None) == (args.old_src is None):
    print("cone: give exactly one of --old-rev REV or --old-src DIR (the committed cone's tree), "
          'or --names-only to skip the text comparison')
    sys.exit(2)

O, ol, od, oroots = parse(args.committed)
N, nl, nd, nroots = parse(args.new)
added = sorted(set(N) - set(O))
removed = sorted(set(O) - set(N))
both = sorted(set(N) & set(O))
resized = [n for n in both if N[n][1] != O[n][1]]
print(f'cone: committed {ol} lines, {od} declarations; now {nl} lines, {nd} declarations')
for n in added: print(f'  added:   {N[n][2]} {n} ({N[n][0]}, {N[n][1]} lines)')
for n in removed: print(f'  removed: {O[n][2]} {n} ({O[n][0]})')
for n in resized: print(f'  lines:   {n} {O[n][1]} -> {N[n][1]}')

changed = []
if args.names_only:
    print('cone: TEXT NOT COMPARED (--names-only)')
else:
    old = Sources(src=args.old_src, rev=args.old_rev)
    new = Sources(src=args.new_src)
    for n in both:
        a, b = old.text(O[n]), new.text(N[n])
        if a != b:
            changed.append(n)
            print(f'  text:    {N[n][2]} {n} ({N[n][0]})')
            if args.diff:
                for l in difflib.unified_diff(a, b, f'committed {n}', f'now {n}', lineterm=''):
                    print('    ' + l)
roots_differ = oroots != nroots
if roots_differ:
    print('  roots, as elaborated: differ')
    if args.diff:
        for l in difflib.unified_diff(oroots, nroots, 'committed roots', 'now roots', lineterm=''):
            print('    ' + l)

if added or removed or resized or changed or roots_differ or ol != nl:
    print('cone: differs from the committed cone (not rewritten)')
    sys.exit(1)
print('cone: same declarations, line count' + ('' if args.names_only else ', texts') + ' and roots')
