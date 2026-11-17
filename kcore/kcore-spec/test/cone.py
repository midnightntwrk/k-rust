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

Usage: python3 -I test/cone.py COMMITTED NEW (--old-git REV | --old-rev REV | --old-src DIR) [--new-src DIR] [--diff] [--roots FILE]
       python3 -I test/cone.py COMMITTED NEW --names-only [--roots FILE]

COMMITTED is the committed cone (v), ../core-cone.txt; NEW is cone (v) as test/ConeV.lean writes it
(.lake/cone-v.txt) or test/ReviewCone.lean (.lake/review-cone-core-hyp.txt), the same cone.
Run from the package root (kcore-spec/). The source of module `A.B.C` is looked up as
`A/B/C.lean` under the package root, `../aml-port` and `../kore-lean`, in that order.
The committed tree is the one the committed cone was computed at. --old-git REV reads its sources
from the git revision REV: `git archive REV` of the package's parent directory (kcore/, which holds
the package and ../aml-port, ../kore-lean) into a temporary directory, then as --old-src (e.g.
`--old-git main` on a git worktree, for a cone computed at main). --old-rev REV reads them with
`jj file show -r REV` (a jj workspace); --old-src DIR reads them from DIR, another package root.
--new-src defaults to `.`. --diff prints a unified diff of each changed declaration's text.
--names-only skips the text comparison and says so (exit 1 still on names and line counts).
--roots FILE (test/roots.toml) checks first that NEW was computed from FILE: its `# roots:` line
lists FILE's roots in order, its `# read as opaque` line FILE's opaque declarations in order (no such
line when there are none), and each opaque declaration's reason is on its `#   opaque` line; exit 1
otherwise.

Exit 1 when the names, the line count, a declaration's own line count, a declaration's text or
the roots section differ; exit 2 when a source cannot be read (or REV of --old-git cannot be
archived)."""
import argparse, difflib, io, os, re, subprocess, sys, tarfile, tempfile, tomllib

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
ap.add_argument('--old-rev'); ap.add_argument('--old-src'); ap.add_argument('--old-git')
ap.add_argument('--new-src', default='.')
ap.add_argument('--diff', action='store_true')
ap.add_argument('--names-only', action='store_true')
ap.add_argument('--roots')
args = ap.parse_args()
if not args.names_only and [args.old_rev, args.old_src, args.old_git].count(None) != 2:
    print("cone: give exactly one of --old-git REV, --old-rev REV or --old-src DIR (the committed "
          "cone's tree), or --names-only to skip the text comparison")
    sys.exit(2)


def git_tree(rev):
    """Extract the package's parent directory at git revision `rev` into a temporary directory;
    return (the TemporaryDirectory, the package root inside it)."""
    def git(*a):
        r = subprocess.run(['git', *a], capture_output=True)
        if r.returncode != 0:
            print(f'cone: git {" ".join(a)} failed: {r.stderr.decode().strip()}')
            sys.exit(2)
        return r.stdout
    top = git('rev-parse', '--show-toplevel').decode().strip()
    prefix = git('rev-parse', '--show-prefix').decode().strip().rstrip('/')
    parent = os.path.dirname(prefix)
    if not prefix or not parent:
        print(f'cone: --old-git needs the package root inside a subdirectory of the git tree (prefix {prefix!r})')
        sys.exit(2)
    data = git('-C', top, 'archive', '--format=tar', rev, '--', parent)
    tmp = tempfile.TemporaryDirectory(prefix='cone-old-git-')
    with tarfile.open(fileobj=io.BytesIO(data)) as t:
        t.extractall(tmp.name, filter='data')
    return tmp, os.path.join(tmp.name, prefix)


old_tmp = None
if args.old_git is not None and not args.names_only:
    old_tmp, args.old_src = git_tree(args.old_git)
    print(f'cone: committed tree read from git {args.old_git}')

if args.roots is not None:
    spec = tomllib.load(open(args.roots, 'rb'))
    want_roots = spec.get('roots', [])
    want_opaque = list(spec.get('opaque', {}).items())
    got_roots, got_opaque, got_reasons = None, [], {}
    for l in open(args.new).read().split('\n'):
        if l.startswith('# roots: '):
            got_roots = l[len('# roots: '):].split(', ')
        elif l.startswith('# read as opaque (type only, value not entered): '):
            got_opaque = l.split(': ', 1)[1].split(', ')
        elif l.startswith('#   opaque '):
            n, r = l[len('#   opaque '):].split(': ', 1)
            got_reasons[n] = r
        elif not l.startswith('#'):
            break
    bad = []
    if got_roots != want_roots: bad.append(f'roots {got_roots} != {want_roots}')
    if got_opaque != [n for n, _ in want_opaque]: bad.append(f'opaque {got_opaque} != {[n for n, _ in want_opaque]}')
    for n, r in want_opaque:
        if got_reasons.get(n) != r: bad.append(f'reason of {n}: {got_reasons.get(n)!r} != {r!r}')
    if bad:
        print(f'cone: {args.new} was not computed from {args.roots}: ' + '; '.join(bad))
        sys.exit(1)
    print(f'cone: computed from {args.roots} ({len(want_roots)} roots, {len(want_opaque)} read as opaque)')

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
