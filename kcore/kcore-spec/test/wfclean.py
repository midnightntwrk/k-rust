"""No text is read clean with `wf` false and no stated reading of what `wf` rejects: `kcore account`
on each text, which ends, when the reader refuses nothing, with `parse: ok; wf B; failing: [...]`,
`coreOK: B; failing: [...]` and `refused by the account: N`. A text the reader reads with nothing
refused is either well formed or names the failing conjunct; this check fails on every such text
whose `wf` is false, unless the account states the construct `wf` rejects and the route around it:
otherwise the reader read the text with no stated reading of that construct, or `wf` rejects a
reading it should admit.

Two constructs are so stated, each by a list the account prints.

A clause whose predicate is not `\top` (the conjunct `clausesPreTop`). `wf`'s consumers derive
`FnHyp` from the named facts and decide totality and termination reading no clause predicate, and
where a predicate is not `\top` the named facts do not give `FnHyp` (test/FnSolvesDet.lean);
`coreOK` does not ask it, and the account lists those clauses and says that the `--core` package's
statements take `FnHyp` itself. The list is stated when it is printed.

A clause holding existential variables or a right-side predicate (the conjunct `clausesNoExsTop`).
Such a clause gives its function's value at a match as the union of its instances, which is one
result only where the instances are decided and those that hold agree; the text does not state
that, so it is owed of the clause as its match obligation (`MatchIndependent`, the fourth conjunct
of `FnHyp`), and `sound_hyp` and `complete_hyp` are stated of the text under it. `coreOK` does not
ask it; the account lists every clause holding existential variables with that obligation. The
list is stated when its heading is printed with a count of at least one, that many clause lines
follow it, and each line says `MatchIndependent open` of a clause `matchObligationsL` names (a
line the account marks as not named is the fact of no statement, and is not stated). The account
lists the clauses by their existential variables: a clause with a right-side predicate and no
existential variable is on no list, and this check does not see it beside a listed clause.

A text read clean with `coreOK` true whose failing conjuncts are `clausesPreTop` alone,
`clausesNoExsTop` alone, or both, each with its list stated, meets layer 1 (i) of C14
(designs/DONE-0: `coreOK` with the failing `wf` conjunct named); it is listed as stated, not as a
failure. The two are accepted together because each list answers its own conjunct and the routes
agree: the package that takes `FnHyp` itself for the predicates takes with it the match
obligations, which are `FnHyp`'s fourth conjunct. Any other failing conjunct, alone or beside
these, is a failure.

The texts: the corpus's extracted ones (`.lake/corpus/defs`, `test/corpus.py` extracts them), the
f2-examples' `.kore` files, and the files and directories given (a directory: every
`definition.kore` below it). One line per text read clean with `wf` false, its failing conjuncts;
then the counts. Each `kcore account` under a 12 GiB memory scope, JOBS at once.

Usage (from kcore-spec, `kcore` built): python3 -I test/wfclean.py [-j JOBS] [--no-corpus] [PATH...]
Exit 1 when some text is read clean with `wf` false and no stated reading."""
import concurrent.futures, os, subprocess, sys

K = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CAP = ['systemd-run', '--user', '--scope', '-q', '-p', 'MemoryMax=12G', '-p', 'MemorySwapMax=0', 'timeout', '300']
EXE = os.path.join(K, '.lake/build/bin/kcore')
# the two `wf` conjuncts with a stated reading, as the account's failing list prints them, and
# the heading of the account's list for each
PRE_TOP = "clauses' premise predicates \\top (clausesPreTop): the checks outside coreOK read no clause predicate"
NO_EXS = ('clauses without an existential variable or a right-side predicate (clausesNoExsTop): '
          'the checks outside coreOK read neither')
PRE_TOP_LIST = 'clauses whose predicate is not \\top (Semantics.clausesPreTop false; not a condition of coreOK:'
NO_EXS_LIST = ("clauses holding existential variables, each a match obligation (the package's match_named, "
               'Semantics.matchObligationsL; not a condition of wf: owed of each is MatchIndependent,')
NOT_NAMED = 'NOT named by matchObligationsL'
# the failing lists accepted, each with the conjuncts it holds
STATED = {f'wf false; failing: [{PRE_TOP}]': ('clausesPreTop',),
          f'wf false; failing: [{NO_EXS}]': ('clausesNoExsTop',),
          f'wf false; failing: [{PRE_TOP}, {NO_EXS}]': ('clausesPreTop', 'clausesNoExsTop')}


def exs_listed(lines):
    """The account's list of the clauses holding existential variables is printed, non-empty, and
    every clause of it is a match obligation."""
    for i, l in enumerate(lines):
        if l.startswith(NO_EXS_LIST):
            n = l.rsplit(': ', 1)[-1]
            if not n.isdigit() or int(n) == 0:
                return False
            rows = lines[i + 1:i + 1 + int(n)]
            return len(rows) == int(n) and all(
                r.startswith('      function ') and 'MatchIndependent open, existential Var' in r
                and NOT_NAMED not in r for r in rows)
    return False


def texts(args, corpus):
    out = []
    if corpus:
        d = os.path.join(K, '.lake/corpus/defs')
        out += sorted(os.path.join(d, f) for f in os.listdir(d)) if os.path.isdir(d) else []
    ex = os.path.join(K, 'f2-examples')
    out += sorted(os.path.join(ex, f) for f in os.listdir(ex) if f.endswith('.kore') and f != 'imp-programs.kore')
    for a in args:
        if os.path.isdir(a):
            for root, _, fs in os.walk(a):
                out += [os.path.join(root, f) for f in fs if f == 'definition.kore']
        else:
            out.append(a)
    return out


def verdict(path):
    r = subprocess.run(CAP + [EXE, 'account', path], capture_output=True, text=True)
    lines = r.stdout.split('\n')
    parse = next((l for l in lines if l.startswith('parse: ')), None)
    core = next((l for l in lines if l.startswith('coreOK: ')), '')
    # the account's own refusals (uninduced constructor axioms, laws of no collection, …)
    if 'refused by the account: 0' not in lines:
        parse = None
    which = STATED.get(parse[len('parse: ok; '):]) if parse and parse.startswith('parse: ok; ') else None
    checks = {'clausesPreTop': lambda: any(l.startswith(PRE_TOP_LIST) for l in lines),
              'clausesNoExsTop': lambda: exs_listed(lines)}
    stated = (which if which and core == 'coreOK: true; failing: []' and all(checks[w]() for w in which)
              else None)
    return path, parse, core, stated


def main():
    argv = sys.argv[1:]
    jobs = 4
    if argv[:1] == ['-j']:
        jobs, argv = int(argv[1]), argv[2:]
    corpus = '--no-corpus' not in argv
    argv = [a for a in argv if a != '--no-corpus']
    ts = texts(argv, corpus)
    with concurrent.futures.ThreadPoolExecutor(jobs) as ex:
        res = list(ex.map(verdict, ts))
    clean = [x for x in res if x[1] is not None]
    notwf = [x for x in clean if not x[1].startswith('parse: ok; wf true')]
    stated = [x for x in notwf if x[3]]
    bad = [x for x in notwf if not x[3]]
    for path, _, _, st in stated:
        print(f'stated: {os.path.relpath(path, K)}: {" and ".join(st)} alone, coreOK true, the clauses listed')
    for path, parse, core, _ in bad:
        print(f'{os.path.relpath(path, K)}: {parse[len("parse: ok; "):]}; {core}')
    print(f'{len(ts)} texts, {len(clean)} read with nothing refused, {len(notwf)} of them with wf false, '
          f'{len(stated)} of those stated (clausesPreTop, clausesNoExsTop or both, alone)')
    sys.exit(1 if bad else 0)


main()
