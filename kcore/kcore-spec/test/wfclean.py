"""No text is read clean with `wf` false and no stated reading of what `wf` rejects: `kcore account`
on each text, which ends, when the reader refuses nothing, with `parse: ok; wf B; failing: [...]`,
`coreOK: B; failing: [...]` and `refused by the account: N`. A text the reader reads with nothing
refused is either well formed or names the failing conjunct; this check fails on every such text
whose `wf` is false, unless the account states the construct `wf` rejects and the route around it:
otherwise the reader read the text with no stated reading of that construct, or `wf` rejects a
reading it should admit.

One construct is so stated: a clause whose predicate is not `\top` (the conjunct `clausesPreTop`).
`wf`'s consumers derive `FnHyp` from the named facts and decide totality and termination reading
no clause predicate, and where a predicate is not `\top` the named facts do not give `FnHyp`
(test/FnSolvesDet.lean); `coreOK` does not ask it, and the account lists those clauses and says
that the `--core` package's statements take `FnHyp` itself. A text read clean whose only failing
conjunct is `clausesPreTop`, with `coreOK` true and that list printed, meets layer 1 (i) of C14
(designs/DONE-0: `coreOK` with the failing `wf` conjunct named); it is listed as stated, not as a
failure.

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
# the failing list of a text whose only failing `wf` conjunct is `clausesPreTop`, and the account's
# line that lists its clauses whose predicate is not `\top`
PRE_TOP_ONLY = "wf false; failing: [clauses' premise predicates \\top (clausesPreTop): the checks outside coreOK read no clause predicate]"
PRE_TOP_LIST = 'clauses whose predicate is not \\top (Semantics.clausesPreTop false; not a condition of coreOK:'


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
    stated = (parse == 'parse: ok; ' + PRE_TOP_ONLY and core == 'coreOK: true; failing: []'
              and any(l.startswith(PRE_TOP_LIST) for l in lines))
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
    for path, _, _, _ in stated:
        print(f'stated: {os.path.relpath(path, K)}: clausesPreTop alone, coreOK true, the clauses listed')
    for path, parse, core, _ in bad:
        print(f'{os.path.relpath(path, K)}: {parse[len("parse: ok; "):]}; {core}')
    print(f'{len(ts)} texts, {len(clean)} read with nothing refused, {len(notwf)} of them with wf false, '
          f'{len(stated)} of those stated (clausesPreTop alone)')
    sys.exit(1 if bad else 0)


main()
