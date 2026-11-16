"""No text is read clean with `wf` false: `kcore account` on each text, which ends, when the reader
refuses nothing, with `parse: ok; wf B; failing: [...]`, `coreOK: B; failing: [...]` and
`refused by the account: N`. A text the reader reads with nothing refused is either well formed or names the failing
conjunct; this check fails on every such text whose `wf` is false: the reader then read the text
with no stated reading of the construct `wf` rejects, or `wf` rejects a reading it should admit.

The texts: the corpus's extracted ones (`.lake/corpus/defs`, `test/corpus.py` extracts them), the
f2-examples' `.kore` files, and the files and directories given (a directory: every
`definition.kore` below it). One line per text read clean with `wf` false, its failing conjuncts;
then the counts. Each `kcore account` under a 12 GiB memory scope, JOBS at once.

Usage (from kcore-spec, `kcore` built): python3 -I test/wfclean.py [-j JOBS] [--no-corpus] [PATH...]
Exit 1 when some text is read clean with `wf` false."""
import concurrent.futures, os, subprocess, sys

K = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CAP = ['systemd-run', '--user', '--scope', '-q', '-p', 'MemoryMax=12G', '-p', 'MemorySwapMax=0', 'timeout', '300']
EXE = os.path.join(K, '.lake/build/bin/kcore')


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
    return path, parse, core


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
    bad = [x for x in clean if not x[1].startswith('parse: ok; wf true')]
    for path, parse, core in bad:
        print(f'{os.path.relpath(path, K)}: {parse[len("parse: ok; "):]}; {core}')
    print(f'{len(ts)} texts, {len(clean)} read with nothing refused, {len(bad)} of them with wf false')
    sys.exit(1 if bad else 0)


main()
