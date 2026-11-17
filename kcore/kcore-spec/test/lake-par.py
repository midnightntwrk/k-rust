#!/usr/bin/env python3
"""Build KcoreSpec modules in import order, several at a time, each `lake build +M` in its own
user systemd scope (MemoryMax=12G, no swap) with one Lean thread.

A module is started only when every KcoreSpec module it imports has finished, so two runs never
build the same module. Lake has no job limit of its own, which is why each run gets its own scope.

How many run at once is decided from the machine, not fixed. Each time a slot is considered, the
script reads MemAvailable and starts another run only if it leaves RESERVE GiB plus PEAK GiB per
run free. PEAK is the largest resident size seen so far, starting at 4 GiB. KCORE_JOBS sets an
upper bound if given.

The script first asks lake whether anything needs building (`lake build --no-build ROOTS`). If
nothing does, it exits at once.

Usage: test/lake-par.py [MODULE...] (default KcoreSpec). Exit 0: all built. Exit 1: a module failed;
its errors are printed and no new module is started.
"""
import os, re, subprocess, sys, time

K = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(K)
env = dict(os.environ, LEAN_NUM_THREADS="1")
SCOPE = ["systemd-run", "--user", "--scope", "-q", "-p", "MemoryMax=12G", "-p", "MemorySwapMax=0"]
RESERVE = float(os.environ.get("KCORE_RESERVE_GIB", "16"))
CAP = int(os.environ.get("KCORE_JOBS", "0")) or os.cpu_count()
roots = sys.argv[1:] or ["KcoreSpec"]

deps, order = {}, []
def visit(m):
    if m in deps: return
    p = m.replace(".", "/") + ".lean"
    deps[m] = []
    if not os.path.exists(p): return
    for line in open(p):
        r = re.match(r"import\s+(KcoreSpec\S*)", line)
        if r:
            deps[m].append(r.group(1)); visit(r.group(1))
    order.append(m)
for m in roots: visit(m)
mods = set(order)
deps = {m: [d for d in deps[m] if d in mods] for m in order}

t0 = time.time()
chk = subprocess.run(["timeout", "600"] + SCOPE + ["lake", "build", "--no-build"] + roots,
                     env=env, capture_output=True, text=True)
if chk.returncode == 0:
    print(f"all built (nothing to build, {time.time()-t0:.0f} s)"); sys.exit(0)

def avail_gib():
    for l in open("/proc/meminfo"):
        if l.startswith("MemAvailable:"): return int(l.split()[1]) / 1048576
    return 0.0

def mine_gib():
    # resident size of the lean processes building this tree (their command line names K)
    out = subprocess.run(["ps", "-o", "rss=,args=", "-C", "lean"], capture_output=True, text=True).stdout
    return sum(int(l.split(None, 1)[0]) for l in out.splitlines() if K in l) / 1048576

def phase1():
    # modules importing no KcoreSpec module pull the other packages (aml-port, kore-lean) in;
    # build those one at a time so no two runs compile the same dependency
    for m in [m for m in order if not deps[m]]:
        r = subprocess.run(["timeout", "3600"] + SCOPE + ["lake", "build", "+" + m], env=env,
                           capture_output=True, text=True)
        if r.returncode != 0:
            print(f"{m}: FAILED"); print("\n".join(l for l in (r.stdout + r.stderr).splitlines()
                                                     if "error" in l or "✖" in l)[:4000]); sys.exit(1)
    return {m for m in order if not deps[m]}

peak = 4.0
done, running, failed = phase1(), {}, None
pending = [m for m in order if m not in done]
while pending or running:
    for m, (p, ts, f) in list(running.items()):
        if p.poll() is None: continue
        del running[m]
        f.seek(0); log = f.read(); f.close()
        if p.returncode != 0:
            failed = failed or m
            print(f"{m}: FAILED ({time.time()-ts:.0f} s)")
            print("\n".join(l for l in log.splitlines() if "error" in l or "✖" in l)[:4000])
        else:
            done.add(m)
            if re.search(r"(Built|Building) " + re.escape(m) + r"\b", log):
                print(f"{m}: built ({time.time()-ts:.0f} s)", flush=True)
    if failed and not running: break
    if not failed:
        for m in list(pending):
            if len(running) >= CAP: break
            if not all(d in done for d in deps[m]): continue
            # charge every run of this script its expected peak until it exits: a run just
            # started has not grown yet, so MemAvailable alone would admit too many at once
            if avail_gib() + mine_gib() - peak * (len(running) + 1) < RESERVE: break
            f = open(f"/tmp/lake-par-{os.getpid()}-{len(done)}-{m}.log", "w+")
            p = subprocess.Popen(["timeout", "3600"] + SCOPE + ["lake", "build", "+" + m],
                                 env=env, stdout=f, stderr=subprocess.STDOUT)
            running[m] = (p, time.time(), f); pending.remove(m)
    # track the largest resident lean process seen, to size the next start
    try:
        out = subprocess.run(["ps", "-o", "rss=,args=", "-C", "lean"], capture_output=True, text=True).stdout
        top = max([int(l.split(None, 1)[0]) for l in out.splitlines() if K in l] or [0]) / 1048576
        peak = max(peak, min(top * 1.25, 12.0))
    except Exception:
        pass
    time.sleep(0.5)

if failed: sys.exit(1)
print(f"all built ({time.time()-t0:.0f} s, peak per module about {peak:.1f} GiB)")
