#!/usr/bin/env python3
"""Build KcoreSpec modules in import order, several at a time, each `lake build +M` in its own
user systemd scope (MemoryMax=12G, no swap) with one Lean thread.

A module is started only when every KcoreSpec module it imports has finished, so two runs never
build the same module. Lake has no job limit of its own, which is why each run gets its own scope.

How many run at once is decided from the machine, not fixed. Each time a slot is considered, the
script reads MemAvailable and starts another run only if it leaves RESERVE GiB free beyond the
module's own expected peak, after charging every running lean process the room it has left to grow, up to the peak
recorded for its source file (shared table, see PEAKS). KCORE_JOBS sets an
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

# The largest resident size seen of each source file's lean run, shared by every tree of this user
# (~/.cache/kcore-lake-peaks.json; keyed by the path below kcore-spec, e.g. KcoreSpec/Step.lean or
# test/Pins.lean). Every run of this script samples all lean processes and records what it sees, so
# the table also learns the test files other agents run by hand. A run is charged the room it has
# left to grow: up to its file's known peak (with a margin), or up to a default when its file was
# never seen. Charging every run the worst case instead admitted too few runs machine-wide.
PEAKS = os.path.expanduser("~/.cache/kcore-lake-peaks.json")
DEFAULT_TEST, DEFAULT_MOD = 9.0, 6.0   # GiB, for a file never seen: a test file can reach 9-10
known, seen, last_save = {}, {}, 0.0
try:
    import json; known = json.load(open(PEAKS))
except Exception:
    known = {}

def lean_procs():
    # (rss GiB, key, args) of every lean process on the machine
    out = subprocess.run(["ps", "-o", "rss=,args=", "-C", "lean"], capture_output=True, text=True).stdout
    res = []
    for l in out.splitlines():
        rss, args = l.split(None, 1)
        src = next((a for a in args.split() if a.endswith(".lean")), "")
        key = src.split("/kcore-spec/", 1)[1] if "/kcore-spec/" in src else src
        res.append((int(rss) / 1048576, key, args))
    return res

def est_gib(key):
    if key in known: return min(12.0, known[key] * 1.15)
    return DEFAULT_MOD if key.startswith("KcoreSpec/") else DEFAULT_TEST

def save_peaks():
    global known
    try:
        import json
        try: cur = json.load(open(PEAKS))
        except Exception: cur = {}
        for k, v in seen.items(): cur[k] = max(cur.get(k, 0.0), round(v, 2))
        os.makedirs(os.path.dirname(PEAKS), exist_ok=True)
        tmp = f"{PEAKS}.{os.getpid()}"; json.dump(cur, open(tmp, "w"), indent=0, sort_keys=True); os.replace(tmp, PEAKS)
        known = cur
    except Exception:
        pass

def committed_gib():
    # the room every running lean process (this tree's and the others') has left to grow
    return sum(max(0.0, max(est_gib(k), rss) - rss) for rss, k, _ in lean_procs())

HERE = os.getcwd().rstrip("/") + "/"

def started_all():
    # every module this run launched has its lean process on the machine (or has finished)
    vis = {a for _, _, args in lean_procs() for a in args.split() if a.endswith(".lean")}
    return all(p.poll() is not None or
               any(v.startswith(HERE) and v.endswith("/" + m.replace(".", "/") + ".lean") for v in vis)
               for m, (p, _, _) in running.items())

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
            # a module launched but whose lean process has not appeared yet is in no one's
            # committed_gib (this run's or another tree's), so admitting more now would charge
            # nothing for it: wait until every running module of this tree is visible
            if not started_all(): break
            # a run just started has not grown yet, so MemAvailable alone would admit too many at
            # once: charge every running lean process the room it has left, and this module its peak
            if avail_gib() - committed_gib() - est_gib(m.replace(".", "/") + ".lean") < RESERVE: break
            f = open(f"/tmp/lake-par-{os.getpid()}-{len(done)}-{m}.log", "w+")
            p = subprocess.Popen(["timeout", "3600"] + SCOPE + ["lake", "build", "+" + m],
                                 env=env, stdout=f, stderr=subprocess.STDOUT)
            running[m] = (p, time.time(), f); pending.remove(m)
    # record the largest resident size seen of each lean run, here and in other trees
    try:
        for rss, k, _ in lean_procs():
            if k: seen[k] = max(seen.get(k, 0.0), rss)
        if time.time() - last_save > 30: save_peaks(); last_save = time.time()
    except Exception:
        pass
    time.sleep(0.5)

save_peaks()
if failed: sys.exit(1)
print(f"all built ({time.time()-t0:.0f} s)")
