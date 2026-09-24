// Memory sampling of a browser process tree through /proc (Linux).

import { readdirSync, readFileSync } from "node:fs";

interface ProcStatus {
  pid: number;
  ppid: number;
  name: string | null;
  rssKb: number;
}

function procStatus(pid: number): ProcStatus | null {
  try {
    const text = readFileSync(`/proc/${pid}/status`, "utf8");
    const field = (name: string) => new RegExp(`^${name}:\\s+(.+)$`, "m").exec(text)?.[1] ?? null;
    return { pid, ppid: Number(field("PPid")), name: field("Name"), rssKb: Number(/^\d+/.exec(field("VmRSS") ?? "0")?.[0] ?? 0) };
  } catch {
    return null;
  }
}

function tree(rootPid: number): ProcStatus[] {
  const all = readdirSync("/proc").filter((n) => /^\d+$/.test(n)).map((n) => procStatus(Number(n))).filter((s): s is ProcStatus => s !== null);
  const selected = new Set([rootPid]);
  let changed = true;
  while (changed) {
    changed = false;
    for (const s of all) if (!selected.has(s.pid) && selected.has(s.ppid)) { selected.add(s.pid); changed = true; }
  }
  return all.filter((s) => selected.has(s.pid));
}

function pssKb(pid: number): number {
  try {
    return Number(/^Pss:\s+(\d+) kB$/m.exec(readFileSync(`/proc/${pid}/smaps_rollup`, "utf8"))?.[1] ?? 0);
  } catch {
    return 0;
  }
}

export interface MemoryPoint {
  atMs: number;
  phase: string;
  processes: number;
  rssKb: number;
  pssKb: number;
  top: Array<{ pid: number; name: string | null; pssKb: number }>;
}

export class TreeSampler {
  phase = "setup";
  samples: MemoryPoint[] = [];
  private timer: ReturnType<typeof setInterval> | null = null;
  private readonly started = performance.now();
  private intervalMs = 100;
  constructor(private readonly rootPid: () => number | null) {}
  start(intervalMs = 100) {
    this.intervalMs = intervalMs;
    this.timer = setInterval(() => {
      const pid = this.rootPid();
      if (pid === null) return;
      const procs = tree(pid).map((p) => ({ ...p, pssKb: pssKb(p.pid) }));
      this.samples.push({
        atMs: performance.now() - this.started,
        phase: this.phase,
        processes: procs.length,
        rssKb: procs.reduce((s, p) => s + p.rssKb, 0),
        pssKb: procs.reduce((s, p) => s + p.pssKb, 0),
        top: procs.sort((a, b) => b.pssKb - a.pssKb).slice(0, 3).map(({ pid, name, pssKb }) => ({ pid, name, pssKb })),
      });
    }, intervalMs);
  }
  stop() {
    if (this.timer) clearInterval(this.timer);
  }
  summary() {
    const peak = (field: "pssKb" | "rssKb") => this.samples.reduce<MemoryPoint | null>((best, s) => (best === null || s[field] > best[field] ? s : best), null);
    const byPhase: Record<string, { peakPssKb: number; peakRssKb: number; samples: number }> = {};
    for (const s of this.samples) {
      const p = (byPhase[s.phase] ??= { peakPssKb: 0, peakRssKb: 0, samples: 0 });
      p.peakPssKb = Math.max(p.peakPssKb, s.pssKb);
      p.peakRssKb = Math.max(p.peakRssKb, s.rssKb);
      p.samples += 1;
    }
    return {
      method: `${this.intervalMs} ms samples of /proc/<pid>/smaps_rollup Pss and VmRSS over the browser process tree; RSS double-counts shared pages`,
      sampleCount: this.samples.length,
      peakPss: peak("pssKb"),
      peakRss: peak("rssKb"),
      byPhase,
    };
  }
}
