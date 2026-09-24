// The static server every browser test page is served from: Bun.serve on
// 127.0.0.1 with `cache-control: no-store` and a request log. A site may hold
// an `assets` link to a directory outside it (the staged pack); only the site
// and that directory are served.
//
// Tests that need byte-level control of a response (the cache test's truncated
// transfers) keep their own node:http server; tests that must exercise the
// release host run browser/release/release.py serve, which applies hosting.toml.

import { realpathSync, statSync } from "node:fs";
import { extname, join, resolve } from "node:path";

const TYPES: Record<string, string> = {
  ".html": "text/html; charset=utf-8",
  ".js": "text/javascript; charset=utf-8",
  ".map": "application/json",
  ".json": "application/json",
  ".wasm": "application/wasm",
  ".rs": "text/plain; charset=utf-8",
  ".toml": "text/plain; charset=utf-8",
};

export interface RequestLogEntry {
  atMs: number;
  method: string;
  path: string;
  status: number;
  bytes: number;
}

export interface SiteServer {
  origin: string;
  log: RequestLogEntry[];
  stop(): void;
}

export function serveSite(dir: string, port: number): SiteServer {
  const root = realpathSync(dir);
  const log: RequestLogEntry[] = [];
  const started = performance.now();
  const server = Bun.serve({
    hostname: "127.0.0.1",
    port,
    fetch(request) {
      const url = new URL(request.url);
      let path = decodeURIComponent(url.pathname);
      if (path.endsWith("/")) path += "index.html";
      const target = resolve(root, `.${path}`);
      try {
        const real = realpathSync(target);
        if (!real.startsWith(`${root}/`) && !real.startsWith(`${realpathSync(join(root, "assets"))}/`)) throw new Error("outside");
        if (!statSync(real).isFile()) throw new Error("not a file");
        const body = Bun.file(real);
        log.push({ atMs: performance.now() - started, method: request.method, path, status: 200, bytes: body.size });
        return new Response(body, { headers: { "content-type": TYPES[extname(real)] ?? "application/octet-stream", "cache-control": "no-store" } });
      } catch {
        log.push({ atMs: performance.now() - started, method: request.method, path, status: 404, bytes: 0 });
        return new Response("not found", { status: 404 });
      }
    },
  });
  return { origin: `http://127.0.0.1:${port}`, log, stop: () => server.stop(true) };
}
