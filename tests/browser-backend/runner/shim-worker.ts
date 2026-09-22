// Browser executor worker: holds rustc.wasm (a compiled Module sent by the
// page), the sysroot, and the pack, and runs one step per message under the
// vendored browser_wasi_shim (ShimSession).

import { ShimSession } from "./shim-session.ts";
import type { WorkerReply, WorkerRequest } from "./worker-client.ts";

interface ShimInit {
  rustc: WebAssembly.Module;
  bundle: Uint8Array;
  pack: Record<string, Uint8Array>;
  sysrootMount: string;
}

const scope = self as unknown as { onmessage: ((event: MessageEvent<WorkerRequest>) => void) | null; postMessage(message: WorkerReply): void };
let session: ShimSession | null = null;
let queue: Promise<void> = Promise.resolve();

scope.onmessage = (event) => {
  const message = event.data;
  queue = queue.then(async () => {
    try {
      if (message.type === "init") {
        const init = message.init as ShimInit;
        session = new ShimSession(init.rustc, init.bundle, init.pack, init.sysrootMount);
        scope.postMessage({ type: "ready" });
      } else if (message.type === "rustc") {
        scope.postMessage({ type: "result", id: message.id, result: await session!.rustc(message.request) });
      } else {
        scope.postMessage({ type: "result", id: message.id, result: await session!.run(message.request) });
      }
    } catch (error) {
      const id = message.type === "init" ? null : message.id;
      scope.postMessage({ type: "error", id, message: String(error instanceof Error ? `${error.name}: ${error.message}` : error) });
    }
  });
};
