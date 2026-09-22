// Headless Chromium driver for the IR-15 gate (WebDriver through a ChromeDriver
// that drivers.ts starts), fresh profile, one page session running the plan.
//
//   bun test/browser/run-chromium.ts [--site DIR] [--out DIR] [--port N]

import { main } from "./run-browser.ts";

await main("chromium", { port: "4315" });
