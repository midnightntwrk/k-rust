// Headless Firefox driver for the IR-15 gate over WebDriver BiDi (no
// geckodriver), as BL-001's run-firefox-evidence.mjs:
// /usr/lib/firefox/firefox --headless --new-instance with a fresh /var/tmp
// profile. No visible window is opened.
//
//   bun test/browser/run-firefox.ts [--site DIR] [--out DIR] [--port N]

import { main } from "./run-browser.ts";

await main("firefox", { port: "4325" });
