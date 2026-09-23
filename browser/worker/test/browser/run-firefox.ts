// Headless Firefox driver for the worker gate over WebDriver BiDi (no
// geckodriver):
// /usr/lib/firefox/firefox --headless --new-instance with a fresh /var/tmp
// profile. No visible window is opened.
//
//   bun test/browser/run-firefox.ts [--site DIR] [--out DIR] [--port N]

import { main } from "./run-browser.ts";

await main("firefox", { port: "4325" });
