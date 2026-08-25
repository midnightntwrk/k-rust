// This file is deliberately not a Rust module. The negative collector mutates
// only the initializer's display filename to point here while retaining the
// exact line/column anchors from lib.rs. The leading padding makes those
// anchors stale, proving split-file provenance cannot silently select a
// different source revision.















impl Machine {
    #[k::init]
    pub fn init() -> Self {
        Self {
            k: k::configuration::KCell::new(k::k![Bar]),
        }
    }
}

// Padding keeps every retained lib.rs coordinate in bounds. The collector
// must therefore diagnose semantic staleness, not merely a short file.
// 01
// 02 deliberately long enough for every retained Unicode-scalar column................
// 03 deliberately long enough for every retained Unicode-scalar column................
// 04 deliberately long enough for every retained Unicode-scalar column................
// 05 deliberately long enough for every retained Unicode-scalar column................
// 06 deliberately long enough for every retained Unicode-scalar column................
// 07 deliberately long enough for every retained Unicode-scalar column................
// 08
// 09
// 10
// 11
// 12
// 13
// 14
// 15
// 16
// 17
// 18
// 19
// 20
