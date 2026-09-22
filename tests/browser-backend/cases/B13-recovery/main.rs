// Recovery control (BL-003 COLLECTOR_MODE=spin; BL-009 cancel_recovery): the
// suite runs this case after every other case in the same host session. Its
// `spin` run is cancelled by the host; the case is then recompiled and rerun.
use std::collections::BTreeMap;
use std::hint::black_box;

fn main() {
    if std::env::var("COLLECTOR_MODE").as_deref() == Ok("spin") {
        println!("spinning");
        loop {
            std::hint::spin_loop();
        }
    }
    let mut counts = BTreeMap::new();
    for word in black_box("a trapped or cancelled build must not poison the next build").split(' ') {
        *counts.entry(word.len()).or_insert(0_u32) += 1;
    }
    let checksum = counts.iter().fold(0x811c_9dc5_u32, |hash, (length, count)| (hash ^ (*length as u32 * 31 + count)).wrapping_mul(0x0100_0193));
    println!("recovered counts={counts:?} checksum={checksum:#010x}");
}
