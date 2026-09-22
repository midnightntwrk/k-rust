// Known gap (silent miscompile): atomic read-modify-write and compare-exchange
// on 8- and 16-bit atomics load and store a full 32-bit word, clobbering the
// neighbouring bytes, and signed min/max compare without sign extension.
use std::hint::black_box;
use std::sync::atomic::{AtomicBool, AtomicI16, AtomicU16, AtomicU8, Ordering::SeqCst};

fn main() {
    let bytes = black_box([AtomicU8::new(1), AtomicU8::new(2), AtomicU8::new(3), AtomicU8::new(4)]);
    let old = bytes[0].swap(black_box(9), SeqCst);
    println!("u8 swap old={old} after={:?}", bytes.iter().map(|x| x.load(SeqCst)).collect::<Vec<_>>());
    let carry = black_box([AtomicU8::new(255), AtomicU8::new(7)]);
    carry[0].fetch_add(black_box(1), SeqCst);
    println!("u8 fetch_add after={:?}", carry.iter().map(|x| x.load(SeqCst)).collect::<Vec<_>>());
    let halves = black_box([AtomicU16::new(0xffff), AtomicU16::new(0x1234)]);
    halves[0].fetch_add(black_box(1), SeqCst);
    println!("u16 fetch_add after={:?}", halves.iter().map(|x| x.load(SeqCst)).collect::<Vec<_>>());
    let cas = black_box([AtomicU8::new(5), AtomicU8::new(6)]);
    let result = cas[0].compare_exchange(black_box(5), black_box(8), SeqCst, SeqCst);
    println!("u8 compare_exchange {result:?} after={:?}", cas.iter().map(|x| x.load(SeqCst)).collect::<Vec<_>>());
    let flags = black_box([AtomicBool::new(false), AtomicBool::new(true)]);
    let was = flags[0].swap(black_box(true), SeqCst);
    println!("bool swap was={was} after={:?}", flags.iter().map(|x| x.load(SeqCst)).collect::<Vec<_>>());
    let signed = black_box(AtomicI16::new(1000));
    signed.fetch_min(black_box(-7), SeqCst);
    println!("i16 fetch_min now={}", signed.load(SeqCst));
}
