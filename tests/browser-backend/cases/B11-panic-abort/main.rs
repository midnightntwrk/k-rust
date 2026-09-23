// panic!, unreachable!, and process::exit under panic=abort (BL-003
// COLLECTOR_MODE=trap). A panic prints its message on stderr and aborts, which
// the host reports as a trap; exit(3) is an ordinary exit status.
use std::hint::black_box;

fn main() {
    let mode = std::env::args().nth(1).unwrap_or_default();
    println!("mode={mode}");
    match mode.as_str() {
        "panic" => panic!("deliberate B11 panic: {}", black_box(42)),
        "unreachable" => unreachable!("deliberate B11 unreachable"),
        "unwrap-none" => {
            let value: Option<u8> = black_box(None);
            println!("{}", value.unwrap());
        }
        "index" => {
            let values = black_box(vec![1_u8, 2, 3]);
            println!("{}", values[black_box(7)]);
        }
        "overflow" => {
            // Overflow checks follow debug assertions: on at opt-level 0, off at 2.
            let value = black_box(u8::MAX);
            println!("wrapped={}", value + black_box(1));
        }
        "exit3" => {
            eprintln!("exiting with status 3");
            std::process::exit(3);
        }
        _ => println!("no failure requested"),
    }
    println!("after {mode}");
}
