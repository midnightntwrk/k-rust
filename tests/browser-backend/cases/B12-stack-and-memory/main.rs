// Stack exhaustion and allocation failure: the host must report a trap or an
// allocation failure, never crash. The class is compared, not the engine text.
use std::hint::black_box;

#[inline(never)]
fn shadow_stack(depth: u64) -> u64 {
    // 4 KiB of the shadow stack (linear memory) per frame.
    let mut frame = [0_u8; 4096];
    frame[(depth % 4096) as usize] = depth as u8;
    black_box(&mut frame);
    if black_box(depth) == u64::MAX {
        return 0;
    }
    shadow_stack(depth + 1).wrapping_add(u64::from(frame[0]))
}

#[inline(never)]
fn native_stack(depth: u64) -> u64 {
    // Few locals: the engine's own call stack is exhausted first.
    if black_box(depth) == u64::MAX {
        return 0;
    }
    native_stack(depth + 1).wrapping_add(1)
}

fn main() {
    let mode = std::env::args().nth(1).unwrap_or_default();
    println!("mode={mode}");
    match mode.as_str() {
        "shadow-stack" => println!("{}", shadow_stack(0)),
        "native-stack" => println!("{}", native_stack(0)),
        "alloc" => {
            // 3 x 1.75 GiB exceeds the 4 GiB wasm32 address space whatever the host
            // limit. Hosts differ in which block fails, so nothing is printed per block.
            let mut blocks: Vec<Vec<u8>> = Vec::new();
            for _ in 0..3 {
                let block: Vec<u8> = Vec::with_capacity(black_box(0x7000_0000));
                blocks.push(black_box(block));
            }
            println!("allocated {} blocks", blocks.len());
        }
        "capacity-overflow" => {
            let block: Vec<u8> = Vec::with_capacity(black_box(usize::MAX));
            println!("{}", block.capacity());
        }
        _ => println!("no failure requested"),
    }
    println!("after {mode}");
}
