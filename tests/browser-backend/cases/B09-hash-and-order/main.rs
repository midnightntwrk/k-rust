// SHA-256 known-answer vectors (sha2 0.10.9 from the pack, as collect.rs
// hashes source identities), sort_unstable, and BTreeMap iteration order.
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::hint::black_box;

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn main() {
    for input in ["", "abc", "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"] {
        println!("sha256({input:?}) = {}", hex(&Sha256::digest(black_box(input).as_bytes())));
    }
    let mut hasher = Sha256::new();
    for _ in 0..1000 {
        hasher.update(black_box([b'a'; 1000]));
    }
    println!("sha256(10^6 x 'a') = {}", hex(&hasher.finalize()));
    // wrapping_mul: a checked i64 multiply at opt-level 0 needs smulhi.i64 (B17 known gap).
    let mut numbers: Vec<i64> = (0..64).map(|index: i64| (index.wrapping_mul(7919) + 13) % 101 - 50).collect();
    numbers.sort_unstable();
    println!("sort_unstable {numbers:?}");
    let mut words = vec!["pear", "apple", "Zebra", "zebra", "apple", "\u{e9}clair", "banana", ""];
    words.sort_unstable();
    println!("sort_unstable words {words:?}");
    let mut pairs: Vec<(u8, &str)> = vec![(2, "b"), (1, "z"), (2, "a"), (1, "a"), (0, "q")];
    pairs.sort_by_key(|pair| pair.0);
    println!("stable sort_by_key {pairs:?}");
    let mut map = BTreeMap::new();
    for (index, word) in ["delta", "alpha", "charlie", "bravo", "alpha"].into_iter().enumerate() {
        *map.entry(word).or_insert(0) += index;
    }
    println!("btreemap {map:?}");
    let set: BTreeSet<i32> = [5, -3, 9, 0, -3, 12].into_iter().collect();
    println!("btreeset {set:?} range {:?}", set.range(0..10).collect::<Vec<_>>());
}
