use std::{env, fs};

fn main() {
    let path = env::args().nth(1).expect("source path");
    let source = fs::read_to_string(path).expect("read source");
    let file = syn::parse_file(&source).expect("parse Rust file");
    println!("parsed {} top-level items", file.items.len());
}
