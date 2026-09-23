// WASI process surface the collector relies on: argv, environ, an empty stdin,
// the current directory, and stdout/stderr ordering (byte-exact capture).
use std::io::{Read, Write};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    println!("args={args:?}");
    let mut vars: Vec<(String, String)> = std::env::vars().collect();
    vars.sort();
    println!("vars={vars:?}");
    println!("KRS_CASE={:?} MISSING={:?}", std::env::var("KRS_CASE"), std::env::var("MISSING").is_err());
    let mut input = Vec::new();
    println!("stdin={:?}", std::io::stdin().read_to_end(&mut input).map(|_| input.len()));
    println!("current_dir={:?}", std::env::current_dir().map(|path| path.display().to_string()));
    let mut stdout = std::io::stdout().lock();
    stdout.write_all(b"no trailing newline, then bytes: \x00\x01\xff").expect("write");
    stdout.flush().expect("flush");
    eprint!("stderr line 1\nstderr partial");
    std::process::exit(0);
}
