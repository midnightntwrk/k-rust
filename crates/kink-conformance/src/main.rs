use kink_conformance::{Invocation, run};
use std::process::ExitCode;

fn main() -> ExitCode {
    let invocation = match Invocation::parse(std::env::args_os().skip(1)) {
        Ok(invocation) => invocation,
        Err(failure) => {
            eprintln!("{failure}");
            return ExitCode::from(failure.kind().exit_code());
        }
    };
    match run(&invocation) {
        Ok(output) => {
            println!("{output}");
            ExitCode::SUCCESS
        }
        Err(failure) => {
            eprintln!("{failure}");
            ExitCode::from(failure.kind().exit_code())
        }
    }
}
