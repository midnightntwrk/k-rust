fn main() -> std::process::ExitCode {
    match kink_corpus::cli::execute(std::env::args_os().skip(1).collect()) {
        Ok(()) => std::process::ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("kink-corpus: {error}");
            std::process::ExitCode::FAILURE
        }
    }
}
