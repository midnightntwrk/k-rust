fn main() -> std::process::ExitCode {
    std::process::ExitCode::from(kink_flow::cli::execute(
        std::env::args_os().skip(1).collect(),
    ))
}
