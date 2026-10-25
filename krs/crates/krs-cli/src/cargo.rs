use std::path::Path;
use std::process::Command;

pub(crate) fn command() -> Command {
    Command::new(std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into()))
}

/// [`command`] with Cargo's target directory set to `target` when one is given, overriding the
/// environment's and the configuration's.
pub(crate) fn command_in(target: Option<&Path>) -> Command {
    let mut command = command();
    if let Some(target) = target {
        command.env("CARGO_TARGET_DIR", target);
    }
    command
}
