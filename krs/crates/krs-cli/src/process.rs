pub(crate) fn run(
    stage: &'static str,
    command: &mut std::process::Command,
) -> Result<std::process::Output, crate::CommandError> {
    let output = command
        .output()
        .map_err(|source| crate::CommandError::ProcessStart { stage, source })?;
    if output.status.success() {
        Ok(output)
    } else {
        Err(crate::CommandError::ProcessFailed {
            stage,
            status: output.status.code(),
            stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
        })
    }
}
