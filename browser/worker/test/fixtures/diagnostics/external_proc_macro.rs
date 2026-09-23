#[derive(serde::Serialize)]
pub struct ExternalProcMacro {
    value: u32,
}

fn main() {
    let _ = ExternalProcMacro { value: 7 };
}
