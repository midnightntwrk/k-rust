//! One `krust fuzz` campaign per call: the definition sources and the campaign specification in,
//! the canonical `krust-fuzz-report` JSON out (`k_rust_fuzz`, whose README documents the
//! campaign and the report).
//!
//! The addon's calls are synchronous, so a campaign runs to its end inside one call; a stepwise
//! API would hold the campaign's backends across calls for nothing. The specification is read
//! by [`crate::campaign`], the file `k-rust-wasm` declares and tests against the library. This
//! module compiles the definitions from in-memory sources, on krun's route, and runs the
//! compilation and the campaign on a thread of its own ([`CAMPAIGN_STACK_SIZE`]).

use k_rust::{
    builtin::embedded,
    kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
    outer::{LoadOptions, ResolvedSource, load_for_compilation},
};
use k_rust_fuzz::CompiledDefinition;
use napi::{Error, Result};
use napi_derive::napi;

use crate::{
    NativeSource, VirtualResolver,
    campaign::{CampaignJson, build_identity},
    compile_error,
};

/// The stack of the thread every campaign runs on: 256 MiB, as the `krust-fuzz` executable's.
///
/// The backend stops a step for lack of stack from the stack that remains, so a case's outcome
/// can depend on the thread (ARCHITECTURE 5.4). Running on a thread of fixed size, rather than
/// on Node's main thread or a worker of whatever size, makes the outcome independent of where
/// JavaScript calls from, and the report records the size as its `thread-stack-size`. The
/// address space is reserved when the thread starts; pages become resident only as recursion
/// touches them.
pub const CAMPAIGN_STACK_SIZE: usize = 256 << 20;

/// One definition's sources, loaded and compiled for the Rust backend as `krust kcompile` does.
#[napi(object)]
pub struct NativeFuzzDefinition {
    pub definition: String,
    pub module_name: String,
    /// The module whose grammar parses the program; selected as `kcompile` does when absent.
    pub syntax_module: Option<String>,
    pub source_name: Option<String>,
    pub sources: Option<Vec<NativeSource>>,
    pub markdown_selector: Option<String>,
    pub include_prelude: Option<bool>,
}

#[napi(object)]
pub struct NativeFuzzCampaignOptions {
    pub definition: String,
    pub module_name: String,
    pub syntax_module: Option<String>,
    pub source_name: Option<String>,
    pub sources: Option<Vec<NativeSource>>,
    pub markdown_selector: Option<String>,
    pub include_prelude: Option<bool>,
    /// The mutant of a differential target.
    pub mutant: Option<NativeFuzzDefinition>,
    /// The campaign specification as JSON, in the fuzz library's kebab-case fields.
    pub campaign: String,
}

/// Run one `krust fuzz` campaign on in-memory definitions and return its report's canonical
/// JSON. The compilation and the campaign run on a thread with a [`CAMPAIGN_STACK_SIZE`] stack,
/// which this call waits for; a panic there is thrown as an error instead of aborting the
/// process. A campaign that runs returns its report, whatever its outcome; a malformed
/// specification, a definition that does not compile, and every refusal of `Campaign::new`
/// throw.
#[napi]
pub fn run_fuzz_campaign_native(options: NativeFuzzCampaignOptions) -> Result<String> {
    let thread = std::thread::Builder::new()
        .name("k-rust-fuzz-campaign".to_owned())
        .stack_size(CAMPAIGN_STACK_SIZE)
        .spawn(move || run(options))
        .map_err(|error| {
            Error::from_reason(format!("the campaign thread did not start: {error}"))
        })?;
    match thread.join() {
        Ok(result) => result.map_err(Error::from_reason),
        Err(panic) => {
            let message = panic
                .downcast_ref::<&str>()
                .map(|message| (*message).to_owned())
                .or_else(|| panic.downcast_ref::<String>().cloned())
                .unwrap_or_else(|| "a panic without a message".to_owned());
            Err(Error::from_reason(format!(
                "the fuzz campaign panicked, which is a k-rust defect: {message}"
            )))
        }
    }
}

/// The campaign of one call, on the campaign thread.
fn run(options: NativeFuzzCampaignOptions) -> std::result::Result<String, String> {
    let campaign: CampaignJson =
        serde_json::from_str(&options.campaign).map_err(|error| format!("campaign: {error}"))?;
    let mut campaign = campaign.parts(&build_identity(
        env!("CARGO_PKG_NAME"),
        env!("CARGO_PKG_VERSION"),
    ))?;
    if campaign.identity.thread_stack_size.is_some() {
        return Err(format!(
            "campaign.identity.thread-stack-size: the campaign runs on a thread of this binding \
             with a {CAMPAIGN_STACK_SIZE}-byte stack, and the report records that size; leave \
             the field out"
        ));
    }
    campaign.identity.thread_stack_size = Some(CAMPAIGN_STACK_SIZE as u64);
    let baseline = compile(NativeFuzzDefinition {
        definition: options.definition,
        module_name: options.module_name,
        syntax_module: options.syntax_module,
        source_name: options.source_name,
        sources: options.sources,
        markdown_selector: options.markdown_selector,
        include_prelude: options.include_prelude,
    })?;
    let mutant = options.mutant.map(compile).transpose()?;
    campaign.run(baseline, mutant)
}

/// Load and compile one definition for the Rust backend, as `krust kcompile` does, and keep
/// what a campaign reads from it, on krun's route.
fn compile(options: NativeFuzzDefinition) -> std::result::Result<CompiledDefinition, String> {
    let source_name = options
        .source_name
        .unwrap_or_else(|| "definition.k".to_owned());
    let mut resolver = VirtualResolver::new(options.sources.unwrap_or_default());
    let implicit_sources = if options.include_prelude.unwrap_or(true) {
        vec![embedded("prelude.md").ok_or("embedded prelude is unavailable")?]
    } else {
        Vec::new()
    };
    let load_options = LoadOptions {
        markdown_selector: options.markdown_selector.unwrap_or_else(|| "k".to_owned()),
        implicit_sources,
        ..CompilationBackend::Rust.load_options()
    };
    let (loaded, syntax_module) = load_for_compilation(
        ResolvedSource::new(source_name, options.definition),
        options.module_name.as_str(),
        options.syntax_module.as_deref(),
        &mut resolver,
        &load_options,
    )
    .map_err(|error| error.to_string())?;
    let artifacts = compile_loaded_definition(&loaded, CompileOptions::default())
        .map_err(|error| compile_error(error).reason.clone())?;
    CompiledDefinition::from_artifacts(
        options.module_name,
        syntax_module,
        loaded.into_definition(),
        artifacts,
    )
    .map_err(|error| error.to_string())
}
