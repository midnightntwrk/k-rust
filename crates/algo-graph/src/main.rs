use std::path::{Path, PathBuf};

use algo_graph::{
    Filters, build_graph, canonical_join_toml, canonical_toml, drift, join_files,
    render_composition, render_composition_focus, render_drift, render_module_map, render_pipeline,
    render_run_overlay, workspace_root, write_output, write_report,
};
use clap::{Args, Parser, Subcommand};

#[derive(Debug, Parser)]
#[command(about = "Build and render the k-rust algorithm graph")]
struct Cli {
    /// Repository root. Defaults to the nearest ancestor of the current directory whose
    /// Cargo.toml declares [workspace], else the workspace that built this binary.
    #[arg(long, global = true)]
    root: Option<PathBuf>,
    #[command(subcommand)]
    command: Command,
}

#[derive(Debug, Subcommand)]
enum Command {
    /// Write the canonical static graph as TOML.
    Graph {
        /// Destination path. Defaults to target/algo/graph.toml below the repository root.
        #[arg(short, long)]
        output: Option<PathBuf>,
    },
    /// Render a generated Mermaid projection.
    Render {
        #[command(subcommand)]
        command: RenderCommand,
    },
    /// Join a Chrome trace and receipt to a canonical static graph.
    Join(JoinArgs),
    /// Report cards whose site items changed while their fences did not.
    Drift(DriftArgs),
}

#[derive(Debug, Subcommand)]
enum RenderCommand {
    /// Render ordered phases and their contained algorithms.
    Pipeline(RenderArgs),
    /// Render algorithms, representations, relationships, and observations.
    Composition(CompositionArgs),
    /// Render the backend source-card inventory as Markdown.
    ModuleMap(OutputArgs),
}

#[derive(Debug, Args)]
struct OutputArgs {
    /// Destination path. Defaults below target/algo/ in the repository root.
    #[arg(short, long)]
    output: Option<PathBuf>,
}

#[derive(Debug, Args)]
struct RenderArgs {
    /// Keep algorithms in this dotted-id area. Repeat for more than one area.
    #[arg(long = "area")]
    areas: Vec<String>,
    /// Keep algorithms contained by this phase. Repeat for more than one phase.
    #[arg(long = "phase")]
    phases: Vec<String>,
    /// Keep algorithms measured by this counter variant or dotted counter name.
    #[arg(long = "counter")]
    counters: Vec<String>,
    /// Destination path. Defaults below target/algo/ in the repository root.
    #[arg(short, long)]
    output: Option<PathBuf>,
}

#[derive(Debug, Args)]
struct CompositionArgs {
    #[command(flatten)]
    render: RenderArgs,
    /// Render this algorithm and its downstream composition closure.
    #[arg(long)]
    focus: Option<String>,
}

#[derive(Debug, Args)]
struct JoinArgs {
    /// Canonical graph TOML produced by `algo-graph graph`.
    #[arg(long)]
    graph: PathBuf,
    /// Chrome trace-event JSON produced by `krust --trace`.
    #[arg(long)]
    trace: PathBuf,
    /// Receipt directory containing metadata, timings, and counters JSON.
    #[arg(long)]
    receipt: PathBuf,
    /// Machine-readable projection. Defaults to target/algo/join.toml.
    #[arg(short, long)]
    output: Option<PathBuf>,
    /// Run-overlay Mermaid. Defaults to target/algo/run-overlay.mmd.
    #[arg(long)]
    overlay: Option<PathBuf>,
}

#[derive(Debug, Args)]
struct DriftArgs {
    /// Revision from which to inspect changes.
    #[arg(long)]
    since: String,
    /// Revision at which to stop. Defaults to the index and working tree.
    #[arg(long)]
    until: Option<String>,
}

fn main() -> Result<(), algo_graph::Error> {
    let cli = Cli::parse();
    let root = cli.root.unwrap_or_else(workspace_root);

    match cli.command {
        Command::Graph { output } => {
            let build = report_build(build_graph(&root)?);
            eprintln!("{}", write_report(&root, &build)?);
            let output = output.unwrap_or_else(|| default_output(&root, "graph.toml"));
            write_output(&output, &canonical_toml(&build.graph)?)?;
            println!("wrote {}", output.display());
        }
        Command::Render { command } => match command {
            RenderCommand::Pipeline(arguments) => {
                let build = report_build(build_graph(&root)?);
                let output = arguments
                    .output
                    .clone()
                    .unwrap_or_else(|| default_output(&root, "pipeline.mmd"));
                write_output(
                    &output,
                    &render_pipeline(&build.graph, &arguments.filters()),
                )?;
                println!("wrote {}", output.display());
            }
            RenderCommand::Composition(arguments) => {
                let build = report_build(build_graph(&root)?);
                let output = arguments
                    .render
                    .output
                    .clone()
                    .unwrap_or_else(|| default_output(&root, "composition.mmd"));
                let filters = arguments.render.filters();
                let rendered = match arguments.focus.as_deref() {
                    None => render_composition(&build.graph, &filters),
                    Some(focus) => render_composition_focus(&build.graph, &filters, focus)?,
                };
                write_output(&output, &rendered)?;
                println!("wrote {}", output.display());
            }
            RenderCommand::ModuleMap(arguments) => {
                let build = report_build(build_graph(&root)?);
                let output = arguments
                    .output
                    .unwrap_or_else(|| default_output(&root, "module-map.md"));
                write_output(&output, &render_module_map(&build.graph))?;
                println!("wrote {}", output.display());
            }
        },
        Command::Join(arguments) => {
            let (graph, join) = join_files(
                &root,
                &arguments.graph,
                &arguments.trace,
                &arguments.receipt,
            )?;
            let output = arguments
                .output
                .unwrap_or_else(|| default_output(&root, "join.toml"));
            let overlay = arguments
                .overlay
                .unwrap_or_else(|| default_output(&root, "run-overlay.mmd"));
            write_output(&output, &canonical_join_toml(&join)?)?;
            write_output(&overlay, &render_run_overlay(&graph, &join))?;
            println!("wrote {}", output.display());
            println!("wrote {}", overlay.display());
        }
        Command::Drift(arguments) => {
            let report = drift(&root, &arguments.since, arguments.until.as_deref())?;
            print!("{}", render_drift(&report));
        }
    }
    Ok(())
}

fn report_build(build: algo_graph::Build) -> algo_graph::Build {
    for failure in &build.failures {
        eprintln!("freshness failure: {failure}");
    }
    for finding in &build.report {
        eprintln!("{finding}");
    }
    build
}

impl RenderArgs {
    fn filters(&self) -> Filters {
        Filters {
            areas: self.areas.clone(),
            phases: self.phases.clone(),
            counters: self.counters.clone(),
        }
    }
}

fn default_output(root: &Path, name: &str) -> PathBuf {
    root.join("target/algo").join(name)
}
