use std::{
    path::{Path, PathBuf},
    process::ExitCode,
};

use algo_graph::{
    Filters, build_graph, canonical_coverage_toml, canonical_join_toml, canonical_toml, drift,
    join_files, normalize_export,
    query::{self, Answer, HotOrder, NotFound},
    render_composition, render_composition_focus, render_drift, render_html, render_module_map,
    render_pipeline, render_run_overlay, workspace_root, write_output, write_report,
};
use clap::{Args, Parser, Subcommand, ValueEnum};

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
        /// Destination path. Defaults to target/algo/graph.toml below the repository root, in which
        /// case the advisory report is also written to target/algo/report.txt.
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
    /// Reduce an `llvm-cov export` JSON document to the canonical coverage.toml the join reads.
    ///
    /// Keeps the functions of workspace sources (`crates/*/src/**`) with their workspace-relative
    /// file, first and last line, demangled name without crate hashes and generic arguments, and
    /// entry count; the instantiations of a generic function are summed. Each file's SHA-256 is
    /// recorded so that the join can check that its checkout holds the covered sources.
    Coverage(CoverageArgs),
    /// Report cards whose site items changed while their fences did not.
    Drift(DriftArgs),
    /// Ask the algorithm graph a question: who owns this code, what does a change affect, where did a run spend time.
    #[command(long_about = QUERY_ABOUT, after_help = QUERY_AFTER)]
    Query(QueryArgs),
}

const QUERY_ABOUT: &str = "\
Ask the k-rust algorithm graph a question and print a compact answer.

The graph is generated from `algorithm` cards: TOML fences in the //! head of each algorithm's
home module (docs/algorithm-cards.md). A card names the algorithm id (such as
backend.matching.syntactic), its sites (functions and methods that implement it), its cost
bounds and cost variable, its counters (crates/k-rust-kore/src/measure.rs Counter), its span
policy, and its relations: produces and consumes (representation types), constrains, falls back
to, and variant of. Phases come from the kompile stage table, which also gives phase order.

Every relation carries a provenance: declared (written on a card), table (read from a registry),
or derived (computed by the tool). An absent relation proves nothing: there is no call graph, and
a helper that no card lists as a site is not attributed to any algorithm.

The graph is rebuilt from the current checkout on every call (about one second), so answers match
the code you see. Every answer line ends with `file::symbol` so the code can be opened next.
Build failures, if any, go to standard error; standard output holds only the answer.
Exit status 2 means an unknown id, path, or area; the error names the three nearest candidates.";

const QUERY_AFTER: &str = "\
Which subcommand:
  editing a file or function            owner crates/k-rust-backend/src/matching/mod.rs::Matcher::run
  what an algorithm is and relates to   show backend.matching.syntactic
  what to recheck after a change        impact kompile.sentences.number
  where a profiled run spent time       hot --join <join.toml>
  what a run never touched              unexercised --join <join.toml> --area backend
  finding an id from words              search sort projection";

#[derive(Debug, Args)]
struct QueryArgs {
    /// Read this saved graph TOML (from `algo-graph graph`) instead of rebuilding from the checkout.
    #[arg(long, global = true, value_name = "graph.toml")]
    graph: Option<PathBuf>,
    /// Output format: plain text for reading, or TOML with the same content for parsing.
    #[arg(long, global = true, value_enum, default_value_t = Format::Text)]
    format: Format,
    #[command(subcommand)]
    command: QueryCommand,
}

#[derive(Clone, Copy, Debug, ValueEnum)]
enum Format {
    Text,
    Toml,
}

#[derive(Debug, Subcommand)]
enum QueryCommand {
    /// Which algorithms own a file, directory, or symbol, with their card, counters, tests, and span policy.
    ///
    /// Use this before editing code: it names the algorithm cards whose sites are in the file
    /// (or at the symbol), where each card lives, which counters measure each algorithm, the
    /// tests its card lists, and its span policy. It also lists representation types defined
    /// there with the algorithms that produce and consume them.
    ///
    /// TARGET is a path relative to the repository root or absolute, optionally followed by
    /// `::symbol` (`Type::method`, `function`, or just `Type`); a directory lists every owner
    /// below it. A TARGET without `/` or `.rs` is a symbol looked up in every file. A symbol that
    /// no card names as a site falls back to the owners of its file, with a note.
    #[command(after_help = "\
Examples:
  algo-graph query owner crates/k-rust-backend/src/matching/mod.rs
  algo-graph query owner crates/k-rust-backend/src/matching/mod.rs::Matcher::run
  algo-graph query owner crates/k-rust/src/kompile/
  algo-graph query owner generate_sort_projections")]
    Owner {
        /// `path`, `path::symbol`, or `symbol`.
        target: String,
    },
    /// One node as a block: an algorithm's card, or a counter, phase, representation, or contract.
    ///
    /// For an algorithm: name, card location, sites, every cost mode with its bound, the cost
    /// variable, counters, tests, span policy, and every relation with its provenance, including
    /// the derived `feeds` / `fed by` relations through shared representations and the phases
    /// that contain it. ID is a dotted algorithm id, an `Algorithm::` variant name, a counter
    /// variant or dotted counter name (shows which algorithms it measures), a phase name, a
    /// representation id, or a contract id.
    #[command(after_help = "\
Examples:
  algo-graph query show backend.matching.syntactic
  algo-graph query show matching.pairs
  algo-graph query show 'number sentences'")]
    Show {
        /// Node id, variant name, or dotted counter name.
        id: String,
    },
    /// What a change to an algorithm (or representation, phase, contract) can affect: reached algorithms with paths, counters, tests.
    ///
    /// Computes the downstream closure and prints each reached algorithm or contract with the path
    /// that reached it, in two classes:
    ///
    /// card relations: produces -> consumed-by through one representation (same type and role),
    /// declared constrains (producer to consumer), and falls-back-to and variant-of read
    /// backwards (a change to the fallback or the general algorithm changes the caller or the
    /// specialised copy);
    ///
    /// stage order only: the phases after a phase that contains the algorithm, and the
    /// algorithms those phases contain (derived contains, table phase order). This is weaker
    /// evidence: a later phase reads what earlier phases rewrote, but may not depend on this one.
    ///
    /// Then the counters to re-measure and the tests to rerun. `measured-by` is listed, never
    /// followed. An absent relation proves nothing; direct callers are not listed unless a card
    /// declares a relation.
    #[command(after_help = "\
Examples:
  algo-graph query impact kompile.sentences.number
  algo-graph query impact 'k_rust::definition::Definition [lowered source]'")]
    Impact {
        /// Algorithm id, contract id, representation id (`type [role]`), or phase name.
        id: String,
    },
    /// Where a profiled run spent time: top algorithms by self or total seconds or count, with counters and cost bounds.
    ///
    /// Reads a join (`algo-graph join` output: one run's trace and receipt projected on the graph).
    /// Prints the run's workload, claim, and commit, then for each algorithm: invocation count,
    /// self seconds (excluding nested algorithm spans) and total seconds, its share of all
    /// algorithm self time, the card's cost bounds and variable, and the nonzero counters in its
    /// spans (self excludes nested spans). Only algorithms with spans are timed; algorithms seen
    /// only through counters are listed at the end.
    #[command(after_help = "\
Examples:
  algo-graph query hot --join target/algo/join.toml
  algo-graph query hot --join target/algo/join.toml --by count --limit 5")]
    Hot {
        #[command(flatten)]
        join: JoinInput,
        /// Number of algorithms to print.
        #[arg(long, default_value_t = 10)]
        limit: usize,
        /// Order by self seconds, total seconds, or invocation count.
        #[arg(long, value_enum, default_value_t = HotBy::SelfSeconds)]
        by: HotBy,
    },
    /// What a run did not show running: declared algorithms and graph edges whose join verdict is not `ran`.
    ///
    /// Algorithms are split by the join's verdict into `not-run` (instrumentation that would
    /// have recorded them recorded nothing) and `unknown` (the run's evidence cannot tell), each
    /// with the evidence that decided it; the join's verdict rule is printed first. Edges are
    /// grouped by kind and verdict, each kind with its verdict rule.
    #[command(after_help = "\
Examples:
  algo-graph query unexercised --join target/algo/join.toml
  algo-graph query unexercised --join target/algo/join.toml --area backend --no-edges")]
    Unexercised {
        #[command(flatten)]
        join: JoinInput,
        /// Keep algorithms of this area (parser, definition, kompile, backend, kore) and edges touching it.
        #[arg(long)]
        area: Option<String>,
        /// Omit the edge list.
        #[arg(long)]
        no_edges: bool,
    },
    /// Find ids from words: matches algorithm, counter, phase, and representation ids, names, files, and site symbols.
    ///
    /// Case-insensitive; every whitespace-separated word must occur in some field of the node.
    /// Algorithms are listed first.
    #[command(after_help = "\
Examples:
  algo-graph query search matching
  algo-graph query search sort projection
  algo-graph query search rewrite/apply.rs")]
    Search {
        /// Words to look for.
        #[arg(required = true, num_args = 1..)]
        text: Vec<String>,
        /// Maximum number of matches to print.
        #[arg(long, default_value_t = 40)]
        limit: usize,
    },
}

#[derive(Debug, Args)]
struct JoinInput {
    /// Join TOML written by `algo-graph join` for one run.
    #[arg(long = "join", value_name = "join.toml")]
    path: PathBuf,
}

#[derive(Clone, Copy, Debug, ValueEnum)]
enum HotBy {
    #[value(name = "self")]
    SelfSeconds,
    Total,
    Count,
}

#[derive(Debug, Subcommand)]
enum RenderCommand {
    /// Render ordered phases and their contained algorithms.
    Pipeline(RenderArgs),
    /// Render algorithms, representations, relationships, and observations.
    Composition(CompositionArgs),
    /// Render the backend source-card inventory as Markdown.
    ModuleMap(OutputArgs),
    /// Render the self-contained HTML explorer, with zero or more embedded runs.
    Html(HtmlArgs),
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
struct HtmlArgs {
    /// Initial filters of the page; the reader may clear them. The whole graph is embedded.
    #[command(flatten)]
    render: RenderArgs,
    /// Run projection TOML produced by `algo-graph join`. Repeat for more than one run.
    #[arg(long = "join")]
    joins: Vec<PathBuf>,
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
    /// coverage.toml from `algo-graph coverage` for a coverage-instrumented execution of the
    /// receipt's command. It decides each algorithm's verdict from whether its site items
    /// executed; the site lines are read from the checkout named by --root, which must hold the
    /// covered sources.
    #[arg(long)]
    coverage: Option<PathBuf>,
}

#[derive(Debug, Args)]
struct CoverageArgs {
    /// JSON written by `llvm-cov export --format=text` for the instrumented binary.
    #[arg(long)]
    export: PathBuf,
    /// Checkout that built the binary; file paths are recorded relative to it.
    #[arg(long)]
    source_root: PathBuf,
    /// The instrumented binary, whose SHA-256 is recorded.
    #[arg(long)]
    binary: Option<PathBuf>,
    /// Destination path. Defaults to target/algo/coverage.toml.
    #[arg(short, long)]
    output: Option<PathBuf>,
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

fn main() -> ExitCode {
    let cli = Cli::parse();
    let root = cli.root.clone().unwrap_or_else(workspace_root);
    let result = match cli.command {
        Command::Query(arguments) => return run_query(&root, arguments),
        command => run(&root, command),
    };
    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("error: {error}");
            ExitCode::FAILURE
        }
    }
}

fn run(root: &Path, command: Command) -> Result<(), algo_graph::Error> {
    let root = root.to_owned();

    match command {
        Command::Graph { output } => {
            let build = report_build(build_graph(&root)?);
            // The report file belongs to the default output location; with `-o` the findings
            // already printed to standard error are the whole report.
            if output.is_none() {
                eprintln!("{}", write_report(&root, &build)?);
            }
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
            RenderCommand::Html(arguments) => {
                let build = report_build(build_graph(&root)?);
                let joins = arguments
                    .joins
                    .iter()
                    .map(|path| {
                        query::read_join(path).map_err(|error| {
                            algo_graph::Error::Invalid(format!(
                                "--join {}: {error}",
                                path.display()
                            ))
                        })
                    })
                    .collect::<Result<Vec<_>, algo_graph::Error>>()?;
                let output = arguments
                    .render
                    .output
                    .clone()
                    .unwrap_or_else(|| default_output(&root, "explorer.html"));
                write_output(
                    &output,
                    &render_html(&build.graph, &joins, &arguments.render.filters())?,
                )?;
                println!("wrote {}", output.display());
            }
        },
        Command::Join(arguments) => {
            let (graph, join) = join_files(
                &root,
                &arguments.graph,
                &arguments.trace,
                &arguments.receipt,
                arguments.coverage.as_deref(),
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
        Command::Coverage(arguments) => {
            let coverage = normalize_export(
                &std::fs::read_to_string(&arguments.export)?,
                &arguments.source_root,
                arguments.binary.as_deref(),
            )?;
            let output = arguments
                .output
                .unwrap_or_else(|| default_output(&root, "coverage.toml"));
            write_output(&output, &canonical_coverage_toml(&coverage))?;
            println!("wrote {}", output.display());
        }
        Command::Drift(arguments) => {
            let report = drift(&root, &arguments.since, arguments.until.as_deref())?;
            print!("{}", render_drift(&report));
        }
        Command::Query(_) => unreachable!("main dispatches query"),
    }
    Ok(())
}

/// Run one query. An unknown id exits 2; an unreadable input exits 1.
fn run_query(root: &Path, arguments: QueryArgs) -> ExitCode {
    match answer_query(root, &arguments) {
        Ok(Ok(text)) => {
            print!("{text}");
            ExitCode::SUCCESS
        }
        Ok(Err(not_found)) => {
            eprintln!("error: {not_found}");
            ExitCode::from(2)
        }
        Err(error) => {
            eprintln!("error: {error}");
            ExitCode::FAILURE
        }
    }
}

fn answer_query(
    root: &Path,
    arguments: &QueryArgs,
) -> Result<Result<String, NotFound>, algo_graph::Error> {
    let (graph, failures) = query::load_graph(root, arguments.graph.as_deref())?;
    for failure in failures {
        eprintln!("freshness failure: {failure}");
    }
    let format = arguments.format;
    let render = |answer: &dyn Rendered| -> Result<String, algo_graph::Error> {
        match format {
            Format::Text => Ok(answer.text()),
            Format::Toml => answer.toml(),
        }
    };
    Ok(match &arguments.command {
        QueryCommand::Owner { target } => match query::owner(&graph, root, target) {
            Ok(answer) => Ok(render(&answer)?),
            Err(error) => Err(error),
        },
        QueryCommand::Show { id } => match query::show(&graph, id) {
            Ok(answer) => Ok(render(&answer)?),
            Err(error) => Err(error),
        },
        QueryCommand::Impact { id } => match query::impact(&graph, id) {
            Ok(answer) => Ok(render(&answer)?),
            Err(error) => Err(error),
        },
        QueryCommand::Hot { join, limit, by } => {
            let join = query::read_join(&join.path)?;
            let by = match by {
                HotBy::SelfSeconds => HotOrder::SelfSeconds,
                HotBy::Total => HotOrder::Total,
                HotBy::Count => HotOrder::Count,
            };
            Ok(render(&query::hot(&graph, &join, by, *limit))?)
        }
        QueryCommand::Unexercised {
            join,
            area,
            no_edges,
        } => {
            let join = query::read_join(&join.path)?;
            match query::unexercised(&graph, &join, area.as_deref(), !no_edges) {
                Ok(answer) => Ok(render(&answer)?),
                Err(error) => Err(error),
            }
        }
        QueryCommand::Search { text, limit } => {
            Ok(render(&query::search(&graph, &text.join(" "), *limit))?)
        }
    })
}

/// Object-safe view of [`Answer`] for the format switch.
trait Rendered {
    fn text(&self) -> String;
    fn toml(&self) -> Result<String, algo_graph::Error>;
}

impl<T: Answer> Rendered for T {
    fn text(&self) -> String {
        Answer::text(self)
    }
    fn toml(&self) -> Result<String, algo_graph::Error> {
        Answer::toml(self)
    }
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
