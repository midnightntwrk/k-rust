use std::{
    path::{Path, PathBuf},
    process::ExitCode,
};

use algo_graph::{
    DwarfSymbolizer, Filters, MAP_PATH, atlas, attribute, build_graph, canonical_coverage_toml,
    canonical_join_toml, canonical_toml, check_staleness, diff, drift, fold_samply, join_files,
    normalize_export,
    query::{self, Answer, HotOrder, NotFound},
    read_atlas_index, read_join_file, read_stacks, receipt_graph, render_composition,
    render_composition_focus, render_drift, render_html, render_map, render_module_map,
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
    /// Write the generated algorithm map, the whole graph in one Markdown document for work that
    /// spans algorithms: pipelines, representations, contracts, fallbacks, and entry sites.
    Map {
        /// Destination path. Defaults to docs/algorithm-map.md below the repository root, the
        /// checked-in copy that the freshness test compares with the rendered map.
        #[arg(short, long)]
        output: Option<PathBuf>,
    },
    /// Render a generated Mermaid projection.
    Render {
        #[command(subcommand)]
        command: RenderCommand,
    },
    /// Join a Chrome trace (or a trace aggregate) and receipt to a canonical static graph.
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
    /// Compare joins of one workload by algorithm: span counts, counters, self and total time, verdicts.
    ///
    /// Each flag is repeatable; the joins of one side are repeats of one workload. A side's value
    /// is the median over its repeats with the min..max range. Span counts and counters are
    /// deterministic, so their deltas are exact; a time delta is `unreplicated` when a side has
    /// one join, `within noise` when the two ranges overlap, and `faster` or `slower` otherwise.
    /// Algorithms are sorted by absolute self-time delta; every changed count is listed in its
    /// own section, and algorithms declared by only one side's graph are reported as added or
    /// removed.
    #[command(after_help = "\
Examples:
  algo-graph diff --before old/join.toml --after new/join.toml
  algo-graph diff --before a/rep-1/join.toml --before a/rep-2/join.toml --after b/rep-1/join.toml --after b/rep-2/join.toml --format toml")]
    Diff(DiffArgs),
    /// Summarize an atlas.toml index of receipts into a cost atlas for agents.
    ///
    /// Per workload: wall and span time, and the algorithms by median self-time share of the
    /// workload's span time (the sum of algorithm self seconds), each with its Amdahl ceiling
    /// 1 / (1 - share), span count, and the counters it moved, cut at 90 % of span time plus
    /// every share above 1 %. Then a matrix of shares across workloads, and per ladder the
    /// least-squares slope of ln(span count), ln(self seconds), and ln(each declared counter)
    /// against ln(param), beside the card's cost bounds. With --check, prints the listed
    /// algorithms whose site files changed since the index commit and exits 1 when there is one.
    #[command(after_help = "\
Examples:
  algo-graph atlas --index receipts/<commit>/atlas.toml -o atlas.md
  algo-graph atlas --index receipts/<commit>/atlas.toml --toml atlas.toml
  algo-graph atlas --index receipts/<commit>/atlas.toml --check")]
    Atlas(AtlasArgs),
    /// Attribute the CPU samples of a `samply record` profile to algorithm cards.
    ///
    /// Resolves every address of the profiled binary to its source frames, one per inlined call,
    /// from the binary's DWARF line tables (build it with the `profiling` profile), and folds equal
    /// stacks. A workspace frame belongs to the algorithm whose card site item contains its line;
    /// a sample's self owner is the innermost owned frame, and every owner on the stack gets a
    /// total sample. Workspace frames no card owns are uncarded code, reported as leaf functions
    /// (the innermost workspace frame) with the algorithm they run under, and by inclusive samples.
    /// Site items are read from the sources below --root, which must be the sources the binary
    /// was built from. Without -o, prints a text summary.
    #[command(after_help = "\
Examples:
  taskset -c 0-15 samply record --save-only -o profile.json.gz -- target/profiling/krust krun ...
  algo-graph profile --samply profile.json.gz --binary target/profiling/krust --stacks stacks.json -o profile.toml
  algo-graph profile --from-stacks stacks.json --graph receipt/graph.toml")]
    Profile(ProfileArgs),
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
struct DiffArgs {
    /// Join TOML of the baseline; repeat for repeated runs of the workload.
    #[arg(long = "before", value_name = "join.toml", required = true)]
    before: Vec<PathBuf>,
    /// Join TOML of the changed build; repeat for repeated runs of the workload.
    #[arg(long = "after", value_name = "join.toml", required = true)]
    after: Vec<PathBuf>,
    /// Output format: plain text for reading, or TOML with the same content for parsing.
    #[arg(long, value_enum, default_value_t = Format::Text)]
    format: Format,
}

#[derive(Debug, Args)]
struct AtlasArgs {
    /// Receipt index (schema 1); join paths are relative to it.
    #[arg(long, value_name = "atlas.toml")]
    index: PathBuf,
    /// Write the Markdown atlas here instead of standard output.
    #[arg(short, long, value_name = "atlas.md")]
    output: Option<PathBuf>,
    /// Also write the atlas as TOML here.
    #[arg(long = "toml", value_name = "atlas.toml")]
    toml: Option<PathBuf>,
    /// Print the staleness of the listed algorithms instead of the Markdown, against the
    /// checkout named by --root, and exit 1 when one is stale.
    #[arg(long)]
    check: bool,
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
    /// Chrome trace-event JSON produced by `krust --trace`, or the aggregate produced by
    /// `krust --trace-aggregate`.
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
struct ProfileArgs {
    /// Profile written by `samply record --save-only` (`.json` or `.json.gz`).
    #[arg(
        long,
        value_name = "profile.json.gz",
        required_unless_present = "from_stacks",
        conflicts_with = "from_stacks",
        requires = "binary"
    )]
    samply: Option<PathBuf>,
    /// The profiled executable; its DWARF line tables resolve the profile's addresses.
    #[arg(long, value_name = "krust")]
    binary: Option<PathBuf>,
    /// Read stacks that an earlier --stacks wrote instead of a samply profile.
    #[arg(long, value_name = "stacks.json")]
    from_stacks: Option<PathBuf>,
    /// Write the symbolicated, folded stacks here (JSON, one stack per line).
    #[arg(long, value_name = "stacks.json", conflicts_with = "from_stacks")]
    stacks: Option<PathBuf>,
    /// Graph TOML whose algorithm sites own frames. Defaults to the graph built from --root.
    #[arg(long, value_name = "graph.toml")]
    graph: Option<PathBuf>,
    /// Write the attribution as TOML here instead of printing a summary.
    #[arg(short, long, value_name = "profile.toml")]
    output: Option<PathBuf>,
    /// Rows per table in the printed summary.
    #[arg(long, default_value_t = 15)]
    limit: usize,
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
        Command::Atlas(arguments) => return run_atlas(&root, &arguments),
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
        Command::Map { output } => {
            let build = report_build(build_graph(&root)?);
            let output = output.unwrap_or_else(|| root.join(MAP_PATH));
            write_output(&output, &render_map(&build.graph))?;
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
        Command::Diff(arguments) => {
            let read = |paths: &[PathBuf]| {
                paths
                    .iter()
                    .map(|path| Ok((path.display().to_string(), read_join_file(path)?)))
                    .collect::<Result<Vec<_>, algo_graph::Error>>()
            };
            let answer = diff(&read(&arguments.before)?, &read(&arguments.after)?)?;
            print!(
                "{}",
                match arguments.format {
                    Format::Text => Answer::text(&answer),
                    Format::Toml => Answer::toml(&answer)?,
                }
            );
        }
        Command::Profile(arguments) => {
            let stacks = match (&arguments.samply, &arguments.from_stacks) {
                (Some(profile), _) => {
                    let binary = arguments.binary.as_deref().expect("clap requires --binary");
                    let name = binary
                        .file_name()
                        .map(|name| name.to_string_lossy().into_owned())
                        .unwrap_or_default();
                    let mut symbolizer = DwarfSymbolizer::new(binary, &root)?;
                    let stacks = fold_samply(profile, &name, &mut symbolizer)?;
                    if let Some(path) = &arguments.stacks {
                        write_output(path, &stacks.json()?)?;
                    }
                    stacks
                }
                (None, Some(path)) => read_stacks(path)?,
                (None, None) => unreachable!("clap requires --samply or --from-stacks"),
            };
            let graph = match &arguments.graph {
                Some(path) => {
                    let source = std::fs::read_to_string(path).map_err(|error| {
                        algo_graph::Error::Invalid(format!("{}: {error}", path.display()))
                    })?;
                    toml::from_str(&source).map_err(|error| {
                        algo_graph::Error::Invalid(format!("{}: {error}", path.display()))
                    })?
                }
                None => build_graph(&root)?.graph,
            };
            let mut profile = attribute(&stacks, &graph, &root)?;
            match &arguments.output {
                Some(output) => {
                    let stacks_path = arguments.stacks.as_ref().or(arguments.from_stacks.as_ref());
                    profile.stacks = stacks_path.map(|path| relative_to(path, output));
                    write_output(output, &profile.toml()?)?;
                    eprintln!("wrote {}", output.display());
                }
                None => print!("{}", profile.text(arguments.limit)),
            }
        }
        Command::Query(_) | Command::Atlas(_) => unreachable!("main dispatches query and atlas"),
    }
    Ok(())
}

/// Write the atlas; with `--check`, exit 1 when a listed algorithm is stale.
fn run_atlas(root: &Path, arguments: &AtlasArgs) -> ExitCode {
    let result = (|| -> Result<bool, algo_graph::Error> {
        let (index, receipts) = read_atlas_index(&arguments.index)?;
        let mut regenerate = format!("algo-graph atlas --index {}", arguments.index.display());
        if let Some(output) = &arguments.output {
            regenerate.push_str(&format!(" -o {}", output.display()));
        }
        if let Some(toml) = &arguments.toml {
            regenerate.push_str(&format!(" --toml {}", toml.display()));
        }
        let atlas = atlas(&index, &receipts, &regenerate);
        if let Some(toml) = &arguments.toml {
            write_output(toml, &atlas.toml()?)?;
            eprintln!("wrote {}", toml.display());
        }
        match &arguments.output {
            Some(output) => {
                write_output(output, &atlas.markdown())?;
                eprintln!("wrote {}", output.display());
            }
            None if !arguments.check => print!("{}", atlas.markdown()),
            None => {}
        }
        if !arguments.check {
            return Ok(false);
        }
        let graph = receipt_graph(&arguments.index, &receipts)?;
        let staleness = check_staleness(root, &index.commit, graph, &atlas.listed_ids())?;
        print!("{}", staleness.text());
        Ok(!staleness.stale.is_empty())
    })();
    match result {
        Ok(false) => ExitCode::SUCCESS,
        Ok(true) => ExitCode::FAILURE,
        Err(error) => {
            eprintln!("error: {error}");
            ExitCode::FAILURE
        }
    }
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

/// `path` relative to the directory of `file` when both are in one directory tree, else `path`.
fn relative_to(path: &Path, file: &Path) -> String {
    let absolute = |path: &Path| std::path::absolute(path).unwrap_or_else(|_| path.to_owned());
    let path = absolute(path);
    let directory = absolute(file)
        .parent()
        .map(Path::to_owned)
        .unwrap_or_default();
    path.strip_prefix(&directory)
        .map_or_else(|_| path.clone(), Path::to_owned)
        .display()
        .to_string()
}

fn default_output(root: &Path, name: &str) -> PathBuf {
    root.join("target/algo").join(name)
}
