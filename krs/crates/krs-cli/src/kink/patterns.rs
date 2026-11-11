//! The patterns of a corpus's KRS patterns packages (`[[patterns]] krs = "PACKAGE"`), which
//! `query` and a `fuzz` pattern job ask beside the kink pattern lists it declares.
//!
//! **Preparing a package.** A patterns package is a Cargo package of the graph Cargo resolves for
//! `--manifest-path`, outside the definition's closure, that depends on the definition's package
//! and declares one KRS definition facet. The front end composes that facet with the definition
//! the command selected, as it composes an observer (`crate::command::patterns_definition`), for
//! its Definition IR only, and emits its `k::patterns!` clauses
//! ([`krs_compiler::emit_patterns`]). Nothing of the package enters `definition.k`, the
//! specification's digest or any key but its own patterns': a pattern's answers are keyed by its
//! compiled target, so editing one clause re-asks that clause's pattern alone.
//!
//! **When.** kink-flow asks for a package only when it assembles the corpus's declared patterns
//! and reaches the package's entry ([`kink_flow::pattern::declared_patterns`]): only `query` and
//! `fuzz --pattern` assemble them, and only when the command line names no list (`--patterns`).
//! So no other verb, and no command that names a list, prepares a package. A package is prepared
//! once per command, when first asked.
//!
//! **The patterns.** Each clause is the `[[pattern]]` a pattern list would write for it: its id,
//! its documentation as `note`, `#[k::cases(..)]` as `programs`, `#[k::expect(no)]` as `expect`,
//! and its steps as `steps`, each with its `unless`. It passes the checks a list's table passes
//! (kink-flow [`kink_flow::pattern::WrittenPattern::checked`]), so a chain of one step without
//! `unless` is that step's single pattern, as in a list. Its source is the package as the corpus
//! names it, the clause's Rust item, and the file and line its name is written at. A package that
//! cannot be prepared, whose clauses do not emit (a binder of two sorts,
//! `krs::analysis::pattern-binder`), or one of whose clauses the checks refuse, gives no pattern:
//! the entry is refused with the reason, naming the clause where one is at fault, and never
//! skipped.
//!
//! **Names.** A clause's binders are K variables in its steps (`before` is `Before`). The front end
//! keeps each clause's binders by its source, so that the annotation names a witness's bindings
//! by the binders the author wrote ([`super::annotate`]). kink's checks of the steps' shared
//! variables are the authority on the steps' text; the binders' sorts are not checked again.

use std::collections::BTreeMap;
use std::path::PathBuf;
use std::sync::OnceLock;

use kink_flow::ManifestError;
use kink_flow::pattern::{
    KrsPatternPackages, PatternEntry, PatternSource, StepText, WrittenForm, WrittenPattern,
};
use krs_compiler::{EmittedPattern, PatternVariable};

use crate::{CommandRequest, DiagnosticSources};

/// A package's patterns, or why it gives none, and the binders of each clause by its Rust item.
struct Prepared {
    patterns: Result<Vec<PatternEntry>, String>,
    binders: BTreeMap<String, Vec<PatternVariable>>,
}

/// The patterns packages a corpus's manifest names, each prepared when kink-flow first asks for
/// it (module documentation).
pub(crate) struct KrsPackages {
    /// The command's selection, which a package is composed with.
    request: CommandRequest,
    /// The command's source roots, which render a package's diagnostics.
    sources: DiagnosticSources,
    /// Each package the manifest names, set once it is prepared.
    packages: BTreeMap<String, OnceLock<Prepared>>,
}

impl KrsPackages {
    /// The packages the `[[patterns]] krs` entries `entries` name, none prepared yet.
    pub(crate) fn new(
        entries: &[kink_flow::PatternsEntry],
        request: CommandRequest,
        sources: DiagnosticSources,
    ) -> Self {
        let packages = entries
            .iter()
            .filter_map(|entry| match entry {
                kink_flow::PatternsEntry::Krs { package } => {
                    Some((package.clone(), OnceLock::new()))
                }
                kink_flow::PatternsEntry::Files { .. } => None,
            })
            .collect();
        Self {
            request,
            sources,
            packages,
        }
    }

    /// The binders of the clause written at the Rust item `item` of the package `package`, as
    /// the manifest names it, when that package was prepared and its clauses emitted.
    pub(crate) fn binders(&self, package: &str, item: &str) -> Option<&[PatternVariable]> {
        self.packages
            .get(package)?
            .get()?
            .binders
            .get(item)
            .map(Vec::as_slice)
    }

    fn prepare(&self, package: &str) -> Prepared {
        let emitted = crate::command::patterns_definition(&self.request, package, &self.sources)
            .and_then(|prepared| {
                krs_compiler::emit_patterns(&prepared.definition)
                    .map(|patterns| (patterns, prepared.roots))
                    .map_err(|error| {
                        format!("the KRS patterns package `{package}` does not emit: {error}")
                    })
            });
        let (emitted, roots) = match emitted {
            Ok(emitted) => emitted,
            Err(reason) => {
                return Prepared {
                    patterns: Err(reason),
                    binders: BTreeMap::new(),
                };
            }
        };
        let binders = emitted
            .iter()
            .map(|pattern| (pattern.item.clone(), pattern.variables.clone()))
            .collect();
        Prepared {
            patterns: emitted
                .into_iter()
                .map(|pattern| entry(package, pattern, &roots))
                .collect(),
            binders,
        }
    }
}

impl KrsPatternPackages for KrsPackages {
    fn patterns(&self, package: &str) -> Option<&Result<Vec<PatternEntry>, String>> {
        let slot = self.packages.get(package)?;
        Some(&slot.get_or_init(|| self.prepare(package)).patterns)
    }
}

/// The pattern entry of the clause `pattern` of the package the manifest names `package`, its
/// source's line read from the file under its package's root in `roots`, checked as a list's
/// `[[pattern]]` is (module documentation); the refusal names the clause.
fn entry(
    package: &str,
    pattern: EmittedPattern,
    roots: &BTreeMap<String, PathBuf>,
) -> Result<PatternEntry, String> {
    let EmittedPattern {
        id,
        note,
        item,
        source,
        programs,
        expect,
        steps,
        variables: _,
    } = pattern;
    let file = roots
        .get(&source.package)
        .map(|root| root.join(&source.file))
        .ok_or_else(|| {
            format!(
                "the clause {item} has no authored source in a package of the composition (package {:?}, file {:?})",
                source.package, source.file
            )
        })?;
    let text = std::fs::read_to_string(&file)
        .map_err(|error| format!("the clause {item}: cannot read {}: {error}", file.display()))?;
    let line = u64::from(source.line(&text));
    let shown = format!("{item} ({}:{line})", source.file);
    let written = WrittenPattern {
        id,
        form: WrittenForm::Steps(
            steps
                .into_iter()
                .map(|step| StepText {
                    pattern: step.pattern,
                    unless: step.unless,
                })
                .collect(),
        ),
        programs,
        expect,
        note,
    };
    let mut entry = written
        .checked(&format!("item {item}"))
        .map_err(|error: ManifestError| format!("the clause {shown}: {error}"))?;
    entry.source = Some(PatternSource::Krs {
        package: package.to_owned(),
        item,
        file: source.file,
        line,
    });
    Ok(entry)
}
