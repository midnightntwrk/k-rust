//! How documents spell next steps for a KRS corpus: `krs kink <verb>` with the selection that
//! reproduces the step on the same corpus.

use kink_flow::{CommandSpelling, Verb};
use std::path::{Path, PathBuf};

use super::KinkRequest;
use crate::{PackageSelector, RegistrationMode};

/// The krs front end's [`CommandSpelling`]: `krs kink <verb>`, then the options that select the
/// package, the facet and the corpus this command ran on, and those that choose how krs builds
/// and judges the package (`--cfg`, `--profile`, `--registration`), so that a next step judges
/// the same K.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct KrsSpelling {
    /// The selection options, each preceded by a space.
    selection: String,
    /// The corpus's own mutation list, which `run` reads without `--mutations` (and keeps its
    /// killer record for); `None` when not known.
    own_mutations: Option<PathBuf>,
}

impl KrsSpelling {
    pub(crate) fn new(request: &KinkRequest) -> Self {
        let mut words = Vec::new();
        if request.manifest_path.as_os_str() != "Cargo.toml" {
            words.push("--manifest-path".to_owned());
            words.push(request.manifest_path.to_string_lossy().into_owned());
        }
        match &request.root.package {
            PackageSelector::Name(name) => {
                words.push("--package".to_owned());
                words.push(name.clone());
            }
            PackageSelector::Id(id) => {
                words.push("--package-id".to_owned());
                words.push(id.clone());
            }
        }
        words.push("--definition".to_owned());
        words.push(request.root.definition.clone());
        for dependency in &request.dependencies {
            words.push("--dependency".to_owned());
            let package = match &dependency.package {
                PackageSelector::Name(name) | PackageSelector::Id(name) => name,
            };
            words.push(format!("{package}:{}", dependency.definition));
        }
        for cfg in &request.cfg {
            words.push("--cfg".to_owned());
            words.push(match &cfg.value {
                Some(value) => format!("{}={value}", cfg.key),
                None => cfg.key.clone(),
            });
        }
        if let Some(profile) = request.profile {
            words.push("--profile".to_owned());
            words.push(profile.as_str().to_owned());
        }
        if request.registration != RegistrationMode::default() {
            words.push("--registration".to_owned());
            words.push(
                match request.registration {
                    RegistrationMode::Inventory => "inventory",
                    RegistrationMode::Explicit => "explicit",
                }
                .to_owned(),
            );
        }
        if let Some(corpus) = &request.corpus {
            words.push("--corpus".to_owned());
            words.push(corpus.to_string_lossy().into_owned());
        }
        let mut selection = String::new();
        for word in &words {
            selection.push(' ');
            selection.push_str(&shell_word(word));
        }
        Self {
            selection,
            own_mutations: None,
        }
    }

    /// The spelling, knowing the corpus's own mutation list `path`, which a `run` of that list
    /// reads without naming it ([`CommandSpelling::run_list`]).
    pub(crate) fn with_own_mutations(mut self, path: Option<PathBuf>) -> Self {
        self.own_mutations = path;
        self
    }

    /// The command that writes `kink/definition.k`.
    pub(crate) fn emit(&self) -> String {
        format!("krs kink emit{}", self.selection)
    }
}

impl CommandSpelling for KrsSpelling {
    fn command(&self, verb: Verb) -> String {
        format!("krs kink {}{}", verb.as_str(), self.selection)
    }

    /// `krs kink run` with `--mutations` unless `mutations` is the corpus's own list, which a run
    /// reads by default and keeps the killer record of.
    fn run_list(&self, mutations: &Path, cache: Option<&Path>) -> String {
        let named = if self.own_mutations.as_deref() == Some(mutations) {
            String::new()
        } else {
            format!(
                " --mutations {}",
                shell_word(&mutations.display().to_string())
            )
        };
        format!(
            "{}{named}{}",
            self.command(Verb::Run),
            kink_flow::cli::cache_option(cache)
        )
    }
}

/// `word` as a shell reads it back: unchanged when it has no character a shell treats
/// specially, single-quoted otherwise.
fn shell_word(word: &str) -> String {
    let plain = !word.is_empty()
        && word
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || "-_./:=@+,%".contains(c));
    if plain {
        word.to_owned()
    } else {
        format!("'{}'", word.replace('\'', r"'\''"))
    }
}

#[cfg(test)]
mod tests {
    use super::KrsSpelling;
    use crate::kink::{KinkRequest, KinkVerb};
    use crate::{FacetSelector, KrsCfg, MessageFormat, PackageSelector, RegistrationMode};
    use kink_flow::{CommandSpelling, Verb};
    use std::path::PathBuf;

    fn request(manifest: &str, corpus: Option<&str>) -> KinkRequest {
        KinkRequest {
            manifest_path: PathBuf::from(manifest),
            root: FacetSelector {
                package: PackageSelector::Name("story-plus".into()),
                definition: "main".into(),
            },
            dependencies: Vec::new(),
            cfg: vec![KrsCfg {
                key: "k_backend".into(),
                value: Some("llvm".into()),
            }],
            registration: RegistrationMode::Inventory,
            profile: None,
            message_format: MessageFormat::Human,
            corpus: corpus.map(PathBuf::from),
            locked: false,
            verb: KinkVerb::Emit { check: false },
        }
    }

    #[test]
    fn a_next_step_names_the_selection_it_ran_on() {
        let spelling = KrsSpelling::new(&request("Cargo.toml", None));
        assert_eq!(
            spelling.command(Verb::Run),
            "krs kink run --package story-plus --definition main --cfg k_backend=llvm"
        );
        assert_eq!(
            spelling.verb(Verb::Coverage),
            spelling.command(Verb::Coverage)
        );
        assert_eq!(
            spelling.emit(),
            "krs kink emit --package story-plus --definition main --cfg k_backend=llvm"
        );
        let mut strict = request("my dir/Cargo.toml", Some("corpora/a"));
        strict.profile = Some(krs_ir::RawKProfile::Strict);
        strict.registration = RegistrationMode::Explicit;
        assert_eq!(
            KrsSpelling::new(&strict).command(Verb::Check),
            "krs kink check --manifest-path 'my dir/Cargo.toml' --package story-plus \
             --definition main --cfg k_backend=llvm --profile strict --registration explicit \
             --corpus corpora/a"
        );
    }
}
