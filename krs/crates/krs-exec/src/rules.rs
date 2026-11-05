//! The compiled definition's rules and equations, by the backend's identity (`UNIQUE_ID`).
//!
//! k-rust names a rule or an equation by its `UNIQUE_ID` in run coverage and in traces, and a
//! run's stop rules are named by label or by KRS item ([`crate::StopRules`]). This catalog is
//! what krs-exec reads both from: each identity's label and kind, as the backend loaded them
//! (`Backend::rule_catalog`), and the KRS item that wrote it.

use std::collections::BTreeMap;

use k_rust::backend::{Backend, CompiledRuleKind};

use crate::{ExecError, UnknownCrate, origin::ItemPath, report::RuleKind};

/// One identity of the catalog.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CatalogRule {
    /// The rule's label, as the backend names it (`SM83.boundary-fetch`, `nat--plus_zero`).
    pub(crate) label: Option<String>,
    /// What kind of sentence it is.
    pub(crate) kind: RuleKind,
    /// The KRS item that wrote it ([`crate::origin::item_path`]).
    pub(crate) item: Option<ItemPath>,
}

/// The rules and equations of the definition a run executes, by `UNIQUE_ID`.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct Rules {
    by_id: BTreeMap<String, CatalogRule>,
    /// The K namespace of the root package: the package whose module is the definition's main
    /// module, which the backend runs, so every other package's rules run only as its imports.
    root: String,
}

impl Rules {
    /// The catalog of the definition `backend` runs, whose main module is `main_module`, each
    /// identity with the item `item_of` names.
    pub(crate) fn new(
        backend: &Backend,
        main_module: &str,
        item_of: impl Fn(&str) -> Option<ItemPath>,
    ) -> Result<Self, ExecError> {
        let mut by_id = BTreeMap::new();
        for rule in backend.rule_catalog(None)? {
            // Equal written axioms share one identity (`shared_identity`); they are one rule.
            let item = item_of(&rule.id);
            by_id.entry(rule.id).or_insert(CatalogRule {
                label: rule.label,
                kind: match rule.kind {
                    CompiledRuleKind::Rewrite => RuleKind::Rule,
                    CompiledRuleKind::FunctionEquation => RuleKind::Equation,
                    CompiledRuleKind::Simplification => RuleKind::Simplification,
                    CompiledRuleKind::Definedness => RuleKind::Definedness,
                },
                item,
            });
        }
        // KRS names a package's module by the package's K namespace (`<NS>`), so the main
        // module's name is the root package's namespace.
        Ok(Self {
            by_id,
            root: main_module.to_owned(),
        })
    }

    #[cfg(test)]
    pub(crate) fn from_entries(
        root: &str,
        entries: impl IntoIterator<Item = (String, CatalogRule)>,
    ) -> Self {
        Self {
            by_id: entries.into_iter().collect(),
            root: root.to_owned(),
        }
    }

    /// The identity `id`, when the catalog holds it.
    pub(crate) fn get(&self, id: &str) -> Option<&CatalogRule> {
        self.by_id.get(id)
    }

    /// The rewrite rules the stop name `requested` selects ([`crate::StopRules`]): by KRS item
    /// when it holds `::` ([`Self::resolve_item`]), else by label ([`Self::resolve_rewrite`]).
    pub(crate) fn resolve_stop(&self, requested: &str) -> Result<Vec<String>, ExecError> {
        if requested.contains("::") {
            self.resolve_item(requested)
        } else {
            self.resolve_rewrite(requested)
        }
    }

    /// The rewrite rules `requested` names, by label: exactly, or by a unique `.`-suffix as
    /// `krs prove --claim` accepts a claim label (`boundary-fetch` for `SM83.boundary-fetch`).
    ///
    /// The name is resolved among the labels of every sentence, whatever its kind, and the
    /// sentences it names must then be rewrite rules: only a rewrite rule takes a step, so a
    /// name that selects an equation, a simplification or a definedness equation is refused,
    /// never read as a suffix of some rewrite rule's label instead. An exact label wins over
    /// every suffix. A label several rewrite rules carry selects each of them; a suffix that two
    /// labels end with is ambiguous.
    pub(crate) fn resolve_rewrite(&self, requested: &str) -> Result<Vec<String>, ExecError> {
        let labelled = || {
            self.by_id
                .iter()
                .filter_map(|(id, rule)| Some((id, rule, rule.label.as_deref()?)))
        };
        let mut named = labelled()
            .filter(|(.., label)| *label == requested)
            .map(|(id, rule, _)| (id, rule))
            .collect::<Vec<_>>();
        if named.is_empty() {
            let suffix = format!(".{requested}");
            let mut labels = BTreeMap::<&str, Vec<(&String, &CatalogRule)>>::new();
            for (id, rule, label) in labelled().filter(|(.., label)| label.ends_with(&suffix)) {
                labels.entry(label).or_default().push((id, rule));
            }
            named = match labels.len() {
                0 => {
                    return Err(ExecError::UnknownRule {
                        requested: requested.to_owned(),
                        sentence: None,
                        suggestion: self.suggestion(requested),
                    });
                }
                1 => labels.into_values().next().unwrap_or_default(),
                _ => {
                    return Err(ExecError::AmbiguousRule {
                        requested: requested.to_owned(),
                        matches: labels.into_keys().map(str::to_owned).collect(),
                    });
                }
            };
        }
        if let Some((_, other)) = named.iter().find(|(_, rule)| rule.kind != RuleKind::Rule) {
            return Err(ExecError::UnknownRule {
                requested: requested.to_owned(),
                sentence: Some((other.label.clone().unwrap_or_default(), other.kind)),
                suggestion: None,
            });
        }
        Ok(named.into_iter().map(|(id, _)| id.clone()).collect())
    }

    /// The rewrite rules a stop named by KRS item selects: every rewrite rule the item
    /// `requested` wrote, whatever the rules' labels.
    ///
    /// The item is named by its Rust path: `crate::` and its path below the root crate's root,
    /// or the crate name of the package that declares it ([`ItemPath::krate`]: its Cargo package
    /// name with `-` written `_`, whatever a depending package's manifest renames it to) and its
    /// path below that crate's root.
    /// A path that starts with neither is read both ways, as Rust reads a path at the crate
    /// root, and is ambiguous where the root package has an item at it and a package of that
    /// crate name has one at its rest ([`ExecError::AmbiguousItem`]); so is a path two packages
    /// of one crate name each have an item at.
    ///
    /// An item lowers to several sentences where KRS or K generates them from one (a context's
    /// heat and cool rules, a strict production's), and a stop is a step by any of them. The
    /// item's sentences that are no rewrite rule take no step, so they are no stop; an item none
    /// of whose sentences is a rewrite rule is refused, naming their kinds. A path no sentence is
    /// the item of is refused naming the items at the path below its first segment, by the names
    /// that select them ([`Self::elsewhere`]), and saying what its first segment is where it
    /// names no package as a stop does ([`UnknownCrate`]).
    pub(crate) fn resolve_item(&self, requested: &str) -> Result<Vec<String>, ExecError> {
        self.resolve_item_named(requested)
            .map_err(|error| match error {
                ExecError::UnknownItem {
                    requested, kinds, ..
                } if kinds.is_empty() => ExecError::UnknownItem {
                    unknown_crate: self.unknown_crate(&requested),
                    suggestions: self.elsewhere(&requested),
                    requested,
                    kinds,
                },
                error => error,
            })
    }

    /// The first segment of `requested` where it is neither `crate` nor the crate name of a
    /// dependency ([`ItemPath::krate`]) nor a module of the root package's items: the root
    /// package's own crate name or `self`, which name the root package but are not how a stop
    /// names its items, or else a name the definition records no package by.
    fn unknown_crate(&self, requested: &str) -> Option<UnknownCrate> {
        let (first, _) = requested.split_once("::")?;
        let module = format!("{first}::");
        let items = || self.by_id.values().filter_map(|rule| rule.item.as_ref());
        let known = first == "crate"
            || items().any(|item| {
                if item.namespace == self.root {
                    item.path.starts_with(&module)
                } else {
                    item.krate == first
                }
            });
        if known {
            None
        } else if first == "self"
            || items().any(|item| item.namespace == self.root && item.krate == first)
        {
            Some(UnknownCrate::Root(first.to_owned()))
        } else {
            Some(UnknownCrate::Unrecorded(first.to_owned()))
        }
    }

    /// The names that select the items with a rewrite rule at the path below `requested`'s
    /// first segment, in any package, other than `requested` itself: what a path written with
    /// another crate's name, a renamed one or `crate::` for a dependency's item, meant.
    fn elsewhere(&self, requested: &str) -> Vec<String> {
        let Some((_, below)) = requested.split_once("::") else {
            return Vec::new();
        };
        let mut names = self
            .by_id
            .values()
            .filter(|rule| rule.kind == RuleKind::Rule)
            .filter_map(|rule| rule.item.as_ref())
            .filter(|item| item.path == below)
            .map(|item| self.spelling(item))
            .filter(|name| name != requested && self.resolve_item_named(name).is_ok())
            .collect::<Vec<_>>();
        names.sort_unstable();
        names.dedup();
        names
    }

    /// [`Self::resolve_item`] without the names a refusal suggests.
    fn resolve_item_named(&self, requested: &str) -> Result<Vec<String>, ExecError> {
        let (in_root, in_dependency) = match requested.split_once("::") {
            Some(("crate", path)) => (path, None),
            Some((krate, path)) => (requested, Some((krate, path))),
            None => (requested, None),
        };
        // The item's sentences by package: their rewrite rules, the kinds of the others, and
        // the item's spelling.
        let mut packages = BTreeMap::<&str, (Vec<String>, Vec<RuleKind>, String)>::new();
        for (id, rule) in &self.by_id {
            let Some(item) = &rule.item else {
                continue;
            };
            let named = if item.namespace == self.root {
                item.path == in_root
            } else {
                in_dependency.is_some_and(|(krate, path)| item.krate == krate && item.path == path)
            };
            if !named {
                continue;
            }
            let (rules, kinds, _) = packages
                .entry(&item.namespace)
                .or_insert_with(|| (Vec::new(), Vec::new(), self.spelling(item)));
            if rule.kind == RuleKind::Rule {
                rules.push(id.clone());
            } else if !kinds.contains(&rule.kind) {
                kinds.push(rule.kind);
            }
        }
        if packages.len() > 1 {
            return Err(ExecError::AmbiguousItem {
                requested: requested.to_owned(),
                matches: packages
                    .into_iter()
                    .map(|(namespace, (.., spelling))| (spelling, namespace.to_owned()))
                    .collect(),
            });
        }
        let (rules, kinds, _) = packages.into_values().next().unwrap_or_default();
        if rules.is_empty() {
            return Err(ExecError::UnknownItem {
                requested: requested.to_owned(),
                kinds,
                unknown_crate: None,
                suggestions: Vec::new(),
            });
        }
        Ok(rules)
    }

    /// The name of `item` that [`Self::resolve_item`] reads as it whatever else the definition
    /// declares: `crate::` and its path for an item of the root package, its crate name and its
    /// path otherwise. It names the item alone except where two packages of one crate name each
    /// have an item at its path, or the root package has an item at the whole of a dependency
    /// item's spelling.
    pub(crate) fn spelling(&self, item: &ItemPath) -> String {
        let krate = if item.namespace == self.root {
            "crate"
        } else {
            &item.krate
        };
        format!("{krate}::{}", item.path)
    }

    /// A name for the rewrite rule `id` that a stop accepts ([`crate::StopRules`]) and that
    /// selects it: its item's spelling where that names the item alone, else its label where
    /// that selects it; `None` where neither does.
    pub(crate) fn stop_name(&self, id: &str) -> Option<String> {
        let rule = self.by_id.get(id)?;
        let selects = |selected: Result<Vec<String>, ExecError>| {
            selected.is_ok_and(|ids| ids.iter().any(|selected| selected == id))
        };
        rule.item
            .as_ref()
            .map(|item| self.spelling(item))
            .filter(|name| selects(self.resolve_item(name)))
            .or_else(|| {
                rule.label
                    .clone()
                    .filter(|label| selects(self.resolve_rewrite(label)))
            })
    }

    /// The name of the KRS item that wrote the rewrite rule `id`, as a stopped end's class names
    /// it ([`crate::EndClass::rule`]); `None` for an identity that is no rewrite rule, that no
    /// item wrote, or whose item no name a stop accepts selects alone ([`Self::item_name`]).
    pub(crate) fn class_name(&self, id: &str) -> Option<String> {
        let rule = self.by_id.get(id)?;
        if rule.kind != RuleKind::Rule {
            return None;
        }
        self.item_name(rule.item.as_ref()?)
    }

    /// The name of the KRS item `requested` names as a stop does ([`crate::StopRules`]: by KRS
    /// item or K label), as a stopped end's class names it ([`Self::item_name`]), or why it names
    /// no one item: a stopped end's class is the KRS item of the rule it stopped at, so a name
    /// for a class selects the rewrite rules of exactly one item.
    pub(crate) fn stop_item(&self, requested: &str) -> Result<String, String> {
        let ids = if requested.contains("::") {
            self.resolve_item(requested)
        } else {
            self.resolve_rewrite(requested)
        }
        .map_err(|error| error.to_string())?;
        let mut items = std::collections::BTreeSet::new();
        for id in &ids {
            let Some(item) = self.by_id.get(id).and_then(|rule| rule.item.as_ref()) else {
                return Err(format!(
                    "`{requested}` selects a rewrite rule no KRS item wrote, so no stopped end's class names it"
                ));
            };
            items.insert(item);
        }
        let mut items = items.into_iter();
        match (items.next(), items.next()) {
            (Some(item), None) => self.item_name(item).ok_or_else(|| {
                format!(
                    "`{requested}` selects the rules of the KRS item `{}`, which no name a stop accepts selects alone",
                    self.spelling(item)
                )
            }),
            (Some(first), Some(second)) => Err(format!(
                "`{requested}` selects the rules of several KRS items (`{}`, `{}`{}), and a stopped end's class is one; name one of them",
                self.spelling(first),
                self.spelling(second),
                if items.len() > 0 { ", .." } else { "" }
            )),
            (None, _) => Err(format!("`{requested}` selects no rewrite rule")),
        }
    }

    /// The one name of `item` that a stopped end's class holds: a name a stop accepts that
    /// selects rewrite rules of `item` and of no other item, so that two classes are equal
    /// exactly when they name one item, and a document that writes the name reads back as the
    /// item. It is the item's spelling ([`Self::spelling`]) where that names the item alone,
    /// else the first label, in label order, of the item's rewrite rules that selects rules of
    /// the item alone; `None` where neither does.
    fn item_name(&self, item: &ItemPath) -> Option<String> {
        let of_item = |selected: Result<Vec<String>, ExecError>| {
            selected.is_ok_and(|ids| {
                !ids.is_empty()
                    && ids.iter().all(|id| {
                        self.by_id
                            .get(id)
                            .is_some_and(|rule| rule.item.as_ref() == Some(item))
                    })
            })
        };
        let spelling = self.spelling(item);
        if of_item(self.resolve_item(&spelling)) {
            return Some(spelling);
        }
        let mut labels = self
            .by_id
            .values()
            .filter(|rule| rule.kind == RuleKind::Rule && rule.item.as_ref() == Some(item))
            .filter_map(|rule| rule.label.as_deref())
            .collect::<Vec<_>>();
        labels.sort_unstable();
        labels.dedup();
        labels
            .into_iter()
            .find(|label| of_item(self.resolve_rewrite(label)))
            .map(str::to_owned)
    }

    /// A did-you-mean for a rule label written as a Rust identifier (`boundary_fetch` for
    /// `boundary-fetch`) or in another case; else for the name of a KRS item, written without
    /// the path that names it as an item (`work_amount` for `crate::work_amount`).
    fn suggestion(&self, requested: &str) -> Option<String> {
        let kebab = requested.replace('_', "-").to_ascii_lowercase();
        let rewrite_rules = || {
            self.by_id
                .values()
                .filter(|rule| rule.kind == RuleKind::Rule)
        };
        let unique = |mut names: Vec<String>| {
            names.sort_unstable();
            names.dedup();
            match <[String; 1]>::try_from(names) {
                Ok([name]) => Some(name),
                Err(_) => None,
            }
        };
        let labels = rewrite_rules()
            .filter_map(|rule| rule.label.as_deref())
            .filter(|label| {
                let local = label.rsplit_once('.').map_or(*label, |(_, local)| local);
                local.to_ascii_lowercase() == kebab || label.to_ascii_lowercase() == kebab
            })
            .map(str::to_owned)
            .collect::<Vec<_>>();
        if !labels.is_empty() {
            return unique(labels);
        }
        unique(
            rewrite_rules()
                .filter_map(|rule| rule.item.as_ref())
                .filter(|item| item.path.rsplit("::").next() == Some(requested))
                .map(|item| self.spelling(item))
                .filter(|name| self.resolve_item(name).is_ok())
                .collect(),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::{CatalogRule, Rules};
    use crate::{ExecError, UnknownCrate, origin::ItemPath, report::RuleKind};

    /// The root package's K namespace in [`rules`].
    const ROOT: &str = "SM83";

    fn rule(id: &str, label: Option<&str>, kind: RuleKind) -> (String, CatalogRule) {
        (
            id.to_owned(),
            CatalogRule {
                label: label.map(str::to_owned),
                kind,
                item: None,
            },
        )
    }

    /// `entry` written by the item at `path` of the package of namespace `namespace` and crate
    /// name `krate`.
    fn by(
        (id, rule): (String, CatalogRule),
        namespace: &str,
        krate: &str,
        path: &str,
    ) -> (String, CatalogRule) {
        let item = Some(ItemPath {
            namespace: namespace.to_owned(),
            krate: krate.to_owned(),
            path: path.to_owned(),
        });
        (id, CatalogRule { item, ..rule })
    }

    fn rules() -> Rules {
        Rules::from_entries(
            ROOT,
            [
                by(
                    rule("r1", Some("SM83.boundary-fetch"), RuleKind::Rule),
                    ROOT,
                    "sm83",
                    "interrupt::boundary",
                ),
                by(
                    rule("r2", Some("SM83.boundary-halted"), RuleKind::Rule),
                    ROOT,
                    "sm83",
                    "interrupt::boundary",
                ),
                by(
                    rule("r3", Some("SM83.step"), RuleKind::Rule),
                    ROOT,
                    "sm83",
                    "step",
                ),
                rule("r4", Some("OTHER.step"), RuleKind::Rule),
                rule("r5", Some("SM83.shared"), RuleKind::Rule),
                rule("r6", Some("SM83.shared"), RuleKind::Rule),
                by(
                    rule("e1", Some("SM83.plus-zero"), RuleKind::Equation),
                    ROOT,
                    "sm83",
                    "interrupt::boundary",
                ),
                rule("e2", None, RuleKind::Equation),
                by(
                    rule("e3", Some("fetch"), RuleKind::Equation),
                    ROOT,
                    "sm83",
                    "fetch",
                ),
                rule("r7", Some("SM83.fetch"), RuleKind::Rule),
                by(
                    rule("s1", Some("SM83.lemma"), RuleKind::Simplification),
                    ROOT,
                    "sm83",
                    "fetch",
                ),
                rule("r8", Some("OTHER.lemma"), RuleKind::Rule),
            ],
        )
    }

    #[test]
    fn stop_rules_resolve_by_exact_label_or_unique_suffix() {
        let rules = rules();
        assert_eq!(
            rules.resolve_rewrite("SM83.boundary-fetch").unwrap(),
            ["r1"]
        );
        assert_eq!(rules.resolve_rewrite("boundary-halted").unwrap(), ["r2"]);
        assert_eq!(rules.resolve_rewrite("OTHER.step").unwrap(), ["r4"]);
        // One label on two axioms selects both.
        assert_eq!(rules.resolve_rewrite("shared").unwrap(), ["r5", "r6"]);
    }

    #[test]
    fn stop_rules_refuse_ambiguous_unknown_and_equation_names() {
        let rules = rules();
        let ambiguous = rules.resolve_rewrite("step").unwrap_err();
        assert!(
            matches!(&ambiguous, ExecError::AmbiguousRule { matches, .. } if matches == &["OTHER.step", "SM83.step"]),
            "{ambiguous:?}"
        );
        assert_eq!(
            ambiguous.to_string(),
            "rule label `step` is ambiguous; matches `OTHER.step`, `SM83.step`"
        );
        let spelled = rules.resolve_rewrite("boundary_fetch").unwrap_err();
        assert_eq!(
            spelled.to_string(),
            "no rewrite rule has label `boundary_fetch`; did you mean `SM83.boundary-fetch`?"
        );
        let equation = rules.resolve_rewrite("plus-zero").unwrap_err();
        assert_eq!(
            equation.to_string(),
            "no rewrite rule has label `plus-zero`: `SM83.plus-zero` is a function equation, which a run applies without taking a step, so no step can stop at it"
        );
        assert!(matches!(
            rules.resolve_rewrite("missing").unwrap_err(),
            ExecError::UnknownRule {
                suggestion: None,
                sentence: None,
                ..
            }
        ));
    }

    /// A KRS item names every rewrite rule it lowers to, whatever their labels, and is refused
    /// where it lowers to none.
    #[test]
    fn a_stop_named_by_item_selects_every_rewrite_rule_of_the_item() {
        let rules = rules();
        // The item's equation takes no step and is left out.
        assert_eq!(
            rules.resolve_item("interrupt::boundary").unwrap(),
            ["r1", "r2"]
        );
        assert_eq!(
            rules.resolve_item("crate::interrupt::boundary").unwrap(),
            ["r1", "r2"]
        );
        assert_eq!(rules.resolve_item("crate::step").unwrap(), ["r3"]);
        let equations = rules.resolve_item("crate::fetch").unwrap_err();
        assert!(
            matches!(&equations, ExecError::UnknownItem { kinds, .. } if kinds == &[RuleKind::Equation, RuleKind::Simplification]),
            "{equations:?}"
        );
        assert_eq!(
            equations.to_string(),
            "no rewrite rule is written by KRS item `crate::fetch`: each of its sentences is a function equation or a simplification, which a run applies without taking a step, so no step can stop at it"
        );
        let missing = rules.resolve_item("ppu::frame_end").unwrap_err();
        assert!(
            matches!(&missing, ExecError::UnknownItem { kinds, .. } if kinds.is_empty()),
            "{missing:?}"
        );
    }

    /// `crate::` names an item of the root package alone, and a dependency's item is named by
    /// its crate name; a path both readings name an item at is ambiguous.
    #[test]
    fn a_stop_named_by_item_tells_the_packages_apart() {
        let rules = Rules::from_entries(
            "VM",
            [
                by(
                    rule("v1", Some("VM.step"), RuleKind::Rule),
                    "VM",
                    "vm",
                    "step",
                ),
                by(
                    rule("l1", Some("LANG.step"), RuleKind::Rule),
                    "LANG",
                    "lang",
                    "step",
                ),
                by(
                    rule("l2", Some("LANG.frame"), RuleKind::Rule),
                    "LANG",
                    "lang",
                    "ppu::frame",
                ),
                by(
                    rule("v2", Some("VM.local-step"), RuleKind::Rule),
                    "VM",
                    "vm",
                    "lang::step",
                ),
                by(
                    rule("o1", Some("OLD.frame"), RuleKind::Rule),
                    "OLD",
                    "lang",
                    "ppu::frame",
                ),
                by(
                    rule("o2", Some("OLD.tick"), RuleKind::Rule),
                    "OLD",
                    "lang",
                    "tick",
                ),
            ],
        );
        // The root's `step`, never the dependency's of the same path.
        assert_eq!(rules.resolve_item("crate::step").unwrap(), ["v1"]);
        assert_eq!(rules.resolve_item("crate::lang::step").unwrap(), ["v2"]);
        assert_eq!(rules.resolve_item("lang::tick").unwrap(), ["o2"]);
        // `lang::step` is the root's module `lang` and the crate `lang` at once.
        let ambiguous = rules.resolve_item("lang::step").unwrap_err();
        assert_eq!(
            ambiguous.to_string(),
            "KRS item `lang::step` is ambiguous: it names `lang::step` of the package of K namespace `LANG` and `crate::lang::step` of the package of K namespace `VM`; `crate::` names the root package's item alone, and a K label names one package's rule"
        );
        // Two packages of one crate name are told apart by label only.
        assert!(matches!(
            rules.resolve_item("lang::ppu::frame").unwrap_err(),
            ExecError::AmbiguousItem { matches, .. } if matches.len() == 2
        ));
        // A dependency's item is not the root's.
        assert!(matches!(
            rules.resolve_item("crate::tick").unwrap_err(),
            ExecError::UnknownItem { .. }
        ));
        // The name a stop prints selects the rule: the item where it names it alone, else the
        // label.
        assert_eq!(rules.stop_name("v1").as_deref(), Some("crate::step"));
        assert_eq!(rules.stop_name("o2").as_deref(), Some("lang::tick"));
        assert_eq!(rules.stop_name("l1").as_deref(), Some("LANG.step"));
        assert_eq!(rules.stop_name("o1").as_deref(), Some("OLD.frame"));
        // A root item's name written as a label is pointed at the item.
        let bare = Rules::from_entries(
            "VM",
            [by(
                rule("w1", Some("VM.work-amount-heat"), RuleKind::Rule),
                "VM",
                "vm",
                "work_amount",
            )],
        );
        assert_eq!(
            bare.resolve_rewrite("work_amount").unwrap_err().to_string(),
            "no rewrite rule has label `work_amount`; did you mean `crate::work_amount`?"
        );
    }

    /// A dependency's item is named by that crate's own name, its package name with `-` written
    /// `_`: a name a depending manifest renames the dependency to is no crate of the definition,
    /// and the refusal says so and names the item by the name that selects it.
    #[test]
    fn a_dependency_is_named_by_its_own_crate_name() {
        let rules = Rules::from_entries(
            "VM",
            [
                by(
                    rule("v1", Some("VM.tick"), RuleKind::Rule),
                    "VM",
                    "vm",
                    "tick",
                ),
                by(
                    rule("c1", Some("CORE.step"), RuleKind::Rule),
                    "CORE",
                    "gb_sm83_core",
                    "step",
                ),
            ],
        );
        assert_eq!(rules.resolve_item("gb_sm83_core::step").unwrap(), ["c1"]);
        // The root's `sm83-core = { package = "gb-sm83-core" }` names the crate `sm83_core` in
        // the root's source only.
        let renamed = rules.resolve_item("sm83_core::step").unwrap_err();
        assert!(
            matches!(&renamed, ExecError::UnknownItem { unknown_crate: Some(UnknownCrate::Unrecorded(krate)), suggestions, .. }
                if krate == "sm83_core" && suggestions == &["gb_sm83_core::step"]),
            "{renamed:?}"
        );
        assert_eq!(
            renamed.to_string(),
            "no rewrite rule is written by KRS item `sm83_core::step`: no sentence of the definition is the item's, and the definition records no package by the name `sm83_core`: a dependency's item is named by its Cargo package name with `-` written `_`, never by a name a depending package's manifest renames it to or a library name its `[lib]` section gives it; did you mean `gb_sm83_core::step`?"
        );
        // `crate::` names the root's items alone.
        let rooted = rules.resolve_item("crate::step").unwrap_err();
        assert!(
            matches!(&rooted, ExecError::UnknownItem { unknown_crate: None, suggestions, .. }
                if suggestions == &["gb_sm83_core::step"]),
            "{rooted:?}"
        );
        // The root's own crate name and `self` name the root package, whose items a stop names
        // `crate::`.
        for written in ["vm", "self"] {
            let refused = rules.resolve_item(&format!("{written}::tick")).unwrap_err();
            assert!(
                matches!(&refused, ExecError::UnknownItem { unknown_crate: Some(UnknownCrate::Root(name)), suggestions, .. }
                    if name == written && suggestions == &["crate::tick"]),
                "{written}: {refused:?}"
            );
            assert_eq!(
                refused.to_string(),
                format!(
                    "no rewrite rule is written by KRS item `{written}::tick`: no sentence of the definition is the item's, and `{written}` names the root package, whose items are named `crate::` and their path; did you mean `crate::tick`?"
                )
            );
        }
        // A dependency's crate name with a path it has no item at points at none.
        let missing = rules.resolve_item("gb_sm83_core::tock").unwrap_err();
        assert_eq!(
            missing.to_string(),
            "no rewrite rule is written by KRS item `gb_sm83_core::tock`: no sentence of the definition is the item's (an item is named by its Rust path: `crate::` and its path in the root package, or a dependency's own crate name and its path there)"
        );
    }

    /// A stopped end's class names the item with its package: two packages' items at one path
    /// are two classes, each named by a name a stop accepts that selects the item's rules alone,
    /// and every name of the item a stop accepts reads as that one class name.
    #[test]
    fn a_class_names_its_item_with_its_package() {
        let rules = Rules::from_entries(
            "VM",
            [
                by(
                    rule("v1", Some("VM.step"), RuleKind::Rule),
                    "VM",
                    "vm",
                    "step",
                ),
                by(
                    rule("l1", Some("LANG.step"), RuleKind::Rule),
                    "LANG",
                    "lang",
                    "step",
                ),
                by(
                    rule("l2", Some("LANG.frame"), RuleKind::Rule),
                    "LANG",
                    "lang",
                    "ppu::frame",
                ),
                by(
                    rule("v2", Some("VM.local-step"), RuleKind::Rule),
                    "VM",
                    "vm",
                    "lang::step",
                ),
                by(
                    rule("o1", Some("OLD.frame"), RuleKind::Rule),
                    "OLD",
                    "lang",
                    "ppu::frame",
                ),
                by(
                    rule("o2", Some("OLD.tick"), RuleKind::Rule),
                    "OLD",
                    "lang",
                    "tick",
                ),
                by(
                    rule("e1", Some("VM.tick-eq"), RuleKind::Equation),
                    "VM",
                    "vm",
                    "tick",
                ),
                rule("n1", Some("VM.unwritten"), RuleKind::Rule),
                by(
                    rule("s1", Some("VM.shared"), RuleKind::Rule),
                    "VM",
                    "vm",
                    "a",
                ),
                by(
                    rule("s2", Some("VM.shared"), RuleKind::Rule),
                    "VM",
                    "vm",
                    "b",
                ),
            ],
        );
        // An item its spelling names alone is named by it, with `crate::` for the root's.
        assert_eq!(rules.class_name("v1").as_deref(), Some("crate::step"));
        assert_eq!(rules.class_name("v2").as_deref(), Some("crate::lang::step"));
        assert_eq!(rules.class_name("o2").as_deref(), Some("lang::tick"));
        // `lang::step` also names the root's `crate::lang::step`, and `lang::ppu::frame` the
        // items of two packages of crate name `lang`: each is named by its label.
        assert_eq!(rules.class_name("l1").as_deref(), Some("LANG.step"));
        assert_eq!(rules.class_name("l2").as_deref(), Some("LANG.frame"));
        assert_eq!(rules.class_name("o1").as_deref(), Some("OLD.frame"));
        // No class names an equation or a rule no item wrote.
        assert_eq!(rules.class_name("e1"), None);
        assert_eq!(rules.class_name("n1"), None);
        // Every name of an item a stop accepts reads as its class name.
        assert_eq!(rules.stop_item("crate::step").unwrap(), "crate::step");
        assert_eq!(rules.stop_item("VM.step").unwrap(), "crate::step");
        assert_eq!(rules.stop_item("OLD.tick").unwrap(), "lang::tick");
        assert_eq!(rules.stop_item("lang::tick").unwrap(), "lang::tick");
        assert_eq!(rules.stop_item("LANG.step").unwrap(), "LANG.step");
        assert_eq!(rules.stop_item("local-step").unwrap(), "crate::lang::step");
        // A name that selects no one item is refused, as an ambiguous stop is.
        assert!(rules.stop_item("lang::step").is_err());
        assert!(rules.stop_item("frame").is_err());
        assert_eq!(rules.class_name("s1").as_deref(), Some("crate::a"));
        assert_eq!(
            rules.stop_item("VM.shared").unwrap_err(),
            "`VM.shared` selects the rules of several KRS items (`crate::a`, `crate::b`), and a stopped end's class is one; name one of them"
        );
        assert_eq!(
            rules.stop_item("VM.unwritten").unwrap_err(),
            "`VM.unwritten` selects a rewrite rule no KRS item wrote, so no stopped end's class names it"
        );
        // A root item is also read without `crate::`, as Rust reads a path at the crate root.
        let rules = self::rules();
        assert_eq!(
            rules.stop_item("interrupt::boundary").unwrap(),
            "crate::interrupt::boundary"
        );
        assert_eq!(
            rules.stop_item("boundary-halted").unwrap(),
            "crate::interrupt::boundary"
        );
    }

    /// An exact label names its own sentence, never a rewrite rule whose label ends with it.
    #[test]
    fn an_exact_label_wins_and_is_refused_when_it_names_no_rewrite_rule() {
        let rules = rules();
        let exact = rules.resolve_rewrite("fetch").unwrap_err();
        assert!(
            matches!(
                &exact,
                ExecError::UnknownRule { sentence: Some((label, RuleKind::Equation)), .. }
                    if label == "fetch"
            ),
            "{exact:?}"
        );
        assert_eq!(rules.resolve_rewrite("SM83.fetch").unwrap(), ["r7"]);
        // A suffix that a simplification's label and a rewrite rule's label end with is
        // ambiguous, and the refusal of a simplification says what it is.
        assert!(matches!(
            rules.resolve_rewrite("lemma").unwrap_err(),
            ExecError::AmbiguousRule { .. }
        ));
        assert_eq!(
            rules.resolve_rewrite("SM83.lemma").unwrap_err().to_string(),
            "no rewrite rule has label `SM83.lemma`: `SM83.lemma` is a simplification, which a run applies without taking a step, so no step can stop at it"
        );
    }
}
