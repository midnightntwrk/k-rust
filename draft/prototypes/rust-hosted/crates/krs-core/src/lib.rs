//! Disposable proof of a real-Rust host for KRS declarations.

use std::collections::{BTreeMap, BTreeSet};
use std::marker::PhantomData;

pub use inventory;
pub use krs_macros::{cells, constructor, ml, rule, sort, term};

/// A type-shaped annotation used only in authored rule signatures.
///
/// `#[rule]` consumes those signatures before rustc type checks their patterns;
/// KRS, rather than Rust's trait solver, assigns their semantic types.
pub struct Term<S: ?Sized>(PhantomData<fn() -> S>);

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Origin {
    pub package: &'static str,
    pub module: &'static str,
    pub item: &'static str,
    pub file: &'static str,
    pub line: u32,
    pub column: u32,
}

impl Origin {
    pub fn stable_path(&self) -> String {
        format!("{}::{}::{}", self.package, self.module, self.item)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SortDescriptor {
    pub name: &'static str,
    pub parents: &'static [&'static str],
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ConstructorDescriptor {
    pub name: &'static str,
    pub sort: &'static str,
    pub syntax: &'static str,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RuleDescriptor {
    pub name: &'static str,
    pub parameter_pattern: &'static str,
    pub parameter_type: &'static str,
    pub result_type: &'static str,
    pub body: &'static str,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Descriptor {
    Sort(SortDescriptor),
    Constructor(ConstructorDescriptor),
    Rule(RuleDescriptor),
}

impl Descriptor {
    fn kind_rank(self) -> u8 {
        match self {
            Self::Sort(_) => 0,
            Self::Constructor(_) => 1,
            Self::Rule(_) => 2,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Registration {
    pub origin: Origin,
    pub descriptor: Descriptor,
}

inventory::collect!(Registration);

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Definition {
    pub registrations: Vec<Registration>,
}

impl Definition {
    pub fn collect() -> Self {
        let mut registrations: Vec<_> = inventory::iter::<Registration>
            .into_iter()
            .copied()
            .collect();
        registrations.sort_by_key(|registration| {
            (
                registration.origin.stable_path(),
                registration.descriptor.kind_rank(),
            )
        });
        Self { registrations }
    }

    pub fn analyze(self) -> Result<AnalyzedDefinition, Vec<String>> {
        let mut errors = Vec::new();
        let mut parents: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();

        for registration in &self.registrations {
            if let Descriptor::Sort(sort) = registration.descriptor {
                if parents.contains_key(sort.name) {
                    errors.push(format!("duplicate sort `{}`", sort.name));
                    continue;
                }
                parents.insert(
                    sort.name.to_owned(),
                    sort.parents.iter().map(|parent| (*parent).to_owned()).collect(),
                );
            }
        }

        for registration in &self.registrations {
            match registration.descriptor {
                Descriptor::Sort(sort) => {
                    for parent in sort.parents {
                        if !parents.contains_key(*parent) {
                            errors.push(format!(
                                "sort `{}` has undeclared parent `{parent}`",
                                sort.name
                            ));
                        }
                    }
                }
                Descriptor::Constructor(constructor) => {
                    if !parents.contains_key(constructor.sort) {
                        errors.push(format!(
                            "constructor `{}` has undeclared result sort `{}`",
                            constructor.name, constructor.sort
                        ));
                    }
                }
                Descriptor::Rule(_) => {}
            }
        }

        let mut closure = BTreeMap::new();
        for sort in parents.keys() {
            let mut ancestors = BTreeSet::new();
            let mut pending = vec![sort.clone()];
            while let Some(current) = pending.pop() {
                if !ancestors.insert(current.clone()) {
                    continue;
                }
                if let Some(direct) = parents.get(&current) {
                    pending.extend(direct.iter().cloned());
                }
            }
            closure.insert(sort.clone(), ancestors);
        }

        if errors.is_empty() {
            Ok(AnalyzedDefinition {
                definition: self,
                subsort_closure: closure,
            })
        } else {
            Err(errors)
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AnalyzedDefinition {
    pub definition: Definition,
    /// Maps a sort to itself and every transitive supersort, exactly once.
    pub subsort_closure: BTreeMap<String, BTreeSet<String>>,
}

impl AnalyzedDefinition {
    pub fn is_subsort(&self, child: &str, parent: &str) -> bool {
        self.subsort_closure
            .get(child)
            .is_some_and(|ancestors| ancestors.contains(parent))
    }

    pub fn stable_paths(&self) -> Vec<String> {
        self.definition
            .registrations
            .iter()
            .map(|registration| registration.origin.stable_path())
            .collect()
    }
}

#[cfg(feature = "native")]
pub mod native;

