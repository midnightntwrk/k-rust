//! What a definition states about the totality of each of its functions, and the list of the
//! totalities it takes on the author's word.
//!
//! A function declared `total` is stated to have a value at every argument, and every reader of
//! the definition uses that statement: a prover asks no definedness of an application of the
//! function, and a solver is told the application is some value of its sort.
//! How far the statement was established differs from function to function, and the emitted K
//! does not say: `[function, total]` is the same text in each case.
//! [`Totality`] is that missing fact, read from the production the Definition IR holds:
//!
//! - `checked`: the function is declared `total` and the definition's equations define it.
//!   The definition was compiled, so each of its equations' results was shown to have a value
//!   wherever the equation applies (`krs::analysis::total-without-value` otherwise).
//!   The check takes each function a result applies at its own declaration and does not judge
//!   recursion, so `checked` is totality given the callees' declarations and termination.
//!   A function with no equation is `checked` too: no equation contradicts the declaration, and
//!   each application has a value the definition does not name;
//! - `assumed`: the function is declared `total, assumed = "reason"`.
//!   Its equations' results were not judged, and its totality is a premise of everything that
//!   uses it;
//! - `hooked`: the function is declared `total` and a hook or an SMT hook defines it, so its
//!   totality is a statement about the operation the hook names, which KRS does not check here;
//! - `partial`: the function is not declared `total`, and an application of it may have no value.
//!
//! [`assumed_totals`] lists the `assumed` functions of a definition, which are its unchecked
//! premises of this kind.
//! The list is of the definition, not of one proof: it names every such premise the definition
//! holds, whichever of them a given proof uses.
//!
//! `symbols.json` carries the same fact on each function's row ([`crate::SymbolMapEntry::totality`]),
//! so the list and the rows are two readings of one attribute of the production and cannot
//! disagree.

use krs_ir::ProductionAttribute;
use krs_ir_levels::{DefinitionIr, DefinitionSentence, ProductionSentence};
use serde::{Deserialize, Serialize};

/// What a definition states about the totality of one function (the module documentation).
///
/// Its JSON is an object whose `state` is the variant's name in lower case; `assumed` carries
/// the `reason` as written.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(tag = "state", rename_all = "snake_case", deny_unknown_fields)]
pub enum Totality {
    /// Declared `total` and defined by the definition's equations, whose results were checked.
    Checked,
    /// Declared `total, assumed = ".."`: total on the author's word, and not checked.
    Assumed {
        /// Why the function is total, as written.
        reason: String,
    },
    /// Declared `total` and defined by a hook or an SMT hook, which KRS does not check here.
    Hooked,
    /// Not declared `total`.
    Partial,
}

impl Totality {
    /// The totality `production` states, or `None` where it is no function.
    #[must_use]
    pub fn of(production: &ProductionSentence) -> Option<Self> {
        let attributes = production.attributes();
        let has = |test: fn(&krs_ir_levels::DefinitionProductionAttribute) -> bool| {
            attributes.iter().any(test)
        };
        if !has(|attribute| matches!(attribute, ProductionAttribute::Function { .. })) {
            return None;
        }
        if !has(|attribute| matches!(attribute, ProductionAttribute::Total { .. })) {
            return Some(Self::Partial);
        }
        if let Some(reason) = attributes.iter().find_map(|attribute| match attribute {
            ProductionAttribute::Assumed { reason, .. } => Some(reason),
            _ => None,
        }) {
            return Some(Self::Assumed {
                reason: reason.clone(),
            });
        }
        // The same three attributes exclude a function from the check of its equations' results
        // (`crate::coverage::checked`): nothing in the definition defines such a function.
        Some(
            if has(|attribute| {
                matches!(
                    attribute,
                    ProductionAttribute::Hook { .. }
                        | ProductionAttribute::RawHook { .. }
                        | ProductionAttribute::SmtHook { .. }
                )
            }) {
                Self::Hooked
            } else {
                Self::Checked
            },
        )
    }

    /// The state's name, as `symbols.json` writes it.
    #[must_use]
    pub const fn state(&self) -> &'static str {
        match self {
            Self::Checked => "checked",
            Self::Assumed { .. } => "assumed",
            Self::Hooked => "hooked",
            Self::Partial => "partial",
        }
    }
}

/// One function whose totality a definition takes on the author's word.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AssumedTotal {
    /// The function's item path as a KRS document names it: `crate`, or the crate name of
    /// another package's library, then the modules and the item (`crate::memory::At9`).
    pub item: String,
    /// The Cargo name of the package that declares the function.
    pub package: String,
    /// The modules below the package's root that hold the function.
    pub module: Vec<String>,
    /// The function's name; a variant's is qualified by its enum (`Reads::At9`).
    pub name: String,
    /// The Definition IR identity of the function's production, which is the `identity` of its
    /// row in `symbols.json`.
    pub production: String,
    /// The function's K symbol.
    pub label: String,
    /// Why the function is total, as written.
    pub reason: String,
    /// The package-relative file and the byte range in it of the function's name in its
    /// declaration, which is the authored range of its production, where the definition records
    /// one.
    pub origin: Option<(String, u32, u32)>,
}

/// The functions whose totality `definition` takes on the author's word, ordered by declaring
/// package, module, name and production identity.
#[must_use]
pub fn assumed_totals(definition: &DefinitionIr) -> Vec<AssumedTotal> {
    let mut assumed = definition
        .modules()
        .iter()
        .flat_map(krs_ir_levels::DefinitionModule::sentences)
        .filter_map(|sentence| {
            let DefinitionSentence::Production(production) = sentence else {
                return None;
            };
            let Some(Totality::Assumed { reason }) = Totality::of(production) else {
                return None;
            };
            // `assumed` is written on an authored function, whose production names its item.
            let item = sentence.item()?;
            let name = crate::coverage::display_name(item);
            let root = if item.package().k_namespace() == definition.main_module().as_str() {
                "crate".to_owned()
            } else {
                definition.crate_name(item.package())
            };
            Some(AssumedTotal {
                item: std::iter::once(root)
                    .chain(item.module_path().iter().cloned())
                    .chain([name.clone()])
                    .collect::<Vec<_>>()
                    .join("::"),
                package: item.package().cargo_name().to_owned(),
                module: item.module_path().to_vec(),
                name,
                production: production.symbol().id().as_str().to_owned(),
                label: production.symbol().emitted_name().to_owned(),
                reason,
                origin: production
                    .origin()
                    .origin()
                    .exact_authored_range()
                    .map(|range| {
                        (
                            range.file.package_relative_path().to_owned(),
                            range.start_byte,
                            range.end_byte,
                        )
                    }),
            })
        })
        .collect::<Vec<_>>();
    assumed.sort_by(|left, right| {
        (&left.package, &left.module, &left.name, &left.production).cmp(&(
            &right.package,
            &right.module,
            &right.name,
            &right.production,
        ))
    });
    assumed
}

#[cfg(test)]
mod tests {
    use krs_ir::testing::origin;
    use krs_ir_levels::{
        DefinitionProductionAttribute, DefinitionSortRef, ProductionItem, SymbolId, SymbolIdentity,
        SymbolKind,
    };

    use super::*;

    /// A production `name()` of sort `Int` with `attributes`.
    fn production(attributes: Vec<DefinitionProductionAttribute>) -> ProductionSentence {
        ProductionSentence::new(
            origin("production"),
            SymbolIdentity::new(
                SymbolId::new("production.f").unwrap(),
                "f",
                SymbolKind::Production,
            )
            .unwrap(),
            DefinitionSortRef::Builtin(krs_ir::BuiltinSort::Int),
            vec![ProductionItem::terminal(origin("terminal"), "f()").unwrap()],
            attributes,
        )
        .unwrap()
    }

    fn function() -> DefinitionProductionAttribute {
        ProductionAttribute::Function {
            origin: origin("function"),
        }
    }

    fn total() -> DefinitionProductionAttribute {
        ProductionAttribute::Total {
            origin: origin("total"),
        }
    }

    fn assumed(reason: &str) -> DefinitionProductionAttribute {
        ProductionAttribute::Assumed {
            origin: origin("assumed"),
            reason: reason.to_owned(),
        }
    }

    fn raw_hook() -> DefinitionProductionAttribute {
        ProductionAttribute::RawHook {
            origin: origin("hook"),
            namespace: "INT".to_owned(),
            name: "zero".to_owned(),
        }
    }

    #[test]
    fn a_production_states_its_totality_by_its_attributes() {
        // A constructor is no function, so it states none.
        assert_eq!(Totality::of(&production(vec![])), None);
        assert_eq!(
            Totality::of(&production(vec![function()])),
            Some(Totality::Partial)
        );
        assert_eq!(
            Totality::of(&production(vec![function(), total()])),
            Some(Totality::Checked)
        );
        assert_eq!(
            Totality::of(&production(vec![function(), total(), assumed("by range")])),
            Some(Totality::Assumed {
                reason: "by range".to_owned()
            })
        );
        // A hook defines the function, so no equation's result was there to check.
        assert_eq!(
            Totality::of(&production(vec![function(), total(), raw_hook()])),
            Some(Totality::Hooked)
        );
        // The author's word is what an assumed function rests on, a hook or not.
        assert_eq!(
            Totality::of(&production(vec![
                function(),
                total(),
                raw_hook(),
                assumed("the hook is total")
            ])),
            Some(Totality::Assumed {
                reason: "the hook is total".to_owned()
            })
        );
    }

    #[test]
    fn a_totality_is_written_as_its_state_and_an_assumed_one_with_its_reason() {
        for (totality, json) in [
            (Totality::Checked, serde_json::json!({"state": "checked"})),
            (Totality::Hooked, serde_json::json!({"state": "hooked"})),
            (Totality::Partial, serde_json::json!({"state": "partial"})),
            (
                Totality::Assumed {
                    reason: "by range".to_owned(),
                },
                serde_json::json!({"state": "assumed", "reason": "by range"}),
            ),
        ] {
            assert_eq!(serde_json::to_value(&totality).unwrap(), json);
            assert_eq!(json["state"], totality.state());
            assert_eq!(serde_json::from_value::<Totality>(json).unwrap(), totality);
        }
        // An assumed totality without its reason, and a state this version does not know, are
        // no totality.
        for refused in [
            serde_json::json!({"state": "assumed"}),
            serde_json::json!({"state": "underspecified"}),
            serde_json::json!("checked"),
        ] {
            assert!(serde_json::from_value::<Totality>(refused).is_err());
        }
    }
}
