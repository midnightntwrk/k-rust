//! Which declarations may serve a collection sort as its unit, element or concatenation symbol; a
//! responsibility, not an algorithm; no counter of its own, no worklist.
//!
//! A collection sort `C` hooked `LIST.List`, `SET.Set` or `MAP.Map` names its unit, element and
//! concatenation symbols in its `unit`, `element` and `concat` attributes, and says that the
//! values of `C` are the finite sequences (sets, finite maps) those symbols build. The backend
//! builds every application of one of them as a value of `C` (`Term::application`), whose sort
//! is `C`. The symbol's own declaration also fixes the sort of its applications and of their
//! arguments, and KORE has no implicit subsorting. A declaration that disagrees with its role
//! gives a role application two sorts, and no reading of the definition satisfies both, so the
//! definition is refused rather than repaired ([`misfit`]):
//!
//! - R1: the symbol has no sort parameters. The attribute names one symbol of `C`, which has no
//!   sort parameters, and a role application is written without sort arguments.
//! - R2: its result sort is exactly `C`. Another sort, even a subsort or supersort of `C`, would
//!   hold a value of `C` without an injection.
//! - R3: the unit takes no argument; the element takes one argument (list, set) or two (map's key
//!   and value); the concatenation takes two arguments, each exactly `C`, since each operand
//!   becomes part of a value of `C`.
//! - R4: its hook, if it has one, is the role's own (`LIST.unit`, `LIST.element`, `LIST.concat`,
//!   and their `SET` and `MAP` twins). The backend implements a role only by its own theory, so
//!   another hook asks for a theory that would not be evaluated: `SET.union` on a set's
//!   concatenation states an idempotent union where the backend builds a concatenation that is
//!   undefined on a shared element.
//!
//! A role symbol needs no hook: the collection sort's attributes alone fix what it builds. The
//! rule compares sorts for equality only, so it is stated over any sort type: the frontend
//! decides a production with it in the definition's own sorts before it emits KORE, and the
//! loader decides KORE from any producer the same way. The element's argument sorts are the
//! collection's element (key, value) sorts by definition; that they are closed is checked where
//! the collection is built.

use std::fmt;

/// The collections whose sorts name role symbols.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CollectionKind {
    List,
    Set,
    Map,
}

impl CollectionKind {
    /// The kind of a collection sort hooked `hook`, if `hook` is a collection sort's hook.
    pub fn of_sort_hook(hook: &str) -> Option<Self> {
        match hook {
            "LIST.List" => Some(Self::List),
            "SET.Set" => Some(Self::Set),
            "MAP.Map" => Some(Self::Map),
            _ => None,
        }
    }

    /// The namespace of the kind's hooks.
    pub const fn namespace(self) -> &'static str {
        match self {
            Self::List => "LIST",
            Self::Set => "SET",
            Self::Map => "MAP",
        }
    }

    const fn noun(self) -> &'static str {
        match self {
            Self::List => "list",
            Self::Set => "set",
            Self::Map => "map",
        }
    }

    /// The number of arguments of the kind's element symbol: an element, or a key and a value.
    pub const fn element_arity(self) -> usize {
        match self {
            Self::List | Self::Set => 1,
            Self::Map => 2,
        }
    }
}

/// The role a symbol plays for a collection sort, as the sort's attribute of that name says.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CollectionRole {
    Unit,
    Element,
    Concat,
}

impl CollectionRole {
    /// The roles in the order they are checked.
    pub const ALL: [Self; 3] = [Self::Unit, Self::Element, Self::Concat];

    /// The name of the role's attribute, which is also the operation of the role's hook.
    pub const fn name(self) -> &'static str {
        match self {
            Self::Unit => "unit",
            Self::Element => "element",
            Self::Concat => "concat",
        }
    }
}

impl fmt::Display for CollectionRole {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.name())
    }
}

/// The declaration of a symbol named as a collection role, in the sorts of the definition at
/// hand.
#[derive(Clone, Copy, Debug)]
pub struct RoleDeclaration<'a, S> {
    /// The number of the symbol's sort parameters.
    pub sort_parameters: usize,
    pub argument_sorts: &'a [S],
    pub result_sort: &'a S,
    pub hook: Option<&'a str>,
}

/// Why `declaration` cannot be the `role` symbol of the `kind` collection sort `collection`, or
/// `None` when it has the role's signature (R1-R4 of the module documentation). The reason
/// continues a sentence whose subject is the symbol ("has result sort Foo, ..."); `render`
/// writes a sort as the reason names it.
pub fn misfit<S: PartialEq>(
    kind: CollectionKind,
    role: CollectionRole,
    collection: &S,
    declaration: &RoleDeclaration<'_, S>,
    render: impl Fn(&S) -> String,
) -> Option<String> {
    if declaration.sort_parameters != 0 {
        return Some(format!(
            "has {} sort {}, but a collection's {role} symbol has none",
            declaration.sort_parameters,
            plural(declaration.sort_parameters, "parameter", "parameters"),
        ));
    }
    if declaration.result_sort != collection {
        return Some(format!(
            "has result sort {}, not the collection sort {}",
            render(declaration.result_sort),
            render(collection)
        ));
    }
    let arity = match role {
        CollectionRole::Unit => 0,
        CollectionRole::Element => kind.element_arity(),
        CollectionRole::Concat => 2,
    };
    let arguments = declaration.argument_sorts.len();
    if arguments != arity {
        return Some(format!(
            "takes {arguments} {}, but a {} {role} symbol takes {arity}",
            plural(arguments, "argument", "arguments"),
            kind.noun(),
        ));
    }
    if role == CollectionRole::Concat
        && let Some((index, operand)) = declaration
            .argument_sorts
            .iter()
            .enumerate()
            .find(|(_, operand)| *operand != collection)
    {
        return Some(format!(
            "has argument {} of sort {}, not the collection sort {}",
            index + 1,
            render(operand),
            render(collection)
        ));
    }
    let own = format!("{}.{}", kind.namespace(), role.name());
    if let Some(hook) = declaration.hook
        && hook != own
    {
        return Some(format!(
            "is hooked {hook}, but a {} {role} symbol carries no hook or {own}",
            kind.noun()
        ));
    }
    None
}

const fn plural(count: usize, one: &'static str, many: &'static str) -> &'static str {
    if count == 1 { one } else { many }
}

#[cfg(test)]
mod tests {
    use super::{CollectionKind, CollectionRole, RoleDeclaration, misfit};

    fn decide(
        kind: CollectionKind,
        role: CollectionRole,
        sort_parameters: usize,
        argument_sorts: &[&str],
        result_sort: &str,
        hook: Option<&str>,
    ) -> Option<String> {
        misfit(
            kind,
            role,
            &"C",
            &RoleDeclaration {
                sort_parameters,
                argument_sorts,
                result_sort: &result_sort,
                hook,
            },
            |sort| (*sort).to_owned(),
        )
    }

    #[test]
    fn the_roles_own_signatures_fit_with_or_without_their_hooks() {
        use CollectionKind::{List, Map, Set};
        use CollectionRole::{Concat, Element, Unit};
        for kind in [List, Set, Map] {
            let element: &[&str] = if kind == Map { &["K", "V"] } else { &["E"] };
            for (role, arguments) in [(Unit, &[][..]), (Element, element), (Concat, &["C", "C"])] {
                let own = format!("{}.{}", kind.namespace(), role.name());
                for hook in [None, Some(own.as_str())] {
                    assert_eq!(
                        decide(kind, role, 0, arguments, "C", hook),
                        None,
                        "{kind:?} {role} {hook:?}"
                    );
                }
            }
        }
    }

    #[test]
    fn each_rule_names_its_misfit() {
        use CollectionKind::{List, Map, Set};
        use CollectionRole::{Concat, Element, Unit};
        let cases = [
            (
                decide(List, Element, 1, &["E"], "C", None),
                "has 1 sort parameter, but a collection's element symbol has none",
            ),
            (
                decide(List, Element, 0, &["E"], "Foo", None),
                "has result sort Foo, not the collection sort C",
            ),
            (
                decide(List, Unit, 0, &["E"], "C", None),
                "takes 1 argument, but a list unit symbol takes 0",
            ),
            (
                decide(Map, Element, 0, &["K"], "C", None),
                "takes 1 argument, but a map element symbol takes 2",
            ),
            (
                decide(Set, Concat, 0, &["C"], "C", None),
                "takes 1 argument, but a set concat symbol takes 2",
            ),
            (
                decide(List, Concat, 0, &["C", "Int"], "C", None),
                "has argument 2 of sort Int, not the collection sort C",
            ),
            (
                decide(Set, Concat, 0, &["C", "C"], "C", Some("SET.union")),
                "is hooked SET.union, but a set concat symbol carries no hook or SET.concat",
            ),
            (
                decide(Map, Concat, 0, &["C", "C"], "C", Some("MAP.updateAll")),
                "is hooked MAP.updateAll, but a map concat symbol carries no hook or MAP.concat",
            ),
            (
                decide(Set, Element, 0, &["E"], "C", Some("LIST.element")),
                "is hooked LIST.element, but a set element symbol carries no hook or SET.element",
            ),
        ];
        for (reason, expected) in cases {
            assert_eq!(reason.as_deref(), Some(expected));
        }
    }
}
