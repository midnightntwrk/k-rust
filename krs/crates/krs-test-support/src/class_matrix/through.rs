//! The indirection dimension: a term case's construct `S` written again through a local,
//! `{ let y = S; y }`, at the positions where a block stands ([`Family::TermsLocal`],
//! [`Family::NotationLocal`]).
//!
//! A local names the value its pattern matched (`docs-site/src/pages/reference/language.mdx`,
//! "A local names the value its pattern matched"): the pattern `y` matches every value, so
//! `{ let y = S; y }` denotes what `S` denotes where it stands. A case through a local (its *derived*
//! case) is therefore expected exactly what its *direct* case, the same slot and construct
//! without the block, is expected ([`super::table`]): accepted where the direct case is, with the
//! direct case's K through the block, and refused where it is, with its class, inside `S` (the
//! derived case's spelling is `S`, its entry the block).
//!
//! Where it holds is a fact of the position and the construct, stated by the generator
//! (`terms::through`), never by table entries: where a block itself stands. A pattern holds no
//! block (`let-outside-term`), and neither does a constant's ground value; a key a pattern
//! computes reads two ways, and a block there fixes the lookup where `S` may select; and a
//! matching-logic predicate at a condition is a formula, where the block's result is an object
//! term.
//!
//! **The K.** K defines `#let P = A #in B` as `#fun(P => B)(A)`, so `( #let Y:S = T #in Y:S )`,
//! whose pattern is a variable read nowhere else, is `T` wherever `T` has the sort `S`, which the
//! lowering gives the local from its value. A derived case's K, with that one block read as its
//! value ([`reductions`]), is the direct case's K: K3 compares them ([`Through::reduced`]). Where
//! it does, the derived case needs no K6 or K7 of its own: both judge K, and the direct case's
//! K6 and K7 judge that one, while the `{ let y = x; y }` spelling at every slot shows that an
//! identity block runs as its value. So the full tier judges a derived case whose K is compared
//! by K1 to K3 alone, and its K7 plan is a skip.
//!
//! Where the derived case's K differs from its direct case's by more than the block, it means
//! the same with other K: where KRS writes a block as the application of a function it lifts (a
//! claim's states and conditions, a static clause's result), the lifted function, its
//! declaration and its application where the block stood; where the lowering reads the direct
//! construct by its spelling around it (a projection's sort test hoisted into the sentence's
//! condition, a framed map result's key compared with the key its subject matched). There
//! [`Through::differs`] says why, and the derived case is judged in full instead: K6, and K7 by
//! its direct case's plans, since it denotes the same value.

use super::Family;

/// What a case through a local ([`super::Case::through`]) is judged by.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Through {
    /// The direct case: the same slot and construct, without the block.
    pub direct: String,
    /// Why the derived case's K is not the direct case's through the block, where it is not
    /// (KRS lifts the block into a function, or lowers the direct construct by its spelling
    /// around it): the full tier judges the case in full (K6, K7). `None` where it is: K3
    /// compares the derived case's K, read through the block, with the direct case's, and K6
    /// and K7 do not judge the case.
    pub differs: Option<&'static str>,
}

impl Through {
    /// Whether the full tier compares the case's K, read through the block, with its direct
    /// case's, and judges it by K1 to K3 alone.
    #[must_use]
    pub const fn reduced(&self) -> bool {
        self.differs.is_none()
    }
}

/// The ID of the direct case of the case `id` through a local: the same slot and construct in
/// the family [`Family::direct`] names, `terms/rule/result/x + 1` of `terms-local/rule/result/x +
/// 1`. `None` for a case of another family.
#[must_use]
pub fn direct(id: &str) -> Option<String> {
    Family::ALL.into_iter().find_map(|family| {
        let direct = family.direct()?;
        let rest = id.strip_prefix(family.name())?.strip_prefix('/')?;
        Some(format!("{}/{rest}", direct.name()))
    })
}

/// The K sentences `additions`, of a derived case written in place, with its block read as its
/// value: in the first sentence that holds one, the leftmost block `( #let Y:S = T #in Y:S )`
/// whose variable `Y` occurs nowhere else in its sentence is replaced by `T`, and again by
/// `( T )` and `(T)`, since where the block stood parenthesized the direct case may write `T`
/// with or without its own parentheses, which group and denote nothing. The block the derived case adds encloses every block `S` holds,
/// so it is the leftmost of them. Empty where no sentence holds such a block.
#[must_use]
pub fn reductions(additions: &[String]) -> Vec<Vec<String>> {
    for (index, sentence) in additions.iter().enumerate() {
        if let Some((range, value)) = identity_block(sentence) {
            return [
                value.to_owned(),
                format!("( {value} )"),
                format!("({value})"),
            ]
            .into_iter()
            .map(|replacement| {
                let mut reduced = additions.to_vec();
                reduced[index] = format!(
                    "{}{replacement}{}",
                    &sentence[..range.start],
                    &sentence[range.end..]
                );
                reduced
            })
            .collect();
        }
    }
    Vec::new()
}

/// The leftmost block `( #let Y:S = T #in Y:S )` of `sentence` whose variable occurs nowhere
/// else in it: its range and `T`.
fn identity_block(sentence: &str) -> Option<(std::ops::Range<usize>, &str)> {
    const OPEN: &str = "( #let ";
    let mut from = 0;
    while let Some(found) = sentence[from..].find(OPEN) {
        let start = from + found;
        from = start + OPEN.len();
        let rest = &sentence[from..];
        let Some((variable, _)) = rest.split_once(" = ") else {
            continue;
        };
        let Some((name, sort)) = variable.split_once(':') else {
            continue;
        };
        let named = name
            .chars()
            .next()
            .is_some_and(|first| first.is_uppercase() || first == '_')
            && name != "_"
            && !sort.is_empty()
            && !variable.contains(char::is_whitespace);
        if !named {
            continue;
        }
        let value_start = from + variable.len() + " = ".len();
        let close = format!(" #in {variable} )");
        let Some(value_end) = balanced_until(sentence, value_start, &close) else {
            continue;
        };
        if occurrences(sentence, name) != 2 {
            continue;
        }
        return Some((
            start..value_end + close.len(),
            &sentence[value_start..value_end],
        ));
    }
    None
}

/// The first index from `start` where `text` continues with `close` outside every parenthesis
/// opened after `start` and every string literal, before a parenthesis closes that was opened
/// before it.
fn balanced_until(text: &str, start: usize, close: &str) -> Option<usize> {
    let mut depth = 0usize;
    let mut quoted = false;
    let mut escaped = false;
    for (offset, character) in text[start..].char_indices() {
        let index = start + offset;
        if quoted {
            match (escaped, character) {
                (true, _) => escaped = false,
                (false, '\\') => escaped = true,
                (false, '"') => quoted = false,
                _ => {}
            }
            continue;
        }
        if depth == 0 && text[index..].starts_with(close) {
            return Some(index);
        }
        match character {
            '"' => quoted = true,
            '(' => depth += 1,
            ')' if depth == 0 => return None,
            ')' => depth -= 1,
            _ => {}
        }
    }
    None
}

/// How often the identifier `name` occurs in `sentence` as a whole word.
fn occurrences(sentence: &str, name: &str) -> usize {
    sentence
        .split(|character: char| {
            !(character.is_alphanumeric() || character == '_' || character == '\'')
        })
        .filter(|word| *word == name)
        .count()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sentences(text: &[&str]) -> Vec<String> {
        text.iter().map(|sentence| (*sentence).to_owned()).collect()
    }

    #[test]
    fn the_block_a_derived_case_adds_reads_as_its_value() {
        let derived = sentences(&[
            "rule <k> cTAG ( X:KItem , _ ) => hold ( ( #let Y:KItem = X:KItem +Int 1 #in Y:KItem ) ) ... </k>",
            "syntax Stmt ::= \"cTAG\"",
        ]);
        assert_eq!(
            reductions(&derived),
            vec![
                sentences(&[
                    "rule <k> cTAG ( X:KItem , _ ) => hold ( X:KItem +Int 1 ) ... </k>",
                    "syntax Stmt ::= \"cTAG\"",
                ]),
                sentences(&[
                    "rule <k> cTAG ( X:KItem , _ ) => hold ( ( X:KItem +Int 1 ) ) ... </k>",
                    "syntax Stmt ::= \"cTAG\"",
                ]),
                sentences(&[
                    "rule <k> cTAG ( X:KItem , _ ) => hold ( (X:KItem +Int 1) ) ... </k>",
                    "syntax Stmt ::= \"cTAG\"",
                ]),
            ]
        );
    }

    #[test]
    fn only_the_outermost_identity_block_is_read_and_a_string_does_not_close_it() {
        let derived = sentences(&[
            "rule f ( X:KItem ) => ( #let Y:KItem = ( #let Z:KItem = pair ( X:KItem , \")\" ) #in Z:KItem ) #in Y:KItem )",
        ]);
        assert_eq!(
            reductions(&derived)[0],
            sentences(&[
                "rule f ( X:KItem ) => ( #let Z:KItem = pair ( X:KItem , \")\" ) #in Z:KItem )"
            ])
        );
    }

    #[test]
    fn a_block_whose_variable_is_read_elsewhere_or_whose_pattern_is_no_variable_is_no_identity() {
        let read_elsewhere = sentences(&[
            "rule f ( X:KItem ) => pair ( ( #let Y:KItem = X:KItem #in Y:KItem ) , Y:KItem )",
        ]);
        assert!(reductions(&read_elsewhere).is_empty());
        let pattern = sentences(&[
            "rule f ( X:KItem ) => ( #let pair ( _ , Y:KItem ) = X:KItem #in pair ( 1 , Y:KItem ) )",
        ]);
        assert!(reductions(&pattern).is_empty());
        let body =
            sentences(&["rule f ( X:KItem ) => ( #let Y:KItem = X:KItem #in hold ( Y:KItem ) )"]);
        assert!(reductions(&body).is_empty());
    }

    #[test]
    fn a_derived_case_s_direct_case_is_its_family_s_direct_family_s() {
        assert_eq!(
            direct("terms-local/rule/result/x + 1").as_deref(),
            Some("terms/rule/result/x + 1")
        );
        assert_eq!(
            direct("notation-local/sort-rule/result/let-body/m[k]").as_deref(),
            Some("notation/sort-rule/result/let-body/m[k]")
        );
        assert_eq!(direct("terms/rule/result/x + 1"), None);
    }
}
