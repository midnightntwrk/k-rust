//! The facade loads no definition whose collection role symbol lacks its role's signature.
//!
//! The list sort `SortLI` names `mkFoo : Int -> Foo` as its element symbol, so an application of
//! `mkFoo` would be a list where the declaration says a `Foo` stands. The definition reaches
//! `mkFoo` only through the equation `g(X) = mkFoo(X)`, so no axiom writes it as an application
//! argument. Read as written, `start(5)` rewrites to `chk(g(5))` and `[hit]` gives `done(1)`;
//! with the element built as a list, the `Foo` pattern of `[hit]` rejects it and the lower
//! priority `[range]` gives `done(7)`. The loader refuses the definition instead.

use k_rust::{
    backend::{Backend, BackendOptions, ExecuteRequest},
    kore::{codec, parser::parse_pattern, printer::Printer},
};

const DEFINITION: &str = r#"[]
module MAIN
  hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
  sort SortKItem{} []
  sort SortFoo{} []
  sort SortProg{} []
  symbol inj{From, To}(From) : To [sortInjection{}()]
  axiom{R} \exists{R}(Value:SortKItem{},
      \equals{SortKItem{}, R}(Value:SortKItem{}, inj{SortFoo{}, SortKItem{}}(From:SortFoo{})))
      [subsort{SortFoo{}, SortKItem{}}()]

  hooked-sort SortLI{}
    [hook{}("LIST.List"), unit{}(dotLI{}()), element{}(mkFoo{}()), concat{}(liConcat{}())]
  symbol dotLI{}() : SortLI{} [function{}(), total{}()]
  symbol mkFoo{}(SortInt{}) : SortFoo{} [constructor{}(), functional{}(), injective{}()]
  symbol liConcat{}(SortLI{}, SortLI{}) : SortLI{} [function{}(), total{}()]

  symbol g{}(SortInt{}) : SortFoo{} [function{}(), total{}()]
  symbol start{}(SortInt{}) : SortProg{} [constructor{}(), functional{}(), injective{}()]
  symbol chk{}(SortKItem{}) : SortProg{} [constructor{}(), functional{}(), injective{}()]
  symbol done{}(SortInt{}) : SortProg{} [constructor{}(), functional{}(), injective{}()]

  axiom{R} \implies{R}(
      \and{R}(\top{R}(), \and{R}(\in{SortInt{}, R}(X0:SortInt{}, VarX:SortInt{}), \top{R}())),
      \equals{SortFoo{}, R}(
        g{}(X0:SortInt{}),
        \and{SortFoo{}}(mkFoo{}(VarX:SortInt{}), \top{SortFoo{}}())
      )
    ) []
  axiom{} \rewrites{SortProg{}}(
      \and{SortProg{}}(start{}(VarI:SortInt{}), \top{SortProg{}}()),
      \and{SortProg{}}(chk{}(inj{SortFoo{}, SortKItem{}}(g{}(VarI:SortInt{}))), \top{SortProg{}}())
    ) [label{}("start")]
  axiom{} \rewrites{SortProg{}}(
      \and{SortProg{}}(chk{}(inj{SortFoo{}, SortKItem{}}(VarF:SortFoo{})), \top{SortProg{}}()),
      \and{SortProg{}}(done{}(\dv{SortInt{}}("1")), \top{SortProg{}}())
    ) [label{}("hit")]
  axiom{} \rewrites{SortProg{}}(
      \and{SortProg{}}(chk{}(VarX:SortKItem{}), \top{SortProg{}}()),
      \and{SortProg{}}(done{}(\dv{SortInt{}}("7")), \top{SortProg{}}())
    ) [label{}("range"), priority{}("60")]
endmodule []"#;

#[test]
fn an_element_symbol_of_another_result_sort_is_refused_at_load() {
    let error = match Backend::new(DEFINITION, "MAIN", BackendOptions::default()) {
        Err(error) => error.to_string(),
        Ok(mut backend) => {
            let request =
                ExecuteRequest::new(parse_pattern(r#"start{}(\dv{SortInt{}}("5"))"#).unwrap());
            let leaves = backend
                .execute(request)
                .map(|result| {
                    result
                        .leaves
                        .iter()
                        .map(|leaf| {
                            Printer::compact()
                                .print_pattern(&codec::from_value(&leaf.state).unwrap())
                        })
                        .collect::<Vec<_>>()
                })
                .map_err(|error| error.to_string());
            panic!("the definition loaded; start(5) gives {leaves:?}");
        }
    };
    assert!(
        error.contains("collection sort SortLI")
            && error.contains("element symbol mkFoo")
            && error.contains("SortFoo"),
        "{error}"
    );
}
