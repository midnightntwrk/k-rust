//! Generated module-graph definitions used by memory and scaling tests.

/// The import topology used by a generated definition.
#[allow(dead_code)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Shape {
    /// Module `n` imports only module `n - 1`.
    Chain,
    /// Module `n` imports every earlier module.
    FanIn,
}

/// Build a definition with the same sort and rule density as the memory pin.
pub fn definition(modules: usize, shape: Shape) -> String {
    const SORTS_PER_MODULE: usize = 8;
    const RULES_PER_MODULE: usize = 12;
    let mut text = String::new();
    for module in 0..modules {
        text.push_str(&format!("module CHAIN-{module}\n"));
        if module == 0 {
            text.push_str("  imports INT\n");
            text.push_str("  syntax Pgm ::= \"start\"\n");
            text.push_str("  configuration <k> $PGM:Pgm </k> <n> 0 </n>\n");
        } else {
            match shape {
                Shape::Chain => text.push_str(&format!("  imports CHAIN-{}\n", module - 1)),
                Shape::FanIn => {
                    for imported in 0..module {
                        text.push_str(&format!("  imports GRAPH-{imported}\n"));
                    }
                }
            }
        }
        for sort in 0..SORTS_PER_MODULE {
            text.push_str(&format!(
                "  syntax S{module}x{sort} ::= \"c{module}x{sort}\" | f{module}x{sort}(S{module}x{sort}, Int) [function]\n"
            ));
        }
        for rule in 0..RULES_PER_MODULE {
            let sort = rule % SORTS_PER_MODULE;
            text.push_str(&format!(
                "  rule f{module}x{sort}(c{module}x{sort}, N:Int) => c{module}x{sort} requires N ==Int {rule}\n"
            ));
        }
        text.push_str("endmodule\n\n");
    }
    text
}

/// Return the generated main-module name.
pub fn main_module(modules: usize) -> String {
    format!("CHAIN-{}", modules - 1)
}
