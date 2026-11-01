# Amendments to the upstream texts

k-rust embeds the builtin K files of the pinned K release ([crates/k-rust/builtin/](../crates/k-rust/builtin/), `runtimeverification/k` at `4a46d1231473b599c699160132fd6e76a5c46406`, version `v7.1.337`) and evaluates the `[crypto]` hooks as blockchain-k-plugin's `plugin/krypto.md` at `651a2db5` describes them ([compatibility.md, Cryptographic hooks](compatibility.md#cryptographic-hooks)).
Where k-rust's reading of those texts goes beyond what they say, or where k-rust loads K text that differs from them, the difference is an amendment, stated here and nowhere else.

## The rule

There are two kinds of amendment, kept in two places.

A meaning statement says what an existing hook's value is where the upstream text leaves it open.
It adds no K text: the code that evaluates the hook exists, and the amendment makes its value determined instead of open.
It lives only in this document, never in an upstream file: a sentence inserted into `domains.md` would read as upstream's own to anyone who does not compare the files, and would move every later line that k-rust's citations and tests name.

K text that k-rust loads and the upstream file does not hold stays in the embedded file, since K has no way to add a rule to an upstream module from outside it, and rewriting the text at load would make the definition k-rust runs differ from the file it shows.
Each such line ends with the comment `// k-rust: AM-<n>`, naming its entry here, and that entry records the upstream line it replaces, or that it replaces none.
An explanation of such an edit is the entry's; the file holds only the marked code lines.

So every file of `crates/k-rust/builtin/` equals the pinned release's file byte for byte once each marked line is undone: removed if its entry says it was added, otherwise replaced by the upstream line its entry records.
A citation `domains.md`:N in compatibility.md names a line of the embedded copy ([compatibility.md](compatibility.md#backend-scope) states the rule); an entry's `Upstream` field names lines of the upstream file itself.

The test [amendments.rs](../crates/k-rust/tests/amendments.rs) enforces the rule.
It holds the SHA-256 digest of each pinned file, so it needs no K installation, and checks that:

- undoing the marked lines of each embedded file as its entries say gives the pinned file's digest, and every marked line is one its entry lists;
- every entry's quoted passage occurs verbatim at the location its `Upstream` field cites: in the pinned file of a builtin (the embedded copy with its marks undone), and for `krypto.md` in [kink's reference copy](../kink/crates/kink-native/reference/krypto.md) of the plugin's file at `651a2db5`, whose digest it also checks;
- every `AM-<n>` in `crates/` and `docs/` names an entry.

A passage is quoted as a block of the upstream file's lines, either a fenced block or `>` lines; it occurs verbatim at its location when the block's text is the cited lines' text, apart from the line breaks and the indentation around them, starting on the first cited line and ending on the last.

## Entries

Each entry has these fields:

- Upstream: the upstream file, its revision, and the lines the passage is on (several locations are separated by `;`, and each has a passage, in order).
- Passage: the upstream text the amendment rests on, quoted verbatim.
- k-rust reads: the sentence k-rust adds to the text.
- Reason: why the reading is the text's evident intent, argued from K's data model and the text itself.
- Evidence: the tests and the differential or reference gates that check it.
- Upstream proposal: the replacement wording, as a diff of the passage, that would make the amendment unnecessary.
- Status: `local` while the proposal has not been sent upstream; `proposed` once it has; `upstream` once the pinned release holds it, when the entry is removed with the next pin.
- Replaces: what the amendment determines (a class of [implementation-chosen hook values](compatibility.md#implementation-chosen-hook-values) and its construct), or, for K text, `K text` with the marked lines of the embedded file and the upstream lines they replace.

### AM-9: The default layout ends a line comment at every line end

- Upstream: `kast.md` at K v7.1.337, :512-513
- Passage:

  ```k
                       | r"(\\/\\/[^\\n\\r]*)"                         // C-style single-line comments
                       | r"([\\ \\n\\r\\t])"                           // Whitespace
  ```

- k-rust reads: A line end is any of the line terminators a source location counts: `\n` through `\r` (line feed, vertical tab, form feed and carriage return), U+0085, U+2028 and U+2029, the last three written in the regexes as `\u` escapes.
  A single-line comment ends at a line end, and every line end is whitespace.
- Reason: module `DEFAULT-LAYOUT` is the layout of the rule and configuration grammars and of every program of a definition that declares no `#Layout` production, and its two regexes say what a line end is to the scanner: a `//` comment runs to the end of its line, and the end of a line separates tokens.
  A location counts a line at every line terminator ([compatibility.md, Token regex line anchors](compatibility.md#token-regex-line-anchors)), so with the upstream classes a comment before U+2028 would run on into the text the location places on the next line, and a vertical tab, form feed, U+0085, U+2028 or U+2029 outside a comment would be no token at all.
  The classes are widened to the line terminators the locations count, so that the scanner and the locations agree on where a line ends; the characters are written as `\u` escapes because a terminator written verbatim in a string ends a line of the file ([compatibility.md, Definition text layout](compatibility.md#definition-text-layout)), and the module's lines are then its lines as written.
- Evidence: `the_default_line_comment_ends_at_every_line_end_a_location_counts` in [cli.rs](../crates/k-rust/tests/cli.rs), which runs both scanners; `the_default_layout_is_the_default_layout_module_of_the_prelude`, `the_default_line_comment_ends_at_every_line_terminator` and `every_line_terminator_is_default_layout` in [scanner.rs](../crates/k-rust/src/inner/parser/scanner.rs).
  No reference gate agrees: the pinned K's scanner is the upstream text ([compatibility.md, Default layout line ends](compatibility.md#default-layout-line-ends) states the divergence).
- Upstream proposal:

  ```diff
  -                     | r"(\\/\\/[^\\n\\r]*)"                         // C-style single-line comments
  -                     | r"([\\ \\n\\r\\t])"                           // Whitespace
  +                     | r"(\\/\\/[^\\n-\\r\u0085\u2028\u2029]*)"      // C-style single-line comments
  +                     | r"([\\ \\t\\n-\\r\u0085\u2028\u2029])"        // Whitespace
  ```

  with the paragraph of k-rust's reading above added before the module.
- Status: local
- Replaces: K text, marked lines `kast.md`:512-513, in place of the upstream lines:

  ```k
                       | r"(\\/\\/[^\\n\\r]*)"                         // C-style single-line comments
                       | r"([\\ \\n\\r\\t])"                           // Whitespace
  ```

### AM-10: The definedness of `divInt` and `bitRangeInt` as ceil equations

- Upstream: `domains.md` at K v7.1.337, :1235-1237, :1438; `domains.md` at K v7.1.337, :1239-1242
- Passage:

  > * Compute the quotient `divInt` or modulus `modInt` of two integers using
  >   Euclidean division, in which the remainder is always non-negative. Division
  >   by zero is `#False`.

  ```k
    rule bitRangeInt(I::Int, IDX::Int, LEN::Int) => (I >>Int IDX) modInt (1 <<Int LEN)
  ```

  > * Compute the arithmetic right shift `>>Int` of two integers. Shifting by a
  >   negative quantity is `#False`.
  > * Compute the left shift of two integers. Shifting by a negative quantity is
  >   `#False`.

- k-rust reads: Module `INT-SYMBOLIC-KORE` states the definedness of `divInt` and of `bitRangeInt` as it states that of `/Int`, `%Int`, `modInt`, `>>Int` and `<<Int`: `#Ceil(@I1 divInt @I2)` is `@I2 =/=Int 0` with the ceils of both operands, and `#Ceil(bitRangeInt(@I, @O, @L))` is `@O >=Int 0 andBool @L >=Int 0` with the ceils of the three operands.
- Reason: a ceil equation is an equality of the definition, so it holds only if it states the application's actual domain.
  `divInt` is Euclidean division, which gives one integer for every nonzero divisor, and division by zero is `#False`: the application is defined exactly where its operands are and its divisor is not zero.
  `bitRangeInt` is defined by its equation in module `INT` as `(I >>Int IDX) modInt (1 <<Int LEN)`: `I >>Int IDX` is defined exactly where `IDX` is not negative, `1 <<Int LEN` exactly where `LEN` is not negative, and it is then at least 1, so the remainder's divisor is never zero; the application is defined exactly where its operands are and `IDX` and `LEN` are not negative.
  Without the two equations the module states the domain of every partial operation of its group but these two, so a claim whose right-hand side holds `V divInt 32` cannot show that it is defined, though the text says it is.
  The domains are not derived from the hooks' text in the backend instead: the ceil theory of a definition is the one source of an application's definedness for the definedness walk, the simplifier's own reading of a `\ceil`, the value classification of irreducible applications and the solver's function summaries (`ceil_theory` in `k-rust-backend`), so a derived condition would have to be added to that theory at load, as equations no source text states.
- Evidence: `primitive_integer_domains_and_signed_literal_values_compose_in_claims` in [proof_semantics.rs](../crates/k-rust/tests/proof_semantics.rs): `safe-ediv`, `safe-negative-ediv`, `safe-symbolic-ediv`, `safe-range`, `safe-zero-range` and `safe-symbolic-range` are proven, and `undefined-ediv`, `undefined-offset`, `undefined-length` and `undefined-operand` disproved with a certified leaf.
  The ground evaluators return the same domain: a zero divisor and a negative index or length are `\bottom` (`int_partial_binary` and `int_bit_range` in `k-rust-backend`'s `builtin.rs`).
- Upstream proposal:

  ```diff
     rule #Ceil(@I1:Int modInt @I2:Int) => {(@I2 =/=Int 0) #Equals true} #And #Ceil(@I1) #And #Ceil(@I2) [simplification]
  +  rule #Ceil(@I1:Int divInt @I2:Int) => {(@I2 =/=Int 0) #Equals true} #And #Ceil(@I1) #And #Ceil(@I2) [simplification]
     rule #Ceil(@I1:Int >>Int  @I2:Int) => {(@I2 >=Int 0)  #Equals true} #And #Ceil(@I1) #And #Ceil(@I2) [simplification]
     rule #Ceil(@I1:Int <<Int  @I2:Int) => {(@I2 >=Int 0)  #Equals true} #And #Ceil(@I1) #And #Ceil(@I2) [simplification]
  +  rule #Ceil(bitRangeInt(@I:Int, @O:Int, @L:Int)) => {(@O >=Int 0 andBool @L >=Int 0) #Equals true} #And #Ceil(@I) #And #Ceil(@O) #And #Ceil(@L) [simplification]
  ```

  in module `INT-SYMBOLIC-KORE` (:1394-1396).
- Status: local
- Replaces: K text, marked lines `domains.md`:1395 and :1398, added (they replace no upstream line).
