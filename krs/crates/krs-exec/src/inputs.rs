//! Inputs by name: the `#[k::init]` parameters of a definition, and the one encoding of a value
//! of a parameter as a document of the JSON data model, read at the parameter's declared type.
//!
//! A case is an assignment of one value to each declared input, by the `#[k::init]` parameter's
//! name. No input is special: the main parameter ([`Parameter::main`]) is the one a program file
//! binds when a front end is given one, and it can be bound by name as every other parameter is.
//! An input with a declared default ([`Parameter::has_default`]) that a case gives no value has
//! its default, so the case assigns it the default.
//! A value is written as K text parsed at the parameter's sort (`$text`, `$text-file`), or as
//! typed data that this module decodes into a [`Value`] at the parameter's declared type, element
//! types included. The encoding is the same for every front end: `krs run`'s inputs, a case
//! document ("Case documents", below), and a corpus tool that binds cases through `krs-exec`.
//!
//! # The encoding
//!
//! This section is the normative statement of the encoding.
//!
//! A *document* is a value of the JSON data model: null, a boolean, a number, a string, an array,
//! or an object. A TOML document is first converted to it ([`toml_document`]): integers and
//! booleans, strings, arrays and tables as themselves, a finite float as a number, a NaN or an
//! infinity as `{"$float": "NaN"}`, `{"$float": "Infinity"}` or `{"$float": "-Infinity"}`, and a
//! datetime is refused, since it has no reading as a term. A JSON text is read with duplicate
//! object keys refused ([`json_document`]); a TOML parser refuses them itself.
//!
//! A document is decoded at a *position*. A position is a declared type: a sort and, for a
//! collection, its element types (`Map<Int, Int>`, the type of the parameter or of an element
//! inside it). A parameter, a cell, a constructor's field and a function's argument or result
//! each have the type their declaration states, element types included (`regs: Map<Reg8, Int>`).
//! A position is *untyped* where the declared type says nothing: a `K` sort, the elements of a
//! collection whose element types are not declared (a field declared `List`, the elements of
//! `$list`), and the field of a sort no KRS declaration names.
//!
//! Every document has at most one reading at a position. Shorthands are read only where the
//! position's type decides them; elsewhere a *tagged form* states the reading. Where a shorthand
//! has two readings at a position, the document is refused and the message names the tagged
//! form of each reading. The decoder refuses rather than guesses.
//!
//! ## Tagged forms
//!
//! A tagged form is an object with exactly one key, which starts with `$`; no Rust identifier
//! does, so a tag never collides with a constructor or field name. An object with a `$` key and
//! other keys is refused. A tagged form means the same at every position, and one whose term is
//! of a sort that is not at most the position's sort is refused.
//!
//! A map key is not a Rust identifier, and one that starts with `$` (a `String` or token key)
//! would make the object shorthand of a `Map` a tagged form: such a map is written in the pairs
//! form, `[["$x", 1]]`, and the refusal of the object says so.
//!
//! | form | value | where |
//! |---|---|---|
//! | `{"$text": "K text"}` | the text, parsed at the parameter's sort as `-c` parses it, or at a stated cell's sort | a whole input, and a whole cell a case's `instances` states |
//! | `{"$text-file": "path"}` | the file's UTF-8 text, as `$text`; parse locations carry the file's name | as `$text` |
//! | `{"$file": "path"}` | a `Bytes` of the file's bytes, unchanged | anywhere `Bytes` fits |
//! | `{"$hex": "00ff1a"}` | a `Bytes` of the bytes the hex digits spell (an even count, either case, no separators) | anywhere `Bytes` fits |
//! | `{"$data-file": "path"}` | the document the file holds (`.json` or `.toml`, by extension), decoded at this position | anywhere |
//! | `{"$string": "text"}` | a `String` | anywhere |
//! | `{"$int": "-0x1f"}`, `{"$int": 31}` | an `Int`: a string by the integer grammar of the `Int` row below, or an integer | anywhere |
//! | `{"$float": 1.5}`, `{"$float": "1.5f"}` | a `Float`: a number read as at `Float` (below), or the value a K `Float` literal names | anywhere |
//! | `{"$token": "text"}` | a token of the position's sort, which is a token sort | a token sort |
//! | `{"$token": {"sort": "Id", "text": "x"}}` | a token of the named token sort | anywhere |
//! | `{"$list": [..]}`, `{"$set": [..]}`, `{"$seq": [..]}` | a `List`, a `Set`, a K sequence, of untyped elements | anywhere |
//! | `{"$map": [[key, value], ..]}` | a `Map` of untyped keys and values | anywhere |
//! | `{"$ctor": {"path::C": fields}}` | the constructor `C` applied to its fields, as the constructor form `{"path::C": fields}` reads it | anywhere |
//! | `{"$call": {"path::f": fields}}` | the application of the function `f` to its arguments | anywhere |
//!
//! A token's text, as `$token` or as a shorthand, is not checked against its sort's lexical
//! syntax: it denotes the domain value of that sort with that text, a term of the sort, even
//! where no K text of the definition spells it (`"top"` at a sort whose tokens match
//! `@[a-z]+`), while `$text` of the same text fails to parse.
//!
//! A path in `$file`, `$text-file` or `$data-file` is relative to the document that holds it
//! (the case file, or the data file that includes it), and the decoder reads no file itself: the
//! caller's [`InputFiles`] resolves and reads it. A `$data-file` that includes itself, directly
//! or through others, is refused naming the cycle.
//!
//! ## Constructors and functions
//!
//! A constructor is written `{"Name": fields}`, with `fields` an object by field name or an array
//! in declaration order (a tuple variant's fields are named `0`, `1`, ..), and `[]` or `{}` for
//! none; at a position of a declared sort a bare string `"Name"` is a nullary constructor.
//! `Name` is the declaration's path, the crate name of its package's library and its path below
//! the crate root (`sm83::machine::Register::A`), or a `::`-aligned suffix of it (`Register::A`,
//! `A`), resolved
//! among the constructors whose result sort is at most the position's sort (among all
//! constructors at an untyped position); a name that selects several is refused naming them.
//! Each field is decoded at its declared type, element types included: a field declared
//! `Map<Reg8, Int>` reads `{"B": 1}`, and one declared `List` has untyped elements.
//!
//! At a declared sort that `Map` is at most (`KItem`, a field declared `KItem`), an object is also
//! a map's object shorthand, so `{"Name": fields}` reads two ways there and is refused. The tagged
//! form `{"$ctor": {"Name": fields}}` states the constructor reading at every position, its name
//! resolved and its fields read as the constructor form's are; a function under `$ctor` is
//! refused, as one in the constructor form is.
//!
//! A function is applied with `$call`, its arguments written as a constructor's fields and
//! resolved among the function productions whose result sort is at most the position's sort. A
//! function written in the constructor form, and a constructor under `$call`, are refused: a
//! reader of a case sees which parts are data and which are computed. Any function may be applied,
//! partial and `internal` ones included, as the initializer's body may apply them; the
//! configuration holds the application, which the definition's equations evaluate when the first
//! state is simplified, before the first step. A function evaluated in one instance of a Map
//! collection (its function context reads a cell group held there, or it applies such a
//! function) is refused: it receives the instance's key, and an input is evaluated in no
//! instance. It is not program syntax for the same reason, and text that applies it (`$text`,
//! `$text-file`), with its own arguments alone as its `syntax` declares them or with the keys its
//! emission adds after them, is refused with the same reason before the run.
//!
//! ## Shorthands
//!
//! | position | shorthands |
//! |---|---|
//! | `Int` | an integer; a string of an optional `-` and decimal digits, or of `0x`, `0o` or `0b` and digits of that base (for values beyond 64 bits, and for hex); a number with a fraction or an exponent is refused, since JSON delivers an integer beyond 64 bits as one and it would be rounded |
//! | `Bool` | `true`, `false` |
//! | `String` | a string |
//! | `Float` | a number, or a string that is a K `Float` literal; an integer is its binary64 value when binary64 holds it exactly and is refused otherwise; a number with a fraction or an exponent is its binary64 value, but one with an integral value of 2^64 or more, or of -2^63 or less, is refused, since a JSON reader delivers an integer it cannot hold as such a number, already rounded (write it as a K `Float` literal) |
//! | `Bytes` | an array of integers in `0..=255`; a bare string is refused, since its byte encoding is not determined |
//! | a token sort (`Id`, a `#[k::token]` sort) | a string, the token's text |
//! | `List<E>`, `Set<E>` | an array of documents at `E`; a `Set` with two elements that decode equal is refused |
//! | `Map<K, V>` | an object, each key read at `K` from its string (an `Int` by the integer grammar, a `String` verbatim, a `Bool` from `"true"` or `"false"`, a token's text, a nullary constructor's name) and each value at `V`; or an array of `[key, value]` pairs; two keys that decode equal are refused |
//! | a declared sort | a constructor form; a bare string: a nullary constructor, a token of a token sort at most it, or a `String` where `String` is at most it; a boolean where `Bool` is; a number where `Int` or `Float` is (below); an array or an object where a collection sort is, as at that sort with untyped elements |
//! | untyped | an integer (an `Int`), a boolean (a `Bool`), a number with a nonzero fraction (a `Float`), a constructor form, a tagged form; a bare string, an array, a number with an integral value written as a float, and any other object are refused as undetermined |
//!
//! At a declared sort that is no builtin, the document's JSON type decides the builtin, as at an
//! untyped position: a string is never an `Int` or a `Float` there, so `"12"` at `Val`, with
//! `Int` and `String` subsorts of `Val`, is the `String` `"12"` (an `Int` beyond 64 bits is
//! written `{"$int": ..}`). A number is an `Int` where `Int` is at most the sort and a `Float`,
//! read as at `Float`, where `Float` is and `Int` is not. Where both are, an integer is an `Int`,
//! a number with a nonzero fraction a `Float`, and a number with an integral value written as a
//! float (`2.0`) is refused as undetermined, since JSON delivers an integer beyond 64 bits so:
//! the `Float` is written `{"$float": 2.0}`. A map key, which is always a string, is read at its
//! sort by every reading of the strings the `Map` row lists, so `"12"` as a key at `Val` reads
//! as an `Int` and as a `String` and is refused; such a map is written in the pairs form.
//!
//! Two map keys or set elements that decode equal are refused because K's concatenation of two
//! maps that bind one key, or of two sets that share an element, has no value: keeping either
//! binding would accept a document that denotes no term, and would let `{"1": 2, "01": 3}` mean
//! a map that the text `1 |-> 2 1 |-> 3` does not.
//!
//! A decoded value is still checked where a parsed one is: the configuration assembler requires
//! its sort to be at most the variable's declared sort, and every part of a collection to fit the
//! declared element types. The decoder's own checks make the refusal earlier and name the
//! position inside the document.
//!
//! Not in the encoding: `$text` inside a value (below a whole input or a whole stated cell), sort-parametric productions (refused as
//! [`ValueIndex::ctor`] refuses them), and console input.
//!
//! ## The canonical document of a value
//!
//! Every value that has a document at a position has one *canonical document* there,
//! which [`encode`](crate::encode()) writes and which decodes back to the value:
//! `decode(encode(v, t), t) = v`.
//! It is the spelling of a concrete value in every KRS-level report
//! (the two sides of a difference, the result of a view),
//! so that an expected value and an actual one read alike.
//! Each rule writes the form a reader of this encoding writes for the value:
//! a shorthand where the position's declared type decides it, a tagged form elsewhere.
//! A shorthand is written only where it has exactly one reading at the position,
//! by the decoder's own table:
//! where the definition gives it a second
//! (a constructor whose result sort is a token sort, named like a token's text,
//! which a definition KRS emits does not have),
//! the tagged form named below is written instead,
//! so no canonical document is one the decoder refuses.
//!
//! - **Int**: at `Int`, an integer where it lies in `-2^63..2^63`
//!   (every JSON and TOML reader holds it), otherwise the string of its decimal digits;
//!   elsewhere an integer in that range, otherwise `{"$int": "<decimal>"}`.
//! - **Bool**: `true` or `false`.
//! - **String**: at `String`, the string;
//!   elsewhere `{"$string": ..}`,
//!   since a bare string at a declared sort may also read as a nullary constructor or a token.
//! - **Float**: at `Float`, a string:
//!   the K `Float` literal of the shortest decimal digits that read back to the value,
//!   a significand with a `.` and at least one fractional digit and an exponent `e<n>`,
//!   then `f` for binary32 and nothing for binary64
//!   (`1.5e0`, `1.0e300`, `5.0e-324`, `1.5e0f`);
//!   `NaN`, `Infinity`, `-Infinity` and `-0.0e0`, suffixed alike.
//!   A value of another format is written as its canonical literal (`1e0p11x5`).
//!   Elsewhere `{"$float": <that string>}`.
//!   Never a JSON number: a reader may round one, and none holds a NaN.
//! - **Bytes**: `{"$hex": "<lowercase digits>"}` at every position,
//!   `{"$hex": ""}` for the empty value.
//!   The array shorthand is read, never written, so a `Bytes` has one spelling.
//! - **A token**: at its own token sort, its text,
//!   or `{"$token": "<text>"}` where the bare text has another reading at that sort;
//!   elsewhere `{"$token": {"sort": S, "text": ..}}`,
//!   `S` the shortest `::`-aligned suffix of the sort's path that names it among the sorts.
//!   A domain value of a sort that is no token sort has no document.
//! - **List, Set**: at a position whose sort is the collection's,
//!   the array of the elements' documents at the element type (untyped where none is declared);
//!   elsewhere `{"$list": ..}` or `{"$set": ..}` with untyped elements.
//!   A set's elements are ordered by the bytes of their canonical text.
//! - **K sequence**: `{"$seq": [..]}`, its items untyped.
//! - **Map**: at a `Map` position whose key type is declared,
//!   where every key has a *key spelling* and none starts with `$`,
//!   the object of the key spellings to the values' documents at the value type;
//!   otherwise, at a `Map` position, the array of `[key, value]` pairs at the key and value types;
//!   elsewhere `{"$map": [[key, value], ..]}` with untyped keys and values.
//!   Pairs are ordered by the bytes of the key's canonical text.
//!   A key spelling is a string whose only reading at the key type is the key:
//!   an `Int` in decimal, a `Bool` as `true` or `false`, a `String` as itself,
//!   a token as its text, a nullary constructor as its name.
//!   `"12"` at `Val`, with `Int` and `String` subsorts of `Val`, reads two ways,
//!   so a map with `Val` keys that holds the `Int` 12 is written in pairs.
//!   An object key that starts with `$` would make the object a tagged form,
//!   so a map with such a key is written in pairs too.
//! - **A constructor**: `{"Name": fields}`,
//!   `fields` the array of its fields in declaration order for a tuple variant (fields `0`, `1`, ..),
//!   `[]` for none, and the object by field name otherwise,
//!   each field's document at its declared type, element types included.
//!   A nullary constructor is the bare string `"Name"` at a declared sort where that string
//!   has no other reading: one that neither `String` nor any token sort is at most.
//!   Where `{"Name": fields}` has another reading at the position
//!   (at a declared sort that `Map` is at most, where an object is a map too),
//!   `{"$ctor": {"Name": fields}}`, with the same name and fields.
//!   `Name` is the shortest `::`-aligned suffix of the declaration's path
//!   that selects exactly this declaration among the constructors the decoder resolves at the position
//!   (among all constructors at an untyped position).
//! - **A function application** (a value [`ValueIndex::call`] builds):
//!   `{"$call": {"Name": arguments}}`,
//!   named among the functions as a constructor is among the constructors.
//! - **No document**:
//!   an `Opaque` part (a variable, an unevaluated application,
//!   a freezer or another constructor without a KRS declaration, a matching-logic connective);
//!   the application of a parametric constructor, which no form of this encoding writes;
//!   and a value whose sort is not at most the position's.
//!   The refusal ([`EncodeError`](crate::EncodeError)) names the part's position,
//!   in the notation of [`InputError`]'s positions
//!   (`.Run.log$list[2]`; an element of a set and a key of a map by its index in the value's order),
//!   what the part is, and the rule that refuses it.
//!   An `Opaque` part and a parametric application are parts a state may hold by its nature;
//!   a value with a part of another kind is refused naming that part, wherever they lie,
//!   so that the first two never hide a part that says the value is not what its position admits.
//!   A caller shows such a value as K text, marked as such,
//!   never as a document with K text inside it.
//!
//! The *canonical text* of a document ([`canonical_text`](crate::canonical_text())) is its compact JSON,
//! with the members of each object ordered by the bytes of their keys,
//! written by this crate rather than by a JSON library's map,
//! so that it is byte-identical across runs and hosts.
//!
//! # Case documents
//!
//! A *case document* is a TOML or a JSON document, by its file's extension,
//! that states one case or several named cases ([`CaseDocument`]).
//! A *case* is a table of five keys, each of which may be absent:
//!
//! - `inputs`: a value for each input, by name
//!   (a parameter's Rust name, or its configuration variable's K name with or without `$`),
//!   each a document of the encoding, read at the parameter's declared type;
//!   a front end may bind the inputs a case does not name in its own ways.
//! - `run`: how the case is run:
//!   `depth`, at most this many rewrite steps;
//!   `stop_before` and `stop_after`, the rules at whose step the run ends,
//!   each an array of names of rules as [`StopRules`](crate::StopRules) takes them:
//!   a KRS item as a stop flag names it (`crate::machine::boundary`, or a dependency's crate name,
//!   the crate name of its library, and its path), or a K label, in full or by a
//!   unique suffix after a `.`;
//!   and `stop_count`, a positive integer, the arrival at a stop the run ends at
//!   ([`StopCriterion::Rules`](crate::StopCriterion::Rules)), the first by default,
//!   which needs a stop rule to count arrivals at;
//!   and `stop_when`, a stop condition ([`StopWhen`](crate::StopWhen)),
//!   a table `{ function, cells, observer }`:
//!   `function` names a function of result sort `Bool` as a view names one,
//!   `cells` the leaf cells it reads by Rust field path, in the order of its parameters,
//!   and `observer`, optional, the definition it is evaluated in, `PACKAGE:DEFINITION`
//!   as an expectation names its observer, the run's own definition by default;
//!   an arrival is then a stop only where the condition holds of the state the run would end at,
//!   and `stop_count` counts those.
//!   The condition needs a stop rule, at whose arrivals it is asked.
//!   The count and the condition belong to the case, beside its rules,
//!   since where a run is observed depends on the program it runs.
//! - `observe`: the observations the case's run declares along its path
//!   ([`ObservationSpec`](crate::ObservationSpec), "Observations", below).
//! - `instances`: the instances the run starts with, of the optional and repeated cells it names
//!   ("Instances", below).
//! - `expect`: the end the case expects of its run ("Expectations", below).
//!
//! A document of one case holds these keys at its top, and no other.
//! A document of named cases holds `case`, the *list* of its cases,
//! and may hold `run`, the `run` of every case that has none of its own
//! (a case's own `run` replaces it whole),
//! and `observe`, likewise the `observe` of every case that has none of its own;
//! it holds no other key, so a document is of one kind or the other.
//! A JSON document that is an array is a list, and a document of named cases.
//! A list is an array (TOML's `[[case]]` tables) of named cases, each a case with a `name`,
//! and of *includes*, `{"$data-file": "path"}`,
//! each naming a `.json` or `.toml` file whose document is a list
//! (an array, or a table whose one key is `case`, as TOML writes a list);
//! the file's cases stand at the include's place.
//! A path written in an included file, an include's or one in a case's values,
//! is relative to that file;
//! the caller's [`InputFiles`] resolves it, under its own rules, as it resolves every path,
//! and a file that includes itself, directly or through others, is refused naming the cycle.
//!
//! A name is a non-empty string that no other case of the document has,
//! the cases of included files included,
//! so that the document and the name identify a case (`<document>#<name>`).
//! A front end selects a case of a document of named cases by its name;
//! the one case of a document has no name, and is selected by none.
//!
//! ## Observations
//!
//! `observe` declares what the case's run shows along its path, beside its end
//! ([`observations`](crate::observations)): a table of three keys,
//! `observer`, `point` and `log`, each of which may be absent.
//! A declaration with no `point` and no `log` declares no channel, and the run is the run without it.
//!
//! - `observer`: the definition the declaration's functions are resolved and evaluated in,
//!   `PACKAGE:DEFINITION` as an expectation names its observer, the run's own definition by default;
//!   only a declaration with a function (a view, a component, a filter or an element function) names one.
//! - `point`: an array of point classes (TOML's `[[observe.point]]` tables), each a table of
//!   `name`, the channel's name, a non-empty string;
//!   `before` and `after`, the rules on whose side of a step the class samples,
//!   each an array of names of rules as `run`'s `stop_before` and `stop_after` name them;
//!   `stutter`, which has no default: `collapse`, under which an element equal to the last one kept is dropped,
//!   or `count`, under which every point is an element;
//!   `cells`, the leaf cells whose values are components, by Rust field path;
//!   `views`, a table of a function by cell of `cells`, whose value is that cell's component;
//!   `components`, an array of tables `{ name, cells, function }`, each a function of the cells it names,
//!   in the order of its parameters;
//!   and `when`, a filter `{ function, cells }` of result sort `Bool`.
//! - `log`: an array of logs (TOML's `[[observe.log]]` tables), each a table of
//!   `name`, the channel's name;
//!   `cell`, the `List` leaf cell, by Rust field path;
//!   `element`, an optional element function, `Item -> List<_>`;
//!   and `at`, the names of the point classes at whose points the log is read, besides the path's end.
//!
//! A function is named as a view names one, by a KRS path as [`ValueIndex::decl`] reads one:
//! `crate::` and its path for the root package's, its full path, or a `::`-aligned suffix of it.
//! Which rules, cells and functions a declaration may name is the run's to judge
//! ([`crate::Semantics::observations`]); a case document refuses only what is no declaration,
//! naming the key.
//!
//! ## Instances
//!
//! The initializer states every fixed cell's start as a function of the inputs,
//! and one instance's template for each optional (`?`) and repeated (`*`) cell;
//! how many instances such a cell starts with is what it cannot state.
//! `instances` states exactly that: the starting instances of the cells it names.
//! A fixed cell starts as the initializer says, and a case that needs another start binds other inputs.
//!
//! `instances` nests by group field as an end document's `cells` does
//! (`instances.harts.hart` is the cell `hart` of the group `harts`),
//! down to an optional or a repeated cell, which it states in the encoding an end document uses:
//! an optional cell as `[]` (absent) or `[content]` (present),
//! a repeated cell as the array of its instances, in order for a `List` collection.
//! An instance is the table of its cells by Rust field (a document for an optional leaf cell),
//! read as an instance a rule creates is:
//!
//! - a stated leaf cell is read at its declared type, element types included,
//!   as an input's value is, and may be K text (`$text`, `$text-file`), parsed at the cell's sort;
//! - a stated group cell is the table of its cells, read the same way;
//! - a stated optional or repeated cell inside an instance states that cell's instances, as above;
//! - a cell the instance does not state takes the template's start, evaluated under the case's inputs,
//!   as the initializer's own instance takes it.
//!   The template is a function of the inputs, which the case binds, so every cell has one.
//!
//! An instance of a `Map` collection states its whole key, its first cell,
//! as a value (no function application):
//! the key is the instance's identity,
//! and two instances with one key are refused, naming the key, since a map holds one instance per key.
//! Two instances of a `Set` collection stated alike are refused too: a set holds an instance once.
//! The stated instances of a cell replace the ones the initializer starts it with,
//! the instance `initial` starts included; a cell `instances` does not name starts as the initializer says.
//! A path that names a fixed cell is refused, listing the optional and repeated cells a case may state,
//! and a path the configuration does not declare is refused, listing the cells there, as an end document's is.
//! A function evaluated in one instance of a Map collection is refused in a stated cell's value or text,
//! as it is in an input's: it receives an instance's key, and the case's values are evaluated in no instance.
//!
//! ```toml
//! inputs.pgm = { "$text-file" = "boot.s" }
//!
//! [[instances.harts.hart]]
//! id = 0
//! pc = 0x1000
//!
//! [[instances.harts.hart]]
//! id = 1
//! pc = 0x2000
//! ```
//!
//! states two harts, keyed `0` and `1`, each with the program counter it gives
//! and every other cell as the template starts it (both run the program `pgm` binds).
//!
//! ## Expectations
//!
//! `expect` states the end the definition computes for the case,
//! as an end document (the section "End documents" of krs-exec's [`ends`](crate::ends) module)
//! with a narrowing:
//!
//! - `halt` and, for `stopped` only, `rule`: how the run ends,
//!   the stop rule named as `run` and every end document name rules, by KRS item or K label,
//!   so that one spelling names a rule in all of them;
//!   the name selects the rules of one KRS item, which a stopped end's class names;
//!   `halt` is never `depth-bound`, which is refused:
//!   the depth counts the compiled definition's steps, heating and cooling included,
//!   so the state after N steps is no fact about the definition,
//!   and a run that reaches its bound is not known to have ended
//!   ([`ends`](crate::ends), "Results");
//!   an expectation of the state at a point of a run stops the run at a named rule
//!   with a `stop_count` and expects `halt = "stopped"` with that `rule`;
//! - `cells`: the cells' values by Rust field path, nested by group field
//!   (`cpu.regs` is `cells.cpu.regs`),
//!   each read at the cell's declared type as an input's value is,
//!   its file paths relative to the document that holds the case;
//! - `compare`: the cells the end is compared on, by declared path,
//!   by default every leaf cell that is not unobservable;
//! - `views`: a table of a view by compared leaf cell (its declared path),
//!   each the name of a function of one parameter ([`views`](crate::views)),
//!   which the comparison applies to the cell's value on both sides,
//!   so that the end is compared on what the case observes of the cell;
//! - `observer`: the definition the views are resolved and evaluated in,
//!   named as a front end names a definition (krs: `PACKAGE:DEFINITION`, as `--dependency` names one),
//!   by default the definition the case runs on;
//!   it is only given with `views`.
//!
//! An expectation states every cell it is compared on:
//! it may omit an unobservable cell, which no use of the definition observes,
//! and a cell `compare` leaves out,
//! but a compared cell it omits is refused, naming the cell and its type, before the case runs,
//! since every value of that cell would meet it, which expects nothing of the cell.
//! A `compare` that names an unobservable cell is refused too: no observation of it exists to compare.
//! A cell the expectation states and does not compare is read, and never compared.
//! A viewed cell is stated as the cell's value, not as the view's:
//! the view is applied to the stated value as to the actual one,
//! so one expected end can be compared under several views.
//! A view that does not apply to its cell, or names no function of the observer, is refused before the case runs,
//! and one without a value at an end refuses the verdict, naming the view, the side and the cell,
//! since an observation that does not exist makes the ends neither agree nor differ.
//! A front end may bound each view's evaluation;
//! one that the bound or another stop of the evaluation ends before it reaches a value makes the verdict inconclusive, since it may yet have a value,
//! as does one that ends short of a value after the solver answered a query `Unknown`.
//!
//! Against the ends of the case's run, the expectation is
//! *met* when every end agrees with it on the halt and on the compared cells;
//! *unmet* when an end does not, which is reported with the first difference
//! ([`Difference`](crate::Difference), `krs-difference/3`, which names the views it applied);
//! and *inconclusive* when no end can be compared,
//! or every known end agrees but not every end is known.
//! No end can be compared where
//! the run halted `indeterminate`, `timeout`, `interrupted`, `unsupported-hook` or `simplification-error`,
//! reached its depth bound (`depth-bound`: a budget ran out, and the definition may go on),
//! reached several states under conditions it cannot decide,
//! ended in a state that carries a constraint,
//! or stopped at a rule it does not name.
//! Not every end is known where a search was cut by its bounds,
//! where a run's path took one of several successors of a state,
//! and where the ends rest on a value the definition leaves open
//! (an implementation-chosen hook value), which another implementation of it may choose otherwise.
//! Inconclusive is never unmet: "no end to compare" and "ends differ" call for different actions.
//! "Every end" is the rule because one disagreeing end of a nondeterministic definition
//! is a result the definition can produce.
//!
//! A run follows one path and has at most one end.
//! An end of it that disagrees is unmet, since the definition reaches it;
//! one that agrees meets the expectation only where it is the definition's only end:
//! no state of the path has several successors,
//! which the path, followed again trying every rule at each step, shows,
//! and the run read no value the definition leaves open.
//! A final-state search gives every end within its bounds.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::num::NonZeroU64;
use std::sync::Arc;

use k_rust::kast::Sort as KastSort;
use krs_ir::{BuiltinSort, CellCollectionType, CellMultiplicity, CellSortArgument};
use krs_ir_levels::{DefinitionIr, DefinitionSentence, DefinitionSortRef};
use num_bigint::BigInt;
use serde_json::Value as Json;

use crate::observations::{Component, Filter, LogChannel, ObservationSpec, PointClass, Stutter};
use crate::values::{CellNode, Decl, Float, SortRef, Value, ValueError, ValueIndex};
use crate::{ConfigValue, ProgramInput};

/// One `#[k::init]` parameter: an input of the definition, from the Definition IR.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Parameter {
    /// The Rust binding, the IR variable's id (`regs`).
    pub name: String,
    /// The K name of its configuration variable, without `$` (`REGS`).
    pub variable: String,
    /// The declared type, element types included.
    pub ty: InputType,
    /// Whether this is the main parameter, which a program file binds: the one marked
    /// `#[k::config_var(.., main)]`, or the one the computation cell reads when none is marked.
    pub main: bool,
    /// Whether the input declares a default (`#[k::config_var(.., default = D)]`): the value it
    /// has when a configuration binds none, so binding it is optional. A binding replaces the
    /// default whole.
    pub has_default: bool,
}

impl Parameter {
    /// Whether a program file binds this parameter as the file's bytes: its declared type is
    /// exactly `Bytes`, the one type whose values are any bytes. Every other type, a sort `Bytes`
    /// is a subsort of included, reads a file as text, parsed at its sort, since only a parse
    /// says which of its values a file denotes.
    #[must_use]
    pub fn reads_file_bytes(&self) -> bool {
        self.ty.sort == SortRef::Builtin(BuiltinSort::Bytes) && self.ty.arguments.is_empty()
    }

    /// Why a program file that is not UTF-8 text binds this main parameter to nothing, where it
    /// does not read a file's bytes: the end of [`crate::ExecError::ProgramNotText`]'s message,
    /// for a caller that names the file itself.
    #[must_use]
    pub fn reads_file_text(&self) -> String {
        format!(
            "the main parameter `{}` (${}: {}) reads a file as text, parsed at its sort; only a main parameter of type exactly `Bytes` takes a file's bytes",
            self.name, self.variable, self.ty
        )
    }
}

/// The main input of a definition as its Definition IR declares it, read without compiling the
/// definition: what a front end needs to bind a program file that is text.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MainVariable {
    /// The Rust binding (`entry`).
    pub name: String,
    /// The K name of its configuration variable, without `$` (`PGM`, `ENTRY`).
    pub variable: String,
    /// Whether a program file binds it as the file's bytes ([`Parameter::reads_file_bytes`]),
    /// where the Definition IR alone says so; `None` where only the compiled definition does.
    pub reads_file_bytes: Option<bool>,
}

/// The configuration variables of `definition`'s `#[k::init]`, in declaration order.
fn configuration_variables(
    definition: &DefinitionIr,
) -> impl Iterator<Item = &krs_ir::FixedConfigurationVariable<DefinitionSortRef>> {
    definition
        .modules()
        .iter()
        .flat_map(krs_ir_levels::DefinitionModule::sentences)
        .filter_map(|sentence| match sentence {
            DefinitionSentence::Configuration(configuration) => Some(configuration),
            _ => None,
        })
        .flat_map(krs_ir::FixedConfiguration::variables)
}

/// Whether a program file binds a parameter of the IR sort `sort` applied to `arguments` as the
/// file's bytes, as [`Parameter::reads_file_bytes`] says of the parameter [`parameters`] types
/// from it; `None` where that type is not a function of the IR sort.
///
/// [`parameters`] maps a builtin sort to itself with its arguments, and a declared sort to a
/// declared KRS sort or, for one no KRS declaration names, to the compiled definition's K sort of
/// the variable, which is that declared sort's own: K's `Bytes` is the builtin's sort, and a
/// definition declares each sort name once. Only where the sort, or one of its arguments, is a
/// cell sort or a sort parameter is the compiled K sort another than the IR names, and it can be
/// K's `Bytes`. So the type is exactly `Bytes` exactly when the IR sort is the builtin `Bytes`
/// with no arguments, except under a cell sort or a sort parameter, where only the compiled
/// definition answers.
fn file_reading(
    sort: &DefinitionSortRef,
    arguments: &[CellSortArgument<DefinitionSortRef>],
) -> Option<bool> {
    fn ir_typed(
        sort: &DefinitionSortRef,
        arguments: &[CellSortArgument<DefinitionSortRef>],
    ) -> bool {
        matches!(
            sort,
            DefinitionSortRef::Builtin(_) | DefinitionSortRef::Declared(_)
        ) && arguments
            .iter()
            .all(|argument| ir_typed(&argument.sort, &argument.arguments))
    }
    ir_typed(sort, arguments)
        .then(|| *sort == DefinitionSortRef::Builtin(BuiltinSort::Bytes) && arguments.is_empty())
}

/// The main parameter of `definition`'s `#[k::init]` ([`Parameter::main`]), from the Definition
/// IR alone; `None` when it has none.
#[must_use]
pub fn main_variable(definition: &DefinitionIr) -> Option<MainVariable> {
    configuration_variables(definition)
        .find(|variable| variable.is_main())
        .map(|variable| MainVariable {
            name: variable.id().as_str().to_owned(),
            variable: variable.external_name().to_owned(),
            reads_file_bytes: file_reading(variable.sort(), variable.arguments()),
        })
}

/// Whether `definition`'s `#[k::init]` has a parameter whose configuration variable's K name is
/// `variable` (without `$`), main or not, from the Definition IR alone.
#[must_use]
pub fn declares_variable(definition: &DefinitionIr, variable: &str) -> bool {
    configuration_variables(definition).any(|declared| declared.external_name() == variable)
}

/// The K names (without `$`) of the configuration variables of `definition`'s `#[k::init]`
/// that declare a default (`#[k::config_var(.., default = D)]`), in declaration order, from the
/// Definition IR alone: the inputs a configuration need not bind.
#[must_use]
pub fn defaulted_variables(definition: &DefinitionIr) -> Vec<String> {
    configuration_variables(definition)
        .filter(|variable| variable.default().is_some())
        .map(|variable| variable.external_name().to_owned())
        .collect()
}

impl fmt::Display for Parameter {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}: {}", self.name, self.ty)
    }
}

/// A declared type: a sort and, for a collection, its element types (`Map<Reg8, Int>`).
///
/// The sort `K` ([`BuiltinSort::KSequence`]) is the untyped position: it takes any term, and
/// the encoding reads no shorthand there.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InputType {
    /// The sort.
    pub sort: SortRef,
    /// The element types of a collection, in order; empty for every other sort and for a
    /// collection declared without them.
    pub arguments: Vec<InputType>,
}

impl InputType {
    /// The untyped position.
    #[must_use]
    pub const fn untyped() -> Self {
        Self::of(SortRef::Builtin(BuiltinSort::KSequence))
    }

    /// The sort with no element types.
    #[must_use]
    pub const fn of(sort: SortRef) -> Self {
        Self {
            sort,
            arguments: Vec::new(),
        }
    }

    /// Whether the type says nothing about a document at it (`K`).
    #[must_use]
    pub fn is_untyped(&self) -> bool {
        self.sort == SortRef::Builtin(BuiltinSort::KSequence)
    }

    /// The type of element `index` of a collection of this type: its declared element type,
    /// or the untyped position when the collection declares none.
    pub(crate) fn element(&self, index: usize) -> Self {
        self.arguments
            .get(index)
            .cloned()
            .unwrap_or_else(Self::untyped)
    }
}

impl fmt::Display for InputType {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&ValueIndex::sort_name(&self.sort))?;
        if !self.arguments.is_empty() {
            formatter.write_str("<")?;
            for (index, argument) in self.arguments.iter().enumerate() {
                if index > 0 {
                    formatter.write_str(", ")?;
                }
                argument.fmt(formatter)?;
            }
            formatter.write_str(">")?;
        }
        Ok(())
    }
}

/// Where the decoder reads the files a document names (`$file`, `$text-file`, `$data-file`).
///
/// The decoder touches no filesystem: a front end resolves a path as its documents are placed
/// (a case file's directory, a manifest's directory under its containment rule).
pub trait InputFiles {
    /// The resolved name and the bytes of `path`, written in the document `from` (the resolved
    /// name an earlier read returned, for a path inside a data file), or in the top document
    /// (`None`).
    ///
    /// The resolved name identifies the file: parse locations carry it, and the cycle check of
    /// `$data-file` compares it.
    ///
    /// # Errors
    ///
    /// Returns why the file cannot be read, which the decoder reports at the path's position.
    fn read(&mut self, from: Option<&str>, path: &str) -> Result<(String, Vec<u8>), String>;
}

/// The [`InputFiles`] of a document that names no file: every read is refused.
#[derive(Clone, Copy, Debug, Default)]
pub struct NoFiles;

impl InputFiles for NoFiles {
    fn read(&mut self, _from: Option<&str>, path: &str) -> Result<(String, Vec<u8>), String> {
        Err(format!("`{path}`: this input reads no files"))
    }
}

/// One case ([module documentation](self#case-documents)): a value for each input by name, how
/// it is run, and the end it expects.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Case {
    /// Its name, in a document of named cases; `None` for the one case of a document.
    pub name: Option<String>,
    /// Each input's name, a parameter's Rust name or its K name with or without `$`, and its
    /// document, by name.
    pub inputs: Vec<(String, Json)>,
    /// How it is run: its own `run`, else its document's (named cases only); `None` when neither
    /// is given.
    pub run: Option<CaseRun>,
    /// The observations its run declares: its own `observe`, else its document's (named cases
    /// only); `None` when neither is given.
    pub observe: Option<Box<ObservationSpec>>,
    /// The `instances` table, read against the definition by
    /// [`crate::Semantics::state_instances`]; `None` when the case states none.
    pub instances: Option<Json>,
    /// The `expect` table, read against the definition by [`crate::Semantics::expectation`].
    pub expect: Option<Json>,
    /// The resolved name ([`InputFiles::read`]) of the data file the case is written in, which
    /// its paths are relative to; `None` for the top document.
    pub file: Option<String>,
}

/// How a case is run: its `run` table.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct CaseRun {
    /// `depth`: at most this many rewrite steps.
    pub depth: Option<u64>,
    /// `stop_before`: the rules before whose step the run ends, each named by KRS item or K
    /// label ([`crate::StopRules::before`]).
    pub stop_before: Vec<String>,
    /// `stop_after`: the rules after whose step the run ends, each named by KRS item or K label
    /// ([`crate::StopRules::after`]).
    pub stop_after: Vec<String>,
    /// `stop_count`: the arrival at a stop the run ends at ([`crate::StopCriterion::Rules`]);
    /// `None` for the first. Only given with stop rules.
    pub stop_count: Option<NonZeroU64>,
    /// `stop_when`: the condition an arrival's stop state must satisfy to be a stop
    /// ([`crate::StopWhen`]); `None` for none. Only given with stop rules.
    pub stop_when: Option<Box<crate::StopWhen>>,
}

impl CaseRun {
    /// Where the run ends besides its own end: at the `stop_count`th arrival at a stop of its
    /// rules, or only on its own where it names none.
    #[must_use]
    pub fn stop(&self) -> crate::StopCriterion {
        let rules = crate::StopRules {
            before: self.stop_before.clone(),
            after: self.stop_after.clone(),
        };
        if rules.is_empty() {
            return rules.into();
        }
        crate::StopCriterion::Rules {
            rules,
            count: self.stop_count.unwrap_or(NonZeroU64::MIN),
            when: self.stop_when.as_deref().cloned(),
        }
    }
}

/// What a case expects of its run ([module documentation](self#expectations)): one end, usually
/// partial, the cells it is compared on, and the views it applies to them.
#[derive(Clone, Debug)]
pub struct Expectation {
    /// The expected end: the class, and the cells the `expect` table states.
    pub end: crate::End,
    /// The compared cells, with no view resolved: a front end resolves [`Self::views`] in the
    /// observer ([`crate::Semantics::cell_views`]) into its `views`.
    pub comparison: crate::Comparison,
    /// The `views` table: a function by declared cell path; empty for none.
    pub views: BTreeMap<String, String>,
    /// The `observer`: the definition the views are resolved in, as the document names it;
    /// `None` for the definition the case runs on.
    pub observer: Option<String>,
}

/// The keys of a case, besides a named case's `name`.
const CASE_KEYS: [&str; 5] = ["inputs", "run", "observe", "instances", "expect"];

/// What a document of named cases gives every case that does not give its own: its `run` and its
/// `observe`.
#[derive(Clone, Copy, Default)]
struct Shared<'a> {
    run: Option<&'a CaseRun>,
    observe: Option<&'a ObservationSpec>,
}

impl Case {
    /// The one case a TOML document states.
    ///
    /// # Errors
    ///
    /// Returns [`InputError`] for a text that is no TOML, a value [`toml_document`] refuses, a
    /// document of named cases (read by [`CaseDocument`]), and a case that is no case
    /// ([module documentation](self#case-documents)).
    pub fn from_toml(text: &str) -> Result<Self, InputError> {
        Self::from_document(toml_case_document(text)?)
    }

    /// The one case a JSON document states.
    ///
    /// # Errors
    ///
    /// Returns [`InputError`] for a text [`json_document`] refuses, a document of named cases
    /// (read by [`CaseDocument`]), and a case that is no case
    /// ([module documentation](self#case-documents)).
    pub fn from_json(text: &str) -> Result<Self, InputError> {
        Self::from_document(json_document(text)?)
    }

    fn from_document(document: Json) -> Result<Self, InputError> {
        let named = match &document {
            Json::Array(items) => Some(items.len()),
            Json::Object(top) => top.get("case").map(|list| match list {
                Json::Array(items) => items.len(),
                _ => 0,
            }),
            _ => None,
        };
        if let Some(count) = named {
            let listed = if count == 0 {
                String::new()
            } else {
                format!(", {count} listed")
            };
            return Err(InputError::document(format!(
                "the document holds named cases{listed}, not one case: it is read as a case document of named cases, and a case of it is selected by name (`krs run --case FILE --case-name NAME`)"
            )));
        }
        let Json::Object(top) = document else {
            return Err(InputError::document(
                "a case document is a table: one case's `inputs`, `run`, `observe`, `instances` and `expect`, or named cases under `case`".to_owned(),
            ));
        };
        case_table(top, "", None, Shared::default(), None)
    }
}

/// The cases of a case document ([module documentation](self#case-documents)).
#[derive(Clone, Debug, PartialEq)]
pub enum CaseDocument {
    /// A document of one case, which has no name.
    One(Case),
    /// A document of named cases, in document order (an included file's at its place), each
    /// with a name no other case of the document has.
    Named(Vec<Case>),
}

impl CaseDocument {
    /// The case document a TOML text states; `files` reads the files of named cases it includes,
    /// relative to it. `top` is the resolved name ([`InputFiles::read`]) of the file that holds
    /// the text, so that an included file that includes it back is refused as the cycle it is;
    /// `None` for a text no file holds.
    ///
    /// # Errors
    ///
    /// Returns [`InputError`] for a text that is no TOML, a value [`toml_document`] refuses, a
    /// file that cannot be read or includes itself, and anything else that is no case document,
    /// naming its position.
    pub fn from_toml(
        text: &str,
        top: Option<&str>,
        files: &mut dyn InputFiles,
    ) -> Result<Self, InputError> {
        Self::from_document(toml_case_document(text)?, top, files)
    }

    /// The case document a JSON text states, as [`Self::from_toml`] reads a TOML one.
    ///
    /// # Errors
    ///
    /// Fails as [`Self::from_toml`] does, for a text [`json_document`] refuses.
    pub fn from_json(
        text: &str,
        top: Option<&str>,
        files: &mut dyn InputFiles,
    ) -> Result<Self, InputError> {
        Self::from_document(json_document(text)?, top, files)
    }

    /// The case document `document` (of the JSON data model) states, as [`Self::from_toml`]
    /// reads the document of a TOML text.
    ///
    /// # Errors
    ///
    /// Fails as [`Self::from_toml`] does.
    pub fn from_document(
        document: Json,
        top: Option<&str>,
        files: &mut dyn InputFiles,
    ) -> Result<Self, InputError> {
        let mut reader = CaseReader {
            files,
            top: top.map(str::to_owned),
            includes: Vec::new(),
            cases: Vec::new(),
            names: BTreeMap::new(),
        };
        match document {
            Json::Array(_) => reader.list(&document, "", Shared::default())?,
            Json::Object(mut top) if top.contains_key("case") => {
                if let Some(key) = top
                    .keys()
                    .find(|key| !matches!(key.as_str(), "case" | "run" | "observe"))
                {
                    return Err(at(
                        "",
                        format!(
                            "a document of named cases holds `case`, `run` and `observe` only; one case's `{key}` belongs in its table in `case`"
                        ),
                    ));
                }
                let run = top
                    .remove("run")
                    .map(|run| case_run(&run, "run", false))
                    .transpose()?;
                let observe = top
                    .remove("observe")
                    .map(|observe| observe_table(&observe, "observe"))
                    .transpose()?;
                let list = top.remove("case").unwrap_or(Json::Null);
                let shared = Shared {
                    run: run.as_ref(),
                    observe: observe.as_ref(),
                };
                reader.list(&list, "case", shared)?;
            }
            Json::Object(top) => {
                return case_table(top, "", None, Shared::default(), None).map(Self::One);
            }
            _ => {
                return Err(InputError::document(
                    "a case document is a table (one case, or named cases under `case`) or an array of named cases".to_owned(),
                ));
            }
        }
        Ok(Self::Named(reader.cases))
    }

    /// The names of its cases, in document order; none for a document of one case.
    pub fn names(&self) -> impl Iterator<Item = &str> {
        let cases = match self {
            Self::One(_) => &[][..],
            Self::Named(cases) => cases.as_slice(),
        };
        cases.iter().filter_map(|case| case.name.as_deref())
    }

    /// The case named `name`; `None` when it has none of that name, as a document of one case
    /// never has.
    #[must_use]
    pub fn named(&self, name: &str) -> Option<&Case> {
        match self {
            Self::One(_) => None,
            Self::Named(cases) => cases.iter().find(|case| case.name.as_deref() == Some(name)),
        }
    }
}

/// The TOML text `text` in the JSON data model.
fn toml_case_document(text: &str) -> Result<Json, InputError> {
    let table = text.parse::<toml::Table>().map_err(|error| {
        InputError::document(format!("the case document is no TOML document: {error}"))
    })?;
    toml_document(&toml::Value::Table(table))
}

/// The TOML text `text` in the JSON data model ([`toml_document`]), for a reader that learns
/// which document it holds from its keys: an end document ([`crate::ends`], "End documents") or
/// a case document ([`CaseDocument::from_document`]).
///
/// # Errors
///
/// Returns [`InputError`] for a text that is no TOML document and a value [`toml_document`]
/// refuses.
pub fn toml_text_document(text: &str) -> Result<Json, InputError> {
    let table = text
        .parse::<toml::Table>()
        .map_err(|error| InputError::document(format!("no TOML document: {error}")))?;
    toml_document(&toml::Value::Table(table))
}

/// A refusal of a case document at `position`.
fn at(position: &str, message: String) -> InputError {
    InputError {
        parameter: None,
        declared: None,
        position: position.to_owned(),
        message,
    }
}

/// `position` followed by the key `key`.
fn key_position(position: &str, key: &str) -> String {
    if position.is_empty() {
        key.to_owned()
    } else {
        format!("{position}.{key}")
    }
}

/// The case the table `top` states at `position`: a named case when `name` lists the names
/// taken so far, the one case of a document otherwise. `shared` is what its document gives every
/// case, `file` the data file it is written in.
fn case_table(
    mut top: serde_json::Map<String, Json>,
    position: &str,
    name: Option<String>,
    shared: Shared<'_>,
    file: Option<&str>,
) -> Result<Case, InputError> {
    let named = name.is_some();
    if let Some(key) = top
        .keys()
        .find(|key| !(CASE_KEYS.contains(&key.as_str()) || named && key.as_str() == "name"))
    {
        let message = if key == "name" {
            "a document of one case names none; named cases are listed under `case`".to_owned()
        } else if named {
            format!(
                "unknown key `{key}` in a case; a named case has the keys `name`, `inputs`, `run`, `observe`, `instances` and `expect`"
            )
        } else {
            format!(
                "unknown key `{key}` in a case; a case has the keys `inputs`, `run`, `observe`, `instances` and `expect`"
            )
        };
        return Err(at(position, message));
    }
    let inputs = match top.remove("inputs") {
        Some(Json::Object(inputs)) => inputs.into_iter().collect(),
        Some(_) => {
            return Err(at(
                position,
                "`inputs` is a table of the case's values by input name".to_owned(),
            ));
        }
        None => Vec::new(),
    };
    let own = top
        .remove("run")
        .map(|document| {
            case_run(
                &document,
                &key_position(position, "run"),
                shared.run.is_some(),
            )
        })
        .transpose()?;
    let observe = top
        .remove("observe")
        .map(|document| observe_table(&document, &key_position(position, "observe")).map(Box::new))
        .transpose()?;
    let instances = match top.remove("instances") {
        Some(Json::Object(instances)) => Some(Json::Object(instances)),
        Some(_) => {
            return Err(at(
                position,
                "`instances` is a table of the starting instances of optional and repeated cells, by Rust field path"
                    .to_owned(),
            ));
        }
        None => None,
    };
    let expect = match top.remove("expect") {
        Some(Json::Object(expect)) => Some(Json::Object(expect)),
        Some(_) => {
            return Err(at(
                position,
                "`expect` is a table of the expected end: `halt`, `rule`, `cells`, `compare`, `views` and `observer`"
                    .to_owned(),
            ));
        }
        None => None,
    };
    Ok(Case {
        name,
        inputs,
        run: own.or_else(|| shared.run.cloned()),
        observe: observe.or_else(|| shared.observe.cloned().map(Box::new)),
        instances,
        expect,
        file: file.map(str::to_owned),
    })
}

/// The `run` table `document` at `position`; `replaces` when it is a case's own `run` beside its
/// document's, which it replaces whole.
fn case_run(document: &Json, position: &str, replaces: bool) -> Result<CaseRun, InputError> {
    const KEYS: &str = "`depth`, `stop_before`, `stop_after`, `stop_count` and `stop_when`";
    let Json::Object(table) = document else {
        return Err(at(position, format!("`run` is a table of {KEYS}")));
    };
    let mut run = CaseRun::default();
    for (key, value) in table {
        match key.as_str() {
            "depth" => {
                run.depth = Some(value.as_u64().ok_or_else(|| {
                    at(
                        position,
                        "`depth` is a count of rewrite steps, a non-negative integer".to_owned(),
                    )
                })?);
            }
            "stop_before" | "stop_after" => {
                let names = match value {
                    Json::Array(items) => items
                        .iter()
                        .map(|item| item.as_str().map(str::to_owned))
                        .collect::<Option<Vec<_>>>(),
                    _ => None,
                }
                .ok_or_else(|| {
                    at(
                        position,
                        format!(
                            "`{key}` is an array of rule names (a KRS item or a K label), each a string"
                        ),
                    )
                })?;
                if key == "stop_before" {
                    run.stop_before = names;
                } else {
                    run.stop_after = names;
                }
            }
            "stop_count" => {
                run.stop_count =
                    Some(value.as_u64().and_then(NonZeroU64::new).ok_or_else(|| {
                        at(
                        position,
                        "`stop_count` is the arrival at a stop the run ends at, a positive integer"
                            .to_owned(),
                    )
                    })?);
            }
            "stop_when" => run.stop_when = Some(Box::new(stop_when(value, position)?)),
            _ => {
                return Err(at(
                    position,
                    format!("unknown key `{key}` in `run`; it has the keys {KEYS}"),
                ));
            }
        }
    }
    // A case's own `run` replaces its document's whole, so a rule the document's names is none
    // of the case's.
    let whole = if replaces {
        "; a case's own `run` replaces the document's `run` whole, so it names none of the \
         document's stop rules"
    } else {
        ""
    };
    if run.stop_when.is_some() && run.stop_before.is_empty() && run.stop_after.is_empty() {
        return Err(at(
            position,
            format!(
                "`stop_when` needs `stop_before` or `stop_after`: it is asked at the arrivals at their rules{whole}"
            ),
        ));
    }
    if run.stop_count.is_some() && run.stop_before.is_empty() && run.stop_after.is_empty() {
        return Err(at(
            position,
            format!(
                "`stop_count` needs `stop_before` or `stop_after`: it counts arrivals at their rules{whole}"
            ),
        ));
    }
    Ok(run)
}

/// A `run`'s `stop_when` table: `function`, `cells` and an optional `observer`.
fn stop_when(document: &Json, position: &str) -> Result<crate::StopWhen, InputError> {
    const SHAPE: &str = "`stop_when` is a table of `function` (a function's path), `cells` (the cells it reads, an array of Rust field paths) and an optional `observer` (`PACKAGE:DEFINITION`)";
    let Json::Object(table) = document else {
        return Err(at(position, SHAPE.to_owned()));
    };
    let mut function = None;
    let mut cells = None;
    let mut observer = None;
    for (key, value) in table {
        match key.as_str() {
            "function" => function = value.as_str().map(str::to_owned),
            "cells" => {
                cells = match value {
                    Json::Array(items) => items
                        .iter()
                        .map(|item| item.as_str().map(str::to_owned))
                        .collect::<Option<Vec<_>>>(),
                    _ => None,
                };
            }
            "observer" => observer = Some(value.as_str().map(str::to_owned)),
            _ => {
                return Err(at(
                    position,
                    format!("unknown key `{key}` in `stop_when`; {SHAPE}"),
                ));
            }
        }
    }
    match (function, cells, observer) {
        (Some(function), Some(cells), None) => Ok(crate::StopWhen {
            function,
            cells,
            observer: None,
        }),
        (Some(function), Some(cells), Some(Some(observer))) => Ok(crate::StopWhen {
            function,
            cells,
            observer: Some(observer),
        }),
        _ => Err(at(position, SHAPE.to_owned())),
    }
}

/// What `stutter` is, said where it is missing or is neither.
const STUTTER: &str = "`stutter` is `collapse` (an element equal to the last one kept is dropped, so the number of points is not observed) or `count` (every point is an element)";

impl ObservationSpec {
    /// The declaration a TOML text states: a document whose one key is `observe`, the table a
    /// case document gives ([module documentation](self#observations)).
    ///
    /// # Errors
    ///
    /// Returns [`InputError`] for a text that is no TOML document, a value [`toml_document`]
    /// refuses, and a document that is no declaration, naming the key.
    pub fn from_toml(text: &str) -> Result<Self, InputError> {
        Self::from_document(toml_text_document(text)?)
    }

    /// The declaration a JSON text states, as [`Self::from_toml`] reads a TOML one.
    ///
    /// # Errors
    ///
    /// Fails as [`Self::from_toml`] does, for a text [`json_document`] refuses.
    pub fn from_json(text: &str) -> Result<Self, InputError> {
        Self::from_document(json_document(text)?)
    }

    /// The declaration `document` (of the JSON data model) states, as [`Self::from_toml`] reads
    /// the document of a TOML text.
    ///
    /// # Errors
    ///
    /// Fails as [`Self::from_toml`] does.
    pub fn from_document(document: Json) -> Result<Self, InputError> {
        const SHAPE: &str = "an observation document is a table whose one key is `observe`, the table a case document gives";
        let Json::Object(mut top) = document else {
            return Err(InputError::document(SHAPE.to_owned()));
        };
        if let Some(key) = top.keys().find(|key| key.as_str() != "observe") {
            return Err(InputError::document(format!(
                "unknown key `{key}`; {SHAPE}"
            )));
        }
        let Some(observe) = top.remove("observe") else {
            return Err(InputError::document(SHAPE.to_owned()));
        };
        observe_table(&observe, "observe")
    }
}

/// The `observe` table `document` at `position` ([module documentation](self#observations)).
fn observe_table(document: &Json, position: &str) -> Result<ObservationSpec, InputError> {
    const KEYS: &str = "`observer`, `point` and `log`";
    let Json::Object(table) = document else {
        return Err(at(position, format!("`observe` is a table of {KEYS}")));
    };
    let mut spec = ObservationSpec::default();
    for (key, value) in table {
        match key.as_str() {
            "observer" => {
                spec.observer = Some(non_empty(value).ok_or_else(|| {
                    at(
                        position,
                        "`observer` is the definition the declaration's functions are evaluated in, `PACKAGE:DEFINITION`".to_owned(),
                    )
                })?);
            }
            "point" => {
                spec.points = tables(value, position, "point", "point classes")?
                    .into_iter()
                    .map(|(item, here)| point_class(item, &here))
                    .collect::<Result<_, _>>()?;
            }
            "log" => {
                spec.logs = tables(value, position, "log", "logs")?
                    .into_iter()
                    .map(|(item, here)| log_channel(item, &here))
                    .collect::<Result<_, _>>()?;
            }
            _ => {
                return Err(at(
                    position,
                    format!("unknown key `{key}` in `observe`; it has the keys {KEYS}"),
                ));
            }
        }
    }
    if spec.observer.is_some() && !spec.declares_function() {
        return Err(at(
            position,
            "`observer` names the definition the declaration's functions are evaluated in, and it declares none (no `views`, `components`, `when` or `element`)".to_owned(),
        ));
    }
    Ok(spec)
}

/// The items of the array `value` of the key `key` of the table at `position`, each with its
/// position: `{position}.{key}[{index}]`. `what` names the items.
fn tables<'d>(
    value: &'d Json,
    position: &str,
    key: &str,
    what: &str,
) -> Result<Vec<(&'d Json, String)>, InputError> {
    let Json::Array(items) = value else {
        return Err(at(
            position,
            format!("`{key}` is an array of {what}, each a table"),
        ));
    };
    let base = key_position(position, key);
    Ok(items
        .iter()
        .enumerate()
        .map(|(index, item)| (item, format!("{base}[{index}]")))
        .collect())
}

/// The string `value`, where it is a non-empty one.
fn non_empty(value: &Json) -> Option<String> {
    value
        .as_str()
        .filter(|text| !text.is_empty())
        .map(str::to_owned)
}

/// The array of strings `value`.
fn strings(value: &Json) -> Option<Vec<String>> {
    match value {
        Json::Array(items) => items
            .iter()
            .map(|item| item.as_str().map(str::to_owned))
            .collect(),
        _ => None,
    }
}

/// The `name` of a channel's table at `position`.
fn channel_name(value: &Json, position: &str) -> Result<String, InputError> {
    non_empty(value).ok_or_else(|| {
        at(
            position,
            "`name` is the channel's name, a non-empty string".to_owned(),
        )
    })
}

/// The `cells` of a table at `position`: leaf cells by Rust field path.
fn cell_paths(value: &Json, position: &str) -> Result<Vec<String>, InputError> {
    strings(value).ok_or_else(|| {
        at(
            position,
            "`cells` is an array of leaf cells by Rust field path, each a string".to_owned(),
        )
    })
}

/// The `function` of a table at `position`: a function's path.
fn function_path(value: &Json, position: &str) -> Result<String, InputError> {
    non_empty(value).ok_or_else(|| {
        at(
            position,
            "`function` is a function's KRS path (`crate::` and its path for the root package's), or a `::`-aligned suffix of it".to_owned(),
        )
    })
}

/// A point class at `position`.
fn point_class(document: &Json, position: &str) -> Result<PointClass, InputError> {
    const KEYS: &str =
        "`name`, `before`, `after`, `stutter`, `cells`, `views`, `components` and `when`";
    let Json::Object(table) = document else {
        return Err(at(position, format!("a point class is a table of {KEYS}")));
    };
    let mut name = None;
    let mut class = PointClass {
        name: String::new(),
        before: Vec::new(),
        after: Vec::new(),
        stutter: Stutter::Count,
        cells: Vec::new(),
        views: BTreeMap::new(),
        components: Vec::new(),
        when: None,
    };
    let mut stutter = None;
    for (key, value) in table {
        match key.as_str() {
            "name" => name = Some(channel_name(value, position)?),
            "before" | "after" => {
                let names = strings(value).ok_or_else(|| {
                    at(
                        position,
                        format!(
                            "`{key}` is an array of rule names (a KRS item or a K label), each a string"
                        ),
                    )
                })?;
                if key == "before" {
                    class.before = names;
                } else {
                    class.after = names;
                }
            }
            "stutter" => {
                stutter = Some(
                    value
                        .as_str()
                        .and_then(Stutter::parse)
                        .ok_or_else(|| at(position, STUTTER.to_owned()))?,
                );
            }
            "cells" => class.cells = cell_paths(value, position)?,
            "views" => {
                class.views = match value {
                    Json::Object(views) => views
                        .iter()
                        .map(|(cell, function)| Some((cell.clone(), non_empty(function)?)))
                        .collect::<Option<_>>(),
                    _ => None,
                }
                .ok_or_else(|| {
                    at(
                        position,
                        "`views` is a table of a function's path by cell of `cells`".to_owned(),
                    )
                })?;
            }
            "components" => {
                class.components = tables(value, position, "components", "components")?
                    .into_iter()
                    .map(|(item, here)| component(item, &here))
                    .collect::<Result<_, _>>()?;
            }
            "when" => class.when = Some(filter(value, position)?),
            _ => {
                return Err(at(
                    position,
                    format!("unknown key `{key}` in a point class; it has the keys {KEYS}"),
                ));
            }
        }
    }
    class.name = name.ok_or_else(|| {
        at(
            position,
            "a point class has a `name`, its channel's name".to_owned(),
        )
    })?;
    class.stutter = stutter.ok_or_else(|| {
        at(
            position,
            format!(
                "a point class has a `stutter`, which has no default: {STUTTER}; which one a specification promises is its author's statement"
            ),
        )
    })?;
    Ok(class)
}

/// A component of a point class at `position`: `{ name, cells, function }`.
fn component(document: &Json, position: &str) -> Result<Component, InputError> {
    const SHAPE: &str = "a component is a table of `name`, `cells` (the cells it reads, an array of Rust field paths) and `function` (a function's path)";
    let Json::Object(table) = document else {
        return Err(at(position, SHAPE.to_owned()));
    };
    let (mut name, mut cells, mut function) = (None, None, None);
    for (key, value) in table {
        match key.as_str() {
            "name" => {
                name = Some(non_empty(value).ok_or_else(|| {
                    at(
                        position,
                        "`name` is the component's name, a non-empty string".to_owned(),
                    )
                })?);
            }
            "cells" => cells = Some(cell_paths(value, position)?),
            "function" => function = Some(function_path(value, position)?),
            _ => {
                return Err(at(
                    position,
                    format!("unknown key `{key}` in a component; {SHAPE}"),
                ));
            }
        }
    }
    match (name, cells, function) {
        (Some(name), Some(cells), Some(function)) => Ok(Component {
            name,
            cells,
            function,
        }),
        _ => Err(at(position, SHAPE.to_owned())),
    }
}

/// A point class's `when` table, at the class's `position`: `{ function, cells }`.
fn filter(document: &Json, position: &str) -> Result<Filter, InputError> {
    const SHAPE: &str = "`when` is a table of `function` (a function's path, of result sort `Bool`) and `cells` (the cells it reads, an array of Rust field paths)";
    let Json::Object(table) = document else {
        return Err(at(position, SHAPE.to_owned()));
    };
    let (mut function, mut cells) = (None, None);
    for (key, value) in table {
        match key.as_str() {
            "function" => function = Some(function_path(value, position)?),
            "cells" => cells = Some(cell_paths(value, position)?),
            _ => {
                return Err(at(
                    position,
                    format!("unknown key `{key}` in `when`; {SHAPE}"),
                ));
            }
        }
    }
    match (function, cells) {
        (Some(function), Some(cells)) => Ok(Filter { function, cells }),
        _ => Err(at(position, SHAPE.to_owned())),
    }
}

/// A log at `position`.
fn log_channel(document: &Json, position: &str) -> Result<LogChannel, InputError> {
    const KEYS: &str = "`name`, `cell`, `element` and `at`";
    let Json::Object(table) = document else {
        return Err(at(position, format!("a log is a table of {KEYS}")));
    };
    let (mut name, mut cell, mut element, mut read_at) = (None, None, None, Vec::new());
    for (key, value) in table {
        match key.as_str() {
            "name" => name = Some(channel_name(value, position)?),
            "cell" => {
                cell = Some(non_empty(value).ok_or_else(|| {
                    at(
                        position,
                        "`cell` is the log's `List` leaf cell, by Rust field path".to_owned(),
                    )
                })?);
            }
            "element" => {
                element = Some(function_path(value, position).map_err(|_| {
                    at(
                        position,
                        "`element` is the path of a function `Item -> List<_>`, applied to each appended item".to_owned(),
                    )
                })?);
            }
            "at" => {
                read_at = strings(value).ok_or_else(|| {
                    at(
                        position,
                        "`at` is an array of the names of the point classes at whose points the log is read".to_owned(),
                    )
                })?;
            }
            _ => {
                return Err(at(
                    position,
                    format!("unknown key `{key}` in a log; it has the keys {KEYS}"),
                ));
            }
        }
    }
    let name = name.ok_or_else(|| {
        at(
            position,
            "a log has a `name`, its channel's name".to_owned(),
        )
    })?;
    let cell = cell.ok_or_else(|| {
        at(
            position,
            "a log has a `cell`, its `List` leaf cell by Rust field path".to_owned(),
        )
    })?;
    Ok(LogChannel {
        name,
        cell,
        element,
        at: read_at,
    })
}

/// One leaf cell's content that a case's `instances` states, read at the cell's declared type
/// ([module documentation](self#instances)).
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct StatedLeaf {
    /// The content's term, typed at the cell's content sort.
    pub(crate) term: k_rust::kore::ast::Pattern,
    /// The content's value where it is data, with no function application and no opaque part:
    /// what a `Map` collection's key is compared by. `None` otherwise.
    pub(crate) value: Option<Value>,
    /// The content as a refusal shows it: its canonical document's text, or its KORE text.
    pub(crate) shown: String,
}

/// A cell that a case's `instances` states ([module documentation](self#instances)).
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum StatedCell {
    /// A leaf cell's content.
    Leaf(StatedLeaf),
    /// A group cell's stated cells, each by its index among the group's cells, in declaration
    /// order; the cells it does not state keep their start.
    Group(Vec<(usize, StatedCell)>),
    /// An optional cell's instance, or none (absent).
    Optional(Option<Box<StatedCell>>),
    /// A repeated cell's instances, in the document's order.
    Repeated(Vec<StatedCell>),
}

/// How [`read_instances`] reads one stated leaf cell: the cell, its document, and the position
/// of the document (`instances.harts.hart[0].pc`) for a refusal's message; the error is the
/// message alone.
pub(crate) type LeafReader<'a> =
    dyn FnMut(&CellNode, &Json, &str) -> Result<StatedLeaf, String> + 'a;

/// The instances the `instances` table `document` states, for the configuration whose root
/// cells are `nodes`: each stated cell by its index among `nodes`, in declaration order, every
/// leaf read by `leaf` ([module documentation](self#instances)).
///
/// # Errors
///
/// Returns [`InputError`] naming the position (`instances.harts.hart[1]`) for a path that names a
/// fixed cell or no cell, an optional or repeated cell stated otherwise than its encoding, a cell
/// of an instance that is no cell of it, a `Map` collection's instance that does not state its
/// whole key as a value or that shares its key with another, two `Set` collection's instances
/// stated alike, and a leaf `leaf` refuses.
pub(crate) fn read_instances(
    nodes: &[CellNode],
    document: &Json,
    leaf: &mut LeafReader<'_>,
) -> Result<Vec<(usize, StatedCell)>, InputError> {
    let Json::Object(table) = document else {
        return Err(at(
            "instances",
            "`instances` is a table of the starting instances of optional and repeated cells, by Rust field path"
                .to_owned(),
        ));
    };
    InstanceReader { roots: nodes, leaf }.fixed(nodes, table, "instances", "")
}

/// Reads one `instances` table ([`read_instances`]).
struct InstanceReader<'n, 'l, 'r> {
    /// The configuration's root cells, for the list of the cells a case may state.
    roots: &'n [CellNode],
    leaf: &'l mut LeafReader<'r>,
}

impl InstanceReader<'_, '_, '_> {
    /// The cells `table` states of the fixed cells `nodes`, outside every instance: `position`
    /// is the table's position, `prefix` the cells' Rust field path prefix (`harts.`).
    fn fixed(
        &mut self,
        nodes: &[CellNode],
        table: &serde_json::Map<String, Json>,
        position: &str,
        prefix: &str,
    ) -> Result<Vec<(usize, StatedCell)>, InputError> {
        let mut stated = Vec::new();
        for (field, document) in table {
            let (index, node) = Self::child(nodes, field, position, prefix)?;
            let here = format!("{position}.{field}");
            let path = format!("{prefix}{field}");
            let cell = match (node.multiplicity, node.children.is_empty(), document) {
                (Some(_), _, _) => self.holder(node, document, &here)?,
                (None, false, Json::Object(inner)) => StatedCell::Group(self.fixed(
                    &node.children,
                    inner,
                    &here,
                    &format!("{path}."),
                )?),
                (None, _, _) => {
                    return Err(at(
                        &here,
                        format!(
                            "`{path}` is a fixed {}: the initializer states its start from the inputs, and a case states only the instances of optional and repeated cells ({}); bind other inputs to start it otherwise",
                            if node.children.is_empty() {
                                "cell"
                            } else {
                                "group cell, here not a table of its cells"
                            },
                            self.holders()
                        ),
                    ));
                }
            };
            stated.push((index, cell));
        }
        stated.sort_by_key(|(index, _)| *index);
        Ok(stated)
    }

    /// The cell of `nodes` that `field` names, refused listing the cells there.
    fn child<'n>(
        nodes: &'n [CellNode],
        field: &str,
        position: &str,
        prefix: &str,
    ) -> Result<(usize, &'n CellNode), InputError> {
        nodes
            .iter()
            .enumerate()
            .find(|(_, node)| node.field == field)
            .ok_or_else(|| {
                at(
                    &format!("{position}.{field}"),
                    format!(
                        "no cell has the path `{prefix}{field}`; the cells are {}",
                        nodes
                            .iter()
                            .map(|node| format!("`{prefix}{}`", node.field))
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                )
            })
    }

    /// The optional and repeated cells a case may state, outside every instance: the ones below
    /// the roots through fixed group cells.
    fn holders(&self) -> String {
        fn walk(nodes: &[CellNode], prefix: &str, output: &mut Vec<String>) {
            for node in nodes {
                let path = format!("{prefix}{}", node.field);
                if node.multiplicity.is_some() {
                    output.push(format!("`{path}`"));
                } else {
                    walk(&node.children, &format!("{path}."), output);
                }
            }
        }
        let mut holders = Vec::new();
        walk(self.roots, "", &mut holders);
        if holders.is_empty() {
            "the configuration has none".to_owned()
        } else {
            format!("here {}", holders.join(", "))
        }
    }

    /// The instances `document` states of the optional or repeated cell `node`.
    fn holder(
        &mut self,
        node: &CellNode,
        document: &Json,
        position: &str,
    ) -> Result<StatedCell, InputError> {
        match (node.multiplicity, document) {
            (Some(CellMultiplicity::Optional), Json::Array(items)) if items.len() <= 1 => {
                Ok(StatedCell::Optional(match items.first() {
                    None => None,
                    Some(item) => Some(Box::new(self.instance(
                        node,
                        item,
                        &format!("{position}[0]"),
                    )?)),
                }))
            }
            (Some(CellMultiplicity::Optional), _) => Err(at(
                position,
                format!(
                    "the optional cell `{}` is stated `[]` (absent) or `[content]` (present)",
                    node.field
                ),
            )),
            (Some(CellMultiplicity::Star), Json::Array(items)) => {
                let instances = items
                    .iter()
                    .enumerate()
                    .map(|(index, item)| self.instance(node, item, &format!("{position}[{index}]")))
                    .collect::<Result<Vec<_>, _>>()?;
                Self::distinct(node, &instances, position)?;
                Ok(StatedCell::Repeated(instances))
            }
            _ => Err(at(
                position,
                format!(
                    "the repeated cell `{}` is stated as the array of its instances",
                    node.field
                ),
            )),
        }
    }

    /// Refuse two instances of the repeated cell `node` that one collection cannot hold both
    /// of: in a `Map` collection, two with one key, and one that does not state its whole key as
    /// a value; in a `Set` collection, two stated alike.
    fn distinct(
        node: &CellNode,
        instances: &[StatedCell],
        position: &str,
    ) -> Result<(), InputError> {
        match node.collection {
            Some(CellCollectionType::Map) if !node.children.is_empty() => {
                let key = &node.children[0];
                let mut keys = Vec::<Vec<&Value>>::new();
                for (index, instance) in instances.iter().enumerate() {
                    let here = format!("{position}[{index}]");
                    let stated = match instance {
                        StatedCell::Group(cells) => cells
                            .iter()
                            .find_map(|(child, cell)| (*child == 0).then_some(cell)),
                        _ => None,
                    };
                    let Some(stated) = stated else {
                        return Err(at(
                            &here,
                            format!(
                                "an instance of the Map collection `{}` states its key, its first cell `{}`: the key is the instance's identity",
                                node.field, key.field
                            ),
                        ));
                    };
                    let value = Self::key(key, stated, &format!("{here}.{}", key.field))?;
                    if let Some(first) = keys.iter().position(|other| *other == value) {
                        return Err(at(
                            &here,
                            format!(
                                "the instance has the key {} of the instance at [{first}]: a Map collection holds one instance per key, its first cell `{}`",
                                Self::shown(stated),
                                key.field
                            ),
                        ));
                    }
                    keys.push(value);
                }
            }
            Some(CellCollectionType::Set) => {
                for (index, instance) in instances.iter().enumerate() {
                    if let Some(first) = instances[..index]
                        .iter()
                        .position(|other| other == instance)
                    {
                        return Err(at(
                            &format!("{position}[{index}]"),
                            format!(
                                "the instance is stated as the instance at [{first}] is: a Set collection holds an instance once, and two instances with the same cells are one"
                            ),
                        ));
                    }
                }
            }
            _ => {}
        }
        Ok(())
    }

    /// The values of the key `stated` states of the key cell `node`, in pre-order of its leaves;
    /// refused unless it states every leaf of the key as a value.
    fn key<'s>(
        node: &CellNode,
        stated: &'s StatedCell,
        position: &str,
    ) -> Result<Vec<&'s Value>, InputError> {
        let refuse = |message: String| Err(at(position, message));
        match stated {
            StatedCell::Leaf(leaf) => match &leaf.value {
                Some(value) => Ok(vec![value]),
                None => refuse(format!(
                    "the key {} is no value: a Map collection's key is compared with the other instances' keys before the run, so it is stated as a value, with no function application",
                    leaf.shown
                )),
            },
            StatedCell::Group(cells) => {
                let mut values = Vec::new();
                for (index, child) in node.children.iter().enumerate() {
                    let Some(cell) = cells
                        .iter()
                        .find_map(|(stated, cell)| (*stated == index).then_some(cell))
                    else {
                        return refuse(format!(
                            "the key does not state `{}`: a Map collection's instance states its whole key, its identity",
                            child.field
                        ));
                    };
                    values.extend(Self::key(
                        child,
                        cell,
                        &format!("{position}.{}", child.field),
                    )?);
                }
                Ok(values)
            }
            StatedCell::Optional(_) | StatedCell::Repeated(_) => {
                refuse("a Map collection's key is a fixed cell".to_owned())
            }
        }
    }

    /// A stated key as a refusal shows it.
    fn shown(stated: &StatedCell) -> String {
        match stated {
            StatedCell::Leaf(leaf) => leaf.shown.clone(),
            StatedCell::Group(cells) => format!(
                "{{{}}}",
                cells
                    .iter()
                    .map(|(_, cell)| Self::shown(cell))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            StatedCell::Optional(_) | StatedCell::Repeated(_) => String::new(),
        }
    }

    /// One instance of the optional or repeated cell `node`: the table of its cells, or the
    /// document of a leaf cell's content.
    fn instance(
        &mut self,
        node: &CellNode,
        document: &Json,
        position: &str,
    ) -> Result<StatedCell, InputError> {
        if node.children.is_empty() {
            return self.leaf(node, document, position);
        }
        let Json::Object(table) = document else {
            return Err(at(
                position,
                format!(
                    "an instance of `{}` is a table of its cells by Rust field",
                    node.field
                ),
            ));
        };
        self.cells(node, table, position).map(StatedCell::Group)
    }

    /// The cells `table` states of the group cell `node` inside an instance.
    fn cells(
        &mut self,
        node: &CellNode,
        table: &serde_json::Map<String, Json>,
        position: &str,
    ) -> Result<Vec<(usize, StatedCell)>, InputError> {
        let mut stated = Vec::new();
        for (field, document) in table {
            let (index, child) = Self::child(&node.children, field, position, "")?;
            let here = format!("{position}.{field}");
            let cell = match (child.multiplicity, child.children.is_empty(), document) {
                (Some(_), _, _) => self.holder(child, document, &here)?,
                (None, true, _) => self.leaf(child, document, &here)?,
                (None, false, Json::Object(inner)) => {
                    StatedCell::Group(self.cells(child, inner, &here)?)
                }
                (None, false, _) => {
                    return Err(at(
                        &here,
                        format!("the group cell `{field}` is a table of its cells by Rust field"),
                    ));
                }
            };
            stated.push((index, cell));
        }
        stated.sort_by_key(|(index, _)| *index);
        Ok(stated)
    }

    fn leaf(
        &mut self,
        node: &CellNode,
        document: &Json,
        position: &str,
    ) -> Result<StatedCell, InputError> {
        (self.leaf)(node, document, position)
            .map(StatedCell::Leaf)
            .map_err(|message| at(position, message))
    }
}

/// Reads the named cases of a document, following its `$data-file` includes.
struct CaseReader<'a> {
    files: &'a mut dyn InputFiles,
    /// The resolved name of the file that holds the document, when one does.
    top: Option<String>,
    /// The resolved names of the included files being read, outermost first.
    includes: Vec<String>,
    cases: Vec<Case>,
    /// Each name taken, with the position of its case.
    names: BTreeMap<String, String>,
}

impl CaseReader<'_> {
    /// The case list `document` at `position`: an array of named cases and includes, or an
    /// include of a file that holds one.
    fn list(
        &mut self,
        document: &Json,
        position: &str,
        shared: Shared<'_>,
    ) -> Result<(), InputError> {
        if let Some(path) = Self::include(document, position)? {
            return self.included(path, position, shared);
        }
        let Json::Array(items) = document else {
            return Err(at(
                position,
                "a list of named cases is an array of cases (TOML's `[[case]]` tables), each with a `name`, and `{\"$data-file\": path}` includes".to_owned(),
            ));
        };
        for (index, item) in items.iter().enumerate() {
            let here = format!("{position}[{index}]");
            if let Some(path) = Self::include(item, &here)? {
                self.included(path, &here, shared)?;
                continue;
            }
            let Json::Object(table) = item else {
                return Err(at(
                    &here,
                    "a named case is a table of `name`, `inputs`, `run`, `observe`, `instances` and `expect`"
                        .to_owned(),
                ));
            };
            let name = match table.get("name") {
                Some(Json::String(name)) if !name.is_empty() => name.clone(),
                Some(_) => {
                    return Err(at(&here, "a case's name is a non-empty string".to_owned()));
                }
                None => {
                    return Err(at(
                        &here,
                        "a case in a list of named cases has a `name`".to_owned(),
                    ));
                }
            };
            if let Some(first) = self.names.get(&name) {
                return Err(at(
                    &here,
                    format!(
                        "the name `{name}` is also the name of the case at `{first}`; the cases of a document have distinct names"
                    ),
                ));
            }
            self.names.insert(name.clone(), here.clone());
            let mut table = table.clone();
            table.remove("name");
            let file = self.includes.last().map(String::as_str);
            let case = case_table(table, &here, Some(name), shared, file)?;
            self.cases.push(case);
        }
        Ok(())
    }

    /// The path an include (`{"$data-file": path}`) names, or `None` for any other document.
    fn include<'d>(document: &'d Json, position: &str) -> Result<Option<&'d str>, InputError> {
        match tagged(document).map_err(|message| at(position, message))? {
            None => Ok(None),
            Some(("$data-file", Json::String(path))) => Ok(Some(path)),
            Some(("$data-file", _)) => {
                Err(at(position, "`$data-file` takes a path string".to_owned()))
            }
            Some((tag, _)) => Err(at(
                position,
                format!(
                    "`{tag}` is no case; a list of named cases includes a file with `$data-file`"
                ),
            )),
        }
    }

    /// The cases of the file `path`, included at `position`, which holds a case list: an array,
    /// or a table whose one key is `case` (TOML's form of an array).
    fn included(
        &mut self,
        path: &str,
        position: &str,
        shared: Shared<'_>,
    ) -> Result<(), InputError> {
        let from = self.includes.last().map(String::as_str);
        let (name, bytes) = self
            .files
            .read(from, path)
            .map_err(|message| at(position, format!("`$data-file` `{path}`: {message}")))?;
        // The file holding the document is the outermost of the files being read.
        let reading = self
            .top
            .iter()
            .chain(&self.includes)
            .cloned()
            .collect::<Vec<_>>();
        if let Some(cycle) = include_cycle(&reading, &name) {
            return Err(at(position, cycle));
        }
        let document = data_document(&name, bytes).map_err(|message| at(position, message))?;
        // A position spells the path as the document writes it; the cycle check and the
        // reads use the resolved name.
        let here = format!("{position}$data-file({path})");
        let list = match document {
            Json::Object(mut table) if table.len() == 1 && table.contains_key("case") => {
                table.remove("case").unwrap_or(Json::Null)
            }
            Json::Array(items) => Json::Array(items),
            _ => {
                return Err(at(
                    &here,
                    "an included file of named cases holds their list: an array, or a table whose one key is `case`".to_owned(),
                ));
            }
        };
        self.includes.push(name);
        let read = self.list(&list, &here, shared);
        self.includes.pop();
        read
    }
}

/// Why a document is no value of its input: the input and its declared type, the position
/// inside the document (`["A"]`, `[3]`, `.Run.steps`, `$call(boot::map_rom).rom`), and the
/// reason.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InputError {
    /// The input's parameter, when the document is one input's.
    pub parameter: Option<String>,
    /// The parameter's declared type (`Map<Reg8, Int>`).
    pub declared: Option<String>,
    /// Where in the document; empty for the whole document.
    pub position: String,
    /// Why.
    pub message: String,
}

impl InputError {
    const fn document(message: String) -> Self {
        Self {
            parameter: None,
            declared: None,
            position: String::new(),
            message,
        }
    }
}

impl fmt::Display for InputError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut prefixed = false;
        if let Some(parameter) = &self.parameter {
            write!(formatter, "input `{parameter}`")?;
            if let Some(declared) = &self.declared {
                write!(formatter, " ({declared})")?;
            }
            prefixed = true;
        }
        if !self.position.is_empty() {
            if prefixed {
                formatter.write_str(" ")?;
            }
            write!(formatter, "at `{}`", self.position)?;
            prefixed = true;
        }
        if prefixed {
            formatter.write_str(": ")?;
        }
        formatter.write_str(&self.message)
    }
}

impl std::error::Error for InputError {}

/// A TOML value in the JSON data model, as the encoding reads TOML.
///
/// A finite float is a number; a NaN or an infinity is the tagged `$float` of its K literal, so
/// that numbers stay finite; a datetime is refused. The conversion matches the TOML value
/// itself rather than going through serde, which renders a datetime as a map with a private key.
///
/// # Errors
///
/// Returns [`InputError`] for a datetime, naming where it is.
pub fn toml_document(value: &toml::Value) -> Result<Json, InputError> {
    fn convert(value: &toml::Value, position: &mut Vec<String>) -> Result<Json, InputError> {
        Ok(match value {
            toml::Value::String(text) => Json::String(text.clone()),
            toml::Value::Integer(integer) => Json::from(*integer),
            toml::Value::Boolean(boolean) => Json::Bool(*boolean),
            toml::Value::Float(float) => {
                if let Some(number) = serde_json::Number::from_f64(*float) {
                    Json::Number(number)
                } else {
                    let literal = if float.is_nan() {
                        "NaN"
                    } else if float.is_sign_negative() {
                        "-Infinity"
                    } else {
                        "Infinity"
                    };
                    serde_json::json!({ "$float": literal })
                }
            }
            toml::Value::Datetime(_) => {
                return Err(InputError {
                    parameter: None,
                    declared: None,
                    position: position.concat(),
                    message: "a TOML datetime has no reading as a term".to_owned(),
                });
            }
            toml::Value::Array(items) => {
                let mut converted = Vec::with_capacity(items.len());
                for (index, item) in items.iter().enumerate() {
                    position.push(format!("[{index}]"));
                    converted.push(convert(item, position)?);
                    position.pop();
                }
                Json::Array(converted)
            }
            toml::Value::Table(table) => {
                let mut converted = serde_json::Map::new();
                for (key, item) in table {
                    position.push(format!("[{}]", Json::String(key.clone())));
                    converted.insert(key.clone(), convert(item, position)?);
                    position.pop();
                }
                Json::Object(converted)
            }
        })
    }
    convert(value, &mut Vec::new())
}

/// A JSON text as a document, with a key repeated in one object refused: a repeated key would
/// otherwise keep only its last value, so the document would mean something its text does not
/// say. The nesting limit of `serde_json` applies.
///
/// # Errors
///
/// Returns [`InputError`] for a text that is no JSON, or an object with a repeated key.
pub fn json_document(text: &str) -> Result<Json, InputError> {
    use serde::de::DeserializeSeed as _;
    let mut deserializer = serde_json::Deserializer::from_str(text);
    let document = UniqueKeys
        .deserialize(&mut deserializer)
        .and_then(|document| deserializer.end().map(|()| document))
        .map_err(|error| InputError::document(format!("the document is no JSON: {error}")))?;
    Ok(document)
}

/// A JSON value with every object's keys distinct ([`json_document`]).
struct UniqueKeys;

impl<'de> serde::de::DeserializeSeed<'de> for UniqueKeys {
    type Value = Json;

    fn deserialize<D: serde::Deserializer<'de>>(self, deserializer: D) -> Result<Json, D::Error> {
        deserializer.deserialize_any(self)
    }
}

impl<'de> serde::de::Visitor<'de> for UniqueKeys {
    type Value = Json;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("a JSON value")
    }

    fn visit_bool<E>(self, value: bool) -> Result<Json, E> {
        Ok(Json::Bool(value))
    }

    fn visit_i64<E>(self, value: i64) -> Result<Json, E> {
        Ok(Json::from(value))
    }

    fn visit_u64<E>(self, value: u64) -> Result<Json, E> {
        Ok(Json::from(value))
    }

    fn visit_f64<E>(self, value: f64) -> Result<Json, E> {
        Ok(serde_json::Number::from_f64(value).map_or(Json::Null, Json::Number))
    }

    fn visit_str<E>(self, value: &str) -> Result<Json, E> {
        Ok(Json::String(value.to_owned()))
    }

    fn visit_string<E>(self, value: String) -> Result<Json, E> {
        Ok(Json::String(value))
    }

    fn visit_unit<E>(self) -> Result<Json, E> {
        Ok(Json::Null)
    }

    fn visit_none<E>(self) -> Result<Json, E> {
        Ok(Json::Null)
    }

    fn visit_seq<A: serde::de::SeqAccess<'de>>(self, mut sequence: A) -> Result<Json, A::Error> {
        let mut items = Vec::new();
        while let Some(item) = sequence.next_element_seed(UniqueKeys)? {
            items.push(item);
        }
        Ok(Json::Array(items))
    }

    fn visit_map<A: serde::de::MapAccess<'de>>(self, mut map: A) -> Result<Json, A::Error> {
        let mut object = serde_json::Map::new();
        while let Some(key) = map.next_key::<String>()? {
            let value = map.next_value_seed(UniqueKeys)?;
            if object.contains_key(&key) {
                return Err(serde::de::Error::custom(format!(
                    "the key `{key}` is repeated in one object"
                )));
            }
            object.insert(key, value);
        }
        Ok(Json::Object(object))
    }
}

/// The parameters of `definition`'s `#[k::init]`, in declaration order, with their types named
/// by `values`; `declared` is the compiled definition's configuration variables, whose K sort
/// types a parameter whose IR sort no KRS declaration names, and `defaulted` says by K name
/// whether the compiled definition carries a variable's default, the value a configuration
/// binds for it when it is given none.
pub(crate) fn parameters(
    definition: &DefinitionIr,
    values: &ValueIndex,
    declared: &BTreeMap<String, KastSort>,
    defaulted: impl Fn(&str) -> bool,
) -> Vec<Parameter> {
    let mut parameters = Vec::new();
    for sentence in definition
        .modules()
        .iter()
        .flat_map(krs_ir_levels::DefinitionModule::sentences)
    {
        let DefinitionSentence::Configuration(configuration) = sentence else {
            continue;
        };
        for variable in configuration.variables() {
            let name = variable.external_name();
            // A sort no KRS declaration names (a cell sort) is read as the compiled definition
            // declares it, or untyped, where the assembler still checks the term's sort.
            let ty = input_type(values, variable.sort(), variable.arguments())
                .or_else(|| {
                    declared
                        .get(name)
                        .and_then(|sort| {
                            values.sort_of_kore(&crate::values::kore_sort_name(&sort.name))
                        })
                        .map(InputType::of)
                })
                .unwrap_or_else(InputType::untyped);
            parameters.push(Parameter {
                name: variable.id().as_str().to_owned(),
                variable: name.to_owned(),
                ty,
                main: variable.is_main(),
                has_default: defaulted(name),
            });
        }
    }
    parameters
}

/// The declared type an IR sort and its element types name, when KRS names each of them: a
/// builtin, or a declared sort with a KRS declaration.
pub(crate) fn input_type(
    values: &ValueIndex,
    sort: &DefinitionSortRef,
    arguments: &[CellSortArgument<DefinitionSortRef>],
) -> Option<InputType> {
    Some(InputType {
        sort: values.sort_ref(sort)?,
        arguments: arguments
            .iter()
            .map(|argument| input_type(values, &argument.sort, &argument.arguments))
            .collect::<Option<_>>()?,
    })
}

/// Why a document is no value at a position: where, and why; [`decode`]'s caller adds the input.
#[derive(Debug)]
pub(crate) struct Refusal {
    pub(crate) position: String,
    pub(crate) message: String,
}

/// What a whole input's document gives: K text to parse, or a value.
pub(crate) enum Decoded {
    /// `$text`.
    Text(String),
    /// `$text-file`, with the file's resolved name.
    TextFile(ProgramInput),
    /// Any other document.
    Value(Value),
}

impl From<Decoded> for ConfigValue {
    fn from(decoded: Decoded) -> Self {
        match decoded {
            Decoded::Text(text) => Self::Text(text),
            Decoded::TextFile(file) => Self::TextFile(file),
            Decoded::Value(value) => Self::Value(value),
        }
    }
}

/// Decode `document`, the whole value of an input declared `ty`, written in the data file `from`
/// (a resolved name [`InputFiles::read`] returned) or in the top document (`None`).
pub(crate) fn decode(
    values: &ValueIndex,
    files: &mut dyn InputFiles,
    from: Option<&str>,
    document: &Json,
    ty: &InputType,
) -> Result<Decoded, Refusal> {
    let mut decoder = Decoder::new(values, files);
    decoder.includes.extend(from.map(str::to_owned));
    match tagged(document) {
        Ok(Some(("$text", body))) => {
            let Json::String(text) = body else {
                return Err(decoder.refuse("`$text` takes a string of K text"));
            };
            Ok(Decoded::Text(text.clone()))
        }
        Ok(Some(("$text-file", body))) => {
            let (name, bytes) = decoder.read_file("$text-file", body)?;
            let text = String::from_utf8(bytes)
                .map_err(|_| decoder.refuse(&format!("`$text-file` `{name}` is no UTF-8 text")))?;
            Ok(Decoded::TextFile(ProgramInput { name, text }))
        }
        Ok(_) => decoder.decode(document, ty).map(Decoded::Value),
        Err(message) => Err(decoder.refuse(&format!("{message}{}", decoder.dollar_key_hint(ty)))),
    }
}

/// Decode `document` at `ty`, below a whole input (`$text` and `$text-file` are refused),
/// written in the data file `from` or in the top document (`None`): `files` reads the files it
/// names.
pub(crate) fn decode_value_in(
    values: &ValueIndex,
    files: &mut dyn InputFiles,
    from: Option<&str>,
    document: &Json,
    ty: &InputType,
) -> Result<Value, InputError> {
    let mut decoder = Decoder::new(values, files);
    decoder.includes.extend(from.map(str::to_owned));
    decoder.decode(document, ty).map_err(|refusal| InputError {
        parameter: None,
        declared: Some(ty.to_string()),
        position: refusal.position,
        message: refusal.message,
    })
}

/// Decode `document` at `ty`, below a whole input: `$text` and `$text-file` are refused, and
/// no file is read.
pub(crate) fn decode_value(
    values: &ValueIndex,
    document: &Json,
    ty: &InputType,
) -> Result<Value, Refusal> {
    let mut files = NoFiles;
    Decoder::new(values, &mut files).decode(document, ty)
}

/// Whether the decoder resolves `name` at `ty` to exactly `decl`, among the functions
/// (`function`) or the constructors: the encoder's choice of a name is the decoder's own
/// resolution.
pub(crate) fn names(
    values: &ValueIndex,
    name: &str,
    ty: &InputType,
    function: bool,
    decl: &Decl,
) -> bool {
    let mut files = NoFiles;
    Decoder::new(values, &mut files)
        .resolve(name, ty, function)
        .is_ok_and(|resolved| resolved == *decl)
}

/// Whether the shorthand `document` has exactly one reading at `ty`, by the decoder's own
/// table: the readings of a string, a number, a boolean or an array depend on the document's
/// JSON type and text, and an object's on its key, never on what it holds.
pub(crate) fn sole_reading(values: &ValueIndex, document: &Json, ty: &InputType) -> bool {
    let mut files = NoFiles;
    Decoder::new(values, &mut files)
        .readings(document, ty, false)
        .is_ok_and(|readings| readings.len() == 1)
}

/// The key the object key `written` denotes at `ty`, when it has exactly one reading there.
pub(crate) fn map_key(values: &ValueIndex, written: &str, ty: &InputType) -> Option<Value> {
    let mut files = NoFiles;
    Decoder::new(values, &mut files).map_key(written, ty).ok()
}

/// Why including the data file `name` from the files `includes` (outermost first) is refused:
/// it is one of them, so it includes itself.
fn include_cycle(includes: &[String], name: &str) -> Option<String> {
    let start = includes.iter().position(|included| included == name)?;
    let cycle = includes[start..]
        .iter()
        .map(String::as_str)
        .chain([name])
        .map(|name| format!("`{name}`"))
        .collect::<Vec<_>>()
        .join(" includes ");
    Some(format!("`$data-file` includes itself: {cycle}"))
}

/// The document the data file `name` holds, read by its extension (`.json` or `.toml`), or why
/// it holds none.
fn data_document(name: &str, bytes: Vec<u8>) -> Result<Json, String> {
    let text =
        String::from_utf8(bytes).map_err(|_| format!("`$data-file` `{name}` is no UTF-8 text"))?;
    let extension = std::path::Path::new(name)
        .extension()
        .and_then(std::ffi::OsStr::to_str)
        .unwrap_or_default();
    if extension.eq_ignore_ascii_case("json") {
        json_document(&text)
    } else if extension.eq_ignore_ascii_case("toml") {
        text.parse::<toml::Table>()
            .map_err(|error| InputError::document(format!("no TOML document: {error}")))
            .and_then(|table| toml_document(&toml::Value::Table(table)))
    } else {
        Err(InputError::document(
            "a data file is `.json` or `.toml`, by its extension".to_owned(),
        ))
    }
    .map_err(|error| {
        let position = if error.position.is_empty() {
            String::new()
        } else {
            format!(" at `{}`", error.position)
        };
        format!("`$data-file` `{name}`{position}: {}", error.message)
    })
}

/// The tag and body of a tagged form; `None` for any other document. An object with a `$` key
/// among others is no tagged form and no other form either.
fn tagged(document: &Json) -> Result<Option<(&str, &Json)>, String> {
    let Json::Object(object) = document else {
        return Ok(None);
    };
    if !object.keys().any(|key| key.starts_with('$')) {
        return Ok(None);
    }
    let mut entries = object.iter();
    match (entries.next(), entries.next()) {
        (Some((tag, body)), None) => Ok(Some((tag.as_str(), body))),
        _ => Err(format!(
            "a tagged form is an object with exactly one key; this one has {}",
            object
                .keys()
                .map(|key| format!("`{key}`"))
                .collect::<Vec<_>>()
                .join(", ")
        )),
    }
}

/// A JSON number, as the encoding reads it.
enum Number {
    /// An integer JSON delivered exactly.
    Integer(BigInt),
    /// Any other number: one with a fraction or an exponent, or an integer beyond 64 bits.
    Float(f64),
}

fn number(number: &serde_json::Number) -> Number {
    if let Some(integer) = number.as_i64() {
        Number::Integer(integer.into())
    } else if let Some(integer) = number.as_u64() {
        Number::Integer(integer.into())
    } else {
        Number::Float(number.as_f64().unwrap_or(f64::NAN))
    }
}

/// The `Int` an integer string spells: an optional `-`, then decimal digits, or `0x`, `0o` or
/// `0b` and digits of that base.
pub(crate) fn parse_int(text: &str) -> Result<BigInt, String> {
    let refuse = || {
        format!(
            "`{text}` is no integer: write an optional `-` and decimal digits, or `0x`, `0o` or `0b` and digits of that base"
        )
    };
    let (negative, unsigned) = match text.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, text),
    };
    let (radix, digits) = if let Some(digits) = unsigned.strip_prefix("0x") {
        (16, digits)
    } else if let Some(digits) = unsigned.strip_prefix("0o") {
        (8, digits)
    } else if let Some(digits) = unsigned.strip_prefix("0b") {
        (2, digits)
    } else {
        (10, unsigned)
    };
    if digits.is_empty() || !digits.chars().all(|digit| digit.is_digit(radix)) {
        return Err(refuse());
    }
    let magnitude = BigInt::parse_bytes(digits.as_bytes(), radix).ok_or_else(refuse)?;
    Ok(if negative { -magnitude } else { magnitude })
}

/// The bytes hex digits spell: an even count, either case, no separators.
pub(crate) fn parse_hex(text: &str) -> Result<Vec<u8>, String> {
    if !text.len().is_multiple_of(2) || !text.chars().all(|digit| digit.is_ascii_hexdigit()) {
        return Err(format!(
            "`{text}` is no hex byte string: write an even count of hex digits, without separators"
        ));
    }
    Ok(text
        .as_bytes()
        .chunks(2)
        .map(|pair| {
            let digits = std::str::from_utf8(pair).expect("hex digits are ASCII");
            u8::from_str_radix(digits, 16).expect("two hex digits are a byte")
        })
        .collect())
}

/// The binary64 `Float` of an integer, when binary64 holds it exactly: when the bits from its
/// highest to its lowest set bit fit binary64's 53-bit significand and its highest bit is below
/// 2^1024.
fn float_of_integer(integer: &BigInt) -> Result<Float, String> {
    let magnitude = integer.magnitude();
    let bits = magnitude.bits();
    let trailing = magnitude.trailing_zeros().unwrap_or(0);
    if bits - trailing > 53 || bits > 1024 {
        return Err(format!(
            "{integer} is no binary64 value exactly; write the Float as a K literal string ({{\"$float\": \"{integer}.0\"}} rounds it)"
        ));
    }
    let significand = (magnitude >> trailing)
        .iter_u64_digits()
        .next()
        .unwrap_or(0);
    let exponent = i32::try_from(trailing).expect("a trailing zero count below 1024");
    #[expect(
        clippy::cast_precision_loss,
        reason = "the significand has at most 53 bits, which binary64 holds exactly"
    )]
    let float = significand as f64 * 2_f64.powi(exponent);
    Ok(Float::from_f64(
        if integer.sign() == num_bigint::Sign::Minus {
            -float
        } else {
            float
        },
    ))
}

/// The `Float` a JSON number denotes at a `Float` position: an integer JSON delivered exactly,
/// when binary64 holds it exactly; any other number its binary64 value, unless it is a float
/// that an integer outside the 64-bit integers rounds to (2^64 or more, -2^63 or less), which is
/// how a JSON reader delivers such an integer.
fn float_of_number(value: &serde_json::Number) -> Result<Float, String> {
    /// 2^64, the least positive integer a JSON reader delivers as a float.
    const ABOVE_U64: f64 = 18_446_744_073_709_551_616.0;
    /// -2^63, the least integer a JSON reader delivers exactly, and the float an integer just
    /// below it rounds to.
    const I64_MIN: f64 = -9_223_372_036_854_775_808.0;
    match number(value) {
        Number::Integer(integer) => float_of_integer(&integer),
        Number::Float(float) if float <= I64_MIN || float >= ABOVE_U64 => Err(format!(
            "{value} is a float that an integer beyond the 64-bit integers rounds to, which is how a JSON reader delivers such an integer; write the Float as a K literal string ({{\"$float\": \"..\"}})"
        )),
        Number::Float(float) => Ok(Float::from_f64(float)),
    }
}

/// One reading a shorthand has at a position.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Reading {
    Int,
    IntText,
    Bool,
    BoolText,
    Float,
    FloatText,
    String,
    Token(SortRef),
    Ctor(Decl),
    List,
    Set,
    Map,
    Bytes,
}

impl Reading {
    /// The tagged or qualified spelling that states this reading, for an ambiguity's message.
    fn spelling(&self) -> String {
        match self {
            Self::Int | Self::IntText => "an `Int` ({\"$int\": ..})".to_owned(),
            Self::Bool | Self::BoolText => "a `Bool` (`true` or `false`)".to_owned(),
            Self::Float | Self::FloatText => "a `Float` ({\"$float\": ..})".to_owned(),
            Self::String => "a `String` ({\"$string\": ..})".to_owned(),
            Self::Token(sort) => {
                let sort = ValueIndex::sort_name(sort);
                format!(
                    "a token of `{sort}` ({{\"$token\": {{\"sort\": \"{sort}\", \"text\": ..}}}})"
                )
            }
            Self::Ctor(decl) => {
                format!("the constructor `{decl}` ({{\"$ctor\": {{\"{decl}\": ..}}}})")
            }
            Self::List => "a `List` ({\"$list\": [..]})".to_owned(),
            Self::Set => "a `Set` ({\"$set\": [..]})".to_owned(),
            Self::Map => "a `Map` ({\"$map\": [[key, value], ..]})".to_owned(),
            Self::Bytes => "a `Bytes` ({\"$hex\": ..})".to_owned(),
        }
    }
}

/// The decoding of one input's document.
struct Decoder<'a> {
    values: &'a ValueIndex,
    files: &'a mut dyn InputFiles,
    /// The resolved names of the data files being decoded, outermost first.
    includes: Vec<String>,
    /// The position inside the document, as segments (`["A"]`, `[3]`, `.Run.steps`).
    path: Vec<String>,
}

impl<'a> Decoder<'a> {
    fn new(values: &'a ValueIndex, files: &'a mut dyn InputFiles) -> Self {
        Self {
            values,
            files,
            includes: Vec::new(),
            path: Vec::new(),
        }
    }

    fn refuse(&self, message: &str) -> Refusal {
        Refusal {
            position: self.path.concat(),
            message: message.to_owned(),
        }
    }

    fn at<T>(
        &mut self,
        segment: String,
        decode: impl FnOnce(&mut Self) -> Result<T, Refusal>,
    ) -> Result<T, Refusal> {
        self.path.push(segment);
        let result = decode(self);
        self.path.pop();
        result
    }

    /// `message`, refused at the position `segment` below the current one.
    fn refuse_at(&self, segment: &str, message: &str) -> Refusal {
        Refusal {
            position: format!("{}{segment}", self.path.concat()),
            message: message.to_owned(),
        }
    }

    /// The resolved name and bytes of the file a `tag` form's `body` names.
    fn read_file(&mut self, tag: &str, body: &Json) -> Result<(String, Vec<u8>), Refusal> {
        let Json::String(path) = body else {
            return Err(self.refuse(&format!("`{tag}` takes a path string")));
        };
        let from = self.includes.last().map(String::as_str);
        self.files
            .read(from, path)
            .map_err(|message| self.refuse(&format!("`{tag}` `{path}`: {message}")))
    }

    fn sort_le(&self, sub: &SortRef, sup: &SortRef) -> bool {
        self.values.is_subsort(sub, sup) == Some(true)
    }

    fn builtin_le(&self, builtin: BuiltinSort, sup: &SortRef) -> bool {
        self.sort_le(&SortRef::Builtin(builtin), sup)
    }

    /// At a position a `Map` fits, how a map whose key starts with `$` is written: an object
    /// with such a key is a tagged form, not the map shorthand.
    fn dollar_key_hint(&self, ty: &InputType) -> &'static str {
        if !ty.is_untyped() && self.builtin_le(BuiltinSort::Map, &ty.sort) {
            "; a map with a key that starts with `$` is written as an array of [key, value] pairs"
        } else {
            ""
        }
    }

    /// Decode `document` at `ty`, below a whole input.
    fn decode(&mut self, document: &Json, ty: &InputType) -> Result<Value, Refusal> {
        let tagged = tagged(document)
            .map_err(|message| self.refuse(&format!("{message}{}", self.dollar_key_hint(ty))))?;
        if let Some((tag, body)) = tagged {
            let value = self.tagged(tag, body, ty)?;
            return self.fitting(value, &format!("`{tag}`"), ty);
        }
        if ty.is_untyped() {
            return self.untyped(document);
        }
        let readings = self.readings(document, ty, false)?;
        self.read_one(document, ty, &readings)
    }

    /// `value`, which `what` gave, when its sort is at most `ty`'s.
    fn fitting(&self, value: Value, what: &str, ty: &InputType) -> Result<Value, Refusal> {
        if !ty.is_untyped()
            && let Some(sort) = self.values.value_sort(&value)
            && self.values.is_subsort(&sort, &ty.sort) == Some(false)
        {
            return Err(self.refuse(&format!(
                "{what} gives a value of sort {}, which is not at most {}",
                ValueIndex::sort_name(&sort),
                ValueIndex::sort_name(&ty.sort)
            )));
        }
        Ok(value)
    }

    fn untyped(&mut self, document: &Json) -> Result<Value, Refusal> {
        const FORMS: &str = "write a constructor form or a tagged form ($string, $int, $token, $float, $list, $set, $seq, $map, $hex, $file, $data-file, $ctor, $call)";
        match document {
            Json::Bool(value) => Ok(Value::Bool(*value)),
            Json::Number(value) => match number(value) {
                Number::Integer(integer) => Ok(Value::Int(integer)),
                Number::Float(float) if float.fract() != 0.0 => Ok(Value::Float(Float::from_f64(float))),
                Number::Float(_) => Err(self.refuse(&format!(
                    "{value} is undetermined at an untyped position: JSON delivers an integer beyond 64 bits as a float, so a float with an integral value reads either way; write a Float as {{\"$float\": {value}}} and an Int as {{\"$int\": \"digits\"}}"
                ))),
            },
            Json::Object(object) if object.len() == 1 => {
                let (name, fields) = object.iter().next().expect("one entry");
                let decl = self.constructor(name, &InputType::untyped())?;
                self.construct(&decl, name, fields, false)
            }
            Json::String(text) => Err(self.refuse(&format!(
                "the string {} is undetermined at an untyped position (a K sort, or the elements of a collection without element types); {FORMS}",
                Json::String(text.clone())
            ))),
            Json::Array(_) => Err(self.refuse(&format!(
                "an array is undetermined at an untyped position; {FORMS}"
            ))),
            Json::Object(_) | Json::Null => Err(self.refuse(&format!(
                "this document is undetermined at an untyped position; {FORMS}"
            ))),
        }
    }

    /// The readings `document`, a shorthand, has at `ty`; `key` reads a map key's string.
    fn readings(
        &self,
        document: &Json,
        ty: &InputType,
        key: bool,
    ) -> Result<Vec<Reading>, Refusal> {
        let sort = &ty.sort;
        let is = |builtin: BuiltinSort| *sort == SortRef::Builtin(builtin);
        let mut readings = Vec::new();
        match document {
            Json::Bool(_) => {
                if self.builtin_le(BuiltinSort::Bool, sort) {
                    readings.push(Reading::Bool);
                }
            }
            Json::Number(value) => {
                // The JSON type decides between the numeric builtins: an integer is an `Int`
                // where `Int` fits, and any number a `Float` where only `Float` does.
                let int = self.builtin_le(BuiltinSort::Int, sort);
                let float = self.builtin_le(BuiltinSort::Float, sort);
                match number(value) {
                    Number::Integer(_) => {
                        if int {
                            readings.push(Reading::Int);
                        } else if float {
                            readings.push(Reading::Float);
                        }
                    }
                    Number::Float(written) => {
                        if float && (!int || written.fract() != 0.0) {
                            readings.push(Reading::Float);
                        } else if is(BuiltinSort::Int) {
                            return Err(self.refuse(&format!(
                                "{value} is no integer that JSON delivers exactly: an Int is written as an integer, and one beyond 64 bits as a string of its digits, so that it is not rounded"
                            )));
                        } else if float {
                            return Err(self.refuse(&format!(
                                "{value} is undetermined at {}: JSON delivers an integer beyond 64 bits as a float, so a float with an integral value reads as an Int or a Float; write a Float as {{\"$float\": {value}}} and an Int as an integer or {{\"$int\": \"digits\"}}",
                                ValueIndex::sort_name(sort)
                            )));
                        } else if int {
                            return Err(self.refuse(&format!(
                                "{value} is no integer that JSON delivers exactly: an Int is written as an integer, and one beyond 64 bits as {{\"$int\": \"digits\"}}, so that it is not rounded"
                            )));
                        }
                    }
                }
            }
            Json::String(text) => {
                if is(BuiltinSort::Int)
                    || (key && self.builtin_le(BuiltinSort::Int, sort) && parse_int(text).is_ok())
                {
                    readings.push(Reading::IntText);
                }
                if is(BuiltinSort::Float) {
                    readings.push(Reading::FloatText);
                }
                if key
                    && self.builtin_le(BuiltinSort::Bool, sort)
                    && matches!(text.as_str(), "true" | "false")
                {
                    readings.push(Reading::BoolText);
                }
                if self.builtin_le(BuiltinSort::String, sort) {
                    readings.push(Reading::String);
                }
                for token in self.values.token_sorts() {
                    if self.sort_le(token, sort) {
                        readings.push(Reading::Token(token.clone()));
                    }
                }
                if let Some(decl) = self.constructor_reading(text, ty)? {
                    readings.push(Reading::Ctor(decl));
                }
            }
            Json::Array(_) => {
                for (builtin, reading) in [
                    (BuiltinSort::List, Reading::List),
                    (BuiltinSort::Set, Reading::Set),
                    (BuiltinSort::Bytes, Reading::Bytes),
                    (BuiltinSort::Map, Reading::Map),
                ] {
                    if self.builtin_le(builtin, sort) {
                        readings.push(reading);
                    }
                }
            }
            Json::Object(object) => {
                if self.builtin_le(BuiltinSort::Map, sort) {
                    readings.push(Reading::Map);
                }
                if object.len() == 1 {
                    let name = object.keys().next().expect("one key");
                    if let Some(decl) = self.constructor_reading(name, ty)? {
                        readings.push(Reading::Ctor(decl));
                    }
                }
            }
            Json::Null => {}
        }
        Ok(readings)
    }

    /// The constructor `name` names at `ty`, if it names one; an ambiguous name is refused.
    fn constructor_reading(&self, name: &str, ty: &InputType) -> Result<Option<Decl>, Refusal> {
        match self.resolve(name, ty, false) {
            Ok(decl) => Ok(Some(decl)),
            Err(ValueError::AmbiguousName { name, candidates }) => Err(self.refuse(&format!(
                "`{name}` names several constructors of {}: {}; write one by a longer path",
                ValueIndex::sort_name(&ty.sort),
                candidates.join(", ")
            ))),
            Err(_) => Ok(None),
        }
    }

    /// Decode `document` by its one reading at `ty`, refusing none and several.
    fn read_one(
        &mut self,
        document: &Json,
        ty: &InputType,
        readings: &[Reading],
    ) -> Result<Value, Refusal> {
        match readings {
            [reading] => self.read(document, ty, reading),
            [] => Err(self.no_reading(document, ty)),
            several => {
                let spellings = several
                    .iter()
                    .map(Reading::spelling)
                    .collect::<Vec<_>>()
                    .join(", or ");
                Err(self.refuse(&format!(
                    "{} reads several ways at {}: as {spellings}; write the form of the one meant",
                    describe(document),
                    ValueIndex::sort_name(&ty.sort)
                )))
            }
        }
    }

    fn no_reading(&self, document: &Json, ty: &InputType) -> Refusal {
        let accepts = match &ty.sort {
            SortRef::Builtin(BuiltinSort::Int) => {
                "an integer, or a string of decimal, 0x, 0o or 0b digits".to_owned()
            }
            SortRef::Builtin(BuiltinSort::Bool) => "`true` or `false`".to_owned(),
            SortRef::Builtin(BuiltinSort::String) => "a string".to_owned(),
            SortRef::Builtin(BuiltinSort::Float) => {
                "a number, or a string that is a K Float literal".to_owned()
            }
            SortRef::Builtin(BuiltinSort::Bytes) => {
                "an array of integers in 0..=255, {\"$hex\": ..} or {\"$file\": ..}; a string has no determined byte encoding".to_owned()
            }
            SortRef::Builtin(BuiltinSort::List | BuiltinSort::Set) => "an array".to_owned(),
            SortRef::Builtin(BuiltinSort::Map) => {
                "an object by key, or an array of [key, value] pairs".to_owned()
            }
            sort if self.values.is_token_sort(sort) => "a string, the token's text".to_owned(),
            sort => {
                let mut names = self
                    .values
                    .productions()
                    .filter(|info| {
                        !info.function
                            && info
                                .result
                                .as_ref()
                                .is_some_and(|result| self.sort_le(&result.sort, sort))
                    })
                    .map(|info| info.decl.path().rsplit("::").next().unwrap_or("").to_owned())
                    .collect::<Vec<_>>();
                names.sort();
                names.dedup();
                let builtins = [
                    BuiltinSort::Int,
                    BuiltinSort::Bool,
                    BuiltinSort::String,
                    BuiltinSort::Float,
                    BuiltinSort::Bytes,
                    BuiltinSort::List,
                    BuiltinSort::Set,
                    BuiltinSort::Map,
                ]
                .into_iter()
                .filter(|builtin| self.builtin_le(*builtin, sort))
                .map(|builtin| ValueIndex::sort_name(&SortRef::Builtin(builtin)))
                .collect::<Vec<_>>();
                let builtins = if builtins.is_empty() {
                    String::new()
                } else {
                    format!(", or a value of its builtin subsorts {}", builtins.join(", "))
                };
                if names.is_empty() {
                    format!(
                        "a tagged form{builtins}; {} has no constructors",
                        ValueIndex::sort_name(sort)
                    )
                } else {
                    format!(
                        "a constructor form{builtins}; its constructors are {}",
                        names.join(", ")
                    )
                }
            }
        };
        let what = match document {
            Json::String(text) => match self.resolve(text, &InputType::untyped(), false) {
                Ok(decl) => format!(
                    "{}, the constructor `{decl}` of another sort,",
                    describe(document)
                ),
                Err(ValueError::WrongKind { decl, .. }) => {
                    return self.refuse(&format!(
                        "`{decl}` is a function; write {{\"$call\": {{\"{text}\": ..}}}} to apply it"
                    ));
                }
                Err(_) => describe(document),
            },
            Json::Object(object) if object.len() == 1 => {
                let name = object.keys().next().expect("one key");
                match self.resolve(name, &InputType::untyped(), false) {
                    Err(ValueError::WrongKind { decl, .. }) => {
                        return self.refuse(&format!(
                            "`{decl}` is a function; write {{\"$call\": {{\"{name}\": ..}}}} to apply it"
                        ));
                    }
                    Ok(decl) => format!("the constructor `{decl}`, of another sort,"),
                    Err(_) => format!("`{name}` names no constructor, and the object"),
                }
            }
            _ => describe(document),
        };
        self.refuse(&format!(
            "{what} is no value of {}; it takes {accepts}",
            ValueIndex::sort_name(&ty.sort)
        ))
    }

    /// Decode `document` by `reading` at `ty`.
    fn read(
        &mut self,
        document: &Json,
        ty: &InputType,
        reading: &Reading,
    ) -> Result<Value, Refusal> {
        let element = |index| {
            if ty.sort
                == SortRef::Builtin(match reading {
                    Reading::Set => BuiltinSort::Set,
                    Reading::Map => BuiltinSort::Map,
                    _ => BuiltinSort::List,
                })
            {
                ty.element(index)
            } else {
                InputType::untyped()
            }
        };
        let text = || match document {
            Json::String(text) => text.clone(),
            _ => String::new(),
        };
        match reading {
            Reading::Bool => Ok(Value::Bool(document.as_bool().unwrap_or_default())),
            Reading::BoolText => Ok(Value::Bool(text() == "true")),
            Reading::Int => match document {
                Json::Number(value) => match number(value) {
                    Number::Integer(integer) => Ok(Value::Int(integer)),
                    Number::Float(_) => Err(self.refuse("no integer")),
                },
                _ => Err(self.refuse("no integer")),
            },
            Reading::IntText => parse_int(&text())
                .map(Value::Int)
                .map_err(|message| self.refuse(&message)),
            Reading::Float => match document {
                Json::Number(value) => float_of_number(value)
                    .map(Value::Float)
                    .map_err(|message| self.refuse(&message)),
                _ => Err(self.refuse("no number")),
            },
            Reading::FloatText => Float::parse(&text())
                .map(Value::Float)
                .map_err(|error| self.refuse(&format!("no K Float literal: {error}"))),
            Reading::String => Ok(Value::String(text())),
            Reading::Token(sort) => Ok(Value::Token {
                sort: sort.clone(),
                text: text(),
            }),
            Reading::Ctor(decl) => match document {
                Json::String(name) => self.construct(decl, name, &Json::Array(Vec::new()), false),
                Json::Object(object) => {
                    let (name, fields) = object.iter().next().expect("one entry");
                    self.construct(decl, name, fields, false)
                }
                _ => Err(self.refuse("no constructor form")),
            },
            Reading::Bytes => self.bytes(document),
            Reading::List | Reading::Set => {
                let Json::Array(items) = document else {
                    return Err(self.refuse("no array"));
                };
                let element = element(0);
                let mut decoded = Vec::with_capacity(items.len());
                for (index, item) in items.iter().enumerate() {
                    decoded.push(self.at(format!("[{index}]"), |decoder| {
                        decoder.decode(item, &element)
                    })?);
                }
                if *reading == Reading::List {
                    Ok(Value::List(decoded))
                } else {
                    self.set(decoded)
                }
            }
            Reading::Map => {
                let (key_type, value_type) = (element(0), element(1));
                match document {
                    Json::Object(object) => {
                        let mut entries = Vec::with_capacity(object.len());
                        for (written, item) in object {
                            let segment = format!("[{}]", Json::String(written.clone()));
                            let decoded_key = self.at(
                                format!("[key {}]", Json::String(written.clone())),
                                |decoder| decoder.map_key(written, &key_type),
                            )?;
                            let decoded_value = self
                                .at(segment.clone(), |decoder| decoder.decode(item, &value_type))?;
                            entries.push((segment, decoded_key, decoded_value));
                        }
                        self.map(entries)
                    }
                    Json::Array(pairs) => self.pairs(pairs, &key_type, &value_type),
                    _ => Err(self.refuse("no object")),
                }
            }
        }
    }

    /// A map key, written as the string `written`, at `ty`.
    fn map_key(&mut self, written: &str, ty: &InputType) -> Result<Value, Refusal> {
        let document = Json::String(written.to_owned());
        if ty.is_untyped() {
            return Err(self.refuse(&format!(
                "the key {document} is undetermined: the map declares no key type; write the map as {{\"$map\": [[key, value], ..]}}"
            )));
        }
        let readings = self.readings(&document, ty, true)?;
        let several = readings.len() > 1;
        self.read_one(&document, ty, &readings).map_err(|mut refusal| {
            if several {
                refusal.message.push_str(
                    "; an object key has no tagged form, so write the map as an array of [key, value] pairs",
                );
            }
            refusal
        })
    }

    fn pairs(
        &mut self,
        pairs: &[Json],
        key_type: &InputType,
        value_type: &InputType,
    ) -> Result<Value, Refusal> {
        let mut entries = Vec::with_capacity(pairs.len());
        for (index, pair) in pairs.iter().enumerate() {
            let Some([key, value]) = pair.as_array().map(Vec::as_slice) else {
                return Err(
                    self.refuse_at(&format!("[{index}]"), "a map entry is a [key, value] pair")
                );
            };
            let decoded_key = self.at(format!("[{index}][0]"), |decoder| {
                decoder.decode(key, key_type)
            })?;
            let decoded_value = self.at(format!("[{index}][1]"), |decoder| {
                decoder.decode(value, value_type)
            })?;
            entries.push((format!("[{index}]"), decoded_key, decoded_value));
        }
        self.map(entries)
    }

    /// The map of `entries`, each with the segment it was written at; equal keys are refused.
    fn map(&self, entries: Vec<(String, Value, Value)>) -> Result<Value, Refusal> {
        let mut map = BTreeMap::new();
        let mut written = BTreeMap::new();
        for (segment, key, value) in entries {
            if let Some(first) = written.get(&key) {
                return Err(self.refuse_at(&segment, &format!(
                    "this key decodes to the same value as the key at `{first}`; K's map of two bindings of one key has no value"
                )));
            }
            written.insert(key.clone(), segment);
            map.insert(key, value);
        }
        Ok(Value::Map(map))
    }

    /// The set of `items`; two equal items are refused.
    fn set(&self, items: Vec<Value>) -> Result<Value, Refusal> {
        let mut set = BTreeSet::new();
        let mut first = BTreeMap::new();
        for (index, item) in items.into_iter().enumerate() {
            if let Some(earlier) = first.get(&item) {
                return Err(self.refuse_at(&format!("[{index}]"), &format!(
                    "this element decodes to the same value as the element at index {earlier}; K's set of two equal elements has no value"
                )));
            }
            first.insert(item.clone(), index);
            set.insert(item);
        }
        Ok(Value::Set(set))
    }

    fn bytes(&self, document: &Json) -> Result<Value, Refusal> {
        let Json::Array(items) = document else {
            return Err(self.refuse("Bytes is an array of integers in 0..=255"));
        };
        let mut bytes = Vec::with_capacity(items.len());
        for (index, item) in items.iter().enumerate() {
            match item.as_u64().and_then(|byte| u8::try_from(byte).ok()) {
                Some(byte) => bytes.push(byte),
                None => {
                    return Err(self.refuse_at(
                        &format!("[{index}]"),
                        &format!("{item} is no byte (an integer in 0..=255)"),
                    ));
                }
            }
        }
        Ok(Value::Bytes(bytes))
    }

    /// The production `name` names at `ty`: among the functions (`function`) or the
    /// constructors whose result sort is at most `ty`'s sort, among all at an untyped position.
    fn resolve(&self, name: &str, ty: &InputType, function: bool) -> Result<Decl, ValueError> {
        let fits = |info: &&crate::values::CtorInfo| {
            ty.is_untyped()
                || info
                    .result
                    .as_ref()
                    .is_some_and(|result| self.sort_le(&result.sort, &ty.sort))
        };
        let of_kind = |wanted: bool| {
            self.values
                .productions()
                .filter(move |info| info.function == wanted)
                .filter(fits)
                .map(|info| &info.decl)
        };
        let kind = if function { "function" } else { "constructor" };
        match self.values.resolve(kind, name, of_kind(function)) {
            Err(ValueError::UnknownName { .. })
                if self.values.resolve(kind, name, of_kind(!function)).is_ok() =>
            {
                Err(ValueError::WrongKind {
                    decl: self
                        .values
                        .resolve(kind, name, of_kind(!function))
                        .map(|decl| decl.to_string())
                        .unwrap_or_default(),
                    function: !function,
                })
            }
            result => result,
        }
    }

    /// The constructor `name` names at `ty`, refusing a function and a name that selects none or
    /// several.
    fn constructor(&self, name: &str, ty: &InputType) -> Result<Decl, Refusal> {
        self.resolve(name, ty, false).map_err(|error| match error {
            ValueError::WrongKind { decl, .. } => self.refuse(&format!(
                "`{decl}` is a function; write {{\"$call\": {{\"{name}\": ..}}}} to apply it"
            )),
            error => self.refuse(&error.to_string()),
        })
    }

    /// The application of `decl`, written `name`, to the fields `body` writes: an object by
    /// field name, or an array in declaration order; `tagged` when a constructor is written
    /// under `$ctor`, which the fields' positions name.
    fn construct(
        &mut self,
        decl: &Decl,
        name: &str,
        body: &Json,
        tagged: bool,
    ) -> Result<Value, Refusal> {
        let values = self.values;
        let info = values
            .info(decl)
            .ok_or_else(|| self.refuse(&format!("no production is declared at `{decl}`")))?;
        let (prefix, verb) = if info.function {
            (format!("$call({name})."), "arguments")
        } else if tagged {
            (format!("$ctor({name})."), "fields")
        } else {
            (format!(".{name}."), "fields")
        };
        let segment = |field: &str| format!("{prefix}{field}");
        let field_type = |index: usize| {
            info.field_types
                .get(index)
                .cloned()
                .flatten()
                .unwrap_or_else(InputType::untyped)
        };
        let expected = || {
            info.fields
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(", ")
        };
        let mut fields: Vec<(Arc<str>, Value)> = Vec::with_capacity(info.fields.len());
        match body {
            Json::Array(items) => {
                if items.len() != info.fields.len() {
                    return Err(self.refuse(&format!(
                        "`{decl}` has {} {verb} ({}), not {}",
                        info.fields.len(),
                        expected(),
                        items.len()
                    )));
                }
                for (index, (field, item)) in info.fields.iter().zip(items).enumerate() {
                    let ty = field_type(index);
                    let value = self.at(segment(field), |decoder| decoder.decode(item, &ty))?;
                    fields.push((field.clone(), value));
                }
            }
            Json::Object(object) => {
                let written = object.keys().cloned().collect::<Vec<_>>();
                let declared = info
                    .fields
                    .iter()
                    .map(ToString::to_string)
                    .collect::<BTreeSet<_>>();
                if written.len() != info.fields.len()
                    || written.iter().any(|field| !declared.contains(field))
                {
                    return Err(self.refuse(&format!(
                        "`{decl}` has the {verb} ({}), not ({})",
                        expected(),
                        written.join(", ")
                    )));
                }
                for (index, field) in info.fields.iter().enumerate() {
                    let ty = field_type(index);
                    let item = &object[field.as_ref()];
                    let value = self.at(segment(field), |decoder| decoder.decode(item, &ty))?;
                    fields.push((field.clone(), value));
                }
            }
            _ => {
                return Err(self.refuse(&format!(
                    "the {verb} of `{decl}` are an object by name or an array in declaration order ([] for none)"
                )));
            }
        }
        let fields = fields
            .iter()
            .map(|(field, value)| (field.as_ref(), value.clone()));
        let built = if info.function {
            values.call(decl.path(), fields)
        } else {
            values.ctor(decl.path(), fields)
        };
        built.map_err(|error| self.refuse(&error.to_string()))
    }

    /// The value of the tagged form `tag` with `body` at `ty`.
    #[expect(
        clippy::too_many_lines,
        reason = "one arm per tag keeps the table of tagged forms in one place"
    )]
    fn tagged(&mut self, tag: &str, body: &Json, ty: &InputType) -> Result<Value, Refusal> {
        let string = |decoder: &Self| match body {
            Json::String(text) => Ok(text.clone()),
            _ => Err(decoder.refuse(&format!("`{tag}` takes a string"))),
        };
        let array = |decoder: &Self| match body {
            Json::Array(items) => Ok(items.clone()),
            _ => Err(decoder.refuse(&format!("`{tag}` takes an array"))),
        };
        match tag {
            "$text" | "$text-file" => Err(self.refuse(&format!(
                "`{tag}` stands for a whole input, which is parsed at the input's sort; inside a value write the value's own form"
            ))),
            "$file" => {
                let (_, bytes) = self.read_file(tag, body)?;
                Ok(Value::Bytes(bytes))
            }
            "$hex" => parse_hex(&string(self)?)
                .map(Value::Bytes)
                .map_err(|message| self.refuse(&message)),
            "$data-file" => {
                let (name, bytes) = self.read_file(tag, body)?;
                if let Some(cycle) = include_cycle(&self.includes, &name) {
                    return Err(self.refuse(&cycle));
                }
                let document = data_document(&name, bytes).map_err(|message| self.refuse(&message))?;
                self.includes.push(name);
                // The position spells the path as the document writes it, as a case list's does.
                let written = body.as_str().unwrap_or_default();
                let decoded = self.at(format!("$data-file({written})"), |decoder| decoder.decode(&document, ty));
                self.includes.pop();
                decoded
            }
            "$string" => Ok(Value::String(string(self)?)),
            "$int" => match body {
                Json::String(text) => parse_int(text)
                    .map(Value::Int)
                    .map_err(|message| self.refuse(&format!("`$int`: {message}"))),
                Json::Number(value) => match number(value) {
                    Number::Integer(integer) => Ok(Value::Int(integer)),
                    Number::Float(_) => Err(self.refuse(&format!(
                        "`$int`: {value} is no integer that JSON delivers exactly; write the Int as a string of its digits"
                    ))),
                },
                _ => Err(self.refuse("`$int` takes a string of digits or an integer")),
            },
            "$float" => match body {
                Json::Number(value) => float_of_number(value)
                    .map(Value::Float)
                    .map_err(|message| self.refuse(&format!("`$float`: {message}"))),
                Json::String(literal) => Float::parse(literal)
                    .map(Value::Float)
                    .map_err(|error| self.refuse(&format!("`$float`: no K Float literal: {error}"))),
                _ => Err(self.refuse("`$float` takes a number or a K Float literal string")),
            },
            "$token" => {
                let (sort, text) = match body {
                    Json::String(text) => {
                        if !self.values.is_token_sort(&ty.sort) {
                            return Err(self.refuse(&format!(
                                "{} is no token sort, so `$token` names its sort: {{\"$token\": {{\"sort\": .., \"text\": ..}}}}",
                                ValueIndex::sort_name(&ty.sort)
                            )));
                        }
                        (ty.sort.clone(), text.clone())
                    }
                    Json::Object(object)
                        if object.len() == 2
                            && object.get("sort").is_some_and(Json::is_string)
                            && object.get("text").is_some_and(Json::is_string) =>
                    {
                        let name = object["sort"].as_str().unwrap_or_default();
                        let sort = self
                            .values
                            .sort(name)
                            .map_err(|error| self.refuse(&format!("`$token`: {error}")))?;
                        if !self.values.is_token_sort(&sort) {
                            return Err(self.refuse(&format!("`$token`: {name} is no token sort")));
                        }
                        (sort, object["text"].as_str().unwrap_or_default().to_owned())
                    }
                    _ => {
                        return Err(self.refuse(
                            "`$token` takes the token's text, or {\"sort\": .., \"text\": ..}",
                        ));
                    }
                };
                Ok(Value::Token { sort, text })
            }
            "$list" | "$set" | "$seq" => {
                let items = array(self)?;
                let mut decoded = Vec::with_capacity(items.len());
                for (index, item) in items.iter().enumerate() {
                    decoded.push(self.at(format!("{tag}[{index}]"), |decoder| {
                        decoder.decode(item, &InputType::untyped())
                    })?);
                }
                match tag {
                    "$list" => Ok(Value::List(decoded)),
                    "$seq" => Ok(Value::Seq(decoded)),
                    _ => self.at(tag.to_owned(), |decoder| decoder.set(decoded)),
                }
            }
            "$map" => {
                let pairs = array(self)?;
                self.at("$map".to_owned(), |decoder| {
                    decoder.pairs(&pairs, &InputType::untyped(), &InputType::untyped())
                })
            }
            "$ctor" => {
                let Json::Object(object) = body else {
                    return Err(self.refuse("`$ctor` takes {\"path::C\": fields}"));
                };
                let mut entries = object.iter();
                let (Some((name, fields)), None) = (entries.next(), entries.next()) else {
                    return Err(self.refuse("`$ctor` takes {\"path::C\": fields}, one constructor"));
                };
                let decl = self.constructor(name, ty)?;
                self.construct(&decl, name, fields, true)
            }
            "$call" => {
                let Json::Object(object) = body else {
                    return Err(self.refuse("`$call` takes {\"path::f\": arguments}"));
                };
                let mut entries = object.iter();
                let (Some((name, arguments)), None) = (entries.next(), entries.next()) else {
                    return Err(self.refuse("`$call` takes {\"path::f\": arguments}, one function"));
                };
                let decl = self.resolve(name, ty, true).map_err(|error| match error {
                    ValueError::WrongKind { decl, .. } => self.refuse(&format!(
                        "`{decl}` is a constructor; write it without $call: {{\"{name}\": ..}}"
                    )),
                    error => self.refuse(&format!("`$call`: {error}")),
                })?;
                if let Some(reason) = self.values.instance_function(&decl, "an input") {
                    return Err(self.refuse(&format!("`$call`: {reason}")));
                }
                self.construct(&decl, name, arguments, false)
            }
            other => Err(self.refuse(&format!(
                "unknown tag `{other}`; the tags are $text, $text-file, $file, $hex, $data-file, $string, $int, $float, $token, $list, $set, $seq, $map, $ctor and $call{}",
                self.dollar_key_hint(ty)
            ))),
        }
    }
}

/// A short description of a document for a message.
fn describe(document: &Json) -> String {
    match document {
        Json::String(text) => format!("the string {}", Json::String(text.clone())),
        Json::Number(value) => format!("the number {value}"),
        Json::Bool(value) => format!("`{value}`"),
        Json::Array(_) => "the array".to_owned(),
        Json::Object(_) => "the object".to_owned(),
        Json::Null => "`null`".to_owned(),
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;
    use std::num::NonZeroU64;

    use super::{
        Case, CaseDocument, CaseRun, InputFiles, Json, json_document, parse_hex, parse_int,
        toml_document,
    };
    use num_bigint::BigInt;

    /// The Definition IR says that a main parameter reads a file's bytes where its sort is the
    /// builtin `Bytes` with no arguments, and that it reads text under any other builtin or
    /// declared sort; under a cell sort or a sort parameter, at any depth, the compiled definition
    /// types the parameter and the IR gives no answer.
    #[test]
    fn the_ir_reads_a_file_as_bytes_only_for_exactly_the_builtin_bytes() {
        use krs_ir::{BuiltinSort, CellSortArgument};
        use krs_ir_levels::{DefinitionSortRef, SortParameterId, SymbolId};

        let symbol = |id: &str| SymbolId::new(id).unwrap();
        let argument = |sort: DefinitionSortRef| CellSortArgument {
            sort,
            arguments: Vec::new(),
        };
        let bytes = DefinitionSortRef::Builtin(BuiltinSort::Bytes);
        let int = DefinitionSortRef::Builtin(BuiltinSort::Int);
        let map = DefinitionSortRef::Builtin(BuiltinSort::Map);
        let declared = DefinitionSortRef::Declared(symbol("sort.op"));
        let cell = DefinitionSortRef::Cell(symbol("cell.rom"));
        let parameter = DefinitionSortRef::Parameter(SortParameterId::new("S"));
        assert_eq!(super::file_reading(&bytes, &[]), Some(true));
        assert_eq!(super::file_reading(&int, &[]), Some(false));
        assert_eq!(super::file_reading(&declared, &[]), Some(false));
        assert_eq!(
            super::file_reading(&map, &[argument(int.clone()), argument(bytes.clone())]),
            Some(false)
        );
        assert_eq!(super::file_reading(&cell, &[]), None);
        assert_eq!(super::file_reading(&parameter, &[]), None);
        assert_eq!(
            super::file_reading(&map, &[argument(int), argument(cell)]),
            None
        );
    }

    #[test]
    fn the_integer_grammar_reads_decimal_and_prefixed_digits_and_nothing_else() {
        for (text, value) in [
            ("0", "0"),
            ("-17", "-17"),
            ("007", "7"),
            ("0x1F", "31"),
            ("0xff", "255"),
            ("-0x10", "-16"),
            ("0o17", "15"),
            ("0b101", "5"),
            ("18446744073709551616", "18446744073709551616"),
            (
                "-340282366920938463463374607431768211456",
                "-340282366920938463463374607431768211456",
            ),
        ] {
            assert_eq!(
                parse_int(text),
                Ok(value.parse::<BigInt>().unwrap()),
                "{text}"
            );
        }
        for text in [
            "", "-", "+1", "1_000", " 1", "1 ", "0x", "0xg", "0b2", "1.0", "1e3", "0X1F", "--1",
        ] {
            assert!(parse_int(text).is_err(), "{text}");
        }
    }

    #[test]
    #[expect(
        clippy::cast_precision_loss,
        reason = "the integers cast are the ones binary64 holds exactly"
    )]
    fn an_integer_is_a_float_only_where_binary64_holds_it_exactly() {
        for exact in [0_i64, -3, 1 << 53, -(1 << 53), 1 << 60, i64::MIN] {
            assert_eq!(
                super::float_of_integer(&exact.into()).unwrap().to_f64(),
                Some(exact as f64),
                "{exact}"
            );
        }
        for inexact in [(1_i64 << 53) + 1, i64::MAX, -(1 << 60) - 1] {
            assert!(
                super::float_of_integer(&inexact.into()).is_err(),
                "{inexact}"
            );
        }
        // Beyond i64 as well: 2^63 and 2^64 are binary64 values, u64::MAX and 2^64 + 1 are not.
        assert_eq!(
            super::float_of_integer(&(1_u64 << 63).into())
                .unwrap()
                .to_f64(),
            Some(9_223_372_036_854_775_808.0)
        );
        assert_eq!(
            super::float_of_integer(&(BigInt::from(1) << 64))
                .unwrap()
                .to_f64(),
            Some(18_446_744_073_709_551_616.0)
        );
        assert!(super::float_of_integer(&u64::MAX.into()).is_err());
        assert!(super::float_of_integer(&((BigInt::from(1) << 64) + 1)).is_err());
        assert!(super::float_of_integer(&(BigInt::from(1) << 1024)).is_err());
    }

    #[test]
    fn a_number_at_float_is_refused_where_a_json_reader_may_have_rounded_it() {
        let float = |text: &str| {
            let Json::Number(number) = super::json_document(text).unwrap() else {
                panic!("{text} is a number");
            };
            super::float_of_number(&number).map(|float| float.to_f64())
        };
        assert_eq!(float("1.5"), Ok(Some(1.5)));
        assert_eq!(
            float("9223372036854775808"),
            Ok(Some(9_223_372_036_854_775_808.0))
        );
        assert_eq!(float("1e19"), Ok(Some(1e19)));
        assert!(float("9007199254740993").is_err());
        // An integer beyond 64 bits arrives rounded, and so does every float of its value.
        assert!(float("18446744073709551617").is_err());
        assert!(float("1.8446744073709552e19").is_err());
        assert!(float("-9223372036854775809").is_err());
        assert_eq!(
            float("-9223372036854775808"),
            Ok(Some(-9_223_372_036_854_775_808.0))
        );
    }

    #[test]
    fn hex_bytes_are_an_even_count_of_digits_of_either_case() {
        assert_eq!(parse_hex("00ff1A"), Ok(vec![0, 0xff, 0x1a]));
        assert_eq!(parse_hex(""), Ok(Vec::new()));
        for text in ["0", "0g", "00 ff", "0x00"] {
            assert!(parse_hex(text).is_err(), "{text}");
        }
    }

    #[test]
    fn toml_converts_to_the_json_data_model_keeping_non_finite_floats_tagged() {
        let table = r#"
            a = 1
            b = 1.5
            c = nan
            d = -inf
            e = "x"
            f = [true, { g = 2 }]
        "#
        .parse::<toml::Table>()
        .unwrap();
        assert_eq!(
            toml_document(&toml::Value::Table(table)).unwrap(),
            serde_json::json!({
                "a": 1, "b": 1.5, "c": {"$float": "NaN"}, "d": {"$float": "-Infinity"},
                "e": "x", "f": [true, {"g": 2}]
            })
        );
    }

    #[test]
    fn a_toml_datetime_is_refused_where_it_stands() {
        let table = "a = [1, 1979-05-27T07:32:00Z]"
            .parse::<toml::Table>()
            .unwrap();
        let error = toml_document(&toml::Value::Table(table)).unwrap_err();
        assert_eq!(error.position, "[\"a\"][1]");
        assert_eq!(
            error.to_string(),
            "at `[\"a\"][1]`: a TOML datetime has no reading as a term"
        );
    }

    #[test]
    fn a_json_object_with_a_repeated_key_is_refused() {
        assert_eq!(
            json_document(r#"{"a": [1, {"b": 2}]}"#).unwrap(),
            serde_json::json!({"a": [1, {"b": 2}]})
        );
        let error = json_document(r#"{"a": {"b": 1, "b": 2}}"#).unwrap_err();
        assert!(
            error
                .message
                .contains("the key `b` is repeated in one object"),
            "{error}"
        );
        assert!(json_document("[1] 2").is_err());
    }

    #[test]
    fn a_case_has_inputs_a_run_and_an_expectation() {
        let case = Case::from_toml(
            "[inputs]\npc = 256\nregs = { A = 1 }\n[run]\ndepth = 3\nstop_after = [\"boundary\"]\nstop_count = 2\n[expect]\nhalt = \"stuck\"\n",
        )
        .unwrap();
        assert_eq!(
            case,
            Case {
                name: None,
                inputs: vec![
                    ("pc".to_owned(), Json::from(256)),
                    ("regs".to_owned(), serde_json::json!({"A": 1}))
                ],
                run: Some(CaseRun {
                    depth: Some(3),
                    stop_before: Vec::new(),
                    stop_after: vec!["boundary".to_owned()],
                    stop_count: NonZeroU64::new(2),
                    stop_when: None,
                }),
                observe: None,
                instances: None,
                expect: Some(serde_json::json!({"halt": "stuck"})),
                file: None,
            }
        );
        assert_eq!(
            Case::from_json(r#"{"inputs": {"pc": 1}}"#)
                .unwrap()
                .inputs
                .len(),
            1
        );
        assert_eq!(Case::from_json("{}").unwrap(), Case::default());
        let refusal = |text: &str| Case::from_toml(text).unwrap_err().to_string();
        assert_eq!(
            refusal("[inputs]\n[other]\n"),
            "unknown key `other` in a case; a case has the keys `inputs`, `run`, `observe`, `instances` and `expect`"
        );
        assert_eq!(
            refusal("name = \"boot\"\n"),
            "a document of one case names none; named cases are listed under `case`"
        );
        assert_eq!(
            refusal("inputs = 1\n"),
            "`inputs` is a table of the case's values by input name"
        );
        assert_eq!(
            refusal("expect = [1]\n"),
            "`expect` is a table of the expected end: `halt`, `rule`, `cells`, `compare`, `views` and `observer`"
        );
        assert_eq!(
            refusal("[run]\ndepth = -1\n"),
            "at `run`: `depth` is a count of rewrite steps, a non-negative integer"
        );
        assert_eq!(
            refusal("[run]\nstop_before = [1]\n"),
            "at `run`: `stop_before` is an array of rule names (a KRS item or a K label), each a string"
        );
        assert_eq!(
            refusal("[run]\nstop_after = [\"tick\"]\nstop_count = 0\n"),
            "at `run`: `stop_count` is the arrival at a stop the run ends at, a positive integer"
        );
        assert_eq!(
            refusal("[run]\nstop_count = 2\n"),
            "at `run`: `stop_count` needs `stop_before` or `stop_after`: it counts arrivals at their rules"
        );
        assert_eq!(
            refusal("[run]\ntrace = true\n"),
            "at `run`: unknown key `trace` in `run`; it has the keys `depth`, `stop_before`, `stop_after`, `stop_count` and `stop_when`"
        );
        assert_eq!(
            refusal("[[case]]\nname = \"a\"\n[[case]]\nname = \"b\"\n"),
            "the document holds named cases, 2 listed, not one case: it is read as a case document of named cases, and a case of it is selected by name (`krs run --case FILE --case-name NAME`)"
        );
        assert!(Case::from_json(r#"{"inputs": [1]}"#).is_err());
        assert!(Case::from_json("[]").is_err());
        assert!(Case::from_json("1").is_err());
    }

    /// The files of a test document: a path is resolved against the directory of the file that
    /// writes it (the top document's is the root), `..` included, so the resolved name identifies
    /// the file.
    struct Files(BTreeMap<&'static str, &'static str>);

    impl InputFiles for Files {
        fn read(&mut self, from: Option<&str>, path: &str) -> Result<(String, Vec<u8>), String> {
            let mut parts = from
                .map(|from| from.split('/').collect::<Vec<_>>())
                .unwrap_or_default();
            parts.pop();
            for part in path.split('/') {
                match part {
                    ".." => {
                        parts.pop();
                    }
                    "." => {}
                    part => parts.push(part),
                }
            }
            let name = parts.join("/");
            self.0
                .get(name.as_str())
                .map(|text| (name.clone(), text.as_bytes().to_vec()))
                .ok_or_else(|| format!("no file `{name}`"))
        }
    }

    fn named(document: &CaseDocument) -> Vec<(&str, Option<&str>, Option<u64>)> {
        let CaseDocument::Named(cases) = document else {
            panic!("a document of one case: {document:?}");
        };
        cases
            .iter()
            .map(|case| {
                (
                    case.name.as_deref().unwrap(),
                    case.file.as_deref(),
                    case.run.as_ref().and_then(|run| run.depth),
                )
            })
            .collect()
    }

    /// A document of named cases lists them inline and through includes, nested, each path
    /// relative to the file that writes it; the document's `run` is every case's that has none,
    /// and a case's file is the one it is written in.
    #[test]
    fn named_cases_are_listed_inline_and_through_includes() {
        let mut files = Files(BTreeMap::from([
            (
                "sst/00.json",
                r#"[{"name": "nop", "inputs": {"pc": 0}}, {"$data-file": "more/01.toml"}]"#,
            ),
            (
                "sst/more/01.toml",
                "[[case]]\nname = \"ld\"\ninputs = { rom = { \"$file\" = \"ld.bin\" } }\n[case.run]\ndepth = 1\n",
            ),
        ]));
        let document = CaseDocument::from_toml(
            "[run]\ndepth = 7\n[[case]]\nname = \"boot\"\n[case.inputs]\npc = 256\n[case.expect]\nhalt = \"stuck\"\n[[case]]\n\"$data-file\" = \"sst/00.json\"\n",
            None,
            &mut files,
        )
        .unwrap();
        assert_eq!(
            named(&document),
            vec![
                ("boot", None, Some(7)),
                ("nop", Some("sst/00.json"), Some(7)),
                ("ld", Some("sst/more/01.toml"), Some(1)),
            ]
        );
        assert_eq!(document.names().collect::<Vec<_>>(), ["boot", "nop", "ld"]);
        let ld = document.named("ld").unwrap();
        assert_eq!(
            ld.inputs,
            vec![("rom".to_owned(), serde_json::json!({"$file": "ld.bin"}))]
        );
        assert!(document.named("absent").is_none());
        assert_eq!(
            document.named("boot").unwrap().expect,
            Some(serde_json::json!({"halt": "stuck"}))
        );

        // A JSON array is a list; `case` may be one include; a document of one case has no names.
        let array = CaseDocument::from_json(r#"[{"name": "a"}]"#, None, &mut files).unwrap();
        assert_eq!(named(&array), vec![("a", None, None)]);
        let included = CaseDocument::from_json(
            r#"{"case": {"$data-file": "sst/00.json"}}"#,
            None,
            &mut files,
        )
        .unwrap();
        assert_eq!(included.names().collect::<Vec<_>>(), ["nop", "ld"]);
        let one = CaseDocument::from_json(r#"{"inputs": {"pc": 1}}"#, None, &mut files).unwrap();
        assert!(matches!(&one, CaseDocument::One(case) if case.inputs.len() == 1));
        assert_eq!(one.names().count(), 0);
        assert!(one.named("pc").is_none());
        let empty = CaseDocument::from_json(r#"{"case": []}"#, None, &mut files).unwrap();
        assert_eq!(empty, CaseDocument::Named(Vec::new()));
    }

    /// Names are present, non-empty and distinct across includes; a document is of one kind; an
    /// include names a file of a list, which does not include itself.
    #[test]
    fn case_documents_refuse_what_is_no_list_of_named_cases() {
        let mut files = Files(BTreeMap::from([
            ("a.json", r#"[{"name": "x"}]"#),
            ("loop.json", r#"[{"$data-file": "sub/back.toml"}]"#),
            (
                "sub/back.toml",
                "[[case]]\n\"$data-file\" = \"../loop.json\"\n",
            ),
            ("table.toml", "[inputs]\npc = 1\n"),
        ]));
        let mut refusal = |text: &str| {
            CaseDocument::from_json(text, None, &mut files)
                .unwrap_err()
                .to_string()
        };
        assert_eq!(
            refusal(r#"{"case": [], "inputs": {}}"#),
            "a document of named cases holds `case`, `run` and `observe` only; one case's `inputs` belongs in its table in `case`"
        );
        assert_eq!(
            refusal(r#"{"case": [{"inputs": {}}]}"#),
            "at `case[0]`: a case in a list of named cases has a `name`"
        );
        assert_eq!(
            refusal(r#"{"case": [{"name": ""}]}"#),
            "at `case[0]`: a case's name is a non-empty string"
        );
        assert_eq!(
            refusal(r#"[{"name": "x", "other": 1}]"#),
            "at `[0]`: unknown key `other` in a case; a named case has the keys `name`, `inputs`, `run`, `observe`, `instances` and `expect`"
        );
        assert_eq!(
            refusal(r#"[{"name": "x"}, {"$data-file": "a.json"}]"#),
            "at `[1]$data-file(a.json)[0]`: the name `x` is also the name of the case at `[0]`; the cases of a document have distinct names"
        );
        assert_eq!(
            refusal(r#"[{"$data-file": "loop.json"}]"#),
            "at `[0]$data-file(loop.json)[0]$data-file(sub/back.toml)[0]`: `$data-file` includes itself: `loop.json` includes `sub/back.toml` includes `loop.json`"
        );
        assert_eq!(
            refusal(r#"{"case": {"$data-file": "table.toml"}}"#),
            "at `case$data-file(table.toml)`: an included file of named cases holds their list: an array, or a table whose one key is `case`"
        );
        assert_eq!(
            refusal(r#"{"case": [{"$data-file": "absent.json"}]}"#),
            "at `case[0]`: `$data-file` `absent.json`: no file `absent.json`"
        );
        assert_eq!(
            refusal(r#"{"case": [{"$hex": "00"}]}"#),
            "at `case[0]`: `$hex` is no case; a list of named cases includes a file with `$data-file`"
        );
        assert_eq!(
            refusal(r#"{"case": 1}"#),
            "at `case`: a list of named cases is an array of cases (TOML's `[[case]]` tables), each with a `name`, and `{\"$data-file\": path}` includes"
        );
        assert_eq!(
            refusal(r"[1]"),
            "at `[0]`: a named case is a table of `name`, `inputs`, `run`, `observe`, `instances` and `expect`"
        );
        assert_eq!(
            refusal("true"),
            "a case document is a table (one case, or named cases under `case`) or an array of named cases"
        );
    }

    /// A file the document includes that includes the document back is a cycle through the
    /// document's own file, refused as one, with the position spelling each path as written.
    #[test]
    fn an_include_of_the_top_document_is_a_cycle() {
        let top = "[[case]]\nname = \"a\"\n[[case]]\n\"$data-file\" = \"cases/sub.json\"\n";
        let mut files = Files(BTreeMap::from([
            ("top.toml", top),
            ("cases/sub.json", r#"[{"$data-file": "../top.toml"}]"#),
        ]));
        assert_eq!(
            CaseDocument::from_toml(top, Some("top.toml"), &mut files)
                .unwrap_err()
                .to_string(),
            "at `case[1]$data-file(cases/sub.json)[0]`: `$data-file` includes itself: `top.toml` includes `cases/sub.json` includes `top.toml`"
        );
    }

    /// A cell of the configuration the `instances` tests read: `field`, its multiplicity and
    /// collection, and its cells (none for a leaf).
    fn cell(
        field: &str,
        multiplicity: Option<krs_ir::CellMultiplicity>,
        collection: Option<krs_ir::CellCollectionType>,
        children: Vec<crate::values::CellNode>,
    ) -> crate::values::CellNode {
        crate::values::CellNode {
            field: field.to_owned(),
            symbol: format!("<{field}>"),
            multiplicity,
            collection,
            unobservable: false,
            children,
            content: None,
        }
    }

    /// `harts { hart*: Map { id, pc, regs { a, b }, reservation?, jobs { job*: Map { jid,
    /// payload } } } }`, `mem`, and `objs*: Set { oid }`.
    fn instance_configuration() -> Vec<crate::values::CellNode> {
        use krs_ir::{CellCollectionType::*, CellMultiplicity::*};
        let leaf = |field: &str| cell(field, None, None, Vec::new());
        vec![
            cell(
                "harts",
                None,
                None,
                vec![cell(
                    "hart",
                    Some(Star),
                    Some(Map),
                    vec![
                        leaf("id"),
                        leaf("pc"),
                        cell("regs", None, None, vec![leaf("a"), leaf("b")]),
                        cell("reservation", Some(Optional), None, Vec::new()),
                        cell(
                            "jobs",
                            None,
                            None,
                            vec![cell(
                                "job",
                                Some(Star),
                                Some(Map),
                                vec![leaf("jid"), leaf("payload")],
                            )],
                        ),
                    ],
                )],
            ),
            leaf("mem"),
            cell("objs", Some(Star), Some(Set), vec![leaf("oid")]),
        ]
    }

    /// An integer leaf as a stated `Int`; `{"$call": ..}` as an application, which is no value;
    /// anything else refused.
    fn int_leaf(
        _: &crate::values::CellNode,
        document: &Json,
        _: &str,
    ) -> Result<super::StatedLeaf, String> {
        let int = |text: String| k_rust::kore::ast::Pattern::DomainValue {
            sort: k_rust::kore::ast::Sort::Application {
                name: "SortInt".to_owned(),
                arguments: Vec::new(),
            },
            value: k_rust::kore::ast::KoreString::from(text.as_str()),
        };
        match document {
            Json::Number(number) => Ok(super::StatedLeaf {
                term: int(number.to_string()),
                value: Some(crate::Value::Int(number.as_i64().unwrap().into())),
                shown: number.to_string(),
            }),
            Json::Object(call) if call.contains_key("$call") => Ok(super::StatedLeaf {
                term: int("call".to_owned()),
                value: None,
                shown: "f(0)".to_owned(),
            }),
            _ => Err("no Int".to_owned()),
        }
    }

    fn instances(document: &Json) -> Result<Vec<(usize, super::StatedCell)>, String> {
        super::read_instances(&instance_configuration(), document, &mut int_leaf)
            .map_err(|error| error.to_string())
    }

    /// A case states the instances of the cells it names, each instance the cells it states:
    /// two harts, the second with a register, an absent and a present reservation, and a job;
    /// what an instance does not state is left out of the statement, so that it keeps the
    /// template's start, which the inputs give every cell.
    #[test]
    fn a_case_states_instances_by_path_each_with_the_cells_it_states() {
        use super::StatedCell::{Group, Leaf, Optional, Repeated};
        let stated = instances(&serde_json::json!({
            "harts": {"hart": [
                {"id": 0, "reservation": []},
                {"pc": 8, "id": 1, "regs": {"b": 2}, "reservation": [3], "jobs": {"job": [{"jid": 4}]}},
            ]},
            "objs": [{"oid": 1}, {"oid": 2}],
        }))
        .unwrap();
        let leaf =
            |value: i64| match int_leaf(&cell("x", None, None, Vec::new()), &value.into(), "") {
                Ok(leaf) => Leaf(leaf),
                Err(error) => panic!("{error}"),
            };
        assert_eq!(
            stated,
            vec![
                (
                    0,
                    Group(vec![(
                        0,
                        Repeated(vec![
                            Group(vec![(0, leaf(0)), (3, Optional(None))]),
                            Group(vec![
                                (0, leaf(1)),
                                (1, leaf(8)),
                                (2, Group(vec![(1, leaf(2))])),
                                (3, Optional(Some(Box::new(leaf(3))))),
                                (
                                    4,
                                    Group(vec![(0, Repeated(vec![Group(vec![(0, leaf(4))])]))])
                                ),
                            ]),
                        ])
                    )])
                ),
                (
                    2,
                    Repeated(vec![Group(vec![(0, leaf(1))]), Group(vec![(0, leaf(2))])])
                ),
            ]
        );
        assert_eq!(instances(&serde_json::json!({})).unwrap(), Vec::new());
        assert_eq!(
            instances(&serde_json::json!({"harts": {"hart": []}})).unwrap(),
            vec![(0, Group(vec![(0, Repeated(Vec::new()))]))]
        );
    }

    /// An optional cell is stated `[]` (absent) or `[content]` (present), as an end document
    /// states it, and nothing else.
    #[test]
    fn an_optional_cell_is_stated_absent_or_present() {
        for reservation in [
            serde_json::json!(3),
            serde_json::json!([1, 2]),
            serde_json::json!({}),
        ] {
            assert_eq!(
                instances(&serde_json::json!({"harts": {"hart": [{"id": 0, "reservation": reservation}]}})),
                Err("at `instances.harts.hart[0].reservation`: the optional cell `reservation` is stated `[]` (absent) or `[content]` (present)".to_owned()),
                "{reservation}"
            );
        }
        assert_eq!(
            instances(&serde_json::json!({"harts": {"hart": {"id": 0}}})),
            Err("at `instances.harts.hart`: the repeated cell `hart` is stated as the array of its instances".to_owned())
        );
    }

    /// A Map collection's instance states its whole key as a value, and no two share one; two
    /// Set instances stated alike are one instance.
    #[test]
    fn instances_that_one_collection_cannot_hold_both_are_refused() {
        for (document, refusal) in [
            (
                serde_json::json!({"harts": {"hart": [{"id": 0}, {"pc": 4}]}}),
                "at `instances.harts.hart[1]`: an instance of the Map collection `hart` states its key, its first cell `id`: the key is the instance's identity",
            ),
            (
                serde_json::json!({"harts": {"hart": [{"id": 0}, {"id": 1}, {"id": 0, "pc": 4}]}}),
                "at `instances.harts.hart[2]`: the instance has the key 0 of the instance at [0]: a Map collection holds one instance per key, its first cell `id`",
            ),
            (
                serde_json::json!({"harts": {"hart": [{"id": 0, "jobs": {"job": [{"jid": 1}, {"jid": 1}]}}]}}),
                "at `instances.harts.hart[0].jobs.job[1]`: the instance has the key 1 of the instance at [0]: a Map collection holds one instance per key, its first cell `jid`",
            ),
            (
                serde_json::json!({"harts": {"hart": [{"id": {"$call": {"f": [0]}}}]}}),
                "at `instances.harts.hart[0].id`: the key f(0) is no value: a Map collection's key is compared with the other instances' keys before the run, so it is stated as a value, with no function application",
            ),
            (
                serde_json::json!({"objs": [{"oid": 1}, {"oid": 2}, {"oid": 1}]}),
                "at `instances.objs[2]`: the instance is stated as the instance at [0] is: a Set collection holds an instance once, and two instances with the same cells are one",
            ),
        ] {
            assert_eq!(instances(&document), Err(refusal.to_owned()), "{document}");
        }
    }

    /// A fixed cell starts as the initializer says, so a path to one is refused, listing the
    /// cells a case may state; a path to no cell is refused, listing the cells there, outside an
    /// instance and inside one; a stated leaf the reader refuses is refused at its position.
    #[test]
    fn a_path_to_a_fixed_cell_or_to_no_cell_is_refused() {
        for (document, refusal) in [
            (
                serde_json::json!({"mem": 1}),
                "at `instances.mem`: `mem` is a fixed cell: the initializer states its start from the inputs, and a case states only the instances of optional and repeated cells (here `harts.hart`, `objs`); bind other inputs to start it otherwise",
            ),
            (
                serde_json::json!({"harts": 1}),
                "at `instances.harts`: `harts` is a fixed group cell, here not a table of its cells: the initializer states its start from the inputs, and a case states only the instances of optional and repeated cells (here `harts.hart`, `objs`); bind other inputs to start it otherwise",
            ),
            (
                serde_json::json!({"cpu": {"pc": 1}}),
                "at `instances.cpu`: no cell has the path `cpu`; the cells are `harts`, `mem`, `objs`",
            ),
            (
                serde_json::json!({"harts": {"core": []}}),
                "at `instances.harts.core`: no cell has the path `harts.core`; the cells are `harts.hart`",
            ),
            (
                serde_json::json!({"harts": {"hart": [{"id": 0, "regs": {"c": 1}}]}}),
                "at `instances.harts.hart[0].regs.c`: no cell has the path `c`; the cells are `a`, `b`",
            ),
            (
                serde_json::json!({"harts": {"hart": [{"id": 0, "regs": 1}]}}),
                "at `instances.harts.hart[0].regs`: the group cell `regs` is a table of its cells by Rust field",
            ),
            (
                serde_json::json!({"harts": {"hart": [{"id": 0, "pc": "x"}]}}),
                "at `instances.harts.hart[0].pc`: no Int",
            ),
            (
                serde_json::json!({"harts": {"hart": [1]}}),
                "at `instances.harts.hart[0]`: an instance of `hart` is a table of its cells by Rust field",
            ),
        ] {
            assert_eq!(instances(&document), Err(refusal.to_owned()), "{document}");
        }
        assert_eq!(
            super::read_instances(&[cell("pc", None, None, Vec::new())], &serde_json::json!({"pc": 1}), &mut int_leaf)
                .map_err(|error| error.to_string()),
            Err("at `instances.pc`: `pc` is a fixed cell: the initializer states its start from the inputs, and a case states only the instances of optional and repeated cells (the configuration has none); bind other inputs to start it otherwise".to_owned())
        );
    }

    /// A case's `instances` is a table, read beside `inputs`, `run` and `expect`.
    #[test]
    fn a_case_holds_its_instances_table() {
        let case = Case::from_toml("[[instances.harts.hart]]\nid = 0\n").unwrap();
        assert_eq!(
            case.instances,
            Some(serde_json::json!({"harts": {"hart": [{"id": 0}]}}))
        );
        assert_eq!(
            Case::from_toml("instances = 1\n").unwrap_err().to_string(),
            "`instances` is a table of the starting instances of optional and repeated cells, by Rust field path"
        );
        assert_eq!(Case::from_toml("[inputs]\n").unwrap().instances, None);
    }
}
