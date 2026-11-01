# Amendments to the upstream texts

k-rust embeds the builtin K files of the pinned K release ([crates/k-rust/builtin/](../crates/k-rust/builtin/), `runtimeverification/k` at `4a46d1231473b599c699160132fd6e76a5c46406`, version `v7.1.337`) and evaluates the `[crypto]` hooks as blockchain-k-plugin's `plugin/krypto.md` at `651a2db5` describes them ([compatibility.md, Cryptographic hooks](compatibility.md#cryptographic-hooks)).
Where k-rust's reading of those texts goes beyond what they say, or where k-rust loads K text that differs from them, the difference is an amendment, stated here and nowhere else.

## The rule

There are two kinds of amendment, kept in two places.

A meaning statement says what an existing hook's value is where the upstream text leaves it open.
It adds no K text: the code that evaluates the hook exists, and the amendment makes its value determined instead of open.
It lives only in this document, never in an upstream file: a sentence inserted into `domains.md` would read as upstream's own to anyone who does not compare the files, and would move every later line that k-rust's citations and tests name.

A meaning statement rests on one of two grounds, which its entry names:

- evident intent: the text fixes the value, and what it leaves out its own model or words supply, an omission of the wording rather than a freedom it grants; no sentence leaves the value to the implementation, as `domains.md` does of `Base2String`'s letter case;
- convention: the text fixes the value up to a spelling or representation convention it does not name, every implementation the entry's evidence covers follows that convention, and the entry states the convention as k-rust's choice, which its upstream proposal would make the text's.

A value neither ground gives stays open ([compatibility.md, Implementation-chosen hook values](compatibility.md#implementation-chosen-hook-values)).

K text that k-rust loads and the upstream file does not hold stays in the embedded file, since K has no way to add a rule to an upstream module from outside it, and rewriting the text at load would make the definition k-rust runs differ from the file it shows.
Each such line ends with the comment `// k-rust: AM-<n>`, naming its entry here, and that entry records the upstream line it replaces, or that it replaces none.
An explanation of such an edit is the entry's; the file holds only the marked code lines.
A K-text entry names a ground too, that of what its lines state. Where the lines make k-rust run something other than what the pinned release runs, the release cannot follow the convention they state: the ground is then a convention of k-rust's own, which the entry says, and compatibility.md states the divergence.

So every file of `crates/k-rust/builtin/` equals the pinned release's file byte for byte once each marked line is undone: removed if its entry says it was added, otherwise replaced by the upstream line its entry records.
A citation `domains.md`:N in compatibility.md names a line of the embedded copy ([compatibility.md](compatibility.md#backend-scope) states the rule); an entry's `Upstream` field names lines of the upstream file itself.

The test [amendments.rs](../crates/k-rust/tests/amendments.rs) enforces the rule.
It holds the SHA-256 digest of each pinned file, so it needs no K installation, and checks that:

- the entries are numbered 1 to N in order, each once, and each has every field below, its `Ground` one of the two grounds;
- undoing the marked lines of each embedded file as its entries say gives the pinned file's digest, every marked line is one its entry lists, and each marked line, its mark removed, is the corresponding `+` line of its entry's upstream proposal;
- every entry's quoted passage occurs verbatim at the location its `Upstream` field cites: in the pinned file of a builtin (the embedded copy with its marks undone), and for `krypto.md` in [kink's reference copy](../kink/crates/kink-native/reference/krypto.md) of the plugin's file at `651a2db5`, whose digest it also checks;
- every `AM-<n>` in `crates/`, `docs/`, `docs-site/`, `krs/` and `kink/` names an entry.

A passage is quoted as a block of the upstream file's lines, either a fenced block or `>` lines. It occurs verbatim at its location when, with every run of whitespace (the line breaks and indentation included) read as one space, its text is a contiguous run of the cited lines' text that starts on the first cited line and ends on the last; it may start or end within a line.

## Entries

Each entry has these fields:

- Upstream: the upstream file, its revision, and the lines the passage is on (several locations are separated by `;`, and each has a passage, in order).
- Passage: the upstream text the amendment rests on, quoted verbatim.
- k-rust reads: the sentence k-rust adds to the text.
- Ground: `evident intent` or `convention`, as the rule above defines them.
- Reason: why the reading rests on that ground, argued from K's data model and the text itself; for a convention, also which implementations follow it.
- Evidence: the tests and the differential or reference gates that check it.
- Upstream proposal: the replacement wording, as a diff of the passage, that would make the amendment unnecessary.
- Status: `local` while the proposal has not been sent upstream; `proposed` once it has; `upstream` once the pinned release holds it, when the entry is removed with the next pin.
- Replaces: what the amendment determines (a class of [implementation-chosen hook values](compatibility.md#implementation-chosen-hook-values) and its construct), or, for K text, `K text` with the marked lines of the embedded file and the upstream lines they replace.

### AM-1: `String2Bytes` and `Bytes2String` write one byte per code point

- Upstream: `domains.md` at K v7.1.337, :1683-1685; `domains.md` at K v7.1.337, :2089-2091; `domains.md` at K v7.1.337, :2094-2096
- Passage:

  > implementation is currently incomplete and does not fully support encodings
  > and code points beyond the initial 256 code points of the Basic Latin and
  > Latin-1 Supplement blocks.

  > You can convert between a `Bytes` and a `String` in O(N) time. The resulting
  > value is a copy of the original and will not be affected by subsequent
  > mutations of the input or output value.

  ```k
    syntax String ::= Bytes2String(Bytes) [function, total, hook(BYTES.bytes2string)]
                    | Bytes2Hex(Bytes)    [function, total, hook(BYTES.bytes2hex)]
    syntax Bytes ::= String2Bytes(String) [function, total, hook(BYTES.string2bytes)]
  ```

- k-rust reads: `Bytes2String(B)` is the string of the same length whose code point at each index is the value of the byte of `B` there, and `String2Bytes(S)`, for a string `S` whose code points are all below 256, is the `Bytes` of the same length whose byte at each index is the code point of `S` there; on those strings the two are inverse.
  Of a string holding a code point above U+00FF the reading says nothing.
- Ground: convention
- Reason: a `Bytes` is a sequence of bytes, the values 0 to 255, and the strings the String domain supports are the sequences of the first 256 code points, the values 0 to 255: the two sorts' supported elements are sequences over alphabets of the same 256 values, and the text calls the operations a conversion between them, of linear cost.
  Both are declared `total`, so `Bytes2String` gives a string for every byte sequence and `String2Bytes` a byte sequence for every supported string.
  So the text fixes a conversion that is total in both directions on the supported strings, each direction the inverse of the other, and linear, between sequences over two alphabets of the same 256 values.
  The encodings K names elsewhere do not meet it: UTF-8, UTF-16 and UTF-32 decode no string from some byte sequences (`b"\xff"`, a sequence of odd length), so a `total` `Bytes2String` read through one of them would need a value the encoding does not give, and their encodings of the code points 128 to 255 are not one byte each.
  What the text does not name is which byte stands for which code point: a conversion that writes each element as one element of another value, the same way everywhere, would meet the same words.
  That correspondence is a representation convention, and the amendment states k-rust's: each element is written as the element of the same value, the byte n as the code point U+00nn, the numbering under which Unicode's Basic Latin and Latin-1 Supplement blocks, the ones the text names, are ISO 8859-1.
  It is the convention of the implementation the evidence covers beside k-rust: the KRS `builtin-domains` gate runs its `strings` cases through k-rust and Java K's LLVM backend, whose results must agree, and they agree that `"\xc1"` converts to one byte and that ASCII text converts there and back unchanged; no differential compares the value of a byte past ASCII.
  Nothing in the text makes the encoding a choice of the implementation, as it does for `Float2String`'s format (:1801-1802) or `Base2String`'s letter case (:1829-1831), but the correspondence is not in the text either, so the ground is convention, not evident intent.
  Beyond U+00FF the text warns that strings are incompletely supported, so the amendment states nothing there, and k-rust leaves `String2Bytes` of such a string unevaluated.
- Evidence: `byte_conversions_are_determined` in [builtin.rs](../crates/k-rust-backend/src/builtin.rs), `a_hook_whose_text_gives_every_argument_a_value_is_defined_on_symbolic_arguments` in the [backend tests](../crates/k-rust-backend/tests/backend/evaluation_mode.rs) (a partial `Bytes2String` of a symbolic `Bytes` defined, since the reading gives it a value on every byte sequence, and a partial `String2Bytes` of a symbolic string undecided, since it says nothing above U+00FF; `kore_simplify_of_a_hex_parse_of_a_partial_bytes_to_string_ends_with_bounded_work` in [cli.rs](../crates/k-rust/tests/cli.rs) keeps KEVM's hex parse of such a `Bytes2String` bounded), `string_to_bytes_above_255_is_unspecified` in [bytes.rs](../crates/k-rust-backend/src/builtin/bytes.rs), `an_amended_value_is_evaluated_outside_an_execution` in the [backend tests](../crates/k-rust-backend/tests/backend/evaluation_mode.rs), and `kprove_proves_no_claim_that_depends_on_an_open_value` (`s2b-latin1`) in [cli.rs](../crates/k-rust/tests/cli.rs).
  The KRS `builtin-domains` gate's `strings` cases `from-string*` and `to-string` run the conversions on Latin-1 text.
- Upstream proposal:

  ```diff
   You can convert between a `Bytes` and a `String` in O(N) time. The resulting
   value is a copy of the original and will not be affected by subsequent
  -mutations of the input or output value. `Bytes2Hex` uses hexadecimal encoding.
  +mutations of the input or output value. `String2Bytes` writes each code point
  +of its string, which must be below 256, as the byte of the same value, and
  +`Bytes2String` reads each byte as the code point of its value.
  +`Bytes2Hex` uses hexadecimal encoding.
  ```

- Status: local
- Replaces: class `byte-encoding` (every `String2Bytes` and `Bytes2String`).

### AM-2: A hex-encoded `String` is lowercase

- Upstream: `krypto.md` at blockchain-k-plugin 651a2db5, :15-16; `krypto.md` at blockchain-k-plugin 651a2db5, :26-30; `krypto.md` at blockchain-k-plugin 651a2db5, :82
- Passage:

  > Throughout,
  > -   `String` values are interpreted as hex-encoded data

  > -   `Keccak256` takes a byte string and returns a 64-character hex-encoded string of the 32-byte keccak256 hash of the input.
  > -   `Sha256` takes a byte string and returns a 64-character hex-encoded string of the 32-byte SHA2-256 hash of the input.
  > -   `Sha512` takes a byte string and returns a 128-character hex-encoded string of the 64-byte SHA2-512 hash of the input.
  > -   `Sha3_256` takes a byte string and returns 64-character hex-encoded string of the 32-byte SHA3-256 hash of the input.
  > -   `RipEmd160` takes a byte string and returns a 40-character hex-encoded string of the 20-byte RIPEMD160 hash of the input.

  > -   `ECDSAPubKey` takes a 32-character byte string of a private key, and returns the 64 byte hex-encoded public key

- k-rust reads: A hex-encoded `String` that a hook returns writes each byte as two hexadecimal digits, the more significant first, in the order of the bytes, and its letter digits are lowercase, `a` to `f`.
- Ground: convention
- Reason: each of these hooks is a `function`, one value per argument, and the text describes the value as the hex encoding of a named digest, or of a public key, of a stated length; two digits per byte, the more significant first, is what the hex encoding of a byte string is ([compatibility.md, Cryptographic hooks](compatibility.md#cryptographic-hooks)).
  The description leaves out only the case of the letter digits, and nothing in the text makes the case a choice of the implementation: where K leaves a letter case to the implementation, it says so, as `domains.md` does of `Base2String` ("Whether the letters returned by `Base2String` are upper or lowercase is determined by the backend, but the backend will consistently choose one or the other", :1829-1831), and `krypto.md` has no such sentence.
  So the text fixes each value up to the spelling of its letter digits, and the hooks have the one value it describes once that spelling is fixed.
  Neither text names a case: no hex literal, no case word, and `Bytes2Hex` only "uses hexadecimal encoding".
  The amendment states lowercase as k-rust's convention, the case in which hexadecimal digests are commonly written as text; the choice between the two cases is k-rust's, not the text's, so the ground is convention, and the upstream proposal would make it the text's.
  The implementation the evidence covers beside k-rust follows it: the execution differential's `crypto` case compares k-rust's `Sha256(b"abc")`, whose digest holds letter digits, with the reference K's output without normalising the case.
  It does not change what a hex `String` argument is read as ("interpreted as hex-encoded data"): no hook k-rust evaluates reads one.
- Evidence: `hex_outputs_are_determined` in [builtin.rs](../crates/k-rust-backend/src/builtin.rs), `hex_digests_are_two_lowercase_hex_digits_per_byte` in [krypto.rs](../crates/k-rust-backend/src/builtin/krypto.rs), `an_amended_value_is_evaluated_outside_an_execution` and `a_hook_whose_text_gives_every_argument_a_value_is_defined_on_symbolic_arguments` (each hex digest, and each raw one, of a symbolic `Bytes` defined at a partial symbol: the text gives every byte string a digest, and this reading its one spelling) in the [backend tests](../crates/k-rust-backend/tests/backend/evaluation_mode.rs), `kore_simplify_of_a_hex_parse_of_an_unread_digest_ends_with_bounded_work` in [cli.rs](../crates/k-rust/tests/cli.rs) (KEVM's hex parse of a symbolic digest ends with bounded work), and `kprove_proves_no_claim_that_depends_on_an_open_value` (`kec-lower`) in [cli.rs](../crates/k-rust/tests/cli.rs).
  The execution differential's `crypto` case ([reference-differential.toml](../scripts/reference-differential.toml)) compares k-rust's `Sha256(b"abc")`, whose digest holds letter digits, with the reference K's output without normalising the case.
- Upstream proposal:

  ```diff
   Throughout,
  --   `String` values are interpreted as hex-encoded data
  +-   `String` values are interpreted as hex-encoded data; a hook that returns one
  +    writes each byte as two hexadecimal digits, the more significant first, with
  +    lowercase letter digits (`a`-`f`)
  ```

- Status: local
- Replaces: class `hex-case` (the hex results of `Keccak256`, `Sha256`, `RipEmd160`, their `HASH` spellings, `KRYPTO.sha3256` and `HASH.sha3_256`, and `ECDSAPubKey`).

### AM-3: The BN128 curve is alt_bn128

- Upstream: `krypto.md` at blockchain-k-plugin 651a2db5, :95; `krypto.md` at blockchain-k-plugin 651a2db5, :97-100
- Passage:

  > The BN128 elliptic curve is defined over 2-dimensional points over the fields of zero- and first-degree polynomials modulo a large prime. (x, y) is a point on G1, whereas (x1 x x2, y1 x y2) is a point on G2, in which x1 and y1 are zero-degree coefficients and x2 and y2 are first-degree coefficients. In each case, (0, 0) is used to represent the point at infinity.

  > -   `BN128Add` adds two points in G1 together,
  > -   `BN128Mul` multiplies a point in G1 by a scalar.
  > -   `BN128AtePairing` accepts a list of points in G1 and a list of points in G2 and returns whether the sum of the product of the discrete logarithm of the G1 points multiplied by the discrete logarithm of the G2 points is equal to zero.
  > -   `isValidPoint` takes a point in either G1 or G2 and validates that it actually falls on the respective elliptic curve.

- k-rust reads: The curve is alt_bn128 of EIP-196 and EIP-197.
  p = 21888242871839275222246405745257275088696311157297823662689037894645226208583 and r = 21888242871839275222246405745257275088548364400416034343698204186575808495617.
  G1 is the group of the points (x, y) with x and y in [0, p) and y² ≡ x³ + 3 (mod p), with (0, 0) denoting the point at infinity; it has order r.
  F_p² is F_p[i]/(i² + 1); the `G2Point` (x1 x x2, y1 x y2) denotes the point (x1 + x2·i, y1 + y2·i) of the twist y² = x³ + 3/(9 + i) over F_p², and (0 x 0, 0 x 0) the point at infinity; G2 is the twist's subgroup of order r.
  `isValidPoint` of a `G1Point` is true exactly when it is a point of G1, and of a `G2Point` exactly when its four coordinates lie in [0, p) and it is a point of G2; it is false for every other point term.
  `BN128Add(P, Q)`, for P and Q in G1, is their sum in G1; `BN128Mul(P, k)`, for P in G1 and every integer k, is k·P (the sum of |k| copies of P, negated when k < 0); `BN128AtePairing(Ps, Qs)`, for two lists of equal length whose items are points of G1 and G2 respectively, is true exactly when Σ aⱼ·bⱼ ≡ 0 (mod r), where Pⱼ = aⱼ·g1 and Qⱼ = bⱼ·g2 for generators g1 of G1 and g2 of G2, and true for two empty lists.
  The reading says nothing of a sum, product or pairing of a term that is no point, or of pairing lists of different lengths.
- Ground: evident intent
- Reason: `krypto.md` is the text of blockchain-k-plugin, whose cryptographic hooks serve KEVM's implementation of Ethereum's precompiles, and its section describes the curve of the two precompiles that EIP-196 and EIP-197 add for pairing-based cryptography: a curve over a prime field whose G2 is over the field of first-degree polynomials, a point of G2 written with its zero-degree coefficients first (:95), and (0, 0) as the point at infinity, which is EIP-196's encoding of it.
  The EIPs call that curve alt_bn128, and Ethereum's clients and libraries call it bn128 or bn256; the name alone fixes no parameters, since BN128 names any Barreto-Naehrig curve of about 128-bit security, so what fixes the curve is the plugin's purpose with the encoding the passage states.
  The text names no parameters because it takes the curve as known from that context, not because it leaves the curve open: each hook is a `function` that adds, multiplies or pairs points of one group G1 or G2 (:97-100), which needs one curve, and no sentence makes the curve the implementation's.
  So the curve is a detail the text takes from its context, and the amendment states it with the parameters EIP-196 and EIP-197 give; the ground is the text's evident intent, not a convention, since the curve is what the text refers to, not a spelling of a value it fixes.
  The `isValidPoint` of a `G2Point` is read as membership of G2, not only of the twist: the text calls a `G2Point` "a point on G2", and the pairing it pairs with G1 is defined through discrete logarithms of G2 points, which exist only in the order-r subgroup.
  A coordinate outside [0, p) is no element of the prime field the points are over, so a pair holding one is no point.
  The text describes the sum, product and pairing of points only, so the amendment fixes their values on points and leaves their outcome elsewhere as the text leaves it.
- Evidence: `validates_concrete_bn128_g1_points`, `validates_concrete_bn128_g2_points_and_subgroup`, `adds_concrete_bn128_g1_points`, `multiplies_concrete_bn128_g1_points_with_reduced_scalars`, `evaluates_concrete_bn128_pairing_products` and `rejects_malformed_concrete_bn128_pairing_arguments` in [krypto.rs](../crates/k-rust-backend/src/builtin/krypto.rs), on points and products of EIP-196 and EIP-197; `bn128_values_are_determined_and_a_non_point_is_outside_domain` in [builtin.rs](../crates/k-rust-backend/src/builtin.rs); `a_hook_whose_text_gives_every_argument_a_value_is_defined_on_symbolic_arguments` in the [backend tests](../crates/k-rust-backend/tests/backend/evaluation_mode.rs) (`isValidPoint` of a symbolic point is defined); `an_amended_value_is_evaluated_outside_an_execution` in the [backend tests](../crates/k-rust-backend/tests/backend/evaluation_mode.rs); and `krun_executes_bn128_fixture_to_pinned_kore_results` and `krun_evaluates_bn128_hooks_on_the_pinned_plugin_point_productions` in [cli.rs](../crates/k-rust/tests/cli.rs).
  No reference gate evaluates the hooks: the pinned Haskell backend implements none of them, so the KRS KEVM gate's Java-reference route skips the BN128 precompile cases (`krs/tests/kevm/verify.py`).
- Upstream proposal:

  ```diff
   The BN128 elliptic curve is defined over 2-dimensional points over the fields of zero- and first-degree polynomials modulo a large prime. (x, y) is a point on G1, whereas (x1 x x2, y1 x y2) is a point on G2, in which x1 and y1 are zero-degree coefficients and x2 and y2 are first-degree coefficients. In each case, (0, 0) is used to represent the point at infinity.
  +The curve is alt_bn128 of EIP-196 and EIP-197: p = 21888242871839275222246405745257275088696311157297823662689037894645226208583, r = 21888242871839275222246405745257275088548364400416034343698204186575808495617.
  +G1 is the group of the points (x, y) with x and y in [0, p) and y² = x³ + 3 (mod p); it has order r.
  +(x1 x x2, y1 x y2) denotes the point (x1 + x2·i, y1 + y2·i) of the twist y² = x³ + 3/(9 + i) over F_p[i]/(i² + 1), and G2 is the twist's subgroup of order r.
  ```

  and, in the `isValidPoint` item, "validates that it actually lies in G1 or G2 respectively, its coordinates in [0, p)".
- Status: local
- Replaces: class `curve` (every outcome of `BN128Add`, `BN128Mul`, `BN128AtePairing` and both `isValidPoint`s); the `\bottom` of a sum, product or pairing outside the points becomes class `outside-domain`.

### AM-4: Float conversions and roots round to nearest, ties to even

- Upstream: `domains.md` at K v7.1.337, :1464-1467, :1653-1654, :1579-1580, :1577
- Passage:

  > Provided here is the syntax of an implementation of arbitrary-precision
  > floating-point arithmetic in K based on a generalization of the IEEE 754
  > standard. This type is hooked to an implementation of floats provided by the
  > backend.

  > You can convert an integer to a floating-point number with the specified
  > precision and exponent range. You can also convert a floating-point number

  > * Round a floating-point number to a specified precision and exponent
  >   range (`roundFloat`). The resulting `Float` will yield the specified values

  > * Compute the Nth integer root `rootFloat` of a float.

- k-rust reads: `Int2Float(I, P, E)` is IEEE 754's conversion of the integer `I` into the format `pPxE`, and `roundFloat(F, P, E)` its conversion of `F` into that format, each under the rounding-direction attribute roundTiesToEven: the value is correctly rounded, a value halfway between two neighbours goes to the one whose significand is even, a magnitude at or beyond `2^emax * (2 - 2^-P)` (half an ulp past the largest finite value) goes to the infinity of its sign, and a nonzero value that rounds to zero to the zero of its sign.
  `rootFloat(F, N)`, for a positive finite `F` and a positive degree `N`, is the positive real `N`th root of `F` correctly rounded to `F`'s format under roundTiesToEven (IEEE 754's `rootn`), and `sqrtFloat` follows by its rule `rootFloat(F, 2)`.
- Ground: evident intent
- Reason: the section gives `Float` as "an implementation of arbitrary-precision floating-point arithmetic in K based on a generalization of the IEEE 754 standard", and its arithmetic hooks name `roundNearestTiesToEven` in their `smt-hook`s.
  IEEE 754 defines a conversion between formats and from integers, and its root `rootn`, as the exact result rounded once according to the applicable rounding-direction attribute, and makes roundTiesToEven the default attribute for binary formats; the text gives these three operations a destination format and no attribute, and its model has no other attribute in force, so each is the IEEE operation under the default one.
  "This type is hooked to an implementation of floats provided by the backend" says where the implementation is, not that its values are the backend's choice, unlike `Base2String`'s case, which the text says the backend determines.
  `Float2Int` "rounds to the nearest integer" and is not amended: IEEE 754 itself defines conversion to an integer with ties to even and with ties away from zero as two operations, and object languages differ there (Wasm's `nearest` rounds ties to even, Rust's `round` away from zero), so its tie stays open.
- Evidence: `the_amended_conversions_roots_and_integral_roundings_are_ieee_754s` (k-rust-backend `builtin/float.rs`: ties to even at 2^24 + 1 and 2^53 + 1, the overflow threshold of binary32 in both signs, `roundFloat` of 0.1, 1.0e300 and -1.0e-50 to binary32, correctly rounded square and cube roots of 2) and `only_a_float2int_tie_is_float_rounding` (`builtin.rs`); [implementation_chosen.rs](../crates/k-rust/tests/implementation_chosen.rs) `only_open_conversion_root_and_crypto_values_are_marked_at_run_time`; [cli.rs](../crates/k-rust/tests/cli.rs) `kprove_proves_no_claim_that_depends_on_an_open_value` (`i2f-inexact`, `rtf-inexact` proven).
  The evaluator computes `Int2Float` with `num-bigint`'s round-to-odd conversion followed by Rust's round-to-nearest-even cast, `roundFloat` with the binary64-to-binary32 cast, and the roots exactly ([k-rust-backend `builtin/float/root.rs`](../crates/k-rust-backend/src/builtin/float/root.rs)).
  The KRS `builtin-domains` gate's `floats` cases `from-int-binary32` (2^24 + 1 to `16777216.0f`) and `round-binary32` (0.1 to `0.1f`) expect these values; no reference differential of k-rust's runs an inexact conversion or root on the Java or Haskell backend.
- Upstream proposal:

  ```diff
   You can convert an integer to a floating-point number with the specified
  -precision and exponent range. You can also convert a floating-point number
  +precision and exponent range, rounded as IEEE 754 rounds to nearest with ties
  +to even (an overflow gives the infinity of the sign). You can also convert a floating-point number
  ```

  and, in "Floating-point mathematics", "Compute the Nth integer root `rootFloat` of a float, correctly rounded to nearest with ties to even" and "Round a floating-point number to a specified precision and exponent range (`roundFloat`), to nearest with ties to even."
- Status: local
- Replaces: class `float-rounding` at `Int2Float` of an integer the format does not hold (an overflow included), `roundFloat` of a value the destination does not hold, and `rootFloat` of a positive finite value in a positive degree whose root no float is; the class keeps `Float2Int` at a tie.

### AM-5: Int2Float of 0 is the positive zero

- Upstream: `domains.md` at K v7.1.337, :1653-1654
- Passage:

  > You can convert an integer to a floating-point number with the specified
  > precision and exponent range. You can also convert a floating-point number

- k-rust reads: `Int2Float(0, P, E)` is the positive zero of the format `pPxE`.
- Ground: evident intent
- Reason: both zeros of a format have the value 0, so "convert an integer to a floating-point number" alone names two elements for the integer 0.
  The conversion is IEEE 754's from an integer ([AM-4](#am-4-float-conversions-and-roots-round-to-nearest-ties-to-even)), whose result takes the sign of its operand, and the integer 0 is not negative: the result is `+0`.
  It is the zero every object language's integer-to-float conversion gives (C's cast, Rust's `as`, Java's widening, Wasm's `f64.convert_i64_s`).
- Evidence: `the_amended_conversions_roots_and_integral_roundings_are_ieee_754s` (`+0` in binary32 and binary64) and `only_a_float2int_tie_is_float_rounding` in k-rust-backend; [cli.rs](../crates/k-rust/tests/cli.rs) `kprove_proves_no_claim_that_depends_on_an_open_value` (`i2f-zero` proven); [choice_sampling.rs](../crates/k-rust/tests/choice_sampling.rs) (`i2f(0)` a control).
  The evaluator's conversion of the integer 0 is `0 * 2^0`, the positive zero.
- Upstream proposal:

  ```diff
   You can convert an integer to a floating-point number with the specified
  -precision and exponent range. You can also convert a floating-point number
  +precision and exponent range (0 converts to positive zero). You can also convert a floating-point number
  ```

- Status: local
- Replaces: class `float-rounding` at `Int2Float(0, P, E)`.

### AM-6: floorFloat, ceilFloat and truncFloat are IEEE 754's roundToIntegral

- Upstream: `domains.md` at K v7.1.337, :1583-1588
- Passage:

  > * Round a float to the next lowest floating-point value which is an integer
  >   (`floorFloat`).
  > * Round a float to the next highest floating-point value which is an integer
  >   (`ceilFloat`).
  > * Round a float to the next closest floating-point value which is an integer, in
  >   the direction of zero (`truncFloat`).

- k-rust reads: `floorFloat`, `ceilFloat` and `truncFloat` are IEEE 754's roundToIntegralTowardNegative, roundToIntegralTowardPositive and roundToIntegralTowardZero: a NaN gives the format's NaN, an infinity gives itself, and a zero result has the argument's sign (`floorFloat(0.5)` is `0.0`, `ceilFloat(-0.5)` and `truncFloat(-0.5)` are `-0.0`).
- Ground: evident intent
- Reason: each sentence describes, for a finite argument, the IEEE 754 operation that rounds to an integral value in one direction, and the three directions are the passage's own (lowest, highest, toward zero).
  The hooks are declared `total`, so a NaN and the infinities have values, which "the next lowest floating-point value which is an integer" does not name: no float is next to a NaN, and taken literally `ceilFloat` of the positive infinity would have none.
  IEEE 754's operations give them: a NaN operand gives a NaN, an infinity is its own integral value, and the result's sign is the operand's, which also picks between the two zeros a non-integer rounding to 0 is equally near.
  The format's one NaN is determined ([compatibility.md, Backend scope](compatibility.md#backend-scope)).
- Evidence: `the_amended_conversions_roots_and_integral_roundings_are_ieee_754s` (NaN, both infinities and `-0.0` for each hook; `floorFloat(0.5)`, `ceilFloat(-0.5)`, `truncFloat(-0.7)` and `truncFloat(0.7f)`) and `values_outside_a_described_domain_are_outside_domain` in k-rust-backend; [cli.rs](../crates/k-rust/tests/cli.rs) `kprove_proves_no_claim_that_depends_on_an_open_value` (`fl-half` proven); [kompile_passes.rs](../crates/k-rust/tests/kompile_passes.rs) `leaves_conversions_roots_and_encodings_the_definition_leaves_open_unfolded` (the three fold).
  The evaluator applies Rust's `floor`, `ceil` and `trunc`, which are these operations.
- Upstream proposal:

  ```diff
   * Round a float to the next lowest floating-point value which is an integer
  -  (`floorFloat`).
  +  (`floorFloat`). This and the next two operations are IEEE 754's roundToIntegral
  +  in their directions: a NaN gives NaN, an infinity itself, and a zero result has
  +  the sign of the argument.
  ```

- Status: local
- Replaces: class `outside-domain` at `floorFloat`, `ceilFloat` and `truncFloat` of a NaN, an infinity, or a non-integer whose rounding is a zero.

### AM-7: `replaceAtBytes` is defined up to the end of its `Bytes`

- Upstream: `domains.md` at K v7.1.337, :2103-2105; `domains.md` at K v7.1.337, :2143-2147
- Passage:

  > The result is `#False` if `value` is
  > not in the range [0..255] or if `index` is not a valid index (ie, less than
  > zero or greater than or equal to the length of the `Bytes` term).

  > You can modify a `Bytes` to return a `Bytes` which is equal to `dest` except the
  > `N` elements starting at `index` are replaced with the contents of `src` in O(N)
  > time. If `--llvm-mutable-bytes` is active, this will not create a new `Bytes`
  > object and will instead modify the original on concrete backends. The result is
  > `#False` if `index` + `N` is not a valid index.

- k-rust reads: In `replaceAtBytes(dest, index, src)`, with `N` the length of `src`, "`index` + `N` is not a valid index" holds exactly when `index + N` is less than 0 or greater than the length of `dest`; so `replaceAtBytes` from a nonnegative `index` with `index + N` equal to the length of `dest` is `dest` with its last `N` bytes replaced by `src`.
  Of a negative `index` whose `index + N` is between 0 and the length of `dest` the reading says nothing.
- Ground: evident intent
- Reason: "valid index" is defined for the index of one byte (`B[I <- V]`), as a position `0 <= i < length`, and the sentence applies it to `index + N`, which is no byte's position but the end of the replaced range, one past its last byte.
  Read as a position, the condition would make every replacement that ends at the end of `dest` `#False`, the replacement of a single last byte and of the whole `dest` included, while the value clause names those `N` bytes of `dest` and their replacement.
  The bound that says the `N` elements starting at `index` lie inside `dest` is `index + N <= length`, the bound of a range's end, as `substrBytes` states it for its `endIndex` ("`lengthBytes(B) <Int endIndex`" is `#Bottom`, :2136-2139).
  So the condition is an end bound, written with the phrase defined for positions; nothing in the text makes the tail case the implementation's.
  A negative `index` with `index + N` in range is outside what the value clause names (no element of `dest` starts there), and the amendment leaves it as the text does.
- Evidence: `replace_at_past_the_end_is_bottom` in [bytes.rs](../crates/k-rust-backend/src/builtin/bytes.rs), `an_undescribed_bottom_is_outside_domain_and_a_stated_one_is_no_class` in [builtin.rs](../crates/k-rust-backend/src/builtin.rs), `an_amended_value_is_evaluated_outside_an_execution` and `a_bottom_outside_a_described_domain_is_of_unknown_definedness_outside_an_execution` in the [backend tests](../crates/k-rust-backend/tests/backend/evaluation_mode.rs), and `kprove_proves_nothing_from_a_hook_outside_its_described_domain` (`rpl-tail-yes`, `rpl-tail-no`, `vac-rpl-tail`) in [cli.rs](../crates/k-rust/tests/cli.rs).
- Upstream proposal:

  ```diff
   object and will instead modify the original on concrete backends. The result is
  -`#False` if `index` + `N` is not a valid index. This function accepts both
  +`#False` if `index` + `N` is less than zero or greater than the length of
  +`dest`. This function accepts both
  ```

- Status: local
- Replaces: class `outside-domain` of `replaceAtBytes` from a nonnegative index up to the end of its `Bytes`; the negative start stays `outside-domain`.

### AM-8: A Float literal is its rational correctly rounded

- Upstream: `domains.md` at K v7.1.337, :1478-1483; `domains.md` at K v7.1.337, :1496
- Passage:

  > The value of a floating-point literal is computed as follows: First the
  > mantissa is read as a rational number. Then it is multiplied by 10 to the
  > power of the exponent, which is interpreted as an integer, and defaults to
  > zero if it is not present. Finally, it is rounded to the nearest possible
  > value in a floating-point type represented like an IEEE754 floating-point type,
  > with the number of bits of precision and exponent specified by the suffix.

  ```k
    syntax Float ::= r"[\\+\\-]?Infinity([fFdD]|([pP][0-9]+[xX][0-9]+))?" [token, prec(3)]
  ```

- k-rust reads: the rounding is IEEE 754's correctly rounded conversion from decimal under roundTiesToEven: a rational halfway between two values of the format goes to the one whose significand is even, a magnitude at or beyond `2^emax * (2 - 2^-N)` (half an ulp past the largest finite value) to the infinity of the literal's sign, and a nonzero rational that rounds to zero to the zero of its sign; and an `Infinity` lexeme, with its sign and suffix, is the infinity of that sign in that format.
- Ground: evident intent
- Reason: "rounded to the nearest possible value in a floating-point type represented like an IEEE754 floating-point type" is IEEE 754's round to nearest, roundTiesToEven, the default attribute for binary formats and the one the section's arithmetic hooks name, under which a conversion from a decimal character sequence is correctly rounded.
  That attribute's definition decides each case "nearest" alone leaves: a tie goes to the even significand, and an exact value of magnitude at least `b^emax * (b - 1/2 * b^(1-p))` rounds to the infinity of its sign, so the reading that takes the largest finite value as the nearest at a finite distance is not IEEE's nearest; a rounded zero has the sign of the exact value.
  A type represented like an IEEE 754 format has one infinity of each sign, and the token syntax admits `Infinity` with a sign and the format suffix, which can name no other value of the format.
  No sentence says that the backend chooses any of these elements.
- Evidence: the canonicalizer `k_rust_domain::float::canonical` (exact rounding in every format, with its tests and the `mpfr-oracle` comparison), `a_request_holding_an_open_literal_is_refused_outside_an_execution` and `the_load_records_the_open_literals_of_each_sentence_as_written` (k-rust-backend `literal.rs`: every Float literal admitted and unrecorded); [cli.rs](../crates/k-rust/tests/cli.rs) `kprove_proves_claims_through_every_float_literal_on_its_one_element`; [implementation_chosen.rs](../crates/k-rust/tests/implementation_chosen.rs) `every_attempt_of_a_sentence_holding_an_open_literal_is_marked` (the Float literals unmarked); [kompile_passes.rs](../crates/k-rust/tests/kompile_passes.rs) `the_fold_reads_no_open_literal_and_folds_every_float_literal`.
  The KRS `builtin-domains` gate's `floats` cases `infinite`, `match-infinity` and `negate-infinity` read the `Infinity` lexeme as the infinity, which their re-record with this change checks.
- Upstream proposal:

  ```diff
   zero if it is not present. Finally, it is rounded to the nearest possible
   value in a floating-point type represented like an IEEE754 floating-point type,
  -with the number of bits of precision and exponent specified by the suffix.
  +with the number of bits of precision and exponent specified by the suffix, as
  +IEEE 754's roundTiesToEven rounds it: ties to the even value, a value past the
  +largest finite one by half an ulp or more to the infinity of its sign, and a
  +nonzero value rounding to zero to the zero of its sign. `Infinity` and
  +`-Infinity`, with an optional suffix, are the infinities of that format.
  ```

- Status: local
- Replaces: class `literal` at `Float` literals (a tie, a magnitude at or beyond the overflow threshold, a nonzero value rounding to a zero, an `Infinity` lexeme), and with it the refusal, on every route but an execution, of a request or a claim holding one; the class keeps the machine-integer literals a width cannot hold.

### AM-9: The default layout ends a line comment at every line end

- Upstream: `kast.md` at K v7.1.337, :512-513
- Passage:

  ```k
                       | r"(\\/\\/[^\\n\\r]*)"                         // C-style single-line comments
                       | r"([\\ \\n\\r\\t])"                           // Whitespace
  ```

- k-rust reads: A line end is any of the line terminators a source location counts: `\n` through `\r` (line feed, vertical tab, form feed and carriage return), U+0085, U+2028 and U+2029, the last three written in the regexes as `\u` escapes.
  A single-line comment ends at a line end, and every line end is whitespace.
- Ground: convention
- Reason: module `DEFAULT-LAYOUT` is the layout of the rule and configuration grammars and of every program of a definition that declares no `#Layout` production, and its two regexes say what a line end is to the scanner: a `//` comment runs to the end of its line, and the end of a line separates tokens.
  The upstream classes name `\n` and `\r` alone, and the pinned K's scanner follows them; the amendment is not a reading of that text but k-rust's own convention for where a line ends, the one its source locations count.
  A location counts a line at every line terminator ([compatibility.md, Token regex line anchors](compatibility.md#token-regex-line-anchors)), so with the upstream classes a comment before U+2028 would run on into the text the location places on the next line, and a vertical tab, form feed, U+0085, U+2028 or U+2029 outside a comment would be no token at all.
  The classes are widened to the line terminators the locations count, so that the scanner and the locations agree on where a line ends; no implementation but k-rust follows this convention, which is a divergence from the pinned release ([compatibility.md, Default layout line ends](compatibility.md#default-layout-line-ends)).
  The characters are written as `\u` escapes because a terminator written verbatim in a string ends a line of the file ([compatibility.md, Definition text layout](compatibility.md#definition-text-layout)), and the module's lines are then its lines as written.
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
- Ground: evident intent
- Reason: a ceil equation is an equality of the definition, so it holds only if it states the application's actual domain.
  `divInt` is Euclidean division, which gives one integer for every nonzero divisor, and division by zero is `#False`: the application is defined exactly where its operands are and its divisor is not zero.
  `bitRangeInt` is defined by its equation in module `INT` as `(I >>Int IDX) modInt (1 <<Int LEN)`: `I >>Int IDX` is defined exactly where `IDX` is not negative, `1 <<Int LEN` exactly where `LEN` is not negative, and it is then at least 1, so the remainder's divisor is never zero; the application is defined exactly where its operands are and `IDX` and `LEN` are not negative.
  The module states the domains of `/Int`, `%Int`, `modInt`, `>>Int` and `<<Int` (upstream :1392-1396) and not those of `divInt` and `bitRangeInt`, so a claim whose right-hand side holds `V divInt 32` cannot show that it is defined, though the text says it is.
  Other partial operations of `INT`, `^Int` and `^%Int` at a negative exponent, `^%Int` with a zero modulus and `log2Int` of a number that is not positive, have no ceil equation in the module either; AM-12 states theirs.
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

### AM-11: The edges of rootFloat in a positive degree are IEEE 754's rootn

- Upstream: `domains.md` at K v7.1.337, :1464-1467, :1577, :1600, :1607, :1671
- Passage:

  > Provided here is the syntax of an implementation of arbitrary-precision
  > floating-point arithmetic in K based on a generalization of the IEEE 754
  > standard. This type is hooked to an implementation of floats provided by the
  > backend.

  > * Compute the Nth integer root `rootFloat` of a float.

  > * Compute the square root `sqrtFloat` of a float.

  ```k
    syntax Float ::= rootFloat(Float, Int)        [function, hook(FLOAT.root)]
  ```

  ```k
    rule sqrtFloat(F:Float) => rootFloat(F, 2)
  ```

- k-rust reads: in a positive degree `N`, `rootFloat(F, N)` is IEEE 754's `rootn(F, N)` in `F`'s format at every `F` that is not negative and at every `F` when `N` is odd, `-0.0` in an even degree excepted: the root of a NaN is the format's NaN; of `+0.0` is `+0.0`, and of `-0.0` in an odd degree `-0.0`; of `+Infinity` is `+Infinity`, and of `-Infinity` in an odd degree `-Infinity`; and of a negative finite `F` in an odd degree it is the negation of the root of `-F`, correctly rounded as [AM-4](#am-4-float-conversions-and-roots-round-to-nearest-ties-to-even) reads that root.
- Ground: evident intent
- Reason: the section's model is IEEE 754, and "the Nth integer root" is its operation with an integer degree, `rootn(x, n)`, the real `x^(1/n)` correctly rounded (IEEE 754-2019 §9.2); AM-4 reads it so at a positive finite `F`, and the text gives the operation the same words at every float.
  For an odd `N` every real `x` has exactly one real `y` with `y^N = x`, the negation of the root of `|x|`: it is the only real a `Float` result can be, and it is `rootn`'s value.
  The root of 0 is 0: `+0.0` gives `+0.0`, and for an odd `N`, where the root is an odd function whose values left of 0 are negative, `-0.0` gives `-0.0`, as `rootn` gives.
  IEEE 754 construes an infinite operand as the limit of real operands of growing magnitude (§6.1): the root of a positive value grows without bound with it, and for an odd `N` the root of a negative one falls without bound, so `+Infinity` gives `+Infinity` and `-Infinity` in an odd degree `-Infinity`.
  An operation of IEEE 754 with a quiet NaN operand and a floating-point result delivers a quiet NaN (§6.2), and a format has one NaN ([compatibility.md, Backend scope](compatibility.md#backend-scope)).
  Three edges stay open. The hook is not declared `total`, and in its block every function of one `Float` whose real counterpart is defined on all reals is (`absFloat`, `floorFloat`, `ceilFloat`, `truncFloat`, `expFloat`, `sinFloat`, `cosFloat`, `atanFloat`) while those undefined on some reals are not (`logFloat`, `tanFloat`, `asinFloat`, `acosFloat`, `sqrtFloat`), :1607-1626: where no real root exists the text admits `\bottom` beside IEEE 754's NaN. That is an even root of a negative value, `-Infinity` included, and a degree of 0 or below, whose Nth root real mathematics does not define (`x^(1/0)` has no value; IEEE 754's `x^(1/n)` for a negative `n` extends the word). And an even root of `-0.0`: `rootn` gives `+0.0` (§9.2.1) and IEEE 754's squareRoot `-0.0` (§5.4.1), while the text calls `sqrtFloat` the square root and defines it as `rootFloat(F, 2)`, so the two IEEE operations it names give one application two values, and no sign rule for an even root of `-0.0` is evident.
- Evidence: `values_outside_a_described_domain_are_outside_domain` (k-rust-backend `builtin.rs`: the determined roots and the open ones) and `float_root_is_the_ieee_rootn_of_every_degree` (the evaluator's values), with `a_seed_takes_the_other_tie_integer_and_another_root_outside_the_domain` (`builtin/float.rs`, `choice-sampling`); [implementation_chosen.rs](../crates/k-rust/tests/implementation_chosen.rs) `only_open_conversion_root_and_crypto_values_are_marked_at_run_time` (`rt(-8.0, 3)`, `rt(0.0, 2)`, `rt(NaN, 2)`, `rt(-Infinity, 3)` unmarked; `rt(-0.0, 2)`, `rt(4.0, 0)` marked); [cli.rs](../crates/k-rust/tests/cli.rs) `kprove_proves_no_claim_that_depends_on_an_open_value` (`rtf-odd-negative`, `rtf-odd-zero`, `rtf-nan` proven; `rtf-even-zero`, `rtf-degree-zero` undecided); [kompile_passes.rs](../crates/k-rust/tests/kompile_passes.rs) `leaves_conversions_roots_and_encodings_the_definition_leaves_open_unfolded`; [choice_sampling.rs](../crates/k-rust/tests/choice_sampling.rs) (the three determined roots are controls).
  The evaluator computes `rootn`'s special values in [k-rust-backend `builtin/float/root.rs`](../crates/k-rust-backend/src/builtin/float/root.rs) (`special_root`) and the odd root of a negative value as the negated root of its magnitude; no reference differential of k-rust's runs these roots on the Java or Haskell backend.
- Upstream proposal:

  ```diff
  -* Compute the Nth integer root `rootFloat` of a float.
  +* Compute the Nth integer root `rootFloat` of a float. In a positive degree it is
  +  IEEE 754's `rootn`: NaN for a NaN, `+0.0` and `+Infinity` for themselves, and in
  +  an odd degree the real root of a negative value, `-0.0` for `-0.0` and
  +  `-Infinity` for `-Infinity`.
  ```

- Status: local
- Replaces: class `outside-domain` at `rootFloat(F, N)` with `N` positive and `F` a NaN, `+0.0` or `+Infinity`, or, with `N` odd, `-0.0`, `-Infinity` or a negative finite value; the class keeps a degree of 0 or below, and an even degree of a negative value or of `-0.0`.

### AM-12: The definedness of `^Int`, `^%Int` and `log2Int` as ceil equations

- Upstream: `domains.md` at K v7.1.337, :1228-1231, :1233-1234, :1250-1251, :1300-1301
- Passage:

  > * Compute the exponentiation `^Int` of two integers.
  > * Compute the exponentiation of two integers modulo another integer (`^%Int`).
  >   `A ^%Int B C` is equal in value to `(A ^Int B) %Int C`, but has a better
  >   asymptotic complexity.

  > * Compute the quotient `/Int` or modulus `%Int` of two integers using
  >   t-division, which rounds towards zero. Division by zero is `#False`.

  ```k
                   Int "^Int" Int                 [function, symbol(_^Int_), left, smt-hook(^), hook(INT.pow)]
                 | Int "^%Int" Int Int            [function, symbol(_^%Int__), left, smt-hook((mod (^ #1 #2) #3)), hook(INT.powmod)]
  ```

  > Log base 2 of zero or a negative number
  > is `#False`.

- k-rust reads: Module `INT-SYMBOLIC-KORE` states the definedness of `^Int`, `^%Int` and `log2Int` as it states that of `/Int`, `%Int`, `modInt`, `>>Int` and `<<Int`: `#Ceil(@I1 ^Int @I2)` is `@I2 >=Int 0 orBool @I1 ==Int 1 orBool @I1 ==Int -1` with the ceils of both operands, `#Ceil(@I1 ^%Int @I2 @I3)` is `@I3 =/=Int 0` and that condition with the ceils of the three operands, and `#Ceil(log2Int(@I))` is `@I >Int 0` with the ceil of its operand.
- Ground: evident intent
- Reason: a ceil equation is an equality of the definition, so it holds only if it states the application's actual domain.
  `^Int` is the exponentiation of two integers, of sort `Int`, and is not declared `total`: its value is the power `A^B`, which is an integer for every nonnegative `B` (`A ^Int 0` is the empty product 1, `0 ^Int 0` included); for a negative `B = -n` the power is `1 / A^n`, an integer exactly when `|A| = 1` (1 for the base 1, and 1 or -1 by the parity of `n` for the base -1), and no number at all for the base 0, so no element of `Int` is the power there and the application is undefined.
  The application is defined exactly where its operands are and `B` is not negative or `A` is 1 or -1.
  `^%Int` is "equal in value to `(A ^Int B) %Int C`": it is defined exactly where that remainder is, where `A ^Int B` is defined and the divisor `C` is not zero ("Division by zero is `#False`"); read as the Euclidean remainder (AM-13), whose division by zero is `#False` as well, the domain is the same.
  `log2Int` of zero or a negative number is `#False`, and of a positive integer is the index of its highest set bit, an integer: the application is defined exactly where its operand is and is positive.
  A power the backend does not compute for its size (a result above its bound, [compatibility.md, Resource bounds](compatibility.md#resource-bounds)) is defined: the bound is the evaluator's, and the equation, like the text, gives every such application a value.
  The module states the domains of `/Int`, `%Int`, `modInt`, `>>Int` and `<<Int` (upstream :1392-1396) and, with AM-10, of `divInt` and `bitRangeInt`, and not these, so a claim whose right-hand side holds `V ^Int 3` cannot show that it is defined, and one holding `V ^Int -1` with `V` above 1 that it is not, though the text says both.
  The domains are stated as equations rather than derived from the hooks' text in the backend for the reason AM-10 gives: the ceil theory is the one source of an application's definedness.
- Evidence: `power_modular_power_and_log2_domains_compose_in_claims` in [proof_semantics.rs](../crates/k-rust/tests/proof_semantics.rs): on symbolic operands `safe-pow`, `safe-symbolic-pow`, `safe-one-pow`, `safe-minus-one-pow`, `safe-unit-pow`, `safe-powmod`, `safe-symbolic-powmod`, `safe-unit-powmod` and `safe-log2` are proven, and `undefined-pow`, `undefined-zero-pow`, `undefined-modulus-powmod`, `undefined-exponent-powmod` and `undefined-log2` disproved with a certified leaf; the claims on literal operands, which the evaluators decide, are the controls and agree.
  The ground evaluators apply the same domain case by case (`int_pow_within`, `int_powmod` and `int_log2` in `k-rust-backend`'s `builtin.rs`): the bases 1 and -1 have a power at every exponent, any other base at a negative exponent is `\bottom`; a zero modulus is `\bottom`, and otherwise `^%Int` at a negative exponent is as `^Int`; and an argument of `log2Int` that is not positive is `\bottom` (`undefined_integer_operations_are_bottom` and `powmod_is_the_euclidean_remainder_of_the_power` there).
- Upstream proposal:

  ```diff
     rule #Ceil(@I1:Int <<Int  @I2:Int) => {(@I2 >=Int 0)  #Equals true} #And #Ceil(@I1) #And #Ceil(@I2) [simplification]
  +  rule #Ceil(@I1:Int ^Int @I2:Int) => {(@I2 >=Int 0 orBool @I1 ==Int 1 orBool @I1 ==Int -1) #Equals true} #And #Ceil(@I1) #And #Ceil(@I2) [simplification]
  +  rule #Ceil(@I1:Int ^%Int @I2:Int @I3:Int) => {(@I3 =/=Int 0 andBool (@I2 >=Int 0 orBool @I1 ==Int 1 orBool @I1 ==Int -1)) #Equals true} #And #Ceil(@I1) #And #Ceil(@I2) #And #Ceil(@I3) [simplification]
  +  rule #Ceil(log2Int(@I:Int)) => {(@I >Int 0) #Equals true} #And #Ceil(@I) [simplification]
   endmodule
  ```

  in module `INT-SYMBOLIC-KORE` (:1396-1397).
- Status: local
- Replaces: K text, marked lines `domains.md`:1399-1401, added (they replace no upstream line).

### AM-13: `^%Int` is the Euclidean remainder of the power

- Upstream: `domains.md` at K v7.1.337, :1229-1231, :1233-1237, :1251
- Passage:

  > * Compute the exponentiation of two integers modulo another integer (`^%Int`).
  >   `A ^%Int B C` is equal in value to `(A ^Int B) %Int C`, but has a better
  >   asymptotic complexity.

  > * Compute the quotient `/Int` or modulus `%Int` of two integers using
  >   t-division, which rounds towards zero. Division by zero is `#False`.
  > * Compute the quotient `divInt` or modulus `modInt` of two integers using
  >   Euclidean division, in which the remainder is always non-negative. Division
  >   by zero is `#False`.

  ```k
                 | Int "^%Int" Int Int            [function, symbol(_^%Int__), left, smt-hook((mod (^ #1 #2) #3)), hook(INT.powmod)]
  ```

- k-rust reads: `A ^%Int B C` is the Euclidean remainder (`modInt`) of `A ^Int B` by `C`, in `[0, |C|)`; where `A ^Int B` is negative this is not the t-division remainder `(A ^Int B) %Int C`, which takes the sign of the dividend.
- Ground: evident intent
- Reason: the operation is "the exponentiation of two integers modulo another integer", modular exponentiation, whose value is a residue modulo `C`; the sentence after it states its value through a remainder to say that the operation computes that power reduced by `C` at a better complexity.
  The production states the value as well: its `smt-hook` is `(mod (^ #1 #2) #3)`, SMT-LIB's `mod` of the power, the Euclidean remainder, in `[0, |C|)` whatever the signs of the power and of `C`.
  The two statements agree wherever the power is not negative, where the t-division and the Euclidean remainder are one number, and differ only for a negative power (a negative base at an odd exponent), where `%Int`'s remainder is negative or zero; there the text gives one application two values, and the residue the operation names and its own production states is the Euclidean one, the remainder `modInt` computes, which the section calls "always non-negative".
  So `%Int` in the prose is an omission of the wording, not a second value the text grants, and the reading changes no domain: both remainders are defined exactly where the power is and `C` is not zero (AM-12).
  The backend states every `^%Int` term to the SMT solver through that `smt-hook` (with the power read as compatibility.md's `^Int` paragraph says), so an evaluator that gave the t-division remainder would let a proof derive two values for one term.
- Evidence: `powmod_is_the_euclidean_remainder_of_the_power` in `k-rust-backend`'s [builtin.rs](../crates/k-rust-backend/src/builtin.rs) (`-2 ^%Int 3 5` is 2 and `-1 ^%Int -1 5` is 4, where `%Int` would give -3 and -1; the modulus' sign changes nothing); `kprove_proves_nothing_from_a_power_where_no_integer_is_its_value` in [cli.rs](../crates/k-rust/tests/cli.rs) states such terms to the solver; no reference differential of k-rust's runs `^%Int` at a negative power on the Java or Haskell backend.
- Upstream proposal:

  ```diff
   * Compute the exponentiation of two integers modulo another integer (`^%Int`).
  -  `A ^%Int B C` is equal in value to `(A ^Int B) %Int C`, but has a better
  +  `A ^%Int B C` is equal in value to `(A ^Int B) modInt C`, but has a better
     asymptotic complexity.
  ```

- Status: local
- Replaces: no class: k-rust's value is unchanged, and `^%Int`'s value was already determined by the production's `smt-hook` in compatibility.md; the amendment records the reading of the prose's `%Int` as the Euclidean remainder.
