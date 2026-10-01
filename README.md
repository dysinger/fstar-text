# Data.Text.Codec — Verified Text Codec Library

A formally verified text codec library in F*, built on the record-based
[Data.Codec] combinator framework.  Provides the bounded-greedy
[text_chars] combinator (one-or-more ASCII characters), UTF-8 encoding and
decoding (RFC 3629), ASCII char↔byte bridges, delimiter codecs (CRLF/SP),
and a Pulse text-encoding tag codec for C extraction (Custard).

Zero admits.  Zero magic.  All roundtrip proofs are structural.

## Architecture

```
Data.Text.Codec          — text_chars combinator + scan/roundtrip lemmas
Data.Text.Codec.Chars    — pure char↔byte maps + ASCII roundtrip induction
Data.Text.Codec.Delims   — CRLF + SP delimiter codecs
Data.Text.Codec.Zero     — empty-aware text_chars0 combinator
Data.Text.Codec.UTF8     — RFC 3629 UTF-8 encode/decode + roundtrip proof
Data.Text.Codec.UTF8String — UTF-8-aware codec string
Data.Text.Codec.Pulse    — C-extractable text-encoding tag codec
```

The char↔byte roundtrip induction is isolated in [Data.Text.Codec.Chars]
(not in [Data.Text.Codec]) to avoid SMT-context pollution from the
[char_of_int]/[char_of_u32] SMTPat family (fstar-proofs §44).  Delimiter
codecs live in [Data.Text.Codec.Delims] rather than [Data.Text.Codec] to
keep [Data.Text.Codec] a single-combinator module (fstar-proofs §45).

## Key properties

- **Zero admits / zero magic.**  Every module verifies with structural
  roundtrip proofs; no `admit()`, no `magic ()`.
- **RFC 3629 compliance.**  [utf8_decode_one] rejects overlong encodings
  (2-, 3-, and 4-byte forms), surrogates, code points above U+10FFFF, and
  truncated sequences.  Minimal forms ([0xE0 0xA0 0x80], [0xF0 0x90 0x80 0x80])
  remain accepted.
- **Bounded greedy [text_chars].**  The [text_chars max pred] decoder is
  BOUNDED greedy (consumes at most [max] bytes), mirroring
  [digits_to_int max_len].  An unbounded greedy scan is not a valid
  invertible-syntax codec (fstar-proofs §43).
- **C extraction.**  [Data.Text.Codec.Pulse] extracts to C11 via Custard
  (`--custard_backend C`, no KaRaMeL).

## text_chars API

[text_chars] takes TWO arguments — this is a BREAKING change from the
GADT-era one-argument form:

```fstar
let text_chars (max: nat) (pred: FStar.Char.char -> bool) : codec string
```

- [max] is the maximum number of bytes the decoder may consume.
  Callers MUST choose a defensible bound (e.g. 8192 for HTTP header
  names/values) — DO NOT pass an unbounded value.
- [pred] is the per-character predicate (ASCII, code point < 128).

## U+D7FF limitation

F*'s [FStar.Char.char_code] is [n < 0xd7ff] (exclusive).  The Unicode scalar
U+D7FF (the last value before the surrogate range) is a VALID RFC 3629
scalar that [FStar.Char.char] cannot represent.  [utf8_decode_one] therefore
rejects [0xED 0x9F 0xBF] (U+D7FF) — this is an F* library bound, not an RFC
3629 violation.  Documented in [Data.Text.Codec.UTF8].[mk_char] and tested
by [test_reject_d7ff].

## Build

```sh
nix develop
make check    # Verify all modules (src + test)
```

Or via nix:

```sh
nix build .#checked  # F* verification gate (0-admit)
nix build .#native   # C11 shared/static lib (default)
nix build .#ocaml    # OCaml findlib package
nix build .#fsharp   # .NET library
```

## Test coverage

Test modules (all zero-admit) in `test/`:

| Module | Coverage |
|--------|----------|
| `Data.Text.Codec.Test.UTF8` | RFC 3629 overlong/surrogate/above-max rejections, minimal-form acceptance, roundtrip vectors (1-4 byte) |
| `Data.Text.Codec.Test.Delims` | CRLF/SP encode length + roundtrip + rejection paths |
| `Data.Text.Codec.Test.Roundtrip` | text_chars edge cases (empty input, max=0, non-match), byte_matchable/ascii_ok predicates |
| `Data.Text.Codec.Test.Zero` | text_chars0 empty-string roundtrip |
| `Data.Text.Codec.Test.UTF8String` | UTF-8 string empty/non-ASCII roundtrip |
| `Data.Text.Codec.Test.Pulse` | Buffer roundtrips + unknown-tag rejection for the Pulse tag codec |
| `Data.Text.Codec.Test.Integration` | Coverage anchors for every public symbol (122 bindings) |

## Dependencies

- `Data.Codec` — record `codec` combinator library (Types: `custom`, `bytes`, `byte_val`, `product`, `map_`)

## Normative reference

The full RFC 3629 text is vendored at `docs/rfc3629.txt` for offline
auditing.  `utf8_decode_one` is verified against RFC 3629 §3 (Table 3-6
lead/continuation byte ranges) and §4 (overlong-form rejection).
