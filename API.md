# Data.Text.Codec API Reference

## Types

### Data.Text.Codec.Chars — Char↔byte bridge

| Function | Signature | Description |
|----------|-----------|-------------|
| `char_to_byte_trunc` | `FStar.Char.char -> byte` | Low byte of a char (`int_of_char c % 256`) |
| `byte_to_char` | `byte{U8.v < 128} -> FStar.Char.char` | ASCII byte → char |
| `text_string_to_bytes` | `string -> list byte` | String → low-byte list |
| `text_bytes_to_string` | `list byte -> string` | Byte list → string (each byte is its codepoint) |
| `ascii_ok` | `(char -> bool) -> char -> bool` | Char is ASCII (< 128) and satisfies predicate |
| `byte_matchable` | `(char -> bool) -> byte -> bool` | Byte < 128 and its char satisfies predicate |

### Data.Text.Codec — text_chars combinator

| Function | Signature | Description |
|----------|-----------|-------------|
| `text_chars` | `nat -> (char -> bool) -> codec string` | One-or-more ASCII chars, bounded-greedy decode |
| `text_chars_dec` | `nat -> (char -> bool) -> byte_seq -> decode_result string` | Bounded-greedy scan decoder |
| `text_chars_enc` | `(char -> bool) -> string -> byte_seq` | String → byte sequence |
| `text_chars_wfcv` | `nat -> (char -> bool) -> string -> bool` | Non-empty, ≤ max, all-ASCII-matchable guard |
| `text_chars_wfcv_prop` | `nat -> (char -> bool) -> string -> prop` | Well-formed proposition (True) |
| `text_chars_rest_cond` | `nat -> (char -> bool) -> string -> byte_seq -> prop` | 3-disjunct suffix condition |
| `scan_text_chars` | `nat -> (char -> bool) -> byte_seq -> list byte` | Bounded-greedy scan |

### Data.Text.Codec.Delims — Delimiter codecs

| Function | Signature | Description |
|----------|-----------|-------------|
| `crlf` | `codec unit` | CR (0x0D) + LF (0x0A) |
| `sp` | `codec unit` | Single space (0x20) |

### Data.Text.Codec.UTF8 — RFC 3629 UTF-8

| Function | Signature | Description |
|----------|-----------|-------------|
| `char_to_utf8` | `FStar.Char.char -> list byte` | Encode a char to 1-4 UTF-8 bytes |
| `utf8_decode_one` | `list byte -> option (char & list byte)` | Decode one char, validating overlong/surrogate/above-max |
| `is_cont` | `byte -> bool` | UTF-8 continuation byte (0b10xxxxxx) |
| `mk_char` | `int -> option FStar.Char.char` | Code point → char (gated on char_code bound) |
| `utf8_bytes` | `string -> codec unit` | Fixed UTF-8 string codec via `bytes` |

### Data.Text.Codec.Pulse — C-extractable tag codec

| Type / Function | Signature | Description |
|----------|-----------|-------------|
| `text_enc` | `TE_ASCII \| TE_UTF8 \| TE_UTF16` | Text encodings |
| `opt_text_enc` | `OTE_None \| OTE_Some (text_enc & U32.t)` | Decode result (C-friendly) |
| `tag_of` | `text_enc -> U8.t` | Encoding → tag byte |
| `tag_to_type` | `U8.t -> option text_enc` | Tag byte → encoding |
| `encode` | `fn text_enc -> A.array U8.t -> U32.t -> U32.t` | Buffer tag encode |
| `decode` | `fn A.array U8.t -> U32.t -> opt_text_enc` | Buffer tag decode |

## Lemmas

| Lemma | Proves |
|-------|--------|
| `lemma_char_ascii` | Matchability + roundtrip for a single ASCII char |
| `lemma_chars_roundtrip_all` | List-level: matchability + string roundtrip for ASCII lists |
| `lemma_text_string_to_bytes_roundtrip` | bytes→string identity for ASCII strings |
| `lemma_scan_consumed_le_len` | Bounded scan consumes ≤ input length |
| `lemma_scan_prefix` | Matchable prefix scans to its own length |
| `lemma_text_chars_roundtrip` | dec(enc v ++ r) == Inr (v, \|enc v\|) |
| `lemma_utf8_1byte` / `2byte` / `3byte` / `4byte` | Per-byte-length encode→decode roundtrip |
| `lemma_utf8_roundtrip` | Exhaustive encode→decode roundtrip for every char |
| `lemma_utf8_encode_valid` | Every char encodes to 1-4 bytes and decodes back |
| `lemma_char_code_bound_pinned` | Pins F* char_code bound: U+D7FF representable? (build-time guard against stdlib drift) |
| `lemma_roundtrip` (Pulse) | tag_of then tag_to_type recovers the original |
| `lemma_pulse_roundtrip` / `lemma_pulse_encode_decode_match` (Pulse) | Pulse encode/decode agree with the pure spec |
