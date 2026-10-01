(**
Data.Text.Codec.UTF8 — UTF-8 encoding and decoding (RFC 3629).

A self-contained RFC package: [char_to_utf8] encodes a [FStar.Char.char]
to 1-4 UTF-8 bytes, and [utf8_decode_one] decodes one character from a
byte list, validating overlong encodings, surrogates, and code points
above U+10FFFF (RFC 3629 §3).

F*'s [FStar.Char.char] type already represents only valid Unicode scalar
values (code points in [[0, 0xD7FF] ∪ [0xE000, 0x10FFFF]]).  A valid char
never encodes to an overlong, surrogate, or above-max form.  The decoder's
rejection cases cover malformed byte sequences only; [mk_char] gates every
[char_of_int] with the exact [char_code] bound, so no [magic] is needed.

Every lemma is proven by explicit case analysis on the byte length (1-4
bytes), using [FStar.Char.char_of_u32_of_char] and the integer
decomposition identity [FStar.Math.Lemmas.lemma_div_mod].  Zero admits.

@header Data.Text.Codec.UTF8
*)
module Data.Text.Codec.UTF8

open Data.Codec
open FStar.String
open FStar.Char
open FStar.UInt8
open FStar.UInt32
open FStar.List.Tot
open FStar.Math.Lemmas

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module L = FStar.List.Tot

(* ── Encode / decode (alphabetical) ─────────────────────────────────── *)

(** [char_to_utf8 c] — encode a char as UTF-8 (1-4 bytes per RFC 3629 §3). *)
let char_to_utf8 (c: FStar.Char.char) : list byte =
  let code = FStar.Char.int_of_char c in
  if code < 0x80 then
    [U8.uint_to_t code]
  else if code < 0x800 then
    [U8.uint_to_t (0xC0 + (code / 64));
     U8.uint_to_t (0x80 + (code % 64))]
  else if code < 0x10000 then
    [U8.uint_to_t (0xE0 + (code / 4096));
     U8.uint_to_t (0x80 + ((code / 64) % 64));
     U8.uint_to_t (0x80 + (code % 64))]
  else
    [U8.uint_to_t (0xF0 + (code / 262144));
     U8.uint_to_t (0x80 + ((code / 4096) % 64));
     U8.uint_to_t (0x80 + ((code / 64) % 64));
     U8.uint_to_t (0x80 + (code % 64))]

(** [is_cont b] — a byte is a UTF-8 continuation byte (0b10xxxxxx). *)
let is_cont (b: byte) : bool = U8.v b >= 0x80 && U8.v b < 0xC0

(** [mk_char cp] — construct a char from a code point only if it is a valid
    Unicode scalar value representable in [FStar.Char.char].

    LIMITATION: [FStar.Char.char_code] is [n < 0xd7ff] (exclusive), so the
    Unicode scalar U+D7FF (the last value before the surrogate range) is a
    VALID RFC 3629 scalar that F*'s [char] type cannot represent.  This
    [mk_char] gate yields only [FStar.Char.char]-representable scalars; U+D7FF
    is excluded by the F* library bound, not by RFC 3629.  This is documented
    in README.md.

    NOTE ON PINNING: the F* [FStar.Char.fsti] DOC comment says "not between
    0xd800 and 0xe000" (Unicode-correct), but the ACTUAL [char_code] type
    refinement is [n < 0xd7ff] (off-by-one — it excludes U+D7FF, a valid
    scalar).  [mk_char] gates on the ACTUAL type bound ([< 0xD7FF]), NOT the
    doc comment ([< 0xD800]) — using the doc bound would make
    [char_of_int 0xD7FF] a type error.  [lemma_char_code_bound_pinned] below
    asserts the exact bound so a future F* change fails verification loudly
    rather than silently changing decoder semantics.

    The bound matches [FStar.Char.char_code] exactly
    ([[0, 0xD7FF] ∪ [0xE000, 0x10FFFF]]), so the [char_of_int] refinement
    discharges without any [magic]. *)
let mk_char (cp: int) : option FStar.Char.char =
  if cp >= 0 && cp < 0xD7FF then
    Some (FStar.Char.char_of_int cp)
  else if cp >= 0xE000 && cp <= 0x10FFFF then
    Some (FStar.Char.char_of_int cp)
  else None

(** [utf8_decode_one bs] — decode one UTF-8 character from the head of a byte
    list (RFC 3629 §3).

    Returns [None] on malformed input (overlong, surrogate, above-max, or
    truncated).  On success, returns the char and the remaining bytes. *)
let utf8_decode_one (bs: list byte) : option (FStar.Char.char & list byte) =
  match bs with
  | [] -> None
  | b0 :: rest ->
    let v0 = U8.v b0 in
    if v0 < 0x80 then
      (match mk_char v0 with
       | Some c -> Some (c, rest)
       | None -> None)
    else if v0 >= 0xC2 && v0 <= 0xDF then
      (* 2-byte: 110xxxxx 10xxxxxx (overlong 0xC0/0xC1 already excluded) *)
      (match rest with
       | b1 :: rest' ->
         let v1 = U8.v b1 in
         if is_cont b1 then
           let cp = ((v0 - 0xC0) * 64) + (v1 - 0x80) in
           (match mk_char cp with
            | Some c -> Some (c, rest')
            | None -> None)
         else None
       | [] -> None)
    else if v0 >= 0xE0 && v0 <= 0xEF then
      (* 3-byte: 1110xxxx 10xxxxxx 10xxxxxx
         RFC 3629 §4: UTF8-3 = %xE0 %xA0-BF UTF8-tail / %xE1-EC 2(UTF8-tail)
         / %xED %x80-9F UTF8-tail / %xEE-EF 2(UTF8-tail).  The %xE0 lead must
         be followed by %xA0..%xBF, else the form is overlong (decodes to a
         sub-0x800 scalar).  The %xED surrogate case is handled by [mk_char]. *)
      (match rest with
       | b1 :: b2 :: rest' ->
         let v1 = U8.v b1 in
         let v2 = U8.v b2 in
         let second_ok = v0 <> 0xE0 || v1 >= 0xA0 in
         if is_cont b1 && is_cont b2 && second_ok then
           let cp = ((v0 - 0xE0) * 4096) + ((v1 - 0x80) * 64) + (v2 - 0x80) in
           (match mk_char cp with
            | Some c -> Some (c, rest')
            | None -> None)
         else None
       | _ -> None)
    else if v0 >= 0xF0 && v0 <= 0xF4 then
      (* 4-byte: 11110xxx 10xxxxxx 10xxxxxx 10xxxxxx (0xF5..0xFF rejected)
         RFC 3629 §4: UTF8-4 = %xF0 %x90-BF 2(UTF8-tail) / %xF1-F3 3(UTF8-tail)
         / %xF4 %x80-8F 2(UTF8-tail).  The %xF0 lead must be followed by
         %x90..%xBF, else the form is overlong (decodes to a sub-0x10000
         scalar).  The %xF4 above-max case is handled by [mk_char]. *)
      (match rest with
       | b1 :: b2 :: b3 :: rest' ->
         let v1 = U8.v b1 in
         let v2 = U8.v b2 in
         let v3 = U8.v b3 in
         let second_ok = v0 <> 0xF0 || v1 >= 0x90 in
         if is_cont b1 && is_cont b2 && is_cont b3 && second_ok then
           let cp = ((v0 - 0xF0) * 262144) + ((v1 - 0x80) * 4096)
                    + ((v2 - 0x80) * 64) + (v3 - 0x80) in
           (match mk_char cp with
            | Some c -> Some (c, rest')
            | None -> None)
         else None
       | _ -> None)
    else None

(** [utf8_bytes s] — a fixed UTF-8 string as a codec.

    Uses the [bytes] combinator (Data.Codec.Types combinator 6) over the
    UTF-8 byte list.  This is the record-codec replacement for the old
    GADT-era [text]/[bytes] helpers. *)
let utf8_bytes (s: string) : codec unit =
  bytes (L.concatMap char_to_utf8 (FStar.String.list_of_string s))

(* ── Boundary + width lemmas (alphabetical) ─────────────────────────── *)

(** [lemma_char_code_bound_pinned] — pin the F* [char_code] bound this
    decoder's [mk_char] gate relies on.

    Asserts that U+D7FF (0xD7FF) is NOT representable in [FStar.Char.char]
    (i.e. [char_of_int 0xD7FF] is a type error, so [mk_char 0xD7FF == None])
    while U+E000 (0xE000, the first scalar after the surrogate gap) IS
    representable.  If a future F* release widens [char_of_int] to include
    0xD7FF, the first conjunct's [mk_char 0xD7FF == None] becomes false and
    this lemma fails to verify — a loud signal that the documented limitation
    must be revisited (fstar-proofs §46). *)
let lemma_char_code_bound_pinned () : Lemma
  (ensures mk_char 0xD7FF == None /\ mk_char 0xE000 == Some (FStar.Char.char_of_int 0xE000))
  = ()

(** [lemma_char_to_utf8_len c] — [char_to_utf8] always produces 1-4 bytes. *)
let lemma_char_to_utf8_len (c: FStar.Char.char) : Lemma
  (ensures 1 <= L.length (char_to_utf8 c) && L.length (char_to_utf8 c) <= 4)
  = ()

(** [lemma_utf8_1byte c] — 1-byte ASCII case: code < 0x80. *)
let lemma_utf8_1byte (c: FStar.Char.char) : Lemma
  (requires FStar.Char.int_of_char c < 0x80)
  (ensures utf8_decode_one (char_to_utf8 c) == Some (c, []))
  = let code = FStar.Char.int_of_char c in
    FStar.Char.char_of_u32_of_char c;
    assert (char_to_utf8 c == [U8.uint_to_t code]);
    assert (U8.v (U8.uint_to_t code) == code);
    ()

(** [lemma_utf8_2byte c] — 2-byte case: 0x80 <= code < 0x800. *)
#push-options "--z3rlimit 200"
let lemma_utf8_2byte (c: FStar.Char.char) : Lemma
  (requires FStar.Char.int_of_char c >= 0x80 && FStar.Char.int_of_char c < 0x800)
  (ensures utf8_decode_one (char_to_utf8 c) == Some (c, []))
  = let code = FStar.Char.int_of_char c in
    let b0 = U8.uint_to_t (0xC0 + (code / 64)) in
    let b1 = U8.uint_to_t (0x80 + (code % 64)) in
    lemma_div_mod code 64;
    assert (code / 64 < 0x20);
    assert (code % 64 < 0x40);
    assert (is_cont b1);
    assert (U8.v b0 >= 0xC2 && U8.v b0 <= 0xDF);
    let cp = ((U8.v b0 - 0xC0) * 64) + (U8.v b1 - 0x80) in
    assert (U8.v b0 - 0xC0 == code / 64);
    assert (U8.v b1 - 0x80 == code % 64);
    assert (cp == code);
    FStar.Char.char_of_u32_of_char c;
    ()
#pop-options

(** [lemma_utf8_3byte c] — 3-byte case: 0x800 <= code < 0x10000 (F* chars
    exclude surrogates). *)
#push-options "--z3rlimit 400"
let lemma_utf8_3byte (c: FStar.Char.char) : Lemma
  (requires FStar.Char.int_of_char c >= 0x800 && FStar.Char.int_of_char c < 0x10000)
  (ensures utf8_decode_one (char_to_utf8 c) == Some (c, []))
  = let code = FStar.Char.int_of_char c in
    let b0 = U8.uint_to_t (0xE0 + (code / 4096)) in
    let b1 = U8.uint_to_t (0x80 + ((code / 64) % 64)) in
    let b2 = U8.uint_to_t (0x80 + (code % 64)) in
    lemma_div_mod code 64;
    lemma_div_mod (code / 64) 64;
    assert (code / 4096 < 0x10);
    assert ((code / 64) % 64 < 0x40);
    assert (code % 64 < 0x40);
    assert (is_cont b1 && is_cont b2);
    let cp = ((U8.v b0 - 0xE0) * 4096) + ((U8.v b1 - 0x80) * 64) + (U8.v b2 - 0x80) in
    assert (U8.v b0 - 0xE0 == code / 4096);
    assert (U8.v b1 - 0x80 == (code / 64) % 64);
    assert (U8.v b2 - 0x80 == code % 64);
    assert (cp == code);
    (* code is a valid F* char code, so not in the surrogate range *)
    assert (not (cp >= 0xD800 && cp <= 0xDFFF));
    FStar.Char.char_of_u32_of_char c;
    ()
#pop-options

(** [lemma_utf8_4byte c] — 4-byte case: 0x10000 <= code <= 0x10FFFF. *)
#push-options "--z3rlimit 400"
let lemma_utf8_4byte (c: FStar.Char.char) : Lemma
  (requires FStar.Char.int_of_char c >= 0x10000)
  (ensures utf8_decode_one (char_to_utf8 c) == Some (c, []))
  = let code = FStar.Char.int_of_char c in
    let b0 = U8.uint_to_t (0xF0 + (code / 262144)) in
    let b1 = U8.uint_to_t (0x80 + ((code / 4096) % 64)) in
    let b2 = U8.uint_to_t (0x80 + ((code / 64) % 64)) in
    let b3 = U8.uint_to_t (0x80 + (code % 64)) in
    lemma_div_mod code 64;
    lemma_div_mod (code / 64) 64;
    lemma_div_mod (code / 4096) 64;
    assert (code / 262144 < 0x08);  (* code <= 0x10FFFF *)
    assert ((code / 4096) % 64 < 0x40);
    assert ((code / 64) % 64 < 0x40);
    assert (code % 64 < 0x40);
    assert (is_cont b1 && is_cont b2 && is_cont b3);
    let cp = ((U8.v b0 - 0xF0) * 262144) + ((U8.v b1 - 0x80) * 4096)
             + ((U8.v b2 - 0x80) * 64) + (U8.v b3 - 0x80) in
    assert (U8.v b0 - 0xF0 == code / 262144);
    assert (U8.v b1 - 0x80 == (code / 4096) % 64);
    assert (U8.v b2 - 0x80 == (code / 64) % 64);
    assert (U8.v b3 - 0x80 == code % 64);
    assert (cp == code);
    assert (cp <= 0x10FFFF);
    FStar.Char.char_of_u32_of_char c;
    ()
#pop-options

(** [lemma_utf8_roundtrip c] — exhaustive case analysis: encode-decode
    roundtrip for every char. *)
#push-options "--z3rlimit 400"
let lemma_utf8_roundtrip (c: FStar.Char.char) : Lemma
  (ensures utf8_decode_one (char_to_utf8 c) == Some (c, []))
  = let code = FStar.Char.int_of_char c in
    if code < 0x80 then lemma_utf8_1byte c
    else if code < 0x800 then lemma_utf8_2byte c
    else if code < 0x10000 then lemma_utf8_3byte c
    else lemma_utf8_4byte c
#pop-options

(** [lemma_utf8_encode_valid c] — every char encodes to 1-4 bytes and decodes
    back to [Some c]. *)
let lemma_utf8_encode_valid (c: FStar.Char.char) : Lemma
  (ensures (let bs = char_to_utf8 c in
    L.length bs >= 1 && L.length bs <= 4 &&
    Some? (utf8_decode_one bs)))
  = lemma_utf8_roundtrip c;
    lemma_char_to_utf8_len c

(* ── Prefix lemmas (alphabetical) ───────────────────────────────────── *)

(** Prefix bridge: [utf8_decode_one] consumes exactly the head char's encoding
    and returns the SUFFIX unchanged, for a NON-EMPTY suffix [rest].  This is
    the §59 Fact-2 lemma needed by the UTF-8-aware char-run scan
    ([Data.Text.Codec.UTF8String]): over a string [char_to_utf8 c @ rest],
    decoding one char returns [c] and the original [rest], regardless of byte
    width (1-4).

    The empty-suffix form [utf8_decode_one (char_to_utf8 c) == Some (c, [])]
    is [lemma_utf8_roundtrip]; these prefix lemmas generalize it to arbitrary
    [rest] by the same per-byte-length case discipline. *)

(** [lemma_utf8_1byte_prefix c rest] — 1-byte ASCII prefix with arbitrary
    suffix. *)
#push-options "--z3rlimit 200"
let lemma_utf8_1byte_prefix (c: FStar.Char.char) (rest: list byte) : Lemma
  (requires FStar.Char.int_of_char c < 0x80)
  (ensures utf8_decode_one (char_to_utf8 c @ rest) == Some (c, rest))
  = let code = FStar.Char.int_of_char c in
    let b0 = U8.uint_to_t code in
    FStar.Char.char_of_u32_of_char c;
    assert (char_to_utf8 c == [b0]);
    assert (char_to_utf8 c @ rest == b0 :: rest);
    assert (utf8_decode_one (b0 :: rest) == Some (c, rest));
    ()
#pop-options

(** [lemma_utf8_2byte_prefix c rest] — 2-byte prefix with arbitrary suffix. *)
#push-options "--z3rlimit 400"
let lemma_utf8_2byte_prefix (c: FStar.Char.char) (rest: list byte) : Lemma
  (requires FStar.Char.int_of_char c >= 0x80 && FStar.Char.int_of_char c < 0x800)
  (ensures utf8_decode_one (char_to_utf8 c @ rest) == Some (c, rest))
  = let code = FStar.Char.int_of_char c in
    let b0 = U8.uint_to_t (0xC0 + (code / 64)) in
    let b1 = U8.uint_to_t (0x80 + (code % 64)) in
    lemma_div_mod code 64;
    assert (code / 64 < 0x20);
    assert (code % 64 < 0x40);
    assert (is_cont b1);
    assert (U8.v b0 >= 0xC2 && U8.v b0 <= 0xDF);
    let cp = ((U8.v b0 - 0xC0) * 64) + (U8.v b1 - 0x80) in
    assert (U8.v b0 - 0xC0 == code / 64);
    assert (U8.v b1 - 0x80 == code % 64);
    assert (cp == code);
    assert (char_to_utf8 c == [b0; b1]);
    assert (char_to_utf8 c @ rest == b0 :: b1 :: rest);
    FStar.Char.char_of_u32_of_char c;
    ()
#pop-options

(** [lemma_utf8_3byte_prefix c rest] — 3-byte prefix with arbitrary suffix. *)
#push-options "--z3rlimit 400"
let lemma_utf8_3byte_prefix (c: FStar.Char.char) (rest: list byte) : Lemma
  (requires FStar.Char.int_of_char c >= 0x800 && FStar.Char.int_of_char c < 0x10000)
  (ensures utf8_decode_one (char_to_utf8 c @ rest) == Some (c, rest))
  = let code = FStar.Char.int_of_char c in
    let b0 = U8.uint_to_t (0xE0 + (code / 4096)) in
    let b1 = U8.uint_to_t (0x80 + ((code / 64) % 64)) in
    let b2 = U8.uint_to_t (0x80 + (code % 64)) in
    lemma_div_mod code 64;
    lemma_div_mod (code / 64) 64;
    assert (code / 4096 < 0x10);
    assert ((code / 64) % 64 < 0x40);
    assert (code % 64 < 0x40);
    assert (is_cont b1 && is_cont b2);
    let cp = ((U8.v b0 - 0xE0) * 4096) + ((U8.v b1 - 0x80) * 64) + (U8.v b2 - 0x80) in
    assert (U8.v b0 - 0xE0 == code / 4096);
    assert (U8.v b1 - 0x80 == (code / 64) % 64);
    assert (U8.v b2 - 0x80 == code % 64);
    assert (cp == code);
    assert (not (cp >= 0xD800 && cp <= 0xDFFF));
    assert (char_to_utf8 c == [b0; b1; b2]);
    assert (char_to_utf8 c @ rest == b0 :: b1 :: b2 :: rest);
    FStar.Char.char_of_u32_of_char c;
    ()
#pop-options

(** [lemma_utf8_4byte_prefix c rest] — 4-byte prefix with arbitrary suffix. *)
#push-options "--z3rlimit 400"
let lemma_utf8_4byte_prefix (c: FStar.Char.char) (rest: list byte) : Lemma
  (requires FStar.Char.int_of_char c >= 0x10000)
  (ensures utf8_decode_one (char_to_utf8 c @ rest) == Some (c, rest))
  = let code = FStar.Char.int_of_char c in
    let b0 = U8.uint_to_t (0xF0 + (code / 262144)) in
    let b1 = U8.uint_to_t (0x80 + ((code / 4096) % 64)) in
    let b2 = U8.uint_to_t (0x80 + ((code / 64) % 64)) in
    let b3 = U8.uint_to_t (0x80 + (code % 64)) in
    lemma_div_mod code 64;
    lemma_div_mod (code / 64) 64;
    lemma_div_mod (code / 4096) 64;
    assert (code / 262144 < 0x08);
    assert ((code / 4096) % 64 < 0x40);
    assert ((code / 64) % 64 < 0x40);
    assert (code % 64 < 0x40);
    assert (is_cont b1 && is_cont b2 && is_cont b3);
    let cp = ((U8.v b0 - 0xF0) * 262144) + ((U8.v b1 - 0x80) * 4096)
             + ((U8.v b2 - 0x80) * 64) + (U8.v b3 - 0x80) in
    assert (U8.v b0 - 0xF0 == code / 262144);
    assert (U8.v b1 - 0x80 == (code / 4096) % 64);
    assert (U8.v b2 - 0x80 == (code / 64) % 64);
    assert (U8.v b3 - 0x80 == code % 64);
    assert (cp == code);
    assert (cp <= 0x10FFFF);
    assert (char_to_utf8 c == [b0; b1; b2; b3]);
    assert (char_to_utf8 c @ rest == b0 :: b1 :: b2 :: b3 :: rest);
    FStar.Char.char_of_u32_of_char c;
    ()
#pop-options

(** [lemma_utf8_decode_prefix c rest] — exhaustive dispatcher:
    [utf8_decode_one] consumes exactly the head char's encoding and returns
    the arbitrary suffix unchanged, for every char. *)
#push-options "--z3rlimit 400"
let lemma_utf8_decode_prefix (c: FStar.Char.char) (rest: list byte) : Lemma
  (ensures utf8_decode_one (char_to_utf8 c @ rest) == Some (c, rest))
  = let code = FStar.Char.int_of_char c in
    if code < 0x80 then lemma_utf8_1byte_prefix c rest
    else if code < 0x800 then lemma_utf8_2byte_prefix c rest
    else if code < 0x10000 then lemma_utf8_3byte_prefix c rest
    else lemma_utf8_4byte_prefix c rest
#pop-options
