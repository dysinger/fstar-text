(**
Data.Text.Codec.Chars — Pure char↔byte maps and roundtrip lemmas.

Isolated child module (fstar-proofs §44 workaround #1): touches ONLY
pure string→list byte / list byte→string maps and the char↔byte ASCII
bridge, with NO codec dependency.  This keeps the [char_of_int] /
[char_of_u32] SMTPat family (§18) out of [Data.Text.Codec] so the
recursive roundtrip induction does not re-verify in a polluted context.

Two lemmas are exported:

- [lemma_char_ascii] — per-character fact: an ASCII char satisfying
  [pred] encodes to a matchable byte and roundtrips back to itself.
  The ASCII bound is an EXPLICIT [requires] ([int_of_char c < 128 &&
  pred c]), never derived by unfolding a recursive predicate, so
  [small_mod] always gets its [< 256] precondition.

- [lemma_chars_roundtrip_all] — list-level induction proving, for a list
  of ASCII chars each satisfying [pred], both (a) every encoded byte is
  byte-level matchable, and (b) the char→byte→char map roundtrips.

@header Data.Text.Codec.Chars
*)
module Data.Text.Codec.Chars

open FStar.UInt8
open FStar.Char
open FStar.String
open FStar.List.Tot
open FStar.Math.Lemmas
open FStar.Mul

module U8 = FStar.UInt8

(** Convert a char to its low byte, unconditionally.

    The [% 256] truncation is a totality safety net.  Well-formed
    [text_chars] strings are all-ASCII ([int_of_char c < 128]), so for
    them the truncation is the identity — proven by [lemma_char_ascii]
    via [small_mod]. *)
unfold
let char_to_byte_trunc (c: FStar.Char.char) : byte =
  FStar.UInt8.uint_to_t (FStar.Char.int_of_char c % 256)

(** Convert an ASCII byte (< 128) to its character. *)
let byte_to_char (b: byte{FStar.UInt8.v b < 128}) : Tot FStar.Char.char =
  FStar.Char.char_of_int (FStar.UInt8.v b)

(** Convert a string to its low-byte list. *)
unfold
let text_string_to_bytes (s: string) : list byte =
  FStar.List.Tot.map char_to_byte_trunc (FStar.String.list_of_string s)

(** Convert a byte list to a string (each byte becomes its codepoint). *)
unfold
let text_bytes_to_string (bs: list byte) : string =
  FStar.String.string_of_list
    (FStar.List.Tot.map (fun b -> FStar.Char.char_of_int (FStar.UInt8.v b)) bs)

(** A character is ASCII and satisfies [pred]. *)
let ascii_ok (pred: FStar.Char.char -> bool) (c: FStar.Char.char) : bool =
  FStar.Char.int_of_char c < 128 && pred c

(** A byte is matchable: < 128 and its character satisfies [pred]. *)
let byte_matchable (pred: FStar.Char.char -> bool) (b: byte) : bool =
  U8.v b < 128 && pred (byte_to_char b)

(** Per-character ASCII fact: matchability + roundtrip, without any
    recursive predicate in the requires. *)
let lemma_char_ascii (pred: FStar.Char.char -> bool) (c: FStar.Char.char)
  : Lemma
    (requires ascii_ok pred c)
    (ensures
      byte_matchable pred (char_to_byte_trunc c) /\
      FStar.Char.char_of_int (U8.v (char_to_byte_trunc c)) == c)
  = FStar.Math.Lemmas.small_mod (FStar.Char.int_of_char c) 256;
    FStar.Char.char_of_u32_of_char c;
    ()

(** List-level induction: matchability + string roundtrip for ASCII lists. *)
let rec lemma_chars_roundtrip_all (pred: FStar.Char.char -> bool) (chars: list FStar.Char.char)
  : Lemma
    (requires List.Tot.for_all (ascii_ok pred) chars)
    (ensures
      List.Tot.for_all (byte_matchable pred) (List.Tot.map char_to_byte_trunc chars) /\
      List.Tot.map (fun b -> FStar.Char.char_of_int (FStar.UInt8.v b))
        (List.Tot.map char_to_byte_trunc chars) == chars)
    (decreases chars)
  = match chars with
    | [] -> ()
    | c :: tl ->
        lemma_char_ascii pred c;
        lemma_chars_roundtrip_all pred tl;
        ()

(** Top-level string roundtrip: bytes→string for an ASCII string. *)
let lemma_text_string_to_bytes_roundtrip (pred: FStar.Char.char -> bool) (s: string)
  : Lemma
    (requires List.Tot.for_all (ascii_ok pred) (FStar.String.list_of_string s))
    (ensures text_bytes_to_string (text_string_to_bytes s) == s)
  = let chars = FStar.String.list_of_string s in
    lemma_chars_roundtrip_all pred chars;
    FStar.String.string_of_list_of_string s;
    ()
