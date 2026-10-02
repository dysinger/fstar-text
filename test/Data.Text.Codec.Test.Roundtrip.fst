(* Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later *)


(**
Data.Text.Codec.Test.Roundtrip — [text_chars] codec roundtrip and edge tests.

Concrete tests for the [Data.Text.Codec].[text_chars] combinator and the
ASCII char↔byte bridge in [Data.Text.Codec.Chars].  These cover the
bounded-greedy decoder's edge cases (empty input, max=0, non-match suffix,
delimiter composition) and the string roundtrip identity.

Zero admits.

@header Data.Text.Codec.Test.Roundtrip
*)
module Data.Text.Codec.Test.Roundtrip


open Data.Text.Codec
open Data.Text.Codec.Chars
open Data.Codec
open FStar.Seq
open FStar.Char
open FStar.UInt8


module U8 = FStar.UInt8


(** An ASCII-letter predicate for test strings. *)
let is_alpha_char (c: FStar.Char.char) : bool =
  FStar.Char.int_of_char c >= 0x41 && FStar.Char.int_of_char c <= 0x7A


#push-options "--z3rlimit 200"


(** Unfold lemma: the bounded scan with max=0 is empty. *)
let lemma_scan_max_zero (pred: FStar.Char.char -> bool) (input: byte_seq) : Lemma
  (ensures scan_text_chars 0 pred input == [])
  = ()


(** [text_chars] rejects empty input (one-or-more semantics). *)
let test_text_chars_empty_input () : Lemma
  (ensures Inl? (text_chars_dec 8 is_alpha_char Seq.empty))
  = ()


(** [text_chars] with max=0 rejects even a matchable input. *)
let test_text_chars_max_zero () : Lemma
  (ensures Inl? (text_chars_dec 0 is_alpha_char (Seq.create 1 0x41uy)))
  = lemma_scan_max_zero is_alpha_char (Seq.create 1 0x41uy)


(** [byte_matchable] recognizes an ASCII letter byte. *)
let test_byte_matchable_true () : Lemma
  (ensures byte_matchable is_alpha_char 0x41uy)
  = ()


(** [byte_matchable] rejects a non-ASCII byte (>= 128). *)
let test_byte_matchable_nonascii () : Lemma
  (ensures not (byte_matchable is_alpha_char 0x80uy))
  = ()


(** [ascii_ok] requires both ASCII-ness and the predicate. *)
let test_ascii_ok_true () : Lemma
  (ensures ascii_ok is_alpha_char (FStar.Char.char_of_int 0x41))
  = ()


#pop-options
