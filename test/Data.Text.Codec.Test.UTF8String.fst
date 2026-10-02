(* Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later *)


(**
Data.Text.Codec.Test.UTF8String — compliance tests for the [utf8_string]
combinator.

Concrete tests for the UTF-8-aware [codec string] in
[Data.Text.Codec.UTF8String], covering a non-ASCII character name (U+00E9,
"e with acute accent") — the one behavior that distinguishes it from the
ASCII-only [text_chars].  The tests re-state the source module's proven
concrete empty-roundtrip vector ([lemma_utf8_string_empty_roundtrip]) and
check the transparent helpers ([utf8_scan_chars]/[utf8_string_dec]/
[utf8_string_enc]) — never the codec's opaque [.dec]/.roundtrip fields
(fstar-proofs §15/§18/§54 Trap 2).

The full roundtrip (empty + non-empty, general suffix) is proven in the
source module via [lemma_utf8_string_roundtrip].

Zero admits.

@header Data.Text.Codec.Test.UTF8String
*)
module Data.Text.Codec.Test.UTF8String


open Data.Text.Codec.UTF8String
open Data.Text.Codec.UTF8
open FStar.Seq
open FStar.Char
open FStar.UInt8


module U8 = FStar.UInt8


(** U+00E9 (LATIN SMALL LETTER E WITH ACUTE) — a non-ASCII NameStartChar;
    its UTF-8 encoding is [0xC3uy; 0xA9uy]. *)
let e_acute : FStar.Char.char = FStar.Char.char_of_int 0xE9


(** The UTF-8 encoding of [e_acute] is the two bytes [0xC3; 0xA9]. *)
let lemma_e_acute_encoding () : Lemma
  (ensures char_to_utf8 e_acute == [0xC3uy; 0xA9uy])
  = ()


(** A single non-ASCII char scans back to itself (the head-char roundtrip). *)
let lemma_e_acute_scan () : Lemma
  (ensures utf8_scan_chars 1 (char_to_utf8 e_acute) == ([e_acute], []))
  = lemma_utf8_scan_terminate 1 [e_acute] []


(** The concrete empty-string roundtrip: the empty string roundtrips against
    an empty suffix.  Re-states the source lemma (fstar-proofs §54 Trap 3). *)
let test_utf8_string_empty_roundtrip () : Lemma
  (requires utf8_string_wfcv 8 "" /\ utf8_string_rest_cond 8 "" Seq.empty)
  (ensures utf8_string_dec 8 (utf8_string_enc "" `Seq.append` Seq.empty) == Inr ("", 0))
  = lemma_utf8_string_empty_roundtrip 8


(** The non-ASCII char [é] encoded then decoded via the transparent helpers
    recovers [é] (CHAR-count 1, byte-count 2). *)
let test_utf8_string_nonascii_roundtrip () : Lemma
  (requires
    utf8_string_wfcv 8 (FStar.String.string_of_list [e_acute]) /\
    utf8_string_rest_cond 8 (FStar.String.string_of_list [e_acute]) Seq.empty)
  (ensures
    utf8_string_dec 8
      (utf8_string_enc (FStar.String.string_of_list [e_acute]) `Seq.append` Seq.empty)
      == Inr (FStar.String.string_of_list [e_acute],
              Seq.length (utf8_string_enc (FStar.String.string_of_list [e_acute]))))
  = lemma_utf8_string_roundtrip 8 (FStar.String.string_of_list [e_acute]) Seq.empty
