(* Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later *)


(**
Data.Text.Codec.Test.Zero — compliance tests for the [text_chars0] combinator.

Concrete tests for the zero-or-more ASCII text combinator in
[Data.Text.Codec.Zero], covering the empty string — the one behavior that
distinguishes it from [text_chars].  The tests re-state the source module's
proven concrete empty-roundtrip vector ([lemma_text_chars0_empty_roundtrip])
as public bindings, so the Integration module can mechanically enforce
coverage (CODE_GUIDELINES §Integration test pattern).

The full roundtrip (empty and non-empty) is proven in the source module via
[lemma_text_chars0_roundtrip]; the codec's opaque [.dec]/.roundtrip fields
(§15/§18) are NOT re-derived here.

Zero admits.

@header Data.Text.Codec.Test.Zero
*)
module Data.Text.Codec.Test.Zero


open Data.Text.Codec.Zero
open FStar.Seq
open FStar.Char


(** Test predicate: any ASCII letter. *)
let is_letter (c: FStar.Char.char) : bool =
  let v = FStar.Char.int_of_char c in
  (0x41 <= v && v <= 0x5A) || (0x61 <= v && v <= 0x7A)


(** The empty string is well-formed for [text_chars0] (the [wfcv] guard does
    not require non-emptiness).  Stated against the concrete empty vector's
    precondition — proven by the source [lemma_text_chars0_empty_roundtrip]. *)
let test_zero_empty_roundtrip () : Lemma
  (requires
    text_chars0_wfcv 8 is_letter "" /\
    text_chars0_rest_cond 8 is_letter "" Seq.empty)
  (ensures text_chars0_dec 8 is_letter (text_chars0_enc is_letter "" `Seq.append` Seq.empty)
           == Inr ("", 0))
  = lemma_text_chars0_empty_roundtrip 8 is_letter
