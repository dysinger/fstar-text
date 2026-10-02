(* Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later *)


(**
Data.Text.Codec.Test.UTF8 — RFC 3629 UTF-8 compliance tests.

Concrete byte-vector tests for the [Data.Text.Codec.UTF8] decoder.  These
are compliance assertions, not production proof infrastructure — they are
in [test/], not [src/] (fstar-proofs §24, §28).

Each test is a [Lemma] whose ensures is a concrete equality on [utf8_decode_one].
The bodies are [()] because the values are fully concrete byte lists — SMT
normalizes [utf8_decode_one] directly (no induction, no opaque predicates).

Coverage:
- Overlong rejections: 2-byte [0xC0 0x81], 3-byte [0xE0 ..], 4-byte [0xF0 ..]
- Minimal-form acceptance: U+0800 ([0xE0 0xA0 0x80]), U+10000 ([0xF0 0x90 0x80 0x80])
- Surrogate rejection: U+D800 ([0xED 0xA0 0x80])
- U+D7FF F* boundary rejection (valid scalar, unrepresentable in FChar)
- Above-max rejection: [0xF4 0x90 0x80 0x80] (> U+10FFFF)
- Roundtrip for every 1-4 byte character class (via [lemma_utf8_roundtrip])

Zero admits.

@header Data.Text.Codec.Test.UTF8
*)
module Data.Text.Codec.Test.UTF8


open Data.Text.Codec.UTF8
open FStar.Char
open FStar.UInt8
open FStar.List.Tot


module U8 = FStar.UInt8


(** Overlong rejections *)


(** Reject the overlong 2-byte encoding of NUL ([0xC0 0x80]). *)
let test_overlong_2byte () : Lemma
  (ensures utf8_decode_one [0xC0uy; 0x80uy] = None)
  = ()


(** Reject the 2-byte overlong form [0xC1 0xBF] (overlong for U+007F). *)
let test_overlong_2byte_hi () : Lemma
  (ensures utf8_decode_one [0xC1uy; 0xBFuy] = None)
  = ()


(** Reject the overlong 3-byte encoding of NUL ([0xE0 0x80 0x80]). *)
let test_overlong_3byte () : Lemma
  (ensures utf8_decode_one [0xE0uy; 0x80uy; 0x80uy] = None)
  = ()


(** Reject the 3-byte overlong form [0xE0 0x9F 0xBF] (overlong for U+07FF). *)
let test_overlong_3byte_hi () : Lemma
  (ensures utf8_decode_one [0xE0uy; 0x9Fuy; 0xBFuy] = None)
  = ()


(** Reject the overlong 4-byte encoding of NUL ([0xF0 0x80 0x80 0x80]). *)
let test_overlong_4byte () : Lemma
  (ensures utf8_decode_one [0xF0uy; 0x80uy; 0x80uy; 0x80uy] = None)
  = ()


(** Reject the 4-byte overlong form [0xF0 0x8F 0xBF 0xBF] (overlong for U+FFFF). *)
let test_overlong_4byte_hi () : Lemma
  (ensures utf8_decode_one [0xF0uy; 0x8Fuy; 0xBFuy; 0xBFuy] = None)
  = ()


(** Minimal-form acceptance *)


(** Accept the minimal 3-byte form [0xE0 0xA0 0x80] (U+0800). *)
let test_minimal_3byte () : Lemma
  (ensures Some? (utf8_decode_one [0xE0uy; 0xA0uy; 0x80uy]))
  = ()


(** Accept a mid-range 3-byte form [0xE1 0x80 0x80] (U+1000). *)
let test_3byte_mid () : Lemma
  (ensures Some? (utf8_decode_one [0xE1uy; 0x80uy; 0x80uy]))
  = ()


(** Accept the minimal 4-byte form [0xF0 0x90 0x80 0x80] (U+10000). *)
let test_minimal_4byte () : Lemma
  (ensures Some? (utf8_decode_one [0xF0uy; 0x90uy; 0x80uy; 0x80uy]))
  = ()


(** Accept a mid-range 4-byte form [0xF1 0x80 0x80 0x80] (U+40000). *)
let test_4byte_mid () : Lemma
  (ensures Some? (utf8_decode_one [0xF1uy; 0x80uy; 0x80uy; 0x80uy]))
  = ()


(** Surrogate and boundary rejections *)


(** Reject the surrogate U+D800 ([0xED 0xA0 0x80]). *)
let test_surrogate_d800 () : Lemma
  (ensures utf8_decode_one [0xEDuy; 0xA0uy; 0x80uy] = None)
  = ()


(** Reject the surrogate U+DFFF ([0xED 0xBF 0xBF]). *)
let test_surrogate_dfff () : Lemma
  (ensures utf8_decode_one [0xEDuy; 0xBFuy; 0xBFuy] = None)
  = ()


(** Reject U+D7FF ([0xED 0x9F 0xBF]) — a valid RFC 3629 scalar that
    [FStar.Char.char] cannot represent (char_code < 0xd7ff).  This is an
    F* library limitation, documented in README.md, not an RFC violation. *)
let test_reject_d7ff () : Lemma
  (ensures utf8_decode_one [0xEDuy; 0x9Fuy; 0xBFuy] = None)
  = ()


(** Reject code points above U+10FFFF ([0xF4 0x90 0x80 0x80]). *)
let test_above_max () : Lemma
  (ensures utf8_decode_one [0xF4uy; 0x90uy; 0x80uy; 0x80uy] = None)
  = ()


(** Reject an out-of-range lead byte [0xF5 ...] (> 0xF4). *)
let test_lead_out_of_range () : Lemma
  (ensures utf8_decode_one [0xF5uy; 0x80uy; 0x80uy; 0x80uy] = None)
  = ()


(** Reject a lone continuation byte [0x80] (no lead byte). *)
let test_lone_continuation () : Lemma
  (ensures utf8_decode_one [0x80uy] = None)
  = ()


(** Reject a truncated 2-byte sequence [0xC2] (missing continuation). *)
let test_truncated_2byte () : Lemma
  (ensures utf8_decode_one [0xC2uy] = None)
  = ()


(** Reject empty input. *)
let test_empty () : Lemma
  (ensures utf8_decode_one [] = None)
  = ()


(** Reject a 3-byte lead followed by a non-continuation second byte. *)
let test_bad_continuation_3byte () : Lemma
  (ensures utf8_decode_one [0xE1uy; 0x20uy; 0x80uy] = None)
  = ()


(** Roundtrip vectors *)


(** ASCII roundtrip: U+0041 'A' encodes to [0x41] and decodes back. *)
let test_roundtrip_ascii () : Lemma
  (ensures utf8_decode_one (char_to_utf8 (FStar.Char.char_of_int 0x41))
           == Some (FStar.Char.char_of_int 0x41, []))
  = lemma_utf8_roundtrip (FStar.Char.char_of_int 0x41)


(** 2-byte roundtrip: U+00E9 'é' encodes to [0xC3 0xA9] and decodes back. *)
let test_roundtrip_2byte () : Lemma
  (ensures utf8_decode_one (char_to_utf8 (FStar.Char.char_of_int 0xE9))
           == Some (FStar.Char.char_of_int 0xE9, []))
  = lemma_utf8_roundtrip (FStar.Char.char_of_int 0xE9)


(** 3-byte roundtrip: U+20AC '€' encodes to 3 bytes and decodes back. *)
let test_roundtrip_3byte () : Lemma
  (ensures utf8_decode_one (char_to_utf8 (FStar.Char.char_of_int 0x20AC))
           == Some (FStar.Char.char_of_int 0x20AC, []))
  = lemma_utf8_roundtrip (FStar.Char.char_of_int 0x20AC)


(** 4-byte roundtrip: U+1F600 encodes to 4 bytes and decodes back. *)
let test_roundtrip_4byte () : Lemma
  (ensures utf8_decode_one (char_to_utf8 (FStar.Char.char_of_int 0x1F600))
           == Some (FStar.Char.char_of_int 0x1F600, []))
  = lemma_utf8_roundtrip (FStar.Char.char_of_int 0x1F600)


(** Every valid char roundtrips (exhaustive, via the production lemma). *)
let test_roundtrip_all () : Lemma
  (ensures (forall (c: FStar.Char.char).
             utf8_decode_one (char_to_utf8 c) == Some (c, [])))
  = FStar.Classical.forall_intro lemma_utf8_roundtrip


(** Head-char prefix bridge: every char's encoding, when followed by an
    arbitrary suffix [rest], decodes to [c] and returns [rest] unchanged.
    This is the §59 Fact-2 lemma that [Data.Text.Codec.UTF8String] needs
    for its char-run scan. *)
let test_decode_prefix_all () : Lemma
  (ensures (forall (c: FStar.Char.char) (rest: list byte).
             utf8_decode_one (char_to_utf8 c @ rest) == Some (c, rest)))
  = FStar.Classical.forall_intro_2
      #FStar.Char.char
      #(fun (_: FStar.Char.char) -> list byte)
      #(fun (c: FStar.Char.char) (rest: list byte) ->
           utf8_decode_one (char_to_utf8 c @ rest) == Some (c, rest))
      (fun c rest -> lemma_utf8_decode_prefix c rest)
