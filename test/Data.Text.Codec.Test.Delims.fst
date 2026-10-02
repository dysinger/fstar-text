(* Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later *)

(**
Data.Text.Codec.Test.Delims — Delimiter codec compliance tests.

Concrete tests for the CRLF and SP delimiter codecs in
[Data.Text.Codec.Delims].  These are compliance assertions, not production
proof infrastructure — they live in [test/] (fstar-proofs §28).

Zero admits.

@header Data.Text.Codec.Test.Delims
*)
module Data.Text.Codec.Test.Delims

open Data.Text.Codec.Delims
open Data.Codec
open FStar.Seq

(** [crlf] encodes to exactly 2 bytes (0x0D 0x0A), per RFC 7230 §3. *)
let test_crlf_two_bytes () : Lemma
  (ensures Seq.length (crlf.enc ()) == 2)
  = ()

(** [crlf] decodes its own encoding back to [()]. *)
let test_crlf_roundtrip () : Lemma
  (ensures crlf.dec (crlf.enc () `Seq.append` Seq.empty) == Inr ((), 2))
  = crlf.roundtrip () Seq.empty

(** [sp] encodes to exactly 1 byte (0x20), per RFC 7230 §3. *)
let test_sp_one_byte () : Lemma
  (ensures Seq.length (sp.enc ()) == 1)
  = ()

(** [sp] decodes its own encoding back to [()]. *)
let test_sp_roundtrip () : Lemma
  (ensures sp.dec (sp.enc () `Seq.append` Seq.empty) == Inr ((), 1))
  = sp.roundtrip () Seq.empty

(** [crlf] rejects a bare carriage return (missing line feed). *)
let test_crlf_rejects_bare_cr () : Lemma
  (ensures Inl? (crlf.dec (Seq.create 1 0x0Duy)))
  = ()

(** [crlf] rejects a bare line feed (missing carriage return). *)
let test_crlf_rejects_bare_lf () : Lemma
  (ensures Inl? (crlf.dec (Seq.create 1 0x0Auy)))
  = ()
