(* Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later *)

(**
Data.Text.Codec.Test.Pulse — buffer-based roundtrip tests for the Pulse tag codec.

Pulse `fn` tests that call the [Data.Text.Codec.Pulse] roundtrip lemmas and
encode/decode through a [Pulse.Lib.Array.array], exercising the byte-buffer
code path.  Each test scopes its scratch buffer with the `let mut … = [| … |]`
array-literal form (the non-deprecated replacement for the retired
[A.alloc]/[A.free] / old Low* `alloca` + `push_frame`/`pop_frame`).

@header Data.Text.Codec.Test.Pulse
*)
module Data.Text.Codec.Test.Pulse
#lang-pulse

open Pulse
open Pulse.Lib.Reference
open Data.Text.Codec.Pulse
open FStar.UInt8
open FStar.UInt32

module A = Pulse.Lib.Array
module US = FStar.SizeT

(** Pulse roundtrip: ASCII tag encode→decode through an A.array buffer. *)
fn test_tag_ascii_roundtrip ()
    requires emp
    returns u: unit
    ensures emp
{
  let mut buf = [| 0uy; 2sz |];
  let (_, result) = lemma_pulse_roundtrip TE_ASCII buf 0ul;
  let Data.Text.Codec.Pulse.OTE_Some _ = result;
  ()
}

(** Pulse roundtrip: UTF-8 tag encode→decode through an A.array buffer. *)
fn test_tag_utf8_roundtrip ()
    requires emp
    returns u: unit
    ensures emp
{
  let mut buf = [| 0uy; 2sz |];
  let (_, result) = lemma_pulse_roundtrip TE_UTF8 buf 0ul;
  let Data.Text.Codec.Pulse.OTE_Some _ = result;
  ()
}

(** Pulse roundtrip: UTF-16 tag encode→decode through an A.array buffer. *)
fn test_tag_utf16_roundtrip ()
    requires emp
    returns u: unit
    ensures emp
{
  let mut buf = [| 0uy; 2sz |];
  let (_, result) = lemma_pulse_roundtrip TE_UTF16 buf 0ul;
  let Data.Text.Codec.Pulse.OTE_Some _ = result;
  ()
}

(** Pulse error test: decoding an unknown tag byte produces OTE_None. *)
fn test_tag_unknown ()
    requires emp
    returns u: unit
    ensures emp
{
  let mut buf = [| 0uy; 2sz |];
  let j0 = US.uint32_to_sizet 0ul;
  buf.(j0) <- 0xFFuy;
  let result = decode buf 0ul;
  let Data.Text.Codec.Pulse.OTE_None = result;
  ()
}

(** Pulse roundtrip through the master lemma: every tag roundtrips. *)
fn test_tag_master_roundtrip ()
    requires emp
    returns u: unit
    ensures emp
{
  let mut buf = [| 0uy; 2sz |];
  let (_, r_ascii) = lemma_pulse_encode_decode_match TE_ASCII buf 0ul;
  let Data.Text.Codec.Pulse.OTE_Some _ = r_ascii;
  let (_, r_utf8) = lemma_pulse_encode_decode_match TE_UTF8 buf 0ul;
  let Data.Text.Codec.Pulse.OTE_Some _ = r_utf8;
  let (_, r_utf16) = lemma_pulse_encode_decode_match TE_UTF16 buf 0ul;
  let Data.Text.Codec.Pulse.OTE_Some _ = r_utf16;
  ()
}
