(* Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later *)

(**
Data.Text.Codec.Pulse — C-extractable text-encoding tag codec via Pulse + Custard.

The Custard-era replacement for the retired KaRaMeL
[Data.Text.Codec.Low] (which used [LowStar.Buffer]/[Stack]; both namespaces
were removed from F* ≥ v2026.09.20).  A single-byte tag selects the text
encoding of a subsequent run — [TE_ASCII] (0x00), [TE_UTF8] (0x01), or
[TE_UTF16] (0x02) — written/read through a [Pulse.Lib.Array.array].

Each encode/decode `fn` carries a byte-level post-condition tied to the pure
spec [tag_of]/[tag_to_type] (both `noextract`; the tag→type mapping is the
single source of truth shared with the pure [Data.Text.Codec] layer).

Written for F* v2026.09.20 (Custard `--custard_backend C`).  Zero admits.

@header Data.Text.Codec.Pulse

@section Types
- [text_enc] — TE_ASCII, TE_UTF8, TE_UTF16
- [opt_text_enc] — C-friendly decode result (no [option])

@section Tag bytes
- [tag_ascii] / [tag_utf8] / [tag_utf16] — the three tag byte constants

@section Specs
- [tag_of] — text_enc → tag byte
- [tag_to_type] — tag byte → text_enc option

@section Encode
- [encode] — write [tag_of t] at [off], returns 1ul

@section Decode
- [decode] — read the tag at [off] into [opt_text_enc]

@section Roundtrip lemmas
- [lemma_roundtrip] — pure [tag_of] ∘ [tag_to_type] roundtrip
- [lemma_pulse_roundtrip] — buffer-level encode→decode roundtrip
- [lemma_pulse_encode_decode_match] — master roundtrip across every tag
*)
module Data.Text.Codec.Pulse
#lang-pulse

open Pulse
open Pulse.Lib.Reference
module A = Pulse.Lib.Array
module US = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Seq = FStar.Seq

open FStar.Seq

(* ── Types (alphabetical) ──────────────────────────────────────────── *)

(** [text_enc] — the text encodings the tag byte selects. *)
type text_enc =
  | TE_ASCII
  | TE_UTF8
  | TE_UTF16

(** [opt_text_enc] — option wrapper for the decode result (C-friendly, no
    [option]). *)
type opt_text_enc =
  | OTE_None
  | OTE_Some of (text_enc & U32.t)

(* ── Tag bytes — single source of truth (fstar-proofs §33) ──────────── *)

(** [tag_ascii] — the ASCII tag byte (0x00). *)
let tag_ascii : U8.t = 0x00uy

(** [tag_utf8] — the UTF-8 tag byte (0x01). *)
let tag_utf8 : U8.t = 0x01uy

(** [tag_utf16] — the UTF-16 tag byte (0x02). *)
let tag_utf16 : U8.t = 0x02uy

(* ── Pure spec (noextract: not C-representable) ─────────────────────── *)

(** [tag_of t] — pure spec: [text_enc] → tag byte. *)
noextract
let tag_of (t: text_enc) : U8.t =
  match t with
  | TE_ASCII -> tag_ascii
  | TE_UTF8 -> tag_utf8
  | TE_UTF16 -> tag_utf16

(** [tag_to_type b] — pure spec: tag byte → [text_enc] option.

    Returns [option text_enc] (not [opt_text_enc]) — [tag_to_type] is the
    PURE spec and is never extracted; only [decode] uses the C-friendly
    [opt_text_enc] wrapper. *)
noextract
let tag_to_type (b: U8.t) : option text_enc =
  if U8.eq b tag_ascii then Some TE_ASCII
  else if U8.eq b tag_utf8 then Some TE_UTF8
  else if U8.eq b tag_utf16 then Some TE_UTF16
  else None

(* ── Encode ─────────────────────────────────────────────────────────── *)

(** [encode t buf off] — encode a text tag into [buf] at [off]; returns 1
    (bytes written).

    @param t The text encoding to write.
    @param buf The destination buffer (must hold at least 1 byte at [off]).
    @param off The write offset.
    @returns The number of bytes written (always [1ul]).
    The byte written equals [tag_of t]. *)
fn encode (t: text_enc) (buf: A.array U8.t) (off: U32.t)
    (#s0: erased (Seq.seq U8.t))
    requires
      A.pts_to buf s0 **
      pure (U32.v off + 1 <= A.length buf)
    returns w: U32.t
    ensures
      (exists* (s1: Seq.seq U8.t).
        A.pts_to buf s1 **
        pure (U32.v off + 1 <= A.length buf /\
              Seq.length s1 == A.length buf /\
              Seq.index s1 (U32.v off) == tag_of t)) **
      pure (w == 1ul)
{
  let j = US.uint32_to_sizet off;
  A.pts_to_len buf;
  buf.(j) <- tag_of t;
  1ul
}

(* ── Decode ─────────────────────────────────────────────────────────── *)

(** [decode buf off] — decode a text tag from [buf] at [off].

    @param buf The source buffer (must hold at least 1 byte at [off]).
    @param off The read offset.
    @returns [OTE_Some (t, 1ul)] when the byte is a known tag, else
             [OTE_None]. *)
fn decode (buf: A.array U8.t) (off: U32.t)
    (#s0: erased (Seq.seq U8.t))
    requires
      A.pts_to buf s0 **
      pure (U32.v off + 1 <= A.length buf)
    returns r: opt_text_enc
    ensures
      A.pts_to buf s0 **
      pure (
        A.length buf == Seq.length s0 /\
        U32.v off + 1 <= A.length buf /\
        (let b = Seq.index s0 (U32.v off) in
         match r, tag_to_type b with
         | OTE_Some (t, n), Some t' -> n == 1ul /\ t == t'
         | OTE_None, None -> True
         | _, _ -> False))
{
  A.pts_to_len buf;
  let j = US.uint32_to_sizet off;
  let tag = buf.(j);
  if U8.eq tag tag_ascii {
    OTE_Some (TE_ASCII, 1ul)
  } else if U8.eq tag tag_utf8 {
    OTE_Some (TE_UTF8, 1ul)
  } else if U8.eq tag tag_utf16 {
    OTE_Some (TE_UTF16, 1ul)
  } else {
    OTE_None
  }
}

(* ── Roundtrip lemmas (alphabetical) ────────────────────────────────── *)

(** [lemma_roundtrip t] — pure roundtrip: encoding then decoding returns the
    original value. *)
let lemma_roundtrip (t: text_enc) : Lemma (tag_to_type (tag_of t) == Some t) =
  match t with
  | TE_ASCII -> ()
  | TE_UTF8 -> ()
  | TE_UTF16 -> ()

(** [lemma_pulse_roundtrip t buf off] — encode then decode a tag roundtrips.

    @param t The text encoding to roundtrip.
    @param buf The buffer.
    @param off The offset.
    Proves [decode buf off] after [encode t buf off] returns
    [OTE_Some (t, 1ul)]. *)
fn lemma_pulse_roundtrip (t: text_enc) (buf: A.array U8.t) (off: U32.t)
    (#s0: erased (Seq.seq U8.t))
    requires
      A.pts_to buf s0 **
      pure (U32.v off + 1 <= A.length buf)
    returns res: (U32.t & opt_text_enc)
    ensures
      (exists* (s1: Seq.seq U8.t).
        A.pts_to buf s1) **
      pure (fst res == 1ul /\ snd res == OTE_Some (t, 1ul))
{
  let n = encode t buf off;
  let r = decode buf off;
  lemma_roundtrip t;
  (n, r)
}

(** [lemma_pulse_encode_decode_match t buf off] — master roundtrip across
    every tag.

    @param t The text encoding.
    @param buf The buffer.
    @param off The offset.
    Proves [decode]∘[encode] returns [OTE_Some (t, 1ul)] for all three tags. *)
fn lemma_pulse_encode_decode_match (t: text_enc) (buf: A.array U8.t) (off: U32.t)
    (#s0: erased (Seq.seq U8.t))
    requires
      A.pts_to buf s0 **
      pure (U32.v off + 1 <= A.length buf)
    returns res: (U32.t & opt_text_enc)
    ensures
      (exists* (s1: Seq.seq U8.t).
        A.pts_to buf s1) **
      pure (fst res == 1ul /\ snd res == OTE_Some (t, 1ul))
{
  match t {
    TE_ASCII -> { lemma_pulse_roundtrip TE_ASCII buf off }
    TE_UTF8 -> { lemma_pulse_roundtrip TE_UTF8 buf off }
    TE_UTF16 -> { lemma_pulse_roundtrip TE_UTF16 buf off }
  }
}
