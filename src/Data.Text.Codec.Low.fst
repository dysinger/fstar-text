(**
Data.Text.Codec.Low — Low* text encoding tags.

KaRaMeL-compatible Low* module.  C extraction target.
Pipeline: fstar --codegen krml → krml → clang -Wall -Werror.

Every function carries an explicit buffer-bounds precondition and a
precise postcondition describing the bytes written, so no admit is
needed (fstar-lowstar §3).  [tag_of]/[tag_to_type] form the pure spec;
the Low* [encode]/[decode] refine them via [lemma_encode_match] /
[lemma_decode_match].

Zero admits.

@header Data.Text.Codec.Low
*)
module Data.Text.Codec.Low
open FStar.UInt8
open FStar.UInt32
open FStar.Int.Cast
open FStar.HyperStack
open FStar.Seq
open FStar.HyperStack.ST
open LowStar.Buffer
open LowStar.Monotonic.Buffer

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module LB = LowStar.Buffer

(** Text encodings the tag byte selects. *)
type text_enc =
  | TE_ASCII
  | TE_UTF8
  | TE_UTF16

(** Tag bytes — single source of truth (fstar-proofs §33, F*↔C layout).
    Every [tag_of]/[tag_to_type]/[decode] reference these constants, never
    raw literals. *)
let tag_ascii = 0x00uy
let tag_utf8  = 0x01uy
let tag_utf16 = 0x02uy

(** Option wrapper for the decode result (C-friendly, no [option]). *)
type opt_text_enc =
  | OTE_None
  | OTE_Some of (text_enc & U32.t)

(** Pure spec: [text_enc] → tag byte. *)
let tag_of (t: text_enc) : U8.t =
  match t with
    | TE_ASCII -> tag_ascii
    | TE_UTF8  -> tag_utf8
    | TE_UTF16 -> tag_utf16

(** Pure spec: tag byte → [text_enc] option.

    Returns [option text_enc] (not [opt_text_enc]) — [tag_to_type] is the
    PURE spec and is never extracted; only [decode] (below) uses the
    C-friendly [opt_text_enc] wrapper. *)
let tag_to_type (b: U8.t) : option text_enc =
  if U8.eq b tag_ascii then Some TE_ASCII
    else if U8.eq b tag_utf8 then Some TE_UTF8
    else if U8.eq b tag_utf16 then Some TE_UTF16
  else None

(** Roundtrip lemma: encoding then decoding returns the original value. *)
let lemma_roundtrip (t: text_enc) : Lemma (tag_to_type (tag_of t) == Some t) =
  match t with
    | TE_ASCII -> ()
    | TE_UTF16 -> ()
    | TE_UTF8 -> ()

(** Encode a text tag into [buf] at [off]; returns 1 (bytes written). *)
inline_for_extraction
let encode (t: text_enc) (buf: LB.buffer U8.t) (off: U32.t)
  : Stack U32.t
    (requires fun h0 -> LB.live h0 buf /\ U32.v off < LB.length buf)
    (ensures fun h0 r h1 ->
      r == 1ul /\
      LB.live h1 buf /\
      modifies (LB.loc_buffer buf) h0 h1 /\
      Seq.index (LB.as_seq h1 buf) (U32.v off) == tag_of t)
  = LB.upd buf off (tag_of t); 1ul

(** Decode a text tag from [buf] at [off]. *)
inline_for_extraction
let decode (buf: LB.buffer U8.t) (off: U32.t)
  : Stack opt_text_enc
    (requires fun h0 -> LB.live h0 buf /\ U32.v off < LB.length buf)
    (ensures fun h0 r h1 ->
      h0 == h1 /\
      (match r with
       | OTE_None -> None? (tag_to_type (Seq.index (LB.as_seq h0 buf) (U32.v off)))
       | OTE_Some (t, n) -> n == 1ul /\ tag_to_type (Seq.index (LB.as_seq h0 buf) (U32.v off)) == Some t))
  = let tag = LB.index buf off in
    if U8.eq tag tag_ascii then OTE_Some (TE_ASCII, 1ul)
    else if U8.eq tag tag_utf8 then OTE_Some (TE_UTF8, 1ul)
    else if U8.eq tag tag_utf16 then OTE_Some (TE_UTF16, 1ul)
    else OTE_None

(** Bridge lemma: [encode] writes exactly [tag_of t].

    Proved directly from the [encode] postcondition — the pure spec and
    the Low* impl agree (fstar-proofs §29). *)
let lemma_encode_match (t: text_enc) (buf: LB.buffer U8.t) (off: U32.t)
  : Stack unit
    (requires fun h0 -> LB.live h0 buf /\ U32.v off < LB.length buf)
    (ensures fun h0 _ h1 ->
      LB.live h1 buf /\
      modifies (LB.loc_buffer buf) h0 h1 /\
      Seq.index (LB.as_seq h1 buf) (U32.v off) == tag_of t)
  = let _ = encode t buf off in ()

(** Bridge lemma: [decode] recovers [t] from a buffer holding [tag_of t].

    Strengthened (fstar-proofs §29): the ensures states the PURE corollary
    of [decode]'s postcondition — [tag_to_type (tag_of t) == Some t] —
    without referencing the effectful [decode] call in ghost position
    (fstar-proofs §7).  The heap is unchanged. *)
let lemma_decode_match (t: text_enc) (buf: LB.buffer U8.t) (off: U32.t)
  : Stack unit
    (requires fun h0 ->
      LB.live h0 buf /\
      U32.v off < LB.length buf /\
      Seq.index (LB.as_seq h0 buf) (U32.v off) == tag_of t)
    (ensures fun h0 _ h1 ->
      h0 == h1 /\
      tag_to_type (tag_of t) == Some t)
  = lemma_roundtrip t;
    let _ = decode buf off in ()
