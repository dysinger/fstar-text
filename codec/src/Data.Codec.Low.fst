(**
Data.Codec.Low — C-extractable codec layer via KaRaMeL.

Non-recursive leaf codecs (8 types) operating on [LowStar.Buffer.buffer].
Each encode/decode function has a full byte-level post-condition —
no weak "modifies-only" specs.  Every function proves correspondence
with the pure codec in [Data.Codec.Types].

@header Data.Codec.Low

@section Types
- [codec_t] — flat GADT: CT_Token, CT_ByteVal, CT_Uint8, CT_Word16BE,
  CT_Word32BE, CT_Word16LE, CT_Word32LE, CT_Varint
- [error_code_c] — C-compatible error codes
- [decode_result_c] — C-compatible decode result

@section Encode functions
Eight leaf encoders, each with a Stack type and byte-level post-condition.
Dispatch via [encode_bytes].

@section Decode functions
Eight leaf decoders, each with a Stack type and result correspondence.
Dispatch via [decode_bytes].  [varint_decode_expected] is the pure spec
for [decode_varint]; the ensures clause equates the two.

@section Roundtrip lemmas
Per-codec lemmas ([lemma_low_roundtrip_*]) prove encode → decode
preserves values through the buffer.  [lemma_low_encode_decode_match]
is the dispatch-level master lemma.

@section KaRaMeL compliance
- No GADT type parameters
- No recursive constructors
- No function-typed constructor arguments
- No [U32.v] in extracted code bodies
- Custom sum types for results

CT_Satisfy excluded: function-typed constructor breaks KaRaMeL extraction.
CT_Bytes, CT_Text excluded: use Stack bridge (Decode.fst/Encode.fst).
*)
module Data.Codec.Low

open FStar.Seq
open FStar.Seq.Properties
open FStar.UInt8
open FStar.UInt32

open FStar.HyperStack
open FStar.HyperStack.ST
open LowStar.Buffer

open Data.Codec.Types

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module LB = LowStar.Buffer
module HS = FStar.HyperStack

(** Common arithmetic lemma *)

(** lemma_pow2_32: single canonical assert_norm for pow2 32 = 2^32. *)
(** Factored from 5 call sites; call once to avoid SMT duplication. *)
let lemma_pow2_32 () : Lemma (pow2 32 == 4294967296) = assert_norm (pow2 32 == 4294967296)

(** Buffer framing lemmas *)

let lemma_buffer_length_bound (b: LB.buffer byte) : Lemma
  (ensures LB.length b < 4294967296)
  = lemma_pow2_32 ()

(** Lemma: off < off+len implies len > 0 in U32 arithmetic. *)
let lemma_decode_guard_implies_len_pos (i n: U32.t) : Lemma
  (requires U32.v i + U32.v n < 4294967296 /\ U32.lt i (U32.add i n))
  (ensures U32.v n > 0)
  = lemma_pow2_32 ();
    FStar.Math.Lemmas.small_mod (U32.v i + U32.v n) (pow2 32);
    assert (U32.v (U32.add i n) == U32.v i + U32.v n);
    ()

(** lemma_lte_add2_implies_len_ge_2. *)
let lemma_lte_add2_implies_len_ge_2 (i n: U32.t) : Lemma
  (requires U32.v i + 2 < 4294967296 /\ U32.v i + U32.v n < 4294967296 /\
            U32.lte (U32.add i 2ul) (U32.add i n))
  (ensures U32.v n >= 2)
  = lemma_pow2_32 ();
    FStar.Math.Lemmas.small_mod (U32.v i + 2) (pow2 32);
    FStar.Math.Lemmas.small_mod (U32.v i + U32.v n) (pow2 32);
    assert (U32.v (U32.add i 2ul) == U32.v i + 2);
    assert (U32.v (U32.add i n) == U32.v i + U32.v n);
    ()

(** lemma_lte_add4_implies_len_ge_4. *)
let lemma_lte_add4_implies_len_ge_4 (i n: U32.t) : Lemma
  (requires U32.v i + 4 < 4294967296 /\ U32.v i + U32.v n < 4294967296 /\
            U32.lte (U32.add i 4ul) (U32.add i n))
  (ensures U32.v n >= 4)
  = lemma_pow2_32 ();
    FStar.Math.Lemmas.small_mod (U32.v i + 4) (pow2 32);
    FStar.Math.Lemmas.small_mod (U32.v i + U32.v n) (pow2 32);
    assert (U32.v (U32.add i 4ul) == U32.v i + 4);
    assert (U32.v (U32.add i n) == U32.v i + U32.v n);
    ()

(** lemma_u32_add_no_overflow. *)
let lemma_u32_add_no_overflow (x y: U32.t) : Lemma
  (requires U32.v x + U32.v y < 4294967296)
  (ensures U32.v (U32.add x y) == U32.v x + U32.v y)
  = lemma_pow2_32 ();
    FStar.Math.Lemmas.small_mod (U32.v x + U32.v y) (pow2 32)

(** varint_encode_pred: canonical predicate describing varint-encoded bytes. *)
(** Single source of truth for all 4 varint encoding locations: *)
(** encode_varint ensures, encode_bytes ensures CT_Varint, *)
(** lemma_encode_varint_matches_pure, lemma_encode_varint_eq_buffer. *)
(** Outer `if` guards Seq.index bounds; inner 5-range if describes bytes. *)
let varint_encode_pred (n: nat) (s: Seq.seq U8.t) (i: nat) : prop =
  if i + nbytes_of_varint n <= Seq.length s then
    (if n < 128 then
      U8.v (Seq.index s i) == n
    else if n < 16384 then
      U8.v (Seq.index s i) == n % 128 + 128 /\
      U8.v (Seq.index s (i + 1)) == n / 128
    else if n < 2097152 then
      U8.v (Seq.index s i) == n % 128 + 128 /\
      U8.v (Seq.index s (i + 1)) == (n / 128) % 128 + 128 /\
      U8.v (Seq.index s (i + 2)) == n / 16384
    else if n < 268435456 then
      U8.v (Seq.index s i) == n % 128 + 128 /\
      U8.v (Seq.index s (i + 1)) == (n / 128) % 128 + 128 /\
      U8.v (Seq.index s (i + 2)) == (n / 16384) % 128 + 128 /\
      U8.v (Seq.index s (i + 3)) == n / 2097152
    else
      U8.v (Seq.index s i) == n % 128 + 128 /\
      U8.v (Seq.index s (i + 1)) == (n / 128) % 128 + 128 /\
      U8.v (Seq.index s (i + 2)) == (n / 16384) % 128 + 128 /\
      U8.v (Seq.index s (i + 3)) == (n / 2097152) % 128 + 128 /\
      U8.v (Seq.index s (i + 4)) == n / 268435456)
  else False

(** lemma_word32_shift_bytes: connects shift_right byte extraction to arithmetic *)
(** division.  For v: U32.t, the byte extracted by shift_right matches the pure *)
(** word32 combinators' division-based extraction. *)
(**  *)
(** Proof: SMT already knows U32.v (v >> k) == U32.v v / pow2 k axiomatically. *)
(** For the 24-bit case, lemma_div_lt_nat proves v/16777216 < 256 (since *)
(** v < 2^32 = 256*16777216), then small_mod proves % 256 is identity. *)
(** The 16-bit and 8-bit cases are trivial: both sides are identical *)
(** (the same % 256 expression) after SMT reduces the shift. *)
(** Called from encode_word32be/encode_word32le bodies to structurally connect *)
(** shift-based body to division-based pure spec. *)
#push-options "--z3rlimit 40"
let lemma_word32_shift_bytes (v: U32.t) : Lemma
  (U32.v (U32.shift_right v 24ul) % 256 == U32.v v / 16777216 /\
   U32.v (U32.shift_right v 16ul) % 256 == (U32.v v / 65536) % 256 /\
   U32.v (U32.shift_right v 8ul) % 256 == (U32.v v / 256) % 256)
  = (* SMT axiomatically knows U32.v (v >> k) == U32.v v / pow2 k.
       24-bit: since v < 2^32, U32.v (v>>24) < 256, so % 256 is identity.
       16-bit: U32.v (v>>16) == U32.v v / 65536; % 256 on both sides identical.
       8-bit:  U32.v (v>>8)  == U32.v v / 256;    % 256 on both sides identical.
       Each shift is asserted explicitly — not left to SMT alone. *)
    (* 24-bit *)
    assert (U32.v (U32.shift_right v 24ul) < 256);
    assert (U32.v v / 16777216 < 256);
    (* 16-bit *)
    assert (U32.v (U32.shift_right v 16ul) == U32.v v / 65536);
    (* 8-bit *)
    assert (U32.v (U32.shift_right v 8ul) == U32.v v / 256);
    ()
#pop-options

(** Types *)

(** Flat codec tag — 8 leaf types extractable to C.

    CT_Satisfy excluded: function-typed constructor breaks extraction.
    CT_Bytes, CT_Text excluded: use Stack bridge. *)
type codec_t =
  | CT_Token      (** Any single byte *)
  | CT_ByteVal of U8.t  (** Specific b byte *)
  | CT_Uint8      (** Unsigned 8-bit integer *)
  | CT_Word16BE   (** Big-endian 16-bit integer *)
  | CT_Word32BE   (** Big-endian 32-bit integer *)
  | CT_Word16LE   (** Little-endian 16-bit integer *)
  | CT_Word32LE   (** Little-endian 32-bit integer *)
  | CT_Varint     (** Variable-length integer *)

(** C-compatible error codes. *)
type error_code_c =
  | EC_UnexpectedEndOfInput
  | EC_ExpectedByte of U8.t
  | EC_Overflow

(** C-compatible decode error. *)
type decode_error_c = { code: error_code_c; pos: U32.t }

(** C-compatible successful decode result. *)
type decode_result_ok = { n: U32.t; value: U32.t }

(** C-compatible decode result: either error or success. *)
type decode_result_c =
  | DR_Inl of decode_error_c
  | DR_Inr of decode_result_ok

(** Encode functions — each with full byte-level post-condition *)

#push-options "--z3rlimit 80"

(** Encode a single byte token into a buffer at offset. Returns 1ul. *)
let encode_token (v: U32.t) (b: LB.buffer U8.t) (i: U32.t)
  : Stack U32.t
    (requires fun h0 ->
      LB.live h0 b /\
      U32.v i + 1 <= LB.length b /\
      U32.v v < 256)
    (ensures fun h0 w h1 ->
      w = 1ul /\
      Seq.slice (LB.as_seq h1 b) (U32.v i) (U32.v i + 1)
        `Seq.equal` token.enc (U8.uint_to_t (U32.v v)) /\
      modifies (LB.loc_buffer b) h0 h1)
  = LB.upd b i (U8.uint_to_t (U32.v v));
    1ul

(** Encode an expected byte value into a buffer. Returns 1ul. *)
let encode_byteval (x: U8.t) (b: LB.buffer U8.t) (i: U32.t)
  : Stack U32.t
    (requires fun h0 ->
      LB.live h0 b /\
      U32.v i + 1 <= LB.length b)
    (ensures fun h0 w h1 ->
      w = 1ul /\
      Seq.slice (LB.as_seq h1 b) (U32.v i) (U32.v i + 1)
        `Seq.equal` (byte_val x).enc () /\
      modifies (LB.loc_buffer b) h0 h1)
  = LB.upd b i x;
    1ul

(** encode_uint8. *)
let encode_uint8 (v: U32.t) (b: LB.buffer U8.t) (i: U32.t)
  : Stack U32.t
    (requires fun h0 ->
      LB.live h0 b /\
      U32.v i + 1 <= LB.length b /\
      U32.v v < 256)
    (ensures fun h0 w h1 ->
      w = 1ul /\
      Seq.slice (LB.as_seq h1 b) (U32.v i) (U32.v i + 1)
        `Seq.equal` uint8.enc (U32.v v) /\
      modifies (LB.loc_buffer b) h0 h1)
  = LB.upd b i (U8.uint_to_t (U32.v v));
    1ul

(** encode_word16be. *)
let encode_word16be (v: U32.t) (b: LB.buffer U8.t) (i: U32.t)
  : Stack U32.t
    (requires fun h0 ->
      LB.live h0 b /\
      U32.v i + 2 <= LB.length b /\
      U32.v v < 65536)
    (ensures fun h0 w h1 ->
      w = 2ul /\
      Seq.slice (LB.as_seq h1 b) (U32.v i) (U32.v i + 2)
        `Seq.equal` word16be.enc (U32.v v) /\
      modifies (LB.loc_buffer b) h0 h1)
  = LB.upd b i (U8.uint_to_t (U32.v v / 256));
    LB.upd b (U32.add i 1ul) (U8.uint_to_t (U32.v v % 256));
    2ul

(** encode_word32be. *)
let encode_word32be (v: U32.t) (b: LB.buffer U8.t) (i: U32.t)
  : Stack U32.t
    (requires fun h0 ->
      LB.live h0 b /\
      U32.v i + 4 <= LB.length b)
    (ensures fun h0 w h1 ->
      w = 4ul /\
      Seq.slice (LB.as_seq h1 b) (U32.v i) (U32.v i + 4)
        `Seq.equal` word32be.enc (U32.v v) /\
      modifies (LB.loc_buffer b) h0 h1)
  = let b0 = U8.uint_to_t (U32.v (U32.shift_right v 24ul) % 256) in
    let b1 = U8.uint_to_t (U32.v (U32.shift_right v 16ul) % 256) in
    let b2 = U8.uint_to_t (U32.v (U32.shift_right v 8ul) % 256) in
    let b3 = U8.uint_to_t (U32.v v % 256) in
    (* Bridge shift-based byte extraction to division-based pure spec *)
    lemma_word32_shift_bytes v;
    LB.upd b i b0;
    LB.upd b (U32.add i 1ul) b1;
    LB.upd b (U32.add i 2ul) b2;
    LB.upd b (U32.add i 3ul) b3;
    4ul

(** encode_word16le. *)
let encode_word16le (v: U32.t) (b: LB.buffer U8.t) (i: U32.t)
  : Stack U32.t
    (requires fun h0 ->
      LB.live h0 b /\
      U32.v i + 2 <= LB.length b /\
      U32.v v < 65536)
    (ensures fun h0 w h1 ->
      w = 2ul /\
      Seq.slice (LB.as_seq h1 b) (U32.v i) (U32.v i + 2)
        `Seq.equal` word16le.enc (U32.v v) /\
      modifies (LB.loc_buffer b) h0 h1)
  = LB.upd b i (U8.uint_to_t (U32.v v % 256));
    LB.upd b (U32.add i 1ul) (U8.uint_to_t (U32.v v / 256));
    2ul

(** encode_word32le. *)
let encode_word32le (v: U32.t) (b: LB.buffer U8.t) (i: U32.t)
  : Stack U32.t
    (requires fun h0 ->
      LB.live h0 b /\
      U32.v i + 4 <= LB.length b)
    (ensures fun h0 w h1 ->
      w = 4ul /\
      Seq.slice (LB.as_seq h1 b) (U32.v i) (U32.v i + 4)
        `Seq.equal` word32le.enc (U32.v v) /\
      modifies (LB.loc_buffer b) h0 h1)
  = let b0 = U8.uint_to_t (U32.v v % 256) in
    let b1 = U8.uint_to_t (U32.v (U32.shift_right v 8ul) % 256) in
    let b2 = U8.uint_to_t (U32.v (U32.shift_right v 16ul) % 256) in
    let b3 = U8.uint_to_t (U32.v (U32.shift_right v 24ul) % 256) in
    (* Bridge shift-based byte extraction to division-based pure spec *)
    lemma_word32_shift_bytes v;
    LB.upd b i b0;
    LB.upd b (U32.add i 1ul) b1;
    LB.upd b (U32.add i 2ul) b2;
    LB.upd b (U32.add i 3ul) b3;
    4ul

(** encode_varint: full byte-level post-condition describing exact bytes written. *)
(**  *)
(** Precondition: U32.v i + 5 <= LB.length b. *)
(** This is conservative — a 5-byte buffer is required even for small values *)
(** (e.g., 0u encodes in 1 byte). The tradeoff avoids dynamic allocation: *)
(** callers provide a worst-case buffer, and the actual bytes written is *)
(** returned. For tighter per-call-site preconditions, use the per-range *)
(** encode functions directly. *)
let encode_varint (v: U32.t) (b: LB.buffer U8.t) (i: U32.t)
  : Stack U32.t
    (requires fun h0 ->
      LB.live h0 b /\
      U32.v i + 5 <= LB.length b)
    (ensures fun h0 w h1 ->
      modifies (LB.loc_buffer b) h0 h1 /\
      (let n = U32.v v in
       let nbytes = nbytes_of_varint n in
       U32.v w == nbytes /\
       varint_encode_pred n (LB.as_seq h1 b) (U32.v i)))
    (* per-byte spec: see varint_encode_pred at line ~96 *)
  = let n = v in
    if U32.lt n 128ul then
      (LB.upd b i (U8.uint_to_t (U32.v n)); 1ul)
    else if U32.lt n 16384ul then
      (LB.upd b i (U8.uint_to_t (U32.v n % 128 + 128));
       LB.upd b (U32.add i 1ul) (U8.uint_to_t (U32.v n / 128));
       2ul)
    else if U32.lt n 2097152ul then
      (LB.upd b i (U8.uint_to_t (U32.v n % 128 + 128));
       LB.upd b (U32.add i 1ul) (U8.uint_to_t ((U32.v n / 128) % 128 + 128));
       LB.upd b (U32.add i 2ul) (U8.uint_to_t (U32.v n / 16384));
       3ul)
    else if U32.lt n 268435456ul then
      (LB.upd b i (U8.uint_to_t (U32.v n % 128 + 128));
       LB.upd b (U32.add i 1ul) (U8.uint_to_t ((U32.v n / 128) % 128 + 128));
       LB.upd b (U32.add i 2ul) (U8.uint_to_t ((U32.v n / 16384) % 128 + 128));
       LB.upd b (U32.add i 3ul) (U8.uint_to_t (U32.v n / 2097152));
       4ul)
    else
      (LB.upd b i (U8.uint_to_t (U32.v n % 128 + 128));
       LB.upd b (U32.add i 1ul) (U8.uint_to_t ((U32.v n / 128) % 128 + 128));
       LB.upd b (U32.add i 2ul) (U8.uint_to_t ((U32.v n / 16384) % 128 + 128));
       LB.upd b (U32.add i 3ul) (U8.uint_to_t ((U32.v n / 2097152) % 128 + 128));
       LB.upd b (U32.add i 4ul) (U8.uint_to_t (U32.v n / 268435456));
       5ul)

(** Decode functions — each with full result-level post-condition *)

let decode_token (b: LB.buffer U8.t) (i: U32.t) (n: U32.t)
  : Stack decode_result_c
    (requires fun h0 ->
      LB.live h0 b /\
      U32.v i + U32.v n <= LB.length b)
    (ensures fun h0 result h1 ->
      h0 == h1 /\
      (let input_slice = Seq.slice (LB.as_seq h0 b) (U32.v i) (U32.v i + U32.v n) in
       match result, token.dec input_slice with
       | DR_Inr r, Inr (dec_val, _) -> r.n = 1ul /\ U32.v r.value == U8.v dec_val
       | DR_Inl _, Inl _ -> True
       | _, _ -> False))
  = if U32.lt i (U32.add i n) then
      let _ = lemma_decode_guard_implies_len_pos i n in
      let b = LB.index b i in
      DR_Inr ({n=1ul; value=U32.uint_to_t (U8.v b)})
    else
      DR_Inl ({code=EC_UnexpectedEndOfInput; pos=i})

(** Decode an expected byte value from a buffer. Returns DR_Inr on match. *)
let decode_byteval (x: U8.t) (b: LB.buffer U8.t) (i: U32.t) (n: U32.t)
  : Stack decode_result_c
    (requires fun h0 ->
      LB.live h0 b /\
      U32.v i + U32.v n <= LB.length b)
    (ensures fun h0 result h1 ->
      h0 == h1 /\
      (let input_slice = Seq.slice (LB.as_seq h0 b) (U32.v i) (U32.v i + U32.v n) in
       match result, (byte_val x).dec input_slice with
       | DR_Inr r, Inr ((), _) -> r.n = 1ul /\ r.value == 0ul
       | DR_Inl _, Inl _ -> True
       | _, _ -> False))
  = if U32.lt i (U32.add i n) then
      let _ = lemma_decode_guard_implies_len_pos i n in
      let b = LB.index b i in
      if U8.eq b x then DR_Inr ({n=1ul; value=0ul})
      else DR_Inl ({code=EC_ExpectedByte b; pos=i})
    else
      DR_Inl ({code=EC_UnexpectedEndOfInput; pos=i})

(** decode_uint8. *)
let decode_uint8 (b: LB.buffer U8.t) (i: U32.t) (n: U32.t)
  : Stack decode_result_c
    (requires fun h0 ->
      LB.live h0 b /\
      U32.v i + U32.v n <= LB.length b)
    (ensures fun h0 result h1 ->
      h0 == h1 /\
      (let input_slice = Seq.slice (LB.as_seq h0 b) (U32.v i) (U32.v i + U32.v n) in
       match result, uint8.dec input_slice with
       | DR_Inr r, Inr (dec_val, _) -> r.n = 1ul /\ U32.v r.value = dec_val
       | DR_Inl _, Inl _ -> True
       | _, _ -> False))
  = if U32.lt i (U32.add i n) then
      let _ = lemma_decode_guard_implies_len_pos i n in
      let b = LB.index b i in
      DR_Inr ({n=1ul; value=U32.uint_to_t (U8.v b)})
    else
      DR_Inl ({code=EC_UnexpectedEndOfInput; pos=i})

(** decode_word16be. *)
let decode_word16be (b: LB.buffer U8.t) (i: U32.t) (n: U32.t)
  : Stack decode_result_c
    (requires fun h0 ->
      LB.live h0 b /\
      U32.v i + U32.v n <= LB.length b /\
      U32.v i + 2 <= LB.length b)
    (ensures fun h0 result h1 ->
      h0 == h1 /\
      (let input_slice = Seq.slice (LB.as_seq h0 b) (U32.v i) (U32.v i + U32.v n) in
       match result, word16be.dec input_slice with
       | DR_Inr r, Inr (dec_val, _) -> r.n = 2ul /\ U32.v r.value = dec_val
       | DR_Inl _, Inl _ -> True
       | _, _ -> False))
  = if U32.lte (U32.add i 2ul) (U32.add i n) then
      let _ = lemma_lte_add2_implies_len_ge_2 i n in
      let hi = LB.index b i in
      let lo = LB.index b (U32.add i 1ul) in
      DR_Inr ({n=2ul; value=U32.add (U32.mul (U32.uint_to_t (U8.v hi)) 256ul) (U32.uint_to_t (U8.v lo))})
    else
      DR_Inl ({code=EC_UnexpectedEndOfInput; pos=i})

(** decode_word32be. *)
let decode_word32be (b: LB.buffer U8.t) (i: U32.t) (n: U32.t)
  : Stack decode_result_c
    (requires fun h0 ->
      LB.live h0 b /\
      U32.v i + U32.v n <= LB.length b /\
      U32.v i + 4 <= LB.length b)
    (ensures fun h0 result h1 ->
      h0 == h1 /\
      (let input_slice = Seq.slice (LB.as_seq h0 b) (U32.v i) (U32.v i + U32.v n) in
       match result, word32be.dec input_slice with
       | DR_Inr r, Inr (dec_val, _) -> r.n = 4ul /\ U32.v r.value = dec_val
       | DR_Inl _, Inl _ -> True
       | _, _ -> False))
  = if U32.lte (U32.add i 4ul) (U32.add i n) then
      let _ = lemma_lte_add4_implies_len_ge_4 i n in
      let b0 = LB.index b i in
      let b1 = LB.index b (U32.add i 1ul) in
      let b2 = LB.index b (U32.add i 2ul) in
      let b3 = LB.index b (U32.add i 3ul) in
      let value = U32.add (U32.add (U32.add
        (U32.mul (U32.uint_to_t (U8.v b0)) 16777216ul)
        (U32.mul (U32.uint_to_t (U8.v b1)) 65536ul))
        (U32.mul (U32.uint_to_t (U8.v b2)) 256ul))
        (U32.uint_to_t (U8.v b3)) in
      DR_Inr ({n=4ul; value=value})
    else
      DR_Inl ({code=EC_UnexpectedEndOfInput; pos=i})

(** decode_word16le. *)
let decode_word16le (b: LB.buffer U8.t) (i: U32.t) (n: U32.t)
  : Stack decode_result_c
    (requires fun h0 ->
      LB.live h0 b /\
      U32.v i + U32.v n <= LB.length b /\
      U32.v i + 2 <= LB.length b)
    (ensures fun h0 result h1 ->
      h0 == h1 /\
      (let input_slice = Seq.slice (LB.as_seq h0 b) (U32.v i) (U32.v i + U32.v n) in
       match result, word16le.dec input_slice with
       | DR_Inr r, Inr (dec_val, _) -> r.n = 2ul /\ U32.v r.value = dec_val
       | DR_Inl _, Inl _ -> True
       | _, _ -> False))
  = if U32.lte (U32.add i 2ul) (U32.add i n) then
      let _ = lemma_lte_add2_implies_len_ge_2 i n in
      let lo = LB.index b i in
      let hi = LB.index b (U32.add i 1ul) in
      DR_Inr ({n=2ul; value=U32.add (U32.uint_to_t (U8.v lo)) (U32.mul (U32.uint_to_t (U8.v hi)) 256ul)})
    else
      DR_Inl ({code=EC_UnexpectedEndOfInput; pos=i})

(** decode_word32le. *)
let decode_word32le (b: LB.buffer U8.t) (i: U32.t) (n: U32.t)
  : Stack decode_result_c
    (requires fun h0 ->
      LB.live h0 b /\
      U32.v i + U32.v n <= LB.length b /\
      U32.v i + 4 <= LB.length b)
    (ensures fun h0 result h1 ->
      h0 == h1 /\
      (let input_slice = Seq.slice (LB.as_seq h0 b) (U32.v i) (U32.v i + U32.v n) in
       match result, word32le.dec input_slice with
       | DR_Inr r, Inr (dec_val, _) -> r.n = 4ul /\ U32.v r.value = dec_val
       | DR_Inl _, Inl _ -> True
       | _, _ -> False))
  = if U32.lte (U32.add i 4ul) (U32.add i n) then
      let _ = lemma_lte_add4_implies_len_ge_4 i n in
      let b0 = LB.index b i in
      let b1 = LB.index b (U32.add i 1ul) in
      let b2 = LB.index b (U32.add i 2ul) in
      let b3 = LB.index b (U32.add i 3ul) in
      let value = U32.add (U32.add (U32.add
        (U32.uint_to_t (U8.v b0))
        (U32.mul (U32.uint_to_t (U8.v b1)) 256ul))
        (U32.mul (U32.uint_to_t (U8.v b2)) 65536ul))
        (U32.mul (U32.uint_to_t (U8.v b3)) 16777216ul) in
      DR_Inr ({n=4ul; value=value})
    else
      DR_Inl ({code=EC_UnexpectedEndOfInput; pos=i})

(** varint_decode_expected: pure spec for decode_varint. *)
(** WARNING: keep in sync with decode_varint body (line ~590).  Any logic change *)
(** MUST update both.  The ensures clause of decode_varint equates result to *)
(** varint_decode_expected; divergence causes verification failure. *)
#push-options "--z3rlimit 20"
let varint_decode_expected (s: Seq.seq U8.t) (i: U32.t) (n: U32.t)
  : Pure decode_result_c
    (requires U32.v i + U32.v n <= Seq.length s)
    (ensures fun _ -> True)
  =
  if U32.lt n 1ul then
    DR_Inl ({code=EC_UnexpectedEndOfInput; pos=i})
  else
    let b0 = Seq.index s (U32.v i) in
    let v0 = U32.uint_to_t (U8.v b0 % 128) in
    if U8.v b0 < 128 then
      DR_Inr ({n=1ul; value=v0})
    else if U32.lt n 2ul then
      DR_Inl ({code=EC_UnexpectedEndOfInput; pos=i})
    else
      let b1 = Seq.index s (U32.v i + 1) in
      let v1 = U32.add v0 (U32.mul (U32.uint_to_t (U8.v b1 % 128)) 128ul) in
      if U8.v b1 < 128 then
        DR_Inr ({n=2ul; value=v1})
      else if U32.lt n 3ul then
        DR_Inl ({code=EC_UnexpectedEndOfInput; pos=i})
      else
        let b2 = Seq.index s (U32.v i + 2) in
        let v2 = U32.add v1 (U32.mul (U32.uint_to_t (U8.v b2 % 128)) 16384ul) in
        if U8.v b2 < 128 then
          DR_Inr ({n=3ul; value=v2})
        else if U32.lt n 4ul then
          DR_Inl ({code=EC_UnexpectedEndOfInput; pos=i})
        else
          let b3 = Seq.index s (U32.v i + 3) in
          let v3 = U32.add v2 (U32.mul (U32.uint_to_t (U8.v b3 % 128)) 2097152ul) in
          if U8.v b3 < 128 then
            DR_Inr ({n=4ul; value=v3})
          else if U32.lt n 5ul then
            DR_Inl ({code=EC_UnexpectedEndOfInput; pos=i})
          else
            let b4 = Seq.index s (U32.v i + 4) in
            let b4_val = U8.v b4 % 128 in
            if b4_val > 15 then
              DR_Inl ({code=EC_Overflow; pos=i})
            else
              let v4 = U32.add v3 (U32.mul (U32.uint_to_t b4_val) 268435456ul) in
              DR_Inr ({n=5ul; value=v4})
#pop-options

(** lemma_encode_varint_matches_pure: the bytes written by encode_varint match *)
(** the pure varint.enc (U32.v v).  This bridges the division-based Low* encoder *)
(** to the recursive pure spec varint_encode_go.  Proved by case analysis on the *)
(** 5 encoding ranges, reusing the arithmetic lemmas from Types.fst. *)
#push-options "--z3rlimit 80"
let lemma_encode_varint_matches_pure (v: U32.t) : Lemma
  (let n = U32.v v in
   Seq.length (varint.enc n) == nbytes_of_varint n /\
   varint_encode_pred n (varint.enc n) 0)
  = varint.roundtrip (U32.v v) Seq.empty;
    lemma_nbytes_of_varint_correct (U32.v v);
    let n = U32.v v in
    if n < 128 then ()
    else if n < 16384 then ( lemma_varint_2byte_arithmetic n )
    else if n < 2097152 then ( lemma_varint_3byte_arithmetic n )
    else if n < 268435456 then ( lemma_varint_4byte_arithmetic n )
    else ( lemma_varint_5byte_arithmetic n )
#pop-options

(** lemma_decode_varint_roundtrip: varint_decode_expected correctly decodes *)
(** bytes produced by varint.enc.  Bridges the gap between the Low* varint *)
(** decoder spec (varint_decode_expected) and the pure varint codec *)
(** (varint.dec).  Proved by 5-range case analysis using the arithmetic *)
(** lemmas from Types.fst.  Called from lemma_low_roundtrip_varint to make *)
(** the proof structural instead of SMT-brute-force. *)
#push-options "--z3rlimit 80"
let lemma_decode_varint_roundtrip (v: U32.t) : Lemma
  (let enc = varint.enc (U32.v v) in
   let enc_len = u32_of_nat (Seq.length enc) in
   varint_decode_expected enc 0ul enc_len
   == DR_Inr ({n=enc_len; value=v}))
  = let n = U32.v v in
    lemma_encode_varint_matches_pure v;
    lemma_nbytes_of_varint_correct n;
    lemma_pow2_32 ();
    if n < 128 then begin
      lemma_varint_enc_dec_1byte n Seq.empty;
      ()
    end else if n < 16384 then begin
      lemma_varint_enc_dec_2byte n Seq.empty;
      lemma_varint_2byte_arithmetic n;
      ()
    end else if n < 2097152 then begin
      lemma_varint_enc_dec_3byte n Seq.empty;
      lemma_varint_3byte_arithmetic n;
      ()
    end else if n < 268435456 then begin
      lemma_varint_enc_dec_4byte n Seq.empty;
      lemma_varint_4byte_arithmetic n;
      ()
    end else begin
      lemma_varint_enc_dec_5byte n Seq.empty;
      lemma_varint_5byte_arithmetic n;
      ()
    end
#pop-options

(** Decode a variable-length integer from a buffer. Result equals varint_decode_expected. *)
let decode_varint (b: LB.buffer U8.t) (i: U32.t) (n: U32.t)
  : Stack decode_result_c
    (requires fun h0 ->
      LB.live h0 b /\
      U32.v i + U32.v n <= LB.length b /\
      U32.v i + 5 < 4294967296)
    (ensures fun h0 result h1 ->
      h0 == h1 /\
      result == varint_decode_expected (LB.as_seq h0 b) i n)
  = (* WARNING: Body duplicates varint_decode_expected (see line ~480).  Ghost/Stack
       barrier (LB.as_seq is GTot) forces this duplication — Error 53.  The ensures
       clause equates result to varint_decode_expected; any logic change MUST update
       both bodies.  Divergence is caught at verify time. *)
    if U32.lt n 1ul then
      DR_Inl ({code=EC_UnexpectedEndOfInput; pos=i})
    else
      let b0 = LB.index b i in
      let v0 = U32.uint_to_t (U8.v b0 % 128) in
      if U8.v b0 < 128 then
        DR_Inr ({n=1ul; value=v0})
      else if U32.lt n 2ul then
        DR_Inl ({code=EC_UnexpectedEndOfInput; pos=i})
      else
        let b1 = LB.index b (U32.add i 1ul) in
        let v1 = U32.add v0 (U32.mul (U32.uint_to_t (U8.v b1 % 128)) 128ul) in
        if U8.v b1 < 128 then
          DR_Inr ({n=2ul; value=v1})
        else if U32.lt n 3ul then
          DR_Inl ({code=EC_UnexpectedEndOfInput; pos=i})
        else
          let b2 = LB.index b (U32.add i 2ul) in
          let v2 = U32.add v1 (U32.mul (U32.uint_to_t (U8.v b2 % 128)) 16384ul) in
          if U8.v b2 < 128 then
            DR_Inr ({n=3ul; value=v2})
          else if U32.lt n 4ul then
            DR_Inl ({code=EC_UnexpectedEndOfInput; pos=i})
          else
            let b3 = LB.index b (U32.add i 3ul) in
            let v3 = U32.add v2 (U32.mul (U32.uint_to_t (U8.v b3 % 128)) 2097152ul) in
            if U8.v b3 < 128 then
              DR_Inr ({n=4ul; value=v3})
            else if U32.lt n 5ul then
              DR_Inl ({code=EC_UnexpectedEndOfInput; pos=i})
            else
              let b4 = LB.index b (U32.add i 4ul) in
              let b4_val = U8.v b4 % 128 in
              if b4_val > 15 then
                DR_Inl ({code=EC_Overflow; pos=i})
              else
                let v4 = U32.add v3 (U32.mul (U32.uint_to_t b4_val) 268435456ul) in
                DR_Inr ({n=5ul; value=v4})

#pop-options  (* close the push at line 135; all encode/decode leaf functions are done *)

(** Dispatch functions — each with full per-constructor post-condition *)

#push-options "--z3rlimit 80"  (* dispatch functions need elevated rlimit for large post-conditions *)

(** encode_bytes: dispatch on codec_t with full per-constructor byte spec. *)
let encode_bytes (c: codec_t) (v: U32.t) (b: LB.buffer U8.t) (i: U32.t)
  : Stack U32.t
    (requires fun h0 ->
      LB.live h0 b /\
      (match c with
       | CT_Token | CT_Uint8 -> U32.v i + 1 <= LB.length b /\ U32.v v < 256
       | CT_ByteVal _ -> U32.v i + 1 <= LB.length b
       | CT_Word16BE | CT_Word16LE -> U32.v i + 2 <= LB.length b /\ U32.v v < 65536
       | CT_Word32BE | CT_Word32LE -> U32.v i + 4 <= LB.length b
       | CT_Varint -> U32.v i + 5 <= LB.length b))
    (ensures fun h0 w h1 ->
      modifies (LB.loc_buffer b) h0 h1 /\
      (match c with
       | CT_Token ->
           w == 1ul /\
           Seq.slice (LB.as_seq h1 b) (U32.v i) (U32.v i + 1)
             `Seq.equal` token.enc (U8.uint_to_t (U32.v v))
       | CT_Uint8 ->
           w == 1ul /\
           Seq.slice (LB.as_seq h1 b) (U32.v i) (U32.v i + 1)
             `Seq.equal` uint8.enc (U32.v v)
       | CT_ByteVal expected_byte ->
           w == 1ul /\
           Seq.slice (LB.as_seq h1 b) (U32.v i) (U32.v i + 1)
             `Seq.equal` (byte_val expected_byte).enc ()
       | CT_Word16BE ->
           w == 2ul /\
           Seq.slice (LB.as_seq h1 b) (U32.v i) (U32.v i + 2)
             `Seq.equal` word16be.enc (U32.v v)
       | CT_Word32BE ->
           w == 4ul /\
           Seq.slice (LB.as_seq h1 b) (U32.v i) (U32.v i + 4)
             `Seq.equal` word32be.enc (U32.v v)
       | CT_Word16LE ->
           w == 2ul /\
           Seq.slice (LB.as_seq h1 b) (U32.v i) (U32.v i + 2)
             `Seq.equal` word16le.enc (U32.v v)
       | CT_Word32LE ->
           w == 4ul /\
           Seq.slice (LB.as_seq h1 b) (U32.v i) (U32.v i + 4)
             `Seq.equal` word32le.enc (U32.v v)
       | CT_Varint ->
           (let n = U32.v v in
            let nbytes = nbytes_of_varint n in
            U32.v w == nbytes /\
            varint_encode_pred n (LB.as_seq h1 b) (U32.v i))))
  = match c with
  | CT_Token -> encode_token v b i
  | CT_ByteVal expected_byte -> encode_byteval expected_byte b i
  | CT_Uint8 -> encode_uint8 v b i
  | CT_Word16BE -> encode_word16be v b i
  | CT_Word32BE -> encode_word32be v b i
  | CT_Word16LE -> encode_word16le v b i
  | CT_Word32LE -> encode_word32le v b i
  | CT_Varint -> encode_varint v b i

(** decode_bytes: dispatch on codec_t with full per-constructor result spec. *)
let decode_bytes (c: codec_t) (b: LB.buffer U8.t) (i: U32.t) (n: U32.t)
  : Stack decode_result_c
    (requires fun h0 ->
      LB.live h0 b /\
      U32.v i + U32.v n <= LB.length b /\
      (match c with
       | CT_Token | CT_ByteVal _ | CT_Uint8 -> True
       | CT_Word16BE | CT_Word16LE -> U32.v i + 2 <= LB.length b
       | CT_Word32BE | CT_Word32LE -> U32.v i + 4 <= LB.length b
       | CT_Varint -> U32.v i + 5 <= LB.length b))
    (ensures fun h0 result h1 ->
      h0 == h1 /\
      (let input_slice = Seq.slice (LB.as_seq h0 b) (U32.v i) (U32.v i + U32.v n) in
       match c with
       | CT_Token ->
           (match result, token.dec input_slice with
            | DR_Inr r, Inr (dec_val, _) -> r.n = 1ul /\ U32.v r.value == U8.v dec_val
            | DR_Inl _, Inl _ -> True
            | _, _ -> False)
       | CT_ByteVal expected_byte ->
           (match result, (byte_val expected_byte).dec input_slice with
            | DR_Inr r, Inr ((), _) -> r.n = 1ul /\ r.value == 0ul
            | DR_Inl _, Inl _ -> True
            | _, _ -> False)
       | CT_Uint8 ->
           (match result, uint8.dec input_slice with
            | DR_Inr r, Inr (dec_val, _) -> r.n = 1ul /\ U32.v r.value = dec_val
            | DR_Inl _, Inl _ -> True
            | _, _ -> False)
       | CT_Word16BE ->
           (match result, word16be.dec input_slice with
            | DR_Inr r, Inr (dec_val, _) -> r.n = 2ul /\ U32.v r.value = dec_val
            | DR_Inl _, Inl _ -> True
            | _, _ -> False)
       | CT_Word32BE ->
           (match result, word32be.dec input_slice with
            | DR_Inr r, Inr (dec_val, _) -> r.n = 4ul /\ U32.v r.value = dec_val
            | DR_Inl _, Inl _ -> True
            | _, _ -> False)
       | CT_Word16LE ->
           (match result, word16le.dec input_slice with
            | DR_Inr r, Inr (dec_val, _) -> r.n = 2ul /\ U32.v r.value = dec_val
            | DR_Inl _, Inl _ -> True
            | _, _ -> False)
       | CT_Word32LE ->
           (match result, word32le.dec input_slice with
            | DR_Inr r, Inr (dec_val, _) -> r.n = 4ul /\ U32.v r.value = dec_val
            | DR_Inl _, Inl _ -> True
            | _, _ -> False)
       | CT_Varint -> result == varint_decode_expected (LB.as_seq h0 b) i n))
  = match c with
  | CT_Token -> decode_token b i n
  | CT_ByteVal expected_byte -> decode_byteval expected_byte b i n
  | CT_Uint8 -> decode_uint8 b i n
  | CT_Word16BE -> decode_word16be b i n
  | CT_Word32BE -> decode_word32be b i n
  | CT_Word16LE -> decode_word16le b i n
  | CT_Word32LE -> decode_word32le b i n
  | CT_Varint -> decode_varint b i n

#pop-options  (* close dispatch push at line 664 *)

(** Slice-to-index bridge *)

let lemma_byteval_index_from_slice (buf: LB.buffer U8.t) (i: U32.t) (expected_byte: U8.t) (h: HS.mem) : Lemma
  (requires
    U32.v i + 1 <= LB.length buf /\
    Seq.equal (Seq.slice (LB.as_seq h buf) (U32.v i) (U32.v i + 1))
              (Seq.create 1 expected_byte))
  (ensures
    Seq.index (LB.as_seq h buf) (U32.v i) == expected_byte)
  = Seq.lemma_eq_elim (Seq.slice (LB.as_seq h buf) (U32.v i) (U32.v i + 1))
                      (Seq.create 1 expected_byte);
    Seq.lemma_index_slice (LB.as_seq h buf) (U32.v i) (U32.v i + 1) 0

(** Value-preserving roundtrip lemmas *)

#push-options "--z3rlimit 40"
let lemma_low_roundtrip_token (v: U32.t) (b: LB.buffer U8.t) (i n: U32.t)
  : Stack (U32.t & decode_result_c)
    (requires fun h0 ->
      LB.live h0 b /\
      U32.v v < 256 /\
      U32.v i + 1 <= LB.length b /\
      U32.v i + 1 <= U32.v i + U32.v n /\
      U32.v i + U32.v n <= LB.length b)
    (ensures fun h0 (n, result) h1 ->
      modifies (LB.loc_buffer b) h0 h1 /\
      result == DR_Inr ({n=n; value=v}))
  = lemma_buffer_length_bound b;
    lemma_u32_add_no_overflow i n;
    lemma_u32_add_no_overflow i 1ul;
    let n = encode_token v b i in
    token.roundtrip (U8.uint_to_t (U32.v v)) Seq.empty;
    let result = decode_token b i n in
    (n, result)
#pop-options

#push-options "--z3rlimit 40"
let lemma_low_roundtrip_byteval (expected_byte: U8.t) (buf: LB.buffer U8.t) (i n: U32.t)
  : Stack (U32.t & decode_result_c)
    (requires fun h0 ->
      LB.live h0 buf /\
      U32.v i + 1 <= LB.length buf /\
      U32.v i + 1 <= U32.v i + U32.v n /\
      U32.v i + U32.v n <= LB.length buf)
    (ensures fun h0 (n, result) h1 ->
      modifies (LB.loc_buffer buf) h0 h1 /\
      result == DR_Inr ({n=n; value=0ul}))
  = lemma_buffer_length_bound buf;
    lemma_u32_add_no_overflow i n;
    lemma_u32_add_no_overflow i 1ul;
    let n = encode_byteval expected_byte buf i in
    (* h_mid: heap state immediately after encode_byteval.  Must be captured
       before any buffer-modifying operation — inserting writes here would
       break the proof by capturing the wrong heap state. *)
    let h_mid = FStar.HyperStack.ST.get () in
    lemma_byteval_index_from_slice buf i expected_byte h_mid;
    (byte_val expected_byte).roundtrip () Seq.empty;
    let result = decode_byteval expected_byte buf i n in
    (n, result)
#pop-options

#push-options "--z3rlimit 40"
let lemma_low_roundtrip_uint8 (v: U32.t) (b: LB.buffer U8.t) (i n: U32.t)
  : Stack (U32.t & decode_result_c)
    (requires fun h0 ->
      LB.live h0 b /\
      U32.v v < 256 /\
      U32.v i + 1 <= LB.length b /\
      U32.v i + 1 <= U32.v i + U32.v n /\
      U32.v i + U32.v n <= LB.length b)
    (ensures fun h0 (n, result) h1 ->
      modifies (LB.loc_buffer b) h0 h1 /\
      result == DR_Inr ({n=n; value=v}))
  = lemma_buffer_length_bound b;
    lemma_u32_add_no_overflow i n;
    lemma_u32_add_no_overflow i 1ul;
    let n = encode_uint8 v b i in
    uint8.roundtrip (U32.v v) Seq.empty;
    let result = decode_uint8 b i n in
    (n, result)
#pop-options

#push-options "--z3rlimit 40"
let lemma_low_roundtrip_word16be (v: U32.t) (b: LB.buffer U8.t) (i n: U32.t)
  : Stack (U32.t & decode_result_c)
    (requires fun h0 ->
      LB.live h0 b /\
      U32.v v < 65536 /\
      U32.v i + 2 <= LB.length b /\
      U32.v i + 2 <= U32.v i + U32.v n /\
      U32.v i + U32.v n <= LB.length b)
    (ensures fun h0 (n, result) h1 ->
      modifies (LB.loc_buffer b) h0 h1 /\
      result == DR_Inr ({n=n; value=v}))
  = lemma_buffer_length_bound b;
    lemma_u32_add_no_overflow i n;
    lemma_u32_add_no_overflow i 2ul;
    let n = encode_word16be v b i in
    word16be.roundtrip (U32.v v) Seq.empty;
    let result = decode_word16be b i n in
    (n, result)
#pop-options

#push-options "--z3rlimit 40"
let lemma_low_roundtrip_word32be (v: U32.t) (b: LB.buffer U8.t) (i n: U32.t)
  : Stack (U32.t & decode_result_c)
    (requires fun h0 ->
      LB.live h0 b /\
      U32.v i + 4 <= LB.length b /\
      U32.v i + 4 <= U32.v i + U32.v n /\
      U32.v i + U32.v n <= LB.length b)
    (ensures fun h0 (n, result) h1 ->
      modifies (LB.loc_buffer b) h0 h1 /\
      result == DR_Inr ({n=n; value=v}))
  = lemma_buffer_length_bound b;
    lemma_u32_add_no_overflow i n;
    lemma_u32_add_no_overflow i 4ul;
    let n = encode_word32be v b i in
    (* encode_word32be post-condition: buffer slice == word32be.enc (U32.v v).
       word32be.roundtrip proves pure roundtrip; no shift lemma needed here —
       Seq.equal in encode_word32be post-condition bridges buffer to pure spec. *)
    word32be.roundtrip (U32.v v) Seq.empty;
    let result = decode_word32be b i n in
    (n, result)
#pop-options

#push-options "--z3rlimit 40"
let lemma_low_roundtrip_word16le (v: U32.t) (b: LB.buffer U8.t) (i n: U32.t)
  : Stack (U32.t & decode_result_c)
    (requires fun h0 ->
      LB.live h0 b /\
      U32.v v < 65536 /\
      U32.v i + 2 <= LB.length b /\
      U32.v i + 2 <= U32.v i + U32.v n /\
      U32.v i + U32.v n <= LB.length b)
    (ensures fun h0 (n, result) h1 ->
      modifies (LB.loc_buffer b) h0 h1 /\
      result == DR_Inr ({n=n; value=v}))
  = lemma_buffer_length_bound b;
    lemma_u32_add_no_overflow i n;
    lemma_u32_add_no_overflow i 2ul;
    let n = encode_word16le v b i in
    word16le.roundtrip (U32.v v) Seq.empty;
    let result = decode_word16le b i n in
    (n, result)
#pop-options

#push-options "--z3rlimit 40"
let lemma_low_roundtrip_word32le (v: U32.t) (b: LB.buffer U8.t) (i n: U32.t)
  : Stack (U32.t & decode_result_c)
    (requires fun h0 ->
      LB.live h0 b /\
      U32.v i + 4 <= LB.length b /\
      U32.v i + 4 <= U32.v i + U32.v n /\
      U32.v i + U32.v n <= LB.length b)
    (ensures fun h0 (n, result) h1 ->
      modifies (LB.loc_buffer b) h0 h1 /\
      result == DR_Inr ({n=n; value=v}))
  = lemma_buffer_length_bound b;
    lemma_u32_add_no_overflow i n;
    lemma_u32_add_no_overflow i 4ul;
    let n = encode_word32le v b i in
    (* encode_word32le post-condition: buffer slice == word32le.enc (U32.v v).
       word32le.roundtrip proves pure roundtrip; no shift lemma needed here —
       Seq.equal in encode_word32le post-condition bridges buffer to pure spec. *)
    word32le.roundtrip (U32.v v) Seq.empty;
    let result = decode_word32le b i n in
    (n, result)
#pop-options

(** lemma_encode_varint_eq_buffer: after encode_varint writes to b, the buffer *)
(** slice at [i, i+nbytes) equals the pure varint.enc.  This structurally *)
(** bridges the Low* encoder to the pure spec by combining the encode_varint *)
(** post-condition (per-byte buffer facts) with lemma_encode_varint_matches_pure *)
(** (per-byte pure facts).  The 5-range case analysis matches encode_varint's *)
(** post-condition exactly; call this from lemma_low_roundtrip_varint after encode. *)
#push-options "--z3rlimit 40"
let lemma_encode_varint_eq_buffer (v: U32.t) (b: LB.buffer U8.t) (i: U32.t) (h: HS.mem) : Lemma
  (requires
    LB.live h b /\
    U32.v i + 5 <= LB.length b /\
    varint_encode_pred (U32.v v) (LB.as_seq h b) (U32.v i))
  (ensures
    Seq.slice (LB.as_seq h b) (U32.v i) (U32.v i + nbytes_of_varint (U32.v v))
      `Seq.equal` varint.enc (U32.v v))
  = let n = U32.v v in
    let nbytes = nbytes_of_varint n in
    lemma_encode_varint_matches_pure v;
    lemma_nbytes_of_varint_correct n;
    (* Requires gives varint_encode_pred n (LB.as_seq h b) (U32.v i).
       lemma_encode_varint_matches_pure gives varint_encode_pred n (varint.enc n) 0.
       Both describe identical per-byte patterns via varint_encode_pred.
       Seq.lemma_eq_intro + SMT bridges buffer to pure enc. *)
    Seq.lemma_eq_intro
      (Seq.slice (LB.as_seq h b) (U32.v i) (U32.v i + nbytes))
      (varint.enc n)
#pop-options

(** lemma_low_roundtrip_varint: composes encode_varint + varint.roundtrip + decode_varint. *)
(** Four-step structural proof chain (no SMT brute force): *)
(** 1. encode_varint writes buffer bytes; h_mid captures post-encode heap *)
(** 2. lemma_encode_varint_eq_buffer → buffer slice == varint.enc n *)
(** 3. lemma_decode_varint_roundtrip → varint_decode_expected on varint.enc n *)
(** returns DR_Inr ({n=len_enc; value=v}) *)
(** 4. decode_varint result == varint_decode_expected on buffer *)
(** = varint_decode_expected on varint.enc n (substituting step 2) *)
(** = DR_Inr ({...; value=v}) (by step 3) *)
(** Note: varint.roundtrip is NOT directly called here but IS transitively *)
(** needed (lemma_decode_varint_roundtrip → lemma_encode_varint_matches_pure *)
(** → varint.roundtrip). *)
#push-options "--z3rlimit 40"
let lemma_low_roundtrip_varint (v: U32.t) (b: LB.buffer U8.t) (i n: U32.t)
  : Stack (U32.t & decode_result_c)
    (requires fun h0 ->
      LB.live h0 b /\
      U32.v i + 5 <= LB.length b /\
      U32.v i + 5 <= U32.v i + U32.v n /\
      U32.v i + U32.v n <= LB.length b)
    (ensures fun h0 (n, result) h1 ->
      modifies (LB.loc_buffer b) h0 h1 /\
      result == DR_Inr ({n=n; value=v}))
  = lemma_buffer_length_bound b;
    lemma_u32_add_no_overflow i n;
    let n = encode_varint v b i in
    (* h_mid: heap state immediately after encode_varint, before any other
       buffer-modifying operation.  encode_varint's post-condition guarantees
       modifies (LB.loc_buffer b) h0 h_mid where h0 is the initial heap
       from the Stack precondition.  This capture must be the first operation
       after encode_varint — inserting buffer modifications here would break
       the proof chain by capturing the wrong heap state. *)    
    let h_mid = FStar.HyperStack.ST.get () in
    (* Step 1-2: buffer bytes match varint.enc n *)
    lemma_encode_varint_eq_buffer v b i h_mid;
    (* Step 3: varint_decode_expected on varint.enc n returns the correct value *)
    lemma_decode_varint_roundtrip v;
    (* Step 4: decode_varint result == varint_decode_expected on buffer
       == varint_decode_expected on varint.enc n == DR_Inr ({...; value=v}) *)
    let result = decode_varint b i n in
    (n, result)
#pop-options

#push-options "--z3rlimit 40"
let lemma_low_encode_decode_match (c: codec_t) (v: U32.t) (b: LB.buffer U8.t) (i n: U32.t)
  : Stack (U32.t & decode_result_c)
    (requires fun h0 ->
      LB.live h0 b /\
      (match c with
       | CT_Token | CT_Uint8 ->
           U32.v v < 256 /\
           U32.v i + 1 <= LB.length b /\
           U32.v i + 1 <= U32.v i + U32.v n
       | CT_ByteVal _ ->
           U32.v i + 1 <= LB.length b /\
           U32.v i + 1 <= U32.v i + U32.v n
       | CT_Word16BE | CT_Word16LE ->
           U32.v v < 65536 /\
           U32.v i + 2 <= LB.length b /\
           U32.v i + 2 <= U32.v i + U32.v n
       | CT_Word32BE | CT_Word32LE ->
           U32.v i + 4 <= LB.length b /\
           U32.v i + 4 <= U32.v i + U32.v n
       | CT_Varint ->
           U32.v i + 5 <= LB.length b /\
           U32.v i + 5 <= U32.v i + U32.v n) /\
      U32.v i + U32.v n <= LB.length b)
    (ensures fun h0 (n, result) h1 ->
      modifies (LB.loc_buffer b) h0 h1 /\
      (match c with
       | CT_ByteVal _ -> result == DR_Inr ({n=n; value=0ul})
       | _ -> result == DR_Inr ({n=n; value=v})))
  = match c with
    | CT_Token -> lemma_low_roundtrip_token v b i n
    | CT_ByteVal expected_byte -> lemma_low_roundtrip_byteval expected_byte b i n
    | CT_Uint8 -> lemma_low_roundtrip_uint8 v b i n
    | CT_Word16BE -> lemma_low_roundtrip_word16be v b i n
    | CT_Word32BE -> lemma_low_roundtrip_word32be v b i n
    | CT_Word16LE -> lemma_low_roundtrip_word16le v b i n
    | CT_Word32LE -> lemma_low_roundtrip_word32le v b i n
    | CT_Varint -> lemma_low_roundtrip_varint v b i n

#pop-options
