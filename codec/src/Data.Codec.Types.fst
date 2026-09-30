(**
Data.Codec.Types — Core types, record codec, helpers, lemmas, and combinators.

This module defines the bidirectional codec framework: a [codec a] is a
verified serializer/deserializer pair with roundtrip, error-bounds, and
n-bounds proofs.  All 21 combinators are standalone functions
returning codec records — no GADT, no n, no mutual recursion.

@header Data.Codec.Types

@section Types
- [codec a] — 8-field record: enc, dec, wfcv, wfcv_prop, rest_cond,
  roundtrip, dec_err_bound, dec_consumed_bound
- [error_code] — sum type of parse errors
- [decode_error] — error record with position and optional label
- [decode_result a] — either an error or a value + bytes consumed

@section Combinators (22 total)
Leaf: token, byte_val, satisfy, pure, text, bytes, uint8,
       word16be, word16le, word32be, word32le, varint, digits_to_int
Combinator: custom, product, sum, map_, count, label, alt, one_of, take_until

@section Lemmas
All lemmas are called explicitly in roundtrip proofs.  SMTPat is used
sparingly and only on pattern-matching decoders (bytes_decode,
lemma_seq_cons_append).

@section Proofs
Every combinator carries its own roundtrip, dec_err_bound, and
dec_consumed_bound proof.  Z3 rlimits are kept ≤ 80 via structural
decomposition.  Zero admits across all 22 combinators.  The [one_of] and
[take_until] roundtrips are proven per-instantiation (concrete literal /
delimiter sets) rather than as a generic [codec] field — see their NOTEs.
*)
module Data.Codec.Types

open FStar.Seq
open FStar.Seq.Properties
open FStar.UInt8
open FStar.UInt32
open FStar.List.Tot
open FStar.Mul
open FStar.Math.Lemmas

module Seq = FStar.Seq
module U8 = FStar.UInt8
module U32 = FStar.UInt32

(** Core Types *)

(** A byte is a [UInt8.t]. *)
type byte = U8.t

(** A sequence of bytes. *)
type byte_seq = Seq.seq byte

(** Error codes returned by decoders. *)
type error_code =
  | UnexpectedEndOfInput    (** General: ran out of bytes while parsing. *)
  | ExpectedByte of byte    (** Expected a specific byte, got something else. *)
  | ExpectedPredicate       (** A byte failed a predicate check (e.g., is_digit, satisfy). *)
  | ExpectedEndOfInput      (** Expected exactly N bytes, got fewer.
                                Used by [text] combinator for fixed-string matching.
                                Distinct from [UnexpectedEndOfInput] which is general. *)
  | ExpectedText            (** Text literal mismatch in [text] combinator. *)
  | ExpectedSumTag           (** Sum tag byte not 0x00 or 0x01. *)

(** A decode error with code, position, and optional label. *)
type decode_error = { err_code: error_code; err_pos: nat; label: option string }

(** Construct a [decode_error] with no label.
    Use this instead of record literal to ensure [label = None] by default. *)
(** Construct a decode_error with no label. *)
let mk_decode_error (c: error_code) (n: nat) : decode_error =
  { err_code = c; err_pos = n; label = None }

(** Result of decoding: either an error or a value plus bytes consumed. *)
type decode_result (a: Type0) = either decode_error (a & nat)

(** Low* variant of decode error using [U32.t] position. *)
type decode_error_lo = { locode: error_code; lopos: U32.t }

(** Low* variant of decode result. *)
type decode_result_lo (a: Type0) = either decode_error_lo (a & U32.t)

(** Clamp negative integers to 0.

    Negative inputs are silently clamped to 0.  All codec wfcv guards
    reject negative values before reaching encoders, so this clamping
    is only a safety net for unguarded calls.  If [nat_of_int] receives
    a negative argument, the wfcv precondition failed first. *)
(** Clamp negative int to 0. Safety net; wfcv guards prevent negative inputs. *)
let nat_of_int (x: int) : nat = if x < 0 then 0 else x

(** Convert [nat] to [U32.t], clamping values ≥ 2^32 to 2^32−1.

    Prefer [u32_of_small_nat] when you have a proof that [n < 4294967296].
    Only use this when clamping is acceptable (e.g., error positions that
    are already bounded by buffer length). *)
(** Convert nat to U32.t, clamping values ≥ 2^32. *)
let u32_of_nat (n: nat) : U32.t =
  U32.uint_to_t (if n > 4294967295 then 4294967295 else n)

(** A verified bidirectional codec for values of type ['a].

    Eight fields:
    - [enc]: serializer from ['a] to [byte_seq]
    - [dec]: deserializer from [byte_seq] to [decode_result a]
    - [wfcv]: well-formed-value guard (runtime-checkable)
    - [wfcv_prop]: well-formed-value property (proof-only, e.g., [v == x] for pure)
    - [rest_cond]: suffix condition — what must hold of bytes after the encoded value
    - [roundtrip]: lemma proving [dec (enc v ++ r) == Inr (v, |enc v|)]
      when [wfcv], [wfcv_prop], and [rest_cond] hold
    - [dec_err_bound]: lemma proving error position ≤ s length
    - [dec_consumed_bound]: lemma proving n bytes ≤ s length *)
noeq
type codec (a: Type) = {
  enc        : a -> Tot byte_seq;
  dec        : byte_seq -> Tot (decode_result a);
  wfcv       : a -> Tot bool;
  wfcv_prop  : a -> Tot prop;
  rest_cond  : a -> byte_seq -> Tot prop;
  roundtrip  : (v: a) -> (r: byte_seq) -> Lemma
    (requires wfcv v /\ wfcv_prop v /\ rest_cond v r)
    (ensures dec (enc v `Seq.append` r) == Inr (v, Seq.length (enc v)));
  dec_err_bound : (s: byte_seq) -> Lemma
    (ensures (match dec s with Inl err -> err.err_pos <= Seq.length s | _ -> True));
  dec_consumed_bound : (s: byte_seq) -> Lemma
    (ensures (match dec s with Inr (_, n) -> n <= Seq.length s | _ -> True));
}

(** Length of the encoding of value [v] under codec [c]. *)
let len_of_enc (#a:Type) (c: codec a) (v: a) : GTot nat = Seq.length (c.enc v)

(** pow2 *)

#push-options "--z3rlimit 40"
(* pow2 returns int (not nat) because callers use it in varint arithmetic
   expressions with mixed int+nat operands (e.g., value + piece * pow2 shift
   where value: int). int return type avoids explicit nat→int casts at each
   call site while staying within F*'s type promotion rules. *)
(** pow2. *)
let rec pow2 (n: nat) : Tot int (decreases n) =
  if n = 0 then 1 else 2 * pow2 (n - 1)
#pop-options

(** string_to_bytes *)

let string_to_bytes (s: string) : Tot byte_seq =
  (* ASCII-only: code points > 255 are truncated via % 256.
     This library does not handle Unicode. Use string_is_ascii to guard. *)
  seq_of_list (FStar.List.Tot.map (fun (c: FStar.Char.char) ->
    U8.uint_to_t (FStar.Char.int_of_char c % 256))
    (FStar.String.list_of_string s))

(** string_is_ascii: true iff every character in s has code point < 128. *)
(** Use as wfcv guard for text combinators to prevent silent truncation. *)
let string_is_ascii (s: string) : Tot bool =
  FStar.List.Tot.for_all (fun (c: FStar.Char.char) ->
    FStar.Char.int_of_char c < 128
  ) (FStar.String.list_of_string s)

(** bytes_decode *)

let rec bytes_decode (bs: list byte) (s: byte_seq) : Tot (decode_result unit) (decreases bs) =
  match bs with
  | [] -> Inr ((), 0)
  | b :: tl ->
    if Seq.length s = 0 then Inl (mk_decode_error UnexpectedEndOfInput 0)
    else if Seq.index s 0 = b then
      match bytes_decode tl (Seq.slice s 1 (Seq.length s)) with
      | Inl err -> Inl ({err with err_pos = err.err_pos + 1})
      | Inr ((), n) -> Inr ((), 1 + n)
    else Inl (mk_decode_error (ExpectedByte b) 0)

(** varint_decode_go *)

#push-options "--z3rlimit 40"
let rec varint_decode_go (s: byte_seq) (n: nat) (p: nat) (value: int) (shift: nat)
  : Tot (decode_result int) (decreases n) =
  if n = 0 then Inl (mk_decode_error UnexpectedEndOfInput p)
  else if p >= Seq.length s then Inl (mk_decode_error UnexpectedEndOfInput p)
  else let b = U8.v (Seq.index s p) in
    let piece = b % 128 in
    let v' = value + piece * pow2 shift in
    if b < 128 then Inr (v', p + 1)
    else varint_decode_go s (n - 1) (p + 1) v' (shift + 7)
#pop-options

(** varint_encode_go *)

#push-options "--z3rlimit 40"
let rec varint_encode_go (nbytes: nat) (i: nat) (v: nat) (a: list byte)
  : Tot (list byte) (decreases (nbytes - i)) =
  if i >= nbytes then rev a
  else if v < 128 then rev ((U8.uint_to_t (nat_of_int v)) :: a)
  else let b = U8.uint_to_t (nat_of_int ((v % 128) + 128)) in
       varint_encode_go nbytes (i + 1) (v / 128) (b :: a)
#pop-options

(** digits_encode *)

#push-options "--z3rlimit 40"
let rec digits_encode (n: nat) : Tot (list byte) (decreases n) =
  if n < 10 then [U8.uint_to_t (0x30 + n)]
  else digits_encode (n / 10) @ [U8.uint_to_t (0x30 + (n % 10))]
#pop-options

(** Digit helpers *)

let dec_nat (k: nat) : nat = if k = 0 then 0 else k - 1

(** True if byte is an ASCII digit (0x30-0x39). *)
let is_digit (b: byte) : bool = 0x30 <= U8.v b && U8.v b <= 0x39

(** Accumulate integer value from digit byte list. *)
let rec acc_digits (ds: list byte) (a: int) : Tot int (decreases ds) =
  match ds with
  | [] -> a
  | d :: tl ->
    if is_digit d then acc_digits tl (Prims.op_Multiply a 10 + (U8.v d - 0x30))
    else acc_digits tl a

(** True if every byte in the list is a digit. *)
let all_digits (ds: list byte) : bool = List.Tot.for_all is_digit ds

(** digits_to_int_decode_go *)

#push-options "--z3rlimit 40"
let rec digits_to_int_decode_go (f: int -> bool) (s: byte_seq) (k: nat) (a: int) (i: nat)
  : Tot (decode_result int) (decreases k) =
  if k = 0 then
    if f a then Inr (a, i) else Inl (mk_decode_error ExpectedPredicate i)
  else if i >= Seq.length s then
    if f a then Inr (a, i) else Inl (mk_decode_error ExpectedPredicate i)
  else let b = U8.v (Seq.index s i) in
    if 0x30 <= b && b <= 0x39 then
      digits_to_int_decode_go f s (k-1) (Prims.op_Multiply a 10 + (b - 0x30)) (i+1)
    else if i = 0 then Inl (mk_decode_error ExpectedPredicate 0)
    else if f a then Inr (a, i)
    else Inl (mk_decode_error ExpectedPredicate i)
#pop-options

(** Decode a digit string to integer, bounded by max digits and predicate. *)
let digits_to_int_decode (n: pos) (f: int -> bool) (s: byte_seq) : Tot (decode_result int) =
  digits_to_int_decode_go f s n 0 0

(** U32 bridge lemmas *)

(** Lemma: [10 < 2^32], proved by normalization. *)
let lemma_10_lt_u32max () : Lemma (10 < 4294967296) =
  assert_norm (10 < 4294967296)

(** Convert a nat known to be [< 2^32] into a [U32.t] without clamping.
    Requires proof that [x < 4294967296]. *)
(** Convert a nat < 2^32 to U32.t without clamping. Requires proof of bound. *)
let u32_of_small_nat (x: nat{x < 4294967296}) : Tot U32.t =
  assert_norm (pow2 32 = 4294967296);
  U32.uint_to_t x

(** Lemma: U32.v (u32_of_small_nat x) == x for bounded x. *)
let lemma_u32_v_small_nat (x: nat) : Lemma
  (requires x < 4294967296)
  (ensures U32.v (u32_of_small_nat x) == x)
  = assert_norm (pow2 32 = 4294967296);
    FStar.Math.Lemmas.small_mod x (pow2 32)

(** lemma_u32_bound_transitive is the canonical bound lemma. *)
(** lemma_u32_bound and lemma_bound_10 are convenience wrappers. *)
let lemma_u32_bound_transitive (x: nat) (n: nat) (m: U32.t) : Lemma
  (requires x <= n /\ n <= U32.v m)
  (ensures x < 4294967296)
  = assert_norm (pow2 32 = 4294967296);
    assert (U32.v m < 4294967296);
    assert (x < 4294967296)

(** Lemma: n ≤ U32.v len implies n < 2^32. *)
let lemma_u32_bound (n: nat) (m: U32.t) : Lemma
  (requires n <= U32.v m)
  (ensures n < 4294967296)
  = lemma_u32_bound_transitive n n m

(** Lemma: x ≤ 10 implies x < 2^32. *)
let lemma_bound_10 (x: nat) : Lemma
  (requires x <= 10)
  (ensures x < 4294967296)
  = lemma_10_lt_u32max ();
    lemma_u32_bound_transitive x 10 (u32_of_small_nat 10)

(** Lemma: error position shifted by buffer offset stays within U32 range. *)
let lemma_decode_err_pos_bound (i n: U32.t) (err_pos: nat) : Lemma
  (requires
    U32.v i + U32.v n < 4294967296 /\
    err_pos <= U32.v n)
  (ensures U32.v i + err_pos < 4294967296)
  = assert_norm (pow2 32 = 4294967296);
    assert (U32.v i + err_pos <= U32.v i + U32.v n);
    assert (U32.v i + err_pos < 4294967296)

(** Lemma: seq_of_list (seq_to_list s) == s (roundtrip identity). *)
let lemma_seq_list_bij (s: byte_seq) : Lemma
  (ensures seq_of_list (Seq.seq_to_list s) == s)
  = Seq.lemma_eq_intro (seq_of_list (Seq.seq_to_list s)) s

(** Lemma: seq_to_list (seq_of_list l) == l (roundtrip identity). *)
let rec lemma_seq_list_bij_rev (l: list byte) : Lemma
  (ensures Seq.seq_to_list (seq_of_list l) == l)
  (decreases l)
  = match l with
    | [] -> ()
    | _ :: tl -> lemma_seq_list_bij_rev tl

(** Lemma: Seq.length (seq_of_list l) == List.Tot.length l. *)
let rec lemma_seq_of_list_length (l: list byte) : Lemma
  (ensures Seq.length (seq_of_list l) == List.Tot.length l)
  (decreases l)
  = match l with
    | [] -> ()
    | _ :: tl -> lemma_seq_of_list_length tl

(** Lemma: [seq_to_list] distributes over append for a [seq_of_list] prefix.
    [seq_to_list (seq_of_list l ++ s) == l ++ seq_to_list s] for an arbitrary
    suffix [s].

    Proven by induction on [l] using the transparent internal stdlib bridges
    [FStar.Seq.Base.lemma_seq_of_list_cons], [FStar.Seq.Properties.append_cons],
    and [FStar.Seq.Base.lemma_seq_to_list_cons].  This is the fact fstar-proofs
    §11/§59/§60 described as "unprovable across module boundaries" — it is
    provable when the internal (transparent [= ()]) bridge lemmas are chained
    explicitly (precedent: [Network.IPv6.lemma_seq_to_list_of_list_append],
    0-admit, --z3rlimit 2000).  It is the bridge a [seq_to_list]-at-the-boundary
    decoder needs for a GENERAL-\ suffix roundtrip. *)
#push-options "--z3rlimit 2000 --split_queries always"
let rec lemma_seq_to_list_of_list_append (l: list byte) (s: byte_seq) : Lemma
  (ensures Seq.seq_to_list (seq_of_list l `Seq.append` s) == l @ Seq.seq_to_list s)
  (decreases l)
  = match l with
    | [] ->
        Seq.lemma_eq_intro (seq_of_list [] `Seq.append` s) s;
        assert (Seq.seq_to_list (seq_of_list [] `Seq.append` s) == Seq.seq_to_list s);
        assert ([] @ Seq.seq_to_list s == Seq.seq_to_list s);
        ()
    | h :: t ->
        lemma_seq_to_list_of_list_append t s;
        let st = seq_of_list t in
        FStar.Seq.Base.lemma_seq_of_list_cons h t;
        FStar.Seq.Properties.append_cons h st s;
        let combined = st `Seq.append` s in
        FStar.Seq.Base.lemma_seq_to_list_cons h combined;
        assert (seq_of_list (h :: t) == Seq.cons h st);
        assert (Seq.cons h st `Seq.append` s == Seq.cons h combined);
        assert (Seq.seq_to_list (Seq.cons h combined) == h :: Seq.seq_to_list combined);
        assert (Seq.seq_to_list combined == t @ Seq.seq_to_list s);
        ()
#pop-options

(** Bytes decode bound lemmas *)

let lemma_bytes_decode_nil (s: byte_seq) : Lemma
  (ensures bytes_decode [] s == Inr ((), 0))
  [SMTPat (bytes_decode [] s)] = ()

(** Lemma: SMTPat unfold for bytes_decode on a cons list. *)
let lemma_bytes_decode_cons (b: byte) (tl: list byte) (s: byte_seq) : Lemma
  (ensures bytes_decode (b :: tl) s ==
    (if Seq.length s = 0 then Inl (mk_decode_error UnexpectedEndOfInput 0)
     else if Seq.index s 0 = b then
       match bytes_decode tl (Seq.slice s 1 (Seq.length s)) with
       | Inl err -> Inl ({err with err_pos = err.err_pos + 1})
       | Inr ((), n) -> Inr ((), 1 + n)
     else Inl (mk_decode_error (ExpectedByte b) 0)))
  [SMTPat (bytes_decode (b :: tl) s)] = ()

#push-options "--z3rlimit 80"
let rec lemma_bytes_decode_prefix (bs: list byte) (s: byte_seq) (i n m: nat)
  : Lemma
    (requires
      i + n <= Seq.length s /\
      List.Tot.length bs <= n /\
      n <= m /\
      i + m <= Seq.length s)
    (ensures bytes_decode bs (Seq.slice s i (i + n)) ==
             bytes_decode bs (Seq.slice s i (i + m)))
    (decreases bs)
  = match bs with
    | [] -> ()
    | b :: tl ->
        if Seq.index s i = b then begin
          lemma_bytes_decode_prefix tl s (i + 1) (n - 1) (m - 1);
          Seq.Properties.slice_slice s i (i + n) 1 n;
          Seq.Properties.slice_slice s i (i + m) 1 m
        end else ()
#pop-options

(** Lemma: successful bytes_decode consumes exactly |bs| bytes. *)
let rec lemma_bytes_decode_inr_consumed (bs: list byte) (s: byte_seq) (n: nat)
  : Lemma
    (requires bytes_decode bs s == Inr ((), n))
    (ensures n == List.Tot.length bs)
    (decreases bs)
  = match bs with
    | [] -> ()
    | b :: tl ->
        lemma_bytes_decode_cons b tl s;
        let tail_r = bytes_decode tl (Seq.slice s 1 (Seq.length s)) in
        match tail_r with
        | Inr ((), n) ->
            lemma_bytes_decode_inr_consumed tl (Seq.slice s 1 (Seq.length s)) n
        | Inl _ -> ()

(** Lemma: bytes_decode error position is bounded by the byte list length. *)
let rec lemma_bytes_decode_inl_bound (bs: list byte) (s: byte_seq) (err: decode_error)
  : Lemma
    (requires bytes_decode bs s == Inl err)
    (ensures err.err_pos <= List.Tot.length bs)
    (decreases bs)
  = match bs with
    | [] -> ()
    | b :: tl ->
      lemma_bytes_decode_cons b tl s;
      if Seq.length s = 0 then ()
      else if Seq.index s 0 = b then begin
        let tail_r = bytes_decode tl (Seq.slice s 1 (Seq.length s)) in
        match tail_r with
        | Inl tail_err ->
            lemma_bytes_decode_inl_bound tl (Seq.slice s 1 (Seq.length s)) tail_err;
            ()
        | _ -> ()
      end else ()

(** Proves that bytes_decode error positions are bounded by the input length. *)
(** Stronger than lemma_bytes_decode_inl_bound (which bounds by |bs|). *)
let rec lemma_bytes_decode_err_pos_le_input (bs: list byte) (s: byte_seq) : Lemma
  (ensures (match bytes_decode bs s with
            | Inl err -> err.err_pos <= Seq.length s
            | _ -> True))
  (decreases bs)
  = match bs with
    | [] -> ()
    | b :: tl ->
      lemma_bytes_decode_cons b tl s;
      if Seq.length s = 0 then ()
      else if Seq.index s 0 = b then begin
        lemma_bytes_decode_err_pos_le_input tl (Seq.slice s 1 (Seq.length s));
        let tail_r = bytes_decode tl (Seq.slice s 1 (Seq.length s)) in
        match tail_r with
        | Inl tail_err -> ()
        | _ -> ()
      end else ()

(** Proves that bytes_decode success means n <= Seq.length s. *)
#push-options "--z3rlimit 40"
let rec lemma_bytes_decode_consumed_le_input (bs: list byte) (s: byte_seq) : Lemma
  (ensures (match bytes_decode bs s with
            | Inr (_, n) -> n <= Seq.length s
            | _ -> True))
  (decreases bs)
  = match bs with
    | [] -> ()
    | b :: tl ->
      lemma_bytes_decode_cons b tl s;
      if Seq.length s = 0 then ()
      else if Seq.index s 0 = b then begin
        lemma_bytes_decode_consumed_le_input tl (Seq.slice s 1 (Seq.length s));
        match bytes_decode tl (Seq.slice s 1 (Seq.length s)) with
        | Inr (_, n) -> ()
        | _ -> ()
      end else ()
#pop-options

(** Varint decode bound lemmas *)

let shift_result (#a:Type) (p: nat) (r: decode_result a) : decode_result a =
  match r with
  | Inr (v, n) -> Inr (v, p + n)
  | Inl err -> Inl ({err with err_pos = err.err_pos + p})

#push-options "--z3rlimit 80"
let rec lemma_varint_decode_shift
  (s: byte_seq) (n p: nat) (value: int) (shift: nat)
  : Lemma
    (requires p + n <= Seq.length s)
    (ensures varint_decode_go s n p value shift ==
             shift_result p (varint_decode_go (Seq.slice s p (p + n)) n 0 value shift))
    (decreases n)
  = if n = 0 then ()
    else begin
      let sub = Seq.slice s p (p + n) in
      let b = U8.v (Seq.index s p) in
      if b < 128 then ()
      else begin
        let piece = b % 128 in
        let v' = value + piece * pow2 shift in
        let shift' : nat = shift + 7 in
        lemma_varint_decode_shift s (n - 1) (p + 1) v' shift';
        lemma_varint_decode_shift sub (n - 1) 1 v' shift';
        Seq.Properties.slice_slice s p (p + n) 1 n;
        (* slice_slice above proves Seq.slice sub 1 n == Seq.slice s (p+1) (p+n).
           Chain: (1) vgo at p+1 == shift_result(p+1)(vgo on slice), (2) vgo on sub's sub ==
           shift_result(1)(vgo on sub-slice).  slice_slice bridges sub's sub == s's sub-sub. *)
        assert (varint_decode_go s n p value shift ==
                varint_decode_go s (n - 1) (p + 1) v' shift');
        assert (varint_decode_go s (n - 1) (p + 1) v' shift' ==
                shift_result (p + 1)
                  (varint_decode_go (Seq.slice s (p + 1) (p + n))
                                   (n - 1) 0 v' shift'));
        ()
      end
    end
#pop-options

(** Lemma: successful varint decode consumed is in (pos, pos+fuel]. *)
let rec lemma_varint_decode_inr_bound (s: byte_seq) (n p: nat) (value: int) (shift: nat)
                                       (v: int) (out_pos: nat)
  : Lemma
    (requires varint_decode_go s n p value shift == Inr (v, out_pos))
    (ensures out_pos <= p + n /\ out_pos > p)
    (decreases n)
  = if n = 0 then ()
    else if p >= Seq.length s then ()
    else begin
      let b = U8.v (Seq.index s p) in
      if b < 128 then ()
      else begin
        let piece = b % 128 in
        let v' = value + piece * pow2 shift in
        lemma_varint_decode_inr_bound s (n - 1) (p + 1) v' (shift + 7) v out_pos
      end
    end

(** Lemma: varint decode with fuel=10 consumes at most 10 bytes. *)
let lemma_varint_decode_inr_bound_10 (s: byte_seq) (v: int) (out_pos: nat) : Lemma
  (requires varint_decode_go s 10 0 0 0 == Inr (v, out_pos))
  (ensures out_pos <= 10 /\ out_pos > 0)
  = lemma_varint_decode_inr_bound s 10 0 0 0 v out_pos

(** Proves that a successful varint decode never consumes more bytes *)
(** than the input length. Structural induction on n. *)
#push-options "--z3rlimit 40"
let rec lemma_varint_decode_consumed_le_len (s: byte_seq) (n p: nat) (value: int) (shift: nat)
  : Lemma
    (ensures (match varint_decode_go s n p value shift with
              | Inr (_, n) -> n <= Seq.length s
              | Inl _ -> True))
    (decreases n)
  = if n = 0 then ()
    else if p >= Seq.length s then ()
    else begin
      let b = U8.v (Seq.index s p) in
      if b < 128 then ()
      else begin
        let piece = b % 128 in
        let v' = value + piece * pow2 shift in
        lemma_varint_decode_consumed_le_len s (n - 1) (p + 1) v' (shift + 7)
      end
    end
#pop-options

(** Lemma: varint decode error position ≤ input length. *)
let rec lemma_varint_decode_inl_len_bound (s: byte_seq) (n p: nat) (value: int) (shift: nat)
                                       (err: decode_error)
  : Lemma
    (requires varint_decode_go s n p value shift == Inl err /\ p <= Seq.length s)
    (ensures err.err_pos <= Seq.length s)
    (decreases n)
  = if n = 0 then ()
    else if p >= Seq.length s then ()
    else begin
      let b = U8.v (Seq.index s p) in
      if b < 128 then ()
      else begin
        let piece = b % 128 in
        let v' = value + piece * pow2 shift in
        lemma_varint_decode_inl_len_bound s (n - 1) (p + 1) v' (shift + 7) err
      end
    end

(** Digit decode bound lemmas *)

let rec lemma_digits_decode_inr_len_bound (f: int -> bool) (s: byte_seq) (k: nat)
                                       (a: int) (i: nat) (v: int) (n: nat)
  : Lemma
    (requires digits_to_int_decode_go f s k a i == Inr (v, n) /\ i <= Seq.length s)
    (ensures n <= Seq.length s)
    (decreases k)
  = if k = 0 then ()
    else if i >= Seq.length s then ()
    else begin
      let b = U8.v (Seq.index s i) in
      if 0x30 <= b && b <= 0x39 then begin
        assert (i + 1 <= Seq.length s);
        lemma_digits_decode_inr_len_bound f s (k-1)
          (Prims.op_Multiply a 10 + (b - 0x30)) (i+1) v n
      end
      else ()
    end

(** Lemma: digits decode go bounds both Inr consumed and Inl err_pos. *)
let rec lemma_digits_decode_go_len_bound (f: int -> bool) (s: byte_seq) (k: nat) (a: int) (i: nat)
  : Lemma
    (requires i <= Seq.length s)
    (ensures (
      match digits_to_int_decode_go f s k a i with
      | Inr (v, n) -> n <= Seq.length s
      | Inl err -> err.err_pos <= Seq.length s))
    (decreases k)
  = if k = 0 then ()
    else if i >= Seq.length s then ()
    else begin
      let b = U8.v (Seq.index s i) in
      if 0x30 <= b && b <= 0x39 then begin
        assert (i + 1 <= Seq.length s);
        lemma_digits_decode_go_len_bound f s (k-1) (Prims.op_Multiply a 10 + (b - 0x30)) (i+1)
      end
      else ()
    end

(** lemma_list_to_slice *)

#push-options "--z3rlimit 80"
let lemma_list_to_slice (l: list byte) (s: byte_seq) (p n: nat) : Lemma
    (requires
      p + n <= Seq.length s /\
      List.Tot.length l == n /\
      (forall (i: nat). i < n ==>
        List.Tot.index l i == Seq.index s (p + i)))
    (ensures seq_of_list l == Seq.slice s p (p + n))
  = let n = n in
    let o = p in
    let sl = Seq.slice s o (o + n) in
    let seq_l = seq_of_list l in
    let rec aux (i: nat) : Lemma
      (requires i <= n)
      (ensures (forall (j: nat). j < i ==> Seq.index seq_l j == Seq.index sl j))
      (decreases i)
    = if i = 0 then ()
      else begin
        aux (i - 1);
        let j = i - 1 in
        assert (Seq.index seq_l j == List.Tot.index l j);
        assert (Seq.index sl j == Seq.index s (o + j));
        assert (List.Tot.index l j == Seq.index s (o + j))
      end
    in
    aux n;
    Seq.lemma_eq_intro seq_l sl;
    Seq.lemma_eq_elim seq_l sl;
    ()
#pop-options

(** Infrastructure lemmas *)

(** slice after prefix *)
#push-options "--z3rlimit 80"
let lemma_slice_after_prefix (enc: byte_seq) (r: byte_seq) : Lemma
  (ensures Seq.slice (Seq.append enc r) (Seq.length enc)
    (Seq.length (Seq.append enc r)) == r)
  = Seq.lemma_len_append enc r;
    assert (Seq.length (Seq.append enc r) == Seq.length enc + Seq.length r);
    Seq.lemma_eq_intro
      (Seq.slice (Seq.append enc r) (Seq.length enc)
        (Seq.length enc + Seq.length r)) r;
    Seq.lemma_eq_elim
      (Seq.slice (Seq.append enc r) (Seq.length enc)
        (Seq.length enc + Seq.length r)) r
#pop-options

(** slice of append prefix: slice(s1 ++ s2, 0, |s1|) == s1 *)
let lemma_slice_append_prefix (s1 s2: byte_seq) : Lemma
  (ensures Seq.slice (Seq.append s1 s2) 0 (Seq.length s1) == s1)
  =
  Seq.lemma_len_append s1 s2;
  Seq.lemma_eq_intro (Seq.slice (Seq.append s1 s2) 0 (Seq.length s1)) s1

(** slice of cons *)
#push-options "--z3rlimit 40"
let lemma_slice_cons_spec (#a:Type) (x: a) (s: Seq.seq a) : Lemma
  (ensures Seq.slice (Seq.cons x s) 1 (Seq.length s + 1) == s)
  = Seq.lemma_eq_intro (Seq.slice (Seq.cons x s) 1 (Seq.length s + 1)) s;
    Seq.lemma_eq_elim (Seq.slice (Seq.cons x s) 1 (Seq.length s + 1)) s
#pop-options

(** bytes self-prefix *)
#push-options "--z3rlimit 80"
let rec lemma_bytes_self_prefix_spec (bs: list byte) (r: byte_seq) : Lemma
  (ensures bytes_decode bs (Seq.append (seq_of_list bs) r) == Inr ((), List.Tot.length bs))
  (decreases bs)
  = match bs with
    | [] -> ()
    | b :: tl ->
        let s_tl = seq_of_list tl in
        let s_app = Seq.append s_tl r in
        Seq.append_assoc (Seq.create 1 b) s_tl r;
        lemma_slice_cons_spec b s_app;
        lemma_bytes_self_prefix_spec tl r;
        ()
#pop-options

(** Digit lemma infrastructure *)

#push-options "--z3rlimit 40"
let rec lemma_all_digits_append_helper (ds1 ds2: list byte) : Lemma
  (ensures all_digits (ds1 @ ds2) == (all_digits ds1 && all_digits ds2))
  (decreases ds1)
  = match ds1 with
    | [] -> ()
    | d :: tl -> lemma_all_digits_append_helper tl ds2
#pop-options

#push-options "--z3rlimit 40"
let rec lemma_digits_encode_all_digits_helper (n: nat) : Lemma
  (ensures all_digits (digits_encode n))
  (decreases n)
  = if n < 10 then ()
    else begin
      let ds_pre = digits_encode (n / 10) in
      let d = U8.uint_to_t (0x30 + (n % 10)) in
      lemma_digits_encode_all_digits_helper (n / 10);
      lemma_all_digits_append_helper ds_pre [d];
      ()
    end
#pop-options

#push-options "--z3rlimit 40"
let rec lemma_acc_digits_append_helper (ds1 ds2: list byte) (a: int) : Lemma
  (ensures acc_digits (ds1 @ ds2) a == acc_digits ds2 (acc_digits ds1 a))
  (decreases ds1)
  = match ds1 with
    | [] -> ()
    | d :: tl -> lemma_acc_digits_append_helper tl ds2
      (if 0x30 <= U8.v d && U8.v d <= 0x39 then a * 10 + (U8.v d - 0x30) else a)
#pop-options

#push-options "--z3rlimit 80"
let rec lemma_acc_digits_encode_helper (n: nat) : Lemma
  (ensures acc_digits (digits_encode n) 0 == n)
  (decreases n)
  = if n < 10 then ()
    else begin
      let n_div = n / 10 in let n_mod = n % 10 in
      let d = U8.uint_to_t (0x30 + n_mod) in
      lemma_acc_digits_encode_helper n_div;
      lemma_acc_digits_append_helper (digits_encode n_div) [d] 0;
      ()
    end
#pop-options

(** Digit shift lemma *)

let nat_add (a b: nat) : nat = a + b
(** Nat increment. *)
let nat_incr (n: nat) : nat = n + 1

#push-options "--z3rlimit 80"
let rec lemma_digits_decode_shift
  (f: int -> bool) (s: byte_seq) (k: nat) (i: nat) (a: int)
  : Lemma
    (requires i < Seq.length s /\ is_digit (Seq.index s i))
    (ensures
      digits_to_int_decode_go f s k a i
      == (match digits_to_int_decode_go f
                (Seq.slice s i (Seq.length s)) k a 0 with
          | Inl err -> Inl ({err with err_pos = nat_add err.err_pos i})
          | Inr (v, n) -> Inr (v, nat_add n i)))
    (decreases k)
  = let sliced = Seq.slice s i (Seq.length s) in
    if k > 0 then begin
      let b = U8.v (Seq.index s i) in
      let a' = Prims.op_Multiply a 10 + (b - 0x30) in
      let cnt1 = nat_incr i in
      if cnt1 >= Seq.length s then ()
      else if is_digit (Seq.index s cnt1) then begin
        let k' : nat = dec_nat k in
        lemma_digits_decode_shift f s k' cnt1 a';
        lemma_digits_decode_shift f sliced k' 1 a';
        (* The two recursive calls prove that decoding from cnt1 on the full s
           and from 1 on the sliced s are shift-equivalent to their respective
           zero-start decodes.  The assert below bridges from (k, a, i) to
           (k'=dec_nat k, a'=a*10+(b-0x30), cnt1=nat_incr i) in one step. *)
        assert (digits_to_int_decode_go f s k a i ==
                digits_to_int_decode_go f s k' a' cnt1);
        ()
      end else ()
    end else ()
#pop-options

(** lemma_digits_process_list *)

#push-options "--z3rlimit 80"
let rec lemma_digits_process_list
  (f: int -> bool) (ds: list byte) (r: byte_seq) (k: nat) (a: int)
  : Lemma
    (requires
      Cons? ds /\
      all_digits ds /\
      f (acc_digits ds a) /\
      List.Tot.length ds <= k /\
      (List.Tot.length ds = k \/
       Seq.length r = 0 \/
       (Seq.length r > 0 /\ not (is_digit (Seq.index r 0)))))
    (ensures
      digits_to_int_decode_go f (Seq.append (seq_of_list ds) r) k a 0
      == Inr (acc_digits ds a, List.Tot.length ds))
    (decreases ds)
  = let s = Seq.append (seq_of_list ds) r in
    let n = List.Tot.length ds in
    match ds with
    | [d] ->
      if k = 1 then ()
      else if Seq.length r = 0 then ()
      else if not (is_digit (Seq.index r 0)) then ()
      else begin
        assert (n = 1);
        assert (k <> 1);
        assert (Seq.length r > 0);
        assert (is_digit (Seq.index r 0));
        assert (False)
      end
    | d :: tl ->
      let k' : nat = dec_nat k in
      let d_val = U8.v d - 0x30 in
      let a' = Prims.op_Multiply a 10 + d_val in
      let tail_input = Seq.append (seq_of_list tl) r in
      assert (digits_to_int_decode_go f s k a 0 ==
              digits_to_int_decode_go f s k' a' 1);
      assert (Seq.equal (Seq.slice s 1 (Seq.length s)) tail_input);
      assert (is_digit (Seq.index s 1));
      lemma_digits_decode_shift f s k' 1 a';
      assert (List.Tot.length tl <= k');
      assert (f (acc_digits tl a'));
      lemma_digits_process_list f tl r k' a';
      assert (digits_to_int_decode_go f tail_input k' a' 0
              == Inr (acc_digits tl a', List.Tot.length tl));
      assert (digits_to_int_decode_go f s k' a' 1
              == Inr (acc_digits tl a', nat_incr (List.Tot.length tl)));
      assert (digits_to_int_decode_go f s k a 0
              == Inr (acc_digits tl a', nat_incr (List.Tot.length tl)));
      assert (acc_digits (d :: tl) a == acc_digits tl a');
      assert (List.Tot.length (d :: tl) == nat_incr (List.Tot.length tl));
      ()
#pop-options

(** lemma_digits_decode_encode_roundtrip *)

#push-options "--z3rlimit 40"
let lemma_digits_decode_encode_roundtrip
  (f: int -> bool) (max_len: nat) (n: nat) (r: byte_seq)
  : Lemma
    (requires
      f n /\
      all_digits (digits_encode n) /\
      acc_digits (digits_encode n) 0 == n /\
      List.Tot.length (digits_encode n) <= max_len /\
      (List.Tot.length (digits_encode n) = max_len \/
       Seq.length r = 0 \/
       (Seq.length r > 0 /\ not (is_digit (Seq.index r 0)))))
    (ensures
      digits_to_int_decode_go f
        (Seq.append (seq_of_list (digits_encode n)) r)
        max_len 0 0
      == Inr (n, List.Tot.length (digits_encode n)))
  = lemma_digits_process_list f (digits_encode n) r max_len 0
#pop-options

(** word32 byte-indexing helper lemmas *)

(** lemma_word32_enc_bytes: given 4 bytes and a nested-append sequence, *)
(** proves the bytes are at the expected indices. Parametric over byte values *)
(** so it can be called from roundtrip proofs without self-reference. *)
#push-options "--z3rlimit 20"
let lemma_word32_enc_bytes (b0 b1 b2 b3: byte)
  (* Refinement is a binding convenience; callers define enc_v as the append
     expression inline. No proof obligation is imposed by this refinement. *)
  (enc_v: byte_seq{
    enc_v == Seq.append
      (Seq.append (Seq.append (Seq.create 1 b0) (Seq.create 1 b1))
                  (Seq.create 1 b2))
      (Seq.create 1 b3)})
  : Lemma
  (Seq.length enc_v == 4 /\
   Seq.index enc_v 0 == b0 /\
   Seq.index enc_v 1 == b1 /\
   Seq.index enc_v 2 == b2 /\
   Seq.index enc_v 3 == b3)
  = let s0 = Seq.create 1 b0 in
    let s1 = Seq.create 1 b1 in
    let s2 = Seq.create 1 b2 in
    let s3 = Seq.create 1 b3 in
    let s01 = Seq.append s0 s1 in
    let s012 = Seq.append s01 s2 in
    // Index 0: enc_v[0] = s012[0] = s01[0] = s0[0] = b0
    lemma_index_app1 s012 s3 0;
    lemma_index_app1 s01 s2 0;
    lemma_index_app1 s0 s1 0;
    lemma_index_create 1 b0 0;
    // Index 1: enc_v[1] = s012[1] = s01[1] = s1[0] = b1
    lemma_index_app1 s012 s3 1;
    lemma_index_app1 s01 s2 1;
    lemma_index_app2 s0 s1 1;
    lemma_index_create 1 b1 0;
    // Index 2: enc_v[2] = s012[2] = s2[0] = b2
    lemma_index_app1 s012 s3 2;
    lemma_index_app2 s01 s2 2;
    lemma_index_create 1 b2 0;
    // Index 3: enc_v[3] = s3[0] = b3
    lemma_index_app2 s012 s3 3;
    lemma_index_create 1 b3 0;
    ()
#pop-options

(** 1. token *)

#push-options "--z3rlimit 10"
let token : codec byte = {
  enc       = (fun b -> Seq.create 1 b);
  dec       = (fun s -> if Seq.length s >= 1 then Inr (Seq.index s 0, 1)
                            else Inl (mk_decode_error UnexpectedEndOfInput 0));
  wfcv      = (fun _ -> true);
  wfcv_prop = (fun _ -> True);
  rest_cond = (fun _ _ -> True);
  roundtrip = (fun v r ->
    lemma_create_len 1 v;
    lemma_index_app1 (Seq.create 1 v) r 0;
    lemma_index_create 1 v 0;
    ());
  dec_err_bound = (fun s -> ());
  dec_consumed_bound = (fun s -> ());
}
#pop-options

(** Combinator 2: byte_val — a specific expected byte.

    @param b The exact byte to match.
    Encodes [b] (1 byte).  Decodes one byte; succeeds if it equals [b],
    fails with [ExpectedByte b] otherwise. *)
#push-options "--z3rlimit 10"
let byte_val (b: byte) : codec unit = {
  enc       = (fun _ -> Seq.create 1 b);
  dec       = (fun s ->
    if Seq.length s >= 1 && Seq.index s 0 = b then Inr ((), 1)
    else if Seq.length s >= 1 then Inl (mk_decode_error (ExpectedByte b) 0)
    else Inl (mk_decode_error UnexpectedEndOfInput 0));
  wfcv      = (fun _ -> true);
  wfcv_prop = (fun _ -> True);
  rest_cond = (fun _ _ -> True);
  roundtrip = (fun v r ->
    lemma_create_len 1 b;
    lemma_index_app1 (Seq.create 1 b) r 0;
    lemma_index_create 1 b 0;
    ());
  dec_err_bound = (fun s -> ());
  dec_consumed_bound = (fun s -> ());
}
#pop-options

(** Combinator 3: satisfy — a byte matching a predicate.

    @param f Predicate the byte must satisfy.
    Encodes as [Seq.create 1 v].  Decoder rejects bytes failing [f]
    with [ExpectedPredicate].  The wfcv guard is [f v]. *)

#push-options "--z3rlimit 10"
let satisfy (f: byte -> Tot bool) : codec byte = {
  enc       = (fun v -> Seq.create 1 v);
  dec       = (fun s ->
    if Seq.length s >= 1 then
      let b = Seq.index s 0 in
      if f b then Inr (b, 1) else Inl (mk_decode_error ExpectedPredicate 0)
    else Inl (mk_decode_error UnexpectedEndOfInput 0));
  wfcv      = (fun v -> f v);
  wfcv_prop = (fun _ -> True);
  rest_cond = (fun _ _ -> True);
  roundtrip = (fun v r ->
    // wfcv v = f v ensures enc v = Seq.create 1 v
    assert (f v);
    lemma_create_len 1 v;
    lemma_index_app1 (Seq.create 1 v) r 0;
    lemma_index_create 1 v 0;
    ());
  dec_err_bound = (fun s -> ());
  dec_consumed_bound = (fun s -> ());
}
#pop-options

(** Combinator 4: pure — a constant value (zero bytes on the wire).

    @param x The constant value.
    Encodes as empty sequence.  Decoder always returns [x] with 0 bytes
    n.  wfcv_prop requires [v == x]. *)

#push-options "--z3rlimit 10"
let pure (#a:Type) (x: a) : codec a = {
  enc       = (fun _ -> Seq.empty);
  dec       = (fun _ -> Inr (x, 0));
  wfcv      = (fun _ -> true);
  wfcv_prop = (fun v -> v == x);
  rest_cond = (fun _ _ -> True);
  roundtrip = (fun v r ->
    // enc v = Seq.empty, so enc v ++ r == r
    // wfcv_prop v = (v == x), so dec r = Inr(v, 0) since v == x
    append_empty_l r;
    ());
  dec_err_bound = (fun s -> ());
  dec_consumed_bound = (fun s -> ());
}
#pop-options

(** Combinator 5: text — a fixed ASCII string.

    @param s The expected string (ASCII only).
    Encodes as [string_to_bytes s].  Decodes exactly [n] bytes and
    compares with [string_to_bytes s].  Fails with [ExpectedEndOfInput]
    if input is too short, [ExpectedText] on mismatch.
    wfcv requires [string_is_ascii s]. *)

#push-options "--z3rlimit 40"
let text (s: string) : codec unit = {
  enc       = (fun () -> string_to_bytes s);
  dec       = (fun input ->
    let expected = string_to_bytes s in
    let n = Seq.length expected in
    if Seq.length input < n then
      Inl (mk_decode_error ExpectedEndOfInput (Seq.length input))
    else if Seq.eq (Seq.slice input 0 n) expected then
      Inr ((), n)
    else Inl (mk_decode_error ExpectedText 0));
  wfcv      = (fun _ -> string_is_ascii s);
  wfcv_prop = (fun _ -> True);
  rest_cond = (fun _ _ -> True);
  roundtrip = (fun v r ->
    let b = string_to_bytes s in
    Seq.lemma_len_append b r;
    lemma_slice_append_prefix b r;
    ());
  dec_err_bound = (fun s -> ());
  dec_consumed_bound = (fun s -> ());
}
#pop-options

(** Combinator 6: bytes — a fixed byte sequence.

    @param bs The expected byte list.
    Encodes as [seq_of_list bs].  Decoder uses [bytes_decode] for
    exact byte-by-byte matching.  Fails with [ExpectedByte b] on
    mismatch at the first differing position. *)

#push-options "--z3rlimit 40"
let bytes (bs: list byte) : codec unit = {
  enc       = (fun () -> seq_of_list bs);
  dec       = (fun s -> bytes_decode bs s);
  wfcv      = (fun _ -> true);
  wfcv_prop = (fun _ -> True);
  rest_cond = (fun _ _ -> True);
  roundtrip = (fun v r ->
    lemma_bytes_self_prefix_spec bs r;
    ());
  dec_err_bound = (fun s -> lemma_bytes_decode_err_pos_le_input bs s);
  dec_consumed_bound = (fun s -> lemma_bytes_decode_consumed_le_input bs s);
}
#pop-options

(** Combinator 7: uint8 — unsigned 8-bit integer.

    Encodes as a single byte.  wfcv: [0 <= v < 256].
    Decoder returns [U8.v] of the byte. *)

#push-options "--z3rlimit 15"
let uint8 : codec int = {
  enc       = (fun v -> Seq.create 1 (U8.uint_to_t (nat_of_int (v % 256))));
  dec       = (fun s ->
    if Seq.length s >= 1 then Inr (U8.v (Seq.index s 0), 1)
    else Inl (mk_decode_error UnexpectedEndOfInput 0));
  wfcv      = (fun v -> 0 <= v && v < 256);
  wfcv_prop = (fun _ -> True);
  rest_cond = (fun _ _ -> True);
  roundtrip = (fun v r ->
    // wfcv v ensures 0 <= v < 256, so v%256 == v and nat_of_int v == v
    let b = U8.uint_to_t (nat_of_int (v % 256)) in
    assert (U8.v b == v);
    lemma_create_len 1 b;
    lemma_index_app1 (Seq.create 1 b) r 0;
    lemma_index_create 1 b 0;
    ());
  dec_err_bound = (fun s -> ());
  dec_consumed_bound = (fun s -> ());
}
#pop-options

(** Combinator 8: word16be — big-endian 16-bit integer.

    Encodes as 2 bytes (hi, lo).  wfcv: [0 <= v < 65536].
    Decoder: [hi*256 + lo]. *)

#push-options "--z3rlimit 20"
let word16be : codec int = {
  enc       = (fun v ->
    let n' = v % 65536 in
    Seq.append (Seq.create 1 (U8.uint_to_t (nat_of_int (n'/256))))
               (Seq.create 1 (U8.uint_to_t (nat_of_int (n'%256)))));
  dec       = (fun s ->
    if Seq.length s >= 2 then
      let hi = U8.v (Seq.index s 0) in let lo = U8.v (Seq.index s 1) in
      Inr (hi*256+lo, 2)
    else Inl (mk_decode_error UnexpectedEndOfInput (Seq.length s)));
  wfcv      = (fun v -> 0 <= v && v < 65536);
  wfcv_prop = (fun _ -> True);
  rest_cond = (fun _ _ -> True);
  roundtrip = (fun v r ->
    // wfcv: 0 <= v < 65536, so v%65536 == v
    let n' = v in
    let hi = nat_of_int (n'/256) in
    let lo = nat_of_int (n'%256) in
    assert (hi < 256);
    assert (lo < 256);
    let enc_v = Seq.append (Seq.create 1 (U8.uint_to_t hi))
                           (Seq.create 1 (U8.uint_to_t lo)) in
    let combined = enc_v `Seq.append` r in
    Seq.lemma_len_append enc_v r;
    lemma_index_app1 enc_v r 0;
    lemma_index_app1 enc_v r 1;
    lemma_index_create 1 (U8.uint_to_t hi) 0;
    lemma_index_create 1 (U8.uint_to_t lo) 0;
    ());
  dec_err_bound = (fun s -> ());
  dec_consumed_bound = (fun s -> ());
}
#pop-options

(** 9. word16le *)

#push-options "--z3rlimit 20"
let word16le : codec int = {
  enc       = (fun v ->
    let n' = v % 65536 in
    Seq.append (Seq.create 1 (U8.uint_to_t (nat_of_int (n'%256))))
               (Seq.create 1 (U8.uint_to_t (nat_of_int (n'/256)))));
  dec       = (fun s ->
    if Seq.length s >= 2 then
      let lo = U8.v (Seq.index s 0) in let hi = U8.v (Seq.index s 1) in
      Inr (lo+hi*256, 2)
    else Inl (mk_decode_error UnexpectedEndOfInput (Seq.length s)));
  wfcv      = (fun v -> 0 <= v && v < 65536);
  wfcv_prop = (fun _ -> True);
  rest_cond = (fun _ _ -> True);
  roundtrip = (fun v r ->
    let n' = v in
    let lo = nat_of_int (n'%256) in
    let hi = nat_of_int (n'/256) in
    assert (hi < 256);
    assert (lo < 256);
    let enc_v = Seq.append (Seq.create 1 (U8.uint_to_t lo))
                           (Seq.create 1 (U8.uint_to_t hi)) in
    let combined = enc_v `Seq.append` r in
    Seq.lemma_len_append enc_v r;
    lemma_index_app1 enc_v r 0;
    lemma_index_app1 enc_v r 1;
    lemma_index_create 1 (U8.uint_to_t lo) 0;
    lemma_index_create 1 (U8.uint_to_t hi) 0;
    ());
  dec_err_bound = (fun s -> ());
  dec_consumed_bound = (fun s -> ());
}
#pop-options

(** 10. word32be *)

#push-options "--z3rlimit 15"
let word32be : codec int = {
  enc       = (fun v ->
    let n' = v % 4294967296 in
    Seq.append (Seq.create 1 (U8.uint_to_t (nat_of_int (n'/16777216))))
    (Seq.append (Seq.create 1 (U8.uint_to_t (nat_of_int ((n'/65536)%256))))
    (Seq.append (Seq.create 1 (U8.uint_to_t (nat_of_int ((n'/256)%256))))
                (Seq.create 1 (U8.uint_to_t (nat_of_int (n'%256)))))));
  dec       = (fun s ->
    if Seq.length s >= 4 then
      let b0 = U8.v (Seq.index s 0) in let b1 = U8.v (Seq.index s 1) in
      let b2 = U8.v (Seq.index s 2) in let b3 = U8.v (Seq.index s 3) in
      Inr (b0*16777216 + b1*65536 + b2*256 + b3, 4)
    else Inl (mk_decode_error UnexpectedEndOfInput (Seq.length s)));
  wfcv      = (fun v -> 0 <= v && v < 4294967296);
  wfcv_prop = (fun _ -> True);
  rest_cond = (fun _ _ -> True);
  roundtrip = (fun v r ->
    // wfcv: 0 <= v < 2^32, so v%4294967296 == v
    let n' = v in
    let b0 = U8.uint_to_t (nat_of_int (n'/16777216)) in
    let b1 = U8.uint_to_t (nat_of_int ((n'/65536)%256)) in
    let b2 = U8.uint_to_t (nat_of_int ((n'/256)%256)) in
    let b3 = U8.uint_to_t (nat_of_int (n'%256)) in
    let enc_v = Seq.append
                (Seq.append (Seq.append (Seq.create 1 b0) (Seq.create 1 b1))
                            (Seq.create 1 b2))
                (Seq.create 1 b3) in
    lemma_word32_enc_bytes b0 b1 b2 b3 enc_v;
    let combined = enc_v `Seq.append` r in
    Seq.lemma_len_append enc_v r;
    lemma_index_app1 enc_v r 0;
    lemma_index_app1 enc_v r 1;
    lemma_index_app1 enc_v r 2;
    lemma_index_app1 enc_v r 3;
    // Arithmetic: n' = b0*16777216 + b1*65536 + b2*256 + b3
    lemma_div_mod n' 16777216;
    lemma_div_mod (n' / 65536) 256;
    lemma_div_mod (n' / 256) 256;
    ());
  dec_err_bound = (fun s -> ());
  dec_consumed_bound = (fun s -> ());
}
#pop-options

(** 11. word32le *)

#push-options "--z3rlimit 15"
let word32le : codec int = {
  enc       = (fun v ->
    let n' = v % 4294967296 in
    Seq.append (Seq.create 1 (U8.uint_to_t (nat_of_int (n'%256))))
    (Seq.append (Seq.create 1 (U8.uint_to_t (nat_of_int ((n'/256)%256))))
    (Seq.append (Seq.create 1 (U8.uint_to_t (nat_of_int ((n'/65536)%256))))
                (Seq.create 1 (U8.uint_to_t (nat_of_int (n'/16777216)))))));
  dec       = (fun s ->
    if Seq.length s >= 4 then
      let b0 = U8.v (Seq.index s 0) in let b1 = U8.v (Seq.index s 1) in
      let b2 = U8.v (Seq.index s 2) in let b3 = U8.v (Seq.index s 3) in
      Inr (b0 + b1*256 + b2*65536 + b3*16777216, 4)
    else Inl (mk_decode_error UnexpectedEndOfInput (Seq.length s)));
  wfcv      = (fun v -> 0 <= v && v < 4294967296);
  wfcv_prop = (fun _ -> True);
  rest_cond = (fun _ _ -> True);
  roundtrip = (fun v r ->
    let n' = v in
    let b0 = U8.uint_to_t (nat_of_int (n'%256)) in
    let b1 = U8.uint_to_t (nat_of_int ((n'/256)%256)) in
    let b2 = U8.uint_to_t (nat_of_int ((n'/65536)%256)) in
    let b3 = U8.uint_to_t (nat_of_int (n'/16777216)) in
    let enc_v = Seq.append
                (Seq.append (Seq.append (Seq.create 1 b0) (Seq.create 1 b1))
                            (Seq.create 1 b2))
                (Seq.create 1 b3) in
    lemma_word32_enc_bytes b0 b1 b2 b3 enc_v;
    let combined = enc_v `Seq.append` r in
    Seq.lemma_len_append enc_v r;
    lemma_index_app1 enc_v r 0;
    lemma_index_app1 enc_v r 1;
    lemma_index_app1 enc_v r 2;
    lemma_index_app1 enc_v r 3;
    // Arithmetic: n' = b0 + b1*256 + b2*65536 + b3*16777216
    lemma_div_mod n' 256;
    lemma_div_mod (n' / 256) 256;
    lemma_div_mod (n' / 65536) 256;
    ());
  dec_err_bound = (fun s -> ());
  dec_consumed_bound = (fun s -> ());
}
#pop-options

(** varint nbytes helper *)

(** nbytes_of_varint: single source of truth for varint encoding length. *)
(** Thresholds: 2^7, 2^14, 2^21, 2^28, 2^35. *)
(** Used by varint.enc, lemma_varint_encode_decode_roundtrip, and encode_varint. *)
(**  *)
(** For values n >= 2^35, returns 6. The varint combinator's wfcv restricts *)
(** to v < 2^35, so the 6-byte case is unreachable for valid codec values. *)
(** lemma_nbytes_of_varint_bound proves this. *)
let nbytes_of_varint (n: int) : nat =
  if n < 128 then 1
  else if n < 16384 then 2
  else if n < 2097152 then 3
  else if n < 268435456 then 4
  else if n < 34359738368 then 5
  else 6

(** lemma_nbytes_of_varint_bound: for values in varint range, nbytes <= 5. *)
(** Explicit 5-range case split — no SMT-only quantifier reasoning. *)
let lemma_nbytes_of_varint_bound (n: int) : Lemma
  (requires 0 <= n /\ n < 34359738368)
  (ensures nbytes_of_varint n <= 5)
  = if n < 128 then ()
    else if n < 16384 then ()
    else if n < 2097152 then ()
    else if n < 268435456 then ()
    else ()

(** lemma_nbytes_of_varint_correct: encoded length matches nbytes_of_varint. *)
#push-options "--z3rlimit 80"
let lemma_nbytes_of_varint_correct (n: int) : Lemma
  (requires 0 <= n /\ n < 34359738368)
  (ensures
    List.Tot.length (varint_encode_go (nbytes_of_varint n) 0 (nat_of_int n) []) == nbytes_of_varint n)
  = let nb = nbytes_of_varint n in
    let v = nat_of_int n in
    lemma_nbytes_of_varint_bound n;
    assert_norm (pow2 7 = 128);
    assert_norm (pow2 14 = 16384);
    assert_norm (pow2 21 = 2097152);
    assert_norm (pow2 28 = 268435456);
    if n < 128 then ()
    else if n < 16384 then (
      assert (varint_encode_go 2 0 v [] ==
        rev (U8.uint_to_t (v / 128) :: [U8.uint_to_t (v % 128 + 128)]));
      assert (List.Tot.length (varint_encode_go 2 0 v []) == 2)
    )
    else if n < 2097152 then (
      let n1 = v / 128 in
      assert (varint_encode_go 3 0 v [] ==
        rev [U8.uint_to_t (n1 / 128); U8.uint_to_t (n1 % 128 + 128); U8.uint_to_t (v % 128 + 128)]);
      assert (List.Tot.length (varint_encode_go 3 0 v []) == 3)
    )
    else if n < 268435456 then (
      let n1 = v / 128 in
      let n2 = n1 / 128 in
      assert (varint_encode_go 4 0 v [] ==
        rev [U8.uint_to_t (n2 / 128); U8.uint_to_t (n2 % 128 + 128);
             U8.uint_to_t (n1 % 128 + 128); U8.uint_to_t (v % 128 + 128)]);
      assert (List.Tot.length (varint_encode_go 4 0 v []) == 4)
    )
    else (
      let n1 = v / 128 in
      let n2 = n1 / 128 in
      let n3 = n2 / 128 in
      assert (varint_encode_go 5 0 v [] ==
        rev [U8.uint_to_t (n3 / 128); U8.uint_to_t (n3 % 128 + 128);
             U8.uint_to_t (n2 % 128 + 128); U8.uint_to_t (n1 % 128 + 128);
             U8.uint_to_t (v % 128 + 128)]);
      assert (List.Tot.length (varint_encode_go 5 0 v []) == 5)
    )
#pop-options

(** Combinator 12: varint — variable-length integer, unsigned LEB128 encoding.

    Encodes values in [0, 2^35) as 1-5 bytes.  wfcv: [0 <= v < 34359738368].
    Decoder uses 10-byte fuel limit (well beyond the 5-byte maximum).

    Encoding length is determined by [nbytes_of_varint] — the single source
    of truth.  Per-nbytes roundtrip lemmas ([lemma_varint_enc_dec_{1..5}byte])
    prove each length case.  Five arithmetic lemmas ([lemma_varint_{2..5}byte_arithmetic])
    provide the integer decomposition identities.

    C extraction: Low* layer provides a U32.t-bounded encoder with
    [varint_encode_pred] byte-level specification. *)

(** NOTE: digits_to_int accumulator and varint_decode_go value parameter *)
(** use unbounded F* `int`. C extraction will need bounds checks *)
(** or fixed-width accumulators to avoid overflow. *)

(** Per-nbytes encode→decode lemmas. Each characterizes the roundtrip for *)
(** a fixed encoding length. The arithmetic identities are extracted into *)
(** standalone lemmas (lemma_varint_*byte_arithmetic) so the roundtrip lemmas *)
(** only need to connect encode/decode byte values, not re-prove the *)
(** lemma_div_mod chain each time. *)

(** Arithmetic identity: n = 128*(n/128) + n%128. *)
(** Uses direct-n ensures (no intermediate bindings) for caller compatibility. *)
let lemma_varint_2byte_arithmetic (n: nat) : Lemma
  (requires 128 <= n /\ n < 16384)
  (ensures
    n / 128 < 128 /\
    n == 128 * (n / 128) + n % 128)
  = lemma_div_mod n 128;
    assert (n / 128 < 128)

(** Arithmetic identity: n = 128^2*(n/16384) + 128*((n/128)%128) + n%128. *)
(** Uses direct-n ensures (no intermediate bindings) for caller compatibility. *)
let lemma_varint_3byte_arithmetic (n: nat) : Lemma
  (requires 16384 <= n /\ n < 2097152)
  (ensures
    n / 16384 < 128 /\
    n == 128 * 128 * (n / 16384) + 128 * ((n / 128) % 128) + n % 128)
  = lemma_div_mod n 128;
    let n1 = n / 128 in
    lemma_div_mod n1 128;
    assert (n1 / 128 < 128);
    assert (n1 / 128 == n / 16384);
    assert (n == 128 * 128 * (n / 16384) + 128 * ((n / 128) % 128) + n % 128)

(** Arithmetic identity: n = 128^3*(n/2097152) + 128^2*((n/16384)%128) + 128*((n/128)%128) + n%128. *)
(** Uses direct-n ensures (no intermediate bindings) for caller compatibility. *)
let lemma_varint_4byte_arithmetic (n: nat) : Lemma
  (requires 2097152 <= n /\ n < 268435456)
  (ensures
    n / 2097152 < 128 /\
    n == 128 * 128 * 128 * (n / 2097152) + 128 * 128 * ((n / 16384) % 128) + 128 * ((n / 128) % 128) + n % 128)
  = lemma_div_mod n 128;
    let n1 = n / 128 in
    lemma_div_mod n1 128;
    let n2 = n1 / 128 in
    lemma_div_mod n2 128;
    assert (n2 / 128 < 128);
    assert (n1 == n / 128);
    assert (n2 == n / 16384);
    assert (n2 / 128 == n / 2097152);
    assert (n == 128 * 128 * 128 * (n / 2097152) + 128 * 128 * ((n / 16384) % 128) + 128 * ((n / 128) % 128) + n % 128)

(** Arithmetic identity: n = 128^4*(n/268435456) + 128^3*((n/2097152)%128) + 128^2*((n/16384)%128) + 128*((n/128)%128) + n%128. *)
(** Expressed directly in terms of n (no intermediate bindings) so callers *)
(** are not forced to replicate the n1..n4 naming scheme. *)
#push-options "--z3rlimit 40"
let lemma_varint_5byte_arithmetic (n: nat) : Lemma
  (requires 268435456 <= n /\ n < 34359738368)
  (ensures
    n / 268435456 < 128 /\
    n == 128 * 128 * 128 * 128 * (n / 268435456) + 128 * 128 * 128 * ((n / 2097152) % 128) + 128 * 128 * ((n / 16384) % 128) + 128 * ((n / 128) % 128) + n % 128)
  = lemma_div_mod n 128;
    let n1 = n / 128 in
    lemma_div_mod n1 128;
    let n2 = n1 / 128 in
    lemma_div_mod n2 128;
    let n3 = n2 / 128 in
    lemma_div_mod n3 128;
    let n4 = n3 / 128 in
    assert (n1 == n / 128);
    assert (n2 == n / 16384);
    assert (n3 == n / 2097152);
    assert (n4 == n / 268435456);
    assert (n4 < 128);
    assert (n == 128 * 128 * 128 * 128 * n4 + 128 * 128 * 128 * (n3 % 128) + 128 * 128 * (n2 % 128) + 128 * (n1 % 128) + n % 128)
#pop-options

#push-options "--z3rlimit 10"
let lemma_varint_enc_dec_1byte (n: nat) (r: byte_seq) : Lemma
  (requires n < 128)
  (ensures (
    let enc_list = varint_encode_go 1 0 n [] in
    varint_decode_go (seq_of_list enc_list `Seq.append` r) 10 0 0 0
    == Inr (n, 1)))
  = lemma_nbytes_of_varint_correct n;
    assert (U8.v (U8.uint_to_t n) == n)
#pop-options

#push-options "--z3rlimit 20"
let lemma_varint_enc_dec_2byte (n: nat) (r: byte_seq) : Lemma
  (requires 128 <= n /\ n < 16384)
  (ensures (
    let enc_list = varint_encode_go 2 0 n [] in
    varint_decode_go (seq_of_list enc_list `Seq.append` r) 10 0 0 0
    == Inr (n, 2)))
  = lemma_nbytes_of_varint_correct n;
    lemma_varint_2byte_arithmetic n;
    let enc_list = varint_encode_go 2 0 n [] in
    let enc_seq = seq_of_list enc_list `Seq.append` r in
    let b0 = Seq.index enc_seq 0 in
    let b1 = Seq.index enc_seq 1 in
    assert (U8.v b0 == n % 128 + 128);
    assert (U8.v b1 == n / 128);
    assert (U8.v b0 >= 128);
    assert (U8.v b0 % 128 == n % 128);
    assert (U8.v b1 < 128);
    assert (n % 128 + (n / 128) * 128 == n)
#pop-options

#push-options "--z3rlimit 20"
let lemma_varint_enc_dec_3byte (n: nat) (r: byte_seq) : Lemma
  (requires 16384 <= n /\ n < 2097152)
  (ensures (
    let enc_list = varint_encode_go 3 0 n [] in
    varint_decode_go (seq_of_list enc_list `Seq.append` r) 10 0 0 0
    == Inr (n, 3)))
  = lemma_nbytes_of_varint_correct n;
    lemma_varint_3byte_arithmetic n;
    let n1 = n / 128 in
    let enc_list = varint_encode_go 3 0 n [] in
    let enc_seq = seq_of_list enc_list `Seq.append` r in
    let b0 = Seq.index enc_seq 0 in
    let b1 = Seq.index enc_seq 1 in
    let b2 = Seq.index enc_seq 2 in
    assert (U8.v b0 == n % 128 + 128);
    assert (U8.v b1 == n1 % 128 + 128);
    assert (U8.v b2 == n1 / 128);
    assert (U8.v b0 % 128 == n % 128);
    assert (U8.v b1 % 128 == n1 % 128);
    assert (U8.v b2 < 128)
#pop-options

#push-options "--z3rlimit 20"
let lemma_varint_enc_dec_4byte (n: nat) (r: byte_seq) : Lemma
  (requires 2097152 <= n /\ n < 268435456)
  (ensures (
    let enc_list = varint_encode_go 4 0 n [] in
    varint_decode_go (seq_of_list enc_list `Seq.append` r) 10 0 0 0
    == Inr (n, 4)))
  = lemma_nbytes_of_varint_correct n;
    lemma_varint_4byte_arithmetic n;
    let n1 = n / 128 in
    let n2 = n1 / 128 in
    assert (n1 == n / 128);
    assert (n2 == n / 16384);
    assert (n2 % 128 == (n / 16384) % 128);
    assert (n2 / 128 == n / 2097152);
    let enc_list = varint_encode_go 4 0 n [] in
    let enc_seq = seq_of_list enc_list `Seq.append` r in
    let b0 = Seq.index enc_seq 0 in
    let b1 = Seq.index enc_seq 1 in
    let b2 = Seq.index enc_seq 2 in
    let b3 = Seq.index enc_seq 3 in
    assert (U8.v b0 == n % 128 + 128);
    assert (U8.v b1 == n1 % 128 + 128);
    assert (U8.v b2 == n2 % 128 + 128);
    assert (U8.v b3 == n2 / 128);
    assert (U8.v b0 % 128 == n % 128);
    assert (U8.v b1 % 128 == n1 % 128);
    assert (U8.v b2 % 128 == n2 % 128);
    assert (U8.v b3 < 128)
#pop-options

#push-options "--z3rlimit 80"
let lemma_varint_enc_dec_5byte (n: nat) (r: byte_seq) : Lemma
  (requires 268435456 <= n /\ n < 34359738368)
  (ensures (
    let enc_list = varint_encode_go 5 0 n [] in
    varint_decode_go (seq_of_list enc_list `Seq.append` r) 10 0 0 0
    == Inr (n, 5)))
  = lemma_nbytes_of_varint_correct n;
    lemma_varint_5byte_arithmetic n;
    assert_norm (pow2 7 == 128);
    assert_norm (pow2 14 == 16384);
    assert_norm (pow2 21 == 2097152);
    assert_norm (pow2 28 == 268435456);
    let enc_list = varint_encode_go 5 0 n [] in
    let enc_seq = seq_of_list enc_list `Seq.append` r in
    let b0 = Seq.index enc_seq 0 in
    let b1 = Seq.index enc_seq 1 in
    let b2 = Seq.index enc_seq 2 in
    let b3 = Seq.index enc_seq 3 in
    let b4 = Seq.index enc_seq 4 in
    // encode bytes: b0..b3 continuation (hi bit set), b4 terminal
    assert (U8.v b0 == n % 128 + 128);
    assert (U8.v b0 >= 128);
    assert (U8.v b1 == (n / 128) % 128 + 128);
    assert (U8.v b1 >= 128);
    assert (U8.v b2 == (n / 16384) % 128 + 128);
    assert (U8.v b2 >= 128);
    assert (U8.v b3 == (n / 2097152) % 128 + 128);
    assert (U8.v b3 >= 128);
    assert (U8.v b4 == n / 268435456);
    assert (U8.v b4 < 128);
    // decode trace: strip hi bits; lemma_varint_5byte_arithmetic proves
    // n decomposes to 128^4*b4 + 128^3*(b3%128) + ... + (b0%128).
    // All terms use direct-n arithmetic (no intermediate n1..n4), so no
    // bridging assert is needed.
    assert (U8.v b0 % 128 == n % 128);
    assert (U8.v b1 % 128 == (n / 128) % 128);
    assert (U8.v b2 % 128 == (n / 16384) % 128);
    assert (U8.v b3 % 128 == (n / 2097152) % 128);
    ()
#pop-options

(** Structural lemma: varint encode → decode roundtrip on [0, 2^35). *)
(** Proved by explicit 5-range case analysis, each calling a per-nbytes lemma *)
(** that uses lemma_div_mod for the arithmetic identity. *)

#push-options "--z3rlimit 40"
let lemma_varint_encode_decode_roundtrip (v: int) (r: byte_seq) : Lemma
  (requires 0 <= v /\ v < 34359738368)
  (ensures
    varint_decode_go
      (Seq.append (seq_of_list (varint_encode_go
        (nat_of_int (nbytes_of_varint v)) 0 (nat_of_int v) [])) r) 10 0 0 0
    == Inr (v, List.Tot.length (varint_encode_go
        (nat_of_int (nbytes_of_varint v)) 0 (nat_of_int v) [])))
  =
  assert_norm (pow2 0 = 1);
  assert_norm (pow2 7 = 128);
  assert_norm (pow2 14 = 16384);
  assert_norm (pow2 21 = 2097152);
  assert_norm (pow2 28 = 268435456);
  let n = nat_of_int v in
  lemma_nbytes_of_varint_correct v;
  if v < 128 then begin
    assert (v < 128);
    lemma_varint_enc_dec_1byte n r
  end else if v < 16384 then begin
    assert (128 <= v && v < 16384);
    lemma_varint_enc_dec_2byte n r
  end else if v < 2097152 then begin
    assert (16384 <= v && v < 2097152);
    lemma_varint_enc_dec_3byte n r
  end else if v < 268435456 then begin
    assert (2097152 <= v && v < 268435456);
    lemma_varint_enc_dec_4byte n r
  end else begin
    assert (268435456 <= v && v < 34359738368);
    lemma_varint_enc_dec_5byte n r
  end
#pop-options

#push-options "--z3rlimit 50"
let varint : codec int = {
  enc       = (fun v ->
    let n = v in
    seq_of_list (varint_encode_go (nat_of_int (nbytes_of_varint n)) 0 (nat_of_int n) []));
  dec       = (fun s -> varint_decode_go s 10 0 0 0);
  (* wfcv range: [0, 2^35).  Low* bridge (Data.Codec.Low) uses U32.t values
     limited to [0, 2^32).  Pure values in [2^32, 2^35) are valid per this
     codec but have no Low* encode/decode path.  This is intentional for
     typical protocols which only need 32-bit values over the wire; the headroom
     ensures all valid U32 values fit comfortably in a 5-byte varint. *)
  wfcv      = (fun v -> 0 <= v && v < 34359738368);
  wfcv_prop = (fun _ -> True);
  rest_cond = (fun _ _ -> True);
  roundtrip = (fun v r ->
    lemma_varint_encode_decode_roundtrip v r;
    ());
  dec_err_bound = (fun s ->
    match varint_decode_go s 10 0 0 0 with
    | Inl err -> lemma_varint_decode_inl_len_bound s 10 0 0 0 err
    | _ -> ());
  dec_consumed_bound = (fun s ->
    lemma_varint_decode_consumed_le_len s 10 0 0 0);
}
#pop-options

(** Combinator 13: digits_to_int — parse a digit string to integer.

    @param n Maximum number of digits to read.
    @param f Validation predicate on the parsed integer.
    Encodes as [seq_of_list (digits_encode (nat_of_int v))].
    wfcv: [pred v] and encoding length ≤ [n].
    rest_cond: suffix does not start with a digit.
    Fails with [ExpectedPredicate] if input doesn't start with a digit. *)

#push-options "--z3rlimit 80"
let digits_to_int (max_len: pos) (f: int -> bool) : codec int = {
  enc       = (fun v -> seq_of_list (digits_encode (nat_of_int v)));
  dec       = (fun s -> digits_to_int_decode max_len f s);
  wfcv      = (fun v ->
    f v && v >= 0 &&
    List.Tot.length (digits_encode (nat_of_int v)) <= max_len);
  wfcv_prop = (fun _ -> True);
  rest_cond = (fun v r ->
    let n_val = nat_of_int v in
    List.Tot.length (digits_encode n_val) = max_len \/
    Seq.length r = 0 \/
    (Seq.length r > 0 /\ not (is_digit (Seq.index r 0))));
  roundtrip = (fun v r ->
    let n_val = nat_of_int v in
    lemma_acc_digits_encode_helper n_val;
    lemma_digits_encode_all_digits_helper n_val;
    lemma_digits_decode_encode_roundtrip f max_len n_val r;
    ());
  dec_err_bound = (fun s ->
    lemma_digits_decode_go_len_bound f s max_len 0 0);
  (* dec_consumed_bound: Inr-only lemma suffices since ensures clause only
     constrains the Inr case. For a unified Inr+Inl lemma, see
     lemma_digits_decode_go_len_bound (used in dec_err_bound above).
     The split is deliberate — each field calls the narrowest sufficient lemma. *)
  dec_consumed_bound = (fun s ->
    match digits_to_int_decode max_len f s with
    | Inr (v, n) ->
        lemma_digits_decode_inr_len_bound f s max_len 0 0 v n
    | _ -> ());
}
#pop-options

(** Lemma: [digits_to_int max_len f].wfcv v expands to the conjunction.
    Definitional within this module. *)
let lemma_digits_to_int_wfcv_eq (max_len: pos) (f: int -> bool) (v: int) : Lemma
  ((digits_to_int max_len f).wfcv v ==
   (f v && v >= 0 &&
    List.Tot.length (digits_encode (nat_of_int v)) <= max_len))
  = ()

(** Lemma: [digits_to_int max_len f].rest_cond v r expands to the three-disjunct
    suffix condition.  First disjunct uses [max_len] (the digit-count parameter),
    not the value — fixed from shadowing bug in earlier versions (fstar-proofs §17).
    Definitional within this module. *)
let lemma_digits_to_int_rest_cond_eq (max_len: pos) (f: int -> bool) (v: int) (r: byte_seq) : Lemma
  ((digits_to_int max_len f).rest_cond v r ==
   (let n_val = nat_of_int v in
    List.Tot.length (digits_encode n_val) = max_len \/
    Seq.length r = 0 \/
    (Seq.length r > 0 /\ not (is_digit (Seq.index r 0)))))
  = ()

(** Combinator 14: custom — user-supplied codec with caller-provided proofs.

    @param d Decoder function.
    @param e Encoder function.
    @param wfcv_custom Well-formed-value guard.
    @param wfcv_prop_custom Well-formed-value proposition.
    @param rest_cond_custom Suffix condition.
    @param roundtrip_custom Roundtrip lemma.
    @param dec_err_bound_custom Error position bound lemma.
    @param dec_consumed_bound_custom Consumed bytes bound lemma.

    Zero admits.  The caller must supply all 6 proof functions.
    This is the verified extension point — no escape hatch.
    The decoder takes [byte_seq] (not [list byte]) to avoid
    [seq_to_list] overhead. *)
#push-options "--z3rlimit 20"
let custom (#a:Type)
  (d: byte_seq -> Tot (decode_result a))
  (e: a -> Tot byte_seq)
  (wfcv_custom: a -> Tot bool)
  (wfcv_prop_custom: a -> Tot prop)
  (rest_cond_custom: a -> byte_seq -> Tot prop)
  (roundtrip_custom: (v: a) -> (r: byte_seq) -> Lemma
    (requires wfcv_custom v /\ wfcv_prop_custom v /\ rest_cond_custom v r)
    (ensures d (e v `Seq.append` r) == Inr (v, Seq.length (e v))))
  (dec_err_bound_custom: (s: byte_seq) -> Lemma
    (ensures (match d s with
              | Inl err -> err.err_pos <= Seq.length s
              | _ -> True)))
  (dec_consumed_bound_custom: (s: byte_seq) -> Lemma
    (ensures (match d s with
              | Inr (_, n) -> n <= Seq.length s
              | _ -> True)))
  : codec a = {
  enc       = e;
  dec       = d;
  wfcv      = wfcv_custom;
  wfcv_prop = wfcv_prop_custom;
  rest_cond = rest_cond_custom;
  roundtrip = (fun v r ->
    assert (wfcv_custom v);
    assert (wfcv_prop_custom v);
    assert (rest_cond_custom v r);
    roundtrip_custom v r;
    ());
  dec_err_bound = (fun s -> dec_err_bound_custom s);
  dec_consumed_bound = (fun s -> dec_consumed_bound_custom s);
}
#pop-options

(** 15. product *)

(** Product decoder error position bound proof. *)
(** Bridges c1.dec_err_bound and c2.dec_err_bound across the slice offset. *)
(** c1.dec_consumed_bound proves that n1 <= Seq.length s when c1.dec *)
(** succeeds, so the "n1 > Seq.length s" branch is unreachable. *)
#push-options "--z3rlimit 40"
let lemma_product_dec_err_bound (#a #b:Type) (c1: codec a) (c2: codec b) (s: byte_seq) : Lemma
  (ensures (match c1.dec s with
            | Inl err -> err.err_pos <= Seq.length s
            | Inr (_, n1) ->
                if n1 <= Seq.length s then
                (match c2.dec (Seq.slice s n1 (Seq.length s)) with
                | Inl err -> err.err_pos + n1 <= Seq.length s
                | _ -> True)
                else True))
  = c1.dec_err_bound s;
    c1.dec_consumed_bound s;
    match c1.dec s with
    | Inl _ -> ()
    | Inr (_, n1) ->
        assert (n1 <= Seq.length s);
        c2.dec_err_bound (Seq.slice s n1 (Seq.length s))
#pop-options

(** Product decoder n count bound proof. *)
(** Bridges c1.dec_consumed_bound and c2.dec_consumed_bound across the slice. *)
(** c1.dec_consumed_bound proves that n1 <= Seq.length s when c1.dec *)
(** succeeds, so the "n1 > Seq.length s" branch is unreachable. *)
#push-options "--z3rlimit 40"
let lemma_product_dec_consumed_bound (#a #b:Type) (c1: codec a) (c2: codec b) (s: byte_seq) : Lemma
  (ensures (match c1.dec s with
            | Inl _ -> True
            | Inr (_, n1) ->
                if n1 <= Seq.length s then
                (match c2.dec (Seq.slice s n1 (Seq.length s)) with
                | Inr (_, n2) -> n1 + n2 <= Seq.length s
                | _ -> True)
                else True))
  = c1.dec_consumed_bound s;
    match c1.dec s with
    | Inl _ -> ()
    | Inr (_, n1) ->
        assert (n1 <= Seq.length s);
        c2.dec_consumed_bound (Seq.slice s n1 (Seq.length s))
#pop-options

(** Combinator 15: product — sequential pair.

    @param c1 First codec, decoding ['a] from the prefix.
    @param c2 Second codec, decoding ['b] from the remaining suffix.
    Encodes [(v1, v2)] as [c1.enc v1 ++ c2.enc v2].
    Decodes c1 then c2 on the suffix; errors from c2 have positions
    shifted by the bytes c1 n.
    wfcv: [c1.wfcv v1 && c2.wfcv v2].
    rest_cond: chains both sub-conditions inductively.
    Called [product] because it forms a monoidal product (not a tuple
    constructor — the F* tuple type is written [a & b]). *)

#push-options "--z3rlimit 80"
let product (#a #b:Type) (c1: codec a) (c2: codec b) : codec (a & b) = {
  enc       = (fun (v1, v2) -> Seq.append (c1.enc v1) (c2.enc v2));
  dec       = (fun s ->
    match c1.dec s with
    | Inl err -> Inl err
    | Inr (v1, n1) ->
      if n1 > Seq.length s
      then Inl (mk_decode_error UnexpectedEndOfInput (Seq.length s))
      else match c2.dec (Seq.slice s n1 (Seq.length s)) with
      | Inl err -> Inl ({err with err_pos = err.err_pos + n1})
      | Inr (v2, n2) -> Inr ((v1, v2), n1 + n2));
  wfcv      = (fun (v1, v2) -> c1.wfcv v1 && c2.wfcv v2);
  wfcv_prop = (fun (v1, v2) -> c1.wfcv_prop v1 /\ c2.wfcv_prop v2);
  (* rest_cond chains inductively: c1's suffix includes c2's encoding,
     so both sub-conditions hold for the nested structure.  This is
     structurally correct for arbitrary product nesting — each level
     adds its element's encoding to the prefix of remaining r. *)
  rest_cond = (fun (v1, v2) r ->
    c1.rest_cond v1 (c2.enc v2 `Seq.append` r) /\ c2.rest_cond v2 r);
  roundtrip = (fun (v1, v2) r ->
    assert (c1.wfcv v1);
    assert (c2.wfcv v2);
    assert (c1.wfcv_prop v1);
    assert (c2.wfcv_prop v2);
    let enc1 = c1.enc v1 in
    let enc2 = c2.enc v2 in
    assert (c1.rest_cond v1 (enc2 `Seq.append` r));
    assert (c2.rest_cond v2 r);
    c1.roundtrip v1 (enc2 `Seq.append` r);
    Seq.append_assoc enc1 enc2 r;
    lemma_slice_after_prefix enc1 (enc2 `Seq.append` r);
    c2.roundtrip v2 r;
    ());
  dec_err_bound = (fun s -> lemma_product_dec_err_bound c1 c2 s);
  dec_consumed_bound = (fun s -> lemma_product_dec_consumed_bound c1 c2 s);
}
#pop-options

(** 16. sum *)

#push-options "--z3rlimit 40"
(** cons-append interchange: (x :: s1) ++ s2 == x :: (s1 ++ s2) *)
let lemma_seq_cons_append (#a:Type) (x: a) (s1 s2: Seq.seq a) : Lemma
  (ensures Seq.cons x s1 `Seq.append` s2 == Seq.cons x (s1 `Seq.append` s2))
  [SMTPat (Seq.cons x s1 `Seq.append` s2)]
  = Seq.lemma_eq_intro (Seq.cons x s1 `Seq.append` s2) (Seq.cons x (s1 `Seq.append` s2))
#pop-options

(** Sum decoder error position bound proof. *)
(** Bridges c1.dec_err_bound and c2.dec_err_bound across the +1 tag offset. *)
(** Written against the inline decoder logic (not (sum c1 c2).dec) *)
(** to avoid forward-reference issues. *)
(** When s is empty: proves 0 <= Seq.length s (trivially true from nat). *)
#push-options "--z3rlimit 20"
let lemma_sum_dec_err_bound (#a #b:Type) (c1: codec a) (c2: codec b) (s: byte_seq) : Lemma
  (ensures (if Seq.length s < 1 then 0 <= Seq.length s
            else let tag = Seq.index s 0 in
              let r = Seq.slice s 1 (Seq.length s) in
              if tag = 0x00uy then
                (match c1.dec r with
                 | Inl err -> err.err_pos + 1 <= Seq.length s
                 | _ -> True)
              else if tag = 0x01uy then
                (match c2.dec r with
                 | Inl err -> err.err_pos + 1 <= Seq.length s
                 | _ -> True)
              else True))
  = if Seq.length s < 1 then ()
    else begin
      let r = Seq.slice s 1 (Seq.length s) in
      let tag = Seq.index s 0 in
      if tag = 0x00uy then c1.dec_err_bound r
      else if tag = 0x01uy then c2.dec_err_bound r
      else ()
    end
#pop-options

(** Sum decoder n count bound proof. *)
(** Bridges c1.dec_consumed_bound and c2.dec_consumed_bound across the +1 tag offset. *)
#push-options "--z3rlimit 20"
let lemma_sum_dec_consumed_bound (#a #b:Type) (c1: codec a) (c2: codec b) (s: byte_seq) : Lemma
  (ensures (if Seq.length s < 1 then True
            else let tag = Seq.index s 0 in
              let r = Seq.slice s 1 (Seq.length s) in
              if tag = 0x00uy then
                (match c1.dec r with
                 | Inr (_, n1) -> 1 + n1 <= Seq.length s
                 | _ -> True)
              else if tag = 0x01uy then
                (match c2.dec r with
                 | Inr (_, n2) -> 1 + n2 <= Seq.length s
                 | _ -> True)
              else True))
  = if Seq.length s < 1 then ()
    else begin
      let r = Seq.slice s 1 (Seq.length s) in
      let tag = Seq.index s 0 in
      if tag = 0x00uy then c1.dec_consumed_bound r
      else if tag = 0x01uy then c2.dec_consumed_bound r
      else ()
    end
#pop-options

(** Combinator 16: sum — tagged union.

    @param c1 Codec for the [Inl] (left) branch.
    @param c2 Codec for the [Inr] (right) branch.
    Encodes [Inl v1] as tag byte [0x00] followed by [c1.enc v1].
    Encodes [Inr v2] as tag byte [0x01] followed by [c2.enc v2].
    Decoder reads the first byte as a discriminator:
    [0x00] → delegate to c1, [0x01] → delegate to c2,
    anything else → [ExpectedSumTag].
    Error positions from sub-decoders are shifted by +1 (the tag byte). *)

#push-options "--z3rlimit 80"
let sum (#a #b:Type) (c1: codec a) (c2: codec b) : codec (either a b) =
  let sum_enc (v: either a b) : Tot byte_seq =
    match v with
    | Inl v1 -> Seq.cons 0x00uy (c1.enc v1)
    | Inr v2 -> Seq.cons 0x01uy (c2.enc v2)
  in
  let sum_dec (s: byte_seq) : Tot (decode_result (either a b)) =
    if Seq.length s < 1
    then Inl (mk_decode_error UnexpectedEndOfInput 0)
    else let tag = Seq.index s 0 in
      let r = Seq.slice s 1 (Seq.length s) in
      if tag = 0x00uy then
        match c1.dec r with
        | Inr (v1, n1) -> Inr (Inl v1, 1 + n1)
        | Inl err -> Inl ({err with err_pos = err.err_pos + 1})
      else if tag = 0x01uy then
        match c2.dec r with
        | Inr (v2, n2) -> Inr (Inr v2, 1 + n2)
        | Inl err -> Inl ({err with err_pos = err.err_pos + 1})
      else Inl (mk_decode_error ExpectedSumTag 0)
  in
  let sum_wfcv (v: either a b) : Tot bool =
    match v with
    | Inl v1 -> c1.wfcv v1
    | Inr v2 -> c2.wfcv v2
  in
  let sum_wfcv_prop (v: either a b) : Tot prop =
    match v with
    | Inl v1 -> c1.wfcv_prop v1
    | Inr v2 -> c2.wfcv_prop v2
  in
  let sum_rest_cond (v: either a b) (r: byte_seq) : Tot prop =
    match v with
    | Inl v1 -> c1.rest_cond v1 r
    | Inr v2 -> c2.rest_cond v2 r
  in
  {
    enc       = sum_enc;
    dec       = sum_dec;
    wfcv      = sum_wfcv;
    wfcv_prop = sum_wfcv_prop;
    rest_cond = sum_rest_cond;
    roundtrip = (fun v r -> match v with
      | Inl v1 ->
        assert (c1.wfcv v1);
        assert (c1.wfcv_prop v1);
        assert (c1.rest_cond v1 r);
        let enc1 = c1.enc v1 in
        lemma_seq_cons_append 0x00uy enc1 r;
        c1.roundtrip v1 r;
        lemma_slice_cons_spec 0x00uy (enc1 `Seq.append` r);
        ()
      | Inr v2 ->
        assert (c2.wfcv v2);
        assert (c2.wfcv_prop v2);
        assert (c2.rest_cond v2 r);
        let enc2 = c2.enc v2 in
        lemma_seq_cons_append 0x01uy enc2 r;
        c2.roundtrip v2 r;
        lemma_slice_cons_spec 0x01uy (enc2 `Seq.append` r);
        ());
    dec_err_bound = (fun s -> lemma_sum_dec_err_bound c1 c2 s);
    dec_consumed_bound = (fun s -> lemma_sum_dec_consumed_bound c1 c2 s);
  }
#pop-options

(** Combinator 17: map_ — value transformation.

    @param f Maps decoded ['a] to optional ['b].  [None] → [ExpectedPredicate].
    @param g Maps ['b] to optional ['a] for encoding.
    @param c The underlying codec.
    Encoder applies [g]; if [None], produces [Seq.empty].
    Decoder uses [c.dec], then applies [f] to the result.
    wfcv: [g v == Some a_val] and [f a_val == Some v] and [c.wfcv a_val].
    Used to build [choice], [then_drop], [drop_then], [between], [optional]. *)

#push-options "--z3rlimit 80"
let map_ (#a #b:Type) (f: a -> Tot (option b)) (g: b -> Tot (option a))
  (c: codec a) : codec b = {
  enc       = (fun v -> match g v with
    | None -> Seq.empty
    | Some a_val -> c.enc a_val);
  dec       = (fun s ->
    match c.dec s with
    | Inl err -> Inl err
    | Inr (a_val, n) -> match f a_val with
      | None -> Inl (mk_decode_error ExpectedPredicate 0)
      | Some v -> Inr (v, n));
  wfcv      = (fun v -> match g v with
    | None -> false
    | Some a_val -> Some? (f a_val) && c.wfcv a_val);
  wfcv_prop = (fun v -> match g v with
    | None -> False
    | Some a_val -> f a_val == Some v /\ c.wfcv_prop a_val);
  rest_cond = (fun v r -> match g v with
    | None -> False
    | Some a_val -> c.rest_cond a_val r);
  roundtrip = (fun v r ->
    match g v with
    | None -> (* unreachable: wfcv v ensures Some? (g v) *)
      ()
    | Some a_val ->
      assert (c.wfcv a_val);
      assert (c.wfcv_prop a_val);
      assert (c.rest_cond a_val r);
      c.roundtrip a_val r;
      ());
  dec_err_bound = (fun s -> c.dec_err_bound s);
  dec_consumed_bound = (fun s -> c.dec_consumed_bound s);
}
#pop-options

(** 18. count *)

let rec count_enc_list (#a:Type) (c: codec a) (vs: list a) : Tot byte_seq (decreases vs) =
  match vs with
  | [] -> Seq.empty
  | v :: tl -> Seq.append (c.enc v) (count_enc_list c tl)

(** Decode a fixed number of elements from a byte sequence. *)
let rec count_dec_list (#a:Type) (c: codec a) (m: nat) (s: byte_seq) : Tot (decode_result (list a)) (decreases m) =
  if m = 0 then Inr ([], 0)
  else match c.dec s with
  | Inl err -> Inl err
  | Inr (v, n1) ->
    (* n1 > Seq.length s is unreachable for well-formed decoders;
       if triggered, emit error at the sub-decoder's reported position clamped to input length. *)
    if n1 > Seq.length s
    then Inl (mk_decode_error UnexpectedEndOfInput (Seq.length s))
    else match count_dec_list c (m - 1) (Seq.slice s n1 (Seq.length s)) with
    | Inl err -> Inl ({err with err_pos = err.err_pos + n1})
    | Inr (tl, n2) -> Inr (v :: tl, n1 + n2)

(** Check wfcv for every element in a list. *)
let rec count_wfcv_list (#a:Type) (c: codec a) (vs: list a) : Tot bool (decreases vs) =
  match vs with | [] -> true | v :: tl -> c.wfcv v && count_wfcv_list c tl

(** Conjunction of wfcv_prop for every element. *)
let rec count_wfcv_prop_list (#a:Type) (c: codec a) (vs: list a) : Tot prop (decreases vs) =
  match vs with | [] -> True | v :: tl -> c.wfcv_prop v /\ count_wfcv_prop_list c tl

(** Chain rest_cond across list elements. *)
let rec count_rest_cond_list (#a:Type) (c: codec a) (vs: list a) (r: byte_seq) : Tot prop (decreases vs) =
  match vs with
  | [] -> True
  | v :: tl -> c.rest_cond v (count_enc_list c tl `Seq.append` r) /\ count_rest_cond_list c tl r

(** Lemma: count encode then decode roundtrip. *)
let rec count_roundtrip_list (#a:Type) (c: codec a) (m: nat) (vs: list a) (r: byte_seq) : Lemma
  (requires
    List.Tot.length vs = m /\
    count_wfcv_list c vs /\
    count_wfcv_prop_list c vs /\
    count_rest_cond_list c vs r)
  (ensures
    count_dec_list c m (count_enc_list c vs `Seq.append` r)
    == Inr (vs, Seq.length (count_enc_list c vs)))
  (decreases vs)
= match vs with
  | [] -> ()
  | v :: tl ->
    let enc_tl = count_enc_list c tl in
    c.roundtrip v (enc_tl `Seq.append` r);
    Seq.append_assoc (c.enc v) enc_tl r;
    lemma_slice_after_prefix (c.enc v) (enc_tl `Seq.append` r);
    count_roundtrip_list c (m - 1) tl r;
    ()

(** count_dec_list error position bound: when it returns Inl, err_pos <= |s| *)
#push-options "--z3rlimit 80"
let rec count_dec_list_err_bound (#a:Type) (c: codec a) (m: nat) (s: byte_seq) : Lemma
  (ensures (match count_dec_list c m s with
            | Inl err -> err.err_pos <= Seq.length s
            | _ -> True))
  (decreases m)
= if m = 0 then ()
  else begin
    c.dec_err_bound s;
    match c.dec s with
    | Inl _ -> ()
    | Inr (_, n1) ->
        if n1 <= Seq.length s then begin
          c.dec_consumed_bound s;
          count_dec_list_err_bound c (m - 1) (Seq.slice s n1 (Seq.length s));
          match count_dec_list c (m - 1) (Seq.slice s n1 (Seq.length s)) with
          | Inl err -> ()
          | _ -> ()
        end else ()
  end
#pop-options

(** count_dec_list n bound: when it returns Inr, n <= |s| *)
#push-options "--z3rlimit 80"
let rec count_dec_list_consumed_bound (#a:Type) (c: codec a) (m: nat) (s: byte_seq) : Lemma
  (ensures (match count_dec_list c m s with
            | Inr (_, n) -> n <= Seq.length s
            | _ -> True))
  (decreases m)
= if m = 0 then ()
  else begin
    c.dec_consumed_bound s;
    match c.dec s with
    | Inl _ -> ()
    | Inr (_, n1) ->
        if n1 <= Seq.length s then begin
          count_dec_list_consumed_bound c (m - 1) (Seq.slice s n1 (Seq.length s));
          match count_dec_list c (m - 1) (Seq.slice s n1 (Seq.length s)) with
          | Inr (_, n2) -> ()
          | _ -> ()
        end else ()
  end
#pop-options

(** Combinator 18: count — fixed-count repetition.

    @param n Exact number of elements to encode/decode.
    @param c Element codec.
    Encodes [n] elements sequentially.  Decoder reads exactly [n]
    elements; fails if any sub-decoder fails.  wfcv: list length = [n]
    and all elements satisfy [c.wfcv]. *)

#push-options "--z3rlimit 80"
let count (#a:Type) (n: nat) (c: codec a) : codec (list a) = {
  enc       = (fun vs -> count_enc_list c vs);
  dec       = (fun s -> count_dec_list c n s);
  wfcv      = (fun vs -> List.Tot.length vs = n && count_wfcv_list c vs);
  wfcv_prop = (fun vs -> List.Tot.length vs = n /\ count_wfcv_prop_list c vs);
  rest_cond = (fun vs r -> count_rest_cond_list c vs r);
  roundtrip = (fun vs r -> count_roundtrip_list c n vs r);
  dec_err_bound = (fun s -> count_dec_list_err_bound c n s);
  dec_consumed_bound = (fun s -> count_dec_list_consumed_bound c n s);
}
#pop-options

(** Combinator 19: label — attach a descriptive name to a codec.

    @param s Label string surfaced in [decode_error.label] on errors.
    @param c The underlying codec.
    Successful decodes pass through unchanged.  On error, the label
    is set to [Some s].  All other fields delegate to [c]. *)

#push-options "--z3rlimit 10"
let label (#a:Type) (s: string) (c: codec a) : codec a = {
  enc       = c.enc;
  dec       = (fun input ->
    match c.dec input with
    | Inl err -> Inl ({err with label = Some s})
    | Inr result -> Inr result);
  wfcv      = c.wfcv;
  wfcv_prop = c.wfcv_prop;
  rest_cond = c.rest_cond;
  roundtrip = (fun v r -> c.roundtrip v r);
  dec_err_bound = c.dec_err_bound;
  dec_consumed_bound = (fun s -> c.dec_consumed_bound s);
}
#pop-options

(** 20. alt *)

(** Combinator 20: alt — content-based alternation on a first-byte predicate.

    Unlike [sum] (which prepends a 0x00/0x01 discriminator byte), [alt]
    dispatches on the CONTENT of the first byte, chosen by a caller-supplied
    predicate [p1].  The encoder emits ONLY the branch bytes (no tag); the
    decoder peeks [Seq.index s 0], dispatches to [c1] when [p1] holds and to
    [c2] otherwise.

    This is the untagged choice primitive (REQ-CODEC-008) for genuinely
    prefix-disjoint branches: [char_ref] (hex [x] vs decimal digit after
    [&#]), [text_char], and [xml_node_body] all disambiguate on the byte
    after a shared structural prefix.  For terminated-literal sets that are
    NOT first-byte-disjoint (e.g. XML [entity_ref]), use [one_of].

    The disjointness is carried in [alt_wfcv], NOT a separate record field:
    a record field would be an opaque lambda across module boundaries
    (fstar-proofs §18).  [alt_wfcv (Inl v1)] requires [|c1.enc v1| > 0] and
    [p1 (Seq.index (c1.enc v1) 0)]; [alt_wfcv (Inr v2)] requires
    [not (p1 (Seq.index (c2.enc v2) 0))].

    @param c1 Codec for the [Inl] (left) branch.
    @param c2 Codec for the [Inr] (right) branch.
    @param p1 Predicate true iff the first byte belongs to the left branch.
    Encodes [Inl v1] as [c1.enc v1] (no tag).  Encodes [Inr v2] as [c2.enc v2] (no tag).
    wfcv: left requires [|c1.enc v1| > 0 /\ p1 (Seq.index (c1.enc v1) 0)];
          right requires [|c2.enc v2| > 0 /\ not (p1 (Seq.index (c2.enc v2) 0))].
    Fails with the sub-decoder's error when the branch decode fails. *)

let alt_enc (#a #b:Type) (c1: codec a) (c2: codec b) (v: either a b) : Tot byte_seq =
  match v with | Inl v1 -> c1.enc v1 | Inr v2 -> c2.enc v2

let alt_dec (#a #b:Type) (c1: codec a) (c2: codec b) (p1: byte -> bool) (s: byte_seq)
  : Tot (decode_result (either a b)) =
  if Seq.length s < 1 then Inl (mk_decode_error UnexpectedEndOfInput 0)
  else let b0 = Seq.index s 0 in
    if p1 b0 then
      match c1.dec s with
      | Inr (v1, n1) -> Inr (Inl v1, n1)
      | Inl err -> Inl err
    else
      match c2.dec s with
      | Inr (v2, n2) -> Inr (Inr v2, n2)
      | Inl err -> Inl err

let alt_wfcv (#a #b:Type) (c1: codec a) (c2: codec b) (p1: byte -> bool) (v: either a b) : Tot bool =
  match v with
  | Inl v1 -> c1.wfcv v1 && Seq.length (c1.enc v1) > 0 && p1 (Seq.index (c1.enc v1) 0)
  | Inr v2 -> c2.wfcv v2 && Seq.length (c2.enc v2) > 0 && not (p1 (Seq.index (c2.enc v2) 0))

let alt_wfcv_prop (#a #b:Type) (c1: codec a) (c2: codec b) (v: either a b) : Tot prop =
  match v with | Inl v1 -> c1.wfcv_prop v1 | Inr v2 -> c2.wfcv_prop v2

let alt_rest_cond (#a #b:Type) (c1: codec a) (c2: codec b) (v: either a b) (r: byte_seq) : Tot prop =
  match v with | Inl v1 -> c1.rest_cond v1 r | Inr v2 -> c2.rest_cond v2 r

#push-options "--z3rlimit 80"
let alt_roundtrip (#a #b:Type) (c1: codec a) (c2: codec b) (p1: byte -> bool)
  (v: either a b) (r: byte_seq) : Lemma
  (requires alt_wfcv c1 c2 p1 v /\ alt_wfcv_prop c1 c2 v /\ alt_rest_cond c1 c2 v r)
  (ensures alt_dec c1 c2 p1 (alt_enc c1 c2 v `Seq.append` r)
           == Inr (v, Seq.length (alt_enc c1 c2 v)))
  = match v with
    | Inl v1 ->
        assert (c1.wfcv v1); assert (c1.wfcv_prop v1); assert (c1.rest_cond v1 r);
        assert (Seq.length (c1.enc v1) > 0);
        assert (p1 (Seq.index (c1.enc v1) 0));
        Seq.lemma_index_app1 (c1.enc v1) r 0;
        c1.roundtrip v1 r; ()
    | Inr v2 ->
        assert (c2.wfcv v2); assert (c2.wfcv_prop v2); assert (c2.rest_cond v2 r);
        assert (Seq.length (c2.enc v2) > 0);
        assert (not (p1 (Seq.index (c2.enc v2) 0)));
        Seq.lemma_index_app1 (c2.enc v2) r 0;
        c2.roundtrip v2 r; ()
#pop-options

let alt_dec_err_bound (#a #b:Type) (c1: codec a) (c2: codec b) (p1: byte -> bool) (s: byte_seq) : Lemma
  (ensures (match alt_dec c1 c2 p1 s with Inl err -> err.err_pos <= Seq.length s | _ -> True))
  = if Seq.length s < 1 then ()
    else begin
      let b0 = Seq.index s 0 in
      if p1 b0 then c1.dec_err_bound s else c2.dec_err_bound s
    end

let alt_dec_consumed_bound (#a #b:Type) (c1: codec a) (c2: codec b) (p1: byte -> bool) (s: byte_seq) : Lemma
  (ensures (match alt_dec c1 c2 p1 s with Inr (_, n) -> n <= Seq.length s | _ -> True))
  = if Seq.length s < 1 then ()
    else begin
      let b0 = Seq.index s 0 in
      if p1 b0 then c1.dec_consumed_bound s else c2.dec_consumed_bound s
    end

#push-options "--z3rlimit 20"
let alt (#a #b:Type) (c1: codec a) (c2: codec b) (p1: byte -> bool) : codec (either a b) = {
  enc = (fun v -> alt_enc c1 c2 v);
  dec = (fun s -> alt_dec c1 c2 p1 s);
  wfcv = (fun v -> alt_wfcv c1 c2 p1 v);
  wfcv_prop = (fun v -> alt_wfcv_prop c1 c2 v);
  rest_cond = (fun v r -> alt_rest_cond c1 c2 v r);
  roundtrip = (fun v r -> alt_roundtrip c1 c2 p1 v r);
  dec_err_bound = (fun s -> alt_dec_err_bound c1 c2 p1 s);
  dec_consumed_bound = (fun s -> alt_dec_consumed_bound c1 c2 p1 s);
}
#pop-options

(** 21. one_of — terminated-literal choice *)

(** Mismatch helper for [one_of]: [x] and [y] differ within [min |x| |y|]
    (neither is a prefix of the other at the first differing index).
    [one_of_mismatch_evident x y] is the precise precondition for
    [bytes_decode x (seq_of_list y ++ r) == Inl]. *)
let rec one_of_mismatch_evident (x y: list byte) : Tot bool (decreases x) =
  match x, y with
  | [], _ -> false
  | _, [] -> false
  | a :: xt, b :: yt -> if a = b then one_of_mismatch_evident xt yt else true

(** Lemma: when [x] and [y] differ within the shorter length,
    [bytes_decode x (seq_of_list y ++ r)] returns [Inl].
    This is the "wrong literal fails" fact that content-alternation needs. *)
#push-options "--z3rlimit 80"
let rec lemma_one_of_bytes_mismatch (x y: list byte) (r: byte_seq) : Lemma
  (requires one_of_mismatch_evident x y)
  (ensures (match bytes_decode x (seq_of_list y `Seq.append` r) with
            | Inl _ -> True | Inr _ -> False))
  (decreases x)
  = match x with
    | [] -> ()
    | a :: xt ->
        match y with
        | [] -> ()
        | b :: yt ->
            if a = b then begin
              Seq.lemma_seq_of_list_cons b yt;
              Seq.append_assoc (Seq.create 1 b) (seq_of_list yt) r;
              lemma_slice_cons_spec b (seq_of_list yt `Seq.append` r);
              lemma_one_of_bytes_mismatch xt yt r
            end else begin
              Seq.lemma_seq_of_list_cons b yt;
              Seq.append_assoc (Seq.create 1 b) (seq_of_list yt) r;
              ()
            end
#pop-options

(** [one_of] encoder: emit the literal of the first pair whose value equals [v].
    Requires [a: eqtype] (decidable equality for the value-keyed lookup). *)
let rec one_of_enc (#a:eqtype) (pairs: list (a & list byte)) (v: a) : Tot byte_seq (decreases pairs) =
  match pairs with
  | [] -> Seq.empty
  | (pv, lit) :: tl -> if pv = v then seq_of_list lit else one_of_enc tl v

(** [one_of] decoder: the value of the first pair whose literal matches,
    failing with the last-branch [bytes_decode] error when none match. *)
let rec one_of_dec (#a:eqtype) (pairs: list (a & list byte)) (s: byte_seq) : Tot (decode_result a) (decreases pairs) =
  match pairs with
  | [] -> Inl (mk_decode_error UnexpectedEndOfInput 0)
  | (pv, lit) :: tl ->
      match bytes_decode lit s with
      | Inr ((), n) -> Inr (pv, n)
      | Inl _ -> one_of_dec tl s

(** [one_of_mem]: true iff [v] keys some pair. *)
let rec one_of_mem (#a:eqtype) (pairs: list (a & list byte)) (v: a) : Tot bool (decreases pairs) =
  match pairs with
  | [] -> false
  | (pv, _) :: tl -> pv = v || one_of_mem tl v

(** NOTE on [one_of] roundtrip scope: the generic per-pair roundtrip
    [dec (enc v ++ r) == Inr (v, |enc v|)] requires that the literal set is
    mutually non-prefix (each literal differs from every other within the
    shorter length — [one_of_mismatch_evident] on all ordered pairs).  This
    property is a WHOLE-LIST invariant, not a per-value guard, so it does not
    fit the [codec] record's per-value [wfcv] field cleanly.  [one_of] is
    therefore exported as ENCODER/DECODER combinators plus the verified
    [lemma_one_of_bytes_mismatch]; the roundtrip for a concrete literal set
    (e.g. the five XML entity refs) is proven at the call site by explicit
    per-branch [lemma_one_of_bytes_mismatch] calls + [lemma_bytes_self_prefix_spec].
    See record-codec-xml Task 2.4/2.5.

    If a future change needs the generic [one_of] roundtrip as a [codec] field,
    add a [mutually_disjoint] predicate and carry it in [wfcv]
    (constant-in-[v], like [digits_to_int.rest_cond] compares against [max_len]).
    That induction is straightforward but hits the recursive-predicate-in-
    [requires] opacity documented in fstar-proofs §44.  The concrete per-site
    proof is the lower-risk path and is what xml/json needs first. *)

(** Combinator 21: one_of — ordered terminated-literal choice (encode/decode).

    @param pairs The [(value, literal)] pairs, value type [a: eqtype].
    NOT a full [codec] (roundtrip is per-instantiation; see the NOTE above).
    Use the encoder/decoder pair plus [lemma_one_of_bytes_mismatch] at the
    call site to build the [custom] roundtrip. *)
let one_of (#a:eqtype) (pairs: list (a & list byte))
  : (a -> Tot byte_seq) & (byte_seq -> Tot (decode_result a)) & (a -> Tot bool)
  = (one_of_enc pairs, one_of_dec pairs, one_of_mem pairs)


(** Field-accessor lemmas

    These lemmas export record-field equalities that are definitional
    within [Data.Codec.Types] but opaque to consumers.  Each body is
    [()] because the equality is definitional in the defining module.

    Without these lemmas, consumers of combinators like [product],
    [map_], and [byte_val] cannot evaluate [.wfcv], [.rest_cond],
    [.wfcv_prop], [.enc], or [.dec] field accesses through the SMT
    solver — the [noeq type] record fields are opaque lambdas across
    module boundaries (fstar-proofs §18). *)

(** Lemma: [product c1 c2].wfcv (x, y) == c1.wfcv x && c2.wfcv y. *)
let lemma_product_wfcv_eq (#a #b:Type) (c1: codec a) (c2: codec b) (x: a) (y: b) : Lemma
  ((product c1 c2).wfcv (x, y) == (c1.wfcv x && c2.wfcv y))
  = ()

(** Lemma: [product c1 c2].wfcv_prop (x, y) == c1.wfcv_prop x /\ c2.wfcv_prop y. *)
let lemma_product_wfcv_prop_eq (#a #b:Type) (c1: codec a) (c2: codec b) (x: a) (y: b) : Lemma
  ((product c1 c2).wfcv_prop (x, y) == (c1.wfcv_prop x /\ c2.wfcv_prop y))
  = ()

(** Lemma: [product c1 c2].rest_cond (v1, v2) r expands to conjunction
    of sub-codec rest_cond. *)
let lemma_product_rest_cond_eq (#a #b:Type) (c1: codec a) (c2: codec b) (v1: a) (v2: b) (r: byte_seq) : Lemma
  ((product c1 c2).rest_cond (v1, v2) r ==
   (c1.rest_cond v1 (c2.enc v2 `Seq.append` r) /\ c2.rest_cond v2 r))
  = ()

(** Lemma: [product c1 c2].enc (v1, v2) == c1.enc v1 ++ c2.enc v2. *)
let lemma_product_enc_eq (#a #b:Type) (c1: codec a) (c2: codec b) (v1: a) (v2: b) : Lemma
  ((product c1 c2).enc (v1, v2) == Seq.append (c1.enc v1) (c2.enc v2))
  = ()

(** Lemma: [product c1 c2].dec s expands to the inline decoder. *)
let lemma_product_dec_eq (#a #b:Type) (c1: codec a) (c2: codec b) (s: byte_seq) : Lemma
  ((product c1 c2).dec s ==
   (match c1.dec s with
    | Inl err -> Inl err
    | Inr (v1, n1) ->
      if n1 > Seq.length s then Inl (mk_decode_error UnexpectedEndOfInput (Seq.length s))
      else match c2.dec (Seq.slice s n1 (Seq.length s)) with
      | Inl err -> Inl ({err with err_pos = err.err_pos + n1})
      | Inr (v2, n2) -> Inr ((v1, v2), n1 + n2)))
  = ()

(** Lemma: [map_ f g c].wfcv v == match g v with ... *)
let lemma_map_wfcv_eq (#a #b:Type) (f: a -> Tot (option b)) (g: b -> Tot (option a))
  (c: codec a) (v: b) : Lemma
  ((map_ f g c).wfcv v ==
   (match g v with
    | None -> false
    | Some a_val -> Some? (f a_val) && c.wfcv a_val))
  = ()

(** Lemma: [map_ f g c].wfcv_prop v == match g v with ... *)
let lemma_map_wfcv_prop_eq (#a #b:Type) (f: a -> Tot (option b)) (g: b -> Tot (option a))
  (c: codec a) (v: b) : Lemma
  ((map_ f g c).wfcv_prop v ==
   (match g v with
    | None -> False
    | Some a_val -> f a_val == Some v /\ c.wfcv_prop a_val))
  = ()

(** Lemma: [map_ f g c].rest_cond v r == match g v with ... *)
let lemma_map_rest_cond_eq (#a #b:Type) (f: a -> Tot (option b)) (g: b -> Tot (option a))
  (c: codec a) (v: b) (r: byte_seq) : Lemma
  ((map_ f g c).rest_cond v r ==
   (match g v with
    | None -> False
    | Some a_val -> c.rest_cond a_val r))
  = ()

(** Lemma: [map_ f g c].enc v == match g v with ... *)
let lemma_map_enc_eq (#a #b:Type) (f: a -> Tot (option b)) (g: b -> Tot (option a))
  (c: codec a) (v: b) : Lemma
  ((map_ f g c).enc v ==
   (match g v with
    | None -> Seq.empty
    | Some a_val -> c.enc a_val))
  = ()

(** Lemma: [map_ f g c].dec s expands to the inline decoder. *)
let lemma_map_dec_eq (#a #b:Type) (f: a -> Tot (option b)) (g: b -> Tot (option a))
  (c: codec a) (s: byte_seq) : Lemma
  ((map_ f g c).dec s ==
   (match c.dec s with
    | Inl err -> Inl err
    | Inr (a_val, n) -> match f a_val with
      | None -> Inl (mk_decode_error ExpectedPredicate 0)
      | Some v -> Inr (v, n)))
  = ()

(** Lemma: [byte_val b].wfcv () == true. *)
let lemma_byte_val_wfcv_eq (b: byte) : Lemma ((byte_val b).wfcv () == true) = ()

(** Lemma: [byte_val b].wfcv_prop () == True. *)
let lemma_byte_val_wfcv_prop_eq (b: byte) : Lemma ((byte_val b).wfcv_prop () == True) = ()

(** Lemma: [byte_val b].rest_cond () r == True. *)
let lemma_byte_val_rest_cond_eq (b: byte) (r: byte_seq) : Lemma
  ((byte_val b).rest_cond () r == True)
  = ()

(** Combinator 22: take_until — delimiter-terminated content run.

    Scans a LIST-level content run that stops exactly at a multi-byte
    delimiter.  This is the verified primitive for delimiter-aware content
    (XML comment [-->], CDATA []]>], PI [?>]) that Mandate 22 requires as a
    [Data.Codec] combinator rather than a bespoke scanner.

    The decoder converts the input to a list ONCE at the boundary
    ([Seq.seq_to_list]) and scans at the LIST level, where the multi-byte
    delimiter lookahead reduces cleanly (fstar-proofs §60); the roundtrip
    bridges back with [lemma_seq_list_bij_rev].  The encoder emits
    [content @ delim].

    @param delim The close-marker byte list (non-empty, e.g. [-->]).
    @param content_ok A content-validity predicate (e.g. [comment_ok]
                      rejects [--]).  Applied to the scanned content and
                      carried by [wfcv].
    @param max The maximum content length.
    NOT a full [codec] (roundtrip is per-instantiation; see the NOTE).
    Use the encoder/decoder/wfcv helpers plus a per-delimiter roundtrip
    lemma at the call site to build the [custom] roundtrip. *)

(** [is_prefix_of] — is [p] a prefix of [l]? *)
let rec is_prefix_of (#a:eqtype) (p l: list a) : Tot bool (decreases p) =
  match p, l with
  | [], _ -> true
  | _, [] -> false
  | ph :: pt, lh :: lt -> ph = lh && is_prefix_of pt lt

(** Lemma: a prefix is no longer than the list it prefixes. *)
let rec lemma_is_prefix_len (#a:eqtype) (p l: list a) : Lemma
  (ensures is_prefix_of p l ==> List.Tot.length p <= List.Tot.length l)
  (decreases p)
  = match p, l with
    | [], _ -> ()
    | _, [] -> ()
    | ph :: pt, lh :: lt ->
        if ph = lh then lemma_is_prefix_len pt lt
        else ()

(** Scan the content up to (not including) the first occurrence of [delim].

    Returns [(content, rest)] where [rest] begins with [delim] when the
    delimiter is present (otherwise [rest] is [] and [content] is the whole
    input). *)
let rec scan_until_split (delim: list byte) (bs: list byte)
  : Tot (list byte & list byte) (decreases bs) =
  if is_prefix_of delim bs then ([], bs)
  else match bs with
       | b :: tl -> let (c, r) = scan_until_split delim tl in (b :: c, r)
       | [] -> ([], [])

(** Scan the content only (the [fst] projection of [scan_until_split]). *)
let scan_until_content (delim: list byte) (bs: list byte) : Tot (list byte) =
  fst (scan_until_split delim bs)

(** The remainder after the content (the [snd] projection of
    [scan_until_split]). *)
let scan_until_rest (delim: list byte) (bs: list byte) : Tot (list byte) =
  snd (scan_until_split delim bs)

(** [take_until] decoder: [Seq.seq_to_list] at the boundary, then the list-level
    scan, then [content_ok] + length validation.  Rejects when the delimiter
    is absent, the content violates [content_ok], or it exceeds [max]. *)
let take_until_dec (delim: list byte) (content_ok: list byte -> Tot bool)
  (max: nat) (s: byte_seq) : Tot (decode_result (list byte)) =
  let bs = Seq.seq_to_list s in
  let (content, rest) = scan_until_split delim bs in
  if is_prefix_of delim rest then
    if List.Tot.length content <= max && content_ok content then
      Inr (content, List.Tot.length content + List.Tot.length delim)
    else Inl (mk_decode_error ExpectedPredicate (List.Tot.length content))
  else Inl (mk_decode_error UnexpectedEndOfInput (Seq.length s))

(** [take_until] encoder: [seq_of_list (content @ delim)]. *)
let take_until_enc (delim: list byte) (content: list byte) : Tot byte_seq =
  seq_of_list (content @ delim)

(** [take_until] well-formedness guard: the content obeys [content_ok]
    and is within [max]. *)
let take_until_wfcv (content_ok: list byte -> Tot bool) (max: nat) (content: list byte) : bool =
  List.Tot.length content <= max && content_ok content

(** [take_until] well-formed proposition — [True]; the boolean [wfcv] carries
    the check (fstar-proofs §18). *)
let take_until_wfcv_prop (content: list byte) : prop = True

(** [take_until] suffix condition: the content is valid and the suffix starts
    with the delimiter (the close marker follows the content). *)
let take_until_rest_cond (delim: list byte) (content_ok: list byte -> Tot bool)
  (max: nat) (content: list byte) (r: byte_seq) : prop =
  take_until_wfcv content_ok max content /\
  is_prefix_of delim (Seq.seq_to_list r)

(** [take_until] helpers tuple (encoder, decoder, wfcv-guard).
    Mirrors [one_of]; the roundtrip is proven per-instantiation. *)
let take_until (delim: list byte) (content_ok: list byte -> Tot bool) (max: nat)
  : ((list byte -> Tot byte_seq) & (byte_seq -> Tot (decode_result (list byte))) & (list byte -> Tot bool))
  = (take_until_enc delim, take_until_dec delim content_ok max, take_until_wfcv content_ok max)

(** The content scan consumes at most [|bs|] bytes. *)
let rec lemma_scan_until_content_le_len (delim: list byte) (bs: list byte) : Lemma
  (ensures List.Tot.length (scan_until_content delim bs) <= List.Tot.length bs)
  (decreases bs)
  = if is_prefix_of delim bs then ()
    else match bs with
         | [] -> ()
         | b :: tl ->
             lemma_scan_until_content_le_len delim tl;
             ()

(** The split is exact: content @ rest == bs. *)
let rec lemma_scan_until_split_exact (delim: list byte) (bs: list byte) : Lemma
  (ensures (let (c, r) = scan_until_split delim bs in c @ r == bs))
  (decreases bs)
  = if is_prefix_of delim bs then ()
    else match bs with
         | [] -> ()
         | b :: tl ->
             lemma_scan_until_split_exact delim tl;
             ()

(** When the delimiter is found, the content length plus the delimiter length
    is at most the input length. *)
let lemma_scan_until_found_bound (delim: list byte) (bs: list byte) : Lemma
  (ensures is_prefix_of delim (scan_until_rest delim bs) ==>
            List.Tot.length (scan_until_content delim bs) + List.Tot.length delim
            <= List.Tot.length bs)
  = let (content, rest) = scan_until_split delim bs in
    lemma_scan_until_split_exact delim bs;
    assert (content @ rest == bs);
    lemma_is_prefix_len delim rest;
    List.Tot.append_length content rest;
    assert (List.Tot.length content + List.Tot.length rest == List.Tot.length bs);
    ()

(** Error-position bound for [take_until_dec]. *)
#push-options "--z3rlimit 400 --split_queries always"
let lemma_take_until_dec_err_bound (delim: list byte)
  (content_ok: list byte -> Tot bool) (max: nat) (s: byte_seq) : Lemma
  (ensures (match take_until_dec delim content_ok max s with
            | Inl err -> err.err_pos <= Seq.length s
            | _ -> True))
  =
  let bs = Seq.seq_to_list s in
  lemma_scan_until_content_le_len delim bs;
  ()
#pop-options

(** Consumed-count bound for [take_until_dec]. *)
#push-options "--z3rlimit 400 --split_queries always"
let lemma_take_until_dec_consumed_bound (delim: list byte)
  (content_ok: list byte -> Tot bool) (max: nat) (s: byte_seq) : Lemma
  (ensures (match take_until_dec delim content_ok max s with
            | Inr (_, n) -> n <= Seq.length s
            | _ -> True))
  =
  let bs = Seq.seq_to_list s in
  lemma_scan_until_found_bound delim bs;
  ()
#pop-options

(** NOTE on [take_until] roundtrip scope.

    The generic per-content roundtrip
    [take_until_dec delim content_ok max (take_until_enc delim content ++ r)
    == Inr (content, |content| + |delim|)] requires that the delimiter does
    NOT occur as a prefix anywhere inside the content.  That is a
    WHOLE-DELIMITER + WHOLE-CONTENT property (\"no [delim] substring of
    [content]\"), which needs induction over BOTH [content] and [delim]
    (a 2D-induction).  For a SYMBOLIC [delim] this does not unfold in
    lockstep with [scan_until_delim] (fstar-proofs §60) — the generic
    roundtrip is therefore NOT shipped as a [codec] field.

    The per-delimiter concrete roundtrips (fixed [-->]/[]]>]/[?>], the
    [one_of] per-instantiation pattern) all verify 0-admit.  [take_until]
    is exported as encoder/decoder/wfcv helpers plus the generic
    [lemma_take_until_dec_err_bound]/[lemma_take_until_dec_consumed_bound];
    the roundtrip for a concrete delimiter must be proven at the call site
    (the [custom] codec's [roundtrip] argument) by [lemma_seq_list_bij_rev]
    + [assert_norm] on the concrete [scan_until_delim] (fstar-proofs §60). *)

