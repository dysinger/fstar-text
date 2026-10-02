(* Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later *)


(**
Data.Text.Codec.UTF8String — a UTF-8-aware [codec string].

[Data.Text.Codec.text_chars] matches one-or-more ASCII characters by their
LOW BYTE ([char_to_byte_trunc]), so it can only represent code points < 128.
This module is the UNICODE counterpart: a [codec string] whose encoder emits
each character's full UTF-8 encoding (1-4 bytes, [char_to_utf8]) and whose
decoder reassembles a [string] from a run of UTF-8-encoded characters,
validating overlong/surrogate/above-max forms ([utf8_decode_one]).

It is the full-XML-1.0 Name/Text codec the [xml] package needs (Phase 5):
XML Names admit non-ASCII Unicode NameStartChar/NameChar (RFC productions
[4]/[4a]/[5] of the Fifth Edition), which the ASCII-only [text_chars] cannot
represent.

It lives in its own module for the same reason as [Data.Text.Codec.Zero] and
[Data.Text.Codec.Delims]: the §45 SMT-context-pollution discipline — a second
[custom] combinator with its own [let rec] scan in [Data.Text.Codec] would
re-trigger the opacity that keeps [text_chars] at 0 admits.  The variable-
width scan and its induction are re-bound here self-contained (fstar-proofs
§44 — cross-module [let rec] is opaque); only the PROVEN non-recursive UTF-8
facts ([char_to_utf8]/[utf8_decode_one]/[mk_char]/[lemma_utf8_decode_prefix])
are reused from [Data.Text.Codec.UTF8].

Design (fstar-proofs §59 Fact 1 + Fact 2, and §60):

- The scan FUEL is a CHAR count, never a byte count — [char_to_utf8 c] is
  1-4 bytes, so a byte-fuel recurrence misaligns with the char-cons
  induction.  The decoder consumes up to [max] CHARACTERS, returning
  [(chars, remaining-bytes)].
- The decoder is [Seq.seq_to_list]-at-the-boundary (fstar-proofs §60): the
  [byte_seq] input is converted to a list ONCE, the list-level scan operates
  on a transparent [list], and the general-suffix roundtrip bridges back with
  the EXPORTED [lemma_seq_to_list_of_list_append].
- The head-char prefix bridge [lemma_utf8_decode_prefix c rest] (§59 Fact 2)
  closes the char-cons induction step.

Well-formedness is LENGTH-ONLY ([FStar.Char.char] already represents valid
Unicode scalars, so every char is encodable/decodable — no per-char predicate
is needed at this layer; a predicate-bearing sibling would just be [map_] over
this codec with a char->bool guard).

@header Data.Text.Codec.UTF8String
*)
module Data.Text.Codec.UTF8String


open Data.Codec
open Data.Text.Codec.UTF8
open FStar.Seq
open FStar.Char
open FStar.String
open FStar.UInt8
open FStar.List.Tot


module Seq = FStar.Seq


(* ── Scan + encode/decode (build order: scanner → plumbing → lemmas) ── *)


(** [utf8_string_to_bytes s] — the UTF-8 byte encoding of a string:
    [concatMap char_to_utf8] over its character list. *)
unfold
let utf8_string_to_bytes (s: string) : list byte =
  FStar.List.Tot.concatMap char_to_utf8 (FStar.String.list_of_string s)


(** [utf8_scan_chars max bs] — variable-width UTF-8 char scan, CHAR-count fuel
    (fstar-proofs §59 Fact 1).

    Consumes up to [max] characters from the head of [bs]; stops early when
    the head does not decode as a valid UTF-8 character.  Returns the
    consumed characters (in order) and the remaining bytes. *)
let rec utf8_scan_chars (max: nat) (bs: list byte)
  : Tot (list FStar.Char.char & list byte) (decreases max)
  = if max = 0 then ([], bs)
    else match utf8_decode_one bs with
      | None -> ([], bs)
      | Some (c, rest) ->
          let (cs, rem) = utf8_scan_chars (max - 1) rest in
          (c :: cs, rem)


(** [lemma_utf8_scan_terminate max cs r'] — the scan over
    [concatMap char_to_utf8 cs @ r'] terminates after consuming exactly [cs]
    when [max >= length cs] AND either the bound is reached
    ([length cs = max]) or the suffix [r'] does not begin a valid char
    ([None? (utf8_decode_one r')]).

    This single lemma covers BOTH [rest_cond] disjuncts: the bounded case
    ([length cs = max]) uses the fuel bound; the suffix case uses the
    head-char prefix bridge at the boundary.  Proved by induction on [cs]. *)
#push-options "--z3rlimit 800"
let rec lemma_utf8_scan_terminate (max: nat) (cs: list FStar.Char.char) (r': list byte)
  : Lemma
    (requires
      max >= List.Tot.length cs /\
      (List.Tot.length cs = max \/ None? (utf8_decode_one r')))
    (ensures utf8_scan_chars max (List.Tot.concatMap char_to_utf8 cs @ r') == (cs, r'))
    (decreases cs)
  = match cs with
    | [] -> ()
    | c :: tl ->
        (* the head char's encoding is consumed, returning the tail-encoding
           @ r' suffix unchanged (§59 Fact 2) *)
        lemma_utf8_decode_prefix c (List.Tot.concatMap char_to_utf8 tl @ r');
        (* recurse: [max >= 1 + length tl] and the boundary condition propagates *)
        lemma_utf8_scan_terminate (max - 1) tl r';
        ()
#pop-options


(** [utf8_string_dec max input] — the UTF-8 string DECODER: [Seq.seq_to_list]
    at the boundary, list-level char scan (CHAR-count fuel), [string_of_list]
    reassembly.

    The consumed count is the NUMBER OF BYTES (the codec contract's [nat] is a
    byte count): [|bs| - |rem|], the bytes dropped off the front of [bs],
    guarded to stay [nat] (fstar-lang §4). *)
let utf8_string_dec (max: nat) (input: byte_seq) : Tot (decode_result string) =
  let bs = Seq.seq_to_list input in
  let (cs, rem) = utf8_scan_chars max bs in
  let consumed_bytes =
    if List.Tot.length bs >= List.Tot.length rem
    then List.Tot.length bs - List.Tot.length rem
    else 0 in
  Inr (FStar.String.string_of_list cs, consumed_bytes)


(** [utf8_string_enc s] — the UTF-8 string ENCODER: string → its full UTF-8
    byte sequence. *)
unfold
let utf8_string_enc (s: string) : Tot byte_seq =
  seq_of_list (utf8_string_to_bytes s)


(** [utf8_string_wfcv max s] — guard: the string has at most [max] characters.
    Length-only — every [FStar.Char.char] is a valid Unicode scalar, so
    encodability is total.

    Marked [unfold] so [.roundtrip]'s internal [assert (wfcv_custom v)]
    discharges at cross-module call sites (fstar-proofs §54 Trap 1). *)
unfold
let utf8_string_wfcv (max: nat) (s: string) : bool =
  List.Tot.length (FStar.String.list_of_string s) <= max


(** [utf8_string_wfcv_prop max s] — well-formed proposition — [True] (the
    boolean guard carries the check). *)
unfold
let utf8_string_wfcv_prop (max: nat) (s: string) : prop =
  True


(** [utf8_string_rest_cond max s r] — suffix condition — the bounded-greedy
    3-disjunct shape: the run fills the whole char bound, OR the suffix is
    empty, OR the suffix does not begin a valid UTF-8 char.  The empty-suffix
    case ([r = Seq.empty]) is subsumed by the third disjunct
    ([utf8_decode_one [] == None]). *)
unfold
let utf8_string_rest_cond (max: nat) (s: string) (r: byte_seq) : prop =
  let n = List.Tot.length (FStar.String.list_of_string s) in
  n = max \/ Seq.length r = 0 \/
  (Seq.length r > 0 && None? (utf8_decode_one (Seq.seq_to_list r)))


(* ── Roundtrip lemmas (alphabetical) ───────────────────────────────── *)


(** [lemma_utf8_string_dec_consumed_bound max input] — consumed-count bound for
    [utf8_string_dec].

    [consumed_bytes <= |bs|] follows directly from the guarded subtraction:
    when [|rem| <= |bs|] it is [|bs| - |rem| <= |bs|]; otherwise it is [0]. *)
#push-options "--z3rlimit 400"
let lemma_utf8_string_dec_consumed_bound (max: nat) (input: byte_seq) : Lemma
  (ensures (match utf8_string_dec max input with
            | Inr (_, n) -> n <= Seq.length input
            | _ -> True))
  = ()
#pop-options


(** [lemma_utf8_string_dec_err_bound max input] — error-position bound for
    [utf8_string_dec] (never errors — always [Inr]). *)
let lemma_utf8_string_dec_err_bound (max: nat) (input: byte_seq) : Lemma
  (ensures (match utf8_string_dec max input with
            | Inl err -> err.err_pos <= Seq.length input
            | _ -> True))
  = ()


(** [lemma_utf8_string_roundtrip max s r] — roundtrip proof for [utf8_string]:
    [dec (enc s ++ r) == Inr (s, |enc s|)].

    Chains (1) [lemma_utf8_scan_terminate max chars r'] (the scan terminates
    after [chars]), (2) [lemma_seq_to_list_of_list_append bytes r] (the
    boundary bridge), (3) [FStar.String.string_of_list_of_string s] (the
    string reassembly). *)
#push-options "--z3rlimit 4000"
let lemma_utf8_string_roundtrip (max: nat) (s: string) (r: byte_seq)
  : Lemma
    (requires
      utf8_string_wfcv max s /\
      utf8_string_wfcv_prop max s /\
      utf8_string_rest_cond max s r)
    (ensures
      utf8_string_dec max (utf8_string_enc s `Seq.append` r)
        == Inr (s, Seq.length (utf8_string_enc s)))
  =
    let chars = FStar.String.list_of_string s in
    let bytes = utf8_string_to_bytes s in
    let r' = Seq.seq_to_list r in
    assert (utf8_string_enc s == seq_of_list bytes);
    lemma_seq_to_list_of_list_append bytes r;
    assert (Seq.seq_to_list (seq_of_list bytes `Seq.append` r)
              == bytes @ r');
    (* [bytes] IS [concatMap char_to_utf8 chars] (definitionally) *)
    lemma_utf8_scan_terminate max chars r';
    assert (utf8_scan_chars max (bytes @ r') == (chars, r'));
    let input = utf8_string_enc s `Seq.append` r in
    assert (Seq.seq_to_list input == bytes @ r');
    assert (utf8_string_dec max input
              == Inr (FStar.String.string_of_list chars,
                      List.Tot.length (bytes @ r') - List.Tot.length r'));
    FStar.String.string_of_list_of_string s;
    assert (FStar.String.string_of_list chars == s);
    assert (Seq.length (utf8_string_enc s) == List.Tot.length bytes);
    assert (List.Tot.length (bytes @ r') == List.Tot.length bytes + List.Tot.length r');
    assert (utf8_string_dec max input == Inr (s, Seq.length (utf8_string_enc s)));
    ()
#pop-options


(** [lemma_utf8_string_empty_roundtrip max] — concrete empty-string roundtrip
    vector: the empty string roundtrips against an empty suffix (CHAR-count 0,
    byte-count 0). *)
#push-options "--z3rlimit 400"
let lemma_utf8_string_empty_roundtrip (max: nat) : Lemma
  (requires utf8_string_wfcv max "" /\ utf8_string_rest_cond max "" Seq.empty)
  (ensures utf8_string_dec max (utf8_string_enc "" `Seq.append` Seq.empty) == Inr ("", 0))
  = lemma_utf8_string_roundtrip max "" Seq.empty
#pop-options


(* ── Combinator ─────────────────────────────────────────────────────── *)


(** [utf8_string max] — the UTF-8-aware [codec string].

    Encodes each char as 1-4 UTF-8 bytes; decodes a run of UTF-8 chars into
    a [string] (CHAR-count fuel, fstar-proofs §59).  Composability (the
    bounded-greedy suffix condition) is the [utf8_string_rest_cond] guard.

    @param max The maximum number of CHARACTERS the decoder may consume. *)
#push-options "--z3rlimit 2000"
let utf8_string (max: nat) : codec string =
  custom
    (utf8_string_dec max)
    utf8_string_enc
    (utf8_string_wfcv max)
    (utf8_string_wfcv_prop max)
    (utf8_string_rest_cond max)
    (lemma_utf8_string_roundtrip max)
    (lemma_utf8_string_dec_err_bound max)
    (lemma_utf8_string_dec_consumed_bound max)
#pop-options
