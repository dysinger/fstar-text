(**
Data.Text.Codec — Common text codec infrastructure.

Typeclasses and common types shared by all text encodings.  Provides
the ASCII char↔byte bridge, string↔bytes conversion helpers, and the
[text_chars] combinator (one-or-more ASCII characters matching a
predicate, decoded with BOUNDED greedy scan into a [string]).

Built on the record-based [Data.Codec] combinator library.  Zero admits.

The [text_chars] decoder is BOUNDED greedy: it consumes up to [max]
matchable bytes, stopping at the bound OR at the first non-matching
byte.  This mirrors [digits_to_int max_len] exactly — an unbounded
greedy scan is not a valid invertible-syntax codec (fstar-proofs §43).
Its [rest_cond] is the 3-disjunct shape (bound \/ empty \/ next
non-match), which composes via [product] with a delimiter byte.

The char↔byte roundtrip induction lives in the child module
[Data.Text.Codec.Chars] (fstar-proofs §44 workaround #1): it proves the
per-char ASCII fact and the char→byte→char map roundtrip in a clean
child module that does not open any codec combinator, so the
[char_of_int] / [char_of_u32] SMTPat family (§18) does not pollute this
module's SMT context and the recursive induction does not re-verify.

Delimiter codecs (CRLF, SP) live in the sibling module
[Data.Text.Codec.Delims] rather than here — a [map_]/[product]/[byte_val]
chain defined after [text_chars] pollutes the SMT context and breaks the
[text_chars] [custom] roundtrip verification (fstar-proofs §45).  Keeping
this module a single combinator keeps [text_chars] fully verified.

@header Data.Text.Codec
*)
module Data.Text.Codec

open Data.Codec
open Data.Text.Codec.Chars
open FStar.Seq
open FStar.Seq.Properties
open FStar.Char
open FStar.String
open FStar.List.Tot

module Seq = FStar.Seq

(* ── Bounded greedy scan (build order: scanner → its lemmas) ──────── *)

(** [scan_text_chars max pred input] — bounded greedy scan of a [byte_seq],
    returning the longest matchable prefix (in order) up to [max] bytes.
    Recurse on the sliced suffix.

    Stops at (a) [max] bytes consumed, (b) end of input, or (c) the first
    non-matching byte — whichever comes first.  This bounded form is what
    makes the codec invertible (fstar-proofs §43). *)
let rec scan_text_chars (max: nat) (pred: FStar.Char.char -> bool) (input: byte_seq)
  : Tot (list byte) (decreases (Seq.length input + max))
  = if max = 0 then []
    else if Seq.length input = 0 then []
    else begin
      let b = Seq.index input 0 in
      if byte_matchable pred b then
        b :: scan_text_chars (max - 1) pred (FStar.Seq.Properties.tail input)
      else []
    end

(** [lemma_scan_consumed_le_len max pred input] — the bounded greedy scan
    consumes at most [|input|] bytes.

    Induct on the input length + bound.  When the head byte is matchable,
    the scan consumes one byte plus the recursive scan of the tail, and
    the tail has length one less than the input. *)
#push-options "--z3rlimit 400"
let rec lemma_scan_consumed_le_len (max: nat) (pred: FStar.Char.char -> bool) (input: byte_seq)
  : Lemma
    (ensures List.Tot.length (scan_text_chars max pred input) <= Seq.length input)
    (decreases (Seq.length input + max))
  = if max = 0 then ()
    else if Seq.length input = 0 then ()
    else begin
      let b = Seq.index input 0 in
      if byte_matchable pred b then begin
        lemma_scan_consumed_le_len (max - 1) pred (FStar.Seq.Properties.tail input);
        assert (List.Tot.length (scan_text_chars max pred input)
                == 1 + List.Tot.length (scan_text_chars (max - 1) pred (FStar.Seq.Properties.tail input)));
        ()
      end else ()
    end
#pop-options

(** [lemma_scan_prefix max pred bs r] — a well-formed matchable prefix scans
    to its own length.

    When [bs] is entirely matchable, [|bs| <= max], and the suffix [r]
    begins with a non-matchable byte (or is empty, or [bs] fills the
    whole bound), scanning [seq_of_list bs ++ r] from 0 consumes
    exactly [bs].  The 3-disjunct precondition mirrors the [rest_cond]
    of the codec. *)
#push-options "--z3rlimit 400"
#restart-solver
let rec lemma_scan_prefix (max: nat) (pred: FStar.Char.char -> bool) (bs: list byte) (r: byte_seq)
  : Lemma
    (requires
      List.Tot.for_all (byte_matchable pred) bs /\
      List.Tot.length bs <= max /\
      (List.Tot.length bs = max \/
       Seq.length r = 0 \/
       (Seq.length r > 0 /\ not (byte_matchable pred (Seq.index r 0)))))
    (ensures scan_text_chars max pred (seq_of_list bs `Seq.append` r) == bs)
    (decreases bs)
  =
    match bs with
    | [] -> ()
    | b :: tl ->
        Seq.lemma_seq_of_list_cons b tl;
        Seq.append_assoc (Seq.create 1 b) (seq_of_list tl) r;
        Seq.Properties.append_slices (Seq.create 1 b) (seq_of_list tl `Seq.append` r);
        lemma_scan_prefix (max - 1) pred tl r;
        ()
#pop-options

(* ── text_chars codec plumbing (decoder/encoder/guards) ─────────────── *)

(** [text_chars_dec max pred input] — the [text_chars] decoder: bounded greedy
    scan, then string conversion.

    Requires the scan to consume at least one byte (a non-empty match),
    so [text_chars] matches one-or-more characters. *)
let text_chars_dec (max: nat) (pred: FStar.Char.char -> bool) (input: byte_seq) : Tot (decode_result string) =
  let consumed = scan_text_chars max pred input in
  if Cons? consumed then Inr (text_bytes_to_string consumed, List.Tot.length consumed)
  else Inl (mk_decode_error ExpectedPredicate 0)

(** [text_chars_enc pred s] — the [text_chars] encoder: string to its byte
    sequence.

    NOTE: [pred] is bound but NOT consulted in the body — the encoder emits
    every character's low byte unconditionally.  This is by design: the
    encoder is UNGUARDED, and well-formedness is enforced only by the
    [text_chars_wfcv] guard (all-ASCII + [pred]) that every roundtrip proof
    carries.  [pred] is present because [custom] requires the encoder to be
    a [string -> byte_seq] function reachable by partial application
    ([text_chars_enc pred]); it is a structural parameter, not a filter. *)
unfold
let text_chars_enc (pred: FStar.Char.char -> bool) (s: string) : Tot byte_seq =
  seq_of_list (text_string_to_bytes s)

(** [text_chars_wfcv max pred s] — guard: the string is non-empty, at most
    [max] chars, all-ASCII, and every character satisfies [pred].  Marked
    [unfold] so SMT can reduce it across module boundaries when a composed
    codec's [.roundtrip] field re-asserts it (fstar-proofs §54 Trap 1). *)
unfold
let text_chars_wfcv (max: nat) (pred: FStar.Char.char -> bool) (s: string) : bool =
  let chars = FStar.String.list_of_string s in
  Cons? chars &&
  List.Tot.length chars <= max &&
  List.Tot.for_all (ascii_ok pred) chars

(** [text_chars_wfcv_prop max pred s] — well-formed proposition — [True].

    SOUND because the boolean [text_chars_wfcv] fully characterizes
    well-formedness (non-empty + length bound + all-ASCII-matchable), and
    the roundtrip lemma's [requires] carries [text_chars_wfcv] directly, so
    the prop need not re-state the check.  Keeping it [True] avoids a
    redundant duplicate obligation in the [custom] combinator's internal
    [wfcv_prop] assertion (fstar-proofs §18).  Marked [unfold] (§54 Trap 1). *)
unfold
let text_chars_wfcv_prop (max: nat) (pred: FStar.Char.char -> bool) (s: string) : prop =
  True

(** [text_chars_rest_cond max pred s r] — suffix condition — the 3-disjunct
    bounded-greedy shape: either the encoded run fills the whole bound, or
    the suffix is empty, or the byte after the run is not matchable.  Marked
    [unfold] (§54 Trap 1). *)
unfold
let text_chars_rest_cond (max: nat) (pred: FStar.Char.char -> bool) (s: string) (r: byte_seq) : prop =
  let n = List.Tot.length (text_string_to_bytes s) in
  n = max \/ Seq.length r = 0 \/ (Seq.length r > 0 && not (byte_matchable pred (Seq.index r 0)))

(* ── Roundtrip lemmas (alphabetical) ───────────────────────────────── *)

(** [lemma_text_chars_dec_err_bound max pred input] — error-position bound for
    [text_chars_dec].  The only error is the empty-match case, at position 0,
    so the bound holds trivially. *)
let lemma_text_chars_dec_err_bound (max: nat) (pred: FStar.Char.char -> bool) (input: byte_seq) : Lemma
  (ensures (match text_chars_dec max pred input with
            | Inl err -> err.err_pos <= Seq.length input
            | _ -> True))
  = ()

(** [lemma_text_chars_dec_consumed_bound max pred input] — consumed-count bound
    for [text_chars_dec].  The consumed count is exactly [|scan|], which
    [lemma_scan_consumed_le_len] bounds by the input length. *)
#push-options "--z3rlimit 400"
let lemma_text_chars_dec_consumed_bound (max: nat) (pred: FStar.Char.char -> bool) (input: byte_seq) : Lemma
  (ensures (match text_chars_dec max pred input with
            | Inr (_, n) -> n <= Seq.length input
            | _ -> True))
  = if Cons? (scan_text_chars max pred input) then begin
      lemma_scan_consumed_le_len max pred input;
      ()
    end else ()
#pop-options

(** [lemma_text_chars_roundtrip max pred s r] — roundtrip proof for [text_chars].

    The bounded greedy scan ([lemma_scan_prefix]), the char↔byte map
    roundtrip ([lemma_chars_roundtrip_all]), and the string roundtrip
    ([lemma_text_string_to_bytes_roundtrip]) — all from the clean child
    module — establish matchability and string identity, then the bounded
    scan result is connected to the decoder's [Inr] payload. *)
#push-options "--z3rlimit 4000"
let lemma_text_chars_roundtrip (max: nat) (pred: FStar.Char.char -> bool) (s: string) (r: byte_seq)
  : Lemma
    (requires
      text_chars_wfcv max pred s /\
      text_chars_wfcv_prop max pred s /\
      text_chars_rest_cond max pred s r)
    (ensures
      text_chars_dec max pred (text_chars_enc pred s `Seq.append` r)
        == Inr (s, Seq.length (text_chars_enc pred s)))
  =
    let chars = FStar.String.list_of_string s in
    let bs = text_string_to_bytes s in
    assert (Cons? chars);
    assert (List.Tot.length chars <= max);
    assert (List.Tot.for_all (ascii_ok pred) chars);
    lemma_chars_roundtrip_all pred chars;
    assert (List.Tot.for_all (byte_matchable pred) bs);
    lemma_text_string_to_bytes_roundtrip pred s;
    assert (text_bytes_to_string bs == s);
    assert (List.Tot.length bs = List.Tot.length chars);
    assert (List.Tot.length bs <= max);
    assert (Cons? bs);
    lemma_scan_prefix max pred bs r;
    assert (scan_text_chars max pred (seq_of_list bs `Seq.append` r) == bs);
    assert (Seq.length (text_chars_enc pred s) == List.Tot.length bs);
    let input = text_chars_enc pred s `Seq.append` r in
    assert (scan_text_chars max pred input == bs);
    assert (text_chars_dec max pred input == Inr (text_bytes_to_string bs, List.Tot.length bs));
    assert (text_chars_dec max pred input == Inr (s, List.Tot.length bs));
    assert (text_chars_dec max pred input == Inr (s, Seq.length (text_chars_enc pred s)));
    ()
#pop-options

(* ── Combinator ─────────────────────────────────────────────────────── *)

(** [text_chars max pred] — match one or more ASCII chars satisfying [pred],
    as a [string].

    The decoder is BOUNDED greedy — it consumes at most [max] matchable
    bytes (fstar-proofs §43).  This keeps the codec invertible and
    composable via [product] with a following delimiter byte.

    @param max The maximum number of bytes the decoder may consume.
    @param pred The per-character predicate (ASCII, code point < 128). *)
#push-options "--z3rlimit 2000"
let text_chars (max: nat) (pred: FStar.Char.char -> bool) : codec string =
  custom
    (text_chars_dec max pred)
    (text_chars_enc pred)
    (text_chars_wfcv max pred)
    (text_chars_wfcv_prop max pred)
    (text_chars_rest_cond max pred)
    (lemma_text_chars_roundtrip max pred)
    (lemma_text_chars_dec_err_bound max pred)
    (lemma_text_chars_dec_consumed_bound max pred)
#pop-options
