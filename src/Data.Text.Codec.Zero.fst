(**
Data.Text.Codec.Zero — the empty-aware text combinator [text_chars0].

[text_chars] matches ONE-or-more ASCII characters; [text_chars0] is the
zero-or-more form — the empty string [""] is representable.  It is the
generic sibling of [text_chars], not an XML-specific combinator: any
delimiter-bracketed or suffix-delimited text run that permits empty (HTTP
OWS, MIME parameter values, XML attribute values, etc.) is this shape.

It lives in its own module (NOT [Data.Text.Codec]) for the same reason as
[Data.Text.Codec.Delims]: the §45 SMT-context-pollution discipline — a
second [custom] combinator in [Data.Text.Codec] would re-trigger the
opacity that keeps [text_chars] at 0 admits.  The bounded-greedy scan and
its induction lemmas are re-bound here (self-contained [let rec], fstar-proofs
§44 — cross-module [let rec] is opaque); only the PURE char↔byte maps and
their roundtrip lemmas are reused from [Data.Text.Codec.Chars] (§44 workaround
#1, which is transparent and non-recursive).

The empty case is the ONLY difference from [text_chars]: the decoder returns
[Inr ("", 0)] when the scan matches nothing (instead of [Inl]), and the
[wfcv] guard drops the non-empty ([Cons? chars]) requirement.  The scan,
[rest_cond], and encode are unchanged — they already admit the empty run.

@header Data.Text.Codec.Zero
*)
module Data.Text.Codec.Zero

open Data.Codec
open Data.Text.Codec.Chars
open FStar.Seq
open FStar.Seq.Properties
open FStar.Char
open FStar.String
open FStar.List.Tot

module Seq = FStar.Seq

(* ── Bounded greedy scan (build order: scanner → its lemmas) ──────── *)

(** [scan_text_chars0 max pred input] — BOUNDED greedy scan of a [byte_seq],
    returning the longest matchable prefix (in order) up to [max] bytes —
    identical to [Data.Text.Codec]'s [scan_text_chars], re-bound here so no
    [let rec] crosses a module boundary (fstar-proofs §44). *)
let rec scan_text_chars0 (max: nat) (pred: FStar.Char.char -> bool) (input: byte_seq)
  : Tot (list byte) (decreases (Seq.length input + max))
  = if max = 0 then []
    else if Seq.length input = 0 then []
    else begin
      let b = Seq.index input 0 in
      if byte_matchable pred b then
        b :: scan_text_chars0 (max - 1) pred (FStar.Seq.Properties.tail input)
      else []
    end

(** [lemma_scan0_consumed_le_len max pred input] — the bounded greedy scan
    consumes at most [|input|] bytes. *)
#push-options "--z3rlimit 400"
let rec lemma_scan0_consumed_le_len (max: nat) (pred: FStar.Char.char -> bool) (input: byte_seq)
  : Lemma
    (ensures List.Tot.length (scan_text_chars0 max pred input) <= Seq.length input)
    (decreases (Seq.length input + max))
  = if max = 0 then ()
    else if Seq.length input = 0 then ()
    else begin
      let b = Seq.index input 0 in
      if byte_matchable pred b then begin
        lemma_scan0_consumed_le_len (max - 1) pred (FStar.Seq.Properties.tail input);
        assert (List.Tot.length (scan_text_chars0 max pred input)
                == 1 + List.Tot.length (scan_text_chars0 (max - 1) pred (FStar.Seq.Properties.tail input)));
        ()
      end else ()
    end
#pop-options

(** [lemma_scan0_prefix max pred bs r] — a well-formed matchable prefix
    (possibly EMPTY) scans to its own length. *)
#push-options "--z3rlimit 400"
#restart-solver
let rec lemma_scan0_prefix (max: nat) (pred: FStar.Char.char -> bool) (bs: list byte) (r: byte_seq)
  : Lemma
    (requires
      List.Tot.for_all (byte_matchable pred) bs /\
      List.Tot.length bs <= max /\
      (List.Tot.length bs = max \/
       Seq.length r = 0 \/
       (Seq.length r > 0 /\ not (byte_matchable pred (Seq.index r 0)))))
    (ensures scan_text_chars0 max pred (seq_of_list bs `Seq.append` r) == bs)
    (decreases bs)
  =
    match bs with
    | [] -> ()
    | b :: tl ->
        Seq.lemma_seq_of_list_cons b tl;
        Seq.append_assoc (Seq.create 1 b) (seq_of_list tl) r;
        Seq.Properties.append_slices (Seq.create 1 b) (seq_of_list tl `Seq.append` r);
        lemma_scan0_prefix (max - 1) pred tl r;
        ()
#pop-options

(* ── text_chars0 codec plumbing (decoder/encoder/guards) ────────────── *)

(** [text_chars0_dec max pred input] — the [text_chars0] decoder: bounded
    greedy scan, then string conversion.

    UNLIKE [text_chars_dec], an empty match is ACCEPTED: the empty scan (when
    the next byte is the delimiter, or input is exhausted) decodes to [""]. *)
let text_chars0_dec (max: nat) (pred: FStar.Char.char -> bool) (input: byte_seq) : Tot (decode_result string) =
  let consumed = scan_text_chars0 max pred input in
  Inr (text_bytes_to_string consumed, List.Tot.length consumed)

(** [text_chars0_enc pred s] — the [text_chars0] encoder: string to its byte
    sequence (empty → empty). *)
unfold
let text_chars0_enc (pred: FStar.Char.char -> bool) (s: string) : Tot byte_seq =
  seq_of_list (text_string_to_bytes s)

(** [text_chars0_wfcv max pred s] — guard: the string is at most [max] chars,
    all-ASCII, every char satisfies [pred] — NO non-empty requirement (empty is
    allowed).  Marked [unfold] so [.roundtrip]'s internal
    [assert (wfcv_custom v)] discharges at cross-module call sites (§15/§18). *)
unfold
let text_chars0_wfcv (max: nat) (pred: FStar.Char.char -> bool) (s: string) : bool =
  let chars = FStar.String.list_of_string s in
  List.Tot.length chars <= max &&
  List.Tot.for_all (ascii_ok pred) chars

(** [text_chars0_wfcv_prop max pred s] — well-formed proposition — [True]
    (the boolean guard carries the check). *)
unfold
let text_chars0_wfcv_prop (max: nat) (pred: FStar.Char.char -> bool) (s: string) : prop =
  True

(** [text_chars0_rest_cond max pred s r] — suffix condition — the same
    3-disjunct bounded-greedy shape as [text_chars]: the run fills the bound,
    or the suffix is empty, or the byte after the run is not matchable.  For
    the empty run this reduces to [0 = max \/ |r| = 0 \/ (|r| > 0 /\ not
    matchable (r[0]))]. *)
unfold
let text_chars0_rest_cond (max: nat) (pred: FStar.Char.char -> bool) (s: string) (r: byte_seq) : prop =
  let n = List.Tot.length (text_string_to_bytes s) in
  n = max \/ Seq.length r = 0 \/ (Seq.length r > 0 && not (byte_matchable pred (Seq.index r 0)))

(* ── Roundtrip lemmas (alphabetical) ───────────────────────────────── *)

(** [lemma_text_chars0_dec_err_bound max pred input] — error-position bound for
    [text_chars0_dec] (never errors — always [Inr]). *)
let lemma_text_chars0_dec_err_bound (max: nat) (pred: FStar.Char.char -> bool) (input: byte_seq) : Lemma
  (ensures (match text_chars0_dec max pred input with
            | Inl err -> err.err_pos <= Seq.length input
            | _ -> True))
  = ()

(** [lemma_text_chars0_dec_consumed_bound max pred input] — consumed-count
    bound for [text_chars0_dec]. *)
#push-options "--z3rlimit 400"
let lemma_text_chars0_dec_consumed_bound (max: nat) (pred: FStar.Char.char -> bool) (input: byte_seq) : Lemma
  (ensures (match text_chars0_dec max pred input with
            | Inr (_, n) -> n <= Seq.length input
            | _ -> True))
  = lemma_scan0_consumed_le_len max pred input
#pop-options

(** [lemma_text_chars0_roundtrip max pred s r] — roundtrip proof for
    [text_chars0] (empty and non-empty alike).

    Mirrors [Data.Text.Codec.lemma_text_chars_roundtrip] but with the
    [Cons? chars] non-empty requirement dropped — the scan lemma already
    covers the [bs = []] case, and [text_chars0_dec] accepts the empty scan. *)
#push-options "--z3rlimit 4000"
let lemma_text_chars0_roundtrip (max: nat) (pred: FStar.Char.char -> bool) (s: string) (r: byte_seq)
  : Lemma
    (requires
      text_chars0_wfcv max pred s /\
      text_chars0_wfcv_prop max pred s /\
      text_chars0_rest_cond max pred s r)
    (ensures
      text_chars0_dec max pred (text_chars0_enc pred s `Seq.append` r)
        == Inr (s, Seq.length (text_chars0_enc pred s)))
  =
    let chars = FStar.String.list_of_string s in
    let bs = text_string_to_bytes s in
    assert (List.Tot.length chars <= max);
    assert (List.Tot.for_all (ascii_ok pred) chars);
    lemma_chars_roundtrip_all pred chars;
    assert (List.Tot.for_all (byte_matchable pred) bs);
    lemma_text_string_to_bytes_roundtrip pred s;
    assert (text_bytes_to_string bs == s);
    assert (List.Tot.length bs = List.Tot.length chars);
    assert (List.Tot.length bs <= max);
    lemma_scan0_prefix max pred bs r;
    assert (scan_text_chars0 max pred (seq_of_list bs `Seq.append` r) == bs);
    assert (Seq.length (text_chars0_enc pred s) == List.Tot.length bs);
    let input = text_chars0_enc pred s `Seq.append` r in
    assert (scan_text_chars0 max pred input == bs);
    assert (text_chars0_dec max pred input == Inr (text_bytes_to_string bs, List.Tot.length bs));
    assert (text_chars0_dec max pred input == Inr (s, List.Tot.length bs));
    assert (text_chars0_dec max pred input == Inr (s, Seq.length (text_chars0_enc pred s)));
    ()
#pop-options

(** [lemma_text_chars0_empty_roundtrip max pred] — concrete empty-roundtrip
    vector: the empty string roundtrips against an empty suffix, proving the
    zero-or-more (empty-representable) semantics at a closed value (the one
    behavior that distinguished [text_chars0] from [text_chars]). *)
#push-options "--z3rlimit 400"
let lemma_text_chars0_empty_roundtrip (max: nat) (pred: FStar.Char.char -> bool) : Lemma
  (requires text_chars0_wfcv max pred "" /\ text_chars0_rest_cond max pred "" Seq.empty)
  (ensures text_chars0_dec max pred (text_chars0_enc pred "" `Seq.append` Seq.empty)
           == Inr ("", 0))
  = lemma_text_chars0_roundtrip max pred "" Seq.empty
#pop-options

(* ── Combinator ─────────────────────────────────────────────────────── *)

(** [text_chars0 max pred] — match ZERO or more ASCII chars satisfying [pred],
    as a [string].  The empty string is representable (encodes to zero bytes).

    @param max The maximum number of bytes the decoder may consume.
    @param pred The per-character predicate (ASCII, code point < 128). *)
#push-options "--z3rlimit 2000"
let text_chars0 (max: nat) (pred: FStar.Char.char -> bool) : codec string =
  custom
    (text_chars0_dec max pred)
    (text_chars0_enc pred)
    (text_chars0_wfcv max pred)
    (text_chars0_wfcv_prop max pred)
    (text_chars0_rest_cond max pred)
    (lemma_text_chars0_roundtrip max pred)
    (lemma_text_chars0_dec_err_bound max pred)
    (lemma_text_chars0_dec_consumed_bound max pred)
#pop-options
