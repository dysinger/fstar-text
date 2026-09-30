(**
Data.Codec — Derived combinators, operator aliases, and character predicates.

Re-exports all 19 base combinators from [Data.Codec.Types] via [include].

@header Data.Codec
*)
module Data.Codec

open FStar.Seq

include Data.Codec.Types

module U8 = FStar.UInt8

(** Derived Combinators *)

let choice (#a:Type) (c1 c2: codec a) : codec a =
  map_ (fun (v: either a a) -> match v with | Inl x -> Some x | Inr x -> Some x)
       (fun (x: a) ->
         if c1.wfcv x then Some (Inl x)
         else if c2.wfcv x then Some (Inr x)
         else None)
       (sum c1 c2)

let lemma_choice_c1_dominates (#a:Type) (c1 c2: codec a) (x: a) : Lemma
  (requires c1.wfcv x /\ c2.wfcv x)
  (ensures (choice c1 c2).enc x == Seq.cons 0x00uy (c1.enc x))
  = assert ((choice c1 c2).enc x == (sum c1 c2).enc (Inl x));
    assert ((sum c1 c2).enc (Inl x) == Seq.cons 0x00uy (c1.enc x));
    ()

let lemma_choice_c2_dominates (#a:Type) (c1 c2: codec a) (x: a) : Lemma
  (requires not (c1.wfcv x) /\ c2.wfcv x)
  (ensures (choice c1 c2).enc x == Seq.cons 0x01uy (c2.enc x))
  = assert ((choice c1 c2).enc x == (sum c1 c2).enc (Inr x));
    assert ((sum c1 c2).enc (Inr x) == Seq.cons 0x01uy (c2.enc x));
    ()

let then_drop (#a:Type) (c1: codec unit) (c2: codec a) : codec a =
  map_ (fun (_, v) -> Some v) (fun v -> Some ((), v)) (product c1 c2)

let drop_then (#a:Type) (c1: codec a) (c2: codec unit) : codec a =
  map_ (fun (v, _) -> Some v) (fun v -> Some (v, ())) (product c1 c2)

let ( *> ) (#a:Type) (c1: codec unit) (c2: codec a) : codec a = then_drop c1 c2

let ( <* ) (#a:Type) (c1: codec a) (c2: codec unit) : codec a = drop_then c1 c2

let ( <|> ) (#a:Type) (c1 c2: codec a) : codec a = choice c1 c2

let between (#a:Type) (open_ close: codec unit) (c: codec a) : codec a =
  map_ (fun ((_, v), _) -> Some v)
       (fun v -> Some (((), v), ()))
       (product (product open_ c) close)

let optional (#a:Type) (c: codec a) : codec (option a) =
  map_ (fun (v: either a unit) -> match v with | Inl x -> Some (Some x) | Inr _ -> Some None)
       (fun (opt: option a) -> match opt with | Some x -> Some (Inl x) | None -> Some (Inr ()))
       (sum c (pure ()))

let take (n: nat) : codec (list byte) = count n token

(** Backward-compat aliases *)

let word16_be = word16be
let word32_be = word32be
let word16_le = word16le
let word32_le = word32le
let varint_codec = varint
let map (#a #b: Type) (f: a -> Tot (option b)) (g: b -> Tot (option a)) (c: codec a) : codec b = map_ f g c
let equiv_map = map_
let digits_to_integer = digits_to_int
let digits_to_int_alias = digits_to_int

(** Character predicates *)

let is_upper (b: byte) : bool =
  let v = U8.v b in 0x41 <= v && v <= 0x5A

let is_lower (b: byte) : bool =
  let v = U8.v b in 0x61 <= v && v <= 0x7A

let is_alpha (b: byte) : bool = is_upper b || is_lower b

let is_alphanum (b: byte) : bool = is_alpha b || is_digit b

let is_space_or_tab (b: byte) : bool =
  let v = U8.v b in v = 0x20 || v = 0x09

let is_whitespace (b: byte) : bool =
  let v = U8.v b in v = 0x20 || v = 0x09 || v = 0x0D || v = 0x0A

let is_printable (b: byte) : bool =
  let v = U8.v b in 0x20 <= v && v <= 0x7E

let char_to_byte (c: FStar.Char.char) : byte =
  U8.uint_to_t (FStar.Char.int_of_char c % 256)

let char_is_digit (c: FStar.Char.char) : bool =
  is_digit (char_to_byte c)

let char_is_upper (c: FStar.Char.char) : bool =
  is_upper (char_to_byte c)

let char_is_lower (c: FStar.Char.char) : bool =
  is_lower (char_to_byte c)

let char_is_alpha (c: FStar.Char.char) : bool =
  is_alpha (char_to_byte c)

let char_is_alphanum (c: FStar.Char.char) : bool =
  is_alphanum (char_to_byte c)

let char_is_space_or_tab (c: FStar.Char.char) : bool =
  is_space_or_tab (char_to_byte c)

let char_is_whitespace (c: FStar.Char.char) : bool =
  is_whitespace (char_to_byte c)

let char_is_printable (c: FStar.Char.char) : bool =
  is_printable (char_to_byte c)

let digit_byte : codec byte = satisfy is_digit
