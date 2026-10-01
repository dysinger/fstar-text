(**
Data.Text.Codec.Delims — Text delimiter codecs.

CRLF (carriage return + line feed) and SP (single space) are the two
byte-level delimiter codecs shared by text protocols (HTTP, SMTP, MIME,
etc.).  They live in their own module rather than [Data.Text.Codec]
because a [map_]/[product]/[byte_val] chain defined AFTER [text_chars] in
the same module pollutes the SMT context and breaks the [text_chars]
[custom] roundtrip verification (fstar-proofs §45).

@header Data.Text.Codec.Delims
*)
module Data.Text.Codec.Delims

open Data.Codec

(* ── Delimiter codecs (alphabetical) ────────────────────────────────── *)

(** [crlf] — CRLF: carriage return (0x0D) followed by line feed (0x0A). *)
let crlf : codec unit =
  map_ (fun (_, _) -> Some ()) (fun _ -> Some ((), ()))
    (product (byte_val 0x0Duy) (byte_val 0x0Auy))

(** [sp] — SP: single space (0x20). *)
let sp : codec unit = byte_val 0x20uy
