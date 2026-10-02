# text — Agent Guide & Handoff

`Data.Text.Codec` — verified text codec library, extracted from the xeno
monorepo, built on `Data.Codec`.  F* source is 0-admit.  This file records the
completed Pulse port so the next session resumes cleanly.

## ⛔ MANDATES (binding — read before doing anything)

1. **NEVER run `fstar.exe`, `nix build`, or `make` in the foreground.**  They
   can hang forever.  **Always** run them **detached** and poll the log:

   ```bash
   cd /Users/user/_/text
   rm -f /tmp/text-build.log
   nohup nix build .#checked --print-out-paths --no-link > /tmp/text-build.log 2>&1 &
   # … poll: tail /tmp/text-build.log ; ps -p $!
   ```

   A stuck process (0% CPU `stopped`, or 100% CPU spin) is a hang — kill it,
   diagnose, don't wait.  Per-step budgets: fstar verify ≤ 10 min, `nix build`
   ≤ 15 min (but the F\* bootstrap itself takes ~20 min *only on first build*;
   it is now cached).

2. **The F\* overlay in `flake.nix` MUST stay byte-identical to
   `codec`/`basen`'s.**  Any comment/whitespace change to the
   `buildPhase`/`installPhase` strings changes the derivation hash and forces a
   full F\* bootstrap.  Do NOT touch those strings.

## ✅ Current state — Pulse port DONE, 4/4 targets GREEN (this session)

The KaRaMeL→Custard port is complete and verified 0-admit.  The old
`src/Data.Text.Codec.Low` (KaRaMeL Low\*: `FStar.HyperStack.ST`,
`LowStar.Buffer`, `Stack`) was **deleted** (Low\* stdlib removed in
`v2026.09.20`), replaced by `src/Data.Text.Codec.Pulse.fst` (`#lang-pulse`).

### Build matrix (verified this session, F* `v2026.09.20+lsp`)

| Target | Status | Output |
|---|---|---|
| `checked` | ✅ GREEN 0-admit | 14 modules verified (7 src + 7 test) |
| `native` (C) | ✅ GREEN | `Custard.c`/`Custard.h`/`text.h`, `libtext.{dylib,a}` (C11, no karamel) |
| `ocaml` | ✅ GREEN | findlib `text-ocaml` |
| `fsharp` (.NET) | ✅ GREEN | `Custard.dll` (.NET 10) |

Target names: `default = native`, `checked`, `ocaml`, `native`, `fsharp`.
`nix flake check` is GREEN.

### The OCaml cross-repo fix (this session)

`Data.Text.Codec`'s pure modules `open Data.Codec` (which `include`s
`Data.Codec.Types`), so the OCaml-extracted `.ml` files reference the *bare*
top-level modules `Data_Codec_Types`/`Data_Codec`.  `codec`'s
`codec-ocaml` findlib package **wraps** its modules into a `Codec.*` namespace
(dune `(wrapped true)` default), so the bare names are unbound.

**Fix (landed):** the `default.nix` `ocaml-src` derivation now extracts the
codec's pure spec (`Data.Codec.Types` + `Data.Codec`) **locally** via
`--codegen OCaml` from `codec-src`, compiles them into the `text-ocaml` dune
library alongside text's own modules, and drops the `codec-ocaml` findlib
dependency.  No `Custard` collision: only the codec *pure* spec is extracted,
never its Pulse leaf.  This is the same "compile the codec spec locally,
unwrapped" shape `codec` itself uses (there `pure-modules` *is* the codec
spec).

### Roll-forward fixes (landed, 0-admit preserved)

- `src/Data.Text.Codec.Chars.fst` / `src/Data.Text.Codec.UTF8.fst`: removed
  `open FStar.Mul` (module deleted in v2026.09.20; `*` is now natively
  multiplication).
- `src/Data.Text.Codec.fst` / `.Zero.fst` / `.UTF8String.fst`: removed
  `--split_queries always` from `#push-options` (option deleted).
- `test/Data.Text.Codec.Test.UTF8.fst`: `FStar.Classical.forall_intro_2`
  needed an explicit `#p` predicate + `#b` argument — in v2026.09.20 the
  implicit `p` (which "only occurs in a pre/postcondition") is no longer
  inferred from a bare lambda.  Annotated the three implicit args explicitly.
- `test/Data.Text.Codec.Test.Integration.fst`: `open …Low` →
  `open …Pulse`; dropped the `FStar.HyperStack`/`LowStar.Buffer` opens; the
  `_l10`/`_l11` anchors now point at `lemma_pulse_roundtrip` /
  `lemma_pulse_encode_decode_match` (the retired `lemma_encode_match` /
  `lemma_decode_match` are gone).

## Architecture (post-port)

```
Data.Text.Codec          — text_chars combinator + scan/roundtrip lemmas (pure)
Data.Text.Codec.Chars    — pure char↔byte maps + ASCII roundtrip induction
Data.Text.Codec.Delims   — CRLF + SP delimiter codecs
Data.Text.Codec.Zero     — empty-aware text_chars0 combinator
Data.Text.Codec.UTF8     — RFC 3629 UTF-8 encode/decode + roundtrip proof
Data.Text.Codec.UTF8String — UTF-8-aware codec string
Data.Text.Codec.Pulse    — C-extractable text-encoding tag codec (Custard)
```

The Pulse leaf is trivial compared to `codec`/`basen`: a single
1-byte tag (`TE_ASCII` 0x00 / `TE_UTF8` 0x01 / `TE_UTF16` 0x02), `encode`/
`decode` (`A.array U8.t`, `fn`), plus `lemma_roundtrip` (pure),
`lemma_pulse_roundtrip`, `lemma_pulse_encode_decode_match`.  No varint, no
multi-byte arithmetic — so none of the varint/word32 SMT-hang complexity from
`codec` applies here.

## The codec dependency

`text` consumes `Data.Codec` from the **published** `dysinger/codec`
repo (flake input `codec`, pinned in `flake.lock`), NOT a vendored copy.
The KaRaMeL-era vendored `./codec/` tree was deleted.  `codec-src` (the flake
input tree) provides the `.fst` sources for `--include`; `codec-checked`
(`codec.packages.<system>.checked`) seeds the `.checked` cache.

## Build commands

```bash
nix build .#checked   # F* verification gate (0-admit)
nix build .#native    # C11 shared/static lib (default)
nix build .#ocaml     # OCaml findlib package
nix build .#fsharp    # .NET library
nix develop && make check   # dev loop (no nix)
```

## Reference

- Canonical references: `../codec` (the codec, incl. its `Data.Codec.Pulse`)
  and `../basen` (the same downstream-dependency shape, `Data.BaseN.Pulse`).
- The F\* skill: `~/.pi/agent/skills/fstar/fstar-2026.09.20/SKILL.md`
  (Custard, Pulse idiom, `U8.v`/`U32.v` → `Int.Cast`, the dead-Low\* delta).
