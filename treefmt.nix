# Copyright 2026 Department of Code LLC.
# SPDX-License-Identifier: AGPL-3.0-or-later

# treefmt formatting config (evaluated by treefmt-nix `evalModule`).
#
# Formats nix (`*.nix`) only.
#
# F* sources (`*.fst`/`*.fsti`) are deliberately NOT formatted: the only F*
# formatters — `fstar.exe --ide` `format` and `fstar.exe --print`/
# `--print_in_place` — are broken upstream in `v2026.09.20+lsp`.  They crash
# with "Pattern matching failed" in `FStarC_Parser_ToDocument.ml` on
# `#lang-pulse` modules, and rewrite `(* … *)` inline comments into `//` line
# comments (which F* can't parse — Error 168), plus lower-case hex literals.
# The `.fst`/`.fsti` files stay hand-formatted.
#
# Markdown (`*.md`) is also left out: the prose docs (AGENTS.md, README.md,
# API.md, LICENSE/CHANGELOG) are hand-written with intentional double-space
# sentence gaps and `*`/`F*` emphasis that prettier rewrites into churn.
# `../fstar-codec/treefmt.nix` makes the same call (it excludes `*.md`).

_: {
  projectRootFile = "flake.nix";

  programs.nixfmt.enable = true;
  programs.deadnix.enable = true; # scan .nix files for dead code
  programs.statix.enable = true; # lint .nix files

  settings.excludes = [
    "out/**"
    "spike/**"
    ".git/**"
    "flake.lock"
  ];

  settings.includeExcludes = true;
}
