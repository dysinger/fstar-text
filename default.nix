# Copyright 2026 Department of Code LLC.
# SPDX-License-Identifier: AGPL-3.0-or-later

# text — Data.Text.Codec verified text codec library.
#
# Takes the F* toolchain as concrete derivations (no `pkgs` blob, no overlay
# assumption, no module-name/order arguments).  Module names and their
# dependency order live in the Makefile (the no-nix build); `checked` delegates
# to `make check`, exporting the toolchain paths the Makefile already reads.
#
# The codec dependency (Data.Codec.Types) is injected as a source dir +
# pre-verified `.checked` cache (`codec-src` / `codec-checked`), sourced from
# the separate `fstar-codec` flake input in flake.nix.
#
# Artifacts (named by deliverable, not by backend):
#   - `checked` — F* verification of src/ + test/ (the 0-admit gate).
#   - `ocaml`   — findlib package shipping ALL OCaml-extractable modules:
#                 the pure spec (Chars/Codec/Delims/Zero/UTF8/UTF8String) AND
#                 the Pulse leaf (Data.Text.Codec.Pulse, `--custard_backend
#                 OCaml`) as one dune library.
#   - `native`  — C11 shared/static lib of the Pulse leaf (Data.Text.Codec.Pulse,
#                 `--custard_backend C`), no karamel.
#   - `fsharp`  — .NET library of the Pulse leaf (`--custard_backend FSharp`).
#
# Returns { checked; ocaml; native; fsharp; }.

{
  fstar,
  fstar-checked,
  lib,
  ocamlPackages,
  stdenv,
  dotnet,
  codec-src,
  codec-checked,
}:

let
  inherit (stdenv) mkDerivation;

  # Package name.  The package is "text" (git repo "fstar-text"), but the internal
  # derivation/artifact names drop the "fstar-" prefix.
  pname = "text";

  pure-modules = [
    "Data.Text.Codec.Chars"
    "Data.Text.Codec"
    "Data.Text.Codec.Delims"
    "Data.Text.Codec.Zero"
    "Data.Text.Codec.UTF8"
    "Data.Text.Codec.UTF8String"
  ];

  fstar-exe = "${fstar}/bin/fstar.exe";
  flib = "${fstar}/lib/fstar";
  ulib = "${flib}/ulib";

  # Pulse ships in the install under $(locate_lib)/pulse (sources under
  # pulse/{common,pulse/lib}, `.checked` under pulse/{common.checked,
  # pulse.checked}).
  pulse-incs = [
    "${flib}/pulse/common"
    "${flib}/pulse/common.checked"
    "${flib}/pulse/pulse/lib"
    "${flib}/pulse/pulse.checked"
  ];

  meta = {
    license = lib.licenses.agpl3Plus;
    maintainers = [
      {
        name = "Tim Dysinger";
        email = "tim@dysinger.net";
      }
    ];
  };

  # The toolchain environment the Makefile reads (see its guards).
  make-env = ''
    export FSTAR="${fstar-exe}"
    export FSTAR_CHECKED="${fstar-checked}"
    export CODEC_SRC="${codec-src}"
    export CODEC_CHECKED="${codec-checked}"
  '';

  checked = mkDerivation {
    pname = "${pname}-checked";
    version = "0.1.0";
    src = ./.;
    nativeBuildInputs = [
      fstar
      fstar-checked
    ];
    inherit meta;
    buildPhase = ''
      ${make-env}
      make check OUT="$out"
      # Flatten $(OUT)/checked/*.checked to $out/*.checked.
      if [ -d "$out/checked" ]; then mv "$out"/checked/*.checked "$out"/ 2>/dev/null || true; rmdir "$out/checked"; fi
    '';
    installPhase = "true";
  };

  # ── OCaml source backend ────────────────────────────────────────────
  #
  # `fstar.exe --codegen OCaml` extracts the pure spec modules; the Pulse leaf
  # is extracted via `--codegen Custard --custard_backend OCaml` and merged into
  # one dune library.  One file per invocation, in dependency order; the codec
  # dependency's `.checked` cache is seeded so cross-module inlining resolves.

  # ocaml-modules: every module compiled into the dune library.  This is the
  # text pure-modules PLUS the codec pure spec (`Data.Codec.Types`,
  # `Data.Codec`) — extracted locally (NOT consumed from `codec-ocaml`) so the
  # raw top-level `Data_Codec_Types`/`Data_Codec` names resolve unwrapped
  # (codec-ocaml wraps its modules into a `Codec.*` namespace, breaking the
  # bare references the text `.ml` emit).  No `Custard` collision: we only
  # extract the codec PURE spec, never its Pulse leaf.
  ocaml-lib-name = builtins.replaceStrings [ "-" ] [ "_" ] pname;
  ocaml-modules = (map (m: builtins.replaceStrings [ "." ] [ "_" ] m) pure-modules) ++ [
    "Data_Codec_Types"
    "Data_Codec"
  ];

  ocaml-src = mkDerivation {
    name = "${pname}-ocaml-src";
    src = ./.;
    nativeBuildInputs = [
      fstar
      fstar-checked
    ];
    buildPhase = ''
            export ULIB="${ulib}"
            mkdir -p $out cache
            cp ${fstar-checked}/*.checked cache/ 2>/dev/null || true
            cp ${codec-checked}/*.checked cache/ 2>/dev/null || true
            # 0) Extract the codec pure spec (Data.Codec.Types + Data.Codec) locally
            #    so the top-level `Data_Codec_Types`/`Data_Codec` module names the
            #    text `.ml` emit resolve unwrapped (codec-ocaml wraps them).
            for m in Data.Codec.Types Data.Codec; do
              ${fstar-exe} \
                --no_default_includes --include "$ULIB" --include ${codec-src}/src \
                --cache_checked_modules --cache_dir cache --odir cache \
                ${codec-src}/src/$m.fst || exit 1
              ${fstar-exe} \
                --no_default_includes --include "$ULIB" --include ${codec-src}/src --include cache \
                --cache_checked_modules --cache_dir cache \
                --codegen OCaml --odir $out \
                ${codec-src}/src/$m.fst || exit 1
            done
            # 1) Extract the pure spec via legacy `--codegen OCaml` (one file per
            #    invocation, dependency order).
            for m in ${builtins.concatStringsSep " " pure-modules}; do
              ${fstar-exe} \
                --no_default_includes --include "$ULIB" --include ${codec-src}/src --include ./src \
                --cache_checked_modules --cache_dir cache --odir cache \
                src/$m.fst || exit 1
              ${fstar-exe} \
                --no_default_includes --include "$ULIB" --include ${codec-src}/src --include ./src --include cache \
                --cache_checked_modules --cache_dir cache \
                --codegen OCaml --odir $out \
                src/$m.fst || exit 1
            done
            # 2) Extract the Pulse leaf (Data.Text.Codec.Pulse), OCaml backend.
            PULSE_INCS=""
            for d in ${lib.concatStringsSep " " pulse-incs}; do
              PULSE_INCS="$PULSE_INCS --include $d"
            done
            ${fstar-exe} \
              --no_default_includes --include "$ULIB" $PULSE_INCS --include ${codec-src}/src --include ./src \
              --already_cached Prims,FStar,Pulse.Nolib,Pulse.Lib,Pulse.Class,PulseCore \
              --z3rlimit 120 \
              --cache_checked_modules --cache_dir cache --odir cache \
              src/Data.Text.Codec.Pulse.fst || exit 1
            ${fstar-exe} \
              --no_default_includes --include "$ULIB" $PULSE_INCS --include ${codec-src}/src --include ./src --include cache \
              --already_cached Prims,FStar,Pulse.Nolib,Pulse.Lib,Pulse.Class,PulseCore \
              --cache_checked_modules --cache_dir cache \
              --codegen Custard --custard_backend OCaml --custard_monomorphize_types true \
              --custard_entry Data.Text.Codec.Pulse.encode \
              --custard_entry Data.Text.Codec.Pulse.decode \
              --odir $out \
              src/Data.Text.Codec.Pulse.fst || exit 1
            # One dune library: pure spec + Pulse leaf together.
            cat > $out/dune-project <<DUNE_PROJECT
      (lang dune 3.11)
      (name ${pname}-ocaml)
      (package (name ${pname}-ocaml))
      DUNE_PROJECT
            cat > $out/dune <<DUNE
      (library
       (name ${ocaml-lib-name})
       (public_name ${pname}-ocaml)
       (modules ${builtins.concatStringsSep " " ocaml-modules} Custard)
       (libraries fstar.lib))
      DUNE
    '';
    installPhase = "true";
  };

  ocaml = ocamlPackages.buildDunePackage {
    pname = "${pname}-ocaml";
    version = "0.1.0";
    src = ocaml-src;
    inherit meta;
    propagatedBuildInputs = [ fstar ];
    buildInputs = with ocamlPackages; [
      batteries
      pprint
      stdint
      yojson
      zarith
      ppx_deriving
      ppx_deriving_yojson
    ];
    OCAMLPATH = "${fstar}/lib";
  };

  # ── native (C) backend ─────────────────────────────────────────────
  #
  # `--codegen Custard --custard_backend C` extracts the Pulse leaf to C11
  # with no karamel runtime.  The whole module is a library (no `main`), rooted
  # at the encode/decode functions.

  native = mkDerivation {
    pname = "${pname}-native";
    version = "0.1.0";
    src = ./.;
    nativeBuildInputs = [
      fstar
      fstar-checked
    ];
    inherit meta;
    buildPhase = ''
      mkdir -p $out cache
      ULIB="${ulib}"
      PULSE_INCS=""
      for d in ${lib.concatStringsSep " " pulse-incs}; do
        PULSE_INCS="$PULSE_INCS --include $d"
      done
      cp ${fstar-checked}/*.checked cache/ 2>/dev/null || true
      cp ${codec-checked}/*.checked cache/ 2>/dev/null || true
      # Verify in dependency order into a cache so cross-module inlining can
      # find our own modules' `.checked` files.
      for m in ${builtins.concatStringsSep " " pure-modules} Data.Text.Codec.Pulse; do
        ${fstar-exe} \
          --no_default_includes --include "$ULIB" $PULSE_INCS --include ${codec-src}/src --include ./src \
          --already_cached Prims,FStar,Pulse.Nolib,Pulse.Lib,Pulse.Class,PulseCore \
          --z3rlimit 120 \
          --cache_checked_modules --cache_dir cache --odir cache \
          src/$m.fst || exit 1
      done
      # Extract the whole `Data.Text.Codec.Pulse` module to C (library mode).
      ${fstar-exe} \
        --no_default_includes --include "$ULIB" $PULSE_INCS --include ${codec-src}/src --include ./src --include cache \
        --already_cached Prims,FStar,Pulse.Nolib,Pulse.Lib,Pulse.Class,PulseCore \
        --cache_checked_modules --cache_dir cache \
        --codegen Custard --custard_backend C --custard_monomorphize_types true \
        --custard_entry Data.Text.Codec.Pulse.encode \
        --custard_entry Data.Text.Codec.Pulse.decode \
        --odir $out \
        src/Data.Text.Codec.Pulse.fst || exit 1
      # Compile the emitted C11 to a shared object + static lib (no karamel).
      cc -c -Wall -Wextra -Werror -std=c11 -O2 -fPIC -I $out $out/Custard.c -o $out/Custard.o
      if [ "$(uname -s)" = Darwin ]; then
        cc -dynamiclib $out/Custard.o -o $out/lib${pname}.dylib
      else
        cc -shared $out/Custard.o -o $out/lib${pname}.so
      fi
      ar rcs $out/lib${pname}.a $out/Custard.o
      cp $out/Custard.h $out/${pname}.h
    '';
    installPhase = "true";
  };

  # ── F# (.NET) backend ─────────────────────────────────────────────
  #
  # Same flat pattern as `native`: verify → extract F# → compile with
  # `dotnet build` into a .NET library assembly.  Rooted at the encode/decode
  # functions (the roundtrip lemmas, which have no F# realization, are not
  # pulled in).

  fsharp = mkDerivation {
    pname = "${pname}-fsharp";
    version = "0.1.0";
    src = ./.;
    nativeBuildInputs = [
      fstar
      fstar-checked
      dotnet
    ];
    inherit meta;
    buildPhase = ''
      mkdir -p $out cache src-out
      export DOTNET_CLI_TELEMETRY_OPTOUT=1
      export DOTNET_NOLOGO=1
      export DOTNET_SKIP_FIRST_TIME_EXPERIENCE=1
      export HOME=$NIX_BUILD_TOP
      ULIB="${ulib}"
      PULSE_INCS=""
      for d in ${lib.concatStringsSep " " pulse-incs}; do
        PULSE_INCS="$PULSE_INCS --include $d"
      done
      cp ${fstar-checked}/*.checked cache/ 2>/dev/null || true
      cp ${codec-checked}/*.checked cache/ 2>/dev/null || true
      for m in ${builtins.concatStringsSep " " pure-modules} Data.Text.Codec.Pulse; do
        ${fstar-exe} \
          --no_default_includes --include "$ULIB" $PULSE_INCS --include ${codec-src}/src --include ./src \
          --already_cached Prims,FStar,Pulse.Nolib,Pulse.Lib,Pulse.Class,PulseCore \
          --z3rlimit 120 \
          --cache_checked_modules --cache_dir cache --odir cache \
          src/$m.fst || exit 1
      done
      ${fstar-exe} \
        --no_default_includes --include "$ULIB" $PULSE_INCS --include ${codec-src}/src --include ./src --include cache \
        --already_cached Prims,FStar,Pulse.Nolib,Pulse.Lib,Pulse.Class,PulseCore \
        --cache_checked_modules --cache_dir cache \
        --codegen Custard --custard_backend FSharp --custard_monomorphize_types true \
        --custard_entry Data.Text.Codec.Pulse.encode \
        --custard_entry Data.Text.Codec.Pulse.decode \
        --odir src-out \
        src/Data.Text.Codec.Pulse.fst || exit 1
      dotnet build src-out/Custard.fsproj -c Release -o $out || exit 1
    '';
    installPhase = "true";
  };

in
{
  inherit
    checked
    ocaml
    native
    fsharp
    ;
}
