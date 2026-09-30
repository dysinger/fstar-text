# Copyright 2026 Department of Code LLC.
# SPDX-License-Identifier: AGPL-3.0-or-later

# fstar-text — Data.Text.Codec library: verified text codecs (KaRaMeL era).
#
# Takes pkgs with fstar, karamel, fstar-checked in scope, plus the codec
# dependency's checked output + source path (injected from the flake).
#
# Returns { text-checked; text-krml }.

{ pkgs, codec-checked, codec-src }:

let
  inherit (pkgs) stdenv fstar karamel fstar-checked;

  fstar-exe = "${fstar}/bin/fstar.exe";
  ulib = "${fstar}/lib/fstar/ulib";
  krmllib = "${karamel.home}/krmllib";

  fstar-flags = "--no_default_includes --include ${ulib} --include ./src --include ${codec-src}/src --include ${krmllib} --include ${krmllib}/obj --z3rlimit 80";

  # Source + test modules in DEPENDENCY ORDER (leaf modules first).
  ordered-text-modules = [
    "Data.Text.Codec.Chars"
    "Data.Text.Codec"
    "Data.Text.Codec.Delims"
    "Data.Text.Codec.Zero"
    "Data.Text.Codec.Low"
    "Data.Text.Codec.UTF8"
    "Data.Text.Codec.UTF8String"
  ];
  ordered-text-test-modules = [
    "Data.Text.Codec.Test.UTF8"
    "Data.Text.Codec.Test.Roundtrip"
    "Data.Text.Codec.Test.Delims"
    "Data.Text.Codec.Test.Zero"
    "Data.Text.Codec.Test.UTF8String"
    "Data.Text.Codec.Test.Integration"
  ];

  text-checked = stdenv.mkDerivation {
    pname = "text-checked";
    version = "0.1.0";
    src = ./.;
    nativeBuildInputs = [ fstar ];
    buildPhase = ''
      mkdir -p $out
      cp ${fstar-checked}/*.checked $out/ 2>/dev/null || true
      cp ${codec-checked}/*.checked $out/ 2>/dev/null || true

      for mod in ${builtins.concatStringsSep " " ordered-text-modules}; do
        echo "=== Verifying $mod ==="
        ${fstar-exe} ${fstar-flags} \
          --cache_checked_modules --cache_dir $out --odir $out \
          src/$mod.fst || exit 1
      done
      for mod in ${builtins.concatStringsSep " " ordered-text-test-modules}; do
        echo "=== Verifying $mod ==="
        ${fstar-exe} ${fstar-flags} --include ./test \
          --cache_checked_modules --cache_dir $out --odir $out \
          test/$mod.fst || exit 1
      done
      rm -f $out/*.krml $out/*.c $out/*.h 2>/dev/null || true
      echo "checked: $(ls $out/*.checked 2>/dev/null | wc -l) files"
    '';
    installPhase = "true";
  };

  text-krml = stdenv.mkDerivation {
    pname = "text-krml";
    version = "0.1.0";
    src = ./.;
    nativeBuildInputs = [ fstar ];
    buildPhase = ''
      mkdir -p $out
      cp ${text-checked}/*.checked $out/ 2>/dev/null || true
      cp ${codec-checked}/*.checked $out/ 2>/dev/null || true
      cp ${fstar-checked}/*.checked $out/ 2>/dev/null || true

      for mod in $(grep -h '^module' src/*.fst | grep -v ' = ' | grep '\.Low' | sed 's/module //'); do
        echo "=== Extracting $mod ==="
        ${fstar-exe} ${fstar-flags} \
          --cache_checked_modules --cache_dir $out \
          --odir $out --codegen krml \
          --extract_module $mod \
          src/$mod.fst || exit 1
      done
      rm -f $out/*.checked $out/*.c $out/*.h $out/*.exe 2>/dev/null || true
      echo "krml: $(ls $out/*.krml 2>/dev/null | wc -l) files"
    '';
    installPhase = "true";
  };
in
{
  inherit text-checked text-krml;
}
