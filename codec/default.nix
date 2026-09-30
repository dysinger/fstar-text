# codec — Data.Codec library: verified serialization framework
#
# Takes pkgs with fstar, karamel, fstar-checked in scope
# (from nixpkgs overlay in top-level flake).
#
# Returns { codec-checked, codec-krml }

{ pkgs }:

let
  inherit (pkgs) stdenv fstar karamel fstar-checked;

  fstar-exe = "${fstar}/bin/fstar.exe";
  ulib = "${fstar}/lib/fstar/ulib";
  krmllib = "${karamel.home}/krmllib";

  fstar-flags = "--no_default_includes --include ${ulib} --include ./src --include ${krmllib} --include ${krmllib}/obj --z3rlimit 80";

  # Source modules in DEPENDENCY ORDER (leaf modules first).  This is
  # required by fstar-build §3 (Warning 247): an alphabetical glob would
  # verify Data.Codec before Data.Codec.Types and silently omit
  # Data.Codec.fst.checked from $out, cascading incomplete .checked sets
  # to every downstream package.
  ordered-src-modules = [ "Data.Codec.Types" "Data.Codec" "Data.Codec.Low" ];

  codec-checked = stdenv.mkDerivation {
    pname = "codec-checked";
    version = "0.1.0";
    src = ./.;
    nativeBuildInputs = [ fstar ];
    buildPhase = ''
      mkdir -p $out
      cp ${fstar-checked}/*.checked $out/ 2>/dev/null || true

      for mod in ${builtins.concatStringsSep " " ordered-src-modules}; do
        echo "=== Verifying $mod ==="
        ${fstar-exe} ${fstar-flags} \
          --cache_checked_modules --cache_dir $out --odir $out \
          src/$mod.fst || exit 1
      done
      rm -f $out/*.krml $out/*.c $out/*.h 2>/dev/null || true
      echo "checked: $(ls $out/*.checked 2>/dev/null | wc -l) files"
    '';
    installPhase = "true";
  };

  codec-krml = stdenv.mkDerivation {
    pname = "codec-krml";
    version = "0.1.0";
    src = ./.;
    nativeBuildInputs = [ fstar ];
    buildPhase = ''
      mkdir -p $out
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
  inherit codec-checked codec-krml;
}
