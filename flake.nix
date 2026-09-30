# Copyright 2026 Department of Code LLC.
# SPDX-License-Identifier: AGPL-3.0-or-later

{
  description = "fstar-text — verified text codecs (KaRaMeL era)";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/c31cf09";
    flake-utils.url = "github:numtide/flake-utils";
    # KaRaMeL-era F* (pre-Custard): Low*/KaRaMeL stdlib still present.
    fstar = {
      url = "github:dysinger/fstar/v2025.10.06+lsp";
      flake = false;
    };
    karamel = {
      url = "github:dysinger/karamel/coextract";
      flake = false;
    };
    # No codec flake input: the codec dependency (Data.Codec.Types/Data.Codec,
    # KaRaMeL era) is vendored in-repo under ./codec, mirroring the basen
    # KaRaMeL-era port.  Switch to `github:dysinger/fstar-codec` when the
    # repo is published and re-pointed at the Custard era.
  };

  outputs =
    inputs@{
      self,
      nixpkgs,
      flake-utils,
      ...
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [
            (_final: prev:
              if prev.stdenv.isDarwin && prev.stdenv.isAarch64 then {
                # Skip OCaml's own testsuite on aarch64-darwin.
                ocaml-ng = prev.ocaml-ng // {
                  ocamlPackages_5_3 = prev.ocaml-ng.ocamlPackages_5_3.overrideScope (_: _: {
                    ocaml = prev.ocaml-ng.ocamlPackages_5_3.ocaml.overrideAttrs (_: {
                      checkPhase = "true";
                    });
                  });
                };
              } else { })
            (_final: prev:
              let
                z3 = prev.callPackage (inputs.fstar + "/.nix/z3.nix") { };
                ocamlPackages = prev.ocaml-ng.ocamlPackages_5_3;
                fstar = (ocamlPackages.callPackage (inputs.fstar + "/.nix/fstar.nix") {
                  version = "unknown";
                  inherit z3;
                }).overrideAttrs (old: {
                  nativeBuildInputs = (old.nativeBuildInputs or [ ]) ++ [ prev.git ];
                });
                gtime = prev.runCommand "gtime" { } ''
                  mkdir -p $out/bin
                  ln -s ${prev.time}/bin/time $out/bin/gtime
                '';
                # fstar-checked: ulib .checked files (pre-verified by fstar compiler).
                fstar-checked = prev.runCommand "fstar-checked"
                  { nativeBuildInputs = [ fstar ]; }
                  ''
                    mkdir -p $out
                    cp ${fstar}/lib/fstar/ulib.checked/*.checked $out/ 2>/dev/null || true
                    echo "checked: $(ls $out/*.checked 2>/dev/null | wc -l) files"
                  '';
                karamel = (prev.callPackage (inputs.karamel + "/.nix/karamel.nix") {
                  inherit fstar ocamlPackages z3;
                  version = "unknown";
                }).overrideAttrs (old: {
                  nativeBuildInputs = (old.nativeBuildInputs or [ ]) ++ [ gtime ];
                });
                fstar-krml = prev.runCommand "fstar-krml"
                  { nativeBuildInputs = [ fstar karamel ]; }
                  ''
                    mkdir -p $out/krml $out/extract
                    cp ${karamel.home}/krmllib/.extract/*.krml $out/krml/ 2>/dev/null || true
                    ULIB_DIR=${fstar}/lib/fstar/ulib
                    find $ULIB_DIR -name '*.fsti' -exec cp {} $out/extract/ \; 2>/dev/null || true
                    find $ULIB_DIR -name '*.fst' -exec cp {} $out/extract/ \; 2>/dev/null || true
                    echo "krml: $(ls $out/krml/*.krml 2>/dev/null | wc -l) files"
                    echo "extract: $(ls $out/extract/ 2>/dev/null | wc -l) files"
                  '';
              in
              {
                inherit fstar karamel fstar-checked fstar-krml;
                ocamlPackages = prev.ocaml-ng.ocamlPackages_5_3;
              })
          ];
        };

        inherit (pkgs) fstar karamel fstar-checked fstar-krml lib stdenv;
        inherit (pkgs) ocamlPackages;

        # The codec dependency (vendored at ./codec, KaRaMeL era).
        _codec = import ./codec/default.nix { inherit pkgs; };

        _pkg = import ./default.nix {
          inherit pkgs;
          inherit (_codec) codec-checked;
          codec-src = ./codec;
        };

      in
      {
        packages.default = _pkg.krml;
        packages.checked = _pkg.checked;
        packages.krml = _pkg.krml;

        devShells.default = pkgs.mkShell {
          dontDetectOcamlConflicts = true;
          shellHook = ''
            export FSTAR_KRML="${fstar-krml}"
            export FSTAR_CHECKED="${fstar-checked}"
            export KRML_HOME="${karamel.home}"
            export KRM_LIB="${karamel.home}/krmllib"
            export KRM_INC="-I${karamel.home}/include -I${karamel.home}/krmllib/c -I${karamel.home}/krmllib/dist/minimal"
          '';
          buildInputs = with pkgs; [
            fstar
            karamel
            ocaml
            ocamlPackages.ocaml-lsp
            python3
          ];
        };
      }
    );
}
