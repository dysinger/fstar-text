# Copyright 2026 Department of Code LLC.
# SPDX-License-Identifier: AGPL-3.0-or-later

{
  description = "text — verified text codec library";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/c31cf09";
    flake-utils.url = "github:numtide/flake-utils";
    treefmt-nix.url = "github:numtide/treefmt-nix";
    fstar = {
      # Fork of F* with the LSP server ported onto the v2026.09.20 base
      # (first stable tag shipping the Custard extractor).
      url = "github:dysinger/fstar/v2026.09.20+lsp";
      flake = false;
    };
    # The codec dependency (Data.Codec.Types).  Consumed from the published
    # `dysinger/fstar-codec` GitHub repo (pinned to its HEAD commit in
    # flake.lock).
    fstar-codec.url = "github:dysinger/fstar-codec";
  };

  outputs =
    inputs@{
      self,
      nixpkgs,
      flake-utils,
      treefmt-nix,
      fstar-codec,
      ...
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [
            (
              _final: prev:
              if prev.stdenv.isDarwin && prev.stdenv.isAarch64 then
                {
                  # Skip OCaml's own testsuite on aarch64-darwin.
                  ocaml-ng = prev.ocaml-ng // {
                    ocamlPackages_5_3 = prev.ocaml-ng.ocamlPackages_5_3.overrideScope (
                      _: _: {
                        ocaml = prev.ocaml-ng.ocamlPackages_5_3.ocaml.overrideAttrs (_: {
                          checkPhase = "true";
                        });
                      }
                    );
                  };
                }
              else
                { }
            )
            (
              _final: prev:
              let
                ocamlPackages = prev.ocaml-ng.ocamlPackages_5_3;
                z3 = prev.callPackage (inputs.fstar + "/.nix/z3.nix") { };
                version = "2026.09.20+lsp";

                fstar =
                  (ocamlPackages.callPackage (inputs.fstar + "/.nix/fstar.nix") {
                    inherit version z3;
                    karamel-src = prev.emptyDirectory;
                    karamelOcamlDeps = [ ];
                    ocamlLibraryPath = "";
                  }).overrideAttrs
                    (old: {
                      nativeBuildInputs = (old.nativeBuildInputs or [ ]) ++ [ prev.git ];
                      # The 4-stage bootstrap verifies ulib with the default z3
                      # rlimit (5).  `FStar.Math.Fermat.binomial_theorem` has always
                      # been flaky (see its git history of "tweak rlimit"/"stabilize
                      # proofs") and deterministically times out under z3 4.13.3,
                      # failing the stage2 `.checked` verification.  Raise the global
                      # rlimit so the bootstrap is deterministic.  OTHERFLAGS is
                      # appended to FSTAR_OPTIONS by mk/generic-1.mk and flows to the
                      # nested `make -f mk/lib.mk` (the .alib2.src.touch recipe does
                      # not re-specify it, unlike fsharp-lib.src).
                      buildPhase = ''
                        export PATH="${z3}/bin:$PATH"
                        export FSTAR_USE_KRML_EXE=1 KRML_EXE=/bin/true
                        mkdir -p karamel
                        printf 'all:\n\t@true\ninstall:\n\t@true\n' > karamel/Makefile
                        make OTHERFLAGS='--z3rlimit 20 --retry 3'
                      '';
                      installPhase = ''
                        export FSTAR_USE_KRML_EXE=1 KRML_EXE=/bin/true
                        mkdir -p karamel
                        printf 'all:\n\t@true\ninstall:\n\t@true\n' > karamel/Makefile
                        PREFIX=$out make install

                        for binary in $out/bin/*
                        do
                          wrapProgram $binary --prefix PATH ":" ${z3}/bin
                        done

                        cd $out
                        installShellCompletion --bash ${inputs.fstar + "/.completion/bash/fstar.exe.bash"}
                        installShellCompletion --fish ${inputs.fstar + "/.completion/fish/fstar.exe.fish"}
                        installShellCompletion --zsh --name _fstar.exe ${inputs.fstar + "/.completion/zsh/__fstar.exe"}
                      '';
                    });

                # fstar-checked: ulib .checked files (pre-verified by the fstar
                # compiler), seeded into the cache so `make check` can write our
                # own modules' .checked stamps.
                fstar-checked = prev.runCommand "fstar-checked" { nativeBuildInputs = [ fstar ]; } ''
                  mkdir -p $out
                  cp ${fstar}/lib/fstar/ulib.checked/*.checked $out/ 2>/dev/null || true
                  echo "checked: $(ls $out/*.checked 2>/dev/null | wc -l) files"
                '';
              in
              {
                inherit fstar fstar-checked;
                inherit ocamlPackages;
              }
            )
          ];
        };

        inherit (pkgs)
          stdenv
          fstar
          fstar-checked
          lib
          dotnet-sdk_10
          ;
        inherit (pkgs) ocamlPackages;

        # The codec dependency's source + checked artifacts come from the
        # fstar-codec flake input (its `checked` package is the pre-verified
        # `.checked` set; its source is the flake's own tree).
        codec-src = fstar-codec;
        codec-checked = fstar-codec.packages.${system}.checked;

        _pkg = import ./default.nix {
          inherit
            fstar
            fstar-checked
            lib
            ocamlPackages
            stdenv
            codec-src
            codec-checked
            ;
          dotnet = dotnet-sdk_10;
        };

        treefmtModule = treefmt-nix.lib.evalModule pkgs ./treefmt.nix;

      in
      {
        formatter = treefmtModule.config.build.wrapper;

        checks.formatting = treefmtModule.config.build.check self;

        # The build targets are named by deliverable (no `text-`
        # prefix); `default` aliases `native` (the C11 shared/static lib).
        packages.default = _pkg.native;
        packages.checked = _pkg.checked;
        packages.ocaml = _pkg.ocaml;
        packages.native = _pkg.native;
        packages.fsharp = _pkg.fsharp;

        devShells.default = pkgs.mkShell {
          dontDetectOcamlConflicts = true;
          shellHook = ''
            export FSTAR_CHECKED="${fstar-checked}"
            export CODEC_SRC="${codec-src}"
            export CODEC_CHECKED="${codec-checked}"
          '';
          # Note: z3 is not listed here on purpose.  The `fstar.exe` wrapper
          # already prepends the correct z3 (4.13.3, from the fstar fork's
          # .nix/z3.nix) onto its own PATH, so `fstar.exe`/`make check` find
          # it.  Exposing that z3 as a separate top-level attr triggers a nix
          # fixpoint stack-overflow (the overlay's `z3 = prev.callPackage
          # (inputs.fstar + "/.nix/z3.nix")` self-references when inherited
          # back out).  `git` + `dotnet-sdk_10` are present for the fsharp
          # target and the fstar bootstrap.
          buildInputs = with pkgs; [
            fstar
            dotnet-sdk_10
            git
            ocaml
            ocamlPackages.ocaml-lsp
          ];
        };
      }
    );
}
