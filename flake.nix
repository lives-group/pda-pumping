{
  description =
    "A machine-checked formalization of the pumping lemma for context-free languages via pushdown automata";

  inputs = {
    # Pinned to nixos-25.05, which ships Agda 2.7.0.1 and standard-library
    # 2.2: the exact pair the development was checked against, and the one
    # named in pda-pumping.agda-lib.  Do not move this to unstable without
    # re-checking src/ first: nixos-25.11 already carries Agda 2.8.0 and
    # standard-library 2.3.
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-25.05";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };

        # ---------------------------------------------------------------
        # Agda 2.7.x with the standard library, for checking src/.
        # ---------------------------------------------------------------
        agdaWithStdlib = pkgs.agda.withPackages (p: [ p.standard-library ]);

        # ---------------------------------------------------------------
        # TeX Live: exactly what paper/paper.tex pulls in.  llncs.cls and
        # splncs04.bst ship with the paper, so they are not listed here.
        # ---------------------------------------------------------------
        texenv = pkgs.texlive.combine {
          inherit (pkgs.texlive)
            scheme-basic
            # engine + bibliography
            latex latex-bin latexmk bibtex
            # packages loaded by the preamble
            amsmath amsfonts fancyvrb xcolor hyperref graphics
            # pulled in transitively (see paper/paper.log); multicol,
            # which llncs.cls loads, lives in the "tools" bundle
            etoolbox tools url iftex infwarerr ltxcmds pdftexcmds
            kvoptions kvsetkeys kvdefinekeys epstopdf-pkg refcount
            rerunfilecheck stringenc uniquecounter bitset intcalc
            bigintcalc pdfescape hycolor gettitlestring auxhook
            atbegshi atveryend zapfding symbol
            # T1 fonts for the typewriter faces used in the code listings
            cm-super ec;
        };

        # ---------------------------------------------------------------
        # Building the paper.  bibtex needs a writable working directory,
        # so we copy the sources in first.
        # ---------------------------------------------------------------
        paper = pkgs.stdenvNoCC.mkDerivation {
          pname = "pda-pumping-paper";
          version = "2026";
          # Only the four real sources, so that a local pdflatex run (which
          # rewrites paper.aux, paper.log, paper.pdf) does not invalidate it.
          src = pkgs.lib.fileset.toSource {
            root = ./paper;
            fileset = pkgs.lib.fileset.unions [
              ./paper/paper.tex
              ./paper/references.bib
              ./paper/llncs.cls
              ./paper/splncs04.bst
            ];
          };
          nativeBuildInputs = [ texenv ];
          buildPhase = ''
            runHook preBuild
            export HOME=$TMPDIR
            pdflatex -interaction=nonstopmode -halt-on-error paper.tex
            bibtex paper || true
            pdflatex -interaction=nonstopmode -halt-on-error paper.tex
            pdflatex -interaction=nonstopmode -halt-on-error paper.tex
            runHook postBuild
          '';
          installPhase = ''
            runHook preInstall
            mkdir -p $out
            cp paper.pdf $out/
            runHook postInstall
          '';
        };

        # ---------------------------------------------------------------
        # Type-checking the formalization.  Arbitrary.agda is the root:
        # it transitively pulls in the other 21 modules and ends in
        # pumping-pda, the end-to-end theorem.
        # ---------------------------------------------------------------
        formalization = pkgs.stdenvNoCC.mkDerivation {
          pname = "pda-pumping-formalization";
          version = "2026";
          # Only the Agda sources and the library file, so that editing the
          # paper or this flake does not invalidate a 20-minute type-check.
          src = pkgs.lib.fileset.toSource {
            root = ./.;
            fileset = pkgs.lib.fileset.unions [ ./src ./pda-pumping.agda-lib ];
          };
          nativeBuildInputs = [ agdaWithStdlib ];
          buildPhase = ''
            runHook preBuild
            export HOME=$TMPDIR
            # pda-pumping.agda-lib supplies the include path and the
            # standard-library-2.2 dependency; the agda wrapper supplies
            # --library-file, so neither must be overridden here.
            agda src/PDA/Pumping/Arbitrary.agda
            runHook postBuild
          '';
          installPhase = ''
            runHook preInstall
            mkdir -p $out
            cp -r _build $out/_build
            runHook postInstall
          '';
        };
      in {
        packages = {
          inherit paper formalization;
          default = paper;
        };

        # `nix flake check` type-checks the Agda and builds the PDF.
        checks = { inherit paper formalization; };

        devShells.default = pkgs.mkShell {
          packages = [ agdaWithStdlib texenv pkgs.poppler_utils ];
          shellHook = ''
            echo "pda-pumping dev shell"
            echo "  check the formalization:  agda -i src src/PDA/Pumping/Arbitrary.agda"
            echo "  build the paper:          cd paper && pdflatex paper && bibtex paper && pdflatex paper && pdflatex paper"
          '';
        };
      });
}
