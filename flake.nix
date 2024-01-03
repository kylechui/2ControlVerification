{
  description = "Local development environment for 2ControlVerification";
  inputs = { nixpkgs.url = "github:nixos/nixpkgs/nixos-23.11"; };

  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system}.extend (final: prev: {
        coq = prev.coq_8_15;
        coqPackages = prev.coqPackages_8_15;
      });
      coq-quantumlib-version = "v1.1.0";
      coq-lsp-version = "v8.15";
    in let
      coq-quantumlib = pkgs.coqPackages.mkCoqDerivation {
        pname = "quantumlib";
        owner = "inQWIRE";
        repo = "QuantumLib";

        defaultVersion = coq-quantumlib-version;
        release.${coq-quantumlib-version} = {
          rev = "71b5b228baa6e2f0c06cc73416ac4a9820f1fd4f";
          sha256 = "sha256-evIxqyjiOc+HkIl9Ft+7DZHYx74v7UGG5mHg6dlG6oA=";
        };
        useDune = true;
      };

      coq-lsp = pkgs.coqPackages.mkCoqDerivation {
        pname = "lsp";
        owner = "jishnusen";
        repo = "coq-lsp";
        defaultVersion = coq-lsp-version;
        release.${coq-lsp-version} = {
          rev = "1c5b5445c4f5b81ce2ab69cb9febb0c2318c9ac6";
          sha256 = "sha256-7/K1BmN3IuPUPwfoFHO26LOugi3sbhHdwESY0Xotcco=";
        };
        installPhase = ''
          runHook preInstall
          dune install coq-lsp --prefix=$out
          wrapProgram $out/bin/coq-lsp --prefix OCAMLPATH : $OCAMLPATH
          runHook postInstall
        '';
        useDune = true;
        nativeBuildInputs = [ pkgs.makeWrapper ];
        propagatedBuildInputs = [ pkgs.coqPackages.serapi ]
          ++ (with pkgs.coq.ocamlPackages; [
            camlp-streams
            dune-build-info
            menhir
            uri
            yojson
          ]);
      };
    in {
      devShell.${system} = pkgs.mkShell {
        packages = [
          pkgs.coq
          pkgs.coq.ocamlPackages.ocaml
          pkgs.coq.ocamlPackages.dune_3
          coq-quantumlib
          coq-lsp
        ];
        propagatedBuildInputs = [ pkgs.coqPackages.serapi ]
          ++ (with pkgs.coq.ocamlPackages; [
            camlp-streams
            dune-build-info
            menhir
            uri
            yojson
          ]);
      };
    };
}
