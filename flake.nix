{
  description = "Local development environment for 2ControlVerification";
  inputs = { nixpkgs.url = "github:nixos/nixpkgs/nixos-23.11"; };

  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
      coq-quantumlib-version = "v1.4.0";
      coq-lsp-version = "v8.18";
    in let
      coq-quantumlib = pkgs.coqPackages.mkCoqDerivation {
        pname = "quantumlib";
        owner = "inQWIRE";
        repo = "QuantumLib";

        defaultVersion = coq-quantumlib-version;
        release.${coq-quantumlib-version} = {
          rev = "80018571961e13968bfd80ea9cb061d9469b0817";
          sha256 = "sha256-mx74GxIwF6mgmrELmNl0l3GiBBf/WrpouHfszylhTYQ=";
        };
        useDune = true;
      };
    in {
      devShell.${system} = pkgs.mkShell {
        packages = [
          pkgs.coq
          pkgs.coq.ocamlPackages.ocaml
          pkgs.coq.ocamlPackages.dune_3
          coq-quantumlib
        ] ++ pkgs.lib.optional (builtins.getEnv "CI" != "true")
          pkgs.coqPackages.coq-lsp; # Don't build the LSP in GitHub Action
      };
    };
}
