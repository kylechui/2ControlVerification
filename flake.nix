{
  description = "Local development environment for 2ControlVerification";
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-23.11";
    nixpkgs-unstable.url = "github:nixos/nixpkgs/nixos-unstable";
  };

  outputs =
    {
      self,
      nixpkgs,
      nixpkgs-unstable,
    }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
      pkgs-unstable = nixpkgs-unstable.legacyPackages.${system};
      coq-quantumlib-version = "v1.6.0";
    in
    let
      coq-quantumlib = pkgs.coqPackages.mkCoqDerivation {
        pname = "quantumlib";
        owner = "inQWIRE";
        repo = "QuantumLib";

        defaultVersion = coq-quantumlib-version;
        release.${coq-quantumlib-version} = {
          rev = "5e0e4da5e64fcf9b4390a274748079ed270c1965";
          sha256 = "sha256-eKKYWUj6zDh48J5mahOr+HwWULgfn3K/3TY3oFhhYJA=";
        };
        useDune = true;
      };
    in
    {
      devShell.${system} = pkgs.mkShell {
        packages =
          [
            pkgs.coq
            pkgs.coq.ocamlPackages.ocaml
            pkgs.coq.ocamlPackages.dune_3
            coq-quantumlib
          ]
          ++ pkgs.lib.optional (builtins.getEnv "CI" != "true") (
            pkgs.coqPackages.coq-lsp.override { coq = pkgs.coq_8_18; }
          ); # Don't build the LSP in GitHub Action
      };
    };
}
