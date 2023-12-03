{
  description = "Local development environment for 2ControlVerification";
  inputs = {
    # Pinned version of nixpkgs containing Coq 8.15.0
    nixpkgs.url =
      "github:nixos/nixpkgs/6e3a86f2f73a466656a401302d3ece26fba401d9";
  };

  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = import nixpkgs {
        inherit system;
        config.allowBroken = true;
      };
      pname = "quantumlib";
      owner = "inQWIRE";
    in let
      coq_quantum_lib = pkgs.coqPackages.mkCoqDerivation {
        inherit pname owner;
        src = pkgs.fetchFromGitHub {
          inherit owner;
          repo = "QuantumLib";
          rev = "main";
          sha256 = "sha256-evIxqyjiOc+HkIl9Ft+7DZHYx74v7UGG5mHg6dlG6oA=";
        };
        useDune = true;
        buildInputs = [ pkgs.dune_3 pkgs.ocaml ];
        installPhase = ''
          runHook preInstall
          dune install coq-${pname} --prefix=$out --mandir=$out/man
          mv $out/lib/coq $out/lib/TEMPORARY
          mkdir $out/lib/coq/
          mv $out/lib/TEMPORARY $out/lib/coq/${pkgs.coq.coq-version}
          runHook postInstall
        '';
      };
    in {
      devShell.${system} =
        pkgs.mkShell { nativeBuildInputs = [ pkgs.coq coq_quantum_lib ]; };
    };
}
