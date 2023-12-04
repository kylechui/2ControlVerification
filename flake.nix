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
      pkgs = nixpkgs.legacyPackages.${system};
      quantumlib-version = "v1.1.0";
    in let
      coq_quantum_lib = pkgs.coqPackages.mkCoqDerivation {
        pname = "quantumlib";
        owner = "inQWIRE";
        repo = "QuantumLib";

        defaultVersion = quantumlib-version;
        release.${quantumlib-version} = {
          rev = "refs/tags/${quantumlib-version}";
          sha256 = "sha256-YVDFLYAMFEfimIa1D6399z6Lo7RgSRJXrgEp2IEDQ0E=";
        };

        useDune = true;
        buildInputs = [ pkgs.dune_2 pkgs.ocaml ];
        installPhase = ''
          runHook preInstall
          dune install coq-quantumlib --prefix=$out
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
