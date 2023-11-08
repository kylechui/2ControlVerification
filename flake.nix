{
  description = "Local development environment for 2ControlVerification";
  inputs = {
    # Pinned version of nixpkgs containing Coq 8.17.0
    nixpkgs.url =
      "github:nixos/nixpkgs/6eef602bdb2a316e7cf5f95aeb10b2ff0a97e4a5";
  };

  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
    in {
      devShell.${system} =
        pkgs.mkShell { nativeBuildInputs = [ pkgs.coqPackages.coq ]; };
    };
}
