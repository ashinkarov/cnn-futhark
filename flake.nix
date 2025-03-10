{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let pkgs = nixpkgs.legacyPackages.${system};
      in {
        #packages.hello = pkgs.hello;

        devShell = pkgs.mkShell { 
          buildInputs = with pkgs; [ 
            darwin.apple_sdk.frameworks.OpenCL
            futhark
          ]; };
      });
}
