{
  description = "A first course in Cubical Agda, given in June and July 2023 at CQTS in NYU-AD. Course written by David Jaz Myers and Mitchell Riley. Nix written by Owen Lynch";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachSystem [ "aarch64-darwin" "x86_64-darwin" "x86_64-linux" ] (system:
      let
        pkgs = import nixpkgs {
          inherit system;
        };
      in
      {
        devShell = pkgs.mkShell {
          buildInputs = with pkgs; [
            agda
            (import ./emacs.nix { inherit pkgs; })
          ];
        };
      }
    );
}
