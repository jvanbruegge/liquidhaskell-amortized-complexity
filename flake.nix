{
  # inspired by: https://serokell.io/blog/practical-nix-flakes#packaging-existing-applications
  description = "LiquidHaskell proofs of amortized complexity for the containers package";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-22.11";
  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = import nixpkgs {
        inherit system;
        overlays = [ self.overlay ];
      };
      haskellPackages = pkgs.myHaskellPackages;
      liquidhaskell-source = pkgs.fetchFromGitHub {
        owner = "ucsd-progsys";
        repo = "liquidhaskell";
        rev = "b86fb5b461a70d07fb7e97ccdbdd0ee330bf3396";
        sha256 = "sha256-4Uryni2Tpo5FGJPNZfBdJm5WfaZ/4uarXcOKwqDb33A=";
      };

      mkLiquidPkg = name: (pkgs.haskell.lib.doJailbreak (
        haskellPackages.callCabal2nixWithOptions name liquidhaskell-source "--subpath ${name}" {})
      ).overrideAttrs (prev: {
        nativeBuildInputs = prev.nativeBuildInputs ++ [ pkgs.z3 ];
      });
    in {
      overlay = (final: prev: {
        myHaskellPackages = prev.haskell.packages.ghc902.override {
          overrides = self: super: {
            liquid-fixpoint = haskellPackages.callCabal2nix "liquid-fixpoint" (
              pkgs.fetchFromGitHub {
                owner = "ucsd-progsys";
                repo = "liquid-fixpoint";
                rev = "c597c2ba3554ddfcf787cca45ee2e2d2ed984d76";
                sha256 = "sha256-rBqcAA/DGYOU7kbj06948nNxqr7FPyNwSVPgUS76KwI=";
              }) { };

            liquidhaskell = (haskellPackages.callCabal2nix "liquidhaskell" liquidhaskell-source { }).overrideAttrs (_: {
              doCheck = false;
            });
            liquid-ghc-prim = mkLiquidPkg "liquid-ghc-prim";
            liquid-base = mkLiquidPkg "liquid-base";
            liquid-prelude = mkLiquidPkg "liquid-prelude";
            z3 = super.z3.overrideAttrs (old: {
              nativeBuildInputs = old.nativeBuildInputs ++ [ pkgs.z3 ];
            });
            rest-rewrite = super.rest-rewrite.overrideAttrs (old: {
              preCheck = "mkdir graphs";
              nativeBuildInputs = old.nativeBuildInputs ++ [ pkgs.z3 pkgs.graphviz ];
              meta = old.meta // {
                broken = false;
              };
            });
          };
        };
        haskell-code = final.myHaskellPackages.callCabal2nix "code" ./code { };
      });
      packages.${system}.haskell-code = pkgs.haskell-code;
      defaultPackage.${system} = self.packages.${system}.haskell-code;
      devShell = haskellPackages.shellFor {
        packages = p: [self.packages.${system}.haskell-code];
        buildInputs = with haskellPackages; [
          cabal-install
          pkgs.z3
          pkgs.cvc4
        ];
      };
    };
}
