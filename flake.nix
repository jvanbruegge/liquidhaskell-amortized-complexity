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
        rev = "dce33e919f41d2248cd1940e6f7c8c41099be83b";
        sha256 = "04yrkzvn3rl3slbsbvbfh3n0bi712i5ipwli0zb6dggv55f4a3fc";
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
                rev = "64f1edd5ee5d6d8f4cf93286a89a08d22ac0f4bf";
                sha256 = "1v5is2sya05ipmxybdigm78cblhilbqcf90qj0i0gpx431vs41y9";
              }) { };

            liquidhaskell = (haskellPackages.callCabal2nix "liquidhaskell" liquidhaskell-source { }).overrideAttrs (_: {
              doCheck = false;
            });
            liquid-ghc-prim = mkLiquidPkg "liquid-ghc-prim";
            liquid-base = (mkLiquidPkg "liquid-base").overrideAttrs(_: {
              postPatch = "sed -i -e 's/== 4.15.0.0/>= 4.15.0.0/' liquid-base.cabal";
            });
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
        ];
      };
    };
}
