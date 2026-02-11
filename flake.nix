{
  description = "c2uplc";

  nixConfig.allow-import-from-derivation = "true";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs";

    flake-parts.url = "github:hercules-ci/flake-parts";

    haskell-nix.url = "github:input-output-hk/haskell.nix";
    iohk-nix.url = "github:input-output-hk/iohk-nix";
    iohk-nix.inputs.nixpkgs.follows = "haskell-nix/nixpkgs";

    CHaP = {
      url = "github:intersectmbo/cardano-haskell-packages?ref=repo";
      flake = false;
    };

    pre-commit-hooks.url = "github:cachix/pre-commit-hooks.nix";
    hercules-ci-effects.url = "github:hercules-ci/hercules-ci-effects";

  };

  outputs = inputs@{ flake-parts, haskell-nix, iohk-nix, CHaP, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [ "x86_64-linux" "aarch64-darwin" "x86_64-darwin" "aarch64-linux" ];

      imports = [
        ./nix/pre-commit.nix
        ./nix/hercules-ci.nix
      ];

      perSystem = { config, pkgs, system, ... }:
        let
          project = pkgs.haskell-nix.cabalProject' {
            src = pkgs.lib.cleanSourceWith {
              src = pkgs.lib.cleanSource ./.;
              filter = path: _:
                let
                  baseName = baseNameOf path;
                  relPath = pkgs.lib.removePrefix (toString ./. + "/") (toString path);
                in
                pkgs.lib.any (p: pkgs.lib.hasPrefix p relPath) [ "src" "app" "test" ]
                || builtins.elem baseName [ "c2uplc.cabal" "cabal.project" "CHANGELOG.md" "README.md" "LICENSE" ];
            };
            compiler-nix-name = "ghc984";
            index-state = "2025-07-30T14:13:57Z";
            inputMap = {
              "https://chap.intersectmbo.org/" = CHaP;
            };
            shell = {
              withHoogle = true;
              withHaddock = true;
              exactDeps = false;
              shellHook = config.pre-commit.installationScript;
              tools = {
                cabal = { };
                haskell-language-server = { };
                hlint = { };
                cabal-fmt = { };
                fourmolu = { };
                hspec-discover = { };
                markdown-unlit = { };
              };
            };
          };
          flake = project.flake { };
        in
        {
          _module.args.pkgs =
            import haskell-nix.inputs.nixpkgs {
              inherit system;
              overlays = [
                haskell-nix.overlay
                iohk-nix.overlays.crypto
                iohk-nix.overlays.haskell-nix-crypto
              ];
              inherit (haskell-nix) config;
            };

          inherit (flake) packages checks devShells;
        };
    };
}
