{
  description = "c2uplc";

  nixConfig = {
    allow-import-from-derivation = "true";
    bash-prompt = "\\[\\e[0m\\][\\[\\e[0;2m\\]nix \\[\\e[0;1m\\]c2uplc \\[\\e[0;93m\\]\\w\\[\\e[0m\\]]\\[\\e[0m\\]$ \\[\\e[0m\\]";
    cores = "1";
    max-jobs = "auto";
    auto-optimise-store = "true";
  };

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
      imports = [
        ./nix/pre-commit.nix
        ./nix/hercules-ci.nix
      ];
      debug = true;
      systems = [ "x86_64-linux" "aarch64-darwin" "x86_64-darwin" "aarch64-linux" ];

      perSystem = { config, system, ... }:
        let
          pkgs =
            import haskell-nix.inputs.nixpkgs {
              inherit system;
              overlays = [
                haskell-nix.overlay
                iohk-nix.overlays.crypto
                iohk-nix.overlays.haskell-nix-crypto
              ];
              inherit (haskell-nix) config;
            };

          project = pkgs.haskell-nix.cabalProject' {
            src = ./.;
            compiler-nix-name = "ghc984";
            # NOTE(bladyjoker): Follow https://github.com/input-output-hk/plutus/blob/master/cabal.project
            index-state = "2025-07-30T14:13:57Z";
            inputMap = {
              "https://chap.intersectmbo.org/" = CHaP;
            };
            shell = {
              withHoogle = true;
              withHaddock = true;
              exactDeps = false;
              # TODO(peter-mlabs): Use `apply-refact` for repo wide refactoring `find -name '*.hs' -not -path './dist-*/*' -exec hlint -j --refactor --refactor-options="--inplace" {} +``
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
          inherit (flake) devShells;
          packages = flake.packages;

          inherit (flake) checks;
        };
    };
}
