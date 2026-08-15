{
  description = "CRIS development environment";
  inputs = {
    nixpkgs.url = "github:snu-sf/nixpkgs/rocq-env-0.2";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs {
          inherit system;
        };
        coq = pkgs.coq_9_0;
        coqPackages = pkgs.mkCoqPackages coq;
        callPackage = pkgs.lib.callPackageWith (pkgs // params // set);
        params = {
          inherit (coqPackages) mkCoqDerivation lib stdlib;
          inherit (coq) ocamlPackages;
        };
        set = {
          inherit coq;
          paco = callPackage coqPackages.paco.override { version = "4.2.3"; };
          ExtLib = callPackage coqPackages.ExtLib.override { version = "0.13.0"; };
          ITree = callPackage coqPackages.ITree.override { version = "5.2.1"; };
          Ordinal = callPackage coqPackages.Ordinal.override { version = "0.5.6"; };
          stdpp = callPackage coqPackages.stdpp.override { version = "1.12.0"; };
          iris = callPackage coqPackages.iris.override { version = "4.4.0"; };
        };
      in
      {
        devShell = pkgs.mkShell {
          buildInputs = pkgs.lib.attrValues set ++ [
            coqPackages.coq-lsp
            pkgs.coqtail-mcp
          ];
          shellHook = ''
            unset COQPATH
          '';
        };
      }
    );
}
