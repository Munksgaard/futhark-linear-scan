# shell.nix
let
  sources = import ./nix/sources.nix;
  pkgs = import sources.nixpkgs {};
  ormolu = import sources.ormolu {};
  buildInputs = [
    pkgs.cabal-install
    pkgs.haskell.compiler.ghc8101
    pkgs.zlib
    pkgs.zlib.dev
    pkgs.zlib.out
    pkgs.hlint
    ormolu.ormolu
    pkgs.ocl-icd
    pkgs.opencl-headers
    pkgs.ghcid
    pkgs.pkgconfig
    pkgs.gmp
    pkgs.libffi
  ];
in
pkgs.mkShell {
  buildInputs = buildInputs;

  shellHook = ''export LD_LIBRARY_PATH=${pkgs.lib.makeLibraryPath buildInputs}:$LD_LIBRARY_PATH'';
}
