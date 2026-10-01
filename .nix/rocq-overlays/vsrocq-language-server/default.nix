{
  metaFetch,
  coq,
  rocq-core,
  lib,
  glib,
  adwaita-icon-theme,
  wrapGAppsHook3,
  version ? null,
}:

let
  ocamlPackages = rocq-core.ocamlPackages;
  ## Everything below that differs from nixpkgs is needed only for Rocq 9.2
  ## (OCaml 5.5); on 9.0/9.1 the nixpkgs choices are correct and mine break
  ## the build, so switch on the version.
  isPre92 = lib.versionOlder rocq-core.rocq-version "9.2";
  defaultVersion =
    let
      case = case: out: { inherit case out; };
    in
    lib.switch rocq-core.rocq-version [
      # When updating the default version here, also update the VsRocq VS Code extension
      #
      # Amended copy of the nixpkgs derivation: 2.4.3 declares
      # `rocq-core >= 9.0+rc1 < 9.3~` upstream, but nixpkgs stops its table at
      # 9.1, which leaves the package unavailable in the 9.2 bundle.  2.5.0
      # declares `rocq-core >= 9.0+rc1 < 9.4~` and covers 9.3.  Drop this
      # overlay once nixpkgs widens the range.
      (case (lib.versions.range "9.3" "9.3") "2.5.0")
      (case (lib.versions.range "8.18" "9.2") "2.4.3")
    ] null;
  location = {
    domain = "github.com";
    owner = "rocq-prover";
    repo = "vsrocq";
  };
  fetch = metaFetch {
    release."2.3.0".rev = "v2.3.0";
    release."2.3.0".sha256 = "sha256-BZLxcCmSGFf04eUmlJXnyxmg4hTwpFaPaIik4VD444M=";
    release."2.3.3".rev = "v2.3.3";
    release."2.3.3".sha256 = "sha256-wgn28wqWhZS4UOLUblkgXQISgLV+XdSIIEMx9uMT/ig=";
    release."2.3.4".rev = "v2.3.4";
    release."2.3.4".sha256 = "sha256-v1hQjE8U1o2VYOlUjH0seIsNG+NrMNZ8ixt4bQNyGvI=";
    release."2.4.3".rev = "v2.4.3";
    release."2.4.3".sha256 = "sha256-R/fpTiYZ9uvtKQcWD4jwUZPvUrcdvHc/wpoTrdkEQoQ=";
    release."2.5.0".rev = "v2.5.0";
    release."2.5.0".sha256 = "sha256-TJO5RLPqWETqYZ9qxWMVi787nFdyuI2yqK3lVZR65xI=";
    inherit location;
  };
  fetched = fetch (if version != null then version else defaultVersion);
  ## 2.5.0 needs `memprof-limits`; nixpkgs ships 0.2.1, which is marked broken
  ## on OCaml >= 5.0.  0.3.0 supports OCaml >= 5.3 again.
  isPre25 = lib.versionOlder fetched.version "2.5.0";
  memprof-limits = ocamlPackages.memprof-limits.overrideAttrs (old: {
    version = "0.3.0";
    src = old.src.override {
      rev = "v0.3.0";
      hash = "sha256-k/uB1jDQtE/PkVPU8zg8cpOmlPttTWVpKerQ0HuWfuI=";
    };
    nativeBuildInputs = (old.nativeBuildInputs or [ ]) ++ [ ocamlPackages.cppo ];
    meta = old.meta // { broken = false; };
  });
in
ocamlPackages.buildDunePackage {
  pname = "vsrocq-language-server";
  inherit (fetched) version;
  src = "${fetched.src}/language-server";
  ## 9.2 resolves the `rocq-runtime.*` findlib packages through `rocq-core`;
  ## the `coq` shim no longer provides them.
  nativeBuildInputs = [ (if isPre92 then coq else rocq-core) ];
  buildInputs = [
    (if isPre92 then coq else rocq-core)
    glib
    adwaita-icon-theme
    wrapGAppsHook3
  ]
  ++ (with ocamlPackages; [
    findlib
    lablgtk3-sourceview3
    zarith
    ppx_inline_test
    ppx_assert
    ppx_sexp_conv
    ppx_deriving
    ppx_import
    sexplib
    ## nixpkgs pins this to yojson 2 while `lsp` below is built against
    ## yojson 3; on the OCaml 5.5 of Rocq 9.2 that makes the two disagree on
    ## the `Yojson__T` interface, so use the default yojson for both there.
    (if isPre92
     then ppx_yojson_conv.override {
            ppx_yojson_conv_lib = ppx_yojson_conv_lib.override { yojson = yojson_2; };
          }
     else ppx_yojson_conv)
    lsp
    sel
    ppx_optcomp
  ])
  ++ lib.optional (!isPre25) memprof-limits;
  preBuild = ''
    make dune-files
  '';

  meta = {
    description = "Language server for the vsrocq vscode/codium extension";
    homepage = "https://github.com/rocq-prover/vsrocq";
    maintainers = with lib.maintainers; [ cohencyril ];
    license = lib.licenses.mit;
  }
  // lib.optionalAttrs (fetched.broken or false) {
    broken = true;
  };
}
