{
  ## DO NOT CHANGE THIS
  format = "1.0.0";
  ## unless you made an automated or manual update
  ## to another supported format.

  ## The attribute to build from the local sources,
  ## either using nixpkgs data or the overlays located in `.nix/rocq-overlays`
  ## and `.nix/coq-overlays`
  ## Will determine the default main-job of the bundles defined below
  attribute = "extmet-qll";

  ## Indicate the relative location of your _CoqProject
  coqproject = "_CoqProject";

  ## Extra packages to have around.  The toolbox already puts `coq-lsp` and
  ## the Coq-era `vscoq-language-server` in the shell; this adds the Rocq one,
  ## which is what the VsRocq editor extension talks to.  MathComp Analysis
  ## is the library the development builds on.
  buildInputs = [ "vsrocq-language-server" "mathcomp-analysis" ];

  ## select an entry to build in the following `bundles` set
  ## defaults to "default"
  ## "9.3" is the latest stable Rocq release.
  default-bundle = "9.3";

  ## write one `bundles.name` attribute set per
  ## alternative configuration
  ## When generating GitHub Action CI, one workflow file
  ## will be created per bundle
  ##
  ## The development is Rocq-only (it uses the `Stdlib` prefix).  The
  ## `coqPackages.coq` override keeps the toolbox's `coq` compatibility shim
  ## (used e.g. by `coq-lsp`) on the same version as `rocq-core`.

  bundles."9.3" = {
    rocqPackages = {
      rocq-core.override.version = "9.3";
      mathcomp.override.version = "2.6.0";
      mathcomp-analysis.override.version = "1.18.0";
    };
    coqPackages.coq.override.version = "9.3";
    ## CI runs on pushes to these branches (the toolbox defaults to "master").
    push-branches = [ "main" ];
  };

  ## Cachix caches to use in CI
  ## Below we list some standard ones
  cachix.coq = {};
  cachix.math-comp = {};
  cachix.coq-community = {};

  ## If you have write access to one of these caches you can
  ## provide the auth token or signing key through a secret
  ## variable on GitHub. Then, you should give the variable
  ## name here. For instance, coq-community projects can use
  ## the following line instead of the one above:
  # cachix.coq-community.authToken = "CACHIX_AUTH_TOKEN";

  ## Or if you have a signing key for a given Cachix cache:
  # cachix.my-cache.signingKey = "CACHIX_SIGNING_KEY"

  ## Note that here, CACHIX_AUTH_TOKEN and CACHIX_SIGNING_KEY
  ## are the names of secret variables. They are set in
  ## GitHub's web interface.
}
