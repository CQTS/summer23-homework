{ pkgs, ... }:

let
  # We make a tiny emacs package to require agda
  # and to read .lagda.md files as agda files.
  emacsConfigFile = pkgs.writeText "default.el" ''
    (require 'agda2-mode)
    (add-to-list 'auto-mode-alist '("\\.lagda.md\\'" . agda2-mode))
  '';

  emacsConfig = pkgs.runCommand "default.el" {} ''
    mkdir -p $out/share/emacs/site-lisp
    cp ${emacsConfigFile} $out/share/emacs/site-lisp/default.el
  '';
in
pkgs.emacsWithPackages (epkgs: [
  epkgs.agda2-mode
  emacsConfig
])
