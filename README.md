# CQTS Summer School 2023 on Cubical Type Theory

## Getting Started

Fork this repository to your own account, by pressing the "Fork"
button in the upper right.

Once you have cloned your fork locally, run the following to fetch the
exact version of the `cubical` Agda library we are using.

``` shell
git submodule update --init
```

To edit Agda files, you will need to install Agda and an editor that
supports `agda-mode`: VSCode, Emacs or Atom.

### Installing Agda

Below we provide some different options for installing Agda, depending
on what system you are on.

Watch out for the available version if you are installing Agda via a
package manager. We are using Agda version 2.6.3, the homework
exercise files may not work with earlier versions.

#### Via Homebrew on Mac

Install Homebrew from https://brew.sh/ , then run
``` shell
brew install agda
```
At the time of writing this installs the correct version of Agda, but
it may not in the future!

#### Via Stack on Windows

Install Stack from https://docs.haskellstack.org/en/stable/install_and_upgrade/

Open PowerShell, and use Stack to install the correct version of Agda:
``` shell
stack config set resolver nightly-2023-05-17
stack install Agda-2.6.3
```

#### Via Nix on Mac and Linux

If installing Agda via `brew` did not work, we have also provided a
Nix shard that will install the correct version of Agda. This will
also install a copy of Emacs, if you would like to use that as your
editor.

First, install the Nix package manager:

Linux:
``` shell
sh <(curl -L https://nixos.org/nix/install) --daemon
```

Mac:
``` shell
sh <(curl -L https://nixos.org/nix/install)
```

Now we need to enable Nix flakes:
``` shell
mkdir -p ~/.config/nix
echo "experimental-features = nix-command flakes" >> ~/.config/nix/nix.conf
```

For a fun series of blog posts on Nix and how to use it, [click this
link](https://ianthehenry.com/posts/how-to-learn-nix/). We won't need
any heavy lifting here, we're just using Nix to install Agda easily.

Now, when you want to work in Agda with Emacs on this project,
navigate to the directory that you cloned this in and run
``` shell
nix develop
```
This might take a while the first time.

### Installing VSCode

Install VSCode from https://code.visualstudio.com/ , and then the
agda-mode extension from
https://marketplace.visualstudio.com/items?itemName=banacorn.agda-mode

If your key combinations (like `C-c C-c`) don't work, you may need to
apply the temporary fix described in
https://github.com/banacorn/agda-mode-vscode/issues/132#issuecomment-1368880358

The most important commands are (C-c C-,) (C-c C-c) (C-c space) (C-c C-.)  

Depending on how you installed Agda, you may need to tell VSCode where
the `agda` executable is located. This is under `Preferences >
Extensions`, and then the `Agda Mode > Connection: Agda Path` option.

### Installing Emacs on Mac

On Mac, you can use Homebrew to install Emacs.
``` shell
brew tap d12frosted/emacs-plus
brew install emacs-plus
agda-mode setup
```

Now try running `emacs` in the terminal. If a nice Emacs window
doesn't appear, run
``` shell
brew link --overwrite emacs-plus
```

Finally, add the following line to your `~/.emacs` file, so that the
literate Agda files are recognised correctly.
``` emacs-lisp
(add-to-list 'auto-mode-alist '("\\.lagda.md\\'" . agda2-mode))
```

## Using `agda-mode`

Test your installation by navigating to the first homework file
(`1--Type-Theory/1-1--Types-and-Functions.lagda.md`), and loading it
into Agda as follows:

Regardless of whether you are using Emacs or VSCode, most Agda
keybindings involve holding down Control or Meta (a.k.a. Alt) and
pressing other keys. Loading and checking an Agda file has the
keybinding `C-c C-l`, so to load the current file into Agda, hold down
Control then press `c` followed by `l`, you do not have to let go of
Control in between.

Here are some of the more useful keys, that will be explained as we
work through the exercises:

* `C-c C-l`: Load and check the file
* `M-.`: Jump to the definition of whatever your cursor is on
* `C-c C-f`: Move to next goal (forward)
* `C-c C-b`: Move to previous goal (backwards)

* `C-c C-c`: Case split (specify an argument to split on)
* `C-c C-r`: Refine goal (Add a `λ` if the goal is a function, add a
  `,` if the goal is a pair, etc. Not always the right move!)
* `C-c C-.`: Show the goal type, context and inferred type

### General editing:

If you are using Emacs, then most keybindings used in the editor are
also of that form. For example:

* `C-x C-f`: Open a file
* `C-x C-s`: Save the current file
* `C-x C-b`: See all the things ("buffers") you have open
* `C-x b`: Choose a buffer to switch to
* `C-_`: Undo
* `M-_`: Redo

## Attribution

This course was written by David Jaz Myers and Mitchell Riley.

Thanks to Owen Lynch for his Nix-fu.
