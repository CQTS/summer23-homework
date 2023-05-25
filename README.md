# Getting Started

To get the cubical library:
``` shell
git submodule update --init
```

## Installing Agda and Emacs with Nix

This is the recommended way to install this course if you do not
already have Agda 2.6.3 installed.

First, install the Nix package manager:

Linux:
``` shell
sh <(curl -L https://nixos.org/nix/install) --daemon
```

Mac:
``` shell
sh <(curl -L https://nixos.org/nix/install)
```

Now we need to enable Nix flakes
``` shell
mkdir -p ~/.config/nix
echo "experimental-features = nix-command flakes" >> ~/.config/nix/nix.conf
```

For a fun series of blog posts on Nix and how to use it, [click this
link](https://ianthehenry.com/posts/how-to-learn-nix/). We won't need
any heavy lifting here, we're just using Nix to install Agda easily.

Now, when you want to work in Agda with emacs on this project,
navigate to the directory that you cloned this in and run
``` shell
nix develop
```

This might take a while the first time. Then you can run
``` shell
emacs
```
then navigate to one of the lecture files, and hit `C-c C-l` to load it.

## Alternative: Install Agda and VSCode on Mac

Install Homebrew from https://brew.sh/ , then run
``` shell
brew install agda git
```

Install VSCode from https://code.visualstudio.com/ , and then the
agda-mode extension from
https://marketplace.visualstudio.com/items?itemName=banacorn.agda-mode

If your key combinations (like `C-c C-c`) don't work, you may need to
apply the temporary fix described in
https://github.com/banacorn/agda-mode-vscode/issues/132#issuecomment-1368880358

## Alternative on Mac: Install Adga and Emacs using Brew

Install Homebrew from https://brew.sh/

``` shell
brew tap d12frosted/emacs-plus
brew install agda git emacs-plus
agda-mode setup
```

Now try running `emacs` in the terminal. If a nice `emacs` window
doesn't appear, run
``` shell
brew link --overwrite emacs-plus
```

Finally, add the following line to your `~/.emacs` file, so that the
literate Agda files are recognised correctly.
``` emacs-lisp
(add-to-list 'auto-mode-alist '("\\.lagda.md\\'" . agda2-mode))
```

## Alternative on Windows: Install Adga using Stack

Install Stack from https://docs.haskellstack.org/en/stable/install_and_upgrade/

Open PowerShell, and use Stack to install Agda:
``` shell
stack config set resolver nightly-2023-05-17
stack install Agda-2.6.3
```

Install VSCode from https://code.visualstudio.com/ , and then the
agda-mode extension from
https://marketplace.visualstudio.com/items?itemName=banacorn.agda-mode


<!-- Install Emacs from http://ftpmirror.gnu.org/emacs/windows by choosing -->
<!-- the latest version (at time of writing, `emacs-28.2-installer.exe`). -->

<!-- Open Emacs, and open your init file, by pressing `C-x C-f` and typing -->
<!-- `~/.emacs`. Add the following lines: -->

<!-- ``` emacs-lisp -->
<!-- (load-file (let ((coding-system-for-read 'utf-8)) -->
<!--                 (shell-command-to-string "agda-mode locate"))) -->

<!-- (add-to-list 'auto-mode-alist '("\\.lagda.md\\'" . agda2-mode)) -->
<!-- ``` -->

# Using agda-mode

Most Agda keybindings involve holding down Control or Meta
(a.k.a. Alt) and pressing other keys. Loading and checking an Agda
file has the keybinding `C-c C-l`, so to open a file, hold down
Control then press `c` followed by `l`, you do not have to let go of
Control between.

* `C-c C-l`: Load and check the file
* `M-.`: Jump to the definition of whatever your cursor is on
* `C-c C-f`: Move to next goal (forward)
* `C-c C-b`: Move to previous goal (backwards)

* `C-c C-c`: Case split (specify an argument to split on)
* `C-c C-r`: Refine goal (Add a `λ` if the goal is a function, add a
  `,` if the goal is a pair, etc. Not always the right move!)
* `C-c C-.`: Show the goal type, context and inferred type

## General editing:

If you are using Emacs, then most of the useful keybindings will also
be of that form.

* `C-x C-f`: Open a file
* `C-x C-s`: Save the current file
* `C-x C-b`: See all the things ("buffers") you have open
* `C-x b`: Choose a buffer to switch to
* `C-_`: Undo
* `M-_`: Redo

# Attribution

This course was written by David Jaz Myers and Mitchell Riley.

Thanks to Owen Lynch for his Nix-fu.
