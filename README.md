# Logic and Proof

This is a textbook for learning logic and proofs, 
as well as interactive theorem proving with `lean4`,
written by Jeremy Avigad, Joseph Hua, Robert Y. Lewis, and Floris van Doorn. 
The web version is [available here](https://leanprover.github.io/logic_and_proof).
It is based on the older version
[available here](https://github.com/leanprover/logic_and_proof_lean3/tree/master),
which uses `lean3`.

# Installation 

## Overview

We need
- an old version of `python` e.g. 3.5.4
- the virtual environment for this version of `python`
- `convert` from [imagemagick](https://imagemagick.org/)
- `xelatex` and `latexmk`

## `imagemagick`/`convert`
- follow [instructions for installing `imagemagick`](https://imagemagick.org/script/download.php)

## `latex`
- there are many ways of installing `xelatex` and `latexmk`,
  we won't describe them here
- note that `latexmk` might come under some other package such as `texlive-binextra`

## `pyenv` and `virtualenv`
- install [`pyenv`](https://github.com/pyenv/pyenv)
- install suitable version of python e.g. `python3.5.4` using `pyenv` by doing 
  ```
  pyenv install 3.5.4
  ```
- change global python version to `3.5.4` by doing
  ```
  pyenv global 3.5.4
  ```
- check versions by doing 
  ```
  pyenv versions
  ```
- install [`pyenv-virtualenv`](https://github.com/pyenv/pyenv-virtualenv)
- add the following to `~/.bashrc` (or equivalent)
  ```
  export PYENV_ROOT="$HOME/.pyenv"
  command -v pyenv >/dev/null || export PATH="$PYENV_ROOT/bin:$PATH"
  eval "$(pyenv init -)"
  eval "$(pyenv virtualenv-init -)"
  ```
- close and reopen terminal for changes to take effect

## Make the virtual environment
- make a virtual environment. We called it environment3.5.4
  ```
  pyenv virtualenv 3.5.4 environment3.5.4
  ```
- you can activate the virtual environment by doing 
  ```
    pyenv activate environment3.5.4
  ```
- then install `sphinx` using `pip` inside virtual environment
  ```
  pip install --trusted-host pypi.python.org sphinx
  ```
- `source deactivate` will deactivate the virtual environment
 
## Clone the sphinx project repository
- clone the project into project directory `/logic_and_proof/`, 
  ```
    git clone https://github.com/leanprover-community/logic_and_proof.git
    cd logic_and_proof
  ```

- go to `MAKE` and make sure 
  ```
  VENVDIR := "$HOME/.pyenv/versions/environment3.5.4"
  ```
  so that `make` will use the virtual environment we made. 
  If you chose a different name for the virtual environment, change this line accordingly.
- now in project directory, with the virtual environment active, we can do 
  ```
  make images
  make html
  make latexpdf
  ```
- The call to `make images` is also only required the first time, or if you add new latex source to `latex_images` after that.
- note that the original 
  ```
  make install-deps
  ```
  seems to no longer work because the link https://bitbucket.org/gebner/pygments-main/get/default.tar.gz#egg=Pygments is dead.
  This would give a bundled version of Sphinx and Pygments with improved syntax highlighting for Lean.


<!-- # How to test the Lean code snippets -->

<!-- ``` -->
<!-- make leantest -->
<!-- ``` -->

<!-- # How to deploy -->

<!-- ``` -->
<!-- ./deploy.sh leanprover logic_and_proof -->
<!-- ``` -->

# How to contribute

Pull requests with corrections are welcome. 
Please follow our [commit conventions](https://github.com/leanprover/lean4/blob/master/doc/dev/commit_convention.md).
If you have questions about whether a change will be considered helpful, 
please contact Jeremy Avigad, ``avigad@cmu.edu``.
