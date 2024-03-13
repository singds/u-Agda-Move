
from ubuntu:22.04

SHELL ["/bin/bash", "-c"]

run apt upgrade \
 && apt -y update \
 && apt -y install \
    ghc \
    cabal-install \
    emacs \
    happy \
    alex \
    pkg-config \
    zlib1g-dev \
    git \
  && cabal update \
  && cabal install Agda-2.6.4

# install agda-stdlib
run mkdir ~/.agda
run cd ~/.agda \
  && git clone https://github.com/agda/agda-stdlib.git \
  && cd ~/.agda/agda-stdlib \
  && git checkout v1.7.3 \
  && cd ~/.agda/ \
  && echo -e "~/.agda/agda-stdlib/standard-library.agda-lib\n" > libraries \
  && echo -e "standard-library\n" > defaults

ENV PATH="${PATH}:/root/.cabal/bin"
