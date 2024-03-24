
FROM ubuntu:22.04

SHELL ["/bin/bash", "-c"]

ARG userID
ARG groupID

RUN if [ -z "${userID}" ];  then echo "ERROR: userID not set" >&2;  exit 1; fi
RUN if [ -z "${groupID}" ]; then echo "ERROR: groupID not set" >&2; exit 1; fi

RUN apt upgrade \
 && apt -y update \
 && apt -y install --no-install-recommends \
    ghc \
    cabal-install \
    emacs \
    happy \
    alex \
    pkg-config \
    zlib1g-dev \
    git \
    ssh \
  && rm -rf /var/lib/apt/lists/*

RUN groupadd -g ${groupID} agda
RUN useradd -m -u ${userID} -g agda --shell /bin/bash agda

USER agda:agda

RUN cabal update \
  && cabal install Agda-2.6.4

# install agda-stdlib
RUN mkdir $HOME/.agda
RUN cd $HOME/.agda \
  && git config --global http.sslVerify false \
  && git clone https://github.com/agda/agda-stdlib.git \
  && cd $HOME/.agda/agda-stdlib \
  && git checkout v1.7.3 \
  && cd $HOME/.agda/ \
  && echo -e "~/.agda/agda-stdlib/standard-library.agda-lib\n" > libraries \
  && echo -e "standard-library\n" > defaults

ENV PATH="${PATH}:/home/agda/.cabal/bin"
