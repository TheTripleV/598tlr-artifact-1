FROM gitpod/workspace-full

RUN sudo apt-get update -y

RUN sudo apt-get install -y haskell-platform
RUN sudo curl -sSL https://get.haskellstack.org/ | sh

RUN sudo apt-get install -y cabal-install

RUN brew install haskell-stack

RUN cabal update
RUN cabal install alex happy

RUN sudo apt-get install -y zlib1g-dev libncurses5-dev

RUN sudo apt-get install -y emacs
RUN cabal install Agda


ENV PATH "$PATH:$HOME/.cabal/bin/"
