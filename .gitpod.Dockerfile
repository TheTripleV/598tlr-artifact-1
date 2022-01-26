FROM gitpod/workspace-full

RUN sudo apt-get update -y

RUN sudo apt-get install -y cabal-install

RUN brew install haskell-stack
RUN stack install brittany hlint

RUN cabal update
RUN cabal install alex happy

RUN sudo apt-get install -y zlib1g-dev libncurses5-dev

RUN cabal install Agda

