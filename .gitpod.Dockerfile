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

RUN ( echo "" ; echo "(setq agda2-backend \"GHC\" )" ; echo "" ) >> /home/gitpod/.emacs

RUN ( echo "" ; echo "(load-file (let ((coding-system-for-read \'utf-8)) (shell-command-to-string \"agda-mode locate\")))" ; echo "" ) >> /home/gitpod/.emacs
