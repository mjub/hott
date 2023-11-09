FROM coqorg/coq

RUN opam update --yes
RUN opam install --yes vscoq-language-server
