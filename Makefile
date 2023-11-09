# Compile Coq files and generate documentation with a single Make command.

VFILES := $(shell find . -name '*.v')
CMD := coq-all real-all coq-html coq-clean

all: coq-all coq-html

clean: coq-clean
	@rm -rf Makefile.coq Makefile.coq.conf html

$(CMD): Makefile.coq
	@+$(MAKE) -f $< $(subst coq-,,$@)

Makefile.coq: _CoqProject Makefile ${VFILES}
	@$(COQBIN)coq_makefile -f $< -o $@ $(shell coqdep -sort ${VFILES})

.PHONY: ${CMD} $(subst coq-,,${CMD})
