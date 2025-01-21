.PHONY: coq all clean

FILES = Chars.v Groups.v Regex.v Tree.v Semantics.v PikeTree.v NFA.v PikeVM.v

COQC = coqc
COQDEP = coqdep

all: coq

%.vo: %.v
	@echo COQC $*.v
	@$(COQC) $*.v

.depend: $(FILES)
	@echo COQDEP: Generating dependencies
	@$(COQDEP) $^ > .depend

coq_depend: .depend

coq: coq_depend $(FILES:%.v=%.vo)

clean:
	@echo Cleaning Coq compiled files
	-@rm .depend
	-@rm *.vo *.glob .*.aux *.vok *.vos .lia.cache

-include .depend
