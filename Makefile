.PHONY: coq all clean

FILES = Regex.v Tree.v Semantics.v

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
