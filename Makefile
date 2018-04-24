TJROOT = /usr/local/bin
#VPATH = ../common

#export TJPATH = ../common

.PHONY: all 
all: basic lkf geometric expansions

.PHONY: basic
basic: lib.lp

.PHONY: lkf 
lkf: basic classical.lp lkf-formulas.lp lkf-kernel.lp

.PHONY: geometric
geometric: geo-fpc.lp geo-examples.lp 

.PHONY: expansions
expansions: exp-fpc.lp exp-examples.lp

%.lpo : %.mod %.sig
	$(TJROOT)/tjcc  $*

%.lp : %.lpo
	$(TJROOT)/tjlink  $*

-include depend
depend: *.mod *.sig
		$(TJROOT)/tjdepend *.mod  > depend-stage
		mv depend-stage depend

.PHONY: clean
clean:
	rm -f *.lpo *.lp *.DT depend

.PHONY: tests
tests: geo-examples.lp exp-examples.lp
	$(TJROOT)/tjsim -b -s "test_all." geo-examples
	$(TJROOT)/tjsim -b -s "test_all." exp-examples
