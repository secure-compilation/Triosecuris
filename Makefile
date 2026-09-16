COQMFFLAGS := -Q . SECF

# For tests: EXCLUDE := MiniCET_Index.v MoreLinearProof.v Safe.v
EXCLUDE := MiniCET_Index.v MoreLinear.v MoreLinearProof.v Safe.v TestingMiniCET.v
ALLVFILES := $(filter-out $(EXCLUDE), $(wildcard *.v))
QC := quickChick # ../QuickChick/quickChickTool/quickChickTool.exe
QCFLAGS := -color -top SECF -N 10000 -failfast -cmd "make -j >/dev/null 2>&1 && echo 'compilation done'" # -ntests 100,1000,10000

build: Makefile.coq
	$(MAKE) -f Makefile.coq

clean::
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	$(RM) $(wildcard Makefile.coq Makefile.coq.conf)
	rm -rf ../_qc_$(shell basename $(CURDIR)).tmp *.bak

test: Makefile.coq clean
	@EXTRAFLAGS=""; \
	if [ -n "$(SECTION)" ]; then EXTRAFLAGS="-s $(SECTION)"; fi; \
	if [ -n "$(EXCLUDE)" ]; then EXTRAFLAGS="-exclude $(EXCLUDE) $$EXTRAFLAGS"; fi; \
	$(QC) $(QCFLAGS) $$EXTRAFLAGS

Makefile.coq: $(ALLVFILES)
	coq_makefile $(COQMFFLAGS) -o Makefile.coq $(ALLVFILES)

-include Makefile.coq

.PHONY: build clean
