.PHONY: coq clean

COQC=coqc -q -R ./Frap Frap

coq:
	$(COQC) Example_Correctness
	$(COQC) Example_Rules

clean:
	rm -f *.vo *.glob
