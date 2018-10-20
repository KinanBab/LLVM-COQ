.PHONY: coq clean frap

COQC=coqc -q -R ./Frap Frap

coq: frap
	$(COQC) Example_Correctness
	$(COQC) Example_Rules

clean:
	rm -f *.vo *.glob

frap:
	cd Frap/ && make lib
