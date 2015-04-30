MODULES := task job priority schedule identmp apa helper liulayland
VS      := $(MODULES:%=%.v)

.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

		Makefile.coq: Makefile $(VS)
				coq_makefile -R . Sched $(VS) -o Makefile.coq

				clean:: Makefile.coq
						$(MAKE) -f Makefile.coq clean
								rm -f Makefile.coq
