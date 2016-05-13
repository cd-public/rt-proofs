#############################################################################
##  v      #                   The Coq Proof Assistant                     ##
## <O___,, #                INRIA - CNRS - LIX - LRI - PPS                 ##
##   \VV/  #                                                               ##
##    //   #  Makefile automagically generated by coq_makefile V8.5pl1     ##
#############################################################################

# WARNING
#
# This Makefile has been automagically generated
# Edit at your own risks !
#
# END OF WARNING

#
# This Makefile was generated by the command line :
# coq_makefile -f _CoqProject ./util/fixedpoint.v ./util/ssromega.v ./util/bigcat.v ./util/nat.v ./util/seqset.v ./util/notation.v ./util/list.v ./util/powerset.v ./util/all.v ./util/sorting.v ./util/tactics.v ./util/bigord.v ./util/exists.v ./util/induction.v ./util/sum.v ./util/divround.v ./util/counting.v ./implementation/basic/bertogna_edf_example.v ./implementation/basic/task.v ./implementation/basic/schedule.v ./implementation/basic/bertogna_fp_example.v ./implementation/basic/job.v ./implementation/basic/arrival_sequence.v ./implementation/parallel/bertogna_edf_example.v ./implementation/parallel/task.v ./implementation/parallel/schedule.v ./implementation/parallel/bertogna_fp_example.v ./implementation/parallel/job.v ./implementation/parallel/arrival_sequence.v ./implementation/jitter/bertogna_edf_example.v ./implementation/jitter/task.v ./implementation/jitter/schedule.v ./implementation/jitter/bertogna_fp_example.v ./implementation/jitter/job.v ./implementation/jitter/arrival_sequence.v ./implementation/apa/bertogna_edf_example.v ./implementation/apa/task.v ./implementation/apa/schedule.v ./implementation/apa/bertogna_fp_example.v ./implementation/apa/job.v ./implementation/apa/arrival_sequence.v ./analysis/basic/bertogna_fp_theory.v ./analysis/basic/interference_bound_edf.v ./analysis/basic/interference_bound_fp.v ./analysis/basic/interference_bound.v ./analysis/basic/bertogna_edf_comp.v ./analysis/basic/bertogna_fp_comp.v ./analysis/basic/bertogna_edf_theory.v ./analysis/basic/workload_bound.v ./analysis/parallel/bertogna_fp_theory.v ./analysis/parallel/interference_bound_edf.v ./analysis/parallel/interference_bound_fp.v ./analysis/parallel/interference_bound.v ./analysis/parallel/bertogna_edf_comp.v ./analysis/parallel/bertogna_fp_comp.v ./analysis/parallel/bertogna_edf_theory.v ./analysis/parallel/workload_bound.v ./analysis/jitter/bertogna_fp_theory.v ./analysis/jitter/interference_bound_edf.v ./analysis/jitter/interference_bound_fp.v ./analysis/jitter/interference_bound.v ./analysis/jitter/bertogna_edf_comp.v ./analysis/jitter/bertogna_fp_comp.v ./analysis/jitter/bertogna_edf_theory.v ./analysis/jitter/workload_bound.v ./analysis/apa/bertogna_fp_theory.v ./analysis/apa/interference_bound_edf.v ./analysis/apa/interference_bound_fp.v ./analysis/apa/interference_bound.v ./analysis/apa/bertogna_edf_comp.v ./analysis/apa/bertogna_fp_comp.v ./analysis/apa/bertogna_edf_theory.v ./analysis/apa/workload_bound.v ./model/basic/time.v ./model/basic/schedulability.v ./model/basic/task.v ./model/basic/task_arrival.v ./model/basic/platform.v ./model/basic/schedule.v ./model/basic/priority.v ./model/basic/interference_edf.v ./model/basic/interference.v ./model/basic/constrained_deadlines.v ./model/basic/workload.v ./model/basic/job.v ./model/basic/arrival_sequence.v ./model/basic/response_time.v ./model/jitter/time.v ./model/jitter/schedulability.v ./model/jitter/task.v ./model/jitter/task_arrival.v ./model/jitter/platform.v ./model/jitter/schedule.v ./model/jitter/priority.v ./model/jitter/interference_edf.v ./model/jitter/interference.v ./model/jitter/constrained_deadlines.v ./model/jitter/workload.v ./model/jitter/job.v ./model/jitter/arrival_sequence.v ./model/jitter/response_time.v ./model/apa/time.v ./model/apa/schedulability.v ./model/apa/task.v ./model/apa/task_arrival.v ./model/apa/platform.v ./model/apa/schedule.v ./model/apa/priority.v ./model/apa/affinity.v ./model/apa/interference_edf.v ./model/apa/interference.v ./model/apa/constrained_deadlines.v ./model/apa/workload.v ./model/apa/job.v ./model/apa/arrival_sequence.v ./model/apa/response_time.v -o Makefile 
#

.DEFAULT_GOAL := all

# This Makefile may take arguments passed as environment variables:
# COQBIN to specify the directory where Coq binaries resides;
# TIMECMD set a command to log .v compilation time;
# TIMED if non empty, use the default time command as TIMECMD;
# ZDEBUG/COQDEBUG to specify debug flags for ocamlc&ocamlopt/coqc;
# DSTROOT to specify a prefix to install path.

# Here is a hack to make $(eval $(shell works:
define donewline


endef
includecmdwithout@ = $(eval $(subst @,$(donewline),$(shell { $(1) | tr -d '\r' | tr '\n' '@'; })))
$(call includecmdwithout@,$(COQBIN)coqtop -config)

TIMED=
TIMECMD=
STDTIME?=/usr/bin/time -f "$* (user: %U mem: %M ko)"
TIMER=$(if $(TIMED), $(STDTIME), $(TIMECMD))

vo_to_obj = $(addsuffix .o,\
  $(filter-out Warning: Error:,\
  $(shell $(COQBIN)coqtop -q -noinit -batch -quiet -print-mod-uid $(1))))

##########################
#                        #
# Libraries definitions. #
#                        #
##########################

COQLIBS?=\
  -R "." rt
COQDOCLIBS?=\
  -R "." rt

##########################
#                        #
# Variables definitions. #
#                        #
##########################


OPT?=
COQDEP?="$(COQBIN)coqdep" -c
COQFLAGS?=-q $(OPT) $(COQLIBS) $(OTHERFLAGS) $(COQ_XML)
COQCHKFLAGS?=-silent -o
COQDOCFLAGS?=-interpolate -utf8 --parse-comments --external https://math-comp.github.io/math-comp/htmldoc/ mathcomp
COQC?=$(TIMER) "$(COQBIN)coqc"
GALLINA?="$(COQBIN)gallina"
COQDOC?="$(COQBIN)coqdoc"
COQCHK?="$(COQBIN)coqchk"
COQMKTOP?="$(COQBIN)coqmktop"

##################
#                #
# Install Paths. #
#                #
##################

ifdef USERINSTALL
XDG_DATA_HOME?="$(HOME)/.local/share"
COQLIBINSTALL=$(XDG_DATA_HOME)/coq
COQDOCINSTALL=$(XDG_DATA_HOME)/doc/coq
else
COQLIBINSTALL="${COQLIB}user-contrib"
COQDOCINSTALL="${DOCDIR}user-contrib"
COQTOPINSTALL="${COQLIB}toploop"
endif

######################
#                    #
# Files dispatching. #
#                    #
######################

VFILES:=util/fixedpoint.v\
  util/ssromega.v\
  util/bigcat.v\
  util/nat.v\
  util/seqset.v\
  util/notation.v\
  util/list.v\
  util/powerset.v\
  util/all.v\
  util/sorting.v\
  util/tactics.v\
  util/bigord.v\
  util/exists.v\
  util/induction.v\
  util/sum.v\
  util/divround.v\
  util/counting.v\
  implementation/basic/bertogna_edf_example.v\
  implementation/basic/task.v\
  implementation/basic/schedule.v\
  implementation/basic/bertogna_fp_example.v\
  implementation/basic/job.v\
  implementation/basic/arrival_sequence.v\
  implementation/parallel/bertogna_edf_example.v\
  implementation/parallel/task.v\
  implementation/parallel/schedule.v\
  implementation/parallel/bertogna_fp_example.v\
  implementation/parallel/job.v\
  implementation/parallel/arrival_sequence.v\
  implementation/jitter/bertogna_edf_example.v\
  implementation/jitter/task.v\
  implementation/jitter/schedule.v\
  implementation/jitter/bertogna_fp_example.v\
  implementation/jitter/job.v\
  implementation/jitter/arrival_sequence.v\
  implementation/apa/bertogna_edf_example.v\
  implementation/apa/task.v\
  implementation/apa/schedule.v\
  implementation/apa/bertogna_fp_example.v\
  implementation/apa/job.v\
  implementation/apa/arrival_sequence.v\
  analysis/basic/bertogna_fp_theory.v\
  analysis/basic/interference_bound_edf.v\
  analysis/basic/interference_bound_fp.v\
  analysis/basic/interference_bound.v\
  analysis/basic/bertogna_edf_comp.v\
  analysis/basic/bertogna_fp_comp.v\
  analysis/basic/bertogna_edf_theory.v\
  analysis/basic/workload_bound.v\
  analysis/parallel/bertogna_fp_theory.v\
  analysis/parallel/interference_bound_edf.v\
  analysis/parallel/interference_bound_fp.v\
  analysis/parallel/interference_bound.v\
  analysis/parallel/bertogna_edf_comp.v\
  analysis/parallel/bertogna_fp_comp.v\
  analysis/parallel/bertogna_edf_theory.v\
  analysis/parallel/workload_bound.v\
  analysis/jitter/bertogna_fp_theory.v\
  analysis/jitter/interference_bound_edf.v\
  analysis/jitter/interference_bound_fp.v\
  analysis/jitter/interference_bound.v\
  analysis/jitter/bertogna_edf_comp.v\
  analysis/jitter/bertogna_fp_comp.v\
  analysis/jitter/bertogna_edf_theory.v\
  analysis/jitter/workload_bound.v\
  analysis/apa/bertogna_fp_theory.v\
  analysis/apa/interference_bound_edf.v\
  analysis/apa/interference_bound_fp.v\
  analysis/apa/interference_bound.v\
  analysis/apa/bertogna_edf_comp.v\
  analysis/apa/bertogna_fp_comp.v\
  analysis/apa/bertogna_edf_theory.v\
  analysis/apa/workload_bound.v\
  model/basic/time.v\
  model/basic/schedulability.v\
  model/basic/task.v\
  model/basic/task_arrival.v\
  model/basic/platform.v\
  model/basic/schedule.v\
  model/basic/priority.v\
  model/basic/interference_edf.v\
  model/basic/interference.v\
  model/basic/constrained_deadlines.v\
  model/basic/workload.v\
  model/basic/job.v\
  model/basic/arrival_sequence.v\
  model/basic/response_time.v\
  model/jitter/time.v\
  model/jitter/schedulability.v\
  model/jitter/task.v\
  model/jitter/task_arrival.v\
  model/jitter/platform.v\
  model/jitter/schedule.v\
  model/jitter/priority.v\
  model/jitter/interference_edf.v\
  model/jitter/interference.v\
  model/jitter/constrained_deadlines.v\
  model/jitter/workload.v\
  model/jitter/job.v\
  model/jitter/arrival_sequence.v\
  model/jitter/response_time.v\
  model/apa/time.v\
  model/apa/schedulability.v\
  model/apa/task.v\
  model/apa/task_arrival.v\
  model/apa/platform.v\
  model/apa/schedule.v\
  model/apa/priority.v\
  model/apa/affinity.v\
  model/apa/interference_edf.v\
  model/apa/interference.v\
  model/apa/constrained_deadlines.v\
  model/apa/workload.v\
  model/apa/job.v\
  model/apa/arrival_sequence.v\
  model/apa/response_time.v

ifneq ($(filter-out archclean clean cleanall printenv,$(MAKECMDGOALS)),)
-include $(addsuffix .d,$(VFILES))
else
ifeq ($(MAKECMDGOALS),)
-include $(addsuffix .d,$(VFILES))
endif
endif

.SECONDARY: $(addsuffix .d,$(VFILES))

VO=vo
VOFILES:=$(VFILES:.v=.$(VO))
GLOBFILES:=$(VFILES:.v=.glob)
GFILES:=$(VFILES:.v=.g)
HTMLFILES:=$(VFILES:.v=.html)
GHTMLFILES:=$(VFILES:.v=.g.html)
OBJFILES=$(call vo_to_obj,$(VOFILES))
ALLNATIVEFILES=$(OBJFILES:.o=.cmi) $(OBJFILES:.o=.cmo) $(OBJFILES:.o=.cmx) $(OBJFILES:.o=.cmxs)
NATIVEFILES=$(foreach f, $(ALLNATIVEFILES), $(wildcard $f))
ifeq '$(HASNATDYNLINK)' 'true'
HASNATDYNLINK_OR_EMPTY := yes
else
HASNATDYNLINK_OR_EMPTY :=
endif

#######################################
#                                     #
# Definition of the toplevel targets. #
#                                     #
#######################################

all: $(VOFILES) 

quick: $(VOFILES:.vo=.vio)

vio2vo:
	$(COQC) $(COQDEBUG) $(COQFLAGS) -schedule-vio2vo $(J) $(VOFILES:%.vo=%.vio)
checkproofs:
	$(COQC) $(COQDEBUG) $(COQFLAGS) -schedule-vio-checking $(J) $(VOFILES:%.vo=%.vio)
gallina: $(GFILES)

html: $(GLOBFILES) $(VFILES)
	- mkdir -p html
	$(COQDOC) -toc $(COQDOCFLAGS) -html $(COQDOCLIBS) -d html $(VFILES)

gallinahtml: $(GLOBFILES) $(VFILES)
	- mkdir -p html
	$(COQDOC) -toc $(COQDOCFLAGS) -html -g $(COQDOCLIBS) -d html $(VFILES)

all.ps: $(VFILES)
	$(COQDOC) -toc $(COQDOCFLAGS) -ps $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $^`

all-gal.ps: $(VFILES)
	$(COQDOC) -toc $(COQDOCFLAGS) -ps -g $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $^`

all.pdf: $(VFILES)
	$(COQDOC) -toc $(COQDOCFLAGS) -pdf $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $^`

all-gal.pdf: $(VFILES)
	$(COQDOC) -toc $(COQDOCFLAGS) -pdf -g $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $^`

validate: $(VOFILES)
	$(COQCHK) $(COQCHKFLAGS) $(COQLIBS) $(addprefix rt., $(subst /,., $(^:.vo=)))

beautify: $(VFILES:=.beautified)
	for file in $^; do mv $${file%.beautified} $${file%beautified}old && mv $${file} $${file%.beautified}; done
	@echo 'Do not do "make clean" until you are sure that everything went well!'
	@echo 'If there were a problem, execute "for file in $$(find . -name \*.v.old -print); do mv $${file} $${file%.old}; done" in your shell/'

.PHONY: all archclean beautify byte clean cleanall gallina gallinahtml html install install-doc install-natdynlink install-toploop opt printenv quick uninstall userinstall validate vio2vo

####################
#                  #
# Special targets. #
#                  #
####################

byte:
	$(MAKE) all "OPT:=-byte"

opt:
	$(MAKE) all "OPT:=-opt"

userinstall:
	+$(MAKE) USERINSTALL=true install

install:
	cd "." && for i in $(VOFILES) $(VFILES) $(GLOBFILES) $(NATIVEFILES) $(CMOFILES) $(CMIFILES) $(CMAFILES); do \
	 install -d "`dirname "$(DSTROOT)"$(COQLIBINSTALL)/rt/$$i`"; \
	 install -m 0644 $$i "$(DSTROOT)"$(COQLIBINSTALL)/rt/$$i; \
	done

install-doc:
	install -d "$(DSTROOT)"$(COQDOCINSTALL)/rt/html
	for i in html/*; do \
	 install -m 0644 $$i "$(DSTROOT)"$(COQDOCINSTALL)/rt/$$i;\
	done

uninstall_me.sh: Makefile
	echo '#!/bin/sh' > $@
	printf 'cd "$${DSTROOT}"$(COQLIBINSTALL)/rt && rm -f $(VOFILES) $(VFILES) $(GLOBFILES) $(NATIVEFILES) $(CMOFILES) $(CMIFILES) $(CMAFILES) && find . -type d -and -empty -delete\ncd "$${DSTROOT}"$(COQLIBINSTALL) && find "rt" -maxdepth 0 -and -empty -exec rmdir -p \{\} \;\n' >> "$@"
	printf 'cd "$${DSTROOT}"$(COQDOCINSTALL)/rt \\\n' >> "$@"
	printf '&& rm -f $(shell find "html" -maxdepth 1 -and -type f -print)\n' >> "$@"
	printf 'cd "$${DSTROOT}"$(COQDOCINSTALL) && find rt/html -maxdepth 0 -and -empty -exec rmdir -p \{\} \;\n' >> "$@"
	chmod +x $@

uninstall: uninstall_me.sh
	sh $<

.merlin:
	@echo 'FLG -rectypes' > .merlin
	@echo "B $(COQLIB) kernel" >> .merlin
	@echo "B $(COQLIB) lib" >> .merlin
	@echo "B $(COQLIB) library" >> .merlin
	@echo "B $(COQLIB) parsing" >> .merlin
	@echo "B $(COQLIB) pretyping" >> .merlin
	@echo "B $(COQLIB) interp" >> .merlin
	@echo "B $(COQLIB) printing" >> .merlin
	@echo "B $(COQLIB) intf" >> .merlin
	@echo "B $(COQLIB) proofs" >> .merlin
	@echo "B $(COQLIB) tactics" >> .merlin
	@echo "B $(COQLIB) tools" >> .merlin
	@echo "B $(COQLIB) toplevel" >> .merlin
	@echo "B $(COQLIB) stm" >> .merlin
	@echo "B $(COQLIB) grammar" >> .merlin
	@echo "B $(COQLIB) config" >> .merlin

clean::
	rm -f $(OBJFILES) $(OBJFILES:.o=.native) $(NATIVEFILES)
	find . -name .coq-native -type d -empty -delete
	rm -f $(VOFILES) $(VOFILES:.vo=.vio) $(GFILES) $(VFILES:.v=.v.d) $(VFILES:=.beautified) $(VFILES:=.old)
	rm -f all.ps all-gal.ps all.pdf all-gal.pdf all.glob $(VFILES:.v=.glob) $(VFILES:.v=.tex) $(VFILES:.v=.g.tex) all-mli.tex
	- rm -rf html mlihtml uninstall_me.sh

cleanall:: clean
	rm -f $(patsubst %.v,.%.aux,$(VFILES))

archclean::
	rm -f *.cmx *.o

printenv:
	@"$(COQBIN)coqtop" -config
	@echo 'CAMLC =	$(CAMLC)'
	@echo 'CAMLOPTC =	$(CAMLOPTC)'
	@echo 'PP =	$(PP)'
	@echo 'COQFLAGS =	$(COQFLAGS)'
	@echo 'COQLIBINSTALL =	$(COQLIBINSTALL)'
	@echo 'COQDOCINSTALL =	$(COQDOCINSTALL)'

Makefile: _CoqProject
	mv -f $@ $@.bak
	"$(COQBIN)coq_makefile" -f $< -o $@


###################
#                 #
# Implicit rules. #
#                 #
###################

$(VOFILES): %.vo: %.v
	$(COQC) $(COQDEBUG) $(COQFLAGS) $*

$(GLOBFILES): %.glob: %.v
	$(COQC) $(COQDEBUG) $(COQFLAGS) $*

$(VFILES:.v=.vio): %.vio: %.v
	$(COQC) -quick $(COQDEBUG) $(COQFLAGS) $*

$(GFILES): %.g: %.v
	$(GALLINA) $<

$(VFILES:.v=.tex): %.tex: %.v
	$(COQDOC) $(COQDOCFLAGS) -latex $< -o $@

$(HTMLFILES): %.html: %.v %.glob
	$(COQDOC) $(COQDOCFLAGS) -html $< -o $@

$(VFILES:.v=.g.tex): %.g.tex: %.v
	$(COQDOC) $(COQDOCFLAGS) -latex -g $< -o $@

$(GHTMLFILES): %.g.html: %.v %.glob
	$(COQDOC) $(COQDOCFLAGS)  -html -g $< -o $@

$(addsuffix .d,$(VFILES)): %.v.d: %.v
	$(COQDEP) $(COQLIBS) "$<" > "$@" || ( RV=$$?; rm -f "$@"; exit $${RV} )

$(addsuffix .beautified,$(VFILES)): %.v.beautified:
	$(COQC) $(COQDEBUG) $(COQFLAGS) -beautify $*

# WARNING
#
# This Makefile has been automagically generated
# Edit at your own risks !
#
# END OF WARNING

