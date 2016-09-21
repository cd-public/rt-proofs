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
# coq_makefile -f _CoqProject ./util/ssromega.v ./util/seqset.v ./util/sorting.v ./util/step_function.v ./util/minmax.v ./util/powerset.v ./util/all.v ./util/ord_quantifier.v ./util/nat.v ./util/sum.v ./util/bigord.v ./util/counting.v ./util/tactics.v ./util/induction.v ./util/list.v ./util/divround.v ./util/bigcat.v ./util/fixedpoint.v ./util/notation.v ./analysis/global/jitter/bertogna_fp_comp.v ./analysis/global/jitter/interference_bound_edf.v ./analysis/global/jitter/workload_bound.v ./analysis/global/jitter/bertogna_edf_comp.v ./analysis/global/jitter/bertogna_fp_theory.v ./analysis/global/jitter/interference_bound.v ./analysis/global/jitter/interference_bound_fp.v ./analysis/global/jitter/bertogna_edf_theory.v ./analysis/global/parallel/bertogna_fp_comp.v ./analysis/global/parallel/interference_bound_edf.v ./analysis/global/parallel/workload_bound.v ./analysis/global/parallel/bertogna_edf_comp.v ./analysis/global/parallel/bertogna_fp_theory.v ./analysis/global/parallel/interference_bound.v ./analysis/global/parallel/interference_bound_fp.v ./analysis/global/parallel/bertogna_edf_theory.v ./analysis/global/basic/bertogna_fp_comp.v ./analysis/global/basic/interference_bound_edf.v ./analysis/global/basic/workload_bound.v ./analysis/global/basic/bertogna_edf_comp.v ./analysis/global/basic/bertogna_fp_theory.v ./analysis/global/basic/interference_bound.v ./analysis/global/basic/interference_bound_fp.v ./analysis/global/basic/bertogna_edf_theory.v ./analysis/apa/bertogna_fp_comp.v ./analysis/apa/interference_bound_edf.v ./analysis/apa/workload_bound.v ./analysis/apa/bertogna_edf_comp.v ./analysis/apa/bertogna_fp_theory.v ./analysis/apa/interference_bound.v ./analysis/apa/interference_bound_fp.v ./analysis/apa/bertogna_edf_theory.v ./analysis/uni/basic/workload_bound_fp.v ./analysis/uni/basic/fp_rta_comp.v ./analysis/uni/basic/fp_rta_theory.v ./model/arrival_sequence.v ./model/task.v ./model/task_arrival.v ./model/partitioned/schedulability.v ./model/partitioned/schedule.v ./model/priority.v ./model/global/workload.v ./model/global/schedulability.v ./model/global/jitter/interference_edf.v ./model/global/jitter/interference.v ./model/global/jitter/job.v ./model/global/jitter/constrained_deadlines.v ./model/global/jitter/schedule.v ./model/global/jitter/platform.v ./model/global/response_time.v ./model/global/basic/interference_edf.v ./model/global/basic/interference.v ./model/global/basic/constrained_deadlines.v ./model/global/basic/schedule.v ./model/global/basic/platform.v ./model/job.v ./model/time.v ./model/arrival_bounds.v ./model/apa/interference_edf.v ./model/apa/interference.v ./model/apa/affinity.v ./model/apa/constrained_deadlines.v ./model/apa/platform.v ./model/uni/workload.v ./model/uni/transformation/construction.v ./model/uni/schedulability.v ./model/uni/schedule_of_task.v ./model/uni/response_time.v ./model/uni/schedule.v ./model/uni/basic/arrival_bounds.v ./model/uni/basic/busy_interval.v ./model/uni/basic/platform.v ./model/uni/service.v ./implementation/arrival_sequence.v ./implementation/task.v ./implementation/global/jitter/arrival_sequence.v ./implementation/global/jitter/task.v ./implementation/global/jitter/bertogna_edf_example.v ./implementation/global/jitter/job.v ./implementation/global/jitter/bertogna_fp_example.v ./implementation/global/jitter/schedule.v ./implementation/global/parallel/bertogna_edf_example.v ./implementation/global/parallel/bertogna_fp_example.v ./implementation/global/basic/bertogna_edf_example.v ./implementation/global/basic/bertogna_fp_example.v ./implementation/global/basic/schedule.v ./implementation/job.v ./implementation/apa/arrival_sequence.v ./implementation/apa/task.v ./implementation/apa/bertogna_edf_example.v ./implementation/apa/job.v ./implementation/apa/bertogna_fp_example.v ./implementation/apa/schedule.v ./implementation/uni/basic/fp_rta_example.v ./implementation/uni/basic/schedule.v -o Makefile 
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
COQDOCFLAGS?=-interpolate -utf8 --plain-comments --parse-comments --external https://math-comp.github.io/math-comp/htmldoc/ mathcomp
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

VFILES:=util/ssromega.v\
  util/seqset.v\
  util/sorting.v\
  util/step_function.v\
  util/minmax.v\
  util/powerset.v\
  util/all.v\
  util/ord_quantifier.v\
  util/nat.v\
  util/sum.v\
  util/bigord.v\
  util/counting.v\
  util/tactics.v\
  util/induction.v\
  util/list.v\
  util/divround.v\
  util/bigcat.v\
  util/fixedpoint.v\
  util/notation.v\
  analysis/global/jitter/bertogna_fp_comp.v\
  analysis/global/jitter/interference_bound_edf.v\
  analysis/global/jitter/workload_bound.v\
  analysis/global/jitter/bertogna_edf_comp.v\
  analysis/global/jitter/bertogna_fp_theory.v\
  analysis/global/jitter/interference_bound.v\
  analysis/global/jitter/interference_bound_fp.v\
  analysis/global/jitter/bertogna_edf_theory.v\
  analysis/global/parallel/bertogna_fp_comp.v\
  analysis/global/parallel/interference_bound_edf.v\
  analysis/global/parallel/workload_bound.v\
  analysis/global/parallel/bertogna_edf_comp.v\
  analysis/global/parallel/bertogna_fp_theory.v\
  analysis/global/parallel/interference_bound.v\
  analysis/global/parallel/interference_bound_fp.v\
  analysis/global/parallel/bertogna_edf_theory.v\
  analysis/global/basic/bertogna_fp_comp.v\
  analysis/global/basic/interference_bound_edf.v\
  analysis/global/basic/workload_bound.v\
  analysis/global/basic/bertogna_edf_comp.v\
  analysis/global/basic/bertogna_fp_theory.v\
  analysis/global/basic/interference_bound.v\
  analysis/global/basic/interference_bound_fp.v\
  analysis/global/basic/bertogna_edf_theory.v\
  analysis/apa/bertogna_fp_comp.v\
  analysis/apa/interference_bound_edf.v\
  analysis/apa/workload_bound.v\
  analysis/apa/bertogna_edf_comp.v\
  analysis/apa/bertogna_fp_theory.v\
  analysis/apa/interference_bound.v\
  analysis/apa/interference_bound_fp.v\
  analysis/apa/bertogna_edf_theory.v\
  analysis/uni/basic/workload_bound_fp.v\
  analysis/uni/basic/fp_rta_comp.v\
  analysis/uni/basic/fp_rta_theory.v\
  model/arrival_sequence.v\
  model/task.v\
  model/task_arrival.v\
  model/partitioned/schedulability.v\
  model/partitioned/schedule.v\
  model/priority.v\
  model/global/workload.v\
  model/global/schedulability.v\
  model/global/jitter/interference_edf.v\
  model/global/jitter/interference.v\
  model/global/jitter/job.v\
  model/global/jitter/constrained_deadlines.v\
  model/global/jitter/schedule.v\
  model/global/jitter/platform.v\
  model/global/response_time.v\
  model/global/basic/interference_edf.v\
  model/global/basic/interference.v\
  model/global/basic/constrained_deadlines.v\
  model/global/basic/schedule.v\
  model/global/basic/platform.v\
  model/job.v\
  model/time.v\
  model/arrival_bounds.v\
  model/apa/interference_edf.v\
  model/apa/interference.v\
  model/apa/affinity.v\
  model/apa/constrained_deadlines.v\
  model/apa/platform.v\
  model/uni/workload.v\
  model/uni/transformation/construction.v\
  model/uni/schedulability.v\
  model/uni/schedule_of_task.v\
  model/uni/response_time.v\
  model/uni/schedule.v\
  model/uni/basic/arrival_bounds.v\
  model/uni/basic/busy_interval.v\
  model/uni/basic/platform.v\
  model/uni/service.v\
  implementation/arrival_sequence.v\
  implementation/task.v\
  implementation/global/jitter/arrival_sequence.v\
  implementation/global/jitter/task.v\
  implementation/global/jitter/bertogna_edf_example.v\
  implementation/global/jitter/job.v\
  implementation/global/jitter/bertogna_fp_example.v\
  implementation/global/jitter/schedule.v\
  implementation/global/parallel/bertogna_edf_example.v\
  implementation/global/parallel/bertogna_fp_example.v\
  implementation/global/basic/bertogna_edf_example.v\
  implementation/global/basic/bertogna_fp_example.v\
  implementation/global/basic/schedule.v\
  implementation/job.v\
  implementation/apa/arrival_sequence.v\
  implementation/apa/task.v\
  implementation/apa/bertogna_edf_example.v\
  implementation/apa/job.v\
  implementation/apa/bertogna_fp_example.v\
  implementation/apa/schedule.v\
  implementation/uni/basic/fp_rta_example.v\
  implementation/uni/basic/schedule.v

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
	find . -name "*.vo" -delete -o -name "*.glob" -delete -o -name "*.v.d" -delete -o -name "*.vio" -delete -o -name "*.old" -delete -o -name "*.beautified" -delete
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

