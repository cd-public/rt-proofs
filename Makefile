#############################################################################
##  v      #                   The Coq Proof Assistant                     ##
## <O___,, #                INRIA - CNRS - LIX - LRI - PPS                 ##
##   \VV/  #                                                               ##
##    //   #  Makefile automagically generated by coq_makefile V8.4pl4     ##
#############################################################################

# WARNING
#
# This Makefile has been automagically generated
# Edit at your own risks !
#
# END OF WARNING

#
# This Makefile was generated by the command line :
# coq_makefile -R . rt ./util/ssromega.v ./util/lemmas.v ./util/Vbase.v ./util/divround.v ./implementation/basic/bertogna_edf_example.v ./implementation/basic/task.v ./implementation/basic/schedule.v ./implementation/basic/job.v ./implementation/basic/arrival_sequence.v ./implementation/jitter/bertogna_edf_example.v ./implementation/jitter/task.v ./implementation/jitter/schedule.v ./implementation/jitter/job.v ./implementation/jitter/arrival_sequence.v ./analysis/basic/bertogna_fp_theory.v ./analysis/basic/interference_bound_edf.v ./analysis/basic/interference_bound_fp.v ./analysis/basic/interference_bound.v ./analysis/basic/bertogna_edf_comp.v ./analysis/basic/bertogna_fp_comp.v ./analysis/basic/bertogna_edf_theory.v ./analysis/basic/workload_bound.v ./analysis/parallel/bertogna_fp_theory.v ./analysis/parallel/interference_bound_edf.v ./analysis/parallel/interference_bound_fp.v ./analysis/parallel/interference_bound.v ./analysis/parallel/bertogna_edf_comp.v ./analysis/parallel/bertogna_fp_comp.v ./analysis/parallel/bertogna_edf_theory.v ./analysis/parallel/workload_bound.v ./analysis/jitter/bertogna_fp_theory.v ./analysis/jitter/interference_bound_edf.v ./analysis/jitter/interference_bound_fp.v ./analysis/jitter/interference_bound.v ./analysis/jitter/bertogna_edf_comp.v ./analysis/jitter/bertogna_fp_comp.v ./analysis/jitter/bertogna_edf_theory.v ./analysis/jitter/workload_bound.v ./model/basic/time.v ./model/basic/schedulability.v ./model/basic/task.v ./model/basic/task_arrival.v ./model/basic/platform.v ./model/basic/schedule.v ./model/basic/priority.v ./model/basic/interference_edf.v ./model/basic/interference.v ./model/basic/workload.v ./model/basic/job.v ./model/basic/arrival_sequence.v ./model/basic/response_time.v ./model/basic/platform_fp.v ./model/jitter/time.v ./model/jitter/schedulability.v ./model/jitter/task.v ./model/jitter/task_arrival.v ./model/jitter/platform.v ./model/jitter/schedule.v ./model/jitter/priority.v ./model/jitter/interference_edf.v ./model/jitter/interference.v ./model/jitter/workload.v ./model/jitter/job.v ./model/jitter/arrival_sequence.v ./model/jitter/response_time.v ./model/jitter/platform_fp.v -o Makefile 
#

.DEFAULT_GOAL := all

# 
# This Makefile may take arguments passed as environment variables:
# COQBIN to specify the directory where Coq binaries resides;
# ZDEBUG/COQDEBUG to specify debug flags for ocamlc&ocamlopt/coqc;
# DSTROOT to specify a prefix to install path.

# Here is a hack to make $(eval $(shell works:
define donewline


endef
includecmdwithout@ = $(eval $(subst @,$(donewline),$(shell { $(1) | tr -d '\r' | tr '\n' '@'; })))
$(call includecmdwithout@,$(COQBIN)coqtop -config)

##########################
#                        #
# Libraries definitions. #
#                        #
##########################

COQLIBS?= -R . rt
COQDOCLIBS?=-R . rt

##########################
#                        #
# Variables definitions. #
#                        #
##########################


OPT?=
COQDEP?=$(COQBIN)coqdep -c
COQFLAGS?=-q $(OPT) $(COQLIBS) $(OTHERFLAGS) $(COQ_XML)
COQCHKFLAGS?=-silent -o
COQDOCFLAGS?=-interpolate -utf8
COQC?=$(COQBIN)coqc
GALLINA?=$(COQBIN)gallina
COQDOC?=$(COQBIN)coqdoc
COQCHK?=$(COQBIN)coqchk

##################
#                #
# Install Paths. #
#                #
##################

ifdef USERINSTALL
XDG_DATA_HOME?=$(HOME)/.local/share
COQLIBINSTALL=$(XDG_DATA_HOME)/coq
COQDOCINSTALL=$(XDG_DATA_HOME)/doc/coq
else
COQLIBINSTALL=${COQLIB}user-contrib
COQDOCINSTALL=${DOCDIR}user-contrib
endif

######################
#                    #
# Files dispatching. #
#                    #
######################

VFILES:=util/ssromega.v\
  util/lemmas.v\
  util/Vbase.v\
  util/divround.v\
  implementation/basic/bertogna_edf_example.v\
  implementation/basic/task.v\
  implementation/basic/schedule.v\
  implementation/basic/job.v\
  implementation/basic/arrival_sequence.v\
  implementation/jitter/bertogna_edf_example.v\
  implementation/jitter/task.v\
  implementation/jitter/schedule.v\
  implementation/jitter/job.v\
  implementation/jitter/arrival_sequence.v\
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
  model/basic/time.v\
  model/basic/schedulability.v\
  model/basic/task.v\
  model/basic/task_arrival.v\
  model/basic/platform.v\
  model/basic/schedule.v\
  model/basic/priority.v\
  model/basic/interference_edf.v\
  model/basic/interference.v\
  model/basic/workload.v\
  model/basic/job.v\
  model/basic/arrival_sequence.v\
  model/basic/response_time.v\
  model/basic/platform_fp.v\
  model/jitter/time.v\
  model/jitter/schedulability.v\
  model/jitter/task.v\
  model/jitter/task_arrival.v\
  model/jitter/platform.v\
  model/jitter/schedule.v\
  model/jitter/priority.v\
  model/jitter/interference_edf.v\
  model/jitter/interference.v\
  model/jitter/workload.v\
  model/jitter/job.v\
  model/jitter/arrival_sequence.v\
  model/jitter/response_time.v\
  model/jitter/platform_fp.v

-include $(addsuffix .d,$(VFILES))
.SECONDARY: $(addsuffix .d,$(VFILES))

VOFILES:=$(VFILES:.v=.vo)
GLOBFILES:=$(VFILES:.v=.glob)
VIFILES:=$(VFILES:.v=.vi)
GFILES:=$(VFILES:.v=.g)
HTMLFILES:=$(VFILES:.v=.html)
GHTMLFILES:=$(VFILES:.v=.g.html)
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

spec: $(VIFILES)

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
	$(COQCHK) $(COQCHKFLAGS) $(COQLIBS) $(notdir $(^:.vo=))

beautify: $(VFILES:=.beautified)
	for file in $^; do mv $${file%.beautified} $${file%beautified}old && mv $${file} $${file%.beautified}; done
	@echo 'Do not do "make clean" until you are sure that everything went well!'
	@echo 'If there were a problem, execute "for file in $$(find . -name \*.v.old -print); do mv $${file} $${file%.old}; done" in your shell/'

.PHONY: all opt byte archclean clean install userinstall depend html validate

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
	for i in $(VOFILES); do \
	 install -d `dirname $(DSTROOT)$(COQLIBINSTALL)/rt/$$i`; \
	 install -m 0644 $$i $(DSTROOT)$(COQLIBINSTALL)/rt/$$i; \
	done

install-doc:
	install -d $(DSTROOT)$(COQDOCINSTALL)/rt/html
	for i in html/*; do \
	 install -m 0644 $$i $(DSTROOT)$(COQDOCINSTALL)/rt/$$i;\
	done

clean:
	rm -f $(VOFILES) $(VIFILES) $(GFILES) $(VFILES:.v=.v.d) $(VFILES:=.beautified) $(VFILES:=.old)
	rm -f all.ps all-gal.ps all.pdf all-gal.pdf all.glob $(VFILES:.v=.glob) $(VFILES:.v=.tex) $(VFILES:.v=.g.tex) all-mli.tex
	- rm -rf html mlihtml

archclean:
	rm -f *.cmx *.o

printenv:
	@$(COQBIN)coqtop -config
	@echo CAMLC =	$(CAMLC)
	@echo CAMLOPTC =	$(CAMLOPTC)
	@echo PP =	$(PP)
	@echo COQFLAGS =	$(COQFLAGS)
	@echo COQLIBINSTALL =	$(COQLIBINSTALL)
	@echo COQDOCINSTALL =	$(COQDOCINSTALL)

###################
#                 #
# Implicit rules. #
#                 #
###################

%.vo %.glob: %.v
	$(COQC) $(COQDEBUG) $(COQFLAGS) $*

%.vi: %.v
	$(COQC) -i $(COQDEBUG) $(COQFLAGS) $*

%.g: %.v
	$(GALLINA) $<

%.tex: %.v
	$(COQDOC) $(COQDOCFLAGS) -latex $< -o $@

%.html: %.v %.glob
	$(COQDOC) $(COQDOCFLAGS) -html $< -o $@

%.g.tex: %.v
	$(COQDOC) $(COQDOCFLAGS) -latex -g $< -o $@

%.g.html: %.v %.glob
	$(COQDOC)$(COQDOCFLAGS)  -html -g $< -o $@

%.v.d: %.v
	$(COQDEP) -slash $(COQLIBS) "$<" > "$@" || ( RV=$$?; rm -f "$@"; exit $${RV} )

%.v.beautified:
	$(COQC) $(COQDEBUG) $(COQFLAGS) -beautify $*

# WARNING
#
# This Makefile has been automagically generated
# Edit at your own risks !
#
# END OF WARNING

