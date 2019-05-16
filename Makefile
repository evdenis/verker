export TIMEOUT   ?= 10
export PROCESSES ?= 4

CC               := gcc
CFLAGS           := -Wall -Werror
CLANG            := clang
CLANGFLAGS       := -g -O1
GEN_CFLAGS       := -w
FUZZ_CFLAGS      := -fsanitize=fuzzer,address -DFUZZ_MAIN
EXT_CFLAGS       := -DDUMMY_MAIN
SPEC_CFLAGS      := -DSPEC
BINDIR           := bin
FUZZDIR          := fzz
GENDIR           := gen
EACSLDIR         := $(GENDIR)/eacsl
RTEDIR           := $(GENDIR)/rte
VALDIR           := $(GENDIR)/val
GENBINDIR        := $(BINDIR)/gen
EACSLBINDIR      := $(GENBINDIR)/eacsl
EACSLFUZZDIR     := $(FUZZDIR)/eacsl
OPAM_VERSION     := $(shell opam --version | grep -q '^2.' && echo 2 || echo 1)
ifeq ($(OPAM_VERSION), 2)
OPAM_EVAL        := eval $$(opam env)
else
OPAM_EVAL        := eval $$(opam config env)
endif
#FRAMAC           := $(OPAM_EVAL); frama-c-gui -c11 -pp-annot -cpp-extra-args " -CC -E -x c $(SPEC_CFLAGS) " -machdep gcc_x86_64
FRAMAC           := $(OPAM_EVAL); frama-c -c11 -pp-annot -cpp-extra-args " -CC -E -x c $(SPEC_CFLAGS) " -machdep gcc_x86_64
FRAMAC_NOHUP     := $(OPAM_EVAL); nohup frama-c -c11 -pp-annot -cpp-extra-args " -CC -E -x c $(SPEC_CFLAGS) " -machdep gcc_x86_64
#FRAMAC_DFLAGS    :=
#FRAMAC_DFLAGS    := -wp
FRAMAC_DFLAGS    := -av
FRAMAC_UFLAGS    := -av -av-target update
FRAMAC_REPLAY    := -av-target why3autoreplay
SPROVE_ARGS      = ''
FRAMAC_SPROVE    = -av-target why3sprove -av-why3-opt " --strategy verker --theory-filter axiom $(SPROVE_ARGS)"
FRAMAC_EFLAGS    := -e-acsl -main LLVMFuzzerTestOneInput -pp-annot -cpp-extra-args " -CC -E -x c -DFUZZ_MAIN "
FRAMAC_EGEN      := -then-last -print -ocode
FRAMAC_RTEFLAGS  := -rte -main LLVMFuzzerTestOneInput -pp-annot -cpp-extra-args " -CC -E -x c -DFUZZ_MAIN "
FRAMAC_VALFLAGS  := -val -main LLVMFuzzerTestOneInput -pp-annot -cpp-extra-args " -CC -E -x c -DFUZZ_MAIN "
FRAMAC_RTEGEN    := -print -ocode
FRAMAC_VALGEN    := $(FRAMAC_RTEGEN)
FRAMAC_ESHARE    := $(shell $(FRAMAC) -print-share-path)/e-acsl
FRAMAC_EMSHARE   := $(shell $(FRAMAC) -print-share-path)/e-acsl/memory_model
FRAMAC_LIBPATH   := $(shell $(FRAMAC) -print-lib-path)
FRAMAC_EACSL_LIB := -DE_ACSL_SEGMENT_MMODEL -DE_ACSL_IDENTIFY -std=c99 -m64 -I$(FRAMAC_ESHARE) $(FRAMAC_ESHARE)/e_acsl_mmodel.c -lm -lpthread $(FRAMAC_LIBPATH)/../libeacsl-gmp.a $(FRAMAC_LIBPATH)/../libeacsl-jemalloc.a

SRCFILES             := $(sort $(shell find ./src -maxdepth 1 -type f \! -name '*.pp.c' -name '*.c'))
FZZAVAILFILES        := $(sort $(shell grep -nre '|[[:space:]]\+[[:digit:]]\+[[:space:]]\+|' ./README.md | cut -d '|' -f 3,6 | grep yes | cut -d '|' -f 1 | tr -d ' \\' | sed -e 's/$$/.c/' -e 's!^!./src/!'))
BINAVAILFILES        := $(sort $(shell grep -nre '|[[:space:]]\+[[:digit:]]\+[[:space:]]\+|' ./README.md | cut -d '|' -f 3 | tr -d ' \\' | sed -e 's/$$/.c/' -e 's!^!./src/!'))
PROVEDFILES          := $(sort $(shell grep -nre '|[[:space:]]\+[[:digit:]]\+[[:space:]]\+|' ./README.md | cut -d '|' -f 3,4 | grep proved | cut -d '|' -f 1 | tr -d ' \\' | sed -e 's/$$/.c/' -e 's!^!./src/!'))
BINFILES             := $(patsubst ./src/%.c, $(BINDIR)/%,     $(BINAVAILFILES))
FUZZFILES            := $(patsubst ./src/%.c, $(FUZZDIR)/%,    $(FZZAVAILFILES))
EACSLFILES           := $(patsubst ./src/%.c, $(EACSLDIR)/%.c, $(BINAVAILFILES))
EACSLPROVEDFILES     := $(patsubst ./src/%.c, $(EACSLDIR)/%.c, $(PROVEDFILES))
RTEFILES             := $(patsubst ./src/%.c, $(RTEDIR)/%.c,   $(SRCFILES))
VALFILES             := $(patsubst ./src/%.c, $(VALDIR)/%.c,   $(SRCFILES))
EACSLBINFILES        := $(patsubst $(EACSLDIR)/%.c, $(EACSLBINDIR)/%, $(EACSLFILES))
EACSLBINPROVEDFILES  := $(patsubst $(EACSLDIR)/%.c, $(EACSLBINDIR)/%, $(EACSLPROVEDFILES))
EACSLFUZZFILES       := $(patsubst $(EACSLDIR)/%.c, $(EACSLFUZZDIR)/%, $(EACSLFILES))
EACSLFUZZPROVEDFILES := $(patsubst $(EACSLDIR)/%.c, $(EACSLFUZZDIR)/%, $(EACSLPROVEDFILES))

all: build ## Default target

build: $(BINDIR) $(BINFILES) ## Build each program.

fuzz: $(FUZZDIR) $(FUZZFILES) ## Fuzz each program.

eacsl: $(GENDIR) $(EACSLDIR) $(EACSLFILES) ## Generate E-ACSL programs.

eacsl-proved: $(GENDIR) $(EACSLDIR) $(EACSLPROVEDFILES) ## Generate E-ACSL for proved programs.

eacsl-build: eacsl $(GENBINDIR) $(EACSLBINDIR) $(EACSLBINFILES) ## Build generated E-ACSL programs.

eacsl-proved-build: eacsl-proved $(GENBINDIR) $(EACSLBINDIR) $(EACSLBINPROVEDFILES) ## Build E-ACSL proved programs.

eacsl-fuzz: eacsl $(EACSLDIR) $(FUZZDIR) $(EACSLFUZZDIR) $(EACSLFUZZFILES) ## Build generated E-ACSL programs with libfuzzer.

eacsl-proved-fuzz: eacsl-proved $(EACSLDIR) $(FUZZDIR) $(EACSLFUZZDIR) $(EACSLFUZZPROVEDFILES) ## Build E-ACSL proved programs with libfuzzer.

rte: $(GENDIR) $(RTEDIR) $(RTEFILES) ## Generate RTE specifications.

val: $(GENDIR) $(VALDIR) $(VALFILES) ## Run value analysis.

$(BINDIR):
	@-mkdir -p $(BINDIR)

$(FUZZDIR):
	@-mkdir -p $(FUZZDIR)

$(GENDIR):
	@-mkdir -p $(GENDIR)

$(EACSLDIR):
	@-mkdir -p $(EACSLDIR)

$(RTEDIR):
	@-mkdir -p $(RTEDIR)

$(VALDIR):
	@-mkdir -p $(VALDIR)

$(GENBINDIR):
	@-mkdir -p $(GENBINDIR)

$(EACSLBINDIR):
	@-mkdir -p $(EACSLBINDIR)

$(EACSLFUZZDIR):
	@-mkdir -p $(EACSLFUZZDIR)

$(BINDIR)/skip_spaces: $(BINDIR)/ctype.o src/skip_spaces.c
	$(CC) $(CFLAGS) $(EXT_CFLAGS) $^ -o $@

$(BINDIR)/strlcpy: $(BINDIR)/memcpy.o src/strlcpy.c
	$(CC) $(CFLAGS) $(EXT_CFLAGS) $^ -o $@

$(BINDIR)/strim: $(BINDIR)/skip_spaces.o $(BINDIR)/ctype.o src/strim.c
	$(CC) $(CFLAGS) $(EXT_CFLAGS) $^ -o $@

$(BINDIR)/_parse_integer_fixup_radix: $(BINDIR)/ctype.o src/_parse_integer_fixup_radix.c
	$(CC) $(CFLAGS) $(EXT_CFLAGS) $^ -o $@

$(BINDIR)/strcasecmp: $(BINDIR)/ctype.o src/strcasecmp.c
	$(CC) $(CFLAGS) $(EXT_CFLAGS) $^ -o $@

$(BINDIR)/strncasecmp: $(BINDIR)/ctype.o src/strncasecmp.c
	$(CC) $(CFLAGS) $(EXT_CFLAGS) $^ -o $@

$(BINDIR)/strnstr: $(BINDIR)/memcmp.o $(BINDIR)/strlen.o src/strnstr.c
	$(CC) $(CFLAGS) $(EXT_CFLAGS) $^ -o $@

$(BINDIR)/%.o: src/%.c src/%.h
	$(CC) $(CFLAGS) -c $< -o $@

$(BINDIR)/%: src/%.c src/%.h
	$(CC) $(CFLAGS) $(EXT_CFLAGS) $< -o $@

$(FUZZDIR)/%.o: src/%.c src/%.h
	$(CLANG) $(CLANGFLAGS) -c $< -o $@

$(FUZZDIR)/skip_spaces: $(FUZZDIR)/ctype.o src/skip_spaces.c
	$(CLANG) $(CLANGFLAGS) $(FUZZ_CFLAGS) $^ -o $@

$(FUZZDIR)/_parse_integer_fixup_radix: $(FUZZDIR)/ctype.o src/_parse_integer_fixup_radix.c
	$(CLANG) $(CLANGFLAGS) $(FUZZ_CFLAGS) $^ -o $@

$(FUZZDIR)/strcasecmp: $(FUZZDIR)/ctype.o src/strcasecmp.c
	$(CLANG) $(CLANGFLAGS) $(FUZZ_CFLAGS) $^ -o $@

$(FUZZDIR)/strncasecmp: $(FUZZDIR)/ctype.o src/strncasecmp.c
	$(CLANG) $(CLANGFLAGS) $(FUZZ_CFLAGS) $^ -o $@

$(FUZZDIR)/strstr: $(FUZZDIR)/memcmp.o src/strstr.c
	$(CLANG) $(CLANGFLAGS) $(FUZZ_CFLAGS) $^ -o $@

$(FUZZDIR)/strnstr: $(FUZZDIR)/memcmp.o $(FUZZDIR)/strlen.o src/strnstr.c
	$(CLANG) $(CLANGFLAGS) $(FUZZ_CFLAGS) $^ -o $@

$(FUZZDIR)/%: src/%.c src/%.h
	$(CLANG) $(CLANGFLAGS) $(FUZZ_CFLAGS) $< -o $@

$(EACSLDIR)/%.c: src/%.c
	$(FRAMAC) $(FRAMAC_EFLAGS) $< $(FRAMAC_EGEN) $@

$(RTEDIR)/%.c: src/%.c
	$(FRAMAC) $(FRAMAC_RTEFLAGS) $< $(FRAMAC_RTEGEN) $@

$(VALDIR)/%.c: src/%.c
	$(FRAMAC) $(FRAMAC_VALFLAGS) $< $(FRAMAC_VALGEN) $@

$(GENBINDIR)/%: $(GENDIR)/%.c
	$(CC) $(GEN_CFLAGS) $(FRAMAC_EACSL_LIB) $< -o $@

$(EACSLFUZZDIR)/%: $(EACSLDIR)/%.c
	$(CLANG) $(CLANGFLAGS) $(GEN_CFLAGS) $(FUZZ_CFLAGS) $(FRAMAC_EACSL_LIB) $< -o $@

fuzz-%: $(FUZZDIR) $(FUZZDIR)/%
	$(FUZZDIR)/$*

run: build ## Run each program. You can also type run-<target>.
	@for i in $(BINFILES); do echo $$i; ./$$i; done

run-%: $(BINDIR) $(BINDIR)/%
	$(BINDIR)/$*

eacsl-run: eacsl-build ## Run each E-ACSL program. You can also type eacsl-run-<target>.
	@for i in $(GENBINFILES); do echo $$i; ./$$i; done

eacsl-run-%: $(GENDIR) $(GENBINDIR) $(GENBINDIR)/%
	$(GENBINDIR)/$*

eacsl-fuzz-%: $(FUZZDIR) $(GENDIR) $(EACSLDIR) $(EACSLFUZZDIR) $(EACSLFUZZDIR)/%
	$(EACSLFUZZDIR)/$*

verify: ## Run Frama-C on all files simultaneously. You can also type verify-<target>.
	@$(FRAMAC) $(FRAMAC_DFLAGS) $(SRCFILES) -av-out sessions/all.av

verify-separatedly: ## Run Frama-C on each file consequently.
	@for i in $(SRCFILES); do i=$$(basename $$i); echo $$i; $(FRAMAC) $(FRAMAC_DFLAGS) src/$$i -av-out sessions/$$i.av; done

verify-proved: ## Run Frama-C on each file consequently. Only completely proved functions.
	@$(FRAMAC) $(FRAMAC_DFLAGS) $(PROVEDFILES) -av-out sessions/proved.av

verify-proved-separatedly: ## Run Frama-C on each file consequently. Only completely proved functions.
	@for i in $(PROVEDFILES); do i=$$(basename $$i); echo $$i; $(FRAMAC) $(FRAMAC_DFLAGS) src/$$i -av-out sessions/$$i.av; done

verify-%:
	@$(FRAMAC) $(FRAMAC_DFLAGS) src/$*.c -av-out sessions/$*.c.av

update-%:
	@$(FRAMAC) $(FRAMAC_UFLAGS) src/$*.c -av-out sessions/$*.c.av

replay: ## Replay proofs simultaiously. You can also type replay-<target>.
	@$(FRAMAC) $(FRAMAC_DFLAGS) $(FRAMAC_REPLAY) $(SRCFILES) -av-out sessions/all.av

replay-separatedly: ## Replay proofs consequently.
	@for i in $(SRCFILES); do i=$$(basename $$i); echo $$i; $(FRAMAC) $(FRAMAC_DFLAGS) $(FRAMAC_REPLAY) src/$$i -av-out sessions/$$i.av; done

replay-proved: ## Replay proofs for completely proved functions.
	@$(FRAMAC) $(FRAMAC_DFLAGS) $(FRAMAC_REPLAY) $(PROVEDFILES) -av-out sessions/proved.av

replay-proved-separatedly: ## Replay proved functions consequently.
	@FAIL=0; for i in $(PROVEDFILES); do i=$$(basename $$i); $(FRAMAC) $(FRAMAC_DFLAGS) $(FRAMAC_REPLAY) src/$$i -av-out sessions/$$i.av > /dev/null 2>&1 && echo "OK:   $$i" || { echo "FAIL: $$i"; FAIL=1; }; done; if [ $$FAIL -eq 1 ]; then exit 1; fi

replay-%:
	@$(FRAMAC) $(FRAMAC_DFLAGS) $(FRAMAC_REPLAY) src/$*.c -av-out sessions/$*.av.c

AV_WHY3_CONF := astraver.why3.conf

define av_why3conf
[main]
running_provers_max = $(PROCESSES)

[strategy]
code = "
start:
  c Alt-Ergo,, 2 2000
  c CVC4,,noBV 2 2000
  c CVC4,, 2 2000
  c Eprover,, 2 2000
  t split_goal_wp start
  t introduce_premises next1
next1:
  t inline_all next2
next2:
  t eliminate_if next3
next3:
  t remove_triggers start
  c Alt-Ergo,, $(TIMEOUT) 8000
  c CVC4,,noBV $(TIMEOUT) 8000
  c CVC4,, $(TIMEOUT) 8000
  c Eprover,, $(TIMEOUT) 8000"
desc = "Strategy for Verker examples"
name = "verker"
endef
export av_why3conf

$(AV_WHY3_CONF):
	@if [ -f $@ ]; then                          \
		tfile=$(shell mktemp);               \
		echo "$$av_why3conf" > $$tfile;      \
		diff -q $@ $$tfile > /dev/null || mv $$tfile $@; \
	else echo "$$av_why3conf" > $@; fi

SPROVE_ARGS = --session $(PWD)/sessions/all.av
sprove: $(AV_WHY3_CONF) ## Replay proofs simultaiously. You can also type sprove-<target>.
	@$(FRAMAC) $(FRAMAC_DFLAGS) $(FRAMAC_SPROVE) $(SRCFILES) -av-out sessions/all.av

sprove-separatedly: $(AV_WHY3_CONF) ## Replay proofs consequently.
	@for i in $(SRCFILES); do i=$$(basename $$i .c); echo $$i; $(FRAMAC) $(FRAMAC_DFLAGS) -av-target why3sprove -av-why3-opt " --strategy verker --theory-filter axiom --session $(PWD)/sessions/$$i.c.av/$${i}_c" src/$$i.c -av-out sessions/$$i.c.av; done

SPROVE_ARGS = --session $(PWD)/sessions/proved.av
sprove-proved: $(AV_WHY3_CONF) ## Run sprove strategy on proved functions.
	@$(FRAMAC) $(FRAMAC_DFLAGS) $(FRAMAC_SPROVE) $(PROVEDFILES) -av-out sessions/proved.av

sprove-proved-separatedly: $(AV_WHY3_CONF) ## Run sprove strategy on proved functions separatedly.
	@for i in $(PROVEDFILES); do i=$$(basename $$i .c); echo $$i; $(FRAMAC) $(FRAMAC_DFLAGS) -av-target why3sprove -av-why3-opt " --strategy verker --theory-filter axiom --session $(PWD)/sessions/$$i.c.av/$${i}_c" src/$$i.c -av-out sessions/$$i.c.av; done

SPROVE_ARGS = --session $(PWD)/sessions/$*.c.av/$*_c
sprove-%: $(AV_WHY3_CONF)
	@$(FRAMAC) $(FRAMAC_DFLAGS) $(FRAMAC_SPROVE) src/$*.c -av-out sessions/$*.c.av

clean: ## Remove all binary and generated files.
	-rm -fr $(AV_WHY3_CONF) $(GENBINDIR) $(RTEDIR) $(VALDIR) $(EACSLDIR) $(BINDIR) $(GENDIR) $(FUZZDIR) src/*.av src/*.o src/*.pp.c src/*.pp.h src/*.jessie

.PHONY: all build fuzz eacsl eacsl-build rte val run eacsl-run verify verify-separatedly verify-proved verify-proved-separatedly sprove-proved replay replay-separatedly replay-proved replay-proved-separatedly sprove sprove-separatedly clean $(AV_WHY3_CONF)

#COLORS
GREEN  := $(shell tput -Txterm setaf 2)
WHITE  := $(shell tput -Txterm setaf 7)
YELLOW := $(shell tput -Txterm setaf 3)
RESET  := $(shell tput -Txterm sgr0)

# Add the following 'help' target to your Makefile
# And add help text after each target name starting with '\#\#'
# A category can be added with @category
HELP_FUN = \
    %help; \
    while(<>) { push @{$$help{$$2 // 'options'}}, [$$1, $$3] if /^([a-zA-Z\-]+)\s*:.*\#\#(?:@([a-zA-Z\-]+))?\s(.*)$$/ }; \
    print "usage: make [target]\n\n"; \
    for (sort keys %help) { \
    print "${WHITE}$$_:${RESET}\n"; \
    for (@{$$help{$$_}}) { \
    $$sep = " " x (32 - length $$_->[0]); \
    print "  ${YELLOW}$$_->[0]${RESET}$$sep${GREEN}$$_->[1]${RESET}\n"; \
    }; \
    print "\n"; }

help: ## Show this help.
	@perl -e '$(HELP_FUN)' $(MAKEFILE_LIST)

.PHONY: help
