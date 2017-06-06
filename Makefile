CC               := gcc
CFLAGS           := -Wall -Werror
CLANG            := clang
CLANGFLAGS       := -g -fsanitize=address -fsanitize-coverage=trace-pc-guard
GEN_CFLAGS       := -w
FUZZ_CFLAGS      := -DFUZZ_MAIN
SPEC_CFLAGS      := -DSPEC
BINDIR           := bin
FUZZDIR          := fzz
GENDIR           := gen
EACSLDIR         := $(GENDIR)/eacsl
RTEDIR           := $(GENDIR)/rte
VALDIR           := $(GENDIR)/val
GENBINDIR        := $(BINDIR)/gen
EACSLBINDIR      := $(GENBINDIR)/eacsl
OPAM_EVAL        := eval $$(opam config env)
FRAMAC           := $(OPAM_EVAL); frama-c -cpp-extra-args " -C -E -x c $(SPEC_CFLAGS) "
FRAMAC_NOHUP     := $(OPAM_EVAL); nohup frama-c -cpp-extra-args " -C -E -x c $(SPEC_CFLAGS) "
FRAMAC_DFLAGS    := -jessie
FRAMAC_UFLAGS    := -jessie -jessie-target update
FRAMAC_REPLAY    := -jessie-target why3autoreplay
FRAMAC_EFLAGS    := -e-acsl -pp-annot -cpp-extra-args " -C -E -x c $(FUZZ_CFLAGS) "
FRAMAC_EGEN      := -then-last -print -ocode
FRAMAC_RTEFLAGS  := -rte -rte-all -rte-precond -pp-annot -cpp-extra-args " -C -E -x c $(FUZZ_CFLAGS) "
FRAMAC_VALFLAGS  := -val -pp-annot -cpp-extra-args " -C -E -x c $(FUZZ_CFLAGS) "
FRAMAC_VALGEN    := -print -ocode
FRAMAC_ESHARE    := $(shell $(FRAMAC) -print-share-path)/e-acsl
FRAMAC_EMSHARE   := $(shell $(FRAMAC) -print-share-path)/e-acsl/memory_model
FRAMAC_EACSL_LIB := $(FRAMAC_ESHARE)/e_acsl.c $(FRAMAC_EMSHARE)/e_acsl_bittree.c $(FRAMAC_EMSHARE)/e_acsl_mmodel.c

SRCFILES       := $(sort $(shell find . -maxdepth 1 -type f -name '*.c'))
FZZAVAILFILES  := $(sort $(shell grep -nrPe '\|\h+\d+\h+\|' ./README.md | cut -d '|' -f 3,7 | grep yes | cut -d '|' -f 1 | tr -d ' \\' | sed -e 's/$$/.c/' -e 's!^!./!'))
BINFILES       := $(patsubst ./%.c, $(BINDIR)/%,     $(SRCFILES))
FUZZFILES      := $(patsubst ./%.c, $(FUZZDIR)/%,    $(FZZAVAILFILES))
EACSLFILES     := $(patsubst ./%.c, $(EACSLDIR)/%.c, $(SRCFILES))
RTEFILES       := $(patsubst ./%.c, $(RTEDIR)/%.c,   $(SRCFILES))
VALFILES       := $(patsubst ./%.c, $(VALDIR)/%.c,   $(SRCFILES))
EACSLBINFILES  := $(patsubst $(EACSLDIR)/%.c, $(EACSLBINDIR)/%, $(EACSLFILES))

all: fuzz ## Default target

build: $(BINDIR) $(BINFILES) ## Build each program.

fuzz: $(FUZZDIR) $(FUZZFILES) ## Fuzz each program.

eacsl: $(GENDIR) $(EACSLDIR) $(EACSLFILES) ## Generate E-ACSL programs.

eacsl-build: eacsl $(GENBINDIR) $(EACSLBINDIR) $(EACSLBINFILES) ## Build generated E-ACSL programs.

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

$(BINDIR)/%: %.c
	$(CC) $(CFLAGS) $< -o $@

$(FUZZDIR)/%.o: %.c %.h
	$(CLANG) $(CLANGFLAGS) -c $< -o $@

$(FUZZDIR)/skip_spaces: $(FUZZDIR)/ctype.o skip_spaces.c
	$(CLANG) $(CLANGFLAGS) $(FUZZ_CFLAGS) libFuzzer.a -lstdc++ $^ -o $@

$(FUZZDIR)/_parse_integer_fixup_radix: $(FUZZDIR)/ctype.o _parse_integer_fixup_radix.c
	$(CLANG) $(CLANGFLAGS) $(FUZZ_CFLAGS) libFuzzer.a -lstdc++ $^ -o $@

$(FUZZDIR)/strcasecmp: $(FUZZDIR)/ctype.o strcasecmp.c
	$(CLANG) $(CLANGFLAGS) $(FUZZ_CFLAGS) libFuzzer.a -lstdc++ $^ -o $@

$(FUZZDIR)/strncasecmp: $(FUZZDIR)/ctype.o strncasecmp.c
	$(CLANG) $(CLANGFLAGS) $(FUZZ_CFLAGS) libFuzzer.a -lstdc++ $^ -o $@

$(FUZZDIR)/strstr: $(FUZZDIR)/memcmp.o strstr.c
	$(CLANG) $(CLANGFLAGS) $(FUZZ_CFLAGS) libFuzzer.a -lstdc++ $^ -o $@

$(FUZZDIR)/strnstr: $(FUZZDIR)/memcmp.o $(FUZZDIR)/strlen.o strnstr.c
	$(CLANG) $(CLANGFLAGS) $(FUZZ_CFLAGS) libFuzzer.a -lstdc++ $^ -o $@

$(FUZZDIR)/%: %.c %.h
	$(CLANG) $(CLANGFLAGS) $(FUZZ_CFLAGS) libFuzzer.a -lstdc++ $< -o $@

$(EACSLDIR)/%.c: %.c
	$(FRAMAC) $(FRAMAC_EFLAGS) $< $(FRAMAC_EGEN) $@

$(RTEDIR)/%.c: %.c
	$(FRAMAC) $(FRAMAC_RTEFLAGS) $< $(FRAMAC_RTEGEN) $@

$(VALDIR)/%.c: %.c
	$(FRAMAC) $(FRAMAC_VALFLAGS) $< $(FRAMAC_VALGEN) $@

$(GENBINDIR)/%: $(GENDIR)/%.c
	$(CC) $(GEN_CFLAGS) $(FRAMAC_EACSL_LIB) $< -o $@

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

verify: ## Run Frama-C on all files simultaneously. You can also type verify-<target>.
	@$(FRAMAC) $(FRAMAC_DFLAGS) $(SRCFILES)

verify-separatedly: ## Run Frama-C on each file consequently.
	@for i in $(SRCFILES); do echo $$i; $(FRAMAC) $(FRAMAC_DFLAGS) $$i; done

verify-%:
	@$(FRAMAC) $(FRAMAC_DFLAGS) $*.c

update-%:
	@$(FRAMAC) $(FRAMAC_UFLAGS) $*.c

replay: ## Replay proofs simultaiously. You can also type replay-<target>.
	@$(FRAMAC) $(FRAMAC_DFLAGS) $(FRAMAC_REPLAY) $(SRCFILES)

replay-separatedly: ## Replay proofs consequently.
	@for i in $(SRCFILES); do echo $$i; $(FRAMAC) $(FRAMAC_DFLAGS) $(FRAMAC_REPLAY) $$i; done

replay-%:
	@$(FRAMAC) $(FRAMAC_DFLAGS) $(FRAMAC_REPLAY) $*.c

clean: ## Remove all binary and generated files.
	-rm -fr $(GENBINDIR) $(RTEDIR) $(VALDIR) $(EACSLDIR) $(BINDIR) $(GENDIR) $(FUZZDIR)

.PHONY: all build fuzz eacsl eacsl-build rte val run eacsl-run verify verify-separatedly replay replay-separatedly clean

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
