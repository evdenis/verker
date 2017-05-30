CC               := gcc
CFLAGS           := -Wall -Werror
CLANG            := clang
CLANGFLAGS       := -g -fsanitize=address -fsanitize-coverage=trace-pc-guard
GEN_CFLAGS       := -w
EXT_CFLAGS       := -DOUT_OF_TASK
BINDIR           := bin
FUZZDIR          := fzz
GENDIR           := gen
EACSLDIR         := $(GENDIR)/eacsl
RTEDIR           := $(GENDIR)/rte
VALDIR           := $(GENDIR)/val
GENBINDIR        := $(BINDIR)/gen
EACSLBINDIR      := $(GENBINDIR)/eacsl
FRAMAC           := frama-c
FRAMAC_DFLAGS    := -jessie
FRAMAC_REPLAY    := -jessie-target why3autoreplay
FRAMAC_EFLAGS    := -e-acsl -pp-annot -cpp-extra-args " -C -E -x c $(EXT_CFLAGS) "
FRAMAC_EGEN      := -then-last -print -ocode
FRAMAC_RTEFLAGS  := -rte -rte-all -rte-precond -pp-annot -cpp-extra-args " -C -E -x c $(EXT_CFLAGS) "
FRAMAC_VALFLAGS  := -val -pp-annot -cpp-extra-args " -C -E -x c $(EXT_CFLAGS) "
FRAMAC_VALGEN    := -print -ocode
FRAMAC_ESHARE    := $(shell frama-c -print-share-path)/e-acsl
FRAMAC_EMSHARE   := $(shell frama-c -print-share-path)/e-acsl/memory_model
FRAMAC_EACSL_LIB := $(FRAMAC_ESHARE)/e_acsl.c $(FRAMAC_EMSHARE)/e_acsl_bittree.c $(FRAMAC_EMSHARE)/e_acsl_mmodel.c


CFLAGS += $(EXT_CFLAGS)
CLANGFLAGS += $(EXT_CFLAGS)

SRCFILES      := $(sort $(shell find . -maxdepth 1 -type f -name '*.c'))
BINFILES      := $(patsubst ./%.c, $(BINDIR)/%,     $(SRCFILES))
FUZZFILES     := $(patsubst ./%.c, $(FUZZDIR)/%,    $(SRCFILES))
EACSLFILES    := $(patsubst ./%.c, $(EACSLDIR)/%.c, $(SRCFILES))
RTEFILES      := $(patsubst ./%.c, $(RTEDIR)/%.c,   $(SRCFILES))
VALFILES      := $(patsubst ./%.c, $(VALDIR)/%.c,   $(SRCFILES))
EACSLBINFILES := $(patsubst $(EACSLDIR)/%.c, $(EACSLBINDIR)/%, $(EACSLFILES))

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

$(FUZZDIR)/%: %.c
	$(CLANG) $(CLANGFLAGS) libFuzzer.a -lstdc++ $< -o $@

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

replay: ## Replay proofs simultaiously. You can also type replay-<target>.
	@$(FRAMAC) $(FRAMAC_DFLAGS) $(FRAMAC_REPLAY) $(SRCFILES)

replay-separatedly: ## Replay proofs consequently.
	@for i in $(SRCFILES); do echo $$i; $(FRAMAC) $(FRAMAC_DFLAGS) $(FRAMAC_REPLAY) $$i; done

replay-%:
	@$(FRAMAC) $(FRAMAC_DFLAGS) $(FRAMAC_REPLAY) $*.c

clean: ## Remove all binary and generated files.
	-rm -fr $(GENBINDIR) $(RTEDIR) $(VALDIR) $(EACSLDIR) $(BINDIR) $(GENDIR)

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
