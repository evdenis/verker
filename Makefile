CC               := gcc
CFLAGS           := -Wall -Werror
CLANG            := clang
CLANGFLAGS       := -g -fsanitize=address -fsanitize-coverage=trace-pc-guard
GEN_CFLAGS       := -w
FUZZ_CFLAGS      := -DFUZZ_MAIN
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
FRAMAC           := $(OPAM_EVAL); frama-c -cpp-extra-args " -C -E -x c $(SPEC_CFLAGS) " -machdep gcc_x86_64
FRAMAC_NOHUP     := $(OPAM_EVAL); nohup frama-c -cpp-extra-args " -C -E -x c $(SPEC_CFLAGS) " -machdep gcc_x86_64
FRAMAC_DFLAGS    := -jessie
FRAMAC_UFLAGS    := -jessie -jessie-target update
FRAMAC_REPLAY    := -jessie-target why3autoreplay
FRAMAC_SPROVE    := -jessie-target why3sprove -jessie-why3-opt " --strategy proof_juicer --theory-filter axiom"
FRAMAC_EFLAGS    := -e-acsl -main LLVMFuzzerTestOneInput -pp-annot -cpp-extra-args " -C -E -x c $(FUZZ_CFLAGS) "
FRAMAC_EGEN      := -then-last -print -ocode
FRAMAC_RTEFLAGS  := -rte -main LLVMFuzzerTestOneInput -rte-all -rte-precond -pp-annot -cpp-extra-args " -C -E -x c $(FUZZ_CFLAGS) "
FRAMAC_VALFLAGS  := -val -main LLVMFuzzerTestOneInput -pp-annot -cpp-extra-args " -C -E -x c $(FUZZ_CFLAGS) "
FRAMAC_VALGEN    := -print -ocode
FRAMAC_ESHARE    := $(shell $(FRAMAC) -print-share-path)/e-acsl
FRAMAC_EMSHARE   := $(shell $(FRAMAC) -print-share-path)/e-acsl/memory_model
FRAMAC_LIBPATH   := $(shell $(FRAMAC) -print-lib-path)
FRAMAC_EACSL_LIB := -DE_ACSL_SEGMENT_MMODEL -DE_ACSL_IDENTIFY -std=c99 -m64 -I$(FRAMAC_ESHARE) $(FRAMAC_ESHARE)/e_acsl_mmodel.c -lm -lpthread $(FRAMAC_LIBPATH)/../libeacsl-gmp.a $(FRAMAC_LIBPATH)/../libeacsl-jemalloc.a

SRCFILES             := $(sort $(shell find . -maxdepth 1 -type f \! -name '*.pp.c' -name '*.c'))
FZZAVAILFILES        := $(sort $(shell grep -nre '|[[:space:]]\+[[:digit:]]\+[[:space:]]\+|' ./README.md | cut -d '|' -f 3,6 | grep yes | cut -d '|' -f 1 | tr -d ' \\' | sed -e 's/$$/.c/' -e 's!^!./!'))
BINAVAILFILES        := $(sort $(shell grep -nre '|[[:space:]]\+[[:digit:]]\+[[:space:]]\+|' ./README.md | cut -d '|' -f 3 | tr -d ' \\' | sed -e 's/$$/.c/' -e 's!^!./!'))
PROVEDFILES          := $(sort $(shell grep -nre '|[[:space:]]\+[[:digit:]]\+[[:space:]]\+|' ./README.md | cut -d '|' -f 3,4 | grep proved | cut -d '|' -f 1 | tr -d ' \\' | sed -e 's/$$/.c/' -e 's!^!./!'))
BINFILES             := $(patsubst ./%.c, $(BINDIR)/%,     $(BINAVAILFILES))
FUZZFILES            := $(patsubst ./%.c, $(FUZZDIR)/%,    $(FZZAVAILFILES))
EACSLFILES           := $(patsubst ./%.c, $(EACSLDIR)/%.c, $(BINAVAILFILES))
EACSLPROVEDFILES     := $(patsubst ./%.c, $(EACSLDIR)/%.c, $(PROVEDFILES))
RTEFILES             := $(patsubst ./%.c, $(RTEDIR)/%.c,   $(SRCFILES))
VALFILES             := $(patsubst ./%.c, $(VALDIR)/%.c,   $(SRCFILES))
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

$(BINDIR)/skip_spaces: $(BINDIR)/ctype.o skip_spaces.c
	$(CC) $(CFLAGS) $(EXT_CFLAGS) $^ -o $@

$(BINDIR)/strlcpy: $(BINDIR)/memcpy.o strlcpy.c
	$(CC) $(CFLAGS) $(EXT_CFLAGS) $^ -o $@

$(BINDIR)/strim: $(BINDIR)/skip_spaces.o $(BINDIR)/ctype.o strim.c
	$(CC) $(CFLAGS) $(EXT_CFLAGS) $^ -o $@

$(BINDIR)/_parse_integer_fixup_radix: $(BINDIR)/ctype.o _parse_integer_fixup_radix.c
	$(CC) $(CFLAGS) $(EXT_CFLAGS) $^ -o $@

$(BINDIR)/strcasecmp: $(BINDIR)/ctype.o strcasecmp.c
	$(CC) $(CFLAGS) $(EXT_CFLAGS) $^ -o $@

$(BINDIR)/strncasecmp: $(BINDIR)/ctype.o strncasecmp.c
	$(CC) $(CFLAGS) $(EXT_CFLAGS) $^ -o $@

$(BINDIR)/strnstr: $(BINDIR)/memcmp.o $(BINDIR)/strlen.o strnstr.c
	$(CC) $(CFLAGS) $(EXT_CFLAGS) $^ -o $@

$(BINDIR)/%.o: %.c %.h
	$(CC) $(CFLAGS) -c $< -o $@

$(BINDIR)/%: %.c %.h
	$(CC) $(CFLAGS) $(EXT_CFLAGS) $< -o $@

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

$(EACSLFUZZDIR)/%: $(EACSLDIR)/%.c
	$(CLANG) $(CLANGFLAGS) $(GEN_CFLAGS) $(FUZZ_CFLAGS) $(FRAMAC_EACSL_LIB) libFuzzer.a -lstdc++ $< -o $@

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
	@$(FRAMAC) $(FRAMAC_DFLAGS) $(SRCFILES)

verify-separatedly: ## Run Frama-C on each file consequently.
	@for i in $(SRCFILES); do echo $$i; $(FRAMAC) $(FRAMAC_DFLAGS) $$i; done

verify-proved: ## Run Frama-C on each file consequently. Only completely proved functions.
	@$(FRAMAC) $(FRAMAC_DFLAGS) $(PROVEDFILES)

verify-proved-separatedly: ## Run Frama-C on each file consequently. Only completely proved functions.
	@for i in $(PROVEDFILES); do echo $$i; $(FRAMAC) $(FRAMAC_DFLAGS) $$i; done

verify-%:
	@$(FRAMAC) $(FRAMAC_DFLAGS) $*.c

update-%:
	@$(FRAMAC) $(FRAMAC_UFLAGS) $*.c

replay: ## Replay proofs simultaiously. You can also type replay-<target>.
	@$(FRAMAC) $(FRAMAC_DFLAGS) $(FRAMAC_REPLAY) $(SRCFILES)

replay-separatedly: ## Replay proofs consequently.
	@for i in $(SRCFILES); do echo $$i; $(FRAMAC) $(FRAMAC_DFLAGS) $(FRAMAC_REPLAY) $$i; done

replay-proved: ## Replay proofs for completely proved functions.
	@$(FRAMAC) $(FRAMAC_DFLAGS) $(FRAMAC_REPLAY) $(PROVEDFILES)

replay-proved-separatedly: ## Replay proved functions consequently.
	@FAIL=0; for i in $(PROVEDFILES); do $(FRAMAC) $(FRAMAC_DFLAGS) $(FRAMAC_REPLAY) $$i > /dev/null 2>&1 && echo "OK:   $$i" || { echo "FAIL: $$i"; FAIL=1; }; done; if [ $$FAIL -eq 1 ]; then exit 1; fi

replay-%:
	@$(FRAMAC) $(FRAMAC_DFLAGS) $(FRAMAC_REPLAY) $*.c

sprove: ## Replay proofs simultaiously. You can also type sprove-<target>.
	@$(FRAMAC) $(FRAMAC_DFLAGS) $(FRAMAC_SPROVE) $(SRCFILES)

sprove-separatedly: ## Replay proofs consequently.
	@for i in $(SRCFILES); do echo $$i; $(FRAMAC) $(FRAMAC_DFLAGS) $(FRAMAC_SPROVE) $$i; done

sprove-proved: ## Run sprove strategy on proved functions.
	@for i in $(PROVEDFILES); do echo $$i; $(FRAMAC) $(FRAMAC_DFLAGS) $(FRAMAC_SPROVE) $$i; done

sprove-%:
	@$(FRAMAC) $(FRAMAC_DFLAGS) $(FRAMAC_SPROVE) $*.c

clean: ## Remove all binary and generated files.
	-rm -fr $(GENBINDIR) $(RTEDIR) $(VALDIR) $(EACSLDIR) $(BINDIR) $(GENDIR) $(FUZZDIR) *.jessie *.pp.c

.PHONY: all build fuzz eacsl eacsl-build rte val run eacsl-run verify verify-separatedly verify-proved verify-proved-separatedly sprove-proved replay replay-separatedly replay-proved replay-proved-separatedly sprove sprove-separatedly clean

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
