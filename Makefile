export TIMEOUT   ?= 10
export PROCESSES ?= 4

CC               := gcc
CFLAGS           := -Wall -Werror
CLANG            := clang
CLANGFLAGS       := -g -O1
GEN_CFLAGS       := -w
FUZZ_CFLAGS      := -fsanitize=fuzzer,address -DFUZZ_MAIN
EXT_CFLAGS       := -DDUMMY_MAIN
SPEC_CFLAGS      := -DSPEC -std=c11
BINDIR           := bin
FUZZDIR          := fzz
GENDIR           := gen
EACSLDIR         := $(GENDIR)/eacsl
RTEDIR           := $(GENDIR)/rte
VALDIR           := $(GENDIR)/val
GENBINDIR        := $(BINDIR)/gen
EACSLBINDIR      := $(GENBINDIR)/eacsl
EACSLFUZZDIR     := $(FUZZDIR)/eacsl
OPAM_EVAL        := eval $$(opam env)
#FRAMAC           := $(OPAM_EVAL); frama-c-gui -c11 -pp-annot -cpp-extra-args " -CC -E -x c $(SPEC_CFLAGS) " -machdep gcc_x86_64
FRAMAC           := $(OPAM_EVAL); frama-c -c11 -pp-annot -cpp-command "gcc -w -C -E -I." -cpp-extra-args " -CC -x c $(SPEC_CFLAGS) " -machdep gcc_x86_64
FRAMAC_EFLAGS    := -e-acsl -main LLVMFuzzerTestOneInput -pp-annot -cpp-extra-args " -CC -E -x c -DFUZZ_MAIN "
FRAMAC_EGEN      := -then-last -print -ocode
FRAMAC_RTEFLAGS  := -rte -main LLVMFuzzerTestOneInput -pp-annot -cpp-extra-args " -CC -E -x c -DFUZZ_MAIN "
FRAMAC_VALFLAGS  := -val -main LLVMFuzzerTestOneInput -pp-annot -cpp-extra-args " -CC -E -x c -DFUZZ_MAIN "
FRAMAC_RTEGEN    := -print -ocode
FRAMAC_VALGEN    := $(FRAMAC_RTEGEN)
FRAMAC_ESHARE    := $(shell $(FRAMAC) -print-share-path)/e-acsl
FRAMAC_LIBPATH   := $(shell $(FRAMAC) -print-lib-path)
FRAMAC_EACSL_LIB := -DE_ACSL_SEGMENT_MMODEL -DE_ACSL_IDENTIFY -std=c99 -m64 -I$(FRAMAC_ESHARE) $(FRAMAC_ESHARE)/e_acsl_mmodel.c -lm -lpthread $(FRAMAC_LIBPATH)/../libeacsl-gmp.a $(FRAMAC_LIBPATH)/../libeacsl-jemalloc.a

SRCFILES             := $(sort $(shell find ./src -maxdepth 1 -type f \! -name '*.pp.c' -name '*.c'))
FZZAVAILFILES        := $(sort $(shell grep -nre '|[[:space:]]\+[[:digit:]]\+[[:space:]]\+|' ./README.md | cut -d '|' -f 3,7 | grep yes | cut -d '|' -f 1 | tr -d ' \\' | sed -e 's/$$/.c/' -e 's!^!./src/!'))
BINAVAILFILES        := $(sort $(shell grep -nre '|[[:space:]]\+[[:digit:]]\+[[:space:]]\+|' ./README.md | cut -d '|' -f 3 | tr -d ' \\' | sed -e 's/$$/.c/' -e 's!^!./src/!'))
PROVEDFILES          := $(sort $(shell grep -nre '|[[:space:]]\+[[:digit:]]\+[[:space:]]\+|' ./README.md | cut -d '|' -f 3,5 | grep proved | cut -d '|' -f 1 | tr -d ' \\' | sed -e 's/$$/.c/' -e 's!^!./src/!'))
PROVEDFILES_H        := $(patsubst       %.c,         %.h,     $(PROVEDFILES))
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
	@for i in $(EACSLBINFILES); do echo $$i; ./$$i; done

eacsl-run-%: $(GENDIR) $(GENBINDIR) $(GENBINDIR)/%
	$(GENBINDIR)/$*

eacsl-fuzz-%: $(FUZZDIR) $(GENDIR) $(EACSLDIR) $(EACSLFUZZDIR) $(EACSLFUZZDIR)/%
	$(EACSLFUZZDIR)/$*

clean: ## Remove all binary and generated files.
	-rm -fr $(GENBINDIR) $(RTEDIR) $(VALDIR) $(EACSLDIR) $(BINDIR) $(GENDIR) $(FUZZDIR) src/*.o src/*.pp.c src/*.pp.h

.PHONY: all build fuzz eacsl eacsl-build rte val run eacsl-run clean

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
