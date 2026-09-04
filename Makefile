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
EVADIR           := $(GENDIR)/eva
GENBINDIR        := $(BINDIR)/gen
EACSLBINDIR      := $(GENBINDIR)/eacsl
EACSLFUZZDIR     := $(FUZZDIR)/eacsl
OPAM_EVAL        := eval $$(opam env)
FRAMAC_COMMON    := -pp-annot -no-unicode -std c11 -cpp-command "gcc -w -C -E -Isrc" -cpp-extra-args " -CC -x c $(SPEC_CFLAGS) " -machdep gcc_x86_64
FRAMAC           := $(OPAM_EVAL); frama-c $(FRAMAC_COMMON)
FRAMAC_GUI       := $(OPAM_EVAL); frama-c-gui $(FRAMAC_COMMON)
FRAMAC_EFLAGS    := -e-acsl -main LLVMFuzzerTestOneInput -pp-annot -cpp-extra-args " -CC -E -x c -DFUZZ_MAIN "
FRAMAC_EGEN      := -then-last -print -ocode
FRAMAC_RTEFLAGS  := -rte -main LLVMFuzzerTestOneInput -pp-annot -cpp-extra-args " -CC -E -x c -DFUZZ_MAIN "
FRAMAC_EVAFLAGS  := -eva -eva-no-builtins-auto -main LLVMFuzzerTestOneInput -pp-annot -cpp-extra-args " -CC -E -x c -DFUZZ_MAIN "
FRAMAC_RTEGEN    := -print -ocode
FRAMAC_EVAGEN    := $(FRAMAC_RTEGEN)
FRAMAC_ESHARE    := $(shell $(FRAMAC) -print-share-path)/e-acsl
FRAMAC_LIBPATH   := $(shell $(FRAMAC) -print-lib-path)
SESSIONDIR       := sessions
REPORTDIR        := $(SESSIONDIR)/reports
# 'script' replays any tactic proof saved under $(SESSIONDIR)/script before
# the SMT provers are tried. Scripts are produced by the wp-auto-<fn> target.
WP_PROVERS       := -wp-prover script -wp-prover alt-ergo -wp-prover cvc5 -wp-prover z3
WP_AUTO          := wp:bitwised,wp:bitshift,wp:bitrange,wp:bittestrange,wp:range,wp:congruence,wp:split
# Both -warn-unsigned-overflow and -warn-unsigned-downcast are deliberately
# off. Unsigned wraparound is defined behaviour in C, and the kernel relies on
# it in two idioms this corpus is full of: `while (count--)`, and the byte
# comparison `c = (unsigned char) *s++`, where the conversion of a negative
# char is the whole point. RTE would ask those functions to prove they never
# do the thing they exist to do. This is what AENO and AENOC used to suppress.
WPFLAGS          := -wp -wp-rte \
                    -wp-model Typed -wp-split \
                    -wp-timeout $(TIMEOUT) -wp-par $(PROCESSES) $(WP_PROVERS) \
                    -wp-interactive batch -wp-script batch -wp-session $(SESSIONDIR)

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
RTEFILES             := $(patsubst ./src/%.c, $(RTEDIR)/%.c,   $(FZZAVAILFILES))
EVAFILES             := $(patsubst ./src/%.c, $(EVADIR)/%.c,   $(FZZAVAILFILES))
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

eva: $(GENDIR) $(EVADIR) $(EVAFILES) ## Run the Eva value analysis over the fuzz harnesses.

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

$(EVADIR):
	@-mkdir -p $(EVADIR)

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

$(EVADIR)/%.c: src/%.c
	$(FRAMAC) $(FRAMAC_EVAFLAGS) $< $(FRAMAC_EVAGEN) $@

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

# --- Frama-C/WP -------------------------------------------------------------
#
# Proof artifacts live in $(SESSIONDIR):
#   cache/            content-hashed prover results   (committed)
#   script/*.json     WP tactic scripts               (committed as they appear)
#   interactive/*.v   hand-written Coq                (committed as they appear)
#   reports/<fn>.json -wp-report-json baselines       (committed)
#
# The cache keys on an exact hash of the goal AND the prover version, so editing
# a function or upgrading a solver invalidates its entries; use wp-rebuild then.

wp: $(SESSIONDIR) ## Run WP on every function. You can also type wp-<function>.
	@$(FRAMAC) $(WPFLAGS) -wp-cache update $(SRCFILES)

wp-proved: $(SESSIONDIR) ## Run WP on the functions marked proved in the README WP column.
	@$(FRAMAC) $(WPFLAGS) -wp-cache update $(PROVEDFILES)

wp-replay: $(SESSIONDIR) ## Replay every proof from the committed cache; never runs a prover.
	@FAIL=0; for i in $(PROVEDFILES); do i=$$(basename $$i .c); \
		$(FRAMAC) $(WPFLAGS) -wp-cache offline src/$$i.c > /dev/null 2>&1 \
		&& echo "OK:   $$i" || { echo "FAIL: $$i"; FAIL=1; }; done; \
	exit $$FAIL

wp-rebuild: $(SESSIONDIR) ## Re-prove from scratch and overwrite the cache (after a toolchain upgrade).
	@$(FRAMAC) $(WPFLAGS) -wp-cache rebuild $(SRCFILES)

wp-status: $(SESSIONDIR) ## List the goals that are still unproved.
	@$(FRAMAC) $(WPFLAGS) -wp-cache update -wp-status $(SRCFILES)

wp-report: $(SESSIONDIR) $(REPORTDIR) ## Refresh the per-function JSON baselines.
	@for i in $(SRCFILES); do i=$$(basename $$i .c); \
		$(FRAMAC) $(WPFLAGS) -wp-cache update -wp-report-json $(REPORTDIR)/$$i.json src/$$i.c > /dev/null 2>&1; \
		sed -i -e 's!"$(CURDIR)/!"!g' $(REPORTDIR)/$$i.json; \
		echo "$$i"; done

wp-smoke: $(SESSIONDIR) ## Vacuity check: fail if a contract is provable because it is unreachable.
	@$(FRAMAC) $(WPFLAGS) -wp-cache update -wp-smoke-tests $(SRCFILES)

wp-gui-%: $(SESSIONDIR)
	@$(FRAMAC_GUI) $(WPFLAGS) -wp-cache update src/$*.c

wp-smoke-%: $(SESSIONDIR)
	@$(FRAMAC) $(WPFLAGS) -wp-cache update -wp-smoke-tests src/$*.c

wp-report-%: $(SESSIONDIR) $(REPORTDIR)
	@$(FRAMAC) $(WPFLAGS) -wp-cache update -wp-report-json $(REPORTDIR)/$*.json src/$*.c
	@sed -i -e 's!"$(CURDIR)/!"!g' $(REPORTDIR)/$*.json

wp-replay-%: $(SESSIONDIR)
	@$(FRAMAC) $(WPFLAGS) -wp-cache offline src/$*.c

wp-%: $(SESSIONDIR)
	@$(FRAMAC) $(WPFLAGS) -wp-cache update src/$*.c

wp-auto-%: $(SESSIONDIR) ## Search for a tactic proof of one function and save the script.
	@$(FRAMAC) $(WPFLAGS) -wp-cache none -wp-script update -wp-auto '$(WP_AUTO)' src/$*.c

wp-clean: ## Drop cache entries that no goal refers to any more.
	@$(FRAMAC) $(WPFLAGS) -wp-cache cleanup $(SRCFILES) > /dev/null

# The committed cache holds exactly the goals of the functions marked proved in
# the README WP column, and only the entries that record a proof. Rebuilding it
# from scratch is the only exact way to do that: a cache entry is keyed by a hash
# of the goal and carries no back-reference to the function it came from.
wp-prune: ## Rebuild the committed cache from the proved functions only.
	@rm -rf $(SESSIONDIR)/cache
	@if [ -n "$(strip $(PROVEDFILES))" ]; then \
		$(FRAMAC) $(WPFLAGS) -wp-cache update $(PROVEDFILES) > /dev/null 2>&1; \
		for f in $(SESSIONDIR)/cache/*.json; do \
			grep -q '"verdict": "valid"' $$f || rm -f $$f; done; \
	fi
	@echo "cache: $$(find $(SESSIONDIR)/cache -type f 2>/dev/null | wc -l) entries"

$(SESSIONDIR):
	@-mkdir -p $(SESSIONDIR)

$(REPORTDIR):
	@-mkdir -p $(REPORTDIR)

clean: ## Remove all binary and generated files.
	-rm -fr $(GENBINDIR) $(RTEDIR) $(EVADIR) $(EACSLDIR) $(BINDIR) $(GENDIR) $(FUZZDIR) src/*.o src/*.pp.c src/*.pp.h

.PHONY: all build fuzz eacsl eacsl-build rte eva run eacsl-run \
        wp wp-proved wp-replay wp-rebuild wp-status wp-report wp-smoke wp-clean wp-prune clean

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
