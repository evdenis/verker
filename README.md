# VerKer
[![Formal Verification](https://github.com/evdenis/verker/actions/workflows/verify.yml/badge.svg)](https://github.com/evdenis/verker/actions/workflows/verify.yml)
[![License](https://img.shields.io/badge/License-GPL%20v2-blue.svg)](LICENSE)

To view this file in Russian, please follow the [link](README_ru.md).

The repository contains ACSL specifications for the Linux kernel functions. The aim of the project is formal verification of Linux kernel library functions.

**Quick Links:** [Contributing](CONTRIBUTING.md) | [Changelog](CHANGELOG.md) | [Issues](https://github.com/evdenis/verker/issues)

## Papers

- [D. V. Efremov, M. U. Mandrykin (2017) Formal verification of Linux kernel library functions In: Proceedings of ISP RAS, 29:6 (2017), 49–76 (in Russian)](http://www.ispras.ru/en/proceedings/isp_29_2017_6/isp_29_2017_6_49/) [[PDF]](http://www.ispras.ru/proceedings/docs/2017/29/6/isp_29_2017_6_49.pdf)
- [Efremov D., Mandrykin M., Khoroshilov A. (2018) Deductive Verification of Unmodified Linux Kernel Library Functions. In: Margaria T., Steffen B. (eds) Leveraging Applications of Formal Methods, Verification and Validation. Verification. ISoLA 2018. Lecture Notes in Computer Science, vol 11245. Springer, Cham](https://link.springer.com/chapter/10.1007%2F978-3-030-03421-4_15) [[ArXiv PDF]](https://arxiv.org/pdf/1809.00626.pdf)
- [G. Volkov, M. Mandrykin and D. Efremov, (2018) Lemma Functions for Frama-C: C Programs as Proofs, Ivannikov Ispras Open Conference (ISPRAS), Moscow, Russia, 2018, pp. 31-38.](https://ieeexplore.ieee.org/document/8675145) [[ArXiv PDF](https://arxiv.org/pdf/1811.05879.pdf)]

## Proofs Status

| ID | Function      | Status | Logic function | libfuzzer | Comment |
|----|---------------|--------|----------------|-----------|---------|
| 1  | check\_bytes8 | proved | proved         | yes       |         |
| 2  | match\_string | proved | not required   |           |         |
| 3  | memchr        | proved |                | yes       |         |
| 4  | memcmp        | proved |                | yes       |         |
| 5  | memscan       | proved | not required   | yes       |         |
| 6  | skip\_spaces  | proved | proved         | yes       | requires too strict (remove strlen) |
| 7  | strcasecmp    | proved |                | yes       |         |
| 8  | strcat        | proved | not required   |           | usr strcmp in ensures |
| 9  | strchr        | proved | proved         | yes       |         |
| 10 | strchrnul     | proved | proved         | yes       |         |
| 11 | strcmp        | proved | proved         | yes       |         |
| 12 | strcpy        | proved | not required   |           | use strcmp logic function |
| 13 | stpcpy        | proved | not required   |           |         |
| 14 | strcspn       | proved | proved         | yes       |         |
| 15 | strim         |        | not required   | !const    |         |
| 16 | strlen        | proved | proved         | yes       |         |
| 17 | strncasecmp   |        |                | yes       |         |
| 18 | strncat       |        | not required   |           |         |
| 19 | strnchr       | proved |                | yes       |         |
| 20 | strncmp       | proved |                | yes       |         |
| 21 | strncpy       |        | not required   |           |         |
| 22 | strnlen       | proved | proved         | yes       |         |
| 23 | strnstr       |        |                | yes       |         |
| 24 | strpbrk       | proved | proved         | yes       |         |
| 25 | strrchr       | proved |                | yes       |         |
| 26 | strreplace    | proved | not required   | !const    |         |
| 27 | strsep        | proved | not required   | !const    |         |
| 28 | strspn        | proved | proved         | yes       |         |
| 29 | strstr        |        |                | yes       |         |
| 30 | sysfs\_streq  | proved |                | yes       |         |
| 31 | strlcat       |        | not required   |           |         |
| 32 | strlcpy       | proved | not required   |           | use strncmp lf in ensures |
| 33 | memmove       | proved\*| not required   |           | use memcmp logic function at ensures |
| 34 | memcpy        | proved | not required   |           | use memcmp logic function at ensures |
| 35 | memset        | proved | not required   | !const    |         |
| 36 | kstrtobool    | proved | not required   | yes       |         |
| 37 | \_parse\_integer\_fixup\_radix | proved | not required | yes | |
| 38 | \_parse\_integer |     |                | yes       |         |

 \* memmove - except pointer difference vc fail. Model limitation.

## Toolchain

The specifications are developed in the [ACSL](http://frama-c.com/download/acsl-implementation-Sulfur-20171101.pdf) language. Frama-C with [AstraVer(Jessie)](https://forge.ispras.ru/projects/astraver) plugin is used as the deductive verification instrument.

### Installation

- **Detailed installation guide**: See [CONTRIBUTING.md](CONTRIBUTING.md#development-setup) for complete setup instructions
- **Quick start**: A description of how to install the tools can be found [here](https://forge.ispras.ru/projects/astraver/wiki). You can run them on Linux, Windows, Mac OS X.
- **Pre-configured VM**: By [link](https://disk.llkl.org/f/be6ea14a2d/?dl=1) you can download the VirtualBox VM image in ova format with pre-installed and already configured tools. Image size ~ 3 gigabytes. OS: Ubuntu. Login: user. Password: 1. There are two repositories in the **workspace** directory. First one is verker, the second is [acsl-proved](https://github.com/evdenis/acsl-proved) (examples with verification protocols).

### Recommended Tool Versions

For the best experience, use these versions (as used in CI):
- **OCaml**: 4.14.2+
- **OPAM**: 2.2.0+
- **SMT Solvers**:
  - cvc5 1.1.0+ (recommended, successor to CVC4)
  - CVC4 1.7+ (legacy support)
  - Alt-Ergo 2.2.0+
  - E-Prover 3.0+
  - Z3 (latest)

See [CHANGELOG.md](CHANGELOG.md) for recent toolchain updates.

### How to use the vanilla Frama-C

There is the compatibility layer with the vanilla Frama-C. You can find it in the **acsl_syntax_extension.h** file. To use the unmodified Frama-C you need to comment out the line ```#define ASTRAVER_TOOLCHAIN 1``` in the acsl syntax extension header. In the **Makefile** you may want to uncomment FRAMAC line to use the gui version. If you don't want to use the deductive verification plugin you need to redefine ```FRAMAC_DFLAGS``` variable in the Makefile.

In details:

```diff
diff --git a/acsl_syntax_extension.h b/acsl_syntax_extension.h
index 7018289..ca7b7e3 100644
--- a/acsl_syntax_extension.h
+++ b/acsl_syntax_extension.h
@@ -5,7 +5,7 @@
  * Comment this define if you want to use
  * vanilla Frama-C.
  */
-#define ASTRAVER_TOOLCHAIN 1
+//#define ASTRAVER_TOOLCHAIN 1
 
 
 #ifdef ASTRAVER_TOOLCHAIN /* used by default */
```

```diff
diff --git a/Makefile b/Makefile
index 4c6f529..0567e01 100644
--- a/Makefile
+++ b/Makefile
@@ -21,12 +21,12 @@ OPAM_EVAL        := eval $$(opam env)
 else
 OPAM_EVAL        := eval $$(opam config env)
 endif
-#FRAMAC           := $(OPAM_EVAL); frama-c-gui -c11 -cpp-extra-args " -C -E -x c $(SPEC_CFLAGS) " -machdep gcc_x86_64
-FRAMAC           := $(OPAM_EVAL); frama-c -c11 -cpp-extra-args " -C -E -x c $(SPEC_CFLAGS) " -machdep gcc_x86_64
+FRAMAC           := $(OPAM_EVAL); frama-c-gui -c11 -cpp-extra-args " -C -E -x c $(SPEC_CFLAGS) " -machdep gcc_x86_64
+#FRAMAC           := $(OPAM_EVAL); frama-c -c11 -cpp-extra-args " -C -E -x c $(SPEC_CFLAGS) " -machdep gcc_x86_64
 FRAMAC_NOHUP     := $(OPAM_EVAL); nohup frama-c -c11 -cpp-extra-args " -C -E -x c $(SPEC_CFLAGS) " -machdep gcc_x86_64
-#FRAMAC_DFLAGS    :=
+FRAMAC_DFLAGS    :=
 #FRAMAC_DFLAGS    := -wp
-FRAMAC_DFLAGS    := -av
+#FRAMAC_DFLAGS    := -av
 FRAMAC_UFLAGS    := -av -av-target update
 FRAMAC_REPLAY    := -av-target why3autoreplay
 FRAMAC_SPROVE    := -av-target why3sprove -av-why3-opt " --strategy proof_juicer --theory-filter axiom"
```

## Repository files

Each library function of the Linux kernel is located in a separate \*.c file. The corresponding \*.h file contains declarations, types, and structures specific to the function.

- The **kernel_definitons.h** file contains common for all functions types, macros, and other declarations.
- In **ctype.h** there are several functions, which were initially developed as macro. For the convenience of formal verification, these macro (islower, isupper, isdigit, ...) have been rewritten as an inline functions.
- The **acsl_syntax_extension.h** file contains the compatibility layer for the vanilla Frama-C.

## How to run

You can type ```make help``` to see the available options. It's recommended to start with already proved functions.

### Proofs Replay

To replay the proofs on your PC you need to type ```make replay-proved```. If you type ```make replay-proved-separatedly``` the instrument will try to replay proofs for functions one-by-one. ```CVC-1.4```, ```CVC-1.6```, ```Alt-Ergo-2.2.0``` solvers are required to replay proofs.

### Prove

To run the tools on a particular file you need to type ```make verify-<function>```. The command will run the Why3 ide with a number of verification conditions. If you type ```make verify-proved``` the instrument will be run only on the already proved functions.

### How to add a function in the repository

There is a tool called dismember in the [repository](https://github.com/evdenis/spec-utils/). It is used to "transfer" the function code into a separate file.
Example (code for the strim function):
```bash
$ dismember -m ~/linux-stable/lib/string.c -k ~/linux-stable --double -f strim --output-dir .
```

Two files will be created: strim.c and strim.h

- **-m** - path to the file with function definition
- **-k** - path to the kernel directory
- **-double** - generate two files \*.h and \*.c
- **-f** - function name
- **-output-dir** - output directory

## Specifications

The specification contract (precondition and postcondition) is located in the corresponding *.h file for each proved function (for example, strlen.h). A header file may also contain lemmas/axioms/logical functions if they are developed for a function.

A \*.c file contain a body of a function with loops invariants, evaluation functions, and assertions.

For some functions, specifications are redundant. In fact, they describe function's behavior in two different ways. For example, the contract for the strlen function consists of a "regular" functional requirements and the requirement for correspondence of the returned result to the logical function strlen.

What is the reason for a such "redundancy"?

The logical function strlen is convenient to use in the other function's specification. For example, strcmp function (and strcmp logical function in the strcpy contract). All the basic properties of a logical functions are expressed in lemmas (lemmas are not proved at this stage). Such specifications can't be translated in the run-time assertions with E-ACSL plugin. Therefore, for those functions with a correspondent logical function, there are additionally exists a "usual" specification.

Criteria to develop a logical function:

1. It is possible to write a logical function only for a pure C function;
2. It is rational to write logical functions if they are useful for developing specifications of other functions. For example, in the memcpy contract, you can express the equality of src and dest by calling the memcmp logical function.

Full verification protocols (solver launches) are included (\*.av folders) in the repository for the [proved funtions](#proofs-status).

At the given stage, the correctness of the lemmas in the specifications is not proved in any way. Thus, they can contain contradictions. The lemmas will be proved at the second project stage by means of Coq or lemma functions.

## How to run the instruments

```bash
$ frama-c -av <func>.c
$ frama-c -av check_bytes8.c
```
Or
```bash
$ make verify-<func>
$ make verify-check_bytes8
```

## LibFuzzer integration

[LibFuzzer](http://llvm.org/docs/LibFuzzer.html) - is the library for function fuzzing. The status of functions fuzzing integration can be viewed in [Proofs Status](#proofs-status) table. It is required to have clang compiler installed and libFuzzer.a in the project directory to run fuzzing.
How to run fuzzing:
```bash
$ make fuzz-<func>
$ make fuzz-check_bytes8
```
