# VerKer
[![Replay Status](https://travis-ci.org/evdenis/verker.svg?branch=master)](https://travis-ci.org/evdenis/verker)

To view this file in Russian, please follow the [link](README_ru.md).

The repository contains ACSL specifications for the Linux kernel functions. The aim of the project is formal verification of Linux kernel library functions.

## Papers

- [D. Efremov, M. Mandrykin, Formal Verification of Linux Kernel Library Functions (in Russian)](http://www.ispras.ru/proceedings/isp_29_2017_6/isp_29_2017_6_49/) [PDF](http://www.ispras.ru/proceedings/docs/2017/29/6/isp_29_2017_6_49.pdf)
- D. Efremov, M. Mandrykin, A. Khoroshilov, Deductive Verification of Unmodified Linux Kernel Library Functions (will be published soon)

## Proofs Status

| ID | Function      | Status | Logic function | libfuzzer | Comment |
|----|---------------|--------|----------------|-----------|---------|
| 1  | check\_bytes8 | proved | proved         | yes       |         |
| 2  | match\_string |        | not required   |           |         |
| 3  | memchr        | proved |                | yes       |         |
| 4  | memcmp        | proved |                | yes       |         |
| 5  | memscan       | proved | not required   | yes       |         |
| 6  | skip\_spaces  | proved | proved         | yes       | requires too strict (remove strlen) |
| 7  | strcasecmp    | proved |                | yes       |         |
| 8  | strcat        | proved | not required   |           | usr strcmp in ensures |
| 9  | strchr        | proved | proved         | yes       |         |
| 10 | strchrnul     | proved | proved         | yes       |         |
| 11 | strcmp        | proved |                | yes       |         |
| 12 | strcpy        | proved | not required   |           | use strcmp logic function |
| 13 | strcspn       | proved | proved         | yes       |         |
| 14 | strim         |        | not required   | !const    |         |
| 15 | strlen        | proved | proved         | yes       |         |
| 16 | strncasecmp   |        |                | yes       |         |
| 17 | strncat       |        | not required   |           |         |
| 18 | strnchr       | proved |                | yes       |         |
| 19 | strncmp       |        |                | yes       |         |
| 20 | strncpy       |        | not required   |           |         |
| 21 | strnlen       | proved | proved         | yes       |         |
| 22 | strnstr       |        |                | yes       |         |
| 23 | strpbrk       | proved | proved         | yes       |         |
| 24 | strrchr       | proved |                | yes       |         |
| 25 | strreplace    |        | not required   | !const    |         |
| 26 | strsep        | proved | not required   | !const    |         |
| 27 | strspn        | proved | proved         | yes       |         |
| 28 | strstr        |        |                | yes       |         |
| 29 | sysfs\_streq  |        |                | yes       |         |
| 30 | strlcat       |        | not required   |           |         |
| 31 | strlcpy       | proved | not required   |           | use strncmp lf in ensures |
| 32 | memmove       | proved\*| not required   |           | use memcmp logic function at ensures |
| 33 | memcpy        | proved | not required   |           | use memcmp logic function at ensures |
| 34 | memset        | proved | not required   | !const    |         |
| 35 | kstrtobool    | proved | not required   | yes       |         |
| 36 | \_parse\_integer\_fixup\_radix | proved | not required | yes | |
| 37 | \_parse\_integer |     |                | yes       |         |

 \* memmove - except pointer difference vc fail. Model limitation.

## Toolchain

The specifications are developed in the [ACSL](http://frama-c.com/download/acsl-implementation-Sulfur-20171101.pdf) language. Frama-C with [AstraVer(Jessie)](https://forge.ispras.ru/projects/astraver) plugin is used as the deductive verification instrument.

- A description of how to install the tools can be found [here](https://forge.ispras.ru/projects/astraver/wiki). You can run them on Linux, Windows, Mac OS X.
- By [link](https://disk.llkl.org/f/be6ea14a2d/?dl=1) you can download the VirtualBox VM image in ova format with pre-installed and already configured tools. Image size ~ 3 gigabytes. OS: Ubuntu. Login: user. Password: 1. There are two repositories in the **workspace** directory. First one is verker, the second is [acsl-proved](https://github.com/evdenis/acsl-proved) (examples with verification protocols).

## Repository files

Each library function of the Linux kernel is located in a separate \*.c file. The corresponding \*.h file contains declarations, types, and structures specific to the function.

- The **kernel_definitons.h** file contains common for all functions types, macros, and other declarations.
- In **ctype.h** there are several functions, which were initially developed as macro. For the convenience of formal verification, these macro (islower, isupper, isdigit, ...) have been rewritten as an inline functions.

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

Full verification protocols (solver launches) are included (\*.jessie folders) in the repository for the [proved funtions](#proofs-status).

At the given stage, the correctness of the lemmas in the specifications is not proved in any way. Thus, they can contain contradictions. The lemmas will be proved at the second project stage by means of Coq or lemma functions.

## How to run the instruments

```bash
$ frama-c -jessie <func>.c
$ frama-c -jessie check_bytes8.c
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
