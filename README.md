# VerKer

To view this file in Russian, please follow the [link](README_ru.md).

ACSL specifications for Linux kernel functions

The aim of this project is the formal verification of Linux kernel library functions.

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

Specifications are developed in the ACSL language. Frama-C with Jessie plugin is used as deductive verification instrument.

- A description of how to install the tools can be found [here](https://forge.ispras.ru/projects/astraver/wiki). You can run them on Linux, Windows, Mac OS X.
- By [link](https://disk.llkl.org/f/be6ea14a2d/?dl=1) you can download the VirtualBox VM image in ova format with pre-installed and already configured tools. Image size ~ 3 gigabytes. OS: Ubuntu. Login: user. Password: 1. There are two repositories in the **workspace** directory. First one is verker, the second is acsl-proven (examples with verification protocols).

## Repository files

Each library function of the Linux kernel is located in a separate \*.c file. The corresponding \*.h file contains declarations, types, and structures specific to the function.

- The **kernel_definitons.h** file contains common for all functions types, macros, and other declarations.
- In **ctype.h** there are several functions, which were initially developed as macros. For the convenience of formal verification, these macros (islower, isupper, isdigit, ...) have been rewritten as inline functions.

### How to add function in repository

The [repository](https://github.com/evdenis/spec-utils/) has a tool called dismember. It is used to "transfer" the function code into a separate file.
Example (code for the strim function):
```bash
$ dismember -m ~/linux-stable/lib/string.c -k ~/linux-stable --double -f strim --output-dir .
```

Two files will be created: strim.c and strim.h

- Argument **-m** - path to the file with function definition
- Argument **-k** - path to the kernel directory
- Argument **-double** - generate two files \*.h and \*.c
- Argument **-f** - function name
- Argument **-output-dir** - output directory

## Specifications

The specification contract (precondition and postcondition) is located in the corresponding *.h file for each proved function (for example, strlen.h). Header file may also contain lemmas/axioms/logical functions if they are developed for the function.

The \*.c files contain a body of a function with cycle invariants, evaluation functions, and assertions.

For some functions, the specifications are redundant. In fact, they describe function's behavior in two different ways. One of such functions is strlen. Its specification consists of usual functional requirements and the requirement for correspondence of the returned result to a call of logical function strlen.

What is the reason for such "redundancy"?

The logical function strlen is convenient to use in the other function's specifications, for example, strcmp (and strcmp logical function in the strcpy functional requirements). All the basic properties of a logical function are expressed in the terms of lemmas (lemmas are not proved at this stage). Such specifications can't be translated in the run-time assertions with E-ACSL plugin. Therefore, for those functions with a logical function in the specifications, there are additionally regular specifications.

Criteria to develop logic function specification:

1. It is possible to write logical function only for pure C function.
2. It is rational to write logical functions if they are useful for developing specifications, including other functions. For example, in the memcpy contract, you can express the equality of src and dest by calling the memcmp logical function.

Full verification protocols (solver launches) are not included in the repository at the moment. This will be done a little later when more functions will be proven.

At the given stage, the correctness of the lemmas in the specifications was not proved in any way. Thus, they can contain contradictions. The lemmas will be proved in the second stage when specifications will be "freezed" and the verification protocols will be committed. The correctness of the lemmas will be proved by means of Coq or lemma functions.

## How to run instruments

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

[LibFuzzer](http://llvm.org/docs/LibFuzzer.html) - is the library for functions fuzzing. The status of functions fuzzing integration can be viewed in Proofs Status table. It is required to have clang compiler installed and libFuzzer.a in the project directory to run fuzzing.
How to run fuzzing:
```bash
$ make fuzz-<func>
$ make fuzz-check_bytes8
```
