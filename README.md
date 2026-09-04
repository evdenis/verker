# VerKer
To view this file in Russian, please follow the [link](README_ru.md).

The repository contains ACSL specifications for the Linux kernel functions. The aim of the project is formal verification of Linux kernel library functions.

## Papers

- [D. V. Efremov, M. U. Mandrykin (2017) Formal verification of Linux kernel library functions In: Proceedings of ISP RAS, 29:6 (2017), 49–76 (in Russian)](http://www.ispras.ru/en/proceedings/isp_29_2017_6/isp_29_2017_6_49/) [[PDF]](http://www.ispras.ru/proceedings/docs/2017/29/6/isp_29_2017_6_49.pdf)
- [Efremov D., Mandrykin M., Khoroshilov A. (2018) Deductive Verification of Unmodified Linux Kernel Library Functions. In: Margaria T., Steffen B. (eds) Leveraging Applications of Formal Methods, Verification and Validation. Verification. ISoLA 2018. Lecture Notes in Computer Science, vol 11245. Springer, Cham](https://link.springer.com/chapter/10.1007%2F978-3-030-03421-4_15) [[ArXiv PDF]](https://arxiv.org/pdf/1809.00626.pdf)
- [G. Volkov, M. Mandrykin and D. Efremov, (2018) Lemma Functions for Frama-C: C Programs as Proofs, Ivannikov Ispras Open Conference (ISPRAS), Moscow, Russia, 2018, pp. 31-38.](https://ieeexplore.ieee.org/document/8675145) [[ArXiv PDF](https://arxiv.org/pdf/1811.05879.pdf)]

## Proofs Status

The **AstraVer** column is the historical record: those functions were proved with the
AstraVer (Jessie) plugin, as described in the papers above. AstraVer is no longer
maintained and the project has moved to stock Frama-C/WP; the **WP** column tracks what
has been re-proved with WP so far.

| ID | Function      | AstraVer | WP | Logic function | libfuzzer | Comment |
|----|---------------|----------|----|----------------|-----------|---------|
| 1  | check\_bytes8 | proved |    | proved         | yes       |         |
| 2  | match\_string | proved |    | not required   |           |         |
| 3  | memchr        | proved |    |                | yes       |         |
| 4  | memcmp        | proved |    |                | yes       |         |
| 5  | memscan       | proved |    | not required   | yes       |         |
| 6  | skip\_spaces  | proved |    | proved         | yes       | requires too strict (remove strlen) |
| 7  | strcasecmp    | proved |    |                | yes       |         |
| 8  | strcat        | proved |    | not required   |           | usr strcmp in ensures |
| 9  | strchr        | proved |    | proved         | yes       |         |
| 10 | strchrnul     | proved |    | proved         | yes       |         |
| 11 | strcmp        | proved |    | proved         | yes       |         |
| 12 | strcpy        | proved |    | not required   |           | use strcmp logic function |
| 13 | stpcpy        | proved |    | not required   |           |         |
| 14 | strcspn       | proved |    | proved         | yes       |         |
| 15 | strim         |        |    | not required   | !const    |         |
| 16 | strlen        | proved |    | proved         | yes       |         |
| 17 | strncasecmp   |        |    |                | yes       |         |
| 18 | strncat       |        |    | not required   |           |         |
| 19 | strnchr       | proved |    |                | yes       |         |
| 20 | strncmp       | proved |    |                | yes       |         |
| 21 | strncpy       |        |    | not required   |           |         |
| 22 | strnlen       | proved |    | proved         | yes       |         |
| 23 | strnstr       |        |    |                | yes       |         |
| 24 | strpbrk       | proved |    | proved         | yes       |         |
| 25 | strrchr       | proved |    |                | yes       |         |
| 26 | strreplace    | proved |    | not required   | !const    |         |
| 27 | strsep        | proved |    | not required   | !const    |         |
| 28 | strspn        | proved |    | proved         | yes       |         |
| 29 | strstr        |        |    |                | yes       |         |
| 30 | sysfs\_streq  | proved |    |                | yes       |         |
| 31 | strlcat       |        |    | not required   |           |         |
| 32 | strlcpy       | proved |    | not required   |           | use strncmp lf in ensures |
| 33 | memmove       | proved\*|    | not required   |           | use memcmp logic function at ensures |
| 34 | memcpy        | proved |    | not required   |           | use memcmp logic function at ensures |
| 35 | memset        | proved |    | not required   | !const    |         |
| 36 | kstrtobool    | proved |    | not required   | yes       |         |
| 37 | \_parse\_integer\_fixup\_radix | proved |    | not required | yes | |
| 38 | \_parse\_integer |     |    |                | yes       |         |

 \* memmove - except pointer difference vc fail. Model limitation.

## Toolchain

The specifications are written in [ACSL](https://frama-c.com/download/frama-c-acsl-implementation.pdf)
and verified with stock [Frama-C](https://frama-c.com/) and its
[WP](https://frama-c.com/fc-plugins/wp.html) plugin. No patched Frama-C is needed any more.

Developed against Frama-C 33.0 (Arsenic) with Why3 1.8.2 and the Alt-Ergo, CVC4, CVC5 and
Z3 solvers. Install it with [opam](https://opam.ocaml.org/):

```bash
$ opam install frama-c why3 alt-ergo
$ frama-c -wp-list-provers
```

Earlier releases of this repository targeted the
[AstraVer (Jessie)](https://forge.ispras.ru/projects/astraver) plugin. That toolchain is
unmaintained and its support has been removed; see the git history for the last AstraVer
state.

## Repository files

Each library function of the Linux kernel is located in a separate \*.c file. The corresponding \*.h file contains declarations, types, and structures specific to the function.

- The **kernel_definitions.h** file contains common for all functions types, macros, and other declarations.
- In **ctype.h** there are several functions, which were initially developed as macro. For the convenience of formal verification, these macro (islower, isupper, isdigit, ...) have been rewritten as an inline functions.

## How to run

You can type ```make help``` to see the available options.

Frama-C/WP targets are being added back as part of the port away from AstraVer; until then
you can run the prover by hand:

```bash
$ frama-c -pp-annot -std c11 -cpp-extra-args " -DSPEC -Isrc " -machdep gcc_x86_64 \
      -wp -wp-rte -warn-unsigned-overflow -warn-unsigned-downcast \
      -wp-model Typed -wp-split src/strlen.c
```

### How to add a function in the repository

There is a tool called extricate in the [repository](https://github.com/evdenis/spec-utils/). It is used to "transfer" the function code into a separate file.
Example (code for the strim function):
```bash
$ extricate -m ~/linux-stable/lib/string.c -k ~/linux-stable --double -f strim --output-dir .
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

The lemmas in the axiomatics are currently assumed rather than proved, so they can contain
contradictions. Under AstraVer they were discharged by lemma functions; those lemma
functions are still in the headers but are parked behind ```#undef LEMMA_FUNCTIONS``` in
**kernel_definitions.h** until they are ported to vanilla ACSL ghost functions.

## LibFuzzer integration

[LibFuzzer](http://llvm.org/docs/LibFuzzer.html) - is the library for function fuzzing. The status of functions fuzzing integration can be viewed in [Proofs Status](#proofs-status) table. It is required to have clang compiler installed and libFuzzer.a in the project directory to run fuzzing.
How to run fuzzing:
```bash
$ make fuzz-<func>
$ make fuzz-check_bytes8
```
