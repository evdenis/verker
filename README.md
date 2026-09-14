# VerKer
[![CI](https://github.com/evdenis/verker/actions/workflows/ci.yml/badge.svg)](https://github.com/evdenis/verker/actions/workflows/ci.yml)

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
| 3  | memchr        | proved | proved |                | yes       |         |
| 4  | memcmp        | proved | proved |                | yes       |         |
| 5  | memscan       | proved | proved | not required   | yes       |         |
| 6  | skip\_spaces  | proved | proved | proved         | yes       | requires too strict (remove strlen) |
| 7  | strcasecmp    | proved | proved |                | yes       | -warn-unsigned-downcast off |
| 8  | strcat        | proved | proved | not required   |           | usr strcmp in ensures |
| 9  | strchr        | proved | proved | proved         | yes       |         |
| 10 | strchrnul     | proved | proved | proved         | yes       |         |
| 11 | strcmp        | proved | proved | proved         | yes       | -warn-unsigned-downcast off |
| 12 | strcpy        | proved | proved | not required   |           | use strcmp logic function |
| 13 | stpcpy        | proved | proved | not required   |           |         |
| 14 | strcspn       | proved | proved | proved         | yes       |         |
| 15 | strim         |        | proved | not required   | !const    |         |
| 16 | strlen        | proved | proved | proved         | yes       |         |
| 17 | strncasecmp   |        |    |                | yes       |         |
| 18 | strncat       |        | proved | not required   |           |         |
| 19 | strnchr       | proved | proved |                | yes       |         |
| 20 | strncmp       | proved | proved |                | yes       | -warn-unsigned-downcast off |
| 21 | strncpy       |        | proved | not required   |           |         |
| 22 | strnlen       | proved | proved | proved         | yes       |         |
| 23 | strnstr       |        |    |                | yes       | memory safety and termination only; no functional postcondition yet |
| 24 | strpbrk       | proved | proved | proved         | yes       |         |
| 25 | strrchr       | proved | proved |                | yes       |         |
| 26 | strreplace    | proved | proved | not required   | !const    |         |
| 27 | strsep        | proved | proved | not required   | !const    |         |
| 28 | strspn        | proved | proved | proved         | yes       |         |
| 29 | strstr        |        |    |                | yes       |         |
| 30 | sysfs\_streq  | proved |    |                | yes       |         |
| 31 | strlcat       |        | proved | not required   |           |         |
| 32 | strlcpy       | proved | proved | not required   |           | use strncmp lf in ensures |
| 33 | memmove       | proved\*| proved | not required   |           | use memcmp logic function at ensures |
| 34 | memcpy        | proved | proved | not required   |           | use memcmp logic function at ensures |
| 35 | memset        | proved | proved | not required   | !const    |         |
| 36 | kstrtobool    | proved | proved | not required   | yes       |         |
| 37 | \_parse\_integer\_fixup\_radix | proved | proved | not required | yes | |
| 38 | \_parse\_integer |     |    |                | yes       |         |
| 39 | hex2bin       |        | proved | not required   |           | the packed byte is written as ```hi * 16 + lo```; see the RTE note above |
| 40 | int\_sqrt     |        |        | not required   |           | memory safety and termination only; no functional postcondition yet |

 \* Under AstraVer, memmove's pointer-difference VC failed (model limitation). It is fully proved under WP.

## Toolchain

The specifications are written in [ACSL](https://frama-c.com/download/frama-c-acsl-implementation.pdf)
and verified with stock [Frama-C](https://frama-c.com/) and its
[WP](https://frama-c.com/fc-plugins/wp.html) plugin. No patched Frama-C is needed any more.

Developed against Frama-C 33.0 (Arsenic) with Why3 1.8.2 and the Alt-Ergo, CVC4, CVC5 and
Z3 solvers. Install it with [opam](https://opam.ocaml.org/):

```bash
$ opam install frama-c why3 alt-ergo z3
$ frama-c -wp-list-provers   # cvc5 is not in opam; install it separately and put it on PATH
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

### Prove

```bash
$ make wp-strlen          # one function
$ make wp                 # all of them
$ make wp-status          # only the goals that are still unproved
$ make wp-gui-strlen      # the same run in the Frama-C GUI
```

```TIMEOUT``` (seconds per goal) and ```PROCESSES``` (parallel provers) are environment
knobs: ```make TIMEOUT=30 wp-strcmp```. Raising ```TIMEOUT``` alone has no effect on a goal
whose timeout is already cached — use ```make wp-rebuild``` to force the provers to run
again.

Some goals are out of reach for the SMT provers but fall to a WP tactic — nibble ranges
and shift equalities are the usual case. ```make wp-auto-<function>``` searches for such a
proof and saves it under ```sessions/script/```; ordinary runs replay those scripts before
calling a prover, so the search cost is paid once. No function currently needs one, so
```sessions/script/``` is empty. The tactics do *not* close "disjoint bits implies sum":
```(hi << 4) | lo == hi * 16 + lo``` stalls at ```wp:bitwised``` even with both operands
proved below 16, which is why hex2bin writes the arithmetic form and marks it
```CODE_CHANGE```.

Every run enables ```-wp-rte```, so the runtime-error obligations are part of the proof.
Two RTE options are deliberately left off, both because the kernel relies on conversions
that are well defined in C but that the checks would forbid:

- ```-warn-unsigned-overflow``` — ```while (count--)``` in memset, memcpy, memmove and
  friends steps past zero on the last iteration, and the wrapped value is never used.
- ```-warn-unsigned-downcast``` — the byte comparison ```c = (unsigned char) *s++``` in
  strcmp, strncmp, strcasecmp and ctype's ```__ismask``` converts a negative ```char```
  on purpose; that conversion is how an unsigned byte comparison is obtained.

Together these are what the AstraVer-era ```AENO``` and ```AENOC``` markers used to
suppress at individual sites. Functions whose proof depends on the second are flagged in
the Comment column of the table.
```make wp-smoke``` adds the vacuity check — it fails if a contract only holds because the
code it guards is unreachable.

### Proofs Replay

Proof artifacts are committed under ```sessions/```:

| Path | Contents |
|------|----------|
| ```sessions/cache/``` | content-hashed prover results |
| ```sessions/script/``` | WP tactic scripts |
| ```sessions/interactive/``` | hand-written Coq proofs |
| ```sessions/reports/``` | per-function ```-wp-report-json``` baselines |

```sessions/``` is marked ```-diff linguist-generated=true``` in ```.gitattributes```, so
these files stay out of ```git diff```, out of GitHub's PR review surface and out of its
language stats. Use ```git diff --text -- sessions/``` to see them anyway, or
```git log -- ':!sessions'``` to drop them from a log entirely.

```make wp-replay``` replays every proved function straight from the cache and never
invokes a solver, so it does not need Alt-Ergo, CVC5 or Z3 installed. Note that WP's cache
is keyed on an exact hash of the goal and on the prover version — unlike Why3 session
shapes it does not tolerate edits, so touching a function or upgrading a solver invalidates
its entries. ```make wp-rebuild``` regenerates them; the JSON baselines in
```sessions/reports/``` are the version-independent record.

The committed cache is restricted to the functions marked proved in the WP column, and
within those to the entries that record an actual proof. ```make wp-prune``` rebuilds it on
exactly that basis; run it before committing session updates. Cached timeouts are never
committed — they are stale negatives that would hide a goal a newer solver can now close.

### Out of reach for WP

Four functions cannot be proved with the Typed memory model as they stand, for reasons that
are not specification problems:

| Function | Obstacle |
|----------|----------|
| ```strscpy``` | reads and writes through ```*(unsigned long *)(src + res)```; WP's Typed model keeps each type in its own memory chunk and cannot reinterpret bytes as words |
| ```memchr_inv``` | same word-at-a-time trick, plus ```(unsigned long)start % 8``` pointer-to-integer arithmetic |
| ```bsearch``` | calls through a function pointer, which WP reports as ```Unknown callee, considering non-terminating call```; it would need a ```calls``` clause enumerating the possible callees |
| ```ctype``` | relating the 256-entry ```_ctype``` table to the ```isalnum```/```isspace```/... predicates needs a case analysis over every byte value, and the deliberate ```(unsigned char)``` reinterpretation of a signed ```char``` trips ```-warn-unsigned-downcast``` |

### Value analysis

```make eva``` runs the Eva plug-in over the libFuzzer harnesses as an independent
bug-finder. It is deliberately *not* chained into the WP run: a property Eva marks valid
would be skipped by WP, and here Eva only ever sees a synthetic harness, so its verdicts
would not generalise to all callers.

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

The logical function strlen is convenient to use in the other function's specification. For example, strcmp function (and strcmp logical function in the strcpy contract). All the basic properties of a logical functions are expressed in lemmas (each lemma is a proof obligation — see below). Such specifications can't be translated in the run-time assertions with E-ACSL plugin. Therefore, for those functions with a correspondent logical function, there are additionally exists a "usual" specification.

Criteria to develop a logical function:

1. It is possible to write a logical function only for a pure C function;
2. It is rational to write logical functions if they are useful for developing specifications of other functions. For example, in the memcpy contract, you can express the equality of src and dest by calling the memcmp logical function.

A ```lemma``` in an active axiomatic is a proof obligation, not an assumption: WP generates
a goal for it like any other. The corpus has 27 such goals and discharges 26; the exception
is ```strcmp_corollary```, which times out. Under AstraVer the inductive ones were discharged
by the plugin's ```lemma``` functions; they now live in the headers as ordinary ACSL ghost
functions whose contract WP proves and which a caller instantiates from ghost code — see the
block after each axiomatic in **strlen.h**, **strnlen.h** and friends.

What *is* assumed rather than proved are the 76 ```axiom```s in **ctype.h**,
**strncasecmp.h** and **hex2bin.h**, which tabulate ```tolower```/```toupper``` and
```hex_to_bin``` over the character set. Nothing checks them, and an inconsistency there
would make every goal that depends on them vacuously provable; ```make wp-smoke``` is the
only thing that would notice.

Three files — **strrchr.h**, **strim.c** and **memcmp.c** — still carry an older axiomatic
inside a plain ```/* */``` comment rather than an ACSL ```/*@ */``` one. That text is inert:
it is not parsed, not proved and not used by anything.

## LibFuzzer integration

[LibFuzzer](http://llvm.org/docs/LibFuzzer.html) - is the library for function fuzzing. The status of functions fuzzing integration can be viewed in [Proofs Status](#proofs-status) table. It is required to have clang compiler installed and libFuzzer.a in the project directory to run fuzzing.
How to run fuzzing:
```bash
$ make fuzz-<func>
$ make fuzz-check_bytes8
```
