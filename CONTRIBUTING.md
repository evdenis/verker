# Contributing to VerKer

Thank you for your interest in contributing to VerKer! This document provides guidelines and instructions for contributing to the formal verification of Linux kernel library functions.

## Table of Contents

- [Getting Started](#getting-started)
- [Development Setup](#development-setup)
- [How to Contribute](#how-to-contribute)
- [Verification Guidelines](#verification-guidelines)
- [Coding Standards](#coding-standards)
- [Pull Request Process](#pull-request-process)

## Getting Started

VerKer is a formal verification project that uses ACSL (ANSI/ISO C Specification Language) to specify and verify Linux kernel library functions using the Frama-C/AstraVer toolchain.

### Prerequisites

Before contributing, familiarize yourself with:
- **ACSL**: [ACSL Implementation Documentation](http://frama-c.com/download/acsl-implementation-Sulfur-20171101.pdf)
- **Frama-C**: [Frama-C Documentation](https://frama-c.com/html/documentation.html)
- **AstraVer**: [AstraVer Wiki](https://forge.ispras.ru/projects/astraver/wiki)
- **Linux kernel string functions**: [Linux kernel lib/string.c](https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git/tree/lib/string.c)

## Development Setup

### Option 1: Using the Pre-configured VM

Download the VirtualBox VM image with pre-installed tools:
- [VM Image](https://disk.llkl.org/f/be6ea14a2d/?dl=1) (~3 GB)
- OS: Ubuntu, Login: user, Password: 1
- Contains VerKer and [acsl-proved](https://github.com/evdenis/acsl-proved) repositories

### Option 2: Manual Installation

1. **Install dependencies** (Ubuntu/Debian):
   ```bash
   sudo apt-get install opam libgtk2.0-dev libgtksourceview2.0-dev
   ```

2. **Install OPAM and OCaml**:
   ```bash
   opam init --compiler=4.14.2
   eval $(opam env)
   ```

3. **Install verification tools**:
   ```bash
   opam repo add ispras https://forge.ispras.ru/git/astraver.opam-repository.git
   opam update
   opam install frama-c astraver why3 alt-ergo
   ```

4. **Install SMT solvers**:
   - **cvc5**: Download from [cvc5 releases](https://github.com/cvc5/cvc5/releases)
   - **E-Prover**: Download from [E-Prover releases](https://github.com/eprover/eprover/releases)
   - **Z3**: `sudo apt-get install z3`

5. **Configure Why3**:
   ```bash
   why3 config --detect
   ```

6. **Clone the repository**:
   ```bash
   git clone https://github.com/evdenis/verker.git
   cd verker
   ```

## How to Contribute

### Types of Contributions

1. **Verify new functions**: Add specifications and proofs for unverified functions
2. **Improve existing proofs**: Optimize proof strategies, reduce assumptions
3. **Prove lemmas**: Formally prove lemmas using Coq or lemma functions
4. **Add fuzzing**: Integrate LibFuzzer for untested functions
5. **Documentation**: Improve documentation, add examples
6. **Bug fixes**: Fix specification bugs or proof errors

### Choosing a Function to Verify

Check the [Proofs Status](README.md#proofs-status) table in README.md:
- Functions without "proved" status need verification
- Functions marked with comments may need improvement
- 8 functions are currently incomplete: `strim`, `strncasecmp`, `strncat`, `strncpy`, `strnstr`, `strstr`, `strlcat`, `_parse_integer`

## Verification Guidelines

### File Structure

Each function requires two files:

1. **Header file (`<function>.h`)**: Contains specifications
   - ACSL axiomatics with logical functions
   - Lemmas (to be proved later)
   - Function contract (requires/ensures/assigns)
   - Optional: lemma functions (when `LEMMA_FUNCTIONS` defined)

2. **Source file (`<function>.c`)**: Contains implementation
   - Function body with loop invariants
   - Ghost variables for verification
   - `FUZZ_MAIN` for LibFuzzer integration
   - `DUMMY_MAIN` for standalone testing

### Adding a New Function

Use the [dismember](https://github.com/evdenis/spec-utils/) tool to extract functions:

```bash
dismember -m ~/linux-stable/lib/string.c \
          -k ~/linux-stable \
          --double \
          -f <function_name> \
          --output-dir ./src
```

This creates `<function>.c` and `<function>.h` in the `src/` directory.

### Writing ACSL Specifications

#### Function Contract Structure

```c
/*@ requires <preconditions>;
    assigns <modified locations>;
    ensures <postconditions>;
*/
```

#### Loop Invariants

Every loop must have:
- **Invariant**: Properties that hold at loop entry/exit
- **Assigns**: What the loop modifies
- **Variant**: Expression that decreases (proves termination)

Example:
```c
/*@ loop invariant 0 <= i <= n;
    loop invariant valid_str(s + i);
    loop assigns i;
    loop variant n - i;
*/
for (i = 0; i < n; i++) { ... }
```

#### Logical Functions vs. Functional Specifications

Develop logical functions when:
1. The C function is pure (no side effects)
2. The logical function is useful in other specifications
3. Example: `memcmp` logical function in `memcpy` ensures clause

Provide both forms when possible:
- Direct functional specification (for E-ACSL runtime checking)
- Logical function specification (for compositional reasoning)

### Verification Workflow

1. **Write initial specification**:
   ```bash
   make verify-<function>
   ```

2. **Analyze verification conditions** in Why3 IDE:
   - Try different solvers (Alt-Ergo, cvc5, E-Prover)
   - Apply transformations (split, inline, etc.)
   - Add lemmas if needed

3. **Iterate on loop invariants** until all VCs pass

4. **Save session**:
   - Session files are stored in `sessions/<function>.av/`
   - Commit these to the repository

5. **Test with fuzzing**:
   ```bash
   make fuzz-<function>
   ```

6. **Replay proofs** to ensure reproducibility:
   ```bash
   make replay-<function>
   ```

### Proof Strategy

The Makefile includes an automated strategy:
- Quick pass: 2s timeout, basic solvers
- Transformations: split, inline, remove triggers
- Deep pass: 10s timeout, all solvers

Modify `TIMEOUT` and `PROCESSES` variables as needed:
```bash
make verify-<function> TIMEOUT=30 PROCESSES=8
```

## Coding Standards

### ACSL Style

- Use descriptive predicate/logic function names
- Add comments explaining non-obvious invariants
- Group related lemmas together
- Use `\at(expr, Label)` for temporal properties

### C Code Style

- Follow Linux kernel coding style
- Keep original function implementation unchanged
- Only add ACSL annotations and ghost code
- Use `//@ ` for single-line annotations
- Use `/*@ ... */` for multi-line annotations

### Git Commit Messages

Format:
```
<function>: <short description>

<detailed explanation>
```

Examples:
```
strlen: add ACSL specification and proof

Add complete functional specification with logical function.
All VCs proved using Alt-Ergo and cvc5.

strcpy: fix loop invariant for buffer bounds

The previous invariant was too weak to prove memory safety.
Added ghost pointer to track original buffer location.
```

## Pull Request Process

1. **Create a feature branch**:
   ```bash
   git checkout -b verify-<function>
   ```

2. **Make your changes**:
   - Add specifications and proofs
   - Ensure all VCs are proved
   - Test with fuzzing if applicable

3. **Update README.md**:
   - Update the [Proofs Status](README.md#proofs-status) table
   - Mark function as "proved"
   - Add fuzzing status if applicable

4. **Verify CI passes locally**:
   ```bash
   make run
   make rte
   make val
   make replay-proved-separatedly
   ```

5. **Commit your changes**:
   ```bash
   git add src/<function>.c src/<function>.h sessions/<function>.av/
   git commit -m "<function>: add verification"
   ```

6. **Push and create PR**:
   ```bash
   git push origin verify-<function>
   ```

7. **PR Description should include**:
   - Which function was verified
   - Proof strategy used
   - Any interesting challenges or insights
   - Fuzzing results (if applicable)

### Review Process

- Maintainers will review specifications for correctness
- CI must pass (proof replay must succeed)
- At least one maintainer approval required
- Session files must be included

## Testing

### Running Tests

```bash
# Build all functions
make build

# Run all programs
make run

# Fuzz specific function
make fuzz-<function>

# Generate E-ACSL runtime assertions
make eacsl-proved

# Run value analysis
make val

# Run RTE (Runtime Error) analysis
make rte
```

### Continuous Integration

GitHub Actions runs on every push:
- Builds all functions
- Runs RTE and value analysis
- Replays all proved functions
- Runs proof strategy on proved functions

## Questions and Support

- **Issues**: [GitHub Issues](https://github.com/evdenis/verker/issues)
- **AstraVer**: [ISPRAS Forum](https://forge.ispras.ru/projects/astraver)
- **Frama-C**: [Frama-C Forum](https://framac.discourse.group/)

## License

By contributing, you agree that your contributions will be licensed under the same license as the project (see [LICENSE](LICENSE)).

## Academic Citations

If your contribution leads to academic work, please cite:

```bibtex
@inproceedings{efremov2018deductive,
  title={Deductive Verification of Unmodified Linux Kernel Library Functions},
  author={Efremov, Denis and Mandrykin, Mikhail and Khoroshilov, Alexey},
  booktitle={International Symposium on Leveraging Applications of Formal Methods},
  pages={216--234},
  year={2018},
  organization={Springer}
}
```

Thank you for contributing to formal verification of the Linux kernel!
