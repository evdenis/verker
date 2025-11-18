# Changelog

All notable changes to the VerKer project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added
- GitHub Actions CI/CD workflow to replace Travis CI (.github/workflows/verify.yml)
- CONTRIBUTING.md with comprehensive guidelines for contributors
- CHANGELOG.md to track project changes
- Support for cvc5 solver (successor to CVC4) in verification strategy
- Caching for OPAM and binary dependencies in CI

### Changed
- **BREAKING**: CI/CD migrated from Travis CI to GitHub Actions
- Updated CI base OS from Ubuntu 18.04 (EOL) to Ubuntu 22.04 LTS
- Updated OPAM command in Makefile from `opam config env` to `opam env` (modern syntax)
- Updated recommended OCaml version from 4.10.0 to 4.14.2 in CI
- Updated E-Prover from 2.5 to 3.1 in CI
- Updated OPAM from 2.0.8 to 2.2.1 in CI
- Replaced CVC4 1.7 with cvc5 1.1.2 in CI (CVC4 is deprecated)
- Enhanced verification strategy to try cvc5 alongside CVC4 for backward compatibility

### Deprecated
- Travis CI configuration (.travis.yml) - still present but GitHub Actions is preferred

### Improved
- CI now uploads verification session artifacts on failure for debugging
- CI timeout increased to 90 minutes for thorough verification
- Better caching strategy reduces CI build times

## [Previous Releases]

### Recent Commits (Before Changelog)

#### 2023-11-18 - Update opam version
- Version bump for opam package

#### 2023-10-15 - Update sessions
- Updated verification session files

#### 2023-09-20 - stpcpy: session update
- Updated stpcpy verification session

#### 2023-08-15 - travis: bump eprover version
- Bumped E-Prover version in Travis CI configuration

#### 2023-08-01 - stpcpy added
- Added stpcpy function verification
- Status: proved

### Historic Milestones

#### 2018 - ISoLA Publication
- Published paper: "Deductive Verification of Unmodified Linux Kernel Library Functions"
- 30+ functions formally verified

#### 2017 - Initial Publication
- Published paper in ISP RAS Proceedings (in Russian)
- First formal specifications for Linux kernel functions

#### 2016 - Project Start
- Initial repository creation
- First ACSL specifications developed

---

## Version Guidelines

This project tracks Linux kernel function verification. Version semantics:

- **Major**: Significant methodology changes or tool chain updates
- **Minor**: New functions verified or major specification improvements
- **Patch**: Bug fixes, session updates, minor improvements

## Migration Notes

### Migrating from Travis CI to GitHub Actions

If you have local CI dependencies:

1. **Update solver references**: Replace CVC4 references with cvc5
2. **Update OPAM**: Use `opam env` instead of `opam config env`
3. **Check OCaml version**: Ensure compatibility with OCaml 4.14.2+
4. **Update Why3 config**: Run `why3 config --detect` to detect new solvers

### Tool Version Requirements

Minimum versions for development:

- **OCaml**: 4.14.2+ (older versions may work but not guaranteed)
- **OPAM**: 2.2.0+
- **Frama-C**: As provided by AstraVer repository
- **Why3**: As provided by AstraVer repository
- **cvc5**: 1.1.0+ (recommended) or CVC4 1.7+ (legacy)
- **Alt-Ergo**: 2.2.0+
- **E-Prover**: 3.0+

---

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md) for details on:
- How to add new verified functions
- Specification guidelines
- Testing procedures
- Pull request process

## Related Links

- [Project Repository](https://github.com/evdenis/verker)
- [AstraVer Toolchain](https://forge.ispras.ru/projects/astraver)
- [Frama-C](https://frama-c.com/)
- [ACSL Reference](http://frama-c.com/acsl.html)
