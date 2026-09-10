# GitHub upload checklist

This directory is the canonical upload package for the Lean 4 formalization
of *On Erdős Problem 767: Cycles with Chords*.

## What to upload

Upload the contents of this directory as the root of one GitHub repository.
In particular, `lakefile.toml`, `lean-toolchain`, `Erdos767.lean`, `README.md`,
and the `Erdos767/` directory must appear at the repository root.

The package deliberately excludes local build output, Git metadata, obsolete
ZIP deliveries, macOS metadata, and the superseded `legacy/` directory.

## Verification before upload

Run from this directory:

```text
lake exe cache get
lake build
lake build Erdos767.Chapter3All Erdos767.Chapter4All Erdos767.Chapter5All
lake env lean Erdos767/Audit.lean
```

The expected result is successful completion of all commands.  Style and
lint warnings do not invalidate a kernel-checked proof.

## Verification after upload

The repository includes `.github/workflows/lean.yml`. GitHub Actions should
show a green `Lean verification` run after the workflow completes. That
workflow verifies the packaged hashes, builds the project, rejects project
proof placeholders and global axiom declarations, checks all three chapter
entry points, and prints the trust audit.

## Accurate public claim

Use the following scope statement:

> This Lean 4 project formalizes and kernel-checks the internal mathematical
> conclusions of Sections 3--5 and the main theorem of the manuscript,
> conditional on the nine cited literature results packaged as an explicit
> `LiteratureTheorems` argument. The project does not claim to prove those
> nine external literature results.

Do not describe the project as an unconditional formalization of the cited
Dirac, Ma--Ning, Fan--Lv--Wang, Erdős--Gallai, or Pósa theorems.

## Evidence files

- `PAPER_LEAN_MAP.md`: label-by-label paper-to-Lean coverage certificate;
- `VERIFICATION_REPORT.md`: build and trust-audit results;
- `CHAPTER4_5_STATUS.md`: Route-A status for Sections 4 and 5;
- `EXCEPTIONAL_PAPER_PROOF.md`: map for the exceptional combinatorial proof;
- `manuscript/ErdosProblem767.pdf`: the exact final PDF supplied by the author;
- `manuscript/ErdosProblem767.tex` and its two TikZ sources: author-designated final TeX;
- `Erdos767/FinalArithmetic.lean`: full-domain signed increment and agreement proof;
- `Erdos767/FinalPaper.lean`: final notation and numbered result interfaces;
- `FINAL_VERSION_SYNC.md`: provenance, changes, and manuscript discrepancies.

Do not upload `legacy/` or `tmp/`. Do not reuse the archived 2026-08-14
build report as evidence for this revision; consult `VERIFICATION_REPORT.md`.
