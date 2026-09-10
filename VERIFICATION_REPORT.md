# Verification report — final revision 2026-09-10

## Environment

Lean `4.33.0-rc2`, Lake `5.0.0-src+d8b1897`, Mathlib pinned to
`v4.33.0-rc2` by the existing manifest and toolchain files. The toolchain was
installed locally for this check. No dependency pin was changed.

The older 2026-08-14 report is archived in `legacy/2026-08-14/`.
It is not used as evidence for this revision.

## Manuscripts

- The latest author-supplied PDF is copied byte-for-byte to
  `manuscript/ErdosProblem767.pdf`. The verified LaTeX and TikZ sources
  are retained locally and excluded from this public package.
- Both the final PDF and local TeX recompilation contain 22 pages.
- Their whitespace-normalized body text is identical after excluding figure
  text and page-number footers (`tmp/pdfs/body-comparison.txt`).
- The two local TikZ files use the final M_0 notation and explicit edge
  legends. The updated figure pages were rendered and visually checked.
- Repeated `pdflatex -interaction=nonstopmode -halt-on-error` passes converged
  with no undefined references or citations. The unchanged main TeX produces
  two hyperref PDF-bookmark-string warnings; these are not compilation errors.
- The supplied PDF was not overwritten with the local recompilation.

## Lean and source checks

- `lake exe cache get`: passed; pinned Mathlib cache restored.
- `lake env lean Erdos767/FinalArithmetic.lean`: passed.
- `lake build Erdos767.FinalArithmetic`: passed (8698 jobs).
- The signed split maximum, its agreement with the natural maximum for
  k + 1 ≤ n, and Claim 5.1(i) for all natural m are checked.
- The latest `FinalPaper.lean` entry point has built successfully, including
  the exact main theorem and the piecewise formula in final notation.
- Final `lake build`: passed (8733 jobs), including the root and both new modules.
- `lake build Erdos767.Chapter3All Erdos767.Chapter4All Erdos767.Chapter5All`: passed (8731 jobs).
- `lake env lean Erdos767/Audit.lean`: passed after the final build.
  The new final theorem, piecewise formula, signed/natural agreement and
  full-domain increment report only `[propext, Classical.choice, Quot.sound]`.
- `SHA256SUMS`: regenerated for the final package and checked successfully.
- Project scan: no proof placeholders, compiler-reflection tactic, or global
  axiom declarations. The 36 project modules have an acyclic import graph.

## Trust boundary

The nine literature results remain explicit `LiteratureTheorems` hypotheses.
The project does not prove those external results. The new signed arithmetic
proofs use no literature inputs. A successful kernel build checks the stated
conclusions; it does not imply that every sentence of an informal proof or
historical discussion is itself formalized.

## Reproduction

```text
lake exe cache get
lake build
lake build Erdos767.Chapter3All Erdos767.Chapter4All Erdos767.Chapter5All
lake env lean Erdos767/Audit.lean
shasum -a 256 -c SHA256SUMS
```

Local execution logs are under `tmp/pdfs/` and are excluded from packaging.
