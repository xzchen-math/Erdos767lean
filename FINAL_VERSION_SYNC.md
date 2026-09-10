# Final manuscript synchronization — 2026-09-10

## Sources

The author designated the latest `On_Erdos_problem_767__Cycles_with_Chords.pdf`
and `v8-0817.tex` as final. The PDF is preserved byte-for-byte at
`manuscript/ErdosProblem767.pdf`; its hash is recorded in `manuscript/README.md`
and `SHA256SUMS`. The LaTeX and TikZ sources are retained locally, outside this public package.
The original draft, historical reports, and superseded first PDF attachment
are kept locally under `legacy/2026-08-14/`, excluded from public packaging.

The latest supplied PDF replaces the earlier attachment at the same path.
The main text of the latest PDF and TeX agrees; the q-membership argument is
unnumbered in both. Source recompilation is kept under `tmp/pdfs/` so it does
not overwrite the original final PDF.

## Changes to Lean

- `FinalPaper.lean` exposes final notation I/R/J/F for legacy A/t/p/h,
  Theorem 1.3 (both F and the displayed maximum), the piecewise Lemma 3.7,
  and numbered interfaces for the remaining results. The root build imports
  this interface through Chapter5All.
- `FinalArithmetic.lean` adds the signed maximum `JInt` and proves Claim 5.1(i)
  for all natural m, including m < a. The old natural-number increment proof
  required a ≤ m. `JInt_eq_nat` proves that the signed and natural maxima agree
  for k + 1 ≤ n, covering the full main theorem range.
- The unnumbered rich-case q ∈ I_k step is exposed as
  `FinalPaper.rich_case_halfCycle_mem_I`.
- Audit includes the new final theorem, piecewise formula, signed/natural
  agreement and full-domain increment. No additional external premise,
  proof placeholder, or global axiom was introduced.

The main extremal formula, sharp threshold, constructions, closure dichotomy,
switching bound, exceptional (3,8,6) proof, and terminal induction retain their
mathematical conclusions. Existing proof identifiers remain compatible.
The nine external results remain explicit `LiteratureTheorems` hypotheses.

## Final manuscript correspondence

The final TeX moves notation into Section 2 and uses I/R/J/F consistently.
Construction 3.3 is called join-type; its graph is the existing `splitGraph`.
The closure dichotomy is Lemma 4.4, followed by its inputs 4.5–4.7.
The exterior edge bound is Lemma 4.8, followed by inputs 4.9–4.11.
The rich-case bounds after Claim 5.3 are unnumbered.
The current TeX label changes are listed in `PAPER_LEAN_MAP.md`.

The final manuscripts correct the earlier PDF's small-cycle range to k ≤ 6
and allow the terminal endpoint in the displayed nearest-integer argument.
Existing Lean proofs already include both cases and retain them.

The two local TikZ sources are updated to the final M_0 notation and explicit
edge legends. They remain editable figures; the supplied final PDF is preserved
as the authoritative rendered version. Recompiled pagination need not be binary
identical because of figure geometry and TeX environment differences.

## Validation

The final PDF and locally recompiled TeX have identical whitespace-normalized
body text after excluding figure text and page-number footers. Both have
22 pages. Figure pages were rendered and visually checked after the TikZ
updates.

See `VERIFICATION_REPORT.md` for actual commands and outcomes.
