# Lean formalization of “On Erdős Problem 767: Cycles with Chords”

This project targets the final manuscript [`ErdosProblem767.pdf`](manuscript/ErdosProblem767.pdf)
provided by the author on 2026-09-10 and uses Lean 4 with Mathlib.
PDF SHA-256: `d4391e3a4db0ce18947a6941fa900175cdd0dee168cd059a005d7b85cee8a576`.

`Erdos767/FinalPaper.lean` provides the final notation `I`, `R`, `J`, `F`
and numbered entry points in `Erdos767.FinalPaper`, including
`theorem_1_3`, `theorem_1_3_max`, and `lemma_3_7`. Existing theorem names
remain available for compatibility. See [`FINAL_VERSION_SYNC.md`](FINAL_VERSION_SYNC.md)
for the changes, source provenance, and domain qualifications.
The public repository includes the final paper PDF and Lean source code.
The manuscript LaTeX and TikZ sources are retained locally and are not distributed here.
`FinalArithmetic.lean` also proves Claim 5.1(i) for signed split terms on the
whole stated domain and proves agreement with the natural maximum in the
main theorem range.
See [`VERIFICATION_REPORT.md`](VERIFICATION_REPORT.md) for this revision's actual check status.

For the exact upload procedure, integrity checks, and the wording of the
public verification claim, see [`UPLOAD_CHECKLIST.md`](UPLOAD_CHECKLIST.md).

The complete label-by-label coverage certificate is
[`PAPER_LEAN_MAP.md`](PAPER_LEAN_MAP.md).  The precise public claim is that the
paper's internal conclusions are verified conditional on the nine explicitly
packaged literature inputs in `LiteratureTheorems`; those cited theorems are
not claimed as proved by this repository.

## Chapter entry points

For chapter-by-chapter checking, use the following three executable modules:

- `Erdos767/Chapter3All.lean`: all Chapter 3 definitions, constructions,
  arithmetic lemmas, and manuscript conclusions.
- `Erdos767/Chapter4All.lean`: all Chapter 4 definitions, Route-A literature
  interfaces, and paper-specific deductions.
- `Erdos767/Chapter5All.lean`: all Chapter 5 deductions, exceptional case,
  base/terminal ranges, and the final theorem.

Each entry point imports the focused source modules containing the actual
proofs and can be built independently.  The root `Erdos767.lean` imports only
these three chapter entry points.

## Current verified layer

- `Erdos767/Basic.lean`: exact natural-number definitions of `I_k` (legacy `A_k`), `R_k` (legacy `t_k`),
  the split-construction term, `J_k` (legacy `p_k`), and `F_k` (legacy `h_k`), with elementary API lemmas.
- `Erdos767/Arithmetic.lean`: kernel-checked proofs of the sharp-threshold
  identity, the fixed-parameter linear increment, the exceptional numerical
  case, the full bounded calculation in `lem:small-c-arithmetic`, and a terminal
  threshold inequality.
- `Erdos767/GraphBasics.lean`: definitions of neighbors on a path, path-fans,
  actual cycle closure, incident chord vertices/count, and a kernel-checked
  proof of `lem:cycle-PF-equivalence`.
- `Erdos767/Constructions.lean`: the cyclic and split lower-bound graphs from
  Section 3, the general maximum-degree obstruction to path-fans, degree bounds
  for the cyclic core and half-shift matching, a proof that the nearly regular
  graph is `PF_(k+2)`-free, its exact edge count `t_k(n)`, and the exact degree
  of every right-side vertex in the split graph. It also proves the split
  graph's exact edge count
  `a*(n-a) + floor(a*(k+1-a)/2)` for every `a ∈ A_k`.
- `Erdos767/Chapter3.lean`: all seven labeled lemmas in Section 3, including
  the exact real `sqrt 3` cutoffs, the three-branch formula for `h_k`, both
  merge inequalities, and both cycle-arithmetic consequences.
- `Erdos767/SplitPathFan.lean`: the full path-alternation proof that the split
  construction is `PF_(k+2)`-free.  Together with its exact edge count, both
  lower-bound constructions are now completely checked.
- `Erdos767/Chapter4.lean`: kernel-checked foundational definitions for
  cycle witnesses, local maximality, Hamiltonian-connectedness,
  2-connectedness and degree-sum closure, including the facts that a longest
  cycle is locally maximal and that a closure step is fixed exactly when the
  graph is degree-sum closed.
- `Erdos767/LiteratureTheorems.lean`: the explicit Route-A assumption
  boundary.  It defines the iterated `C`-closure, the canonical `W`, `X`, and
  `Y` hosts, components outside a cycle, strong attachments, edge switching,
  and exact proposition-valued statements for the nine cited external
  inputs.  `LiteratureTheorems` packages those statements as fields; the file
  does not claim to prove them and contains no global `axiom` declaration.
- `Erdos767/Chapter4RouteA.lean`: finite stabilization of degree-sum closure,
  the closed-core minimum-degree proof, the complete paper-specific
  Ma--Ning degree--clique dichotomy, the full
  `exceptional-low-degree-or-W` lemma, and closure monotonicity facts. Any
  cited input is received through `lit : LiteratureTheorems`.
- `Erdos767/Switching.lean`, `ExteriorComponents.lean`,
  `StrongAttachment.lean`, `AttachmentPaths.lean`, `AttachmentCount.lean`,
  `AttachmentPacking.lean`, `CycleSuccessors.lean`, `CycleSplicing.lean`,
  `CyclePacking.lean`, and `MaNingEdges.lean`: the terminating switching
  construction, exterior-component decomposition, strong-attachment and
  cycle-spacing arguments, `claim:switching-terminal`, and both parts of
  `lem:Ma-Ning-e(G)`.
- `Erdos767/Chapter5.lean`: the cycle-degree lemma, both parts of the
  fixed-split-term increment claim, preservation of path-fan-freeness under
  induced subgraphs, the longest-path endpoint degree lemma, exact vertex
  deletion edge accounting, and the complete terminal-range induction.  The
  theorem `terminal_bound` exposes `lem:base` as an explicit premise, and
  `terminal_bound_of_literature` discharges it from the completed Route-A
  base-range proof.
- `Erdos767/Chapter5RouteA.lean`: exact-value interfaces (upper bound plus an
  attaining graph), all lower-bound witnesses, the complete `k=1` main-theorem
  branch from Pósa, and all three rich-exterior claims.
- `Erdos767/BaseSetup.lean`, `GraphSeparators.lean`,
  `CycleCaseBounds.lean`, `RichCase.lean`, `ExceptionalCertificate.lean`,
  `ExceptionalCase.lean`, and `BaseRange.lean`: the minimal-counterexample
  setup, every cycle-dichotomy subcase, the exceptional `(3,8,6)` certificate,
  `lem:base`, `lem:terminal`, and the unified theorem
  `main_theorem_of_literature`.

## Section 3 theorem map

| Manuscript label | Lean theorem |
|---|---|
| `lem:cycle-PF-equivalence` | `cycle_pathFan_equivalence` |
| `lem:linear-bound` | `linear_bound_real` |
| `lem:S-terminal` | `p_eq_terminal` |
| `lem:B-equals-f` | `h_eq_piecewise_real` |
| `lem:merge-ineq` | `merge_ineq_both` |
| `lem:cycle-arithmetic-consequences` | `cycle_arithmetic_consequences` |
| `lem:small-c-arithmetic` | `small_c_arithmetic` |

The corresponding integer-only versions of the irrational cutoff are exposed
as `linear_bound_discrete` and `h_eq_piecewise_discrete`.

There are no global `axiom`, `sorry`, or `admit` declarations in the checked
files.  The fields of `LiteratureTheorems` are explicit hypotheses, not
theorems asserted by the project.

The exceptional `(3,8,6)` case is now proved by the manuscript's explicit
combinatorial classification.  Lean separately checks the exterior-vertex
case split, the alternating-triple classification, every displayed 7/8-cycle,
and the final type-I/type-II chord count.  It uses no `bv_decide` certificate.
See `EXCEPTIONAL_PAPER_PROOF.md` for the manuscript-to-Lean map.

## Build

With `elan`/`lake` on `PATH`:

```text
lake build
```

The project pins its Lean and Mathlib versions in `lean-toolchain` and
`lakefile.toml`.

GitHub Actions verifies the packaged file hashes, runs the complete
kernel-checked build and all three chapter entry points, rejects project source
containing `sorry`, `admit`, `bv_decide`, or a global `axiom` declaration, and
prints the `Audit.lean` trust report.

## Scope

All labeled lemmas and both lower-bound constructions in Section 3 are now
checked. The eight cited Chapter 4 inputs and Pósa's theorem used in the
`k = 1` case are stated explicitly in `LiteratureTheorems.lean`. Route A is
complete through `main_theorem_of_literature`. For Route B, the nine
literature fields must additionally be proved.  The former compiler-reflected
exceptional certificate has already been replaced by a kernel-checked proof.
`CHAPTER4_5_STATUS.md` gives the label-by-label audit.

No external result is introduced with `axiom`, `sorry`, or `admit`.
