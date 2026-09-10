# Paper-to-Lean coverage certificate

This document maps the final PDF `manuscript/ErdosProblem767.pdf` supplied on 2026-09-10,
SHA-256 `d4391e3a4db0ce18947a6941fa900175cdd0dee168cd059a005d7b85cee8a576`, to the Lean source.
The author also designated the locally retained `v8-0817.tex`
as final, SHA-256 `0e09328070ec4011775bfc5fe71df200d97a527a8458365f998c857f4c774834`. Numbers below are from the PDF;
the TeX uses the same result numbers. The q-membership argument is unnumbered.
Legacy LaTeX labels are retained as stable keys for existing proof comments. The final numbered API is `Erdos767.FinalPaper`.

## Precise verification claim

The project formalizes and kernel-checks the internal mathematical conclusions
of Sections 3--5 and the main theorem, conditional on the nine cited literature
results packaged as an explicit argument `lit : LiteratureTheorems`.  It does
not claim to prove those nine literature results.  No literature result is
introduced as a global project axiom.

Status terminology:

- **proved**: Lean contains a proof term checked by the kernel;
- **proved from Route A**: Lean contains a proof whose theorem type explicitly
  receives `lit : LiteratureTheorems`;
- **Route-A premise**: the exact cited statement is a field of
  `LiteratureTheorems` and is deliberately outside the project scope;
- **definition**: the paper object is represented by the named Lean definition.

## Front matter and main result

| Manuscript item | Status | Lean item | Source |
|---|---|---|---|
| Problem 1.1 (`thm:Bollobas`) | contextual research question, not a claimed theorem | -- | `manuscript/ErdosProblem767.pdf` |
| Theorem 1.2 (`thm:Jiang`) | contextual external theorem, not used as a proof input | -- | `manuscript/ErdosProblem767.pdf` |
| Introduction, unnumbered Pósa result (`thm:Posa-chorded-cycle`) | Route-A premise used for the `k=1` branch | `LiteratureTheorems.posaChordedCycle` | `Erdos767/LiteratureTheorems.lean` |
| Theorem 1.3 (`thm:main`) | proved from Route A | `main_theorem_of_literature` | `Erdos767/BaseRange.lean` |
| exact extremal-value interface | definition | `ExactUniversalEdgeBound` | `Erdos767/Chapter5RouteA.lean` |
| extremal function displayed in Theorem 1.3 (`thm:main`) | definition and piecewise identities proved | `h`, `h_eq_piecewise_real`, `h_eq_terminal` | `Erdos767/Basic.lean`, `Erdos767/Chapter3.lean` |

The final Lean theorem concludes
`ExactUniversalEdgeBound (k + 2) n (h k n)` for every `k >= 1` and
`n >= k + 2`.

## Section 3: extremal constructions and arithmetic

| Manuscript item | Status | Lean item | Source |
|---|---|---|---|
| `I_k`, `R_k(n)`, split term, `J_k(n)`, `F_k(n)` | definition | `FinalPaper.I`, `FinalPaper.R`, `splitTerm`, `FinalPaper.J`, `FinalPaper.F` | `Erdos767/Basic.lean` |
| Lemma 3.1 (`lem:cycle-PF-equivalence`) | proved | `cycle_pathFan_equivalence` | `Erdos767/GraphBasics.lean` |
| Construction 3.2 | definition | `nearlyRegularGraph` | `Erdos767/Constructions.lean` |
| its exact edge count `t_k(n)` | proved | `nearlyRegularGraph_card_edgeFinset_eq_t` | `Erdos767/Constructions.lean` |
| its `PF_(k+2)`-freeness | proved | `nearlyRegularGraph_pathFanFree` | `Erdos767/Constructions.lean` |
| Construction 3.3 (`thm:lower-S`) split construction | definition | `splitGraph` | `Erdos767/Constructions.lean` |
| its exact edge count | proved | `splitGraph_card_edgeFinset_eq` | `Erdos767/Constructions.lean` |
| its `PF_(k+2)`-freeness | proved | `splitGraph_pathFanFree` | `Erdos767/SplitPathFan.lean` |
| Lemma 3.5 (`lem:linear-bound`) | proved | `linear_bound_real` | `Erdos767/Chapter3.lean` |
| Lemma 3.6 (`lem:S-terminal`) | proved | `p_eq_terminal` | `Erdos767/Chapter3.lean` |
| Lemma 3.7 (`lem:B-equals-f`) | proved | `h_eq_piecewise_real` | `Erdos767/Chapter3.lean` |
| Claim 3.1 (`claim:h_k(n)-merge`) | proved | `h_le_mul_sub_one_of_p_lt_h` | `Erdos767/Chapter3.lean` |
| Lemma 3.8 (`lem:merge-ineq`), parts (i) and (ii) | proved | `merge_ineq_both` | `Erdos767/Chapter3.lean` |
| Lemma 3.9 (`lem:cycle-arithmetic-consequences`), parts (i) and (ii) | proved | `cycle_arithmetic_consequences` | `Erdos767/Chapter3.lean` |
| Lemma 3.10 (`lem:small-c-arithmetic`) | proved | `small_c_arithmetic` | `Erdos767/Arithmetic.lean` |

The listed proof terms establish the stated arithmetic conclusions; they
need not reproduce every intermediate line of the informal proofs.  Integer-only companion statements are exposed
as `linear_bound_discrete` and `h_eq_piecewise_discrete`.

## Section 4: closure, switching, and stability tools

| Manuscript item | Status | Lean item | Source |
|---|---|---|---|
| graph families `W`, `X`, `Y` | definition, with supporting facts proved | `IsWGraph`, `IsXGraph`, `IsYGraph`, `wGraphFromPartition` | `Erdos767/LiteratureTheorems.lean` |
| Theorem 4.1 (`thm:Dirac-cycle`) | Route-A premise | `LiteratureTheorems.diracCycle` | `Erdos767/LiteratureTheorems.lean` |
| Theorem 4.2 (`thm:MN-exterior-stability`) | Route-A premise | `LiteratureTheorems.maNingExteriorStability` | `Erdos767/LiteratureTheorems.lean` |
| Lemma 4.3 (`lem:exceptional-low-degree-or-W`) | proved | `exceptional_low_degree_or_W` | `Erdos767/Chapter4RouteA.lean` |
| Lemma 4.5 (`lem:closure-preserves-local-maximality`) | Route-A premise | `LiteratureTheorems.closurePreservesLocalMaximality` | `Erdos767/LiteratureTheorems.lean` |
| Lemma 4.6 (`lem:Ma-Ning-non-ha`) | Route-A premise | `LiteratureTheorems.maNingNonHamiltonianConnected` | `Erdos767/LiteratureTheorems.lean` |
| Lemma 4.7 (`lem:Ma-Ning-degree`) | Route-A premise | `LiteratureTheorems.maNingDegree` | `Erdos767/LiteratureTheorems.lean` |
| Lemma 4.4 (`lem:Ma-Ning-cycle-dichotomy`) | proved from Route A | `maNing_cycle_dichotomy` | `Erdos767/Chapter4RouteA.lean` |
| Lemma 4.9 (`lem:Ma-Ning-strong-attachment`) | Route-A premise | `LiteratureTheorems.maNingStrongAttachment` | `Erdos767/LiteratureTheorems.lean` |
| Lemma 4.10 (`lem:Fan-Lv-Wang-switch`) | Route-A premise | `LiteratureTheorems.fanLvWangSwitch` | `Erdos767/LiteratureTheorems.lean` |
| Lemma 4.11 (`lem:EG-path`) | Route-A premise | `LiteratureTheorems.erdosGallaiPath` | `Erdos767/LiteratureTheorems.lean` |
| Claim 4.1 (`claim:switching-terminal`) | proved from Route A | `switching_terminal_claim_of_literature` | `Erdos767/ExteriorComponents.lean` |
| Lemma 4.8 (`lem:Ma-Ning-e(G)`), part (i) | proved from Route A | `maNing_edge_bound_i_of_literature` | `Erdos767/MaNingEdges.lean` |
| Lemma 4.8 (`lem:Ma-Ning-e(G)`), part (ii) | proved from Route A | `maNing_edge_bound_ii_of_literature` | `Erdos767/MaNingEdges.lean` |

The proof chain also kernel-checks closure stabilization, the closed cycle
core, switching descent, exterior-component decomposition, strong
attachments, longest paths, cyclic spacing, and inside/crossing/outside edge
accounting in the focused modules imported by `Chapter4All.lean`.

## Section 5: proof of the main theorem

| Manuscript item | Status | Lean item | Source |
|---|---|---|---|
| Lemma 5.1 (`lem:base`) upper bound | proved from Route A | `base_range_upper_of_literature` | `Erdos767/BaseRange.lean` |
| exact base range, including attaining graphs | proved from Route A | `exact_base_range_of_literature` | `Erdos767/BaseRange.lean` |
| Lemma 5.2 (`lem:terminal`) | proved from Route A | `terminal_bound_of_literature` | `Erdos767/BaseRange.lean` |
| Lemma 5.3 (`lem:cycle-degree`) | proved | `cycle_degree_on_cycle` | `Erdos767/Chapter5.lean` |
| Lemma 5.4 (`lem:minimal-counterexample-setup`) | proved from Route A and the explicit induction hypothesis | `minimalCounterexample_setup` | `Erdos767/BaseSetup.lean` |
| Claim 5.1 (`claim:Sk-linear-increment`), part (i) | proved | `FinalPaper.claim_5_1_i`, `claim_5_1_i_signed` | `Erdos767/FinalArithmetic.lean` |
| Claim 5.1 (`claim:Sk-linear-increment`), part (ii) | proved | `h_eq_t_descends` | `Erdos767/Chapter5.lean` |
| cycle-dichotomy case (i) | proved from Route A | `cycle_case_i_edge_bound` | `Erdos767/CycleCaseBounds.lean` |
| cycle-dichotomy case (ii), inside case | proved | `cycle_case_ii_inside_bound` | `Erdos767/CycleCaseBounds.lean` |
| cycle-dichotomy case (ii), sparse case | proved | `cycle_case_ii_sparse_edge_bound` | `Erdos767/CycleCaseBounds.lean` |
| cycle-dichotomy case (ii), small case or exceptional tuple | proved from Route A | `cycle_case_ii_small_edge_bound_or_exception` | `Erdos767/CycleCaseBounds.lean` |
| exceptional `(k,n,c)=(3,8,6)` classification | proved by the paper's combinatorial argument | `exceptional_fin8_impossible_paper`, `exceptional_case_contradiction` | `Erdos767/ExceptionalCertificate.lean`, `Erdos767/ExceptionalCase.lean` |
| Claim 5.2 (`claim:ext-rich-host1`) | proved from Route A | `ext_rich_host1_of_literature` | `Erdos767/Chapter5RouteA.lean` |
| Claim 5.3 (`claim:ext-rich-host2`) | proved | `ext_rich_host2` | `Erdos767/Chapter5RouteA.lean` |
| Unnumbered rich-case edge bound after Claim 5.3 (`claim:ext-rich-edge-bound`) | proved | `ext_rich_edge_bound` | `Erdos767/Chapter5RouteA.lean` |
| Unnumbered rich-case step: `q ∈ I_k` | proved from the cycle lower bound and a large exterior attachment | `FinalPaper.rich_case_halfCycle_mem_I`, `halfCycle_mem_A_of_large_outside_attachment` | `Erdos767/FinalPaper.lean`, `Erdos767/Chapter5RouteA.lean` |
| rich exterior subcase | proved from Route A | `cycle_case_ii_rich_edge_bound` | `Erdos767/RichCase.lean` |
| Theorem 1.3 (`thm:main`), `k=1`, including the `n=3` exception | proved from the Posa Route-A premise | `main_k_one_of_three_le` | `Erdos767/Chapter5RouteA.lean` |
| Theorem 1.3 (`thm:main`), `k>=2` | proved from Route A | `main_k_ge_two_of_literature` | `Erdos767/BaseRange.lean` |
| unified Theorem 1.3 (`thm:main`) | proved from Route A | `main_theorem_of_literature` | `Erdos767/BaseRange.lean` |

The ninth Route-A input, used in the `k=1` branch, is
`LiteratureTheorems.posaChordedCycle`.

## Reproducible verification

The root module `Erdos767.lean` imports exactly the three chapter entry points
`Chapter3All`, `Chapter4All`, and `Chapter5All`.  From a clean checkout run:

```text
lake exe cache get
lake build
lake build Erdos767.Chapter3All Erdos767.Chapter4All Erdos767.Chapter5All
lake env lean Erdos767/Audit.lean
```

`Audit.lean` prints the trusted assumptions of the representative and final
theorems.  The GitHub workflow additionally verifies the packaged hashes and
rejects project source containing proof placeholders, compiler-reflection
certificates, or global axiom declarations.

## Scope boundary

The following nine cited inputs are outside Route A and are not claimed as
proved here: Dirac cycle, Ma--Ning exterior stability, preservation of local
maximality under cycle closure, Ma--Ning non-Hamiltonian-connectedness,
Ma--Ning degree, Ma--Ning strong attachment, Fan--Lv--Wang switching,
Erdos--Gallai path, and Posa's chorded-cycle bound.  Proving these fields would
constitute the separate unconditional Route B.

## Final-version qualifications

`FinalPaper.J` uses the existing natural-number implementation. Its split terms
match the signed expression when `a ≤ n`. `FinalPaper.JInt` implements the
signed maximum on the full domain, and `FinalPaper.JInt_eq_nat` proves agreement
with `p` when `k + 1 ≤ n`. The new `claim_5_1_i_signed` (also exported as
`FinalPaper.claim_5_1_i`) proves the increment for all natural m, including
m < a, without the former `a ≤ m` premise. Thus it covers the paper's m ≥ 1.
`FinalPaper.F` uses the binomial branch below k + 2.

The supplied TeX's Claim 5.1 label is `claim:increment-properties`; the old
proof comments use `claim:Sk-linear-increment`. The q-membership step is an unnumbered
paragraph in both final manuscripts. Its proof is unchanged. The following rich-case
edge estimate is unnumbered in both supplied finals.

The nine external statements are unchanged: Pósa's unnumbered theorem,
Theorems 4.1–4.2, and Lemmas 4.5–4.7 and 4.9–4.11. Their numbered aliases
still require `LiteratureTheorems`.

## Final TeX label changes

| Current TeX label | Old proof-comment key | PDF / TeX number |
|---|---|---|
| `prob:Bollobas` | `thm:Bollobas` | 1.1 |
| `lem:path-fan-equivalence` | `lem:cycle-PF-equivalence` | 3.1 |
| `cons:split-construction` | `thm:lower-S` | 3.3 |
| `lem:join-term-linear-range` | `lem:S-terminal` | 3.6 |
| `claim:F_k(n)-merge` | `claim:h_k(n)-merge` | Claim 3.1 |
| `lem:exterior-edge-bound` | `lem:Ma-Ning-e(G)` | 4.8 |
| `claim:increment-properties` | `claim:Sk-linear-increment` | Claim 5.1 |

The old `claim:ext-rich-edge-bound` has no matching numbered environment in
the final TeX. Its full edge bound remains proved by `ext_rich_edge_bound`.
