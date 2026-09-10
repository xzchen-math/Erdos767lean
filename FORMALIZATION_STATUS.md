# Formalization status

Final PDF synchronization (2026-09-10): use `PAPER_LEAN_MAP.md` for current
numbering and `VERIFICATION_REPORT.md` for current verification status.
The stable theorem names and legacy label keys below remain valid.

Source manuscript: `/Users/vccc/Desktop/CN260601/ErdosProblem767.tex`
(latest version, checked 2026-08-14).

Snapshot: `manuscript/ErdosProblem767.tex`  
SHA-256: `b3048490a604d3b9d794def269d558bbfef518c37cc55a3fc03bcb924ea198ac`

## Lean-checked without `sorry`, `admit`, or project-declared axioms

- Arithmetic definitions `A`, `t`, `p`, `h`.
- The complete finite check in `lem:small-c-arithmetic` and supporting
  arithmetic results listed in `Erdos767/Arithmetic.lean`.
- Mathlib-compatible definitions of paths, cycles, and chords.
- `HasPathFan`: a center `x` and an `IsPath` avoiding `x`, with at least `ell`
  neighbors of `x` on the path.
- `CenteredCycle`: the actual cycle obtained from `x-u-P-v-x`.
- `incidentChordVertices` and `incidentChordCount`, defined using Mathlib's
  `Walk.IsChord`.
- `cycle_pathFan_equivalence`, corresponding to
  `lem:cycle-PF-equivalence` in the manuscript.
- `PathFanFree` and the general theorem that maximum degree at most `d`
  excludes `PF_(d+1)`.
- The cyclic jump graph, the half-shift matching, the nearly regular graph,
  and the split graph from the lower-bound subsection.
- The cyclic core degree bound, the fact that the half-shift graph is a
  matching, and `cyclicDegreeGraph_degree_le`.
- `nearlyRegularGraph_pathFanFree`: the nearly regular construction contains
  no `PF_(k+2)`.
- `circulant_degree_eq` and `circulant_card_edgeFinset_eq`: the cyclic core has
  its exact regular degree and edge count when its target degree is below the
  group order.
- `halfShiftMatching_edgeFinset_eq` and
  `halfShiftMatching_card_edgeFinset`: the half-shift edges are indexed
  bijectively by `Fin (n/2)`, so there are exactly `floor(n/2)` of them.
- `circulant_disjoint_halfShiftMatching`: in the odd case, the short cyclic
  edges and long matching edges are disjoint.
- `nearlyRegularGraph_card_edgeFinset_eq_t`: for `n ≥ k+2`, the nearly regular
  graph has exactly `t k n = floor((k+1)n/2)` edges.
- `ncard_edgeSet_sum_eq`: the edge count of a graph disjoint sum is additive.
- `completeBipartiteGraph_card_edgeFinset`: the complete bipartite cross graph
  on `Fin a ⊕ Fin b` has exactly `a*b` edges.
- `sum_disjoint_completeBipartiteGraph`: internal summand edges and complete
  bipartite cross edges are disjoint.
- `splitGraph_card_edgeFinset_eq_splitTerm` and
  `splitGraph_card_edgeFinset_eq`: for every `a ∈ A_k`, the split graph has
  exactly `a(n-a) + floor(a(k+1-a)/2)` edges.
- The split graph's left, right, and cross adjacency laws, including
  `splitGraph_degree_right`, which proves that every right-side vertex has
  degree exactly `a`.
- `splitGraph_pathFanFree`: the split construction is `PF_(k+2)`-free for
  every manuscript parameter `k ≥ 1` and `a ∈ A_k`.
- Every labeled lemma in Section 3:
  - `cycle_pathFan_equivalence` (`lem:cycle-PF-equivalence`);
  - `linear_bound_real` (`lem:linear-bound`), including the exact floor and
    ceiling of `(1 + sqrt 3 / 2)(k+1)`;
  - `p_eq_terminal` (`lem:S-terminal`);
  - `h_eq_piecewise_real` (`lem:B-equals-f`);
  - `merge_ineq_both` (`lem:merge-ineq`);
  - `cycle_arithmetic_consequences`
    (`lem:cycle-arithmetic-consequences`);
  - `small_c_arithmetic` (`lem:small-c-arithmetic`).
- Integer-only companion interfaces `linear_bound_discrete` and
  `h_eq_piecewise_discrete`, used internally to avoid unnecessary real
  arithmetic in later proofs.
- Chapter 4 foundation layer:
  - `CycleWitness`, `IsLocallyMaximalCycle`, `IsLongestCycle`;
  - `IsLongestCycle.isLocallyMaximal`;
  - `IsHamiltonianConnected`, `IsTwoConnected`;
  - `closureStep`, `IsRClosed`, `closureStep_eq_self_iff`.
- Route-A literature interface (definitions and explicit premises, not proved
  theorems):
  - `cycleClosure`, `IsWGraph`, `IsXGraph`, `IsYGraph`;
  - `IsComponentOutsideCycle`, `IsStrongAttachment`, `edgeSwitch`;
  - the nine proposition-valued external statements packaged by
    `LiteratureTheorems`.
- Route-A Chapter 4 deductions:
  - finite stabilization and closedness of `rClosure`;
  - `cycleCoreClosure` has the correct order and minimum degree at least two;
  - `exceptional_low_degree_or_W` (`lem:exceptional-low-degree-or-W`);
  - `degreeCliqueDichotomy_of_literature` and `maNing_cycle_dichotomy`
    (`lem:Ma-Ning-cycle-dichotomy`);
  - closure changes no outside-cycle adjacency and preserves 2-connectivity
    under edge addition;
  - terminating switching descent and all exterior-component bookkeeping;
  - `switching_terminal_claim_of_literature`
    (`claim:switching-terminal`);
  - `maNing_edge_bound_i_of_literature` and
    `maNing_edge_bound_ii_of_literature` (`lem:Ma-Ning-e(G)`).
- Independently closed Chapter 5 results:
  - `cycle_degree` and `cycle_degree_on_cycle` (`lem:cycle-degree`, including
    its literal arbitrary-cycle/induced-degree statement);
  - `h_eq_t_descends` and the earlier `p_succ_ge_of_eq_splitTerm`
    (`claim:Sk-linear-increment`);
  - `pathFanFree_induce`;
  - `exists_low_degree_of_pathFanFree`;
  - `card_edgeFinset_eq_induce_compl_singleton_add_degree`;
  - `terminal_bound_of_base`, the full longest-path endpoint induction;
  - `terminal_bound`, with `lem:base` explicitly present as a premise.
- Route-A Chapter 5 assembly:
  - `attained_t`, `attained_p`, `attained_h`, and `attained_terminal`;
  - `minimalCounterexample_setup`;
  - `ext_rich_host1_of_literature`, `ext_rich_host2`, and
    `ext_rich_edge_bound` (the three rich-exterior claims);
  - sparse, small-cycle, rich-exterior, and exceptional-case bounds;
  - `base_range_upper_of_literature` and
    `exact_base_range_of_literature` (`lem:base`);
  - `terminal_bound_of_literature` (`lem:terminal`);
  - the complete `k=1` branch `main_k_one_of_three_le`;
  - `main_k_ge_two_of_literature` and the unified
    `main_theorem_of_literature` (`thm:main`).

`Erdos767/Audit.lean` prints the axioms of representative graph and
construction theorems. The paper-specific deductions take the cited results
through an explicit `LiteratureTheorems` argument, rather than global axioms.
The exceptional `(3,8,6)` branch follows the manuscript's combinatorial proof
in `ExceptionalCertificate.lean`: it classifies the two exterior
neighborhoods, checks the displayed long-cycle constructions, and carries out
the exact type-I/type-II chord-incidence count.  No `bv_decide` or generated
compiler-reflection axiom remains in this branch.

## Important representation choice

A cycle with a distinguished center is stored by its center-deleted path. The
theorem `CenteredCycle.walk_isCycle` proves that closing this path produces a
Mathlib `IsCycle`. The chord count is then computed on that actual closed walk,
not stipulated by definition.

## Remaining work outside Route A

Route A is complete. An unconditional Route-B project would additionally
formalize proofs of the nine external literature fields.  The exceptional
finite configuration is already kernel-checked by the paper proof.
