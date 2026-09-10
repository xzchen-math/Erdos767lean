# Chapter 4–5 Lean status (Route A)

Final PDF synchronization (2026-09-10): use `PAPER_LEAN_MAP.md` for current
numbering and `VERIFICATION_REPORT.md` for current verification status.
The stable theorem names and legacy label keys below remain valid.

The Route-A formalization is complete: the cited literature results are
explicit fields of `LiteratureTheorems`, and every paper-specific deduction in
Chapters 4 and 5 is proved from that structure. The project does **not** claim
to prove the cited literature theorems themselves.

## Chapter 4

| Manuscript item | Lean status | Lean item |
|---|---|---|
| `W`, `X`, `Y` graph families | defined and supporting facts proved | `IsWGraph`, `IsXGraph`, `IsYGraph`, `wGraphFromPartition` |
| `thm:Dirac-cycle` | Route-A premise | `LiteratureTheorems.diracCycle` |
| `thm:MN-exterior-stability` | Route-A premise | `LiteratureTheorems.maNingExteriorStability` |
| `lem:exceptional-low-degree-or-W` | proved | `exceptional_low_degree_or_W` |
| `lem:closure-preserves-local-maximality` | Route-A premise | `LiteratureTheorems.closurePreservesLocalMaximality` |
| `lem:Ma-Ning-non-ha` | Route-A premise | `LiteratureTheorems.maNingNonHamiltonianConnected` |
| `lem:Ma-Ning-degree` | Route-A premise | `LiteratureTheorems.maNingDegree` |
| `lem:Ma-Ning-cycle-dichotomy` | proved from Route-A premises | `maNing_cycle_dichotomy` |
| `lem:Ma-Ning-strong-attachment` | Route-A premise | `LiteratureTheorems.maNingStrongAttachment` |
| `lem:Fan-Lv-Wang-switch` | Route-A premise | `LiteratureTheorems.fanLvWangSwitch` |
| `lem:EG-path` | Route-A premise | `LiteratureTheorems.erdosGallaiPath` |
| `claim:switching-terminal` | proved from Route-A premises | `switching_terminal_claim_of_literature` |
| `lem:Ma-Ning-e(G)` (i) | proved from Route-A premises | `maNing_edge_bound_i_of_literature` |
| `lem:Ma-Ning-e(G)` (ii) | proved from Route-A premises | `maNing_edge_bound_ii_of_literature` |

The supporting proof chain includes finite closure stabilization, the closed
cycle core, switching descent, exterior connected-component decomposition,
longest paths inside components, strong attachments, cycle-successor spacing,
and exact inside/crossing/outside edge accounting.

## Chapter 5

| Manuscript item | Lean status | Lean item |
|---|---|---|
| `lem:cycle-degree` | proved | `cycle_degree_on_cycle` |
| `claim:Sk-linear-increment` (i) | proved | `p_succ_ge_of_eq_splitTerm` |
| `claim:Sk-linear-increment` (ii) | proved | `h_eq_t_descends` |
| `lem:minimal-counterexample-setup` | proved from Route-A premises and the strong-induction hypothesis | `minimalCounterexample_setup` |
| cycle-dichotomy case (i) edge bound | proved | `cycle_case_i_edge_bound` |
| cycle-dichotomy case (ii), inside/sparse/small cases | proved | `cycle_case_ii_inside_bound`, `cycle_case_ii_sparse_edge_bound`, `cycle_case_ii_small_edge_bound_or_exception` |
| exceptional `(k,n,c)=(3,8,6)` case | proved by the manuscript's stepwise combinatorial classification | `exceptional_fin8_impossible_paper`, `exceptional_case_contradiction` |
| `claim:ext-rich-host1` | proved from Route-A exterior stability | `ext_rich_host1_of_literature` |
| `claim:ext-rich-host2` | proved | `ext_rich_host2` |
| `claim:ext-rich-edge-bound` | proved | `ext_rich_edge_bound` |
| rich exterior subcase | proved | `cycle_case_ii_rich_edge_bound` |
| `lem:base` | proved from Route-A premises | `base_range_upper_of_literature` |
| exact base range | proved, including attaining constructions | `exact_base_range_of_literature` |
| `lem:terminal` | proved from Route-A premises | `terminal_bound_of_literature` |
| `thm:main`, `k=1` | proved from the Pósa Route-A premise | `main_k_one_of_three_le` |
| `thm:main`, `k≥2` | proved from Route-A premises | `main_k_ge_two_of_literature` |
| complete `thm:main` | proved from Route-A premises | `main_theorem_of_literature` |

`main_theorem_of_literature` has conclusion
`ExactUniversalEdgeBound (k+2) n (h k n)`. In the admissible range,
`h k n` is exactly the maximum of the nearly-regular and split-construction
edge counts displayed in the manuscript.

## Build and trust boundary

- `lake build` succeeds for the complete project.
- The checked project sources contain no `sorry`, `admit`, or global project
  `axiom` declaration.
- The nine cited results are hypotheses supplied through a value
  `lit : LiteratureTheorems`; they are not silently asserted as proved.
- The exceptional case contains no Boolean adjacency-matrix enumeration and
  no `bv_decide`.  Its named Lean lemmas mirror the paper's exterior-edge
  exclusion, alternating-triple classification, explicit 7/8-cycle
  constructions, and type-I/type-II chord-incidence contradiction.
- Standard Lean/Mathlib foundational dependencies such as `propext`,
  `Classical.choice`, and `Quot.sound` also appear in `#print axioms` output.

Thus the precise claim is: **Chapters 4 and 5 are formally derived in Lean
under the explicit Route-A literature premises; the exceptional finite case
is checked by a kernel-verified formalization of the manuscript proof.**
