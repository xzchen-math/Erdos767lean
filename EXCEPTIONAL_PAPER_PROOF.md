# Exceptional `(3,8,6)` case: manuscript-to-Lean map

Final PDF synchronization (2026-09-10): use `PAPER_LEAN_MAP.md` for current
numbering and `VERIFICATION_REPORT.md` for current verification status.
The stable theorem names and legacy label keys below remain valid.

The executable proof is in `Erdos767/ExceptionalCertificate.lean`.  The
arbitrary-labelled graph is transported to `Fin 8` in
`Erdos767/ExceptionalCase.lean` and then passed to
`exceptional_fin8_impossible_paper`.

| Manuscript proof step | Lean lemma |
|---|---|
| Split the 17 edges into 11 inside the six-cycle, edges to the two exterior vertices, and the possible exterior edge | `edge_count_finset_decomposition`, `outside_sixSet_edge_card`, `crossing_sixSet_card_eq_cycleNeighbors_add` |
| If the two exterior vertices are adjacent, their cycle-neighborhood sizes sum to 5 and one has size 3 | adjacent branch of `exceptional_fin8_impossible_paper` |
| A 3-set and a 2-set on a six-cycle contain a pair at cyclic distance at most two | `short_oriented_pair_of_card_three_two` |
| Replacing the short cycle arc by the path through the exterior edge gives a 7- or 8-cycle | `long_cycle_of_adjacent_outside_short_pair` |
| Hence the exterior vertices are nonadjacent and both have three neighbors on the cycle | nonadjacent branch of `exceptional_fin8_impossible_paper` |
| No exterior neighborhood contains consecutive cycle vertices | `no_consecutive_cycle_neighbors` |
| A size-three subset of a six-cycle with no consecutive pair is one of the two alternating triples | `independent_cycle_triple_classification` |
| Different alternating triples give the displayed Hamilton 8-cycle | `opposite_alternating_neighbors_give_eight_cycle` |
| A chord inside the complementary alternating triple gives the displayed 7-cycle | `odd_triple_chords_forbidden`, `even_triple_chords_forbidden` |
| The six induced degrees sum to 22 because there are 11 induced edges | `six_cycle_degree_sum_eq_twenty_two` |
| There are five chords; with `r` type-I and `s` type-II chords, `r+s=5`, `s≤3`, hence `r≥2`; their incidence at the common triple is `2r+s=r+5≥7`, but the degree bound permits at most 6 chord incidences | `even_common_triple_incidence_contradiction`, `odd_common_triple_incidence_contradiction` |

`decide` is used only for closed, very small facts such as distinctness of
listed `Fin 8` vertices and membership in fixed finite sets.  It is not used
to enumerate graphs or discharge the exceptional theorem wholesale.  There
is no `bv_decide` invocation.
