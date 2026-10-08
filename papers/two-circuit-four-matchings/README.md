# Four perfect matchings for snarks with a two-circuit 2-factor

This directory contains the supplied paper **Graph Puzzles IV.2-preview**,
its standalone [TeX source](two_circuit_four_perfect_matchings.tex), and the
matching [PDF](two_circuit_four_perfect_matchings.pdf). The title, date
(6 October 2026), author attribution and typography are preserved.

The graph hypotheses in `IsProperSnark` are connectedness, bridgelessness,
simplicity, cubic degree, girth at least five, cyclic edge-connectivity at
least four, and non-three-edge-colourability. `IsPetersen` is graph isomorphism
to the explicitly labelled Petersen graph. `TwoCircuitFactor` records the
two spanning, vertex-disjoint circuit components. Its complementary
matching may have chords.

| Paper statement | Lean declaration |
| --- | --- |
| Theorem 1.1: four-cover retaining the specified complementary matching | `Claims.two_circuit_four_matchings_prescribed` |
| Theorem 1.1: perfect matching index exactly four | `Claims.two_circuit_perfect_matching_index_four` |
| Corollary 1.2: permutation snarks, for each induced two-circuit factor | `Claims.permutation_four_matchings` |
| Lemma 2.1: matching-covered contraction / hub lemma | `LoopMultigraph.isMatchingCovered_of_hub` |
| Lemma 2.2: snarks are bricks | `LoopMultigraph.isBrick_of_properSnark` |
| Theorem 2.3: Campos–Lucchesi | `Claims.campos_lucchesi` |
| Lemma 2.4: odd circuits and separating cross-spoke cut | `TwoCircuitFactor.odd_of_not_colourable`, `TwoCircuitFactor.isSeparatingCut_A` |
| Theorem 3.1: Karabáš–Máčajová's Hamiltonian three-pole theorem | `Claims.karabas_macajova` |
| Lemma 3.2: the three-spoke cover | `LoopMultigraph.kmThreeSpokes` |
| Section 4: odd-path reduction and cover lifting | `TwoCircuitFactor.exists_fourCover_of_three_crossing` |

All declarations above are in the `GraphPuzzles` namespace. The cover is
an indexed family of perfect-matching occurrences; the first member is
exactly the matching complementary to the chosen factor. The exact index
statement excludes every smaller cover size, including zero. The
permutation corollary assumes that both factor circuits are induced.

Both cited matching-theory ingredients are proved in the exported code.
No Campos–Lucchesi, Karabáš–Máčajová, or bicriticality hypothesis is supplied
by the reader. Original papers cited in the bibliography are referenced
by their links; local literature copies are not part of the release.

The source and adjacent PDF were frozen byte-for-byte from the current
paper directory. The source digest matches its successful latexmk build
record. PDF margin references remain visible, printable and clickable,
while body and bibliography text remain selectable. See
[the verification record](../../VERIFICATION.md) for the checks.
