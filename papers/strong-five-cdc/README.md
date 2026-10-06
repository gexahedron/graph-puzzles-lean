# Strong five-cycle double covers: paper and Lean

This directory contains the exact supplied source
[strong_five_cycle_double_covers.tex](strong_five_cycle_double_covers.tex)
and its [matching 18-page PDF](strong_five_cycle_double_covers.pdf).
The title is *Graph Puzzles III.2-preview: Strong five-cycle double covers*,
dated 6 October 2026. The supplied attribution is preserved.

Import `GraphPuzzles.Results.StrongFiveCycleDoubleCover` for the underlying
proofs or `GraphPuzzles.Claims.StrongFiveCycleDoubleCover` for the statements
below. All names in the table are under `GraphPuzzles.Claims`.

| Paper | Lean declaration | Conclusion |
| --- | --- | --- |
| Theorem 1.1, prescribed circuit | `prescribed_circuit_five_iff` | Entire-member 5CDC iff `G − V(C)` is properly 3-edge-colourable |
| Theorem 1.2, critical case | `critical_entire_five` | Every prescribed circuit is an entire member |
| Theorem 1.2, permutation case | `permutation_entire_five` | Every prescribed circuit is an entire member |
| Theorem 1.3, induced hexagon | `hexagonal_core_strong_five` | Every prescribed circuit is a component of a member |
| Corollary 1.4, defect three | `defect_three_strong_five` | Every prescribed circuit is a component of a member |

`critical_strong_five` and `permutation_strong_five` give the standard
component conclusions from the stronger entire-member theorems.

## Conventions and hypotheses

The endpoint multigraph model distinguishes vertices and labelled edges,
allows parallel edges, and counts a loop twice in degree. `OrdinaryCircuit`
is nonempty, connected and 2-regular. A `CycleDoubleCover 5` has five indexed
even edge sets, including empty members when padding is needed. Repeated
members retain their multiplicities. These are the paper's conventions.

`HasStrongCycleDoubleCover 5` means each circuit is a **component** of some
member. `HasEntireLayerStrongCycleDoubleCover 5` means the circuit is the
**entire member**. The defect-three corollary asserts the first property.

`IsCritical` asks for a proper colouring after deleting the two ends of
each edge. Thus the critical theorem applies directly to the paper's
critical snarks, without a girth condition or a separate factorization model.
The permutation theorem uses a spanning `TwoCircuitFactor` whose two rims
are induced, together with cubicity and looplessness. It applies to all
permutation snarks, without requiring girth exactly five.

`IsSnark` records connectivity, bridgelessness, looplessness, cubicity and
failure of a proper 3-edge-colouring. `HasColoringDefect 3` supplies an
attaining triple of perfect matchings with exactly three uncovered edges,
and a lower bound of three for every triple. It is the numerical minimum
condition, rather than an assumed hexagon or an auxiliary colouring.

The critical, prescribed-circuit and hexagon Lean proofs do not need the
paper's connectivity assumption. In particular, the published statements
follow by specialization. Endpoint reversals are handled explicitly when
extracting a hexagon from the optimal triple.

## Proof locations

| Construction | Source |
| --- | --- |
| Circuit extension and component-wise parity balancing | `GraphPuzzles/CycleCovers/CircuitExtension.lean` |
| Deleted-vertex colouring extension and critical case | `GraphPuzzles/CycleCovers/CircuitExtensionCorollaries.lean` |
| Exact converse and equivalences | `GraphPuzzles/CycleCovers/CircuitExtensionExact.lean` |
| Permutation-graph complement colouring | `GraphPuzzles/CycleCovers/TwoCircuitFactor.lean` |
| Numerical defect and optimal matching triple | `GraphPuzzles/DefectThree/MatchingTriple{,Structure}.lean` |
| Optimal triple supplies a hexagonal exterior colouring | `GraphPuzzles/DefectThree/DefectThreeCore.lean` |
| Disjoint circuit, toggling, restoration and recolouring | `GraphPuzzles/DefectThree/HexagonDisjointFive.lean` |
| Meeting circuit and assembly of the hexagon theorem | `GraphPuzzles/DefectThree/HexagonStrong.lean` |
| Numerical defect-three strong-five conclusion | `GraphPuzzles/DefectThree/StrongFive.lean` |

For Theorem 1.1, the exact file states both the deleted-vertex equivalence
(`OrdinaryCircuit.exists_fiveCycleDoubleCover_iff_properOff`) and the
deleted-edge equivalence
(`OrdinaryCircuit.exists_fiveCycleDoubleCover_iff_complementColoring`).
The paper also presents that edge colouring as a nowhere-zero
`F₂²`-flow on `G/C`; this export uses the complement-colouring representation
and does not introduce a separate quotient-graph API for that presentation.

The defect-three extraction proves the required direction of KMNS Theorem
3.3 using `MatchingTriple.IsOptimal.exists_hexagonalCore` and
`HasColoringDefect.hasHexagonalCore`. It is a proved dependency of Corollary
1.4. The restoration argument internally constructs six layers and merges
two disjoint layers to obtain five; this intermediate construction belongs
to the five-cover proof.

`GraphPuzzles/Audit/StrongFiveCycleDoubleCover.lean` checks the exact axiom
lists of the seven statement declarations and seven underlying endpoints,
including the numerical defect-to-hexagon construction.
