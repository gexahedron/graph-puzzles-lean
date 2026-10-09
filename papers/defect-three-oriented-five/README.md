# Oriented five-cycle double covers of snarks with colouring defect three

This directory contains **Graph Puzzles III.3-preview**, its standalone
[TeX source](defect3_oriented_5cdc.tex) and matching [PDF](defect3_oriented_5cdc.pdf).
The supplied title, date (30 August 2026), author attribution and typography
are preserved.

Import `GraphPuzzles.Claims.OrientedFiveCycleDoubleCover`.
`LoopMultigraph.IsSnark` records connectedness, bridgelessness, cubic degree,
absence of loops, and non-three-edge-colourability. `HasColoringDefect 3`
means that an optimal triple of perfect matchings has exactly three uncovered
edges. Optimality minimizes the number of uncovered edges over all triples.

| Paper statement or construction | Lean declaration |
| --- | --- |
| Definition 1.1: five directed even subgraphs, double coverage in opposite directions | `LoopMultigraph.OrientedCycleDoubleCover` |
| Lemma 1.2: ordered-pair criterion | `LoopMultigraph.exists_orientedCover_of_labels` |
| Theorem 2.1: for every chosen optimal triple, its entire core is one indexed member | `Claims.defect_three_oriented_five_prescribed_core` |
| Numerical oriented-five existence | `Claims.defect_three_oriented_five` |
| Structural hexagonal-core version | `Claims.hexagonal_core_oriented_five` |
| Core characterization retaining the chosen triple | `MatchingTriple.IsOptimal.exists_hexagonalCore_eq_core` |
| Three auxiliary orientations | `Hexagon.ExteriorColoring.exists_orientations` |
| Finished five-cover containing the hexagon | `Hexagon.ExteriorColoring.exists_oriented_five_cover` |
| Sign-word table and reversal | `LoopMultigraph.signTable`, `LoopMultigraph.signTable_flip` |
| Exterior and core vertex cases | `LoopMultigraph.balance_exterior`, `LoopMultigraph.balance_core'` |
| Cover transport retaining the prescribed member | `EndpointIso.orientedCycleDoubleCover_contains` |

All declarations are in `GraphPuzzles`; the matching, hexagon and endpoint
isomorphism namespaces in the table are under `LoopMultigraph`.
The core is the set of edges whose matching multiplicity differs from one.
`Contains` means equality with an entire indexed member, not just containment
as a component. The result quantifies over every optimal triple; it does not
choose a single preferred triple. Auxiliary orientations are constructed
internally, and no orientation hypothesis is assumed by the headline theorem.

Lemma 1.2 is formalized with the more general local equality of outgoing
and incoming label counts; a directed triangle satisfies that condition.
The construction checks the finite sign-word table and both local balance
cases directly in Lean. For the auxiliary orientations, the formal proof
uses a binary parity/T-join construction and the same Kempe-colouring
obstruction as the paper, avoiding a separate suppressed-path representation.
The numerical hexagonal-core characterization is proved in the library,
rather than supplied as an additional assumption.
The paper's final observation that all five members are nonempty is not a
separate Lean declaration in this release.

The source and adjacent PDF were frozen byte-for-byte from the current paper
directory. The source digest matches its successful latexmk build record.
PDF margin references remain visible, printable and clickable while body and
bibliography text remain selectable. See [verification](../../VERIFICATION.md).
