# v0.5.0 — Oriented five-cycle double covers of snarks with colouring defect three

Publishes **Graph Puzzles III.3-preview: Oriented five-cycle double covers
of snarks with colouring defect three**, together with its exact TeX/PDF
and Lean proofs.

For every chosen optimal matching triple in a snark of colouring defect
three, an oriented five-cycle double cover contains that triple's entire
hexagonal core as one indexed member. Every edge occurs in exactly two
directed even subgraphs, with opposite directions.

The core characterization, auxiliary orientations, ordered-pair criterion,
sign-word table and both vertex cases are proved in Lean. Import
`GraphPuzzles.Claims.OrientedFiveCycleDoubleCover` for the paper statements.
The [paper-to-Lean guide](papers/defect-three-oriented-five/README.md)
explains the hypotheses and construction.

Earlier proof modules and paper files are retained. The release includes
the reviewed source archive, standalone TeX and PDF. The PDF is also on
[GitHub Pages](https://gexahedron.github.io/graph_theory/defect3_oriented_5cdc.pdf).

# v0.4.0 — Four perfect matchings for snarks with a two-circuit 2-factor

Publishes **Graph Puzzles IV.2-preview: Four perfect matchings for snarks
with a two-circuit 2-factor**, together with its exact TeX/PDF and Lean proofs.

For a snark other than the Petersen graph and any chosen two-circuit
2-factor, the matching complementary to that factor belongs to a cover
by four perfect matchings. Chords are allowed. The perfect matching index
is exactly four, and the result includes every permutation snark other
than the Petersen graph.

The exported proof includes proofs of the Campos–Lucchesi and
Karabáš–Máčajová ingredients and their reviewed prerequisites. Import
`GraphPuzzles.Claims.TwoCircuitFourMatchings` for the paper statements.
The [paper-to-Lean guide](papers/two-circuit-four-matchings/README.md) gives
the hypotheses and theorem map.

Earlier proof modules and paper files are retained. A shared degree-counting
lemma was separated from private hexagon/oriented-cover constructions.

Release assets include the reviewed source archive, standalone TeX, and PDF.
The PDF is also available on
[GitHub Pages](https://gexahedron.github.io/graph_theory/two_circuit_four_perfect_matchings.pdf).

# Version 0.3.0: Factorisations of hypohamiltonian and permutation snarks

This release accompanies *Graph Puzzles IV.1-preview: Factorisations of
hypohamiltonian and permutation snarks*.

- Unique multisets of cyclically five-edge-connected factors for hypohamiltonian
  snarks, permutation snarks and hypohamiltonian permutation snarks, including multiplicities.
- Preservation of each class at every decomposition along a cycle-separating four-edge cut.
- Hamilton-cycle descent, the good-class criterion, and the atom/diamond and bicritical prerequisites.
- The paper PDF and self-contained TeX source, with their original title, date and attribution.
- A paper-to-Lean guide, statement checks and 33 new exact axiom guards.

The existing Sabidussi, general CDC and strong-five results remain available.
The dependency versions are unchanged. Section 6's order-counting and residue
observations are not separate Lean theorems in this release.

Files `unique_factorisation_snarks.pdf` and `unique_factorisation_snarks.tex`
are available with the source archive as release assets. The PDF is also
[available on GitHub Pages](https://gexahedron.github.io/graph_theory/unique_factorisation_snarks.pdf).

See the [paper guide](papers/factorisations/README.md) and
[verification record](VERIFICATION.md) for precise statements and checks.
