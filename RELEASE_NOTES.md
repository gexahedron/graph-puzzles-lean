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
