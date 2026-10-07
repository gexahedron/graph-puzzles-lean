# Factorisations of hypohamiltonian and permutation snarks

[Read the paper](unique_factorisation_snarks.pdf) or its
[self-contained TeX source](unique_factorisation_snarks.tex).
The supplied title, date (6 October 2026) and author attribution are preserved.

The main results give a unique multiset of cyclically five-edge-connected
factors, up to isomorphism and with multiplicities, for hypohamiltonian
snarks, permutation snarks and their intersection. Every intermediate
factor remains in the relevant class.

## Paper and Lean

Import `GraphPuzzles.Claims.SnarkFactorisation`. Names in the following table
are in `GraphPuzzles.Claims`, unless qualified otherwise.

| Paper statement | Lean declaration |
| --- | --- |
| Theorem 1.1: hypohamiltonian factorisation | `hypohamiltonian_factorisation` |
| Theorem 1.2: permutation factorisation | `permutation_factorisation` |
| Corollary 1.3: hypohamiltonian permutation factorisation | `hypohamiltonian_permutation_factorisation` |
| Intermediate factors in Theorem 1.1 | `hypohamiltonian_factor_step` |
| Intermediate factors in Theorem 1.2 | `permutation_factor_step` |
| Intermediate factors in Corollary 1.3 | `hypohamiltonian_permutation_factor_step` |
| Lemma 3.2: Hamilton-cycle descent in a dot product | `GraphPuzzles.LoopMultigraph.DotProduct.descent` |
| Theorem 4.3: the factorisation criterion | `factorisation_criterion` |
| Lemma 5.1: a four-cut uses two edges of each rim | `GraphPuzzles.FinGraph.IsPermGraph.cycSep_structure` |
| Lemma 5.1: colourable shore poles and permutation completions | `GraphPuzzles.FinGraph.goodClass_permutation` |

The combined factorisation statements include existence, class membership,
terminal connectivity and uniqueness. `Multiset.Rel` matches the factors
by graph isomorphism without discarding multiplicities. `Step` is the
canonical decomposition along a cycle-separating four-edge cut.
`Chain` recursively decomposes both factors until neither admits a step.

The class predicates are `GraphPuzzles.FinGraph.IsHypohamiltonianSnark`,
`IsPermutationSnark` and `IsHPSnark`. The hypohamiltonian predicate includes
closedness, cubicity, non-colourability, hypohamiltonicity and a lower order
bound of six. Its bicriticality, girth and cyclic connectivity are proved.
The permutation predicate requires a closed cubic uncolourable graph with
two induced spanning rims and their matching; girth, cyclic connectivity,
colourable shore poles and closure are proved. Bicriticality is not an
assumption of the permutation result.

For terminal class members, `∀ X, ¬ H.CycSep X` expresses the absence of a
cycle-separating four-edge cut. The good-class proofs already establish
cyclic four-edge-connectivity, so terminal factors are cyclically
five-edge-connected in the paper's sense. The one-step closure results
apply repeatedly to every intermediate factor.

The good-class criterion and its atom/diamond argument are formalized in
`Factorization/FactorSystem.lean`, `FactorChain.lean`, `FactorMain.lean` and
their imports. The bicritical prerequisites are formalized here, rather
than supplied as external mathematical assumptions. The standalone
dot-product descent proof uses the endpoint graph model; the class closure
proof also carries out Hamilton-cycle descent for the canonical finite-set
completions.

The elementary order-counting and residue observations in Section 6 of the
paper are not exposed as separate Lean theorems in this release.

## Checking

From the repository root:

```bash
LEAN_NUM_THREADS=1 lake --wfail build
LEAN_NUM_THREADS=1 lake --wfail build GraphPuzzles.Audit
LEAN_NUM_THREADS=1 lake env lean -j1 -M4096 GraphPuzzles/Audit.lean
LEAN_NUM_THREADS=1 lake env lean -j1 -M4096 checks/SnarkFactorisation.lean
python3 tools/publication.py check --public-tree
```

The new audit module checks the exact standard axiom lists of 33 result
and intermediate declarations. The statement check includes all three
classes, intermediate closure and dot-product descent with independent
vertex and edge universes. See the [formalization guide](../../GraphPuzzles/README.md)
and [verification record](../../VERIFICATION.md) for the full release checks.

## Paper build

The TeX source contains its bibliography and margin-reference definitions
inline and compiles with pdfLaTeX. The included PDF is the matching local
build of the supplied source. Its full margin references are visible,
printable and linked; body text and the end bibliography remain selectable.
