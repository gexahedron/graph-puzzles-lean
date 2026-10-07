# Formalization guide

This page describes the mathematical statements, their Lean entry points,
the source layout, and how to build and check the proofs.

## Results and entry points

| Result | Entry point |
| --- | --- |
| Sabidussi's compatibility conjecture with 4 colours | `GraphPuzzles.Results.Sabidussi` |
| Cycle double covers of finite bridgeless graphs | `GraphPuzzles.Results.CycleDoubleCover` |
| Strong 5-cycle double covers for critical, permutation and colouring-defect-three snarks | `GraphPuzzles.Results.StrongFiveCycleDoubleCover` |
| Unique factorisations of hypohamiltonian, permutation and hypohamiltonian permutation snarks | `GraphPuzzles.Results.SnarkFactorisation` |

Import `GraphPuzzles` for the results together, or import one of the entry
points above. The declarations share the `GraphPuzzles` namespace.

## Sabidussi compatibility

The headline declaration is `GraphPuzzles.LoopMultigraph.sabidussi_theorem`.
Its strengthened colouring conclusion and compatible decomposition use
ordinary nonempty, connected, 2-regular circuits. The dominating-circuit
corollary supplies a five-cycle double cover with the prescribed circuit as
an entire layer.

The [paper](../papers/sabidussi/sabidussi_proof.pdf) accompanies the proof.
The PDF is kept under `papers/sabidussi/`. The original
[sabidussi-lean repository](https://github.com/gexahedron/sabidussi-lean)
remains available independently; this project uses the `GraphPuzzles` module
paths.

## Cycle double covers

The declaration `GraphPuzzles.LoopMultigraph.exists_ordinaryCycleDoubleCover`
covers loops, parallel edges, isolated vertices, disconnected graphs and the
empty graph. Its list retains repeated circuit occurrences and covers each
edge exactly twice. The eight-layer result permits empty or disconnected
layers; decomposing those layers may produce more than eight ordinary
circuits.

The proof uses the pinned
[OpenAI formalization](https://github.com/openai/cdc-lean/tree/577e9d9ea326d520f80672ee69b830bf1d513df5).
This project supplies the bridge to its graph representation, restores loops,
and decomposes the cover into ordinary circuits. The upstream source and
attribution remain in the dependency.

## Strong five-cycle double covers

The [paper](../papers/strong-five-cdc/strong_five_cycle_double_covers.pdf)
and its [exact TeX source](../papers/strong-five-cdc/strong_five_cycle_double_covers.tex)
accompany the proofs. Critical and permutation cubic graphs admit every
prescribed circuit as an **entire member** of a five-cover. For numerical
colouring defect three, the prescribed circuit is a **component** of a
member. The proof constructs the hexagonal core from the numerical defect
hypothesis.

Import `GraphPuzzles.Results.StrongFiveCycleDoubleCover` for the underlying
proofs or `GraphPuzzles.Claims.StrongFiveCycleDoubleCover` for the paper
statements. The [paper-to-Lean guide](../papers/strong-five-cdc/README.md)
lists the theorem names, hypotheses and conventions.
The factorisation release retains these proof sources and paper files unchanged.

The extension proof is in `CycleCovers/CircuitExtension{,Corollaries,Exact}.lean`.
`CycleCovers/TwoCircuitFactor.lean` constructs the permutation-graph colouring;
`CycleCovers/StrongFive.lean` supplies the critical and permutation conclusions.
`DefectThree/StrongFive.lean` combines the optimal matching triple and hexagon
construction to obtain the numerical defect-three conclusion.

`CycleCovers/StrongProperties.lean` defines strong containment.
`CycleCovers/CoverTransportBasic.lean` transports ordinary covers through
vertex and edge relabelling and endpoint reversals.

## Snark factorisations

The [paper](../papers/factorisations/unique_factorisation_snarks.pdf) and its
[TeX source](../papers/factorisations/unique_factorisation_snarks.tex) accompany
proofs of unique factorisation for hypohamiltonian snarks, permutation snarks
and their intersection. Decompositions use cycle-separating four-edge cuts.
Terminal factors are cyclically five-edge-connected and remain in the
original class. Uniqueness compares multisets up to graph isomorphism,
including repeated isomorphism types.

Import `GraphPuzzles.Results.SnarkFactorisation` for the proofs or
`GraphPuzzles.Claims.SnarkFactorisation` for the combined paper statements.
The [paper-to-Lean guide](../papers/factorisations/README.md) lists the
statements, intermediate closure proofs and the formalization scope.
The permutation theorem proves its class hypotheses directly; it does not
assume the conjecture that permutation snarks are bicritical.

`Factorization/FactorChain.lean` proves abstract multiset uniqueness;
`Factorization/FactorMain.lean` applies it to a good class of finite graphs.
The `Hypohamiltonian/` and `Permutation/` subdirectories prove the class
instances and descent lemmas. The `Diamond/` subdirectory proves the
commuting refinements used by the atom argument. Bicritical factorisation
and its local structural lemmas are included as prerequisites.

## Graph model and source layout

The graph model allows labelled parallel edges and loops; each loop
contributes two incidences to degree. Vertices and edges have independent
types. `Graph/Model.lean` contains the trusted graph and circuit data.
The factorisation proofs also use `FinGraph`, which represents finite
labelled graphs and multipoles by finite sets of natural-number labels.
Its Hamilton cycles, proper colourings, cuts, completions and isomorphisms
are defined in `FinGraph/`.

| Directory | Contents |
| --- | --- |
| `Core/` | Four-colour algebra, local patterns, parity, balancing, cyclic words and finite counting |
| `Graph/` | Endpoint graph model, boundaries, connectivity, bridgelessness, relabelling and the cyclic-word bridge |
| `Circuits/` | Ordinary circuits, Euler traversals and parity colourings |
| `CycleCovers/` | Dominating-circuit covers, exact circuit extension, strong five-covers and the general CDC bridge |
| `DefectThree/` | Matching triples, hexagonal core extraction and strong five-covers |
| `FinGraph/` | Finite graphs, multipoles, colourings, Hamilton cycles, completions and isomorphisms |
| `Poles/` | The Kempe-walk construction used by four-pole colourings |
| `Factorization/` | Atom and diamond arguments, class closure and unique terminal factors |
| `Results/` | Imports for the mathematical results |
| `Claims/` | Statements with explicit graph hypotheses and conclusions |

## Build and verify

Lean is pinned to `v4.31.0`, Mathlib to
`9a9483a92959bc92bd6a60176dd1fe597298c1f8`, and `cdc_lean` to
`577e9d9ea326d520f80672ee69b830bf1d513df5`.

```bash
lake exe cache get
LEAN_NUM_THREADS=1 lake --wfail build
LEAN_NUM_THREADS=1 lake --wfail build GraphPuzzles.Audit
LEAN_NUM_THREADS=1 lake env lean -j1 -M4096 GraphPuzzles/Audit.lean
LEAN_NUM_THREADS=1 lake env lean -j1 -M4096 checks/CycleDoubleCover.lean
LEAN_NUM_THREADS=1 lake env lean -j1 -M4096 checks/StrongFiveCycleDoubleCover.lean
LEAN_NUM_THREADS=1 lake env lean -j1 -M4096 checks/SnarkFactorisation.lean
LEAN_NUM_THREADS=1 lake --wfail build SabidussiSolution
python3 tools/publication.py check --public-tree
```

`lake-manifest.json` records the dependency revisions. Use `lake update` only
when intentionally changing those pins. A missing dependency cache can
require a larger local build; inspect available RAM and disk first and use
one Lean worker.

`Audit.lean` checks the exact axioms of the result declarations and
intermediate constructions. Its guards permit only `propext`,
`Classical.choice`, and `Quot.sound`. The [verification record](../VERIFICATION.md)
describes the checks performed for this release. The exported files and
their import closure are recorded in `publication/public-manifest.json`.

`SabidussiChallenge.lean` is the trusted Comparator specification and contains
an intentional proof placeholder. `SabidussiSolution.lean` supplies the
checked proof. The placeholder is outside the production library and its
axiom audit.

## Licensing and citation

Code is licensed under [Apache-2.0](../LICENSE). Cite the individual papers
for their mathematical results; `CITATION.cff` describes the software.
