# Public source guide

| Directory | Contents |
| --- | --- |
| `Core/` | Four-colour algebra, local patterns, parity, balancing and cyclic words |
| `Graph/` | Endpoint graph model, bridgelessness, graph relabelling and the cyclic-word bridge |
| `Circuits/` | Ordinary circuits and Euler traversals |
| `CycleCovers/` | Dominating-circuit covers and the general CDC bridge |
| `Results/` | Separate imports for the two proof families |
| `Claims/` | Checked statements with explicit graph hypotheses and conclusions |

`Graph/Model.lean` contains the trusted graph and circuit data.
`Audit.lean` checks the exact axioms of the public endpoints and critical
intermediate constructions. Only `propext`, `Classical.choice`, and
`Quot.sound` are permitted by these guards.

Module paths describe topics, while declarations use the shared `GraphPuzzles`
namespace. Import `GraphPuzzles.Results.Sabidussi` or
`GraphPuzzles.Results.CycleDoubleCover` for one family, or `GraphPuzzles` for
both. The full build instructions are in [README.md](../README.md).
