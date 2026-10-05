# Cycle double covers of finite bridgeless multigraphs

Start with [`Theorem.lean`](Theorem.lean). The public ordinary-circuit result is
`LoopMultigraph.exists_ordinaryCycleDoubleCover`, also packaged as
`LoopMultigraph.cycleDoubleCover : CycleDoubleCoverTheorem`. The explicit list
statement is `Claims.cycle_double_cover`.

The only graph hypothesis is `H.IsBridgeless`. Vertex and edge types are finite
and may live in different universes. Loops, parallel edges, isolated vertices,
disconnected graphs and empty graphs are included. A circuit is a nonempty
connected edge set with degree two at each supported vertex. The output list
retains repeated circuits, and every labelled edge occurs exactly twice.

`exists_eightCycleDoubleCover` additionally returns eight even subgraphs using
the existing `CycleDoubleCover 8` interface. Its layers may be empty or
disconnected; decomposing them need not produce only eight ordinary circuits.
This result does not prescribe a circuit or assert a five-layer or oriented cover.

| Module | Role |
| --- | --- |
| [`Statement`](Statement.lean) | Ordinary-circuit cover and the frozen theorem statement. |
| [`Upstream`](Upstream.lean) | Compose the checked upstream eight-flow, cubic affine-pair and expansion results; prove that deleting loops preserves bridgelessness. |
| [`Transport`](Transport.lean) | Convert binary indicators to our edge sets; restore each loop in layers zero and one. |
| [`Decomposition`](Decomposition.lean) | Apply our existing ordinary-circuit decomposition to every layer, preserving multiplicities. This works for any bounded cover already in the library. |
| [`Theorem`](Theorem.lean) | Assemble the unconditional eight-layer and ordinary-circuit conclusions. |

The external proof input is the source dependency
[`openai/cdc-lean`](https://github.com/openai/cdc-lean/tree/577e9d9ea326d520f80672ee69b830bf1d513df5),
pinned in `lakefile.toml` and `lake-manifest.json`. Lean recompiles the imported
proofs with the same mathlib revision as this project. We use proved lemmas,
not an additional axiom or a theorem-shaped hypothesis. In particular,
Jaeger–Kilpatrick's eight-flow theorem is proved in the dependency.

The upstream proof chooses compatible affine pairs in `F₂³` on a cubic
expansion, then projects the resulting eight even layers to the original graph.
Our bridge keeps all non-loop edge labels. Loops contribute zero binary
incidence and are inserted into precisely two layers. Finally, the existing
`decompose_even_edge_set_ordinary` splits each layer into connected circuits.
The list-count equation proves that this step preserves the double coverage.

See [VERIFICATION.md](../../../VERIFICATION.md) for the verification of this public source tree.
