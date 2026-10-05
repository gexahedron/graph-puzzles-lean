# Graph Puzzles in Lean

This library currently contains two proof families: Sabidussi compatibility and
cycle double covers of finite bridgeless multigraphs. The namespace is
`GraphPuzzles`. The graph model allows labelled parallel edges and loops; each
loop contributes two incidences to degree.

## Results

| Result | Entry point |
| --- | --- |
| All five numbered results in the v0.4 Sabidussi paper | `GraphPuzzles.Results.Sabidussi` |
| Ordinary-circuit CDCs and eight even cover layers for finite bridgeless multigraphs | `GraphPuzzles.Results.CycleDoubleCover` |

The headline Sabidussi declaration is
`GraphPuzzles.LoopMultigraph.sabidussi_theorem`. Its strengthened colouring
conclusion and compatible decomposition use ordinary nonempty, connected,
2-regular circuits. The dominating-circuit corollary supplies a five-cycle
double cover with the prescribed circuit as an entire layer.

The CDC declaration is `GraphPuzzles.LoopMultigraph.exists_ordinaryCycleDoubleCover`.
It covers loops, parallel edges, isolated vertices, disconnected and empty
graphs. The list retains repeated circuit occurrences and covers each edge
exactly twice. The eight-layer result allows empty or disconnected layers;
decomposing those layers may produce more than eight ordinary circuits.

The CDC proof uses the pinned
[OpenAI formalization](https://github.com/openai/cdc-lean/tree/577e9d9ea326d520f80672ee69b830bf1d513df5).
This library supplies the bridge to its graph representation, restores loops,
and decomposes the cover into ordinary circuits. The upstream source and
attribution remain in the dependency, rather than being vendored here.

The [Sabidussi paper on arXiv](https://arxiv.org/abs/2607.13225) accompanies its
formalization. The original [sabidussi-lean repository](https://github.com/gexahedron/sabidussi-lean)
remains available independently; this repository uses new module paths.

## Build and verify

Lean is pinned to `v4.31.0`, Mathlib to
`9a9483a92959bc92bd6a60176dd1fe597298c1f8`, and `cdc_lean` to
`577e9d9ea326d520f80672ee69b830bf1d513df5`.

```bash
lake exe cache get
LEAN_NUM_THREADS=1 lake --wfail build
LEAN_NUM_THREADS=1 lake env lean -j1 -M4096 GraphPuzzles/Audit.lean
LEAN_NUM_THREADS=1 lake env lean -j1 -M4096 checks/CycleDoubleCover.lean
LEAN_NUM_THREADS=1 lake --wfail build SabidussiSolution
python3 tools/publication.py check --public-tree
```

`lake-manifest.json` records the dependency revisions. Use `lake update` only
when intentionally changing those pins. A missing dependency cache can require
a larger local build; inspect available RAM and disk first.

Use `import GraphPuzzles` for both families or import either result entry point
above. [The source guide](GraphPuzzles/README.md) and
[verification record](VERIFICATION.md) describe the source and checks. Public
files and their import closure are explicitly recorded in
`publication/public-manifest.json`.

`SabidussiChallenge.lean` is the trusted Comparator specification and contains
an intentional proof placeholder. `SabidussiSolution.lean` supplies the actual
checked proof. The placeholder is outside the production library and its
axiom audit.

Code is licensed under [Apache-2.0](LICENSE). Cite individual papers for their
mathematical results; `CITATION.cff` describes the software.
