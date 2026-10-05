# Verification

The exported public source tree was checked on 2026-10-05 with Lean 4.31.0,
Mathlib `9a9483a92959bc92bd6a60176dd1fe597298c1f8` and OpenAI CDC
`577e9d9ea326d520f80672ee69b830bf1d513df5`.

| Check | Result |
| --- | --- |
| `LEAN_NUM_THREADS=1 lake --wfail build GraphPuzzles` | Passed, 1770 jobs |
| `lake env lean -j1 -M4096 GraphPuzzles/Audit.lean` | Passed, 20 exact axiom guards |
| `lake env lean -j1 -M4096 checks/CycleDoubleCover.lean` | Passed |
| `lake --wfail build SabidussiSolution` | Passed, 1771 jobs |
| `python3 tools/publication.py check --public-tree` | Passed, exactly 27 production modules and 47 files |
| Pinned OpenAI production shortcut scan | Passed |

The project build cache was fresh; only pinned third-party dependency caches
were reused. The build used one worker, took 75.6 seconds and peaked at
2579.5 MiB resident RAM, with no additional swap use recorded.

The scope checks cover independent vertex/edge universes, empty graphs,
isolated vertices, loops, parallel edges and disconnected graphs. A single
non-loop edge is checked as a negative bridgelessness case.

The axiom guards check the recorded lists containing only `propext`,
`Classical.choice` and `Quot.sound`. They ignore whitespace to tolerate line
wrapping while retaining exact axiom names and ordering.

`SabidussiChallenge.lean` is a trusted Comparator specification with an
intentional proof placeholder. It is outside the production library and its
axiom audit. `SabidussiSolution.lean` provides the checked proof. The Linux
Comparator isolation workflow is configured for GitHub CI; it was not run
locally on the Mac used for these checks.
