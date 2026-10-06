# Verification of version 0.2.1

This patch builds `GraphPuzzles.Audit` before the standalone axiom check in
CI and the checking instructions. The proof source and paper contents are
identical to v0.2.0; the paper filenames are shortened.

A check with both compiled audit modules removed reproduced the missing
dependency reported by CI. The explicit build restored them, and the 34
axiom guards, both statement checks and publication boundary then passed.
This check completed in 30.2 seconds, peaking at 1528.6 MiB with no swap growth.

The release proof sources were checked locally on 2026-10-06 with Lean 4.31.0,
Mathlib `9a9483a92959bc92bd6a60176dd1fe597298c1f8` and OpenAI CDC
`577e9d9ea326d520f80672ee69b830bf1d513df5`. All ten dependency checkouts
matched the revisions in `lake-manifest.json` and had clean tracked sources.

| Check | Result |
| --- | --- |
| Full exported library build with `lake --wfail build` | Passed, 1793 jobs |
| Final `lake --wfail build GraphPuzzles.Audit SabidussiSolution` | Passed, 1796 jobs |
| `lake env lean -j1 -M4096 GraphPuzzles/Audit.lean` | Passed, 34 exact axiom guards: 20 existing and 14 new |
| `lake env lean -j1 -M4096 checks/CycleDoubleCover.lean` | Passed |
| `lake env lean -j1 -M4096 checks/StrongFiveCycleDoubleCover.lean` | Passed |
| `python3 tools/publication.py check --public-tree` | Passed, exactly 51 modules and 76 files |
| Exporter privacy-boundary regression tests | Passed, 11 tests, including explicit draft overlays and private-import rejection |
| Already public proof sources | All 24 proof source files unchanged; the new umbrellas and audit add the strong-five results |

The initial export used a fresh project build cache and reused only pinned
third-party dependency caches. It completed in 157.0
seconds with one Lean worker and a peak resident process-tree footprint of
2469.3 MiB. The final dependency separation was rebuilt and
all exported checks rerun successfully in 91.1 seconds, peaking at 2570.1
MiB with no swap growth. Runs were bounded by a 6 GiB resident budget, a 4 GiB Lean heap limit,
swap/disk checks and explicit time limits.

The guards require the exact lists containing only `propext`, `Classical.choice`
and `Quot.sound`. They tolerate whitespace wrapping, while checking axiom
names and ordering. The production-source boundary scan rejects proof
placeholders, additional axioms and native decision shortcuts.

The strong-five statement check uses independent vertex and edge universes.
It checks entire-member containment for critical and permutation graphs and
component containment from the numerical defect-three hypothesis, with no
assumed hexagon, auxiliary exterior colouring or girth-five restriction.
The previous CDC scope checks cover empty/disconnected graphs, loops,
parallel edges and isolated vertices.

The current supplied TeX source was frozen without edits and compiled successfully
with the desktop editor. A matching 18-page PDF was exported from that frozen
source using the existing pdfLaTeX/latexmk installation. The source MD5 matches
the successful PDF build record. The source title, date and attribution are
preserved.

`SabidussiChallenge.lean` is the existing trusted Comparator specification
with an intentional proof placeholder, outside the production library and
its axiom audit. `SabidussiSolution.lean` supplies the checked proof. At the time of local verification, Linux
Comparator and GitHub CI were pending;
the workflows check the published release. Their live results are available on GitHub.

The Sabidussi PDF is copied byte-for-byte from the supplied local arXiv v2
submission folder. Its title and the first and last pages were checked; it
contains 10 pages. The repository README links directly to both paper PDFs.
