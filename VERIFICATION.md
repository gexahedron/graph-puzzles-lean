# Verification of version 0.3.0

The release is checked with Lean 4.31.0, Mathlib
`9a9483a92959bc92bd6a60176dd1fe597298c1f8` and OpenAI CDC
`577e9d9ea326d520f80672ee69b830bf1d513df5`.

All checks below passed locally on 2026-10-07 in a fresh public project cache.
All ten dependency checkouts matched their pinned revisions and had clean
tracked sources. Only pinned third-party dependency caches were reused.

| Check | Result |
| --- | --- |
| `lake --wfail build GraphPuzzles GraphPuzzles.Audit SabidussiSolution` | Passed, 1878 jobs |
| Direct `GraphPuzzles/Audit.lean` check | Passed, 67 exact axiom guards |
| `checks/CycleDoubleCover.lean` | Passed |
| `checks/StrongFiveCycleDoubleCover.lean` | Passed |
| `checks/SnarkFactorisation.lean` | Passed |
| Exact public-tree/import boundary check | Passed, 128 modules and 157 files |
| Exporter privacy-boundary regression tests | Passed, 11 tests |
| Previously released proof modules | All 48 unchanged; three library/audit entry points expand |

The fresh build completed in 364.0 seconds, with one Lean worker, a peak
resident process-tree footprint of 2510.5 MiB and at most 80.8 MiB of swap
growth. The standalone checks completed in 20.2 seconds, peaking at
2219.4 MiB with no swap growth. The runs were bounded by a 6 GiB resident
budget, a 4 GiB Lean heap limit, swap/disk checks and explicit deadlines.

The axiom guards permit exactly `propext`, `Classical.choice` and `Quot.sound`.
The production-source scan rejects proof placeholders, extra axioms and
native decision shortcuts. The only intentional placeholder is the trusted
Comparator specification described below.

The statement check covers the main factorisation theorems and their intersection,
multiset multiplicities, terminal connectivity, intermediate class closure and
Hamilton-cycle descent. The permutation conclusion assumes no bicriticality
conjecture. Section 6's numerical corollaries are not separate Lean theorems.

The supplied source was frozen byte-for-byte and compiled successfully with
the desktop LaTeX editor. The included 11-page PDF matches the source digest
in its successful latexmk build record. Structural checks of its seven margin
appearances and URI links passed, as did native PDFKit text-selection and link
hit tests. Pages 1, 2, 6 and 11 were rendered and inspected; margin references,
body text and the final bibliography are present and legible.

The paper title, source date and author attribution are preserved. The source
SHA-256 is `a5232366d5dfb3f6b2f812e7ccb4308b9befd9480971548718a915e571a3f158`;
the PDF SHA-256 is `cd96e5a17d73e4c985ba3b5b244e484b9c422d9f1d1700fef4883aba73c5c47c`.

`SabidussiChallenge.lean` is the existing trusted Comparator specification,
with its intentional proof placeholder outside the production library and audit.
`SabidussiSolution.lean` supplies the checked proof. The published commit is
also checked by GitHub Lean CI and Comparator.
