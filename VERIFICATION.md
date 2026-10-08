# Verification of version 0.4.0

The release was checked locally on 8 October 2026 with Lean 4.31.0,
Mathlib `9a9483a92959bc92bd6a60176dd1fe597298c1f8` and OpenAI CDC
`577e9d9ea326d520f80672ee69b830bf1d513df5`. All ten dependency checkouts
matched their pins and had clean tracked sources. The public project build
cache started empty; only pinned third-party sources and caches were shared.

| Check | Result |
| --- | --- |
| `lake --wfail build GraphPuzzles GraphPuzzles.Audit SabidussiSolution` | Passed, 2285 jobs |
| Direct `GraphPuzzles/Audit.lean` check | Passed, 87 exact axiom guards |
| `checks/CycleDoubleCover.lean` | Passed |
| `checks/StrongFiveCycleDoubleCover.lean` | Passed |
| `checks/SnarkFactorisation.lean` | Passed |
| `checks/TwoCircuitFourMatchings.lean` | Passed |
| Exact public-tree/import boundary | Passed, 364 modules and 397 files |
| Exporter privacy-boundary regression tests | Passed, 11 tests |
| Previously released proof modules | All 126 unchanged; two aggregate entry points expand |
| Previously released paper source/PDF files | All unchanged |

The fresh build took 1870.0 seconds, with a peak resident
process-tree footprint of 3770.2 MiB and at most
1359.8 MiB of system-wide swap growth. It used one Lean
thread, low CPU priority, CPU throttling, a 4 GiB Lean heap limit, a 6 GiB
resident budget, a 10 GiB free-disk floor, pressure/swap monitoring and an
explicit deadline. The standalone checks took 30.9 seconds,
peaking at 2654.6 MiB with no swap growth.

The exact axiom guards permit only `propext`, `Classical.choice` and
`Quot.sound`. Production sources are scanned for proof placeholders, extra
axioms and native decision shortcuts. The only intentional placeholder is
the pre-existing trusted Comparator specification outside the production
library and its audit.

The new statement check verifies the prescribed complementary matching as
member zero, the perfect matching index exactly four (excluding all smaller
sizes), the permutation corollary and both proved matching-theory ingredients.
The main result permits chords and excludes the Petersen graph. The proper
snark definition includes connectedness, bridgelessness, simplicity, cubic
degree, girth at least five, cyclic edge-connectivity at least four and
non-three-edge-colourability. No external Campos–Lucchesi or Karabáš–Máčajová
hypothesis is supplied. Their reviewed supporting matching theory is included.

A general degree-counting lemma was separated from private hexagon suppression
and orientation imports before export. Those unrelated endpoints remain
private. Unselected results, all three unfinished families, manuscripts and
local literature copies are outside the exact allowlist.

The exact paper TeX and eight-page PDF were frozen from the current paper
folder. The source digest matches its successful latexmk build record, and
the adjacent PDF is identical to the build output. The standalone TeX also
compiled successfully in the desktop editor. Structural checks passed for
seven printable margin appearances, URI links, bounds and overlap. Native
PDFKit confirmed isolated margin text, selectable body/bibliography text and
seven working link hit tests. Pages 1, 3 and 8 were rendered and inspected;
the title, mathematical text, margin references and bibliography are legible.

The paper's title, source date and author attribution are preserved.
TeX SHA-256: `2faa8d713941648793521129d0f25978203d755e7d4254aa1b14c6805c606d01`.
PDF SHA-256: `2868db1651827aa4ccd71e1eeccc52de439fd6f6dc8099095d9457304ad1ead2`.

`SabidussiChallenge.lean` remains the trusted Comparator specification;
`SabidussiSolution.lean` supplies the checked proof. GitHub Lean CI and
Comparator check the published commit as well.
