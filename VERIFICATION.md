# Verification of v0.5.0

Prepared on 9 October 2026 for **Graph Puzzles III.3-preview: Oriented
five-cycle double covers of snarks with colouring defect three**.

The explicit publication manifest contains 373 Lean modules and 410 files.
The nine new modules form the selected proof's reviewed dependency closure.
All 362 earlier proof modules outside the two import aggregates, all four
earlier statement checks, and all earlier papers are byte-for-byte unchanged.
The aggregate changes only import the new claims and axiom guards.

The numerical and prescribed-core endpoints, auxiliary constructions,
21 new exact standard-axiom guards, and independent statement checks compile
locally with Lean v4.31.0, one worker and a 4096 MiB Lean heap limit. The
checks unpack the exact core member, double coverage, opposite directions,
arbitrary reference directions and independent vertex/edge universes.
All 108 axiom guards allow exactly `propext`, `Classical.choice`, and
`Quot.sound`. The production source scan rejects proof placeholders, custom
axioms, native decision shortcuts and unsafe replacements. The pinned
OpenAI CDC production dependency passed the same scan. All ten dependency
source checkouts match their pins; unrelated Finder metadata is ignored.

A separate public build tree reused only the previously verified public
v0.4.0 project cache and pinned third-party caches. Its full local build
stopped at the 10 GiB disk floor. No private project cache was copied into
that tree. The full library, aggregate axiom audit, all five independent
statement files and the Sabidussi wrapper are enforced by
[Lean CI](.github/workflows/lean.yml). Comparator independently checks the
Sabidussi wrapper. The release is tagged only after both workflows pass for
the exact public commit.

The standalone TeX and five-page PDF were frozen from the current paper
directory. The source hash matches the successful latexmk build record and
the adjacent PDF matches the build output. The desktop compiler also
compiled the frozen source successfully. Structural checks verified both
printable margin appearances and their unique URI links, page bounds and
absence of overlaps. Native PDFKit verified text selection and both margin
link hit tests. Pages 1, 3 and 5 were rendered and inspected.

The [paper-to-Lean guide](papers/defect-three-oriented-five/README.md)
describes the exact mathematical scope and the auxiliary construction.
Unselected research modules are absent from the export. The original
`gexahedron/sabidussi-lean` repository is preserved independently.
