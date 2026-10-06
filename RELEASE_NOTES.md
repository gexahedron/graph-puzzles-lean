# Version 0.2.1

This patch explicitly builds the audit module before running its standalone
axiom check in CI and the source-guide instructions. The proofs and papers
are unchanged from v0.2.0.

This release accompanies *Graph Puzzles III.2-preview: Strong five-cycle
double covers* (6 October 2026). It adds proofs of strong five-cycle double
covers for critical, permutation and colouring-defect-three snarks.

- A prescribed circuit is an entire member of a five-cycle double cover
  exactly when deleting its vertices leaves a properly 3-edge-colourable graph.
- Critical cubic graphs and cubic permutation graphs admit every prescribed
  circuit as an entire cover member.
- An induced hexagon with exterior spoke colours `1,1,2,2,3,3` gives the
  standard component form of strong 5CDC.
- The hexagon is constructed from numerical colouring defect three in a
  snark, giving the defect-three corollary without an extra structural assumption.

The [paper guide](papers/strong-five-cdc/README.md) maps these results to the
Lean declarations and explains their hypotheses. The supplied paper source
and matching PDF are included. The previously released Sabidussi and OpenAI
CDC formalizations remain available through their existing entry points.

Lean, Mathlib and OpenAI CDC revisions retain their existing pins. The
verification record describes the local build, axiom and publication-boundary
checks for this release.

The Sabidussi PDF is updated to the supplied local arXiv v2 submission.
The main README introduces the project and links directly to the repository
papers; formalization and build details are in the separate source guide.
