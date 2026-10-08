import GraphPuzzles.Petersen.PetersenBoundaryFibers

/-! Adjacency lifting for the canonical Petersen fiber names. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E} {X : Finset V}

namespace PetersenFiberModel

/-- Every canonical Petersen adjacency has a labelled original edge
between its two fibers. -/
theorem canonical_exists_join (R : H.PetersenFiberModel X) {p q : Fin 10}
    (hadj : ∃ f, LoopMultigraph.petersen.Joins f p q) :
    ∃ a ∈ R.canonicalFiber p, ∃ b ∈ R.canonicalFiber q, ∃ e, H.Joins e a b := by
  obtain ⟨f, hf⟩ := hadj
  obtain ⟨e, a, b, he, ha, hb⟩ := R.exists_canonical_join hf
  exact ⟨a, (R.mem_canonicalFiber p a).mpr ha, b,
    (R.mem_canonicalFiber q b).mpr hb, e, he⟩

/-- If the exterior fiber is a singleton, the lifted neighbor is the
chosen canonical representative. -/
theorem canonical_exists_join_representative (R : H.PetersenFiberModel X) {p q : Fin 10}
    (hadj : ∃ f, LoopMultigraph.petersen.Joins f p q)
    (hq : (R.canonicalFiber q).card ≤ 1) :
    ∃ a ∈ R.canonicalFiber p, ∃ e, H.Joins e a (R.canonicalRepresentative q) := by
  obtain ⟨a, ha, b, hb, e, he⟩ := R.canonical_exists_join hadj
  have hb' : b = R.canonicalRepresentative q := R.canonicalFiber_subsingleton hq
    ((R.mem_canonicalFiber q b).mp hb) (R.canonicalVertex_representative q)
  exact ⟨a, ha, e, hb' ▸ he⟩

end PetersenFiberModel

end GraphPuzzles.LoopMultigraph
