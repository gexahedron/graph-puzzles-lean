import GraphPuzzles.DefectThree.HexagonDisjointFive

/-! Degree counting at a cubic vertex. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- A cubic vertex has degree exactly two in an edge set containing two of its half-edges but not
the third. -/
theorem degreeIn_eq_two_of_halfEdges {G : LoopMultigraph V E} (hCubic : ∀ v : V, G.degree v = 3)
    {F : Finset E} {w : V} (x₁ x₂ x₃ : G.halfEdgesAt w) (h12 : x₁ ≠ x₂)
    (h₁ : x₁.1.1 ∈ F) (h₂ : x₂.1.1 ∈ F) (h₃ : x₃.1.1 ∉ F) : G.degreeIn F w = 2 := by
  have hle : G.degreeIn F w ≤ 2 := by
    rw [G.degreeIn_eq_card_halfEdges]
    have hsub : (Finset.univ.filter fun x : G.halfEdgesAt w ↦ x.1.1 ∈ F) ⊆
        Finset.univ.erase x₃ := by
      intro x hx
      rw [Finset.mem_erase]
      refine ⟨fun h ↦ h₃ (h ▸ (Finset.mem_filter.mp hx).2), Finset.mem_univ _⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at this
    have hdeg : Fintype.card (G.halfEdgesAt w) = 3 := hCubic w
    omega
  have hge := G.two_le_degreeIn_of_ne x₁ x₂ h12 h₁ h₂
  omega

end GraphPuzzles.LoopMultigraph
