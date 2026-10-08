import GraphPuzzles.Matching.MatchingOn

/-! Transport of partial matchings and factor-criticality through edge restrictions. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

theorem IsPerfectMatchingOn.of_restrictEdges {F : Finset E} {S : Finset V} {M : Finset F}
    (hM : (H.restrictEdges F).IsPerfectMatchingOn S M) :
    H.IsPerfectMatchingOn S (M.image Subtype.val) := by
  constructor
  · intro e he k
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    exact hM.1 f hf k
  · intro v hv
    rw [restrictEdges_degreeIn]
    exact hM.2 v hv

theorem IsPerfectMatchingOn.exists_restrictEdges {F M : Finset E} {S : Finset V}
    (hM : H.IsPerfectMatchingOn S M) (hMF : M ⊆ F) :
    ∃ N, (H.restrictEdges F).IsPerfectMatchingOn S N ∧ N.image Subtype.val = M := by
  let N : Finset F := Finset.univ.filter fun e ↦ e.1 ∈ M
  have heq : N.image Subtype.val = M := by
    ext e
    constructor
    · intro he
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
      exact (Finset.mem_filter.mp hf).2
    · intro he
      exact Finset.mem_image.mpr ⟨⟨e, hMF he⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩, rfl⟩
  refine ⟨N, ⟨?_, ?_⟩, heq⟩
  · intro e he k
    exact hM.1 e.1 (Finset.mem_filter.mp he).2 k
  · intro v hv
    rw [← restrictEdges_degreeIn, heq]
    exact hM.2 v hv

theorem IsFactorCritical.of_restrictEdges {F : Finset E} {S : Finset V}
    (hfc : (H.restrictEdges F).IsFactorCritical S) : H.IsFactorCritical S := by
  intro v hv
  obtain ⟨M, hM⟩ := hfc v hv
  exact ⟨M.image Subtype.val, hM.of_restrictEdges⟩

/-- Adding available edges preserves factor-criticality of the specified shore. -/
theorem IsFactorCritical.restrictEdges_mono {F G : Finset E} {S : Finset V}
    (hfc : (H.restrictEdges F).IsFactorCritical S) (hFG : F ⊆ G) :
    (H.restrictEdges G).IsFactorCritical S := by
  intro v hv
  obtain ⟨M, hM⟩ := hfc v hv
  obtain ⟨N, hN, _⟩ := hM.of_restrictEdges.exists_restrictEdges (F := G) (by
    intro e he
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp he
    exact hFG f.2)
  exact ⟨N, hN⟩

end GraphPuzzles.LoopMultigraph
