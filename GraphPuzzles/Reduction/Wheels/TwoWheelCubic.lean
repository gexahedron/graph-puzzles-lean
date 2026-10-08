import GraphPuzzles.Reduction.Wheels.OddWheelCutDeletion

/-! The cubic structure once the cut between two wheels is itself a matching. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- The labels off the rim of a shore contraction are precisely its
original boundary labels. -/
theorem contract_nonrim_eq (X : Finset V) :
    Finset.univ \ (H.contract X).edgesIn (Finset.univ.erase none) =
      H.contractMatching X (H.dangling X) := by
  ext e
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, mem_contractMatching]
  constructor
  · intro hh
    by_contra hn
    have heq : (H.endAt e.1 0 ∈ X ↔ H.endAt e.1 1 ∈ X) := by
      simpa only [mem_dangling, not_not] using hn
    apply hh
    apply mem_edgesIn.mpr
    intro k
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    intro hnone
    have hk := (contract_endAt_eq_none_iff X e k).mp hnone
    obtain ⟨j, hj⟩ := mem_meets.mp e.2
    fin_cases k <;> fin_cases j <;> tauto
  · intro he hR
    have hmem (k : Fin 2) : H.endAt e.1 k ∈ X := by
      by_contra hn
      exact (Finset.mem_erase.mp ((mem_edgesIn.mp hR) k)).1
        ((contract_endAt_eq_none_iff X e k).mpr hn)
    exact (mem_dangling.mp he) (by simp [hmem])

/-- An odd-wheel shore whose boundary is an original perfect matching
has degree three at every retained vertex. -/
theorem IsOddWheel.degree_three_of_matching_boundary {X : Finset V}
    (hw : (H.contract X).IsOddWheel none) (hm : H.IsPerfectMatching (H.dangling X))
    {w : V} (hwX : w ∈ X) : H.degree w = 3 := by
  obtain ⟨W⟩ := hw
  have hR := W.rim_degree_two (w := some ⟨w, hwX⟩) (by simp)
  have hh := degreeIn_add_compl (H := H.contract X)
    ((H.contract X).edgesIn (Finset.univ.erase none)) (some ⟨w, hwX⟩)
  rw [hR, contract_nonrim_eq, contractMatching, contract_degreeIn_some,
    hm w, contract_degree_some] at hh
  exact hh.symm

/-- Two opposite wheel contractions and a perfect-matching cut give a
cubic original graph. -/
theorem cubic_of_oddWheel_contractions {X : Finset V}
    (hl : (H.contract X).IsOddWheel none)
    (hr : (H.contract (Finset.univ \ X)).IsOddWheel none)
    (hm : H.IsPerfectMatching (H.dangling X)) : ∀ w, H.degree w = 3 := by
  intro w
  by_cases hw : w ∈ X
  · exact hl.degree_three_of_matching_boundary hm hw
  · apply hr.degree_three_of_matching_boundary (w := w) (by simpa only [dangling_compl] using hm)
    simp [hw]

end GraphPuzzles.LoopMultigraph
