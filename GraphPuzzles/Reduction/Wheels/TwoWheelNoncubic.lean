import GraphPuzzles.Reduction.Wheels.TwoWheelCubic
import GraphPuzzles.Reduction.Wheels.TwoWheelRestorationShore

/-! Choosing a removable spoke in the noncubic two-wheel case. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E} {X : Finset V}

/-- The two rim edges account for the entire degree off the selected cut. -/
theorem IsOddWheel.degree_eq_two_add_boundary
    (hw : (H.contract X).IsOddWheel none) {w : V} (hwX : w ∈ X) :
    H.degree w = 2 + H.degreeIn (H.dangling X) w := by
  obtain ⟨W⟩ := hw
  have hR := W.rim_degree_two (w := some ⟨w, hwX⟩) (by simp)
  have hh := degreeIn_add_compl (H := H.contract X)
    ((H.contract X).edgesIn (Finset.univ.erase none)) (some ⟨w, hwX⟩)
  rw [hR, contract_nonrim_eq, contractMatching, contract_degreeIn_some,
    contract_degree_some] at hh
  exact hh.symm

/-- In a cubic graph with two wheel contractions, the selected cut is
itself a perfect matching. -/
theorem matching_boundary_of_cubic_oddWheel_contractions
    (hl : (H.contract X).IsOddWheel none)
    (hr : (H.contract (Finset.univ \ X)).IsOddWheel none)
    (hc : ∀ w, H.degree w = 3) : H.IsPerfectMatching (H.dangling X) := by
  intro w
  have hdeg : H.degree w = 2 + H.degreeIn (H.dangling X) w := by
    by_cases hwX : w ∈ X
    · exact hl.degree_eq_two_add_boundary hwX
    · simpa only [dangling_compl] using hr.degree_eq_two_add_boundary (by simp [hwX])
  have hh := hc w
  omega

/-- Failure of cubicity forces at least two selected cut edges at some vertex. -/
theorem exists_boundary_degree_ge_two_of_not_cubic
    (hl : (H.contract X).IsOddWheel none)
    (hr : (H.contract (Finset.univ \ X)).IsOddWheel none)
    (hc : ¬ ∀ w, H.degree w = 3) : ∃ w, 2 ≤ H.degreeIn (H.dangling X) w := by
  push Not at hc
  obtain ⟨w, hw⟩ := hc
  have hpos : 0 < H.degreeIn (H.dangling X) w := by
    apply (H.degreeIn_pos_iff_mem_edgeSupport _ w).mpr
    apply H.mem_edgeSupport_iff.mpr
    by_cases hwX : w ∈ X
    · exact hl.exists_incident_cut_edge hwX
    · simpa only [dangling_compl] using hr.exists_incident_cut_edge (by simp [hwX])
  have hdeg : H.degree w = 2 + H.degreeIn (H.dangling X) w := by
    by_cases hwX : w ∈ X
    · exact hl.degree_eq_two_add_boundary hwX
    · simpa only [dangling_compl] using hr.degree_eq_two_add_boundary (by simp [hwX])
  exact ⟨w, by omega⟩

/-- A perfect matching misses a cut edge at every vertex with cut degree at least two. -/
theorem IsPerfectMatching.exists_avoided_boundary_edge {M : Finset E}
    (hM : H.IsPerfectMatching M) {w : V} (hw : 2 ≤ H.degreeIn (H.dangling X) w) :
    ∃ e ∈ H.dangling X, e ∉ M ∧ ∃ k, H.endAt e k = w := by
  by_contra hn
  push Not at hn
  have hle : H.degreeIn (H.dangling X) w ≤ H.degreeIn M w := by
    apply Finset.card_le_card
    intro p hp
    obtain ⟨hp, he⟩ := Finset.mem_filter.mp hp
    have hpC := (Finset.mem_product.mp hp).1
    have hpM : p.1 ∈ M := by
      by_contra hpM
      exact hn p.1 hpC hpM p.2 he
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨hpM, Finset.mem_univ _⟩, he⟩
  have hh := hM w
  omega

/-- In the noncubic two-wheel case, the already-proved avoided-spoke
deletion theorem supplies a near-brick without any suppression argument. -/
theorem IsRobustCut.exists_deleted_nearBrick_of_not_cubic
    (hX : H.IsRobustCut X) (hsl : (H.contract X).IsSolid)
    (hsr : (H.contract (Finset.univ \ X)).IsSolid)
    (hl : (H.contract X).IsOddWheel none)
    (hr : (H.contract (Finset.univ \ X)).IsOddWheel none)
    (hc : ¬ ∀ w, H.degree w = 3)
    {M : Finset E} (hM : H.IsPerfectMatching M)
    (h5 : 5 ≤ (M ∩ H.dangling X).card) :
    ∃ e ∈ H.dangling X, ∃ k, 2 ≤ H.degreeIn (H.dangling X) (H.endAt e k) ∧
      (H.deleteEdge e).IsNearBrick ∧ (H.deleteEdge e).IsRobustCut X := by
  obtain ⟨w, hw⟩ := exists_boundary_degree_ge_two_of_not_cubic hl hr hc
  obtain ⟨e, he, heM, k, hk⟩ := hM.exists_avoided_boundary_edge hw
  have hh := hX.deleteEdge_of_avoided_oddWheel_spoke hsl hsr hl hr hM h5 he heM
  exact ⟨e, he, k, hk.symm ▸ hw, hh⟩

end GraphPuzzles.LoopMultigraph
