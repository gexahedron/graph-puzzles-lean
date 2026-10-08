import GraphPuzzles.Petersen.PetersenExpansion
import GraphPuzzles.Reduction.Induction.WitnessCrossingInduction

/-! Section 6, Case 3, and the complete elimination of cut witnesses. -/

namespace GraphPuzzles.LoopMultigraph

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- A maximal disjoint witness either succeeds directly under induction
or reduces to the now explicit Petersen expansion matching. -/
theorem IsBrick.three_of_disjoint_witness (hb : H.IsBrick)
    (ih : NearBrickCutInductionHypothesis.{u, v} H.inductionSize)
    {X : Finset V} (hsX : H.IsSeparatingCut X) (hX : IsNontrivialCut X)
    (hex : ∃ Y, H.IsCutWitness X Y ∧ Y ⊆ Finset.univ \ X) :
    ∃ M, H.IsPerfectMatching M ∧ (M ∩ H.dangling X).card = 3 := by
  obtain ⟨Y, hw, hYX, hmax⟩ := exists_maximal_disjoint_witness hex
  have hXY : X ⊆ Finset.univ \ Y := by
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hy ↦ (Finset.mem_sdiff.mp (hYX hy)).2 hv⟩
  rcases hw.three_or_petersen_contraction hb hsX hX hXY hmax ih with h3 | hp
  · exact h3
  · have hr := hw.robust.compl
    have hR := hr.nontrivial hb.matchingCovered
    have ho : Odd (X ∩ (Finset.univ \ Y)).card := by
      rw [Finset.inter_eq_left.mpr hXY]
      exact hsX.odd_shore hb.matchingCovered.1 hX
    have hsA := hw.compl_witness.cohesive.separating_intersection_contract
      hb.matchingCovered.1 (Finset.card_pos.mp (by have := hR.2; omega)) ho
    have hh := hr.isSeparatingCut.exists_three_crossing_of_petersen_expansion hp
      hr.notTight (none_not_mem_contractShore _ _) hsA (hw.nontrivial_contractShore hX hXY)
    simpa only [sourceShore_contractShore, Finset.inter_eq_right.mpr hXY] using hh

/-- Section 6, Case 3, with either orientation of the selected cut and witness. -/
theorem IsBrick.cutConclusion_of_noncrossing_witness (hb : H.IsBrick)
    (ih : NearBrickCutInductionHypothesis.{u, v} H.inductionSize)
    {X Y : Finset V} (hsX : H.IsSeparatingCut X) (hX : IsNontrivialCut X)
    (hw : H.IsCutWitness X Y) (hnc : ¬ CutsCross X Y) : H.NearBrickCutConclusion X := by
  have ho := hsX.odd_shore hb.matchingCovered.1 hX
  apply Or.inl
  apply (cutCharacteristic_eq_three_iff ho).mpr
  rcases hw.disjoint_orientation hnc with hex | hex
  · exact hb.three_of_disjoint_witness ih hsX hX hex
  · have hex' : ∃ Z, H.IsCutWitness (Finset.univ \ X) Z ∧
        Z ⊆ Finset.univ \ (Finset.univ \ X) := by
      simpa only [Finset.sdiff_sdiff_eq_self (Finset.subset_univ X)] using hex
    simpa only [dangling_compl] using hb.three_of_disjoint_witness ih hsX.compl hX.compl hex'

/-- Cases 3 and 4 exhaust the witness alternatives. -/
theorem IsBrick.cutConclusion_of_witness (hb : H.IsBrick)
    (ih : NearBrickCutInductionHypothesis.{u, v} H.inductionSize)
    {X Y : Finset V} (hsX : H.IsSeparatingCut X) (hX : IsNontrivialCut X)
    (hw : H.IsCutWitness X Y) : H.NearBrickCutConclusion X := by
  classical
  by_cases hex : ∃ Z, H.IsCutWitness X Z ∧ ¬ CutsCross X Z
  · obtain ⟨Z, hwZ, hnc⟩ := hex
    exact hb.cutConclusion_of_noncrossing_witness ih hsX hX hwZ hnc
  · apply hb.cutConclusion_of_all_crossing_witnesses ih hsX hX hw
    intro Z hwZ
    by_contra hn
    exact hex ⟨Z, hwZ, hn⟩

end GraphPuzzles.LoopMultigraph
