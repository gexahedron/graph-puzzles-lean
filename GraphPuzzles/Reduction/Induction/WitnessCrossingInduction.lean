import GraphPuzzles.Reduction.Induction.WitnessUncrossing
import GraphPuzzles.Cuts.Shores.CrossingAttachments

/-! Section 6, Case 4: every witness crosses the selected cut. -/

namespace GraphPuzzles.LoopMultigraph

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

private theorem not_crosses_of_right_subset {X Y : Finset V} (h : Y ⊆ X) :
    ¬ CutsCross X Y := by
  intro hc
  obtain ⟨v, hv⟩ := hc.2.2.1
  exact (Finset.mem_sdiff.mp hv).2 (h (Finset.mem_sdiff.mp hv).1)

/-- With the odd intersection oriented, two applications of Proposition
6.1 leave two opposite attachments; brick connectivity excludes them. -/
theorem IsBrick.three_of_all_crossing_witnesses_oriented (hb : H.IsBrick)
    {X Y : Finset V} (hw : H.IsCutWitness X Y) (ho : Odd (X ∩ Y).card)
    (hall : ∀ Z, H.IsCutWitness X Z → CutsCross X Z)
    (ih : NearBrickCutInductionHypothesis.{u, v} H.inductionSize) :
    ∃ M, H.IsPerfectMatching M ∧ (M ∩ H.dangling X).card = 3 := by
  have hcross := hall Y hw
  rcases hw.three_or_inner_witness_or_attachment hb hcross ho ih with h3 | hinner | ⟨i, hi, hI⟩
  · exact h3
  · obtain ⟨Z, hwZ, hZ⟩ := hinner
    exact ((not_crosses_of_right_subset (hZ.trans Finset.inter_subset_left)) (hall Z hwZ)).elim
  · have hother : H.IsCutWitness (Finset.univ \ X) (Finset.univ \ Y) :=
      hw.compl.compl_witness
    have hall' : ∀ Z, H.IsCutWitness (Finset.univ \ X) Z → CutsCross (Finset.univ \ X) Z := by
      intro Z hwZ
      have hwX : H.IsCutWitness X Z := by
        simpa only [Finset.sdiff_sdiff_eq_self (Finset.subset_univ X)] using hwZ.compl
      exact (cutsCross_compl_left X Z).mpr (hall Z hwX)
    have ho' := hw.cohesive.odd_complement_intersection hb.matchingCovered.1
      (hw.robust.nontrivial hb.matchingCovered) ho
    rcases hother.three_or_inner_witness_or_attachment hb (hall' _ hother) ho' ih with
      h3 | hinner | ⟨j, hj, hJ⟩
    · simpa only [dangling_compl] using h3
    · obtain ⟨Z, hwZ, hZ⟩ := hinner
      exact ((not_crosses_of_right_subset (hZ.trans Finset.inter_subset_left)) (hall' Z hwZ)).elim
    · exact (hw.cohesive.not_connectedAfterDeletingPairs_of_opposite_attachments
        hcross ho hi hj hI hJ
        (hb.connectedAfterDeletingPairs hb.matchingCovered.loopless)).elim

/-- Section 6, Case 4. The existence of a witness and absence of a
noncrossing witness force characteristic three. -/
theorem IsBrick.cutConclusion_of_all_crossing_witnesses (hb : H.IsBrick)
    (ih : NearBrickCutInductionHypothesis.{u, v} H.inductionSize)
    {X Y : Finset V} (hsX : H.IsSeparatingCut X) (hX : IsNontrivialCut X)
    (hw : H.IsCutWitness X Y) (hall : ∀ Z, H.IsCutWitness X Z → CutsCross X Z) :
    H.NearBrickCutConclusion X := by
  have hoX := hsX.odd_shore hb.matchingCovered.1 hX
  apply Or.inl
  apply (cutCharacteristic_eq_three_iff hoX).mpr
  by_cases ho : Odd (X ∩ Y).card
  · exact hb.three_of_all_crossing_witnesses_oriented hw ho hall ih
  · have he : X ∩ (Finset.univ \ Y) = X \ Y := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    have ho' : Odd (X ∩ (Finset.univ \ Y)).card := by
      rw [he, Nat.odd_iff]
      have hc := Finset.card_sdiff_add_card_inter X Y
      rw [Nat.odd_iff] at ho hoX
      omega
    exact hb.three_of_all_crossing_witnesses_oriented hw.compl_witness ho' hall ih

end GraphPuzzles.LoopMultigraph
