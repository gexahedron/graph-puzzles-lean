import GraphPuzzles.Reduction.Induction.NearBrickInduction
import GraphPuzzles.Petersen.Minors.TightPetersenNeighborhood
import GraphPuzzles.Cuts.CrossingTightCut

/-! Section 6, Case 2: every nontrivial tight cut crosses the selected cut. -/

namespace GraphPuzzles.LoopMultigraph

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- The oriented crossing-tight-cut step. The Petersen alternative would
produce a new noncrossing tight cut and contradict the case hypothesis. -/
theorem IsNearBrick.cutConclusion_of_crossing_tight_oriented (hn : H.IsNearBrick)
    (ih : NearBrickCutInductionHypothesis.{u, v} H.inductionSize)
    {X Y : Finset V} (hsX : H.IsSeparatingCut X) (htY : H.IsTightCut Y)
    (hY : IsNontrivialCut Y) (hnY : (H.contract Y).IsNearBrick)
    (hbY : (H.contract (Finset.univ \ Y)).IsBipartite)
    (ho : Odd (X ∩ Y).card)
    (hcross : ∀ Z, H.IsTightCut Z → IsNontrivialCut Z → CutsCross X Z) :
    H.NearBrickCutConclusion X := by
  let A := contractShore Y X
  let B := contractShore (Finset.univ \ Y) (Finset.univ \ X)
  have hc := hsX.cohesive_pair_tight htY
  have hsY := htY.isSeparatingCut hn.matchingCovered
    (Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0 < 2) hY.1))
    (Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0 < 2) hY.2))
  obtain ⟨hsA, hsB⟩ := hc.separating_uncrossed_contracts hn.matchingCovered.1 hY ho
  have hbChar : (H.contract (Finset.univ \ Y)).cutCharacteristic B = ⊤ :=
    hbY.cutCharacteristic_eq_top_of_separating hsY.2.1 hsB
  have hchar : H.cutCharacteristic X = (H.contract Y).cutCharacteristic A := by
    have he := hc.characteristic_uncross_tight hn.matchingCovered.1 hY ho htY
    change H.cutCharacteristic X = min ((H.contract Y).cutCharacteristic A)
      ((H.contract (Finset.univ \ Y)).cutCharacteristic B) at he
    simpa only [hbChar, min_eq_left le_top] using he
  rcases ih (H.contract Y) (inductionSize_contract_lt hY) hnY A hsA with
    h3 | ht | ⟨_, hp⟩
  · exact Or.inl (hchar.trans h3)
  · exact Or.inr (Or.inl (hchar.trans ht))
  · have hno : (H.contract Y).HasNoInternalTightCut A :=
      HasNoInternalTightCut.of_crossing htY hY hcross
    obtain ⟨T, hsT, hcardT⟩ := hp.exists_shore_card A (Or.inl rfl) hno
    have hcardA : A.card = 5 := hcardT.trans hsT.petersen_shore_card
    have hcardI : (X ∩ Y).card = 5 := by
      have he := card_sourceShore Y A (none_not_mem_contractShore Y X)
      rw [sourceShore_contractShore, Finset.inter_comm] at he
      exact he.trans hcardA
    have hN := hp.unique_cross_neighbor A (Or.inl rfl) hno
    have hoB : Odd B.card := by
      rw [← card_sourceShore (Finset.univ \ Y) B (none_not_mem_contractShore _ _),
        sourceShore_contractShore]
      simpa only [Finset.inter_comm] using hc.odd_complement_intersection hn.matchingCovered.1 hY ho
    have htB := hbY.tight_of_separating hsY.2.1 hsB hoB
    have heB : sourceShore (Finset.univ \ Y) B = Finset.univ \ (X ∪ Y) := by
      rw [sourceShore_contractShore]
      ext v
      simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ, true_and,
        Finset.mem_union, not_or]
      tauto
    have htU : H.IsTightCut (X ∪ Y) := by
      have hh := (htY.compl.lift_contract htB (none_not_mem_contractShore _ _)).compl
      change H.IsTightCut (Finset.univ \ sourceShore (Finset.univ \ Y) B) at hh
      simpa only [heB, Finset.sdiff_sdiff_eq_self (Finset.subset_univ (X ∪ Y))] using hh
    obtain ⟨D, htD, hD, hnD⟩ := hc.exists_noncrossing_tight_of_unique_attachment ho
      (hcross Y htY hY) htY htU (by omega) hN
    exact (hnD (hcross D htD hD)).elim

/-- Section 6, Case 2, with either tight-cut orientation and either parity
orientation of the selected cut. -/
theorem IsNearBrick.cutConclusion_of_all_crossing_tight (hn : H.IsNearBrick)
    (ih : NearBrickCutInductionHypothesis.{u, v} H.inductionSize)
    {X Y : Finset V} (hsX : H.IsSeparatingCut X) (htY : H.IsTightCut Y)
    (hY : IsNontrivialCut Y)
    (hcross : ∀ Z, H.IsTightCut Z → IsNontrivialCut Z → CutsCross X Z) :
    H.NearBrickCutConclusion X := by
  have key {Z : Finset V} (htZ : H.IsTightCut Z) (hZ : IsNontrivialCut Z)
      (hnZ : (H.contract Z).IsNearBrick)
      (hbZ : (H.contract (Finset.univ \ Z)).IsBipartite) :
      H.NearBrickCutConclusion X := by
    by_cases ho : Odd (X ∩ Z).card
    · exact hn.cutConclusion_of_crossing_tight_oriented ih hsX htZ hZ hnZ hbZ ho hcross
    · have hsZ := htZ.isSeparatingCut hn.matchingCovered
        (Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0 < 2) hZ.1))
        (Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0 < 2) hZ.2))
      have hoZ := hsZ.odd_shore hn.matchingCovered.1 hZ
      have ho' : Odd ((Finset.univ \ X) ∩ Z).card := by
        have he : (Finset.univ \ X) ∩ Z = Z \ X := by ext v; simp; tauto
        rw [he, Nat.odd_iff]
        have hc := Finset.card_sdiff_add_card_inter Z X
        rw [Finset.inter_comm Z X] at hc
        rw [Nat.odd_iff] at ho hoZ
        omega
      have hcross' : ∀ T, H.IsTightCut T → IsNontrivialCut T → CutsCross (Finset.univ \ X) T :=
        fun T ht hT ↦ (cutsCross_compl_left X T).mpr (hcross T ht hT)
      have hh := (hn.cutConclusion_of_crossing_tight_oriented ih hsX.compl htZ hZ hnZ hbZ ho' hcross').compl
      simpa only [Finset.sdiff_sdiff_eq_self (Finset.subset_univ X)] using hh
  rcases hn.tight_contractions htY hY with hh | hh
  · apply key htY.compl hY.compl hh.2
    rw [Finset.sdiff_sdiff_eq_self (Finset.subset_univ Y)]
    exact hh.1
  · exact key htY hY hh.1 hh.2

/-- The two tight-cut cases exhaust near-bricks that are not bricks. -/
theorem IsNearBrick.cutConclusion_of_not_brick (hn : H.IsNearBrick) (hnb : ¬ H.IsBrick)
    (ih : NearBrickCutInductionHypothesis.{u, v} H.inductionSize)
    {X : Finset V} (hsX : H.IsSeparatingCut X) : H.NearBrickCutConclusion X := by
  classical
  by_cases hX : IsNontrivialCut X
  · have hex : ∃ Y, H.IsTightCut Y ∧ IsNontrivialCut Y := by
      by_contra he
      apply hnb
      refine ⟨hn.notBipartite, hn.matchingCovered, ?_⟩
      intro Y ht hY
      exact he ⟨Y, ht, hY⟩
    by_cases hnc : ∃ Y, H.IsTightCut Y ∧ IsNontrivialCut Y ∧ ¬ CutsCross X Y
    · obtain ⟨Y, htY, hY, hnc⟩ := hnc
      exact hn.cutConclusion_of_noncrossing_tight ih hsX hX htY hY hnc
    · obtain ⟨Y, htY, hY⟩ := hex
      apply hn.cutConclusion_of_all_crossing_tight ih hsX htY hY
      intro Z htZ hZ
      by_contra hh
      exact hnc ⟨Z, htZ, hZ, hh⟩
  · exact Or.inr (Or.inl (cutCharacteristic_eq_top_of_not_nontrivial hX))

end GraphPuzzles.LoopMultigraph
