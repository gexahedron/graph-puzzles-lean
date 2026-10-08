import GraphPuzzles.Reduction.Induction.WitnessContraction

/-! The induction step across a maximal noncrossing witness. -/

namespace GraphPuzzles.LoopMultigraph

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- Orient two noncrossing cuts so that a witness shore is disjoint from
one of the selected cut's shores. -/
theorem IsCutWitness.disjoint_orientation {X Y : Finset V} (hw : H.IsCutWitness X Y)
    (hnc : ¬ CutsCross X Y) :
    (∃ Z, H.IsCutWitness X Z ∧ Z ⊆ Finset.univ \ X) ∨
      (∃ Z, H.IsCutWitness (Finset.univ \ X) Z ∧ Z ⊆ X) := by
  rcases (not_cutsCross_iff X Y).mp hnc with h | h | h | h
  · refine Or.inl ⟨Finset.univ \ Y, hw.compl_witness, ?_⟩
    intro z hz
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hx ↦ (Finset.mem_sdiff.mp hz).2 (h hx)⟩
  · refine Or.inl ⟨Y, hw, ?_⟩
    intro z hz
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hx ↦ (Finset.mem_sdiff.mp (h hx)).2 hz⟩
  · refine Or.inr ⟨Finset.univ \ Y, hw.compl.compl_witness, ?_⟩
    intro z hz
    by_contra hx
    exact (Finset.mem_sdiff.mp hz).2 (h (by simp [hx]))
  · refine Or.inr ⟨Y, hw.compl, ?_⟩
    intro z hz
    by_contra hx
    exact (Finset.mem_sdiff.mp (h (by simp [hx]))).2 hz

/-- Section 6, Case 3 reduced to the Petersen expansion lemma: a maximal
disjoint witness either yields the desired matching directly by induction,
or its complementary contraction is already Petersen up to parallel edges.
No tight-minor contraction remains in the second alternative. -/
theorem IsCutWitness.three_or_petersen_contraction {X Y : Finset V}
    (hw : H.IsCutWitness X Y) (hb : H.IsBrick) (hsX : H.IsSeparatingCut X)
    (hX : IsNontrivialCut X) (hXY : X ⊆ Finset.univ \ Y)
    (hmax : ∀ Z, H.IsCutWitness X Z → Z ⊆ Finset.univ \ X → Z.card ≤ Y.card)
    (ih : NearBrickCutInductionHypothesis.{u, v} H.inductionSize) :
    (∃ M, H.IsPerfectMatching M ∧ (M ∩ H.dangling X).card = 3) ∨
      (H.contract (Finset.univ \ Y)).IsPetersenUpToParallel := by
  let R := Finset.univ \ Y
  let A := contractShore R X
  have hr : H.IsRobustCut R := hw.robust.compl
  have hR := hr.nontrivial hb.matchingCovered
  have hA : IsNontrivialCut A := hw.nontrivial_contractShore hX hXY
  have ho : Odd (X ∩ R).card := by
    rw [Finset.inter_eq_left.mpr hXY]
    exact hsX.odd_shore hb.matchingCovered.1 hX
  have hsA : (H.contract R).IsSeparatingCut A :=
    hw.compl_witness.cohesive.separating_intersection_contract hb.matchingCovered.1
      (Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0 < 2) hR.2)) ho
  have hoA := hsA.odd_shore hr.leftNear.matchingCovered.1 hA
  rcases ih (H.contract R) (inductionSize_contract_lt hR) hr.leftNear A hsA with
    h3 | hi | ⟨_, hp⟩
  · obtain ⟨M, hM, hcM⟩ := (cutCharacteristic_eq_three_iff hoA).mp h3
    obtain ⟨N, hN, hcN⟩ := hw.compl_witness.cohesive.extend_intersection_matching ho hM
    exact Or.inl ⟨N, hN, hcN.trans hcM⟩
  · exact (hw.not_tight_contract hb hX hXY ((cutCharacteristic_eq_top_iff_tight hoA).mp hi)).elim
  · exact Or.inr (hp.petersen_of_tight_crossing (hw.tight_crossing_of_maximal hb hsX hX hXY hmax))

end GraphPuzzles.LoopMultigraph
