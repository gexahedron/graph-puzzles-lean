import GraphPuzzles.Reduction.Induction.NearBrickSimpleInduction
import GraphPuzzles.Reduction.Induction.WitnessNoncrossingInduction
import GraphPuzzles.Petersen.PetersenInternalEdge
import GraphPuzzles.Reduction.Wheels.OddWheelCutReduction
import GraphPuzzles.Reduction.Wheels.TwoWheelNoncubicInduction

/-! Reduction of the complete induction to the final cubic two-wheel case. -/

namespace GraphPuzzles.LoopMultigraph

universe u v

/-- The final structural classification remaining after the induction reductions. -/
def CubicTwoWheelClassification : Prop :=
  ∀ {V : Type u} {E : Type v} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (H : LoopMultigraph V E),
    H.IsSimple → H.IsBrick → ∀ X, H.IsRobustCut X →
    (H.contract X).IsSolid → (H.contract (Finset.univ \ X)).IsSolid →
    (H.contract X).IsOddWheel none →
    (H.contract (Finset.univ \ X)).IsOddWheel none →
    H.IsPerfectMatching (H.dangling X) → 5 ≤ (H.dangling X).card →
    (∀ e ∈ H.dangling X, ¬ (H.deleteEdge e).IsNearBrick) →
    (¬ ∃ M, H.IsPerfectMatching M ∧ (M ∩ H.dangling X).card = 3) → H.IsPetersen

/-- Cases 1–6 and the noncubic part of Case 7 reduce the full theorem
to a matching cut between two wheels with no b-removable spoke. -/
theorem nearBrickCutTheorem_of_cubic_twoWheel_step
    (step : ∀ {V : Type u} {E : Type v} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (H : LoopMultigraph V E),
      H.IsSimple → H.IsBrick → ∀ X, H.IsRobustCut X →
      (H.contract X).IsSolid → (H.contract (Finset.univ \ X)).IsSolid →
      (H.contract X).IsOddWheel none →
      (H.contract (Finset.univ \ X)).IsOddWheel none →
      H.IsPerfectMatching (H.dangling X) → 5 ≤ (H.dangling X).card →
      (∀ e ∈ H.dangling X, ¬ (H.deleteEdge e).IsNearBrick) →
      (∃ M, H.IsPerfectMatching M ∧ (M ∩ H.dangling X).card = 3) ∨ H.IsPetersen) :
    NearBrickCutTheorem.{u, v} := by
  apply nearBrickCutTheorem_of_simple_brick_step
  intro V E _ _ _ _ H ih hsimple hb hnotP X hs hX
  have finish (h : ∃ M, H.IsPerfectMatching M ∧ (M ∩ H.dangling X).card = 3) :
      H.NearBrickCutConclusion X :=
    Or.inl ((cutCharacteristic_eq_three_iff (hs.odd_shore hb.matchingCovered.1 hX)).mpr h)
  by_cases hthree : ∃ M, H.IsPerfectMatching M ∧ (M ∩ H.dangling X).card = 3
  · exact finish hthree
  by_cases hw : ∃ Y, H.IsCutWitness X Y
  · obtain ⟨Y, hY⟩ := hw
    exact hb.cutConclusion_of_witness ih hs hX hY
  obtain hh | ⟨hr, hsl, hsr⟩ := hs.witness_or_robust_solid hb hX
  · exact (hw hh).elim
  have hdel : ∀ e, e ∉ H.dangling X → (H.deleteEdge e).IsNearBrick →
      (H.deleteEdge e).IsSeparatingCut X → False := by
    intro e he hn hd
    exact hthree (hb.exists_three_crossing_of_internal_deleted_nearBrick hsimple ih hs hX hn hd he)
  obtain ⟨hwl, hwr⟩ := hb.oddWheel_contractions_of_no_witness_or_internal_removable
    hs hX hw hthree hdel
  obtain ⟨M, hM, hgt⟩ := hs.exists_crossing_gt_one hb.matchingCovered.1 hX hr.notTight
  have hodd := hs.odd_shore hb.matchingCovered.1 hX
  have hpar := hM.crossing_mod_two X
  rw [Nat.odd_iff] at hodd
  have hne : (M ∩ H.dangling X).card ≠ 3 := fun hh ↦ hthree ⟨M, hM, hh⟩
  have h5 : 5 ≤ (M ∩ H.dangling X).card := by omega
  by_cases hc : ∀ w, H.degree w = 3
  · have hC := matching_boundary_of_cubic_oddWheel_contractions hwl hwr hc
    have hC5 : 5 ≤ (H.dangling X).card :=
      h5.trans (Finset.card_le_card Finset.inter_subset_right)
    have hno : ∀ e ∈ H.dangling X, ¬ (H.deleteEdge e).IsNearBrick := by
      intro e he hn
      exact hthree (hb.three_of_cubic_deleted_spoke ih hr hsl hsr hwl hwr hc hM h5 he hn)
    rcases step H hsimple hb X hr hsl hsr hwl hwr hC hC5 hno with h3 | hp
    · exact finish h3
    · exact (hnotP hp).elim
  · exact finish (hb.three_of_noncubic_oddWheel_contractions hsimple ih hr hsl hsr
      hwl hwr hc hM h5)

/-- The final cubic classification discharges the last premise of the
complete near-brick induction. -/
theorem nearBrickCutTheorem_of_cubic_twoWheel_classification
    (hfinal : CubicTwoWheelClassification.{u, v}) : NearBrickCutTheorem.{u, v} := by
  apply nearBrickCutTheorem_of_cubic_twoWheel_step
  intro V E _ _ _ _ H hs hb X hr hsl hsr hwl hwr hC h5 hno
  by_cases hthree : ∃ M, H.IsPerfectMatching M ∧ (M ∩ H.dangling X).card = 3
  · exact Or.inl hthree
  · exact Or.inr (hfinal H hs hb X hr hsl hsr hwl hwr hC h5 hno hthree)

end GraphPuzzles.LoopMultigraph
