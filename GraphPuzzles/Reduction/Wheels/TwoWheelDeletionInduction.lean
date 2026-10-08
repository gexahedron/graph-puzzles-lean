import GraphPuzzles.Petersen.PetersenMatchingBoundary
import GraphPuzzles.Reduction.Wheels.TwoWheelNoncubic
import GraphPuzzles.Reduction.Induction.DeletedSeparatingCut

/-! The induction step after deleting a spoke from a perfect-matching cut. -/

namespace GraphPuzzles.LoopMultigraph

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E} {X : Finset V}

/-- Every spoke preserves separation when the two solid wheel shores
have at least five rim vertices. -/
theorem IsRobustCut.deleteEdge_separating_of_oddWheel_spoke
    (hr : H.IsRobustCut X) (hsl : (H.contract X).IsSolid)
    (hsr : (H.contract (Finset.univ \ X)).IsSolid)
    (hwl : (H.contract X).IsOddWheel none)
    (hwr : (H.contract (Finset.univ \ X)).IsOddWheel none)
    {M : Finset E} (hM : H.IsPerfectMatching M)
    (h5 : 5 ≤ (M ∩ H.dangling X).card) {e : E} (he : e ∈ H.dangling X) :
    (H.deleteEdge e).IsSeparatingCut X := by
  obtain ⟨Wl⟩ := hwl
  obtain ⟨Wr⟩ := hwr
  have hc : e ∈ H.dangling (Finset.univ \ X) := by simpa only [dangling_compl] using he
  have hcl : 5 ≤ X.card := h5.trans (hM.crossing_le_card X)
  have hcr : 5 ≤ (Finset.univ \ X).card := by
    have hh := hM.crossing_le_card (Finset.univ \ X)
    rw [dangling_compl] at hh
    omega
  have hl := (deleteContractIso X ⟨e, dangling_subset_meets X he⟩).symm.isNearBrick
    (hr.leftNear.deleteEdge_of_solid hsl (Wl.isRemovable_cut_label hcl he))
  have hh := (deleteContractIso (Finset.univ \ X) ⟨e, dangling_subset_meets _ hc⟩).symm.isNearBrick
    (hr.rightNear.deleteEdge_of_solid hsr (Wr.isRemovable_cut_label hcr hc))
  exact ⟨hl.matchingCovered, hh.matchingCovered⟩

/-- A near-brick deletion from a perfect-matching cut discharges its
Petersen alternative by the restored two-fiber matching. -/
theorem IsBrick.three_of_deleted_matching_cut (hb : H.IsBrick)
    (ih : NearBrickCutInductionHypothesis.{u, v} H.inductionSize)
    (hs : H.IsSeparatingCut X) (hX : IsNontrivialCut X)
    (hC : H.IsPerfectMatching (H.dangling X)) {e : E} (he : e ∈ H.dangling X)
    (hn : (H.deleteEdge e).IsNearBrick) (hd : (H.deleteEdge e).IsSeparatingCut X) :
    ∃ M, H.IsPerfectMatching M ∧ (M ∩ H.dangling X).card = 3 := by
  rcases hb.three_or_deleted_petersenMinor ih hs hX hn hd with h3 | hp
  · exact h3
  · obtain ⟨R, hbi⟩ := hp.exists_bipartite_fiberModel hn
    exact R.exists_three_crossing_of_matching_cut hb hn.matchingCovered
      hn.matchingCovered hbi hC he

/-- The cubic two-wheel case is settled whenever a selected spoke is
b-removable. This is the matching construction of Proposition 6.11. -/
theorem IsBrick.three_of_cubic_deleted_spoke (hb : H.IsBrick)
    (ih : NearBrickCutInductionHypothesis.{u, v} H.inductionSize)
    (hr : H.IsRobustCut X) (hsl : (H.contract X).IsSolid)
    (hsr : (H.contract (Finset.univ \ X)).IsSolid)
    (hwl : (H.contract X).IsOddWheel none)
    (hwr : (H.contract (Finset.univ \ X)).IsOddWheel none)
    (hc : ∀ w, H.degree w = 3) {M : Finset E} (hM : H.IsPerfectMatching M)
    (h5 : 5 ≤ (M ∩ H.dangling X).card) {e : E} (he : e ∈ H.dangling X)
    (hn : (H.deleteEdge e).IsNearBrick) :
    ∃ N, H.IsPerfectMatching N ∧ (N ∩ H.dangling X).card = 3 := by
  exact hb.three_of_deleted_matching_cut ih hr.isSeparatingCut
    (hr.nontrivial hb.matchingCovered)
    (matching_boundary_of_cubic_oddWheel_contractions hwl hwr hc) he hn
    (hr.deleteEdge_separating_of_oddWheel_spoke hsl hsr hwl hwr hM h5 he)

end GraphPuzzles.LoopMultigraph
