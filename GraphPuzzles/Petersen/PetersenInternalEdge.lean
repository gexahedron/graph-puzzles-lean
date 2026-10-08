import GraphPuzzles.Petersen.PetersenTwoRestoredFibers
import GraphPuzzles.Petersen.Minors.DeletedPetersenSingleFiber
import GraphPuzzles.Reduction.Induction.DeletedSeparatingCut

/-! Completing the internal removable-edge case of Section 6. -/

namespace GraphPuzzles.LoopMultigraph

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E} {e : E} {X : Finset V}

namespace PetersenFiberModel

/-- The restored endpoints determine every possible nonsingleton fiber.
The zero-, one-, and two-fiber matching constructions exhaust the cases. -/
theorem exists_three_crossing_of_endpoints_in_shore
    (R : (H.deleteEdge e).PetersenFiberModel X) (hb : H.IsBrick) (hsimple : H.IsSimple)
    (hr : H.IsRemovable e) (hm : (H.deleteEdge e).IsMatchingCovered)
    (hbi : ∀ w, (H.deleteEdge e).IsBipartiteOn (R.quotient.fiber w))
    (hs : (H.deleteEdge e).IsSeparatingCut X) (hX : IsNontrivialCut X)
    (heX : ∀ k, H.endAt e k ∈ X) :
    ∃ M, H.IsPerfectMatching M ∧ (M ∩ H.dangling X).card = 3 := by
  let p := R.canonicalVertex (H.endAt e 0)
  let q := R.canonicalVertex (H.endAt e 1)
  have haway : ∀ r, r ≠ p → r ≠ q → (R.canonicalFiber r).card ≤ 1 :=
    fun _ hp hq ↦ R.singleton_away_from_restored_endpoints hb hr hm hbi hp hq
  by_cases hpq : p = q
  · apply R.exists_three_crossing_of_single_fiber hb hsimple hr hm hbi hs hX p
    intro r hr
    exact haway r hr (by rwa [← hpq])
  · by_cases h0 : 2 ≤ (R.canonicalFiber p).card
    · by_cases h1 : 2 ≤ (R.canonicalFiber q).card
      · exact R.exists_three_crossing_two_restored_fibers hb hr hm hbi heX hpq h0 h1
      · apply R.exists_three_crossing_of_single_fiber hb hsimple hr hm hbi hs hX p
        intro r hr
        by_cases hrq : r = q
        · subst r
          omega
        · exact haway r hr hrq
    · apply R.exists_three_crossing_of_single_fiber hb hsimple hr hm hbi hs hX q
      intro r hr
      by_cases hrp : r = p
      · subst r
        omega
      · exact haway r hrp hr

/-- Restoring an edge internal to either selected shore always destroys
the deleted Petersen obstruction by a three-crossing perfect matching. -/
theorem exists_three_crossing_of_internal_edge
    (R : (H.deleteEdge e).PetersenFiberModel X) (hb : H.IsBrick) (hsimple : H.IsSimple)
    (hr : H.IsRemovable e) (hm : (H.deleteEdge e).IsMatchingCovered)
    (hbi : ∀ w, (H.deleteEdge e).IsBipartiteOn (R.quotient.fiber w))
    (hs : (H.deleteEdge e).IsSeparatingCut X) (hX : IsNontrivialCut X) (he : e ∉ H.dangling X) :
    ∃ M, H.IsPerfectMatching M ∧ (M ∩ H.dangling X).card = 3 := by
  have hiff : H.endAt e 0 ∈ X ↔ H.endAt e 1 ∈ X := by
    by_contra hn
    exact he (mem_dangling.mpr hn)
  by_cases h0 : H.endAt e 0 ∈ X
  · apply R.exists_three_crossing_of_endpoints_in_shore hb hsimple hr hm hbi hs hX
    intro k
    fin_cases k
    · exact h0
    · exact hiff.mp h0
  · have heC : ∀ k, H.endAt e k ∈ Finset.univ \ X := by
      intro k
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      fin_cases k
      · exact h0
      · exact fun h1 ↦ h0 (hiff.mpr h1)
    obtain ⟨M, hM, hMC⟩ := R.compl.exists_three_crossing_of_endpoints_in_shore
      hb hsimple hr hm hbi hs.compl hX.compl heC
    exact ⟨M, hM, by simpa only [dangling_compl] using hMC⟩

end PetersenFiberModel

/-- Campos–Lucchesi Section 6, Case 6: an internal b-removable edge
whose deletion preserves the selected separating cut gives characteristic three. -/
theorem IsBrick.exists_three_crossing_of_internal_deleted_nearBrick
    (hb : H.IsBrick) (hsimple : H.IsSimple)
    (ih : NearBrickCutInductionHypothesis.{u, v} H.inductionSize)
    (hs : H.IsSeparatingCut X) (hX : IsNontrivialCut X)
    (hn : (H.deleteEdge e).IsNearBrick) (hd : (H.deleteEdge e).IsSeparatingCut X)
    (he : e ∉ H.dangling X) :
    ∃ M, H.IsPerfectMatching M ∧ (M ∩ H.dangling X).card = 3 := by
  rcases hb.three_or_deleted_petersenMinor ih hs hX hn hd with h3 | hp
  · exact h3
  · obtain ⟨R, hbi⟩ := hp.exists_bipartite_fiberModel hn
    exact R.exists_three_crossing_of_internal_edge hb hsimple hn.matchingCovered
      hn.matchingCovered hbi hd hX he

end GraphPuzzles.LoopMultigraph
