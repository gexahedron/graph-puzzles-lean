import GraphPuzzles.Reduction.Wheels.OddWheelNearBrick
import GraphPuzzles.Reduction.Removable.RemovableContraction
import GraphPuzzles.Reduction.Removable.DoubletonCrossing
import GraphPuzzles.Bricks.BrickEdgeConnectivity
import GraphPuzzles.Reduction.Induction.WitnessContraction

/-! The odd-wheel contraction reduction in Section 6, Proposition 6.7. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- With the removable-edge and doubleton cases excluded, a solid
robust-cut contraction is an odd wheel with the contraction pole as hub. -/
theorem IsBrick.oddWheel_contract_of_no_internal_removable (hb : H.IsBrick)
    {X : Finset V} (hr : H.IsRobustCut X) (hs : (H.contract X).IsSolid)
    (hthree : ¬ ∃ M, H.IsPerfectMatching M ∧ (M ∩ H.dangling X).card = 3)
    (hdel : ∀ e, (∀ k, H.endAt e k ∈ X) → (H.deleteEdge e).IsNearBrick →
      (H.deleteEdge e).IsSeparatingCut X → False) :
    (H.contract X).IsOddWheel none := by
  obtain ⟨M, hM, hcross⟩ := hr.isSeparatingCut.exists_crossing_gt_one
    hb.matchingCovered.1 (hr.nontrivial hb.matchingCovered) hr.notTight
  have h3 := hb.isThreeEdgeConnected.contract X
    (Finset.card_pos.mp (by have := (hr.nontrivial hb.matchingCovered).2; omega))
  have hvm : (H.contract X).IsVertexMatching none (H.contractMatching X M) := by
    intro w hw
    cases w with
    | none => exact (hw rfl).elim
    | some w => rw [contractMatching, contract_degreeIn_some]; exact hM w.1
  rcases hr.leftNear.oddWheel_or_removable_of_solid h3 hs hvm with hw | ⟨e, heM, hev, he⟩
  · exact hw
  · have heX : ∀ k, H.endAt e.1 k ∈ X := by
      intro k
      by_contra hk
      exact hev k (by change contractVertex X (H.endAt e.1 k) = none; simp [contractVertex, hk])
    rcases he with he | ⟨f, _, _, hef⟩
    · have hm : e.1 ∉ M := fun hh ↦ heM ((mem_contractMatching X M e).mpr hh)
      have hh := hr.deleteEdge_of_internal_removable hs heX he hM hm hcross
      exact (hdel e.1 heX hh.2.2 hh.2.1.isSeparatingCut).elim
    · exact (hthree (hr.exists_three_crossing_of_removableDoubleton hb.matchingCovered hef)).elim

/-- Proposition 6.7, simultaneously for both shores. -/
theorem IsBrick.oddWheel_contractions_of_no_witness_or_internal_removable
    (hb : H.IsBrick) {X : Finset V} (hs : H.IsSeparatingCut X) (hX : IsNontrivialCut X)
    (hw : ¬ ∃ Y, H.IsCutWitness X Y)
    (hthree : ¬ ∃ M, H.IsPerfectMatching M ∧ (M ∩ H.dangling X).card = 3)
    (hdel : ∀ e, e ∉ H.dangling X → (H.deleteEdge e).IsNearBrick →
      (H.deleteEdge e).IsSeparatingCut X → False) :
    (H.contract X).IsOddWheel none ∧
      (H.contract (Finset.univ \ X)).IsOddWheel none := by
  rcases hs.witness_or_robust_solid hb hX with hh | ⟨hr, hsl, hsr⟩
  · exact (hw hh).elim
  have hleft := hb.oddWheel_contract_of_no_internal_removable hr hsl hthree
    (fun e he ↦ hdel e (by simp [mem_dangling, he 0, he 1]))
  have hthree' : ¬ ∃ M, H.IsPerfectMatching M ∧
      (M ∩ H.dangling (Finset.univ \ X)).card = 3 := by
    simpa only [dangling_compl] using hthree
  refine ⟨hleft, hb.oddWheel_contract_of_no_internal_removable hr.compl hsr hthree' ?_⟩
  intro e he hn hs
  apply hdel e (by
    have h0 := (Finset.mem_sdiff.mp (he 0)).2
    have h1 := (Finset.mem_sdiff.mp (he 1)).2
    simp [mem_dangling, h0, h1]) hn
  simpa only [Finset.sdiff_sdiff_eq_self (Finset.subset_univ X)] using hs.compl

end GraphPuzzles.LoopMultigraph
