import GraphPuzzles.Reduction.Induction.NearBrickInduction
import GraphPuzzles.Cuts.Shores.DeletedTightShore

/-! The decreasing edge-deletion step of the near-brick induction. -/

namespace GraphPuzzles.LoopMultigraph

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

omit [DecidableEq V] in
theorem inductionSize_deleteEdge_lt (e : E) :
    (H.deleteEdge e).inductionSize < H.inductionSize := by
  have hh := Finset.card_erase_lt_of_mem (Finset.mem_univ e)
  simpa only [inductionSize, Fintype.card_coe, Finset.card_univ, Nat.add_lt_add_iff_left] using hh

/-- A nontight separating cut in a smaller near-brick obtained by deleting
one edge either gives the required original matching or a Petersen certificate. -/
theorem three_or_deleted_petersenMinor
    (ih : NearBrickCutInductionHypothesis.{u, v} H.inductionSize)
    {e : E} (hn : (H.deleteEdge e).IsNearBrick) {X : Finset V}
    (hs : (H.deleteEdge e).IsSeparatingCut X) (hnt : ¬ (H.deleteEdge e).IsTightCut X)
    (hX : IsNontrivialCut X) :
    (∃ M, H.IsPerfectMatching M ∧ (M ∩ H.dangling X).card = 3) ∨
      (H.deleteEdge e).HasTightPetersenMinor X := by
  have ho := hs.odd_shore hn.matchingCovered.1 hX
  rcases ih (H.deleteEdge e) (inductionSize_deleteEdge_lt e) hn X hs with h3 | ht | ⟨_, hp⟩
  · exact Or.inl (exists_matching_crossing_of_restrictEdges
      ((cutCharacteristic_eq_three_iff ho).mp h3))
  · exact (hnt ((cutCharacteristic_eq_top_iff_tight ho).mp ht)).elim
  · exact Or.inr hp

end GraphPuzzles.LoopMultigraph
