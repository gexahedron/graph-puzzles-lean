import GraphPuzzles.Reduction.Induction.EdgeDeletionInduction

/-! The nontightness prerequisite for the edge-deletion case. -/

namespace GraphPuzzles.LoopMultigraph

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- A retained matching-covered contraction cannot become bipartite
after deleting an edge if it was originally nonbipartite. -/
theorem notBipartite_contract_deleteEdge {X : Finset V} {e : E}
    (hm : (H.contract X).IsMatchingCovered) (hn : ¬ (H.contract X).IsBipartite)
    (hd : ((H.deleteEdge e).contract X).IsMatchingCovered) :
    ¬ ((H.deleteEdge e).contract X).IsBipartite := by
  by_cases he : e ∈ H.meets X
  · let a : H.meets X := ⟨e, he⟩
    have hr : (H.contract X).IsRemovable a := (deleteContractIso X a).isMatchingCovered hd
    exact fun hb ↦ hr.notBipartite hm hn ((deleteContractIso X a).isBipartite hb)
  · exact fun hb ↦ hn ((deleteAwayContractIso X e he).isBipartite hb)

/-- A nontrivial separating cut of a brick remains strictly separating
whenever it remains separating after deleting one edge. -/
theorem IsBrick.strictlySeparatingCut_deleteEdge (hb : H.IsBrick)
    {X : Finset V} (hs : H.IsSeparatingCut X) (hX : IsNontrivialCut X)
    {e : E} (hd : (H.deleteEdge e).IsSeparatingCut X) :
    (H.deleteEdge e).IsStrictlySeparatingCut X := by
  have hn := hb.nonbipartite_contractions hs hX
  exact ⟨hd, notBipartite_contract_deleteEdge hs.1 hn.1 hd.1,
    notBipartite_contract_deleteEdge hs.2 hn.2 hd.2⟩

/-- The edge-deletion induction alternative with all nontightness
obligations discharged from the original brick and preserved separation. -/
theorem IsBrick.three_or_deleted_petersenMinor (hb : H.IsBrick)
    (ih : NearBrickCutInductionHypothesis.{u, v} H.inductionSize)
    {X : Finset V} (hs : H.IsSeparatingCut X) (hX : IsNontrivialCut X)
    {e : E} (hn : (H.deleteEdge e).IsNearBrick)
    (hd : (H.deleteEdge e).IsSeparatingCut X) :
    (∃ M, H.IsPerfectMatching M ∧ (M ∩ H.dangling X).card = 3) ∨
      (H.deleteEdge e).HasTightPetersenMinor X :=
  GraphPuzzles.LoopMultigraph.three_or_deleted_petersenMinor ih hn hd
    ((hb.strictlySeparatingCut_deleteEdge hs hX hd).not_tight hn) hX

end GraphPuzzles.LoopMultigraph
