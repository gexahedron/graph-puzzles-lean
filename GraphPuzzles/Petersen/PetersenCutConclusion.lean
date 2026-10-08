import GraphPuzzles.Petersen.PetersenCuts
import GraphPuzzles.Reduction.Parallel.ParallelPetersenTransport
import GraphPuzzles.Cuts.TrivialCutCharacteristic

/-! The Petersen terminal case of the near-brick induction. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- A Petersen graph with arbitrary parallel labels has precisely the
characteristic-five terminal alternative on its nontrivial separating cuts. -/
theorem IsPetersenUpToParallel.cutConclusion (hp : H.IsPetersenUpToParallel)
    {X : Finset V} (hs : H.IsSeparatingCut X) : H.NearBrickCutConclusion X := by
  by_cases hX : IsNontrivialCut X
  · obtain ⟨f⟩ := hp
    have hsP := (f.isSeparatingCut_iff_contract X).mp hs
    have hXP := (f.nontrivial_mapVertices X).mpr hX
    have hn := petersen_isBrick.nonbipartite_contractions hsP hXP
    have hstrict : petersen.IsStrictlySeparatingCut (f.mapVertices X) := ⟨hsP, hn.1, hn.2⟩
    refine Or.inr (Or.inr ⟨?_, .here ⟨f⟩ ((f.isStrictlySeparatingCut_iff X).mpr hstrict)⟩)
    exact (f.cutCharacteristic_mapVertices X).symm.trans
      (petersen_separatingCut_cutCharacteristic hsP hXP)
  · exact Or.inr (Or.inl (cutCharacteristic_eq_top_of_not_nontrivial hX))

theorem IsPetersen.cutConclusion (hp : H.IsPetersen) {X : Finset V}
    (hs : H.IsSeparatingCut X) : H.NearBrickCutConclusion X := by
  obtain ⟨f⟩ := hp
  exact (show H.IsPetersenUpToParallel from ⟨f.parallelReduction⟩).cutConclusion hs

end GraphPuzzles.LoopMultigraph
