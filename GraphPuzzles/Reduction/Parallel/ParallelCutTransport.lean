import GraphPuzzles.Reduction.Parallel.ParallelContraction
import GraphPuzzles.Cuts.CutWitness

/-! Strictly separating cuts are preserved by parallel-edge reduction. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E W F : Type*} [Fintype V] [Fintype E] [Fintype W] [Fintype F]
  [DecidableEq V] [DecidableEq E] [DecidableEq W] [DecidableEq F]
  {H : LoopMultigraph V E} {K : LoopMultigraph W F}

theorem ParallelReduction.isStrictlySeparatingCut_iff (f : ParallelReduction H K)
    (X : Finset V) :
    H.IsStrictlySeparatingCut X ↔ K.IsStrictlySeparatingCut (f.mapVertices X) := by
  have hsep := f.isSeparatingCut_iff_contract X
  have hl := (f.contract X).isBipartite_iff
  have hr := (f.contract (Finset.univ \ X)).isBipartite_iff
  rw [f.mapVertices_compl] at hr
  constructor
  · intro hs
    exact ⟨hsep.mp hs.separating, fun hb ↦ hs.leftNonbipartite (hl.mpr hb),
      fun hb ↦ hs.rightNonbipartite (hr.mpr hb)⟩
  · intro hs
    exact ⟨hsep.mpr hs.separating, fun hb ↦ hs.leftNonbipartite (hl.mp hb),
      fun hb ↦ hs.rightNonbipartite (hr.mp hb)⟩

end GraphPuzzles.LoopMultigraph
