import GraphPuzzles.Reduction.Parallel.ParallelSimplification
import GraphPuzzles.Reduction.Parallel.ParallelPetersenTransport
import GraphPuzzles.Reduction.Induction.NearBrickInduction

/-! The parallel-label reduction in the near-brick induction. -/

namespace GraphPuzzles.LoopMultigraph

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- A nonsimple near-brick reduces to its strictly smaller simple spanning
representative, preserving the selected cut and the entire Petersen alternative. -/
theorem IsNearBrick.cutConclusion_of_not_simple (hn : H.IsNearBrick)
    (hns : ¬ H.IsSimple) (ih : NearBrickCutInductionHypothesis.{u, v} H.inductionSize)
    {X : Finset V} (hs : H.IsSeparatingCut X) : H.NearBrickCutConclusion X := by
  have hlt : H.simpleParallelGraph.inductionSize < H.inductionSize := by
    have hc := H.card_simpleParallelEdges_lt hn.matchingCovered.loopless hns
    simp only [inductionSize]
    omega
  have hs' : H.simpleParallelGraph.IsSeparatingCut X := by
    simpa only [simpleParallelReduction_mapVertices] using
      (H.simpleParallelReduction.isSeparatingCut_iff_contract X).mp hs
  have hh := ih H.simpleParallelGraph hlt (H.simpleParallelGraph_isNearBrick_iff.mpr hn) X hs'
  apply NearBrickCutConclusion.of_parallelReduction H.simpleParallelReduction
  simpa only [simpleParallelReduction_mapVertices] using hh

end GraphPuzzles.LoopMultigraph
