import GraphPuzzles.CycleCovers.StrongProperties
import GraphPuzzles.CycleCovers.TwoCircuitFactor

/-! Critical cubic graphs and induced two-circuit factors have entire-layer strong 5CDC. -/

namespace GraphPuzzles
namespace LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- Critical cubic graphs satisfy the entire-layer strong property. -/
theorem IsCritical.hasEntireLayerStrongCycleDoubleCover (h : H.IsCritical)
    (hCubic : ∀ v, H.degree v = 3) : H.HasEntireLayerStrongCycleDoubleCover 5 :=
  fun C ↦ C.exists_fiveCycleDoubleCover_of_isCritical hCubic h

/-- Permutation factors give the entire-layer strong property. -/
theorem TwoCircuitFactor.IsInduced.hasEntireLayerStrongCycleDoubleCover
    {F : H.TwoCircuitFactor} (hF : F.IsInduced) (hCubic : ∀ v, H.degree v = 3)
    (hloopless : ∀ e, H.endAt e 0 ≠ H.endAt e 1) :
    H.HasEntireLayerStrongCycleDoubleCover 5 :=
  fun C ↦ F.exists_fiveCycleDoubleCover hCubic hF hloopless C


end LoopMultigraph
end GraphPuzzles
