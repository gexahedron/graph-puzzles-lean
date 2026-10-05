import GraphPuzzles.Results.CycleDoubleCover

namespace GraphPuzzles.Claims

open LoopMultigraph

universe u v
variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] {H : LoopMultigraph V E}

/-- Every finite bridgeless multigraph has an ordinary circuit double cover. -/
theorem cycle_double_cover (hb : H.IsBridgeless) :
    ∃ L : List H.OrdinaryCircuit, ∀ e : E,
      (L.filter fun C ↦ e ∈ C.edges).length = 2 := by
  obtain ⟨D⟩ := H.exists_ordinaryCycleDoubleCover hb
  exact ⟨D.circuits, D.coveredTwice⟩

/-- Eight even layers, which may be empty or disconnected. -/
theorem eight_cycle_double_cover (hb : H.IsBridgeless) :
    Nonempty (H.CycleDoubleCover 8) := H.exists_eightCycleDoubleCover hb

end GraphPuzzles.Claims
