import GraphPuzzles.CycleCovers.General.Decomposition
import GraphPuzzles.CycleCovers.General.Transport

/-! The cycle double cover theorem for arbitrary finite endpoint multigraphs. -/

namespace GraphPuzzles.LoopMultigraph

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] {H : LoopMultigraph V E}

/-- Every finite bridgeless multigraph has eight even layers covering each edge twice.
Loops, parallel edges, isolated vertices, disconnected graphs and empty graphs are allowed. -/
theorem exists_eightCycleDoubleCover (hb : H.IsBridgeless) :
    Nonempty (H.CycleDoubleCover 8) := by
  obtain ⟨D⟩ := CycleDoubleCoverProof.exists_indexed_even_cover
    (CycleDoubleCoverProof.nonLoopGraph H)
    (CycleDoubleCoverProof.nonLoopGraph_bridgeless H hb)
  exact ⟨CycleDoubleCoverProof.toEightCover D⟩

/-- The ordinary-circuit form of the cycle double cover theorem. -/
theorem exists_ordinaryCycleDoubleCover (hb : H.IsBridgeless) :
    Nonempty H.OrdinaryCycleDoubleCover := by
  obtain ⟨D⟩ := exists_eightCycleDoubleCover hb
  exact ⟨D.toOrdinary⟩

/-- The exact frozen statement, with independently polymorphic vertex and edge universes. -/
theorem cycleDoubleCover : CycleDoubleCoverTheorem.{u, v} :=
  fun _ _ _ _ _ _ _ hb ↦ exists_ordinaryCycleDoubleCover hb

end GraphPuzzles.LoopMultigraph
