import GraphPuzzles.Graph.LoopMultigraph

/-! Connectivity without a matching-theory dependency. -/

namespace GraphPuzzles
namespace LoopMultigraph

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (H : LoopMultigraph V E)

/-- Connected: every two-colouring of the vertices constant along the edges is constant. -/
def IsConnected : Prop :=
  ∀ c : V → Bool, (∀ e, c (H.endAt e 0) = c (H.endAt e 1)) → ∀ u w, c u = c w


end LoopMultigraph
end GraphPuzzles
