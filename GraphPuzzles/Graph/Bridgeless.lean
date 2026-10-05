import GraphPuzzles.Graph.LoopMultigraph

/-! Bridgelessness in the endpoint-multigraph model, independent of matching theory. -/

namespace GraphPuzzles.LoopMultigraph

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]

/-- The ends of every edge receive the same colour under every two-colouring
constant along the other edges. Loops satisfy this condition automatically. -/
def IsBridgeless (H : LoopMultigraph V E) : Prop :=
  ∀ e, ∀ c : V → Bool, (∀ f, f ≠ e → c (H.endAt f 0) = c (H.endAt f 1)) →
    c (H.endAt e 0) = c (H.endAt e 1)

end GraphPuzzles.LoopMultigraph
