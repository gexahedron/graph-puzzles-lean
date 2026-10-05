import GraphPuzzles.Results.Sabidussi

namespace GraphPuzzles.Claims

open LoopMultigraph

universe u v
variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] {H : LoopMultigraph V E}

/-- The ordinary-circuit conclusion of Sabidussi compatibility. -/
theorem sabidussi_compatibility (T : H.EulerTour) (hmin : ∀ w, 4 ≤ H.degree w) :
    ∃ S : H.OrdinaryCircuitDecomposition, S.Compatible T :=
  loop_sabidussi_compatibility_ordinary T hmin

/-- A dominating circuit is an entire layer in a five-cycle double cover. -/
theorem dominating_circuit_five (hc : ∀ w, H.degree w = 3)
    (C : H.OrdinaryCircuit) (hC : C.Dominates) :
    ∃ D : H.CycleDoubleCover 5, D.Contains C.edges :=
  C.exists_fiveCycleDoubleCover_containing hc hC

end GraphPuzzles.Claims
