import GraphPuzzles

/-! Compile the paper's conclusions using independent vertex/edge universes and only
their stated graph hypotheses. In particular, numerical defect three does not require
an assumed hexagon or an auxiliary exterior colouring. -/

open GraphPuzzles GraphPuzzles.LoopMultigraph

universe u v
variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] {H : LoopMultigraph V E}

example (hc : ∀ w, H.degree w = 3) (hcrit : H.IsCritical) (C : H.OrdinaryCircuit) :
    ∃ D : H.CycleDoubleCover 5, D.Contains C.edges :=
  GraphPuzzles.Claims.critical_entire_five hc hcrit C

example (hc : ∀ w, H.degree w = 3) (hl : ∀ e, H.endAt e 0 ≠ H.endAt e 1)
    (F : H.TwoCircuitFactor) (hF : F.IsInduced) (C : H.OrdinaryCircuit) :
    ∃ D : H.CycleDoubleCover 5, D.Contains C.edges :=
  GraphPuzzles.Claims.permutation_entire_five hc hl F hF C

example (hs : H.IsSnark) (hd : H.HasColoringDefect 3) (C : H.OrdinaryCircuit) :
    ∃ D : H.CycleDoubleCover 5, D.ContainsComponent C :=
  GraphPuzzles.Claims.defect_three_strong_five hs hd C
