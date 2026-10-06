import GraphPuzzles.Results.StrongFiveCycleDoubleCover

namespace GraphPuzzles.Claims

open LoopMultigraph

universe u v
variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] {H : LoopMultigraph V E}

/-- Paper Theorem 1.1: an entire prescribed circuit is equivalent to colouring `G − V(C)`. -/
theorem prescribed_circuit_five_iff (hc : ∀ w, H.degree w = 3) (C : H.OrdinaryCircuit) :
    (∃ D : H.CycleDoubleCover 5, D.Contains C.edges) ↔
      ∃ g, H.ProperOff (H.edgeSupport C.edges) g :=
  C.exists_fiveCycleDoubleCover_iff_properOff hc

/-- Paper Theorem 1.2, critical case: the prescribed circuit is an entire member. -/
theorem critical_entire_five (hc : ∀ w, H.degree w = 3) (hcrit : H.IsCritical) :
    H.HasEntireLayerStrongCycleDoubleCover 5 :=
  hcrit.hasEntireLayerStrongCycleDoubleCover hc

/-- The standard component conclusion for critical cubic graphs. -/
theorem critical_strong_five (hc : ∀ w, H.degree w = 3) (hcrit : H.IsCritical) :
    H.HasStrongCycleDoubleCover 5 :=
  (critical_entire_five hc hcrit).strong

/-- Paper Theorem 1.2, permutation case: two induced spanning circuits suffice. -/
theorem permutation_entire_five (hc : ∀ w, H.degree w = 3)
    (hl : ∀ e, H.endAt e 0 ≠ H.endAt e 1) (F : H.TwoCircuitFactor) (hF : F.IsInduced) :
    H.HasEntireLayerStrongCycleDoubleCover 5 :=
  hF.hasEntireLayerStrongCycleDoubleCover hc hl

/-- The standard component conclusion for cubic permutation graphs. -/
theorem permutation_strong_five (hc : ∀ w, H.degree w = 3)
    (hl : ∀ e, H.endAt e 0 ≠ H.endAt e 1) (F : H.TwoCircuitFactor) (hF : F.IsInduced) :
    H.HasStrongCycleDoubleCover 5 :=
  (permutation_entire_five hc hl F hF).strong

/-- Paper Theorem 1.3: the induced hexagon with spoke word `aabbcc` gives component strong 5CDC. -/
theorem hexagonal_core_strong_five (hc : ∀ w, H.degree w = 3)
    (X : H.Hexagon) (g : X.ExteriorColoring) : H.HasStrongCycleDoubleCover 5 :=
  g.hasStrongCycleDoubleCover hc

/-- Paper Corollary 1.4: numerical defect three in a snark gives component strong 5CDC. -/
theorem defect_three_strong_five (hs : H.IsSnark) (hd : H.HasColoringDefect 3) :
    H.HasStrongCycleDoubleCover 5 :=
  hd.strong_five hs

end GraphPuzzles.Claims
