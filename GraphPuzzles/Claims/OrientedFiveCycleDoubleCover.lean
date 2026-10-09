import GraphPuzzles.Results.OrientedFiveCycleDoubleCover

namespace GraphPuzzles.Claims

open LoopMultigraph

universe u v
variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] {H : LoopMultigraph V E}

/-- Paper Theorem 2.1, for every chosen optimal matching triple. -/
theorem defect_three_oriented_five_prescribed_core (hs : H.IsSnark)
    (hd : H.HasColoringDefect 3) (M : H.MatchingTriple) (hopt : M.IsOptimal) :
    ∃ D : H.OrientedCycleDoubleCover 5, D.Contains M.core := by
  obtain ⟨N, hN, hoptN⟩ := hd
  have hupper := hopt N
  have hlower := hoptN M
  have hu : M.uncovered.card = 3 := by omega
  exact hopt.exists_orientedFiveCover_prescribed_core hu hs

/-- The numerical endpoint uses the proved defect-to-hexagon bridge. -/
theorem defect_three_oriented_five (hs : H.IsSnark) (hd : H.HasColoringDefect 3)
    : H.HasOrientedCycleDoubleCover 5 :=
  hd.oriented_five hs

/-- The structural version constructs the auxiliary orientations internally. -/
theorem hexagonal_core_oriented_five (hs : H.IsSnark) (hcore : H.HasHexagonalCore) :
    H.HasOrientedCycleDoubleCover 5 :=
  hcore.hasOrientedFive hs.cubic hs.notColourable

end GraphPuzzles.Claims
