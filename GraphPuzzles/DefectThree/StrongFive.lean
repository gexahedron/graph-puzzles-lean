import GraphPuzzles.DefectThree.DefectThreeCore
import GraphPuzzles.DefectThree.HexagonStrong
import GraphPuzzles.CycleCovers.CoverTransportBasic
import GraphPuzzles.Graph.Connectivity
import GraphPuzzles.Graph.Bridgeless

/-! Numerical colouring defect three implies the standard component strong 5CDC.
The optimal matching triple constructs the hexagonal exterior colouring; it is not assumed. -/

namespace GraphPuzzles
namespace LoopMultigraph

universe u v
variable {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- A snark without girth or cyclic-connectivity restrictions. -/
structure IsSnark (H : LoopMultigraph V E) : Prop where
  connected : H.IsConnected
  bridgeless : H.IsBridgeless
  loopless : ∀ e, H.endAt e 0 ≠ H.endAt e 1
  cubic : ∀ v, H.degree v = 3
  notColourable : ¬ ∃ g : E → Color, H.ProperOff ∅ g

/-- An induced hexagon with the exterior spoke word `aabbcc`, after endpoint renumbering. -/
def HasHexagonalCore (H : LoopMultigraph V E) : Prop :=
  ∃ ends : E → (Fin 2 ≃ Fin 2), ∃ X : (H.relabelEnds ends).Hexagon,
    Nonempty X.ExteriorColoring

/-- Numerical defect three in a snark supplies a hexagonal core.
This statement is proved below by `defectThreeHexagon`. -/
def DefectThreeHexagon : Prop :=
  ∀ {V' : Type u} {E' : Type v} [Fintype V'] [Fintype E'] [DecidableEq V'] [DecidableEq E']
    (H : LoopMultigraph V' E'), H.IsSnark → H.HasColoringDefect 3 → H.HasHexagonalCore

variable {H : LoopMultigraph V E}

/-- Extract the induced hexagon and its exterior colouring from an optimal matching triple. -/
theorem HasColoringDefect.hasHexagonalCore (hd : H.HasColoringDefect 3) (hs : H.IsSnark) :
    H.HasHexagonalCore := by
  obtain ⟨M, hu, ho⟩ := hd
  exact ho.exists_hexagonalCore hu hs.cubic hs.loopless hs.notColourable

/-- KMNS Theorem 3.3, implication (i) → (iii), restricted to snarks. -/
theorem defectThreeHexagon : DefectThreeHexagon.{u, v} := by
  intro V' E' _ _ _ _ H hs hd
  exact hd.hasHexagonalCore hs

/-- A single hexagonal core suffices for the standard component form of strong 5CDC,
independently of endpoint numbering. -/
theorem HasHexagonalCore.hasStrongFive (h : H.HasHexagonalCore)
    (hCubic : ∀ v, H.degree v = 3) : H.HasStrongCycleDoubleCover 5 := by
  obtain ⟨ends, X, ⟨g⟩⟩ := h
  let f := H.relabelEndsIso ends
  have hc : ∀ v, (H.relabelEnds ends).degree v = 3 := fun v ↦
    (f.degree_eq v).trans (hCubic v)
  exact f.symm.hasStrongCycleDoubleCover (g.hasStrongCycleDoubleCover hc)

/-- **Defect-three strong 5CDC.** Every prescribed circuit is a component of one of five
even layers. The hexagonal core is constructed from the optimal matching triple. -/
theorem HasColoringDefect.strong_five (hd : H.HasColoringDefect 3) (hs : H.IsSnark)
    : H.HasStrongCycleDoubleCover 5 :=
  (hd.hasHexagonalCore hs).hasStrongFive hs.cubic


end LoopMultigraph
end GraphPuzzles
