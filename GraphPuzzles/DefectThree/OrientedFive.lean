import GraphPuzzles.DefectThree.StrongFive
import GraphPuzzles.DefectThree.HexagonOrientation
import GraphPuzzles.CycleCovers.OrientedTransport

/-!
# Oriented five-cycle double covers with the prescribed defect-three core

Every optimal matching triple in a snark of colouring defect three has an
induced hexagonal core. The oriented cover contains that entire core as one
indexed member. Auxiliary orientations are constructed rather than assumed.
-/

namespace GraphPuzzles
namespace LoopMultigraph

universe u v
variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E] {H : LoopMultigraph V E}

/-- The oriented five-cover theorem is independent of endpoint numbering. -/
theorem HasHexagonalCore.hasOrientedFive (h : H.HasHexagonalCore)
    (hCubic : ∀ v, H.degree v = 3)
    (hnc : ¬ ∃ g : E → Color, H.ProperOff ∅ g) : H.HasOrientedCycleDoubleCover 5 := by
  obtain ⟨ends, X, ⟨g⟩⟩ := h
  let f := H.relabelEndsIso ends
  have hc : ∀ v, (H.relabelEnds ends).degree v = 3 := by
    intro v
    exact (f.degree_eq v).trans (hCubic v)
  have hn : ¬ ∃ c : E → Color, (H.relabelEnds ends).ProperOff ∅ c := by
    rintro ⟨c, hc⟩
    exact hnc ⟨_, f.symm.properOff_empty hc⟩
  obtain ⟨D, _⟩ := g.exists_oriented_five_cover hc hn
  exact f.symm.hasOrientedCycleDoubleCover ⟨D⟩

namespace MatchingTriple

/-- The numerical core extraction retains the exact core of the chosen triple. -/
theorem IsOptimal.exists_hexagonalCore_eq_core {M : H.MatchingTriple} (ho : M.IsOptimal)
    (hu : M.uncovered.card = 3) (hc : ∀ w, H.degree w = 3)
    (hl : ∀ e, H.endAt e 0 ≠ H.endAt e 1)
    (hn : ¬ ∃ c : E → Color, H.ProperOff ∅ c) :
    ∃ ends : E → (Fin 2 ≃ Fin 2), ∃ X : (H.relabelEnds ends).Hexagon,
      X.edgeSet = M.core ∧ Nonempty X.ExteriorColoring := by
  have hr := ho.regular_of_uncovered_le_three hc hl hu.le
  obtain ⟨d, hd⟩ := M.exists_double_edges hc hn hr
  let D : M.DoubleFrame := ⟨d, hd⟩
  refine ⟨D.cyclicEnds hc hu, D.hexagon hc hu ho hr hn hl, ?_,
    ⟨D.exteriorColoring hc hu ho hr hn hl⟩⟩
  ext e
  rw [M.mem_core]
  change e ∈ Finset.univ.image (D.coreEdge hc hu) ↔ M.multiplicity e ≠ 1
  constructor
  · intro he
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
    rw [D.coreEdge_mult hc hu i]
    split_ifs <;> decide
  · intro he
    by_contra hnot
    have hoff : ∀ i, e ≠ D.coreEdge hc hu i := by
      intro i hi
      exact hnot (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi.symm⟩)
    exact he (D.mult_one_off_core hc hu ho hr hoff)

/-- The oriented cover has the chosen optimal triple's whole core as a member. -/
theorem IsOptimal.exists_orientedFiveCover_prescribed_core {M : H.MatchingTriple}
    (ho : M.IsOptimal) (hu : M.uncovered.card = 3) (hs : H.IsSnark) :
    ∃ D : H.OrientedCycleDoubleCover 5, D.Contains M.core := by
  obtain ⟨ends, X, hcore, ⟨g⟩⟩ :=
    ho.exists_hexagonalCore_eq_core hu hs.cubic hs.loopless hs.notColourable
  let f := H.relabelEndsIso ends
  have hc : ∀ w, (H.relabelEnds ends).degree w = 3 :=
    fun w ↦ (f.degree_eq w).trans (hs.cubic w)
  have hn : ¬ ∃ c : E → Color, (H.relabelEnds ends).ProperOff ∅ c := by
    rintro ⟨c, h⟩
    exact hs.notColourable ⟨_, f.symm.properOff_empty h⟩
  obtain ⟨D, hD⟩ := g.exists_oriented_five_cover hc hn
  refine ⟨f.symm.orientedCycleDoubleCover D, ?_⟩
  have h := f.symm.orientedCycleDoubleCover_contains hD
  simpa [EndpointIso.mapEdges, f, relabelEndsIso, EndpointIso.symm, hcore] using h

end MatchingTriple

/-- Numerical defect three in a snark implies o5CDC.
Auxiliary orientations are constructed in `HexagonOrientation`. -/
theorem HasColoringDefect.oriented_five (hd : H.HasColoringDefect 3) (hs : H.IsSnark)
    : H.HasOrientedCycleDoubleCover 5 :=
  (hd.hasHexagonalCore hs).hasOrientedFive hs.cubic hs.notColourable

end LoopMultigraph
end GraphPuzzles
