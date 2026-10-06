import GraphPuzzles.CycleCovers.StrongProperties
import GraphPuzzles.CycleCovers.CircuitExtensionCorollaries
import GraphPuzzles.Graph.LoopMultigraphIso

/-! Covers are invariant under vertex and edge relabelling and independent endpoint reversals. -/

namespace GraphPuzzles
namespace LoopMultigraph

variable {V₁ E₁ V₂ E₂ : Type*}
  [Fintype V₁] [Fintype E₁] [Fintype V₂] [Fintype E₂]
  [DecidableEq V₁] [DecidableEq E₁] [DecidableEq V₂] [DecidableEq E₂]
variable {G₁ : LoopMultigraph V₁ E₁} {G₂ : LoopMultigraph V₂ E₂}

namespace EndpointIso

variable (f : EndpointIso G₁ G₂)

/-- Half-edges at corresponding vertices are in bijection. -/
def halfEdgesAtEquiv (v : V₁) : G₁.halfEdgesAt v ≃ G₂.halfEdgesAt (f.vertexEquiv v) :=
  f.halfEdgeEquiv.subtypeEquiv fun h ↦ by
    rw [f.vertex_halfEdgeEquiv]
    exact f.vertexEquiv.injective.eq_iff.symm

omit [DecidableEq E₁] [DecidableEq E₂] in
theorem degree_eq (v : V₁) : G₂.degree (f.vertexEquiv v) = G₁.degree v :=
  Fintype.card_congr (f.halfEdgesAtEquiv v).symm

omit [DecidableEq V₁] [DecidableEq E₁] [DecidableEq V₂] [DecidableEq E₂] in
/-- Transport a proper colouring of the entire graph. -/
theorem properOff_empty {c : E₁ → Color} (hc : G₁.ProperOff ∅ c) :
    G₂.ProperOff ∅ (fun e ↦ c (f.edgeEquiv.symm e)) := by
  refine ⟨fun e _ ↦ hc.1 _ (by simp), ?_⟩
  intro w _ x y _ _ hxy
  obtain ⟨v, rfl⟩ := f.vertexEquiv.surjective w
  obtain ⟨x, rfl⟩ := (f.halfEdgesAtEquiv v).surjective x
  obtain ⟨y, rfl⟩ := (f.halfEdgesAtEquiv v).surjective y
  apply congrArg (f.halfEdgesAtEquiv v)
  apply hc.2 v (by simp) x y (by simp) (by simp)
  change c (f.edgeEquiv.symm (f.edgeEquiv x.1.1)) =
    c (f.edgeEquiv.symm (f.edgeEquiv y.1.1)) at hxy
  simpa only [Equiv.symm_apply_apply] using hxy

/-- Transport a bounded cycle double cover. -/
def cycleDoubleCover {k : ℕ} (D : G₁.CycleDoubleCover k) : G₂.CycleDoubleCover k where
  cycles i := ⟨f.mapEdges (D.cycles i).edges,
    (f.isEvenEdgeSet_mapEdges _).mpr (D.cycles i).even⟩
  coveredTwice e := by
    obtain ⟨e, rfl⟩ := f.edgeEquiv.surjective e
    simpa using D.coveredTwice e

theorem cycleDoubleCover_contains {k : ℕ} {D : G₁.CycleDoubleCover k} {F : Finset E₁}
    (h : D.Contains F) : (f.cycleDoubleCover D).Contains (f.mapEdges F) := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i, congrArg f.mapEdges hi⟩

theorem component_mapEdges {C : G₁.OrdinaryCircuit} {F : Finset E₁}
    (h : C.IsComponentOf F) : (f.ordinaryCircuit C).IsComponentOf (f.mapEdges F) := by
  refine ⟨?_, ?_⟩
  · intro e' he
    obtain ⟨e, rfl⟩ := f.edgeEquiv.surjective e'
    exact (f.mem_mapEdges F e).mpr (h.1 ((f.mem_mapEdges C.edges e).mp he))
  · intro e' he i hi
    obtain ⟨e, rfl⟩ := f.edgeEquiv.surjective e'
    obtain ⟨heF, heC⟩ := Finset.mem_sdiff.mp he
    have hnot : e ∉ C.edges := fun he ↦ heC ((f.mem_mapEdges C.edges e).mpr he)
    apply h.2 e (Finset.mem_sdiff.mpr ⟨(f.mem_mapEdges F e).mp heF, hnot⟩)
      ((f.endEquiv e).symm i)
    apply (f.mem_edgeSupport_mapEdges C.edges _).mp
    have hv : f.vertexEquiv (G₁.endAt e ((f.endEquiv e).symm i)) =
        G₂.endAt (f.edgeEquiv e) i := by
      simpa only [Equiv.apply_symm_apply] using f.map_endAt e ((f.endEquiv e).symm i)
    rw [hv]
    exact hi

include f in
theorem hasStrongCycleDoubleCover {k : ℕ} (h : G₁.HasStrongCycleDoubleCover k) :
    G₂.HasStrongCycleDoubleCover k := by
  intro C
  obtain ⟨D, i, hi⟩ := h (f.symm.ordinaryCircuit C)
  refine ⟨f.cycleDoubleCover D, i, ?_⟩
  have ht := f.component_mapEdges hi
  have hround : f.mapEdges (f.symm.mapEdges C.edges) = C.edges := by
    ext e
    simp [mapEdges, symm]
  simpa only [OrdinaryCircuit.IsComponentOf, ordinaryCircuit, cycleDoubleCover, hround] using ht

include f in
/-- Entire-layer strong covers are invariant under isomorphism. -/
theorem hasEntireLayerStrongCycleDoubleCover {k : ℕ}
    (h : G₁.HasEntireLayerStrongCycleDoubleCover k) :
    G₂.HasEntireLayerStrongCycleDoubleCover k := by
  intro C
  obtain ⟨D, hD⟩ := h (f.symm.ordinaryCircuit C)
  refine ⟨f.cycleDoubleCover D, ?_⟩
  have ht := f.cycleDoubleCover_contains hD
  have hround : f.mapEdges (f.symm.mapEdges C.edges) = C.edges := by
    ext e
    simp [mapEdges, symm]
  simpa only [EndpointIso.ordinaryCircuit, hround] using ht

end EndpointIso

end LoopMultigraph
end GraphPuzzles
