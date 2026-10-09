import GraphPuzzles.CycleCovers.OrientedProperties
import GraphPuzzles.CycleCovers.CoverTransportBasic

/-! Covers are invariant under vertex and edge relabelling and independent endpoint reversals. -/

namespace GraphPuzzles
namespace LoopMultigraph

variable {V₁ E₁ V₂ E₂ : Type*}
  [Fintype V₁] [Fintype E₁] [Fintype V₂] [Fintype E₂]
  [DecidableEq V₁] [DecidableEq E₁] [DecidableEq V₂] [DecidableEq E₂]
variable {G₁ : LoopMultigraph V₁ E₁} {G₂ : LoopMultigraph V₂ E₂}

namespace EndpointIso

variable (f : EndpointIso G₁ G₂)

/-- The tails of a directed subgraph after relabelling. -/
def mapTail (tail : E₁ → Fin 2) (e : E₂) : Fin 2 :=
  f.endEquiv (f.edgeEquiv.symm e) (tail (f.edgeEquiv.symm e))

/-- Transport a directed even subgraph. -/
def directedCycle (D : G₁.DirectedCycle) : G₂.DirectedCycle where
  edges := f.mapEdges D.edges
  tail := f.mapTail D.tail
  balanced w := by
    obtain ⟨v, rfl⟩ := f.vertexEquiv.surjective w
    have hcount (select : Fin 2 → Fin 2 → Prop) [DecidableRel select]
        (hs : ∀ e i j, select (f.endEquiv e i) (f.endEquiv e j) ↔ select i j) :
        (Finset.univ.filter fun x : G₂.halfEdgesAt (f.vertexEquiv v) ↦
          x.1.1 ∈ f.mapEdges D.edges ∧ select x.1.2 (f.mapTail D.tail x.1.1)).card =
        (Finset.univ.filter fun x : G₁.halfEdgesAt v ↦
          x.1.1 ∈ D.edges ∧ select x.1.2 (D.tail x.1.1)).card := by
      rw [← Fintype.card_subtype, ← Fintype.card_subtype]
      symm
      apply Fintype.card_congr ((f.halfEdgesAtEquiv v).subtypeEquiv ?_)
      intro x
      change (x.1.1 ∈ D.edges ∧ select x.1.2 (D.tail x.1.1)) ↔
        (f.edgeEquiv x.1.1 ∈ f.mapEdges D.edges ∧
          select (f.endEquiv x.1.1 x.1.2) (f.mapTail D.tail (f.edgeEquiv x.1.1)))
      simp only [mem_mapEdges, mapTail, Equiv.symm_apply_apply, hs]
    rw [hcount (· = ·) (fun e i j ↦ (f.endEquiv e).injective.eq_iff),
      hcount (· ≠ ·) (fun e i j ↦ (f.endEquiv e).injective.ne_iff)]
    exact D.balanced v

/-- Transport an oriented cover, including its opposite-direction condition. -/
def orientedCycleDoubleCover {k : ℕ} (D : G₁.OrientedCycleDoubleCover k) :
    G₂.OrientedCycleDoubleCover k where
  cycles i := f.directedCycle (D.cycles i)
  coveredTwice e := by
    obtain ⟨e, rfl⟩ := f.edgeEquiv.surjective e
    simpa [directedCycle] using D.coveredTwice e
  opposite e i j hij hi hj := by
    obtain ⟨e, rfl⟩ := f.edgeEquiv.surjective e
    change f.mapTail (D.cycles i).tail (f.edgeEquiv e) ≠
      f.mapTail (D.cycles j).tail (f.edgeEquiv e)
    simp only [mapTail, Equiv.symm_apply_apply]
    apply (f.endEquiv e).injective.ne
    exact D.opposite e i j hij ((f.mem_mapEdges _ _).mp hi) ((f.mem_mapEdges _ _).mp hj)

theorem orientedCycleDoubleCover_contains {k : ℕ} {D : G₁.OrientedCycleDoubleCover k}
    {F : Finset E₁} (h : D.Contains F) :
    (f.orientedCycleDoubleCover D).Contains (f.mapEdges F) := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i, congrArg f.mapEdges hi⟩

include f in
theorem hasOrientedCycleDoubleCover {k : ℕ} (h : G₁.HasOrientedCycleDoubleCover k) :
    G₂.HasOrientedCycleDoubleCover k := h.map f.orientedCycleDoubleCover

end EndpointIso
end LoopMultigraph
end GraphPuzzles
