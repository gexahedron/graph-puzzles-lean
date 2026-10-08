import GraphPuzzles.Reduction.Parallel.ParallelReduction

/-! An incidence embedding of a simple graph with the same edge count is an isomorphism. -/

namespace GraphPuzzles.LoopMultigraph

variable {V W E F : Type*} [Fintype V] [Fintype W] [Fintype E] [Fintype F]
  [DecidableEq V] [DecidableEq W] [DecidableEq E] [DecidableEq F]
variable {H : LoopMultigraph V E} {K : LoopMultigraph W F}

omit [DecidableEq V] [DecidableEq E] [DecidableEq F] in
/-- Choose the labelled edges of a spanning simple graph. Equal edge
counts then force these labels to exhaust the ambient graph. -/
theorem exists_endpointIso_of_spanning_simple
    (hK : K.IsSimple) (ev : W ≃ V) (hcard : Fintype.card F = Fintype.card E)
    (hedge : ∀ f, ∃ e, H.Joins e (ev (K.endAt f 0)) (ev (K.endAt f 1))) :
    ∃ f : EndpointIso K H, f.vertexEquiv = ev := by
  classical
  choose em hem using hedge
  have hiff (f : F) (a b : W) : K.Joins f a b ↔ H.Joins (em f) (ev a) (ev b) := by
    rcases hem f with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · simp only [Joins, h0, h1, Equiv.apply_eq_iff_eq]
    · simp only [Joins, h0, h1, Equiv.apply_eq_iff_eq]
      tauto
  have hinj : Function.Injective em := by
    intro f g hfg
    apply hK.no_parallel f g
    apply (hiff g _ _).mpr
    rw [← hfg]
    exact hem f
  have hsurj := ((Fintype.bijective_iff_injective_and_card em).mpr ⟨hinj, hcard⟩).2
  let red : ParallelReduction K H := {
    vertexEquiv := ev
    edgeMap := em
    edge_surjective := hsurj
    joins_iff := hiff }
  exact ⟨red.toEndpointIso_of_injective hinj, rfl⟩

end GraphPuzzles.LoopMultigraph
