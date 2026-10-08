import GraphPuzzles.Petersen.Minors.TightMinorFibers

/-! A tight quotient with only singleton fibers is an isomorphism. -/

namespace GraphPuzzles.LoopMultigraph

universe u v

variable {V W : Type u} {E F : Type v}
  [Fintype V] [Fintype W] [Fintype E] [Fintype F]
  [DecidableEq V] [DecidableEq W] [DecidableEq E] [DecidableEq F]
variable {H : LoopMultigraph V E} {K : LoopMultigraph W F}

namespace TightVertexQuotient

variable (Q : H.TightVertexQuotient K)

private theorem end_cases (σ : Fin 2 ≃ Fin 2) :
    (σ 0 = 0 ∧ σ 1 = 1) ∨ (σ 0 = 1 ∧ σ 1 = 0) := by
  have hn : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
  have h0 := (σ 0).isLt
  have h1 := (σ 1).isLt
  omega

omit [DecidableEq F] in
/-- Exact incidence of every retained labelled edge. -/
theorem joins_edgeLift (f : F) :
    K.Joins f (Q.vertexMap (H.endAt (Q.edgeLift f) 0))
      (Q.vertexMap (H.endAt (Q.edgeLift f) 1)) := by
  rw [Q.map_endAt, Q.map_endAt]
  rcases end_cases (Q.endEquiv f) with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;>
    simp only [Joins, h0, h1, true_and, or_true, true_or]

omit [DecidableEq F] in
/-- Every original edge between different fibers induces a terminal
edge with those two endpoint images. -/
theorem exists_join_of_distinct_images {e : E} {a b : V}
    (he : H.Joins e a b) (hne : Q.vertexMap a ≠ Q.vertexMap b) :
    ∃ f, Q.edgeLift f = e ∧ K.Joins f (Q.vertexMap a) (Q.vertexMap b) := by
  have hh : Q.vertexMap (H.endAt e 0) ≠ Q.vertexMap (H.endAt e 1) := by
    rcases he with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · simpa only [h0, h1] using hne
    · simpa only [h0, h1] using hne.symm
  obtain ⟨f, hf⟩ := Q.edge_complete e hh
  refine ⟨f, hf, ?_⟩
  have hj := Q.joins_edgeLift f
  rw [hf] at hj
  rcases he with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · simpa only [h0, h1] using hj
  · simpa only [h0, h1] using (K.joins_comm.mp hj)

/-- Without nonsingleton fibers the quotient retains every vertex and,
for a loopless source graph, every edge. -/
noncomputable def toEndpointIso_of_singleton
    (hloop : ∀ e, H.endAt e 0 ≠ H.endAt e 1)
    (hS : ∀ w, (Q.fiber w).card ≤ 1) : EndpointIso H K := by
  have hi : Function.Injective Q.vertexMap := by
    intro a b hab
    exact Finset.card_le_one.mp (hS (Q.vertexMap b)) a
      ((Q.mem_fiber _ _).mpr hab) b (by simp)
  have he : Function.Surjective Q.edgeLift := by
    intro e
    exact Q.edge_complete e (fun h ↦ hloop e (hi h))
  let ev : V ≃ W := Equiv.ofBijective Q.vertexMap ⟨hi, Q.surjective⟩
  let ee : F ≃ E := Equiv.ofBijective Q.edgeLift ⟨Q.edge_injective, he⟩
  exact {
    vertexEquiv := ev
    edgeEquiv := ee.symm
    endEquiv e := Q.endEquiv (ee.symm e)
    map_endAt e i := by
      have hh := Q.map_endAt (ee.symm e) i
      have hl : Q.edgeLift (ee.symm e) = e := ee.apply_symm_apply e
      simpa only [hl, ev, Equiv.ofBijective_apply] using hh }

omit [DecidableEq F] in
/-- The empty-expansion case of a terminal Petersen model. -/
theorem isPetersenUpToParallel_of_singleton
    (hloop : ∀ e, H.endAt e 0 ≠ H.endAt e 1)
    (hS : ∀ w, (Q.fiber w).card ≤ 1) (hp : K.IsPetersenUpToParallel) :
    H.IsPetersenUpToParallel :=
  (Q.toEndpointIso_of_singleton hloop hS).symm.isPetersenUpToParallel hp

end TightVertexQuotient

end GraphPuzzles.LoopMultigraph
