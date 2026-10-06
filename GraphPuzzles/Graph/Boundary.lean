import GraphPuzzles.CycleCovers.TJoin

/-! Binary boundary algebra for finite endpoint multigraphs. -/

namespace GraphPuzzles
namespace LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LoopMultigraph V E)

section Boundary

theorem boundary_union (P Q : Finset E) (h : Disjoint P Q) (w : V) :
    G.boundary (P ∪ Q) w = G.boundary P w + G.boundary Q w := by
  unfold boundary
  rw [Finset.sum_union h]

theorem boundary_sdiff {P D : Finset E} (h : P ⊆ D) (w : V) :
    G.boundary (D \ P) w = G.boundary D w + G.boundary P w := by
  have := G.boundary_union (D \ P) P Finset.sdiff_disjoint w
  rw [Finset.sdiff_union_of_subset h] at this
  rw [this, add_assoc, F₂_add_self, add_zero]

omit [DecidableEq E] in
theorem boundary_singleton (e : E) (w : V) :
    G.boundary {e} w =
      (if G.endAt e 0 = w then 1 else 0) + (if G.endAt e 1 = w then 1 else 0) := by
  simp [boundary, edgeIncidence]

omit [DecidableEq E] in
/-- An edge set whose ends lie in `S` has zero boundary outside `S`. -/
theorem boundary_eq_zero_of_ends {X : Finset E} {S : Finset V}
    (hX : ∀ e ∈ X, ∀ i, G.endAt e i ∈ S) {w : V} (hw : w ∉ S) : G.boundary X w = 0 := by
  unfold boundary
  apply Finset.sum_eq_zero
  intro e he
  have h0 : G.endAt e 0 ≠ w := fun h ↦ hw (h ▸ hX e he 0)
  have h1 : G.endAt e 1 ≠ w := fun h ↦ hw (h ▸ hX e he 1)
  simp [edgeIncidence, h0, h1]

omit [DecidableEq E] in
theorem boundary_mono_zero {X : Finset E} (hX : G.IsEvenEdgeSet X) (w : V) :
    G.boundary X w = 0 := hX w

theorem boundary_pair {e f : E} (hne : e ≠ f) (w : V) :
    G.boundary {e, f} w =
      ((if G.endAt e 0 = w then 1 else 0) + (if G.endAt e 1 = w then 1 else 0)) +
        ((if G.endAt f 0 = w then 1 else 0) + (if G.endAt f 1 = w then 1 else 0)) := by
  unfold boundary
  rw [Finset.sum_pair hne]
  rfl

omit [DecidableEq E] in
theorem edgeIncidence_eq (w : V) (e : E) :
    G.edgeIncidence w e =
      (if G.endAt e 0 = w then 1 else 0) + (if G.endAt e 1 = w then 1 else 0) :=
  rfl

end Boundary


end LoopMultigraph
end GraphPuzzles
