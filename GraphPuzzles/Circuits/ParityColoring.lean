import GraphPuzzles.CycleCovers.CircuitExtensionCorollaries

/-!
# Rotated traversals and parity colourings of circuits

A circuit traversed from a chosen vertex can be two-coloured by the parity of the position of
each edge; the colouring is proper at every vertex of the circuit except possibly the starting
vertex.  Giving the last edge a third colour makes it proper everywhere.  These colourings are
the elementary input for the permutation-graph application of the exact extension theorem.
-/

namespace GraphPuzzles
namespace LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

private theorem fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  revert i
  decide

namespace EulerTour

variable {G : LoopMultigraph V E} (T : G.EulerTour)

/-- Rotate a tour so that position `k` becomes the first position. -/
def rotate (k : Fin (T.n + 1)) : G.EulerTour where
  n := T.n
  edge := (Equiv.addRight k).trans T.edge
  depart i := T.depart (i + k)
  continuous i := by
    have h := T.continuous (i + k)
    have hrot : finRotate (T.n + 1) (i + k) = finRotate (T.n + 1) i + k := by
      rw [finRotate_apply, finRotate_apply, add_right_comm]
    rw [hrot] at h
    exact h

omit [DecidableEq V] [DecidableEq E] in
@[simp]
theorem rotate_n (k : Fin (T.n + 1)) : (T.rotate k).n = T.n := rfl

omit [DecidableEq V] [DecidableEq E] in
@[simp]
theorem rotate_edge (k i : Fin (T.n + 1)) : (T.rotate k).edge i = T.edge (i + k) := rfl

omit [DecidableEq V] [DecidableEq E] in
@[simp]
theorem rotate_depart (k i : Fin (T.n + 1)) : (T.rotate k).depart i = T.depart (i + k) := rfl

omit [DecidableEq V] [DecidableEq E] in
theorem rotate_vertexAt (k i : Fin (T.n + 1)) :
    (T.rotate k).vertexAt i = T.vertexAt (i + k) := rfl

omit [DecidableEq V] [DecidableEq E] in
/-- The previous position is the predecessor. -/
theorem prev_eq_sub_one (i : T.Pos) : T.prev i = i - 1 :=
  finRotate_symm_apply i

end EulerTour

section Colors

/-- The parity colour of a position: `(1, 0)` at even positions and `(0, 1)` at odd ones. -/
def parityColor {n : ℕ} (p : Fin (n + 1)) : Color :=
  if p.val % 2 = 0 then (1, 0) else (0, 1)

/-- The tail colour: the third colour at the last position, and the parity colour elsewhere. -/
def tailColor {n : ℕ} (p : Fin (n + 1)) : Color :=
  if p = Fin.last n then (1, 1) else parityColor p

theorem parityColor_ne_zero {n : ℕ} (p : Fin (n + 1)) : parityColor p ≠ 0 := by
  unfold parityColor
  split_ifs <;> decide

theorem parityColor_ne_third {n : ℕ} (p : Fin (n + 1)) : parityColor p ≠ (1, 1) := by
  unfold parityColor
  split_ifs <;> decide

theorem tailColor_ne_zero {n : ℕ} (p : Fin (n + 1)) : tailColor p ≠ 0 := by
  unfold tailColor
  split_ifs
  · decide
  · exact parityColor_ne_zero p

theorem parityColor_sub_one {n : ℕ} (p : Fin (n + 1)) (hp : p ≠ 0) :
    parityColor (p - 1) ≠ parityColor p := by
  have hval : (p - 1).val = p.val - 1 := by
    rw [Fin.coe_sub_one, if_neg hp]
  have hpos : 0 < p.val := Fin.pos_iff_ne_zero.mpr hp
  unfold parityColor
  rw [hval]
  by_cases h : p.val % 2 = 0
  · have h' : ¬ (p.val - 1) % 2 = 0 := by omega
    simp only [h, h', if_true, if_false]
    decide
  · have h' : (p.val - 1) % 2 = 0 := by omega
    simp only [h, h', if_true, if_false]
    decide

private theorem zero_sub_one_eq_last (n : ℕ) : (0 : Fin (n + 1)) - 1 = Fin.last n := by
  apply Fin.ext
  rw [Fin.coe_sub_one, if_pos rfl, Fin.val_last]

private theorem last_ne_zero_of_le {n : ℕ} (hn : 1 ≤ n) : (Fin.last n : Fin (n + 1)) ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  rw [Fin.val_last, Fin.val_zero] at this
  omega

theorem tailColor_sub_one {n : ℕ} (hn : 1 ≤ n) (p : Fin (n + 1)) :
    tailColor (p - 1) ≠ tailColor p := by
  by_cases hp : p = 0
  · subst hp
    unfold tailColor
    rw [zero_sub_one_eq_last, if_pos rfl, if_neg (last_ne_zero_of_le hn).symm]
    exact (parityColor_ne_third 0).symm
  · have hne : p - 1 ≠ Fin.last n := by
      intro h
      apply hp
      have := congrArg Fin.val h
      rw [Fin.coe_sub_one, if_neg hp, Fin.val_last] at this
      apply Fin.ext
      rw [Fin.val_zero]
      have hlt := p.2
      omega
    unfold tailColor
    rw [if_neg hne]
    by_cases hl : p = Fin.last n
    · rw [if_pos hl]
      exact parityColor_ne_third _
    · rw [if_neg hl]
      exact parityColor_sub_one p hp

end Colors

namespace TraversedCircuit

variable {H : LoopMultigraph V E} (C : H.TraversedCircuit)

/-- Rotate the traversal so that position `k` becomes the first position. -/
def rotate (k : C.tour.Pos) : H.TraversedCircuit :=
  { C with tour := C.tour.rotate k }

omit [DecidableEq E] in
@[simp]
theorem rotate_edges (k : C.tour.Pos) : (C.rotate k).edges = C.edges := rfl

omit [DecidableEq E] in
@[simp]
theorem rotate_vertices (k : C.tour.Pos) : (C.rotate k).vertices = C.vertices := rfl

omit [DecidableEq E] in
theorem rotate_vertexAt_zero (k : C.tour.Pos) :
    (C.rotate k).tour.vertexAt 0 = C.tour.vertexAt k := by
  change C.tour.vertexAt (0 + k) = _
  rw [zero_add]

/-- Rotate the traversal so that a given circuit vertex sits at position zero. -/
noncomputable def rotateTo {v : V} (hv : v ∈ C.vertices) : H.TraversedCircuit :=
  C.rotate (C.positionVertexEquiv.symm ⟨v, hv⟩)

omit [DecidableEq E] in
@[simp]
theorem rotateTo_edges {v : V} (hv : v ∈ C.vertices) : (C.rotateTo hv).edges = C.edges := rfl

omit [DecidableEq E] in
@[simp]
theorem rotateTo_vertices {v : V} (hv : v ∈ C.vertices) :
    (C.rotateTo hv).vertices = C.vertices := rfl

omit [DecidableEq E] in
@[simp]
theorem rotateTo_n {v : V} (hv : v ∈ C.vertices) : (C.rotateTo hv).tour.n = C.tour.n := rfl

omit [DecidableEq E] in
theorem rotateTo_vertexAt_zero {v : V} (hv : v ∈ C.vertices) :
    (C.rotateTo hv).tour.vertexAt 0 = v := by
  unfold rotateTo
  rw [C.rotate_vertexAt_zero]
  exact congrArg Subtype.val (C.positionVertexEquiv.apply_symm_apply ⟨v, hv⟩)

omit [DecidableEq E] in
/-- A traversed circuit with a single edge is a loop. -/
theorem one_le_n_of_loopless (hloopless : ∀ e, H.endAt e 0 ≠ H.endAt e 1) :
    1 ≤ C.tour.n := by
  by_contra hn
  have hzero : C.tour.n = 0 := by omega
  haveI : Subsingleton (Fin (C.tour.n + 1)) :=
    ⟨fun a b ↦ Fin.ext (by have ha := a.2; have hb := b.2; omega)⟩
  have hcont := C.tour.continuous 0
  have hrot : finRotate (C.tour.n + 1) 0 = 0 := Subsingleton.elim _ _
  rw [hrot] at hcont
  change H.endAt (C.tour.edge 0).1 (Fin.rev (C.tour.depart 0)) =
    H.endAt (C.tour.edge 0).1 (C.tour.depart 0) at hcont
  rcases fin2_cases (C.tour.depart 0) with hd | hd
  · rw [hd] at hcont
    exact hloopless _ (by simpa using hcont.symm)
  · rw [hd] at hcont
    exact hloopless _ (by simpa using hcont)

/-- Colour circuit edges by the parity of their position, and all other edges by the third
colour. -/
noncomputable def parityColoring (e : E) : Color :=
  if he : e ∈ C.edges then parityColor (C.tour.edge.symm ⟨e, he⟩) else (1, 1)

theorem parityColoring_edge (p : C.tour.Pos) :
    C.parityColoring (C.tour.edge p).1 = parityColor p := by
  simp [parityColoring, (C.tour.edge p).2]

theorem parityColoring_of_not_mem {e : E} (he : e ∉ C.edges) :
    C.parityColoring e = (1, 1) := by
  simp [parityColoring, he]

theorem parityColoring_ne_zero (e : E) : C.parityColoring e ≠ 0 := by
  unfold parityColoring
  split_ifs
  · exact parityColor_ne_zero _
  · decide

/-- Colour circuit edges by the tail colouring, and all other edges by the third colour. -/
noncomputable def tailColoring (e : E) : Color :=
  if he : e ∈ C.edges then tailColor (C.tour.edge.symm ⟨e, he⟩) else (1, 1)

theorem tailColoring_edge (p : C.tour.Pos) :
    C.tailColoring (C.tour.edge p).1 = tailColor p := by
  simp [tailColoring, (C.tour.edge p).2]

theorem tailColoring_ne_zero (e : E) : C.tailColoring e ≠ 0 := by
  unfold tailColoring
  split_ifs
  · exact tailColor_ne_zero _
  · decide

section Injective

variable (hCubic : ∀ v : V, H.degree v = 3)

/-- A colouring taking pairwise distinct values on the three half-edges at a circuit vertex is
injective there. -/
theorem injective_at_of_positions (p : C.tour.Pos) (g : E → Color)
    (h01 : g (C.tour.edge p).1 ≠ g (C.tour.edge (C.tour.prev p)).1)
    (h02 : g (C.tour.edge p).1 ≠ g (C.boundaryHalfEdge hCubic p).1)
    (h12 : g (C.tour.edge (C.tour.prev p)).1 ≠ g (C.boundaryHalfEdge hCubic p).1)
    (h₁ h₂ : H.halfEdgesAt (C.tour.vertexAt p)) (heq : g h₁.1.1 = g h₂.1.1) : h₁ = h₂ := by
  obtain ⟨j₁, hj₁⟩ := C.positionHalfEdge_surjective hCubic p h₁
  obtain ⟨j₂, hj₂⟩ := C.positionHalfEdge_surjective hCubic p h₂
  rw [← hj₁, ← hj₂] at heq
  apply Subtype.ext
  rw [← hj₁, ← hj₂]
  fin_cases j₁ <;> fin_cases j₂
  · rfl
  · exact absurd heq h01
  · exact absurd heq h02
  · exact absurd heq.symm h01
  · rfl
  · exact absurd heq h12
  · exact absurd heq.symm h02
  · exact absurd heq.symm h12
  · rfl

include hCubic in
/-- The same conclusion restricted to half-edges of circuit edges, needing only the circuit
values to differ. -/
theorem injective_at_of_positions_circuit (p : C.tour.Pos) (g : E → Color)
    (h01 : g (C.tour.edge p).1 ≠ g (C.tour.edge (C.tour.prev p)).1)
    (h₁ h₂ : H.halfEdgesAt (C.tour.vertexAt p)) (hm₁ : h₁.1.1 ∈ C.edges)
    (hm₂ : h₂.1.1 ∈ C.edges) (heq : g h₁.1.1 = g h₂.1.1) : h₁ = h₂ := by
  obtain ⟨j₁, hj₁⟩ := C.positionHalfEdge_surjective hCubic p h₁
  obtain ⟨j₂, hj₂⟩ := C.positionHalfEdge_surjective hCubic p h₂
  rw [← hj₁, ← hj₂] at heq
  rw [← hj₁] at hm₁
  rw [← hj₂] at hm₂
  apply Subtype.ext
  rw [← hj₁, ← hj₂]
  have hbd := C.boundaryHalfEdge_not_mem hCubic p
  fin_cases j₁ <;> fin_cases j₂
  · rfl
  · exact absurd heq h01
  · exact absurd hm₂ hbd
  · exact absurd heq.symm h01
  · rfl
  · exact absurd hm₂ hbd
  · exact absurd hm₁ hbd
  · exact absurd hm₁ hbd
  · rfl

/-- The parity colouring, extended by the third colour on the exterior edge, is injective at
every circuit vertex other than the starting vertex. -/
theorem parity_injective_at (g : E → Color)
    (hg : ∀ p : C.tour.Pos, g (C.tour.edge p).1 = parityColor p)
    (p : C.tour.Pos) (hp : p ≠ 0) (hbd : g (C.boundaryHalfEdge hCubic p).1 = (1, 1))
    (h₁ h₂ : H.halfEdgesAt (C.tour.vertexAt p)) (heq : g h₁.1.1 = g h₂.1.1) : h₁ = h₂ := by
  apply C.injective_at_of_positions hCubic p g _ _ _ h₁ h₂ heq
  · rw [hg, hg, C.tour.prev_eq_sub_one]
    exact (parityColor_sub_one p hp).symm
  · rw [hg, hbd]
    exact parityColor_ne_third p
  · rw [hg, hbd]
    exact parityColor_ne_third _

include hCubic in
/-- The tail colouring is injective on circuit half-edges at every circuit vertex. -/
theorem tail_injective_at (hn : 1 ≤ C.tour.n) (g : E → Color)
    (hg : ∀ p : C.tour.Pos, g (C.tour.edge p).1 = tailColor p)
    (p : C.tour.Pos) (h₁ h₂ : H.halfEdgesAt (C.tour.vertexAt p)) (hm₁ : h₁.1.1 ∈ C.edges)
    (hm₂ : h₂.1.1 ∈ C.edges) (heq : g h₁.1.1 = g h₂.1.1) : h₁ = h₂ := by
  apply C.injective_at_of_positions_circuit hCubic p g _ h₁ h₂ hm₁ hm₂ heq
  rw [hg, hg, C.tour.prev_eq_sub_one]
  exact (tailColor_sub_one hn p).symm

end Injective

end TraversedCircuit

namespace OrdinaryCircuit

variable {H : LoopMultigraph V E}

omit [DecidableEq V] [DecidableEq E] in
private theorem edgeAdjacent_symm {e f : E} (h : H.EdgeAdjacent e f) : H.EdgeAdjacent f e := by
  obtain ⟨i, j, hij⟩ := h
  exact ⟨j, i, hij.symm⟩

/-- An edge of a circuit `D` adjacent to an edge of a circuit `C ⊆ D` lies in `C`: otherwise the
common vertex would have degree three in `D`. -/
private theorem mem_of_adjacent (C D : H.OrdinaryCircuit) (hCD : C.edges ⊆ D.edges)
    {e f : E} (he : e ∈ C.edges) (hf : f ∈ D.edges) (hadj : H.EdgeAdjacent e f) :
    f ∈ C.edges := by
  by_contra hfC
  obtain ⟨i, j, hij⟩ := hadj
  let v := H.endAt e i
  have hvC : v ∈ H.edgeSupport C.edges := H.mem_edgeSupport_iff.mpr ⟨e, he, i, rfl⟩
  have hvD : v ∈ H.edgeSupport D.edges :=
    H.mem_edgeSupport_iff.mpr ⟨e, hCD he, i, rfl⟩
  have hdC := C.twoRegular v hvC
  have hdD := D.twoRegular v hvD
  unfold degreeIn at hdC hdD
  have hsub : ((C.edges ×ˢ (Finset.univ : Finset (Fin 2))).filter fun h ↦ H.endAt h.1 h.2 = v) ⊂
      ((D.edges ×ˢ (Finset.univ : Finset (Fin 2))).filter fun h ↦ H.endAt h.1 h.2 = v) := by
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨(f, j), ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hf, Finset.mem_univ _⟩, hij.symm⟩
      · intro hmem
        exact hfC (Finset.mem_product.mp (Finset.mem_filter.mp hmem).1).1
    · intro x hx
      have hx' := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hCD (Finset.mem_product.mp hx'.1).1, Finset.mem_univ _⟩, hx'.2⟩
  have hlt := Finset.card_lt_card hsub
  omega

/-- A circuit contained in a circuit is the whole circuit. -/
theorem edges_eq_of_subset (C D : H.OrdinaryCircuit) (hCD : C.edges ⊆ D.edges) :
    C.edges = D.edges := by
  obtain ⟨root, hroot, hreach⟩ := D.connected
  obtain ⟨e₀, he₀⟩ := C.nonempty
  let R : E → E → Prop := fun x y ↦ x ∈ D.edges ∧ y ∈ D.edges ∧ H.EdgeAdjacent x y
  have hRsymm : ∀ x y, R x y → R y x := fun x y hxy ↦ ⟨hxy.2.1, hxy.1, edgeAdjacent_symm hxy.2.2⟩
  have hstep : ∀ {x y : E}, x ∈ C.edges → R x y → y ∈ C.edges := fun hx hxy ↦
    mem_of_adjacent C D hCD hx hxy.2.1 hxy.2.2
  have hclosed : ∀ {x y : E}, Relation.ReflTransGen R x y → x ∈ C.edges → y ∈ C.edges := by
    intro x y hxy hx
    induction hxy with
    | refl => exact hx
    | tail _ hbc ih => exact hstep ih hbc
  have hroot_C : root ∈ C.edges := by
    have h := hreach e₀ (hCD he₀)
    have hrev : Relation.ReflTransGen R e₀ root :=
      Relation.ReflTransGen.mono (r := Function.swap R) (p := R)
        (fun x y hxy ↦ hRsymm y x hxy) h.swap
    exact hclosed hrev he₀
  apply Finset.Subset.antisymm hCD
  intro f hf
  exact hclosed (hreach f hf) hroot_C

end OrdinaryCircuit

end LoopMultigraph
end GraphPuzzles
