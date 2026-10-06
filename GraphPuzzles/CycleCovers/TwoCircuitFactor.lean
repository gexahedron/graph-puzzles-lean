import GraphPuzzles.Circuits.ParityColoring

/-!
# Strong five-cycle double covers of cubic permutation graphs

A cubic permutation graph has a 2-factor consisting of two induced circuits.  Every circuit `C`
of such a graph is an entire member of a five-cycle double cover: either `C` meets both factor
circuits, in which case traversing each factor circuit from a vertex of `C` and colouring by
position parity gives a proper colouring of the graph obtained by deleting the vertices of `C`;
or `C` is one of the factor circuits and the other one is coloured with the tail colouring.
-/

namespace GraphPuzzles
namespace LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- A spanning factor with exactly two vertex-disjoint circuits. Matching chords within either
circuit are allowed. The stronger permutation hypothesis is `TwoCircuitFactor.IsInduced`. -/
structure TwoCircuitFactor (H : LoopMultigraph V E) where
  A : H.TraversedCircuit
  B : H.TraversedCircuit
  disjoint : ∀ v, v ∈ A.vertices → v ∉ B.vertices
  cover : ∀ v, v ∈ A.vertices ∨ v ∈ B.vertices

namespace TwoCircuitFactor

variable {H : LoopMultigraph V E} (F : H.TwoCircuitFactor)

/-- Both factor circuits are induced: the extra hypothesis defining a permutation factor. -/
structure IsInduced : Prop where
  inducedA : ∀ e, (∀ i, H.endAt e i ∈ F.A.vertices) → e ∈ F.A.edges
  inducedB : ∀ e, (∀ i, H.endAt e i ∈ F.B.vertices) → e ∈ F.B.edges

/-- Exchange the two circuits. -/
def swap : H.TwoCircuitFactor where
  A := F.B
  B := F.A
  disjoint := fun v hB hA ↦ F.disjoint v hA hB
  cover := fun v ↦ (F.cover v).symm

omit [DecidableEq E] in
/-- Exchanging the rims preserves the permutation hypothesis. -/
theorem IsInduced.swap (hF : F.IsInduced) : F.swap.IsInduced :=
  ⟨hF.inducedB, hF.inducedA⟩

omit [DecidableEq E] in
theorem endAt_mem_A {e : E} (he : e ∈ F.A.edges) (i : Fin 2) : H.endAt e i ∈ F.A.vertices :=
  H.mem_edgeSupport_iff.mpr ⟨e, he, i, rfl⟩

omit [DecidableEq E] in
theorem endAt_mem_B {e : E} (he : e ∈ F.B.edges) (i : Fin 2) : H.endAt e i ∈ F.B.vertices :=
  H.mem_edgeSupport_iff.mpr ⟨e, he, i, rfl⟩

omit [DecidableEq E] in
/-- An edge with an end in `A` is not an edge of `B`. -/
theorem not_mem_B_of_endAt_mem_A {e : E} {i : Fin 2} (hi : H.endAt e i ∈ F.A.vertices) :
    e ∉ F.B.edges :=
  fun hB ↦ F.disjoint _ hi (F.endAt_mem_B hB i)

omit [DecidableEq E] in
/-- An edge with an end in `B` is not an edge of `A`. -/
theorem not_mem_A_of_endAt_mem_B {e : E} {i : Fin 2} (hi : H.endAt e i ∈ F.B.vertices) :
    e ∉ F.A.edges :=
  fun hA ↦ F.disjoint _ (F.endAt_mem_A hA i) hi

omit [DecidableEq E] in
theorem not_mem_A_of_mem_B {e : E} (he : e ∈ F.B.edges) : e ∉ F.A.edges :=
  F.not_mem_A_of_endAt_mem_B (F.endAt_mem_B he 0)

section Meets

variable (hCubic : ∀ v : V, H.degree v = 3)

include hCubic in
/-- When a circuit meets both factor circuits, traversing each factor circuit from a vertex of
the circuit and colouring by position parity properly colours the graph obtained by deleting the
circuit's vertices. -/
theorem exists_fiveCycleDoubleCover_of_meets (C : H.OrdinaryCircuit)
    {u w : V} (huC : u ∈ H.edgeSupport C.edges) (huA : u ∈ F.A.vertices)
    (hwC : w ∈ H.edgeSupport C.edges) (hwB : w ∈ F.B.vertices) :
    ∃ D : H.CycleDoubleCover 5, D.Contains C.edges := by
  let A' := F.A.rotateTo huA
  let B' := F.B.rotateTo hwB
  let g : E → Color := fun e ↦
    if e ∈ F.A.edges then A'.parityColoring e
    else if e ∈ F.B.edges then B'.parityColoring e else (1, 1)
  have hgA : ∀ p : A'.tour.Pos, g (A'.tour.edge p).1 = parityColor p := by
    intro p
    have hmem : (A'.tour.edge p).1 ∈ F.A.edges := (A'.tour.edge p).2
    simp only [g, if_pos hmem]
    exact A'.parityColoring_edge p
  have hgB : ∀ p : B'.tour.Pos, g (B'.tour.edge p).1 = parityColor p := by
    intro p
    have hmemB : (B'.tour.edge p).1 ∈ F.B.edges := (B'.tour.edge p).2
    have hnotA : (B'.tour.edge p).1 ∉ F.A.edges := F.not_mem_A_of_mem_B hmemB
    simp only [g, if_neg hnotA, if_pos hmemB]
    exact B'.parityColoring_edge p
  have hnz : ∀ e, g e ≠ 0 := by
    intro e
    simp only [g]
    split_ifs
    · exact A'.parityColoring_ne_zero e
    · exact B'.parityColoring_ne_zero e
    · decide
  apply C.toTraversedCircuit.exists_fiveCycleDoubleCover_of_deletedColoring hCubic
  refine ⟨g, fun e _ ↦ hnz e, ?_⟩
  intro v hv h₁ h₂ _ _ heq
  rcases F.cover v with hvA | hvB
  · obtain ⟨p, hp⟩ : ∃ p, A'.tour.vertexAt p = v :=
      ⟨A'.positionVertexEquiv.symm ⟨v, hvA⟩,
        congrArg Subtype.val (A'.positionVertexEquiv.apply_symm_apply ⟨v, hvA⟩)⟩
    subst hp
    have hp0 : p ≠ 0 := by
      rintro rfl
      have hv' : (F.A.rotateTo huA).tour.vertexAt 0 ∉ H.edgeSupport C.edges := hv
      rw [F.A.rotateTo_vertexAt_zero huA] at hv'
      exact hv' huC
    apply A'.parity_injective_at hCubic g hgA p hp0 _ h₁ h₂ heq
    have hbA : (A'.boundaryHalfEdge hCubic p).1 ∉ F.A.edges :=
      A'.boundaryHalfEdge_not_mem hCubic p
    have hbB : (A'.boundaryHalfEdge hCubic p).1 ∉ F.B.edges := by
      apply F.not_mem_B_of_endAt_mem_A (i := (A'.boundaryHalfEdge hCubic p).2)
      rw [A'.boundaryHalfEdge_endpoint]
      exact A'.vertexAt_mem_vertices p
    simp only [g, if_neg hbA, if_neg hbB]
  · obtain ⟨p, hp⟩ : ∃ p, B'.tour.vertexAt p = v :=
      ⟨B'.positionVertexEquiv.symm ⟨v, hvB⟩,
        congrArg Subtype.val (B'.positionVertexEquiv.apply_symm_apply ⟨v, hvB⟩)⟩
    subst hp
    have hp0 : p ≠ 0 := by
      rintro rfl
      have hv' : (F.B.rotateTo hwB).tour.vertexAt 0 ∉ H.edgeSupport C.edges := hv
      rw [F.B.rotateTo_vertexAt_zero hwB] at hv'
      exact hv' hwC
    apply B'.parity_injective_at hCubic g hgB p hp0 _ h₁ h₂ heq
    have hbB : (B'.boundaryHalfEdge hCubic p).1 ∉ F.B.edges :=
      B'.boundaryHalfEdge_not_mem hCubic p
    have hbA : (B'.boundaryHalfEdge hCubic p).1 ∉ F.A.edges := by
      apply F.not_mem_A_of_endAt_mem_B (i := (B'.boundaryHalfEdge hCubic p).2)
      rw [B'.boundaryHalfEdge_endpoint]
      exact B'.vertexAt_mem_vertices p
    simp only [g, if_neg hbA, if_neg hbB]

include hCubic in
/-- When a circuit avoids the first factor circuit, it is the second one, and the tail colouring
of the first factor circuit properly colours the graph obtained by deleting its vertices. -/
theorem exists_fiveCycleDoubleCover_of_avoids (hF : F.IsInduced)
    (hloopless : ∀ e, H.endAt e 0 ≠ H.endAt e 1)
    (C : H.OrdinaryCircuit) (hA : ∀ v, v ∈ H.edgeSupport C.edges → v ∉ F.A.vertices) :
    ∃ D : H.CycleDoubleCover 5, D.Contains C.edges := by
  have hsub : C.edges ⊆ F.B.edges := by
    intro e he
    apply hF.inducedB
    intro i
    have hi : H.endAt e i ∈ H.edgeSupport C.edges := H.mem_edgeSupport_iff.mpr ⟨e, he, i, rfl⟩
    rcases F.cover (H.endAt e i) with h | h
    · exact absurd h (hA _ hi)
    · exact h
  have heq : C.edges = F.B.edges :=
    OrdinaryCircuit.edges_eq_of_subset C F.B.toOrdinaryCircuit hsub
  have hsupp : H.edgeSupport C.edges = F.B.vertices := by
    rw [heq]
  let g := F.A.tailColoring
  apply C.toTraversedCircuit.exists_fiveCycleDoubleCover_of_deletedColoring hCubic
  refine ⟨g, fun e _ ↦ F.A.tailColoring_ne_zero e, ?_⟩
  intro v hv h₁ h₂ hi₁ hi₂ hgeq
  have hvB : v ∉ F.B.vertices := by
    rw [← hsupp]
    exact hv
  have hvA : v ∈ F.A.vertices := (F.cover v).resolve_right hvB
  obtain ⟨p, hp⟩ : ∃ p, F.A.tour.vertexAt p = v :=
    ⟨F.A.positionVertexEquiv.symm ⟨v, hvA⟩,
      congrArg Subtype.val (F.A.positionVertexEquiv.apply_symm_apply ⟨v, hvA⟩)⟩
  subst hp
  have hmA : ∀ h : H.halfEdgesAt (F.A.tour.vertexAt p),
      C.toTraversedCircuit.IsInternal h.1.1 → h.1.1 ∈ F.A.edges := by
    intro h hint
    apply hF.inducedA
    intro i
    have hnot : H.endAt h.1.1 i ∉ F.B.vertices := by
      rw [← hsupp]
      exact hint i
    exact (F.cover _).resolve_right hnot
  exact F.A.tail_injective_at hCubic (F.A.one_le_n_of_loopless hloopless) g
    F.A.tailColoring_edge p h₁ h₂ (hmA h₁ hi₁) (hmA h₂ hi₂) hgeq

include F hCubic in
/-- **Cubic permutation graphs satisfy the strong five-cycle double cover property**, with the
prescribed circuit as an entire member. -/
theorem exists_fiveCycleDoubleCover (hF : F.IsInduced)
    (hloopless : ∀ e, H.endAt e 0 ≠ H.endAt e 1)
    (C : H.OrdinaryCircuit) : ∃ D : H.CycleDoubleCover 5, D.Contains C.edges := by
  by_cases hA : ∃ u, u ∈ H.edgeSupport C.edges ∧ u ∈ F.A.vertices
  · by_cases hB : ∃ w, w ∈ H.edgeSupport C.edges ∧ w ∈ F.B.vertices
    · obtain ⟨u, huC, huA⟩ := hA
      obtain ⟨w, hwC, hwB⟩ := hB
      exact F.exists_fiveCycleDoubleCover_of_meets hCubic C huC huA hwC hwB
    · push Not at hB
      exact F.swap.exists_fiveCycleDoubleCover_of_avoids hCubic hF.swap hloopless C hB
  · push Not at hA
    exact F.exists_fiveCycleDoubleCover_of_avoids hCubic hF hloopless C hA

end Meets

end TwoCircuitFactor

end LoopMultigraph
end GraphPuzzles
