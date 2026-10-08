import GraphPuzzles.Petersen.Minors.TightMinorFibers

/-! Matching transport outside the nonsingleton fibers of a tight minor. -/

namespace GraphPuzzles.LoopMultigraph

open scoped BigOperators

universe u v

variable {V W : Type u} {E F : Type v} [Fintype V] [Fintype W] [Fintype E] [Fintype F]
  [DecidableEq V] [DecidableEq W] [DecidableEq E] [DecidableEq F]
variable {H : LoopMultigraph V E} {K : LoopMultigraph W F}

namespace TightVertexQuotient

variable (Q : H.TightVertexQuotient K)


omit [DecidableEq F] in
/-- Original degree agrees with target degree at a singleton fiber. -/
theorem degreeIn_lift_of_singleton (M : Finset F) {v : V}
    (hv : (Q.fiber (Q.vertexMap v)).card ≤ 1) :
    H.degreeIn (M.image Q.edgeLift) v = K.degreeIn M (Q.vertexMap v) := by
  have hunique {w : V} (hw : Q.vertexMap w = Q.vertexMap v) : w = v :=
    Finset.card_le_one.mp hv w ((Q.mem_fiber _ _).mpr hw) v (by simp)
  unfold degreeIn
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_product, Finset.sum_product,
    Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro f _
    apply Fintype.sum_equiv (Q.endEquiv f)
    intro i
    have hh : H.endAt (Q.edgeLift f) i = v ↔
        K.endAt f (Q.endEquiv f i) = Q.vertexMap v := by
      rw [← Q.map_endAt]
      exact ⟨congrArg Q.vertexMap, hunique⟩
    simp only [hh]
  · intro f _ g _ h
    exact Q.edge_injective h

omit [DecidableEq F] in
/-- A target matching on singleton fibers lifts to exactly their original
vertices, retaining each selected edge label. -/
theorem lift_matchingOn {S : Finset W} {M : Finset F}
    (hM : K.IsPerfectMatchingOn S M)
    (hS : ∀ w ∈ S, (Q.fiber w).card ≤ 1) :
    H.IsPerfectMatchingOn (Q.preimage S) (M.image Q.edgeLift) := by
  constructor
  · intro e he i
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    rw [Q.mem_preimage, Q.map_endAt]
    exact hM.1 f hf _
  · intro v hv
    have hw := (Q.mem_preimage S v).mp hv
    rw [Q.degreeIn_lift_of_singleton M (hS _ hw)]
    exact hM.2 _ hw

private theorem end_cases (σ : Fin 2 ≃ Fin 2) :
    (σ 0 = 0 ∧ σ 1 = 1) ∨ (σ 0 = 1 ∧ σ 1 = 0) := by
  have hn : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
  have h0 := (σ 0).isLt
  have h1 := (σ 1).isLt
  omega

omit [DecidableEq F] in
/-- A retained edge crosses the original selected cut exactly when its
terminal edge crosses the terminal selected cut. -/
theorem lift_mem_dangling (Z : Finset W) (f : F) :
    Q.edgeLift f ∈ H.dangling (Q.preimage Z) ↔ f ∈ K.dangling Z := by
  simp only [mem_dangling, mem_preimage, Q.map_endAt]
  rcases end_cases (Q.endEquiv f) with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rw [h0, h1]
  · rw [h0, h1]
    tauto

/-- Lifting preserves crossing counts, even for partial matchings. -/
theorem crossing_lift (Z : Finset W) (M : Finset F) :
    (M.image Q.edgeLift ∩ H.dangling (Q.preimage Z)).card =
      (M ∩ K.dangling Z).card := by
  have he : M.image Q.edgeLift ∩ H.dangling (Q.preimage Z) =
      (M ∩ K.dangling Z).image Q.edgeLift := by
    ext e
    constructor
    · intro he
      obtain ⟨hm, hd⟩ := Finset.mem_inter.mp he
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hm
      exact Finset.mem_image.mpr ⟨f,
        Finset.mem_inter.mpr ⟨hf, (Q.lift_mem_dangling Z f).mp hd⟩, rfl⟩
    · intro he
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
      exact Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨f, (Finset.mem_inter.mp hf).1, rfl⟩,
        (Q.lift_mem_dangling Z f).mpr (Finset.mem_inter.mp hf).2⟩
  rw [he, Finset.card_image_of_injective _ Q.edge_injective]

end TightVertexQuotient

end GraphPuzzles.LoopMultigraph
