import GraphPuzzles.Matching.MatchingIso

/-! Relabelling vertices and identifying parallel edge labels. -/

namespace GraphPuzzles.LoopMultigraph

variable {V₁ E₁ V₂ E₂ V₃ E₃ : Type*}
  [Fintype V₁] [Fintype E₁] [Fintype V₂] [Fintype E₂] [Fintype V₃] [Fintype E₃]
  [DecidableEq V₁] [DecidableEq E₁] [DecidableEq V₂] [DecidableEq E₂]
  [DecidableEq V₃] [DecidableEq E₃]

/-- A vertex relabelling and surjective edge map preserving exactly the
unordered endpoints of every edge. Only parallel labels can be identified. -/
structure ParallelReduction (H : LoopMultigraph V₁ E₁) (K : LoopMultigraph V₂ E₂) where
  vertexEquiv : V₁ ≃ V₂
  edgeMap : E₁ → E₂
  edge_surjective : Function.Surjective edgeMap
  joins_iff : ∀ e a b, H.Joins e a b ↔ K.Joins (edgeMap e) (vertexEquiv a) (vertexEquiv b)

namespace ParallelReduction

variable {H : LoopMultigraph V₁ E₁} {K : LoopMultigraph V₂ E₂}
  {G : LoopMultigraph V₃ E₃}

def refl (H : LoopMultigraph V₁ E₁) : ParallelReduction H H where
  vertexEquiv := Equiv.refl _
  edgeMap := id
  edge_surjective := Function.surjective_id
  joins_iff _ _ _ := Iff.rfl

def trans (f : ParallelReduction H K) (g : ParallelReduction K G) : ParallelReduction H G where
  vertexEquiv := f.vertexEquiv.trans g.vertexEquiv
  edgeMap := g.edgeMap ∘ f.edgeMap
  edge_surjective := g.edge_surjective.comp f.edge_surjective
  joins_iff e a b := (f.joins_iff e a b).trans (g.joins_iff _ _ _)

omit [DecidableEq V₁] [DecidableEq E₁] [DecidableEq V₂] [DecidableEq E₂] in
/-- A simple graph has no parallel labels for such a map to identify. -/
theorem edge_injective (f : ParallelReduction H K) (hs : H.IsSimple) :
    Function.Injective f.edgeMap := by
  intro e g heg
  apply hs.no_parallel e g
  apply (f.joins_iff g _ _).mpr
  rw [← heg]
  exact (f.joins_iff e _ _).mp (Or.inl ⟨rfl, rfl⟩)

/-- An injective parallel reduction is an endpoint isomorphism. -/
noncomputable def toEndpointIso_of_injective (f : ParallelReduction H K)
    (hi : Function.Injective f.edgeMap) :
    EndpointIso H K := by
  classical
  have he (e : E₁) : ∃ σ : Fin 2 ≃ Fin 2, ∀ i,
      f.vertexEquiv (H.endAt e i) = K.endAt (f.edgeMap e) (σ i) := by
    rcases (f.joins_iff e _ _).mp (Or.inl ⟨rfl, rfl⟩) with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · refine ⟨Equiv.refl _, ?_⟩
      intro i
      fin_cases i
      · exact h0.symm
      · exact h1.symm
    · refine ⟨Equiv.swap 0 1, ?_⟩
      intro i
      fin_cases i
      · simpa using h1.symm
      · simpa using h0.symm
  choose σ hσ using he
  exact {
    vertexEquiv := f.vertexEquiv
    edgeEquiv := Equiv.ofBijective f.edgeMap ⟨hi, f.edge_surjective⟩
    endEquiv := σ
    map_endAt := hσ }

/-- A parallel reduction of a simple graph is an endpoint isomorphism. -/
noncomputable def toEndpointIso (f : ParallelReduction H K) (hs : H.IsSimple) :
    EndpointIso H K := f.toEndpointIso_of_injective (f.edge_injective hs)

end ParallelReduction

namespace EndpointIso

variable {H : LoopMultigraph V₁ E₁} {K : LoopMultigraph V₂ E₂}

omit [DecidableEq V₁] [DecidableEq E₁] [DecidableEq V₂] [DecidableEq E₂] in
theorem joins_iff (f : EndpointIso H K) (e : E₁) (a b : V₁) :
    H.Joins e a b ↔ K.Joins (f.edgeEquiv e) (f.vertexEquiv a) (f.vertexEquiv b) := by
  have h0 := f.map_endAt e 0
  have h1 := f.map_endAt e 1
  have hn := (f.endEquiv e).injective.ne (by decide : (0 : Fin 2) ≠ 1)
  have hz := ((f.endEquiv e) 0).isLt
  have ho := ((f.endEquiv e) 1).isLt
  have he : ((f.endEquiv e) 0 = 0 ∧ (f.endEquiv e) 1 = 1) ∨
      ((f.endEquiv e) 0 = 1 ∧ (f.endEquiv e) 1 = 0) := by omega
  rcases he with ⟨he0, he1⟩ | ⟨he0, he1⟩
  · rw [he0] at h0
    rw [he1] at h1
    simp only [Joins, ← h0, ← h1, Equiv.apply_eq_iff_eq]
  · rw [he0] at h0
    rw [he1] at h1
    simp only [Joins, ← h0, ← h1, Equiv.apply_eq_iff_eq]
    tauto

def parallelReduction (f : EndpointIso H K) : ParallelReduction H K where
  vertexEquiv := f.vertexEquiv
  edgeMap := f.edgeEquiv
  edge_surjective := f.edgeEquiv.surjective
  joins_iff := f.joins_iff

end EndpointIso

/-- Being the Petersen graph after identifying parallel edge labels. -/
def IsPetersenUpToParallel (H : LoopMultigraph V₁ E₁) : Prop :=
  Nonempty (ParallelReduction H petersen)

omit [DecidableEq V₁] [DecidableEq E₁] in
theorem IsPetersenUpToParallel.isPetersen {H : LoopMultigraph V₁ E₁}
    (hp : H.IsPetersenUpToParallel) (hs : H.IsSimple) : H.IsPetersen :=
  ⟨hp.some.toEndpointIso hs⟩

omit [DecidableEq V₁] [DecidableEq E₁] [DecidableEq V₂] [DecidableEq E₂] in
theorem EndpointIso.isPetersenUpToParallel {H : LoopMultigraph V₁ E₁}
    {K : LoopMultigraph V₂ E₂} (f : EndpointIso H K) (hp : H.IsPetersenUpToParallel) :
    K.IsPetersenUpToParallel := ⟨f.symm.parallelReduction.trans hp.some⟩

end GraphPuzzles.LoopMultigraph
