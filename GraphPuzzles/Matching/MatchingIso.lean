import GraphPuzzles.Cuts.TightCutTransport

/-! Matching-covered graphs, bipartiteness and tight cuts are invariant under relabelling. -/

namespace GraphPuzzles.LoopMultigraph

variable {V₁ E₁ V₂ E₂ V₃ E₃ : Type*}
  [Fintype V₁] [Fintype E₁] [Fintype V₂] [Fintype E₂] [Fintype V₃] [Fintype E₃]
  [DecidableEq V₁] [DecidableEq E₁] [DecidableEq V₂] [DecidableEq E₂]
  [DecidableEq V₃] [DecidableEq E₃]
variable {G₁ : LoopMultigraph V₁ E₁} {G₂ : LoopMultigraph V₂ E₂} {G₃ : LoopMultigraph V₃ E₃}

namespace EndpointIso

def refl (G : LoopMultigraph V₁ E₁) : EndpointIso G G where
  vertexEquiv := Equiv.refl _
  edgeEquiv := Equiv.refl _
  endEquiv _ := Equiv.refl _
  map_endAt _ _ := rfl

def trans (f : EndpointIso G₁ G₂) (g : EndpointIso G₂ G₃) : EndpointIso G₁ G₃ where
  vertexEquiv := f.vertexEquiv.trans g.vertexEquiv
  edgeEquiv := f.edgeEquiv.trans g.edgeEquiv
  endEquiv e := (f.endEquiv e).trans (g.endEquiv (f.edgeEquiv e))
  map_endAt e k := by
    change g.vertexEquiv (f.vertexEquiv (G₁.endAt e k)) = _
    rw [f.map_endAt, g.map_endAt]
    rfl

variable (f : EndpointIso G₁ G₂)

def mapVertices (X : Finset V₁) : Finset V₂ := X.map f.vertexEquiv.toEmbedding

omit [DecidableEq V₁] [DecidableEq E₁] [DecidableEq V₂] [DecidableEq E₂] in
@[simp]
theorem mem_mapVertices (X : Finset V₁) (v : V₁) :
    f.vertexEquiv v ∈ f.mapVertices X ↔ v ∈ X := by simp [mapVertices]

omit [DecidableEq V₁] [DecidableEq E₁] [DecidableEq V₂] [DecidableEq E₂] in
@[simp]
theorem mapVertices_symm_mapVertices (X : Finset V₂) :
    f.mapVertices (f.symm.mapVertices X) = X := by ext v; simp [mapVertices, symm]

omit [DecidableEq V₁] [DecidableEq E₁] [DecidableEq V₂] [DecidableEq E₂] in
@[simp]
theorem symm_mapVertices_mapVertices (X : Finset V₁) :
    f.symm.mapVertices (f.mapVertices X) = X := by ext v; simp [mapVertices, symm]

omit [DecidableEq V₁] [DecidableEq E₁] [DecidableEq V₂] [DecidableEq E₂] in
@[simp]
theorem mapEdges_symm_mapEdges (M : Finset E₂) : f.mapEdges (f.symm.mapEdges M) = M := by
  ext e
  simp [mapEdges, symm]

private theorem end_cases (σ : Fin 2 ≃ Fin 2) :
    (σ 0 = 0 ∧ σ 1 = 1) ∨ (σ 0 = 1 ∧ σ 1 = 0) := by
  have hn : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
  have h0 := (σ 0).isLt
  have h1 := (σ 1).isLt
  omega

omit [DecidableEq E₁] [DecidableEq E₂] in
theorem mem_dangling_mapVertices (X : Finset V₁) (e : E₁) :
    f.edgeEquiv e ∈ G₂.dangling (f.mapVertices X) ↔ e ∈ G₁.dangling X := by
  have h0 := f.map_endAt e 0
  have h1 := f.map_endAt e 1
  rcases end_cases (f.endEquiv e) with ⟨hzero, hone⟩ | ⟨hone, hzero⟩
  · rw [hzero] at h0
    rw [hone] at h1
    simp only [mem_dangling, ← h0, ← h1, mem_mapVertices]
  · rw [hone] at h0
    rw [hzero] at h1
    simp only [mem_dangling, ← h0, ← h1, mem_mapVertices]
    tauto

omit [DecidableEq E₁] [DecidableEq E₂] in
theorem map_dangling (X : Finset V₁) :
    f.mapEdges (G₁.dangling X) = G₂.dangling (f.mapVertices X) := by
  ext e
  obtain ⟨e, rfl⟩ := f.edgeEquiv.surjective e
  simp only [mem_mapEdges, mem_dangling_mapVertices]

theorem crossing_map (M : Finset E₁) (X : Finset V₁) :
    (f.mapEdges M ∩ G₂.dangling (f.mapVertices X)).card = (M ∩ G₁.dangling X).card := by
  rw [← f.map_dangling]
  simp only [mapEdges, ← Finset.map_inter, Finset.card_map]

omit [DecidableEq E₁] [DecidableEq E₂] in
theorem mapVertices_compl (X : Finset V₁) :
    f.mapVertices (Finset.univ \ X) = Finset.univ \ f.mapVertices X := by
  ext v
  obtain ⟨v, rfl⟩ := f.vertexEquiv.surjective v
  simp only [mem_mapVertices, Finset.mem_sdiff, Finset.mem_univ, true_and]

omit [DecidableEq E₁] [DecidableEq E₂] in
theorem nontrivial_mapVertices (X : Finset V₁) :
    IsNontrivialCut (f.mapVertices X) ↔ IsNontrivialCut X := by
  unfold IsNontrivialCut
  rw [← f.mapVertices_compl]
  simp only [mapVertices, Finset.card_map]

theorem isPerfectMatching {M : Finset E₁} (hM : G₁.IsPerfectMatching M) :
    G₂.IsPerfectMatching (f.mapEdges M) := by
  intro v
  obtain ⟨v, rfl⟩ := f.vertexEquiv.surjective v
  rw [f.degreeIn_mapEdges, hM]

include f in
omit [DecidableEq V₁] [DecidableEq E₁] [DecidableEq V₂] [DecidableEq E₂] in
theorem isConnected (hc : G₁.IsConnected) : G₂.IsConnected := by
  intro c he u v
  have hh (e : E₁) : c (f.vertexEquiv (G₁.endAt e 0)) = c (f.vertexEquiv (G₁.endAt e 1)) := by
    rw [f.map_endAt, f.map_endAt]
    rcases end_cases (f.endEquiv e) with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · simpa only [h0, h1] using he (f.edgeEquiv e)
    · simpa only [h0, h1] using (he (f.edgeEquiv e)).symm
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
    hc (c ∘ f.vertexEquiv) hh (f.vertexEquiv.symm u) (f.vertexEquiv.symm v)

include f in
theorem isMatchingCovered (hm : G₁.IsMatchingCovered) : G₂.IsMatchingCovered := by
  refine ⟨f.isConnected hm.1, ?_⟩
  intro e
  obtain ⟨e, rfl⟩ := f.edgeEquiv.surjective e
  obtain ⟨M, hM, he⟩ := hm.2 e
  exact ⟨f.mapEdges M, f.isPerfectMatching hM, (f.mem_mapEdges M e).mpr he⟩

include f in
omit [DecidableEq V₁] [DecidableEq E₁] [DecidableEq V₂] [DecidableEq E₂] in
theorem isBipartite (hb : G₁.IsBipartite) : G₂.IsBipartite := by
  obtain ⟨c, hc⟩ := hb
  refine ⟨c ∘ f.vertexEquiv.symm, ?_⟩
  intro e
  obtain ⟨e, rfl⟩ := f.edgeEquiv.surjective e
  have h0 := f.map_endAt e 0
  have h1 := f.map_endAt e 1
  rcases end_cases (f.endEquiv e) with ⟨hzero, hone⟩ | ⟨hone, hzero⟩
  · rw [hzero] at h0
    rw [hone] at h1
    simpa only [Function.comp_apply, ← h0, ← h1, Equiv.symm_apply_apply] using hc e
  · rw [hone] at h0
    rw [hzero] at h1
    simpa only [Function.comp_apply, ← h0, ← h1, Equiv.symm_apply_apply] using (hc e).symm

omit [DecidableEq V₁] [DecidableEq E₁] [DecidableEq V₂] [DecidableEq E₂] in
theorem isBipartiteOn {X : Finset V₁} (hb : G₁.IsBipartiteOn X) :
    G₂.IsBipartiteOn (f.mapVertices X) := by
  obtain ⟨c, hc⟩ := hb
  refine ⟨c ∘ f.vertexEquiv.symm, ?_⟩
  intro e hv0 hv1
  obtain ⟨e, rfl⟩ := f.edgeEquiv.surjective e
  have h0 := f.map_endAt e 0
  have h1 := f.map_endAt e 1
  rcases end_cases (f.endEquiv e) with ⟨hzero, hone⟩ | ⟨hone, hzero⟩
  · rw [hzero] at h0
    rw [hone] at h1
    simp only [← h0, ← h1, mem_mapVertices] at hv0 hv1
    simpa only [Function.comp_apply, ← h0, ← h1, Equiv.symm_apply_apply] using hc e hv0 hv1
  · rw [hone] at h0
    rw [hzero] at h1
    simp only [← h0, ← h1, mem_mapVertices] at hv0 hv1
    simpa only [Function.comp_apply, ← h0, ← h1, Equiv.symm_apply_apply] using (hc e hv1 hv0).symm

theorem isTightCut {X : Finset V₁} (ht : G₁.IsTightCut X) :
    G₂.IsTightCut (f.mapVertices X) := by
  intro M hM
  rw [← f.mapEdges_symm_mapEdges M, f.crossing_map]
  exact ht _ (f.symm.isPerfectMatching hM)

include f in
theorem isBrick (hb : G₁.IsBrick) : G₂.IsBrick := by
  refine ⟨fun h ↦ hb.notBipartite (f.symm.isBipartite h), f.isMatchingCovered hb.matchingCovered, ?_⟩
  intro X ht hn
  exact hb.tight_trivial (f.symm.mapVertices X) (f.symm.isTightCut ht)
    ((f.symm.nontrivial_mapVertices X).mpr hn)

end EndpointIso
end GraphPuzzles.LoopMultigraph
