import GraphPuzzles.Reduction.Parallel.ParallelStructureTransport
import GraphPuzzles.Cuts.Contraction.ContractionBarrierLift

/-! Parallel reduction commutes with retaining and contracting corresponding shores. -/

namespace GraphPuzzles.LoopMultigraph.ParallelReduction

variable {V₁ E₁ V₂ E₂ : Type*}
  [Fintype V₁] [Fintype E₁] [Fintype V₂] [Fintype E₂]
  [DecidableEq V₁] [DecidableEq E₁] [DecidableEq V₂] [DecidableEq E₂]
variable {H : LoopMultigraph V₁ E₁} {K : LoopMultigraph V₂ E₂}
variable (f : ParallelReduction H K)

omit [DecidableEq V₁] [DecidableEq E₁] [DecidableEq V₂] [DecidableEq E₂] in
theorem mapVertices_injective : Function.Injective f.mapVertices := by
  intro X Y h
  ext v
  rw [← f.mem_mapVertices X v, ← f.mem_mapVertices Y v, h]

/-- The vertex equivalence restricted to a retained shore. -/
def shoreEquiv (X : Finset V₁) : X ≃ f.mapVertices X where
  toFun v := ⟨f.vertexEquiv v.val, (f.mem_mapVertices X v.val).mpr v.property⟩
  invFun v := ⟨f.vertexEquiv.symm v.val, by
    apply (f.mem_mapVertices X _).mp
    simpa only [Equiv.apply_symm_apply] using v.property⟩
  left_inv v := Subtype.ext (f.vertexEquiv.symm_apply_apply v.val)
  right_inv v := Subtype.ext (f.vertexEquiv.apply_symm_apply v.val)

/-- Retained vertices are relabelled; the contracted pole is fixed. -/
def contractVertexEquiv (X : Finset V₁) : Option X ≃ Option (f.mapVertices X) :=
  Equiv.optionCongr (f.shoreEquiv X)

omit [DecidableEq V₁] [DecidableEq E₁] [DecidableEq V₂] [DecidableEq E₂] in
@[simp] theorem contractVertexEquiv_none (X : Finset V₁) :
    f.contractVertexEquiv X none = none := rfl

omit [DecidableEq V₁] [DecidableEq E₁] [DecidableEq V₂] [DecidableEq E₂] in
@[simp] theorem contractVertexEquiv_some (X : Finset V₁) (v : X) :
    f.contractVertexEquiv X (some v) = some (f.shoreEquiv X v) := rfl

omit [DecidableEq E₁] [DecidableEq E₂] in
theorem contractVertex_map (X : Finset V₁) (v : V₁) :
    f.contractVertexEquiv X (contractVertex X v) =
      contractVertex (f.mapVertices X) (f.vertexEquiv v) := by
  by_cases hv : v ∈ X
  · have hf := (f.mem_mapVertices X v).mpr hv
    simp only [contractVertex, dif_pos hv, dif_pos hf, contractVertexEquiv_some]
    rfl
  · have hf : f.vertexEquiv v ∉ f.mapVertices X := fun h ↦ hv ((f.mem_mapVertices X v).mp h)
    simp only [contractVertex, dif_neg hv, dif_neg hf, contractVertexEquiv_none]

omit [DecidableEq E₁] [DecidableEq E₂] in
theorem mem_meets_mapVertices (X : Finset V₁) (e : E₁) :
    f.edgeMap e ∈ K.meets (f.mapVertices X) ↔ e ∈ H.meets X := by
  have ends (G : LoopMultigraph V₁ E₁) (e : E₁) :
      e ∈ G.meets X ↔ G.endAt e 0 ∈ X ∨ G.endAt e 1 ∈ X := by
    rw [mem_meets]
    constructor
    · rintro ⟨k, hk⟩
      fin_cases k
      · exact Or.inl hk
      · exact Or.inr hk
    · rintro (h | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
  have ends' : f.edgeMap e ∈ K.meets (f.mapVertices X) ↔
      K.endAt (f.edgeMap e) 0 ∈ f.mapVertices X ∨
      K.endAt (f.edgeMap e) 1 ∈ f.mapVertices X := by
    rw [mem_meets]
    constructor
    · rintro ⟨k, hk⟩
      fin_cases k
      · exact Or.inl hk
      · exact Or.inr hk
    · rintro (h | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
  rw [ends, ends']
  rcases (f.joins_iff e _ _).mp (Or.inl ⟨rfl, rfl⟩) with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · simp only [h0, h1, mem_mapVertices]
  · simp only [h0, h1, mem_mapVertices, or_comm]

/-- The parallel reduction induced on the contractions of corresponding shores. -/
def contract (X : Finset V₁) : ParallelReduction (H.contract X) (K.contract (f.mapVertices X)) where
  vertexEquiv := f.contractVertexEquiv X
  edgeMap e := ⟨f.edgeMap e.val, (f.mem_meets_mapVertices X e.val).mpr e.property⟩
  edge_surjective g := by
    obtain ⟨e, he⟩ := f.edge_surjective g.val
    have hm : e ∈ H.meets X := (f.mem_meets_mapVertices X e).mp (he.symm ▸ g.property)
    exact ⟨⟨e, hm⟩, Subtype.ext he⟩
  joins_iff e a b := by
    rcases (f.joins_iff e.val _ _).mp (Or.inl ⟨rfl, rfl⟩) with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · have h0' : (K.contract (f.mapVertices X)).endAt
          ⟨f.edgeMap e.val, (f.mem_meets_mapVertices X e.val).mpr e.property⟩ 0 =
          f.contractVertexEquiv X ((H.contract X).endAt e 0) := by
        change contractVertex (f.mapVertices X) (K.endAt (f.edgeMap e.val) 0) =
          f.contractVertexEquiv X (contractVertex X (H.endAt e.val 0))
        rw [h0, f.contractVertex_map]
      have h1' : (K.contract (f.mapVertices X)).endAt
          ⟨f.edgeMap e.val, (f.mem_meets_mapVertices X e.val).mpr e.property⟩ 1 =
          f.contractVertexEquiv X ((H.contract X).endAt e 1) := by
        change contractVertex (f.mapVertices X) (K.endAt (f.edgeMap e.val) 1) =
          f.contractVertexEquiv X (contractVertex X (H.endAt e.val 1))
        rw [h1, f.contractVertex_map]
      simp only [Joins, h0', h1', Equiv.apply_eq_iff_eq]
    · have h0' : (K.contract (f.mapVertices X)).endAt
          ⟨f.edgeMap e.val, (f.mem_meets_mapVertices X e.val).mpr e.property⟩ 0 =
          f.contractVertexEquiv X ((H.contract X).endAt e 1) := by
        change contractVertex (f.mapVertices X) (K.endAt (f.edgeMap e.val) 0) =
          f.contractVertexEquiv X (contractVertex X (H.endAt e.val 1))
        rw [h0, f.contractVertex_map]
      have h1' : (K.contract (f.mapVertices X)).endAt
          ⟨f.edgeMap e.val, (f.mem_meets_mapVertices X e.val).mpr e.property⟩ 1 =
          f.contractVertexEquiv X ((H.contract X).endAt e 0) := by
        change contractVertex (f.mapVertices X) (K.endAt (f.edgeMap e.val) 1) =
          f.contractVertexEquiv X (contractVertex X (H.endAt e.val 0))
        rw [h1, f.contractVertex_map]
      simp only [Joins, h0', h1', Equiv.apply_eq_iff_eq]
      tauto

omit [DecidableEq E₁] [DecidableEq E₂] in
@[simp] theorem contract_vertexEquiv (X : Finset V₁) :
    (f.contract X).vertexEquiv = f.contractVertexEquiv X := rfl

omit [DecidableEq E₁] [DecidableEq E₂] in
@[simp] theorem none_mem_contract_mapVertices (X : Finset V₁) (Y : Finset (Option X)) :
    none ∈ (f.contract X).mapVertices Y ↔ none ∈ Y :=
  (f.contract X).mem_mapVertices Y none

omit [DecidableEq E₁] [DecidableEq E₂] in
theorem map_expandedContractShore (X : Finset V₁) (Y : Finset (Option X)) :
    f.mapVertices (expandedContractShore X Y) =
      expandedContractShore (f.mapVertices X) ((f.contract X).mapVertices Y) := by
  ext v
  obtain ⟨v, rfl⟩ := f.vertexEquiv.surjective v
  rw [f.mem_mapVertices, mem_expandedContractShore, mem_expandedContractShore,
    ← f.contractVertex_map]
  exact ((f.contract X).mem_mapVertices Y (contractVertex X v)).symm

omit [DecidableEq E₁] [DecidableEq E₂] in
theorem map_sourceShore (X : Finset V₁) (Y : Finset (Option X)) (hn : none ∉ Y) :
    f.mapVertices (sourceShore X Y) =
      sourceShore (f.mapVertices X) ((f.contract X).mapVertices Y) := by
  have hn' : none ∉ (f.contract X).mapVertices Y :=
    fun h ↦ hn ((f.none_mem_contract_mapVertices X Y).mp h)
  rw [← expandedContractShore_eq_source X Y hn,
    ← expandedContractShore_eq_source (f.mapVertices X) _ hn', f.map_expandedContractShore]

/-- Corresponding contractions give separating-cut transport without ambient
connectivity or nonempty-shore assumptions. -/
theorem isSeparatingCut_iff_contract (X : Finset V₁) :
    H.IsSeparatingCut X ↔ K.IsSeparatingCut (f.mapVertices X) := by
  unfold IsSeparatingCut
  rw [← f.mapVertices_compl, (f.contract X).isMatchingCovered_iff,
    (f.contract (Finset.univ \ X)).isMatchingCovered_iff]

end GraphPuzzles.LoopMultigraph.ParallelReduction
