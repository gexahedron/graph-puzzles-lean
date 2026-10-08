import GraphPuzzles.Cuts.Contraction.ContractionIso

/-! Contractions of disjoint shores commute, with the two poles exchanged explicitly. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- A retained shore together with the previous contraction pole. -/
noncomputable def poleShore (X Z : Finset V) : Finset (Option X) :=
  insert none (contractShore X Z)

omit [Fintype V] in
@[simp]
theorem none_mem_poleShore (X Z : Finset V) : none ∈ poleShore X Z := by simp [poleShore]

omit [Fintype V] in
@[simp]
theorem some_mem_poleShore (X Z : Finset V) (v : X) :
    some v ∈ poleShore X Z ↔ v.1 ∈ Z := by simp [poleShore]

theorem compl_contractShore (X Z : Finset V) :
    Finset.univ \ contractShore X Z = poleShore X (Finset.univ \ Z) := by
  ext v
  cases v <;> simp [poleShore]

theorem compl_poleShore (X Z : Finset V) :
    Finset.univ \ poleShore X Z = contractShore X (Finset.univ \ Z) := by
  ext v
  cases v <;> simp [poleShore]

omit [DecidableEq E] in
theorem contract_end_mem_poleShore {X Z : Finset V} (hu : X ∪ Z = Finset.univ)
    (e : H.meets X) (k : Fin 2) :
    (H.contract X).endAt e k ∈ poleShore X Z ↔ H.endAt e.1 k ∈ Z := by
  rw [contract_endAt]
  split_ifs with hx
  · simp
  · have hz : H.endAt e.1 k ∈ Z := by
      have hh : H.endAt e.1 k ∈ X ∪ Z := hu.symm ▸ Finset.mem_univ _
      exact (Finset.mem_union.mp hh).resolve_left hx
    simp [hz]

omit [DecidableEq E] in
theorem contract_mem_meets_poleShore {X Z : Finset V} (hu : X ∪ Z = Finset.univ)
    (e : H.meets X) :
    e ∈ (H.contract X).meets (poleShore X Z) ↔ e.1 ∈ H.meets Z := by
  simp only [mem_meets, contract_end_mem_poleShore hu]

noncomputable def swapContractVertex (X Z : Finset V) :
    Option ↥(poleShore X Z) → Option ↥(poleShore Z X)
  | none => some ⟨none, none_mem_poleShore Z X⟩
  | some ⟨none, _⟩ => none
  | some ⟨some v, hv⟩ =>
    some ⟨some ⟨v.1, (some_mem_poleShore X Z v).mp hv⟩,
      (some_mem_poleShore Z X _).mpr v.2⟩

omit [Fintype V] in
theorem swapContractVertex_involutive (X Z : Finset V) (v : Option ↥(poleShore X Z)) :
    swapContractVertex Z X (swapContractVertex X Z v) = v := by
  cases v with
  | none => rfl
  | some v =>
    obtain ⟨v, hv⟩ := v
    cases v <;> rfl

noncomputable def commuteContractVertexEquiv (X Z : Finset V) :
    Option ↥(poleShore X Z) ≃ Option ↥(poleShore Z X) where
  toFun := swapContractVertex X Z
  invFun := swapContractVertex Z X
  left_inv := swapContractVertex_involutive X Z
  right_inv := swapContractVertex_involutive Z X

noncomputable def commuteContractEdgeEquiv {X Z : Finset V} (hu : X ∪ Z = Finset.univ) :
    ↥((H.contract X).meets (poleShore X Z)) ≃ ↥((H.contract Z).meets (poleShore Z X)) where
  toFun e := by
    have hz := (contract_mem_meets_poleShore hu e.1).mp e.2
    exact ⟨⟨e.1.1, hz⟩, (contract_mem_meets_poleShore
      (by rwa [Finset.union_comm]) ⟨e.1.1, hz⟩).mpr e.1.2⟩
  invFun e := by
    have hx := (contract_mem_meets_poleShore (X := Z) (Z := X)
      (by rwa [Finset.union_comm]) e.1).mp e.2
    exact ⟨⟨e.1.1, hx⟩, (contract_mem_meets_poleShore hu ⟨e.1.1, hx⟩).mpr e.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Keeping two shores whose union is the whole graph commutes. Equivalently, the
two disjoint complementary shores may be contracted in either order. -/
noncomputable def contractCommuteIso {X Z : Finset V} (hu : X ∪ Z = Finset.univ) :
    EndpointIso ((H.contract X).contract (poleShore X Z))
      ((H.contract Z).contract (poleShore Z X)) where
  vertexEquiv := commuteContractVertexEquiv X Z
  edgeEquiv := commuteContractEdgeEquiv hu
  endEquiv _ := Equiv.refl _
  map_endAt e k := by
    classical
    by_cases hx : H.endAt e.1.1 k ∈ X <;> by_cases hz : H.endAt e.1.1 k ∈ Z
    · simp [contract_endAt, hx, hz, commuteContractVertexEquiv, commuteContractEdgeEquiv,
        swapContractVertex]
    · simp [contract_endAt, hx, hz, commuteContractVertexEquiv, commuteContractEdgeEquiv,
        swapContractVertex]
    · simp [contract_endAt, hx, hz, commuteContractVertexEquiv, commuteContractEdgeEquiv,
        swapContractVertex]
    · have hh : H.endAt e.1.1 k ∈ X ∪ Z := hu.symm ▸ Finset.mem_univ _
      exact ((Finset.mem_union.mp hh).elim hx hz).elim

end GraphPuzzles.LoopMultigraph
