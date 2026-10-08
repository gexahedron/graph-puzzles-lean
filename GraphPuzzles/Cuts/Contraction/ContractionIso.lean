import GraphPuzzles.Matching.MatchingIso

/-! Explicit graph isomorphisms for iterated shore contractions. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem contractShore_sourceShore (X : Finset V) (Y : Finset (Option X)) (hn : none ∉ Y) :
    contractShore X (sourceShore X Y) = Y := by
  ext v
  cases v with
  | none => simp [hn]
  | some v =>
    rw [some_mem_contractShore]
    simp only [sourceShore, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨w, hw, he⟩
      have hh : w = v := Subtype.ext he
      rwa [hh] at hw
    · intro hv
      exact ⟨v, hv, rfl⟩

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem card_contractShore_of_subset {X Z : Finset V} (hs : Z ⊆ X) :
    (contractShore X Z).card = Z.card := by
  rw [← card_sourceShore X (contractShore X Z) (none_not_mem_contractShore X Z),
    sourceShore_contractShore, Finset.inter_eq_right.mpr hs]

omit [DecidableEq E] in
theorem contract_end_mem_contractShore (X Z : Finset V) (e : H.meets X) (k : Fin 2) :
    (H.contract X).endAt e k ∈ contractShore X Z ↔
      H.endAt e.1 k ∈ X ∧ H.endAt e.1 k ∈ Z := by
  rw [contract_endAt]
  split_ifs with h
  · simp [h]
  · simp [h]

omit [DecidableEq E] in
theorem contract_mem_meets_shore {X Z : Finset V} (hs : Z ⊆ X) (e : H.meets X) :
    e ∈ (H.contract X).meets (contractShore X Z) ↔ e.1 ∈ H.meets Z := by
  simp only [mem_meets, contract_end_mem_contractShore]
  exact ⟨fun ⟨k, _, hk⟩ ↦ ⟨k, hk⟩, fun ⟨k, hk⟩ ↦ ⟨k, hs hk, hk⟩⟩

/-- The vertices retained by the second of two nested contractions are exactly the
vertices of the inner shore. -/
noncomputable def contractShoreEquiv {X Z : Finset V} (hs : Z ⊆ X) :
    ↥(contractShore X Z) ≃ ↥Z where
  toFun y := by
    obtain ⟨y, hy⟩ := y
    cases y with
    | none => exact ((none_not_mem_contractShore X Z) hy).elim
    | some v => exact ⟨v.1, (some_mem_contractShore X Z v).mp hy⟩
  invFun z := ⟨some ⟨z.1, hs z.2⟩, by simp [z.2]⟩
  left_inv y := by
    obtain ⟨y, hy⟩ := y
    cases y with
    | none => exact ((none_not_mem_contractShore X Z) hy).elim
    | some v => rfl
  right_inv z := rfl

noncomputable def contractNestedEdgeEquiv {X Z : Finset V} (hs : Z ⊆ X) :
    ↥((H.contract X).meets (contractShore X Z)) ≃ ↥(H.meets Z) where
  toFun e := ⟨e.1.1, (contract_mem_meets_shore hs e.1).mp e.2⟩
  invFun e := by
    have he : e.1 ∈ H.meets X := by
      obtain ⟨k, hk⟩ := mem_meets.mp e.2
      exact mem_meets.mpr ⟨k, hs hk⟩
    exact ⟨⟨e.1, he⟩, (contract_mem_meets_shore hs ⟨e.1, he⟩).mpr e.2⟩
  left_inv e := rfl
  right_inv e := rfl

/-- Retaining a nested shore after contraction is the same as contracting directly to it. -/
noncomputable def contractNestedIso {X Z : Finset V} (hs : Z ⊆ X) :
    EndpointIso ((H.contract X).contract (contractShore X Z)) (H.contract Z) where
  vertexEquiv := Equiv.optionCongr (contractShoreEquiv hs)
  edgeEquiv := contractNestedEdgeEquiv hs
  endEquiv _ := Equiv.refl _
  map_endAt e k := by
    classical
    by_cases hz : H.endAt e.1.1 k ∈ Z
    · have hx := hs hz
      simp only [contract_endAt, dif_pos hx, some_mem_contractShore, dif_pos hz,
        Equiv.refl_apply, Equiv.optionCongr, Equiv.coe_fn_mk, Option.map_some,
        contractShoreEquiv, contractNestedEdgeEquiv]
    · by_cases hx : H.endAt e.1.1 k ∈ X
      · simp only [contract_endAt, dif_pos hx, some_mem_contractShore, dif_neg hz,
          Equiv.refl_apply, Equiv.optionCongr, Equiv.coe_fn_mk, Option.map_none,
          contractNestedEdgeEquiv]
      · simp [contract_endAt, hx, hz, Equiv.optionCongr, contractNestedEdgeEquiv]

end GraphPuzzles.LoopMultigraph
