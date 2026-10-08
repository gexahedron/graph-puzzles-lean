import GraphPuzzles.Cuts.Shores.ShoreConnectivity
import GraphPuzzles.Cuts.Contraction.ContractionIso

/-! Connectivity on retained shores is unchanged by contracting their complement. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

omit [DecidableEq E] in
theorem contract_connectedOn_iff {X Z : Finset V} (hZX : Z ⊆ X) :
    (H.contract X).IsConnectedOn (contractShore X Z) ↔ H.IsConnectedOn Z := by
  constructor
  · intro hc c he a ha b hb
    let d : Option X → Bool := fun v ↦ match v with
      | none => false
      | some v => c v.1
    have hlocal (e : H.meets X)
        (h0 : (H.contract X).endAt e 0 ∈ contractShore X Z)
        (h1 : (H.contract X).endAt e 1 ∈ contractShore X Z) :
        d ((H.contract X).endAt e 0) = d ((H.contract X).endAt e 1) := by
      obtain ⟨h0X, h0Z⟩ := (contract_end_mem_contractShore X Z e 0).mp h0
      obtain ⟨h1X, h1Z⟩ := (contract_end_mem_contractShore X Z e 1).mp h1
      simpa only [contract_endAt, dif_pos h0X, dif_pos h1X, d] using he e.1 h0Z h1Z
    exact hc d hlocal (some ⟨a, hZX ha⟩) ((some_mem_contractShore _ _ _).mpr ha)
      (some ⟨b, hZX hb⟩) ((some_mem_contractShore _ _ _).mpr hb)
  · intro hc c he a ha b hb
    cases a with
    | none => exact (none_not_mem_contractShore X Z ha).elim
    | some a =>
      cases b with
      | none => exact (none_not_mem_contractShore X Z hb).elim
      | some b =>
        let d : V → Bool := fun v ↦ c (contractVertex X v)
        have hlocal (e : E) (h0 : H.endAt e 0 ∈ Z) (h1 : H.endAt e 1 ∈ Z) :
            d (H.endAt e 0) = d (H.endAt e 1) := by
          let f : H.meets X := ⟨e, mem_meets.mpr ⟨0, hZX h0⟩⟩
          exact he f ((contract_end_mem_contractShore X Z f 0).mpr ⟨hZX h0, h0⟩)
            ((contract_end_mem_contractShore X Z f 1).mpr ⟨hZX h1, h1⟩)
        have hh := hc d hlocal a.1 ((some_mem_contractShore _ _ _).mp ha)
          b.1 ((some_mem_contractShore _ _ _).mp hb)
        simpa only [d, contractVertex_some] using hh

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem contractShore_erase (X : Finset V) (v : X) :
    contractShore X (X.erase v.1) = (Finset.univ.erase none).erase (some v) := by
  ext w
  cases w with
  | none => simp
  | some w =>
    rw [some_mem_contractShore]
    constructor
    · intro hw
      exact Finset.mem_erase.mpr ⟨fun he ↦ (Finset.mem_erase.mp hw).1
        (congrArg Subtype.val (Option.some.inj he)),
        Finset.mem_erase.mpr ⟨by simp, Finset.mem_univ _⟩⟩
    · intro hw
      exact Finset.mem_erase.mpr ⟨fun he ↦ (Finset.mem_erase.mp hw).1
        (congrArg some (Subtype.ext he)), w.2⟩

omit [DecidableEq E] in
/-- Delete the contraction vertex and one retained vertex, then read the
remaining connected shore in the original graph. -/
theorem contract_connectedOn_delete_iff (X : Finset V) (v : X) :
    (H.contract X).IsConnectedOn ((Finset.univ.erase none).erase (some v)) ↔
      H.IsConnectedOn (X.erase v.1) := by
  rw [← contractShore_erase]
  exact contract_connectedOn_iff (Finset.erase_subset _ _)

omit [DecidableEq E] in
theorem contract_joins_none_some {X : Finset V} (e : H.meets X) (v : X) :
    (H.contract X).Joins e none (some v) ↔ ∃ u, u ∉ X ∧ H.Joins e.1 u v.1 := by
  constructor
  · intro h
    rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact ⟨H.endAt e.1 0, (contract_endAt_eq_none_iff X e 0).mp h0,
        Or.inl ⟨rfl, (contract_endAt_eq_some_iff X e 1 v).mp h1⟩⟩
    · exact ⟨H.endAt e.1 1, (contract_endAt_eq_none_iff X e 1).mp h1,
        Or.inr ⟨(contract_endAt_eq_some_iff X e 0 v).mp h0, rfl⟩⟩
  · rintro ⟨u, hu, h⟩
    rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact Or.inl ⟨(contract_endAt_eq_none_iff X e 0).mpr (h0.symm ▸ hu),
        (contract_endAt_eq_some_iff X e 1 v).mpr h1⟩
    · exact Or.inr ⟨(contract_endAt_eq_some_iff X e 0 v).mpr h0,
        (contract_endAt_eq_none_iff X e 1).mpr (h1.symm ▸ hu)⟩

end GraphPuzzles.LoopMultigraph
