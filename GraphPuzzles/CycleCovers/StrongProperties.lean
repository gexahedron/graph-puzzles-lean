import GraphPuzzles.CycleCovers.DominatingCircuit

/-! Strong covers prescribe a circuit as a component. Entire-layer containment is separate.
Empty indexed layers are permitted, so the layer count is an upper bound. -/

namespace GraphPuzzles
namespace LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- A circuit is a component of an edge set if it is included and the remaining edges have
no endpoint on the circuit. Connectivity of the circuit is part of `OrdinaryCircuit`. -/
def OrdinaryCircuit.IsComponentOf (C : H.OrdinaryCircuit) (F : Finset E) : Prop :=
  C.edges ⊆ F ∧ ∀ e ∈ F \ C.edges, ∀ i, H.endAt e i ∉ H.edgeSupport C.edges

/-- A cover contains the prescribed circuit as a component of an even layer. -/
def CycleDoubleCover.ContainsComponent {k : ℕ} (D : H.CycleDoubleCover k)
    (C : H.OrdinaryCircuit) : Prop := ∃ i, C.IsComponentOf (D.cycles i).edges

/-- A bounded cycle double cover exists. -/
def HasCycleDoubleCover (H : LoopMultigraph V E) (k : ℕ) : Prop :=
  Nonempty (H.CycleDoubleCover k)

/-- The standard strong property: each prescribed circuit is a component of some `k`-cover. -/
def HasStrongCycleDoubleCover (H : LoopMultigraph V E) (k : ℕ) : Prop :=
  ∀ C : H.OrdinaryCircuit, ∃ D : H.CycleDoubleCover k, D.ContainsComponent C

/-- The stronger property that each prescribed circuit is an entire indexed layer. -/
def HasEntireLayerStrongCycleDoubleCover (H : LoopMultigraph V E) (k : ℕ) : Prop :=
  ∀ C : H.OrdinaryCircuit, ∃ D : H.CycleDoubleCover k, D.Contains C.edges

theorem CycleDoubleCover.Contains.containsComponent {k : ℕ} {D : H.CycleDoubleCover k}
    {C : H.OrdinaryCircuit} (h : D.Contains C.edges) : D.ContainsComponent C := by
  obtain ⟨i, hi⟩ := h
  refine ⟨i, ?_⟩
  rw [hi]
  exact ⟨Finset.Subset.refl _, by simp⟩

theorem CycleDoubleCover.containsComponent_of_contains_union {k : ℕ}
    {D : H.CycleDoubleCover k} (C : H.OrdinaryCircuit) (F : Finset E)
    (h : D.Contains (C.edges ∪ F))
    (hdisj : ∀ e ∈ F, ∀ i, H.endAt e i ∉ H.edgeSupport C.edges) :
    D.ContainsComponent C := by
  obtain ⟨i, hi⟩ := h
  refine ⟨i, ?_⟩
  rw [hi]
  refine ⟨Finset.subset_union_left, ?_⟩
  intro e he j
  obtain ⟨he, hn⟩ := Finset.mem_sdiff.mp he
  exact hdisj e ((Finset.mem_union.mp he).resolve_left hn) j

theorem HasEntireLayerStrongCycleDoubleCover.strong {k : ℕ}
    (h : H.HasEntireLayerStrongCycleDoubleCover k) : H.HasStrongCycleDoubleCover k := by
  intro C
  obtain ⟨D, hD⟩ := h C
  exact ⟨D, hD.containsComponent⟩


end LoopMultigraph
end GraphPuzzles
