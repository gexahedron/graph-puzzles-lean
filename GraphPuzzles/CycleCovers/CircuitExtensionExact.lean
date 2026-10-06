import GraphPuzzles.CycleCovers.CircuitExtensionCorollaries

/-!
# The exact circuit-extension equivalences

The converse uses the four labels in `F₂²` for the four layers other than the prescribed
circuit. The sum of the two labels on an outside edge is nonzero, and evenness of every
layer makes these colours sum to zero at every vertex outside the circuit.
-/

namespace GraphPuzzles
namespace LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- Three nonzero `F₂²` colours summing to zero are pairwise distinct. -/
theorem color_injective_of_sum_zero {I : Type*} [Fintype I]
    (hcard : Fintype.card I = 3) (f : I → Color)
    (hnz : ∀ i, f i ≠ 0) (hsum : ∑ i, f i = 0) : Function.Injective f := by
  classical
  let e := Fintype.equivFinOfCardEq hcard
  have hfin : ∀ g : Fin 3 → Color, (∀ i, g i ≠ 0) → (∑ i, g i = 0) →
      Function.Injective g := by decide
  have hi := hfin (fun i ↦ f (e.symm i)) (fun i ↦ hnz _) (by
    rw [e.symm.sum_comp]
    exact hsum)
  intro a b hab
  apply e.injective
  apply hi
  simpa using hab

namespace CycleDoubleCover

/-- The sum of arbitrary colour labels of the layers containing an edge. -/
def labelColor {k : ℕ} (D : H.CycleDoubleCover k) (label : Fin k → Color) (e : E) : Color :=
  ∑ i, if e ∈ (D.cycles i).edges then label i else 0

/-- Evenness of the layers gives the flow equation for the sum of their labels. -/
theorem sum_labelColor {k : ℕ} (D : H.CycleDoubleCover k) (label : Fin k → Color) (v : V) :
    ∑ h : H.halfEdgesAt v, D.labelColor label h.1.1 = 0 := by
  unfold labelColor
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i _
  have hi := (H.isEvenEdgeSet_iff_sum_halfEdges _).mp (D.cycles i).even v
  calc
    (∑ h : H.halfEdgesAt v, if h.1.1 ∈ (D.cycles i).edges then label i else 0) =
        (∑ h : H.halfEdgesAt v, if h.1.1 ∈ (D.cycles i).edges then (1 : F₂) else 0) •
          label i := by
      rw [Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro h _
      split_ifs <;> simp
    _ = 0 := by rw [hi, zero_smul]

/-- A five-cover with an entire prescribed circuit gives a complement colouring. -/
theorem exists_complementColoring (D : H.CycleDoubleCover 5) (C : H.TraversedCircuit)
    (hCubic : ∀ v, H.degree v = 3) (hC : D.Contains C.edges) :
    Nonempty C.ComplementColoring := by
  classical
  obtain ⟨r, hr⟩ := hC
  let other : {i : Fin 5 // i ≠ r} ≃ Color := Fintype.equivOfCardEq (by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    decide)
  let label : Fin 5 → Color := fun i ↦ if hi : i = r then 0 else other ⟨i, hi⟩
  have hnz : ∀ e, e ∉ C.edges → D.labelColor label e ≠ 0 := by
    intro e he
    obtain ⟨a, b, hab, hpair⟩ := Finset.card_eq_two.mp (D.coveredTwice e)
    have ha : e ∈ (D.cycles a).edges := by
      have : a ∈ Finset.univ.filter fun i ↦ e ∈ (D.cycles i).edges := by
        rw [hpair]; simp
      exact (Finset.mem_filter.mp this).2
    have hb : e ∈ (D.cycles b).edges := by
      have : b ∈ Finset.univ.filter fun i ↦ e ∈ (D.cycles i).edges := by
        rw [hpair]; simp
      exact (Finset.mem_filter.mp this).2
    have har : a ≠ r := by intro h; subst a; exact he (hr ▸ ha)
    have hbr : b ≠ r := by intro h; subst b; exact he (hr ▸ hb)
    have hl : label a ≠ label b := by
      simp only [label, dif_neg har, dif_neg hbr]
      intro h
      exact hab (congrArg Subtype.val (other.injective h))
    rw [labelColor, ← Finset.sum_filter, hpair, Finset.sum_pair hab]
    intro h
    apply hl
    calc
      label a = label a + (label b + label b) := by simp
      _ = (label a + label b) + label b := (add_assoc _ _ _).symm
      _ = label b := by rw [h, zero_add]
  refine ⟨⟨D.labelColor label, hnz, ?_⟩⟩
  intro v hv
  exact color_injective_of_sum_zero (hCubic v) _
    (fun h ↦ hnz _ (C.edge_not_mem_of_vertex_not_mem hv h)) (D.sum_labelColor label v)

end CycleDoubleCover

namespace OrdinaryCircuit

/-- **Exact extension theorem:** entire-layer containment is equivalent to a proper
three-edge-colouring of the complement of the circuit. -/
theorem exists_fiveCycleDoubleCover_iff_complementColoring (C : H.OrdinaryCircuit)
    (hCubic : ∀ v, H.degree v = 3) :
    (∃ D : H.CycleDoubleCover 5, D.Contains C.edges) ↔
      Nonempty C.toTraversedCircuit.ComplementColoring := by
  constructor
  · rintro ⟨D, hD⟩
    exact D.exists_complementColoring C.toTraversedCircuit hCubic hD
  · rintro ⟨g⟩
    exact C.toTraversedCircuit.exists_fiveCycleDoubleCover_of_complementColoring hCubic g

/-- The same exact equivalence stated using deletion of the circuit's vertices. -/
theorem exists_fiveCycleDoubleCover_iff_properOff (C : H.OrdinaryCircuit)
    (hCubic : ∀ v, H.degree v = 3) :
    (∃ D : H.CycleDoubleCover 5, D.Contains C.edges) ↔
      ∃ g, H.ProperOff (H.edgeSupport C.edges) g := by
  constructor
  · intro h
    obtain ⟨g⟩ := (C.exists_fiveCycleDoubleCover_iff_complementColoring hCubic).mp h
    refine ⟨g.color, ?_, ?_⟩
    · intro e he
      apply g.nonzero
      intro hmem
      exact he 0 (H.mem_edgeSupport_iff.mpr ⟨e, hmem, 0, rfl⟩)
    · intro v hv a b _ _ hab
      exact g.injective_at v hv a b hab
  · rintro ⟨g, hg⟩
    exact C.toTraversedCircuit.exists_fiveCycleDoubleCover_of_properOff hCubic hg

end OrdinaryCircuit
end LoopMultigraph
end GraphPuzzles
