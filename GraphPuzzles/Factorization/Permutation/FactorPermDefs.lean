import GraphPuzzles.FinGraph.FinGraphCycleCut
import GraphPuzzles.Factorization.Bicritical.FactorParity

/-!
# Permutation graphs

A permutation graph is a cubic graph with a `2`-factor consisting of two induced odd cycles
(the rims), the remaining edges (the spokes) forming a perfect matching between them.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

variable {Γ : FinGraph}

/-- A permutation structure: rims `R₁`, `R₂` on the vertex sets `V₁`, `V₂`, each an induced
Hamilton cycle of its side, the remaining edges (spokes) forming a perfect matching.  Rims of
length one or two are excluded (the two-vertex dumbbell-like cases); for a snark the rims are
odd (`IsPermGraph.odd`). -/
structure IsPermGraph (Γ : FinGraph) (V₁ V₂ R₁ R₂ : Finset ℕ) : Prop where
  disj : Disjoint V₁ V₂
  union : V₁ ∪ V₂ = Γ.Vs
  ham₁ : Γ.IsHamCycle V₁ R₁
  ham₂ : Γ.IsHamCycle V₂ R₂
  induced₁ : Γ.edgesIn V₁ = R₁
  induced₂ : Γ.edgesIn V₂ = R₂
  spoke : ∀ v ∈ Γ.Vs, Γ.degIn (Γ.bd V₁) v = 1
  three : 3 ≤ V₁.card

/-- **Permutation snarks**: closed cubic uncolourable permutation graphs. -/
def IsPermutationSnark (Γ : FinGraph) : Prop :=
  Γ.IsClosed ∧ Γ.IsCubic ∧ ¬ Γ.Colourable ∧ ∃ V₁ V₂ R₁ R₂, Γ.IsPermGraph V₁ V₂ R₁ R₂

namespace IsPermGraph

variable {V₁ V₂ R₁ R₂ : Finset ℕ} (hP : Γ.IsPermGraph V₁ V₂ R₁ R₂)
include hP

theorem V₁_subset : V₁ ⊆ Γ.Vs := by rw [← hP.union]; exact Finset.subset_union_left
theorem V₂_subset : V₂ ⊆ Γ.Vs := by rw [← hP.union]; exact Finset.subset_union_right

theorem mem_V₂_iff {v : ℕ} (hv : v ∈ Γ.Vs) : v ∈ V₂ ↔ v ∉ V₁ := by
  constructor
  · intro h h'
    exact Finset.disjoint_left.mp hP.disj h' h
  · intro h
    rw [← hP.union, Finset.mem_union] at hv
    exact hv.resolve_left h

theorem V₂_eq : V₂ = Γ.Vs \ V₁ := by
  ext v
  rw [Finset.mem_sdiff]
  constructor
  · intro h
    exact ⟨hP.V₂_subset h, fun h' ↦ Finset.disjoint_left.mp hP.disj h' h⟩
  · rintro ⟨hv, h⟩
    exact (hP.mem_V₂_iff hv).mpr h

theorem bd_V₂ (hcl : Γ.IsClosed) : Γ.bd V₂ = Γ.bd V₁ := by
  rw [hP.V₂_eq, bd_compl hcl]

theorem R₁_subset : R₁ ⊆ Γ.Es := hP.ham₁.subset.trans (edgesIn_subset _)
theorem R₂_subset : R₂ ⊆ Γ.Es := hP.ham₂.subset.trans (edgesIn_subset _)

theorem no_loop₁ : ∀ e ∈ R₁, Γ.ends e 0 ≠ Γ.ends e 1 :=
  hP.ham₁.no_loop (by have := hP.three; omega)

theorem card_bd : (Γ.bd V₁).card = V₁.card := by
  have h := sum_degIn_eq (Γ := Γ) (Γ.bd V₁) V₁
  rw [Finset.sum_congr rfl (fun v hv ↦ hP.spoke v (hP.V₁_subset hv)), Finset.sum_const,
    smul_eq_mul, mul_one, Finset.sum_congr rfl (fun e he ↦ endsIn_of_mem_bd he), Finset.sum_const,
    smul_eq_mul, mul_one] at h
  exact h.symm

theorem card_V₂ (hcl : Γ.IsClosed) : V₂.card = V₁.card := by
  have h := sum_degIn_eq (Γ := Γ) (Γ.bd V₁) V₂
  rw [Finset.sum_congr rfl (fun v hv ↦ hP.spoke v (hP.V₂_subset hv)), Finset.sum_const,
    smul_eq_mul, mul_one, ← hP.bd_V₂ hcl,
    Finset.sum_congr rfl (fun e he ↦ endsIn_of_mem_bd he), Finset.sum_const,
    smul_eq_mul, mul_one, hP.bd_V₂ hcl, hP.card_bd] at h
  exact h

theorem no_loop₂ (hcl : Γ.IsClosed) : ∀ e ∈ R₂, Γ.ends e 0 ≠ Γ.ends e 1 :=
  hP.ham₂.no_loop (by rw [hP.card_V₂ hcl]; have := hP.three; omega)

/-- Every edge at a vertex of `V₁` is a rim edge of `R₁` or a spoke. -/
theorem edge_at_V₁ {e : ℕ} (he : e ∈ Γ.Es) {i : Fin 2} (hi : Γ.ends e i ∈ V₁) :
    e ∈ R₁ ∨ e ∈ Γ.bd V₁ := by
  rcases mem_edgesIn_or_bd he hi with h | h
  · exact Or.inl (hP.induced₁ ▸ h)
  · exact Or.inr h

theorem edge_at_V₂ (hcl : Γ.IsClosed) {e : ℕ} (he : e ∈ Γ.Es) {i : Fin 2} (hi : Γ.ends e i ∈ V₂) :
    e ∈ R₂ ∨ e ∈ Γ.bd V₁ := by
  rcases mem_edgesIn_or_bd he hi with h | h
  · exact Or.inl (hP.induced₂ ▸ h)
  · rw [hP.bd_V₂ hcl] at h
    exact Or.inr h

/-- No loops at all. -/
theorem no_loop (hcl : Γ.IsClosed) : ∀ e ∈ Γ.Es, Γ.ends e 0 ≠ Γ.ends e 1 := by
  intro e he hl
  have h0 := hcl e he 0
  rw [← hP.union, Finset.mem_union] at h0
  rcases h0 with h0 | h0
  · rcases hP.edge_at_V₁ he h0 with h | h
    · exact hP.no_loop₁ e h hl
    · rw [mem_bd] at h
      exact h.2 ⟨fun _ ↦ hl ▸ h0, fun _ ↦ h0⟩
  · rcases hP.edge_at_V₂ hcl he h0 with h | h
    · exact hP.no_loop₂ hcl e h hl
    · rw [mem_bd] at h
      have h0' : Γ.ends e 0 ∉ V₁ := fun h' ↦ Finset.disjoint_left.mp hP.disj h' h0
      exact h.2 ⟨fun h' ↦ absurd h' h0', fun h' ↦ absurd (hl ▸ h') h0'⟩

/-- A rim edge and a spoke are different edges; two spokes at a vertex coincide. -/
theorem spoke_unique {v : ℕ} (hv : v ∈ Γ.Vs) {e f : ℕ} (he : e ∈ Γ.bd V₁) (hf : f ∈ Γ.bd V₁)
    {i j : Fin 2} (hi : Γ.ends e i = v) (hj : Γ.ends f j = v) : e = f := by
  by_contra hne
  have := degIn_bd_le_of_two_edges he hf hne hi hj
  have := hP.spoke v hv
  omega

theorem rim_not_spoke₁ {e : ℕ} (he : e ∈ R₁) : e ∉ Γ.bd V₁ :=
  fun h ↦ Finset.disjoint_left.mp (disjoint_edgesIn_bd V₁) (hP.induced₁ ▸ he) h

theorem rim_not_spoke₂ (hcl : Γ.IsClosed) {e : ℕ} (he : e ∈ R₂) : e ∉ Γ.bd V₁ := by
  rw [← hP.bd_V₂ hcl]
  exact fun h ↦ Finset.disjoint_left.mp (disjoint_edgesIn_bd V₂) (hP.induced₂ ▸ he) h

/-- The rims are disjoint. -/
theorem disjoint_rims : Disjoint R₁ R₂ := by
  rw [Finset.disjoint_left]
  intro e h1 h2
  have := (mem_edgesIn.mp (hP.ham₁.subset h1)).2 0
  have := (mem_edgesIn.mp (hP.ham₂.subset h2)).2 0
  exact Finset.disjoint_left.mp hP.disj ‹_› ‹_›

/-- Six vertices at least. -/
theorem six_le (hcl : Γ.IsClosed) : 6 ≤ Γ.Vs.card := by
  rw [← hP.union, Finset.card_union_of_disjoint hP.disj, hP.card_V₂ hcl]
  have := hP.three; omega

end IsPermGraph

end FinGraph
end GraphPuzzles
