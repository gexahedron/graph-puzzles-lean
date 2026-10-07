import GraphPuzzles.Factorization.Permutation.FactorPermDefs
import GraphPuzzles.Factorization.Bicritical.FactorHalfEdgeMap

/-!
# Colouring a pole of a permutation graph

If a shore `Y` cuts both rims, the pole at `Y` is three-edge-colourable: spokes get the third
colour, and each rim's side part is coloured alternately (`exists_two_colouring_cut`).
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

variable {Γ : FinGraph} {V₁ V₂ R₁ R₂ : Finset ℕ} (hP : Γ.IsPermGraph V₁ V₂ R₁ R₂)
  (hcl : Γ.IsClosed)
include hP hcl

/-- Proper two-edge-colourings of the two rims' side parts at the vertices of `Y` give a
colouring of the pole at `Y` (spokes receive the third colour). -/
theorem IsPermGraph.pole_colourable_of_two_colourings {Y : Finset ℕ} (c₁ c₂ : ℕ → Fin 2)
    (hc₁ : ∀ f ∈ Γ.sidePart R₁ Y, ∀ g ∈ Γ.sidePart R₁ Y, f ≠ g →
      ∀ v ∈ Y, ∀ i j, Γ.ends f i = v → Γ.ends g j = v → c₁ f ≠ c₁ g)
    (hc₂ : ∀ f ∈ Γ.sidePart R₂ Y, ∀ g ∈ Γ.sidePart R₂ Y, f ≠ g →
      ∀ v ∈ Y, ∀ i j, Γ.ends f i = v → Γ.ends g j = v → c₂ f ≠ c₂ g) :
    (Γ.pole Y).Colourable := by
  classical
  have hloop := hP.no_loop hcl
  refine ⟨fun e ↦ if e ∈ R₁ then twoColor (c₁ e) else if e ∈ R₂ then twoColor (c₂ e) else (1, 1),
    ?_, ?_⟩
  · intro e _
    dsimp only
    split_ifs
    · exact twoColor_ne_zero _
    · exact twoColor_ne_zero _
    · decide
  · intro v hv h₁ h₁m h₂ h₂m heq
    have hv' : v ∈ Y := hv
    rw [halfEdgesIn_pole_eq hv'] at h₁m h₂m
    rw [mem_halfEdgesIn] at h₁m h₂m
    obtain ⟨f, i⟩ := h₁
    obtain ⟨g, j⟩ := h₂
    dsimp only at h₁m h₂m heq
    have hvV : v ∈ Γ.Vs := by rw [← h₁m.2]; exact hcl f h₁m.1 i
    -- the generic rim argument
    have rim : ∀ (R : Finset ℕ) (c : ℕ → Fin 2) (V : Finset ℕ), Γ.IsHamCycle V R →
        (∀ f ∈ Γ.sidePart R Y, ∀ g ∈ Γ.sidePart R Y, f ≠ g → ∀ v ∈ Y, ∀ i j,
          Γ.ends f i = v → Γ.ends g j = v → c f ≠ c g) →
        f ∈ R → g ∈ R → twoColor (c f) = twoColor (c g) → (f, i) = (g, j) := by
      intro R c V hR hc hf hg hcol
      have hRE : R ⊆ Γ.Es := hR.subset.trans (edgesIn_subset V)
      by_cases hfg : f = g
      · subst hfg
        rw [idx_eq_of_ends_eq_single (hloop f h₁m.1) (h₁m.2.trans h₂m.2.symm)]
      · exfalso
        exact hc f (mem_sidePart_of_ends hRE hf (h₁m.2 ▸ hv')) g
          (mem_sidePart_of_ends hRE hg (h₂m.2 ▸ hv')) hfg v hv' i j h₁m.2 h₂m.2 (twoColor_inj hcol)
    have hspoke : ∀ f, f ∈ Γ.bd V₁ → f ∉ R₁ ∧ f ∉ R₂ :=
      fun f hf ↦ ⟨fun h ↦ hP.rim_not_spoke₁ h hf, fun h ↦ hP.rim_not_spoke₂ hcl h hf⟩
    have h12 : ∀ f, f ∈ R₁ → f ∉ R₂ := fun f hf hg ↦ Finset.disjoint_left.mp hP.disjoint_rims hf hg
    -- classify the two edges
    have hclass : ∀ f, f ∈ Γ.Es → ∀ i, Γ.ends f i = v → f ∈ R₁ ∨ f ∈ R₂ ∨ f ∈ Γ.bd V₁ := by
      intro f hf i hi
      have hvV' : Γ.ends f i ∈ Γ.Vs := hcl f hf i
      rw [← hP.union, Finset.mem_union] at hvV'
      rcases hvV' with h | h
      · rcases hP.edge_at_V₁ hf h with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inr h')
      · rcases hP.edge_at_V₂ hcl hf h with h' | h'
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr h')
    rcases hclass f h₁m.1 i h₁m.2 with hf | hf | hf <;>
      rcases hclass g h₂m.1 j h₂m.2 with hg | hg | hg
    · rw [if_pos hf, if_pos hg] at heq
      exact rim R₁ c₁ V₁ hP.ham₁ hc₁ hf hg heq
    · exfalso
      have hv₁ : v ∈ V₁ := by rw [← h₁m.2]; exact (mem_edgesIn.mp (hP.ham₁.subset hf)).2 i
      have hv₂ : v ∈ V₂ := by rw [← h₂m.2]; exact (mem_edgesIn.mp (hP.ham₂.subset hg)).2 j
      exact Finset.disjoint_left.mp hP.disj hv₁ hv₂
    · exfalso
      rw [if_pos hf, if_neg (hspoke g hg).1, if_neg (hspoke g hg).2] at heq
      exact twoColor_ne_third _ heq
    · exfalso
      have hv₁ : v ∈ V₁ := by rw [← h₂m.2]; exact (mem_edgesIn.mp (hP.ham₁.subset hg)).2 j
      have hv₂ : v ∈ V₂ := by rw [← h₁m.2]; exact (mem_edgesIn.mp (hP.ham₂.subset hf)).2 i
      exact Finset.disjoint_left.mp hP.disj hv₁ hv₂
    · rw [if_neg (fun h ↦ h12 f h hf), if_pos hf, if_neg (fun h ↦ h12 g h hg), if_pos hg] at heq
      exact rim R₂ c₂ V₂ hP.ham₂ hc₂ hf hg heq
    · exfalso
      rw [if_neg (fun h ↦ h12 f h hf), if_pos hf, if_neg (hspoke g hg).1, if_neg (hspoke g hg).2] at heq
      exact twoColor_ne_third _ heq
    · exfalso
      rw [if_neg (hspoke f hf).1, if_neg (hspoke f hf).2, if_pos hg] at heq
      exact twoColor_ne_third _ heq.symm
    · exfalso
      rw [if_neg (hspoke f hf).1, if_neg (hspoke f hf).2, if_neg (fun h ↦ h12 g h hg), if_pos hg] at heq
      exact twoColor_ne_third _ heq.symm
    · have := hP.spoke_unique hvV hf hg h₁m.2 h₂m.2
      subst this
      rw [idx_eq_of_ends_eq_single (hloop f h₁m.1) (h₁m.2.trans h₂m.2.symm)]

/-- **Both rims cut ⟹ the pole is colourable.** -/
theorem IsPermGraph.pole_colourable_of_cut {Y : Finset ℕ} {e₁ : ℕ} (he₁ : e₁ ∈ R₁)
    (he₁Y : e₁ ∈ Γ.bd Y) {e₂ : ℕ} (he₂ : e₂ ∈ R₂) (he₂Y : e₂ ∈ Γ.bd Y) :
    (Γ.pole Y).Colourable := by
  have h3 : 2 ≤ V₁.card := by have := hP.three; omega
  have h3' : 2 ≤ V₂.card := by rw [hP.card_V₂ hcl]; exact h3
  obtain ⟨c₁, hc₁⟩ := exists_two_colouring_cut hP.ham₁ h3 he₁ he₁Y
  obtain ⟨c₂, hc₂⟩ := exists_two_colouring_cut hP.ham₂ h3' he₂ he₂Y
  exact hP.pole_colourable_of_two_colourings hcl c₁ c₂ hc₁ hc₂

/-- **The rims of a permutation snark are odd**: two even rims would be two-edge-colourable,
and the spokes could receive the third colour. -/
theorem IsPermGraph.odd (hnc : ¬ Γ.Colourable) : Odd V₁.card := by
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  have h3 : 2 ≤ V₁.card := by have := hP.three; omega
  have h3' : 2 ≤ V₂.card := by rw [hP.card_V₂ hcl]; exact h3
  have hodd' : Even V₂.card := by rw [hP.card_V₂ hcl]; exact hodd
  obtain ⟨c₁, hc₁⟩ := hP.ham₁.exists_two_colouring_even h3 hodd
  obtain ⟨c₂, hc₂⟩ := hP.ham₂.exists_two_colouring_even h3' hodd'
  obtain ⟨c, hc⟩ := hP.pole_colourable_of_two_colourings hcl (Y := Γ.Vs) c₁ c₂
    (fun f hf g hg hfg v _ i j hi hj ↦ hc₁ f (sidePart_subset hf) g (sidePart_subset hg) hfg v
      (by rw [← hi]; exact (mem_edgesIn.mp (hP.ham₁.subset (sidePart_subset hf))).2 i) i j hi hj)
    (fun f hf g hg hfg v _ i j hi hj ↦ hc₂ f (sidePart_subset hf) g (sidePart_subset hg) hfg v
      (by rw [← hi]; exact (mem_edgesIn.mp (hP.ham₂.subset (sidePart_subset hf))).2 i) i j hi hj)
  exact hnc ⟨c, hcl.isColouring_iff.mpr hc⟩

end FinGraph
end GraphPuzzles
