import GraphPuzzles.Factorization.Permutation.FactorPermCut

/-!
# Rim segments of a cycle-separating `4`-cut

For a cycle-separating `4`-cut `Y` of a permutation snark: the two sides of `Y` meet the rims in
segments (paths), the spokes inside `Y` match `Y ∩ V₁` with `Y ∩ V₂`, and a proper
two-edge-colouring of each rim's side part yields a colouring of the pole.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

variable {Γ : FinGraph} {V₁ V₂ R₁ R₂ : Finset ℕ} (hP : Γ.IsPermGraph V₁ V₂ R₁ R₂)
  (hcl : Γ.IsClosed) (hcub : Γ.IsCubic) (hnc : ¬ Γ.Colourable)
include hP hcl

section Colouring

omit hcub hnc in
/-- **Combining rim colourings.**  Proper two-edge-colourings of the side parts of both rims at
the vertices of `Y` yield a colouring of the pole at `Y`. -/
theorem IsPermGraph.isColouring_of_rims {Y : Finset ℕ} {c₁ c₂ : ℕ → Fin 2}
    (hc₁ : ∀ f ∈ Γ.sidePart R₁ Y, ∀ g ∈ Γ.sidePart R₁ Y, f ≠ g →
      ∀ v ∈ Y, ∀ i j, Γ.ends f i = v → Γ.ends g j = v → c₁ f ≠ c₁ g)
    (hc₂ : ∀ f ∈ Γ.sidePart R₂ Y, ∀ g ∈ Γ.sidePart R₂ Y, f ≠ g →
      ∀ v ∈ Y, ∀ i j, Γ.ends f i = v → Γ.ends g j = v → c₂ f ≠ c₂ g) :
    (Γ.pole Y).IsColouring
      (fun e ↦ if e ∈ R₁ then twoColor (c₁ e) else if e ∈ R₂ then twoColor (c₂ e) else (1, 1)) := by
  classical
  have hloop := hP.no_loop hcl
  refine ⟨?_, ?_⟩
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

end Colouring

section Segment

include hcub hnc

variable {Y : Finset ℕ} (hY : Γ.CycSep Y)
include hY

/-- No spoke crosses a cycle-separating `4`-cut. -/
theorem IsPermGraph.spoke_notMem_bd {s : ℕ} (hs : s ∈ Γ.bd V₁) : s ∉ Γ.bd Y := by
  intro h
  have := (hP.cycSep_structure hcl hcub hnc hY).2.2
  exact Finset.notMem_empty s (this ▸ Finset.mem_inter.mpr ⟨h, hs⟩)

/-- The spoke of a vertex of `Y` lies inside `Y`. -/
theorem IsPermGraph.spoke_mem_edgesIn {s v : ℕ} (hs : s ∈ Γ.bd V₁) {i : Fin 2}
    (hi : Γ.ends s i = v) (hv : v ∈ Y) : s ∈ Γ.edgesIn Y := by
  rcases mem_edgesIn_or_bd (bd_subset _ hs) (hi ▸ hv) with h | h
  · exact h
  · exact absurd h (hP.spoke_notMem_bd hcl hcub hnc hY hs)

omit hnc hcub hY in
theorem IsPermGraph.endsIn_inter_of_spoke {Y : Finset ℕ} {e : ℕ} (he : e ∈ Γ.bd V₁)
    (heY : e ∈ Γ.edgesIn Y) : Γ.endsIn (Y ∩ V₁) e = 1 ∧ Γ.endsIn (Y ∩ V₂) e = 1 := by
  have h0 := (mem_edgesIn.mp heY).2 0
  have h1 := (mem_edgesIn.mp heY).2 1
  rw [mem_bd] at he
  have heE := he.1
  have hV : ∀ i, Γ.ends e i ∈ V₁ ∨ Γ.ends e i ∈ V₂ := by
    intro i
    have := hcl e heE i
    rw [← hP.union, Finset.mem_union] at this
    exact this
  have hd : ∀ i, Γ.ends e i ∈ V₁ → Γ.ends e i ∉ V₂ := fun i h h' ↦
    Finset.disjoint_left.mp hP.disj h h'
  rw [endsIn_eq, endsIn_eq]
  simp only [Finset.mem_inter]
  by_cases ha : Γ.ends e 0 ∈ V₁
  · have hb : Γ.ends e 1 ∉ V₁ := fun hb ↦ he.2 ⟨fun _ ↦ hb, fun _ ↦ ha⟩
    have hb₂ : Γ.ends e 1 ∈ V₂ := (hV 1).resolve_left hb
    rw [if_pos ⟨h0, ha⟩, if_neg (fun h ↦ hb h.2), if_neg (fun h ↦ hd 0 ha h.2), if_pos ⟨h1, hb₂⟩]
    exact ⟨rfl, rfl⟩
  · have hb : Γ.ends e 1 ∈ V₁ := by
      by_contra hb
      exact he.2 ⟨fun h ↦ absurd h ha, fun h ↦ absurd h hb⟩
    have ha₂ : Γ.ends e 0 ∈ V₂ := (hV 0).resolve_left ha
    rw [if_neg (fun h ↦ ha h.2), if_pos ⟨h1, hb⟩, if_pos ⟨h0, ha₂⟩, if_neg (fun h ↦ hd 1 hb h.2)]
    exact ⟨rfl, rfl⟩

/-- **The two rim segments of a shore have the same number of vertices.** -/
theorem IsPermGraph.card_inter_eq : (Y ∩ V₁).card = (Y ∩ V₂).card := by
  classical
  set S := Γ.bd V₁ ∩ Γ.edgesIn Y with hSdef
  -- every vertex of `Y` has exactly one spoke, and it lies inside `Y`
  have hdeg : ∀ v ∈ Y, Γ.degIn S v = 1 := by
    intro v hv
    rw [degIn_eq_card]
    have : Γ.halfEdgesIn S v = Γ.halfEdgesIn (Γ.bd V₁) v := by
      ext ⟨e, i⟩
      rw [mem_halfEdgesIn, mem_halfEdgesIn, hSdef, Finset.mem_inter]
      constructor
      · rintro ⟨⟨he, -⟩, hi⟩; exact ⟨he, hi⟩
      · rintro ⟨he, hi⟩
        exact ⟨⟨he, hP.spoke_mem_edgesIn hcl hcub hnc hY he hi hv⟩, hi⟩
    rw [this, ← degIn_eq_card]
    exact hP.spoke v (hY.1 hv)
  have h1 := sum_degIn_eq (Γ := Γ) S (Y ∩ V₁)
  have h2 := sum_degIn_eq (Γ := Γ) S (Y ∩ V₂)
  rw [Finset.sum_congr rfl (fun v hv ↦ hdeg v (Finset.mem_inter.mp hv).1), Finset.sum_const,
    smul_eq_mul, mul_one,
    Finset.sum_congr rfl (fun e he ↦ (hP.endsIn_inter_of_spoke hcl (Finset.mem_inter.mp he).1
      (Finset.mem_inter.mp he).2).1), Finset.sum_const, smul_eq_mul, mul_one] at h1
  rw [Finset.sum_congr rfl (fun v hv ↦ hdeg v (Finset.mem_inter.mp hv).1), Finset.sum_const,
    smul_eq_mul, mul_one,
    Finset.sum_congr rfl (fun e he ↦ (hP.endsIn_inter_of_spoke hcl (Finset.mem_inter.mp he).1
      (Finset.mem_inter.mp he).2).2), Finset.sum_const, smul_eq_mul, mul_one] at h2
  rw [h1, h2]

end Segment

end FinGraph
end GraphPuzzles
