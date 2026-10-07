import GraphPuzzles.Factorization.Bicritical.FactorGirth
import GraphPuzzles.Factorization.Bicritical.FactorHalfEdgeMap

/-!
# Local structure at the edges of an independent cut

In a cubic graph without loops every vertex carries three distinct edges.  At a vertex `x`
incident with exactly one edge `d` of a cut `bd Y`, the boundary of `Y.erase x` is obtained by
replacing `d` with the two other edges at `x`.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

variable {Γ : FinGraph}

theorem idx_eq_of_ends_eq (hloop : ∀ e ∈ Γ.Es, Γ.ends e 0 ≠ Γ.ends e 1) {e : ℕ} (he : e ∈ Γ.Es)
    {i j : Fin 2} (h : Γ.ends e i = Γ.ends e j) : i = j := by
  by_contra hij
  have hi : i = 0 ∨ i = 1 := by omega
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact hij rfl
  · exact hloop e he h
  · exact hloop e he h.symm
  · exact hij rfl

/-- The two other edges at a vertex of a cubic graph without loops. -/
theorem exists_two_others (hcub : Γ.IsCubic) (hloop : ∀ e ∈ Γ.Es, Γ.ends e 0 ≠ Γ.ends e 1)
    {v : ℕ} (hv : v ∈ Γ.Vs) {d : ℕ} (hd : d ∈ Γ.Es) {j : Fin 2} (hj : Γ.ends d j = v) :
    ∃ g₁ g₂, g₁ ∈ Γ.Es ∧ g₂ ∈ Γ.Es ∧ g₁ ≠ g₂ ∧ g₁ ≠ d ∧ g₂ ≠ d ∧ (∃ i, Γ.ends g₁ i = v) ∧
      (∃ i, Γ.ends g₂ i = v) ∧ ∀ y ∈ Γ.Es, ∀ j', Γ.ends y j' = v → y = d ∨ y = g₁ ∨ y = g₂ := by
  have hcard : (Γ.halfEdgesIn Γ.Es v).card = 3 := hcub v hv
  obtain ⟨⟨e, i⟩, hm, hne⟩ := Finset.exists_mem_ne (by omega : 1 < (Γ.halfEdgesIn Γ.Es v).card) (d, j)
  rw [mem_halfEdgesIn] at hm
  have hed : e ≠ d := by
    rintro rfl
    exact hne (Prod.ext rfl (idx_eq_of_ends_eq hloop hd (hm.2.trans hj.symm)))
  obtain ⟨x, hx, ⟨k, hk⟩, hxd, hxe, hall⟩ := third_edge hcub hloop hv hd hm.1 hed.symm hj hm.2
  refine ⟨e, x, hm.1, hx, hxe.symm, hed, hxd, ⟨i, hm.2⟩, ⟨k, hk⟩, ?_⟩
  intro y hy j' hj'
  rcases hall y hy j' hj' with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

section Independent

variable (hcl : Γ.IsClosed) (hcub : Γ.IsCubic) (hloop : ∀ e ∈ Γ.Es, Γ.ends e 0 ≠ Γ.ends e 1)
  {Y : Finset ℕ} (hY : Y ⊆ Γ.Vs) (hind : Γ.IsIndependentCut Y)

include hind in
/-- Two cut edges at a common vertex coincide. -/
theorem IsIndependentCut.eq_of_ends {d d' : ℕ} (hd : d ∈ Γ.bd Y) (hd' : d' ∈ Γ.bd Y) {i j : Fin 2}
    (hi : Γ.ends d i = Γ.ends d' j) : d = d' := by
  by_contra hne
  have := degIn_bd_le_of_two_edges hd hd' hne hi rfl
  have := hind (Γ.ends d' j)
  omega

include hind in
/-- An edge at the vertex of a cut edge, other than the cut edge, lies inside the shore. -/
theorem IsIndependentCut.mem_edgesIn {d e : ℕ} (hd : d ∈ Γ.bd Y) (he : e ∈ Γ.Es) (hed : e ≠ d)
    {i j : Fin 2} (hi : Γ.ends e i = Γ.ends d j) (hv : Γ.ends d j ∈ Y) : e ∈ Γ.edgesIn Y := by
  rcases mem_edgesIn_or_bd he (hi ▸ hv) with h | h
  · exact h
  · exact absurd (hind.eq_of_ends h hd hi) hed

include hcl hind in
theorem IsIndependentCut.compl : Γ.IsIndependentCut (Γ.Vs \ Y) := by
  intro v
  rw [bd_compl hcl]
  exact hind v

include hcl hcub hloop hY hind in
omit hcl in
/-- **The boundary after removing the vertex of a cut edge.** -/
theorem bd_erase_of_cut {d : ℕ} (hd : d ∈ Γ.bd Y) {j : Fin 2} (hx : Γ.ends d j ∈ Y) :
    ∃ g₁ g₂, g₁ ∈ Γ.edgesIn Y ∧ g₂ ∈ Γ.edgesIn Y ∧ g₁ ≠ g₂ ∧ g₁ ≠ d ∧ g₂ ≠ d ∧
      (∃ i, Γ.ends g₁ i = Γ.ends d j) ∧ (∃ i, Γ.ends g₂ i = Γ.ends d j) ∧
      Γ.bd (Y.erase (Γ.ends d j)) = insert g₁ (insert g₂ ((Γ.bd Y).erase d)) := by
  set x := Γ.ends d j with hxdef
  obtain ⟨g₁, g₂, hg₁, hg₂, h12, h1d, h2d, ⟨i₁, hi₁⟩, ⟨i₂, hi₂⟩, hall⟩ :=
    exists_two_others hcub hloop (hY hx) (bd_subset Y hd) (j := j) rfl
  have hg₁Y : g₁ ∈ Γ.edgesIn Y := hind.mem_edgesIn hd hg₁ h1d hi₁ hx
  have hg₂Y : g₂ ∈ Γ.edgesIn Y := hind.mem_edgesIn hd hg₂ h2d hi₂ hx
  refine ⟨g₁, g₂, hg₁Y, hg₂Y, h12, h1d, h2d, ⟨i₁, hi₁⟩, ⟨i₂, hi₂⟩, ?_⟩
  have hg₁bd : g₁ ∉ Γ.bd Y := fun h ↦ Finset.disjoint_left.mp (disjoint_edgesIn_bd Y) hg₁Y h
  have hg₂bd : g₂ ∉ Γ.bd Y := fun h ↦ Finset.disjoint_left.mp (disjoint_edgesIn_bd Y) hg₂Y h
  -- an edge inside `Y` at `x` is on the boundary of `Y.erase x`
  have hin : ∀ g ∈ Γ.edgesIn Y, ∀ i, Γ.ends g i = x → g ∈ Γ.bd (Y.erase x) := by
    intro g hg i hi
    rw [mem_edgesIn] at hg
    rw [mem_bd]
    refine ⟨hg.1, ?_⟩
    have hrev : Γ.ends g (Fin.rev i) ≠ x := by
      intro h
      have := idx_eq_of_ends_eq hloop hg.1 (h.trans hi.symm)
      have hi0 : i = 0 ∨ i = 1 := by omega
      rcases hi0 with rfl | rfl <;> simp at this
    have hi0 : i = 0 ∨ i = 1 := by omega
    rcases hi0 with rfl | rfl
    · rw [Iso.rev_zero'] at hrev
      intro h
      have := h.mpr (Finset.mem_erase.mpr ⟨hrev, hg.2 1⟩)
      exact (Finset.mem_erase.mp this).1 hi
    · rw [Iso.rev_one'] at hrev
      intro h
      have := h.mp (Finset.mem_erase.mpr ⟨hrev, hg.2 0⟩)
      exact (Finset.mem_erase.mp this).1 hi
  -- an edge with no end at `x` is on the boundary of `Y.erase x` iff on the boundary of `Y`
  have hno : ∀ e, (∀ i, Γ.ends e i ≠ x) → (e ∈ Γ.bd (Y.erase x) ↔ e ∈ Γ.bd Y) := by
    intro e he
    rw [mem_bd, mem_bd]
    have h0 : Γ.ends e 0 ∈ Y.erase x ↔ Γ.ends e 0 ∈ Y := by
      rw [Finset.mem_erase]; exact ⟨fun h ↦ h.2, fun h ↦ ⟨he 0, h⟩⟩
    have h1 : Γ.ends e 1 ∈ Y.erase x ↔ Γ.ends e 1 ∈ Y := by
      rw [Finset.mem_erase]; exact ⟨fun h ↦ h.2, fun h ↦ ⟨he 1, h⟩⟩
    rw [h0, h1]
  ext e
  simp only [Finset.mem_insert, Finset.mem_erase]
  constructor
  · intro he
    have heE : e ∈ Γ.Es := bd_subset _ he
    by_cases hx' : ∃ i, Γ.ends e i = x
    · obtain ⟨i, hi⟩ := hx'
      rcases hall e heE i hi with rfl | rfl | rfl
      · -- the cut edge is not on the new boundary
        exfalso
        rw [mem_bd] at he
        obtain ⟨k, hk, hk'⟩ := bd_side hd
        have hkj : k = j := by
          by_contra hkj
          have hk2 : Fin.rev k = j := by rw [fin2_eq_rev_of_ne hkj, Fin.rev_rev]
          rw [hk2] at hk'
          exact hk' hx
        subst hkj
        have hnot : ∀ l, Γ.ends e l ∉ Y.erase x := by
          intro l hl
          rw [Finset.mem_erase] at hl
          by_cases hlk : l = k
          · exact hl.1 (by rw [hlk])
          · rw [fin2_eq_rev_of_ne hlk] at hl
            exact hk' hl.2
        exact he.2 ⟨fun h ↦ absurd h (hnot 0), fun h ↦ absurd h (hnot 1)⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · push Not at hx'
      right; right
      have := (hno e hx').mp he
      refine ⟨?_, this⟩
      rintro rfl
      exact hx' j rfl
  · rintro (rfl | rfl | ⟨hed, he⟩)
    · exact hin _ hg₁Y i₁ hi₁
    · exact hin _ hg₂Y i₂ hi₂
    · have hx' : ∀ i, Γ.ends e i ≠ x := by
        intro i hi
        rcases hall e (bd_subset _ he) i hi with h | h | h
        · exact hed h
        · exact hg₁bd (h ▸ he)
        · exact hg₂bd (h ▸ he)
      exact (hno e hx').mpr he

end Independent

end FinGraph
end GraphPuzzles
