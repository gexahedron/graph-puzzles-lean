import GraphPuzzles.Factorization.FactorJoinCap

/-!
# Girth `5` from the absence of short cycles

A cubic graph without loops, parallel edges, triangles and quadrilaterals has no nonempty even
edge set of fewer than five edges.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

variable {Γ : FinGraph}

theorem joins_of_end {e v : ℕ} {i : Fin 2} (hi : Γ.ends e i = v) :
    Γ.Joins e v (Γ.ends e (Fin.rev i)) := by
  have h : i = 0 ∨ i = 1 := by omega
  rcases h with rfl | rfl
  · rw [Iso.rev_zero']; exact Or.inl ⟨hi, rfl⟩
  · rw [Iso.rev_one']; exact Or.inr ⟨rfl, hi⟩

/-- In an even edge set, an edge at `v` has a companion at `v`. -/
theorem exists_companion {F : Finset ℕ} (hev : Γ.IsEven F) {v : ℕ} (hv : v ∈ Γ.Vs) {e : ℕ}
    {i : Fin 2} (he : e ∈ F) (hi : Γ.ends e i = v) :
    ∃ h ∈ Γ.halfEdgesIn F v, h ≠ (e, i) := by
  have hmem : (e, i) ∈ Γ.halfEdgesIn F v := mem_halfEdgesIn.mpr ⟨he, hi⟩
  have hpos : 0 < Γ.degIn F v := Finset.card_pos.mpr ⟨_, hmem⟩
  have hev' := hev v hv
  have h2 : 1 < Γ.degIn F v := by
    obtain ⟨k, hk⟩ := hev'
    unfold degIn at hpos hk ⊢
    omega
  exact Finset.exists_mem_ne h2 (e, i)

/-- **Girth `5` from the absence of short cycles.** -/
theorem girth5_of_no_short_cycles (hcl : Γ.IsClosed)
    (hloop : ∀ e ∈ Γ.Es, Γ.ends e 0 ≠ Γ.ends e 1)
    (hpar : ∀ e ∈ Γ.Es, ∀ e' ∈ Γ.Es, e ≠ e' → ∀ a b, a ≠ b → Γ.Joins e a b → Γ.Joins e' a b → False)
    (htri : ∀ e₁ ∈ Γ.Es, ∀ e₂ ∈ Γ.Es, ∀ e₃ ∈ Γ.Es, e₁ ≠ e₂ → e₁ ≠ e₃ → e₂ ≠ e₃ →
      ∀ a b c, a ≠ b → b ≠ c → a ≠ c → Γ.Joins e₁ a b → Γ.Joins e₂ b c → Γ.Joins e₃ c a → False)
    (hquad : ∀ e₁ ∈ Γ.Es, ∀ e₂ ∈ Γ.Es, ∀ e₃ ∈ Γ.Es, ∀ e₄ ∈ Γ.Es,
      e₁ ≠ e₂ → e₁ ≠ e₃ → e₁ ≠ e₄ → e₂ ≠ e₃ → e₂ ≠ e₄ → e₃ ≠ e₄ →
      ∀ a b c d, a ≠ b → b ≠ c → c ≠ d → a ≠ d → a ≠ c → b ≠ d →
      Γ.Joins e₁ a b → Γ.Joins e₂ b c → Γ.Joins e₃ c d → Γ.Joins e₄ d a → False) :
    Γ.Girth5 := by
  intro F hF hne hev
  by_contra hlt
  push Not at hlt
  obtain ⟨e₁, he₁⟩ := hne
  have he₁E := hF he₁
  set a := Γ.ends e₁ 0 with ha
  set b := Γ.ends e₁ 1 with hb
  have hab : a ≠ b := hloop e₁ he₁E
  have haV : a ∈ Γ.Vs := hcl e₁ he₁E 0
  have hbV : b ∈ Γ.Vs := hcl e₁ he₁E 1
  have j₁ : Γ.Joins e₁ a b := Or.inl ⟨rfl, rfl⟩
  -- the ends of an edge at a vertex, with its other end
  have other : ∀ (e : ℕ) (i : Fin 2) (v : ℕ), e ∈ F → Γ.ends e i = v →
      e ∈ Γ.Es ∧ Γ.Joins e v (Γ.ends e (Fin.rev i)) ∧ Γ.ends e (Fin.rev i) ≠ v ∧
        Γ.ends e (Fin.rev i) ∈ Γ.Vs := by
    intro e i v he hi
    have heE := hF he
    refine ⟨heE, joins_of_end hi, ?_, hcl e heE _⟩
    have hi0 : i = 0 ∨ i = 1 := by omega
    rcases hi0 with rfl | rfl
    · rw [Iso.rev_zero']; rw [← hi]; exact (hloop e heE).symm
    · rw [Iso.rev_one']; rw [← hi]; exact hloop e heE
  -- the companion of `e₁` at `a`
  obtain ⟨⟨e₂, i₂⟩, h₂m, h₂ne⟩ := exists_companion hev haV he₁ (i := 0) rfl
  rw [mem_halfEdgesIn] at h₂m
  have he₂ : e₂ ∈ F := h₂m.1
  have hi₂ : Γ.ends e₂ i₂ = a := h₂m.2
  have h₂₁ : e₂ ≠ e₁ := by
    intro h
    subst h
    apply h₂ne
    have hi : i₂ = 0 ∨ i₂ = 1 := by omega
    rcases hi with rfl | rfl
    · rfl
    · exact absurd hi₂ (hloop e₂ he₁E).symm
  obtain ⟨he₂E, j₂, hca, hcV⟩ := other e₂ i₂ a he₂ hi₂
  set c := Γ.ends e₂ (Fin.rev i₂) with hc
  have hcb : c ≠ b := by
    intro h
    rw [h] at j₂
    exact hpar e₁ he₁E e₂ he₂E h₂₁.symm a b hab j₁ j₂
  -- the companion of `e₁` at `b`
  obtain ⟨⟨e₃, i₃⟩, h₃m, h₃ne⟩ := exists_companion hev hbV he₁ (i := 1) rfl
  rw [mem_halfEdgesIn] at h₃m
  have he₃ : e₃ ∈ F := h₃m.1
  have hi₃ : Γ.ends e₃ i₃ = b := h₃m.2
  have h₃₁ : e₃ ≠ e₁ := by
    intro h
    subst h
    apply h₃ne
    have hi : i₃ = 0 ∨ i₃ = 1 := by omega
    rcases hi with rfl | rfl
    · exact absurd hi₃ (hloop e₃ he₁E)
    · rfl
  obtain ⟨he₃E, j₃, hdb, hdV⟩ := other e₃ i₃ b he₃ hi₃
  set d := Γ.ends e₃ (Fin.rev i₃) with hd
  have h₃₂ : e₃ ≠ e₂ := by
    intro h
    -- `e₂` joins `a` and `c`; it is at `b`, so `b ∈ {a, c}`
    rw [h] at hi₃
    rcases (Joins.end_eq (joins_of_end hi₂) i₃) with h' | h'
    · exact hab (h'.symm.trans hi₃)
    · exact hcb (h'.symm.trans hi₃)
  have hda : d ≠ a := by
    intro h
    rw [h] at j₃
    exact hpar e₁ he₁E e₃ he₃E h₃₁.symm a b hab j₁ j₃.symm
  by_cases hdc : d = c
  · -- a triangle
    rw [hdc] at j₃
    exact htri e₁ he₁E e₃ he₃E e₂ he₂E h₃₁.symm h₂₁.symm h₃₂ a b c hab hcb.symm hca.symm
      j₁ j₃ (Joins.symm j₂)
  -- the companion of `e₂` at `c`
  obtain ⟨⟨e₄, i₄⟩, h₄m, h₄ne⟩ := exists_companion hev hcV he₂ (i := Fin.rev i₂) rfl
  rw [mem_halfEdgesIn] at h₄m
  have he₄ : e₄ ∈ F := h₄m.1
  have hi₄ : Γ.ends e₄ i₄ = c := h₄m.2
  have h₄₂ : e₄ ≠ e₂ := by
    intro h
    subst h
    apply h₄ne
    have hi : i₄ = 0 ∨ i₄ = 1 := by omega
    have hi' : i₂ = 0 ∨ i₂ = 1 := by omega
    rcases hi with rfl | rfl <;> rcases hi' with h' | h' <;> rw [h'] at hi₂ hc ⊢
    · rw [Iso.rev_zero'] at hc; exact absurd (hi₄.trans hc) (hloop e₄ he₂E)
    · rw [Iso.rev_one']
    · rw [Iso.rev_zero']
    · rw [Iso.rev_one'] at hc; exact absurd (hc.symm.trans hi₄.symm) (hloop e₄ he₂E)
  have h₄₁ : e₄ ≠ e₁ := by
    intro h
    rw [h] at hi₄
    rcases Joins.end_eq j₁ i₄ with h' | h'
    · exact hca (hi₄.symm.trans h')
    · exact hcb (hi₄.symm.trans h')
  have h₄₃ : e₄ ≠ e₃ := by
    intro h
    rw [h] at hi₄
    rcases Joins.end_eq j₃ i₄ with h' | h'
    · exact hcb (hi₄.symm.trans h')
    · exact hdc (h'.symm.trans hi₄)
  obtain ⟨he₄E, j₄, hcx, hxV⟩ := other e₄ i₄ c he₄ hi₄
  -- `F` has at least the four edges `e₁ e₂ e₃ e₄`, hence exactly these
  have hsub : ({e₁, e₂, e₃, e₄} : Finset ℕ) ⊆ F := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hcard4 : ({e₁, e₂, e₃, e₄} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [h₂₁.symm, h₃₁.symm, h₄₁.symm]),
      Finset.card_insert_of_notMem (by simp [h₃₂.symm, h₄₂.symm]), Finset.card_pair h₄₃.symm]
  have hFeq : F = {e₁, e₂, e₃, e₄} := by
    symm
    apply Finset.eq_of_subset_of_card_le hsub
    rw [hcard4]; omega
  -- the companion of `e₃` at `d` must be `e₄`
  obtain ⟨⟨e₅, i₅⟩, h₅m, h₅ne⟩ := exists_companion hev hdV he₃ (i := Fin.rev i₃) rfl
  rw [mem_halfEdgesIn] at h₅m
  have he₅ : e₅ ∈ F := h₅m.1
  have hi₅ : Γ.ends e₅ i₅ = d := h₅m.2
  rw [hFeq] at he₅
  simp only [Finset.mem_insert, Finset.mem_singleton] at he₅
  rcases he₅ with rfl | rfl | rfl | rfl
  · rcases Joins.end_eq j₁ i₅ with h' | h'
    · exact hda (hi₅.symm.trans h')
    · exact hdb (hi₅.symm.trans h')
  · rcases Joins.end_eq j₂ i₅ with h' | h'
    · exact hda (hi₅.symm.trans h')
    · exact hdc (hi₅.symm.trans h')
  · exfalso
    apply h₅ne
    have hi : i₅ = 0 ∨ i₅ = 1 := by omega
    have hi' : i₃ = 0 ∨ i₃ = 1 := by omega
    rcases hi with rfl | rfl <;> rcases hi' with h' | h' <;> rw [h'] at hi₃ hd ⊢
    · rw [Iso.rev_zero'] at hd; exact absurd (hi₅.trans hd) (hloop e₅ he₃E)
    · rw [Iso.rev_one']
    · rw [Iso.rev_zero']
    · rw [Iso.rev_one'] at hd; exact absurd (hd.symm.trans hi₅.symm) (hloop e₅ he₃E)
  · -- `e₄` is at `d`: its other end is `d`, giving the quadrilateral `a b d c`
    have hx : Γ.ends e₅ (Fin.rev i₄) = d := by
      rcases Joins.end_eq j₄ i₅ with h' | h'
      · exact absurd (hi₅.symm.trans h') hdc
      · have : i₅ ≠ i₄ := by
          intro h
          rw [h] at hi₅
          exact hdc (hi₅.symm.trans hi₄)
        have h1 : i₅ = 0 ∨ i₅ = 1 := by omega
        have h2 : i₄ = 0 ∨ i₄ = 1 := by omega
        rcases h1 with rfl | rfl <;> rcases h2 with h2 | h2 <;> rw [h2] at this hi₄ ⊢
        · exact absurd rfl this
        · rw [Iso.rev_one']; exact hi₅
        · rw [Iso.rev_zero']; exact hi₅
        · exact absurd rfl this
    have j₄' : Γ.Joins e₅ c d := by
      rw [← hx]; exact j₄
    exact hquad e₁ he₁E e₃ he₃E e₅ he₄E e₂ he₂E h₃₁.symm h₄₁.symm h₂₁.symm h₄₃.symm h₃₂ h₄₂
      a b d c hab hdb.symm hdc hca.symm hda.symm hcb.symm j₁ j₃ (Joins.symm j₄') (Joins.symm j₂)

end FinGraph
end GraphPuzzles
