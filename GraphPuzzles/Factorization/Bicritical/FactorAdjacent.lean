import GraphPuzzles.Factorization.FactorRecap
import GraphPuzzles.Factorization.Bicritical.FactorHalfEdgeMap
import GraphPuzzles.Factorization.Bicritical.FactorGirth

/-!
# The pole of an adjacent pair

Removing two adjacent vertices `x`, `y` from a snark of girth at least five leaves a `4`-pole
whose colourings give the two edges at `x` the same colour (and likewise at `y`): the graph is
the cap of this pole (`recap_iso`), so the pole is isochromatic for the vertex couples.
(Chladný–Škoviera, Proposition 2.2, in the form needed here.)
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

variable {Γ : FinGraph} (hcl : Γ.IsClosed) (hcub : Γ.IsCubic) (hnc : ¬ Γ.Colourable)
  (hg5 : Γ.Girth5)
include hcl hcub hnc hg5

/-- **Adjacent pair.**  In any colouring of the pole avoiding adjacent `x`, `y`, the two edges
at `x` other than the link receive the same colour. -/
theorem adjacent_colour_eq {x y g : ℕ} (hxV : x ∈ Γ.Vs) (hyV : y ∈ Γ.Vs) (hxy : x ≠ y)
    (hg : g ∈ Γ.Es) (hgxy : Γ.Joins g x y) {d₁ d₂ : ℕ} (hd₁ : d₁ ∈ Γ.Es) (hd₂ : d₂ ∈ Γ.Es)
    (hne : d₁ ≠ d₂) (hd₁g : d₁ ≠ g) (hd₂g : d₂ ≠ g) {i₁ i₂ : Fin 2} (hi₁ : Γ.ends d₁ i₁ = x)
    (hi₂ : Γ.ends d₂ i₂ = x) {c : ℕ → Color} (hc : (Γ.pole (Γ.Vs \ {x, y})).IsColouring c) :
    c d₁ = c d₂ := by
  have hloop : ∀ e ∈ Γ.Es, Γ.ends e 0 ≠ Γ.ends e 1 := fun e he ↦ hg5.no_loop he (hcl e he 0)
  set Z := Γ.Vs \ {x, y} with hZdef
  have hxyV : ({x, y} : Finset ℕ) ⊆ Γ.Vs := by
    intro v hv
    rw [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> assumption
  -- the only edge inside `{x, y}` is the link
  have hin : Γ.edgesIn {x, y} = {g} := by
    ext e
    rw [Finset.mem_singleton, mem_edgesIn]
    constructor
    · rintro ⟨he, hends⟩
      by_contra heg
      have h0 := hends 0
      have h1 := hends 1
      rw [Finset.mem_insert, Finset.mem_singleton] at h0 h1
      have hj : Γ.Joins e x y := by
        rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
        · exact absurd (h0.trans h1.symm) (hloop e he)
        · exact Or.inl ⟨h0, h1⟩
        · exact Or.inr ⟨h0, h1⟩
        · exact absurd (h0.trans h1.symm) (hloop e he)
      exact hg5.no_two_cycle hg he (Ne.symm heg) hxy hgxy hj
    · rintro rfl
      refine ⟨hg, fun i ↦ ?_⟩
      rcases Joins.end_eq hgxy i with h | h <;> rw [h] <;> simp
  have hbd4 : (Γ.bd {x, y}).card = 4 := by
    have := three_mul_card_eq hcub hxyV
    rw [Finset.card_pair hxy, hin, Finset.card_singleton] at this
    omega
  have hbdZ : Γ.bd Z = Γ.bd {x, y} := bd_compl hcl _
  have hP : (Γ.pole Z).IsPole4 := pole_isPole4 hcub Finset.sdiff_subset (by rw [hbdZ]; exact hbd4)
  have hat : ∀ v ∈ ({x, y} : Finset ℕ), ∀ e ∈ Γ.Es, ∀ i, Γ.ends e i = v → e = g ∨ e ∈ Γ.bd Z := by
    intro v hv e he i hi
    rcases mem_edgesIn_or_bd he (hi ▸ hv) with h | h
    · rw [hin, Finset.mem_singleton] at h; exact Or.inl h
    · rw [hbdZ]; exact Or.inr h
  have hatx : ∀ e ∈ Γ.Es, ∀ i, Γ.ends e i = x → e = g ∨ e ∈ Γ.bd Z :=
    hat x (Finset.mem_insert_self _ _)
  have haty : ∀ e ∈ Γ.Es, ∀ i, Γ.ends e i = y → e = g ∨ e ∈ Γ.bd Z :=
    hat y (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hd₁Z : d₁ ∈ Γ.bd Z := (hatx d₁ hd₁ i₁ hi₁).resolve_left hd₁g
  have hd₂Z : d₂ ∈ Γ.bd Z := (hatx d₂ hd₂ i₂ hi₂).resolve_left hd₂g
  have hgZ : g ∉ Γ.bd Z := by
    rw [hbdZ]
    intro h
    exact Finset.disjoint_left.mp (disjoint_edgesIn_bd {x, y}) (by rw [hin]; exact Finset.mem_singleton_self g) h
  -- the pairing matching `d₁` with `d₂`
  obtain ⟨k₁, hk₁⟩ := exists_bdEmb_eq hP (by rw [dangling_pole]; exact hd₁Z)
  obtain ⟨k₂, hk₂⟩ := exists_bdEmb_eq hP (by rw [dangling_pole]; exact hd₂Z)
  have hk : k₁ ≠ k₂ := fun h ↦ hne (by rw [← hk₁, ← hk₂, h])
  obtain ⟨m, hm⟩ := exists_pairing_eq hk
  have hpd : partner hP m d₁ = d₂ := by rw [← hk₁, partner_bdEmb, hm, hk₂]
  have hXset : ∀ e ∈ Γ.bd Z, (∃ i, Γ.ends e i = x) ↔ (e = d₁ ∨ e = d₂) := by
    intro e he
    constructor
    · rintro ⟨i, hi⟩
      obtain ⟨x₃, hx₃, ⟨k, hk⟩, h31, h32, hall⟩ := third_edge hcub hloop hxV hd₁ hd₂ hne hi₁ hi₂
      obtain ⟨ig, hig⟩ := Joins.exists_end hgxy
      have hg3 : g = x₃ := by
        rcases hall g hg ig hig with h | h | h
        · exact absurd h.symm hd₁g
        · exact absurd h.symm hd₂g
        · exact h
      rcases hall e (bd_subset _ he) i hi with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd he (h ▸ hg3 ▸ hgZ)
    · rintro (rfl | rfl)
      · exact ⟨i₁, hi₁⟩
      · exact ⟨i₂, hi₂⟩
  have hV : Γ.Vs = insert x (insert y Z) := by
    ext v
    simp only [Finset.mem_insert, hZdef, Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · intro hv
      by_cases hvx : v = x
      · exact Or.inl hvx
      · by_cases hvy : v = y
        · exact Or.inr (Or.inl hvy)
        · exact Or.inr (Or.inr ⟨hv, by tauto⟩)
    · rintro (rfl | rfl | ⟨hv, -⟩)
      · exact hxV
      · exact hyV
      · exact hv
  have hxZ : x ∉ Z := by simp [hZdef]
  have hyZ : y ∉ Z := by simp [hZdef]
  obtain ⟨f⟩ := recap_iso hcl hxy hxZ hyZ hV hg hgxy hP m hatx haty hd₁Z hpd hXset
  have hcapnc : ¬ (cap hP m).Colourable := fun h ↦ hnc (f.symm.colourable h)
  have hiso := isoWith_of_cap_not_colourable hP m hcapnc
  have := hiso (tvec hP c) ⟨c, hc, rfl⟩ k₁
  simp only [tvec] at this
  rw [hk₁, hm, hk₂] at this
  exact this

end FinGraph
end GraphPuzzles
