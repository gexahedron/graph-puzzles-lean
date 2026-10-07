import GraphPuzzles.Factorization.FactorRecap
import GraphPuzzles.Factorization.Diamond.FactorDblJJ
import GraphPuzzles.Factorization.Diamond.FactorDiamond

/-!
# The structure of a quasiatomic shore

A quasiatomic shore `Y ⊇ A` consists of `A` and two adjacent vertices `v₁, v₂`.  We extract the
edge `f = v₁v₂`, the edges `a₁, a₂` from `A` to `v₁, v₂`, and the edges `l₁, l₂` leaving `Y`
at `v₁, v₂`, together with their basic properties.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

/-- The data of a quasiatomic shore. -/
structure QuasiData (Δ : FinGraph) (A Y : Finset ℕ) where
  v₁ : ℕ
  v₂ : ℕ
  f : ℕ
  a₁ : ℕ
  a₂ : ℕ
  l₁ : ℕ
  l₂ : ℕ
  hv : v₁ ≠ v₂
  hv₁A : v₁ ∉ A
  hv₂A : v₂ ∉ A
  hY : Y = insert v₁ (insert v₂ A)
  hf : f ∈ Δ.Es
  hfj : Δ.Joins f v₁ v₂
  ha₁ : a₁ ∈ Δ.bd A
  ha₂ : a₂ ∈ Δ.bd A
  ha₁v : ∃ i, Δ.ends a₁ i = v₁
  ha₂v : ∃ i, Δ.ends a₂ i = v₂
  hl₁ : l₁ ∈ Δ.bd Y
  hl₂ : l₂ ∈ Δ.bd Y
  hl₁v : ∃ i, Δ.ends l₁ i = v₁
  hl₂v : ∃ i, Δ.ends l₂ i = v₂
  /-- the edges at `v₁` -/
  hat₁ : ∀ e ∈ Δ.Es, ∀ i, Δ.ends e i = v₁ → e = f ∨ e = a₁ ∨ e = l₁
  hat₂ : ∀ e ∈ Δ.Es, ∀ i, Δ.ends e i = v₂ → e = f ∨ e = a₂ ∨ e = l₂
  hfa₁ : f ≠ a₁
  hfl₁ : f ≠ l₁
  hal₁ : a₁ ≠ l₁
  hfa₂ : f ≠ a₂
  hfl₂ : f ≠ l₂
  hal₂ : a₂ ≠ l₂

section Extract

variable {Δ : FinGraph} (hcl : Δ.IsClosed) (hcub : Δ.IsCubic) (hg : Δ.Girth5)
  {A Y : Finset ℕ} (hA : Δ.CycSep A) (hY : Δ.CycSep Y) (hAY : A ⊆ Y) (hq : Δ.IsQuasiatomic A Y)
include hcl hcub hg hA hY hAY hq

omit hcl hcub hg hA hY hAY hq in
/-- The unique edge of a one-element `between` set. -/
theorem exists_between_eq {X Z : Finset ℕ} (h : (Δ.between X Z).card = 1) :
    ∃ e, Δ.between X Z = {e} := Finset.card_eq_one.mp h

omit hA in
/-- **Extraction of the quasiatomic data.** -/
theorem quasiData : Nonempty (QuasiData Δ A Y) := by
  obtain ⟨-, v₁, v₂, hv, hK, h12, hA1, hA2⟩ := hq
  have hYV := hY.1
  have hv₁ : v₁ ∈ Y \ A := by rw [hK]; exact Finset.mem_insert_self _ _
  have hv₂ : v₂ ∈ Y \ A := by rw [hK]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hv₁Y := (Finset.mem_sdiff.mp hv₁).1
  have hv₂Y := (Finset.mem_sdiff.mp hv₂).1
  have hv₁A := (Finset.mem_sdiff.mp hv₁).2
  have hv₂A := (Finset.mem_sdiff.mp hv₂).2
  have hv₁V := hYV hv₁Y
  have hv₂V := hYV hv₂Y
  have hYeq : Y = insert v₁ (insert v₂ A) := by
    ext v
    simp only [Finset.mem_insert]
    constructor
    · intro hv'
      by_cases h : v ∈ A
      · exact Or.inr (Or.inr h)
      · have : v ∈ Y \ A := Finset.mem_sdiff.mpr ⟨hv', h⟩
        rw [hK, Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
    · rintro (rfl | rfl | h)
      · exact hv₁Y
      · exact hv₂Y
      · exact hAY h
  -- the three special edges
  obtain ⟨f, hf⟩ := Finset.card_eq_one.mp h12
  obtain ⟨a₁, ha₁⟩ := Finset.card_eq_one.mp hA1
  obtain ⟨a₂, ha₂⟩ := Finset.card_eq_one.mp hA2
  have hfm : f ∈ Δ.between {v₁} {v₂} := by rw [hf]; exact Finset.mem_singleton_self _
  have ha₁m : a₁ ∈ Δ.between A {v₁} := by rw [ha₁]; exact Finset.mem_singleton_self _
  have ha₂m : a₂ ∈ Δ.between A {v₂} := by rw [ha₂]; exact Finset.mem_singleton_self _
  rw [mem_between] at hfm ha₁m ha₂m
  simp only [Finset.mem_singleton] at hfm ha₁m ha₂m
  have hfE := hfm.1
  have hfj : Δ.Joins f v₁ v₂ := hfm.2
  -- an edge at `v₁` other than `f` and `a₁`
  have hfat₁ : f ∈ Δ.edgesAt v₁ := by
    rw [mem_edgesAt]
    refine ⟨hfE, ?_⟩
    rcases hfj with ⟨h0, -⟩ | ⟨-, h1⟩
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩
  have ha₁at : a₁ ∈ Δ.edgesAt v₁ := by
    rw [mem_edgesAt]
    refine ⟨ha₁m.1, ?_⟩
    rcases ha₁m.2 with ⟨-, h1⟩ | ⟨h0, -⟩
    · exact ⟨1, h1⟩
    · exact ⟨0, h0⟩
  have hfa₁ : f ≠ a₁ := by
    intro h
    rw [h] at hfm
    -- `a₁` has an end in `A`, but both ends of `f` are `v₁, v₂ ∉ A`
    rcases ha₁m.2 with ⟨h0, -⟩ | ⟨-, h1⟩ <;> rcases hfm.2 with ⟨g0, g1⟩ | ⟨g0, g1⟩
    · exact hv₁A (g0 ▸ h0)
    · exact hv₂A (g0 ▸ h0)
    · exact hv₂A (g1 ▸ h1)
    · exact hv₁A (g1 ▸ h1)
  have third : ∀ v ∈ Δ.Vs, ∀ e₁ e₂, e₁ ∈ Δ.edgesAt v → e₂ ∈ Δ.edgesAt v → e₁ ≠ e₂ →
      ∃ e₃, e₃ ∈ Δ.edgesAt v ∧ e₃ ≠ e₁ ∧ e₃ ≠ e₂ ∧
        ∀ e ∈ Δ.edgesAt v, e = e₁ ∨ e = e₂ ∨ e = e₃ := by
    intro v hv e₁ e₂ h₁ h₂ hne
    have hcard : (Δ.edgesAt v).card = 3 := by rw [card_edgesAt hg hcl hv, hcub v hv]
    have hsub : ({e₁, e₂} : Finset ℕ) ⊆ Δ.edgesAt v := by
      intro e he
      rw [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl <;> assumption
    have hsd : (Δ.edgesAt v \ {e₁, e₂}).card = 1 := by
      rw [Finset.card_sdiff_of_subset hsub, hcard, Finset.card_pair hne]
    obtain ⟨e₃, he₃⟩ := Finset.card_eq_one.mp hsd
    have he₃m : e₃ ∈ Δ.edgesAt v \ {e₁, e₂} := by rw [he₃]; exact Finset.mem_singleton_self _
    rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at he₃m
    refine ⟨e₃, he₃m.1, fun h ↦ he₃m.2 (Or.inl h), fun h ↦ he₃m.2 (Or.inr h), ?_⟩
    intro e he
    by_cases h : e = e₁ ∨ e = e₂
    · rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · right; right
      have : e ∈ Δ.edgesAt v \ {e₁, e₂} := by
        rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
        exact ⟨he, h⟩
      rw [he₃, Finset.mem_singleton] at this
      exact this
  obtain ⟨l₁, hl₁at, hl₁f, hl₁a, hall₁⟩ := third v₁ hv₁V f a₁ hfat₁ ha₁at hfa₁
  -- symmetric facts for `v₂`
  have hfat₂ : f ∈ Δ.edgesAt v₂ := by
    rw [mem_edgesAt]
    refine ⟨hfE, ?_⟩
    rcases hfj with ⟨-, h1⟩ | ⟨h0, -⟩
    · exact ⟨1, h1⟩
    · exact ⟨0, h0⟩
  have ha₂at : a₂ ∈ Δ.edgesAt v₂ := by
    rw [mem_edgesAt]
    refine ⟨ha₂m.1, ?_⟩
    rcases ha₂m.2 with ⟨-, h1⟩ | ⟨h0, -⟩
    · exact ⟨1, h1⟩
    · exact ⟨0, h0⟩
  have hfa₂ : f ≠ a₂ := by
    intro h
    rw [h] at hfm
    rcases ha₂m.2 with ⟨h0, -⟩ | ⟨-, h1⟩ <;> rcases hfm.2 with ⟨g0, g1⟩ | ⟨g0, g1⟩
    · exact hv₁A (g0 ▸ h0)
    · exact hv₂A (g0 ▸ h0)
    · exact hv₂A (g1 ▸ h1)
    · exact hv₁A (g1 ▸ h1)
  obtain ⟨l₂, hl₂at, hl₂f, hl₂a, hall₂⟩ := third v₂ hv₂V f a₂ hfat₂ ha₂at hfa₂
  -- the other end of `l₁` is outside `Y`
  have hl_out : ∀ (l v : ℕ) (a : ℕ), v ∈ Δ.Vs → l ∈ Δ.edgesAt v → l ≠ f → l ≠ a →
      Δ.between A {v} = {a} → (∀ w, w = v₁ ∨ w = v₂ → v ≠ w → Δ.between {v} {w} = {f}) →
      (v = v₁ ∨ v = v₂) → l ∈ Δ.bd Y ∧ ∃ i, Δ.ends l i = v := by
    intro l v a hvV hl hlf hla hbetA hbetf hvv
    obtain ⟨hlE, i, hi⟩ := mem_edgesAt.mp hl
    refine ⟨?_, i, hi⟩
    rw [mem_bd]
    refine ⟨hlE, ?_⟩
    have hvY : v ∈ Y := by rcases hvv with rfl | rfl <;> assumption
    have hother : Δ.ends l (Fin.rev i) ∉ Y := by
      intro hoY
      rw [hYeq, Finset.mem_insert, Finset.mem_insert] at hoY
      have hloop := hg.no_loop hlE (hcl l hlE 0)
      rcases hoY with ho | ho | ho
      · -- the other end is `v₁`
        by_cases hvv₁ : v = v₁
        · -- a loop
          have hi0 : i = 0 ∨ i = 1 := by omega
          rcases hi0 with rfl | rfl
          · rw [Iso.rev_zero'] at ho; exact hloop (hi.trans (hvv₁.trans ho.symm))
          · rw [Iso.rev_one'] at ho; exact hloop (ho.trans (hvv₁.symm.trans hi.symm))
        · -- parallel to `f`
          have hmem : l ∈ Δ.between {v} {v₁} := by
            rw [mem_between]
            refine ⟨hlE, ?_⟩
            simp only [Finset.mem_singleton]
            have hi0 : i = 0 ∨ i = 1 := by omega
            rcases hi0 with rfl | rfl
            · rw [Iso.rev_zero'] at ho; exact Or.inl ⟨hi, ho⟩
            · rw [Iso.rev_one'] at ho; exact Or.inr ⟨ho, hi⟩
          rw [hbetf v₁ (Or.inl rfl) hvv₁, Finset.mem_singleton] at hmem
          exact hlf hmem
      · by_cases hvv₂ : v = v₂
        · have hi0 : i = 0 ∨ i = 1 := by omega
          rcases hi0 with rfl | rfl
          · rw [Iso.rev_zero'] at ho; exact hloop (hi.trans (hvv₂.trans ho.symm))
          · rw [Iso.rev_one'] at ho; exact hloop (ho.trans (hvv₂.symm.trans hi.symm))
        · have hmem : l ∈ Δ.between {v} {v₂} := by
            rw [mem_between]
            refine ⟨hlE, ?_⟩
            simp only [Finset.mem_singleton]
            have hi0 : i = 0 ∨ i = 1 := by omega
            rcases hi0 with rfl | rfl
            · rw [Iso.rev_zero'] at ho; exact Or.inl ⟨hi, ho⟩
            · rw [Iso.rev_one'] at ho; exact Or.inr ⟨ho, hi⟩
          rw [hbetf v₂ (Or.inr rfl) hvv₂, Finset.mem_singleton] at hmem
          exact hlf hmem
      · -- the other end is in `A`: then `l ∈ between A {v}`
        have hmem : l ∈ Δ.between A {v} := by
          rw [mem_between]
          refine ⟨hlE, ?_⟩
          simp only [Finset.mem_singleton]
          have hi0 : i = 0 ∨ i = 1 := by omega
          rcases hi0 with rfl | rfl
          · rw [Iso.rev_zero'] at ho; exact Or.inr ⟨hi, ho⟩
          · rw [Iso.rev_one'] at ho; exact Or.inl ⟨ho, hi⟩
        rw [hbetA, Finset.mem_singleton] at hmem
        exact hla hmem
    have hi0 : i = 0 ∨ i = 1 := by omega
    rcases hi0 with rfl | rfl
    · rw [Iso.rev_zero'] at hother
      rw [hi]
      exact fun h ↦ hother (h.mp hvY)
    · rw [Iso.rev_one'] at hother
      rw [hi]
      exact fun h ↦ hother (h.mpr hvY)
  have hbetf : ∀ v, (v = v₁ ∨ v = v₂) → ∀ w, (w = v₁ ∨ w = v₂) → v ≠ w →
      Δ.between {v} {w} = {f} := by
    rintro v (rfl | rfl) w (rfl | rfl) hvw
    · exact absurd rfl hvw
    · exact hf
    · rw [between_comm]; exact hf
    · exact absurd rfl hvw
  obtain ⟨hl₁bd, hl₁v⟩ := hl_out l₁ v₁ a₁ hv₁V hl₁at hl₁f hl₁a ha₁ (hbetf v₁ (Or.inl rfl))
    (Or.inl rfl)
  obtain ⟨hl₂bd, hl₂v⟩ := hl_out l₂ v₂ a₂ hv₂V hl₂at hl₂f hl₂a ha₂ (hbetf v₂ (Or.inr rfl))
    (Or.inr rfl)
  -- `a₁` is a boundary edge of `A`
  have ha₁bd : a₁ ∈ Δ.bd A := by
    rw [mem_bd]
    refine ⟨ha₁m.1, ?_⟩
    rcases ha₁m.2 with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · rw [h1]; exact fun h ↦ hv₁A (h.mp h0)
    · rw [h0]; exact fun h ↦ hv₁A (h.mpr h1)
  have ha₂bd : a₂ ∈ Δ.bd A := by
    rw [mem_bd]
    refine ⟨ha₂m.1, ?_⟩
    rcases ha₂m.2 with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · rw [h1]; exact fun h ↦ hv₂A (h.mp h0)
    · rw [h0]; exact fun h ↦ hv₂A (h.mpr h1)
  refine ⟨⟨v₁, v₂, f, a₁, a₂, l₁, l₂, hv, hv₁A, hv₂A, hYeq, hfE, hfj, ha₁bd, ha₂bd, ?_, ?_, hl₁bd,
    hl₂bd, hl₁v, hl₂v, ?_, ?_, hfa₁, hl₁f.symm, hl₁a.symm, hfa₂, hl₂f.symm, hl₂a.symm⟩⟩
  · rcases ha₁m.2 with ⟨-, h1⟩ | ⟨h0, -⟩
    · exact ⟨1, h1⟩
    · exact ⟨0, h0⟩
  · rcases ha₂m.2 with ⟨-, h1⟩ | ⟨h0, -⟩
    · exact ⟨1, h1⟩
    · exact ⟨0, h0⟩
  · intro e he i hi
    exact hall₁ e (mem_edgesAt.mpr ⟨he, i, hi⟩)
  · intro e he i hi
    exact hall₂ e (mem_edgesAt.mpr ⟨he, i, hi⟩)

end Extract

end FinGraph
end GraphPuzzles
