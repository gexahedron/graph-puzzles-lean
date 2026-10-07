import GraphPuzzles.Factorization.Bicritical.FactorParity
import GraphPuzzles.Factorization.FactorJoinCap

/-!
# The pole of a quadrilateral

The `4`-pole obtained by cutting the four edges leaving a quadrilateral has colourings with a
constant boundary vector and with boundary vectors isochromatic for each of the two pairings
of adjacent pendant edges.  Hence it is neither isochromatic nor heterochromatic for any
pairing.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

section Criterion

variable {Γ : FinGraph} {c : ℕ → Color}

/-- A colouring criterion: nonzero colours, no loops, and distinct edges at a vertex receive
distinct colours. -/
theorem isColouring_of_distinct (hnz : ∀ e ∈ Γ.Es, c e ≠ 0)
    (hloop : ∀ e ∈ Γ.Es, Γ.ends e 0 ≠ Γ.ends e 1)
    (hdist : ∀ v ∈ Γ.Vs, ∀ e ∈ Γ.Es, ∀ e' ∈ Γ.Es, e ≠ e' → (∃ i, Γ.ends e i = v) →
      (∃ j, Γ.ends e' j = v) → c e ≠ c e') : Γ.IsColouring c := by
  refine ⟨hnz, ?_⟩
  intro v hv h₁ h₁m h₂ h₂m heq
  rw [mem_halfEdgesIn] at h₁m h₂m
  by_cases he : h₁.1 = h₂.1
  · by_cases hi : h₁.2 = h₂.2
    · exact Prod.ext he hi
    · exfalso
      have h1 := h₁m.2
      have h2 := h₂m.2
      rw [he] at h1
      have hi0 : h₁.2 = 0 ∨ h₁.2 = 1 := by omega
      have hi0' : h₂.2 = 0 ∨ h₂.2 = 1 := by omega
      rcases hi0 with a | a <;> rcases hi0' with b | b <;> rw [a] at h1 hi <;> rw [b] at h2 hi
      · exact hi rfl
      · exact hloop _ h₂m.1 (h1.trans h2.symm)
      · exact hloop _ h₂m.1 (h2.trans h1.symm)
      · exact hi rfl
  · exact absurd heq (hdist v hv _ h₁m.1 _ h₂m.1 he ⟨_, h₁m.2⟩ ⟨_, h₂m.2⟩)

/-- The partner formulation of isochromaticity. -/
theorem IsoWith.partner_eq {P : FinGraph} (hP : P.IsPole4) {m : Fin 3} (h : IsoWith hP m)
    (hc : P.IsColouring c) {d : ℕ} (hd : d ∈ P.dangling) : c d = c (partner hP m d) := by
  obtain ⟨k, rfl⟩ := exists_bdEmb_eq hP hd
  rw [partner_bdEmb]
  exact h (tvec hP c) ⟨c, hc, rfl⟩ k

/-- The partner formulation of heterochromaticity. -/
theorem HetWith.partner_ne {P : FinGraph} (hP : P.IsPole4) {m : Fin 3} (h : HetWith hP m)
    (hc : P.IsColouring c) {d : ℕ} (hd : d ∈ P.dangling) : c d ≠ c (partner hP m d) := by
  obtain ⟨k, rfl⟩ := exists_bdEmb_eq hP hd
  rw [partner_bdEmb]
  exact h (tvec hP c) ⟨c, hc, rfl⟩ k

theorem Joins.eq_of_eq {e a b a' b' : ℕ} (h : Γ.Joins e a b) (h' : Γ.Joins e a' b') :
    (a = a' ∧ b = b') ∨ (a = b' ∧ b = a') := by
  rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rcases h' with ⟨g0, g1⟩ | ⟨g0, g1⟩
  · exact Or.inl ⟨h0.symm.trans g0, h1.symm.trans g1⟩
  · exact Or.inr ⟨h0.symm.trans g0, h1.symm.trans g1⟩
  · exact Or.inr ⟨h1.symm.trans g1, h0.symm.trans g0⟩
  · exact Or.inl ⟨h1.symm.trans g1, h0.symm.trans g0⟩

theorem Joins.ends_mem {e a b : ℕ} (h : Γ.Joins e a b) {X : Finset ℕ} (ha : a ∈ X) (hb : b ∈ X)
    (i : Fin 2) : Γ.ends e i ∈ X := by
  rcases Joins.end_eq h i with h' | h' <;> rw [h'] <;> assumption

end Criterion

section FourCycle

variable {Γ : FinGraph} {X : Finset ℕ} {v₁ v₂ v₃ v₄ t₁ t₂ t₃ t₄ e₁ e₂ e₃ e₄ : ℕ}
  (hX : X = {v₁, v₂, v₃, v₄}) (h12 : v₁ ≠ v₂) (h13 : v₁ ≠ v₃) (h14 : v₁ ≠ v₄) (h23 : v₂ ≠ v₃)
  (h24 : v₂ ≠ v₄) (h34 : v₃ ≠ v₄)
  (jt₁ : Γ.Joins t₁ v₁ v₂) (jt₂ : Γ.Joins t₂ v₂ v₃) (jt₃ : Γ.Joins t₃ v₃ v₄) (jt₄ : Γ.Joins t₄ v₄ v₁)
  (he₁ : ∃ i, Γ.ends e₁ i = v₁ ∧ Γ.ends e₁ (Fin.rev i) ∉ X)
  (he₂ : ∃ i, Γ.ends e₂ i = v₂ ∧ Γ.ends e₂ (Fin.rev i) ∉ X)
  (he₃ : ∃ i, Γ.ends e₃ i = v₃ ∧ Γ.ends e₃ (Fin.rev i) ∉ X)
  (he₄ : ∃ i, Γ.ends e₄ i = v₄ ∧ Γ.ends e₄ (Fin.rev i) ∉ X)
  (hEs : (Γ.pole X).Es = {t₁, t₂, t₃, t₄, e₁, e₂, e₃, e₄})

/-- The three colourings of the quadrilateral pole. -/
def qc₀ (t₁ t₂ t₃ t₄ : ℕ) (e : ℕ) : Color :=
  if e = t₁ ∨ e = t₃ then (1, 0) else if e = t₂ ∨ e = t₄ then (0, 1) else (1, 1)

def qc₁ (t₁ t₂ t₃ t₄ e₁ e₄ : ℕ) (e : ℕ) : Color :=
  if e = t₁ ∨ e = t₃ then (1, 0) else if e = t₂ then (0, 1) else if e = t₄ then (1, 1)
  else if e = e₁ ∨ e = e₄ then (0, 1) else (1, 1)

def qc₂ (t₁ t₂ t₃ t₄ e₁ e₂ : ℕ) (e : ℕ) : Color :=
  if e = t₁ then (1, 1) else if e = t₂ ∨ e = t₄ then (1, 0) else if e = t₃ then (0, 1)
  else if e = e₁ ∨ e = e₂ then (0, 1) else (1, 1)

include hX h12 h13 h14 h23 h24 h34 jt₁ jt₂ jt₃ jt₄ he₁ he₂ he₃ he₄ hEs in
/-- **The quadrilateral pole is neither isochromatic nor heterochromatic.** -/
theorem fourCycle_types (hP : (Γ.pole X).IsPole4) (m : Fin 3) :
    ¬ IsoWith hP m ∧ ¬ HetWith hP m := by
  have hv₁ : v₁ ∈ X := by rw [hX]; simp
  have hv₂ : v₂ ∈ X := by rw [hX]; simp
  have hv₃ : v₃ ∈ X := by rw [hX]; simp
  have hv₄ : v₄ ∈ X := by rw [hX]; simp
  obtain ⟨i₁, hi₁, ho₁⟩ := he₁
  obtain ⟨i₂, hi₂, ho₂⟩ := he₂
  obtain ⟨i₃, hi₃, ho₃⟩ := he₃
  obtain ⟨i₄, hi₄, ho₄⟩ := he₄
  -- an end of a pendant edge lying in `X` is its attachment vertex
  have pend : ∀ (e v : ℕ) (i : Fin 2), Γ.ends e i = v → Γ.ends e (Fin.rev i) ∉ X →
      ∀ (k : Fin 2) (w : ℕ), Γ.ends e k = w → w ∈ X → w = v := by
    intro e v i hi ho k w hk hw
    by_cases hki : k = i
    · rw [hki, hi] at hk; exact hk.symm
    · have : k = Fin.rev i := fin2_eq_rev_of_ne hki
      rw [← this, hk] at ho
      exact absurd hw ho
  -- distinctness of the eight edges
  have tt : ∀ (t t' a b a' b' : ℕ), Γ.Joins t a b → Γ.Joins t' a' b' → t = t' →
      (a = a' ∧ b = b') ∨ (a = b' ∧ b = a') := by
    intro t t' a b a' b' h h' heq
    rw [heq] at h
    exact Joins.eq_of_eq h h'
  have t12 : t₁ ≠ t₂ := fun h ↦ by
    rcases tt _ _ _ _ _ _ jt₁ jt₂ h with ⟨h', -⟩ | ⟨h', -⟩
    · exact h12 h'
    · exact h13 h'
  have t13 : t₁ ≠ t₃ := fun h ↦ by
    rcases tt _ _ _ _ _ _ jt₁ jt₃ h with ⟨h', -⟩ | ⟨h', -⟩
    · exact h13 h'
    · exact h14 h'
  have t14 : t₁ ≠ t₄ := fun h ↦ by
    rcases tt _ _ _ _ _ _ jt₁ jt₄ h with ⟨h', -⟩ | ⟨-, h'⟩
    · exact h14 h'
    · exact h24 h'
  have t23 : t₂ ≠ t₃ := fun h ↦ by
    rcases tt _ _ _ _ _ _ jt₂ jt₃ h with ⟨h', -⟩ | ⟨h', -⟩
    · exact h23 h'
    · exact h24 h'
  have t24 : t₂ ≠ t₄ := fun h ↦ by
    rcases tt _ _ _ _ _ _ jt₂ jt₄ h with ⟨h', -⟩ | ⟨h', -⟩
    · exact h24 h'
    · exact h12 h'.symm
  have t34 : t₃ ≠ t₄ := fun h ↦ by
    rcases tt _ _ _ _ _ _ jt₃ jt₄ h with ⟨h', -⟩ | ⟨h', -⟩
    · exact h34 h'
    · exact h13 h'.symm
  -- cycle edges have both ends in `X`, pendant edges do not
  have te : ∀ (t a b e v : ℕ) (i : Fin 2), Γ.Joins t a b → a ∈ X → b ∈ X →
      Γ.ends e i = v → Γ.ends e (Fin.rev i) ∉ X → t ≠ e := by
    intro t a b e v i h ha hb hi ho heq
    rw [← heq] at ho
    exact ho (Joins.ends_mem h ha hb _)
  have t₁e₁ := te _ _ _ _ _ _ jt₁ hv₁ hv₂ hi₁ ho₁
  have t₁e₂ := te _ _ _ _ _ _ jt₁ hv₁ hv₂ hi₂ ho₂
  have t₁e₃ := te _ _ _ _ _ _ jt₁ hv₁ hv₂ hi₃ ho₃
  have t₁e₄ := te _ _ _ _ _ _ jt₁ hv₁ hv₂ hi₄ ho₄
  have t₂e₁ := te _ _ _ _ _ _ jt₂ hv₂ hv₃ hi₁ ho₁
  have t₂e₂ := te _ _ _ _ _ _ jt₂ hv₂ hv₃ hi₂ ho₂
  have t₂e₃ := te _ _ _ _ _ _ jt₂ hv₂ hv₃ hi₃ ho₃
  have t₂e₄ := te _ _ _ _ _ _ jt₂ hv₂ hv₃ hi₄ ho₄
  have t₃e₁ := te _ _ _ _ _ _ jt₃ hv₃ hv₄ hi₁ ho₁
  have t₃e₂ := te _ _ _ _ _ _ jt₃ hv₃ hv₄ hi₂ ho₂
  have t₃e₃ := te _ _ _ _ _ _ jt₃ hv₃ hv₄ hi₃ ho₃
  have t₃e₄ := te _ _ _ _ _ _ jt₃ hv₃ hv₄ hi₄ ho₄
  have t₄e₁ := te _ _ _ _ _ _ jt₄ hv₄ hv₁ hi₁ ho₁
  have t₄e₂ := te _ _ _ _ _ _ jt₄ hv₄ hv₁ hi₂ ho₂
  have t₄e₃ := te _ _ _ _ _ _ jt₄ hv₄ hv₁ hi₃ ho₃
  have t₄e₄ := te _ _ _ _ _ _ jt₄ hv₄ hv₁ hi₄ ho₄
  -- distinct pendant edges
  have ee : ∀ (e v e' v' : ℕ) (i i' : Fin 2), Γ.ends e i = v → Γ.ends e (Fin.rev i) ∉ X →
      Γ.ends e' i' = v' → v ∈ X → v' ∈ X → v ≠ v' → e ≠ e' := by
    intro e v e' v' i i' hi ho hi' hv hv' hne heq
    rw [← heq] at hi'
    exact hne (pend e v i hi ho i' v' hi' hv').symm
  have e12 := ee _ _ _ _ _ _ hi₁ ho₁ hi₂ hv₁ hv₂ h12
  have e13 := ee _ _ _ _ _ _ hi₁ ho₁ hi₃ hv₁ hv₃ h13
  have e14 := ee _ _ _ _ _ _ hi₁ ho₁ hi₄ hv₁ hv₄ h14
  have e23 := ee _ _ _ _ _ _ hi₂ ho₂ hi₃ hv₂ hv₃ h23
  have e24 := ee _ _ _ _ _ _ hi₂ ho₂ hi₄ hv₂ hv₄ h24
  have e34 := ee _ _ _ _ _ _ hi₃ ho₃ hi₄ hv₃ hv₄ h34
  -- membership
  have mem : ∀ e, e ∈ (Γ.pole X).Es ↔ e = t₁ ∨ e = t₂ ∨ e = t₃ ∨ e = t₄ ∨ e = e₁ ∨ e = e₂ ∨
      e = e₃ ∨ e = e₄ := by
    intro e
    rw [hEs]
    simp only [Finset.mem_insert, Finset.mem_singleton]
  -- the edges at each vertex
  have at₁ : ∀ e ∈ (Γ.pole X).Es, (∃ i, Γ.ends e i = v₁) → e = t₁ ∨ e = t₄ ∨ e = e₁ := by
    intro e he ⟨i, hi⟩
    rw [mem] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exfalso; rcases Joins.end_eq jt₂ i with h | h <;> rw [hi] at h
      · exact h12 h
      · exact h13 h
    · exfalso; rcases Joins.end_eq jt₃ i with h | h <;> rw [hi] at h
      · exact h13 h
      · exact h14 h
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
    · exact absurd (pend _ _ _ hi₂ ho₂ i v₁ hi hv₁) h12
    · exact absurd (pend _ _ _ hi₃ ho₃ i v₁ hi hv₁) h13
    · exact absurd (pend _ _ _ hi₄ ho₄ i v₁ hi hv₁) h14
  have at₂ : ∀ e ∈ (Γ.pole X).Es, (∃ i, Γ.ends e i = v₂) → e = t₁ ∨ e = t₂ ∨ e = e₂ := by
    intro e he ⟨i, hi⟩
    rw [mem] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exfalso; rcases Joins.end_eq jt₃ i with h | h <;> rw [hi] at h
      · exact h23 h
      · exact h24 h
    · exfalso; rcases Joins.end_eq jt₄ i with h | h <;> rw [hi] at h
      · exact h24 h
      · exact h12 h.symm
    · exact absurd (pend _ _ _ hi₁ ho₁ i v₂ hi hv₂) h12.symm
    · exact Or.inr (Or.inr rfl)
    · exact absurd (pend _ _ _ hi₃ ho₃ i v₂ hi hv₂) h23
    · exact absurd (pend _ _ _ hi₄ ho₄ i v₂ hi hv₂) h24
  have at₃ : ∀ e ∈ (Γ.pole X).Es, (∃ i, Γ.ends e i = v₃) → e = t₂ ∨ e = t₃ ∨ e = e₃ := by
    intro e he ⟨i, hi⟩
    rw [mem] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso; rcases Joins.end_eq jt₁ i with h | h <;> rw [hi] at h
      · exact h13 h.symm
      · exact h23 h.symm
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exfalso; rcases Joins.end_eq jt₄ i with h | h <;> rw [hi] at h
      · exact h34 h
      · exact h13 h.symm
    · exact absurd (pend _ _ _ hi₁ ho₁ i v₃ hi hv₃) h13.symm
    · exact absurd (pend _ _ _ hi₂ ho₂ i v₃ hi hv₃) h23.symm
    · exact Or.inr (Or.inr rfl)
    · exact absurd (pend _ _ _ hi₄ ho₄ i v₃ hi hv₃) h34
  have at₄ : ∀ e ∈ (Γ.pole X).Es, (∃ i, Γ.ends e i = v₄) → e = t₃ ∨ e = t₄ ∨ e = e₄ := by
    intro e he ⟨i, hi⟩
    rw [mem] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso; rcases Joins.end_eq jt₁ i with h | h <;> rw [hi] at h
      · exact h14 h.symm
      · exact h24 h.symm
    · exfalso; rcases Joins.end_eq jt₂ i with h | h <;> rw [hi] at h
      · exact h24 h.symm
      · exact h34 h.symm
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact absurd (pend _ _ _ hi₁ ho₁ i v₄ hi hv₄) h14.symm
    · exact absurd (pend _ _ _ hi₂ ho₂ i v₄ hi hv₄) h24.symm
    · exact absurd (pend _ _ _ hi₃ ho₃ i v₄ hi hv₄) h34.symm
    · exact Or.inr (Or.inr rfl)
  -- no loops
  have hloop : ∀ e ∈ (Γ.pole X).Es, (Γ.pole X).ends e 0 ≠ (Γ.pole X).ends e 1 := by
    intro e he
    rw [pole_ends]
    rw [mem] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rcases jt₁ with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rw [h0, h1]
      · exact h12
      · exact h12.symm
    · rcases jt₂ with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rw [h0, h1]
      · exact h23
      · exact h23.symm
    · rcases jt₃ with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rw [h0, h1]
      · exact h34
      · exact h34.symm
    · rcases jt₄ with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rw [h0, h1]
      · exact h14.symm
      · exact h14
    all_goals
      first
      | (intro h
         have hi0 : i₁ = 0 ∨ i₁ = 1 := by omega
         rcases hi0 with h' | h' <;> rw [h'] at hi₁ ho₁
         · rw [Iso.rev_zero'] at ho₁; exact ho₁ (h ▸ hi₁ ▸ hv₁)
         · rw [Iso.rev_one'] at ho₁; exact ho₁ (h.symm ▸ hi₁ ▸ hv₁))
      | (intro h
         have hi0 : i₂ = 0 ∨ i₂ = 1 := by omega
         rcases hi0 with h' | h' <;> rw [h'] at hi₂ ho₂
         · rw [Iso.rev_zero'] at ho₂; exact ho₂ (h ▸ hi₂ ▸ hv₂)
         · rw [Iso.rev_one'] at ho₂; exact ho₂ (h.symm ▸ hi₂ ▸ hv₂))
      | (intro h
         have hi0 : i₃ = 0 ∨ i₃ = 1 := by omega
         rcases hi0 with h' | h' <;> rw [h'] at hi₃ ho₃
         · rw [Iso.rev_zero'] at ho₃; exact ho₃ (h ▸ hi₃ ▸ hv₃)
         · rw [Iso.rev_one'] at ho₃; exact ho₃ (h.symm ▸ hi₃ ▸ hv₃))
      | (intro h
         have hi0 : i₄ = 0 ∨ i₄ = 1 := by omega
         rcases hi0 with h' | h' <;> rw [h'] at hi₄ ho₄
         · rw [Iso.rev_zero'] at ho₄; exact ho₄ (h ▸ hi₄ ▸ hv₄)
         · rw [Iso.rev_one'] at ho₄; exact ho₄ (h.symm ▸ hi₄ ▸ hv₄))
  -- the vertices of the pole
  have hVs : ∀ v ∈ (Γ.pole X).Vs, v = v₁ ∨ v = v₂ ∨ v = v₃ ∨ v = v₄ := by
    intro v hv
    rw [pole_Vs, hX] at hv
    simpa using hv
  -- the generic properness argument
  have proper : ∀ (c : ℕ → Color), (∀ e ∈ (Γ.pole X).Es, c e ≠ 0) →
      (c t₁ ≠ c t₄ ∧ c t₁ ≠ c e₁ ∧ c t₄ ≠ c e₁) →
      (c t₁ ≠ c t₂ ∧ c t₁ ≠ c e₂ ∧ c t₂ ≠ c e₂) →
      (c t₂ ≠ c t₃ ∧ c t₂ ≠ c e₃ ∧ c t₃ ≠ c e₃) →
      (c t₃ ≠ c t₄ ∧ c t₃ ≠ c e₄ ∧ c t₄ ≠ c e₄) → (Γ.pole X).IsColouring c := by
    intro c hnz d₁ d₂ d₃ d₄
    refine isColouring_of_distinct hnz hloop ?_
    intro v hv e he e' he' hne hev hev'
    rw [pole_ends] at hev hev'
    rcases hVs v hv with rfl | rfl | rfl | rfl
    · rcases at₁ e he hev with rfl | rfl | rfl <;> rcases at₁ e' he' hev' with rfl | rfl | rfl <;>
        first
        | exact absurd rfl hne
        | exact d₁.1
        | exact d₁.1.symm
        | exact d₁.2.1
        | exact d₁.2.1.symm
        | exact d₁.2.2
        | exact d₁.2.2.symm
    · rcases at₂ e he hev with rfl | rfl | rfl <;> rcases at₂ e' he' hev' with rfl | rfl | rfl <;>
        first
        | exact absurd rfl hne
        | exact d₂.1
        | exact d₂.1.symm
        | exact d₂.2.1
        | exact d₂.2.1.symm
        | exact d₂.2.2
        | exact d₂.2.2.symm
    · rcases at₃ e he hev with rfl | rfl | rfl <;> rcases at₃ e' he' hev' with rfl | rfl | rfl <;>
        first
        | exact absurd rfl hne
        | exact d₃.1
        | exact d₃.1.symm
        | exact d₃.2.1
        | exact d₃.2.1.symm
        | exact d₃.2.2
        | exact d₃.2.2.symm
    · rcases at₄ e he hev with rfl | rfl | rfl <;> rcases at₄ e' he' hev' with rfl | rfl | rfl <;>
        first
        | exact absurd rfl hne
        | exact d₄.1
        | exact d₄.1.symm
        | exact d₄.2.1
        | exact d₄.2.1.symm
        | exact d₄.2.2
        | exact d₄.2.2.symm
  -- values of the colourings
  have v₀ : qc₀ t₁ t₂ t₃ t₄ t₁ = (1, 0) ∧ qc₀ t₁ t₂ t₃ t₄ t₂ = (0, 1) ∧ qc₀ t₁ t₂ t₃ t₄ t₃ = (1, 0) ∧
      qc₀ t₁ t₂ t₃ t₄ t₄ = (0, 1) ∧ qc₀ t₁ t₂ t₃ t₄ e₁ = (1, 1) ∧ qc₀ t₁ t₂ t₃ t₄ e₂ = (1, 1) ∧
      qc₀ t₁ t₂ t₃ t₄ e₃ = (1, 1) ∧ qc₀ t₁ t₂ t₃ t₄ e₄ = (1, 1) := by
    simp [qc₀, t13, t23, t24, t12.symm, t13.symm, t14.symm, t24.symm,
      t34.symm, t₁e₁.symm, t₁e₂.symm, t₁e₃.symm, t₁e₄.symm, t₂e₁.symm, t₂e₂.symm, t₂e₃.symm,
      t₂e₄.symm, t₃e₁.symm, t₃e₂.symm, t₃e₃.symm, t₃e₄.symm, t₄e₁.symm, t₄e₂.symm, t₄e₃.symm,
      t₄e₄.symm]
  have v₁' : qc₁ t₁ t₂ t₃ t₄ e₁ e₄ t₁ = (1, 0) ∧ qc₁ t₁ t₂ t₃ t₄ e₁ e₄ t₂ = (0, 1) ∧
      qc₁ t₁ t₂ t₃ t₄ e₁ e₄ t₃ = (1, 0) ∧ qc₁ t₁ t₂ t₃ t₄ e₁ e₄ t₄ = (1, 1) ∧
      qc₁ t₁ t₂ t₃ t₄ e₁ e₄ e₁ = (0, 1) ∧ qc₁ t₁ t₂ t₃ t₄ e₁ e₄ e₂ = (1, 1) ∧
      qc₁ t₁ t₂ t₃ t₄ e₁ e₄ e₃ = (1, 1) ∧ qc₁ t₁ t₂ t₃ t₄ e₁ e₄ e₄ = (0, 1) := by
    simp [qc₁, t13, t23, t12.symm, t13.symm, t14.symm, t24.symm,
      t34.symm, t₁e₁.symm, t₁e₂.symm, t₁e₃.symm, t₁e₄.symm, t₂e₁.symm, t₂e₂.symm, t₂e₃.symm,
      t₂e₄.symm, t₃e₁.symm, t₃e₂.symm, t₃e₃.symm, t₃e₄.symm, t₄e₁.symm, t₄e₂.symm, t₄e₃.symm,
      t₄e₄.symm, e14, e24, e34, e12.symm, e13.symm, e14.symm]
  have v₂' : qc₂ t₁ t₂ t₃ t₄ e₁ e₂ t₁ = (1, 1) ∧ qc₂ t₁ t₂ t₃ t₄ e₁ e₂ t₂ = (1, 0) ∧
      qc₂ t₁ t₂ t₃ t₄ e₁ e₂ t₃ = (0, 1) ∧ qc₂ t₁ t₂ t₃ t₄ e₁ e₂ t₄ = (1, 0) ∧
      qc₂ t₁ t₂ t₃ t₄ e₁ e₂ e₁ = (0, 1) ∧ qc₂ t₁ t₂ t₃ t₄ e₁ e₂ e₂ = (0, 1) ∧
      qc₂ t₁ t₂ t₃ t₄ e₁ e₂ e₃ = (1, 1) ∧ qc₂ t₁ t₂ t₃ t₄ e₁ e₂ e₄ = (1, 1) := by
    simp [qc₂, t24, t34, t12.symm, t13.symm, t14.symm, t23.symm, t24.symm, t₁e₁.symm, t₁e₂.symm, t₁e₃.symm, t₁e₄.symm, t₂e₁.symm, t₂e₂.symm, t₂e₃.symm,
      t₂e₄.symm, t₃e₁.symm, t₃e₂.symm, t₃e₃.symm, t₃e₄.symm, t₄e₁.symm, t₄e₂.symm, t₄e₃.symm,
      t₄e₄.symm, e12, e12.symm, e13.symm, e14.symm, e23.symm, e24.symm]
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := v₀
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := v₁'
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := v₂'
  have nz : ∀ (c : ℕ → Color), c t₁ ≠ 0 → c t₂ ≠ 0 → c t₃ ≠ 0 → c t₄ ≠ 0 → c e₁ ≠ 0 → c e₂ ≠ 0 →
      c e₃ ≠ 0 → c e₄ ≠ 0 → ∀ e ∈ (Γ.pole X).Es, c e ≠ 0 := by
    intro c n1 n2 n3 n4 n5 n6 n7 n8 e he
    rw [mem] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  have col₀ : (Γ.pole X).IsColouring (qc₀ t₁ t₂ t₃ t₄) :=
    proper _ (nz _ (by rw [a1]; decide) (by rw [a2]; decide) (by rw [a3]; decide)
      (by rw [a4]; decide) (by rw [a5]; decide) (by rw [a6]; decide) (by rw [a7]; decide)
      (by rw [a8]; decide))
      ⟨by rw [a1, a4]; decide, by rw [a1, a5]; decide, by rw [a4, a5]; decide⟩
      ⟨by rw [a1, a2]; decide, by rw [a1, a6]; decide, by rw [a2, a6]; decide⟩
      ⟨by rw [a2, a3]; decide, by rw [a2, a7]; decide, by rw [a3, a7]; decide⟩
      ⟨by rw [a3, a4]; decide, by rw [a3, a8]; decide, by rw [a4, a8]; decide⟩
  have col₁ : (Γ.pole X).IsColouring (qc₁ t₁ t₂ t₃ t₄ e₁ e₄) :=
    proper _ (nz _ (by rw [b1]; decide) (by rw [b2]; decide) (by rw [b3]; decide)
      (by rw [b4]; decide) (by rw [b5]; decide) (by rw [b6]; decide) (by rw [b7]; decide)
      (by rw [b8]; decide))
      ⟨by rw [b1, b4]; decide, by rw [b1, b5]; decide, by rw [b4, b5]; decide⟩
      ⟨by rw [b1, b2]; decide, by rw [b1, b6]; decide, by rw [b2, b6]; decide⟩
      ⟨by rw [b2, b3]; decide, by rw [b2, b7]; decide, by rw [b3, b7]; decide⟩
      ⟨by rw [b3, b4]; decide, by rw [b3, b8]; decide, by rw [b4, b8]; decide⟩
  have col₂ : (Γ.pole X).IsColouring (qc₂ t₁ t₂ t₃ t₄ e₁ e₂) :=
    proper _ (nz _ (by rw [c1]; decide) (by rw [c2]; decide) (by rw [c3]; decide)
      (by rw [c4]; decide) (by rw [c5]; decide) (by rw [c6]; decide) (by rw [c7]; decide)
      (by rw [c8]; decide))
      ⟨by rw [c1, c4]; decide, by rw [c1, c5]; decide, by rw [c4, c5]; decide⟩
      ⟨by rw [c1, c2]; decide, by rw [c1, c6]; decide, by rw [c2, c6]; decide⟩
      ⟨by rw [c2, c3]; decide, by rw [c2, c7]; decide, by rw [c3, c7]; decide⟩
      ⟨by rw [c3, c4]; decide, by rw [c3, c8]; decide, by rw [c4, c8]; decide⟩
  -- the dangling edges
  have hdang : ∀ e, e ∈ (Γ.pole X).dangling ↔ e = e₁ ∨ e = e₂ ∨ e = e₃ ∨ e = e₄ := by
    intro e
    rw [mem_dangling, pole_Vs, mem]
    constructor
    · rintro ⟨h, i, hi⟩
      rw [pole_ends] at hi
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact absurd (Joins.ends_mem jt₁ hv₁ hv₂ i) hi
      · exact absurd (Joins.ends_mem jt₂ hv₂ hv₃ i) hi
      · exact absurd (Joins.ends_mem jt₃ hv₃ hv₄ i) hi
      · exact absurd (Joins.ends_mem jt₄ hv₄ hv₁ i) hi
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), _, ho₁⟩
      · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))), _, ho₂⟩
      · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))), _, ho₃⟩
      · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))), _, ho₄⟩
  have he₁d : e₁ ∈ (Γ.pole X).dangling := (hdang e₁).mpr (Or.inl rfl)
  have hp := partner_mem hP m he₁d
  have hpne := partner_ne hP m he₁d
  rw [hdang] at hp
  constructor
  · intro hiso
    rcases hp with h | h | h | h
    · exact hpne h
    · have := hiso.partner_eq hP col₁ he₁d
      rw [h, b5, b6] at this
      exact absurd this (by decide)
    · have := hiso.partner_eq hP col₁ he₁d
      rw [h, b5, b7] at this
      exact absurd this (by decide)
    · have := hiso.partner_eq hP col₂ he₁d
      rw [h, c5, c8] at this
      exact absurd this (by decide)
  · intro hhet
    have := hhet.partner_ne hP col₀ he₁d
    rcases hp with h | h | h | h
    · exact hpne h
    · rw [h, a5, a6] at this; exact this rfl
    · rw [h, a5, a7] at this; exact this rfl
    · rw [h, a5, a8] at this; exact this rfl

end FourCycle

end FinGraph
end GraphPuzzles
