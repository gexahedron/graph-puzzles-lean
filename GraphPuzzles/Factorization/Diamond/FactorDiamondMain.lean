import GraphPuzzles.Factorization.Diamond.FactorDiamond

/-!
# The diamond for a non-associated cut (Chladný–Škoviera, Lemma 10.1)

For an atom `A` and a cycle-separating shore `Y ⊇ A` which is neither `A` nor quasiatomic,
the two decompositions (along `∂A` and along `∂Y`) can be completed by one further step each
to isomorphic multisets of factors.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

section Sets

variable {Δ : FinGraph} {A Y : Finset ℕ}

theorem sdiff_sdiff_sdiff_eq (_hAY : A ⊆ Y) (hY : Y ⊆ Δ.Vs) :
    (Δ.Vs \ A) \ (Δ.Vs \ Y) = Y \ A := by
  ext v
  simp only [Finset.mem_sdiff, not_and, not_not]
  constructor
  · rintro ⟨⟨hv, hA⟩, h⟩
    exact ⟨h hv, hA⟩
  · rintro ⟨hvY, hA⟩
    exact ⟨⟨hY hvY, hA⟩, fun _ ↦ hvY⟩

end Sets

section Class

variable {P : FinGraph → Prop} (hG : GoodClass P) {Δ : FinGraph} (hΔ : P Δ)
include hG hΔ

theorem factorOf_mem {Y : Finset ℕ} (hY : Δ.CycSep Y) : P (factorOf Δ Y) := by
  obtain ⟨_, _, _, h⟩ := factor_cases hG hΔ hY
  rcases h with ⟨-, -, h3, h4, -, -⟩ | ⟨-, -, h3, h4, -, -⟩ <;> rw [h3] <;> exact h4

/-- Boundary couples of an atom never lie inside the boundary of a non-associated shore. -/
theorem noCouple_A {A Y : Finset ℕ} (hA : Δ.IsAtom A) (hY : Δ.CycSep Y) (hAY : A ⊆ Y)
    (hne : Y ≠ A) (hPA : (Δ.pole A).IsPole4) {mA : Fin 3}
    (hmA : IsoWith hPA mA ∨ HetWith hPA mA) :
    ∀ d ∈ Δ.bd A, d ∈ Δ.bd Y → partner hPA mA d ∉ Δ.bd Y := by
  intro d hd hdY hpY
  have hd' : d ∈ (Δ.pole A).dangling := dangling_pole A ▸ hd
  obtain ⟨k, rfl⟩ := exists_bdEmb_eq hPA hd'
  rw [partner_bdEmb] at hpY
  have hPY := hY.isPole4 (hG.cubic Δ hΔ)
  exact not_couple_of_bdA hG hΔ hA hY hAY hne hPA hPY (pairing_ne mA k).symm hdY hpY hmA rfl

/-- Boundary couples of a non-associated shore never lie inside the boundary of the atom. -/
theorem noCouple_Y {A Y : Finset ℕ} (hA : Δ.IsAtom A) (hY : Δ.CycSep Y) (hAY : A ⊆ Y)
    (hne : Y ≠ A) (hPY : (Δ.pole Y).IsPole4) {mY : Fin 3}
    (hmY : IsoWith hPY mY ∨ HetWith hPY mY) :
    ∀ d ∈ Δ.bd Y, d ∈ Δ.bd A → partner hPY mY d ∉ Δ.bd A := by
  intro d hd hdA hpA
  have hd' : d ∈ (Δ.pole Y).dangling := dangling_pole Y ▸ hd
  obtain ⟨k, rfl⟩ := exists_bdEmb_eq hPY hd'
  rw [partner_bdEmb] at hpA
  have hle := card_inter_le_two hG hΔ hA hY hAY hne
  have hcard : (Δ.bd A ∩ Δ.bd Y).card = 2 := by
    have hsub : ({bdEmb hPY k, bdEmb hPY (pairing mY k)} : Finset ℕ) ⊆ Δ.bd A ∩ Δ.bd Y := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hdA, hd⟩
      · exact Finset.mem_inter.mpr ⟨hpA, dangling_pole Y ▸ bdEmb_mem hPY _⟩
    have hc2 : ({bdEmb hPY k, bdEmb hPY (pairing mY k)} : Finset ℕ).card = 2 := by
      rw [Finset.card_pair]
      intro h
      exact pairing_ne mY k (bdEmb_injective hPY h).symm
    have := Finset.card_le_card hsub
    omega
  exact no_couple_in_cut hG hΔ hA.1 hY hAY hne hPY hdA hpA hcard hmY rfl

/-- **The diamond for a non-associated shore containing the atom.** -/
theorem diamond_of_subset {A Y : Finset ℕ} (hA : Δ.IsAtom A) (hY : Δ.CycSep Y) (hAY : A ⊆ Y)
    (hne : Y ≠ A) (hnq : ¬ Δ.IsQuasiatomic A Y) :
    ∃ A₀' C' C'' D', Step (factorOf Δ Y) A₀' C' ∧ Nonempty (Iso A₀' (factorOf Δ A)) ∧
      Step (factorOf Δ (Δ.Vs \ A)) C'' D' ∧ Nonempty (Iso C'' C') ∧
      Nonempty (Iso D' (factorOf Δ (Δ.Vs \ Y))) := by
  have hcl := hG.closed Δ hΔ
  have hcub := hG.cubic Δ hΔ
  have hYV : Y ⊆ Δ.Vs := hY.1
  have hAV : A ⊆ Δ.Vs := hA.1.1
  have hAc := cycSep_compl hcl hA.1
  have hYc := cycSep_compl hcl hY
  have hXW' : Δ.Vs \ Y ⊆ Δ.Vs \ A := fun v hv ↦
    Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hv).1, fun h ↦ (Finset.mem_sdiff.mp hv).2 (hAY h)⟩
  have hVA : Δ.Vs \ A ⊆ Δ.Vs := Finset.sdiff_subset
  obtain ⟨hPY, hPYc, mY, hcY⟩ := factor_cases hG hΔ hY
  obtain ⟨hPA, hPAc, mA, hcA⟩ := factor_cases hG hΔ hA.1
  have hcolA := hG.pole_colourable Δ hΔ A hA.1
  have hcolY := hG.pole_colourable Δ hΔ Y hY
  have hcolAc := hG.pole_colourable Δ hΔ _ hAc
  have hcolYc := hG.pole_colourable Δ hΔ _ hYc
  have hmA : IsoWith hPA mA ∨ HetWith hPA mA := by
    rcases hcA with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have hmY : IsoWith hPY mY ∨ HetWith hPY mY := by
    rcases hcY with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have hnoA := noCouple_A hG hΔ hA hY hAY hne hPA hmA
  have hnoY := noCouple_Y hG hΔ hA hY hAY hne hPY hmY
  -- the dangling sets of complementary poles agree
  have hdA : (Δ.pole A).dangling = (Δ.pole (Δ.Vs \ A)).dangling := by
    rw [dangling_pole, dangling_pole, bd_compl hcl]
  have hdY : (Δ.pole Y).dangling = (Δ.pole (Δ.Vs \ Y)).dangling := by
    rw [dangling_pole, dangling_pole, bd_compl hcl]
  have hpA : partner hPA mA = partner hPAc mA := funext (partner_congr hPA mA hPAc hdA)
  have hpY : partner hPY mY = partner hPYc mY := funext (partner_congr hPY mY hPYc hdY)
  have hbdA : Δ.bd (Δ.Vs \ A) = Δ.bd A := bd_compl hcl A
  have hbdY : Δ.bd (Δ.Vs \ Y) = Δ.bd Y := bd_compl hcl Y
  -- the first factor along `Y` and the atom inside it
  have hP₁ : P (factorOf Δ Y) := factorOf_mem hG hΔ hY
  have hcsA : (factorOf Δ Y).CycSep A := cycSep_in_factor hG hΔ hA hY hAY hne hnq
  have hcl₁ := hG.closed _ hP₁
  have hcub₁ := hG.cubic _ hP₁
  have hP₁A : ((factorOf Δ Y).pole A).IsPole4 := hcsA.isPole4 hcub₁
  have hcol₁A := hG.pole_colourable _ hP₁ A hcsA
  have step1 := exists_step_of_cycSep hG hP₁ hcsA
  -- the pole of `A` in the first factor is the pole of `A`
  have fA : Nonempty (Iso ((factorOf Δ Y).pole A) (Δ.pole A)) := by
    rcases hcY with ⟨-, -, h3, -, -, -⟩ | ⟨-, -, h3, -, -, -⟩
    · rw [h3]; exact ⟨capPoleIso hPY mY hcl hYV hAY⟩
    · rw [h3]
      refine ⟨joinPoleIso hPY mY hYV A hAY ?_⟩
      intro k h1 h2
      have := hnoY (bdEmb hPY k) (dangling_pole Y ▸ bdEmb_mem hPY k) h1
      rw [partner_bdEmb] at this
      exact this h2
  obtain ⟨fA⟩ := fA
  have iso1 : Nonempty (Iso (factorOf (factorOf Δ Y) A) (factorOf Δ A)) := by
    obtain ⟨_, _, m, hm⟩ := factor_cases hG hP₁ hcsA
    rcases hm with ⟨h, -⟩ | ⟨h, -⟩
    · exact factorOf_iso_of_pole_iso fA hP₁A hcol₁A (Or.inl h)
    · exact factorOf_iso_of_pole_iso fA hP₁A hcol₁A (Or.inr h)
  -- the factor along the complement of the atom and the projected cut
  have hB₀ : P (factorOf Δ (Δ.Vs \ A)) := factorOf_mem hG hΔ hAc
  have hclB := hG.closed _ hB₀
  have hcubB := hG.cubic _ hB₀
  have hVYB : Δ.Vs \ Y ⊆ (factorOf Δ (Δ.Vs \ A)).Vs := by
    rcases hcA with ⟨-, -, -, -, h5, -⟩ | ⟨-, -, -, -, h5, -⟩
    · rw [h5, join_Vs, pole_Vs]; exact hXW'
    · rw [h5, cap_Vs, pole_Vs]
      exact fun v hv ↦ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hXW' hv))
  have hcsY' : (factorOf Δ (Δ.Vs \ A)).CycSep ((factorOf Δ (Δ.Vs \ A)).Vs \ (Δ.Vs \ Y)) := by
    rcases hcA with ⟨-, h2, -, -, h5, h6⟩ | ⟨-, h2, -, -, h5, h6⟩
    · rw [h5]
      have := (projected_cycSep hG hΔ hA hY hAY hne hnq hPAc mA).2 h2 h6
      rw [join_Vs_sdiff hPAc mA, sdiff_sdiff_sdiff_eq hAY hYV]
      exact this
    · rw [h5]
      have := (projected_cycSep hG hΔ hA hY hAY hne hnq hPAc mA).1 h2 h6
      rw [cap_Vs_sdiff hXW' hPAc mA, sdiff_sdiff_sdiff_eq hAY hYV]
      exact this
  have hcsVY : (factorOf Δ (Δ.Vs \ A)).CycSep (Δ.Vs \ Y) := by
    have := cycSep_compl hclB hcsY'
    rw [Finset.sdiff_sdiff_eq_self hVYB] at this
    exact this
  have step2 := exists_step_of_cycSep hG hB₀ hcsY'
  rw [Finset.sdiff_sdiff_eq_self hVYB] at step2
  -- the pole of `Δ.Vs \ Y` in the complement factor is the pole of `Δ.Vs \ Y`
  have hPBY : ((factorOf Δ (Δ.Vs \ A)).pole (Δ.Vs \ Y)).IsPole4 := hcsVY.isPole4 hcubB
  have hcolBY := hG.pole_colourable _ hB₀ _ hcsVY
  have fY : Nonempty (Iso ((factorOf Δ (Δ.Vs \ A)).pole (Δ.Vs \ Y)) (Δ.pole (Δ.Vs \ Y))) := by
    rcases hcA with ⟨-, -, -, -, h5, -⟩ | ⟨-, -, -, -, h5, -⟩
    · rw [h5]
      refine ⟨joinPoleIso hPAc mA hVA (Δ.Vs \ Y) hXW' ?_⟩
      intro k h1 h2
      rw [hbdY] at h1 h2
      have hk : bdEmb hPAc k ∈ Δ.bd A := by
        have := bdEmb_mem hPAc k
        rw [dangling_pole, hbdA] at this
        exact this
      have := hnoA (bdEmb hPAc k) hk h1
      rw [hpA, partner_bdEmb] at this
      exact this h2
    · rw [h5]; exact ⟨capPoleIso hPAc mA hcl hVA hXW'⟩
  obtain ⟨fY⟩ := fY
  have iso3 : Nonempty (Iso (factorOf (factorOf Δ (Δ.Vs \ A)) (Δ.Vs \ Y))
      (factorOf Δ (Δ.Vs \ Y))) := by
    obtain ⟨_, _, m, hm⟩ := factor_cases hG hB₀ hcsVY
    rcases hm with ⟨h, -⟩ | ⟨h, -⟩
    · exact factorOf_iso_of_pole_iso fY hPBY hcolBY (Or.inl h)
    · exact factorOf_iso_of_pole_iso fY hPBY hcolBY (Or.inr h)
  -- the middle isomorphism through the canonical double completion
  have hcase' : (IsoWith hPY mY ∧ HetWith hPYc mY) ∨ (HetWith hPY mY ∧ IsoWith hPYc mY) := by
    rcases hcY with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
  have eA : Δ.Vs \ (Δ.Vs \ A) = A := Finset.sdiff_sdiff_eq_self hAV
  have hPAcc : (Δ.pole (Δ.Vs \ (Δ.Vs \ A))).IsPole4 := IsPole4.congr (pole_congr eA.symm) hPA
  have hcaseA' : (IsoWith hPAc mA ∧ HetWith hPAcc mA) ∨ (HetWith hPAc mA ∧ IsoWith hPAcc mA) := by
    rcases hcA with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
    · exact Or.inr ⟨h2, IsoWith.congr (pole_congr eA.symm) hPA hPAcc mA h1⟩
    · exact Or.inl ⟨h2, HetWith.congr (pole_congr eA.symm) hPA hPAcc mA h1⟩
  have hmYc : IsoWith hPYc mY ∨ HetWith hPYc mY := by
    rcases hcY with ⟨-, h2, -⟩ | ⟨-, h2, -⟩
    · exact Or.inr h2
    · exact Or.inl h2
  have hnoX' : ∀ d ∈ Δ.bd (Δ.Vs \ Y), d ∈ Δ.bd (Δ.Vs \ A) → partner hPYc mY d ∉ Δ.bd (Δ.Vs \ A) := by
    rw [hbdY, hbdA, ← hpY]; exact hnoY
  have hnoW' : ∀ d ∈ Δ.bd (Δ.Vs \ A), d ∈ Δ.bd (Δ.Vs \ Y) → partner hPAc mA d ∉ Δ.bd (Δ.Vs \ Y) := by
    rw [hbdY, hbdA, ← hpA]; exact hnoA
  -- the gadget flags
  obtain ⟨gA, hgA⟩ : ∃ gA : Bool, gA = true ↔ HetWith hPA mA := by
    rcases hmA with h | h
    · exact ⟨false, ⟨fun h' ↦ absurd h' (by decide), fun h' ↦ absurd h' (fun h' ↦
        not_isoWith_hetWith hPA hcolA h h')⟩⟩
    · exact ⟨true, ⟨fun _ ↦ h, fun _ ↦ rfl⟩⟩
  obtain ⟨gY, hgY⟩ : ∃ gY : Bool, gY = true ↔ IsoWith hPY mY := by
    rcases hmY with h | h
    · exact ⟨true, ⟨fun _ ↦ h, fun _ ↦ rfl⟩⟩
    · exact ⟨false, ⟨fun h' ↦ absurd h' (by decide), fun h' ↦ absurd h' (fun h' ↦
        not_isoWith_hetWith hPY hcolY h' h)⟩⟩
  have hgA' : gA = true ↔ IsoWith hPAc mA := by
    rw [hgA]
    constructor
    · intro h; exact isoWith_compl hG hΔ hA.1 hPA hPAc h
    · intro h
      rcases hmA with h' | h'
      · exact absurd h (fun h ↦ not_isoWith_hetWith hPAc hcolAc h (hetWith_compl hG hΔ hA.1 hPA hPAc h'))
      · exact h'
  have hgY' : gY = true ↔ HetWith hPYc mY := by
    rw [hgY]
    constructor
    · intro h; exact hetWith_compl hG hΔ hY hPY hPYc h
    · intro h
      rcases hmY with h' | h'
      · exact h'
      · exact absurd h (fun h ↦ not_isoWith_hetWith hPYc hcolYc (isoWith_compl hG hΔ hY hPY hPYc h') h)
  obtain ⟨h1⟩ := dbl_outer_iso hG hΔ hAY hY hPY hPYc mY hPA mA hcase' hmA hnoA hnoY hcsA gA gY hgA hgY
  obtain ⟨h2⟩ := dbl_outer_iso hG hΔ hXW' hAc hPAc hPAcc mA hPYc mY hcaseA' hmYc hnoX' hnoW'
    hcsVY gY gA hgY' hgA'
  rw [sdiff_sdiff_sdiff_eq hAY hYV, hbdY, hbdA, ← hpY, ← hpA] at h2
  have hneYA : (Δ.bd Y \ Δ.bd A).Nonempty := sdiffW_nonempty hPY mY hnoY
  have hneAY : (Δ.bd A \ Δ.bd Y).Nonempty := sdiffX_nonempty hPA mA hnoA
  have hsym := canSymm Δ (Y \ A) (Δ.bd Y) (Δ.bd A) (partner hPY mY) (partner hPA mA) gY gA
    (bd_subset Y) (bd_subset A) hneYA hneAY
  exact ⟨_, _, _, _, step1, iso1, step2, ⟨(h2.trans hsym).trans h1.symm⟩, iso3⟩

end Class

end FinGraph
end GraphPuzzles
