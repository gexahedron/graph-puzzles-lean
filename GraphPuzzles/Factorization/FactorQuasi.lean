import GraphPuzzles.Factorization.FactorJoinCap
import GraphPuzzles.Factorization.Diamond.FactorDiamondMain

/-!
# The quasiatomic case (Chladný–Škoviera, Proposition 8.2)

For an atom `A` and a quasiatomic shore `Y ⊇ A`, the factors along `∂Y` are isomorphic to the
factors along `∂A`.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

section Class

variable {P : FinGraph → Prop} (hG : GoodClass P) {Δ : FinGraph} (hΔ : P Δ)
include hG hΔ

/-- **Chladný–Škoviera, Proposition 8.2.** -/
theorem quasi_iso {A Y : Finset ℕ} (hA : Δ.IsAtom A) (hY : Δ.CycSep Y) (hAY : A ⊆ Y)
    (hq : Δ.IsQuasiatomic A Y) :
    Nonempty (Iso (factorOf Δ Y) (factorOf Δ A)) ∧
      Nonempty (Iso (factorOf Δ (Δ.Vs \ Y)) (factorOf Δ (Δ.Vs \ A))) := by
  have hcl := hG.closed Δ hΔ
  have hcub := hG.cubic Δ hΔ
  have hg := hG.girth Δ hΔ
  obtain ⟨q⟩ := quasiData hcl hcub hg hY hAY hq
  obtain ⟨v₁, v₂, f, a₁, a₂, l₁, l₂, hv, hv₁A, hv₂A, hYeq, hfE, hfj, ha₁, ha₂, ha₁v, ha₂v, hl₁, hl₂,
    hl₁v, hl₂v, hat₁, hat₂, hfa₁, hfl₁, hal₁, hfa₂, hfl₂, hal₂⟩ := q
  have hYV : Y ⊆ Δ.Vs := hY.1
  have hAV : A ⊆ Δ.Vs := hA.1.1
  have hv₁Y : v₁ ∈ Y := by rw [hYeq]; exact Finset.mem_insert_self _ _
  have hv₂Y : v₂ ∈ Y := by rw [hYeq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hv₁V := hYV hv₁Y
  have hv₂V := hYV hv₂Y
  have hAc := cycSep_compl hcl hA.1
  have hYc := cycSep_compl hcl hY
  have hVA : Δ.Vs \ A ⊆ Δ.Vs := Finset.sdiff_subset
  have hXW' : Δ.Vs \ Y ⊆ Δ.Vs \ A := fun v hv ↦
    Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hv).1, fun h ↦ (Finset.mem_sdiff.mp hv).2 (hAY h)⟩
  obtain ⟨hPY, hPYc, mY, hcY⟩ := factor_cases hG hΔ hY
  obtain ⟨hPA, hPAc, mA, hcA⟩ := factor_cases hG hΔ hA.1
  have hcolA := hG.pole_colourable Δ hΔ A hA.1
  have hcolYc := hG.pole_colourable Δ hΔ _ hYc
  have hbdA : Δ.bd (Δ.Vs \ A) = Δ.bd A := bd_compl hcl A
  have hbdY : Δ.bd (Δ.Vs \ Y) = Δ.bd Y := bd_compl hcl Y
  -- inner ends
  obtain ⟨i₁, hi₁⟩ := hl₁v
  obtain ⟨i₂, hi₂⟩ := hl₂v
  have hil₁ : innerEnd hPY l₁ = v₁ := (innerEnd_eq_of_end hPY hl₁ (hi₁ ▸ hv₁Y)).trans hi₁
  have hil₂ : innerEnd hPY l₂ = v₂ := (innerEnd_eq_of_end hPY hl₂ (hi₂ ▸ hv₂Y)).trans hi₂
  have hl₁o : Δ.ends l₁ (Fin.rev i₁) ∉ Y := other_end_notMem hl₁ (hi₁ ▸ hv₁Y)
  have hl₂o : Δ.ends l₂ (Fin.rev i₂) ∉ Y := other_end_notMem hl₂ (hi₂ ▸ hv₂Y)
  have hl₁l₂ : l₁ ≠ l₂ := by
    intro h
    have := hil₁
    rw [h, hil₂] at this
    exact hv this.symm
  have hfY : f ∈ Δ.edgesIn Y := by
    refine mem_edgesIn.mpr ⟨hfE, fun i ↦ ?_⟩
    rcases hfj.end_eq i with h | h <;> rw [h] <;> assumption
  have hfAc : f ∈ Δ.edgesIn (Δ.Vs \ A) := by
    refine mem_edgesIn.mpr ⟨hfE, fun i ↦ ?_⟩
    rcases hfj.end_eq i with h | h <;> rw [h]
    · exact Finset.mem_sdiff.mpr ⟨hv₁V, hv₁A⟩
    · exact Finset.mem_sdiff.mpr ⟨hv₂V, hv₂A⟩
  -- the other ends of `a₁`, `a₂` lie in `A`
  have bd_other : ∀ a ∈ Δ.bd A, ∀ i, Δ.ends a i ∉ A → Δ.ends a (Fin.rev i) ∈ A := by
    intro a ha i hi
    rw [mem_bd] at ha
    have h1 : i = 0 ∨ i = 1 := by omega
    rcases h1 with rfl | rfl
    · rw [Iso.rev_zero']; by_contra h; exact ha.2 ⟨fun h' ↦ absurd h' hi, fun h' ↦ absurd h' h⟩
    · rw [Iso.rev_one']; by_contra h; exact ha.2 ⟨fun h' ↦ absurd h' h, fun h' ↦ absurd h' hi⟩
  obtain ⟨j₁, hj₁⟩ := ha₁v
  obtain ⟨j₂, hj₂⟩ := ha₂v
  have ha₁o : Δ.ends a₁ (Fin.rev j₁) ∈ A := bd_other a₁ ha₁ j₁ (hj₁ ▸ hv₁A)
  have ha₂o : Δ.ends a₂ (Fin.rev j₂) ∈ A := bd_other a₂ ha₂ j₂ (hj₂ ▸ hv₂A)
  have hia₁ : innerEnd hPAc a₁ = v₁ :=
    (innerEnd_eq_of_end hPAc (hbdA ▸ ha₁) (hj₁ ▸ Finset.mem_sdiff.mpr ⟨hv₁V, hv₁A⟩)).trans hj₁
  have hia₂ : innerEnd hPAc a₂ = v₂ :=
    (innerEnd_eq_of_end hPAc (hbdA ▸ ha₂) (hj₂ ▸ Finset.mem_sdiff.mpr ⟨hv₂V, hv₂A⟩)).trans hj₂
  have ha₁a₂ : a₁ ≠ a₂ := by
    intro h
    have := hia₁
    rw [h, hia₂] at this
    exact hv this.symm
  -- `∂Y` and `∂A` as boundaries of the complements, for the second application
  have hl₁' : l₁ ∈ Δ.bd (Δ.Vs \ Y) := hbdY ▸ hl₁
  have hl₂' : l₂ ∈ Δ.bd (Δ.Vs \ Y) := hbdY ▸ hl₂
  have ha₁' : a₁ ∈ Δ.bd (Δ.Vs \ A) := hbdA ▸ ha₁
  have ha₂' : a₂ ∈ Δ.bd (Δ.Vs \ A) := hbdA ▸ ha₂
  have hVAeq : Δ.Vs \ A = insert v₁ (insert v₂ (Δ.Vs \ Y)) := by
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_insert]
    constructor
    · rintro ⟨hvV, hvA⟩
      by_cases hvY : v ∈ Y
      · rw [hYeq, Finset.mem_insert, Finset.mem_insert] at hvY
        rcases hvY with rfl | rfl | h
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact absurd h hvA
      · exact Or.inr (Or.inr ⟨hvV, hvY⟩)
    · rintro (rfl | rfl | ⟨hvV, hvY⟩)
      · exact ⟨hv₁V, hv₁A⟩
      · exact ⟨hv₂V, hv₂A⟩
      · exact ⟨hvV, fun h ↦ hvY (hAY h)⟩
  have hv₁Yc : v₁ ∉ Δ.Vs \ Y := fun h ↦ (Finset.mem_sdiff.mp h).2 hv₁Y
  have hv₂Yc : v₂ ∉ Δ.Vs \ Y := fun h ↦ (Finset.mem_sdiff.mp h).2 hv₂Y
  -- (a) the pole of `Y` is heterochromatic
  rcases hcY with ⟨hisoY, -, -, hcapY, -, -⟩ | ⟨hhetY, hisoYc, hY3, hY4, hY5, hY6⟩
  · exfalso
    exact cap_short_cycle hPY mY hl₁ hl₂ hl₁l₂ hv hil₁ hil₂ hfY hfj (hG.girth _ hcapY)
  -- (b) no couple of the `Y`-cut lies inside `∂A`
  have hgJ := hG.girth _ hY4
  have hnoY : ∀ k, bdEmb hPY k ∈ Δ.bd A → bdEmb hPY (pairing mY k) ∈ Δ.bd A → False := by
    intro k h1 h2
    have hd : bdEmb hPY k ∈ (Δ.pole Y).dangling := bdEmb_mem hPY k
    have hl₁A : l₁ ∉ Δ.bd A := by
      rw [mem_bd]; rintro ⟨-, h⟩
      have h1' : Δ.ends l₁ i₁ ∉ A := hi₁ ▸ hv₁A
      have h2' : Δ.ends l₁ (Fin.rev i₁) ∉ A := fun h' ↦ hl₁o (hAY h')
      have hi0 : i₁ = 0 ∨ i₁ = 1 := by omega
      rcases hi0 with rfl | rfl
      · rw [Iso.rev_zero'] at h2'; exact h ⟨fun h' ↦ absurd h' h1', fun h' ↦ absurd h' h2'⟩
      · rw [Iso.rev_one'] at h2'; exact h ⟨fun h' ↦ absurd h' h2', fun h' ↦ absurd h' h1'⟩
    have hl₂A : l₂ ∉ Δ.bd A := by
      rw [mem_bd]; rintro ⟨-, h⟩
      have h1' : Δ.ends l₂ i₂ ∉ A := hi₂ ▸ hv₂A
      have h2' : Δ.ends l₂ (Fin.rev i₂) ∉ A := fun h' ↦ hl₂o (hAY h')
      have hi0 : i₂ = 0 ∨ i₂ = 1 := by omega
      rcases hi0 with rfl | rfl
      · rw [Iso.rev_zero'] at h2'; exact h ⟨fun h' ↦ absurd h' h1', fun h' ↦ absurd h' h2'⟩
      · rw [Iso.rev_one'] at h2'; exact h ⟨fun h' ↦ absurd h' h2', fun h' ↦ absurd h' h1'⟩
    have hl₁d : l₁ ∈ (Δ.pole Y).dangling := dangling_pole Y ▸ hl₁
    have hl₂d : l₂ ∈ (Δ.pole Y).dangling := dangling_pole Y ▸ hl₂
    have hne1 : l₁ ≠ bdEmb hPY k := fun h ↦ hl₁A (h ▸ h1)
    have hne2 : l₁ ≠ partner hPY mY (bdEmb hPY k) := by
      rw [partner_bdEmb]; exact fun h ↦ hl₁A (h ▸ h2)
    have hfour := dangling_eq_four hPY mY hd hl₁d hne1 hne2
    have hl₂mem := hl₂d
    rw [hfour, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton,
      partner_bdEmb] at hl₂mem
    rcases hl₂mem with h | h | h | h
    · exact hl₂A (h ▸ h1)
    · exact hl₂A (h ▸ h2)
    · exact hl₁l₂ h.symm
    · exact join_parallel hPY mY hl₁ hl₁l₂ hv hil₁ hil₂ hfY hfj h.symm hgJ
  -- (c) the join along `Y` is a cap along `A`
  have hfjY : Δ.Joins f v₁ v₂ := hfj
  obtain ⟨m₀, ⟨J₁⟩⟩ := join_is_cap hAY hYV hv hv₁A hv₂A hYeq hfE hfjY ha₁ ⟨j₁, hj₁⟩ ha₂ ⟨j₂, hj₂⟩
    hl₁ ⟨i₁, hi₁⟩ hl₂ ⟨i₂, hi₂⟩ hat₁ hat₂ hPY mY hPA hnoY
  -- the cap along `A` is uncolourable, so the pole of `A` is isochromatic with pairing `m₀`
  have hncA : ¬ (cap hPA m₀).Colourable := fun h ↦ hG.snark _ hY4 (J₁.colourable_iff.mpr h)
  have hisoA₀ : IsoWith hPA m₀ := isoWith_of_cap_not_colourable hPA m₀ hncA
  rcases hcA with ⟨hisoA, hhetAc, hA3, hA4, hA5, hA6⟩ | ⟨hhetA, -, -, -, -, -⟩
  swap
  · exact absurd hisoA₀ (fun h ↦ not_isoWith_hetWith hPA hcolA h hhetA)
  have hmA : mA = m₀ := IsoWith.unique hPA hcolA hisoA hisoA₀
  refine ⟨?_, ?_⟩
  · rw [hY3, hA3, hmA]; exact ⟨J₁⟩
  -- (d) the join along `Δ.Vs \ A` is a cap along `Δ.Vs \ Y`
  have hgJA := hG.girth _ hA6
  have hnoA : ∀ k, bdEmb hPAc k ∈ Δ.bd (Δ.Vs \ Y) →
      bdEmb hPAc (pairing mA k) ∈ Δ.bd (Δ.Vs \ Y) → False := by
    intro k h1 h2
    rw [hbdY] at h1 h2
    have hd : bdEmb hPAc k ∈ (Δ.pole (Δ.Vs \ A)).dangling := bdEmb_mem hPAc k
    have ha₁Y : a₁ ∉ Δ.bd Y := by
      rw [mem_bd]; rintro ⟨-, h⟩
      have h1' : Δ.ends a₁ j₁ ∈ Y := hj₁ ▸ hv₁Y
      have h2' : Δ.ends a₁ (Fin.rev j₁) ∈ Y := hAY ha₁o
      have hi0 : j₁ = 0 ∨ j₁ = 1 := by omega
      rcases hi0 with rfl | rfl
      · rw [Iso.rev_zero'] at h2'; exact h ⟨fun _ ↦ h2', fun _ ↦ h1'⟩
      · rw [Iso.rev_one'] at h2'; exact h ⟨fun _ ↦ h1', fun _ ↦ h2'⟩
    have ha₂Y : a₂ ∉ Δ.bd Y := by
      rw [mem_bd]; rintro ⟨-, h⟩
      have h1' : Δ.ends a₂ j₂ ∈ Y := hj₂ ▸ hv₂Y
      have h2' : Δ.ends a₂ (Fin.rev j₂) ∈ Y := hAY ha₂o
      have hi0 : j₂ = 0 ∨ j₂ = 1 := by omega
      rcases hi0 with rfl | rfl
      · rw [Iso.rev_zero'] at h2'; exact h ⟨fun _ ↦ h2', fun _ ↦ h1'⟩
      · rw [Iso.rev_one'] at h2'; exact h ⟨fun _ ↦ h1', fun _ ↦ h2'⟩
    have ha₁d : a₁ ∈ (Δ.pole (Δ.Vs \ A)).dangling := dangling_pole _ ▸ ha₁'
    have ha₂d : a₂ ∈ (Δ.pole (Δ.Vs \ A)).dangling := dangling_pole _ ▸ ha₂'
    have hne1 : a₁ ≠ bdEmb hPAc k := fun h ↦ ha₁Y (h ▸ h1)
    have hne2 : a₁ ≠ partner hPAc mA (bdEmb hPAc k) := by
      rw [partner_bdEmb]; exact fun h ↦ ha₁Y (h ▸ h2)
    have hfour := dangling_eq_four hPAc mA hd ha₁d hne1 hne2
    have ha₂mem := ha₂d
    rw [hfour, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton,
      partner_bdEmb] at ha₂mem
    rcases ha₂mem with h | h | h | h
    · exact ha₂Y (h ▸ h1)
    · exact ha₂Y (h ▸ h2)
    · exact ha₁a₂ h.symm
    · exact join_parallel hPAc mA ha₁' ha₁a₂ hv hia₁ hia₂ hfAc hfj h.symm hgJA
  have hat₁' : ∀ e ∈ Δ.Es, ∀ i, Δ.ends e i = v₁ → e = f ∨ e = l₁ ∨ e = a₁ := by
    intro e he i hi
    rcases hat₁ e he i hi with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  have hat₂' : ∀ e ∈ Δ.Es, ∀ i, Δ.ends e i = v₂ → e = f ∨ e = l₂ ∨ e = a₂ := by
    intro e he i hi
    rcases hat₂ e he i hi with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  obtain ⟨m₁, ⟨J₂⟩⟩ := join_is_cap hXW' hVA hv hv₁Yc hv₂Yc hVAeq hfE hfjY hl₁' ⟨i₁, hi₁⟩ hl₂'
    ⟨i₂, hi₂⟩ ha₁' ⟨j₁, hj₁⟩ ha₂' ⟨j₂, hj₂⟩ hat₁' hat₂' hPAc mA hPYc hnoA
  have hncY : ¬ (cap hPYc m₁).Colourable := fun h ↦ hG.snark _ hA6 (J₂.colourable_iff.mpr h)
  have hisoYc₁ : IsoWith hPYc m₁ := isoWith_of_cap_not_colourable hPYc m₁ hncY
  have hmY : mY = m₁ := IsoWith.unique hPYc hcolYc hisoYc hisoYc₁
  rw [hY5, hA5, hmY]
  exact ⟨J₂.symm⟩

end Class

end FinGraph
end GraphPuzzles
