import GraphPuzzles.Poles.PoleRotate
import GraphPuzzles.Poles.PoleColouring
import GraphPuzzles.Poles.PoleSuppression
import GraphPuzzles.Poles.PoleAlternating

/-!
# Theorem 3.1 of Karabáš–Máčajová for abstract poles

Every abstract Hamiltonian cubic `3`-pole has a proper four-cover.  The proof is the strong
induction of the paper on the number of vertices: a pole with three odd segments is covered by
Lemma 3.3 (`coverOfThreeOdd`); otherwise two segments are even and, after rotating the odd
segment into the middle, either one of the even segments has a unique exterior chord (Lemmas 3.4
and 3.5, `exists_cover_of_ext_T₀`), or both have at least three and Lemma 3.6
(`exists_altCycle_of_good`) provides an alternating cycle whose suppression is smaller; its
cover lifts back by Lemma 3.2 (`AltCycle.lift`).
-/

namespace GraphPuzzles
namespace Pole

/-- The normalized case: the segments `T₀` and `T₂` are even. -/
theorem exists_cover_normalized (P : Pole) (he₀ : Even P.s₂) (he₂ : Even (P.n - P.s₁))
    (ih : ∀ Q : Pole, Q.n < P.n → Nonempty Q.Cover) : Nonempty P.Cover := by
  have hodd₀ : P.ext P.T₀ % 2 = 1 := by
    rw [ext_mod_two (fun _ hp ↦ inner_of_mem_T₀ hp), card_T₀]
    obtain ⟨k, hk⟩ := he₀
    have := P.s₂_pos
    omega
  have hodd₂ : P.ext P.T₂ % 2 = 1 := by
    rw [ext_mod_two (fun _ hp ↦ inner_of_mem_T₂ hp), card_T₂]
    obtain ⟨k, hk⟩ := he₂
    have := P.s₁_lt_n
    omega
  by_cases h₀ : P.ext P.T₀ = 1
  · exact exists_cover_of_ext_T₀ he₀ h₀
  by_cases h₂ : P.ext P.T₂ = 1
  · have hs₂' : Even P.rotS₁.s₂ := by
      rw [rotS₁_s₂]
      exact he₂
    have hext' : P.rotS₁.ext P.rotS₁.T₀ = 1 := by
      rw [rotS₁_ext_T₀]
      exact h₂
    obtain ⟨C⟩ := exists_cover_of_ext_T₀ hs₂' hext'
    exact ⟨C.unrotS₁⟩
  have hgood : Good P := ⟨he₀, he₂, by omega, by omega⟩
  obtain ⟨A⟩ := exists_altCycle_of_good P.n P rfl hgood
  obtain ⟨C⟩ := ih A.suppress A.suppress_n_lt
  exact ⟨A.lift C⟩

/-- Theorem 3.1: every abstract Hamiltonian cubic `3`-pole has a proper four-cover. -/
theorem exists_cover : ∀ (n : ℕ) (P : Pole), P.n = n → Nonempty P.Cover := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro P hPn
    have ih' : ∀ Q : Pole, Q.n < P.n → Nonempty Q.Cover := fun Q hQ ↦ ih Q.n (hPn ▸ hQ) Q rfl
    have hodd := @n_odd P
    have hs := P.s₂_lt_s₁
    have hsn := P.s₁_lt_n
    obtain ⟨c, hc⟩ := hodd
    by_cases h₀ : Odd P.s₂
    · obtain ⟨a, ha⟩ := h₀
      by_cases h₁ : Odd (P.s₁ - P.s₂)
      · obtain ⟨b, hb⟩ := h₁
        have h₂ : Odd (P.n - P.s₁) := ⟨c - a - b - 1, by omega⟩
        exact ⟨coverOfThreeOdd ⟨a, ha⟩ ⟨b, hb⟩ h₂⟩
      · have he₁ : Even (P.s₁ - P.s₂) := Nat.not_odd_iff_even.mp h₁
        obtain ⟨b, hb⟩ := he₁
        obtain ⟨C⟩ := exists_cover_normalized P.rotS₁ (by rw [rotS₁_s₂]; exact ⟨c - a - b, by omega⟩)
          (by rw [rotS₁_n, rotS₁_s₁]; exact ⟨b, by omega⟩) (fun Q hQ ↦ ih' Q hQ)
        exact ⟨C.unrotS₁⟩
    · have he₀ : Even P.s₂ := Nat.not_odd_iff_even.mp h₀
      obtain ⟨a, ha⟩ := he₀
      by_cases h₂ : Odd (P.n - P.s₁)
      · obtain ⟨b, hb⟩ := h₂
        obtain ⟨C⟩ := exists_cover_normalized P.rotS₂ (by rw [rotS₂_s₂]; exact ⟨c - a - b, by omega⟩)
          (by rw [rotS₂_n, rotS₂_s₁]; exact ⟨a, by omega⟩) (fun Q hQ ↦ ih' Q hQ)
        exact ⟨C.unrotS₂⟩
      · have he₂ : Even (P.n - P.s₁) := Nat.not_odd_iff_even.mp h₂
        exact exists_cover_normalized P ⟨a, ha⟩ he₂ ih'

/-- Theorem 3.1, unbundled. -/
theorem exists_cover' (P : Pole) : Nonempty P.Cover := exists_cover P.n P rfl

end Pole
end GraphPuzzles
