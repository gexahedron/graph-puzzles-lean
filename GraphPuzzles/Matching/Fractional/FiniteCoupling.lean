import GraphPuzzles.Matching.Fractional.FractionalMatching

/-! A finite rational coupling of positive distributions with a common marginal. -/

namespace GraphPuzzles

open scoped BigOperators

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K] [DecidableEq K]

/-- A nonnegative matrix with the specified row and column sums. -/
structure FiniteCoupling (a : I → ℚ) (b : J → ℚ) where
  mass : I → J → ℚ
  nonneg : ∀ i j, 0 ≤ mass i j
  row : ∀ i, ∑ j, mass i j = a i
  column : ∀ j, ∑ i, mass i j = b j

omit [Fintype J] [Fintype K] in
theorem positive_marginal (a : I → ℚ) (f : I → K) (m : K → ℚ)
    (ha : ∀ i, 0 < a i) (hm : ∀ k, (∑ i, if f i = k then a i else 0) = m k) (i : I) :
    0 < m (f i) := by
  have hle := Finset.single_le_sum (s := Finset.univ) (f := fun j ↦ if f j = f i then a j else 0)
    (fun j _ ↦ by split_ifs; exact (ha j).le; exact le_refl _) (Finset.mem_univ i)
  have hle' : a i ≤ m (f i) := by simpa [hm] using hle
  exact (ha i).trans_le hle'

namespace FiniteCoupling

/-- Condition on the shared tag, then take the product of the two conditional distributions. -/
def ofCommonMarginal (a : I → ℚ) (b : J → ℚ) (f : I → K) (g : J → K) (m : K → ℚ)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j)
    (hfa : ∀ k, (∑ i, if f i = k then a i else 0) = m k)
    (hgb : ∀ k, (∑ j, if g j = k then b j else 0) = m k) : FiniteCoupling a b where
  mass i j := if f i = g j then a i * b j / m (f i) else 0
  nonneg i j := by
    split_ifs
    · exact div_nonneg (mul_nonneg (ha i).le (hb j).le) (positive_marginal a f m ha hfa i).le
    · exact le_refl _
  row i := by
    calc
      _ = (a i / m (f i)) * ∑ j, if g j = f i then b j else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        by_cases h : f i = g j
        · rw [if_pos h, if_pos h.symm]
          ring
        · rw [if_neg h, if_neg (Ne.symm h)]
          ring
      _ = a i := by rw [hgb]; exact div_mul_cancel₀ _ (ne_of_gt (positive_marginal a f m ha hfa i))
  column j := by
    calc
      _ = (b j / m (g j)) * ∑ i, if f i = g j then a i else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        by_cases h : f i = g j
        · rw [if_pos h, if_pos h, h]
          ring
        · rw [if_neg h, if_neg h]
          ring
      _ = b j := by rw [hfa]; exact div_mul_cancel₀ _ (ne_of_gt (positive_marginal b g m hb hgb j))

omit [Fintype K] in
theorem ofCommonMarginal_zero_of_ne (a : I → ℚ) (b : J → ℚ)
    (f : I → K) (g : J → K) (m : K → ℚ) (ha hb hfa hgb)
    {i : I} {j : J} (h : f i ≠ g j) :
    (ofCommonMarginal a b f g m ha hb hfa hgb).mass i j = 0 := if_neg h

end FiniteCoupling
end GraphPuzzles
