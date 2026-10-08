import GraphPuzzles.Cuts.CutUncrossing

/-! Fractional matching faces and the matchings supporting them. -/

namespace GraphPuzzles.LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

omit [DecidableEq E] in
theorem weightedDegree_family {I : Type*} [Fintype I] (w : I → ℚ) (f : I → E → ℚ) (v : V) :
    H.weightedDegree (fun e ↦ ∑ i, w i * f i e) v = ∑ i, w i * H.weightedDegree (f i) v := by
  have hite (p : Prop) [Decidable p] (g : I → ℚ) :
      (if p then ∑ i, g i else 0) = ∑ i, if p then g i else 0 := by
    by_cases hp : p <;> simp [hp]
  unfold weightedDegree
  simp_rw [hite]
  calc
    _ = ∑ e, ∑ i, ∑ k : Fin 2, if H.endAt e k = v then w i * f i e else 0 := by
      apply Finset.sum_congr rfl
      intro e _
      exact Finset.sum_comm
    _ = ∑ i, ∑ e, ∑ k : Fin 2, if H.endAt e k = v then w i * f i e else 0 := Finset.sum_comm
    _ = _ := by
      simp only [Finset.mul_sum, mul_ite, mul_zero]

omit [DecidableEq E] in
theorem cutWeight_family {I : Type*} [Fintype I] (w : I → ℚ) (f : I → E → ℚ) (X : Finset V) :
    H.cutWeight (fun e ↦ ∑ i, w i * f i e) X = ∑ i, w i * H.cutWeight (f i) X := by
  unfold cutWeight
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

namespace MatchingCombination

variable {x : E → ℚ} (C : H.MatchingCombination x)

include C

/-- Convex combinations satisfy all the fractional constraints. -/
theorem isFractional : H.IsFractionalPerfectMatching x := by
  have hrep : x = fun e ↦ ∑ M : C.support, C.weight M.1 * matchingVector M.1 e :=
    funext fun e ↦ (C.support_marginal e).symm
  refine ⟨?_, ?_, ?_⟩
  · intro e
    rw [hrep]
    exact Finset.sum_nonneg fun M _ ↦
      mul_nonneg (C.nonneg M.1) ((C.support_valid M).isFractional.nonneg e)
  · intro v
    rw [hrep, weightedDegree_family]
    have hh (M : C.support) : H.weightedDegree (matchingVector M.1) v = 1 :=
      (C.support_valid M).isFractional.degree v
    simp only [hh, mul_one]
    exact C.support_total
  · intro X hX
    rw [hrep, cutWeight_family]
    calc
      1 = ∑ M : C.support, C.weight M.1 * 1 := by simpa using C.support_total.symm
      _ ≤ _ := Finset.sum_le_sum fun M _ ↦
        mul_le_mul_of_nonneg_left ((C.support_valid M).isFractional.odd_cut X hX) (C.nonneg _)

/-- A positive edge belongs to a matching receiving positive mass. -/
theorem exists_support_containing {e : E} (he : 0 < x e) :
    ∃ M : C.support, e ∈ M.1 := by
  have hs : 0 < ∑ M : C.support, C.weight M.1 * matchingVector M.1 e := by
    rw [C.support_marginal]
    exact he
  obtain ⟨M, _, hm⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun M _ ↦ mul_nonneg (C.nonneg M.1) ((C.support_valid M).isFractional.nonneg e))).mp hs
  refine ⟨M, ?_⟩
  by_contra hn
  simp [matchingVector, hn] at hm

/-- Equality in an odd-cut inequality forces every supported matching to cross once. -/
theorem support_crossing_one {X : Finset V} (hX : Odd X.card) (ht : H.cutWeight x X = 1)
    (M : C.support) : (M.1 ∩ H.dangling X).card = 1 := by
  have hrep : x = fun e ↦ ∑ N : C.support, C.weight N.1 * matchingVector N.1 e :=
    funext fun e ↦ (C.support_marginal e).symm
  have hn (N : C.support) : (0 : ℚ) ≤ C.weight N.1 * (H.cutWeight (matchingVector N.1) X - 1) :=
    mul_nonneg (C.nonneg _) (sub_nonneg.mpr ((C.support_valid N).isFractional.odd_cut X hX))
  have hz : (∑ N : C.support, C.weight N.1 * (H.cutWeight (matchingVector N.1) X - 1)) = 0 := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
    rw [← cutWeight_family, ← hrep, ht, C.support_total, sub_self]
  have heq := (Finset.sum_eq_zero_iff_of_nonneg (fun N _ ↦ hn N)).mp hz M (Finset.mem_univ _)
  have hw : C.weight M.1 ≠ 0 := ne_of_gt (C.support_positive M)
  have hc := sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_left hw)
  rw [cutWeight_matchingVector] at hc
  exact_mod_cast hc

end MatchingCombination
end GraphPuzzles.LoopMultigraph
