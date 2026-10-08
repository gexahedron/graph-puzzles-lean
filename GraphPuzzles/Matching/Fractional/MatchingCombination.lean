import GraphPuzzles.Matching.Fractional.FractionalMatching

/-! Rational convex combinations of perfect matching incidence vectors. -/

namespace GraphPuzzles.LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- A finite rational distribution on perfect matchings, with prescribed edge marginals. -/
structure MatchingCombination (H : LoopMultigraph V E) (x : E → ℚ) where
  weight : Finset E → ℚ
  nonneg : ∀ M, 0 ≤ weight M
  valid : ∀ M, weight M ≠ 0 → H.IsPerfectMatching M
  total : ∑ M, weight M = 1
  marginal : ∀ e, ∑ M, weight M * matchingVector M e = x e

namespace MatchingCombination

variable {x y : E → ℚ}

def support (C : H.MatchingCombination x) : Finset (Finset E) :=
  Finset.univ.filter fun M ↦ C.weight M ≠ 0

theorem mem_support (C : H.MatchingCombination x) (M : Finset E) :
    M ∈ C.support ↔ C.weight M ≠ 0 := by simp [support]

theorem support_positive (C : H.MatchingCombination x) (M : C.support) : 0 < C.weight M.1 :=
  lt_of_le_of_ne (C.nonneg _) ((C.mem_support _).mp M.2).symm

theorem support_valid (C : H.MatchingCombination x) (M : C.support) : H.IsPerfectMatching M.1 :=
  C.valid _ ((C.mem_support _).mp M.2)

theorem sum_support (C : H.MatchingCombination x) (f : Finset E → ℚ) :
    ∑ M : C.support, C.weight M.1 * f M.1 = ∑ M, C.weight M * f M := by
  rw [← Finset.sum_subtype C.support (fun _ ↦ Iff.rfl) (fun M ↦ C.weight M * f M)]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro M _ hM
  have hz : C.weight M = 0 := by simpa only [C.mem_support, not_not] using hM
  simp [hz]

theorem support_total (C : H.MatchingCombination x) : ∑ M : C.support, C.weight M.1 = 1 := by
  simpa using (C.sum_support (fun _ ↦ 1)).trans (by simpa using C.total)

theorem support_marginal (C : H.MatchingCombination x) (e : E) :
    ∑ M : C.support, C.weight M.1 * matchingVector M.1 e = x e :=
  (C.sum_support (matchingVector · e)).trans (C.marginal e)

/-- An arbitrary finite indexed family can be collected into a distribution on edge sets. -/
def ofFamily {I : Type*} [Fintype I] (M : I → Finset E) (w : I → ℚ)
    (hn : ∀ i, 0 ≤ w i) (hv : ∀ i, w i ≠ 0 → H.IsPerfectMatching (M i))
    (ht : ∑ i, w i = 1) (hm : ∀ e, ∑ i, w i * matchingVector (M i) e = x e) :
    H.MatchingCombination x where
  weight N := ∑ i, if M i = N then w i else 0
  nonneg N := Finset.sum_nonneg fun i _ ↦ by split_ifs; exact hn i; exact le_refl _
  valid N h := by
    by_contra hf
    apply h
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : M i = N
    · rw [if_pos hi]
      by_contra hnz
      exact hf (hi ▸ hv i hnz)
    · exact if_neg hi
  total := by
    rw [Finset.sum_comm]
    simpa using ht
  marginal e := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    convert hm e using 1
    apply Finset.sum_congr rfl
    intro i _
    simp [ite_mul]

/-- A single perfect matching has a point-mass representation. -/
def single {M : Finset E} (hM : H.IsPerfectMatching M) :
    H.MatchingCombination (matchingVector M) where
  weight N := if N = M then 1 else 0
  nonneg N := by split_ifs <;> norm_num
  valid N h := by
    by_cases hn : N = M
    · simpa [hn] using hM
    · exact (h (if_neg hn)).elim
  total := by simp
  marginal e := by simp

/-- Mixtures of distributions give the corresponding convex combinations of marginals. -/
def mix (C : H.MatchingCombination x) (D : H.MatchingCombination y)
    (a : ℚ) (ha : 0 ≤ a) (ha' : a ≤ 1) :
    H.MatchingCombination (fun e ↦ a * x e + (1 - a) * y e) where
  weight M := a * C.weight M + (1 - a) * D.weight M
  nonneg M := add_nonneg (mul_nonneg ha (C.nonneg M)) (mul_nonneg (sub_nonneg.mpr ha') (D.nonneg M))
  valid M h := by
    by_cases hc : C.weight M = 0
    · apply D.valid M
      intro hd
      simp [hc, hd] at h
    · exact C.valid M hc
  total := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, C.total, D.total]
    ring
  marginal e := by
    simp only [add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum,
      C.marginal, D.marginal]

/-- Any linear cut statistic is averaged by the same distribution. -/
theorem cutWeight (C : H.MatchingCombination x) (X : Finset V) :
    H.cutWeight x X = ∑ M, C.weight M * ((M ∩ H.dangling X).card : ℚ) := by
  unfold LoopMultigraph.cutWeight
  simp_rw [← C.marginal]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro M _
  rw [← Finset.mul_sum]
  exact congrArg (C.weight M * ·) (cutWeight_matchingVector M X)

/-- A tight cut has weight one under every convex combination of perfect matchings. -/
theorem tight_cut_weight (C : H.MatchingCombination x) (X : Finset V)
    (ht : ∀ M, H.IsPerfectMatching M → (M ∩ H.dangling X).card = 1) :
    H.cutWeight x X = 1 := by
  rw [C.cutWeight]
  calc
    _ = ∑ M, C.weight M := by
      apply Finset.sum_congr rfl
      intro M _
      by_cases hm : C.weight M = 0
      · simp [hm]
      · rw [ht M (C.valid M hm)]
        simp
    _ = 1 := C.total

/-- Once the all-`1/3` distribution is constructed, the cubic tight-cut count is immediate. -/
theorem card_tight_cut (C : H.MatchingCombination (fun _ ↦ 1 / 3)) (X : Finset V)
    (ht : ∀ M, H.IsPerfectMatching M → (M ∩ H.dangling X).card = 1) :
    (H.dangling X).card = 3 := by
  have h := C.tight_cut_weight X ht
  rw [cutWeight_const] at h
  have h' : ((H.dangling X).card : ℚ) = 3 := by linarith
  exact_mod_cast h'

end MatchingCombination
end GraphPuzzles.LoopMultigraph
