import GraphPuzzles.Matching.Fractional.FractionalContraction

/-! Linear identities and finite bounds used in the matching-polytope induction. -/

namespace GraphPuzzles.LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

section Arithmetic
omit [DecidableEq E]

theorem weightedDegree_sub (x y : E → ℚ) (v : V) :
    H.weightedDegree (fun e ↦ x e - y e) v = H.weightedDegree x v - H.weightedDegree y v := by
  unfold weightedDegree
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp

theorem weightedDegree_mul (a : ℚ) (x : E → ℚ) (v : V) :
    H.weightedDegree (fun e ↦ a * x e) v = a * H.weightedDegree x v := by
  unfold weightedDegree
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp

theorem weightedDegree_div (x : E → ℚ) (a : ℚ) (v : V) :
    H.weightedDegree (fun e ↦ x e / a) v = H.weightedDegree x v / a := by
  simpa only [div_eq_mul_inv, mul_comm] using weightedDegree_mul (H := H) a⁻¹ x v

theorem cutWeight_sub (x y : E → ℚ) (X : Finset V) :
    H.cutWeight (fun e ↦ x e - y e) X = H.cutWeight x X - H.cutWeight y X :=
  Finset.sum_sub_distrib ..

theorem cutWeight_mul (a : ℚ) (x : E → ℚ) (X : Finset V) :
    H.cutWeight (fun e ↦ a * x e) X = a * H.cutWeight x X :=
  (Finset.mul_sum ..).symm

theorem cutWeight_div (x : E → ℚ) (a : ℚ) (X : Finset V) :
    H.cutWeight (fun e ↦ x e / a) X = H.cutWeight x X / a := by
  simpa only [div_eq_mul_inv, mul_comm] using cutWeight_mul (H := H) a⁻¹ x X

theorem le_weightedDegree {x : E → ℚ} (hx : ∀ e, 0 ≤ x e) (e : E) (k : Fin 2) :
    x e ≤ H.weightedDegree x (H.endAt e k) := by
  have hn (f : E) (j : Fin 2) : 0 ≤ if H.endAt f j = H.endAt e k then x f else 0 :=
    by split_ifs; exact hx f; exact le_refl _
  calc
    x e = (if H.endAt e k = H.endAt e k then x e else 0) := by simp
    _ ≤ ∑ j : Fin 2, if H.endAt e j = H.endAt e k then x e else 0 :=
      Finset.single_le_sum (fun j _ ↦ hn e j) (Finset.mem_univ k)
    _ ≤ H.weightedDegree x (H.endAt e k) :=
      Finset.single_le_sum (fun f _ ↦ Finset.sum_nonneg fun j _ ↦ hn f j) (Finset.mem_univ e)

theorem eq_of_le_of_weightedDegree_eq {x y : E → ℚ} (hxy : ∀ e, y e ≤ x e)
    (hd : ∀ v, H.weightedDegree x v = H.weightedDegree y v) : x = y := by
  funext e
  have hh := le_weightedDegree (H := H) (fun e ↦ sub_nonneg.mpr (hxy e)) e 0
  rw [weightedDegree_sub, hd, sub_self] at hh
  linarith [hxy e]

theorem cutWeight_compl (x : E → ℚ) (X : Finset V) :
    H.cutWeight x (Finset.univ \ X) = H.cutWeight x X := by
  simp only [cutWeight, dangling_compl]

theorem IsFractionalPerfectMatching.card_even {x : E → ℚ}
    (hx : H.IsFractionalPerfectMatching x) : Even (Fintype.card V) := by
  by_contra hn
  have ho : Odd (Finset.univ : Finset V).card := by
    simpa only [Finset.card_univ] using Nat.not_even_iff_odd.mp hn
  have hh := hx.odd_cut _ ho
  have he : H.dangling Finset.univ = ∅ := by ext e; simp [dangling]
  simp only [cutWeight, he, Finset.sum_empty] at hh
  norm_num at hh

theorem IsFractionalPerfectMatching.odd_compl {x : E → ℚ}
    (hx : H.IsFractionalPerfectMatching x) {X : Finset V} (hX : Odd X.card) :
    Odd (Finset.univ \ X).card := by
  have hn := hx.card_even
  have hle := Finset.card_le_univ X
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
  rw [Nat.even_iff] at hn
  rw [Nat.odd_iff] at hX ⊢
  omega

end Arithmetic

theorem IsPerfectMatching.crossing_le_card {M : Finset E} (hM : H.IsPerfectMatching M)
    (X : Finset V) : (M ∩ H.dangling X).card ≤ X.card := by
  have h := cutWeight_le_sum_weightedDegree (H := H) hM.isFractional.nonneg X
  simp only [cutWeight_matchingVector, hM.isFractional.degree, Finset.sum_const,
    nsmul_eq_mul, mul_one] at h
  exact_mod_cast h

theorem IsPerfectMatching.nontrivial_of_crossing_gt_one {M : Finset E}
    (hM : H.IsPerfectMatching M) {X : Finset V} (hX : 1 < (M ∩ H.dangling X).card) :
    IsNontrivialCut X := by
  have h1 := hM.crossing_le_card X
  have h2 := hM.crossing_le_card (Finset.univ \ X)
  rw [dangling_compl] at h2
  exact ⟨by omega, by omega⟩

end GraphPuzzles.LoopMultigraph
