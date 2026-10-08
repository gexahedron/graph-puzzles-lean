import GraphPuzzles.Matching.MatchingHub

/-!
# Fractional perfect matchings

The degree equations and odd-cut inequalities in Edmonds' perfect matching polytope.
Weights are rational; incidences are counted separately, as in the endpoint graph model.
This module supplies the weighted counting infrastructure for the polytope proof.
-/

namespace GraphPuzzles.LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- The sum of edge weights at a vertex, counting both ends of a loop. -/
def weightedDegree (H : LoopMultigraph V E) (x : E → ℚ) (v : V) : ℚ :=
  ∑ e, ∑ k : Fin 2, if H.endAt e k = v then x e else 0

/-- The total weight of the edge boundary of a shore. -/
def cutWeight (H : LoopMultigraph V E) (x : E → ℚ) (X : Finset V) : ℚ :=
  ∑ e ∈ H.dangling X, x e

/-- The rational feasibility conditions for the perfect matching polytope. -/
structure IsFractionalPerfectMatching (H : LoopMultigraph V E) (x : E → ℚ) : Prop where
  nonneg : ∀ e, 0 ≤ x e
  degree : ∀ v, H.weightedDegree x v = 1
  odd_cut : ∀ X : Finset V, Odd X.card → 1 ≤ H.cutWeight x X

/-- An edge set as a rational incidence vector. -/
def matchingVector (M : Finset E) (e : E) : ℚ := if e ∈ M then 1 else 0

theorem weightedDegree_matchingVector (M : Finset E) (v : V) :
    H.weightedDegree (matchingVector M) v = H.degreeIn M v := by
  unfold weightedDegree degreeIn
  rw [Finset.card_filter, Finset.sum_product]
  push_cast
  calc
    _ = ∑ e, if e ∈ M then (∑ k : Fin 2, if H.endAt e k = v then (1 : ℚ) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro e _
      by_cases he : e ∈ M <;> simp [matchingVector, he]
    _ = _ := by rw [← Finset.sum_filter]; simp

theorem cutWeight_matchingVector (M : Finset E) (X : Finset V) :
    H.cutWeight (matchingVector M) X = (M ∩ H.dangling X).card := by
  simp only [cutWeight, matchingVector]
  rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_comm]

theorem weightedDegree_const (q : ℚ) (v : V) :
    H.weightedDegree (fun _ ↦ q) v = (H.degree v : ℚ) * q := by
  have h := weightedDegree_matchingVector (H := H) Finset.univ v
  have hv : matchingVector (Finset.univ : Finset E) = fun _ ↦ (1 : ℚ) := by
    funext e
    simp [matchingVector]
  rw [hv, degreeIn_univ'] at h
  rw [weightedDegree, ← h, weightedDegree, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp

omit [DecidableEq E] in
theorem cutWeight_const (q : ℚ) (X : Finset V) :
    H.cutWeight (fun _ ↦ q) X = ((H.dangling X).card : ℚ) * q := by
  simp [cutWeight]

/-- Every perfect matching satisfies the odd-cut inequalities. -/
theorem IsPerfectMatching.isFractional {M : Finset E} (hM : H.IsPerfectMatching M) :
    H.IsFractionalPerfectMatching (matchingVector M) := by
  refine ⟨fun e ↦ by unfold matchingVector; split_ifs <;> norm_num, ?_, ?_⟩
  · intro v
    rw [weightedDegree_matchingVector, hM v]
    norm_num
  · intro X hX
    have h := sum_degreeIn_mod_two (K := H) X M
    rw [Finset.sum_congr rfl (fun v _ ↦ hM v)] at h
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
    have hpos : 1 ≤ (M ∩ H.dangling X).card := by
      rw [Nat.odd_iff] at hX
      omega
    rw [cutWeight_matchingVector]
    exact_mod_cast hpos

/-- The all-`1/3` vector is feasible in every bridgeless cubic graph. -/
theorem isFractionalPerfectMatching_third (hc : ∀ v, H.degree v = 3)
    (hb : H.IsBridgeless) : H.IsFractionalPerfectMatching (fun _ ↦ 1 / 3) := by
  refine ⟨fun _ ↦ by norm_num, ?_, ?_⟩
  · intro v
    rw [weightedDegree_const, hc]
    norm_num
  · intro X hX
    have ho := odd_card_dangling (H := H) (fun v ↦ by rw [hc]; decide) hX
    have hn := card_dangling_ne_one hb X
    have h3 : 3 ≤ (H.dangling X).card := by rw [Nat.odd_iff] at ho; omega
    rw [cutWeight_const]
    have h3' : (3 : ℚ) ≤ (H.dangling X).card := by exact_mod_cast h3
    linarith

omit [DecidableEq E] in
/-- Weighted handshake on a shore. -/
theorem sum_weightedDegree (x : E → ℚ) (X : Finset V) :
    ∑ v ∈ X, H.weightedDegree x v = ∑ e, (H.endsIn X e : ℚ) * x e := by
  unfold weightedDegree
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_comm]
  unfold endsIn
  rw [Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : H.endAt e k ∈ X
  · simp [hk]
  · simp [hk]

theorem cutWeight_le_sum_weightedDegree {x : E → ℚ} (hx : ∀ e, 0 ≤ x e) (X : Finset V) :
    H.cutWeight x X ≤ ∑ v ∈ X, H.weightedDegree x v := by
  rw [sum_weightedDegree, cutWeight]
  calc
    _ ≤ ∑ e ∈ H.dangling X, (H.endsIn X e : ℚ) * x e := by
      apply Finset.sum_le_sum
      intro e he
      have hn : 1 ≤ H.endsIn X e := by
        have hm := endsIn_mod_two (K := H) X e
        rw [if_pos he] at hm
        omega
      have hn' : (1 : ℚ) ≤ H.endsIn X e := by exact_mod_cast hn
      simpa using mul_le_mul_of_nonneg_right hn' (hx e)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun e _ _ ↦ mul_nonneg (Nat.cast_nonneg _) (hx e))

end GraphPuzzles.LoopMultigraph
