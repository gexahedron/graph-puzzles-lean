import GraphPuzzles.Reduction.Removable.DoubletonBipartite

/-! The removable-doubleton case of the Campos--Lucchesi proof. -/

namespace GraphPuzzles.LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- In a near-brick contraction with a removable doubleton, a perfect matching
of the original graph crosses the contraction cut at most three times. -/
theorem IsPerfectMatching.crossing_le_three_of_removableDoubleton
    {X : Finset V} (hn : (H.contract X).IsNearBrick) {e f : H.meets X}
    (hd : (H.contract X).IsRemovableDoubleton e f)
    {M : Finset E} (hM : H.IsPerfectMatching M) :
    (M ∩ H.dangling X).card ≤ 3 := by
  let K := H.contract X
  obtain ⟨c, he0, he1, hf0, hf1, hc⟩ := hd.exists_bipartition hn
  let p : Option X → ℚ := fun v ↦ if c v then 1 else -1
  let x : H.meets X → ℚ := fun g ↦ matchingVector M g.1
  obtain ⟨P, hP⟩ := hd.matchingCovered.exists_perfectMatching_of_ne (hn.matchingCovered.loopless e)
  have hz : (∑ v, p v) = 0 := by
    apply hP.on_univ.signed_sum_zero c
    intro g _
    have hg := g.2
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton, not_or] at hg
    exact hc g.1 hg.1 hg.2
  have hs (v : X) : K.weightedDegree x (some v) = 1 :=
    (contract_weightedDegree_some X (matchingVector M) v).trans (hM.isFractional.degree v.1)
  have hpole : K.weightedDegree x none = ((M ∩ H.dangling X).card : ℚ) := by
    rw [contract_weightedDegree_none, cutWeight_matchingVector]
  have hleft : (∑ v, p v * K.weightedDegree x v) =
      p none * (((M ∩ H.dangling X).card : ℚ) - 1) := by
    calc
      _ = (∑ v, p v) + ∑ v, p v * (K.weightedDegree x v - 1) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro v _
        ring
      _ = p none * (K.weightedDegree x none - 1) := by
        rw [hz, zero_add]
        apply Finset.sum_eq_single none
        · intro v _ hv
          cases v with
          | none => exact (hv rfl).elim
          | some v => rw [hs v]; ring
        · simp
      _ = _ := by rw [hpole]
  have hedge (g : H.meets X) : p (K.endAt g 0) + p (K.endAt g 1) =
      (if g = e then (2 : ℚ) else 0) - (if g = f then (2 : ℚ) else 0) := by
    by_cases hge : g = e
    · subst g
      norm_num [p, he0, he1, hd.ne, K]
    by_cases hgf : g = f
    · subst g
      norm_num [p, hf0, hf1, hd.ne.symm, K]
    have hh : c (K.endAt g 0) ≠ c (K.endAt g 1) := hc g hge hgf
    cases h0 : c (K.endAt g 0) <;> cases h1 : c (K.endAt g 1) <;>
      simp_all [p]
  have hright : (∑ g, x g * (p (K.endAt g 0) + p (K.endAt g 1))) =
      2 * x e - 2 * x f := by
    simp only [hedge, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero]
    simp [mul_comm]
  have hh := sum_vertexWeight_degree (H := K) p x
  rw [hleft, hright] at hh
  have hle : ((M ∩ H.dangling X).card : ℚ) ≤ 3 := by
    by_cases heM : e.1 ∈ M <;> by_cases hfM : f.1 ∈ M <;>
      cases hn : c none <;> simp [p, x, matchingVector, heM, hfM, hn] at hh <;> linarith
  exact_mod_cast hle

/-- Campos--Lucchesi Section 6, Case 5: a removable doubleton in a robust-cut
contraction supplies a perfect matching crossing the cut exactly three times. -/
theorem IsRobustCut.exists_three_crossing_of_removableDoubleton
    {X : Finset V} (hr : H.IsRobustCut X) (hm : H.IsMatchingCovered)
    {e f : H.meets X} (hd : (H.contract X).IsRemovableDoubleton e f) :
    ∃ M, H.IsPerfectMatching M ∧ (M ∩ H.dangling X).card = 3 := by
  obtain ⟨M, hM, hgt⟩ := hr.isSeparatingCut.exists_crossing_gt_one hm.1
    (hr.nontrivial hm) hr.notTight
  have hle := hM.crossing_le_three_of_removableDoubleton hr.leftNear hd
  have ho := hr.isSeparatingCut.odd_shore hm.1 (hr.nontrivial hm)
  have hpar := hM.crossing_mod_two X
  rw [Nat.odd_iff] at ho
  exact ⟨M, hM, by omega⟩

/-- The same case applies when the removable doubleton is in the other
contraction of the robust cut. -/
theorem IsRobustCut.exists_three_crossing_of_removableDoubleton_compl
    {X : Finset V} (hr : H.IsRobustCut X) (hm : H.IsMatchingCovered)
    {e f : H.meets (Finset.univ \ X)}
    (hd : (H.contract (Finset.univ \ X)).IsRemovableDoubleton e f) :
    ∃ M, H.IsPerfectMatching M ∧ (M ∩ H.dangling X).card = 3 := by
  have hc : H.IsRobustCut (Finset.univ \ X) := by
    refine ⟨?_, hr.rightNear, ?_⟩
    · simpa only [IsTightCut, dangling_compl] using hr.notTight
    · rw [Finset.sdiff_sdiff_eq_self (Finset.subset_univ X)]
      exact hr.leftNear
  simpa only [dangling_compl] using hc.exists_three_crossing_of_removableDoubleton hm hd

end GraphPuzzles.LoopMultigraph
