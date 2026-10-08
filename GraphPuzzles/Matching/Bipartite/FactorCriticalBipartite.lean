import GraphPuzzles.Cuts.Contraction.BipartiteContraction
import GraphPuzzles.Matching.Barriers.MaximalBarrier
import GraphPuzzles.Matching.MatchingOn

/-! A factor-critical bipartite shore contains at most one vertex. -/

namespace GraphPuzzles.LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- The two colour classes of a perfectly matched bipartite shore have equal size,
expressed as a signed sum. -/
theorem IsPerfectMatchingOn.signed_sum_zero {S : Finset V} {P : Finset E}
    (hP : H.IsPerfectMatchingOn S P) (c : V → Bool)
    (hc : ∀ e ∈ P, c (H.endAt e 0) ≠ c (H.endAt e 1)) :
    (∑ v ∈ S, if c v then (1 : ℚ) else -1) = 0 := by
  let p : V → ℚ := fun v ↦ if c v then 1 else -1
  have hh := sum_vertexWeight_degree (H := H) p (matchingVector P)
  have hd (v : V) : p v * H.weightedDegree (matchingVector P) v =
      if v ∈ S then p v else 0 := by
    rw [weightedDegree_matchingVector]
    by_cases hv : v ∈ S
    · simp [hP.2 v hv, hv]
    · simp [hP.degree_zero hv, hv]
  have he (e : E) : matchingVector P e * (p (H.endAt e 0) + p (H.endAt e 1)) = 0 := by
    by_cases he : e ∈ P
    · have hn := hc e he
      cases h0 : c (H.endAt e 0) <;> cases h1 : c (H.endAt e 1) <;>
        simp_all [p]
    · simp [matchingVector, he]
  simpa only [hd, he, Finset.sum_const_zero, ← Finset.sum_filter,
    Finset.filter_mem_eq_inter, Finset.univ_inter, p] using hh

/-- Campos--Lucchesi Lemma 2.9: a nontrivial factor-critical shore is nonbipartite. -/
theorem IsFactorCritical.card_le_one_of_bipartiteOn {Q : Finset V}
    (hf : H.IsFactorCritical Q) (hb : H.IsBipartiteOn Q) : Q.card ≤ 1 := by
  obtain ⟨c, hc⟩ := hb
  let p : V → ℚ := fun v ↦ if c v then 1 else -1
  have hs (w : V) (hw : w ∈ Q) : (∑ v ∈ Q, p v) = p w := by
    obtain ⟨P, hP⟩ := hf w hw
    have hz := hP.signed_sum_zero c (fun e he ↦ hc e
      (Finset.mem_of_mem_erase (hP.1 e he 0)) (Finset.mem_of_mem_erase (hP.1 e he 1)))
    have he := Finset.sum_erase_add Q p hw
    change (∑ v ∈ Q.erase w, p v) = 0 at hz
    rw [hz, zero_add] at he
    exact he.symm
  rcases Q.eq_empty_or_nonempty with rfl | ⟨w, hw⟩
  · simp
  · have he := hs w hw
    have hsum : (∑ v ∈ Q, p v) = (Q.card : ℚ) * p w := by
      calc
        _ = ∑ _v ∈ Q, p w := Finset.sum_congr rfl fun v hv ↦ (hs v hv).symm.trans he
        _ = _ := by simp
    have hcard : (Q.card : ℚ) = 1 := by
      cases hcw : c w <;> simp only [p, hcw, Bool.false_eq_true, if_false, if_true] at he hsum <;>
        linarith
    have hcQ : Q.card = 1 := by exact_mod_cast hcard
    omega

end GraphPuzzles.LoopMultigraph
