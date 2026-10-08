import GraphPuzzles.Matching.VertexMatching
import GraphPuzzles.Matching.Bipartite.TwoPoleBipartite

/-! Bipartite degree balance for the hub matchings in the odd-wheel theorem. -/

namespace GraphPuzzles.LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- In a bipartite graph admitting a perfect matching, a vertex matching
is itself a perfect matching. -/
theorem IsVertexMatching.isPerfectMatching_of_bipartite {v : V} {M P : Finset E}
    (hM : H.IsVertexMatching v M) (hb : H.IsBipartite) (hP : H.IsPerfectMatching P) :
    H.IsPerfectMatching M := by
  obtain ⟨c, hc⟩ := hb
  have hs := bipartite_sum_weightedDegree (H := H) c hc
    (fun e ↦ matchingVector M e - matchingVector P e)
  have hz : (∑ w, bipartiteSign c w * H.weightedDegree
      (fun e ↦ matchingVector M e - matchingVector P e) w) =
      bipartiteSign c v * ((H.degreeIn M v : ℚ) - 1) := by
    rw [Finset.sum_eq_single v]
    · rw [weightedDegree_sub, weightedDegree_matchingVector, hP.isFractional.degree]
    · intro w _ hw
      rw [weightedDegree_sub, weightedDegree_matchingVector,
        hM w hw, hP.isFractional.degree]
      norm_num
    · simp
  rw [hz] at hs
  have hv : H.degreeIn M v = 1 := by
    have hh : (H.degreeIn M v : ℚ) = 1 := by
      cases hcv : c v <;> simp [bipartiteSign, hcv] at hs <;> linarith
    exact_mod_cast hh
  intro w
  by_cases hw : w = v
  · simpa [hw] using hv
  · exact hM w hw

/-- With two exceptional vertices in a bipartite graph, their degrees
sum to two on the same side and are equal on opposite sides. -/
theorem bipartite_degreeIn_pair_balance {c : V → Bool}
    (hc : ∀ e, c (H.endAt e 0) ≠ c (H.endAt e 1)) {P M : Finset E}
    (hP : H.IsPerfectMatching P) {p q : V} (hpq : p ≠ q)
    (hd : ∀ w, w ≠ p → w ≠ q → H.degreeIn M w = 1) :
    (c p = c q → H.degreeIn M p + H.degreeIn M q = 2) ∧
      (c p ≠ c q → H.degreeIn M p = H.degreeIn M q) := by
  have hh := bipartite_two_vertex_balance (H := H) c hc hpq
    (matchingVector M) (matchingVector P) (fun w hwp hwq ↦ by
      rw [weightedDegree_matchingVector, hd w hwp hwq, hP.isFractional.degree]
      norm_num)
  simp only [weightedDegree_matchingVector, hP p, hP q] at hh
  constructor
  · intro he
    cases hp : c p <;> cases hq : c q <;>
      simp_all [bipartiteSign] <;> exact_mod_cast (by linarith :
        (H.degreeIn M p : ℚ) + H.degreeIn M q = 2)
  · intro he
    cases hp : c p <;> cases hq : c q <;>
      simp_all [bipartiteSign] <;> exact_mod_cast (by linarith :
        (H.degreeIn M p : ℚ) = H.degreeIn M q)

/-- Restricting a vertex matching to a shore not containing the hub gives
a vertex matching at the contraction pole. -/
theorem IsVertexMatching.contract_of_notMem {v : V} {M : Finset E}
    (hM : H.IsVertexMatching v M) {X : Finset V} (hv : v ∉ X) :
    (H.contract X).IsVertexMatching none (H.contractMatching X M) := by
  intro w hw
  cases w with
  | none => exact (hw rfl).elim
  | some w =>
    rw [contractMatching, contract_degreeIn_some]
    exact hM w.1 (fun he ↦ hv (he ▸ w.2))

/-- The same restriction is perfect when the retained contraction is
bipartite and has a perfect matching. -/
theorem IsVertexMatching.contract_perfect_of_bipartite {v : V} {M : Finset E}
    (hM : H.IsVertexMatching v M) {X : Finset V} (hv : v ∉ X)
    (hb : (H.contract X).IsBipartite) {P : Finset (H.meets X)}
    (hP : (H.contract X).IsPerfectMatching P) :
    (H.contract X).IsPerfectMatching (H.contractMatching X M) :=
  (hM.contract_of_notMem hv).isPerfectMatching_of_bipartite hb hP

/-- The pole degree of a restricted edge set is its original crossing count. -/
theorem contractMatching_degreeIn_none (X : Finset V) (M : Finset E) :
    (H.contract X).degreeIn (H.contractMatching X M) none =
      (M ∩ H.dangling X).card := by
  have hh := contract_weightedDegree_none (H := H) X (matchingVector M)
  rw [← matchingVector_contractMatching, weightedDegree_matchingVector,
    cutWeight_matchingVector] at hh
  exact_mod_cast hh

/-- The retained hub and the contraction pole are the only possible
exceptions to degree one; their two-colour relation determines the balance. -/
theorem IsVertexMatching.contract_pair_balance {v : V} {M : Finset E}
    (hM : H.IsVertexMatching v M) {X : Finset V} (hv : v ∈ X)
    {c : Option X → Bool}
    (hc : ∀ e, c ((H.contract X).endAt e 0) ≠ c ((H.contract X).endAt e 1))
    {P : Finset (H.meets X)} (hP : (H.contract X).IsPerfectMatching P) :
    (c (some ⟨v, hv⟩) = c none → H.degreeIn M v + (M ∩ H.dangling X).card = 2) ∧
      (c (some ⟨v, hv⟩) ≠ c none → H.degreeIn M v = (M ∩ H.dangling X).card) := by
  have hh := bipartite_degreeIn_pair_balance (H := H.contract X) hc hP
    (p := some ⟨v, hv⟩) (q := none) (M := H.contractMatching X M) (by simp) (by
      intro w hp hq
      cases w with
      | none => exact (hq rfl).elim
      | some w =>
        rw [contractMatching, contract_degreeIn_some]
        apply hM
        intro he
        apply hp
        exact congrArg some (Subtype.ext he))
  have hs : (H.contract X).degreeIn (H.contractMatching X M) (some ⟨v, hv⟩) =
      H.degreeIn M v := contract_degreeIn_some (H := H) X M ⟨v, hv⟩
  simpa only [hs, contractMatching_degreeIn_none] using hh

/-- If the hub and the contraction pole are on the same bipartition
side, oddness forces both exceptional degrees to be one. -/
theorem IsVertexMatching.perfect_of_contract_same_color {v : V} {M : Finset E}
    (hM : H.IsVertexMatching v M) (heven : Even (Fintype.card V))
    {X : Finset V} (hv : v ∈ X) (ho : Odd X.card) {c : Option X → Bool}
    (hc : ∀ e, c ((H.contract X).endAt e 0) ≠ c ((H.contract X).endAt e 1))
    {P : Finset (H.meets X)} (hP : (H.contract X).IsPerfectMatching P)
    (hcolor : c (some ⟨v, hv⟩) = c none) :
    H.IsPerfectMatching M ∧ (M ∩ H.dangling X).card = 1 := by
  have hsum := (hM.contract_pair_balance hv hc hP).1 hcolor
  have hvpos := (hM.odd_hub_degree heven).pos
  have hcrosspos := (hM.odd_crossing heven ho).pos
  have hvone : H.degreeIn M v = 1 := by omega
  refine ⟨?_, by omega⟩
  intro w
  by_cases hw : w = v
  · simpa [hw] using hvone
  · exact hM w hw

end GraphPuzzles.LoopMultigraph
