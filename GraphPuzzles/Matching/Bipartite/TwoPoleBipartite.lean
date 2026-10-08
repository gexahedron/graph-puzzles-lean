import GraphPuzzles.Cuts.SeparatingCutLift
import GraphPuzzles.Cuts.CutOrder

/-! Bipartite two-pole contractions control the two original matching crossing counts. -/

namespace GraphPuzzles.LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

def bipartiteSign (c : V → Bool) (v : V) : ℚ := if c v then 1 else -1

omit [DecidableEq E] in
theorem bipartite_sum_weightedDegree (c : V → Bool)
    (hc : ∀ e, c (H.endAt e 0) ≠ c (H.endAt e 1)) (x : E → ℚ) :
    (∑ v, bipartiteSign c v * H.weightedDegree x v) = 0 := by
  rw [sum_vertexWeight_degree]
  apply Finset.sum_eq_zero
  intro e _
  have hh := hc e
  cases h0 : c (H.endAt e 0) <;> cases h1 : c (H.endAt e 1) <;>
    simp_all [bipartiteSign]

omit [DecidableEq E] in
/-- For a bipartite graph, changes in weighted degree at only two vertices must balance. -/
theorem bipartite_two_vertex_balance (c : V → Bool)
    (hc : ∀ e, c (H.endAt e 0) ≠ c (H.endAt e 1)) {p q : V} (hpq : p ≠ q)
    (x y : E → ℚ) (hd : ∀ v, v ≠ p → v ≠ q → H.weightedDegree x v = H.weightedDegree y v) :
    bipartiteSign c p * (H.weightedDegree x p - H.weightedDegree y p) +
      bipartiteSign c q * (H.weightedDegree x q - H.weightedDegree y q) = 0 := by
  have heq : (∑ v ∈ ({p, q} : Finset V), bipartiteSign c v *
      H.weightedDegree (fun e ↦ x e - y e) v) =
      ∑ v, bipartiteSign c v * H.weightedDegree (fun e ↦ x e - y e) v := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v _ hv
    have hvp : v ≠ p := fun h ↦ hv (by simp [h])
    have hvq : v ≠ q := fun h ↦ hv (by simp [h])
    rw [weightedDegree_sub, hd v hvp hvq, sub_self, mul_zero]
  rw [Finset.sum_pair hpq, weightedDegree_sub, weightedDegree_sub,
    bipartite_sum_weightedDegree c hc] at heq
  exact heq

/-- Weighted degree at the two poles is the crossing weight on the two nested original cuts. -/
theorem bipartite_nested_cut_balance {X Z : Finset V} (hZX : Z ⊆ X)
    (c : Option ↥(poleShore X (Finset.univ \ Z)) → Bool)
    (hc : ∀ e, c (((H.contract X).contract (poleShore X (Finset.univ \ Z))).endAt e 0) ≠
      c (((H.contract X).contract (poleShore X (Finset.univ \ Z))).endAt e 1))
    (x y : E → ℚ) (hd : ∀ v, H.weightedDegree x v = H.weightedDegree y v) :
    bipartiteSign c none * (H.cutWeight x Z - H.cutWeight y Z) +
      bipartiteSign c (some ⟨none, none_mem_poleShore _ _⟩) *
        (H.cutWeight x X - H.cutWeight y X) = 0 := by
  let K := (H.contract X).contract (poleShore X (Finset.univ \ Z))
  let q : Option ↥(poleShore X (Finset.univ \ Z)) := some ⟨none, none_mem_poleShore _ _⟩
  have hp (w : E → ℚ) : K.weightedDegree (fun e ↦ w e.1.1) none = H.cutWeight w Z := by
    rw [contract_weightedDegree_none (H := H.contract X) (poleShore X (Finset.univ \ Z))
      (fun e ↦ w e.1), ← compl_contractShore, cutWeight_compl,
      contract_cutWeight_sourceShore X (contractShore X Z) (none_not_mem_contractShore _ _),
      sourceShore_contractShore, Finset.inter_eq_right.mpr hZX]
  have hq (w : E → ℚ) : K.weightedDegree (fun e ↦ w e.1.1) q = H.cutWeight w X := by
    rw [contract_weightedDegree_some (H := H.contract X) (poleShore X (Finset.univ \ Z))
      (fun e ↦ w e.1) ⟨none, none_mem_poleShore _ _⟩, contract_weightedDegree_none]
  have hrest (v : Option ↥(poleShore X (Finset.univ \ Z))) (hv : v ≠ none) (hvq : v ≠ q) :
      K.weightedDegree (fun e ↦ x e.1.1) v = K.weightedDegree (fun e ↦ y e.1.1) v := by
    cases v with
    | none => exact (hv rfl).elim
    | some v =>
      obtain ⟨v, hv⟩ := v
      cases v with
      | none => exact (hvq rfl).elim
      | some v =>
        rw [contract_weightedDegree_some (H := H.contract X) _ (fun e ↦ x e.1) _,
          contract_weightedDegree_some X x v,
          contract_weightedDegree_some (H := H.contract X) _ (fun e ↦ y e.1) _,
          contract_weightedDegree_some X y v, hd]
  have hh := bipartite_two_vertex_balance (H := K) c hc (p := none) (q := q)
    (by simp [q]) (fun e ↦ x e.1.1) (fun e ↦ y e.1.1) hrest
  simpa only [hp, hq] using hh

/-- A bipartite region between nested cuts makes them matching-equivalent, or both
cuts are tight. A common one-crossing matching fixes the additive constant. -/
theorem IsBipartite.middle_both_tight_or_matchingEquivalent {X Z : Finset V} (hZX : Z ⊆ X)
    (hb : ((H.contract X).contract (poleShore X (Finset.univ \ Z))).IsBipartite)
    {N : Finset E} (hN : H.IsPerfectMatching N)
    (hNX : (N ∩ H.dangling X).card = 1) (hNZ : (N ∩ H.dangling Z).card = 1) :
    (H.IsTightCut Z ∧ H.IsTightCut X) ∨ H.MatchingEquivalentCuts Z X := by
  obtain ⟨c, hc⟩ := hb
  let q : Option ↥(poleShore X (Finset.univ \ Z)) := some ⟨none, none_mem_poleShore _ _⟩
  have balance (M : Finset E) (hM : H.IsPerfectMatching M) :
      bipartiteSign c none * (((M ∩ H.dangling Z).card : ℚ) - 1) +
        bipartiteSign c q * (((M ∩ H.dangling X).card : ℚ) - 1) = 0 := by
    have hh := bipartite_nested_cut_balance hZX c hc (matchingVector M) (matchingVector N)
      (fun v ↦ (hM.isFractional.degree v).trans (hN.isFractional.degree v).symm)
    simpa only [cutWeight_matchingVector, hNX, hNZ, Nat.cast_one] using hh
  by_cases heq : c none = c q
  · have hones (M : Finset E) (hM : H.IsPerfectMatching M) :
        (M ∩ H.dangling Z).card = 1 ∧ (M ∩ H.dangling X).card = 1 := by
      have hh := balance M hM
      have heq' : (((M ∩ H.dangling Z).card : ℚ) + (M ∩ H.dangling X).card) = 2 := by
        simp only [bipartiteSign, ← heq] at hh
        cases hb : c none <;> simp only [hb, Bool.false_eq_true, ite_false, ite_true] at hh <;> linarith
      have hn : (M ∩ H.dangling Z).card + (M ∩ H.dangling X).card = 2 := by exact_mod_cast heq'
      have ho := hN.odd_of_crossing_one hNZ
      have hp := hM.crossing_mod_two Z
      rw [Nat.odd_iff] at ho
      omega
    exact Or.inl ⟨fun M hM ↦ (hones M hM).1, fun M hM ↦ (hones M hM).2⟩
  · refine Or.inr ?_
    intro M hM
    have hh := balance M hM
    have hsign : bipartiteSign c q = -bipartiteSign c none := by
      cases h0 : c none <;> cases h1 : c q <;> simp_all [bipartiteSign]
    rw [hsign] at hh
    have heq' : ((M ∩ H.dangling Z).card : ℚ) = (M ∩ H.dangling X).card := by
      cases hb : c none <;> simp only [bipartiteSign, hb, Bool.false_eq_true, ite_false, ite_true]
        at hh <;> linarith
    exact_mod_cast heq'

theorem IsBipartite.middle_tight_or_matchingEquivalent {X Z : Finset V} (hZX : Z ⊆ X)
    (hb : ((H.contract X).contract (poleShore X (Finset.univ \ Z))).IsBipartite)
    {N : Finset E} (hN : H.IsPerfectMatching N)
    (hNX : (N ∩ H.dangling X).card = 1) (hNZ : (N ∩ H.dangling Z).card = 1) :
    H.IsTightCut Z ∨ H.MatchingEquivalentCuts Z X :=
  (hb.middle_both_tight_or_matchingEquivalent hZX hN hNX hNZ).imp And.left id

theorem IsBipartite.middle_matchingEquivalent_of_not_tight {X Z : Finset V} (hZX : Z ⊆ X)
    (hb : ((H.contract X).contract (poleShore X (Finset.univ \ Z))).IsBipartite)
    {N : Finset E} (hN : H.IsPerfectMatching N)
    (hNX : (N ∩ H.dangling X).card = 1) (hNZ : (N ∩ H.dangling Z).card = 1)
    (hnt : ¬ H.IsTightCut X) : H.MatchingEquivalentCuts Z X :=
  (hb.middle_both_tight_or_matchingEquivalent hZX hN hNX hNZ).resolve_left (fun h ↦ hnt h.2)

end GraphPuzzles.LoopMultigraph
