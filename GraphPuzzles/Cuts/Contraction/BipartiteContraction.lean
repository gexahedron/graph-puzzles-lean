import GraphPuzzles.Cuts.CohesiveCuts

/-! Bipartiteness and separating-cut contractions. -/

namespace GraphPuzzles.LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- The subgraph induced by a shore admits a bipartition. -/
def IsBipartiteOn (H : LoopMultigraph V E) (X : Finset V) : Prop :=
  ∃ c : V → Bool, ∀ e, H.endAt e 0 ∈ X → H.endAt e 1 ∈ X →
    c (H.endAt e 0) ≠ c (H.endAt e 1)

omit [DecidableEq V] [DecidableEq E] in
theorem IsBipartite.on_shore (hb : H.IsBipartite) (X : Finset V) : H.IsBipartiteOn X := by
  obtain ⟨c, hc⟩ := hb
  exact ⟨c, fun e _ _ ↦ hc e⟩

omit [DecidableEq E] in
theorem IsBipartite.induced_of_contract {X : Finset V} (hb : (H.contract X).IsBipartite) :
    H.IsBipartiteOn X := by
  obtain ⟨c, hc⟩ := hb
  refine ⟨c ∘ contractVertex X, ?_⟩
  intro e h0 h1
  have hh := hc ⟨e, mem_meets.mpr ⟨0, h0⟩⟩
  simpa only [Function.comp_apply, contractVertex, contract_endAt, dif_pos h0, dif_pos h1] using hh

/-- Campos--Lucchesi Lemma 2.1: bipartiteness of the induced shore extends to a
separating-cut contraction. -/
theorem IsBipartiteOn.contract_of_separating {X : Finset V} (hb : H.IsBipartiteOn X)
    (hs : H.IsSeparatingCut X) : (H.contract X).IsBipartite := by
  classical
  obtain ⟨c, hc⟩ := hb
  let p : V → ℚ := fun v ↦ if v ∈ X then (if c v then 1 else -1) else 0
  let s : ℚ := ∑ v, p v
  let q : E → ℚ := fun e ↦ p (H.endAt e 0) + p (H.endAt e 1)
  have hzero (e : E) (he : e ∉ H.dangling X) : q e = 0 := by
    by_cases h0 : H.endAt e 0 ∈ X <;> by_cases h1 : H.endAt e 1 ∈ X
    · have hh := hc e h0 h1
      cases hc0 : c (H.endAt e 0) <;> cases hc1 : c (H.endAt e 1) <;> simp_all [q, p]
    · exact (he (mem_dangling.mpr (by tauto))).elim
    · exact (he (mem_dangling.mpr (by tauto))).elim
    · simp [q, p, h0, h1]
  have hsame (e : E) (he : e ∈ H.dangling X) : q e = s := by
    obtain ⟨M, hM, heM, hm⟩ := hs.exists_perfectMatching_through e
    have hi : M ∩ H.dangling X = {e} := by
      apply (Finset.eq_of_subset_of_card_le
        (Finset.singleton_subset_iff.mpr (Finset.mem_inter.mpr ⟨heM, he⟩)) ?_).symm
      simp [hm]
    have hh := sum_vertexWeight_degree (H := H) p (matchingVector M)
    simp only [hM.isFractional.degree, mul_one] at hh
    change s = ∑ f, matchingVector M f * q f at hh
    rw [Finset.sum_eq_single e] at hh
    · simpa only [matchingVector, if_pos heM, one_mul] using hh.symm
    · intro f _ hf
      by_cases hfM : f ∈ M
      · have hn : f ∉ H.dangling X := by
          intro hd
          have hm' : f ∈ M ∩ H.dangling X := Finset.mem_inter.mpr ⟨hfM, hd⟩
          rw [hi, Finset.mem_singleton] at hm'
          exact hf hm'
        simp [hzero f hn]
      · simp [matchingVector, hfM]
    · simp
  let d : Option X → Bool
    | none => decide (s ≠ 1)
    | some v => c v.1
  refine ⟨d, ?_⟩
  intro e
  by_cases h0 : H.endAt e.1 0 ∈ X <;> by_cases h1 : H.endAt e.1 1 ∈ X
  · simpa only [contract_endAt, dif_pos h0, dif_pos h1, d] using hc e.1 h0 h1
  · have he : e.1 ∈ H.dangling X := mem_dangling.mpr (by tauto)
    have hh := hsame e.1 he
    simp only [q, p, if_pos h0, if_neg h1, add_zero] at hh
    simp only [contract_endAt, dif_pos h0, dif_neg h1, d]
    cases hc0 : c (H.endAt e.1 0) <;> simp_all; linarith
  · have he : e.1 ∈ H.dangling X := mem_dangling.mpr (by tauto)
    have hh := hsame e.1 he
    simp only [q, p, if_neg h0, if_pos h1, zero_add] at hh
    simp only [contract_endAt, dif_neg h0, dif_pos h1, d]
    cases hc1 : c (H.endAt e.1 1) <;> simp_all; linarith
  · obtain ⟨k, hk⟩ := mem_meets.mp e.2
    fin_cases k <;> contradiction

/-- A separating-cut contraction of a bipartite graph is bipartite. -/
theorem IsBipartite.contract_of_separating {X : Finset V} (hb : H.IsBipartite)
    (hs : H.IsSeparatingCut X) : (H.contract X).IsBipartite :=
  (hb.on_shore X).contract_of_separating hs

theorem IsSeparatingCut.bipartite_contract_iff {X : Finset V} (hs : H.IsSeparatingCut X) :
    (H.contract X).IsBipartite ↔ H.IsBipartiteOn X :=
  ⟨fun h ↦ h.induced_of_contract, fun h ↦ h.contract_of_separating hs⟩

omit [DecidableEq E] in
/-- Bipartitions of the two contractions glue after choosing their relative phase. -/
theorem IsBipartite.of_contracts {X : Finset V} (hL : (H.contract X).IsBipartite)
    (hR : (H.contract (Finset.univ \ X)).IsBipartite) : H.IsBipartite := by
  obtain ⟨c, hc⟩ := hL
  obtain ⟨d, hd⟩ := hR
  let f : Bool → Bool := fun b ↦ if b = d none then !c none else c none
  have hinj (a b : Bool) (hne : a ≠ b) : f a ≠ f b := by
    cases a <;> cases b <;> cases hcn : c none <;> cases hdn : d none <;> simp_all [f]
  let g : V → Bool := fun v ↦ if h : v ∈ X then c (some ⟨v, h⟩)
    else f (d (some ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h⟩⟩))
  refine ⟨g, ?_⟩
  intro e
  by_cases h0 : H.endAt e 0 ∈ X <;> by_cases h1 : H.endAt e 1 ∈ X
  · have hh := hc ⟨e, mem_meets.mpr ⟨0, h0⟩⟩
    simpa only [contract_endAt, dif_pos h0, dif_pos h1, g] using hh
  · have h0' : H.endAt e 0 ∉ Finset.univ \ X := by simp [h0]
    have h1' : H.endAt e 1 ∈ Finset.univ \ X := by simp [h1]
    have hh := hc ⟨e, mem_meets.mpr ⟨0, h0⟩⟩
    have hh' := hd ⟨e, mem_meets.mpr ⟨1, h1'⟩⟩
    simp only [contract_endAt, dif_pos h0, dif_neg h1] at hh
    simp only [contract_endAt, dif_neg h0', dif_pos h1'] at hh'
    simpa only [g, dif_pos h0, dif_neg h1, f, if_neg (Ne.symm hh')] using hh
  · have h0' : H.endAt e 0 ∈ Finset.univ \ X := by simp [h0]
    have h1' : H.endAt e 1 ∉ Finset.univ \ X := by simp [h1]
    have hh := hc ⟨e, mem_meets.mpr ⟨1, h1⟩⟩
    have hh' := hd ⟨e, mem_meets.mpr ⟨0, h0'⟩⟩
    simp only [contract_endAt, dif_neg h0, dif_pos h1] at hh
    simp only [contract_endAt, dif_pos h0', dif_neg h1'] at hh'
    simpa only [g, dif_neg h0, dif_pos h1, f, if_neg hh'] using hh
  · have h0' : H.endAt e 0 ∈ Finset.univ \ X := by simp [h0]
    have h1' : H.endAt e 1 ∈ Finset.univ \ X := by simp [h1]
    have hh := hd ⟨e, mem_meets.mpr ⟨0, h0'⟩⟩
    simp only [contract_endAt, dif_pos h0', dif_pos h1'] at hh
    simpa only [g, dif_neg h0, dif_neg h1] using hinj _ _ hh

theorem IsSeparatingCut.bipartite_iff {X : Finset V} (hs : H.IsSeparatingCut X) :
    H.IsBipartite ↔ (H.contract X).IsBipartite ∧ (H.contract (Finset.univ \ X)).IsBipartite :=
  ⟨fun h ↦ ⟨h.contract_of_separating hs, h.contract_of_separating hs.compl⟩,
    fun h ↦ h.1.of_contracts h.2⟩

end GraphPuzzles.LoopMultigraph
