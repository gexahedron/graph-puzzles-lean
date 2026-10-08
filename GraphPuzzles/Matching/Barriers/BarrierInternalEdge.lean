import GraphPuzzles.Matching.Barriers.BarrierBicritical
import GraphPuzzles.Matching.Barriers.BarrierPrecedence

/-! Barrier counting with an edge whose two ends lie in the barrier. -/

namespace GraphPuzzles.LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

namespace ComponentFamily

variable {B : Finset V} (F : H.ComponentFamily B)

/-- An internal edge uses two barrier incidences in addition to all component
boundary weights. Matching-coveredness is not needed for this inequality. -/
theorem sum_odd_cutWeight_add_internal_le {x : E → ℚ} (hx : ∀ e, 0 ≤ x e)
    {e : E} (h0 : H.endAt e 0 ∈ B) (h1 : H.endAt e 1 ∈ B) :
    (∑ Q ∈ F.odd, H.cutWeight x Q) + 2 * x e ≤ ∑ v ∈ B, H.weightedDegree x v := by
  let C := F.odd.biUnion H.dangling
  have hCB : C ⊆ H.dangling B :=
    Finset.biUnion_subset.mpr fun Q hQ ↦ F.dangling_subset (F.mem_odd.mp hQ).1
  have heB : H.endsIn B e = 2 := by
    have hall : ∀ k : Fin 2, H.endAt e k ∈ B := by intro k; fin_cases k <;> assumption
    simp [endsIn, hall]
  have heC : e ∉ C := fun he ↦ (mem_dangling.mp (hCB he)) (by simp [h0, h1])
  have hs : (∑ Q ∈ F.odd, H.cutWeight x Q) = ∑ f ∈ C, x f := by
    symm
    apply Finset.sum_biUnion
    intro Q hQ R hR hne
    exact F.disjoint_dangling (F.mem_odd.mp hQ).1 (F.mem_odd.mp hR).1 hne
  rw [hs, sum_weightedDegree]
  calc
    _ = ∑ f, ((if f ∈ C then x f else 0) + (if f = e then 2 * x f else 0)) := by
      rw [Finset.sum_add_distrib]
      have heq : (∑ f, if f = e then 2 * x f else 0) = 2 * x e := by simp
      rw [heq]
      simp only [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
    _ ≤ _ := Finset.sum_le_sum (by
      intro f _
      by_cases hfe : f = e
      · subst f
        simp [heC, heB]
      · simp only [if_neg hfe, add_zero]
        by_cases hf : f ∈ C
        · rw [if_pos hf]
          have hh := endsIn_mod_two (K := H) B f
          rw [if_pos (hCB hf)] at hh
          have hn : (1 : ℚ) ≤ H.endsIn B f := by exact_mod_cast (show 1 ≤ H.endsIn B f by omega)
          exact (one_mul (x f)).symm.trans_le (mul_le_mul_of_nonneg_right hn (hx f))
        · rw [if_neg hf]
          exact mul_nonneg (Nat.cast_nonneg _) (hx f))

end ComponentFamily

namespace ContractionBarrier

variable {X : Finset V} {B : Finset (Option X)}
variable (F : (H.contract X).ComponentFamily B)

/-- An admissible original edge internal to a contraction barrier forces the
contraction vertex into that barrier. -/
theorem none_mem_of_internal_edge (hb : F.IsBarrier) (ho : Odd X.card)
    {e : H.meets X} (h0 : (H.contract X).endAt e 0 ∈ B)
    (h1 : (H.contract X).endAt e 1 ∈ B)
    {M : Finset E} (hM : H.IsPerfectMatching M) (he : e.1 ∈ M) : none ∈ B := by
  by_contra hn
  have hs := F.sum_odd_cutWeight_add_internal_le
    (fun e ↦ hM.isFractional.nonneg e.1) h0 h1
  have hd : (∑ v ∈ B, (H.contract X).weightedDegree
      (fun e ↦ matchingVector M e.1) v) = B.card := by
    calc
      _ = ∑ _v ∈ B, (1 : ℚ) := Finset.sum_congr rfl (by
        intro v hv
        cases v with
        | none => exact (hn hv).elim
        | some v => exact (contract_weightedDegree_some X _ v).trans (hM.isFractional.degree v.1))
      _ = _ := by simp
  have hl : (F.odd.card : ℚ) ≤ ∑ Q ∈ F.odd,
      (H.contract X).cutWeight (fun e ↦ matchingVector M e.1) Q := by
    calc
      _ = ∑ _Q ∈ F.odd, (1 : ℚ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun Q hQ ↦
        hM.isFractional.contract_odd_cut X ho Q (F.mem_odd.mp hQ).2
  rw [hd, show matchingVector M e.1 = 1 from if_pos he] at hs
  rw [show F.odd.card = B.card from hb] at hl
  linarith

/-- Every component boundary precedes the outer boundary, with a strict deficit
of two whenever the original matching uses the internal barrier edge. -/
theorem crossing_add_internal_le (hb : F.IsBarrier) (hn : none ∈ B)
    {e : H.meets X} (h0 : (H.contract X).endAt e 0 ∈ B)
    (h1 : (H.contract X).endAt e 1 ∈ B)
    {Q : Finset (Option X)} (hQ : Q ∈ F.odd)
    {M : Finset E} (hM : H.IsPerfectMatching M) :
    ((M ∩ H.dangling (sourceShore X Q)).card : ℚ) + 2 * matchingVector M e.1 ≤
      (M ∩ H.dangling X).card := by
  have hs := F.sum_odd_cutWeight_add_internal_le
    (fun e ↦ hM.isFractional.nonneg e.1) h0 h1
  have hd : (∑ v ∈ B, (H.contract X).weightedDegree
      (fun e ↦ matchingVector M e.1) v) =
      ((B.erase none).card : ℚ) + (M ∩ H.dangling X).card := by
    rw [← Finset.sum_erase_add B _ hn, contract_weightedDegree_none, cutWeight_matchingVector]
    congr 1
    calc
      _ = ∑ _v ∈ B.erase none, (1 : ℚ) := Finset.sum_congr rfl (by
        intro v hv
        cases v with
        | none => simp at hv
        | some v => exact (contract_weightedDegree_some X _ v).trans (hM.isFractional.degree v.1))
      _ = _ := by simp
  have hl : (∑ R ∈ F.odd, (H.contract X).cutWeight
      (fun e ↦ matchingVector M e.1) R) =
      ∑ R ∈ F.odd, ((M ∩ H.dangling (sourceShore X R)).card : ℚ) := by
    apply Finset.sum_congr rfl
    intro R hR
    rw [contract_cutWeight_sourceShore X R (none_not_mem F hn (F.mem_odd.mp hR).1),
      cutWeight_matchingVector]
  rw [hd, hl, ← Finset.sum_erase_add F.odd _ hQ] at hs
  have hr : ((F.odd.erase Q).card : ℚ) ≤
      ∑ R ∈ F.odd.erase Q, ((M ∩ H.dangling (sourceShore X R)).card : ℚ) := by
    calc
      _ = ∑ _R ∈ F.odd.erase Q, (1 : ℚ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun R hR ↦ by
        exact_mod_cast crossing_pos F hn (Finset.mem_of_mem_erase hR) hM
  have hc : (F.odd.erase Q).card = (B.erase none).card := by
    have hF : F.odd.card = B.card := hb
    simp [Finset.card_erase_of_mem hQ, Finset.card_erase_of_mem hn, hF]
  rw [hc] at hr
  linarith

theorem precedes_of_internal_edge (hb : F.IsBarrier) (hn : none ∈ B)
    {e : H.meets X} (h0 : (H.contract X).endAt e 0 ∈ B)
    (h1 : (H.contract X).endAt e 1 ∈ B)
    {Q : Finset (Option X)} (hQ : Q ∈ F.odd) :
    H.CutPrecedes (sourceShore X Q) X := by
  intro M hM
  have hh := crossing_add_internal_le F hb hn h0 h1 hQ hM
  have hnM := hM.isFractional.nonneg e.1
  have hle : ((M ∩ H.dangling (sourceShore X Q)).card : ℚ) ≤
      (M ∩ H.dangling X).card := by linarith
  exact_mod_cast hle

theorem strictlyPrecedes_of_internal_edge (hb : F.IsBarrier) (hn : none ∈ B)
    {e : H.meets X} (h0 : (H.contract X).endAt e 0 ∈ B)
    (h1 : (H.contract X).endAt e 1 ∈ B)
    {Q : Finset (Option X)} (hQ : Q ∈ F.odd)
    {M : Finset E} (hM : H.IsPerfectMatching M) (he : e.1 ∈ M) :
    H.CutStrictlyPrecedes (sourceShore X Q) X := by
  refine ⟨precedes_of_internal_edge F hb hn h0 h1 hQ, M, hM, ?_⟩
  have hh := crossing_add_internal_le F hb hn h0 h1 hQ hM
  rw [show matchingVector M e.1 = 1 from if_pos he] at hh
  have hlt : ((M ∩ H.dangling (sourceShore X Q)).card : ℚ) <
      (M ∩ H.dangling X).card := by linarith
  exact_mod_cast hlt

end ContractionBarrier

end GraphPuzzles.LoopMultigraph
