import GraphPuzzles.Matching.Barriers.DeletedBarrierCount
import GraphPuzzles.Reduction.Removable.EdgeConnectivity
import GraphPuzzles.Matching.Barriers.MaximalBarrier

/-! Barriers exposed by mutually dependent edges, without removable deletion. -/

namespace GraphPuzzles.LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

namespace ComponentFamily

variable {B : Finset V}

/-- Restoring an edge contributes at most two extra component crossings,
while every retained edge internal to the barrier consumes two incidences. -/
theorem deleted_internal_set_bound {f : E} (F : (H.deleteEdge f).ComponentFamily B)
    (I : Finset E) (hf : f ∉ I) (hI : ∀ e ∈ I, ∀ k, H.endAt e k ∈ B)
    {x : E → ℚ} (hx : ∀ e, 0 ≤ x e) :
    (∑ Q ∈ F.odd, H.cutWeight x Q) + 2 * (∑ e ∈ I, x e) ≤
      (∑ v ∈ B, H.weightedDegree x v) + 2 * x f := by
  have hi (e : E) (he : e ∈ I) :
      H.boundaryMultiplicity F.odd e = 0 ∧ H.endsIn B e = 2 := by
    constructor
    · apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro Q hQ
      obtain ⟨hQ, heQ⟩ := Finset.mem_filter.mp hQ
      have h0 : H.endAt e 0 ∉ Q := fun h ↦ F.avoid Q (F.mem_odd.mp hQ).1 _ h (hI e he 0)
      have h1 : H.endAt e 1 ∉ Q := fun h ↦ F.avoid Q (F.mem_odd.mp hQ).1 _ h (hI e he 1)
      exact (mem_dangling.mp heQ) (by simp [h0, h1])
    · simp [endsIn, hI e he]
  have hcoeff (g : E) : (H.boundaryMultiplicity F.odd g : ℚ) +
      (if g ∈ I then 2 else 0) ≤ (H.endsIn B g : ℚ) + (if g = f then 2 else 0) := by
    by_cases hgf : g = f
    · subst g
      have hc := boundaryMultiplicity_le_two (H := H) F.odd (fun Q hQ R hR hne ↦
        F.pairwise Q (F.mem_odd.mp hQ).1 R (F.mem_odd.mp hR).1 hne) f
      have hc' : (H.boundaryMultiplicity F.odd f : ℚ) ≤ 2 := by exact_mod_cast hc
      have hz : (0 : ℚ) ≤ H.endsIn B f := Nat.cast_nonneg _
      simp only [if_neg hf, add_zero, if_true]
      linarith
    · by_cases hgI : g ∈ I
      · obtain ⟨h0, h2⟩ := hi g hgI
        simp [h0, h2, hgI, hgf]
      · have hh := F.boundaryMultiplicity_le_endsIn ⟨g, by simp [hgf]⟩
        have heq : (H.deleteEdge f).boundaryMultiplicity F.odd ⟨g, by simp [hgf]⟩ =
            H.boundaryMultiplicity F.odd g := by
          simp only [boundaryMultiplicity, deleteEdge, restrictEdges_mem_dangling]
        rw [heq] at hh
        simp only [if_neg hgI, if_neg hgf, add_zero]
        exact_mod_cast hh
  have hh := Finset.sum_le_sum (fun g (_ : g ∈ (Finset.univ : Finset E)) ↦
    mul_le_mul_of_nonneg_right (hcoeff g) (hx g))
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul] at hh
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at hh
  simpa only [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
    ← Finset.mul_sum, sum_cutWeight_eq_boundaryMultiplicity, sum_weightedDegree] using hh

/-- An edge mutually dependent on the deleted edge is the only edge internal
to a barrier containing its ends. -/
theorem IsBarrier.internal_edge_unique {e f : E}
    (F : (H.deleteEdge f).ComponentFamily B) (hb : F.IsBarrier)
    (hm : H.IsMatchingCovered) (hef : e ≠ f) (hd : H.MutuallyDependent e f)
    (he0 : H.endAt e 0 ∈ B) (he1 : H.endAt e 1 ∈ B)
    {g : E} (hg0 : H.endAt g 0 ∈ B) (hg1 : H.endAt g 1 ∈ B) : g = e := by
  obtain ⟨N, hN, heN⟩ := hm.2 e
  have hfB := hb.deleted_edge_avoids F hef he0 he1 hN heN ((hd N hN).mp heN)
  have hgf : g ≠ f := fun h ↦ hfB 0 (h ▸ hg0)
  by_contra hge
  obtain ⟨M, hM, hgM⟩ := hm.2 g
  have hs := F.deleted_internal_set_bound {e, g} (by simp [hef.symm, hgf.symm]) (by
    intro a ha k
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl <;> fin_cases k <;> assumption) hM.isFractional.nonneg
  simp only [Finset.sum_pair (Ne.symm hge), hM.isFractional.degree,
    Finset.sum_const, nsmul_eq_mul, mul_one] at hs
  rw [hd.matchingVector_eq hM, show matchingVector M g = 1 from if_pos hgM] at hs
  have hl : (B.card : ℚ) ≤ ∑ Q ∈ F.odd, H.cutWeight (matchingVector M) Q := by
    calc
      _ = ∑ _Q ∈ F.odd, (1 : ℚ) := by simp [show F.odd.card = B.card from hb]
      _ ≤ _ := Finset.sum_le_sum fun Q hQ ↦ hM.isFractional.odd_cut Q (F.mem_odd.mp hQ).2
  linarith

/-- If all but one part are singletons and only one edge is internal to the
barrier, barrier membership colours all other edges meeting the complement. -/
theorem barrierColor_except_part {e f : E} (F : (H.deleteEdge f).ComponentFamily B)
    (hloop : ∀ g, H.endAt g 0 ≠ H.endAt g 1) {Q : Finset V}
    (hsingle : ∀ R ∈ F.parts, R ≠ Q → R.card = 1)
    (hunique : ∀ g, H.endAt g 0 ∈ B → H.endAt g 1 ∈ B → g = e)
    {g : E} (hge : g ≠ e) (hgf : g ≠ f) (hg : g ∈ H.meets (Finset.univ \ Q)) :
    decide (H.endAt g 0 ∈ B) ≠ decide (H.endAt g 1 ∈ B) := by
  by_cases h0 : H.endAt g 0 ∈ B
  · have h1 : H.endAt g 1 ∉ B := fun h ↦ hge (hunique g h0 h)
    simp [h0, h1]
  · have h1 : H.endAt g 1 ∈ B := by
      by_contra hn1
      obtain ⟨R, hR, hvR⟩ := F.cover _ h0
      have hwR : H.endAt g 1 ∈ R := F.closed R hR ⟨g, by simp [hgf]⟩ 0 hvR hn1
      by_cases hRQ : R = Q
      · subst R
        obtain ⟨k, hk⟩ := mem_meets.mp hg
        have hkQ : H.endAt g k ∈ Q := by fin_cases k <;> assumption
        exact (Finset.mem_sdiff.mp hk).2 hkQ
      · exact hloop g (Finset.card_le_one_iff.mp (hsingle R hR hRQ).le hvR hwR)
    simp [h0, h1]

end ComponentFamily

/-- Mutual dependence exposes a maximal barrier whenever the deletion still
has a perfect matching; connectivity of that deletion suffices to provide one. -/
theorem MutuallyDependent.exists_maximal_barrier {e f : E}
    (hd : H.MutuallyDependent e f) (hef : e ≠ f) (hm : H.IsMatchingCovered)
    (hc : (H.deleteEdge f).IsConnected) :
    ∃ P, (H.deleteEdge f).IsPerfectMatching P ∧ ∃ B,
      H.endAt e 0 ∈ B ∧ H.endAt e 1 ∈ B ∧
      ∃ F : (H.deleteEdge f).ComponentFamily B, F.IsMaximalBarrier := by
  obtain ⟨M, hM, hfM⟩ := hm.exists_perfectMatching_omitting hc
  obtain ⟨P, hP, _⟩ := hM.exists_restrictEdges (S := Finset.univ.erase f) (by
    intro g hg
    exact Finset.mem_erase.mpr ⟨ne_of_mem_of_not_mem hg hfM, Finset.mem_univ _⟩)
  let a : Finset.univ.erase f := ⟨e, by simp [hef]⟩
  have hna : ¬ ∃ N, (H.deleteEdge f).IsPerfectMatching N ∧ a ∈ N := by
    rintro ⟨N, hN, heN⟩
    have he : e ∈ N.image Subtype.val := Finset.mem_image.mpr ⟨a, heN, rfl⟩
    have hf := (hd _ hN.of_restrictEdges).mp he
    obtain ⟨g, _, hgf⟩ := Finset.mem_image.mp hf
    exact (Finset.mem_erase.mp g.2).1 hgf
  obtain ⟨B₀, he0, he1, F₀, hF₀⟩ :=
    hP.exists_barrier_of_inadmissible_edge (e := a) (hm.loopless e) hna
  obtain ⟨B, hB, F, hF⟩ := hF₀.exists_maximal
  exact ⟨P, hP, B, hB he0, hB he1, F, hF⟩

end GraphPuzzles.LoopMultigraph
