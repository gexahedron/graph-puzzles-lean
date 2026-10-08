import GraphPuzzles.Reduction.Removable.EdgeDependence
import GraphPuzzles.Matching.Barriers.BarrierInternalEdge

/-! Barrier counting after deletion of one of two mutually dependent edges. -/

namespace GraphPuzzles.LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- The number of members of a shore family whose boundary contains an edge. -/
def boundaryMultiplicity (H : LoopMultigraph V E) (C : Finset (Finset V)) (e : E) : ℕ :=
  (C.filter fun Q ↦ e ∈ H.dangling Q).card

theorem sum_cutWeight_eq_boundaryMultiplicity (C : Finset (Finset V)) (x : E → ℚ) :
    (∑ Q ∈ C, H.cutWeight x Q) = ∑ e, (H.boundaryMultiplicity C e : ℚ) * x e := by
  have hcut (Q : Finset V) : H.cutWeight x Q =
      ∑ e, if e ∈ H.dangling Q then x e else 0 := by
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, cutWeight]
  simp only [hcut]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [← Finset.sum_filter]
  simp [boundaryMultiplicity]

/-- Disjoint shores can contain at most the two ends of an edge. -/
theorem boundaryMultiplicity_le_two (C : Finset (Finset V))
    (hd : ∀ Q ∈ C, ∀ R ∈ C, Q ≠ R → Disjoint Q R) (e : E) :
    H.boundaryMultiplicity C e ≤ 2 := by
  have one (v : V) : (C.filter fun Q ↦ v ∈ Q).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro Q hQ R hR
    by_contra hne
    exact Finset.disjoint_left.mp (hd Q (Finset.mem_filter.mp hQ).1 R
      (Finset.mem_filter.mp hR).1 hne) (Finset.mem_filter.mp hQ).2 (Finset.mem_filter.mp hR).2
  have hsub : C.filter (fun Q ↦ e ∈ H.dangling Q) ⊆
      (C.filter fun Q ↦ H.endAt e 0 ∈ Q) ∪ (C.filter fun Q ↦ H.endAt e 1 ∈ Q) := by
    intro Q hQ
    obtain ⟨hQC, he⟩ := Finset.mem_filter.mp hQ
    have hn := mem_dangling.mp he
    by_cases h0 : H.endAt e 0 ∈ Q
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hQC, h0⟩)
    · have h1 : H.endAt e 1 ∈ Q := by tauto
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hQC, h1⟩)
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have h0 := one (H.endAt e 0)
  have h1 := one (H.endAt e 1)
  change (C.filter fun Q ↦ e ∈ H.dangling Q).card ≤ 2
  omega

namespace ComponentFamily

variable {B : Finset V}

theorem boundaryMultiplicity_le_endsIn (F : H.ComponentFamily B) (e : E) :
    H.boundaryMultiplicity F.odd e ≤ H.endsIn B e := by
  have hc : H.boundaryMultiplicity F.odd e ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro Q hQ R hR
    by_contra hne
    obtain ⟨hQ, heQ⟩ := Finset.mem_filter.mp hQ
    obtain ⟨hR, heR⟩ := Finset.mem_filter.mp hR
    exact Finset.disjoint_left.mp
      (F.disjoint_dangling (F.mem_odd.mp hQ).1 (F.mem_odd.mp hR).1 hne) heQ heR
  by_cases hp : H.boundaryMultiplicity F.odd e = 0
  · rw [hp]; exact Nat.zero_le _
  · obtain ⟨Q, hQ⟩ := Finset.card_pos.mp (show 0 < (F.odd.filter fun Q ↦ e ∈ H.dangling Q).card by
      change 0 < H.boundaryMultiplicity F.odd e; omega)
    obtain ⟨hQ, heQ⟩ := Finset.mem_filter.mp hQ
    have heB := F.dangling_subset (F.mem_odd.mp hQ).1 heQ
    have hh := endsIn_mod_two (K := H) B e
    rw [if_pos heB] at hh
    omega

/-- Restoring one deleted edge adds at most two component crossings. The
incidences of that edge in the barrier are accounted for separately. -/
theorem deleted_internal_bound {f : E} (F : (H.deleteEdge f).ComponentFamily B)
    {e : E} (hef : e ≠ f) (he0 : H.endAt e 0 ∈ B) (he1 : H.endAt e 1 ∈ B)
    {x : E → ℚ} (hx : ∀ g, 0 ≤ x g) :
    (∑ Q ∈ F.odd, H.cutWeight x Q) + 2 * x e + (H.endsIn B f : ℚ) * x f ≤
      (∑ v ∈ B, H.weightedDegree x v) + 2 * x f := by
  have heC : H.boundaryMultiplicity F.odd e = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro Q hQ
    obtain ⟨hQ, heQ⟩ := Finset.mem_filter.mp hQ
    have h0 := F.avoid Q (F.mem_odd.mp hQ).1 (H.endAt e 0)
    have h1 := F.avoid Q (F.mem_odd.mp hQ).1 (H.endAt e 1)
    exact (mem_dangling.mp heQ) (by
      constructor <;> intro h
      · exact (h0 h he0).elim
      · exact (h1 h he1).elim)
  have heB : H.endsIn B e = 2 := by
    have hall : ∀ k : Fin 2, H.endAt e k ∈ B := by intro k; fin_cases k <;> assumption
    simp [endsIn, hall]
  have hfC := boundaryMultiplicity_le_two (H := H) F.odd (fun Q hQ R hR hne ↦
    F.pairwise Q (F.mem_odd.mp hQ).1 R (F.mem_odd.mp hR).1 hne) f
  have hcoeff (g : E) : (H.boundaryMultiplicity F.odd g : ℚ) +
      (if g = e then 2 else 0) + (if g = f then (H.endsIn B f : ℚ) else 0) ≤
      (H.endsIn B g : ℚ) + (if g = f then 2 else 0) := by
    by_cases hgf : g = f
    · subst g
      have hh : (H.boundaryMultiplicity F.odd f : ℚ) ≤ 2 := by exact_mod_cast hfC
      simp only [if_neg hef.symm, add_zero, if_true]
      linarith
    · by_cases hge : g = e
      · subst g
        simp [heC, heB, hef]
      · have hh := F.boundaryMultiplicity_le_endsIn ⟨g, by simp [hgf]⟩
        have hm : (H.deleteEdge f).boundaryMultiplicity F.odd ⟨g, by simp [hgf]⟩ =
            H.boundaryMultiplicity F.odd g := by
          simp only [boundaryMultiplicity, deleteEdge, restrictEdges_mem_dangling]
        rw [hm] at hh
        simp only [if_neg hgf, if_neg hge, add_zero]
        exact_mod_cast hh
  have hsum := Finset.sum_le_sum (fun g (_ : g ∈ (Finset.univ : Finset E)) ↦
    mul_le_mul_of_nonneg_right (hcoeff g) (hx g))
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul] at hsum
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at hsum
  simpa only [sum_cutWeight_eq_boundaryMultiplicity, sum_weightedDegree] using hsum

/-- Mutual dependence cancels the two exceptional incidence contributions;
every odd component cut is tight in the original graph. -/
theorem IsBarrier.isTightCut_of_mutuallyDependent {e f : E}
    (F : (H.deleteEdge f).ComponentFamily B) (hb : F.IsBarrier)
    (hef : e ≠ f) (he0 : H.endAt e 0 ∈ B) (he1 : H.endAt e 1 ∈ B)
    (hd : H.MutuallyDependent e f) {Q : Finset V} (hQ : Q ∈ F.odd) :
    H.IsTightCut Q := by
  intro M hM
  have hs := F.deleted_internal_bound hef he0 he1 hM.isFractional.nonneg
  simp only [hM.isFractional.degree, Finset.sum_const, nsmul_eq_mul, mul_one] at hs
  rw [hd.matchingVector_eq hM] at hs
  have hp := mul_nonneg (Nat.cast_nonneg (H.endsIn B f)) (hM.isFractional.nonneg f)
  have hu : (∑ R ∈ F.odd, H.cutWeight (matchingVector M) R) ≤ B.card := by linarith
  have hl (R : Finset V) (hR : R ∈ F.odd) := hM.isFractional.odd_cut R (F.mem_odd.mp hR).2
  have heq : H.cutWeight (matchingVector M) Q = 1 := by
    by_contra hn
    have hlt := lt_of_le_of_ne (hl Q hQ) (Ne.symm hn)
    have hsum := Finset.sum_lt_sum hl ⟨Q, hQ, hlt⟩
    have hc : F.odd.card = B.card := hb
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, hc] at hsum
    linarith
  rw [cutWeight_matchingVector] at heq
  exact_mod_cast heq

/-- If a matching uses both exceptional edges, the restored edge has neither
end in the barrier. -/
theorem IsBarrier.deleted_edge_avoids {e f : E}
    (F : (H.deleteEdge f).ComponentFamily B) (hb : F.IsBarrier)
    (hef : e ≠ f) (he0 : H.endAt e 0 ∈ B) (he1 : H.endAt e 1 ∈ B)
    {M : Finset E} (hM : H.IsPerfectMatching M) (heM : e ∈ M) (hfM : f ∈ M) :
    ∀ k, H.endAt f k ∉ B := by
  have hs := F.deleted_internal_bound hef he0 he1 hM.isFractional.nonneg
  simp only [hM.isFractional.degree, Finset.sum_const, nsmul_eq_mul, mul_one] at hs
  rw [show matchingVector M e = 1 from if_pos heM,
    show matchingVector M f = 1 from if_pos hfM] at hs
  have hl : (B.card : ℚ) ≤ ∑ Q ∈ F.odd, H.cutWeight (matchingVector M) Q := by
    calc
      _ = ∑ _Q ∈ F.odd, (1 : ℚ) := by simp [show F.odd.card = B.card from hb]
      _ ≤ _ := Finset.sum_le_sum fun Q hQ ↦ hM.isFractional.odd_cut Q (F.mem_odd.mp hQ).2
  have heq : (H.endsIn B f : ℚ) = 0 := by
    have hp : (0 : ℚ) ≤ H.endsIn B f := Nat.cast_nonneg _
    linarith
  have hz : H.endsIn B f = 0 := by exact_mod_cast heq
  intro k hk
  have hp : 0 < H.endsIn B f := Finset.card_pos.mpr
    ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩
  omega

end ComponentFamily

end GraphPuzzles.LoopMultigraph
