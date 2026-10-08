import GraphPuzzles.Matching.Barriers.BarrierPrecedence

/-! Barriers of separating-cut contractions of a brick. -/

namespace GraphPuzzles.LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

namespace ComponentFamily

variable {Z : Finset V} (F : H.ComponentFamily Z)

/-- Only the degree constraints on the barrier and the bounds on its odd
components are needed for the equality case. -/
theorem IsBarrier.cutWeight_one_of_constraints (hb : F.IsBarrier)
    (hm : H.IsMatchingCovered) {x : E → ℚ}
    (hd : ∀ v ∈ Z, H.weightedDegree x v = 1)
    (ho : ∀ Q ∈ F.odd, 1 ≤ H.cutWeight x Q)
    {Q : Finset V} (hQ : Q ∈ F.odd) : H.cutWeight x Q = 1 := by
  have hs := hb.sum_cutWeight_eq_sum_degree F hm x
  have hh : (∑ v ∈ Z, H.weightedDegree x v) = Z.card := by
    calc
      _ = ∑ _v ∈ Z, (1 : ℚ) := Finset.sum_congr rfl hd
      _ = _ := by simp
  rw [hh] at hs
  by_contra hne
  have hlt := lt_of_le_of_ne (ho Q hQ) (Ne.symm hne)
  have hsum : (∑ _R ∈ F.odd, (1 : ℚ)) < ∑ R ∈ F.odd, H.cutWeight x R :=
    Finset.sum_lt_sum ho ⟨Q, hQ, hlt⟩
  have hc : F.odd.card = Z.card := hb
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, hs, hc, lt_self_iff_false] at hsum

end ComponentFamily

/-- Absence of a barrier with at least two vertices implies bicriticality. -/
theorem IsMatchingCovered.isBicritical_of_no_barrier (hm : H.IsMatchingCovered)
    (hn : ∀ (B : Finset V) (F : H.ComponentFamily B), F.IsBarrier → B.card ≤ 1) :
    H.IsBicritical := by
  intro u v huv
  obtain ⟨e, _⟩ := hm.1.dangling_nonempty (X := {u})
    (Finset.singleton_nonempty u) ⟨v, by simp [Ne.symm huv]⟩
  obtain ⟨M, hM, _⟩ := hm.2 e
  by_contra hno
  obtain ⟨B₀, hu, hv, F, hge⟩ := exists_componentFamily_of_no_matching hm.loopless
    hM.isFractional.card_even huv hno
  have hB : (B₀ ∪ {u, v}).card = B₀.card + 2 := by
    rw [Finset.card_union_of_disjoint, Finset.card_pair huv]
    rw [Finset.disjoint_insert_right, Finset.disjoint_singleton_right]
    exact ⟨hu, hv⟩
  have hle := F.odd_card_le_of_fractional hM.isFractional
  have hb : F.IsBarrier := by
    change F.odd.card = (B₀ ∪ {u, v}).card
    omega
  have hh := hn _ F hb
  omega

namespace ContractionBarrier

variable {X : Finset V} {B : Finset (Option X)}
variable (F : (H.contract X).ComponentFamily B)

/-- If a barrier avoids the contraction vertex, its component cuts are tight
even for restrictions of original fractional matchings. -/
theorem cutWeight_one_of_pole_not_mem (hb : F.IsBarrier)
    (hm : (H.contract X).IsMatchingCovered) (hX : Odd X.card) (hn : none ∉ B)
    {x : E → ℚ} (hx : H.IsFractionalPerfectMatching x)
    {Q : Finset (Option X)} (hQ : Q ∈ F.odd) :
    (H.contract X).cutWeight (fun e ↦ x e.1) Q = 1 := by
  apply hb.cutWeight_one_of_constraints F hm ?_ ?_ hQ
  · intro v hv
    cases v with
    | none => exact (hn hv).elim
    | some v => exact (contract_weightedDegree_some X x v).trans (hx.degree v.1)
  · intro R hR
    exact hx.contract_odd_cut X hX R (F.mem_odd.mp hR).2

/-- Every barrier with at least two vertices in a brick's nontrivial
separating-cut contraction contains the contraction vertex. -/
theorem none_mem_of_brick (hb : F.IsBarrier) (hg : H.IsBrick)
    (hs : H.IsSeparatingCut X) (hX : IsNontrivialCut X) (hB : 2 ≤ B.card) :
    none ∈ B := by
  by_contra hn
  have hBne : B.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨Q, hQ, hnQ⟩ := F.cover none hn
  have hQo := hb.mem_odd_of_mem F hs.1 hBne hQ
  have hnQC : none ∉ Finset.univ \ Q := by simp [hnQ]
  have ht : H.IsTightCut (sourceShore X (Finset.univ \ Q)) := by
    intro M hM
    have hh := cutWeight_one_of_pole_not_mem F hb hs.1
      (hs.odd_shore hg.matchingCovered.1 hX) hn hM.isFractional hQo
    have hh' : (H.contract X).cutWeight (fun e ↦ matchingVector M e.1)
        (Finset.univ \ Q) = 1 := by
      simpa only [cutWeight_compl] using hh
    rw [contract_cutWeight_sourceShore X (Finset.univ \ Q) hnQC,
      cutWeight_matchingVector] at hh'
    exact_mod_cast hh'
  have hBQ : B ⊆ Finset.univ \ Q := by
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h ↦ F.avoid Q hQ v h hv⟩
  have hleft := Finset.card_le_card hBQ
  rw [← card_sourceShore X (Finset.univ \ Q) hnQC] at hleft
  have hsub : Finset.univ \ X ⊆ Finset.univ \ sourceShore X (Finset.univ \ Q) := by
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hh ↦
      (Finset.mem_sdiff.mp hv).2 (sourceShore_subset X (Finset.univ \ Q) hh)⟩
  have hright := Finset.card_le_card hsub
  exact hg.tight_trivial _ ht ⟨by omega, by have hh := hX.2; omega⟩

/-- Any nontrivial barrier of a minimal separating cut admits the smaller-shore
reduction, without assuming where the contraction vertex lies. -/
theorem exists_reduction_of_minimal_barrier (hb : F.IsBarrier) (hs : H.IsSeparatingCut X)
    (hg : H.IsBrick) (hB : 2 ≤ B.card) {M : Finset E} (hM : H.IsPerfectMatching M)
    (hcross : 1 < (M ∩ H.dangling X).card)
    (hmin : ∀ Y, H.IsSeparatingCut Y → 1 < (M ∩ H.dangling Y).card →
      H.CutPrecedes Y X → ¬ H.CutStrictlyPrecedes Y X) :
    ∃ Q ∈ F.odd, IsNontrivialCut Q ∧
      (H.contract X).IsTightCut Q ∧
      H.IsSeparatingCut (sourceShore X Q) ∧
      H.MatchingEquivalentCuts (sourceShore X Q) X ∧
      ((H.contract X).contract (Finset.univ \ Q)).IsBipartite ∧
      (sourceShore X Q).card < X.card :=
  exists_reduction_of_minimal F hb hs hg
    (none_mem_of_brick F hb hg hs (hM.nontrivial_of_crossing_gt_one hcross) hB)
    hB hM hcross hmin

end ContractionBarrier

/-- Among matching-equivalent separating shores, a smallest shore has a
bicritical contraction whenever its cut is minimal in the precedence order. -/
theorem IsSeparatingCut.bicritical_contract_of_minimum_shore {X : Finset V}
    (hs : H.IsSeparatingCut X) (hg : H.IsBrick) {M : Finset E}
    (hM : H.IsPerfectMatching M) (hcross : 1 < (M ∩ H.dangling X).card)
    (hmin : ∀ Y, H.IsSeparatingCut Y → 1 < (M ∩ H.dangling Y).card →
      H.CutPrecedes Y X → ¬ H.CutStrictlyPrecedes Y X)
    (hcard : ∀ Y, H.IsSeparatingCut Y → H.MatchingEquivalentCuts Y X → X.card ≤ Y.card) :
    (H.contract X).IsBicritical := by
  apply hs.1.isBicritical_of_no_barrier
  intro B F hb
  by_contra hn
  have hB : 2 ≤ B.card := by omega
  obtain ⟨Q, _, _, _, hsep, heq, _, hlt⟩ :=
    ContractionBarrier.exists_reduction_of_minimal_barrier F hb hs hg hB hM hcross hmin
  exact (not_lt_of_ge (hcard _ hsep heq)) hlt

/-- A minimal separating cut has a matching-equivalent representative whose
one contraction is bicritical. This does not yet assert robustness. -/
theorem IsSeparatingCut.exists_equivalent_bicritical_contraction {X : Finset V}
    (hs : H.IsSeparatingCut X) (hg : H.IsBrick) {M : Finset E}
    (hM : H.IsPerfectMatching M) (hcross : 1 < (M ∩ H.dangling X).card)
    (hmin : ∀ Y, H.IsSeparatingCut Y → 1 < (M ∩ H.dangling Y).card →
      H.CutPrecedes Y X → ¬ H.CutStrictlyPrecedes Y X) :
    ∃ Y, H.IsSeparatingCut Y ∧ H.MatchingEquivalentCuts Y X ∧
      Y.card ≤ X.card ∧ (H.contract Y).IsBicritical := by
  classical
  let C := Finset.univ.filter fun Y ↦ H.IsSeparatingCut Y ∧ H.MatchingEquivalentCuts Y X
  have hCX : X ∈ C := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hs, MatchingEquivalentCuts.refl X⟩
  obtain ⟨Y, hY, hsmall⟩ := C.exists_min_image Finset.card ⟨X, hCX⟩
  obtain ⟨hsY, heq⟩ := (Finset.mem_filter.mp hY).2
  have hpre := matchingEquivalentCuts_iff_precedes.mp heq
  refine ⟨Y, hsY, heq, hsmall X hCX,
    hsY.bicritical_contract_of_minimum_shore hg hM ?_ ?_ ?_⟩
  · rw [heq M hM]
    exact hcross
  · intro Z hsZ hZM hZY hstrict
    apply hmin Z hsZ hZM (hZY.trans hpre.1)
    obtain ⟨_, N, hN, hlt⟩ := hstrict
    exact ⟨hZY.trans hpre.1, N, hN, by simpa only [heq N hN] using hlt⟩
  · intro Z hsZ heZ
    apply hsmall Z
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsZ, heZ.trans heq⟩

end GraphPuzzles.LoopMultigraph
