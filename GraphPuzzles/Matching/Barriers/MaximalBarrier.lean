import GraphPuzzles.Matching.Barriers.ComponentRefinement

/-!
# Maximal barriers

In a graph with a perfect matching, every component left by a maximal barrier
is odd and factor-critical. These facts are used to construct the
Dulmage--Mendelsohn barriers in the ELP proof.
-/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

namespace ComponentFamily

variable {Z : Finset V} (F : H.ComponentFamily Z)

/-- The separator is a barrier, and no strictly larger separator is a barrier. -/
structure IsMaximalBarrier : Prop where
  isBarrier : F.IsBarrier
  maximal : ∀ (B : Finset V) (P : H.ComponentFamily B), P.IsBarrier → Z ⊆ B → B = Z

/-- A maximal barrier has no even components, without requiring the graph to
be matching covered. -/
theorem IsMaximalBarrier.odd_parts (hm : F.IsMaximalBarrier)
    {M : Finset E} (hM : H.IsPerfectMatching M) {Q : Finset V} (hQ : Q ∈ F.parts) :
    Odd Q.card := by
  by_contra hnQ
  obtain ⟨w, hw⟩ := F.nonempty Q hQ
  have hT : ({w} : Finset V) ⊆ Q := Finset.singleton_subset_iff.mpr hw
  obtain ⟨P, _⟩ := H.exists_componentFamily ((Finset.univ \ Q) ∪ {w})
  have hpar := P.odd_card_mod_two
  have heq : Finset.univ \ ((Finset.univ \ Q) ∪ {w}) = Q.erase w := by
    ext v
    simp
  rw [heq, Finset.card_erase_of_mem hw] at hpar
  have hQeven := Nat.not_odd_iff_even.mp hnQ
  rw [Nat.even_iff] at hQeven
  have hpQ := Finset.card_pos.mpr (F.nonempty Q hQ)
  have hpP : 1 ≤ P.odd.card := by omega
  have hnot : Q ∉ F.odd := fun h ↦ hnQ (F.mem_odd.mp h).2
  let R := F.refinePart hQ hT P
  have hc := F.refinePart_odd_card hQ hT P
  rw [Finset.erase_eq_of_notMem hnot] at hc
  have hz := F.refinePart_separator_card hQ hT
  simp only [Finset.card_singleton] at hz
  have hZ : F.odd.card = Z.card := hm.isBarrier
  have hbound := R.odd_card_le_of_fractional hM.isFractional
  have hb : R.IsBarrier := by
    change R.odd.card = (Z ∪ {w}).card
    change R.odd.card = F.odd.card + P.odd.card at hc
    omega
  have he := hm.maximal _ R hb Finset.subset_union_left
  have hwZ : w ∈ Z := he ▸ Finset.mem_union_right Z (Finset.mem_singleton_self w)
  exact F.avoid Q hQ w hw hwZ

/-- Every component of a maximal barrier is factor-critical. A Tutte obstruction
after deleting one vertex would refine the component and enlarge the barrier. -/
theorem IsMaximalBarrier.factorCritical_parts (hm : F.IsMaximalBarrier)
    {M : Finset E} (hM : H.IsPerfectMatching M) {Q : Finset V} (hQ : Q ∈ F.parts) :
    H.IsFactorCritical Q := by
  intro w hw
  by_contra hno
  have ho := hm.odd_parts F hM hQ
  have heven : Even (Q.erase w).card := by
    rw [Finset.card_erase_of_mem hw, Nat.even_iff]
    rw [Nat.odd_iff] at ho
    omega
  obtain ⟨T, hT, P, hP⟩ := exists_componentFamily_of_no_matchingOn_even (Q.erase w) heven hno
  let U := insert w T
  have hU : U ⊆ Q := Finset.insert_subset hw (hT.trans (Finset.erase_subset _ _))
  have hwT : w ∉ T := fun h ↦ (Finset.mem_erase.mp (hT h)).1 rfl
  have hcU : U.card = T.card + 1 := Finset.card_insert_of_notMem hwT
  have hsep : (Finset.univ \ Q.erase w) ∪ T = (Finset.univ \ Q) ∪ U := by
    ext v
    simp only [U, Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_erase, Finset.mem_insert]
    tauto
  have hex : ∃ P' : H.ComponentFamily ((Finset.univ \ Q) ∪ U), T.card + 2 ≤ P'.odd.card := by
    rw [← hsep]
    exact ⟨P, hP⟩
  obtain ⟨P', hP'⟩ := hex
  let R := F.refinePart hQ hU P'
  have hc := F.refinePart_odd_card hQ hU P'
  change R.odd.card = (F.odd.erase Q).card + P'.odd.card at hc
  have hQodd : Q ∈ F.odd := F.mem_odd.mpr ⟨hQ, ho⟩
  have he := Finset.card_erase_add_one hQodd
  have hz := F.refinePart_separator_card hQ hU
  have hZ : F.odd.card = Z.card := hm.isBarrier
  have hbound := R.odd_card_le_of_fractional hM.isFractional
  have hb : R.IsBarrier := by
    change R.odd.card = (Z ∪ U).card
    omega
  have heq := hm.maximal _ R hb Finset.subset_union_left
  have hwZ : w ∈ Z := heq ▸ Finset.mem_union_right Z (Finset.mem_insert_self w T)
  exact F.avoid Q hQ w hw hwZ

end ComponentFamily

omit [DecidableEq E] in
/-- Every barrier extends to an inclusion-maximal barrier. -/
theorem ComponentFamily.IsBarrier.exists_maximal {Z : Finset V}
    {F : H.ComponentFamily Z} (hF : F.IsBarrier) :
    ∃ B, Z ⊆ B ∧ ∃ P : H.ComponentFamily B, P.IsMaximalBarrier := by
  classical
  let C := Finset.univ.filter fun B : Finset V ↦ Z ⊆ B ∧ ∃ P : H.ComponentFamily B, P.IsBarrier
  have hZ : Z ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.Subset.refl _, F, hF⟩
  obtain ⟨B, hB, hmax⟩ := C.exists_max_image Finset.card ⟨Z, hZ⟩
  obtain ⟨hZB, P, hP⟩ := (Finset.mem_filter.mp hB).2
  refine ⟨B, hZB, P, hP, ?_⟩
  intro T R hR hBT
  have hTC : T ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hZB.trans hBT, R, hR⟩
  exact (Finset.eq_of_subset_of_card_le hBT (hmax T hTC)).symm

/-- A graph with a perfect matching has a maximal barrier. -/
theorem IsPerfectMatching.exists_maximal_barrier {M : Finset E} (hM : H.IsPerfectMatching M) :
    ∃ B, ∃ F : H.ComponentFamily B, F.IsMaximalBarrier := by
  obtain ⟨F, _⟩ := H.exists_componentFamily ∅
  have hb : F.IsBarrier := by
    have hh := F.odd_card_le_of_fractional hM.isFractional
    simpa only [ComponentFamily.IsBarrier, Finset.card_empty, Nat.le_zero] using hh
  obtain ⟨B, _, P, hP⟩ := hb.exists_maximal
  exact ⟨B, P, hP⟩

end GraphPuzzles.LoopMultigraph
