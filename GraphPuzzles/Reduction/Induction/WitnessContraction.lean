import GraphPuzzles.Reduction.Induction.NearBrickInduction
import GraphPuzzles.Petersen.Minors.TightPetersenRigidity

/-! Maximal witnesses in the noncrossing case of the main induction. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

theorem IsRobustCut.compl {X : Finset V} (hr : H.IsRobustCut X) :
    H.IsRobustCut (Finset.univ \ X) := by
  refine ⟨fun ht ↦ hr.notTight ?_, hr.rightNear, ?_⟩
  · simpa only [Finset.sdiff_sdiff_eq_self (Finset.subset_univ X)] using ht.compl
  · rw [Finset.sdiff_sdiff_eq_self (Finset.subset_univ X)]
    exact hr.leftNear

theorem IsCutWitness.compl_witness {X Y : Finset V} (hw : H.IsCutWitness X Y) :
    H.IsCutWitness X (Finset.univ \ Y) := by
  refine ⟨hw.robust.compl, ?_, ?_⟩
  · simpa only [Finset.image_insert, Finset.image_singleton,
      Finset.sdiff_sdiff_eq_self (Finset.subset_univ X)] using hw.compl.cohesive.compls
  · simpa only [MatchingEquivalentCuts, dangling_compl] using hw.notEquivalent

/-- A shore disjoint from a witness is a proper subset of the retained
shore: equality would make the two cuts matching-equivalent. -/
theorem IsCutWitness.ssubset_compl {X Y : Finset V} (hw : H.IsCutWitness X Y)
    (hXY : X ⊆ Finset.univ \ Y) : X ⊂ Finset.univ \ Y := by
  refine Finset.ssubset_iff_subset_ne.mpr ⟨hXY, ?_⟩
  intro he
  apply hw.notEquivalent
  intro M _
  rw [he, dangling_compl]

theorem IsCutWitness.nontrivial_contractShore {X Y : Finset V}
    (hw : H.IsCutWitness X Y) (hX : IsNontrivialCut X)
    (hXY : X ⊆ Finset.univ \ Y) :
    IsNontrivialCut (contractShore (Finset.univ \ Y) X) := by
  have hc := card_contractShore_of_subset hXY
  have hlt := Finset.card_lt_card (hw.ssubset_compl hXY)
  refine ⟨by rw [hc]; exact hX.1, ?_⟩
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    Fintype.card_option, Fintype.card_coe, hc]
  omega

/-- Contracting a disjoint witness does not make the selected cut tight. -/
theorem IsCutWitness.not_tight_contract {X Y : Finset V} (hw : H.IsCutWitness X Y)
    (hb : H.IsBrick) (hX : IsNontrivialCut X) (hXY : X ⊆ Finset.univ \ Y) :
    ¬ (H.contract (Finset.univ \ Y)).IsTightCut (contractShore (Finset.univ \ Y) X) := by
  intro ht
  have he : sourceShore (Finset.univ \ Y) (contractShore (Finset.univ \ Y) X) = X := by
    rw [sourceShore_contractShore, Finset.inter_eq_right.mpr hXY]
  have hr := hw.robust.compl
  have hh := hr.isSeparatingCut.tight_in_nearBrick_contraction hr.leftNear
    hb.matchingCovered.1 (hr.nontrivial hb.matchingCovered) ht
    (hw.nontrivial_contractShore hX hXY) (none_not_mem_contractShore _ _)
  rw [he] at hh
  rcases hh with htX | heq
  · exact hb.tight_trivial X htX hX
  · apply hw.notEquivalent
    intro M hM
    simpa only [dangling_compl] using (heq M hM).symm

/-- A nontight separating cut cannot be contained in either shore of a
bipartite region. With a common excluded pole this fixes its nested orientation. -/
theorem IsSeparatingCut.subset_of_noncrossing_bipartite {X Y : Finset V}
    (hs : H.IsSeparatingCut X) (hc : H.IsConnected) (hX : IsNontrivialCut X)
    (hnt : ¬ H.IsTightCut X) (hnc : ¬ CutsCross X Y)
    (hb : (H.contract (Finset.univ \ Y)).IsBipartite)
    (p : V) (hpX : p ∉ X) (hpY : p ∉ Y) : X ⊆ Y := by
  rcases (not_cutsCross_iff X Y).mp hnc with h | h | h | h
  · exact h
  · exact (hnt (hs.tight_of_bipartite hc hX
      ((hb.induced_of_contract.mono h).contract_of_separating hs))).elim
  · exact (hpY (h (by simp [hpX]))).elim
  · have ht := hs.compl.tight_of_bipartite hc hX.compl
      ((hb.induced_of_contract.mono h).contract_of_separating hs.compl)
    exact (hnt (by simpa only [Finset.sdiff_sdiff_eq_self (Finset.subset_univ X)]
      using ht.compl)).elim

/-- A finite family of witnesses disjoint from the selected shore has a
member with the largest shore. -/
theorem exists_maximal_disjoint_witness {X : Finset V}
    (hex : ∃ Y, H.IsCutWitness X Y ∧ Y ⊆ Finset.univ \ X) :
    ∃ Y, H.IsCutWitness X Y ∧ Y ⊆ Finset.univ \ X ∧
      ∀ Z, H.IsCutWitness X Z → Z ⊆ Finset.univ \ X → Z.card ≤ Y.card := by
  classical
  let C := Finset.univ.filter fun Y : Finset V ↦ H.IsCutWitness X Y ∧ Y ⊆ Finset.univ \ X
  obtain ⟨Y, hw, hs⟩ := hex
  have hC : C.Nonempty := ⟨Y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw, hs⟩⟩
  obtain ⟨Z, hZ, hm⟩ := C.exists_max_image Finset.card hC
  obtain ⟨hwZ, hsZ⟩ := (Finset.mem_filter.mp hZ).2
  exact ⟨Z, hwZ, hsZ, fun W hwW hsW ↦
    hm W (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwW, hsW⟩)⟩

/-- In the contraction across a largest disjoint witness, every nontrivial
tight cut crosses the selected cut. This is the maximality argument of
Section 6, Case 3. -/
theorem IsCutWitness.tight_crossing_of_maximal {X Y : Finset V}
    (hw : H.IsCutWitness X Y) (hb : H.IsBrick) (hsX : H.IsSeparatingCut X)
    (hX : IsNontrivialCut X) (hXY : X ⊆ Finset.univ \ Y)
    (hmax : ∀ Z, H.IsCutWitness X Z → Z ⊆ Finset.univ \ X → Z.card ≤ Y.card) :
    ∀ Z, (H.contract (Finset.univ \ Y)).IsTightCut Z → IsNontrivialCut Z →
      CutsCross (contractShore (Finset.univ \ Y) X) Z := by
  let R := Finset.univ \ Y
  let A := contractShore R X
  have hr : H.IsRobustCut R := hw.robust.compl
  have hR := hr.nontrivial hb.matchingCovered
  have hA : IsNontrivialCut A := hw.nontrivial_contractShore hX hXY
  have ho : Odd (X ∩ R).card := by
    rw [Finset.inter_eq_left.mpr hXY]
    exact hsX.odd_shore hb.matchingCovered.1 hX
  have hsA : (H.contract R).IsSeparatingCut A :=
    hw.compl_witness.cohesive.separating_intersection_contract hb.matchingCovered.1
      (Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0 < 2) hR.2)) ho
  have hntA : ¬ (H.contract R).IsTightCut A := hw.not_tight_contract hb hX hXY
  have key (Z : Finset (Option R)) (ht : (H.contract R).IsTightCut Z)
      (hZ : IsNontrivialCut Z) (hp : none ∉ Z) : CutsCross A Z := by
    by_contra hn
    let S := sourceShore R Z
    have hS : IsNontrivialCut S := hR.sourceShore hZ hp
    have hntS : ¬ H.IsTightCut S := fun hh ↦ hb.tight_trivial S hh hS
    have heq : H.MatchingEquivalentCuts S R :=
      (hr.isSeparatingCut.tight_in_nearBrick_contraction hr.leftNear hb.matchingCovered.1
        hR ht hZ hp).resolve_left hntS
    obtain ⟨hrS, hbZ⟩ := hr.lift_tight_of_not_tight hb.matchingCovered hR ht hZ hp hntS
    have hAZ := hsA.subset_of_noncrossing_bipartite hr.leftNear.matchingCovered.1 hA
      hntA hn hbZ none (none_not_mem_contractShore _ _) hp
    have hXS : X ⊆ S := by
      intro x hx
      have hh : some ⟨x, hXY hx⟩ ∈ Z := hAZ ((some_mem_contractShore R X _).mpr hx)
      exact Finset.mem_image.mpr ⟨⟨x, hXY hx⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩, rfl⟩
    have heqY : H.MatchingEquivalentCuts S Y := by
      intro M hM
      simpa only [R, dangling_compl] using heq M hM
    have hwS : H.IsCutWitness X S := by
      refine ⟨hrS, hw.cohesive.pair_predecessor
        (matchingEquivalentCuts_iff_precedes.mp heqY).1
        (hrS.isSeparatingCut.odd_shore hb.matchingCovered.1 hS), ?_⟩
      exact fun hh ↦ hw.notEquivalent (heqY.symm.trans hh)
    have hT : Finset.univ \ S ⊆ Finset.univ \ X := by
      intro x hx
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
        fun hxX ↦ (Finset.mem_sdiff.mp hx).2 (hXS hxX)⟩
    have hle := hmax (Finset.univ \ S) hwS.compl_witness hT
    have hsCard : S.card = Z.card := card_sourceShore R Z hp
    have hzCard := hZ.2
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ Z), Finset.card_univ,
      Fintype.card_option, Fintype.card_coe] at hzCard
    have hsumS := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
    have hsumY := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ Y)
    rw [Finset.card_univ] at hsumS hsumY
    change R.card + Y.card = Fintype.card V at hsumY
    omega
  intro Z ht hZ
  by_cases hp : none ∈ Z
  · exact (cutsCross_compl_right A Z).mp (key (Finset.univ \ Z) ht.compl hZ.compl (by simp [hp]))
  · exact key Z ht hZ hp

end GraphPuzzles.LoopMultigraph
