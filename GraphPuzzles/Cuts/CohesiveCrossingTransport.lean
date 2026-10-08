import GraphPuzzles.Cuts.CutCharacteristic

/-! Extension of matchings from the uncrossed shores of a cohesive pair. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- Extend a matching from one contraction so that its crossing count on the intersection
becomes the crossing count on the original cut. Cohesiveness supplies the other half. -/
theorem IsCohesiveCuts.extend_intersection_matching {X Y : Finset V}
    (hc : H.IsCohesiveCuts {X, Y}) (ho : Odd (X ∩ Y).card)
    {M : Finset (H.meets Y)} (hM : (H.contract Y).IsPerfectMatching M) :
    ∃ P, H.IsPerfectMatching P ∧ (P ∩ H.dangling X).card =
      (M ∩ (H.contract Y).dangling (contractShore Y X)).card := by
  have hcu := hc.uncross (X := X) (Y := Y) (by simp) (by simp) ho
  let e := hM.contractBoundary
  have he := hM.contract_boundary_mem.2
  obtain ⟨Q, hQ, heQ, hq⟩ := hcu e
  have hqY : (Q ∩ H.dangling Y).card = 1 := hq Y (by simp)
  have hqU : (Q ∩ H.dangling (X ∪ Y)).card = 1 := hq (X ∪ Y) (by simp)
  have hqYC : (Q ∩ H.dangling (Finset.univ \ Y)).card = 1 := by
    simpa only [dangling_compl] using hqY
  let N := H.contractMatching (Finset.univ \ Y) Q
  have hN : (H.contract (Finset.univ \ Y)).IsPerfectMatching N :=
    hQ.contract_of_crossing_one _ hqYC
  have he' : e ∈ H.dangling (Finset.univ \ Y) := by simpa only [dangling_compl] using he
  have heN : e ∈ N.image Subtype.val := Finset.mem_image.mpr
    ⟨⟨e, dangling_subset_meets _ he'⟩, (mem_contractMatching _ _ _).mpr heQ, rfl⟩
  have hag : hM.contractBoundary = hN.contractBoundary := (hN.contract_boundary_iff he').mp heN
  let P := M.image Subtype.val ∪ N.image Subtype.val
  have hP : H.IsPerfectMatching P :=
    glue_contract_matchings hM hN (contract_boundary_agreement hM hN hag)
  have hpY : (P ∩ H.dangling Y).card = 1 := glue_contract_cut_card hM hN hag
  have hpYC : (P ∩ H.dangling (Finset.univ \ Y)).card = 1 := by
    simpa only [dangling_compl] using hpY
  have hpM := hM.contractMatching_eq_of_subset hP hpY Finset.subset_union_left
  have hpN := hN.contractMatching_eq_of_subset hP hpYC Finset.subset_union_right
  have hI : sourceShore Y (contractShore Y X) = X ∩ Y := by
    rw [sourceShore_contractShore, Finset.inter_comm]
  have hU : sourceShore (Finset.univ \ Y)
      (contractShore (Finset.univ \ Y) (Finset.univ \ X)) = Finset.univ \ (X ∪ Y) := by
    rw [sourceShore_contractShore]
    ext v
    simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_union, not_or]
    tauto
  have hpU : (P ∩ H.dangling (X ∪ Y)).card = 1 := by
    have hhP := contractMatching_crossing (H := H) (Finset.univ \ Y)
      (contractShore (Finset.univ \ Y) (Finset.univ \ X))
      (none_not_mem_contractShore _ _) P
    have hhQ := contractMatching_crossing (H := H) (Finset.univ \ Y)
      (contractShore (Finset.univ \ Y) (Finset.univ \ X))
      (none_not_mem_contractShore _ _) Q
    rw [hU, dangling_compl, hpN] at hhP
    rw [hU, dangling_compl, hqU] at hhQ
    exact hhP.symm.trans hhQ
  have hpI := contractMatching_crossing (H := H) Y (contractShore Y X)
    (none_not_mem_contractShore _ _) P
  rw [hI, hpM] at hpI
  have hm := hc.crossing_modular (X := X) (Y := Y) (by simp) (by simp) ho P
  exact ⟨P, hP, by omega⟩

/-- One half of the characteristic bound for crossing cohesive cuts. -/
theorem IsCohesiveCuts.characteristic_le_intersection {X Y : Finset V}
    (hc : H.IsCohesiveCuts {X, Y}) (ho : Odd (X ∩ Y).card) :
    H.cutCharacteristic X ≤ (H.contract Y).cutCharacteristic (contractShore Y X) := by
  apply Finset.min_mono
  intro n hn
  obtain ⟨hm, hgt⟩ := Finset.mem_filter.mp hn
  obtain ⟨M, hM, hm⟩ := mem_matchingCrossings.mp hm
  obtain ⟨P, hP, hp⟩ := hc.extend_intersection_matching ho hM
  exact Finset.mem_filter.mpr ⟨mem_matchingCrossings.mpr ⟨P, hP, hp.trans hm⟩, hgt⟩

/-- The other half of the bound, represented by the complementary shores. -/
theorem IsCohesiveCuts.characteristic_le_complement_intersection {X Y : Finset V}
    (hc : H.IsCohesiveCuts {X, Y})
    (ho : Odd ((Finset.univ \ X) ∩ (Finset.univ \ Y)).card) :
    H.cutCharacteristic X ≤ (H.contract (Finset.univ \ Y)).cutCharacteristic
      (contractShore (Finset.univ \ Y) (Finset.univ \ X)) := by
  have hc' : H.IsCohesiveCuts {Finset.univ \ X, Finset.univ \ Y} := by
    simpa only [Finset.image_insert, Finset.image_singleton] using hc.compls
  simpa only [cutCharacteristic_compl] using hc'.characteristic_le_intersection ho

/-- Campos--Lucchesi Lemma 4.6(iii), equality when the second cut is tight.
Both odd regions are explicit; matching-coveredness supplies their parity in applications. -/
theorem IsCohesiveCuts.characteristic_eq_min_of_tight {X Y : Finset V}
    (hc : H.IsCohesiveCuts {X, Y}) (ho : Odd (X ∩ Y).card)
    (ho' : Odd ((Finset.univ \ X) ∩ (Finset.univ \ Y)).card) (ht : H.IsTightCut Y) :
    H.cutCharacteristic X = min
      ((H.contract Y).cutCharacteristic (contractShore Y X))
      ((H.contract (Finset.univ \ Y)).cutCharacteristic
        (contractShore (Finset.univ \ Y) (Finset.univ \ X))) := by
  apply le_antisymm
  · exact le_min (hc.characteristic_le_intersection ho)
      (hc.characteristic_le_complement_intersection ho')
  · apply Finset.le_min
    intro n hn
    obtain ⟨hm, hgt⟩ := Finset.mem_filter.mp hn
    obtain ⟨M, hM, hmn⟩ := mem_matchingCrossings.mp hm
    have hmY := ht M hM
    have hmYC := ht.compl M hM
    have hmod := hc.crossing_modular (X := X) (Y := Y) (by simp) (by simp) ho M
    have hleft := contractMatching_crossing (H := H) Y (contractShore Y X)
      (none_not_mem_contractShore _ _) M
    rw [sourceShore_contractShore, Finset.inter_comm Y X] at hleft
    have hU : (Finset.univ \ Y) ∩ (Finset.univ \ X) = Finset.univ \ (X ∪ Y) := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ, true_and,
        Finset.mem_union, not_or]
      tauto
    have hright := contractMatching_crossing (H := H) (Finset.univ \ Y)
      (contractShore (Finset.univ \ Y) (Finset.univ \ X))
      (none_not_mem_contractShore _ _) M
    rw [sourceShore_contractShore, hU, dangling_compl] at hright
    simp only [contractMatching] at hleft hright
    have hpI := hM.crossing_mod_two (X ∩ Y)
    have hpU := hM.crossing_mod_two ((Finset.univ \ Y) ∩ (Finset.univ \ X))
    rw [hU, dangling_compl] at hpU
    have hoU : Odd (Finset.univ \ (X ∪ Y)).card := by
      rwa [Finset.inter_comm, hU] at ho'
    rw [Nat.odd_iff] at ho hoU
    by_cases hbig : 1 < (M ∩ H.dangling (X ∩ Y)).card
    · have hle := cutCharacteristic_le (X := contractShore Y X)
        (hM.contract_of_crossing_one Y hmY) (hleft.symm ▸ hbig)
      rw [hleft] at hle
      have hbound : (M ∩ H.dangling (X ∩ Y)).card ≤ n := by omega
      exact (min_le_left _ _).trans (hle.trans (WithTop.coe_le_coe.mpr hbound))
    · have hbigU : 1 < (M ∩ H.dangling (X ∪ Y)).card := by omega
      have hle := cutCharacteristic_le
        (X := contractShore (Finset.univ \ Y) (Finset.univ \ X))
        (hM.contract_of_crossing_one _ hmYC) (hright.symm ▸ hbigU)
      rw [hright] at hle
      have hbound : (M ∩ H.dangling (X ∪ Y)).card ≤ n := by omega
      exact (min_le_right _ _).trans (hle.trans (WithTop.coe_le_coe.mpr hbound))

/-- The complementary region is odd whenever the cohesive pair has a nontrivial shore
in a connected graph. -/
theorem IsCohesiveCuts.odd_complement_intersection {X Y : Finset V}
    (hc : H.IsCohesiveCuts {X, Y}) (hconn : H.IsConnected) (hn : IsNontrivialCut Y)
    (ho : Odd (X ∩ Y).card) : Odd ((Finset.univ \ X) ∩ (Finset.univ \ Y)).card := by
  obtain ⟨e, _⟩ := hconn.dangling_nonempty (X := Y)
    (Finset.card_pos.mp (by have hh := hn.1; omega))
    (Finset.card_pos.mp (by have hh := hn.2; omega))
  obtain ⟨M, hM, _, hm⟩ := hc e
  have hX := hM.odd_of_crossing_one (hm X (by simp))
  have hY := hM.odd_of_crossing_one (hm Y (by simp))
  have hU := hM.isFractional.odd_compl (odd_union_of_odd_inter hX hY ho)
  have he : (Finset.univ \ X) ∩ (Finset.univ \ Y) = Finset.univ \ (X ∪ Y) := by
    ext v
    simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_union, not_or]
  rwa [he]

/-- The equality in Lemma 4.6 with the second region's parity derived. -/
theorem IsCohesiveCuts.characteristic_uncross_tight {X Y : Finset V}
    (hc : H.IsCohesiveCuts {X, Y}) (hconn : H.IsConnected) (hn : IsNontrivialCut Y)
    (ho : Odd (X ∩ Y).card) (ht : H.IsTightCut Y) :
    H.cutCharacteristic X = min
      ((H.contract Y).cutCharacteristic (contractShore Y X))
      ((H.contract (Finset.univ \ Y)).cutCharacteristic
        (contractShore (Finset.univ \ Y) (Finset.univ \ X))) :=
  hc.characteristic_eq_min_of_tight ho (hc.odd_complement_intersection hconn hn ho) ht

/-- The intersection cut is separating in the contraction retaining it. -/
theorem IsCohesiveCuts.separating_intersection_contract {X Y : Finset V}
    (hc : H.IsCohesiveCuts {X, Y}) (hconn : H.IsConnected)
    (hYC : (Finset.univ \ Y).Nonempty) (ho : Odd (X ∩ Y).card) :
    (H.contract Y).IsSeparatingCut (contractShore Y X) := by
  have hcu := hc.uncross (X := X) (Y := Y) (by simp) (by simp) ho
  have hsource : sourceShore Y (contractShore Y X) = X ∩ Y := by
    rw [sourceShore_contractShore, Finset.inter_comm]
  have hcp : H.IsCohesiveCuts {Y, sourceShore Y (contractShore Y X)} := by
    apply hcu.subset
    intro Z hZ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hZ ⊢
    rw [hsource] at hZ
    tauto
  have hnonempty : (contractShore Y X).Nonempty := by
    apply Finset.card_pos.mp
    rw [← card_sourceShore Y (contractShore Y X) (none_not_mem_contractShore _ _), hsource]
    exact ho.pos
  exact hcp.separating_contract (hconn.contract Y hYC) hnonempty
    ⟨none, by simp⟩ (none_not_mem_contractShore _ _)

/-- Both cuts appearing in the characteristic formula are separating in their contractions. -/
theorem IsCohesiveCuts.separating_uncrossed_contracts {X Y : Finset V}
    (hc : H.IsCohesiveCuts {X, Y}) (hconn : H.IsConnected) (hn : IsNontrivialCut Y)
    (ho : Odd (X ∩ Y).card) :
    (H.contract Y).IsSeparatingCut (contractShore Y X) ∧
      (H.contract (Finset.univ \ Y)).IsSeparatingCut
        (contractShore (Finset.univ \ Y) (Finset.univ \ X)) := by
  refine ⟨hc.separating_intersection_contract hconn
    (Finset.card_pos.mp (by have hh := hn.2; omega)) ho, ?_⟩
  have hc' : H.IsCohesiveCuts {Finset.univ \ X, Finset.univ \ Y} := by
    simpa only [Finset.image_insert, Finset.image_singleton] using hc.compls
  apply hc'.separating_intersection_contract hconn ?_
    (hc.odd_complement_intersection hconn hn ho)
  rw [Finset.sdiff_sdiff_eq_self (Finset.subset_univ Y)]
  exact Finset.card_pos.mp (by have hh := hn.1; omega)

end GraphPuzzles.LoopMultigraph
