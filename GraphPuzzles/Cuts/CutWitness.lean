import GraphPuzzles.Cuts.MinimalCutRobust

/-!
# Witnesses and solid contractions

Campos--Lucchesi Lemma 6.2 reduces a nontrivial separating cut of a brick
to a robust cut with solid contractions, unless another robust cut is
cohesive with it and has different matching crossing counts.
-/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- A separating cut whose two contractions are nonbipartite. -/
structure IsStrictlySeparatingCut (H : LoopMultigraph V E) (X : Finset V) : Prop where
  separating : H.IsSeparatingCut X
  leftNonbipartite : ¬ (H.contract X).IsBipartite
  rightNonbipartite : ¬ (H.contract (Finset.univ \ X)).IsBipartite

/-- Solid graphs have no strictly separating cut. -/
def IsSolid (H : LoopMultigraph V E) : Prop := ∀ X, ¬ H.IsStrictlySeparatingCut X

omit [DecidableEq E] in
theorem IsStrictlySeparatingCut.compl {X : Finset V} (hs : H.IsStrictlySeparatingCut X) :
    H.IsStrictlySeparatingCut (Finset.univ \ X) := by
  refine ⟨hs.separating.compl, hs.rightNonbipartite, ?_⟩
  rw [Finset.sdiff_sdiff_eq_self (Finset.subset_univ X)]
  exact hs.leftNonbipartite

theorem IsStrictlySeparatingCut.nontrivial {X : Finset V}
    (hs : H.IsStrictlySeparatingCut X) (hm : H.IsMatchingCovered) : IsNontrivialCut X := by
  constructor
  · by_contra hn
    exact hs.leftNonbipartite (bipartite_contract_of_card_le_one hm.loopless (by omega))
  · by_contra hn
    exact hs.rightNonbipartite (bipartite_contract_of_card_le_one hm.loopless (by omega))

/-- A strictly separating cut of a near-brick cannot be tight. -/
theorem IsStrictlySeparatingCut.not_tight {X : Finset V}
    (hs : H.IsStrictlySeparatingCut X) (hb : H.IsNearBrick) : ¬ H.IsTightCut X := by
  intro ht
  rcases hb.noStrictTightCut X ht (hs.nontrivial hb.matchingCovered) with h | h
  · exact hs.leftNonbipartite h
  · exact hs.rightNonbipartite h

/-- A nontight separating cut has a matching crossing more than once. -/
theorem IsSeparatingCut.exists_crossing_gt_one {X : Finset V}
    (hs : H.IsSeparatingCut X) (hc : H.IsConnected) (hX : IsNontrivialCut X)
    (hnt : ¬ H.IsTightCut X) :
    ∃ M, H.IsPerfectMatching M ∧ 1 < (M ∩ H.dangling X).card := by
  change ¬ ∀ M, H.IsPerfectMatching M → (M ∩ H.dangling X).card = 1 at hnt
  push Not at hnt
  obtain ⟨M, hM, hn⟩ := hnt
  have ho := hs.odd_shore hc hX
  have hp := hM.crossing_mod_two X
  rw [Nat.odd_iff] at ho
  exact ⟨M, hM, by omega⟩

/-- A witness for `X` is a robust cut cohesive with `X` but not
matching-equivalent to it (Campos--Lucchesi, Section 6). -/
structure IsCutWitness (H : LoopMultigraph V E) (X Y : Finset V) : Prop where
  robust : H.IsRobustCut Y
  cohesive : H.IsCohesiveCuts {X, Y}
  notEquivalent : ¬ H.MatchingEquivalentCuts Y X

theorem IsCutWitness.compl {X Y : Finset V} (hw : H.IsCutWitness X Y) :
    H.IsCutWitness (Finset.univ \ X) Y := by
  refine ⟨hw.robust, ?_, ?_⟩
  · intro e
    obtain ⟨M, hM, he, hc⟩ := hw.cohesive e
    refine ⟨M, hM, he, ?_⟩
    intro Z hZ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hZ
    rcases hZ with rfl | rfl
    · simpa only [dangling_compl] using hc X (by simp)
    · exact hc _ (by simp)
  · simpa only [MatchingEquivalentCuts, dangling_compl] using hw.notEquivalent

/-- Precedence transfers a cohesive pair to a separating predecessor. -/
theorem IsCohesiveCuts.pair_predecessor {X Y Z : Finset V}
    (hc : H.IsCohesiveCuts {X, Y}) (hp : H.CutPrecedes Z Y) (ho : Odd Z.card) :
    H.IsCohesiveCuts {X, Z} := by
  apply (hc.insert_of_precedes (by simp : Y ∈ ({X, Y} : Finset (Finset V))) hp ho).subset
  intro W hW
  simp only [Finset.mem_insert, Finset.mem_singleton] at hW ⊢
  tauto

/-- The first part of Lemma 6.2: absence of a witness forces robustness. -/
theorem IsSeparatingCut.witness_or_robust {X : Finset V} (hs : H.IsSeparatingCut X)
    (hg : H.IsBrick) (hX : IsNontrivialCut X) :
    (∃ Y, H.IsCutWitness X Y) ∨ H.IsRobustCut X := by
  classical
  obtain ⟨M, hM, _, hcross⟩ := hg.exists_crossing_at_least_three hs hX
  have hcross' : 1 < (M ∩ H.dangling X).card := by omega
  obtain ⟨Y, hsY, hMY, hp, hmin⟩ := hs.exists_minimal_preceding hcross'
  have hminY : ∀ Z, H.IsSeparatingCut Z → 1 < (M ∩ H.dangling Z).card →
      H.CutPrecedes Z Y → ¬ H.CutStrictlyPrecedes Z Y :=
    fun Z hsZ hMZ hpZ ↦ hmin Z hsZ hMZ (hpZ.trans hp)
  have hr := hsY.isRobustCut_of_minimal hg hM hMY hminY
  by_cases he : H.MatchingEquivalentCuts Y X
  · exact Or.inr (hs.isRobustCut_of_minimal hg hM hcross' (he.symm.transfer_minimal hminY))
  · refine Or.inl ⟨Y, hr, ?_, he⟩
    intro e
    obtain ⟨N, hN, heN, hcN⟩ := hs.exists_perfectMatching_through e
    have hNY := hp.facePrecedes (hsY.odd_shore hg.matchingCovered.1
      (hM.nontrivial_of_crossing_gt_one hMY)) N hN hcN
    refine ⟨N, hN, heN, ?_⟩
    intro Z hZ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hZ
    rcases hZ with rfl | rfl
    · exact hcN
    · exact hNY

/-- A strictly separating cut in a robust-cut contraction provides a witness
in the original brick. The extended matching distinguishes the two cuts. -/
theorem IsRobustCut.exists_witness_of_not_solid {X : Finset V} (hr : H.IsRobustCut X)
    (hg : H.IsBrick) (hn : ¬ (H.contract X).IsSolid) : ∃ Z, H.IsCutWitness X Z := by
  classical
  change ¬ ∀ Y, ¬ (H.contract X).IsStrictlySeparatingCut Y at hn
  push Not at hn
  obtain ⟨Y₀, hY₀⟩ := hn
  have hy : ∃ Y, (H.contract X).IsStrictlySeparatingCut Y ∧ none ∉ Y := by
    by_cases hnY : none ∈ Y₀
    · exact ⟨Finset.univ \ Y₀, hY₀.compl, by simp [hnY]⟩
    · exact ⟨Y₀, hY₀, hnY⟩
  obtain ⟨Y, hY, hnY⟩ := hy
  have hYnt := hY.nontrivial hr.leftNear.matchingCovered
  obtain ⟨N, hN, hNY⟩ := hY.separating.exists_crossing_gt_one
    hr.leftNear.matchingCovered.1 hYnt (hY.not_tight hr.leftNear)
  obtain ⟨M, hM, hMX, heM⟩ := hN.extend_contract_exact hr.isSeparatingCut.2
  let D := sourceShore X Y
  have hMD : 1 < (M ∩ H.dangling D).card := by
    rw [← contractMatching_crossing X Y hnY, heM]
    exact hNY
  have hDnt := (hr.nontrivial hg.matchingCovered).sourceShore hYnt hnY
  have hsD := hr.isSeparatingCut.lift_contract hY.separating hnY hg.matchingCovered.1
    (Finset.card_pos.mp (by have hh := hDnt.1; omega))
    (Finset.card_pos.mp (by have hh := hDnt.2; omega))
  obtain ⟨Z, hrZ, hMZ, hpZ⟩ := hsD.exists_robust_preceding hg hM hMD
  have hoZ := hrZ.isSeparatingCut.odd_shore hg.matchingCovered.1 (hrZ.nontrivial hg.matchingCovered)
  refine ⟨Z, hrZ, (hr.isSeparatingCut.cohesive_lift hY.separating hnY).pair_predecessor hpZ hoZ, ?_⟩
  intro he
  have hh := he M hM
  omega

/-- Campos--Lucchesi Lemma 6.2: a separating cut of a brick either has a
witness or is robust with both contractions solid. -/
theorem IsSeparatingCut.witness_or_robust_solid {X : Finset V} (hs : H.IsSeparatingCut X)
    (hg : H.IsBrick) (hX : IsNontrivialCut X) :
    (∃ Y, H.IsCutWitness X Y) ∨
      (H.IsRobustCut X ∧ (H.contract X).IsSolid ∧ (H.contract (Finset.univ \ X)).IsSolid) := by
  classical
  rcases hs.witness_or_robust hg hX with hw | hr
  · exact Or.inl hw
  · by_cases hl : (H.contract X).IsSolid
    · by_cases hrc : (H.contract (Finset.univ \ X)).IsSolid
      · exact Or.inr ⟨hr, hl, hrc⟩
      · have hrC : H.IsRobustCut (Finset.univ \ X) := by
          refine ⟨?_, hr.rightNear, ?_⟩
          · simpa only [IsTightCut, dangling_compl] using hr.notTight
          · rw [Finset.sdiff_sdiff_eq_self (Finset.subset_univ X)]
            exact hr.leftNear
        obtain ⟨Z, hZ⟩ := hrC.exists_witness_of_not_solid hg hrc
        exact Or.inl ⟨Z, by simpa only [Finset.sdiff_sdiff_eq_self (Finset.subset_univ X)] using hZ.compl⟩
    · exact Or.inl (hr.exists_witness_of_not_solid hg hl)

end GraphPuzzles.LoopMultigraph
