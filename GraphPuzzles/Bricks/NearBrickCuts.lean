import GraphPuzzles.Matching.Bipartite.TwoPoleBipartite
import GraphPuzzles.Cuts.Contraction.BipartiteExpansion

/-! Tight cuts inside near-brick contractions and the nested robust-cut reduction. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- A robust cut is nontight and both its contractions are near-bricks. -/
structure IsRobustCut (H : LoopMultigraph V E) (X : Finset V) : Prop where
  notTight : ¬ H.IsTightCut X
  leftNear : (H.contract X).IsNearBrick
  rightNear : (H.contract (Finset.univ \ X)).IsNearBrick

theorem IsRobustCut.isSeparatingCut {X : Finset V} (hr : H.IsRobustCut X) :
    H.IsSeparatingCut X := ⟨hr.leftNear.matchingCovered, hr.rightNear.matchingCovered⟩

/-- A tight cut in a near-brick contraction lifts either to a tight cut or to a cut
matching-equivalent to the outer cut. -/
theorem IsSeparatingCut.tight_in_nearBrick_contraction {X : Finset V}
    (hs : H.IsSeparatingCut X) (hb : (H.contract X).IsNearBrick)
    (hc : H.IsConnected) (hX : IsNontrivialCut X)
    {Y : Finset (Option X)} (htY : (H.contract X).IsTightCut Y)
    (hY : IsNontrivialCut Y) (hn : none ∉ Y) :
    H.IsTightCut (sourceShore X Y) ∨ H.MatchingEquivalentCuts (sourceShore X Y) X := by
  let Z := sourceShore X Y
  have hZX : Z ⊆ X := sourceShore_subset X Y
  have he : contractShore X Z = Y := contractShore_sourceShore X Y hn
  have hZ : IsNontrivialCut Z := hX.sourceShore hY hn
  have hsY := htY.isSeparatingCut hb.matchingCovered
    (Finset.card_pos.mp (by have hh := hY.1; omega))
    (Finset.card_pos.mp (by have hh := hY.2; omega))
  have hsZ : H.IsSeparatingCut Z := hs.lift_contract hsY hn hc
    (show Z.Nonempty from Finset.card_pos.mp (by have hh := hZ.1; omega))
    (show (Finset.univ \ Z).Nonempty from
      Finset.card_pos.mp (by have hh := hZ.2; omega))
  rcases hb.tight_contractions htY hY with ⟨hbY, _⟩ | ⟨_, hbYC⟩
  · have hb' : ((H.contract X).contract (contractShore X Z)).IsBipartite := he.symm ▸ hbY
    have hbZ := (contractNestedIso (H := H) hZX).isBipartite hb'
    exact Or.inl (hsZ.tight_of_bipartite hc hZ hbZ)
  · have hb' : ((H.contract X).contract (Finset.univ \ contractShore X Z)).IsBipartite :=
      he.symm ▸ hbYC
    have hbK : ((H.contract X).contract (poleShore X (Finset.univ \ Z))).IsBipartite :=
      compl_contractShore X Z ▸ hb'
    obtain ⟨e, _⟩ := hc.dangling_nonempty (X := X)
      (Finset.card_pos.mp (by have hh := hX.1; omega))
      (Finset.card_pos.mp (by have hh := hX.2; omega))
    obtain ⟨N, hN, _, hm⟩ := hs.cohesive_lift hsY hn e
    exact hbK.middle_tight_or_matchingEquivalent hZX hN (hm X (by simp)) (hm Z (by simp [Z]))

/-- The tight-or-matching-equivalent assertion in Campos--Lucchesi Lemma 3.1.
The robustness assertion is proved below in `tight_or_robust_of_tight_or_robust`. -/
theorem tight_or_matchingEquivalent_of_tight_or_robust (hm : H.IsMatchingCovered)
    {X : Finset V} (hX : IsNontrivialCut X) (hD : H.IsTightCut X ∨ H.IsRobustCut X)
    {Y : Finset (Option X)} (htY : (H.contract X).IsTightCut Y)
    (hY : IsNontrivialCut Y) (hn : none ∉ Y) :
    H.IsTightCut (sourceShore X Y) ∨ H.MatchingEquivalentCuts (sourceShore X Y) X := by
  rcases hD with ht | hr
  · exact Or.inl (ht.lift_contract htY hn)
  · exact hr.isSeparatingCut.tight_in_nearBrick_contraction hr.leftNear hm.1 hX htY hY hn

/-- The robustness and bipartite-middle assertions of the nested tight-cut reduction. -/
theorem IsRobustCut.lift_tight_of_not_tight (hm : H.IsMatchingCovered)
    {X : Finset V} (hr : H.IsRobustCut X) (hX : IsNontrivialCut X)
    {Y : Finset (Option X)} (htY : (H.contract X).IsTightCut Y)
    (hY : IsNontrivialCut Y) (hn : none ∉ Y)
    (hnt : ¬ H.IsTightCut (sourceShore X Y)) :
    H.IsRobustCut (sourceShore X Y) ∧
      ((H.contract X).contract (Finset.univ \ Y)).IsBipartite := by
  let Z := sourceShore X Y
  let W := Finset.univ \ Z
  let U := Finset.univ \ X
  have hZX : Z ⊆ X := sourceShore_subset X Y
  have hUW : U ⊆ W := by
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hz ↦ (Finset.mem_sdiff.mp hv).2 (hZX hz)⟩
  have he : contractShore X Z = Y := contractShore_sourceShore X Y hn
  have hZ : IsNontrivialCut Z := hX.sourceShore hY hn
  have hs := hr.isSeparatingCut
  have hsY := htY.isSeparatingCut hr.leftNear.matchingCovered
    (Finset.card_pos.mp (by have hh := hY.1; omega))
    (Finset.card_pos.mp (by have hh := hY.2; omega))
  have hsZ : H.IsSeparatingCut Z := hs.lift_contract hsY hn hm.1
    (show Z.Nonempty from Finset.card_pos.mp (by have hh := hZ.1; omega))
    (show (Finset.univ \ Z).Nonempty from
      Finset.card_pos.mp (by have hh := hZ.2; omega))
  have heq : H.MatchingEquivalentCuts Z X :=
    (hs.tight_in_nearBrick_contraction hr.leftNear hm.1 hX htY hY hn).resolve_left hnt
  have hparts : ((H.contract X).contract Y).IsNearBrick ∧
      ((H.contract X).contract (Finset.univ \ Y)).IsBipartite := by
    rcases hr.leftNear.tight_contractions htY hY with ⟨hb, _⟩ | h
    · have hb' : ((H.contract X).contract (contractShore X Z)).IsBipartite := he.symm ▸ hb
      have hbZ := (contractNestedIso (H := H) hZX).isBipartite hb'
      exact (hnt (hsZ.tight_of_bipartite hm.1 hZ hbZ)).elim
    · exact h
  have hleft : (H.contract Z).IsNearBrick := by
    have hh : ((H.contract X).contract (contractShore X Z)).IsNearBrick := he.symm ▸ hparts.1
    exact (contractNestedIso (H := H) hZX).isNearBrick hh
  have hright : (H.contract W).IsNearBrick := by
    let T := contractShore W U
    have htT : (H.contract W).IsTightCut T := by
      intro M hM
      obtain ⟨P, hP, hc, heM⟩ := hM.extend_contract_exact hsZ.compl.2
      rw [← heM, contractMatching_crossing W T (none_not_mem_contractShore W U),
        sourceShore_contractShore, Finset.inter_eq_right.mpr hUW]
      have hh := heq P hP
      simpa only [U, W, dangling_compl, hh] using hc
    have hT : IsNontrivialCut T := by
      have hcT : T.card = U.card := card_contractShore_of_subset hUW
      have hcZ : Z.card = Y.card := card_sourceShore X Y hn
      have hy := hY.2
      have hx := hX.2
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ Y), Finset.card_univ,
        Fintype.card_option, Fintype.card_coe] at hy
      refine ⟨by rw [hcT]; exact hx, ?_⟩
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ T), Finset.card_univ,
        Fintype.card_option, Fintype.card_coe, hcT]
      have hW : W.card = Fintype.card V - Z.card := by simp [W, Finset.card_sdiff]
      have hU : U.card = Fintype.card V - X.card := by simp [U, Finset.card_sdiff]
      have hxle := Finset.card_le_card (Finset.subset_univ X)
      simp only [Finset.card_univ] at hxle
      omega
    have hnear : ((H.contract W).contract T).IsNearBrick :=
      (contractNestedIso (H := H) hUW).symm.isNearBrick hr.rightNear
    have hb : ((H.contract W).contract (Finset.univ \ T)).IsBipartite := by
      have hb' : ((H.contract X).contract (Finset.univ \ contractShore X Z)).IsBipartite :=
        he.symm ▸ hparts.2
      have hb'' : ((H.contract X).contract (poleShore X W)).IsBipartite :=
        compl_contractShore X Z ▸ hb'
      have hu : X ∪ W = Finset.univ := by
        ext v
        simp only [W, Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and, iff_true]
        by_cases hx : v ∈ X
        · exact Or.inl hx
        · exact Or.inr (fun hz ↦ hx (hZX hz))
      have hh := (contractCommuteIso (H := H) hu).isBipartite hb''
      have heT : Finset.univ \ T = poleShore W X := by
        rw [compl_contractShore]
        congr 1
        exact Finset.sdiff_sdiff_eq_self (Finset.subset_univ X)
      exact heT.symm ▸ hh
    exact IsNearBrick.of_tight_contractions_left hsZ.2 htT hT hnear hb
  exact ⟨⟨hnt, hleft, hright⟩, hparts.2⟩

/-- Campos--Lucchesi Lemma 3.1 for a nontrivial tight cut in the contraction. -/
theorem tight_or_robust_of_tight_or_robust (hm : H.IsMatchingCovered)
    {X : Finset V} (hX : IsNontrivialCut X) (hD : H.IsTightCut X ∨ H.IsRobustCut X)
    {Y : Finset (Option X)} (htY : (H.contract X).IsTightCut Y)
    (hY : IsNontrivialCut Y) (hn : none ∉ Y) :
    H.IsTightCut (sourceShore X Y) ∨
      (H.MatchingEquivalentCuts (sourceShore X Y) X ∧
        H.IsRobustCut (sourceShore X Y) ∧
        ((H.contract X).contract (Finset.univ \ Y)).IsBipartite) := by
  by_cases ht : H.IsTightCut (sourceShore X Y)
  · exact Or.inl ht
  · rcases hD with hd | hr
    · exact (ht (hd.lift_contract htY hn)).elim
    · have heq := (hr.isSeparatingCut.tight_in_nearBrick_contraction
        hr.leftNear hm.1 hX htY hY hn).resolve_left ht
      exact Or.inr ⟨heq, hr.lift_tight_of_not_tight hm hX htY hY hn ht⟩

end GraphPuzzles.LoopMultigraph
