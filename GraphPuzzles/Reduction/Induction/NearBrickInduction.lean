import GraphPuzzles.Petersen.Minors.TightPetersenMinor
import GraphPuzzles.Cuts.CohesiveCrossingTransport
import GraphPuzzles.Cuts.CutCrossing

/-! The decreasing measure and nested tight-cut step in the main induction. -/

namespace GraphPuzzles.LoopMultigraph

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- Counting vertices and labelled edges decreases under both nontrivial
shore contractions and edge deletions. -/
def inductionSize (_H : LoopMultigraph V E) : ℕ := Fintype.card V + Fintype.card E

omit [DecidableEq E] in
theorem inductionSize_contract_lt {X : Finset V} (hX : IsNontrivialCut X) :
    (H.contract X).inductionSize < H.inductionSize := by
  have hcard := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ X)
  have he := Finset.card_le_univ (H.meets X)
  simp only [inductionSize, Fintype.card_option, Fintype.card_coe]
  rw [Finset.card_univ] at hcard
  have hh := hX.2
  omega

/-- Only strictly smaller graphs may be used by an induction step. -/
def NearBrickCutInductionHypothesis (n : ℕ) : Prop :=
  ∀ {V' : Type u} {E' : Type v} [Fintype V'] [Fintype E'] [DecidableEq V'] [DecidableEq E']
    (G : LoopMultigraph V' E'), G.inductionSize < n → G.IsNearBrick →
      ∀ X : Finset V', G.IsSeparatingCut X → G.NearBrickCutConclusion X

/-- A tight contraction preserves the whole conclusion, including its
cut-preserving Petersen certificate. -/
theorem NearBrickCutConclusion.lift_tight {Y : Finset V} (ht : H.IsTightCut Y)
    (hY : IsNontrivialCut Y) (hsY : H.IsSeparatingCut Y)
    {X : Finset (Option Y)} (hp : none ∉ X)
    (h : (H.contract Y).NearBrickCutConclusion X) :
    H.NearBrickCutConclusion (sourceShore Y X) := by
  have he := ht.characteristic_contract hsY X hp
  rcases h with h3 | hi | ⟨h5, hm⟩
  · exact Or.inl (he.symm.trans h3)
  · exact Or.inr (Or.inl (he.symm.trans hi))
  · exact Or.inr (Or.inr ⟨he.symm.trans h5, .contract Y ht hY X hp hm⟩)

/-- Section 6, Case 1 in nested-shore form. The complementary orientations
follow by replacing either shore by its complement. -/
theorem IsNearBrick.cutConclusion_of_nested_tight (hn : H.IsNearBrick)
    (ih : NearBrickCutInductionHypothesis.{u, v} H.inductionSize)
    {X Y : Finset V} (hsX : H.IsSeparatingCut X) (hX : IsNontrivialCut X)
    (hXY : X ⊆ Y) (htY : H.IsTightCut Y) (hY : IsNontrivialCut Y) :
    H.NearBrickCutConclusion X := by
  have hsY := htY.isSeparatingCut hn.matchingCovered
    (Finset.card_pos.mp (by have := hY.1; omega))
    (Finset.card_pos.mp (by have := hY.2; omega))
  have ho := hsX.odd_shore hn.matchingCovered.1 hX
  rcases hn.tight_contractions htY hY with hh | hh
  · obtain ⟨c, hc⟩ := hh.1.induced_of_contract
    have hbx : H.IsBipartiteOn X := ⟨c, fun e h0 h1 ↦ hc e (hXY h0) (hXY h1)⟩
    have htX := hsX.tight_of_bipartite hn.matchingCovered.1 hX
      (hbx.contract_of_separating hsX)
    exact Or.inr (Or.inl ((cutCharacteristic_eq_top_iff_tight ho).mpr htX))
  · have hcoh := hsX.cohesive_pair_tight htY
    have hi : Odd (X ∩ Y).card := by simpa only [Finset.inter_eq_left.mpr hXY] using ho
    have hs := hcoh.separating_intersection_contract hn.matchingCovered.1
      (Finset.card_pos.mp (by have := hY.2; omega)) hi
    have hc := ih (H.contract Y) (inductionSize_contract_lt hY) hh.1 (contractShore Y X) hs
    have hl := hc.lift_tight htY hY hsY (none_not_mem_contractShore Y X)
    simpa only [sourceShore_contractShore, Finset.inter_eq_right.mpr hXY] using hl

/-- Section 6, Case 1, with no orientation chosen in advance. -/
theorem IsNearBrick.cutConclusion_of_noncrossing_tight (hn : H.IsNearBrick)
    (ih : NearBrickCutInductionHypothesis.{u, v} H.inductionSize)
    {X Y : Finset V} (hsX : H.IsSeparatingCut X) (hX : IsNontrivialCut X)
    (htY : H.IsTightCut Y) (hY : IsNontrivialCut Y) (hcross : ¬ CutsCross X Y) :
    H.NearBrickCutConclusion X := by
  rcases (not_cutsCross_iff X Y).mp hcross with h | h | h | h
  · exact hn.cutConclusion_of_nested_tight ih hsX hX h htY hY
  · exact hn.cutConclusion_of_nested_tight ih hsX hX h htY.compl hY.compl
  · have hh := (hn.cutConclusion_of_nested_tight ih hsX.compl hX.compl h htY hY).compl
    simpa only [Finset.sdiff_sdiff_eq_self (Finset.subset_univ X)] using hh
  · have hh := (hn.cutConclusion_of_nested_tight ih hsX.compl hX.compl h
      htY.compl hY.compl).compl
    simpa only [Finset.sdiff_sdiff_eq_self (Finset.subset_univ X)] using hh

end GraphPuzzles.LoopMultigraph
