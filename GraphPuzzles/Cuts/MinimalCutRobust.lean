import GraphPuzzles.Bricks.BrickCharacterization
import GraphPuzzles.Cuts.MinimalCutReduction
import GraphPuzzles.Bricks.RobustNearBrick

/-!
# Minimal separating cuts are robust

Campos--Lucchesi Lemma 3.3. The recursive barrier reduction ends at a
bicritical contraction with connected pair deletions. The proved brick
characterization makes this terminal graph a brick, and bipartite tight-cut
expansion then makes the original contraction a near-brick. Apply the same
argument to the complementary shore.
-/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- Each contraction of a minimal separating cut in a brick is a near-brick. -/
theorem IsSeparatingCut.contract_isNearBrick_of_minimal {X : Finset V}
    (hs : H.IsSeparatingCut X) (hg : H.IsBrick) {M : Finset E}
    (hM : H.IsPerfectMatching M) (hcross : 1 < (M ∩ H.dangling X).card)
    (hmin : ∀ Y, H.IsSeparatingCut Y → 1 < (M ∩ H.dangling Y).card →
      H.CutPrecedes Y X → ¬ H.CutStrictlyPrecedes Y X) :
    (H.contract X).IsNearBrick := by
  obtain ⟨Y, _, hsY, heY, hbY, hcY, hexpand⟩ :=
    hs.exists_bicritical_reduction hg hM hcross hmin
  have hcrossY : 1 < (M ∩ H.dangling Y).card := by rw [heY M hM]; exact hcross
  have hY := hM.nontrivial_of_crossing_gt_one hcrossY
  have hnb := (hg.nonbipartite_contractions hsY hY).1
  exact hexpand (hsY.1.isBrick_of_bicritical hnb hbY hcY).isNearBrick

/-- Campos--Lucchesi Lemma 3.3: a minimal separating cut retaining a
specified matching's multiple crossings is robust. -/
theorem IsSeparatingCut.isRobustCut_of_minimal {X : Finset V}
    (hs : H.IsSeparatingCut X) (hg : H.IsBrick) {M : Finset E}
    (hM : H.IsPerfectMatching M) (hcross : 1 < (M ∩ H.dangling X).card)
    (hmin : ∀ Y, H.IsSeparatingCut Y → 1 < (M ∩ H.dangling Y).card →
      H.CutPrecedes Y X → ¬ H.CutStrictlyPrecedes Y X) : H.IsRobustCut X := by
  refine ⟨fun ht ↦ (by have hh := ht M hM; omega),
    hs.contract_isNearBrick_of_minimal hg hM hcross hmin, ?_⟩
  apply hs.compl.contract_isNearBrick_of_minimal hg hM
    (by simpa only [dangling_compl] using hcross)
  intro Y hsY hcrossY hp
  have hpX : H.CutPrecedes Y X := by
    simpa only [CutPrecedes, dangling_compl] using hp
  simpa only [CutStrictlyPrecedes, CutPrecedes, dangling_compl] using
    hmin Y hsY hcrossY hpX

/-- Every separating cut crossed more than once by a prescribed matching
has a robust predecessor retaining that property. -/
theorem IsSeparatingCut.exists_robust_preceding {X : Finset V}
    (hs : H.IsSeparatingCut X) (hg : H.IsBrick) {M : Finset E}
    (hM : H.IsPerfectMatching M) (hcross : 1 < (M ∩ H.dangling X).card) :
    ∃ Y, H.IsRobustCut Y ∧ 1 < (M ∩ H.dangling Y).card ∧ H.CutPrecedes Y X := by
  obtain ⟨Y, hsY, hMY, hpY, hmin⟩ := hs.exists_minimal_preceding hcross
  exact ⟨Y, hsY.isRobustCut_of_minimal hg hM hMY
    (fun Z hsZ hMZ hpZ ↦ hmin Z hsZ hMZ (hpZ.trans hpY)), hMY, hpY⟩

end GraphPuzzles.LoopMultigraph
