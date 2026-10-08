import GraphPuzzles.Cuts.Contraction.ContractionTwoSeparation

/-!
# Reducing a minimal separating cut

Repeated barrier reductions terminate at a bicritical contraction with connected
pair deletions. The proof also retains the implication needed to expand a
near-brick back through all the discarded bipartite tight-cut sides.
`MinimalCutRobust` completes this reduction using `BrickCharacterization`.
-/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- Minimality transfers to a matching-equivalent cut. -/
theorem MatchingEquivalentCuts.transfer_minimal {X Y : Finset V}
    (heq : H.MatchingEquivalentCuts Y X) {M : Finset E}
    (hmin : ∀ Z, H.IsSeparatingCut Z → 1 < (M ∩ H.dangling Z).card →
      H.CutPrecedes Z X → ¬ H.CutStrictlyPrecedes Z X) :
    ∀ Z, H.IsSeparatingCut Z → 1 < (M ∩ H.dangling Z).card →
      H.CutPrecedes Z Y → ¬ H.CutStrictlyPrecedes Z Y := by
  have hp := (matchingEquivalentCuts_iff_precedes.mp heq).1
  intro Z hs hcross hpre hstrict
  apply hmin Z hs hcross (hpre.trans hp)
  obtain ⟨_, N, hN, hlt⟩ := hstrict
  exact ⟨hpre.trans hp, N, hN, by simpa only [heq N hN] using hlt⟩

/-- A minimal separating cut reduces to a bicritical contraction with connected
pair deletions. If the terminal contraction is a near-brick, so is the original
contraction, by the proved expansion theorem. -/
theorem IsSeparatingCut.exists_bicritical_reduction {X : Finset V}
    (hs : H.IsSeparatingCut X) (hg : H.IsBrick) {M : Finset E}
    (hM : H.IsPerfectMatching M) (hcross : 1 < (M ∩ H.dangling X).card)
    (hmin : ∀ Y, H.IsSeparatingCut Y → 1 < (M ∩ H.dangling Y).card →
      H.CutPrecedes Y X → ¬ H.CutStrictlyPrecedes Y X) :
    ∃ Y, Y ⊆ X ∧ H.IsSeparatingCut Y ∧ H.MatchingEquivalentCuts Y X ∧
      (H.contract Y).IsBicritical ∧ (H.contract Y).ConnectedAfterDeletingPairs ∧
      ((H.contract Y).IsNearBrick → (H.contract X).IsNearBrick) := by
  classical
  induction hn : X.card using Nat.strong_induction_on generalizing X with
  | h n ih =>
    by_cases hb : (H.contract X).IsBicritical
    · exact ⟨X, Finset.Subset.refl _, hs, MatchingEquivalentCuts.refl X, hb,
        hs.connectedAfterDeletingPairs_of_minimal_bicritical hg hb hM hcross hmin, id⟩
    · have hex : ∃ (B : Finset (Option X)) (F : (H.contract X).ComponentFamily B),
          F.IsBarrier ∧ 2 ≤ B.card := by
        by_contra hno
        push Not at hno
        apply hb
        apply hs.1.isBicritical_of_no_barrier
        intro B F hF
        have hh := hno B F hF
        omega
      obtain ⟨B, F, hF, hB⟩ := hex
      obtain ⟨Q, hQ, hQnt, htQ, hsZ, heq, hbmid, hlt⟩ :=
        ContractionBarrier.exists_reduction_of_minimal_barrier F hF hs hg hB hM hcross hmin
      let Z := sourceShore X Q
      change Z.card < X.card at hlt
      have hZX : Z ⊆ X := sourceShore_subset X Q
      have hMZ : 1 < (M ∩ H.dangling Z).card := by rw [heq M hM]; exact hcross
      have hminZ := heq.transfer_minimal hmin
      obtain ⟨Y, hYZ, hsY, heY, hbcY, hcY, hexpand⟩ :=
        ih Z.card (by omega) hsZ hMZ hminZ rfl
      refine ⟨Y, hYZ.trans hZX, hsY, heY.trans heq, hbcY, hcY, ?_⟩
      intro hbY
      have hbZ : (H.contract Z).IsNearBrick := hexpand hbY
      have hnQ : none ∉ Q := ContractionBarrier.none_not_mem F
        (ContractionBarrier.none_mem_of_brick F hF hg hs
          (hM.nontrivial_of_crossing_gt_one hcross) hB) (F.mem_odd.mp hQ).1
      have hQS : contractShore X Z = Q := contractShore_sourceShore X Q hnQ
      have hleft : ((H.contract X).contract Q).IsNearBrick := by
        have hh := (contractNestedIso (H := H) hZX).symm.isNearBrick hbZ
        exact hQS ▸ hh
      exact IsNearBrick.of_tight_contractions_left hs.1 htQ hQnt hleft hbmid

end GraphPuzzles.LoopMultigraph
