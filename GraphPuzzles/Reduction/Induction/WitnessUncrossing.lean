import GraphPuzzles.Reduction.Induction.WitnessInduction
import GraphPuzzles.Petersen.Minors.TightPetersenNeighborhood
import GraphPuzzles.Cuts.CrossingTightCut

/-! Section 6, Proposition 6.1: uncrossing a witness into an inner witness or an attachment. -/

namespace GraphPuzzles.LoopMultigraph

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- A nontrivial tight shore inside the selected intersection of a witness
contraction lifts to another witness contained in that intersection. -/
theorem IsCutWitness.lift_internal_tight {X Y : Finset V}
    (hw : H.IsCutWitness X Y) (hb : H.IsBrick)
    {Z : Finset (Option Y)} (ht : (H.contract Y).IsTightCut Z)
    (hZ : IsNontrivialCut Z) (hsub : Z ⊆ contractShore Y X) :
    H.IsCutWitness X (sourceShore Y Z) ∧ sourceShore Y Z ⊆ X ∩ Y := by
  have hY := hw.robust.nontrivial hb.matchingCovered
  have hp : none ∉ Z := fun h ↦ (none_not_mem_contractShore Y X) (hsub h)
  have hS := hY.sourceShore hZ hp
  have hnt : ¬ H.IsTightCut (sourceShore Y Z) := fun h ↦ hb.tight_trivial _ h hS
  have heq := (hw.robust.isSeparatingCut.tight_in_nearBrick_contraction
    hw.robust.leftNear hb.matchingCovered.1 hY ht hZ hp).resolve_left hnt
  have hr := (hw.robust.lift_tight_of_not_tight hb.matchingCovered hY ht hZ hp hnt).1
  refine ⟨⟨hr, hw.cohesive.pair_predecessor
    (matchingEquivalentCuts_iff_precedes.mp heq).1
    (hr.isSeparatingCut.odd_shore hb.matchingCovered.1 hS),
    fun h ↦ hw.notEquivalent (heq.symm.trans h)⟩, ?_⟩
  have hh := sourceShore_mono hsub
  rw [sourceShore_contractShore] at hh
  simpa only [Finset.inter_comm] using hh

/-- Proposition 6.1 with its preceding successful induction alternative
retained: a crossing witness yields a three-crossing matching, an inner
witness, or a single attachment from the odd intersection to the far shore. -/
theorem IsCutWitness.three_or_inner_witness_or_attachment {X Y : Finset V}
    (hw : H.IsCutWitness X Y) (hb : H.IsBrick)
    (hcross : CutsCross X Y) (ho : Odd (X ∩ Y).card)
    (ih : NearBrickCutInductionHypothesis.{u, v} H.inductionSize) :
    (∃ M, H.IsPerfectMatching M ∧ (M ∩ H.dangling X).card = 3) ∨
    (∃ Z, H.IsCutWitness X Z ∧ Z ⊆ X ∩ Y) ∨
    (∃ i ∈ X ∩ Y, ∀ a ∈ X ∩ Y, ∀ w, w ∉ Y → ∀ e, H.Joins e w a → a = i) := by
  classical
  let A := contractShore Y X
  have hY := hw.robust.nontrivial hb.matchingCovered
  have hcard : (X ∩ Y).card = A.card := by
    have hh := card_sourceShore Y A (none_not_mem_contractShore Y X)
    rw [sourceShore_contractShore, Finset.inter_comm] at hh
    exact hh
  by_cases hA : IsNontrivialCut A
  · by_cases hex : ∃ Z, (H.contract Y).IsTightCut Z ∧ IsNontrivialCut Z ∧ Z ⊆ A
    · obtain ⟨Z, htZ, hZ, hsub⟩ := hex
      exact Or.inr (Or.inl ⟨sourceShore Y Z, hw.lift_internal_tight hb htZ hZ hsub⟩)
    · have hsA := hw.cohesive.separating_intersection_contract hb.matchingCovered.1
        (Finset.card_pos.mp (by have hh := hY.2; omega)) ho
      have hoA := hsA.odd_shore hw.robust.leftNear.matchingCovered.1 hA
      rcases ih (H.contract Y) (inductionSize_contract_lt hY) hw.robust.leftNear A hsA with
        h3 | ht | ⟨_, hp⟩
      · obtain ⟨M, hM, hM3⟩ := (cutCharacteristic_eq_three_iff hoA).mp h3
        obtain ⟨N, hN, hNM⟩ := hw.cohesive.extend_intersection_matching ho hM
        exact Or.inl ⟨N, hN, hNM.trans hM3⟩
      · exact (hex ⟨A, (cutCharacteristic_eq_top_iff_tight hoA).mp ht,
          hA, Finset.Subset.refl _⟩).elim
      · have hno : (H.contract Y).HasNoInternalTightCut A :=
          fun Z htZ hZ hsub ↦ hex ⟨Z, htZ, hZ, hsub⟩
        have hN := hp.unique_cross_neighbor A (Or.inl rfl) hno
        exact Or.inr (Or.inr (hN.exists_attachment hcross.1))
  · have hcomp : 2 ≤ (Finset.univ \ A).card := by
      have hp := Finset.card_pos.mpr hcross.2.2.1
      have hh := Finset.card_sdiff_add_card_inter Y X
      rw [Finset.inter_comm Y X, hcard] at hh
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ A), Finset.card_univ,
        Fintype.card_option, Fintype.card_coe]
      omega
    have hpos := Finset.card_pos.mpr hcross.1
    have hone : (X ∩ Y).card = 1 := by
      have hnot : ¬ 2 ≤ A.card := fun h ↦ hA ⟨h, hcomp⟩
      omega
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hone
    refine Or.inr (Or.inr ⟨i, ?_, ?_⟩)
    · rw [hi]
      exact Finset.mem_singleton_self _
    · intro a ha _ _ _ _
      simpa only [hi, Finset.mem_singleton] using ha

end GraphPuzzles.LoopMultigraph
