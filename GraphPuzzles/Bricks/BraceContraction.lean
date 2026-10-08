import GraphPuzzles.Bricks.NearBrick

/-! A nonbrick near-brick has a tight cut with a brace on one side. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- The minimal bipartite side of a nontrivial tight cut is a brace.
Minimizing its number of retained vertices suffices: every further
nontrivial tight contraction would give a strictly smaller candidate. -/
theorem IsNearBrick.exists_brace_contraction (hn : H.IsNearBrick) (hb : ¬ H.IsBrick) :
    ∃ X : Finset V, IsNontrivialCut X ∧ H.IsTightCut X ∧
      (H.contract X).IsBrace ∧ (H.contract (Finset.univ \ X)).IsNearBrick := by
  classical
  have hex : ∃ X : Finset V, IsNontrivialCut X ∧ H.IsTightCut X := by
    by_contra he
    push Not at he
    exact hb ⟨hn.notBipartite, hn.matchingCovered,
      fun X ht hX ↦ he X hX ht⟩
  let Q := (Finset.univ : Finset (Finset V)).filter fun X ↦
    IsNontrivialCut X ∧ H.IsTightCut X ∧ (H.contract X).IsBipartite
  have hQ : Q.Nonempty := by
    obtain ⟨X, hX, ht⟩ := hex
    rcases hn.tight_contractions ht hX with hh | hh
    · exact ⟨X, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hX, ht, hh.1⟩⟩
    · exact ⟨Finset.univ \ X,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hX.compl, ht.compl, hh.2⟩⟩
  obtain ⟨X, hXQ, hmin⟩ := Q.exists_min_image Finset.card hQ
  obtain ⟨hX, htX, hbx⟩ := (Finset.mem_filter.mp hXQ).2
  have hsX := htX.isSeparatingCut hn.matchingCovered
    (Finset.card_pos.mp (by have := hX.1; omega))
    (Finset.card_pos.mp (by have := hX.2; omega))
  have key (Y : Finset (Option X)) (htY : (H.contract X).IsTightCut Y)
      (hY : IsNontrivialCut Y) (hp : none ∉ Y) : False := by
    let Z := sourceShore X Y
    have hZ : IsNontrivialCut Z := hX.sourceShore hY hp
    have htZ : H.IsTightCut Z := htX.lift_contract htY hp
    have hsY := htY.isSeparatingCut hsX.1
      (Finset.card_pos.mp (by have := hY.1; omega))
      (Finset.card_pos.mp (by have := hY.2; omega))
    have hby := hbx.contract_of_separating hsY
    have he : contractShore X Z = Y := contractShore_sourceShore X Y hp
    have hbz : (H.contract Z).IsBipartite := by
      apply (contractNestedIso (H := H) (sourceShore_subset X Y)).isBipartite
      change ((H.contract X).contract (contractShore X Z)).IsBipartite
      rw [he]
      exact hby
    have hZQ : Z ∈ Q := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hZ, htZ, hbz⟩
    have hle := hmin Z hZQ
    have hcard : Z.card = Y.card := card_sourceShore X Y hp
    have hcomp := hY.2
    simp only [Finset.card_sdiff_of_subset (Finset.subset_univ Y), Finset.card_univ,
      Fintype.card_option, Fintype.card_coe] at hcomp
    omega
  have hbrace : (H.contract X).IsBrace := ⟨hbx, hsX.1, by
    intro Y htY hY
    by_cases hp : none ∈ Y
    · exact key (Finset.univ \ Y) htY.compl hY.compl (by simp [hp])
    · exact key Y htY hY hp⟩
  refine ⟨X, hX, htX, hbrace, ?_⟩
  rcases hn.tight_contractions htX hX with hh | hh
  · exact hh.2
  · exact (hh.1.notBipartite hbx).elim

end GraphPuzzles.LoopMultigraph
