import GraphPuzzles.Cuts.Shores.UniqueShoreNeighbors
import GraphPuzzles.Petersen.PetersenCuts

/-! Neighbor uniqueness on a shore that survives a tight Petersen reduction. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- No outside vertex can be adjacent to two vertices of a surviving
Petersen shore. In Case 2 this is applied to the first contraction pole. -/
theorem HasTightPetersenMinor.unique_cross_neighbor {X : Finset V}
    (h : H.HasTightPetersenMinor X) (S : Finset V)
    (hSX : S = X ∨ S = Finset.univ \ X) (hno : H.HasNoInternalTightCut S) :
    H.HasUniqueCrossNeighbor S := by
  induction h with
  | here hp hs =>
    obtain ⟨f⟩ := hp
    have hsS := hSX.elim (fun h ↦ h.symm ▸ hs) (fun h ↦ h.symm ▸ hs.compl)
    have hsP := (f.isStrictlySeparatingCut_iff S).mp hsS
    exact (HasUniqueCrossNeighbor.of_perfect_dangling
      hsP.petersen_dangling_isPerfectMatching).of_parallelReduction f
  | @contract V' E' _ _ _ _ G Y ht hY X hp _ ih =>
    rcases hSX with rfl | rfl
    · apply HasUniqueCrossNeighbor.of_contract hp
      apply ih X (Or.inl rfl)
      intro Z htZ hZ hZX
      have hpZ : none ∉ Z := fun hn ↦ hp (hZX hn)
      exact hno (sourceShore Y Z) (ht.lift_contract htZ hpZ)
        (hY.sourceShore hZ hpZ) (sourceShore_mono hZX)
    · exact (hno (Finset.univ \ Y) ht.compl hY.compl (by
        intro v hv
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
          fun h ↦ (Finset.mem_sdiff.mp hv).2 (sourceShore_subset Y X h)⟩)).elim
  | @compl V' E' _ _ _ _ G Z _ ih =>
    have hh : S = Z ∨ S = Finset.univ \ Z := by
      rcases hSX with h | h
      · exact Or.inr h
      · exact Or.inl (by simpa only [Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)] using h)
    exact ih S hh hno
  | @iso V' W' E' F' _ _ _ _ _ _ _ _ G K Z f _ ih =>
    let U := f.symm.mapVertices S
    have hU : U = Z ∨ U = Finset.univ \ Z := by
      rcases hSX with rfl | rfl
      · exact Or.inl (f.symm_mapVertices_mapVertices _)
      · exact Or.inr (by
          dsimp only [U]
          rw [← f.mapVertices_compl, f.symm_mapVertices_mapVertices])
    have hnoU : G.HasNoInternalTightCut U := by
      intro Y htY hY hsub
      apply hno (f.mapVertices Y) (f.isTightCut htY) ((f.nontrivial_mapVertices Y).mpr hY)
      have hh : f.mapVertices Y ⊆ f.mapVertices U := Finset.map_subset_map.mpr hsub
      simpa only [U, f.mapVertices_symm_mapVertices] using hh
    exact (ih U hU hnoU).of_parallelReduction f.symm.parallelReduction

end GraphPuzzles.LoopMultigraph
