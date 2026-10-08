import GraphPuzzles.Cuts.CutCharacteristic

/-! Characteristic infinity for trivial and bipartite separating cuts. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

theorem cutCharacteristic_eq_top_of_not_nontrivial {X : Finset V}
    (hX : ¬ IsNontrivialCut X) : H.cutCharacteristic X = ⊤ := by
  apply cutCharacteristic_eq_top_iff.mpr
  intro M hM
  by_contra hh
  exact hX (hM.nontrivial_of_crossing_gt_one (Nat.lt_of_not_ge hh))

/-- Every singleton is tight: an odd matching crossing cannot exceed one. -/
theorem isTightCut_singleton (H : LoopMultigraph V E) (w : V) : H.IsTightCut {w} := by
  apply (cutCharacteristic_eq_top_iff_tight (by simp : Odd ({w} : Finset V).card)).mp
  exact cutCharacteristic_eq_top_of_not_nontrivial (by simp [IsNontrivialCut])

theorem IsBipartite.cutCharacteristic_eq_top_of_separating (hb : H.IsBipartite)
    (hc : H.IsConnected) {X : Finset V} (hs : H.IsSeparatingCut X) :
    H.cutCharacteristic X = ⊤ := by
  by_cases hX : IsNontrivialCut X
  · have ht := hs.tight_of_bipartite hc hX (hb.contract_of_separating hs)
    exact cutCharacteristic_eq_top_iff.mpr (fun M hM ↦ (ht M hM).le)
  · exact cutCharacteristic_eq_top_of_not_nontrivial hX

theorem IsBipartite.tight_of_separating (hb : H.IsBipartite)
    (hc : H.IsConnected) {X : Finset V} (hs : H.IsSeparatingCut X) (ho : Odd X.card) :
    H.IsTightCut X :=
  (cutCharacteristic_eq_top_iff_tight ho).mp (hb.cutCharacteristic_eq_top_of_separating hc hs)

end GraphPuzzles.LoopMultigraph
