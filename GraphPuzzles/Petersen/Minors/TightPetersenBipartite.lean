import GraphPuzzles.Petersen.Minors.TightPetersenMinor

/-! A matching-covered graph carrying a tight Petersen certificate is nonbipartite. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- Bipartiteness survives separating contractions, whereas the terminal
strictly separating cut excludes it. -/
theorem HasTightPetersenMinor.notBipartite {X : Finset V}
    (hp : H.HasTightPetersenMinor X) (hm : H.IsMatchingCovered) : ¬ H.IsBipartite := by
  induction hp with
  | here _ hs =>
    exact fun hb ↦ hs.leftNonbipartite (hb.contract_of_separating hs.separating)
  | contract Y ht hY _ _ _ ih =>
    have hs := ht.isSeparatingCut hm
      (Finset.card_pos.mp (by have hh := hY.1; omega))
      (Finset.card_pos.mp (by have hh := hY.2; omega))
    exact fun hb ↦ ih hs.1 (hb.contract_of_separating hs)
  | compl _ ih => exact ih hm
  | iso f _ ih => exact fun hb ↦ ih (f.symm.isMatchingCovered hm) (f.symm.isBipartite hb)

/-- When a tight contraction keeps a Petersen certificate, it keeps the
near-brick side; the discarded shore has a bipartite contraction. -/
theorem IsNearBrick.tight_contractions_of_petersenMinor (hn : H.IsNearBrick)
    {Y : Finset V} (ht : H.IsTightCut Y) (hY : IsNontrivialCut Y)
    {X : Finset (Option Y)} (hp : (H.contract Y).HasTightPetersenMinor X) :
    (H.contract Y).IsNearBrick ∧ (H.contract (Finset.univ \ Y)).IsBipartite := by
  rcases hn.tight_contractions ht hY with h | h
  · have hs := ht.isSeparatingCut hn.matchingCovered
      (Finset.card_pos.mp (by have hh := hY.1; omega))
      (Finset.card_pos.mp (by have hh := hY.2; omega))
    exact (hp.notBipartite hs.1 h.1).elim
  · exact h

end GraphPuzzles.LoopMultigraph
