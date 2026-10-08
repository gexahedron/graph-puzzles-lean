import GraphPuzzles.Petersen.PetersenNeighborhood

/-! The twelve orientations of the nontrivial separating Petersen cuts. -/

namespace GraphPuzzles.LoopMultigraph

def petersenPatchShore (i : Fin 6) (b : Bool) : Finset (Fin 10) :=
  if b then Finset.univ \ petersenMatchingShore i else petersenMatchingShore i

theorem IsSeparatingCut.eq_petersenPatchShore {X : Finset (Fin 10)}
    (hs : petersen.IsSeparatingCut X) (hX : IsNontrivialCut X) :
    ∃ i : Fin 6, ∃ b : Bool, X = petersenPatchShore i b := by
  obtain ⟨i, h | h⟩ := hs.eq_petersenMatchingShore hX
  · exact ⟨i, false, h⟩
  · exact ⟨i, true, h⟩

end GraphPuzzles.LoopMultigraph
