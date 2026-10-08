import GraphPuzzles.Petersen.Minors.TightPetersenMinor
import GraphPuzzles.Cuts.CutCrossing

/-! A cut-preserving Petersen certificate cannot contract a cut crossing
the selected cut. This is the rigidity step used in Section 6, Case 3. -/

namespace GraphPuzzles.LoopMultigraph

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem cutsCross_compl_left (X Y : Finset V) :
    CutsCross (Finset.univ \ X) Y ↔ CutsCross X Y := by
  apply not_iff_not.mp
  simp only [not_cutsCross_iff, Finset.sdiff_sdiff_eq_self (Finset.subset_univ X)]
  tauto

theorem cutsCross_compl_right (X Y : Finset V) :
    CutsCross X (Finset.univ \ Y) ↔ CutsCross X Y := by
  apply not_iff_not.mp
  simp only [not_cutsCross_iff, Finset.sdiff_sdiff_eq_self (Finset.subset_univ Y)]
  tauto

variable {E W F : Type*} [Fintype E] [Fintype W] [Fintype F]
  [DecidableEq E] [DecidableEq W] [DecidableEq F]
  {H : LoopMultigraph V E} {K : LoopMultigraph W F}

omit [DecidableEq E] [DecidableEq F] in
theorem EndpointIso.cutsCross_mapVertices (f : EndpointIso H K) (X Y : Finset V) :
    CutsCross (f.mapVertices X) (f.mapVertices Y) ↔ CutsCross X Y := by
  apply not_iff_not.mp
  rw [not_cutsCross_iff, not_cutsCross_iff, ← f.mapVertices_compl X,
    ← f.mapVertices_compl Y]
  simp only [EndpointIso.mapVertices, Finset.map_subset_map]

/-- If every nontrivial tight cut crosses the selected cut, no first
contraction in a cut-preserving Petersen certificate is possible. -/
theorem HasTightPetersenMinor.petersen_of_tight_crossing {X : Finset V}
    (h : H.HasTightPetersenMinor X)
    (hcross : ∀ Y, H.IsTightCut Y → IsNontrivialCut Y → CutsCross X Y) :
    H.IsPetersenUpToParallel := by
  induction h with
  | here hp _ => exact hp
  | contract Y ht hY X _ _ _ =>
    exact ((not_cutsCross_iff (sourceShore Y X) Y).mpr
      (Or.inl (sourceShore_subset Y X)) (hcross Y ht hY)).elim
  | compl _ ih =>
    exact ih (fun Y ht hY ↦ (cutsCross_compl_left _ Y).mp (hcross Y ht hY))
  | iso f _ ih =>
    apply f.isPetersenUpToParallel
    apply ih
    intro Y ht hY
    exact (f.cutsCross_mapVertices _ Y).mp
      (hcross (f.mapVertices Y) (f.isTightCut ht) ((f.nontrivial_mapVertices Y).mpr hY))

end GraphPuzzles.LoopMultigraph
