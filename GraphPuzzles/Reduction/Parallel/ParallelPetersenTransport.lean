import GraphPuzzles.Reduction.Parallel.ParallelCutTransport
import GraphPuzzles.Petersen.Minors.TightPetersenMinor

/-! Pulling a cut-preserving tight Petersen certificate back through parallel reduction. -/

namespace GraphPuzzles.LoopMultigraph

universe u v

variable {V W : Type u} {E F : Type v}
  [Fintype V] [Fintype E] [Fintype W] [Fintype F]
  [DecidableEq V] [DecidableEq E] [DecidableEq W] [DecidableEq F]
variable {H : LoopMultigraph V E} {K : LoopMultigraph W F}

private theorem HasTightPetersenMinor.parallel_preimage {Y : Finset W}
    (hp : K.HasTightPetersenMinor Y) :
    ∀ {V' : Type u} {E' : Type v} [Fintype V'] [Fintype E'] [DecidableEq V'] [DecidableEq E']
      {G : LoopMultigraph V' E'} (f : ParallelReduction G K) (X : Finset V'),
      f.mapVertices X = Y → G.HasTightPetersenMinor X := by
  induction hp with
  | here hp hs =>
    intro V E _ _ _ _ G f X hX
    refine .here ⟨f.trans hp.some⟩ ((f.isStrictlySeparatingCut_iff X).mpr ?_)
    exact hX.symm ▸ hs
  | contract Y ht hY A hn hp ih =>
    intro V E _ _ _ _ G f X hX
    obtain ⟨Z, hZ⟩ := f.mapVertices_surjective Y
    subst Y
    obtain ⟨B, hB⟩ := (f.contract Z).mapVertices_surjective A
    subst A
    have hnB : none ∉ B := fun h ↦ hn ((f.none_mem_contract_mapVertices Z B).mpr h)
    have hsource : sourceShore Z B = X :=
      f.mapVertices_injective ((f.map_sourceShore Z B hnB).trans hX.symm)
    rw [← hsource]
    exact .contract Z ((f.isTightCut_iff Z).mpr ht) ((f.nontrivial_mapVertices Z).mp hY)
      B hnB (ih (f.contract Z) B rfl)
  | compl hp ih =>
    intro V E _ _ _ _ G f X hX
    have hm := congrArg (fun S ↦ Finset.univ \ S) hX
    rw [← f.mapVertices_compl, Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)] at hm
    have hh := (ih f (Finset.univ \ X) hm).compl
    simpa only [Finset.sdiff_sdiff_eq_self (Finset.subset_univ X)] using hh
  | iso e hp ih =>
    intro V E _ _ _ _ G f X hX
    apply ih (f.trans e.symm.parallelReduction) X
    have hh := congrArg e.symm.mapVertices hX
    rw [e.symm_mapVertices_mapVertices] at hh
    simpa only [ParallelReduction.mapVertices, ParallelReduction.trans,
      EndpointIso.parallelReduction, EndpointIso.mapVertices, Finset.map_map,
      Equiv.trans_toEmbedding] using hh

/-- Parallel-edge identification can be reversed throughout the entire
certificate, with every tight cut and the selected cut transported exactly. -/
theorem HasTightPetersenMinor.of_parallelReduction (f : ParallelReduction H K)
    {X : Finset V} (hp : K.HasTightPetersenMinor (f.mapVertices X)) :
    H.HasTightPetersenMinor X := hp.parallel_preimage f X rfl

theorem NearBrickCutConclusion.of_parallelReduction (f : ParallelReduction H K)
    {X : Finset V} (h : K.NearBrickCutConclusion (f.mapVertices X)) :
    H.NearBrickCutConclusion X := by
  rcases h with h | h | ⟨h, hp⟩
  · exact Or.inl ((f.cutCharacteristic_mapVertices X).symm.trans h)
  · exact Or.inr (Or.inl ((f.cutCharacteristic_mapVertices X).symm.trans h))
  · exact Or.inr (Or.inr ⟨(f.cutCharacteristic_mapVertices X).symm.trans h,
      hp.of_parallelReduction f⟩)

end GraphPuzzles.LoopMultigraph
