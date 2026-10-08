import GraphPuzzles.Reduction.Parallel.ParallelCutTransport
import GraphPuzzles.Petersen.Minors.TightPetersenRigidity

/-! A shore containing no nontrivial tight shore survives a cut-preserving
Petersen reduction. The first invariant is its number of vertices. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- No nontrivial tight-cut shore is contained in the given shore. -/
def HasNoInternalTightCut (H : LoopMultigraph V E) (S : Finset V) : Prop :=
  ∀ Y, H.IsTightCut Y → IsNontrivialCut Y → ¬ Y ⊆ S

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem sourceShore_mono {Y : Finset V} {S T : Finset (Option Y)} (h : S ⊆ T) :
    sourceShore Y S ⊆ sourceShore Y T := by
  intro v hv
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
  exact Finset.mem_image.mpr ⟨w, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, h (Finset.mem_filter.mp hw).2⟩, rfl⟩

/-- The selected part of a crossing tight contraction has no internal
nontrivial tight shore when all original nontrivial tight cuts cross it. -/
theorem HasNoInternalTightCut.of_crossing {X Y : Finset V}
    (htY : H.IsTightCut Y) (hY : IsNontrivialCut Y)
    (hcross : ∀ Z, H.IsTightCut Z → IsNontrivialCut Z → CutsCross X Z) :
    (H.contract Y).HasNoInternalTightCut (contractShore Y X) := by
  intro Z htZ hZ hsub
  have hp : none ∉ Z := fun h ↦ (none_not_mem_contractShore Y X) (hsub h)
  have hS : IsNontrivialCut (sourceShore Y Z) := hY.sourceShore hZ hp
  have htS := htY.lift_contract htZ hp
  have hSX : sourceShore Y Z ⊆ X := by
    have hh := sourceShore_mono hsub
    rw [sourceShore_contractShore] at hh
    exact hh.trans Finset.inter_subset_right
  apply (not_cutsCross_iff X (sourceShore Y Z)).mpr
    (Or.inr (Or.inr (Or.inr ?_))) (hcross _ htS hS)
  intro v hv
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hs ↦ (Finset.mem_sdiff.mp hv).2 (hSX hs)⟩

/-- A shore with no internal nontrivial tight shore survives the whole
certificate. Its contraction is a Petersen shore contraction up to parallel
labels, and the contraction pole is preserved. -/
theorem HasTightPetersenMinor.exists_shore_reduction {X : Finset V}
    (h : H.HasTightPetersenMinor X)
    (S : Finset V) (hSX : S = X ∨ S = Finset.univ \ X)
    (hno : H.HasNoInternalTightCut S) :
    ∃ T : Finset (Fin 10), petersen.IsStrictlySeparatingCut T ∧
      ∃ f : ParallelReduction (H.contract S) (petersen.contract T), f.vertexEquiv none = none := by
  induction h with
  | here hp hs =>
    obtain ⟨f⟩ := hp
    have hsS := hSX.elim (fun h ↦ h.symm ▸ hs) (fun h ↦ h.symm ▸ hs.compl)
    exact ⟨f.mapVertices S, (f.isStrictlySeparatingCut_iff S).mp hsS, f.contract S, rfl⟩
  | @contract V' E' _ _ _ _ G Y ht hY X hp _ ih =>
    rcases hSX with rfl | rfl
    · have hnoX : (G.contract Y).HasNoInternalTightCut X := by
        intro Z htZ hZ hZX
        have hpZ : none ∉ Z := fun hn ↦ hp (hZX hn)
        exact hno (sourceShore Y Z) (ht.lift_contract htZ hpZ)
          (hY.sourceShore hZ hpZ) (sourceShore_mono hZX)
      have he := contractShore_sourceShore Y X hp
      obtain ⟨T, hsT, f, hf⟩ := ih (contractShore Y (sourceShore Y X)) (Or.inl he)
        (by simpa only [he] using hnoX)
      refine ⟨T, hsT,
        (contractNestedIso (sourceShore_subset Y X)).symm.parallelReduction.trans f, ?_⟩
      exact hf
    · exact (hno (Finset.univ \ Y) ht.compl hY.compl (by
        intro v hv
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
          fun h ↦ (Finset.mem_sdiff.mp hv).2 (sourceShore_subset Y X h)⟩)).elim
  | @compl V' E' _ _ _ _ G Z tail ih =>
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
    obtain ⟨T, hsT, g, hg⟩ := ih U hU hnoU
    exact ⟨T, hsT, (f.symm.parallelReduction.contract S).trans g, hg⟩

/-- In particular, the surviving shore has the cardinality of a strictly
separating Petersen shore. -/
theorem HasTightPetersenMinor.exists_shore_card {X : Finset V}
    (h : H.HasTightPetersenMinor X) (S : Finset V)
    (hSX : S = X ∨ S = Finset.univ \ X) (hno : H.HasNoInternalTightCut S) :
    ∃ T : Finset (Fin 10), petersen.IsStrictlySeparatingCut T ∧ S.card = T.card := by
  obtain ⟨T, hsT, f, _⟩ := h.exists_shore_reduction S hSX hno
  have hc := Fintype.card_congr f.vertexEquiv
  simp only [Fintype.card_option, Fintype.card_coe] at hc
  exact ⟨T, hsT, by omega⟩

end GraphPuzzles.LoopMultigraph
