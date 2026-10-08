import GraphPuzzles.Bricks.NearBrick

/-! A separating cut of a separating-cut contraction lifts to a separating cut. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- The original separating cut and a separating cut lifted from its contraction are cohesive. -/
theorem IsSeparatingCut.cohesive_lift {X : Finset V} (hs : H.IsSeparatingCut X)
    {Y : Finset (Option X)} (hY : (H.contract X).IsSeparatingCut Y) (hn : none ∉ Y) :
    H.IsCohesiveCuts {X, sourceShore X Y} := by
  have finish {P : Finset E} {M : Finset (H.meets X)}
      (hc : (P ∩ H.dangling X).card = 1) (hr : H.contractMatching X P = M)
      (hy : (M ∩ (H.contract X).dangling Y).card = 1) :
      H.RespectsCuts P {X, sourceShore X Y} := by
    intro Z hZ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hZ
    rcases hZ with rfl | rfl
    · exact hc
    · rw [← contractMatching_crossing X Y hn P, hr, hy]
  intro e
  by_cases he : e ∈ H.meets X
  · obtain ⟨M, hM, heM, hm⟩ := hY.exists_perfectMatching_through ⟨e, he⟩
    obtain ⟨P, hP, hc, hr⟩ := hM.extend_contract_exact hs.2
    refine ⟨P, hP, ?_, finish hc hr hm⟩
    apply (mem_contractMatching X P ⟨e, he⟩).mp
    rwa [hr]
  · obtain ⟨Q, hQ, heQ, hq⟩ := hs.exists_perfectMatching_through e
    have hqC : (Q ∩ H.dangling (Finset.univ \ X)).card = 1 := by
      simpa only [dangling_compl] using hq
    let N := H.contractMatching (Finset.univ \ X) Q
    have hN : (H.contract (Finset.univ \ X)).IsPerfectMatching N :=
      hQ.contract_of_crossing_one _ hqC
    let f := hN.contractBoundary
    have hf : f ∈ H.dangling X := by
      simpa only [dangling_compl] using hN.contract_boundary_mem.2
    obtain ⟨M, hM, hfM, hm⟩ := hY.exists_perfectMatching_through
      ⟨f, dangling_subset_meets X hf⟩
    have hfM' : f ∈ M.image Subtype.val := Finset.mem_image.mpr ⟨_, hfM, rfl⟩
    have hag : hM.contractBoundary = hN.contractBoundary :=
      ((hM.contract_boundary_iff hf).mp hfM').symm
    let P := M.image Subtype.val ∪ N.image Subtype.val
    have hP : H.IsPerfectMatching P :=
      glue_contract_matchings hM hN (contract_boundary_agreement hM hN hag)
    have hc : (P ∩ H.dangling X).card = 1 := glue_contract_cut_card hM hN hag
    have hr := hM.contractMatching_eq_of_subset hP hc Finset.subset_union_left
    refine ⟨P, hP, ?_, finish hc hr hm⟩
    apply Finset.mem_union_right
    have heC : e ∈ H.meets (Finset.univ \ X) := by
      apply mem_meets.mpr
      refine ⟨0, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      exact fun hx ↦ he (mem_meets.mpr ⟨0, hx⟩)
    exact Finset.mem_image.mpr ⟨⟨e, heC⟩, (mem_contractMatching _ _ _).mpr heQ, rfl⟩

/-- Separation lifts from a contraction; both shores of the lifted cut are explicit. -/
theorem IsSeparatingCut.lift_contract {X : Finset V} (hs : H.IsSeparatingCut X)
    {Y : Finset (Option X)} (hY : (H.contract X).IsSeparatingCut Y) (hn : none ∉ Y)
    (hc : H.IsConnected) (hZ : (sourceShore X Y).Nonempty)
    (hZC : (Finset.univ \ sourceShore X Y).Nonempty) :
    H.IsSeparatingCut (sourceShore X Y) := by
  apply isSeparatingCut_of_crossing_one hc hZ hZC
  intro e
  obtain ⟨M, hM, he, hm⟩ := hs.cohesive_lift hY hn e
  exact ⟨M, hM, he, hm _ (by simp)⟩

end GraphPuzzles.LoopMultigraph
