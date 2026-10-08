import GraphPuzzles.Reduction.Parallel.ParallelMatchingTransport
import GraphPuzzles.Reduction.Parallel.ParallelEdges
import GraphPuzzles.Bricks.NearBrick
import GraphPuzzles.Cuts.CutCharacteristic

/-! Structural properties preserved by identifying parallel edge labels. -/

namespace GraphPuzzles.LoopMultigraph

variable {V₁ E₁ V₂ E₂ : Type*}
  [Fintype V₁] [Fintype E₁] [Fintype V₂] [Fintype E₂]
  [DecidableEq V₁] [DecidableEq E₁] [DecidableEq V₂] [DecidableEq E₂]
variable {H : LoopMultigraph V₁ E₁} {K : LoopMultigraph V₂ E₂}

namespace ParallelReduction

variable (f : ParallelReduction H K)

omit [DecidableEq V₁] [DecidableEq E₁] [DecidableEq V₂] [DecidableEq E₂] in
theorem forall_edges_map_iff (R : V₂ → V₂ → Prop) (hR : ∀ ⦃a b⦄, R a b → R b a) :
    (∀ e, R (f.vertexEquiv (H.endAt e 0)) (f.vertexEquiv (H.endAt e 1))) ↔
      ∀ g, R (K.endAt g 0) (K.endAt g 1) := by
  constructor
  · intro h g
    obtain ⟨e, rfl⟩ := f.edge_surjective g
    rcases (f.joins_iff e _ _).mp (Or.inl ⟨rfl, rfl⟩) with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · simpa only [h0, h1] using h e
    · simpa only [h0, h1] using hR (h e)
  · intro h e
    rcases (f.joins_iff e _ _).mp (Or.inl ⟨rfl, rfl⟩) with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · simpa only [h0, h1] using h (f.edgeMap e)
    · simpa only [h0, h1] using hR (h (f.edgeMap e))

include f in
omit [DecidableEq V₁] [DecidableEq E₁] [DecidableEq V₂] [DecidableEq E₂] in
theorem isConnected_iff : H.IsConnected ↔ K.IsConnected := by
  constructor
  · intro h c hc u v
    have hh := (f.forall_edges_map_iff (fun x y ↦ c x = c y) (fun _ _ h ↦ h.symm)).mpr hc
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
      h (c ∘ f.vertexEquiv) hh (f.vertexEquiv.symm u) (f.vertexEquiv.symm v)
  · intro h c hc u v
    have hh := (f.forall_edges_map_iff
      (fun x y ↦ c (f.vertexEquiv.symm x) = c (f.vertexEquiv.symm y))
      (fun _ _ h ↦ h.symm)).mp (by simpa only [Equiv.symm_apply_apply] using hc)
    simpa only [Function.comp_apply, Equiv.symm_apply_apply] using
      h (c ∘ f.vertexEquiv.symm) hh (f.vertexEquiv u) (f.vertexEquiv v)

include f in
omit [DecidableEq V₁] [DecidableEq E₁] [DecidableEq V₂] [DecidableEq E₂] in
theorem isBipartite_iff : H.IsBipartite ↔ K.IsBipartite := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c ∘ f.vertexEquiv.symm, ?_⟩
    apply (f.forall_edges_map_iff
      (fun a b ↦ c (f.vertexEquiv.symm a) ≠ c (f.vertexEquiv.symm b))
      (fun _ _ h ↦ Ne.symm h)).mp
    simpa only [Function.comp_apply, Equiv.symm_apply_apply] using hc
  · rintro ⟨c, hc⟩
    exact ⟨c ∘ f.vertexEquiv, (f.forall_edges_map_iff
      (fun a b ↦ c a ≠ c b) (fun _ _ h ↦ Ne.symm h)).mpr hc⟩

omit [DecidableEq V₁] [DecidableEq E₁] [DecidableEq V₂] [DecidableEq E₂] in
@[simp] theorem mem_mapVertices (X : Finset V₁) (v : V₁) :
    f.vertexEquiv v ∈ f.mapVertices X ↔ v ∈ X := by simp [mapVertices]

omit [DecidableEq E₁] [DecidableEq E₂] in
theorem mapVertices_compl (X : Finset V₁) :
    f.mapVertices (Finset.univ \ X) = Finset.univ \ f.mapVertices X := by
  ext v
  obtain ⟨v, rfl⟩ := f.vertexEquiv.surjective v
  simp only [mem_mapVertices, Finset.mem_sdiff, Finset.mem_univ, true_and]

omit [DecidableEq E₁] [DecidableEq E₂] in
theorem nontrivial_mapVertices (X : Finset V₁) :
    IsNontrivialCut (f.mapVertices X) ↔ IsNontrivialCut X := by
  unfold IsNontrivialCut
  rw [← f.mapVertices_compl]
  simp only [mapVertices, Finset.card_map]

omit [DecidableEq V₁] [DecidableEq E₁] [DecidableEq V₂] [DecidableEq E₂] in
theorem isBipartiteOn_iff (X : Finset V₁) :
    H.IsBipartiteOn X ↔ K.IsBipartiteOn (f.mapVertices X) := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c ∘ f.vertexEquiv.symm, ?_⟩
    apply (f.forall_edges_map_iff
      (fun a b ↦ a ∈ f.mapVertices X → b ∈ f.mapVertices X →
        c (f.vertexEquiv.symm a) ≠ c (f.vertexEquiv.symm b))
      (by intro a b h hb ha; exact Ne.symm (h ha hb))).mp
    simpa only [mem_mapVertices, Function.comp_apply, Equiv.symm_apply_apply] using hc
  · rintro ⟨c, hc⟩
    refine ⟨c ∘ f.vertexEquiv, ?_⟩
    have hh := (f.forall_edges_map_iff
      (fun a b ↦ a ∈ f.mapVertices X → b ∈ f.mapVertices X → c a ≠ c b)
      (by intro a b h hb ha; exact Ne.symm (h ha hb))).mpr hc
    simpa only [mem_mapVertices, Function.comp_apply] using hh

omit [DecidableEq V₁] [DecidableEq V₂] in
theorem image_liftMatching (M : Finset E₂) : (f.liftMatching M).image f.edgeMap = M := by
  rw [liftMatching, Finset.image_image]
  change (f.representativeIso.symm.mapEdges M).image f.representativeIso.edgeEquiv = M
  have hh := f.representativeIso.mapEdges_symm_mapEdges M
  simpa [EndpointIso.mapEdges, Finset.map_eq_image] using hh

/-- A quotient matching can be lifted while retaining any prescribed original label. -/
theorem exists_lift_through {M : Finset E₂} (hM : K.IsPerfectMatching M)
    {e : E₁} (he : f.edgeMap e ∈ M) :
    ∃ N, H.IsPerfectMatching N ∧ e ∈ N ∧ N.image f.edgeMap = M := by
  let P := f.liftMatching M
  have hP : H.IsPerfectMatching P := f.isPerfectMatching_lift hM
  have hPM : P.image f.edgeMap = M := f.image_liftMatching M
  by_cases heP : e ∈ P
  · exact ⟨P, hP, heP, hPM⟩
  have hm : f.edgeMap e ∈ P.image f.edgeMap := hPM.symm ▸ he
  obtain ⟨g, hgP, hge⟩ := Finset.mem_image.mp hm
  have hj : H.Joins e (H.endAt g 0) (H.endAt g 1) := by
    apply (f.joins_iff e _ _).mpr
    rw [← hge]
    exact (f.joins_iff g _ _).mp (Or.inl ⟨rfl, rfl⟩)
  have hgn : H.endAt g 0 ≠ H.endAt g 1 := by
    intro hh
    have hi := eq_incidence_of_degreeIn_one (hP (H.endAt g 0)) hgP hgP rfl hh.symm
    have hk := congrArg Prod.snd hi
    norm_num at hk
  have hQ := hP.erase_edge hgP
  have hS : Finset.univ \ {H.endAt g 0, H.endAt g 1} =
      ((Finset.univ.erase (H.endAt g 0)).erase (H.endAt g 1)) := by
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Finset.mem_erase, and_true, not_or]
    exact and_comm
  rw [hS] at hQ
  refine ⟨insert e (P.erase g), hQ.insert_perfect hj hgn, Finset.mem_insert_self _ _, ?_⟩
  rw [← hPM]
  ext a
  simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_erase]
  constructor
  · rintro ⟨b, rfl | ⟨_, hb⟩, hba⟩
    · exact ⟨g, hgP, hge.trans hba⟩
    · exact ⟨b, hb, hba⟩
  · rintro ⟨b, hb, hba⟩
    by_cases hbg : b = g
    · subst b
      exact ⟨e, Or.inl rfl, hge.symm.trans hba⟩
    · exact ⟨b, Or.inr ⟨hbg, hb⟩, hba⟩

include f in
theorem isMatchingCovered_iff : H.IsMatchingCovered ↔ K.IsMatchingCovered := by
  constructor
  · intro hm
    refine ⟨f.isConnected_iff.mp hm.1, ?_⟩
    intro g
    obtain ⟨e, rfl⟩ := f.edge_surjective g
    obtain ⟨M, hM, he⟩ := hm.2 e
    exact ⟨M.image f.edgeMap, f.isPerfectMatching_image hM, Finset.mem_image.mpr ⟨e, he, rfl⟩⟩
  · intro hm
    refine ⟨f.isConnected_iff.mpr hm.1, ?_⟩
    intro e
    obtain ⟨M, hM, he⟩ := hm.2 (f.edgeMap e)
    obtain ⟨N, hN, heN, _⟩ := f.exists_lift_through hM he
    exact ⟨N, hN, heN⟩

theorem isTightCut_iff (X : Finset V₁) :
    H.IsTightCut X ↔ K.IsTightCut (f.mapVertices X) := by
  constructor
  · intro ht M hM
    rw [← f.liftMatching_crossing M X]
    exact ht _ (f.isPerfectMatching_lift hM)
  · intro ht M hM
    rw [← f.matching_crossing_image hM X]
    exact ht _ (f.isPerfectMatching_image hM)

omit [DecidableEq V₁] [DecidableEq E₁] [DecidableEq V₂] [DecidableEq E₂] in
theorem mapVertices_surjective : Function.Surjective f.mapVertices := by
  intro Y
  refine ⟨Y.map f.vertexEquiv.symm.toEmbedding, ?_⟩
  ext v
  simp [mapVertices]

include f in
theorem isNearBrick_iff : H.IsNearBrick ↔ K.IsNearBrick := by
  constructor
  · intro hn
    have hm := f.isMatchingCovered_iff.mp hn.matchingCovered
    refine LoopMultigraph.isNearBrick_iff.mpr
      ⟨hm, fun h ↦ hn.notBipartite (f.isBipartite_iff.mpr h), ?_⟩
    intro Y htY hY
    obtain ⟨X, rfl⟩ := f.mapVertices_surjective Y
    have htX := (f.isTightCut_iff X).mpr htY
    have hX := (f.nontrivial_mapVertices X).mp hY
    have hs := htY.isSeparatingCut hm
      (Finset.card_pos.mp (by have hh := hY.1; omega))
      (Finset.card_pos.mp (by have hh := hY.2; omega))
    rcases hn.noStrictTightCut X htX hX with h | h
    · exact Or.inl (((f.isBipartiteOn_iff X).mp h.induced_of_contract).contract_of_separating hs)
    · have hh := (f.isBipartiteOn_iff (Finset.univ \ X)).mp h.induced_of_contract
      rw [f.mapVertices_compl] at hh
      exact Or.inr (hh.contract_of_separating hs.compl)
  · intro hn
    have hm := f.isMatchingCovered_iff.mpr hn.matchingCovered
    refine LoopMultigraph.isNearBrick_iff.mpr
      ⟨hm, fun h ↦ hn.notBipartite (f.isBipartite_iff.mp h), ?_⟩
    intro X htX hX
    have hs := htX.isSeparatingCut hm
      (Finset.card_pos.mp (by have hh := hX.1; omega))
      (Finset.card_pos.mp (by have hh := hX.2; omega))
    rcases hn.noStrictTightCut (f.mapVertices X) ((f.isTightCut_iff X).mp htX)
        ((f.nontrivial_mapVertices X).mpr hX) with h | h
    · exact Or.inl (((f.isBipartiteOn_iff X).mpr h.induced_of_contract).contract_of_separating hs)
    · have hh := h.induced_of_contract
      rw [← f.mapVertices_compl] at hh
      exact Or.inr (((f.isBipartiteOn_iff (Finset.univ \ X)).mpr hh).contract_of_separating hs.compl)

theorem isSeparatingCut_iff (hc : H.IsConnected) {X : Finset V₁}
    (hX : X.Nonempty) (hXC : (Finset.univ \ X).Nonempty) :
    H.IsSeparatingCut X ↔ K.IsSeparatingCut (f.mapVertices X) := by
  have hY : (f.mapVertices X).Nonempty := hX.map
  have hYC : (Finset.univ \ f.mapVertices X).Nonempty :=
    f.mapVertices_compl X ▸ hXC.map
  rw [isSeparatingCut_iff_crossing_one hc hX hXC,
    isSeparatingCut_iff_crossing_one (f.isConnected_iff.mp hc) hY hYC]
  constructor
  · intro h g
    obtain ⟨e, rfl⟩ := f.edge_surjective g
    obtain ⟨M, hM, heM, hcross⟩ := h e
    exact ⟨M.image f.edgeMap, f.isPerfectMatching_image hM,
      Finset.mem_image.mpr ⟨e, heM, rfl⟩, (f.matching_crossing_image hM X).trans hcross⟩
  · intro h e
    obtain ⟨M, hM, heM, hcross⟩ := h (f.edgeMap e)
    obtain ⟨N, hN, heN, hNM⟩ := f.exists_lift_through hM heM
    refine ⟨N, hN, heN, ?_⟩
    have hh := f.matching_crossing_image hN X
    rw [hNM, hcross] at hh
    exact hh.symm

theorem matchingCrossings_mapVertices (X : Finset V₁) :
    K.matchingCrossings (f.mapVertices X) = H.matchingCrossings X := by
  ext n
  simp only [mem_matchingCrossings]
  constructor
  · rintro ⟨M, hM, hm⟩
    exact ⟨f.liftMatching M, f.isPerfectMatching_lift hM, (f.liftMatching_crossing M X).trans hm⟩
  · rintro ⟨M, hM, hm⟩
    exact ⟨M.image f.edgeMap, f.isPerfectMatching_image hM, (f.matching_crossing_image hM X).trans hm⟩

theorem cutCharacteristic_mapVertices (X : Finset V₁) :
    K.cutCharacteristic (f.mapVertices X) = H.cutCharacteristic X := by
  simp only [cutCharacteristic, f.matchingCrossings_mapVertices]

end ParallelReduction
end GraphPuzzles.LoopMultigraph
