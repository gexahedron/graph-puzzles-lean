import GraphPuzzles.Reduction.Parallel.ParallelReduction
import GraphPuzzles.Matching.MatchingOnRestriction
import GraphPuzzles.Reduction.Removable.EdgeRestriction

/-! Lifting matchings through the identification of parallel edge labels. -/

namespace GraphPuzzles.LoopMultigraph

variable {V₁ E₁ V₂ E₂ : Type*}
  [Fintype V₁] [Fintype E₁] [Fintype V₂] [Fintype E₂]
  [DecidableEq V₁] [DecidableEq E₁] [DecidableEq V₂] [DecidableEq E₂]
variable {H : LoopMultigraph V₁ E₁} {K : LoopMultigraph V₂ E₂}

/-- Relabelling also preserves perfect matchings of an induced shore. -/
theorem EndpointIso.isPerfectMatchingOn (f : EndpointIso H K)
    {S : Finset V₁} {M : Finset E₁} (hM : H.IsPerfectMatchingOn S M) :
    K.IsPerfectMatchingOn (f.mapVertices S) (f.mapEdges M) := by
  constructor
  · intro e he k
    obtain ⟨g, hg, rfl⟩ := Finset.mem_map.mp he
    change K.endAt (f.edgeEquiv g) k ∈ f.mapVertices S
    have hh := f.map_endAt g ((f.endEquiv g).symm k)
    simp only [Equiv.apply_symm_apply] at hh
    rw [← hh]
    exact (f.mem_mapVertices S _).mpr (hM.1 g hg _)
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hv
    change K.degreeIn (f.mapEdges M) (f.vertexEquiv w) = 1
    rw [f.degreeIn_mapEdges]
    exact hM.2 w hw

namespace ParallelReduction

variable (f : ParallelReduction H K)

omit [DecidableEq E₁] [DecidableEq V₂] [DecidableEq E₂] in
/-- A matching uses at most one label from each parallel class. -/
theorem edgeMap_injOn_matchingOn {S : Finset V₁} {M : Finset E₁}
    (hM : H.IsPerfectMatchingOn S M) : Set.InjOn f.edgeMap M := by
  intro e he g hg heg
  have hjoin : H.Joins g (H.endAt e 0) (H.endAt e 1) := by
    apply (f.joins_iff g _ _).mpr
    rw [← heg]
    exact (f.joins_iff e _ _).mp (Or.inl ⟨rfl, rfl⟩)
  have hd := hM.2 _ (hM.1 e he 0)
  rcases hjoin with ⟨h0, _⟩ | ⟨_, h1⟩
  · exact congrArg Prod.fst (eq_incidence_of_degreeIn_one hd he hg rfl h0)
  · exact congrArg Prod.fst (eq_incidence_of_degreeIn_one hd he hg rfl h1)

omit [DecidableEq E₁] in
/-- Identifying parallel labels preserves degrees on any edge set on
which the edge map is injective. -/
theorem degreeIn_image {M : Finset E₁} (hi : Set.InjOn f.edgeMap M) (v : V₁) :
    K.degreeIn (M.image f.edgeMap) (f.vertexEquiv v) = H.degreeIn M v := by
  unfold degreeIn
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_product, Finset.sum_product,
    Finset.sum_image hi]
  apply Finset.sum_congr rfl
  intro e _
  rcases (f.joins_iff e _ _).mp (Or.inl ⟨rfl, rfl⟩) with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · simp only [Fin.sum_univ_two, h0, h1, Equiv.apply_eq_iff_eq]
  · simp only [Fin.sum_univ_two, h0, h1, Equiv.apply_eq_iff_eq]
    omega

omit [DecidableEq E₁] in
/-- A perfect matching projects to a perfect matching of the parallel quotient. -/
theorem isPerfectMatching_image {M : Finset E₁} (hM : H.IsPerfectMatching M) :
    K.IsPerfectMatching (M.image f.edgeMap) := by
  intro v
  obtain ⟨w, rfl⟩ := f.vertexEquiv.surjective v
  rw [f.degreeIn_image (f.edgeMap_injOn_matchingOn hM.on_univ)]
  exact hM w

/-- Choose one original label for each parallel class. -/
noncomputable def representative : E₂ → E₁ := Function.surjInv f.edge_surjective

omit [DecidableEq V₁] [DecidableEq E₁] [DecidableEq V₂] [DecidableEq E₂] in
@[simp] theorem map_representative (e : E₂) : f.edgeMap (f.representative e) = e :=
  Function.surjInv_eq f.edge_surjective e

noncomputable def representativeEdges : Finset E₁ := Finset.univ.image f.representative

/-- The chosen representatives have exactly the quotient's labelled edges. -/
noncomputable def representativeReduction : ParallelReduction (H.restrictEdges f.representativeEdges) K where
  vertexEquiv := f.vertexEquiv
  edgeMap e := f.edgeMap e.1
  edge_surjective e := ⟨⟨f.representative e,
    Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩⟩, f.map_representative e⟩
  joins_iff e a b := f.joins_iff e.1 a b

omit [DecidableEq V₁] [DecidableEq V₂] [DecidableEq E₂] in
theorem representativeReduction_injective : Function.Injective f.representativeReduction.edgeMap := by
  intro e g heg
  obtain ⟨a, _, ha⟩ := Finset.mem_image.mp e.2
  obtain ⟨b, _, hb⟩ := Finset.mem_image.mp g.2
  change f.edgeMap e.1 = f.edgeMap g.1 at heg
  rw [← ha, ← hb, f.map_representative, f.map_representative] at heg
  apply Subtype.ext
  exact ha.symm.trans ((congrArg f.representative heg).trans hb)

/-- The subgraph retaining one representative of each parallel class is
isomorphic to the quotient, with the original vertex relabelling. -/
noncomputable def representativeIso : EndpointIso (H.restrictEdges f.representativeEdges) K :=
  f.representativeReduction.toEndpointIso_of_injective f.representativeReduction_injective

noncomputable def liftMatching (M : Finset E₂) : Finset E₁ :=
  (f.representativeIso.symm.mapEdges M).image Subtype.val

/-- Any quotient perfect matching lifts to a perfect matching in the original graph. -/
theorem isPerfectMatching_lift {M : Finset E₂} (hM : K.IsPerfectMatching M) :
    H.IsPerfectMatching (f.liftMatching M) :=
  (f.representativeIso.symm.isPerfectMatching hM).of_restrictEdges

/-- Partial perfect matchings lift on the corresponding vertex shore. -/
theorem isPerfectMatchingOn_lift {S : Finset V₂} {M : Finset E₂}
    (hM : K.IsPerfectMatchingOn S M) :
    H.IsPerfectMatchingOn (S.map f.vertexEquiv.symm.toEmbedding) (f.liftMatching M) :=
  (f.representativeIso.symm.isPerfectMatchingOn hM).of_restrictEdges

/-- Relabel an original shore in the parallel quotient. -/
def mapVertices (X : Finset V₁) : Finset V₂ := X.map f.vertexEquiv.toEmbedding

omit [DecidableEq E₁] [DecidableEq E₂] in
theorem mem_dangling_mapVertices (X : Finset V₁) (e : E₁) :
    f.edgeMap e ∈ K.dangling (f.mapVertices X) ↔ e ∈ H.dangling X := by
  rcases (f.joins_iff e _ _).mp (Or.inl ⟨rfl, rfl⟩) with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · simp only [mem_dangling, h0, h1, mapVertices, Finset.mem_map_equiv, Equiv.symm_apply_apply]
  · simp only [mem_dangling, h0, h1, mapVertices, Finset.mem_map_equiv, Equiv.symm_apply_apply]
    tauto

/-- Projection preserves matching crossing counts exactly. -/
theorem matching_crossing_image {M : Finset E₁} (hM : H.IsPerfectMatching M) (X : Finset V₁) :
    (M.image f.edgeMap ∩ K.dangling (f.mapVertices X)).card = (M ∩ H.dangling X).card := by
  have he : M.image f.edgeMap ∩ K.dangling (f.mapVertices X) =
      (M ∩ H.dangling X).image f.edgeMap := by
    ext g
    constructor
    · intro hg
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hg).1
      exact Finset.mem_image.mpr ⟨e, Finset.mem_inter.mpr
        ⟨he, (f.mem_dangling_mapVertices X e).mp (Finset.mem_inter.mp hg).2⟩, rfl⟩
    · rintro hg
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hg
      exact Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨e, (Finset.mem_inter.mp he).1, rfl⟩,
        (f.mem_dangling_mapVertices X e).mpr (Finset.mem_inter.mp he).2⟩
  rw [he]
  exact Finset.card_image_iff.mpr (fun e he g hg h ↦
    f.edgeMap_injOn_matchingOn hM.on_univ (Finset.mem_inter.mp he).1
      (Finset.mem_inter.mp hg).1 h)

/-- A lifted matching has exactly the quotient's crossing count. -/
theorem liftMatching_crossing (M : Finset E₂) (X : Finset V₁) :
    (f.liftMatching M ∩ H.dangling X).card = (M ∩ K.dangling (f.mapVertices X)).card := by
  change (((f.representativeIso.symm.mapEdges M).image Subtype.val) ∩ H.dangling X).card = _
  rw [restrictEdges_crossing]
  have hh := f.representativeIso.crossing_map (f.representativeIso.symm.mapEdges M) X
  rw [f.representativeIso.mapEdges_symm_mapEdges] at hh
  exact hh.symm

end ParallelReduction

end GraphPuzzles.LoopMultigraph
