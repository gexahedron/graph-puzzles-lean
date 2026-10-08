import GraphPuzzles.Petersen.PetersenCuts
import GraphPuzzles.Cuts.TightCutTransport
import GraphPuzzles.Reduction.Parallel.ParallelMatchingTransport
import GraphPuzzles.Matching.Bipartite.VertexMatchingBipartite

namespace GraphPuzzles.LoopMultigraph

/-- The pole and its three neighbors in the labelled Petersen graph. -/
def petersenClosedNeighborhood : Fin 10 → Finset (Fin 10) :=
  ![{0, 1, 4, 5}, {0, 1, 2, 6}, {1, 2, 3, 7}, {2, 3, 4, 8}, {0, 3, 4, 9}, {0, 5, 7, 8}, {1, 6, 8, 9}, {2, 5, 7, 9}, {3, 5, 6, 8}, {4, 6, 7, 9}]

theorem petersen_mem_closedNeighborhood (p v : Fin 10) :
    v ∈ petersenClosedNeighborhood p ↔ v = p ∨ ∃ e, petersen.Joins e p v := by
  unfold Joins
  fin_cases p <;> fin_cases v <;> decide

private def petersenFarMatching : Fin 10 → Bool → Finset (Fin 15) :=
  ![(fun b ↦ if b then {7, 8, 14} else {2, 11, 12}),
    (fun b ↦ if b then {8, 9, 10} else {3, 12, 13}),
    (fun b ↦ if b then {5, 9, 11} else {4, 13, 14}),
    (fun b ↦ if b then {5, 6, 12} else {0, 10, 14}),
    (fun b ↦ if b then {6, 7, 13} else {1, 10, 11}),
    (fun b ↦ if b then {2, 6, 9} else {1, 3, 14}),
    (fun b ↦ if b then {3, 5, 7} else {2, 4, 10}),
    (fun b ↦ if b then {4, 6, 8} else {0, 3, 11}),
    (fun b ↦ if b then {1, 4, 12} else {0, 7, 9}),
    (fun b ↦ if b then {1, 5, 8} else {0, 2, 13})]

private theorem petersenFarMatching_spec (p : Fin 10) (b : Bool) :
    petersen.IsPerfectMatchingOn (Finset.univ \ petersenClosedNeighborhood p)
      (petersenFarMatching p b) := by
  unfold IsPerfectMatchingOn
  fin_cases p <;> cases b <;> decide

private theorem petersenFarMatching_crossings (i : Fin 6) (p : Fin 10) :
    ∃ b : Bool,
      (petersenFarMatching p b ∩ petersen.dangling (petersenMatchingShore i)).card = 0 ∧
      (petersenFarMatching p (!b) ∩ petersen.dangling (petersenMatchingShore i)).card = 2 := by
  simp only [petersenMatchingShore_dangling]
  fin_cases i <;> fin_cases p <;> decide

/-- The two finite patches used when a Petersen pole is expanded and three
boundary edges remain in a matching: they give zero or two further cut crossings. -/
theorem petersen_neighborhood_patch (i : Fin 6) (p : Fin 10) :
    ∃ M₀ M₂ : Finset (Fin 15),
      petersen.IsPerfectMatchingOn (Finset.univ \ petersenClosedNeighborhood p) M₀ ∧
      petersen.IsPerfectMatchingOn (Finset.univ \ petersenClosedNeighborhood p) M₂ ∧
      (M₀ ∩ petersen.dangling (petersenMatchingShore i)).card = 0 ∧
      (M₂ ∩ petersen.dangling (petersenMatchingShore i)).card = 2 := by
  obtain ⟨b, h0, h2⟩ := petersenFarMatching_crossings i p
  exact ⟨_, _, petersenFarMatching_spec p b, petersenFarMatching_spec p (!b), h0, h2⟩

/-- The patch is independent of the chosen orientation of the pentagonal cut. -/
theorem IsSeparatingCut.petersen_neighborhood_patch {X : Finset (Fin 10)}
    (hs : petersen.IsSeparatingCut X) (hX : IsNontrivialCut X) (p : Fin 10) :
    ∃ M₀ M₂ : Finset (Fin 15),
      petersen.IsPerfectMatchingOn (Finset.univ \ petersenClosedNeighborhood p) M₀ ∧
      petersen.IsPerfectMatchingOn (Finset.univ \ petersenClosedNeighborhood p) M₂ ∧
      (M₀ ∩ petersen.dangling X).card = 0 ∧
      (M₂ ∩ petersen.dangling X).card = 2 := by
  obtain ⟨i, rfl | rfl⟩ := hs.eq_petersenMatchingShore hX
  · exact GraphPuzzles.LoopMultigraph.petersen_neighborhood_patch i p
  · simpa only [dangling_compl] using GraphPuzzles.LoopMultigraph.petersen_neighborhood_patch i p

section ContractionPatch

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- A partial matching avoiding a contraction pole lifts to its retained vertices. -/
theorem IsPerfectMatchingOn.lift_of_avoids_contraction_pole {X : Finset V}
    {S : Finset (Option X)} {M : Finset (H.meets X)}
    (hM : (H.contract X).IsPerfectMatchingOn S M) (hn : none ∉ S) :
    H.IsPerfectMatchingOn (sourceShore X S) (M.image Subtype.val) := by
  constructor
  · intro e he k
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    exact (contract_mem_sourceShore X S hn f k).mpr (hM.1 f hf k)
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact (contract_degreeIn_image_some X M w).symm.trans
      (hM.2 (some w) (Finset.mem_filter.mp hw).2)

/-- Lifting a retained edge set preserves every cut avoiding the pole. -/
theorem contraction_patch_crossing {X : Finset V} (M : Finset (H.meets X))
    {Y : Finset (Option X)} (hn : none ∉ Y) :
    (M.image Subtype.val ∩ H.dangling (sourceShore X Y)).card =
      (M ∩ (H.contract X).dangling Y).card := by
  have hi : H.contractMatching X (M.image Subtype.val) = M := by
    ext e
    rw [mem_contractMatching]
    constructor
    · intro he
      obtain ⟨f, hf, heq⟩ := Finset.mem_image.mp he
      exact (Subtype.ext heq : f = e) ▸ hf
    · intro he
      exact Finset.mem_image.mpr ⟨e, he, rfl⟩
  rw [← contractMatching_crossing X Y hn, hi]

end ContractionPatch

section VertexProjection

variable {V₁ E₁ V₂ E₂ : Type*}
  [Fintype V₁] [Fintype E₁] [Fintype V₂] [Fintype E₂]
  [DecidableEq V₁] [DecidableEq E₁] [DecidableEq V₂] [DecidableEq E₂]
variable {H : LoopMultigraph V₁ E₁} {K : LoopMultigraph V₂ E₂}

omit [DecidableEq E₁] [DecidableEq V₂] [DecidableEq E₂] in
/-- A loopless vertex matching still uses at most one label per parallel class. -/
theorem ParallelReduction.edgeMap_injOn_vertexMatching (f : ParallelReduction H K)
    {v : V₁} {M : Finset E₁} (hM : H.IsVertexMatching v M)
    (hl : ∀ e, H.endAt e 0 ≠ H.endAt e 1) : Set.InjOn f.edgeMap M := by
  intro e he g hg heg
  have hjoin : H.Joins g (H.endAt e 0) (H.endAt e 1) := by
    apply (f.joins_iff g _ _).mpr
    rw [← heg]
    exact (f.joins_iff e _ _).mp (Or.inl ⟨rfl, rfl⟩)
  by_cases hv : H.endAt e 0 = v
  · have hd := hM (H.endAt e 1) (fun h ↦ hl e (hv.trans h.symm))
    rcases hjoin with ⟨_, h1⟩ | ⟨h0, _⟩
    · exact congrArg Prod.fst (eq_incidence_of_degreeIn_one hd he hg rfl h1)
    · exact congrArg Prod.fst (eq_incidence_of_degreeIn_one hd he hg rfl h0)
  · have hd := hM (H.endAt e 0) hv
    rcases hjoin with ⟨h0, _⟩ | ⟨_, h1⟩
    · exact congrArg Prod.fst (eq_incidence_of_degreeIn_one hd he hg rfl h0)
    · exact congrArg Prod.fst (eq_incidence_of_degreeIn_one hd he hg rfl h1)

omit [DecidableEq E₁] in
/-- Vertex matchings project through a parallel reduction of a loopless graph. -/
theorem ParallelReduction.isVertexMatching_image (f : ParallelReduction H K)
    {v : V₁} {M : Finset E₁} (hM : H.IsVertexMatching v M)
    (hl : ∀ e, H.endAt e 0 ≠ H.endAt e 1) :
    K.IsVertexMatching (f.vertexEquiv v) (M.image f.edgeMap) := by
  intro w hw
  obtain ⟨w, rfl⟩ := f.vertexEquiv.surjective w
  rw [f.degreeIn_image (f.edgeMap_injOn_vertexMatching hM hl)]
  exact hM w (fun h ↦ hw (congrArg f.vertexEquiv h))

/-- Crossing preservation only needs edge-map injectivity on the selected set. -/
theorem ParallelReduction.crossing_image_of_injOn (f : ParallelReduction H K)
    {M : Finset E₁} (hi : Set.InjOn f.edgeMap M) (X : Finset V₁) :
    (M.image f.edgeMap ∩ K.dangling (f.mapVertices X)).card =
      (M ∩ H.dangling X).card := by
  have he : M.image f.edgeMap ∩ K.dangling (f.mapVertices X) =
      (M ∩ H.dangling X).image f.edgeMap := by
    ext g
    constructor
    · intro hg
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hg).1
      exact Finset.mem_image.mpr ⟨e, Finset.mem_inter.mpr
        ⟨he, (f.mem_dangling_mapVertices X e).mp (Finset.mem_inter.mp hg).2⟩, rfl⟩
    · intro hg
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hg
      exact Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨e, (Finset.mem_inter.mp he).1, rfl⟩,
        (f.mem_dangling_mapVertices X e).mpr (Finset.mem_inter.mp he).2⟩
  rw [he]
  exact Finset.card_image_iff.mpr (fun e he g hg h ↦
    hi (Finset.mem_inter.mp he).1 (Finset.mem_inter.mp hg).1 h)

end VertexProjection

/-- A Petersen vertex matching has either one or all three incidences at its hub. -/
theorem IsVertexMatching.petersen_hub_degree {p : Fin 10} {M : Finset (Fin 15)}
    (hM : petersen.IsVertexMatching p M) :
    petersen.degreeIn M p = 1 ∨ petersen.degreeIn M p = 3 := by
  have ho := hM.odd_hub_degree (by decide : Even (Fintype.card (Fin 10)))
  have hl := degreeIn_add_compl (H := petersen) M p
  rw [petersen_degree] at hl
  rw [Nat.odd_iff] at ho
  omega

section PetersenContraction

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- Every matching crosses a separating Petersen contraction in one or three edges. -/
theorem IsPerfectMatching.petersen_contraction_crossing_one_or_three
    {M : Finset E} (hM : H.IsPerfectMatching M) {X : Finset V}
    (hs : H.IsSeparatingCut X) (hp : (H.contract X).IsPetersenUpToParallel) :
    (M ∩ H.dangling X).card = 1 ∨ (M ∩ H.dangling X).card = 3 := by
  obtain ⟨f⟩ := hp
  have hN : (H.contract X).IsVertexMatching none (H.contractMatching X M) := by
    intro w hw
    cases w with
    | none => exact (hw rfl).elim
    | some w =>
      rw [contractMatching, contract_degreeIn_some]
      exact hM w.1
  have hi := f.edgeMap_injOn_vertexMatching hN hs.1.loopless
  have hP := f.isVertexMatching_image hN hs.1.loopless
  have hh := hP.petersen_hub_degree
  rw [f.degreeIn_image hi, contractMatching_degreeIn_none] at hh
  exact hh

/-- Nontightness of a separating Petersen contraction supplies three boundary edges. -/
theorem IsSeparatingCut.exists_crossing_three_of_petersen_contraction_nontight
    {X : Finset V} (hs : H.IsSeparatingCut X)
    (hp : (H.contract X).IsPetersenUpToParallel) (hnt : ¬ H.IsTightCut X) :
    ∃ M, H.IsPerfectMatching M ∧ (M ∩ H.dangling X).card = 3 := by
  classical
  simp only [IsTightCut, not_forall] at hnt
  obtain ⟨M, hM, hne⟩ := hnt
  exact ⟨M, hM, (hM.petersen_contraction_crossing_one_or_three hs hp).resolve_left hne⟩

end PetersenContraction

end GraphPuzzles.LoopMultigraph
