import GraphPuzzles.Petersen.Minors.TightMinorMatching
import GraphPuzzles.Petersen.Minors.TightQuotientIso
import GraphPuzzles.Reduction.Parallel.ParallelStructureTransport
import GraphPuzzles.Petersen.PetersenNeighborhood

/-! Canonical Petersen vertex names for a labelled expansion model. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E} {X : Finset V}

namespace PetersenFiberModel

noncomputable section

variable (R : H.PetersenFiberModel X)

def reduction : ParallelReduction R.graph GraphPuzzles.LoopMultigraph.petersen := R.petersen.some

def canonicalVertex (v : V) : Fin 10 := R.reduction.vertexEquiv (R.quotient.vertexMap v)

def canonicalFiber (p : Fin 10) : Finset V := R.quotient.fiber (R.reduction.vertexEquiv.symm p)

def canonicalPreimage (S : Finset (Fin 10)) : Finset V :=
  Finset.univ.filter fun v ↦ R.canonicalVertex v ∈ S

def canonicalCut : Finset (Fin 10) := R.reduction.mapVertices R.cut

def canonicalLift (M : Finset (Fin 15)) : Finset E :=
  (R.reduction.liftMatching M).image R.quotient.edgeLift

theorem canonicalVertex_surjective : Function.Surjective R.canonicalVertex :=
  R.reduction.vertexEquiv.surjective.comp R.quotient.surjective

def canonicalRepresentative (p : Fin 10) : V :=
  (R.canonicalVertex_surjective p).choose

@[simp] theorem canonicalVertex_representative (p : Fin 10) :
    R.canonicalVertex (R.canonicalRepresentative p) = p :=
  (R.canonicalVertex_surjective p).choose_spec

theorem canonicalRepresentative_injective : Function.Injective R.canonicalRepresentative := by
  intro p q hpq
  simpa only [canonicalVertex_representative] using congrArg R.canonicalVertex hpq

@[simp] theorem mem_canonicalFiber (p : Fin 10) (v : V) :
    v ∈ R.canonicalFiber p ↔ R.canonicalVertex v = p := by
  simp only [canonicalFiber, TightVertexQuotient.mem_fiber, canonicalVertex]
  constructor
  · intro h
    rw [h, Equiv.apply_symm_apply]
  · intro h
    simpa only [Equiv.symm_apply_apply] using congrArg R.reduction.vertexEquiv.symm h

@[simp] theorem mem_canonicalPreimage (S : Finset (Fin 10)) (v : V) :
    v ∈ R.canonicalPreimage S ↔ R.canonicalVertex v ∈ S := by
  simp [canonicalPreimage]

theorem canonicalFiber_nonempty (p : Fin 10) : (R.canonicalFiber p).Nonempty :=
  R.quotient.fiber_nonempty _

theorem canonicalFiber_disjoint {p q : Fin 10} (hne : p ≠ q) :
    Disjoint (R.canonicalFiber p) (R.canonicalFiber q) :=
  R.quotient.fiber_disjoint (R.reduction.vertexEquiv.symm.injective.ne hne)

theorem canonicalFiber_subsingleton {p : Fin 10} (hc : (R.canonicalFiber p).card ≤ 1)
    {a b : V} (ha : R.canonicalVertex a = p) (hb : R.canonicalVertex b = p) : a = b :=
  Finset.card_le_one.mp hc a ((R.mem_canonicalFiber p a).mpr ha)
    b ((R.mem_canonicalFiber p b).mpr hb)

theorem canonicalFiber_eq_singleton {p : Fin 10} (hc : (R.canonicalFiber p).card ≤ 1) :
    R.canonicalFiber p = {R.canonicalRepresentative p} := by
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨by simp, ?_⟩
  intro v hv
  exact R.canonicalFiber_subsingleton hc ((R.mem_canonicalFiber p v).mp hv)
    (R.canonicalVertex_representative p)

@[simp] theorem mem_canonicalCut (v : V) : R.canonicalVertex v ∈ R.canonicalCut ↔ v ∈ X := by
  rw [canonicalVertex, canonicalCut, R.reduction.mem_mapVertices,
    ← R.quotient.mem_preimage, R.selected_eq]

@[simp] theorem representative_mem_selected (p : Fin 10) :
    R.canonicalRepresentative p ∈ X ↔ p ∈ R.canonicalCut := by
  rw [← R.mem_canonicalCut, R.canonicalVertex_representative]

theorem canonicalPreimage_cut : R.canonicalPreimage R.canonicalCut = X := by
  ext v
  simp

theorem canonical_cut_separating : GraphPuzzles.LoopMultigraph.petersen.IsSeparatingCut R.canonicalCut := by
  have hc : R.graph.IsConnected := R.reduction.isConnected_iff.mpr petersen_isConnected
  have hm : R.graph.IsMatchingCovered := R.reduction.isMatchingCovered_iff.mpr petersen_isMatchingCovered
  have hn := R.strict.nontrivial hm
  exact (R.reduction.isSeparatingCut_iff hc (Finset.card_pos.mp (by have hh := hn.1; omega))
    (Finset.card_pos.mp (by have hh := hn.2; omega))).mp R.strict.separating

theorem canonical_cut_nontrivial : IsNontrivialCut R.canonicalCut := by
  have hm : R.graph.IsMatchingCovered := R.reduction.isMatchingCovered_iff.mpr petersen_isMatchingCovered
  exact (R.reduction.nontrivial_mapVertices R.cut).mpr (R.strict.nontrivial hm)

/-- Every crossing original edge is an edge of Petersen between its
canonical fiber names. -/
theorem canonical_join_of_distinct_images {e : E} {a b : V}
    (he : H.Joins e a b) (hne : R.canonicalVertex a ≠ R.canonicalVertex b) :
    ∃ f, GraphPuzzles.LoopMultigraph.petersen.Joins f (R.canonicalVertex a) (R.canonicalVertex b) := by
  have hh : R.quotient.vertexMap a ≠ R.quotient.vertexMap b :=
    fun h ↦ hne (congrArg R.reduction.vertexEquiv h)
  obtain ⟨f, _, hf⟩ := R.quotient.exists_join_of_distinct_images he hh
  exact ⟨R.reduction.edgeMap f, (R.reduction.joins_iff f _ _).mp hf⟩

theorem canonical_neighbor_of_boundary {p : Fin 10} {e : E} {a b : V}
    (he : H.Joins e a b) (ha : a ∈ R.canonicalFiber p) (hb : b ∉ R.canonicalFiber p) :
    R.canonicalVertex b ∈ petersenClosedNeighborhood p := by
  have ha' := (R.mem_canonicalFiber p a).mp ha
  have hb' : R.canonicalVertex b ≠ p := fun hh ↦ hb ((R.mem_canonicalFiber p b).mpr hh)
  obtain ⟨f, hf⟩ := R.canonical_join_of_distinct_images he (by rw [ha']; exact hb'.symm)
  rw [ha'] at hf
  exact (petersen_mem_closedNeighborhood p _).mpr (Or.inr ⟨f, hf⟩)

/-- Representatives carry the selected canonical shore to the original one. -/
theorem representative_image_sdiff (S : Finset (Fin 10)) :
    S.image R.canonicalRepresentative \ X =
      (S \ R.canonicalCut).image R.canonicalRepresentative := by
  ext v
  constructor
  · intro hv
    obtain ⟨hvS, hvX⟩ := Finset.mem_sdiff.mp hv
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hvS
    exact Finset.mem_image.mpr ⟨p, Finset.mem_sdiff.mpr ⟨hp,
      fun hh ↦ hvX ((R.representative_mem_selected p).mpr hh)⟩, rfl⟩
  · intro hv
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨p, (Finset.mem_sdiff.mp hp).1, rfl⟩,
      fun hh ↦ (Finset.mem_sdiff.mp hp).2 ((R.representative_mem_selected p).mp hh)⟩

theorem card_representatives_outside (S : Finset (Fin 10)) :
    (S.image R.canonicalRepresentative \ X).card = (S \ R.canonicalCut).card := by
  rw [R.representative_image_sdiff, Finset.card_image_of_injective _ R.canonicalRepresentative_injective]

/-- Canonical partial matchings lift through every singleton exterior
fiber of an expansion model. -/
theorem canonicalLift_matchingOn {S : Finset (Fin 10)} {M : Finset (Fin 15)}
    (hM : GraphPuzzles.LoopMultigraph.petersen.IsPerfectMatchingOn S M)
    (hS : ∀ p ∈ S, (R.canonicalFiber p).card ≤ 1) :
    H.IsPerfectMatchingOn (R.canonicalPreimage S) (R.canonicalLift M) := by
  have hp := R.reduction.isPerfectMatchingOn_lift hM
  have hsingle : ∀ w ∈ S.map R.reduction.vertexEquiv.symm.toEmbedding,
      (R.quotient.fiber w).card ≤ 1 := by
    intro w hw
    have hw' : R.reduction.vertexEquiv w ∈ S := by
      simpa only [Finset.mem_map_equiv, Equiv.symm_symm] using hw
    simpa only [canonicalFiber, Equiv.symm_apply_apply] using hS _ hw'
  have hh := R.quotient.lift_matchingOn hp hsingle
  have he : R.quotient.preimage (S.map R.reduction.vertexEquiv.symm.toEmbedding) =
      R.canonicalPreimage S := by
    ext v
    simp only [TightVertexQuotient.mem_preimage, Finset.mem_map_equiv,
      Equiv.symm_symm, mem_canonicalPreimage, canonicalVertex]
  rw [he] at hh
  exact hh

/-- The two label transports preserve the selected-cut crossing count. -/
theorem canonicalLift_crossing (M : Finset (Fin 15)) :
    (R.canonicalLift M ∩ H.dangling X).card = (M ∩ GraphPuzzles.LoopMultigraph.petersen.dangling R.canonicalCut).card := by
  have hh := (R.quotient.crossing_lift R.cut (R.reduction.liftMatching M)).trans
    (R.reduction.liftMatching_crossing M R.cut)
  simpa only [canonicalLift, canonicalCut, R.selected_eq] using hh

theorem canonicalFiber_preimage_singleton (p : Fin 10) :
    R.canonicalFiber p = R.canonicalPreimage {p} := by
  ext v
  simp

theorem canonicalPreimage_union (S T : Finset (Fin 10)) :
    R.canonicalPreimage (S ∪ T) = R.canonicalPreimage S ∪ R.canonicalPreimage T := by
  ext v
  simp

theorem canonicalPreimage_insert (p : Fin 10) (S : Finset (Fin 10)) :
    R.canonicalPreimage (insert p S) = R.canonicalFiber p ∪ R.canonicalPreimage S := by
  ext v
  simp

@[simp] theorem canonicalPreimage_empty : R.canonicalPreimage ∅ = ∅ := by
  ext v
  simp

@[simp] theorem canonicalPreimage_univ : R.canonicalPreimage Finset.univ = Finset.univ := by
  ext v
  simp

theorem canonicalPreimage_eq_image {S : Finset (Fin 10)}
    (hS : ∀ p ∈ S, (R.canonicalFiber p).card ≤ 1) :
    R.canonicalPreimage S = S.image R.canonicalRepresentative := by
  ext v
  constructor
  · intro hv
    have hp := (R.mem_canonicalPreimage S v).mp hv
    refine Finset.mem_image.mpr ⟨R.canonicalVertex v, hp, ?_⟩
    exact R.canonicalFiber_subsingleton (hS _ hp)
      (R.canonicalVertex_representative _) rfl
  · intro hv
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
    simpa only [mem_canonicalPreimage, canonicalVertex_representative] using hp

theorem canonicalPreimage_compl (S : Finset (Fin 10)) :
    R.canonicalPreimage (Finset.univ \ S) = Finset.univ \ R.canonicalPreimage S := by
  ext v
  simp

end

end PetersenFiberModel

end GraphPuzzles.LoopMultigraph
