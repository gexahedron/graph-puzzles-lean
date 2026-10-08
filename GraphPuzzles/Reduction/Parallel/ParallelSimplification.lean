import GraphPuzzles.Reduction.Parallel.ParallelStructureTransport

/-! A simple spanning representative of every loopless endpoint multigraph.

The final edge type is a subtype of the original edge type, so this construction
preserves the universes used by the edge-count induction. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (H : LoopMultigraph V E)

/-- The unordered endpoint pair of an edge, allowing a singleton for a loop. -/
def endpointPair (e : E) : Finset V := {H.endAt e 0, H.endAt e 1}

omit [DecidableEq E] in
theorem endpointPair_eq_iff (e g : E) :
    H.endpointPair e = H.endpointPair g ↔ H.Joins g (H.endAt e 0) (H.endAt e 1) := by
  constructor
  · intro h
    have h0 : H.endAt g 0 = H.endAt e 0 ∨ H.endAt g 0 = H.endAt e 1 := by
      have : H.endAt g 0 ∈ H.endpointPair e := by rw [h]; simp [endpointPair]
      simpa only [endpointPair, Finset.mem_insert, Finset.mem_singleton] using this
    have h1 : H.endAt g 1 = H.endAt e 0 ∨ H.endAt g 1 = H.endAt e 1 := by
      have : H.endAt g 1 ∈ H.endpointPair e := by rw [h]; simp [endpointPair]
      simpa only [endpointPair, Finset.mem_insert, Finset.mem_singleton] using this
    have he0 : H.endAt e 0 ∈ H.endpointPair g := by rw [← h]; simp [endpointPair]
    have he1 : H.endAt e 1 ∈ H.endpointPair g := by rw [← h]; simp [endpointPair]
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
    all_goals simp_all [endpointPair, Joins]
  · rintro (⟨h0, h1⟩ | ⟨h0, h1⟩)
    · simp only [endpointPair, h0, h1]
    · simp only [endpointPair, h0, h1, Finset.pair_comm]

private def endpointClasses : Finset (Finset V) := Finset.univ.image H.endpointPair

private noncomputable def endpointRepresentative (p : H.endpointClasses) : E :=
  Classical.choose (Finset.mem_image.mp p.property)

omit [DecidableEq E] in
private theorem endpointRepresentative_spec (p : H.endpointClasses) :
    H.endpointPair (H.endpointRepresentative p) = p.val :=
  (Classical.choose_spec (Finset.mem_image.mp p.property)).2

private def endpointClass (e : E) : H.endpointClasses :=
  ⟨H.endpointPair e, Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩⟩

omit [DecidableEq E] in
private theorem endpointClass_representative (p : H.endpointClasses) :
    H.endpointClass (H.endpointRepresentative p) = p :=
  Subtype.ext (H.endpointRepresentative_spec p)

private noncomputable def endpointClassGraph : LoopMultigraph V H.endpointClasses :=
  ⟨fun p i ↦ H.endAt (H.endpointRepresentative p) i⟩

private noncomputable def endpointClassReduction : ParallelReduction H H.endpointClassGraph where
  vertexEquiv := Equiv.refl _
  edgeMap := H.endpointClass
  edge_surjective p := ⟨H.endpointRepresentative p, H.endpointClass_representative p⟩
  joins_iff e a b := by
    have hp : H.endpointPair e = H.endpointPair (H.endpointRepresentative (H.endpointClass e)) :=
      (H.endpointRepresentative_spec (H.endpointClass e)).symm
    rcases (H.endpointPair_eq_iff _ _).mp hp with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · simp only [Joins, endpointClassGraph, Equiv.refl_apply, h0, h1]
    · simp only [Joins, endpointClassGraph, Equiv.refl_apply, h0, h1]
      tauto

/-- Retain one original edge label from each unordered endpoint class. -/
noncomputable def simpleParallelEdges : Finset E := H.endpointClassReduction.representativeEdges

/-- The spanning graph retaining a single label for every parallel class. -/
noncomputable def simpleParallelGraph : LoopMultigraph V H.simpleParallelEdges :=
  H.restrictEdges H.simpleParallelEdges

/-- Identifying parallel labels gives the spanning representative graph. -/
noncomputable def simpleParallelReduction : ParallelReduction H H.simpleParallelGraph :=
  H.endpointClassReduction.trans H.endpointClassReduction.representativeIso.symm.parallelReduction

@[simp] theorem simpleParallelReduction_vertexEquiv :
    H.simpleParallelReduction.vertexEquiv = Equiv.refl V := rfl

@[simp] theorem simpleParallelReduction_mapVertices (X : Finset V) :
    H.simpleParallelReduction.mapVertices X = X := by
  simp only [ParallelReduction.mapVertices, simpleParallelReduction_vertexEquiv]
  ext v
  simp

/-- Removing parallel multiplicity from a loopless graph gives a simple graph. -/
theorem simpleParallelGraph_isSimple (hl : ∀ e, H.endAt e 0 ≠ H.endAt e 1) :
    H.simpleParallelGraph.IsSimple := by
  refine ⟨fun e ↦ hl e.val, ?_⟩
  intro e g hj
  apply H.endpointClassReduction.representativeReduction_injective
  change H.endpointClass e.val = H.endpointClass g.val
  apply Subtype.ext
  exact (H.endpointPair_eq_iff e.val g.val).mpr hj

/-- A loopless graph with parallel labels has a strictly smaller representative. -/
theorem card_simpleParallelEdges_lt (hl : ∀ e, H.endAt e 0 ≠ H.endAt e 1)
    (hns : ¬ H.IsSimple) : Fintype.card H.simpleParallelEdges < Fintype.card E := by
  have hs := H.simpleParallelGraph_isSimple hl
  have hni : ¬ Function.Injective H.simpleParallelReduction.edgeMap := by
    intro hi
    apply hns
    refine ⟨hl, fun e g hj ↦ hi ?_⟩
    apply hs.no_parallel
    have he := (H.simpleParallelReduction.joins_iff e _ _).mp (Or.inl ⟨rfl, rfl⟩)
    have hg := (H.simpleParallelReduction.joins_iff g _ _).mp hj
    exact he.parallel hg
  have hle := Fintype.card_le_of_surjective _ H.simpleParallelReduction.edge_surjective
  by_contra hlt
  have heq : Fintype.card E = Fintype.card H.simpleParallelEdges := by omega
  exact hni ((Fintype.bijective_iff_surjective_and_card
    H.simpleParallelReduction.edgeMap).mpr ⟨H.simpleParallelReduction.edge_surjective, heq⟩).1

/-- The representative construction preserves near-brickness. -/
theorem simpleParallelGraph_isNearBrick_iff :
    H.simpleParallelGraph.IsNearBrick ↔ H.IsNearBrick :=
  H.simpleParallelReduction.isNearBrick_iff.symm

/-- It preserves the characteristic of the literal original vertex shore. -/
theorem simpleParallelGraph_cutCharacteristic (X : Finset V) :
    H.simpleParallelGraph.cutCharacteristic X = H.cutCharacteristic X := by
  simpa only [simpleParallelReduction_mapVertices] using
    H.simpleParallelReduction.cutCharacteristic_mapVertices X

end GraphPuzzles.LoopMultigraph
