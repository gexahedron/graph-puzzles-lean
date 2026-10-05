import GraphPuzzles.Circuits.OrdinaryCircuit

/-!
# Relabelling endpoint multigraphs

An isomorphism of endpoint multigraphs may relabel vertices and edges and independently reverse
the two numbered ends of each edge.  This file records the induced equivalence on half-edges and
proves that ordinary degrees and binary-even edge sets are invariant under such a relabelling.
-/

namespace GraphPuzzles
namespace LoopMultigraph

variable {V₁ E₁ V₂ E₂ : Type*}
  [Fintype V₁] [Fintype E₁] [Fintype V₂] [Fintype E₂]
  [DecidableEq V₁] [DecidableEq E₁] [DecidableEq V₂] [DecidableEq E₂]

/-- An endpoint-multigraph isomorphism.  The numbered ends of each edge may be exchanged. -/
structure EndpointIso (G₁ : LoopMultigraph V₁ E₁) (G₂ : LoopMultigraph V₂ E₂) where
  vertexEquiv : V₁ ≃ V₂
  edgeEquiv : E₁ ≃ E₂
  endEquiv : ∀ _e : E₁, Fin 2 ≃ Fin 2
  map_endAt : ∀ (e : E₁) (i : Fin 2),
    vertexEquiv (G₁.endAt e i) = G₂.endAt (edgeEquiv e) (endEquiv e i)

namespace EndpointIso

variable {G₁ : LoopMultigraph V₁ E₁} {G₂ : LoopMultigraph V₂ E₂}
  (f : EndpointIso G₁ G₂)

/-- Invert a relabelling, including the local reversal of each edge. -/
def symm : EndpointIso G₂ G₁ where
  vertexEquiv := f.vertexEquiv.symm
  edgeEquiv := f.edgeEquiv.symm
  endEquiv e := (f.endEquiv (f.edgeEquiv.symm e)).symm
  map_endAt e i := by
    apply f.vertexEquiv.injective
    simpa using (f.map_endAt (f.edgeEquiv.symm e)
      ((f.endEquiv (f.edgeEquiv.symm e)).symm i)).symm

/-- The induced equivalence of numbered half-edges. -/
def halfEdgeEquiv : HalfEdge E₁ ≃ HalfEdge E₂ where
  toFun h := (f.edgeEquiv h.1, f.endEquiv h.1 h.2)
  invFun h :=
    let e := f.edgeEquiv.symm h.1
    (e, (f.endEquiv e).symm h.2)
  left_inv h := by rcases h with ⟨e, i⟩; simp
  right_inv h := by rcases h with ⟨e, i⟩; simp

omit [DecidableEq V₁] [DecidableEq E₁] [DecidableEq V₂] [DecidableEq E₂] in
@[simp]
theorem halfEdgeEquiv_fst (h : HalfEdge E₁) :
    (f.halfEdgeEquiv h).1 = f.edgeEquiv h.1 := rfl

omit [DecidableEq V₁] [DecidableEq E₁] [DecidableEq V₂] [DecidableEq E₂] in
@[simp]
theorem vertex_halfEdgeEquiv (h : HalfEdge E₁) :
    G₂.vertex (f.halfEdgeEquiv h) = f.vertexEquiv (G₁.vertex h) := by
  exact (f.map_endAt h.1 h.2).symm

/-- Relabel an edge set along the edge equivalence. -/
def mapEdges (F : Finset E₁) : Finset E₂ :=
  F.map f.edgeEquiv.toEmbedding

omit [DecidableEq V₁] [DecidableEq E₁] [DecidableEq V₂] [DecidableEq E₂] in
@[simp]
theorem mem_mapEdges (F : Finset E₁) (e : E₁) :
    f.edgeEquiv e ∈ f.mapEdges F ↔ e ∈ F := by
  simp [mapEdges]

omit [DecidableEq V₁] [DecidableEq E₁] [DecidableEq V₂] [DecidableEq E₂] in
@[simp]
theorem symm_mapEdges_mapEdges (F : Finset E₁) : f.symm.mapEdges (f.mapEdges F) = F := by
  ext e
  simp [mapEdges, symm]

omit [DecidableEq E₁] [DecidableEq E₂] in
/-- Relabelling preserves the support of an edge set. -/
theorem mem_edgeSupport_mapEdges (F : Finset E₁) (v : V₁) :
    f.vertexEquiv v ∈ G₂.edgeSupport (f.mapEdges F) ↔ v ∈ G₁.edgeSupport F := by
  rw [G₂.mem_edgeSupport_iff, G₁.mem_edgeSupport_iff]
  constructor
  · rintro ⟨e', he', i, hi⟩
    obtain ⟨e, he, rfl⟩ := Finset.mem_map.mp he'
    refine ⟨e, he, (f.endEquiv e).symm i, f.vertexEquiv.injective ?_⟩
    calc
      f.vertexEquiv (G₁.endAt e ((f.endEquiv e).symm i)) = G₂.endAt (f.edgeEquiv e) i := by
        simpa using f.map_endAt e ((f.endEquiv e).symm i)
      _ = f.vertexEquiv v := hi
  · rintro ⟨e, he, i, hi⟩
    refine ⟨f.edgeEquiv e, (f.mem_mapEdges F e).mpr he, f.endEquiv e i, ?_⟩
    rw [← f.map_endAt, hi]

/-- Incidences in an edge set at corresponding vertices are in bijection. -/
def incidenceEquiv (F : Finset E₁) (v : V₁) :
    {h : HalfEdge E₁ // h.1 ∈ F ∧ G₁.vertex h = v} ≃
      {h : HalfEdge E₂ // h.1 ∈ f.mapEdges F ∧ G₂.vertex h = f.vertexEquiv v} :=
  f.halfEdgeEquiv.subtypeEquiv fun h ↦ by
    simp [mapEdges, f.vertex_halfEdgeEquiv h]

private theorem degreeIn_eq_card_incidenceSubtype
    (G : LoopMultigraph V₁ E₁) (F : Finset E₁) (v : V₁) :
    G.degreeIn F v = Fintype.card {h : HalfEdge E₁ // h.1 ∈ F ∧ G.vertex h = v} := by
  rw [Fintype.card_subtype]
  change ((F ×ˢ (Finset.univ : Finset (Fin 2))).filter
      fun h ↦ G.endAt h.1 h.2 = v).card =
    ((Finset.univ : Finset (HalfEdge E₁)).filter
      fun h ↦ h.1 ∈ F ∧ G.endAt h.1 h.2 = v).card
  congr 1
  ext h
  simp

/-- Relabelling preserves the degree contributed by an edge set. -/
theorem degreeIn_mapEdges (F : Finset E₁) (v : V₁) :
    G₂.degreeIn (f.mapEdges F) (f.vertexEquiv v) = G₁.degreeIn F v := by
  rw [degreeIn_eq_card_incidenceSubtype, degreeIn_eq_card_incidenceSubtype]
  exact Fintype.card_congr (f.incidenceEquiv F v).symm

/-- Relabelling preserves binary evenness of edge sets. -/
theorem isEvenEdgeSet_mapEdges (F : Finset E₁) :
    G₂.IsEvenEdgeSet (f.mapEdges F) ↔ G₁.IsEvenEdgeSet F := by
  rw [G₂.isEvenEdgeSet_iff_even_degree, G₁.isEvenEdgeSet_iff_even_degree]
  constructor
  · intro h v
    have hv := h (f.vertexEquiv v)
    rwa [f.degreeIn_mapEdges] at hv
  · intro h w
    let v := f.vertexEquiv.symm w
    have hv := h v
    have hw : f.vertexEquiv v = w := by simp [v]
    rw [← hw, f.degreeIn_mapEdges]
    exact hv

omit [DecidableEq V₁] [DecidableEq E₁] [DecidableEq V₂] [DecidableEq E₂] in
/-- Relabelling preserves edge-chain connectivity. -/
theorem edgeConnected_mapEdges {F : Finset E₁} (hF : G₁.EdgeConnected F) :
    G₂.EdgeConnected (f.mapEdges F) := by
  obtain ⟨r, hr, hconn⟩ := hF
  refine ⟨f.edgeEquiv r, (f.mem_mapEdges F r).mpr hr, ?_⟩
  intro e' he'
  obtain ⟨e, he, rfl⟩ := Finset.mem_map.mp he'
  have hp := hconn e he
  clear he he'
  induction hp with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hxy ih =>
    apply ih.tail
    obtain ⟨hx, hy, i, j, hij⟩ := hxy
    refine ⟨(f.mem_mapEdges _ _).mpr hx, (f.mem_mapEdges _ _).mpr hy,
      f.endEquiv b i, f.endEquiv c j, ?_⟩
    exact (f.map_endAt b i).symm.trans ((congrArg f.vertexEquiv hij).trans (f.map_endAt c j))

/-- Transport an ordinary circuit through a relabelling. -/
def ordinaryCircuit (C : G₁.OrdinaryCircuit) : G₂.OrdinaryCircuit where
  edges := f.mapEdges C.edges
  nonempty := C.nonempty.map
  connected := f.edgeConnected_mapEdges C.connected
  twoRegular w hw := by
    let v := f.vertexEquiv.symm w
    have hwv : f.vertexEquiv v = w := f.vertexEquiv.apply_symm_apply w
    rw [← hwv] at hw ⊢
    rw [f.degreeIn_mapEdges]
    exact C.twoRegular v ((f.mem_edgeSupport_mapEdges _ _).mp hw)

end EndpointIso

/-- Change only the numbering of the ends of each edge. This does not change the graph. -/
def relabelEnds (G : LoopMultigraph V₁ E₁) (ends : E₁ → (Fin 2 ≃ Fin 2)) :
    LoopMultigraph V₁ E₁ where
  endAt e i := G.endAt e (ends e i)

/-- The canonical isomorphism witnessing invariance under endpoint numbering. -/
def relabelEndsIso (G : LoopMultigraph V₁ E₁) (ends : E₁ → (Fin 2 ≃ Fin 2)) :
    EndpointIso G (G.relabelEnds ends) where
  vertexEquiv := Equiv.refl _
  edgeEquiv := Equiv.refl _
  endEquiv e := (ends e).symm
  map_endAt e i := by simp [relabelEnds]

end LoopMultigraph
end GraphPuzzles
