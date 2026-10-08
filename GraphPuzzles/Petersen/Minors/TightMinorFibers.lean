import GraphPuzzles.Petersen.Minors.TightPetersenMinor
import GraphPuzzles.Cuts.TrivialCutCharacteristic

/-! Original-vertex fibers and exact edge labels of a tight Petersen minor. -/

namespace GraphPuzzles.LoopMultigraph

universe u v

variable {V W U : Type u} {E F I : Type v}
  [Fintype V] [Fintype W] [Fintype U] [Fintype E] [Fintype F] [Fintype I]
  [DecidableEq V] [DecidableEq W] [DecidableEq U]
  [DecidableEq E] [DecidableEq F] [DecidableEq I]
variable {H : LoopMultigraph V E} {K : LoopMultigraph W F} {G : LoopMultigraph U I}

/-- Tightness lifts through a tight contraction with either orientation
of the retained cut, including when its shore contains the pole. -/
theorem IsTightCut.lift_expanded {X : Finset V} (ht : H.IsTightCut X)
    {Z : Finset (Option X)} (hZ : (H.contract X).IsTightCut Z) :
    H.IsTightCut (expandedContractShore X Z) := by
  by_cases hn : none ∈ Z
  · have hh := (ht.lift_contract hZ.compl (by simp [hn])).compl
    have he : Finset.univ \ sourceShore X (Finset.univ \ Z) = expandedContractShore X Z := by
      rw [← expandedContractShore_eq_source X (Finset.univ \ Z) (by simp [hn])]
      ext v
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, mem_expandedContractShore, not_not]
    exact he ▸ hh
  · rw [expandedContractShore_eq_source X Z hn]
    exact ht.lift_contract hZ hn

/-- An exact labelled quotient. The target keeps all parallel labels;
only edges internal to a vertex fiber may disappear. Every vertex fiber
is a tight shore in the original graph. -/
structure TightVertexQuotient (H : LoopMultigraph V E) (K : LoopMultigraph W F) where
  vertexMap : V → W
  surjective : Function.Surjective vertexMap
  edgeLift : F → E
  edge_injective : Function.Injective edgeLift
  endEquiv : F → Fin 2 ≃ Fin 2
  map_endAt : ∀ f i, vertexMap (H.endAt (edgeLift f) i) = K.endAt f (endEquiv f i)
  edge_complete : ∀ e, vertexMap (H.endAt e 0) ≠ vertexMap (H.endAt e 1) →
    ∃ f, edgeLift f = e
  fiber_tight : ∀ w, H.IsTightCut (Finset.univ.filter fun v ↦ vertexMap v = w)

namespace TightVertexQuotient

variable (Q : H.TightVertexQuotient K)

omit [DecidableEq F]

def preimage (Z : Finset W) : Finset V := Finset.univ.filter fun v ↦ Q.vertexMap v ∈ Z

def fiber (w : W) : Finset V := Q.preimage {w}

@[simp] theorem mem_preimage (Z : Finset W) (v : V) : v ∈ Q.preimage Z ↔ Q.vertexMap v ∈ Z := by
  simp [preimage]

@[simp] theorem mem_fiber (w : W) (v : V) : v ∈ Q.fiber w ↔ Q.vertexMap v = w := by
  simp [fiber]

theorem tight_fiber (w : W) : H.IsTightCut (Q.fiber w) := by
  simpa only [fiber, preimage, Finset.mem_singleton] using Q.fiber_tight w

theorem preimage_compl (Z : Finset W) : Q.preimage (Finset.univ \ Z) = Finset.univ \ Q.preimage Z := by
  ext v
  simp

theorem fiber_nonempty (w : W) : (Q.fiber w).Nonempty := by
  obtain ⟨v, hv⟩ := Q.surjective w
  exact ⟨v, (Q.mem_fiber w v).mpr hv⟩

theorem fiber_disjoint {w z : W} (hne : w ≠ z) : Disjoint (Q.fiber w) (Q.fiber z) := by
  apply Finset.disjoint_left.mpr
  intro v hvw hvz
  exact hne (((Q.mem_fiber w v).mp hvw).symm.trans ((Q.mem_fiber z v).mp hvz))

theorem fibers_cover : Finset.univ.biUnion Q.fiber = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro v
  exact Finset.mem_biUnion.mpr ⟨Q.vertexMap v, Finset.mem_univ _, by simp⟩

theorem fiber_side (Z : Finset W) (w : W) :
    Q.fiber w ⊆ Q.preimage Z ∨ Q.fiber w ⊆ Finset.univ \ Q.preimage Z := by
  by_cases hw : w ∈ Z
  · exact Or.inl (by intro v hv; simpa only [mem_preimage, (Q.mem_fiber w v).mp hv] using hw)
  · exact Or.inr (by intro v hv; simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
      mem_preimage, (Q.mem_fiber w v).mp hv, hw, not_false_eq_true])

/-- Every target vertex has at least one original representative. -/
theorem card_le_preimage (Z : Finset W) : Z.card ≤ (Q.preimage Z).card := by
  have hi : (Q.preimage Z).image Q.vertexMap = Z := by
    ext w
    constructor
    · intro hw
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      exact (Q.mem_preimage Z v).mp hv
    · intro hw
      obtain ⟨v, rfl⟩ := Q.surjective w
      exact Finset.mem_image.mpr ⟨v, (Q.mem_preimage Z v).mpr hw, rfl⟩
  calc
    Z.card = ((Q.preimage Z).image Q.vertexMap).card := congrArg Finset.card hi.symm
    _ ≤ (Q.preimage Z).card := Finset.card_image_le

theorem fiber_injective : Function.Injective Q.fiber := by
  intro w z he
  obtain ⟨v, hv⟩ := Q.fiber_nonempty w
  have hz : v ∈ Q.fiber z := he ▸ hv
  exact ((Q.mem_fiber w v).mp hv).symm.trans ((Q.mem_fiber z v).mp hz)

/-- With at least three target vertices, every nonsingleton fiber is a
nontrivial original cut. -/
theorem fiber_nontrivial (hc : 3 ≤ Fintype.card W) {w : W}
    (hw : 1 < (Q.fiber w).card) : IsNontrivialCut (Q.fiber w) := by
  refine ⟨hw, ?_⟩
  have hh := Q.card_le_preimage (Finset.univ \ {w})
  rw [Q.preimage_compl] at hh
  change (Finset.univ \ {w}).card ≤ (Finset.univ \ Q.fiber w).card at hh
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    Finset.card_singleton] at hh
  omega

/-- Identity quotient, before any contraction. -/
def refl (H : LoopMultigraph V E) : H.TightVertexQuotient H where
  vertexMap := id
  surjective := Function.surjective_id
  edgeLift := id
  edge_injective := Function.injective_id
  endEquiv _ := Equiv.refl _
  map_endAt _ _ := rfl
  edge_complete e _ := ⟨e, rfl⟩
  fiber_tight w := by
    have he : (Finset.univ.filter fun v : V ↦ id v = w) = {w} := by ext v; simp
    rw [he]
    exact isTightCut_singleton H w

/-- Prepend one tight contraction to an existing quotient. -/
def prependContract {X : Finset V} (ht : H.IsTightCut X)
    (hXC : (Finset.univ \ X).Nonempty) (Q : (H.contract X).TightVertexQuotient K) :
    H.TightVertexQuotient K where
  vertexMap := Q.vertexMap ∘ contractVertex X
  surjective := Q.surjective.comp (contractVertex_surjective X hXC)
  edgeLift f := (Q.edgeLift f).1
  edge_injective := fun f g h ↦ Q.edge_injective (Subtype.ext h)
  endEquiv := Q.endEquiv
  map_endAt := Q.map_endAt
  edge_complete e he := by
    have hem : e ∈ H.meets X := by
      by_contra hn
      have hout (k : Fin 2) : H.endAt e k ∉ X := fun h ↦ hn (mem_meets.mpr ⟨k, h⟩)
      exact he (by simp [contractVertex, hout])
    obtain ⟨f, hf⟩ := Q.edge_complete ⟨e, hem⟩ he
    exact ⟨f, congrArg Subtype.val hf⟩
  fiber_tight w := by
    have he : (Finset.univ.filter fun v ↦ (Q.vertexMap ∘ contractVertex X) v = w) =
        expandedContractShore X (Q.fiber w) := by
      ext v
      simp
    rw [he]
    exact ht.lift_expanded (Q.tight_fiber w)

/-- Relabel the source graph of a quotient; no edge labels are lost. -/
def mapSource (Q : H.TightVertexQuotient K) (f : EndpointIso H G) :
    G.TightVertexQuotient K where
  vertexMap := Q.vertexMap ∘ f.vertexEquiv.symm
  surjective := Q.surjective.comp f.vertexEquiv.symm.surjective
  edgeLift := f.edgeEquiv ∘ Q.edgeLift
  edge_injective := f.edgeEquiv.injective.comp Q.edge_injective
  endEquiv e := (f.endEquiv (Q.edgeLift e)).symm.trans (Q.endEquiv e)
  map_endAt e i := by
    have hh := congrArg f.vertexEquiv.symm
      (f.map_endAt (Q.edgeLift e) ((f.endEquiv (Q.edgeLift e)).symm i))
    simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply] at hh
    change Q.vertexMap (f.vertexEquiv.symm (G.endAt (f.edgeEquiv (Q.edgeLift e)) i)) = _
    rw [← hh]
    exact Q.map_endAt e _
  edge_complete e he := by
    have hold : Q.vertexMap (H.endAt (f.edgeEquiv.symm e) 0) ≠
        Q.vertexMap (H.endAt (f.edgeEquiv.symm e) 1) := by
      intro hn
      apply he
      change Q.vertexMap (f.vertexEquiv.symm (G.endAt e 0)) =
        Q.vertexMap (f.vertexEquiv.symm (G.endAt e 1))
      change Q.vertexMap (f.symm.vertexEquiv (G.endAt e 0)) =
        Q.vertexMap (f.symm.vertexEquiv (G.endAt e 1))
      rw [f.symm.map_endAt, f.symm.map_endAt]
      have same (i j : Fin 2) : Q.vertexMap (H.endAt (f.edgeEquiv.symm e) i) =
          Q.vertexMap (H.endAt (f.edgeEquiv.symm e) j) := by
        fin_cases i <;> fin_cases j
        · rfl
        · exact hn
        · exact hn.symm
        · rfl
      exact same _ _
    obtain ⟨a, ha⟩ := Q.edge_complete _ hold
    exact ⟨a, by change f.edgeEquiv (Q.edgeLift a) = e; rw [ha, Equiv.apply_symm_apply]⟩
  fiber_tight w := by
    have he : (Finset.univ.filter fun v ↦ (Q.vertexMap ∘ f.vertexEquiv.symm) v = w) =
        f.mapVertices (Q.fiber w) := by
      ext v
      obtain ⟨v, rfl⟩ := f.vertexEquiv.surjective v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply,
        Equiv.symm_apply_apply, f.mem_mapVertices, mem_fiber]
    rw [he]
    exact f.isTightCut (Q.tight_fiber w)

end TightVertexQuotient

/-- A flattened terminal Petersen multigraph, with all original vertex
fibers, tightness witnesses, and exact surviving parallel edge labels. -/
structure PetersenFiberModel (H : LoopMultigraph V E) (X : Finset V) where
  Vertex : Type u
  Edge : Type v
  [vertexFintype : Fintype Vertex]
  [edgeFintype : Fintype Edge]
  [vertexDecidableEq : DecidableEq Vertex]
  [edgeDecidableEq : DecidableEq Edge]
  graph : LoopMultigraph Vertex Edge
  quotient : H.TightVertexQuotient graph
  petersen : graph.IsPetersenUpToParallel
  cut : Finset Vertex
  strict : graph.IsStrictlySeparatingCut cut
  selected_eq : quotient.preimage cut = X

attribute [instance] PetersenFiberModel.vertexFintype PetersenFiberModel.edgeFintype
  PetersenFiberModel.vertexDecidableEq PetersenFiberModel.edgeDecidableEq

/-- Every sequential tight-Petersen certificate has an equivalent
partition of the original vertices into tight fibers. -/
theorem HasTightPetersenMinor.exists_fiberModel {X : Finset V} (h : H.HasTightPetersenMinor X) :
    Nonempty (H.PetersenFiberModel X) := by
  induction h with
  | here hp hs =>
    exact ⟨{
      Vertex := _
      Edge := _
      graph := _
      quotient := TightVertexQuotient.refl _
      petersen := hp
      cut := _
      strict := hs
      selected_eq := by ext v; simp [TightVertexQuotient.preimage, TightVertexQuotient.refl] }⟩
  | contract Y ht hY X hp _ ih =>
    obtain ⟨Q⟩ := ih
    let R := TightVertexQuotient.prependContract ht
      (Finset.card_pos.mp (by have := hY.2; omega)) Q.quotient
    refine ⟨{
      Vertex := Q.Vertex
      Edge := Q.Edge
      graph := Q.graph
      quotient := R
      petersen := Q.petersen
      cut := Q.cut
      strict := Q.strict
      selected_eq := ?_ }⟩
    have he : R.preimage Q.cut = expandedContractShore Y (Q.quotient.preimage Q.cut) := by
      ext v
      simp [R, TightVertexQuotient.prependContract]
    rw [he, Q.selected_eq, expandedContractShore_eq_source Y X hp]
  | compl _ ih =>
    obtain ⟨Q⟩ := ih
    exact ⟨{ Q with
      cut := Finset.univ \ Q.cut
      strict := Q.strict.compl
      selected_eq := by rw [Q.quotient.preimage_compl, Q.selected_eq] }⟩
  | iso f _ ih =>
    obtain ⟨Q⟩ := ih
    refine ⟨{
      Vertex := Q.Vertex
      Edge := Q.Edge
      graph := Q.graph
      quotient := Q.quotient.mapSource f
      petersen := Q.petersen
      cut := Q.cut
      strict := Q.strict
      selected_eq := ?_ }⟩
    have he : (Q.quotient.mapSource f).preimage Q.cut = f.mapVertices (Q.quotient.preimage Q.cut) := by
      ext v
      obtain ⟨v, rfl⟩ := f.vertexEquiv.surjective v
      simp [TightVertexQuotient.mapSource, f.mem_mapVertices]
    rw [he, Q.selected_eq]

end GraphPuzzles.LoopMultigraph
