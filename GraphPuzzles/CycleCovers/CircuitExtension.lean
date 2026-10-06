import GraphPuzzles.CycleCovers.DominatingCircuit
import GraphPuzzles.CycleCovers.TJoin

/-!
# Extending an edge-colouring of the complement of a circuit to a five-cycle double cover

Let `H` be a finite cubic endpoint multigraph and `C` a circuit of `H`.  If the edges outside
`C` have a proper three-edge-colouring, with the three nonzero elements of `F₂²` as colours,
then `H` has a double cover by five even subgraphs one of which is exactly `C`.

The construction rotates the colouring independently on the classes of vertices outside `C`
that are joined by edges avoiding `C`, uses the generalized cyclic-word theorem to colour the
edges of `C`, and repairs the remaining parity conditions with a binary T-join.
-/

namespace GraphPuzzles
namespace LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

section Rotate

/-- The three cyclic rotations of the nonzero colours, as linear maps of `F₂²`. -/
def rotate (t : Fin 3) (c : Color) : Color := tripleDifference c t

@[simp]
theorem rotate_zero (t : Fin 3) : rotate t 0 = 0 := by
  fin_cases t <;> simp [rotate, tripleDifference]

theorem rotate_add (t : Fin 3) (a b : Color) :
    rotate t (a + b) = rotate t a + rotate t b := by
  fin_cases t <;> simp [rotate, tripleDifference, Prod.ext_iff] <;> abel

theorem rotate_ne_zero (t : Fin 3) {c : Color} (hc : c ≠ 0) : rotate t c ≠ 0 :=
  tripleDifference_ne_zero c hc t

private theorem color_eq_of_add_eq_zero {a b : Color} (h : a + b = 0) : a = b := by
  calc
    a = a + (b + b) := by rw [color_add_self, add_zero]
    _ = (a + b) + b := by abel
    _ = b := by rw [h, zero_add]

theorem rotate_injective (t : Fin 3) : Function.Injective (rotate t) := by
  intro a b hab
  by_contra hne
  have hsum : a + b ≠ 0 := fun h ↦ hne (color_eq_of_add_eq_zero h)
  apply rotate_ne_zero t hsum
  rw [rotate_add, hab, color_add_self]

theorem sum_rotate (c : Color) : ∑ t, rotate t c = 0 := sum_tripleDifference c

/-- The rotations as additive homomorphisms. -/
def rotateHom (t : Fin 3) : Color →+ Color where
  toFun := rotate t
  map_zero' := rotate_zero t
  map_add' := rotate_add t

@[simp]
theorem rotateHom_apply (t : Fin 3) (c : Color) : rotateHom t c = rotate t c := rfl

theorem sum_rotate_family {I : Type*} [Fintype I] (t : Fin 3) (g : I → Color) :
    ∑ i, rotate t (g i) = rotate t (∑ i, g i) := by
  change ∑ i, rotateHom t (g i) = rotateHom t (∑ i, g i)
  exact (map_sum (rotateHom t) g Finset.univ).symm

end Rotate

section ColorFacts

theorem card_nonzeroColor : Fintype.card {c : Color // c ≠ 0} = 3 := by decide

theorem sum_nonzeroColor : ∑ c : {c : Color // c ≠ 0}, c.1 = 0 := by decide

theorem sum_nonzeroColor_rotate (t : Fin 3) :
    ∑ c : {c : Color // c ≠ 0}, rotate t c.1 = 0 := by
  revert t
  decide

theorem sum_nonzeroColor_quadratic_rotate (t : Fin 3) :
    ∑ c : {c : Color // c ≠ 0}, quadratic (rotate t c.1) = 1 := by
  revert t
  decide

theorem sum_nonzeroColor_one : ∑ _c : {c : Color // c ≠ 0}, (1 : F₂) = 1 := by decide

theorem quadratic_eq_indicator (x : Color) :
    quadratic x = if x = ((1, 1) : Color) then 1 else 0 := by
  rcases x with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;> decide

/-- Bracketing with a fixed nonzero colour takes each value on exactly two colours. -/
theorem card_bracket_eq {c : Color} (hc : c ≠ 0) (ε : F₂) :
    (Finset.univ.filter fun a : Color ↦ bracket a c = ε).card = 2 := by
  revert c ε
  decide

end ColorFacts

section Incidence

variable (G : LoopMultigraph V E)

omit [DecidableEq E] in
/-- Sums over the half-edges at a vertex, written as edge sums weighted by incidence. -/
theorem sum_halfEdgesAt_eq_sum_incidence {M : Type*} [AddCommGroup M] [Module F₂ M]
    (v : V) (g : E → M) :
    ∑ h : G.halfEdgesAt v, g h.1.1 = ∑ e, G.edgeIncidence v e • g e := by
  change ∑ h : {h : HalfEdge E // G.vertex h = v}, g h.1.1 = _
  rw [← Finset.sum_subtype (Finset.univ.filter fun h : HalfEdge E ↦ G.vertex h = v) (by simp)
    (fun h : HalfEdge E ↦ g h.1)]
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  apply Fintype.sum_congr
  intro e
  rw [Fin.sum_univ_two]
  simp only [edgeIncidence, vertex, add_smul]
  by_cases h0 : G.endAt e 0 = v <;> by_cases h1 : G.endAt e 1 = v <;> simp [h0, h1]

/-- Binary evenness, read off the half-edges at every vertex. -/
theorem isEvenEdgeSet_iff_sum_halfEdges (F : Finset E) :
    G.IsEvenEdgeSet F ↔
      ∀ v, ∑ h : G.halfEdgesAt v, (if h.1.1 ∈ F then (1 : F₂) else 0) = 0 := by
  unfold IsEvenEdgeSet
  apply forall_congr'
  intro v
  rw [G.sum_halfEdgesAt_eq_sum_incidence v (fun e ↦ if e ∈ F then (1 : F₂) else 0)]
  simp only [smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  simp

end Incidence

private theorem fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  revert i
  decide

private theorem fin2_eq_rev_of_ne {i j : Fin 2} (h : i ≠ j) : j = Fin.rev i := by
  revert i j
  decide

namespace TraversedCircuit

variable {H : LoopMultigraph V E} (C : H.TraversedCircuit)

omit [DecidableEq E] in
/-- Vertices outside the circuit are incident with no circuit edge. -/
theorem edge_not_mem_of_vertex_not_mem {v : V} (hv : v ∉ C.vertices)
    (h : H.halfEdgesAt v) : h.1.1 ∉ C.edges := by
  intro he
  apply hv
  exact H.mem_edgeSupport_iff.mpr ⟨h.1.1, he, h.1.2, h.2⟩

/-- A proper three-edge-colouring of the edges outside the circuit, with the three nonzero
elements of `F₂²` as colours.  Properness is required only at vertices outside the circuit;
every circuit vertex is incident with a single exterior edge. -/
structure ComplementColoring where
  color : E → Color
  nonzero : ∀ e, e ∉ C.edges → color e ≠ 0
  injective_at : ∀ v, v ∉ C.vertices →
    ∀ h₁ h₂ : H.halfEdgesAt v, color h₁.1.1 = color h₂.1.1 → h₁ = h₂

section EdgeTypes

/-- An edge with exactly one end on the circuit. -/
def IsPendant (e : E) : Prop :=
  ∃ i : Fin 2, H.endAt e i ∈ C.vertices ∧ H.endAt e (Fin.rev i) ∉ C.vertices

/-- An edge with both ends outside the circuit. -/
def IsInternal (e : E) : Prop := ∀ i : Fin 2, H.endAt e i ∉ C.vertices

instance (e : E) : Decidable (C.IsInternal e) :=
  inferInstanceAs (Decidable (∀ i : Fin 2, H.endAt e i ∉ C.vertices))

instance (e : E) : Decidable (C.IsPendant e) :=
  inferInstanceAs (Decidable (∃ i : Fin 2,
    H.endAt e i ∈ C.vertices ∧ H.endAt e (Fin.rev i) ∉ C.vertices))

/-- The edges with both ends outside the circuit. -/
def internalEdges : Finset E := Finset.univ.filter fun e ↦ C.IsInternal e

omit [DecidableEq E] in
@[simp]
theorem mem_internalEdges (e : E) : e ∈ C.internalEdges ↔ C.IsInternal e := by
  simp [internalEdges]

/-- The side of a pendant edge lying on the circuit. -/
def circuitSide (e : E) : Fin 2 := if H.endAt e 0 ∈ C.vertices then 0 else 1

omit [DecidableEq E] in
theorem circuitSide_spec {e : E} (he : C.IsPendant e) :
    H.endAt e (C.circuitSide e) ∈ C.vertices ∧
      H.endAt e (Fin.rev (C.circuitSide e)) ∉ C.vertices := by
  obtain ⟨i, hi, hrev⟩ := he
  rcases fin2_cases i with rfl | rfl
  · simp only [circuitSide, if_pos hi]
    exact ⟨hi, hrev⟩
  · have h0 : H.endAt e 0 ∉ C.vertices := by simpa using hrev
    simp only [circuitSide, if_neg h0]
    exact ⟨hi, by simpa using h0⟩

/-- The end of a pendant edge outside the circuit. -/
def farEnd (e : E) : V := H.endAt e (Fin.rev (C.circuitSide e))

omit [DecidableEq E] in
theorem farEnd_not_mem {e : E} (he : C.IsPendant e) : C.farEnd e ∉ C.vertices :=
  (C.circuitSide_spec he).2

omit [DecidableEq E] in
theorem not_mem_edges_of_isPendant {e : E} (he : C.IsPendant e) : e ∉ C.edges := by
  intro hmem
  apply C.farEnd_not_mem he
  exact H.mem_edgeSupport_iff.mpr ⟨e, hmem, _, rfl⟩

omit [DecidableEq E] in
theorem not_mem_edges_of_isInternal {e : E} (he : C.IsInternal e) : e ∉ C.edges := by
  intro hmem
  apply he 0
  exact H.mem_edgeSupport_iff.mpr ⟨e, hmem, 0, rfl⟩

omit [DecidableEq E] in
theorem side_eq_circuitSide_of_isPendant {e : E} (he : C.IsPendant e) {s : Fin 2}
    (hs : H.endAt e s ∈ C.vertices) : s = C.circuitSide e := by
  obtain ⟨_, hoff⟩ := C.circuitSide_spec he
  by_contra hne
  apply hoff
  rw [← fin2_eq_rev_of_ne (Ne.symm hne)]
  exact hs

omit [DecidableEq E] in
theorem isPendant_of_ends {e : E} {i : Fin 2} (hi : H.endAt e i ∈ C.vertices)
    (hrev : H.endAt e (Fin.rev i) ∉ C.vertices) : C.IsPendant e :=
  ⟨i, hi, hrev⟩

omit [DecidableEq E] in
/-- Every edge outside the circuit with an end outside the circuit is internal or pendant. -/
theorem isInternal_or_isPendant {e : E} {i : Fin 2} (hi : H.endAt e i ∉ C.vertices) :
    C.IsInternal e ∨ C.IsPendant e := by
  by_cases hrev : H.endAt e (Fin.rev i) ∈ C.vertices
  · right
    refine ⟨Fin.rev i, hrev, ?_⟩
    simpa using hi
  · left
    intro j
    rcases fin2_cases i with rfl | rfl <;> rcases fin2_cases j with rfl | rfl <;> simp_all

omit [DecidableEq E] in
theorem endAt_circuitSide_mem {e : E} (h : ∃ i, H.endAt e i ∈ C.vertices) :
    H.endAt e (C.circuitSide e) ∈ C.vertices := by
  obtain ⟨i, hi⟩ := h
  unfold circuitSide
  by_cases h0 : H.endAt e 0 ∈ C.vertices
  · rw [if_pos h0]
    exact h0
  · rw [if_neg h0]
    rcases fin2_cases i with rfl | rfl
    · exact absurd hi h0
    · exact hi

end EdgeTypes

section Classes

/-- Adjacency of two vertices outside the circuit through an edge. -/
def HubAdj (u w : C.Hub) : Prop := ∃ e : E, H.endAt e 0 = u.1 ∧ H.endAt e 1 = w.1

/-- Classes of vertices outside `C` under adjacency through edges avoiding `C`. -/
def HubClass := Quot C.HubAdj

noncomputable instance : DecidableEq C.HubClass := Classical.decEq _

noncomputable instance : Fintype C.HubClass :=
  Fintype.ofSurjective (Quot.mk C.HubAdj) Quot.mk_surjective

/-- The class of a vertex outside the circuit. -/
def hubClass (v : C.Hub) : C.HubClass := Quot.mk _ v

omit [DecidableEq E] in
theorem hubClass_eq_of_edge {e : E} {h0 : H.endAt e 0 ∉ C.vertices}
    {h1 : H.endAt e 1 ∉ C.vertices} :
    C.hubClass ⟨H.endAt e 0, h0⟩ = C.hubClass ⟨H.endAt e 1, h1⟩ :=
  Quot.sound ⟨e, rfl, rfl⟩

omit [DecidableEq E] in
/-- A function on outside vertices constant along internal edges factors through the classes. -/
theorem hubClass_lift_eq (c : V → F₂)
    (hc : ∀ e, C.IsInternal e → c (H.endAt e 0) = c (H.endAt e 1))
    (u w : C.Hub) (huw : C.hubClass u = C.hubClass w) : c u.1 = c w.1 := by
  have hrel := Quot.eqvGen_exact huw
  clear huw
  induction hrel with
  | rel x y hxy =>
      obtain ⟨e, hx, hy⟩ := hxy
      have hint : C.IsInternal e := by
        intro i
        rcases fin2_cases i with rfl | rfl
        · rw [hx]; exact x.2
        · rw [hy]; exact y.2
      rw [← hx, ← hy]
      exact hc e hint
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Letters of the boundary word: a class of outside vertices or a chord. -/
abbrev Letter := C.HubClass ⊕ C.Chord

/-- The letter of an edge outside the circuit: the class of an outside end if there is one,
and the chord itself otherwise. -/
noncomputable def edgeLetter (e : E) (he : e ∉ C.edges) : C.Letter :=
  if h0 : H.endAt e 0 ∉ C.vertices then Sum.inl (C.hubClass ⟨H.endAt e 0, h0⟩)
  else if h1 : H.endAt e 1 ∉ C.vertices then Sum.inl (C.hubClass ⟨H.endAt e 1, h1⟩)
  else Sum.inr ⟨e, he, fun i ↦ by
    rcases fin2_cases i with rfl | rfl
    · exact not_not.mp h0
    · exact not_not.mp h1⟩

omit [DecidableEq E] in
theorem edgeLetter_eq_of_end {e : E} (he : e ∉ C.edges) (i : Fin 2)
    (hi : H.endAt e i ∉ C.vertices) :
    C.edgeLetter e he = Sum.inl (C.hubClass ⟨H.endAt e i, hi⟩) := by
  rcases fin2_cases i with rfl | rfl
  · unfold edgeLetter
    rw [dif_pos hi]
  · unfold edgeLetter
    by_cases h0 : H.endAt e 0 ∉ C.vertices
    · rw [dif_pos h0]
      exact congrArg Sum.inl C.hubClass_eq_of_edge
    · rw [dif_neg h0, dif_pos hi]

omit [DecidableEq E] in
theorem edgeLetter_eq_inr {e : E} (he : e ∉ C.edges) (hall : ∀ i, H.endAt e i ∈ C.vertices) :
    C.edgeLetter e he = Sum.inr ⟨e, he, hall⟩ := by
  unfold edgeLetter
  rw [dif_neg (not_not.mpr (hall 0)), dif_neg (not_not.mpr (hall 1))]

omit [DecidableEq E] in
theorem edgeLetter_of_halfEdgeAt (v : C.Hub) (h : H.halfEdgesAt v.1) :
    C.edgeLetter h.1.1 (C.edge_not_mem_of_vertex_not_mem v.2 h) = Sum.inl (C.hubClass v) := by
  have hv : H.endAt h.1.1 h.1.2 ∉ C.vertices := by
    have hh : H.endAt h.1.1 h.1.2 = v.1 := h.2
    rw [hh]
    exact v.2
  rw [C.edgeLetter_eq_of_end _ h.1.2 hv]
  have hveq : (⟨H.endAt h.1.1 h.1.2, hv⟩ : C.Hub) = v := Subtype.ext h.2
  rw [hveq]

omit [DecidableEq E] in
theorem edgeLetter_of_isPendant {e : E} (he : C.IsPendant e) :
    C.edgeLetter e (C.not_mem_edges_of_isPendant he) =
      Sum.inl (C.hubClass ⟨C.farEnd e, C.farEnd_not_mem he⟩) :=
  C.edgeLetter_eq_of_end _ _ (C.farEnd_not_mem he)

end Classes

section Boundary

variable (hCubic : ∀ v : V, H.degree v = 3)

/-- The exterior half-edge at a circuit position. -/
noncomputable abbrev boundaryHalfEdge (p : C.tour.Pos) : E × Fin 2 :=
  (C.boundaryAtPosition hCubic p).1

theorem boundaryHalfEdge_not_mem (p : C.tour.Pos) :
    (C.boundaryHalfEdge hCubic p).1 ∉ C.edges :=
  (C.boundaryAtPosition hCubic p).2.1

theorem boundaryHalfEdge_endpoint (p : C.tour.Pos) :
    H.endAt (C.boundaryHalfEdge hCubic p).1 (C.boundaryHalfEdge hCubic p).2 =
      C.tour.vertexAt p :=
  C.boundaryAtPosition_endpoint hCubic p

theorem boundaryHalfEdge_injective : Function.Injective (C.boundaryHalfEdge hCubic) := by
  intro p q hpq
  apply (C.positionBoundaryEquiv hCubic).injective
  exact Subtype.ext hpq

/-- The letter at a position: the letter of its exterior edge. -/
noncomputable def letterAt (p : C.tour.Pos) : C.Letter :=
  C.edgeLetter (C.boundaryHalfEdge hCubic p).1 (C.boundaryHalfEdge_not_mem hCubic p)

/-- The boundary word of the circuit. -/
noncomputable def boundaryWord : CyclicWord.Word (V := C.Letter) where
  n := C.tour.n
  letter := C.letterAt hCubic

@[simp]
theorem boundaryWord_letter (p : C.tour.Pos) :
    (C.boundaryWord hCubic).letter p = C.letterAt hCubic p := rfl

@[simp]
theorem boundaryWord_prev (p : C.tour.Pos) :
    (C.boundaryWord hCubic).prev p = C.tour.prev p := rfl

/-- The three half-edges at the circuit vertex of a position: the departing circuit half-edge,
the arriving circuit half-edge, and the exterior half-edge. -/
noncomputable def positionHalfEdge (p : C.tour.Pos) : Fin 3 → E × Fin 2
  | 0 => ((C.tour.edge p).1, C.tour.depart p)
  | 1 => ((C.tour.edge (C.tour.prev p)).1, Fin.rev (C.tour.depart (C.tour.prev p)))
  | 2 => C.boundaryHalfEdge hCubic p

theorem vertex_positionHalfEdge (p : C.tour.Pos) (j : Fin 3) :
    H.vertex (C.positionHalfEdge hCubic p j) = C.tour.vertexAt p := by
  fin_cases j
  · rfl
  · exact C.tour.arrival_prev_eq_vertexAt p
  · exact C.boundaryHalfEdge_endpoint hCubic p

omit [DecidableEq E] in
theorem occurrence_val_eq (p : C.tour.Pos) (o : C.tour.Occurrence (C.tour.vertexAt p)) :
    o.1 = p := by
  have hcard := C.occurrence_card_eq_one (C.vertexAt_mem_vertices p)
  have hle : Fintype.card (C.tour.Occurrence (C.tour.vertexAt p)) ≤ 1 := by omega
  haveI : Subsingleton (C.tour.Occurrence (C.tour.vertexAt p)) :=
    ⟨Fintype.card_le_one_iff.mp hle⟩
  exact congrArg Subtype.val (Subsingleton.elim o ⟨p, rfl⟩)

omit [DecidableEq E] in
private theorem circuit_sides_ne (p : C.tour.Pos) :
    ((C.tour.edge p).1, C.tour.depart p) ≠
      ((C.tour.edge (C.tour.prev p)).1, Fin.rev (C.tour.depart (C.tour.prev p))) := by
  intro h
  have hpair :
      C.tour.positionSideEquivHalfEdge (p, 0) = C.tour.positionSideEquivHalfEdge (p, 1) := by
    change C.tour.positionSideToHalfEdge (p, 0) = C.tour.positionSideToHalfEdge (p, 1)
    change (C.tour.edge p, C.tour.depart p) =
      (C.tour.edge (C.tour.prev p), Fin.rev (C.tour.depart (C.tour.prev p)))
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    exact Prod.ext (Subtype.ext h1) h2
  have := congrArg Prod.snd (C.tour.positionSideEquivHalfEdge.injective hpair)
  simp at this

theorem positionHalfEdge_injective (p : C.tour.Pos) :
    Function.Injective (C.positionHalfEdge hCubic p) := by
  intro a b hab
  have hmem : ∀ j : Fin 3, j ≠ 2 → (C.positionHalfEdge hCubic p j).1 ∈ C.edges := by
    intro j hj
    fin_cases j
    · exact (C.tour.edge p).2
    · exact (C.tour.edge (C.tour.prev p)).2
    · exact absurd rfl hj
  have hnot : (C.positionHalfEdge hCubic p 2).1 ∉ C.edges := C.boundaryHalfEdge_not_mem hCubic p
  fin_cases a <;> fin_cases b
  · rfl
  · exact absurd hab (C.circuit_sides_ne p)
  · exact absurd (congrArg Prod.fst hab ▸ hmem 0 (by decide)) hnot
  · exact absurd hab.symm (C.circuit_sides_ne p)
  · rfl
  · exact absurd (congrArg Prod.fst hab ▸ hmem 1 (by decide)) hnot
  · exact absurd (congrArg Prod.fst hab.symm ▸ hmem 0 (by decide)) hnot
  · exact absurd (congrArg Prod.fst hab.symm ▸ hmem 1 (by decide)) hnot
  · rfl

theorem positionHalfEdge_surjective (p : C.tour.Pos)
    (h : H.halfEdgesAt (C.tour.vertexAt p)) :
    ∃ j : Fin 3, C.positionHalfEdge hCubic p j = h.1 := by
  rcases h with ⟨⟨e, s⟩, hv⟩
  by_cases he : e ∈ C.edges
  · let h' : C.restricted.halfEdgesAt (C.tour.vertexAt p) := ⟨(⟨e, he⟩, s), hv⟩
    obtain ⟨⟨o, t⟩, hot⟩ := (C.tour.occurrenceSideEquivHalfEdgesAt _).surjective h'
    have hop : o.1 = p := C.occurrence_val_eq p o
    have hval : C.tour.positionSideToHalfEdge (o.1, t) = (⟨e, he⟩, s) :=
      congrArg Subtype.val hot
    rw [hop] at hval
    fin_cases t
    · refine ⟨0, ?_⟩
      change (C.tour.edge p, C.tour.depart p) = (⟨e, he⟩, s) at hval
      change ((C.tour.edge p).1, C.tour.depart p) = (e, s)
      obtain ⟨h1, h2⟩ := Prod.mk.inj hval
      exact Prod.ext (congrArg Subtype.val h1) h2
    · refine ⟨1, ?_⟩
      change (C.tour.edge (C.tour.prev p), Fin.rev (C.tour.depart (C.tour.prev p))) =
        (⟨e, he⟩, s) at hval
      change ((C.tour.edge (C.tour.prev p)).1, Fin.rev (C.tour.depart (C.tour.prev p))) =
        (e, s)
      obtain ⟨h1, h2⟩ := Prod.mk.inj hval
      exact Prod.ext (congrArg Subtype.val h1) h2
  · refine ⟨2, ?_⟩
    have hmem : (e, s) ∈ C.externalHalfEdges (C.tour.vertexAt p) :=
      (C.mem_externalHalfEdges _ _).mpr ⟨he, hv⟩
    exact (C.externalHalfEdge_unique hCubic _ (C.vertexAt_mem_vertices p) hmem).symm

/-- The enumeration of the three half-edges at a circuit vertex. -/
noncomputable def positionHalfEdgeEquiv (p : C.tour.Pos) :
    Fin 3 ≃ H.halfEdgesAt (C.tour.vertexAt p) :=
  Equiv.ofBijective
    (fun j ↦ ⟨C.positionHalfEdge hCubic p j, C.vertex_positionHalfEdge hCubic p j⟩)
    ⟨fun a b hab ↦ C.positionHalfEdge_injective hCubic p (congrArg Subtype.val hab),
      fun h ↦ by
        obtain ⟨j, hj⟩ := C.positionHalfEdge_surjective hCubic p h
        exact ⟨j, Subtype.ext hj⟩⟩

/-- Sums over the half-edges at a circuit vertex split into the three normal-form terms. -/
theorem sum_halfEdgesAt_circuit {M : Type*} [AddCommMonoid M] (p : C.tour.Pos)
    (g : E × Fin 2 → M) :
    ∑ h : H.halfEdgesAt (C.tour.vertexAt p), g h.1 =
      g ((C.tour.edge p).1, C.tour.depart p) +
        g ((C.tour.edge (C.tour.prev p)).1, Fin.rev (C.tour.depart (C.tour.prev p))) +
        g (C.boundaryHalfEdge hCubic p) := by
  rw [← (C.positionHalfEdgeEquiv hCubic p).sum_comp, Fin.sum_univ_three]
  rfl


/-- The far end of the exterior half-edge at a position. -/
noncomputable def farVertex (p : C.tour.Pos) : V :=
  H.endAt (C.boundaryHalfEdge hCubic p).1 (Fin.rev (C.boundaryHalfEdge hCubic p).2)

/-- The position whose exterior half-edge is the circuit side of an edge meeting the circuit. -/
noncomputable def posOf (e : E) (h : e ∉ C.edges ∧ ∃ i, H.endAt e i ∈ C.vertices) :
    C.tour.Pos :=
  (C.positionBoundaryEquiv hCubic).symm ⟨(e, C.circuitSide e), h.1, C.endAt_circuitSide_mem h.2⟩

theorem posOf_boundary (p : C.tour.Pos) (hp : C.IsPendant (C.boundaryHalfEdge hCubic p).1)
    (h : (C.boundaryHalfEdge hCubic p).1 ∉ C.edges ∧
      ∃ i, H.endAt (C.boundaryHalfEdge hCubic p).1 i ∈ C.vertices) :
    C.posOf hCubic _ h = p := by
  unfold posOf
  apply (C.positionBoundaryEquiv hCubic).injective
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  change ((C.boundaryHalfEdge hCubic p).1, C.circuitSide (C.boundaryHalfEdge hCubic p).1) =
    C.boundaryHalfEdge hCubic p
  rw [← C.side_eq_circuitSide_of_isPendant hp (by
    rw [C.boundaryHalfEdge_endpoint]
    exact C.vertexAt_mem_vertices p)]

end Boundary

section DoubleCount

variable (hCubic : ∀ v : V, H.degree v = 3) (f : C.ComplementColoring)

/-- The colour of a half-edge at an outside vertex, as a nonzero colour. -/
def hubColor (v : C.Hub) (h : H.halfEdgesAt v.1) : {c : Color // c ≠ 0} :=
  ⟨f.color h.1.1, f.nonzero _ (C.edge_not_mem_of_vertex_not_mem v.2 h)⟩

include hCubic in
omit [DecidableEq E] in
theorem hubColor_bijective (v : C.Hub) : Function.Bijective (C.hubColor f v) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun h₁ h₂ hh ↦ f.injective_at v.1 v.2 h₁ h₂ (congrArg Subtype.val hh), ?_⟩
  rw [card_nonzeroColor]
  exact hCubic v.1

include hCubic in
omit [DecidableEq E] in
theorem sum_hub_one (v : C.Hub) : ∑ _h : H.halfEdgesAt v.1, (1 : F₂) = 1 := by
  rw [Finset.sum_const, Finset.card_univ]
  change (H.degree v.1) • (1 : F₂) = 1
  rw [hCubic]
  decide

include hCubic in
omit [DecidableEq E] in
/-- Sums over the half-edges at an outside vertex are sums over the three nonzero colours. -/
theorem sum_hub_colors {M : Type*} [AddCommMonoid M] (v : C.Hub) (g : Color → M) :
    ∑ h : H.halfEdgesAt v.1, g (f.color h.1.1) = ∑ c : {c : Color // c ≠ 0}, g c.1 :=
  (C.hubColor_bijective hCubic f v).sum_comp (fun c ↦ g c.1)

private theorem sum_hub_indicator (c : V → F₂) (w : V) :
    ∑ v : C.Hub, c v.1 * (if w = v.1 then (1 : F₂) else 0) =
      if w ∈ C.vertices then 0 else c w := by
  change ∑ v : {v : V // v ∉ C.vertices}, c v.1 * (if w = v.1 then (1 : F₂) else 0) = _
  rw [← Finset.sum_subtype (Finset.univ.filter fun v : V ↦ v ∉ C.vertices) (by simp)
    (fun v ↦ c v * (if w = v then (1 : F₂) else 0))]
  rw [Finset.sum_filter, Finset.sum_eq_single w]
  · by_cases hw : w ∈ C.vertices <;> simp [hw]
  · intro v _ hv
    simp [Ne.symm hv]
  · intro h
    exact absurd (Finset.mem_univ w) h

private theorem sum_hub_mul_edgeIncidence (c : V → F₂) (e : E) :
    ∑ v : C.Hub, c v.1 * H.edgeIncidence v.1 e =
      (if H.endAt e 0 ∈ C.vertices then 0 else c (H.endAt e 0)) +
        (if H.endAt e 1 ∈ C.vertices then 0 else c (H.endAt e 1)) := by
  simp only [edgeIncidence, mul_add, Finset.sum_add_distrib]
  rw [C.sum_hub_indicator c (H.endAt e 0), C.sum_hub_indicator c (H.endAt e 1)]

private theorem rev_zero_fin2 : Fin.rev (0 : Fin 2) = 1 := by decide
private theorem rev_one_fin2 : Fin.rev (1 : Fin 2) = 0 := by decide

omit [DecidableEq E] in
private theorem weight_eq (c : V → F₂)
    (hc : ∀ e, C.IsInternal e → c (H.endAt e 0) = c (H.endAt e 1)) (e : E) :
    (if H.endAt e 0 ∈ C.vertices then 0 else c (H.endAt e 0)) +
        (if H.endAt e 1 ∈ C.vertices then 0 else c (H.endAt e 1)) =
      if C.IsPendant e then c (C.farEnd e) else 0 := by
  by_cases h0 : H.endAt e 0 ∈ C.vertices <;> by_cases h1 : H.endAt e 1 ∈ C.vertices
  · have hnp : ¬ C.IsPendant e := by
      rintro ⟨i, _, hrev⟩
      rcases fin2_cases i with rfl | rfl
      · rw [rev_zero_fin2] at hrev
        exact hrev h1
      · rw [rev_one_fin2] at hrev
        exact hrev h0
    simp [h0, h1, hnp]
  · have hp : C.IsPendant e := ⟨0, h0, by rw [rev_zero_fin2]; exact h1⟩
    have hside : C.circuitSide e = 0 := by simp [circuitSide, h0]
    have hfar : C.farEnd e = H.endAt e 1 := by
      unfold farEnd
      rw [hside, rev_zero_fin2]
    simp [h0, h1, hp, hfar]
  · have hp : C.IsPendant e := ⟨1, h1, by rw [rev_one_fin2]; exact h0⟩
    have hside : C.circuitSide e = 1 := by simp [circuitSide, h0]
    have hfar : C.farEnd e = H.endAt e 0 := by
      unfold farEnd
      rw [hside, rev_one_fin2]
    simp [h0, h1, hp, hfar]
  · have hint : C.IsInternal e := by
      intro i
      rcases fin2_cases i with rfl | rfl
      · exact h0
      · exact h1
    have hnp : ¬ C.IsPendant e := by
      rintro ⟨i, hi, _⟩
      exact hint i hi
    simp [h0, h1, hnp, hc e hint]

/-- **Double counting across the circuit.**  For a vertex function constant along internal
edges, the weighted sum of the half-edge sums at outside vertices reduces to a sum over pendant
edges, each weighted by the value at its outside end. -/
theorem sum_hub_weighted {M : Type*} [AddCommGroup M] [Module F₂ M] (c : V → F₂)
    (hc : ∀ e, C.IsInternal e → c (H.endAt e 0) = c (H.endAt e 1)) (g : E → M) :
    ∑ v : C.Hub, c v.1 • ∑ h : H.halfEdgesAt v.1, g h.1.1 =
      ∑ e, (if C.IsPendant e then c (C.farEnd e) else 0) • g e := by
  calc
    ∑ v : C.Hub, c v.1 • ∑ h : H.halfEdgesAt v.1, g h.1.1
        = ∑ v : C.Hub, ∑ e, (c v.1 * H.edgeIncidence v.1 e) • g e := by
          apply Fintype.sum_congr
          intro v
          rw [H.sum_halfEdgesAt_eq_sum_incidence, Finset.smul_sum]
          apply Fintype.sum_congr
          intro e
          rw [smul_smul]
    _ = ∑ e, (∑ v : C.Hub, c v.1 * H.edgeIncidence v.1 e) • g e := by
          rw [Finset.sum_comm]
          apply Fintype.sum_congr
          intro e
          rw [Finset.sum_smul]
    _ = _ := by
          apply Fintype.sum_congr
          intro e
          rw [C.sum_hub_mul_edgeIncidence, C.weight_eq c hc]

/-- Sums over pendant edges are sums over the positions whose exterior edge is pendant. -/
theorem sum_pendant_positions {M : Type*} [AddCommMonoid M] (F : E → M) :
    ∑ p : C.tour.Pos,
      (if C.IsPendant (C.boundaryHalfEdge hCubic p).1 then F (C.boundaryHalfEdge hCubic p).1
        else 0) =
      ∑ e, if C.IsPendant e then F e else 0 := by
  let G : E × Fin 2 → M := fun x ↦ if C.IsPendant x.1 then F x.1 else 0
  have h1 : ∑ p : C.tour.Pos, G (C.positionBoundaryEquiv hCubic p).1 =
      ∑ x : C.BoundaryHalfEdge, G x.1 :=
    (C.positionBoundaryEquiv hCubic).sum_comp (fun x ↦ G x.1)
  change ∑ p : C.tour.Pos, G (C.positionBoundaryEquiv hCubic p).1 = _
  rw [h1]
  change ∑ x : {x : E × Fin 2 // x.1 ∉ C.edges ∧ H.endAt x.1 x.2 ∈ C.vertices}, G x.1 = _
  rw [← Finset.sum_subtype (Finset.univ.filter fun x : E × Fin 2 ↦
    x.1 ∉ C.edges ∧ H.endAt x.1 x.2 ∈ C.vertices) (by simp) G]
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  apply Fintype.sum_congr
  intro e
  rw [Fin.sum_univ_two]
  by_cases hp : C.IsPendant e
  · obtain ⟨hon, hoff⟩ := C.circuitSide_spec hp
    have hne := C.not_mem_edges_of_isPendant hp
    rcases fin2_cases (C.circuitSide e) with hs | hs
    · rw [hs] at hon hoff
      rw [rev_zero_fin2] at hoff
      simp [G, hne, hon, hoff, hp]
    · rw [hs] at hon hoff
      rw [rev_one_fin2] at hoff
      simp [G, hne, hon, hoff, hp]
  · simp [G, hp]

theorem farVertex_not_mem_iff (p : C.tour.Pos) :
    C.farVertex hCubic p ∉ C.vertices ↔ C.IsPendant (C.boundaryHalfEdge hCubic p).1 := by
  constructor
  · intro h
    refine ⟨(C.boundaryHalfEdge hCubic p).2, ?_, h⟩
    rw [C.boundaryHalfEdge_endpoint]
    exact C.vertexAt_mem_vertices p
  · intro hp
    have hside : (C.boundaryHalfEdge hCubic p).2 =
        C.circuitSide (C.boundaryHalfEdge hCubic p).1 := by
      apply C.side_eq_circuitSide_of_isPendant hp
      rw [C.boundaryHalfEdge_endpoint]
      exact C.vertexAt_mem_vertices p
    unfold farVertex
    rw [hside]
    exact C.farEnd_not_mem hp

theorem farVertex_eq_farEnd {p : C.tour.Pos}
    (hp : C.IsPendant (C.boundaryHalfEdge hCubic p).1) :
    C.farVertex hCubic p = C.farEnd (C.boundaryHalfEdge hCubic p).1 := by
  have hside : (C.boundaryHalfEdge hCubic p).2 =
      C.circuitSide (C.boundaryHalfEdge hCubic p).1 := by
    apply C.side_eq_circuitSide_of_isPendant hp
    rw [C.boundaryHalfEdge_endpoint]
    exact C.vertexAt_mem_vertices p
  unfold farVertex farEnd
  rw [hside]

/-- A position whose exterior edge is not pendant sees a chord. -/
theorem chord_of_not_isPendant {p : C.tour.Pos}
    (hp : ¬ C.IsPendant (C.boundaryHalfEdge hCubic p).1) :
    ∀ i, H.endAt (C.boundaryHalfEdge hCubic p).1 i ∈ C.vertices := by
  intro i
  by_contra hi
  rcases C.isInternal_or_isPendant hi with hint | hpend
  · apply hint (C.boundaryHalfEdge hCubic p).2
    rw [C.boundaryHalfEdge_endpoint]
    exact C.vertexAt_mem_vertices p
  · exact hp hpend

/-- Lift a vertex function constant along internal edges to the letters. -/
noncomputable def letterLift (c : V → F₂)
    (hc : ∀ e, C.IsInternal e → c (H.endAt e 0) = c (H.endAt e 1)) : C.Letter → F₂ :=
  Sum.elim
    (Quot.lift (fun v : C.Hub ↦ c v.1)
      (fun u w huw ↦ C.hubClass_lift_eq c hc u w (Quot.sound huw)))
    (fun _ ↦ 0)

omit [DecidableEq E] in
@[simp]
theorem letterLift_inl (c : V → F₂)
    (hc : ∀ e, C.IsInternal e → c (H.endAt e 0) = c (H.endAt e 1)) (v : C.Hub) :
    C.letterLift c hc (Sum.inl (C.hubClass v)) = c v.1 := rfl

omit [DecidableEq E] in
@[simp]
theorem letterLift_inr (c : V → F₂)
    (hc : ∀ e, C.IsInternal e → c (H.endAt e 0) = c (H.endAt e 1)) (x : C.Chord) :
    C.letterLift c hc (Sum.inr x) = 0 := rfl

theorem letterLift_letterAt (c : V → F₂)
    (hc : ∀ e, C.IsInternal e → c (H.endAt e 0) = c (H.endAt e 1)) (p : C.tour.Pos) :
    (if C.IsPendant (C.boundaryHalfEdge hCubic p).1 then
      c (C.farEnd (C.boundaryHalfEdge hCubic p).1) else 0) =
      C.letterLift c hc (C.letterAt hCubic p) := by
  by_cases hp : C.IsPendant (C.boundaryHalfEdge hCubic p).1
  · rw [if_pos hp]
    unfold letterAt
    rw [C.edgeLetter_of_isPendant hp]
    rfl
  · rw [if_neg hp]
    unfold letterAt
    rw [C.edgeLetter_eq_inr _ (C.chord_of_not_isPendant hCubic hp)]
    rfl

/-- Regrouping a sum over positions according to their letters. -/
theorem sum_over_letters {M : Type*} [AddCommMonoid M] (F : C.Letter → C.tour.Pos → M) :
    ∑ p, F (C.letterAt hCubic p) p =
      ∑ ℓ, ∑ o : (C.boundaryWord hCubic).Occurrence ℓ, F ℓ o.1 := by
  let e := Equiv.sigmaFiberEquiv (C.letterAt hCubic)
  calc
    ∑ p, F (C.letterAt hCubic p) p =
        ∑ q : Σ ℓ, {p // C.letterAt hCubic p = ℓ}, F (C.letterAt hCubic q.2.1) q.2.1 := by
          symm
          exact e.sum_comp (fun p ↦ F (C.letterAt hCubic p) p)
    _ = ∑ ℓ, ∑ o : {p // C.letterAt hCubic p = ℓ}, F ℓ o.1 := by
          rw [Fintype.sum_sigma]
          apply Fintype.sum_congr
          intro ℓ
          apply Fintype.sum_congr
          intro o
          rw [o.2]

/-- The letter form of the double count. -/
theorem sum_hub_weighted_letters {M : Type*} [AddCommGroup M] [Module F₂ M] (c : V → F₂)
    (hc : ∀ e, C.IsInternal e → c (H.endAt e 0) = c (H.endAt e 1)) (g : E → M) :
    ∑ v : C.Hub, c v.1 • ∑ h : H.halfEdgesAt v.1, g h.1.1 =
      ∑ ℓ, C.letterLift c hc ℓ •
        ∑ o : (C.boundaryWord hCubic).Occurrence ℓ, g (C.boundaryHalfEdge hCubic o.1).1 := by
  rw [C.sum_hub_weighted c hc g]
  have h1 : ∀ e, (if C.IsPendant e then c (C.farEnd e) else 0) • g e =
      if C.IsPendant e then c (C.farEnd e) • g e else 0 := by
    intro e
    by_cases hp : C.IsPendant e <;> simp [hp]
  simp_rw [h1]
  rw [← C.sum_pendant_positions hCubic (fun e ↦ c (C.farEnd e) • g e)]
  have h2 : ∀ p : C.tour.Pos,
      (if C.IsPendant (C.boundaryHalfEdge hCubic p).1 then
        c (C.farEnd (C.boundaryHalfEdge hCubic p).1) • g (C.boundaryHalfEdge hCubic p).1
        else 0) =
      C.letterLift c hc (C.letterAt hCubic p) • g (C.boundaryHalfEdge hCubic p).1 := by
    intro p
    rw [← C.letterLift_letterAt hCubic c hc p]
    by_cases hp : C.IsPendant (C.boundaryHalfEdge hCubic p).1 <;> simp [hp]
  simp_rw [h2]
  rw [C.sum_over_letters hCubic
    (fun ℓ p ↦ C.letterLift c hc ℓ • g (C.boundaryHalfEdge hCubic p).1)]
  apply Fintype.sum_congr
  intro ℓ
  rw [Finset.smul_sum]

end DoubleCount

section Patterns

variable (hCubic : ∀ v : V, H.degree v = 3) (f : C.ComplementColoring)

/-- The boundary colour at a position. -/
noncomputable def boundaryColor (p : C.tour.Pos) : Color :=
  f.color (C.boundaryHalfEdge hCubic p).1

theorem boundaryColor_ne_zero (p : C.tour.Pos) : C.boundaryColor hCubic f p ≠ 0 :=
  f.nonzero _ (C.boundaryHalfEdge_not_mem hCubic p)

/-- The boundary colours at the occurrences of a class letter sum to zero. -/
theorem sum_boundaryColor_inl (K : C.HubClass) :
    ∑ o : (C.boundaryWord hCubic).Occurrence (Sum.inl K), C.boundaryColor hCubic f o.1 = 0 := by
  classical
  let c : V → F₂ := fun v ↦
    if h : v ∉ C.vertices then (if C.hubClass ⟨v, h⟩ = K then 1 else 0) else 0
  have hc : ∀ e, C.IsInternal e → c (H.endAt e 0) = c (H.endAt e 1) := by
    intro e he
    simp only [c, dif_pos (he 0), dif_pos (he 1)]
    rw [C.hubClass_eq_of_edge]
  have hlift : ∀ ℓ, C.letterLift c hc ℓ = if ℓ = Sum.inl K then 1 else 0 := by
    intro ℓ
    rcases ℓ with K' | x
    · induction K' using Quot.ind with
      | mk v =>
          change c v.1 = _
          simp only [c, dif_pos v.2]
          simp [hubClass]
    · simp
  have h := C.sum_hub_weighted_letters hCubic c hc f.color
  have hL : ∑ v : C.Hub, c v.1 • ∑ h : H.halfEdgesAt v.1, f.color h.1.1 = 0 := by
    apply Fintype.sum_eq_zero
    intro v
    rw [show ∑ h : H.halfEdgesAt v.1, f.color h.1.1 = ∑ c : {c : Color // c ≠ 0}, c.1 from
      C.sum_hub_colors hCubic f v (fun x ↦ x), sum_nonzeroColor, smul_zero]
  rw [hL] at h
  simp only [hlift, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at h
  exact h.symm

/-- The boundary half-edge of a chord side. -/
def chordBoundary (x : C.Chord) (i : Fin 2) : C.BoundaryHalfEdge := ⟨(x.1, i), x.2.1, x.2.2 i⟩

/-- The position of a chord side. -/
noncomputable def chordPos (x : C.Chord) (i : Fin 2) : C.tour.Pos :=
  (C.positionBoundaryEquiv hCubic).symm (C.chordBoundary x i)

theorem boundaryHalfEdge_chordPos (x : C.Chord) (i : Fin 2) :
    C.boundaryHalfEdge hCubic (C.chordPos hCubic x i) = (x.1, i) := by
  change ((C.positionBoundaryEquiv hCubic) ((C.positionBoundaryEquiv hCubic).symm
    (C.chordBoundary x i))).1 = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem letterAt_chordPos (x : C.Chord) (i : Fin 2) :
    C.letterAt hCubic (C.chordPos hCubic x i) = Sum.inr x := by
  have hb := C.boundaryHalfEdge_chordPos hCubic x i
  have hedge : (C.boundaryHalfEdge hCubic (C.chordPos hCubic x i)).1 = x.1 :=
    congrArg Prod.fst hb
  have hall : ∀ j, H.endAt (C.boundaryHalfEdge hCubic (C.chordPos hCubic x i)).1 j ∈
      C.vertices := by
    rw [hedge]
    exact x.2.2
  unfold letterAt
  rw [C.edgeLetter_eq_inr _ hall]
  congr 1
  exact Subtype.ext hedge

omit [DecidableEq E] in
theorem eq_of_edgeLetter_eq_inr {e : E} {he : e ∉ C.edges} {x : C.Chord}
    (h : C.edgeLetter e he = Sum.inr x) : e = x.1 := by
  unfold edgeLetter at h
  split_ifs at h with h0 h1
  exact congrArg Subtype.val (Sum.inr.inj h)

/-- The two sides of a chord are exactly the occurrences of its letter. -/
noncomputable def chordOccurrenceEquiv (x : C.Chord) :
    Fin 2 ≃ (C.boundaryWord hCubic).Occurrence (Sum.inr x) :=
  Equiv.ofBijective (fun i ↦ ⟨C.chordPos hCubic x i, C.letterAt_chordPos hCubic x i⟩)
    ⟨by
      intro i j hij
      have hp : C.chordPos hCubic x i = C.chordPos hCubic x j := congrArg Subtype.val hij
      have hb := (C.positionBoundaryEquiv hCubic).symm.injective hp
      exact congrArg (fun y : C.BoundaryHalfEdge ↦ y.1.2) hb,
    by
      rintro ⟨p, hp⟩
      have hp' : C.edgeLetter (C.boundaryHalfEdge hCubic p).1
          (C.boundaryHalfEdge_not_mem hCubic p) = Sum.inr x := hp
      have hedge : (C.boundaryHalfEdge hCubic p).1 = x.1 :=
        C.eq_of_edgeLetter_eq_inr hp'
      refine ⟨(C.boundaryHalfEdge hCubic p).2, Subtype.ext ?_⟩
      change (C.positionBoundaryEquiv hCubic).symm _ = p
      apply (C.positionBoundaryEquiv hCubic).injective
      rw [Equiv.apply_symm_apply]
      apply Subtype.ext
      change (x.1, (C.boundaryHalfEdge hCubic p).2) = C.boundaryHalfEdge hCubic p
      rw [← hedge]⟩

theorem sum_chord_occurrences {M : Type*} [AddCommMonoid M] (x : C.Chord)
    (F : C.tour.Pos → M) :
    ∑ o : (C.boundaryWord hCubic).Occurrence (Sum.inr x), F o.1 =
      F (C.chordPos hCubic x 0) + F (C.chordPos hCubic x 1) := by
  rw [← (C.chordOccurrenceEquiv hCubic x).sum_comp (fun o ↦ F o.1), Fin.sum_univ_two]
  rfl

theorem boundaryColor_chordPos (x : C.Chord) (i : Fin 2) :
    C.boundaryColor hCubic f (C.chordPos hCubic x i) = f.color x.1 := by
  unfold boundaryColor
  rw [C.boundaryHalfEdge_chordPos]

theorem sum_boundaryColor_inr (x : C.Chord) :
    ∑ o : (C.boundaryWord hCubic).Occurrence (Sum.inr x), C.boundaryColor hCubic f o.1 = 0 := by
  rw [C.sum_chord_occurrences hCubic x, C.boundaryColor_chordPos, C.boundaryColor_chordPos,
    color_add_self]

theorem sum_boundaryColor (ℓ : C.Letter) :
    ∑ o : (C.boundaryWord hCubic).Occurrence ℓ, C.boundaryColor hCubic f o.1 = 0 := by
  rcases ℓ with K | x
  · exact C.sum_boundaryColor_inl hCubic f K
  · exact C.sum_boundaryColor_inr hCubic f x

/-- The pattern family on the boundary word: the three rotations of the boundary colours. -/
noncomputable def boundaryPatterns : (C.boundaryWord hCubic).Patterns where
  pattern _ t o := rotate t (C.boundaryColor hCubic f o.1)
  ne_zero _ t o := rotate_ne_zero t (C.boundaryColor_ne_zero hCubic f o.1)
  sum_occurrences ℓ t := by
    rw [sum_rotate_family, C.sum_boundaryColor hCubic f ℓ, rotate_zero]
  sum_choices _ o := sum_rotate _

/-- A colouring of the circuit gaps supplied by the generalized cyclic-word theorem, together
with the chosen rotation at every letter. -/
structure GapColoring where
  choice : C.Letter → Fin 3
  color : C.tour.Pos → Color
  transition_ne : ∀ p, color (C.tour.prev p) ≠ color p
  color_even : ∀ (ℓ : C.Letter) (z : Color),
    Even (Fintype.card {os : (C.boundaryWord hCubic).Occurrence ℓ × Fin 2 //
      (C.boundaryWord hCubic).incidentColor color os.1 os.2 = z})
  diff : ∀ p, color (C.tour.prev p) + color p =
    rotate (choice (C.letterAt hCubic p)) (C.boundaryColor hCubic f p)

theorem exists_gapColoring : Nonempty (C.GapColoring hCubic f) := by
  obtain ⟨choice, X, hdiff⟩ :=
    (C.boundaryWord hCubic).exists_coloring_of_patterns (C.boundaryPatterns hCubic f)
  exact ⟨{
    choice := choice
    color := X.color
    transition_ne := X.transition_ne
    color_even := X.color_even
    diff := hdiff }⟩

theorem posOf_chord (x : C.Chord)
    (h : x.1 ∉ C.edges ∧ ∃ i, H.endAt x.1 i ∈ C.vertices) :
    C.posOf hCubic x.1 h = C.chordPos hCubic x 0 := by
  unfold posOf chordPos
  congr 1
  apply Subtype.ext
  change (x.1, C.circuitSide x.1) = (x.1, 0)
  rw [show C.circuitSide x.1 = 0 by simp [circuitSide, x.2.2 0]]

end Patterns

section Lift

namespace GapColoring

variable {C} {hCubic : ∀ v : V, H.degree v = 3} {f : C.ComplementColoring}
  (B : C.GapColoring hCubic f)

/-- The colouring outside the circuit after rotating every letter by its chosen rotation. -/
noncomputable def rotated (e : E) : Color :=
  if he : e ∈ C.edges then f.color e else rotate (B.choice (C.edgeLetter e he)) (f.color e)

theorem rotated_of_not_mem {e : E} (he : e ∉ C.edges) :
    B.rotated e = rotate (B.choice (C.edgeLetter e he)) (f.color e) := by
  unfold rotated
  rw [dif_neg he]

theorem rotated_ne_zero {e : E} (he : e ∉ C.edges) : B.rotated e ≠ 0 := by
  rw [B.rotated_of_not_mem he]
  exact rotate_ne_zero _ (f.nonzero e he)

theorem rotated_at_hub (v : C.Hub) (h : H.halfEdgesAt v.1) :
    B.rotated h.1.1 = rotate (B.choice (Sum.inl (C.hubClass v))) (f.color h.1.1) := by
  rw [B.rotated_of_not_mem (C.edge_not_mem_of_vertex_not_mem v.2 h),
    C.edgeLetter_of_halfEdgeAt v h]

/-- The rotated boundary colour at a position is the difference of the adjacent gap colours. -/
theorem rotated_boundary (p : C.tour.Pos) :
    B.rotated (C.boundaryHalfEdge hCubic p).1 = B.color (C.tour.prev p) + B.color p := by
  rw [B.rotated_of_not_mem (C.boundaryHalfEdge_not_mem hCubic p), B.diff p]
  rfl

theorem sum_hub_rotated (v : C.Hub) : ∑ h : H.halfEdgesAt v.1, B.rotated h.1.1 = 0 := by
  have h1 : ∀ h : H.halfEdgesAt v.1,
      B.rotated h.1.1 = rotate (B.choice (Sum.inl (C.hubClass v))) (f.color h.1.1) :=
    B.rotated_at_hub v
  simp_rw [h1]
  rw [C.sum_hub_colors hCubic f v (fun x ↦ rotate (B.choice (Sum.inl (C.hubClass v))) x)]
  exact sum_nonzeroColor_rotate _

theorem sum_hub_quadratic_rotated (v : C.Hub) :
    ∑ h : H.halfEdgesAt v.1, quadratic (B.rotated h.1.1) = 1 := by
  have h1 : ∀ h : H.halfEdgesAt v.1, quadratic (B.rotated h.1.1) =
      quadratic (rotate (B.choice (Sum.inl (C.hubClass v))) (f.color h.1.1)) :=
    fun h ↦ by rw [B.rotated_at_hub v h]
  simp_rw [h1]
  rw [C.sum_hub_colors hCubic f v
    (fun x ↦ quadratic (rotate (B.choice (Sum.inl (C.hubClass v))) x))]
  exact sum_nonzeroColor_quadratic_rotate _

/-- The boundary bit at a position. -/
noncomputable def epsAt (p : C.tour.Pos) : F₂ :=
  bracket (B.color (C.tour.prev p)) (B.color (C.tour.prev p) + B.color p)

/-- Polarization of the quadratic form across a position. -/
theorem quadratic_pair (p : C.tour.Pos) :
    quadratic (B.color (C.tour.prev p)) + quadratic (B.color p) =
      quadratic (B.color (C.tour.prev p) + B.color p) + B.epsAt p := by
  rw [quadratic_add, epsAt, bracket_add_right, bracket_self, zero_add, add_assoc,
    F₂_add_self, add_zero]

/-- The quadratic moment over the gap incidences of every letter vanishes. -/
theorem sum_quadratic_incidences (ℓ : C.Letter) :
    ∑ o : (C.boundaryWord hCubic).Occurrence ℓ,
      (quadratic (B.color (C.tour.prev o.1)) + quadratic (B.color o.1)) = 0 := by
  have heven := B.color_even ℓ (1, 1)
  have hcast : ((Fintype.card {os : (C.boundaryWord hCubic).Occurrence ℓ × Fin 2 //
      (C.boundaryWord hCubic).incidentColor B.color os.1 os.2 = (1, 1)} : ℕ) : F₂) = 0 :=
    ZMod.natCast_eq_zero_iff_even.mpr heven
  rw [Fintype.card_subtype] at hcast
  have h1 : ∑ os : (C.boundaryWord hCubic).Occurrence ℓ × Fin 2,
      quadratic ((C.boundaryWord hCubic).incidentColor B.color os.1 os.2) = 0 := by
    simp_rw [quadratic_eq_indicator]
    rw [Finset.sum_boole]
    exact hcast
  rw [Fintype.sum_prod_type] at h1
  simpa [Fin.sum_univ_two, CyclicWord.Word.incidentColor] using h1

theorem diff_chordPos (x : C.Chord) (i : Fin 2) :
    B.color (C.tour.prev (C.chordPos hCubic x i)) + B.color (C.chordPos hCubic x i) =
      rotate (B.choice (Sum.inr x)) (f.color x.1) := by
  rw [B.diff, C.letterAt_chordPos, C.boundaryColor_chordPos]

private theorem F₂_eq_of_pair {q e₀ e₁ : F₂} (h : q + e₀ + (q + e₁) = 0) : e₀ = e₁ := by
  revert q e₀ e₁
  decide

/-- The two sides of a chord prescribe the same bit. -/
theorem epsAt_chordPos (x : C.Chord) :
    B.epsAt (C.chordPos hCubic x 0) = B.epsAt (C.chordPos hCubic x 1) := by
  have h := B.sum_quadratic_incidences (Sum.inr x)
  rw [C.sum_chord_occurrences hCubic x
    (fun p ↦ quadratic (B.color (C.tour.prev p)) + quadratic (B.color p))] at h
  rw [B.quadratic_pair, B.quadratic_pair, B.diff_chordPos, B.diff_chordPos] at h
  exact F₂_eq_of_pair h

/-- The required boundary parity at each vertex: one at outside vertices, corrected by the bits
of the pendant edges there, and zero on the circuit. -/
noncomputable def target (v : V) : F₂ :=
  if v ∈ C.vertices then 0
  else 1 + ∑ p : C.tour.Pos, if C.farVertex hCubic p = v then B.epsAt p else 0

theorem target_of_mem {v : V} (hv : v ∈ C.vertices) : B.target v = 0 := by
  simp [target, hv]

theorem target_of_not_mem {v : V} (hv : v ∉ C.vertices) :
    B.target v = 1 + ∑ p : C.tour.Pos, if C.farVertex hCubic p = v then B.epsAt p else 0 := by
  simp [target, hv]

private theorem sum_hub_indicator' (c : V → F₂) (w : V) (a : F₂) :
    ∑ v : C.Hub, c v.1 * (if w = v.1 then a else 0) =
      (if w ∈ C.vertices then 0 else c w) * a := by
  rw [← C.sum_hub_indicator c w, Finset.sum_mul]
  apply Fintype.sum_congr
  intro v
  by_cases h : w = v.1 <;> simp [h]

theorem sum_hub_target (c : V → F₂) :
    ∑ v, c v * B.target v =
      ∑ v : C.Hub, c v.1 +
        ∑ p : C.tour.Pos,
          (if C.IsPendant (C.boundaryHalfEdge hCubic p).1 then
            c (C.farEnd (C.boundaryHalfEdge hCubic p).1) else 0) * B.epsAt p := by
  have hsplit : ∑ v, c v * B.target v = ∑ v : C.Hub, c v.1 * B.target v.1 := by
    change _ = ∑ v : {v : V // v ∉ C.vertices}, c v.1 * B.target v.1
    rw [← Finset.sum_subtype (Finset.univ.filter fun v : V ↦ v ∉ C.vertices) (by simp)
      (fun v ↦ c v * B.target v)]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro v _ hv
    have hvC : v ∈ C.vertices := by
      by_contra h
      exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ v, h⟩)
    rw [B.target_of_mem hvC, mul_zero]
  rw [hsplit]
  have hexp : ∀ v : C.Hub, c v.1 * B.target v.1 =
      c v.1 + ∑ p, c v.1 * (if C.farVertex hCubic p = v.1 then B.epsAt p else 0) := by
    intro v
    rw [B.target_of_not_mem v.2, mul_add, mul_one, Finset.mul_sum]
  simp_rw [hexp]
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  congr 1
  apply Fintype.sum_congr
  intro p
  rw [sum_hub_indicator' c (C.farVertex hCubic p) (B.epsAt p)]
  congr 1
  by_cases hp : C.IsPendant (C.boundaryHalfEdge hCubic p).1
  · rw [if_pos hp, if_neg ((C.farVertex_not_mem_iff hCubic p).mpr hp),
      C.farVertex_eq_farEnd hCubic hp]
  · rw [if_neg hp]
    have hmem : C.farVertex hCubic p ∈ C.vertices := by
      by_contra h
      exact hp ((C.farVertex_not_mem_iff hCubic p).mp h)
    rw [if_pos hmem]

/-- The target parities are orthogonal to every function constant along internal edges. -/
theorem target_orthogonal (c : V → F₂)
    (hc : ∀ e, C.IsInternal e → c (H.endAt e 0) = c (H.endAt e 1)) :
    ∑ v, c v * B.target v = 0 := by
  rw [B.sum_hub_target c]
  have h1 : ∑ v : C.Hub, c v.1 =
      ∑ ℓ, C.letterLift c hc ℓ *
        ∑ o : (C.boundaryWord hCubic).Occurrence ℓ,
          quadratic (B.rotated (C.boundaryHalfEdge hCubic o.1).1) := by
    have h := C.sum_hub_weighted_letters hCubic c hc (fun e ↦ quadratic (B.rotated e))
    simp only [smul_eq_mul] at h
    rw [← h]
    apply Fintype.sum_congr
    intro v
    rw [B.sum_hub_quadratic_rotated v, mul_one]
  have h2 : ∑ p : C.tour.Pos,
      (if C.IsPendant (C.boundaryHalfEdge hCubic p).1 then
        c (C.farEnd (C.boundaryHalfEdge hCubic p).1) else 0) * B.epsAt p =
      ∑ ℓ, C.letterLift c hc ℓ *
        ∑ o : (C.boundaryWord hCubic).Occurrence ℓ, B.epsAt o.1 := by
    simp_rw [C.letterLift_letterAt hCubic c hc]
    rw [C.sum_over_letters hCubic (fun ℓ p ↦ C.letterLift c hc ℓ * B.epsAt p)]
    apply Fintype.sum_congr
    intro ℓ
    rw [Finset.mul_sum]
  rw [h1, h2, ← Finset.sum_add_distrib]
  apply Fintype.sum_eq_zero
  intro ℓ
  rw [← mul_add, ← Finset.sum_add_distrib]
  have h3 : ∑ o : (C.boundaryWord hCubic).Occurrence ℓ,
      (quadratic (B.rotated (C.boundaryHalfEdge hCubic o.1).1) + B.epsAt o.1) = 0 := by
    rw [← B.sum_quadratic_incidences ℓ]
    apply Fintype.sum_congr
    intro o
    rw [B.rotated_boundary, B.quadratic_pair]
  rw [h3, mul_zero]

/-- A binary T-join inside the internal edges realizing the target parities. -/
structure Join where
  edges : Finset E
  subset : edges ⊆ C.internalEdges
  boundary_eq : ∀ v, H.boundary edges v = B.target v

theorem exists_join : Nonempty B.Join := by
  obtain ⟨J, hJ, hbd⟩ := H.exists_boundary_eq C.internalEdges B.target (by
    intro c hc
    apply B.target_orthogonal c
    intro e he
    exact hc e ((C.mem_internalEdges e).mpr he))
  exact ⟨⟨J, hJ, hbd⟩⟩

/-- The boundary bit of an edge, read at its circuit side. -/
noncomputable def epsBnd (e : E) : F₂ :=
  if h : e ∉ C.edges ∧ ∃ i, H.endAt e i ∈ C.vertices then B.epsAt (C.posOf hCubic e h) else 0

/-- The bit of every edge: one on the T-join, and the boundary bit otherwise. -/
noncomputable def eps (R : B.Join) (e : E) : F₂ :=
  (if e ∈ R.edges then 1 else 0) + B.epsBnd e

theorem epsBnd_of_isInternal {e : E} (he : C.IsInternal e) : B.epsBnd e = 0 := by
  unfold epsBnd
  rw [dif_neg]
  rintro ⟨_, i, hi⟩
  exact he i hi

theorem epsBnd_of_mem {e : E} (he : e ∈ C.edges) : B.epsBnd e = 0 := by
  unfold epsBnd
  rw [dif_neg]
  rintro ⟨h, _⟩
  exact h he

theorem eps_boundary (R : B.Join) (p : C.tour.Pos) :
    B.eps R (C.boundaryHalfEdge hCubic p).1 = B.epsAt p := by
  have hne : (C.boundaryHalfEdge hCubic p).1 ∉ C.edges := C.boundaryHalfEdge_not_mem hCubic p
  have hon : H.endAt (C.boundaryHalfEdge hCubic p).1 (C.boundaryHalfEdge hCubic p).2 ∈
      C.vertices := by
    rw [C.boundaryHalfEdge_endpoint]
    exact C.vertexAt_mem_vertices p
  have hnotJ : (C.boundaryHalfEdge hCubic p).1 ∉ R.edges := by
    intro hJ
    exact ((C.mem_internalEdges _).mp (R.subset hJ)) _ hon
  have hcond : (C.boundaryHalfEdge hCubic p).1 ∉ C.edges ∧
      ∃ i, H.endAt (C.boundaryHalfEdge hCubic p).1 i ∈ C.vertices := ⟨hne, _, hon⟩
  unfold eps epsBnd
  rw [if_neg hnotJ, dif_pos hcond, zero_add]
  by_cases hp : C.IsPendant (C.boundaryHalfEdge hCubic p).1
  · rw [C.posOf_boundary hCubic p hp hcond]
  · have hall := C.chord_of_not_isPendant hCubic hp
    let x : C.Chord := ⟨(C.boundaryHalfEdge hCubic p).1, hne, hall⟩
    have hpos : C.posOf hCubic (C.boundaryHalfEdge hCubic p).1 hcond =
        C.chordPos hCubic x 0 :=
      C.posOf_chord hCubic x hcond
    rw [hpos]
    have hp' : ∀ s : Fin 2, C.boundaryHalfEdge hCubic p = (x.1, s) →
        B.epsAt (C.chordPos hCubic x 0) = B.epsAt p := by
      intro s hs
      have hps : p = C.chordPos hCubic x s := by
        unfold chordPos
        apply (C.positionBoundaryEquiv hCubic).injective
        rw [Equiv.apply_symm_apply]
        apply Subtype.ext
        exact hs
      rw [hps]
      rcases fin2_cases s with rfl | rfl
      · rfl
      · exact B.epsAt_chordPos x
    exact hp' (C.boundaryHalfEdge hCubic p).2 rfl

omit [DecidableEq E] in
private theorem edgeIncidence_pendant {e : E} (he : C.IsPendant e) {w : V}
    (hw : w ∉ C.vertices) :
    H.edgeIncidence w e = if C.farEnd e = w then 1 else 0 := by
  obtain ⟨hon, hoff⟩ := C.circuitSide_spec he
  have hne : H.endAt e (C.circuitSide e) ≠ w := fun h ↦ hw (h ▸ hon)
  unfold farEnd
  rcases fin2_cases (C.circuitSide e) with hs | hs
  · rw [hs] at hne ⊢
    rw [rev_zero_fin2]
    simp [edgeIncidence, hne, eq_comm]
  · rw [hs] at hne ⊢
    rw [rev_one_fin2]
    simp [edgeIncidence, hne, eq_comm]

omit [DecidableEq E] in
private theorem edgeIncidence_eq_zero_of_ends_mem {e : E}
    (hall : ∀ i, H.endAt e i ∈ C.vertices) {w : V} (hw : w ∉ C.vertices) :
    H.edgeIncidence w e = 0 := by
  have h0 : H.endAt e 0 ≠ w := fun h ↦ hw (h ▸ hall 0)
  have h1 : H.endAt e 1 ≠ w := fun h ↦ hw (h ▸ hall 1)
  simp [edgeIncidence, h0, h1]

theorem sum_incidence_epsBnd (w : C.Hub) :
    ∑ e, H.edgeIncidence w.1 e * B.epsBnd e =
      ∑ p : C.tour.Pos, if C.farVertex hCubic p = w.1 then B.epsAt p else 0 := by
  have hL : ∀ e, H.edgeIncidence w.1 e * B.epsBnd e =
      if C.IsPendant e then (if C.farEnd e = w.1 then B.epsBnd e else 0) else 0 := by
    intro e
    by_cases hp : C.IsPendant e
    · rw [if_pos hp, edgeIncidence_pendant hp w.2]
      by_cases hfar : C.farEnd e = w.1 <;> simp [hfar]
    · rw [if_neg hp]
      by_cases hmem : e ∈ C.edges
      · rw [B.epsBnd_of_mem hmem, mul_zero]
      · by_cases hout : ∃ i, H.endAt e i ∉ C.vertices
        · obtain ⟨i, hi⟩ := hout
          rcases C.isInternal_or_isPendant hi with hint | hpend
          · rw [B.epsBnd_of_isInternal hint, mul_zero]
          · exact absurd hpend hp
        · push Not at hout
          rw [edgeIncidence_eq_zero_of_ends_mem hout w.2, zero_mul]
  have hR : ∀ p : C.tour.Pos, (if C.farVertex hCubic p = w.1 then B.epsAt p else 0) =
      if C.IsPendant (C.boundaryHalfEdge hCubic p).1 then
        (if C.farEnd (C.boundaryHalfEdge hCubic p).1 = w.1 then
          B.epsBnd (C.boundaryHalfEdge hCubic p).1 else 0)
      else 0 := by
    intro p
    by_cases hp : C.IsPendant (C.boundaryHalfEdge hCubic p).1
    · rw [if_pos hp, C.farVertex_eq_farEnd hCubic hp]
      have hcond : (C.boundaryHalfEdge hCubic p).1 ∉ C.edges ∧
          ∃ i, H.endAt (C.boundaryHalfEdge hCubic p).1 i ∈ C.vertices :=
        ⟨C.boundaryHalfEdge_not_mem hCubic p, (C.boundaryHalfEdge hCubic p).2, by
          rw [C.boundaryHalfEdge_endpoint]
          exact C.vertexAt_mem_vertices p⟩
      have hb : B.epsBnd (C.boundaryHalfEdge hCubic p).1 = B.epsAt p := by
        unfold epsBnd
        rw [dif_pos hcond, C.posOf_boundary hCubic p hp hcond]
      rw [hb]
    · rw [if_neg hp]
      have hmem : C.farVertex hCubic p ∈ C.vertices := by
        by_contra h
        exact hp ((C.farVertex_not_mem_iff hCubic p).mp h)
      have hne : C.farVertex hCubic p ≠ w.1 := fun h ↦ w.2 (h ▸ hmem)
      rw [if_neg hne]
  simp_rw [hL, hR]
  exact (C.sum_pendant_positions hCubic
    (fun e ↦ if C.farEnd e = w.1 then B.epsBnd e else 0)).symm

/-- At every outside vertex the incident bits sum to one. -/
theorem sum_hub_eps (R : B.Join) (w : C.Hub) : ∑ h : H.halfEdgesAt w.1, B.eps R h.1.1 = 1 := by
  rw [H.sum_halfEdgesAt_eq_sum_incidence w.1 (B.eps R)]
  simp only [eps, smul_eq_mul, mul_add, Finset.sum_add_distrib]
  have hJ : ∑ e, H.edgeIncidence w.1 e * (if e ∈ R.edges then (1 : F₂) else 0) =
      B.target w.1 := by
    rw [← R.boundary_eq w.1]
    unfold boundary
    simp only [mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    simp
  rw [hJ, B.sum_incidence_epsBnd w, B.target_of_not_mem w.2, add_assoc, F₂_add_self, add_zero]

/-- The even subgraph associated with a colour. -/
noncomputable def lifted (R : B.Join) (a : Color) : Finset E :=
  Finset.univ.filter fun e ↦
    if he : e ∈ C.edges then B.color (C.tour.edge.symm ⟨e, he⟩) = a
    else bracket a (B.rotated e) = B.eps R e

theorem mem_lifted_circuit (R : B.Join) (a : Color) (p : C.tour.Pos) :
    (C.tour.edge p).1 ∈ B.lifted R a ↔ B.color p = a := by
  simp [lifted, (C.tour.edge p).2]

theorem mem_lifted_external (R : B.Join) (a : Color) {e : E} (he : e ∉ C.edges) :
    e ∈ B.lifted R a ↔ bracket a (B.rotated e) = B.eps R e := by
  simp [lifted, he]

private theorem circuit_parity (a x y : Color) (hxy : x ≠ y) :
    ((if y = a then 1 else 0) + (if x = a then 1 else 0) +
      (if bracket a (x + y) = bracket x (x + y) then 1 else 0) : F₂) = 0 := by
  revert a x y
  decide

private theorem F₂_indicator_eq (x y : F₂) : (if x = y then (1 : F₂) else 0) = 1 + x + y := by
  revert x y
  decide

theorem lifted_even (R : B.Join) (a : Color) : H.IsEvenEdgeSet (B.lifted R a) := by
  rw [H.isEvenEdgeSet_iff_sum_halfEdges]
  intro v
  by_cases hv : v ∈ C.vertices
  · obtain ⟨p, hp⟩ : ∃ p, C.tour.vertexAt p = v :=
      ⟨C.positionVertexEquiv.symm ⟨v, hv⟩,
        congrArg Subtype.val (C.positionVertexEquiv.apply_symm_apply ⟨v, hv⟩)⟩
    subst hp
    rw [C.sum_halfEdgesAt_circuit hCubic p (fun h ↦ if h.1 ∈ B.lifted R a then (1 : F₂) else 0)]
    simp only [B.mem_lifted_circuit R a, B.mem_lifted_external R a
      (C.boundaryHalfEdge_not_mem hCubic p), B.rotated_boundary p, B.eps_boundary R p, epsAt]
    exact circuit_parity a _ _ (B.transition_ne p)
  · let w : C.Hub := ⟨v, hv⟩
    have hmem : ∀ h : H.halfEdgesAt v, (if h.1.1 ∈ B.lifted R a then (1 : F₂) else 0) =
        1 + bracket a (B.rotated h.1.1) + B.eps R h.1.1 := by
      intro h
      simp only [B.mem_lifted_external R a (C.edge_not_mem_of_vertex_not_mem hv h)]
      exact F₂_indicator_eq _ _
    simp_rw [hmem]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_bracket_right]
    change (∑ _h : H.halfEdgesAt w.1, (1 : F₂)) +
      bracket a (∑ h : H.halfEdgesAt w.1, B.rotated h.1.1) +
      ∑ h : H.halfEdgesAt w.1, B.eps R h.1.1 = 0
    rw [C.sum_hub_one hCubic w, B.sum_hub_rotated w, bracket_zero_right, add_zero,
      B.sum_hub_eps R w]
    exact F₂_add_self 1

/-- The five even subgraphs: the circuit and the four lifted colour classes. -/
noncomputable def fiveSubgraphs (R : B.Join) : Option Color → H.EvenSubgraph
  | none => ⟨C.edges, OrdinaryCircuit.even H C.toOrdinaryCircuit⟩
  | some a => ⟨B.lifted R a, B.lifted_even R a⟩

theorem fiveSubgraphs_cover_twice (R : B.Join) (e : E) :
    (Finset.univ.filter fun k : Option Color ↦ e ∈ (B.fiveSubgraphs R k).edges).card = 2 := by
  by_cases he : e ∈ C.edges
  · let p := C.tour.edge.symm ⟨e, he⟩
    have hep : (C.tour.edge p).1 = e :=
      congrArg Subtype.val (C.tour.edge.apply_symm_apply ⟨e, he⟩)
    have heq : (Finset.univ.filter fun k : Option Color ↦ e ∈ (B.fiveSubgraphs R k).edges) =
        {none, some (B.color p)} := by
      ext k
      cases k with
      | none => simp [fiveSubgraphs, he]
      | some a =>
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
            Finset.mem_singleton, fiveSubgraphs, reduceCtorEq, false_or, Option.some.injEq]
          rw [← hep, B.mem_lifted_circuit R a p]
          exact eq_comm
    rw [heq]
    simp
  · have heq : (Finset.univ.filter fun k : Option Color ↦ e ∈ (B.fiveSubgraphs R k).edges) =
        (Finset.univ.filter fun a : Color ↦ bracket a (B.rotated e) = B.eps R e).map
          ⟨some, Option.some_injective _⟩ := by
      ext k
      cases k with
      | none => simp [fiveSubgraphs, he]
      | some a => simp [fiveSubgraphs, B.mem_lifted_external R a he]
    rw [heq, Finset.card_map]
    exact card_bracket_eq (B.rotated_ne_zero he) _

/-- The five-cycle double cover containing the circuit. -/
noncomputable def cycleDoubleCover (R : B.Join) : H.CycleDoubleCover 5 where
  cycles i := B.fiveSubgraphs R (fiveIndexEquiv i)
  coveredTwice := by
    intro e
    rw [← B.fiveSubgraphs_cover_twice R e]
    exact Finset.card_equiv fiveIndexEquiv (by simp)

theorem cycleDoubleCover_contains (R : B.Join) : (B.cycleDoubleCover R).Contains C.edges := by
  refine ⟨fiveIndexEquiv.symm none, ?_⟩
  change (B.fiveSubgraphs R (fiveIndexEquiv (fiveIndexEquiv.symm none))).edges = C.edges
  rw [Equiv.apply_symm_apply]
  rfl

end GapColoring

end Lift

/-- **Exact extension theorem.**  If the edges outside a circuit of a cubic endpoint multigraph
have a proper three-edge-colouring, then the graph has a five-cycle double cover one of whose
members is exactly the circuit. -/
theorem exists_fiveCycleDoubleCover_of_complementColoring (hCubic : ∀ v : V, H.degree v = 3)
    (f : C.ComplementColoring) : ∃ D : H.CycleDoubleCover 5, D.Contains C.edges := by
  obtain ⟨B⟩ := C.exists_gapColoring hCubic f
  obtain ⟨R⟩ := B.exists_join
  exact ⟨B.cycleDoubleCover R, B.cycleDoubleCover_contains R⟩

end TraversedCircuit

namespace OrdinaryCircuit

/-- The exact extension theorem in the paper's unbundled language: a proper three-edge-colouring
of the edges outside an ordinary circuit of a cubic endpoint multigraph yields a five-cycle
double cover containing that circuit as an entire member. -/
theorem exists_fiveCycleDoubleCover_of_coloring {H : LoopMultigraph V E} (C : H.OrdinaryCircuit)
    (hCubic : ∀ v : V, H.degree v = 3) (color : E → Color)
    (hnz : ∀ e, e ∉ C.edges → color e ≠ 0)
    (hinj : ∀ v, v ∉ H.edgeSupport C.edges →
      ∀ h₁ h₂ : H.halfEdgesAt v, color h₁.1.1 = color h₂.1.1 → h₁ = h₂) :
    ∃ D : H.CycleDoubleCover 5, D.Contains C.edges :=
  C.toTraversedCircuit.exists_fiveCycleDoubleCover_of_complementColoring hCubic
    ⟨color, hnz, hinj⟩

end OrdinaryCircuit

end LoopMultigraph
end GraphPuzzles
