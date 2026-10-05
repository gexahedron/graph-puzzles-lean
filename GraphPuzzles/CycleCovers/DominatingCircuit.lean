import GraphPuzzles.CycleCovers.DominatingCircuitCore
import GraphPuzzles.Circuits.CircuitEulerTour
import GraphPuzzles.Graph.LoopMultigraphIso

/-!
# Dominating circuits and bounded cycle double covers

This file formalizes Corollary 1.2 of the paper.  A cycle is represented by its (possibly empty)
binary-even edge set, as in the bounded-cover convention used in the statement of the corollary.
-/

namespace GraphPuzzles

namespace LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- A circuit together with a cyclic traversal of its edges.  The traversal is bundled data, not
an extra graph-theoretic hypothesis: it is the usual presentation of a finite circuit as a closed
trail. -/
structure TraversedCircuit (H : LoopMultigraph V E) extends H.OrdinaryCircuit where
  tour : toOrdinaryCircuit.restricted.EulerTour

/-- An ordinary circuit dominates when every edge has at least one end on the circuit. -/
def OrdinaryCircuit.Dominates {H : LoopMultigraph V E} (C : H.OrdinaryCircuit) : Prop :=
  ∀ e : E, ∃ i : Fin 2, H.endAt e i ∈ H.edgeSupport C.edges

namespace TraversedCircuit

variable {H : LoopMultigraph V E} (C : H.TraversedCircuit)

/-- The vertices met by the circuit. -/
abbrev vertices : Finset V := H.edgeSupport C.edges

/-- A circuit dominates when every edge has at least one end on the circuit. -/
def Dominates : Prop :=
  C.toOrdinaryCircuit.Dominates

end TraversedCircuit

/-- Half-edges at `v` whose underlying edge is not in the circuit. -/
def TraversedCircuit.externalHalfEdges {H : LoopMultigraph V E}
    (C : H.TraversedCircuit) (v : V) : Finset (E × Fin 2) :=
  ((Finset.univ \ C.edges) ×ˢ (Finset.univ : Finset (Fin 2))).filter
    fun h ↦ H.endAt h.1 h.2 = v

@[simp]
theorem TraversedCircuit.mem_externalHalfEdges {H : LoopMultigraph V E}
    (C : H.TraversedCircuit) (v : V) (h : E × Fin 2) :
    h ∈ C.externalHalfEdges v ↔ h.1 ∉ C.edges ∧ H.endAt h.1 h.2 = v := by
  simp [externalHalfEdges]

omit [DecidableEq E] in
private theorem degreeIn_univ (H : LoopMultigraph V E) (v : V) :
    H.degreeIn Finset.univ v = H.degree v := by
  simp only [degreeIn, degree, halfEdgesAt, vertex]
  rw [Fintype.card_subtype]
  congr 1

private theorem fin2_eq_rev_of_ne {i j : Fin 2} (h : i ≠ j) : j = Fin.rev i := by
  fin_cases i <;> fin_cases j <;> simp_all [Fin.rev]

private theorem degreeIn_compl_add (H : LoopMultigraph V E) (F : Finset E) (v : V) :
    H.degreeIn (Finset.univ \ F) v + H.degreeIn F v = H.degree v := by
  rw [← H.degreeIn_univ v]
  simp only [degreeIn]
  let A := ((Finset.univ : Finset E) ×ˢ (Finset.univ : Finset (Fin 2))).filter
    fun h ↦ H.endAt h.1 h.2 = v
  let B := (F ×ˢ (Finset.univ : Finset (Fin 2))).filter
    fun h ↦ H.endAt h.1 h.2 = v
  have hB : B ⊆ A := by
    intro h hh
    simp [A, B] at hh ⊢
    exact hh.2
  have hdiff :
      (((Finset.univ \ F) ×ˢ (Finset.univ : Finset (Fin 2))).filter
        fun h ↦ H.endAt h.1 h.2 = v) = A \ B := by
    ext h
    simp [A, B]
    constructor
    · rintro ⟨hnF, hv⟩
      exact ⟨hv, fun hF ↦ (hnF hF).elim⟩
    · rintro ⟨hv, hbad⟩
      exact ⟨fun hF ↦ hbad hF hv, hv⟩
  rw [hdiff]
  exact Finset.card_sdiff_add_card_eq_card hB

theorem TraversedCircuit.card_externalHalfEdges_eq_one {H : LoopMultigraph V E}
    (C : H.TraversedCircuit) (hCubic : ∀ v : V, H.degree v = 3) {v : V}
    (hv : v ∈ C.vertices) : (C.externalHalfEdges v).card = 1 := by
  change H.degreeIn (Finset.univ \ C.edges) v = 1
  have htotal := degreeIn_compl_add H C.edges v
  have hC : H.degreeIn C.edges v = 2 := C.twoRegular v hv
  rw [hCubic v, hC] at htotal
  omega

/-- The unique half-edge outside a cubic circuit at a circuit vertex. -/
noncomputable def TraversedCircuit.externalHalfEdge {H : LoopMultigraph V E}
    (C : H.TraversedCircuit) (hCubic : ∀ v : V, H.degree v = 3)
    (v : V) (hv : v ∈ C.vertices) : E × Fin 2 :=
  (Finset.card_eq_one.mp (C.card_externalHalfEdges_eq_one hCubic hv)).choose

theorem TraversedCircuit.externalHalfEdge_mem {H : LoopMultigraph V E}
    (C : H.TraversedCircuit) (hCubic : ∀ v : V, H.degree v = 3)
    (v : V) (hv : v ∈ C.vertices) :
    C.externalHalfEdge hCubic v hv ∈ C.externalHalfEdges v := by
  let h := Finset.card_eq_one.mp (C.card_externalHalfEdges_eq_one hCubic hv)
  change h.choose ∈ C.externalHalfEdges v
  have hm :
      (h.choose ∈ C.externalHalfEdges v) =
        (h.choose ∈ ({h.choose} : Finset (E × Fin 2))) :=
    congrArg (fun S : Finset (E × Fin 2) ↦ h.choose ∈ S) h.choose_spec
  exact Eq.mp hm.symm (by simp)

theorem TraversedCircuit.externalHalfEdge_unique {H : LoopMultigraph V E}
    (C : H.TraversedCircuit) (hCubic : ∀ v : V, H.degree v = 3)
    (v : V) (hv : v ∈ C.vertices) {h : E × Fin 2}
    (hh : h ∈ C.externalHalfEdges v) :
    h = C.externalHalfEdge hCubic v hv := by
  let hs := Finset.card_eq_one.mp (C.card_externalHalfEdges_eq_one hCubic hv)
  have heq : C.externalHalfEdges v = {C.externalHalfEdge hCubic v hv} := hs.choose_spec
  simpa [heq] using hh

namespace TraversedCircuit

variable {H : LoopMultigraph V E} (C : H.TraversedCircuit)
  (hCubic : ∀ v : V, H.degree v = 3) (hDom : C.Dominates)

/-- Exterior edges whose two ends lie on the circuit.  These are precisely the two-ended
components after deleting the circuit. -/
abbrev Chord :=
  {e : E // e ∉ C.edges ∧ ∀ i : Fin 2, H.endAt e i ∈ C.vertices}

/-- Vertices outside the circuit.  Domination makes each one the centre of a three-edge star. -/
abbrev Hub := {v : V // v ∉ C.vertices}

/-- Exterior half-edges based at circuit vertices. -/
abbrev BoundaryHalfEdge :=
  {x : E × Fin 2 // x.1 ∉ C.edges ∧ H.endAt x.1 x.2 ∈ C.vertices}

/-- Slots of deleted components: two per chord and three per off-circuit cubic vertex. -/
abbrev AmbientSlot := (C.Chord × Fin 2) ⊕ (C.Hub × Fin 3)

omit [DecidableEq E] in
private theorem restricted_degree (v : V) :
    C.toOrdinaryCircuit.restricted.degree v = H.degreeIn C.edges v := by
  change Fintype.card (C.toOrdinaryCircuit.restricted.halfEdgesAt v) =
    (((C.edges ×ˢ (Finset.univ : Finset (Fin 2))).filter
      fun h ↦ H.endAt h.1 h.2 = v).card)
  change Fintype.card
      {h : {e : E // e ∈ C.edges} × Fin 2 // H.endAt h.1.1 h.2 = v} =
    (((C.edges ×ˢ (Finset.univ : Finset (Fin 2))).filter
      fun h ↦ H.endAt h.1 h.2 = v).card)
  rw [Fintype.card_subtype]
  change
    (((Finset.univ : Finset ({e : E // e ∈ C.edges} × Fin 2)).filter
      fun h ↦ H.endAt h.1.1 h.2 = v).card) =
        (((C.edges ×ˢ (Finset.univ : Finset (Fin 2))).filter
          fun h ↦ H.endAt h.1 h.2 = v).card)
  refine Finset.card_bij (fun h _ ↦ (h.1.1, h.2)) ?_ ?_ ?_
  · intro h hh
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨h.1.2, Finset.mem_univ _⟩,
        (Finset.mem_filter.mp hh).2⟩
  · intro h₁ hh₁ h₂ hh₂ heq
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun z : E × Fin 2 ↦ z.1) heq
    · exact congrArg (fun z : E × Fin 2 ↦ z.2) heq
  · intro h hh
    refine ⟨(⟨h.1, (Finset.mem_product.mp (Finset.mem_filter.mp hh).1).1⟩, h.2), ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hh).2⟩

omit [DecidableEq E] in
theorem occurrence_card_eq_one {v : V} (hv : v ∈ C.vertices) :
    Fintype.card (C.tour.Occurrence v) = 1 := by
  have hd := C.tour.degree_eq_two_mul_card_occurrence v
  rw [C.restricted_degree, C.twoRegular v hv] at hd
  omega

omit [DecidableEq E] in
theorem vertexAt_mem_vertices (p : C.tour.Pos) : C.tour.vertexAt p ∈ C.vertices := by
  apply H.mem_edgeSupport_iff.mpr
  exact ⟨(C.tour.edge p).1, (C.tour.edge p).2, C.tour.depart p, rfl⟩

/-- Circuit positions are exactly circuit vertices: a connected 2-regular circuit is visited once
at each supported vertex. -/
noncomputable def positionVertexEquiv : C.tour.Pos ≃ {v : V // v ∈ C.vertices} :=
  Equiv.ofBijective
    (fun p ↦ ⟨C.tour.vertexAt p, C.vertexAt_mem_vertices p⟩)
    ⟨by
      intro p q hpq
      let op : C.tour.Occurrence (C.tour.vertexAt p) := ⟨p, rfl⟩
      let oq : C.tour.Occurrence (C.tour.vertexAt p) := ⟨q, by
        exact congrArg Subtype.val hpq |>.symm⟩
      have hcard := C.occurrence_card_eq_one (C.vertexAt_mem_vertices p)
      have hle : Fintype.card (C.tour.Occurrence (C.tour.vertexAt p)) ≤ 1 := by omega
      haveI : Subsingleton (C.tour.Occurrence (C.tour.vertexAt p)) :=
        ⟨Fintype.card_le_one_iff.mp hle⟩
      exact congrArg Subtype.val (Subsingleton.elim op oq),
    by
      rintro ⟨v, hv⟩
      have hcard := C.occurrence_card_eq_one hv
      have hpos : 0 < Fintype.card (C.tour.Occurrence v) := by omega
      let o : C.tour.Occurrence v := Classical.choice (Fintype.card_pos_iff.mp hpos)
      refine ⟨o.1, ?_⟩
      apply Subtype.ext
      exact o.2⟩

omit [DecidableEq E] in
@[simp]
theorem positionVertexEquiv_apply_val (p : C.tour.Pos) :
    (C.positionVertexEquiv p).1 = C.tour.vertexAt p := rfl

/-- An arbitrary but fixed numbering of the three half-edges at an off-circuit cubic vertex. -/
noncomputable def hubEnds (h : C.Hub) : Fin 3 ≃ H.halfEdgesAt h.1 :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin]
    exact (hCubic h.1).symm)

omit [DecidableEq E] in
theorem hubEnd_edge_not_mem (h : C.Hub) (j : Fin 3) :
    (C.hubEnds hCubic h j).1.1 ∉ C.edges := by
  intro he
  apply h.2
  apply H.mem_edgeSupport_iff.mpr
  exact ⟨_, he, (C.hubEnds hCubic h j).1.2,
    (C.hubEnds hCubic h j).2⟩

omit [DecidableEq E] in
theorem hubEnd_opposite_mem_vertices (dom : C.Dominates) (h : C.Hub) (j : Fin 3) :
    H.endAt (C.hubEnds hCubic h j).1.1
      (Fin.rev (C.hubEnds hCubic h j).1.2) ∈ C.vertices := by
  obtain ⟨i, hi⟩ := dom (C.hubEnds hCubic h j).1.1
  have hne : i ≠ (C.hubEnds hCubic h j).1.2 := by
    intro heq
    subst i
    apply h.2
    rw [← (C.hubEnds hCubic h j).2]
    exact hi
  have hrev : i = Fin.rev (C.hubEnds hCubic h j).1.2 := by
    exact fin2_eq_rev_of_ne (Ne.symm hne)
  simpa [hrev] using hi

/-- The unique exterior half-edge at a circuit position. -/
noncomputable def boundaryAtPosition (p : C.tour.Pos) : C.BoundaryHalfEdge := by
  let v : V := C.tour.vertexAt p
  let hv : v ∈ C.vertices := C.vertexAt_mem_vertices p
  let x := C.externalHalfEdge hCubic v hv
  have hx := (C.mem_externalHalfEdges v x).mp (C.externalHalfEdge_mem hCubic v hv)
  exact ⟨x, hx.1, hx.2 ▸ hv⟩

theorem boundaryAtPosition_endpoint (p : C.tour.Pos) :
    H.endAt (C.boundaryAtPosition hCubic p).1.1
      (C.boundaryAtPosition hCubic p).1.2 = C.tour.vertexAt p := by
  simp only [boundaryAtPosition]
  exact (C.mem_externalHalfEdges _ _).mp
    (C.externalHalfEdge_mem hCubic _ (C.vertexAt_mem_vertices p)) |>.2

/-- Circuit positions are equivalent to the exterior half-edges based on the circuit. -/
noncomputable def positionBoundaryEquiv : C.tour.Pos ≃ C.BoundaryHalfEdge where
  toFun := C.boundaryAtPosition hCubic
  invFun x := C.positionVertexEquiv.symm ⟨H.endAt x.1.1 x.1.2, x.2.2⟩
  left_inv p := by
    apply C.positionVertexEquiv.injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    exact C.boundaryAtPosition_endpoint hCubic p
  right_inv x := by
    let q := C.positionVertexEquiv.symm ⟨H.endAt x.1.1 x.1.2, x.2.2⟩
    change C.boundaryAtPosition hCubic q = x
    apply Subtype.ext
    have hq : C.tour.vertexAt q = H.endAt x.1.1 x.1.2 := by
      exact congrArg Subtype.val (C.positionVertexEquiv.apply_symm_apply
        ⟨H.endAt x.1.1 x.1.2, x.2.2⟩)
    change C.externalHalfEdge hCubic (C.tour.vertexAt q) (C.vertexAt_mem_vertices q) = x.1
    symm
    apply C.externalHalfEdge_unique hCubic
    simp [x.2.1, hq]

/-- Turn a component slot into its exterior half-edge based on the circuit. -/
noncomputable def slotToBoundary : C.AmbientSlot → C.BoundaryHalfEdge
  | Sum.inl (c, j) => ⟨(c.1, j), c.2.1, c.2.2 j⟩
  | Sum.inr (h, j) =>
      let x := C.hubEnds hCubic h j
      ⟨(x.1.1, Fin.rev x.1.2), C.hubEnd_edge_not_mem hCubic h j,
        C.hubEnd_opposite_mem_vertices hCubic hDom h j⟩

/-- Classify a boundary half-edge as a chord end or as a spoke at an off-circuit hub. -/
noncomputable def boundaryToSlot (x : C.BoundaryHalfEdge) : C.AmbientSlot := by
  let w := H.endAt x.1.1 (Fin.rev x.1.2)
  if hw : w ∈ C.vertices then
    let c : C.Chord := ⟨x.1.1, x.2.1, by
      intro i
      by_cases hi : i = x.1.2
      · simpa [hi] using x.2.2
      · have hir : i = Fin.rev x.1.2 := fin2_eq_rev_of_ne (Ne.symm hi)
        simpa [w, hir] using hw⟩
    exact Sum.inl (c, x.1.2)
  else
    let h : C.Hub := ⟨w, hw⟩
    let y : H.halfEdgesAt h.1 := ⟨(x.1.1, Fin.rev x.1.2), rfl⟩
    exact Sum.inr (h, (C.hubEnds hCubic h).symm y)

/-- Component slots and circuit-based exterior half-edges are the same finite data. -/
noncomputable def slotBoundaryEquiv : C.AmbientSlot ≃ C.BoundaryHalfEdge :=
  Equiv.ofBijective (C.slotToBoundary hCubic hDom) ⟨by
    intro a b hab
    have hv : (C.slotToBoundary hCubic hDom a).1 =
        (C.slotToBoundary hCubic hDom b).1 :=
      congrArg (fun z : C.BoundaryHalfEdge ↦ z.1) hab
    cases a with
    | inl cj =>
        rcases cj with ⟨c, i⟩
        cases b with
        | inl c'j =>
            rcases c'j with ⟨c', j⟩
            have he : c.1 = c'.1 := congrArg Prod.fst hv
            have hi : i = j := congrArg Prod.snd hv
            have hc : c = c' := Subtype.ext he
            subst c'
            subst j
            rfl
        | inr hj =>
            rcases hj with ⟨h, j⟩
            exfalso
            let x := C.hubEnds hCubic h j
            have he : c.1 = x.1.1 := congrArg Prod.fst hv
            apply h.2
            rw [← x.2]
            change H.endAt x.1.1 x.1.2 ∈ C.vertices
            rw [← he]
            exact c.2.2 x.1.2
    | inr hi =>
        rcases hi with ⟨h, i⟩
        cases b with
        | inl cj =>
            rcases cj with ⟨c, j⟩
            exfalso
            let x := C.hubEnds hCubic h i
            have he : x.1.1 = c.1 := congrArg Prod.fst hv
            apply h.2
            rw [← x.2]
            change H.endAt x.1.1 x.1.2 ∈ C.vertices
            rw [he]
            exact c.2.2 x.1.2
        | inr h'j =>
            rcases h'j with ⟨h', j⟩
            let x := C.hubEnds hCubic h i
            let y := C.hubEnds hCubic h' j
            have hv' : (x.1.1, Fin.rev x.1.2) =
                (y.1.1, Fin.rev y.1.2) := by
              simpa [slotToBoundary, x, y] using hv
            have hp : x.1.1 = y.1.1 ∧
                Fin.rev x.1.2 = Fin.rev y.1.2 := by
              simpa only [Prod.mk.injEq] using hv'
            have he : x.1.1 = y.1.1 := hp.1
            have hrev : Fin.rev x.1.2 = Fin.rev y.1.2 := hp.2
            have hs : x.1.2 = y.1.2 := by
              calc
                x.1.2 = Fin.rev (Fin.rev x.1.2) := by simp
                _ = Fin.rev (Fin.rev y.1.2) := congrArg Fin.rev hrev
                _ = y.1.2 := by simp
            have hh : h = h' := by
              apply Subtype.ext
              calc
                h.1 = H.endAt x.1.1 x.1.2 := x.2.symm
                _ = H.endAt y.1.1 y.1.2 := by rw [he, hs]
                _ = h'.1 := y.2
            subst h'
            have hij : i = j := by
              apply (C.hubEnds hCubic h).injective
              apply Subtype.ext
              exact Prod.ext he hs
            subst j
            rfl,
    by
      intro x
      let w := H.endAt x.1.1 (Fin.rev x.1.2)
      by_cases hw : w ∈ C.vertices
      · let c : C.Chord := ⟨x.1.1, x.2.1, by
          intro i
          by_cases hi : i = x.1.2
          · simpa [hi] using x.2.2
          · have hir : i = Fin.rev x.1.2 := fin2_eq_rev_of_ne (Ne.symm hi)
            simpa [w, hir] using hw⟩
        refine ⟨Sum.inl (c, x.1.2), ?_⟩
        apply Subtype.ext
        rfl
      · let h : C.Hub := ⟨w, hw⟩
        let y : H.halfEdgesAt h.1 := ⟨(x.1.1, Fin.rev x.1.2), rfl⟩
        let j : Fin 3 := (C.hubEnds hCubic h).symm y
        refine ⟨Sum.inr (h, j), ?_⟩
        apply Subtype.ext
        change ((C.hubEnds hCubic h j).1.1,
          Fin.rev (C.hubEnds hCubic h j).1.2) = x.1
        rw [show C.hubEnds hCubic h j = y by
          exact (C.hubEnds hCubic h).apply_symm_apply y]
        simp [y]⟩

/-- The aligned component slot at every circuit position. -/
noncomputable def slotPositionEquiv : C.AmbientSlot ≃ C.tour.Pos :=
  (C.slotBoundaryEquiv hCubic hDom).trans (C.positionBoundaryEquiv hCubic).symm

/-- Forget the numbered slot and retain its deleted component. -/
def slotComponent : C.AmbientSlot → C.Chord ⊕ C.Hub
  | Sum.inl (c, _) => Sum.inl c
  | Sum.inr (h, _) => Sum.inr h

/-- The contracted Euler word: its letter at a circuit vertex is the component of the deleted
exterior edge incident with that vertex. -/
noncomputable def contractedWord : CyclicWord.Word (V := C.Chord ⊕ C.Hub) where
  n := C.tour.n
  letter p := C.slotComponent ((C.slotPositionEquiv hCubic hDom).symm p)

/-- The two aligned occurrences of a chord component. -/
noncomputable def chordOccurrence (c : C.Chord) :
    Fin 2 ≃ (C.contractedWord hCubic hDom).Occurrence (Sum.inl c) :=
  Equiv.ofBijective
    (fun j ↦ ⟨C.slotPositionEquiv hCubic hDom (Sum.inl (c, j)), by
      simp [contractedWord, slotComponent]⟩)
    ⟨by
      intro i j hij
      have hp :
          C.slotPositionEquiv hCubic hDom (Sum.inl (c, i)) =
            C.slotPositionEquiv hCubic hDom (Sum.inl (c, j)) :=
        congrArg Subtype.val hij
      have hs : (Sum.inl (c, i) : C.AmbientSlot) = Sum.inl (c, j) :=
        (C.slotPositionEquiv hCubic hDom).injective hp
      exact congrArg Prod.snd (Sum.inl.inj hs),
    by
      rintro ⟨p, hp⟩
      let s := (C.slotPositionEquiv hCubic hDom).symm p
      have hspos : C.slotPositionEquiv hCubic hDom s = p := by
        simp [s]
      have hcomponent : C.slotComponent s = Sum.inl c := by
        simpa [contractedWord, s] using hp
      cases hs : s with
      | inl cj =>
          rcases cj with ⟨c', j⟩
          have hc : c' = c := by
            have hsum : (Sum.inl c' : C.Chord ⊕ C.Hub) = Sum.inl c := by
              simpa [slotComponent, hs] using hcomponent
            exact Sum.inl.inj hsum
          subst c'
          refine ⟨j, Subtype.ext ?_⟩
          apply Fin.ext
          have hval := congrArg Fin.val hspos
          simpa [hs] using hval
      | inr hj =>
          rcases hj with ⟨h, j⟩
          have hbad : (Sum.inr h : C.Chord ⊕ C.Hub) = Sum.inl c := by
            simp [slotComponent, hs] at hcomponent
          cases hbad⟩

/-- The three aligned occurrences of an off-circuit star component. -/
noncomputable def hubOccurrence (h : C.Hub) :
    Fin 3 ≃ (C.contractedWord hCubic hDom).Occurrence (Sum.inr h) :=
  Equiv.ofBijective
    (fun j ↦ ⟨C.slotPositionEquiv hCubic hDom (Sum.inr (h, j)), by
      simp [contractedWord, slotComponent]⟩)
    ⟨by
      intro i j hij
      have hp :
          C.slotPositionEquiv hCubic hDom (Sum.inr (h, i)) =
            C.slotPositionEquiv hCubic hDom (Sum.inr (h, j)) :=
        congrArg Subtype.val hij
      have hs : (Sum.inr (h, i) : C.AmbientSlot) = Sum.inr (h, j) :=
        (C.slotPositionEquiv hCubic hDom).injective hp
      exact congrArg Prod.snd (Sum.inr.inj hs),
    by
      rintro ⟨p, hp⟩
      let s := (C.slotPositionEquiv hCubic hDom).symm p
      have hspos : C.slotPositionEquiv hCubic hDom s = p := by
        simp [s]
      have hcomponent : C.slotComponent s = Sum.inr h := by
        simpa [contractedWord, s] using hp
      cases hs : s with
      | inl cj =>
          rcases cj with ⟨c, j⟩
          have hbad : (Sum.inl c : C.Chord ⊕ C.Hub) = Sum.inr h := by
            simp [slotComponent, hs] at hcomponent
          cases hbad
      | inr hj =>
          rcases hj with ⟨h', j⟩
          have hh : h' = h := by
            have hsum : (Sum.inr h' : C.Chord ⊕ C.Hub) = Sum.inr h := by
              simpa [slotComponent, hs] using hcomponent
            exact Sum.inr.inj hsum
          subst h'
          refine ⟨j, Subtype.ext ?_⟩
          apply Fin.ext
          have hval := congrArg Fin.val hspos
          simpa [hs] using hval⟩

/-- The explicit chord/star normal form extracted from a cubic dominating circuit. -/
noncomputable def normalForm : DominatingCircuitCore.NormalForm C.Chord C.Hub where
  word := C.contractedWord hCubic hDom
  chordOccurrence := C.chordOccurrence hCubic hDom
  hubOccurrence := C.hubOccurrence hCubic hDom

@[simp]
theorem normalForm_chordPos (c : C.Chord) (j : Fin 2) :
    (C.normalForm hCubic hDom).chordPos c j =
      C.slotPositionEquiv hCubic hDom (Sum.inl (c, j)) := by
  change (C.chordOccurrence hCubic hDom c j).1 =
    C.slotPositionEquiv hCubic hDom (Sum.inl (c, j))
  rfl

@[simp]
theorem normalForm_hubPos (h : C.Hub) (j : Fin 3) :
    (C.normalForm hCubic hDom).hubPos h j =
      C.slotPositionEquiv hCubic hDom (Sum.inr (h, j)) := by
  change (C.hubOccurrence hCubic hDom h j).1 =
    C.slotPositionEquiv hCubic hDom (Sum.inr (h, j))
  rfl

theorem positionVertex_chordSlot (c : C.Chord) (j : Fin 2) :
    (C.positionVertexEquiv
      (C.slotPositionEquiv hCubic hDom (Sum.inl (c, j)))).1 = H.endAt c.1 j := by
  simp [slotPositionEquiv, slotBoundaryEquiv, slotToBoundary, positionBoundaryEquiv]

theorem positionVertex_hubSlot (h : C.Hub) (j : Fin 3) :
    (C.positionVertexEquiv
      (C.slotPositionEquiv hCubic hDom (Sum.inr (h, j)))).1 =
      H.endAt (C.hubEnds hCubic h j).1.1
        (Fin.rev (C.hubEnds hCubic h j).1.2) := by
  simp [slotPositionEquiv, slotBoundaryEquiv, slotToBoundary, positionBoundaryEquiv]

end TraversedCircuit

namespace TraversedCircuit

variable {H : LoopMultigraph V E} (C : H.TraversedCircuit)
  (hCubic : ∀ v : V, H.degree v = 3) (hDom : C.Dominates)

abbrev NormalExternalEdge :=
  DominatingCircuitCore.NormalForm.ExternalEdge C.Chord C.Hub

/-- Relabel a normal-form chord or spoke by its original edge of `H`. -/
noncomputable def externalEdgeToComplement :
    C.NormalExternalEdge → {e : E // e ∉ C.edges}
  | Sum.inl c => ⟨c.1, c.2.1⟩
  | Sum.inr (h, j) =>
      ⟨(C.hubEnds hCubic h j).1.1, C.hubEnd_edge_not_mem hCubic h j⟩

omit [DecidableEq E] in
theorem externalEdgeToComplement_injective (dom : C.Dominates) :
    Function.Injective (C.externalEdgeToComplement hCubic) := by
  intro a b hab
  cases a with
  | inl c =>
      cases b with
      | inl c' =>
          have he : c.1 = c'.1 :=
            congrArg (fun z : {e : E // e ∉ C.edges} ↦ z.1) hab
          have hc : c = c' := Subtype.ext he
          subst c'
          rfl
      | inr hj =>
          rcases hj with ⟨h, j⟩
          exfalso
          let x := C.hubEnds hCubic h j
          have he : c.1 = x.1.1 :=
            congrArg (fun z : {e : E // e ∉ C.edges} ↦ z.1) hab
          apply h.2
          rw [← x.2]
          change H.endAt x.1.1 x.1.2 ∈ C.vertices
          rw [← he]
          exact c.2.2 x.1.2
  | inr hj =>
      rcases hj with ⟨h, j⟩
      cases b with
      | inl c =>
          exfalso
          let x := C.hubEnds hCubic h j
          have he : x.1.1 = c.1 :=
            congrArg (fun z : {e : E // e ∉ C.edges} ↦ z.1) hab
          apply h.2
          rw [← x.2]
          change H.endAt x.1.1 x.1.2 ∈ C.vertices
          rw [he]
          exact c.2.2 x.1.2
      | inr h'j' =>
          rcases h'j' with ⟨h', j'⟩
          let x := C.hubEnds hCubic h j
          let y := C.hubEnds hCubic h' j'
          have he : x.1.1 = y.1.1 :=
            congrArg (fun z : {e : E // e ∉ C.edges} ↦ z.1) hab
          have hs : x.1.2 = y.1.2 := by
            by_contra hne
            have hrev : y.1.2 = Fin.rev x.1.2 := by
              exact fin2_eq_rev_of_ne hne
            apply h'.2
            rw [← y.2]
            change H.endAt y.1.1 y.1.2 ∈ C.vertices
            rw [← he, hrev]
            exact C.hubEnd_opposite_mem_vertices hCubic dom h j
          have hh : h = h' := by
            apply Subtype.ext
            calc
              h.1 = H.endAt x.1.1 x.1.2 := x.2.symm
              _ = H.endAt y.1.1 y.1.2 := by rw [he, hs]
              _ = h'.1 := y.2
          subst h'
          have hj : j = j' := by
            apply (C.hubEnds hCubic h).injective
            apply Subtype.ext
            exact Prod.ext he hs
          subst j'
          rfl

omit [DecidableEq E] in
theorem externalEdgeToComplement_surjective (dom : C.Dominates) :
    Function.Surjective (C.externalEdgeToComplement hCubic) := by
  rintro ⟨e, he⟩
  obtain ⟨i, hi⟩ := dom e
  by_cases ho : H.endAt e (Fin.rev i) ∈ C.vertices
  · let c : C.Chord := ⟨e, he, by
      intro j
      fin_cases i <;> fin_cases j <;> simp_all [Fin.rev]⟩
    refine ⟨Sum.inl c, ?_⟩
    apply Subtype.ext
    rfl
  · let h : C.Hub := ⟨H.endAt e (Fin.rev i), ho⟩
    let y : H.halfEdgesAt h.1 := ⟨(e, Fin.rev i), rfl⟩
    let j : Fin 3 := (C.hubEnds hCubic h).symm y
    refine ⟨Sum.inr (h, j), ?_⟩
    apply Subtype.ext
    change (C.hubEnds hCubic h j).1.1 = e
    rw [show C.hubEnds hCubic h j = y by
      exact (C.hubEnds hCubic h).apply_symm_apply y]

/-- The normal-form exterior edges are exactly the edges outside the given circuit. -/
noncomputable def externalEdgeEquiv :
    C.NormalExternalEdge ≃ {e : E // e ∉ C.edges} :=
  Equiv.ofBijective (C.externalEdgeToComplement hCubic)
    ⟨C.externalEdgeToComplement_injective hCubic hDom,
      C.externalEdgeToComplement_surjective hCubic hDom⟩

/-- Relabel normal-form vertices by their original vertices. -/
noncomputable def normalVertexEquiv :
    (C.normalForm hCubic hDom).Vertex ≃ V :=
  (Equiv.sumCongr C.positionVertexEquiv (Equiv.refl C.Hub)).trans
    (Equiv.sumCompl fun v : V ↦ v ∈ C.vertices)

/-- Relabel normal-form edges by the original circuit and exterior edges. -/
noncomputable def normalEdgeEquiv :
    (C.normalForm hCubic hDom).Edge ≃ E :=
  (Equiv.sumCongr C.tour.edge (C.externalEdgeEquiv hCubic hDom)).trans
    (Equiv.sumCompl fun e : E ↦ e ∈ C.edges)

@[simp]
theorem normalVertexEquiv_circuit (p : C.tour.Pos) :
    C.normalVertexEquiv hCubic hDom (Sum.inl p) = C.tour.vertexAt p := rfl

@[simp]
theorem normalVertexEquiv_hub (h : C.Hub) :
    C.normalVertexEquiv hCubic hDom (Sum.inr h) = h.1 := rfl

@[simp]
theorem normalEdgeEquiv_circuit (p : C.tour.Pos) :
    C.normalEdgeEquiv hCubic hDom
      ((C.normalForm hCubic hDom).circuitEdge p) = (C.tour.edge p).1 := rfl

@[simp]
theorem normalEdgeEquiv_chord (c : C.Chord) :
    C.normalEdgeEquiv hCubic hDom
      ((C.normalForm hCubic hDom).chordEdge c) = c.1 := rfl

@[simp]
theorem normalEdgeEquiv_spoke (h : C.Hub) (j : Fin 3) :
    C.normalEdgeEquiv hCubic hDom
      ((C.normalForm hCubic hDom).spokeEdge h j) =
      (C.hubEnds hCubic h j).1.1 := rfl

/-- The end-numbering equivalence that sends `0` to a chosen side. -/
def orientEnds (d : Fin 2) : Fin 2 ≃ Fin 2 where
  toFun i := if i = 0 then d else Fin.rev d
  invFun i := if i = 0 then d else Fin.rev d
  left_inv i := by fin_cases i <;> fin_cases d <;> rfl
  right_inv i := by fin_cases i <;> fin_cases d <;> rfl

@[simp]
theorem orientEnds_zero (d : Fin 2) : orientEnds d 0 = d := rfl

@[simp]
theorem orientEnds_one (d : Fin 2) : orientEnds d 1 = Fin.rev d := by
  fin_cases d <;> rfl

/-- Per-edge orientations matching the normal-form end numbers to those of the original graph. -/
noncomputable def normalEndEquiv
    (e : (C.normalForm hCubic hDom).Edge) : Fin 2 ≃ Fin 2 :=
  match e with
  | Sum.inl p => orientEnds (C.tour.depart p)
  | Sum.inr (Sum.inl _) => Equiv.refl _
  | Sum.inr (Sum.inr (h, j)) =>
      orientEnds (Fin.rev (C.hubEnds hCubic h j).1.2)

/-- The explicit normal form is isomorphic to the original cubic graph, including the numbered
ends of every labelled edge. -/
noncomputable def normalEndpointIso :
    EndpointIso (C.normalForm hCubic hDom).graph H where
  vertexEquiv := C.normalVertexEquiv hCubic hDom
  edgeEquiv := C.normalEdgeEquiv hCubic hDom
  endEquiv := C.normalEndEquiv hCubic hDom
  map_endAt := by
    intro e i
    cases e with
    | inl p =>
        fin_cases i
        · rfl
        · change C.tour.vertexAt (finRotate (C.tour.n + 1) p) =
            H.endAt (C.tour.edge p).1 (Fin.rev (C.tour.depart p))
          exact (C.tour.continuous p).symm
    | inr x =>
        cases x with
        | inl c =>
            fin_cases i
            · change (C.positionVertexEquiv
                  ((C.normalForm hCubic hDom).chordPos c 0)).1 = H.endAt c.1 0
              rw [C.normalForm_chordPos hCubic hDom]
              exact C.positionVertex_chordSlot hCubic hDom c 0
            · change (C.positionVertexEquiv
                  ((C.normalForm hCubic hDom).chordPos c 1)).1 = H.endAt c.1 1
              rw [C.normalForm_chordPos hCubic hDom]
              exact C.positionVertex_chordSlot hCubic hDom c 1
        | inr hj =>
            rcases hj with ⟨h, j⟩
            fin_cases i
            · change (C.positionVertexEquiv
                  ((C.normalForm hCubic hDom).hubPos h j)).1 =
                H.endAt (C.hubEnds hCubic h j).1.1
                  (Fin.rev (C.hubEnds hCubic h j).1.2)
              rw [C.normalForm_hubPos hCubic hDom]
              exact C.positionVertex_hubSlot hCubic hDom h j
            · have hmap :
                  C.normalEdgeEquiv hCubic hDom (Sum.inr (Sum.inr (h, j))) =
                    (C.hubEnds hCubic h j).1.1 := by
                change C.normalEdgeEquiv hCubic hDom
                  ((C.normalForm hCubic hDom).spokeEdge h j) =
                    (C.hubEnds hCubic h j).1.1
                exact C.normalEdgeEquiv_spoke hCubic hDom h j
              simpa [DominatingCircuitCore.NormalForm.graph, normalEndEquiv, hmap,
                LoopMultigraph.vertex] using
                (C.hubEnds hCubic h j).2.symm

/-- Under the normal-form isomorphism, the distinguished circuit edge set is exactly `C.edges`. -/
theorem map_normalCircuitEdges :
    (C.normalEndpointIso hCubic hDom).mapEdges
      (C.normalForm hCubic hDom).circuitEdges = C.edges := by
  ext e
  constructor
  · intro he
    rw [EndpointIso.mapEdges, Finset.mem_map] at he
    obtain ⟨d, hd, hde⟩ := he
    cases d with
    | inl p =>
        have hep : (C.tour.edge p).1 = e := by
          change C.normalEdgeEquiv hCubic hDom (Sum.inl p) = e at hde
          have hmap : C.normalEdgeEquiv hCubic hDom (Sum.inl p) =
              (C.tour.edge p).1 := by
            change C.normalEdgeEquiv hCubic hDom
              ((C.normalForm hCubic hDom).circuitEdge p) = (C.tour.edge p).1
            exact C.normalEdgeEquiv_circuit hCubic hDom p
          exact hmap.symm.trans hde
        rw [← hep]
        exact (C.tour.edge p).2
    | inr x =>
        simp [DominatingCircuitCore.NormalForm.circuitEdges] at hd
  · intro he
    let ce : {e : E // e ∈ C.edges} := ⟨e, he⟩
    let p : C.tour.Pos := C.tour.edge.symm ce
    apply Finset.mem_map.mpr
    refine ⟨(C.normalForm hCubic hDom).circuitEdge p,
      (C.normalForm hCubic hDom).circuitEdge_mem_circuitEdges p, ?_⟩
    change (C.tour.edge p).1 = e
    exact congrArg Subtype.val (C.tour.edge.apply_symm_apply ce)

end TraversedCircuit

/-- A cycle in the bounded-cover sense: a possibly disconnected even subgraph. -/
structure EvenSubgraph (H : LoopMultigraph V E) where
  edges : Finset E
  even : H.IsEvenEdgeSet edges

/-- A `k`-cycle double cover, padded by empty cycles if fewer than `k` are needed. -/
structure CycleDoubleCover (H : LoopMultigraph V E) (k : ℕ) where
  cycles : Fin k → H.EvenSubgraph
  coveredTwice : ∀ e : E, (Finset.univ.filter fun i ↦ e ∈ (cycles i).edges).card = 2

/-- A bounded cycle double cover contains an edge set when one of its members is exactly that
edge set. -/
def CycleDoubleCover.Contains {H : LoopMultigraph V E} {k : ℕ}
    (D : H.CycleDoubleCover k) (F : Finset E) : Prop :=
  ∃ i, (D.cycles i).edges = F

noncomputable section

open DominatingCircuitCore

variable {Chord Hub : Type*}
  [Fintype Chord] [DecidableEq Chord] [Fintype Hub] [DecidableEq Hub]

/-- Identify the five normal-form cover indices (`none` and the four colours) with `Fin 5`. -/
noncomputable def fiveIndexEquiv : Fin 5 ≃ Option Color :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, DominatingCircuitCore.NormalForm.card_option_color])

/-- Transport a normal-form five-cycle double cover through an endpoint-multigraph isomorphism.

The normal-form core deliberately proves evenness by explicit local degree formulas.  The
`hEven` argument is the single interface lemma saying that those formulas compute degree in
`M.graph`; no contraction or lifting assertion is assumed here. -/
noncomputable def transportNormalFormCover
    (M : DominatingCircuitCore.NormalForm Chord Hub)
    (D : M.FiveCycleDoubleCover) (H : LoopMultigraph V E)
    (f : EndpointIso M.graph H)
    (hEven : ∀ A : M.EvenSubgraph, M.graph.IsEvenEdgeSet A.edges) :
    H.CycleDoubleCover 5 where
  cycles i :=
    { edges := f.mapEdges (D.cycles (fiveIndexEquiv i)).edges
      even := (f.isEvenEdgeSet_mapEdges _).mpr (hEven _) }
  coveredTwice := by
    intro e
    let d : M.Edge := f.edgeEquiv.symm e
    let ι : Fin 5 ≃ Option Color := fiveIndexEquiv
    have he : f.edgeEquiv d = e := by simp [d]
    have hcard :
        Fintype.card {i : Fin 5 //
          e ∈ f.mapEdges (D.cycles (ι i)).edges} =
        Fintype.card {k : Option Color // d ∈ (D.cycles k).edges} := by
      apply Fintype.card_congr
      exact ι.subtypeEquiv fun i ↦ by
        rw [← he, f.mem_mapEdges]
    calc
      (Finset.univ.filter fun i : Fin 5 ↦
          e ∈ f.mapEdges (D.cycles (ι i)).edges).card =
          Fintype.card {i : Fin 5 //
            e ∈ f.mapEdges (D.cycles (ι i)).edges} := by
            rw [Fintype.card_subtype]
      _ = Fintype.card {k : Option Color // d ∈ (D.cycles k).edges} := hcard
      _ = (Finset.univ.filter fun k : Option Color ↦
          d ∈ (D.cycles k).edges).card := by
            rw [Fintype.card_subtype]
      _ = 2 := D.coveredTwice d

/-- The transported cover contains the image of the normal form's distinguished circuit. -/
theorem transportNormalFormCover_containsCircuit
    (M : DominatingCircuitCore.NormalForm Chord Hub)
    (D : M.FiveCycleDoubleCover) (H : LoopMultigraph V E)
    (f : EndpointIso M.graph H)
    (hEven : ∀ A : M.EvenSubgraph, M.graph.IsEvenEdgeSet A.edges) :
    (transportNormalFormCover M D H f hEven).Contains (f.mapEdges M.circuitEdges) := by
  let ι : Fin 5 ≃ Option Color := fiveIndexEquiv
  refine ⟨ι.symm none, ?_⟩
  have hi : fiveIndexEquiv (ι.symm none) = none := by
    change ι (ι.symm none) = none
    exact ι.apply_symm_apply none
  change f.mapEdges (D.cycles (fiveIndexEquiv (ι.symm none))).edges =
    f.mapEdges M.circuitEdges
  rw [hi, D.containsCircuit]

end

namespace TraversedCircuit

variable {H : LoopMultigraph V E} (C : H.TraversedCircuit)

/-- Corollary 1.2 for a circuit with its cyclic traversal bundled: a cubic graph with a
dominating circuit has a five-cycle double cover containing that circuit. -/
theorem exists_fiveCycleDoubleCover_containing
    (hCubic : ∀ v : V, H.degree v = 3) (hDom : C.Dominates) :
    ∃ D : H.CycleDoubleCover 5, D.Contains C.edges := by
  let M := C.normalForm hCubic hDom
  obtain ⟨D⟩ := M.exists_fiveCycleDoubleCover
  let f := C.normalEndpointIso hCubic hDom
  have hEven : ∀ A : M.EvenSubgraph, M.graph.IsEvenEdgeSet A.edges := by
    intro A
    exact (M.graph_isEvenEdgeSet_iff A.edges).mpr A.even
  let R : H.CycleDoubleCover 5 := transportNormalFormCover M D H f hEven
  refine ⟨R, ?_⟩
  have hc := transportNormalFormCover_containsCircuit M D H f hEven
  change R.Contains (f.mapEdges M.circuitEdges) at hc
  rw [C.map_normalCircuitEdges hCubic hDom] at hc
  exact hc

end TraversedCircuit

namespace OrdinaryCircuit

/-- Bundle the cyclic traversal that every finite ordinary circuit possesses. -/
noncomputable def toTraversedCircuit {H : LoopMultigraph V E} (C : H.OrdinaryCircuit) :
    H.TraversedCircuit where
  toOrdinaryCircuit := C
  tour := C.eulerTour

/-- Corollary 1.2 in the paper's unbundled language. -/
theorem exists_fiveCycleDoubleCover_containing {H : LoopMultigraph V E}
    (C : H.OrdinaryCircuit) (hCubic : ∀ v : V, H.degree v = 3)
    (hDom : C.Dominates) :
    ∃ D : H.CycleDoubleCover 5, D.Contains C.edges := by
  let T := C.toTraversedCircuit
  have hDomT : T.Dominates := hDom
  simpa [T, toTraversedCircuit] using
    T.exists_fiveCycleDoubleCover_containing hCubic hDomT

end OrdinaryCircuit

end LoopMultigraph

end GraphPuzzles
