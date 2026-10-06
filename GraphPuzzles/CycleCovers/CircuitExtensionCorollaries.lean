import GraphPuzzles.CycleCovers.CircuitExtension

/-!
# Consequences of the exact extension theorem

This file derives three statements from `exists_fiveCycleDoubleCover_of_complementColoring`.

* A proper three-edge-colouring of the graph obtained by deleting the vertices of a circuit
  extends to a proper colouring of the edges outside the circuit, by assigning the unused colours
  at each outside vertex to its edges into the circuit.
* Every circuit of a critical cubic graph, one in which deleting the two ends of any edge leaves a
  three-edge-colourable graph, is an entire member of a five-cycle double cover.
* If three perfect matchings cover every edge outside a circuit exactly once, that circuit is an
  entire member of a five-cycle double cover.
-/

namespace GraphPuzzles
namespace LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- A proper three-edge-colouring of the graph obtained by deleting a set of vertices: edges
avoiding `S` receive nonzero colours, and at every vertex outside `S` distinct half-edges of such
edges receive distinct colours. -/
def ProperOff (H : LoopMultigraph V E) (S : Finset V) (g : E → Color) : Prop :=
  (∀ e, (∀ i, H.endAt e i ∉ S) → g e ≠ 0) ∧
  ∀ v, v ∉ S → ∀ h₁ h₂ : H.halfEdgesAt v,
    (∀ i, H.endAt h₁.1.1 i ∉ S) → (∀ i, H.endAt h₂.1.1 i ∉ S) →
      g h₁.1.1 = g h₂.1.1 → h₁ = h₂

omit [DecidableEq V] [DecidableEq E] in
theorem ProperOff.mono {H : LoopMultigraph V E} {S S' : Finset V} {g : E → Color}
    (hg : H.ProperOff S g) (hSS' : S ⊆ S') : H.ProperOff S' g := by
  refine ⟨fun e he ↦ hg.1 e (fun i hi ↦ he i (hSS' hi)), ?_⟩
  intro v hv h₁ h₂ h₁S h₂S heq
  exact hg.2 v (fun h ↦ hv (hSS' h)) h₁ h₂ (fun i hi ↦ h₁S i (hSS' hi))
    (fun i hi ↦ h₂S i (hSS' hi)) heq

/-- A cubic graph is critical when deleting the two ends of any edge leaves a
three-edge-colourable graph. -/
def IsCritical (H : LoopMultigraph V E) : Prop :=
  ∀ e : E, ∃ g : E → Color, H.ProperOff {H.endAt e 0, H.endAt e 1} g

private theorem fin2_eq_rev_of_ne {i j : Fin 2} (h : i ≠ j) : j = Fin.rev i := by
  revert i j
  decide

namespace TraversedCircuit

variable {H : LoopMultigraph V E} (C : H.TraversedCircuit)

/-- A proper colouring of the edges with both ends outside the circuit. -/
structure DeletedColoring where
  color : E → Color
  nonzero : ∀ e, C.IsInternal e → color e ≠ 0
  injective_at : ∀ v, v ∉ C.vertices → ∀ h₁ h₂ : H.halfEdgesAt v,
    C.IsInternal h₁.1.1 → C.IsInternal h₂.1.1 → color h₁.1.1 = color h₂.1.1 → h₁ = h₂

/-- A colouring proper off the circuit vertices is a deleted colouring. -/
def DeletedColoring.ofProperOff {g : E → Color} (hg : H.ProperOff C.vertices g) :
    C.DeletedColoring where
  color := g
  nonzero := fun e he ↦ hg.1 e he
  injective_at := fun v hv h₁ h₂ h₁i h₂i heq ↦ hg.2 v hv h₁ h₂ h₁i h₂i heq

namespace DeletedColoring

variable {C} (g : C.DeletedColoring)

/-- Internal half-edges at an outside vertex. -/
abbrev IntHalf (v : C.Hub) := {h : H.halfEdgesAt v.1 // C.IsInternal h.1.1}

/-- Pendant half-edges at an outside vertex. -/
abbrev PendHalf (v : C.Hub) := {h : H.halfEdgesAt v.1 // ¬ C.IsInternal h.1.1}

/-- The colour of an internal half-edge, as a nonzero colour. -/
def intColor (v : C.Hub) (h : IntHalf v) : {c : Color // c ≠ 0} :=
  ⟨g.color h.1.1.1, g.nonzero _ h.2⟩

omit [DecidableEq E] in
theorem intColor_injective (v : C.Hub) : Function.Injective (g.intColor v) := by
  intro h₁ h₂ hh
  exact Subtype.ext
    (g.injective_at v.1 v.2 h₁.1 h₂.1 h₁.2 h₂.2 (congrArg Subtype.val hh))

/-- Nonzero colours not used by the internal half-edges at `v`. -/
abbrev Unused (v : C.Hub) :=
  {c : {c : Color // c ≠ 0} // c ∉ Set.range (g.intColor v)}

omit [DecidableEq E] in
theorem card_pendHalf (hCubic : ∀ v : V, H.degree v = 3) (v : C.Hub) :
    Fintype.card (PendHalf v) = 3 - Fintype.card (IntHalf v) := by
  rw [Fintype.card_subtype_compl]
  congr 1
  exact hCubic v.1

omit [DecidableEq E] in
theorem card_unused (v : C.Hub) : Fintype.card (g.Unused v) = 3 - Fintype.card (IntHalf v) := by
  classical
  rw [Fintype.card_subtype_compl, card_nonzeroColor]
  congr 1
  exact Set.card_range_of_injective (g.intColor_injective v)

/-- An arbitrary bijection between the pendant half-edges at `v` and the unused colours. -/
noncomputable def pendBij (hCubic : ∀ v : V, H.degree v = 3) (v : C.Hub) :
    PendHalf v ≃ g.Unused v :=
  Fintype.equivOfCardEq (by rw [card_pendHalf hCubic v, g.card_unused v])

omit [DecidableEq E] in
theorem not_isInternal_of_isPendant {e : E} (he : C.IsPendant e) : ¬ C.IsInternal e :=
  fun hint ↦ hint _ (C.circuitSide_spec he).1

/-- The pendant half-edge of a pendant edge at its outside end. -/
def pendHalf {e : E} (he : C.IsPendant e) : PendHalf ⟨C.farEnd e, C.farEnd_not_mem he⟩ :=
  ⟨⟨(e, Fin.rev (C.circuitSide e)), rfl⟩, not_isInternal_of_isPendant he⟩

/-- A pendant half-edge at an outside vertex, as an element of `PendHalf`. -/
def pendHalfAt (v : C.Hub) (h : H.halfEdgesAt v.1) (hp : C.IsPendant h.1.1) : PendHalf v :=
  ⟨h, not_isInternal_of_isPendant hp⟩

/-- Extend the colouring to all edges outside the circuit. -/
noncomputable def extend (hCubic : ∀ v : V, H.degree v = 3) (e : E) : Color :=
  if C.IsInternal e then g.color e
  else if he : C.IsPendant e then
    (g.pendBij hCubic ⟨C.farEnd e, C.farEnd_not_mem he⟩ (pendHalf he)).1.1
  else (1, 0)

omit [DecidableEq E] in
theorem extend_of_isInternal (hCubic : ∀ v : V, H.degree v = 3) {e : E}
    (he : C.IsInternal e) : g.extend hCubic e = g.color e := by
  unfold extend
  rw [if_pos he]

omit [DecidableEq E] in
theorem pendBij_congr (hCubic : ∀ v : V, H.degree v = 3) {w₁ w₂ : C.Hub} (hw : w₁ = w₂)
    (y : PendHalf w₁) :
    (g.pendBij hCubic w₁ y).1.1 = (g.pendBij hCubic w₂ ⟨⟨y.1.1, hw ▸ y.1.2⟩, y.2⟩).1.1 := by
  subst hw
  rfl

omit [DecidableEq E] in
theorem extend_of_isPendant_at (hCubic : ∀ v : V, H.degree v = 3) (v : C.Hub)
    (h : H.halfEdgesAt v.1) (hp : C.IsPendant h.1.1) :
    g.extend hCubic h.1.1 = (g.pendBij hCubic v (pendHalfAt v h hp)).1.1 := by
  have hv : H.endAt h.1.1 h.1.2 = v.1 := h.2
  have hoff : H.endAt h.1.1 h.1.2 ∉ C.vertices := by
    rw [hv]
    exact v.2
  have hon : H.endAt h.1.1 (Fin.rev h.1.2) ∈ C.vertices := by
    obtain ⟨i, hi, _⟩ := hp
    by_cases his : i = h.1.2
    · subst his
      exact absurd hi hoff
    · rw [← fin2_eq_rev_of_ne (Ne.symm his)]
      exact hi
  have hside : Fin.rev h.1.2 = C.circuitSide h.1.1 := C.side_eq_circuitSide_of_isPendant hp hon
  have hfar : C.farEnd h.1.1 = v.1 := by
    unfold farEnd
    rw [← hside, Fin.rev_rev, hv]
  have hw : (⟨C.farEnd h.1.1, C.farEnd_not_mem hp⟩ : C.Hub) = v := Subtype.ext hfar
  have hy : (⟨⟨(h.1.1, Fin.rev (C.circuitSide h.1.1)), by
      change H.endAt h.1.1 (Fin.rev (C.circuitSide h.1.1)) = v.1
      rw [← hside, Fin.rev_rev]
      exact hv⟩, not_isInternal_of_isPendant hp⟩ : PendHalf v) = pendHalfAt v h hp := by
    apply Subtype.ext
    apply Subtype.ext
    change (h.1.1, Fin.rev (C.circuitSide h.1.1)) = h.1
    rw [← hside, Fin.rev_rev]
  unfold extend
  rw [if_neg (not_isInternal_of_isPendant hp), dif_pos hp, g.pendBij_congr hCubic hw]
  exact congrArg (fun y : PendHalf v ↦ (g.pendBij hCubic v y).1.1) hy

omit [DecidableEq E] in
theorem extend_nonzero (hCubic : ∀ v : V, H.degree v = 3) (e : E) :
    g.extend hCubic e ≠ 0 := by
  unfold extend
  split_ifs with hint hp
  · exact g.nonzero e hint
  · exact (g.pendBij hCubic _ (pendHalf hp)).1.2
  · decide

omit [DecidableEq E] in
theorem extend_injective_at (hCubic : ∀ v : V, H.degree v = 3) (v : C.Hub)
    (h₁ h₂ : H.halfEdgesAt v.1) (heq : g.extend hCubic h₁.1.1 = g.extend hCubic h₂.1.1) :
    h₁ = h₂ := by
  have hcl : ∀ h : H.halfEdgesAt v.1, C.IsInternal h.1.1 ∨ C.IsPendant h.1.1 := by
    intro h
    apply C.isInternal_or_isPendant (i := h.1.2)
    have hv : H.endAt h.1.1 h.1.2 = v.1 := h.2
    rw [hv]
    exact v.2
  have hmix : ∀ h h' : H.halfEdgesAt v.1, C.IsInternal h.1.1 → C.IsPendant h'.1.1 →
      g.extend hCubic h.1.1 ≠ g.extend hCubic h'.1.1 := by
    intro h h' hi hp heq'
    rw [g.extend_of_isInternal hCubic hi, g.extend_of_isPendant_at hCubic v h' hp] at heq'
    apply (g.pendBij hCubic v (pendHalfAt v h' hp)).2
    exact ⟨⟨h, hi⟩, Subtype.ext heq'⟩
  rcases hcl h₁ with hi₁ | hp₁ <;> rcases hcl h₂ with hi₂ | hp₂
  · apply g.injective_at v.1 v.2 h₁ h₂ hi₁ hi₂
    rwa [g.extend_of_isInternal hCubic hi₁, g.extend_of_isInternal hCubic hi₂] at heq
  · exact absurd heq (hmix h₁ h₂ hi₁ hp₂)
  · exact absurd heq.symm (hmix h₂ h₁ hi₂ hp₁)
  · rw [g.extend_of_isPendant_at hCubic v h₁ hp₁, g.extend_of_isPendant_at hCubic v h₂ hp₂]
      at heq
    have := (g.pendBij hCubic v).injective (Subtype.ext (Subtype.ext heq))
    exact congrArg (fun y : PendHalf v ↦ y.1) this

/-- Every deleted colouring extends to a proper colouring of the edges outside the circuit. -/
noncomputable def toComplementColoring (hCubic : ∀ v : V, H.degree v = 3) :
    C.ComplementColoring where
  color := g.extend hCubic
  nonzero := fun e _ ↦ g.extend_nonzero hCubic e
  injective_at := fun v hv h₁ h₂ heq ↦ g.extend_injective_at hCubic ⟨v, hv⟩ h₁ h₂ heq

end DeletedColoring

theorem exists_fiveCycleDoubleCover_of_deletedColoring (hCubic : ∀ v : V, H.degree v = 3)
    (g : C.DeletedColoring) : ∃ D : H.CycleDoubleCover 5, D.Contains C.edges :=
  C.exists_fiveCycleDoubleCover_of_complementColoring hCubic (g.toComplementColoring hCubic)

/-- A colouring proper off the vertex set of a circuit yields a five-cycle double cover
containing the circuit as an entire member. -/
theorem exists_fiveCycleDoubleCover_of_properOff (hCubic : ∀ v : V, H.degree v = 3)
    {g : E → Color} (hg : H.ProperOff C.vertices g) :
    ∃ D : H.CycleDoubleCover 5, D.Contains C.edges :=
  C.exists_fiveCycleDoubleCover_of_deletedColoring hCubic (DeletedColoring.ofProperOff C hg)

end TraversedCircuit

/-- **Critical cubic graphs satisfy the strong five-cycle double cover property**, with the
prescribed circuit as an entire member. -/
theorem OrdinaryCircuit.exists_fiveCycleDoubleCover_of_isCritical {H : LoopMultigraph V E}
    (hCubic : ∀ v : V, H.degree v = 3) (hcrit : H.IsCritical) (C : H.OrdinaryCircuit) :
    ∃ D : H.CycleDoubleCover 5, D.Contains C.edges := by
  obtain ⟨e, he⟩ := C.nonempty
  obtain ⟨g, hg⟩ := hcrit e
  have hsub : ({H.endAt e 0, H.endAt e 1} : Finset V) ⊆ H.edgeSupport C.edges := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact H.mem_edgeSupport_iff.mpr ⟨e, he, 0, rfl⟩
    · rw [Finset.mem_singleton] at hv
      subst hv
      exact H.mem_edgeSupport_iff.mpr ⟨e, he, 1, rfl⟩
  exact C.toTraversedCircuit.exists_fiveCycleDoubleCover_of_properOff hCubic (hg.mono hsub)

/-- A perfect matching: every vertex has exactly one incident half-edge in the set. -/
def IsPerfectMatching (H : LoopMultigraph V E) (M : Finset E) : Prop :=
  ∀ v, H.degreeIn M v = 1

theorem two_le_degreeIn_of_ne (H : LoopMultigraph V E) {M : Finset E} {v : V}
    (h₁ h₂ : H.halfEdgesAt v) (hne : h₁ ≠ h₂) (hm₁ : h₁.1.1 ∈ M) (hm₂ : h₂.1.1 ∈ M) :
    2 ≤ H.degreeIn M v := by
  unfold degreeIn
  have hsub : ({h₁.1, h₂.1} : Finset (E × Fin 2)) ⊆
      (M ×ˢ (Finset.univ : Finset (Fin 2))).filter fun h ↦ H.endAt h.1 h.2 = v := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hm₁, Finset.mem_univ _⟩, h₁.2⟩
    · rw [Finset.mem_singleton] at hx
      subst hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hm₂, Finset.mem_univ _⟩, h₂.2⟩
  have hcard : ({h₁.1, h₂.1} : Finset (E × Fin 2)).card = 2 :=
    Finset.card_pair (fun h ↦ hne (Subtype.ext h))
  exact hcard.symm.le.trans (Finset.card_le_card hsub)

/-- The colour of an edge relative to a triple of edge sets: the sum of the reference colours of
the sets containing it. -/
def tripleColor (M : Fin 3 → Finset E) (e : E) : Color :=
  ∑ j, if e ∈ M j then choiceColor j else 0

theorem choiceColor_injective : ∀ a b : Fin 3, choiceColor a = choiceColor b → a = b := by
  decide

omit [Fintype E] in
theorem tripleColor_eq {M : Fin 3 → Finset E} {e : E} {j : Fin 3} (hj : e ∈ M j)
    (huniq : ∀ k, e ∈ M k → k = j) : tripleColor M e = choiceColor j := by
  unfold tripleColor
  rw [Finset.sum_eq_single j]
  · simp [hj]
  · intro k _ hk
    have : e ∉ M k := fun h ↦ hk (huniq k h)
    simp [this]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- **Single circuit core.**  If three perfect matchings of a cubic graph cover every edge
outside a circuit exactly once, the circuit is an entire member of a five-cycle double cover. -/
theorem OrdinaryCircuit.exists_fiveCycleDoubleCover_of_matchings {H : LoopMultigraph V E}
    (hCubic : ∀ v : V, H.degree v = 3) (C : H.OrdinaryCircuit)
    (M : Fin 3 → Finset E) (hM : ∀ j, H.IsPerfectMatching (M j))
    (hcore : ∀ e, e ∉ C.edges → ∃! j, e ∈ M j) :
    ∃ D : H.CycleDoubleCover 5, D.Contains C.edges := by
  apply C.exists_fiveCycleDoubleCover_of_coloring hCubic (tripleColor M)
  · intro e he
    obtain ⟨j, hj, huniq⟩ := hcore e he
    rw [tripleColor_eq hj huniq]
    exact choiceColor_ne_zero j
  · intro v hv h₁ h₂ heq
    have hne₁ : h₁.1.1 ∉ C.edges := fun h ↦ hv (H.mem_edgeSupport_iff.mpr ⟨_, h, _, h₁.2⟩)
    have hne₂ : h₂.1.1 ∉ C.edges := fun h ↦ hv (H.mem_edgeSupport_iff.mpr ⟨_, h, _, h₂.2⟩)
    obtain ⟨j₁, hj₁, hu₁⟩ := hcore _ hne₁
    obtain ⟨j₂, hj₂, hu₂⟩ := hcore _ hne₂
    rw [tripleColor_eq hj₁ hu₁, tripleColor_eq hj₂ hu₂] at heq
    have hj : j₁ = j₂ := choiceColor_injective _ _ heq
    subst hj
    by_contra hne
    have h2 := H.two_le_degreeIn_of_ne h₁ h₂ hne hj₁ hj₂
    rw [hM j₁ v] at h2
    omega

end LoopMultigraph
end GraphPuzzles
