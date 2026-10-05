import GraphPuzzles.Core.CyclicWord
import GraphPuzzles.Graph.LoopMultigraph
import GraphPuzzles.Circuits.OrdinaryCircuit

/-!
# The normal-form lift behind the dominating-circuit corollary

After deleting a dominating circuit from a cubic graph, every nontrivial component is either

* one chord joining two vertices of the circuit, or
* a three-edge star whose centre is off the circuit.

This file isolates the finite combinatorics of the standard contraction and lift.  A normal form
is a cyclic word whose letters are chord components or star centres.  Chord letters occur exactly
twice and star letters exactly three times.  Its edge type consists of the cyclic gaps, one edge
for every chord, and three spokes for every star.

The four-colouring theorem supplies four lifted even subgraphs.  Each lifted subgraph contains a
circuit gap precisely in its colour class and contains the unique exterior edge at a circuit
position precisely when that colour occurs on one of the two adjacent gaps.  The component parity
in the word colouring makes this rule well-defined at chords and even at star centres.  Adding the
distinguished circuit gives five even subgraphs covering every edge exactly twice.
-/

namespace GraphPuzzles
namespace DominatingCircuitCore

open CyclicWord
noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {Chord Hub : Type*}
  [Fintype Chord] [DecidableEq Chord] [Fintype Hub] [DecidableEq Hub]

private theorem degreeIn_eq_card_selectedHalfEdges
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : LoopMultigraph V E) (F : Finset E) (v : V) :
    G.degreeIn F v =
      Fintype.card {h : G.halfEdgesAt v // h.1.1 ∈ F} := by
  classical
  let A := {x : E × Fin 2 // x.1 ∈ F ∧ G.endAt x.1 x.2 = v}
  let B := {h : G.halfEdgesAt v // h.1.1 ∈ F}
  let e : B ≃ A :=
    { toFun := fun h ↦ ⟨h.1.1, h.2, h.1.2⟩
      invFun := fun x ↦ ⟨⟨x.1, x.2.2⟩, x.2.1⟩
      left_inv := by intro h; apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := by intro x; apply Subtype.ext; rfl }
  calc
    G.degreeIn F v = Fintype.card A := by
      unfold LoopMultigraph.degreeIn A
      rw [Fintype.card_subtype]
      congr 1
      ext x
      simp [and_comm]
    _ = Fintype.card B := (Fintype.card_congr e).symm
    _ = _ := rfl

/-- A cyclic circuit together with its partition into two-ended chord components and
three-ended star components. -/
structure NormalForm (Chord Hub : Type*)
    [Fintype Chord] [DecidableEq Chord] [Fintype Hub] [DecidableEq Hub] where
  word : Word (V := Chord ⊕ Hub)
  chordOccurrence : ∀ c : Chord, Fin 2 ≃ word.Occurrence (Sum.inl c)
  hubOccurrence : ∀ h : Hub, Fin 3 ≃ word.Occurrence (Sum.inr h)

namespace NormalForm

variable (M : NormalForm Chord Hub)

/-- Positions, equivalently vertices, of the distinguished circuit. -/
abbrev Pos := M.word.Pos

/-- Exterior edges: one per chord and three spokes per off-circuit cubic centre. -/
abbrev ExternalEdge (Chord Hub : Type*) := Chord ⊕ (Hub × Fin 3)

/-- All edges of the normal-form cubic graph.  The left summand is the distinguished circuit. -/
abbrev Edge := M.Pos ⊕ ExternalEdge Chord Hub

/-- Vertices of the normal-form cubic graph: circuit positions and off-circuit star centres. -/
abbrev Vertex := M.Pos ⊕ Hub

/-- The circuit edge occupying a cyclic gap. -/
def circuitEdge (i : M.Pos) : M.Edge := Sum.inl i

/-- The exterior chord represented by a two-element component. -/
def chordEdge (c : Chord) : M.Edge := Sum.inr (Sum.inl c)

/-- A spoke from a circuit position to an off-circuit cubic centre. -/
def spokeEdge (h : Hub) (j : Fin 3) : M.Edge := Sum.inr (Sum.inr (h, j))

/-- The full edge set of the distinguished circuit. -/
def circuitEdges : Finset M.Edge := by
  classical
  exact Finset.univ.filter fun e ↦ match e with
    | Sum.inl _ => True
    | Sum.inr _ => False

@[simp]
theorem circuitEdge_mem_circuitEdges (i : M.Pos) : M.circuitEdge i ∈ M.circuitEdges := by
  simp [circuitEdges, circuitEdge]

@[simp]
theorem chordEdge_not_mem_circuitEdges (c : Chord) : M.chordEdge c ∉ M.circuitEdges := by
  simp [circuitEdges, chordEdge]

@[simp]
theorem spokeEdge_not_mem_circuitEdges (h : Hub) (j : Fin 3) :
    M.spokeEdge h j ∉ M.circuitEdges := by
  simp [circuitEdges, spokeEdge]

@[simp]
theorem externalEdge_not_mem_circuitEdges (x : ExternalEdge Chord Hub) :
    Sum.inr x ∉ M.circuitEdges := by
  simp [circuitEdges]

/-- A chord position with its occurrence proof forgotten. -/
def chordPos (c : Chord) (j : Fin 2) : M.Pos := (M.chordOccurrence c j).1

/-- A star position with its occurrence proof forgotten. -/
def hubPos (h : Hub) (j : Fin 3) : M.Pos := (M.hubOccurrence h j).1

@[simp]
theorem word_letter_chordPos (c : Chord) (j : Fin 2) :
    M.word.letter (M.chordPos c j) = Sum.inl c :=
  (M.chordOccurrence c j).2

@[simp]
theorem word_letter_hubPos (h : Hub) (j : Fin 3) :
    M.word.letter (M.hubPos h j) = Sum.inr h :=
  (M.hubOccurrence h j).2

/-- A slot is an end of a contracted exterior component. -/
abbrev Slot (Chord Hub : Type*) := (Chord × Fin 2) ⊕ (Hub × Fin 3)

/-- The circuit position represented by a component slot. -/
def slotPos : Slot Chord Hub → M.Pos
  | Sum.inl (c, j) => M.chordPos c j
  | Sum.inr (h, j) => M.hubPos h j

theorem slotPos_injective : Function.Injective M.slotPos := by
  intro a b hab
  cases a with
  | inl cj =>
      rcases cj with ⟨c, j⟩
      cases b with
      | inl c'j' =>
          rcases c'j' with ⟨c', j'⟩
          have hc : c = c' := by
            apply Sum.inl.inj
            calc
              Sum.inl c = M.word.letter (M.chordPos c j) :=
                (M.word_letter_chordPos c j).symm
              _ = M.word.letter (M.chordPos c' j') := congrArg M.word.letter hab
              _ = Sum.inl c' := M.word_letter_chordPos c' j'
          subst c'
          have hj : j = j' := by
            apply (M.chordOccurrence c).injective
            apply Subtype.ext
            exact hab
          subst j'
          rfl
      | inr h'j' =>
          rcases h'j' with ⟨h', j'⟩
          have hbad : (Sum.inl c : Chord ⊕ Hub) = Sum.inr h' := by
            calc
              Sum.inl c = M.word.letter (M.chordPos c j) :=
                (M.word_letter_chordPos c j).symm
              _ = M.word.letter (M.hubPos h' j') := congrArg M.word.letter hab
              _ = Sum.inr h' := M.word_letter_hubPos h' j'
          cases hbad
  | inr hj =>
      rcases hj with ⟨h, j⟩
      cases b with
      | inl c'j' =>
          rcases c'j' with ⟨c', j'⟩
          have hbad : (Sum.inr h : Chord ⊕ Hub) = Sum.inl c' := by
            calc
              Sum.inr h = M.word.letter (M.hubPos h j) :=
                (M.word_letter_hubPos h j).symm
              _ = M.word.letter (M.chordPos c' j') := congrArg M.word.letter hab
              _ = Sum.inl c' := M.word_letter_chordPos c' j'
          cases hbad
      | inr h'j' =>
          rcases h'j' with ⟨h', j'⟩
          have hh : h = h' := by
            apply Sum.inr.inj
            calc
              Sum.inr h = M.word.letter (M.hubPos h j) :=
                (M.word_letter_hubPos h j).symm
              _ = M.word.letter (M.hubPos h' j') := congrArg M.word.letter hab
              _ = Sum.inr h' := M.word_letter_hubPos h' j'
          subst h'
          have hj : j = j' := by
            apply (M.hubOccurrence h).injective
            apply Subtype.ext
            exact hab
          subst j'
          rfl

theorem slotPos_surjective : Function.Surjective M.slotPos := by
  intro p
  cases hletter : M.word.letter p with
  | inl c =>
      let o : M.word.Occurrence (Sum.inl c) := ⟨p, hletter⟩
      let j := (M.chordOccurrence c).symm o
      refine ⟨Sum.inl (c, j), ?_⟩
      exact congrArg Subtype.val ((M.chordOccurrence c).apply_symm_apply o)
  | inr h =>
      let o : M.word.Occurrence (Sum.inr h) := ⟨p, hletter⟩
      let j := (M.hubOccurrence h).symm o
      refine ⟨Sum.inr (h, j), ?_⟩
      exact congrArg Subtype.val ((M.hubOccurrence h).apply_symm_apply o)

/-- Component slots are exactly the circuit positions. -/
noncomputable def slotEquiv : Slot Chord Hub ≃ M.Pos :=
  Equiv.ofBijective M.slotPos ⟨M.slotPos_injective, M.slotPos_surjective⟩

/-- The exterior-component slot at a circuit position. -/
noncomputable def slotAt (p : M.Pos) : Slot Chord Hub := M.slotEquiv.symm p

@[simp]
theorem slotAt_chordPos (c : Chord) (j : Fin 2) :
    M.slotAt (M.chordPos c j) = Sum.inl (c, j) := by
  change M.slotEquiv.symm (M.slotEquiv (Sum.inl (c, j))) = Sum.inl (c, j)
  exact M.slotEquiv.symm_apply_apply _

@[simp]
theorem slotAt_hubPos (h : Hub) (j : Fin 3) :
    M.slotAt (M.hubPos h j) = Sum.inr (h, j) := by
  change M.slotEquiv.symm (M.slotEquiv (Sum.inr (h, j))) = Sum.inr (h, j)
  exact M.slotEquiv.symm_apply_apply _

@[simp]
theorem slotPos_slotAt (p : M.Pos) : M.slotPos (M.slotAt p) = p :=
  M.slotEquiv.apply_symm_apply p

/-- The cubic graph represented by the normal form.  Circuit gap `i` runs from position `i` to
the next position; a chord joins its two occurrences; and a spoke joins its occurrence to its
off-circuit centre. -/
def graph : LoopMultigraph M.Vertex M.Edge where
  endAt
    | Sum.inl i, 0 => Sum.inl i
    | Sum.inl i, 1 => Sum.inl (finRotate (M.word.n + 1) i)
    | Sum.inr (Sum.inl c), 0 => Sum.inl (M.chordPos c 0)
    | Sum.inr (Sum.inl c), 1 => Sum.inl (M.chordPos c 1)
    | Sum.inr (Sum.inr (h, j)), 0 => Sum.inl (M.hubPos h j)
    | Sum.inr (Sum.inr (h, _)), 1 => Sum.inr h

/-- Every component has at least two circuit positions, so the cyclic-word theorem applies. -/
theorem min_card_occurrence (v : Chord ⊕ Hub) :
    2 ≤ Fintype.card (M.word.Occurrence v) := by
  cases v with
  | inl c =>
      have hcard := Fintype.card_congr (M.chordOccurrence c)
      simp at hcard
      omega
  | inr h =>
      have hcard := Fintype.card_congr (M.hubOccurrence h)
      have : Fintype.card (M.word.Occurrence (Sum.inr h)) = 3 := by
        simpa using hcard.symm
      omega

/-- The four-colouring of the circuit gaps supplied by the paper's cyclic-word theorem. -/
theorem exists_coloring : Nonempty M.word.Coloring :=
  M.word.exists_coloring M.min_card_occurrence

section Lift

variable (C : M.word.Coloring)

/-- A colour is used at a circuit position when it colours one of the two adjacent gaps. -/
def UsesColor (p : M.Pos) (z : Color) : Prop :=
  C.color (M.word.prev p) = z ∨ C.color p = z

/-- Forgetting the unique side coloured `z` identifies coloured occurrence-sides with the
occurrences at which `z` is used. -/
noncomputable def coloredSideEquivUsesColor (v : Chord ⊕ Hub) (z : Color) :
    {os : M.word.Occurrence v × Fin 2 //
      M.word.incidentColor C.color os.1 os.2 = z} ≃
    {o : M.word.Occurrence v // UsesColor M C o.1 z} where
  toFun os := by
    refine ⟨os.1.1, ?_⟩
    rcases os with ⟨⟨o, s⟩, hs⟩
    fin_cases s
    · change C.color (M.word.prev o.1) = z at hs
      exact Or.inl hs
    · change C.color o.1 = z at hs
      exact Or.inr hs
  invFun o := by
    by_cases hp : C.color (M.word.prev o.1.1) = z
    · exact ⟨⟨o.1, 0⟩, hp⟩
    · exact ⟨⟨o.1, 1⟩, by
        exact o.2.resolve_left hp⟩
  left_inv os := by
    rcases os with ⟨⟨o, s⟩, hs⟩
    apply Subtype.ext
    fin_cases s
    · change C.color (M.word.prev o.1) = z at hs
      simp [hs]
    · change C.color o.1 = z at hs
      have hprev : C.color (M.word.prev o.1) ≠ z := by
        intro h
        exact C.transition_ne o.1 (h.trans hs.symm)
      simp [hprev]
  right_inv o := by
    rcases o with ⟨o, ho⟩
    apply Subtype.ext
    apply Subtype.ext
    by_cases hp : C.color (M.word.prev o.1) = z <;> simp [hp]

/-- Word-colouring parity, expressed as parity of the positions at which a colour is used. -/
theorem usesColor_even (v : Chord ⊕ Hub) (z : Color) :
    Even (Fintype.card {o : M.word.Occurrence v // UsesColor M C o.1 z}) := by
  classical
  let e := coloredSideEquivUsesColor M C v z
  have hcard := Fintype.card_congr e
  rw [← hcard]
  exact C.color_even v z

/-- Transport the positions using a colour at a chord to its two slots. -/
def chordUsesEquiv (c : Chord) (z : Color) :
    {j : Fin 2 // UsesColor M C (M.chordPos c j) z} ≃
    {o : M.word.Occurrence (Sum.inl c) // UsesColor M C o.1 z} :=
  (M.chordOccurrence c).subtypeEquiv fun _ ↦ Iff.rfl

/-- Transport the positions using a colour at a star to its three spokes. -/
def hubUsesEquiv (h : Hub) (z : Color) :
    {j : Fin 3 // UsesColor M C (M.hubPos h j) z} ≃
    {o : M.word.Occurrence (Sum.inr h) // UsesColor M C o.1 z} :=
  (M.hubOccurrence h).subtypeEquiv fun _ ↦ Iff.rfl

private theorem finTwo_filter_even_iff {P : Fin 2 → Prop} [DecidablePred P] :
    Even (Fintype.card {j : Fin 2 // P j}) ↔ (P 0 ↔ P 1) := by
  classical
  rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter,
    Fin.sum_univ_two]
  by_cases h0 : P 0 <;> by_cases h1 : P 1 <;> simp_all

/-- At the two ends of a chord, the same colours are used.  This is exactly the parity condition
at the corresponding 4-valent contracted vertex. -/
theorem usesColor_chord_iff (c : Chord) (z : Color) :
    UsesColor M C (M.chordPos c 0) z ↔ UsesColor M C (M.chordPos c 1) z := by
  classical
  apply (finTwo_filter_even_iff
    (P := fun j ↦ UsesColor M C (M.chordPos c j) z)).mp
  rw [Fintype.card_congr (chordUsesEquiv M C c z)]
  exact usesColor_even (M := M) (C := C) (Sum.inl c) z

/-- The unique exterior edge incident with a circuit position. -/
noncomputable def externalAt (p : M.Pos) : ExternalEdge Chord Hub :=
  match M.slotAt p with
  | Sum.inl (c, _) => Sum.inl c
  | Sum.inr (h, j) => Sum.inr (h, j)

@[simp]
theorem externalAt_chordPos (c : Chord) (j : Fin 2) :
    M.externalAt (M.chordPos c j) = Sum.inl c := by
  simp [externalAt]

@[simp]
theorem externalAt_hubPos (h : Hub) (j : Fin 3) :
    M.externalAt (M.hubPos h j) = Sum.inr (h, j) := by
  simp [externalAt]

/-- The exterior half-edge incident with a circuit position. -/
noncomputable def externalHalfEdgeAt (p : M.Pos) : M.Edge × Fin 2 :=
  match M.slotAt p with
  | Sum.inl (c, j) => (M.chordEdge c, j)
  | Sum.inr (h, j) => (M.spokeEdge h j, 0)

@[simp]
theorem externalHalfEdgeAt_chordPos (c : Chord) (j : Fin 2) :
    M.externalHalfEdgeAt (M.chordPos c j) = (M.chordEdge c, j) := by
  simp [externalHalfEdgeAt]

@[simp]
theorem externalHalfEdgeAt_hubPos (h : Hub) (j : Fin 3) :
    M.externalHalfEdgeAt (M.hubPos h j) = (M.spokeEdge h j, 0) := by
  simp [externalHalfEdgeAt]

@[simp]
theorem graph_vertex_externalHalfEdgeAt (p : M.Pos) :
    M.graph.vertex (M.externalHalfEdgeAt p) = Sum.inl p := by
  have hp := M.slotPos_slotAt p
  cases hs : M.slotAt p with
  | inl cj =>
      rcases cj with ⟨c, j⟩
      simp [slotPos, hs] at hp
      subst p
      rw [M.externalHalfEdgeAt_chordPos]
      fin_cases j <;> rfl
  | inr hj =>
      rcases hj with ⟨h, j⟩
      simp [slotPos, hs] at hp
      subst p
      rw [M.externalHalfEdgeAt_hubPos]
      rfl

@[simp]
theorem externalHalfEdgeAt_fst (p : M.Pos) :
    (M.externalHalfEdgeAt p).1 = Sum.inr (M.externalAt p) := by
  cases hs : M.slotAt p with
  | inl cj =>
      rcases cj with ⟨c, j⟩
      simp [externalHalfEdgeAt, externalAt, chordEdge, hs]
  | inr hj =>
      rcases hj with ⟨h, j⟩
      simp [externalHalfEdgeAt, externalAt, spokeEdge, hs]

/-- The three half-edges at a circuit vertex in their normal-form order. -/
noncomputable def circuitHalfEdgeAt (p : M.Pos) : Fin 3 → M.Edge × Fin 2
  | 0 => (M.circuitEdge p, 0)
  | 1 => (M.circuitEdge (M.word.prev p), 1)
  | 2 => M.externalHalfEdgeAt p

@[simp]
theorem graph_vertex_circuitHalfEdgeAt (p : M.Pos) (j : Fin 3) :
    M.graph.vertex (M.circuitHalfEdgeAt p j) = Sum.inl p := by
  fin_cases j
  · rfl
  · change Sum.inl (finRotate (M.word.n + 1) (M.word.prev p)) = Sum.inl p
    simp [Word.prev]
  · exact M.graph_vertex_externalHalfEdgeAt p

/-- The normal-form enumeration of all half-edges at a circuit vertex. -/
noncomputable def circuitHalfEdgeEquiv (p : M.Pos) :
    Fin 3 ≃ M.graph.halfEdgesAt (Sum.inl p) :=
  Equiv.ofBijective
    (fun j ↦ ⟨M.circuitHalfEdgeAt p j, M.graph_vertex_circuitHalfEdgeAt p j⟩)
    ⟨by
      intro a b hab
      fin_cases a <;> fin_cases b
      · rfl
      · have hs := congrArg (fun h ↦ h.1.2) hab
        simp [circuitHalfEdgeAt] at hs
      · have he := congrArg (fun h ↦ h.1.1) hab
        simp [circuitHalfEdgeAt, circuitEdge, externalHalfEdgeAt_fst] at he
      · have hs := congrArg (fun h ↦ h.1.2) hab
        simp [circuitHalfEdgeAt] at hs
      · rfl
      · have he := congrArg (fun h ↦ h.1.1) hab
        simp [circuitHalfEdgeAt, circuitEdge, externalHalfEdgeAt_fst] at he
      · have he := congrArg (fun h ↦ h.1.1) hab
        simp [circuitHalfEdgeAt, circuitEdge, externalHalfEdgeAt_fst] at he
      · have he := congrArg (fun h ↦ h.1.1) hab
        simp [circuitHalfEdgeAt, circuitEdge, externalHalfEdgeAt_fst] at he
      · rfl,
    by
      intro hh
      rcases hh with ⟨⟨e, s⟩, hend⟩
      cases e with
      | inl i =>
          fin_cases s
          · have hi : i = p := Sum.inl.inj hend
            subst i
            exact ⟨0, Subtype.ext rfl⟩
          · have hnext : finRotate (M.word.n + 1) i = p := Sum.inl.inj hend
            have hi : i = M.word.prev p := by
              have := congrArg (finRotate (M.word.n + 1)).symm hnext
              simpa [Word.prev] using this
            subst i
            exact ⟨1, Subtype.ext rfl⟩
      | inr x =>
          cases x with
          | inl c =>
              fin_cases s
              · have hp : M.chordPos c 0 = p := Sum.inl.inj hend
                refine ⟨2, Subtype.ext ?_⟩
                have hs : M.slotAt p = Sum.inl (c, 0) := by
                  rw [← hp]
                  exact M.slotAt_chordPos c 0
                simp [circuitHalfEdgeAt, externalHalfEdgeAt, chordEdge, hs]
              · have hp : M.chordPos c 1 = p := Sum.inl.inj hend
                refine ⟨2, Subtype.ext ?_⟩
                have hs : M.slotAt p = Sum.inl (c, 1) := by
                  rw [← hp]
                  exact M.slotAt_chordPos c 1
                simp [circuitHalfEdgeAt, externalHalfEdgeAt, chordEdge, hs]
          | inr hj =>
              rcases hj with ⟨h, j⟩
              fin_cases s
              · have hp : M.hubPos h j = p := Sum.inl.inj hend
                refine ⟨2, Subtype.ext ?_⟩
                have hs : M.slotAt p = Sum.inr (h, j) := by
                  rw [← hp]
                  exact M.slotAt_hubPos h j
                simp [circuitHalfEdgeAt, externalHalfEdgeAt, spokeEdge, hs]
              · cases hend⟩

/-- The three spokes are exactly the half-edges at an off-circuit centre. -/
noncomputable def hubHalfEdgeEquiv (h : Hub) :
    Fin 3 ≃ M.graph.halfEdgesAt (Sum.inr h) :=
  Equiv.ofBijective
    (fun j ↦ ⟨(M.spokeEdge h j, 1), rfl⟩)
    ⟨by
      intro a b hab
      simpa [spokeEdge] using congrArg (fun x ↦ x.1.1) hab,
    by
      intro hh
      rcases hh with ⟨⟨e, s⟩, hend⟩
      cases e with
      | inl i => fin_cases s <;> cases hend
      | inr x =>
          cases x with
          | inl c => fin_cases s <;> cases hend
          | inr hj =>
              rcases hj with ⟨h', j⟩
              fin_cases s
              · cases hend
              · have hh' : h' = h := Sum.inr.inj hend
                subst h'
                exact ⟨j, Subtype.ext rfl⟩⟩

/-- The `z`-lift: its circuit edges are the `z` colour class and its exterior edges repair the
odd local incidences created at circuit positions. -/
def liftedEdges (C : M.word.Coloring) (z : Color) : Finset M.Edge := by
  classical
  exact Finset.univ.filter fun e ↦ match e with
    | Sum.inl i => C.color i = z
    | Sum.inr (Sum.inl c) => UsesColor M C (M.chordPos c 0) z
    | Sum.inr (Sum.inr (h, j)) => UsesColor M C (M.hubPos h j) z

@[simp]
theorem circuitEdge_mem_liftedEdges_iff (i : M.Pos) (z : Color) :
    M.circuitEdge i ∈ liftedEdges M C z ↔ C.color i = z := by
  simp [liftedEdges, circuitEdge]

@[simp]
theorem chordEdge_mem_liftedEdges_iff (c : Chord) (z : Color) :
    M.chordEdge c ∈ liftedEdges M C z ↔
      UsesColor M C (M.chordPos c 0) z := by
  simp [liftedEdges, chordEdge]

@[simp]
theorem spokeEdge_mem_liftedEdges_iff (h : Hub) (j : Fin 3) (z : Color) :
    M.spokeEdge h j ∈ liftedEdges M C z ↔
      UsesColor M C (M.hubPos h j) z := by
  simp [liftedEdges, spokeEdge]

/-- Membership of the exterior edge at a position is precisely the local repair rule. -/
theorem externalAt_mem_liftedEdges_iff (p : M.Pos) (z : Color) :
    Sum.inr (M.externalAt p) ∈ liftedEdges M C z ↔ UsesColor M C p z := by
  have hpos := M.slotPos_slotAt p
  cases hs : M.slotAt p with
  | inl cj =>
      rcases cj with ⟨c, j⟩
      simp [slotPos, hs] at hpos
      have hext : M.externalAt p = Sum.inl c := by simp [externalAt, hs]
      rw [hext]
      change M.chordEdge c ∈ liftedEdges M C z ↔ UsesColor M C p z
      rw [chordEdge_mem_liftedEdges_iff]
      fin_cases j
      · have hpos' : M.chordPos c (0 : Fin 2) = p := by
          simpa using hpos
        rw [hpos']
      · rw [usesColor_chord_iff (M := M) (C := C) c z]
        have hpos' : M.chordPos c (1 : Fin 2) = p := by
          simpa using hpos
        rw [hpos']
  | inr hj =>
      rcases hj with ⟨h, j⟩
      simp [slotPos, hs] at hpos
      have hext : M.externalAt p = Sum.inr (h, j) := by simp [externalAt, hs]
      rw [hext]
      change M.spokeEdge h j ∈ liftedEdges M C z ↔ UsesColor M C p z
      rw [spokeEdge_mem_liftedEdges_iff]
      simp [hpos]

end Lift

section EvenSubgraphs

/-- The degree of an edge set at a circuit vertex, written in the normal form.  The three terms
are the preceding circuit edge, the following circuit edge, and the unique exterior edge. -/
def circuitDegree (F : Finset M.Edge) (p : M.Pos) : ℕ :=
  (if M.circuitEdge (M.word.prev p) ∈ F then 1 else 0) +
    (if M.circuitEdge p ∈ F then 1 else 0) +
    (if Sum.inr (M.externalAt p) ∈ F then 1 else 0)

/-- The degree at an off-circuit cubic centre. -/
def hubDegree (F : Finset M.Edge) (h : Hub) : ℕ :=
  (Finset.univ.filter fun j : Fin 3 ↦ M.spokeEdge h j ∈ F).card

/-- Evenness for the normal-form cubic graph. -/
def IsEvenEdgeSet (F : Finset M.Edge) : Prop :=
  (∀ p : M.Pos, Even (M.circuitDegree F p)) ∧
    ∀ h : Hub, Even (M.hubDegree F h)

/-- Selecting half-edges commutes with the normal-form enumeration at a circuit vertex. -/
noncomputable def selectedCircuitHalfEdgeEquiv (F : Finset M.Edge) (p : M.Pos) :
    {j : Fin 3 // (M.circuitHalfEdgeAt p j).1 ∈ F} ≃
    {hh : M.graph.halfEdgesAt (Sum.inl p) // hh.1.1 ∈ F} :=
  (M.circuitHalfEdgeEquiv p).subtypeEquiv fun _ ↦ Iff.rfl

/-- Selecting half-edges commutes with the spoke enumeration at an off-circuit centre. -/
noncomputable def selectedHubHalfEdgeEquiv (F : Finset M.Edge) (h : Hub) :
    {j : Fin 3 // M.spokeEdge h j ∈ F} ≃
    {hh : M.graph.halfEdgesAt (Sum.inr h) // hh.1.1 ∈ F} :=
  (M.hubHalfEdgeEquiv h).subtypeEquiv fun _ ↦ Iff.rfl

/-- The actual graph degree at a circuit vertex is the three-term normal-form degree. -/
theorem graph_degreeIn_circuit (F : Finset M.Edge) (p : M.Pos) :
    M.graph.degreeIn F (Sum.inl p) = M.circuitDegree F p := by
  classical
  rw [degreeIn_eq_card_selectedHalfEdges]
  have hcard := Fintype.card_congr (M.selectedCircuitHalfEdgeEquiv F p)
  rw [← hcard, Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter,
    Fin.sum_univ_three]
  simp [circuitDegree, circuitHalfEdgeAt, Nat.add_comm]
  rfl

/-- The actual graph degree at an off-circuit centre is its spoke count. -/
theorem graph_degreeIn_hub (F : Finset M.Edge) (h : Hub) :
    M.graph.degreeIn F (Sum.inr h) = M.hubDegree F h := by
  classical
  rw [degreeIn_eq_card_selectedHalfEdges]
  have hcard := Fintype.card_congr (M.selectedHubHalfEdgeEquiv F h)
  rw [← hcard, Fintype.card_subtype]
  rfl

/-- The local normal-form parity predicate is exactly binary evenness in the explicit graph. -/
theorem graph_isEvenEdgeSet_iff (F : Finset M.Edge) :
    M.graph.IsEvenEdgeSet F ↔ M.IsEvenEdgeSet F := by
  rw [M.graph.isEvenEdgeSet_iff_even_degree]
  constructor
  · intro heven
    constructor
    · intro p
      rw [← M.graph_degreeIn_circuit F p]
      exact heven (Sum.inl p)
    · intro h
      rw [← M.graph_degreeIn_hub F h]
      exact heven (Sum.inr h)
  · rintro ⟨hcircuit, hhub⟩ v
    cases v with
    | inl p =>
        rw [M.graph_degreeIn_circuit F p]
        exact hcircuit p
    | inr h =>
        rw [M.graph_degreeIn_hub F h]
        exact hhub h

/-- A cycle in the bounded-cover sense: a possibly disconnected even subgraph. -/
structure EvenSubgraph where
  edges : Finset M.Edge
  even : M.IsEvenEdgeSet edges

/-- The distinguished circuit is itself even. -/
theorem circuitEdges_even : M.IsEvenEdgeSet M.circuitEdges := by
  constructor
  · intro p
    simp [circuitDegree]
  · intro h
    simp [hubDegree]

/-- The distinguished circuit is even in the explicit `LoopMultigraph`. -/
theorem graph_circuitEdges_even : M.graph.IsEvenEdgeSet M.circuitEdges :=
  (M.graph_isEvenEdgeSet_iff M.circuitEdges).2 M.circuitEdges_even

/-- The distinguished circuit as an even subgraph. -/
def circuitSubgraph : M.EvenSubgraph where
  edges := M.circuitEdges
  even := M.circuitEdges_even

section Colored

variable (C : M.word.Coloring)

/-- Every repaired colour class is an even subgraph of the normal form. -/
theorem liftedEdges_even (z : Color) : M.IsEvenEdgeSet (liftedEdges M C z) := by
  constructor
  · intro p
    have hne := C.transition_ne p
    by_cases hp : C.color (M.word.prev p) = z
    · have hc : C.color p ≠ z := by
        intro hc
        exact hne (hp.trans hc.symm)
      simp [circuitDegree, externalAt_mem_liftedEdges_iff, UsesColor, hp, hc]
    · by_cases hc : C.color p = z
      · simp [circuitDegree, externalAt_mem_liftedEdges_iff, UsesColor, hp, hc]
      · simp [circuitDegree, externalAt_mem_liftedEdges_iff, UsesColor, hp, hc]
  · intro h
    have heven := usesColor_even (M := M) (C := C) (Sum.inr h) z
    have hcard := Fintype.card_congr (hubUsesEquiv M C h z)
    rw [← hcard] at heven
    rw [Fintype.card_subtype] at heven
    simpa [hubDegree] using heven

/-- Every repaired colour class is even in the explicit `LoopMultigraph`. -/
theorem graph_liftedEdges_even (z : Color) :
    M.graph.IsEvenEdgeSet (liftedEdges M C z) :=
  (M.graph_isEvenEdgeSet_iff (liftedEdges M C z)).2 (M.liftedEdges_even C z)

/-- One of the four lifted colour classes as an even subgraph. -/
def liftedSubgraph (z : Color) : M.EvenSubgraph where
  edges := liftedEdges M C z
  even := liftedEdges_even M C z

/-- The five members of the cover, indexed by `none` for the distinguished circuit and by the
four colours for the lifted subgraphs. -/
def fiveSubgraphs : Option Color → M.EvenSubgraph
  | none => M.circuitSubgraph
  | some z => M.liftedSubgraph C z

@[simp]
theorem fiveSubgraphs_none_edges : (M.fiveSubgraphs C none).edges = M.circuitEdges := rfl

@[simp]
theorem fiveSubgraphs_some_edges (z : Color) :
    (M.fiveSubgraphs C (some z)).edges = liftedEdges M C z := rfl

private theorem card_option_singleton (a : Color) :
    (Finset.univ.filter fun k : Option Color ↦
      match k with
      | none => True
      | some z => z = a).card = 2 := by
  classical
  have heq : (Finset.univ.filter fun k : Option Color ↦
      match k with
      | none => True
      | some z => z = a) = {none, some a} := by
    ext k
    cases k <;> simp
  rw [heq]
  simp

private theorem card_option_two_colors (a b : Color) (hab : a ≠ b) :
    (Finset.univ.filter fun k : Option Color ↦
      match k with
      | none => False
      | some z => a = z ∨ b = z).card = 2 := by
  classical
  have heq : (Finset.univ.filter fun k : Option Color ↦
      match k with
      | none => False
      | some z => a = z ∨ b = z) = {some a, some b} := by
    ext k
    cases k <;> simp [eq_comm]
  rw [heq]
  simp [hab]

/-- Every normal-form edge occurs in exactly two of the five subgraphs. -/
theorem fiveSubgraphs_cover_twice (e : M.Edge) :
    (Finset.univ.filter fun k : Option Color ↦
      e ∈ (M.fiveSubgraphs C k).edges).card = 2 := by
  classical
  cases e with
  | inl i =>
      have heq : (Finset.univ.filter fun k : Option Color ↦
          Sum.inl i ∈ (M.fiveSubgraphs C k).edges) =
          Finset.univ.filter fun k : Option Color ↦
            match k with | none => True | some z => z = C.color i := by
        ext k
        cases k <;> simp [fiveSubgraphs, circuitSubgraph, circuitEdges,
          liftedSubgraph, liftedEdges, eq_comm]
      rw [heq]
      exact card_option_singleton (C.color i)
  | inr x =>
      cases x with
      | inl c =>
          let p := M.chordPos c 0
          have hne : C.color (M.word.prev p) ≠ C.color p := C.transition_ne p
          have heq : (Finset.univ.filter fun k : Option Color ↦
              Sum.inr (Sum.inl c) ∈ (M.fiveSubgraphs C k).edges) =
              Finset.univ.filter fun k : Option Color ↦
                match k with
                | none => False
                | some z => C.color (M.word.prev p) = z ∨ C.color p = z := by
            ext k
            cases k <;> simp [fiveSubgraphs, circuitSubgraph, liftedSubgraph,
              liftedEdges, circuitEdges, UsesColor, p]
          rw [heq]
          exact card_option_two_colors (C.color (M.word.prev p)) (C.color p) hne
      | inr hj =>
          rcases hj with ⟨h, j⟩
          let p := M.hubPos h j
          have hne : C.color (M.word.prev p) ≠ C.color p := C.transition_ne p
          have heq : (Finset.univ.filter fun k : Option Color ↦
              Sum.inr (Sum.inr (h, j)) ∈ (M.fiveSubgraphs C k).edges) =
              Finset.univ.filter fun k : Option Color ↦
                match k with
                | none => False
                | some z => C.color (M.word.prev p) = z ∨ C.color p = z := by
            ext k
            cases k <;> simp [fiveSubgraphs, circuitSubgraph, liftedSubgraph,
              liftedEdges, circuitEdges, UsesColor, p]
          rw [heq]
          exact card_option_two_colors (C.color (M.word.prev p)) (C.color p) hne

/-- A five-cycle double cover of the normal form which contains the distinguished circuit. -/
structure FiveCycleDoubleCover where
  cycles : Option Color → M.EvenSubgraph
  coveredTwice : ∀ e : M.Edge,
    (Finset.univ.filter fun k : Option Color ↦ e ∈ (cycles k).edges).card = 2
  containsCircuit : (cycles none).edges = M.circuitEdges

/-- The lift of a compatible four-colouring is the desired five-cycle double cover. -/
def fiveCycleDoubleCover : M.FiveCycleDoubleCover where
  cycles := M.fiveSubgraphs C
  coveredTwice := M.fiveSubgraphs_cover_twice C
  containsCircuit := rfl

end Colored

/-- The index type really has five elements. -/
theorem card_option_color : Fintype.card (Option Color) = 5 := by decide

/-- The cyclic-word theorem and the normal-form lift together give the desired cover. -/
theorem exists_fiveCycleDoubleCover : Nonempty M.FiveCycleDoubleCover := by
  obtain ⟨C⟩ := M.exists_coloring
  exact ⟨M.fiveCycleDoubleCover C⟩

end EvenSubgraphs

end NormalForm

end

end DominatingCircuitCore
end GraphPuzzles
