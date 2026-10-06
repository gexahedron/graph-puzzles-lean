import GraphPuzzles.DefectThree.HexagonCore
import GraphPuzzles.Graph.Boundary

/-!
# Circuits disjoint from a hexagonal core

The defect-three note handles a prescribed circuit `C` vertex-disjoint from the hexagon `H` by
two elementary tools: the *toggle* of a proper three-edge-colouring by two vertex-disjoint even
subgraphs, and the *restoration* of the hexagon in a double cover of its complement.  Together
they produce six even layers with `C` and `H` entire, or five layers with `C ∪ H` entire.

This module proves the restoration lemma and the toggle lemma in the parity language of the
repository, without deleting or suppressing anything in the graph: all layers are edge sets of
the original graph, and the paths of the informal proof are replaced by binary T-joins.
-/

namespace GraphPuzzles
namespace LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

private theorem fin2_cases (k : Fin 2) : k = 0 ∨ k = 1 := by
  revert k
  decide

private theorem fin2_rev_of_ne {a b : Fin 2} (h : a ≠ b) : b = Fin.rev a := by
  revert a b
  decide

private theorem fin6_ne_add_one (a : Fin 6) : a ≠ a + 1 := by
  revert a
  decide

section Indicators

omit [DecidableEq E] in
/-- The boundary of a set defined by an `F₂`-valued indicator is the incidence pairing. -/
theorem boundary_filter_eq (χ : E → F₂) (w : V) :
    H.boundary (Finset.univ.filter fun e ↦ χ e = 1) w = ∑ e, χ e * H.edgeIncidence w e := by
  unfold boundary
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : χ e = 1
  · rw [if_pos h, h, one_mul]
  · have h0 : χ e = 0 := by
      rcases (show ∀ x : F₂, x = 0 ∨ x = 1 by decide) (χ e) with h0 | h1
      · exact h0
      · exact absurd h1 h
    rw [if_neg h, h0, zero_mul]

theorem sum_indicator_mul (S : Finset E) (f : E → F₂) :
    ∑ e, (if e ∈ S then (1 : F₂) else 0) * f e = ∑ e ∈ S, f e := by
  simp only [boole_mul]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- The degree of a vertex in an edge set counts the half-edges at it belonging to the set. -/
theorem degreeIn_eq_card_halfEdges (J : Finset E) (w : V) :
    H.degreeIn J w = (Finset.univ.filter fun x : H.halfEdgesAt w ↦ x.1.1 ∈ J).card := by
  unfold degreeIn
  apply Finset.card_bij (fun x hx ↦ ⟨x, (Finset.mem_filter.mp hx).2⟩)
  · intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).1⟩
  · intro x _ y _ hxy
    exact congrArg Subtype.val hxy
  · intro y hy
    exact ⟨y.1, Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨(Finset.mem_filter.mp hy).2, Finset.mem_univ _⟩, y.2⟩, rfl⟩

omit [DecidableEq E] in
theorem boundary_eq_degreeIn_cast (J : Finset E) (w : V) :
    H.boundary J w = (H.degreeIn J w : F₂) := (H.degreeIn_cast J w).symm

end Indicators

section Merge

/-- The union of two disjoint members of a double cover, as an even subgraph. -/
noncomputable def CycleDoubleCover.mergedSubgraph {k : ℕ} (D : H.CycleDoubleCover (k + 1))
    (a : Fin k)
    (hdisj : Disjoint (D.cycles (Fin.castSucc a)).edges (D.cycles (Fin.last k)).edges) :
    H.EvenSubgraph where
  edges := (D.cycles (Fin.castSucc a)).edges ∪ (D.cycles (Fin.last k)).edges
  even := by
    intro w
    change H.boundary _ w = 0
    rw [H.boundary_union _ _ hdisj]
    have h1 : H.boundary (D.cycles (Fin.castSucc a)).edges w = 0 :=
      (D.cycles (Fin.castSucc a)).even w
    have h2 : H.boundary (D.cycles (Fin.last k)).edges w = 0 := (D.cycles (Fin.last k)).even w
    rw [h1, h2, add_zero]

theorem CycleDoubleCover.mergedSubgraph_edges {k : ℕ} (D : H.CycleDoubleCover (k + 1)) (a : Fin k)
    (hdisj : Disjoint (D.cycles (Fin.castSucc a)).edges (D.cycles (Fin.last k)).edges) :
    (D.mergedSubgraph a hdisj).edges =
      (D.cycles (Fin.castSucc a)).edges ∪ (D.cycles (Fin.last k)).edges := rfl

/-- Merging two disjoint members of a double cover. -/
noncomputable def CycleDoubleCover.merge {k : ℕ} (D : H.CycleDoubleCover (k + 1)) (a : Fin k)
    (hdisj : Disjoint (D.cycles (Fin.castSucc a)).edges (D.cycles (Fin.last k)).edges) :
    H.CycleDoubleCover k where
  cycles i := if i = a then D.mergedSubgraph a hdisj else D.cycles (Fin.castSucc i)
  coveredTwice e := by
    have h := D.coveredTwice e
    rw [Finset.card_filter, Fin.sum_univ_castSucc] at h
    rw [Finset.card_filter]
    have hpt : ∀ i : Fin k,
        (if e ∈ (if i = a then D.mergedSubgraph a hdisj else D.cycles (Fin.castSucc i)).edges
          then 1 else 0) =
        (if e ∈ (D.cycles (Fin.castSucc i)).edges then 1 else 0) +
          (if i = a then (if e ∈ (D.cycles (Fin.last k)).edges then 1 else 0) else 0) := by
      intro i
      by_cases hia : i = a
      · subst hia
        simp only [if_true, CycleDoubleCover.mergedSubgraph_edges, Finset.mem_union]
        by_cases h1 : e ∈ (D.cycles (Fin.castSucc i)).edges <;>
          by_cases h2 : e ∈ (D.cycles (Fin.last k)).edges <;> simp [h1, h2]
        exact absurd h2 (Finset.disjoint_left.mp hdisj h1)
      · simp [hia]
    simp only [hpt, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact h

/-- Padding a double cover by an empty member. -/
noncomputable def CycleDoubleCover.pad {k : ℕ} (D : H.CycleDoubleCover k) :
    H.CycleDoubleCover (k + 1) where
  cycles := Fin.lastCases ⟨∅, fun w ↦ by
    change H.boundary ∅ w = 0
    exact H.boundary_empty w⟩ D.cycles
  coveredTwice e := by
    have h := D.coveredTwice e
    rw [Finset.card_filter] at h
    rw [Finset.card_filter, Fin.sum_univ_castSucc]
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last, Finset.notMem_empty, if_false, add_zero]
    exact h

theorem CycleDoubleCover.pad_contains {k : ℕ} (D : H.CycleDoubleCover k) {F : Finset E}
    (h : D.Contains F) : D.pad.Contains F := by
  obtain ⟨i, hi⟩ := h
  exact ⟨Fin.castSucc i, by simp [pad, hi]⟩

theorem CycleDoubleCover.merge_cycles_self {k : ℕ} (D : H.CycleDoubleCover (k + 1)) (a : Fin k)
    (hdisj : Disjoint (D.cycles (Fin.castSucc a)).edges (D.cycles (Fin.last k)).edges) :
    ((D.merge a hdisj).cycles a).edges =
      (D.cycles (Fin.castSucc a)).edges ∪ (D.cycles (Fin.last k)).edges := by
  simp [merge, mergedSubgraph_edges]

end Merge

namespace Hexagon

variable (X : H.Hexagon)

/-- The hexagon vertices as a finset. -/
def vertexSet : Finset V := Finset.univ.image X.v

/-- The hexagon edges as a finset. -/
def edgeSet : Finset E := Finset.univ.image X.h

omit [DecidableEq V] [DecidableEq E] in
theorem spoke_injective : Function.Injective X.spoke := by
  intro i j hij
  by_cases hs : X.side i = X.side j
  · apply X.v_injective
    rw [← X.spoke_end i, ← X.spoke_end j, hij, hs]
  · exfalso
    have hrev : X.side j = Fin.rev (X.side i) := fin2_rev_of_ne hs
    apply X.spoke_far i j
    rw [← hrev, hij]
    exact X.spoke_end j

omit [DecidableEq E] in
theorem mem_vertexSet {w : V} : w ∈ X.vertexSet ↔ ∃ i, X.v i = w := by
  simp [vertexSet]

omit [DecidableEq V] in
theorem mem_edgeSet {e : E} : e ∈ X.edgeSet ↔ ∃ i, X.h i = e := by
  simp [edgeSet]

omit [DecidableEq V] in
theorem h_mem_edgeSet (i : Fin 6) : X.h i ∈ X.edgeSet := X.mem_edgeSet.mpr ⟨i, rfl⟩

omit [DecidableEq V] in
theorem spoke_notin_edgeSet (i : Fin 6) : X.spoke i ∉ X.edgeSet := by
  intro h
  obtain ⟨j, hj⟩ := X.mem_edgeSet.mp h
  exact X.spoke_ne_h i j hj.symm

/-- An edge set of hexagon edges has zero boundary off the hexagon. -/
theorem boundary_eq_zero_of_subset_edgeSet {J : Finset E} (hJ : J ⊆ X.edgeSet) {w : V}
    (hw : ∀ i, w ≠ X.v i) : H.boundary J w = 0 := by
  apply H.boundary_eq_zero_of_ends (S := X.vertexSet)
  · intro e he k
    obtain ⟨i, rfl⟩ := X.mem_edgeSet.mp (hJ he)
    rcases fin2_cases k with rfl | rfl
    · rw [X.h_end0]
      exact X.mem_vertexSet.mpr ⟨i, rfl⟩
    · rw [X.h_end1]
      exact X.mem_vertexSet.mpr ⟨i + 1, rfl⟩
  · intro hmem
    obtain ⟨i, hi⟩ := X.mem_vertexSet.mp hmem
    exact hw i hi.symm

/-- The boundary at a hexagon vertex of a cubic graph counts the three half-edges there. -/
theorem boundary_at_vertex (hCubic : ∀ v : V, H.degree v = 3) (J : Finset E) (i : Fin 6) :
    H.boundary J (X.v i) =
      (if X.h i ∈ J then 1 else 0) + ((if X.h (i - 1) ∈ J then 1 else 0) +
        (if X.spoke i ∈ J then 1 else 0)) := by
  rw [H.boundary_eq_degreeIn_cast, H.degreeIn_eq_card_halfEdges]
  have huniv : (Finset.univ : Finset (H.halfEdgesAt (X.v i))) =
      {X.hex0 i, X.hex1 i, X.spokeHalf i} := by
    ext x
    simp only [Finset.mem_univ, true_iff]
    rcases X.halfEdge_cases hCubic i x with rfl | rfl | rfl <;> simp
  rw [huniv, Finset.filter_insert, Finset.filter_insert, Finset.filter_singleton]
  have h01 : X.hex0 i ≠ X.hex1 i := X.hex0_ne_hex1 i
  have h02 : X.hex0 i ≠ X.spokeHalf i := X.hex0_ne_spokeHalf i
  have h12 : X.hex1 i ≠ X.spokeHalf i := X.hex1_ne_spokeHalf i
  have e0 : (X.hex0 i).1.1 = X.h i := rfl
  have e1 : (X.hex1 i).1.1 = X.h (i - 1) := rfl
  have e2 : (X.spokeHalf i).1.1 = X.spoke i := rfl
  rw [e0, e1, e2]
  by_cases ha : X.h i ∈ J <;> by_cases hb : X.h (i - 1) ∈ J <;> by_cases hc : X.spoke i ∈ J <;>
    simp only [ha, hb, hc, if_true, if_false] <;>
    simp [Finset.card_insert_of_notMem, h01, h02, h12] <;> decide

/-- Five even layers on the complement of the hexagon whose spoke labels have the restorable
pattern `{s, t i}`, with `t` constant on the pairs `(i, i + 1)` for `i ≡ j (mod 2)`. -/
structure PreCover where
  layer : Fin 5 → Finset E
  avoid : ∀ k i, X.h i ∉ layer k
  twice : ∀ e, (∀ i, e ≠ X.h i) → (Finset.univ.filter fun k ↦ e ∈ layer k).card = 2
  even_off : ∀ k w, (∀ i, w ≠ X.v i) → H.boundary (layer k) w = 0
  s : Fin 5
  t : Fin 6 → Fin 5
  j : Fin 6
  spoke_layers : ∀ i k, X.spoke i ∈ layer k ↔ (k = s ∨ k = t i)
  s_ne_t : ∀ i, s ≠ t i
  t_pair : ∀ i, i.val % 2 = j.val % 2 → t (i + 1) = t i

namespace PreCover

variable {X} (P : X.PreCover)

/-- The layer receiving the hexagon edge `i` besides the hexagon layer. -/
def assign (i : Fin 6) : Fin 5 := if i.val % 2 = P.j.val % 2 then P.t i else P.s

/-- The hexagon edges assigned to layer `k`. -/
def hexAssigned (k : Fin 5) : Finset E :=
  (Finset.univ.filter fun i ↦ P.assign i = k).image X.h

theorem mem_hexAssigned {k : Fin 5} {e : E} :
    e ∈ P.hexAssigned k ↔ ∃ i, P.assign i = k ∧ X.h i = e := by
  simp [hexAssigned]

theorem h_mem_hexAssigned_iff (i : Fin 6) (k : Fin 5) :
    X.h i ∈ P.hexAssigned k ↔ k = P.assign i := by
  rw [P.mem_hexAssigned]
  constructor
  · rintro ⟨i', hi', hh⟩
    rw [X.h_injective hh] at hi'
    exact hi'.symm
  · intro h
    exact ⟨i, h.symm, rfl⟩

theorem spoke_notin_hexAssigned (i : Fin 6) (k : Fin 5) : X.spoke i ∉ P.hexAssigned k := by
  rw [P.mem_hexAssigned]
  rintro ⟨i', -, hh⟩
  exact X.spoke_ne_h i i' hh.symm

theorem notin_hexAssigned_of_not_h {e : E} (he : ∀ i, e ≠ X.h i) (k : Fin 5) :
    e ∉ P.hexAssigned k := by
  rw [P.mem_hexAssigned]
  rintro ⟨i, -, hh⟩
  exact he i hh.symm

theorem hexAssigned_subset (k : Fin 5) : P.hexAssigned k ⊆ X.edgeSet := by
  intro e he
  obtain ⟨i, -, rfl⟩ := P.mem_hexAssigned.mp he
  exact X.h_mem_edgeSet i

theorem disjoint_layer_hexAssigned (k : Fin 5) : Disjoint (P.layer k) (P.hexAssigned k) := by
  rw [Finset.disjoint_left]
  intro e he he'
  obtain ⟨i, -, rfl⟩ := P.mem_hexAssigned.mp he'
  exact P.avoid k i he

/-- The six layers of the restored cover: the five extended layers and the hexagon. -/
def full : Fin 6 → Finset E :=
  Fin.lastCases X.edgeSet (fun k ↦ P.layer k ∪ P.hexAssigned k)

theorem full_castSucc (k : Fin 5) : P.full (Fin.castSucc k) = P.layer k ∪ P.hexAssigned k := by
  simp [full]

theorem full_last : P.full (Fin.last 5) = X.edgeSet := by
  unfold full
  exact Fin.lastCases_last

theorem assign_parity_eq (i : Fin 6) (hi : i.val % 2 = P.j.val % 2) : P.assign i = P.t i := by
  simp [assign, hi]

theorem assign_parity_ne (i : Fin 6) (hi : i.val % 2 ≠ P.j.val % 2) : P.assign i = P.s := by
  simp [assign, hi]

private theorem fin6_parity_sub_one (i j : Fin 6) :
    (i - 1).val % 2 = j.val % 2 ↔ i.val % 2 ≠ j.val % 2 := by
  revert i j
  decide

/-- The extended layers are even at the hexagon vertices. -/
theorem boundary_full_castSucc_vertex (hCubic : ∀ v : V, H.degree v = 3) (k : Fin 5)
    (i : Fin 6) : H.boundary (P.full (Fin.castSucc k)) (X.v i) = 0 := by
  rw [P.full_castSucc, X.boundary_at_vertex hCubic]
  have hh : ∀ i', X.h i' ∈ P.layer k ∪ P.hexAssigned k ↔ k = P.assign i' := by
    intro i'
    rw [Finset.mem_union, P.h_mem_hexAssigned_iff]
    exact ⟨fun h ↦ h.resolve_left (P.avoid k i'), Or.inr⟩
  have hs : X.spoke i ∈ P.layer k ∪ P.hexAssigned k ↔ (k = P.s ∨ k = P.t i) := by
    rw [Finset.mem_union, P.spoke_layers]
    exact ⟨fun h ↦ h.resolve_right (P.spoke_notin_hexAssigned i k), Or.inl⟩
  simp only [hh, hs]
  have hst : P.s ≠ P.t i := P.s_ne_t i
  by_cases hi : i.val % 2 = P.j.val % 2
  · have h1 : P.assign i = P.t i := P.assign_parity_eq i hi
    have h2 : P.assign (i - 1) = P.s :=
      P.assign_parity_ne (i - 1) (fun h ↦ ((fin6_parity_sub_one i P.j).mp h) hi)
    rw [h1, h2]
    by_cases hk1 : k = P.t i <;> by_cases hk2 : k = P.s
    · exact absurd (hk2.symm.trans hk1) hst
    · rw [if_pos hk1, if_neg hk2, if_pos (Or.inr hk1)]
      decide
    · rw [if_neg hk1, if_pos hk2, if_pos (Or.inl hk2)]
      decide
    · rw [if_neg hk1, if_neg hk2, if_neg (not_or.mpr ⟨hk2, hk1⟩)]
      decide
  · have h1 : P.assign i = P.s := P.assign_parity_ne i hi
    have h2 : P.assign (i - 1) = P.t i := by
      rw [P.assign_parity_eq (i - 1) ((fin6_parity_sub_one i P.j).mpr hi)]
      have := P.t_pair (i - 1) ((fin6_parity_sub_one i P.j).mpr hi)
      rw [sub_add_cancel] at this
      exact this.symm
    rw [h1, h2]
    by_cases hk1 : k = P.t i <;> by_cases hk2 : k = P.s
    · exact absurd (hk2.symm.trans hk1) hst
    · rw [if_pos hk1, if_neg hk2, if_pos (Or.inr hk1)]
      decide
    · rw [if_neg hk1, if_pos hk2, if_pos (Or.inl hk2)]
      decide
    · rw [if_neg hk1, if_neg hk2, if_neg (not_or.mpr ⟨hk2, hk1⟩)]
      decide

theorem boundary_full_last_vertex (hCubic : ∀ v : V, H.degree v = 3) (i : Fin 6) :
    H.boundary (P.full (Fin.last 5)) (X.v i) = 0 := by
  rw [P.full_last, X.boundary_at_vertex hCubic, if_pos (X.h_mem_edgeSet i),
    if_pos (X.h_mem_edgeSet (i - 1)), if_neg (X.spoke_notin_edgeSet i)]
  decide

theorem full_even (hCubic : ∀ v : V, H.degree v = 3) (k : Fin 6) : H.IsEvenEdgeSet (P.full k) := by
  intro w
  change H.boundary (P.full k) w = 0
  by_cases hw : ∃ i, X.v i = w
  · obtain ⟨i, rfl⟩ := hw
    induction k using Fin.lastCases with
    | last => exact P.boundary_full_last_vertex hCubic i
    | cast k => exact P.boundary_full_castSucc_vertex hCubic k i
  · push Not at hw
    have hw' : ∀ i, w ≠ X.v i := fun i h ↦ hw i h.symm
    induction k using Fin.lastCases with
    | last =>
      rw [P.full_last]
      exact X.boundary_eq_zero_of_subset_edgeSet subset_rfl hw'
    | cast k =>
      rw [P.full_castSucc, H.boundary_union _ _ (P.disjoint_layer_hexAssigned k),
        P.even_off k w hw', X.boundary_eq_zero_of_subset_edgeSet (P.hexAssigned_subset k) hw',
        add_zero]

theorem full_twice (e : E) : (Finset.univ.filter fun k ↦ e ∈ P.full k).card = 2 := by
  rw [Finset.card_filter, Fin.sum_univ_castSucc]
  simp only [P.full_castSucc, P.full_last]
  by_cases he : ∃ i, X.h i = e
  · obtain ⟨i, rfl⟩ := he
    have hh : ∀ k, X.h i ∈ P.layer k ∪ P.hexAssigned k ↔ P.assign i = k := by
      intro k
      rw [Finset.mem_union, P.h_mem_hexAssigned_iff]
      exact ⟨fun h ↦ (h.resolve_left (P.avoid k i)).symm, fun h ↦ Or.inr h.symm⟩
    simp only [hh, Finset.sum_ite_eq, Finset.mem_univ, if_true, X.h_mem_edgeSet]
  · push Not at he
    have he' : ∀ i, e ≠ X.h i := fun i h ↦ he i h.symm
    have hh : ∀ k, e ∈ P.layer k ∪ P.hexAssigned k ↔ e ∈ P.layer k := by
      intro k
      rw [Finset.mem_union]
      exact ⟨fun h ↦ h.resolve_right (P.notin_hexAssigned_of_not_h he' k), Or.inl⟩
    have hne : e ∉ X.edgeSet := fun h ↦ by
      obtain ⟨i, hi⟩ := X.mem_edgeSet.mp h
      exact he i hi
    simp only [hh, hne, if_false, add_zero]
    rw [← Finset.card_filter]
    exact P.twice e he'

/-- The restored six-layer double cover. -/
noncomputable def cover (hCubic : ∀ v : V, H.degree v = 3) : H.CycleDoubleCover 6 where
  cycles k := ⟨P.full k, P.full_even hCubic k⟩
  coveredTwice := P.full_twice

theorem cover_cycles_edges (hCubic : ∀ v : V, H.degree v = 3) (k : Fin 6) :
    ((P.cover hCubic).cycles k).edges = P.full k := rfl

theorem hexAssigned_eq_empty {k : Fin 5} (hk : ∀ i, P.assign i ≠ k) : P.hexAssigned k = ∅ := by
  ext e
  simp only [Finset.notMem_empty, iff_false]
  intro he
  obtain ⟨i, hi, -⟩ := P.mem_hexAssigned.mp he
  exact hk i hi

/-- A layer receiving no hexagon edge is an entire member of the restored cover. -/
theorem cover_contains_layer (hCubic : ∀ v : V, H.degree v = 3) {k : Fin 5}
    (hk : ∀ i, P.assign i ≠ k) : (P.cover hCubic).Contains (P.layer k) :=
  ⟨Fin.castSucc k, by rw [P.cover_cycles_edges, P.full_castSucc, P.hexAssigned_eq_empty hk,
    Finset.union_empty]⟩

theorem cover_contains_edgeSet (hCubic : ∀ v : V, H.degree v = 3) :
    (P.cover hCubic).Contains X.edgeSet :=
  ⟨Fin.last 5, by rw [P.cover_cycles_edges, P.full_last]⟩

/-- Merging a layer receiving no hexagon edge with the hexagon layer gives five layers with
their union entire. -/
theorem exists_fiveCover_union (hCubic : ∀ v : V, H.degree v = 3) {k : Fin 5}
    (hk : ∀ i, P.assign i ≠ k) :
    ∃ D : H.CycleDoubleCover 5, D.Contains (P.layer k ∪ X.edgeSet) := by
  have hdisj : Disjoint ((P.cover hCubic).cycles (Fin.castSucc k)).edges
      ((P.cover hCubic).cycles (Fin.last 5)).edges := by
    rw [P.cover_cycles_edges, P.cover_cycles_edges, P.full_castSucc, P.full_last,
      P.hexAssigned_eq_empty hk, Finset.union_empty, Finset.disjoint_left]
    intro e he he'
    obtain ⟨i, rfl⟩ := X.mem_edgeSet.mp he'
    exact P.avoid k i he
  refine ⟨(P.cover hCubic).merge k hdisj, k, ?_⟩
  rw [CycleDoubleCover.merge_cycles_self, P.cover_cycles_edges, P.cover_cycles_edges,
    P.full_castSucc, P.full_last, P.hexAssigned_eq_empty hk, Finset.union_empty]

end PreCover

/-- A nonzero colour is one of three given pairwise distinct nonzero colours. -/
private theorem three_colors_cover (x y z : Color)
    (h : x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z) :
    ∀ t : Color, t ≠ 0 → t = x ∨ t = y ∨ t = z := by
  revert x y z
  decide

namespace ExteriorColoring

variable {X : H.Hexagon} (g : X.ExteriorColoring)

omit [DecidableEq V] [DecidableEq E] in
theorem exists_index {x : Color} (hx : x ≠ 0) : ∃ a, g.c a = x := by
  have hne : ∀ p q : Fin 3, p ≠ q → g.c p ≠ g.c q := fun p q hpq h ↦ hpq (g.c_injective h)
  rcases three_colors_cover (g.c 0) (g.c 1) (g.c 2) ⟨g.c_ne_zero 0, g.c_ne_zero 1, g.c_ne_zero 2,
    hne 0 1 (by decide), hne 0 2 (by decide), hne 1 2 (by decide)⟩ x hx with h | h | h
  · exact ⟨0, h.symm⟩
  · exact ⟨1, h.symm⟩
  · exact ⟨2, h.symm⟩

/-- The colour index of a nonzero colour. -/
noncomputable def idx (x : Color) : Fin 3 := if h : ∃ a, g.c a = x then h.choose else 0

omit [DecidableEq V] [DecidableEq E] in
theorem c_idx {x : Color} (hx : x ≠ 0) : g.c (g.idx x) = x := by
  have h := g.exists_index hx
  unfold idx
  rw [dif_pos h]
  exact h.choose_spec

omit [DecidableEq V] [DecidableEq E] in
theorem idx_c (a : Fin 3) : g.idx (g.c a) = a :=
  g.c_injective (g.c_idx (g.c_ne_zero a))

/-- The complement of a colour class among the non-hexagon edges. -/
def bLayer (a : Fin 3) : Finset E :=
  Finset.univ.filter fun e ↦ (∀ i, e ≠ X.h i) ∧ g.color e ≠ g.c a

omit [DecidableEq V] in
theorem mem_bLayer_iff {a : Fin 3} {e : E} (he : ∀ i, e ≠ X.h i) :
    e ∈ g.bLayer a ↔ g.idx (g.color e) ≠ a := by
  simp only [bLayer, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h hidx
    exact h.2 (by rw [← hidx, g.c_idx (g.nonzero e he)])
  · intro h
    refine ⟨he, fun hc ↦ h ?_⟩
    rw [hc, g.idx_c]

omit [DecidableEq V] in
theorem h_notin_bLayer (a : Fin 3) (i : Fin 6) : X.h i ∉ g.bLayer a := by
  simp only [bLayer, Finset.mem_filter, Finset.mem_univ, true_and, not_and]
  intro h
  exact absurd rfl (h i)

omit [DecidableEq V] [DecidableEq E] in
/-- No half-edge at a vertex off the hexagon is a hexagon edge. -/
theorem halfEdge_not_h {w : V} (hw : ∀ i, w ≠ X.v i) (x : H.halfEdgesAt w) (i : Fin 6) :
    x.1.1 ≠ X.h i := by
  intro h
  have hx : H.endAt x.1.1 x.1.2 = w := x.2
  rw [h] at hx
  rcases fin2_cases x.1.2 with hk | hk
  · rw [hk, X.h_end0] at hx
    exact hw i hx.symm
  · rw [hk, X.h_end1] at hx
    exact hw (i + 1) hx.symm

/-- At a vertex off the hexagon of a cubic graph, each colour occurs on exactly one half-edge,
so the complement of a colour class has even degree. -/
theorem boundary_bLayer (hCubic : ∀ v : V, H.degree v = 3) (a : Fin 3) {w : V}
    (hw : ∀ i, w ≠ X.v i) : H.boundary (g.bLayer a) w = 0 := by
  rw [H.boundary_eq_degreeIn_cast, H.degreeIn_eq_card_halfEdges]
  let φ : H.halfEdgesAt w → Fin 3 := fun x ↦ g.idx (g.color x.1.1)
  have hφ : Function.Injective φ := by
    intro x y hxy
    have hx := halfEdge_not_h hw x
    have hy := halfEdge_not_h hw y
    apply g.injective_at w x y hx hy
    have := congrArg g.c hxy
    simp only [φ] at this
    rwa [g.c_idx (g.nonzero _ hx), g.c_idx (g.nonzero _ hy)] at this
  have hcard : Fintype.card (H.halfEdgesAt w) = Fintype.card (Fin 3) := by
    rw [Fintype.card_fin]
    exact hCubic w
  have hbij : Function.Bijective φ :=
    (Fintype.bijective_iff_injective_and_card φ).mpr ⟨hφ, hcard⟩
  obtain ⟨x₀, hx₀⟩ := hbij.2 a
  have hfilter : (Finset.univ.filter fun x : H.halfEdgesAt w ↦ x.1.1 ∈ g.bLayer a) =
      Finset.univ.filter fun x ↦ φ x ≠ a := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact g.mem_bLayer_iff (halfEdge_not_h hw x)
  have hone : (Finset.univ.filter fun x : H.halfEdgesAt w ↦ φ x = a) = {x₀} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      exact hφ (h.trans hx₀.symm)
    · rintro rfl
      exact hx₀
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (H.halfEdgesAt w)))
    (p := fun x ↦ φ x = a)
  have hdeg : Fintype.card (H.halfEdgesAt w) = 3 := hCubic w
  rw [hone, Finset.card_singleton, Finset.card_univ, hdeg] at hsplit
  rw [hfilter]
  have h2 : (Finset.univ.filter fun x : H.halfEdgesAt w ↦ φ x ≠ a).card = 2 := by
    have : (Finset.univ.filter fun x : H.halfEdgesAt w ↦ ¬ φ x = a).card = 2 := by omega
    exact this
  rw [h2]
  decide

end ExteriorColoring

section Toggle

variable {X : H.Hexagon} (g : X.ExteriorColoring) (C : H.OrdinaryCircuit) (D₀ : Finset E)

/-- Indicator of the toggled colour layer `a`: the complement of colour class `a`, toggled by
`C` and by `D₀`. -/
def toggleInd (a : Fin 3) (e : E) : F₂ :=
  (if e ∈ g.bLayer a then 1 else 0) + ((if e ∈ C.edges then 1 else 0) + (if e ∈ D₀ then 1 else 0))

/-- The toggled colour layer `a`. -/
def colourLayer (a : Fin 3) : Finset E := Finset.univ.filter fun e ↦ toggleInd g C D₀ a e = 1

/-- The five toggled layers: three colour layers, `C`, and `D₀`. -/
def toggleLayer : Fin 5 → Finset E :=
  ![colourLayer g C D₀ 0, colourLayer g C D₀ 1, colourLayer g C D₀ 2, C.edges, D₀]

theorem toggleLayer_three : toggleLayer g C D₀ 3 = C.edges := rfl
theorem toggleLayer_four : toggleLayer g C D₀ 4 = D₀ := rfl

theorem boundary_colourLayer (w : V) (a : Fin 3) :
    H.boundary (colourLayer g C D₀ a) w =
      H.boundary (g.bLayer a) w + (H.boundary C.edges w + H.boundary D₀ w) := by
  unfold colourLayer
  rw [H.boundary_filter_eq]
  simp only [toggleInd, add_mul, Finset.sum_add_distrib, sum_indicator_mul]
  rfl

private theorem F₂_toggle_cases (u : F₂) (b d : Bool) :
    (u + ((if b then 1 else 0) + (if d then 1 else 0)) = (1 : F₂)) ↔
      (if (b && !d) || (!b && d) then u = 0 else u = 1) := by
  revert u b d
  decide

theorem mem_colourLayer_iff {a : Fin 3} {e : E} (he : ∀ i, e ≠ X.h i) :
    e ∈ colourLayer g C D₀ a ↔
      (if (e ∈ C.edges ∧ e ∉ D₀) ∨ (e ∉ C.edges ∧ e ∈ D₀) then g.idx (g.color e) = a
        else g.idx (g.color e) ≠ a) := by
  simp only [colourLayer, Finset.mem_filter, Finset.mem_univ, true_and, toggleInd]
  by_cases hC : e ∈ C.edges <;> by_cases hD : e ∈ D₀ <;>
    simp only [hC, hD, if_true, if_false, not_true, not_false_eq_true, and_self, and_false,
      or_false, false_or, and_true, or_self] <;>
    by_cases hb : e ∈ g.bLayer a <;> simp only [hb, if_true, if_false] <;>
    rw [g.mem_bLayer_iff he] at hb <;> simp only [ne_eq, not_not] at hb <;> simp [hb]

theorem h_notin_colourLayer (a : Fin 3) (i : Fin 6) (hC : ∀ i, X.v i ∉ H.edgeSupport C.edges)
    (hD : ∀ i, X.h i ∉ D₀) : X.h i ∉ colourLayer g C D₀ a := by
  simp only [colourLayer, Finset.mem_filter, Finset.mem_univ, true_and, toggleInd]
  have h1 : X.h i ∉ g.bLayer a := g.h_notin_bLayer a i
  have h2 : X.h i ∉ C.edges := fun h ↦ hC i (H.mem_edgeSupport_iff.mpr ⟨_, h, 0, X.h_end0 i⟩)
  rw [if_neg h1, if_neg h2, if_neg (hD i)]
  decide

/-- The colour index `a` as a layer index. -/
def c5 (a : Fin 3) : Fin 5 := ⟨a.val, by omega⟩

theorem c5_injective : Function.Injective c5 := by
  intro a b h
  exact Fin.ext (Fin.mk.inj_iff.mp h)

theorem c5_ne_three (a : Fin 3) : c5 a ≠ 3 := by
  revert a
  decide

theorem c5_ne_four (a : Fin 3) : c5 a ≠ 4 := by
  revert a
  decide

theorem toggleLayer_c5 (a : Fin 3) : toggleLayer g C D₀ (c5 a) = colourLayer g C D₀ a := by
  fin_cases a <;> rfl

theorem toggleLayer_avoid (hC : ∀ i, X.v i ∉ H.edgeSupport C.edges) (hD : ∀ i, X.h i ∉ D₀)
    (k : Fin 5) (i : Fin 6) : X.h i ∉ toggleLayer g C D₀ k := by
  fin_cases k
  · exact h_notin_colourLayer g C D₀ 0 i hC hD
  · exact h_notin_colourLayer g C D₀ 1 i hC hD
  · exact h_notin_colourLayer g C D₀ 2 i hC hD
  · exact fun h ↦ hC i (H.mem_edgeSupport_iff.mpr ⟨_, h, 0, X.h_end0 i⟩)
  · exact hD i

theorem toggleLayer_even_off (hCubic : ∀ v : V, H.degree v = 3)
    (hD₀off : ∀ w, (∀ i, w ≠ X.v i) → H.boundary D₀ w = 0) (k : Fin 5) (w : V)
    (hw : ∀ i, w ≠ X.v i) : H.boundary (toggleLayer g C D₀ k) w = 0 := by
  have hCw : H.boundary C.edges w = 0 := OrdinaryCircuit.even H C w
  have hcol : ∀ a : Fin 3, H.boundary (colourLayer g C D₀ a) w = 0 := by
    intro a
    rw [boundary_colourLayer, g.boundary_bLayer hCubic a hw, hCw, hD₀off w hw]
    decide
  fin_cases k
  · exact hcol 0
  · exact hcol 1
  · exact hcol 2
  · exact hCw
  · exact hD₀off w hw

theorem toggleLayer_twice (hCD : Disjoint C.edges D₀) (e : E) (he : ∀ i, e ≠ X.h i) :
    (Finset.univ.filter fun k ↦ e ∈ toggleLayer g C D₀ k).card = 2 := by
  rw [Finset.card_filter, Fin.sum_univ_five]
  change (if e ∈ colourLayer g C D₀ 0 then 1 else 0) + (if e ∈ colourLayer g C D₀ 1 then 1 else 0)
    + (if e ∈ colourLayer g C D₀ 2 then 1 else 0) + (if e ∈ C.edges then 1 else 0) +
    (if e ∈ D₀ then 1 else 0) = 2
  simp only [mem_colourLayer_iff g C D₀ he]
  generalize g.idx (g.color e) = a
  by_cases hC' : e ∈ C.edges <;> by_cases hD' : e ∈ D₀
  · exact absurd hD' (Finset.disjoint_left.mp hCD hC')
  · simp only [hC', hD', not_false_eq_true, and_self, not_true_eq_false, or_false,
      if_true, if_false]
    fin_cases a <;> simp
  · simp only [hC', hD', not_false_eq_true, and_self, not_true_eq_false, false_or,
      if_true, if_false]
    fin_cases a <;> simp
  · simp only [hC', hD', not_false_eq_true, and_false, false_and, or_self, if_false]
    fin_cases a <;> simp

theorem spoke_mem_colourLayer (hC : ∀ i, X.v i ∉ H.edgeSupport C.edges) (i : Fin 6) (a : Fin 3) :
    X.spoke i ∈ colourLayer g C D₀ a ↔
      (if X.spoke i ∈ D₀ then hexWord (i + g.r) = a else hexWord (i + g.r) ≠ a) := by
  rw [mem_colourLayer_iff g C D₀ (fun j ↦ X.spoke_ne_h i j), g.spoke_color, g.idx_c]
  have hsC : X.spoke i ∉ C.edges :=
    fun h ↦ hC i (H.mem_edgeSupport_iff.mpr ⟨_, h, X.side i, X.spoke_end i⟩)
  by_cases hsD : X.spoke i ∈ D₀ <;> simp [hsC, hsD]

theorem spoke_notin_toggleLayer_three (hC : ∀ i, X.v i ∉ H.edgeSupport C.edges) (i : Fin 6) :
    X.spoke i ∉ toggleLayer g C D₀ 3 :=
  fun h ↦ hC i (H.mem_edgeSupport_iff.mpr ⟨_, h, X.side i, X.spoke_end i⟩)

end Toggle

section Words

theorem hexWord_pair (r j : Fin 6) (hj : (j + r).val % 2 = 0) :
    hexWord (j + 1 + r) = hexWord (j + r) := by
  revert r j
  decide

theorem hexWord_ne_of_pair (r i j : Fin 6) (hj : (j + r).val % 2 = 0) (hi : i ≠ j)
    (hi' : i ≠ j + 1) : hexWord (i + r) ≠ hexWord (j + r) := by
  revert r i j
  decide

theorem hexWord_succ_of_parity (r i j : Fin 6) (hj : (j + r).val % 2 = 0)
    (hi : i.val % 2 = j.val % 2) : hexWord (i + 1 + r) = hexWord (i + r) := by
  revert r i j
  decide

theorem pair_shift (i j : Fin 6) (hi : i.val % 2 = j.val % 2) :
    ((i + 1 = j ∨ i + 1 = j + 1) ↔ (i = j ∨ i = j + 1)) := by
  revert i j
  decide

theorem fin3_third_iff (p q a : Fin 3) (hpq : p ≠ q) :
    (q ≠ a ↔ (a = p ∨ a = thirdIndex p q)) := by
  revert p q a
  decide

theorem exists_pairAt (r : Fin 6) : ∃ j : Fin 6, (j + r).val % 2 = 0 := by
  revert r
  decide

end Words

section Connectivity

variable (X : H.Hexagon) (C : H.OrdinaryCircuit)

/-- The edges avoiding both the circuit and the hexagon. -/
def freeEdges : Finset E :=
  Finset.univ.filter fun e ↦ ∀ k, H.endAt e k ∉ H.edgeSupport C.edges ∧ ∀ i, H.endAt e k ≠ X.v i

theorem mem_freeEdges {e : E} :
    e ∈ X.freeEdges C ↔ ∀ k, H.endAt e k ∉ H.edgeSupport C.edges ∧ ∀ i, H.endAt e k ≠ X.v i := by
  simp [freeEdges]

/-- Two vertices are joined in the graph of free edges when every binary vertex function that is
constant along free edges agrees on them. -/
def FreeConn (u w : V) : Prop :=
  ∀ c : V → F₂, (∀ e ∈ X.freeEdges C, c (H.endAt e 0) = c (H.endAt e 1)) → c u = c w

/-- The outer end of the spoke at position `i`. -/
def far (i : Fin 6) : V := H.endAt (X.spoke i) (Fin.rev (X.side i))

omit [DecidableEq V] [DecidableEq E] in
theorem far_ne_v (i j : Fin 6) : X.far i ≠ X.v j := X.spoke_far i j

/-- A binary T-join between two joined vertices. -/
theorem exists_path {u w : V} (huw : X.FreeConn C u w) :
    ∃ P ⊆ X.freeEdges C, ∀ v, H.boundary P v =
      (if u = v then 1 else 0) + (if w = v then 1 else 0) := by
  apply H.exists_boundary_eq
  intro c hc
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  rw [huw c hc]
  exact F₂_add_self _

theorem freeEdge_notin_C {e : E} (he : e ∈ X.freeEdges C) : e ∉ C.edges := by
  intro hmem
  exact ((X.mem_freeEdges C).mp he 0).1 (H.mem_edgeSupport_iff.mpr ⟨e, hmem, 0, rfl⟩)

theorem spoke_notin_freeEdges (i : Fin 6) : X.spoke i ∉ X.freeEdges C := by
  intro h
  exact ((X.mem_freeEdges C).mp h (X.side i)).2 i (X.spoke_end i)

theorem h_notin_freeEdges (i : Fin 6) : X.h i ∉ X.freeEdges C := by
  intro h
  exact ((X.mem_freeEdges C).mp h 0).2 i (X.h_end0 i)

omit [DecidableEq E] in
/-- The incidence of a spoke at a vertex off the hexagon is the indicator of its outer end. -/
theorem edgeIncidence_spoke {w : V} (hw : ∀ i, w ≠ X.v i) (i : Fin 6) :
    H.edgeIncidence w (X.spoke i) = if X.far i = w then 1 else 0 := by
  rw [H.edgeIncidence_eq]
  unfold far
  have hv : H.endAt (X.spoke i) (X.side i) ≠ w := fun h ↦ hw i (h.symm.trans (X.spoke_end i))
  rcases fin2_cases (X.side i) with hs | hs <;> rw [hs] at hv ⊢ <;> simp [hv]

end Connectivity

section PairCase

variable {X : H.Hexagon} (g : X.ExteriorColoring) (C : H.OrdinaryCircuit)

/-- **A connected equal-colour pair.**  If the outer ends of the two spokes of an equal-colour
pair are joined off `C ∪ H`, then `G` has six even layers double covering it with `C` and `H`
entire. -/
theorem exists_sixCover_of_pair_conn (hCubic : ∀ v : V, H.degree v = 3)
    (hC : ∀ i, X.v i ∉ H.edgeSupport C.edges) (j : Fin 6) (hj : g.PairAt j)
    (hconn : X.FreeConn C (X.far j) (X.far (j + 1))) :
    (∃ D : H.CycleDoubleCover 6, D.Contains C.edges ∧ D.Contains X.edgeSet) ∧
      ∃ D : H.CycleDoubleCover 5, D.Contains (C.edges ∪ X.edgeSet) := by
  obtain ⟨P, hP, hPbd⟩ := X.exists_path C hconn
  have hsne : X.spoke j ≠ X.spoke (j + 1) := fun h ↦ fin6_ne_add_one j (X.spoke_injective h)
  set S : Finset E := {X.spoke j, X.spoke (j + 1)} with hS
  have hPS : Disjoint P S := by
    rw [Finset.disjoint_left]
    intro e heP heS
    simp only [hS, Finset.mem_insert, Finset.mem_singleton] at heS
    rcases heS with rfl | rfl
    · exact X.spoke_notin_freeEdges C j (hP heP)
    · exact X.spoke_notin_freeEdges C (j + 1) (hP heP)
  set D₀ := P ∪ S with hD₀
  have hD₀hex : ∀ i, X.h i ∉ D₀ := by
    intro i h
    rw [hD₀, Finset.mem_union, hS, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h
    · exact X.h_notin_freeEdges C i (hP h)
    · exact X.spoke_ne_h j i h.symm
    · exact X.spoke_ne_h (j + 1) i h.symm
  have hCD : Disjoint C.edges D₀ := by
    rw [Finset.disjoint_left]
    intro e heC heD
    rw [hD₀, Finset.mem_union, hS, Finset.mem_insert, Finset.mem_singleton] at heD
    rcases heD with h | rfl | rfl
    · exact X.freeEdge_notin_C C (hP h) heC
    · exact hC j (H.mem_edgeSupport_iff.mpr ⟨_, heC, X.side j, X.spoke_end j⟩)
    · exact hC (j + 1) (H.mem_edgeSupport_iff.mpr ⟨_, heC, X.side (j + 1), X.spoke_end (j + 1)⟩)
  have hD₀off : ∀ w, (∀ i, w ≠ X.v i) → H.boundary D₀ w = 0 := by
    intro w hw
    rw [hD₀, H.boundary_union _ _ hPS, hPbd w, hS, H.boundary_pair hsne, ← H.edgeIncidence_eq,
      ← H.edgeIncidence_eq, X.edgeIncidence_spoke hw, X.edgeIncidence_spoke hw]
    exact F₂_add_self _
  have hsD : ∀ i, X.spoke i ∈ D₀ ↔ (i = j ∨ i = j + 1) := by
    intro i
    rw [hD₀, Finset.mem_union, hS, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (h | h | h)
      · exact absurd (hP h) (X.spoke_notin_freeEdges C i)
      · exact Or.inl (X.spoke_injective h)
      · exact Or.inr (X.spoke_injective h)
    · rintro (rfl | rfl)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
  have hword : ∀ i, (i = j ∨ i = j + 1) → hexWord (i + g.r) = hexWord (j + g.r) := by
    rintro i (rfl | rfl)
    · rfl
    · exact hexWord_pair g.r j hj
  have hword' : ∀ i, ¬ (i = j ∨ i = j + 1) → hexWord (i + g.r) ≠ hexWord (j + g.r) := by
    intro i hi
    rw [not_or] at hi
    exact hexWord_ne_of_pair g.r i j hj hi.1 hi.2
  let t : Fin 6 → Fin 5 := fun i ↦
    if i = j ∨ i = j + 1 then 4 else c5 (thirdIndex (hexWord (j + g.r)) (hexWord (i + g.r)))
  have hcol : ∀ i (a : Fin 3), X.spoke i ∈ colourLayer g C D₀ a ↔
      (c5 a = c5 (hexWord (j + g.r)) ∨ c5 a = t i) := by
    intro i a
    rw [spoke_mem_colourLayer g C D₀ hC, c5_injective.eq_iff]
    by_cases hi : i = j ∨ i = j + 1
    · simp only [t, (hsD i).mpr hi, if_true, hi, hword i hi]
      rw [eq_comm]
      exact ⟨Or.inl, fun h ↦ h.resolve_right (c5_ne_four a)⟩
    · have hnot : X.spoke i ∉ D₀ := fun h ↦ hi ((hsD i).mp h)
      simp only [t, hnot, if_false, hi, c5_injective.eq_iff]
      exact fin3_third_iff _ _ _ (hword' i hi).symm
  let P' : X.PreCover :=
    { layer := toggleLayer g C D₀
      avoid := toggleLayer_avoid g C D₀ hC hD₀hex
      twice := toggleLayer_twice g C D₀ hCD
      even_off := toggleLayer_even_off g C D₀ hCubic hD₀off
      s := c5 (hexWord (j + g.r))
      t := t
      j := j
      spoke_layers := by
        intro i k
        fin_cases k
        · exact hcol i 0
        · exact hcol i 1
        · exact hcol i 2
        · refine ⟨fun h ↦ absurd h (spoke_notin_toggleLayer_three g C D₀ hC i), ?_⟩
          rintro (h | h)
          · exact absurd h.symm (c5_ne_three _)
          · simp only [t] at h
            split_ifs at h with hi
            · exact absurd h (by decide)
            · exact absurd h.symm (c5_ne_three _)
        · show X.spoke i ∈ D₀ ↔ _
          rw [hsD i]
          constructor
          · intro hi
            exact Or.inr (by simp [t, hi])
          · rintro (h | h)
            · exact absurd h.symm (c5_ne_four _)
            · simp only [t] at h
              split_ifs at h with hi
              · exact hi
              · exact absurd h.symm (c5_ne_four _)
      s_ne_t := by
        intro i
        simp only [t]
        split_ifs with hi
        · exact c5_ne_four _
        · intro h
          exact thirdIndex_ne_left (hword' i hi).symm (c5_injective h).symm
      t_pair := by
        intro i hi
        simp only [t, pair_shift i j hi]
        by_cases h : i = j ∨ i = j + 1
        · simp [h]
        · simp only [h, if_false]
          rw [hexWord_succ_of_parity g.r i j hj hi] }
  have hk : ∀ i, P'.assign i ≠ 3 := by
    intro i
    simp only [PreCover.assign, P', t]
    split_ifs
    · decide
    · exact c5_ne_three _
    · exact c5_ne_three _
  exact ⟨⟨P'.cover hCubic, P'.cover_contains_layer hCubic hk, P'.cover_contains_edgeSet hCubic⟩,
    P'.exists_fiveCover_union hCubic hk⟩

include g in
/-- **Three connected opposite pairs.**  If each spoke's outer end is joined off `C ∪ H` to the
outer end of the opposite spoke, then `G` has six even layers double covering it with `C` and
`H` entire. -/
theorem exists_sixCover_of_opposite_conn (hCubic : ∀ v : V, H.degree v = 3)
    (hC : ∀ i, X.v i ∉ H.edgeSupport C.edges)
    (hconn : ∀ i : Fin 6, X.FreeConn C (X.far i) (X.far (i + 3))) :
    (∃ D : H.CycleDoubleCover 6, D.Contains C.edges ∧ D.Contains X.edgeSet) ∧
      ∃ D : H.CycleDoubleCover 5, D.Contains (C.edges ∪ X.edgeSet) := by
  obtain ⟨P0, hP0, hb0⟩ := X.exists_path C (hconn 0)
  obtain ⟨P1, hP1, hb1⟩ := X.exists_path C (hconn 1)
  obtain ⟨P2, hP2, hb2⟩ := X.exists_path C (hconn 2)
  set S : Finset E := Finset.univ.image X.spoke with hS
  have hSmem : ∀ e, e ∈ S ↔ ∃ i, X.spoke i = e := by simp [hS]
  let χ : E → F₂ := fun e ↦ (if e ∈ P0 then 1 else 0) +
    ((if e ∈ P1 then 1 else 0) + ((if e ∈ P2 then 1 else 0) + (if e ∈ S then 1 else 0)))
  set D₀ := Finset.univ.filter fun e ↦ χ e = 1 with hD₀
  have hmemD₀ : ∀ e, e ∈ D₀ ↔ χ e = 1 := by simp [hD₀]
  have hspokeD₀ : ∀ i, X.spoke i ∈ D₀ := by
    intro i
    rw [hmemD₀]
    simp only [χ]
    rw [if_neg (fun h ↦ X.spoke_notin_freeEdges C i (hP0 h)),
      if_neg (fun h ↦ X.spoke_notin_freeEdges C i (hP1 h)),
      if_neg (fun h ↦ X.spoke_notin_freeEdges C i (hP2 h)), if_pos ((hSmem _).mpr ⟨i, rfl⟩)]
    decide
  have hD₀hex : ∀ i, X.h i ∉ D₀ := by
    intro i h
    rw [hmemD₀] at h
    simp only [χ] at h
    rw [if_neg (fun h ↦ X.h_notin_freeEdges C i (hP0 h)),
      if_neg (fun h ↦ X.h_notin_freeEdges C i (hP1 h)),
      if_neg (fun h ↦ X.h_notin_freeEdges C i (hP2 h)),
      if_neg (fun h ↦ by
        obtain ⟨i', hi'⟩ := (hSmem _).mp h
        exact X.spoke_ne_h i' i hi')] at h
    exact absurd h (by decide)
  have hCD : Disjoint C.edges D₀ := by
    rw [Finset.disjoint_left]
    intro e heC heD
    rw [hmemD₀] at heD
    simp only [χ] at heD
    have hs : e ∉ S := fun h ↦ by
      obtain ⟨i, rfl⟩ := (hSmem _).mp h
      exact hC i (H.mem_edgeSupport_iff.mpr ⟨_, heC, X.side i, X.spoke_end i⟩)
    rw [if_neg (fun h ↦ X.freeEdge_notin_C C (hP0 h) heC),
      if_neg (fun h ↦ X.freeEdge_notin_C C (hP1 h) heC),
      if_neg (fun h ↦ X.freeEdge_notin_C C (hP2 h) heC), if_neg hs] at heD
    exact absurd heD (by decide)
  have hD₀off : ∀ w, (∀ i, w ≠ X.v i) → H.boundary D₀ w = 0 := by
    intro w hw
    rw [hD₀, H.boundary_filter_eq]
    simp only [χ, add_mul, Finset.sum_add_distrib, sum_indicator_mul]
    change H.boundary P0 w + (H.boundary P1 w + (H.boundary P2 w + H.boundary S w)) = 0
    have hSb : H.boundary S w = ∑ i : Fin 6, if X.far i = w then 1 else 0 := by
      unfold boundary
      rw [hS, Finset.sum_image (fun i _ j _ h ↦ X.spoke_injective h)]
      exact Finset.sum_congr rfl (fun i _ ↦ X.edgeIncidence_spoke hw i)
    rw [hb0 w, hb1 w, hb2 w, hSb, Fin.sum_univ_six]
    simp only [show ((0 : Fin 6) + 3 = 3) from rfl, show ((1 : Fin 6) + 3 = 4) from rfl,
      show ((2 : Fin 6) + 3 = 5) from rfl]
    generalize (if X.far 0 = w then (1 : F₂) else 0) = x0
    generalize (if X.far 1 = w then (1 : F₂) else 0) = x1
    generalize (if X.far 2 = w then (1 : F₂) else 0) = x2
    generalize (if X.far 3 = w then (1 : F₂) else 0) = x3
    generalize (if X.far 4 = w then (1 : F₂) else 0) = x4
    generalize (if X.far 5 = w then (1 : F₂) else 0) = x5
    revert x0 x1 x2 x3 x4 x5
    decide
  obtain ⟨j, hj⟩ := exists_pairAt g.r
  let t : Fin 6 → Fin 5 := fun i ↦ c5 (hexWord (i + g.r))
  have hcol : ∀ i (a : Fin 3), X.spoke i ∈ colourLayer g C D₀ a ↔
      (c5 a = 4 ∨ c5 a = t i) := by
    intro i a
    rw [spoke_mem_colourLayer g C D₀ hC, if_pos (hspokeD₀ i)]
    simp only [t, c5_injective.eq_iff]
    rw [eq_comm]
    exact ⟨Or.inr, fun h ↦ h.resolve_left (c5_ne_four a)⟩
  let P' : X.PreCover :=
    { layer := toggleLayer g C D₀
      avoid := toggleLayer_avoid g C D₀ hC hD₀hex
      twice := toggleLayer_twice g C D₀ hCD
      even_off := toggleLayer_even_off g C D₀ hCubic hD₀off
      s := 4
      t := t
      j := j
      spoke_layers := by
        intro i k
        fin_cases k
        · exact hcol i 0
        · exact hcol i 1
        · exact hcol i 2
        · refine ⟨fun h ↦ absurd h (spoke_notin_toggleLayer_three g C D₀ hC i), ?_⟩
          rintro (h | h)
          · exact absurd h (by decide)
          · exact absurd h.symm (c5_ne_three _)
        · exact ⟨fun _ ↦ Or.inl rfl, fun _ ↦ hspokeD₀ i⟩
      s_ne_t := fun i ↦ (c5_ne_four _).symm
      t_pair := by
        intro i hi
        simp only [t]
        rw [hexWord_succ_of_parity g.r i j hj hi] }
  have hk : ∀ i, P'.assign i ≠ 3 := by
    intro i
    simp only [PreCover.assign, P', t]
    split_ifs
    · exact c5_ne_three _
    · decide
  exact ⟨⟨P'.cover hCubic, P'.cover_contains_layer hCubic hk, P'.cover_contains_edgeSet hCubic⟩,
    P'.exists_fiveCover_union hCubic hk⟩

end PairCase

section Table

/-- The four target spoke words of the partition lemma, in pair-colour indices (the original
word is `0,0,1,1,2,2`). -/
def tabW : Fin 4 → Fin 6 → Fin 3 :=
  ![![0, 0, 1, 2, 2, 1], ![0, 1, 1, 0, 2, 2], ![0, 2, 1, 1, 2, 0], ![0, 1, 2, 0, 1, 2]]

/-- The hexagon edge colours completing the four target words: entry `q` colours the edge
between positions `q` and `q + 1`. -/
def tabX : Fin 4 → Fin 6 → Fin 3 :=
  ![![1, 2, 0, 1, 0, 2], ![2, 0, 2, 1, 0, 1], ![1, 0, 2, 0, 1, 2], ![2, 0, 1, 2, 0, 1]]

theorem tab_proper (k : Fin 4) (q : Fin 6) :
    tabX k q ≠ tabW k q ∧ tabX k q ≠ tabW k (q + 1) ∧ tabX k q ≠ tabX k (q + 1) := by
  revert k q
  decide

/-- Unordered pair test. -/
def pr (a b q q' : Fin 6) : Prop := (q = a ∧ q' = b) ∨ (q = b ∧ q' = a)

instance (a b q q' : Fin 6) : Decidable (pr a b q q') := by unfold pr; infer_instance

/-- The positions on which each target word takes equal values. -/
theorem tab_eq_pairs (k : Fin 4) (q q' : Fin 6) (h : tabW k q = tabW k q') (hne : q ≠ q') :
    pr 0 1 q q' ∨ pr 2 3 q q' ∨ pr 4 5 q q' ∨
    (k = 0 ∧ (pr 2 5 q q' ∨ pr 3 4 q q')) ∨
    (k = 1 ∧ (pr 0 3 q q' ∨ pr 1 2 q q')) ∨
    (k = 2 ∧ (pr 0 5 q q' ∨ pr 1 4 q q')) ∨
    (k = 3 ∧ (pr 0 3 q q' ∨ pr 1 4 q q' ∨ pr 2 5 q q')) := by
  revert k q q'
  decide

theorem hexWord_add (r j q : Fin 6) (hj : (j + r).val % 2 = 0) :
    hexWord (j + q + r) = hexWord (j + r) + hexWord q := by
  revert r j q
  decide

/-- Core of the partition lemma: if none of the four target words is available, the
partition is the exceptional one. -/
theorem relation_core (s : Fin 6 → Fin 6 → Prop) (hsymm : ∀ a b, s a b → s b a)
    (htrans : ∀ a b c, s a b → s b c → s a c)
    (h01 : ¬ s 0 1) (h23 : ¬ s 2 3) (h45 : ¬ s 4 5)
    (hA : s 2 5 ∨ s 3 4) (hB : s 0 3 ∨ s 1 2) (hC : s 0 5 ∨ s 1 4)
    (hD : s 0 3 ∨ s 1 4 ∨ s 2 5) : s 0 3 ∧ s 1 4 ∧ s 2 5 := by
  rcases hA with h25 | h34 <;> rcases hB with h03 | h12 <;> rcases hC with h05 | h14
  · exact absurd (htrans _ _ _ h25 (htrans _ _ _ (hsymm _ _ h05) h03)) h23
  · rcases hD with h | h | h
    · exact ⟨h03, h14, h25⟩
    · exact ⟨h03, h14, h25⟩
    · exact ⟨h03, h14, h25⟩
  · exact absurd (htrans _ _ _ h05 (htrans _ _ _ (hsymm _ _ h25) (hsymm _ _ h12))) h01
  · exact absurd (htrans _ _ _ (hsymm _ _ h14) (htrans _ _ _ h12 h25)) h45
  · exact absurd (htrans _ _ _ (hsymm _ _ h34) (htrans _ _ _ (hsymm _ _ h03) h05)) h45
  · exact absurd (htrans _ _ _ h03 (htrans _ _ _ h34 (hsymm _ _ h14))) h01
  · rcases hD with h | h | h
    · exact absurd (htrans _ _ _ (hsymm _ _ h34) (htrans _ _ _ (hsymm _ _ h) h05)) h45
    · exact absurd (htrans _ _ _ (hsymm _ _ h12) (htrans _ _ _ h (hsymm _ _ h34))) h23
    · exact absurd (htrans _ _ _ h05 (htrans _ _ _ (hsymm _ _ h) (hsymm _ _ h12))) h01
  · exact absurd (htrans _ _ _ (hsymm _ _ h12) (htrans _ _ _ h14 (hsymm _ _ h34))) h23

/-- **Partition lemma.**  For an equivalence relation on the six spoke positions separating the
three equal-colour pairs and different from the opposite-pair partition, one of the four target
words is injective on every class. -/
theorem exists_table_word (s : Fin 6 → Fin 6 → Prop) (hsymm : ∀ a b, s a b → s b a)
    (htrans : ∀ a b c, s a b → s b c → s a c)
    (h01 : ¬ s 0 1) (h23 : ¬ s 2 3) (h45 : ¬ s 4 5) (hexc : ¬ (s 0 3 ∧ s 1 4 ∧ s 2 5)) :
    ∃ k : Fin 4, ∀ q q', q ≠ q' → tabW k q = tabW k q' → ¬ s q q' := by
  have hpr : ∀ a b q q', pr a b q q' → ¬ s a b → ¬ s q q' := by
    rintro a b q q' (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) hab
    · exact hab
    · exact fun h ↦ hab (hsymm _ _ h)
  by_cases hW1 : ¬ s 2 5 ∧ ¬ s 3 4
  · refine ⟨0, fun q q' hne h ↦ ?_⟩
    rcases tab_eq_pairs 0 q q' h hne with h | h | h | ⟨-, h | h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact hpr _ _ _ _ h h01
    · exact hpr _ _ _ _ h h23
    · exact hpr _ _ _ _ h h45
    · exact hpr _ _ _ _ h hW1.1
    · exact hpr _ _ _ _ h hW1.2
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  by_cases hW2 : ¬ s 0 3 ∧ ¬ s 1 2
  · refine ⟨1, fun q q' hne h ↦ ?_⟩
    rcases tab_eq_pairs 1 q q' h hne with h | h | h | ⟨h, -⟩ | ⟨-, h | h⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact hpr _ _ _ _ h h01
    · exact hpr _ _ _ _ h h23
    · exact hpr _ _ _ _ h h45
    · exact absurd h (by decide)
    · exact hpr _ _ _ _ h hW2.1
    · exact hpr _ _ _ _ h hW2.2
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  by_cases hW3 : ¬ s 0 5 ∧ ¬ s 1 4
  · refine ⟨2, fun q q' hne h ↦ ?_⟩
    rcases tab_eq_pairs 2 q q' h hne with h | h | h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h | h⟩ | ⟨h, -⟩
    · exact hpr _ _ _ _ h h01
    · exact hpr _ _ _ _ h h23
    · exact hpr _ _ _ _ h h45
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact hpr _ _ _ _ h hW3.1
    · exact hpr _ _ _ _ h hW3.2
    · exact absurd h (by decide)
  by_cases hW4 : ¬ s 0 3 ∧ ¬ s 1 4 ∧ ¬ s 2 5
  · refine ⟨3, fun q q' hne h ↦ ?_⟩
    rcases tab_eq_pairs 3 q q' h hne with h | h | h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h | h | h⟩
    · exact hpr _ _ _ _ h h01
    · exact hpr _ _ _ _ h h23
    · exact hpr _ _ _ _ h h45
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact hpr _ _ _ _ h hW4.1
    · exact hpr _ _ _ _ h hW4.2.1
    · exact hpr _ _ _ _ h hW4.2.2
  exfalso
  apply hexc
  exact relation_core s hsymm htrans h01 h23 h45
    ((not_and_or.mp hW1).imp not_not.mp not_not.mp)
    ((not_and_or.mp hW2).imp not_not.mp not_not.mp)
    ((not_and_or.mp hW3).imp not_not.mp not_not.mp)
    ((not_and_or.mp hW4).imp not_not.mp (fun h ↦ (not_and_or.mp h).imp not_not.mp not_not.mp))

theorem equal_pair_of_hexWord_eq (r i i' : Fin 6) (h : hexWord (i + r) = hexWord (i' + r))
    (hne : i ≠ i') :
    (i' = i + 1 ∧ (i + r).val % 2 = 0) ∨ (i = i' + 1 ∧ (i' + r).val % 2 = 0) := by
  revert r i i'
  decide

theorem pairAt_add_two (r j : Fin 6) (hj : (j + r).val % 2 = 0) : (j + 2 + r).val % 2 = 0 := by
  revert r j
  decide

theorem pairAt_add_four (r j : Fin 6) (hj : (j + r).val % 2 = 0) : (j + 4 + r).val % 2 = 0 := by
  revert r j
  decide

end Table

section FreeVertices

variable (X : H.Hexagon) (C : H.OrdinaryCircuit)

/-- Vertices off the circuit and off the hexagon. -/
def IsFree (w : V) : Prop := w ∉ H.edgeSupport C.edges ∧ ∀ i, w ≠ X.v i

instance (w : V) : Decidable (X.IsFree C w) := by
  unfold IsFree
  infer_instance

omit [DecidableEq E] in
theorem freeConn_refl (u : V) : X.FreeConn C u u := fun _ _ ↦ rfl

omit [DecidableEq E] in
theorem freeConn_symm {u w : V} (h : X.FreeConn C u w) : X.FreeConn C w u :=
  fun c hc ↦ (h c hc).symm

omit [DecidableEq E] in
theorem freeConn_trans {u w z : V} (h₁ : X.FreeConn C u w) (h₂ : X.FreeConn C w z) :
    X.FreeConn C u z :=
  fun c hc ↦ (h₁ c hc).trans (h₂ c hc)

omit [DecidableEq E] in
theorem freeConn_of_freeEdge {e : E} (he : e ∈ X.freeEdges C) :
    X.FreeConn C (H.endAt e 0) (H.endAt e 1) :=
  fun _ hc ↦ hc e he

theorem mem_freeEdges_of_isFree {e : E} (h0 : X.IsFree C (H.endAt e 0))
    (h1 : X.IsFree C (H.endAt e 1)) : e ∈ X.freeEdges C := by
  rw [X.mem_freeEdges]
  intro k
  rcases fin2_cases k with rfl | rfl
  · exact h0
  · exact h1

open Classical in
/-- The spoke positions whose outer end is joined to `w`. -/
noncomputable def block (w : V) : Finset (Fin 6) :=
  Finset.univ.filter fun i ↦ X.FreeConn C (X.far i) w

omit [DecidableEq E] in
theorem mem_block {w : V} {i : Fin 6} : i ∈ X.block C w ↔ X.FreeConn C (X.far i) w := by
  simp [block]

omit [DecidableEq E] in
theorem block_eq_of_freeConn {u w : V} (h : X.FreeConn C u w) : X.block C u = X.block C w := by
  ext i
  rw [X.mem_block, X.mem_block]
  exact ⟨fun h' ↦ X.freeConn_trans C h' h, fun h' ↦ X.freeConn_trans C h' (X.freeConn_symm C h)⟩

omit [DecidableEq E] in
theorem mem_block_far (i : Fin 6) : i ∈ X.block C (X.far i) :=
  (X.mem_block C).mpr (X.freeConn_refl C _)

omit [DecidableEq E] in
theorem freeConn_of_mem_block {w : V} {i i' : Fin 6} (hi : i ∈ X.block C w)
    (hi' : i' ∈ X.block C w) : X.FreeConn C (X.far i) (X.far i') :=
  X.freeConn_trans C ((X.mem_block C).mp hi) (X.freeConn_symm C ((X.mem_block C).mp hi'))

end FreeVertices

section Recolour

variable {X : H.Hexagon} (C : H.OrdinaryCircuit) (g : X.ExteriorColoring) (j : Fin 6) (k : Fin 4)

/-- Pair-colour indices to colour indices: the first pair has colour index `hexWord (j + r)`. -/
def pc (m : Fin 3) : Fin 3 := hexWord (j + g.r) + m

omit [DecidableEq V] [DecidableEq E] in
theorem pc_injective : Function.Injective (pc g j) := fun _ _ h ↦ add_left_cancel h

/-- The original spoke word. -/
def origWord (i : Fin 6) : Fin 3 := hexWord (i + g.r)

/-- The target spoke word from table row `k`, read from pair position `j`. -/
def targetWord (i : Fin 6) : Fin 3 := pc g j (tabW k (i - j))

/-- The hexagon edge colours from table row `k`. -/
def edgeWord (i : Fin 6) : Fin 3 := pc g j (tabX k (i - j))

omit [DecidableEq V] [DecidableEq E] in
/-- A colour permutation realising the target word on a block. -/
theorem exists_blockPerm (B : Finset (Fin 6))
    (hB : ∀ i ∈ B, ∀ i' ∈ B, origWord g i = origWord g i' ↔ targetWord g j k i = targetWord g j k i') :
    ∃ π : Equiv.Perm (Fin 3), ∀ i ∈ B, π (origWord g i) = targetWord g j k i := by
  classical
  let f : Fin 3 → Fin 3 := fun a ↦
    if h : ∃ i ∈ B, origWord g i = a then targetWord g j k h.choose else a
  have hf : ∀ i ∈ B, f (origWord g i) = targetWord g j k i := by
    intro i hi
    have h : ∃ i' ∈ B, origWord g i' = origWord g i := ⟨i, hi, rfl⟩
    simp only [f, dif_pos h]
    exact (hB _ h.choose_spec.1 i hi).mp h.choose_spec.2
  have hinj : Set.InjOn f (B.image (origWord g)) := by
    intro a ha b hb hab
    rw [Finset.mem_coe] at ha hb
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hb
    rw [hf i hi, hf i' hi'] at hab
    exact (hB i hi i' hi').mpr hab
  obtain ⟨e, he⟩ := Finset.exists_equiv_extend_of_card_eq (t := (Finset.univ : Finset (Fin 3)))
    (by simp) (s := B.image (origWord g)) (f := f) (Finset.subset_univ _) hinj
  refine ⟨e.trans (Equiv.subtypeUnivEquiv (fun x ↦ Finset.mem_univ x)), fun i hi ↦ ?_⟩
  show (e (origWord g i)).1 = _
  rw [he _ (Finset.mem_image_of_mem _ hi), hf i hi]

/-- The block permutation, or the identity when the block condition fails. -/
noncomputable def blockPerm (B : Finset (Fin 6)) : Equiv.Perm (Fin 3) :=
  if h : ∀ i ∈ B, ∀ i' ∈ B,
      origWord g i = origWord g i' ↔ targetWord g j k i = targetWord g j k i' then
    (exists_blockPerm g j k B h).choose
  else 1

omit [DecidableEq V] [DecidableEq E] in
theorem blockPerm_spec (B : Finset (Fin 6))
    (hB : ∀ i ∈ B, ∀ i' ∈ B, origWord g i = origWord g i' ↔ targetWord g j k i = targetWord g j k i') :
    ∀ i ∈ B, blockPerm g j k B (origWord g i) = targetWord g j k i := by
  unfold blockPerm
  rw [dif_pos hB]
  exact (exists_blockPerm g j k B hB).choose_spec

/-- The colour permutation applied around a vertex. -/
noncomputable def vertexPerm (w : V) : Equiv.Perm (Fin 3) := blockPerm g j k (X.block C w)

/-- The colour permutation applied to an edge: that of its free end. -/
noncomputable def edgePerm (e : E) : Equiv.Perm (Fin 3) :=
  if X.IsFree C (H.endAt e 0) then vertexPerm C g j k (H.endAt e 0)
  else if X.IsFree C (H.endAt e 1) then vertexPerm C g j k (H.endAt e 1) else 1

theorem edgePerm_eq_vertexPerm {e : E} {w : V} (hw : X.IsFree C w) {kk : Fin 2}
    (hk : H.endAt e kk = w) : edgePerm C g j k e = vertexPerm C g j k w := by
  unfold edgePerm
  by_cases h0 : X.IsFree C (H.endAt e 0)
  · rw [if_pos h0]
    rcases fin2_cases kk with rfl | rfl
    · rw [hk]
    · have h1 : X.IsFree C (H.endAt e 1) := by
        rw [hk]
        exact hw
      have he : e ∈ X.freeEdges C := X.mem_freeEdges_of_isFree C h0 h1
      unfold vertexPerm
      rw [X.block_eq_of_freeConn C (X.freeConn_of_freeEdge C he), hk]
  · rw [if_neg h0]
    rcases fin2_cases kk with rfl | rfl
    · exact absurd (hk ▸ hw) h0
    · have h1 : X.IsFree C (H.endAt e 1) := by
        rw [hk]
        exact hw
      rw [if_pos h1, hk]

/-- The recoloured non-hexagon edges. -/
noncomputable def recolour (e : E) : Color :=
  if ∀ i, e ≠ X.h i then g.c (edgePerm C g j k e (g.idx (g.color e))) else g.color e

/-- The recoloured graph, with the hexagon edges coloured from the table. -/
noncomputable def recolourFull (e : E) : Color :=
  if hi : ∃ i, e = X.h i then g.c (edgeWord g j k hi.choose) else recolour C g j k e

theorem recolourFull_h (i : Fin 6) : recolourFull C g j k (X.h i) = g.c (edgeWord g j k i) := by
  have hi : ∃ i', X.h i = X.h i' := ⟨i, rfl⟩
  unfold recolourFull
  rw [dif_pos hi]
  congr 2
  exact X.h_injective hi.choose_spec.symm

theorem recolourFull_of_not_h {e : E} (he : ∀ i, e ≠ X.h i) :
    recolourFull C g j k e = g.c (edgePerm C g j k e (g.idx (g.color e))) := by
  unfold recolourFull recolour
  rw [dif_neg (fun ⟨i, hi⟩ ↦ he i hi), if_pos he]

theorem recolourFull_ne_zero (e : E) : recolourFull C g j k e ≠ 0 := by
  by_cases he : ∃ i, e = X.h i
  · obtain ⟨i, rfl⟩ := he
    rw [recolourFull_h]
    exact g.c_ne_zero _
  · push Not at he
    rw [recolourFull_of_not_h C g j k he]
    exact g.c_ne_zero _

omit [DecidableEq E] in
/-- The block condition holds on every block when the pairs are separated and the target word
is injective on classes. -/
theorem block_condition
    (hpairs : ∀ i, g.PairAt i → ¬ X.FreeConn C (X.far i) (X.far (i + 1)))
    (hinj : ∀ q q', q ≠ q' → tabW k q = tabW k q' →
      ¬ X.FreeConn C (X.far (j + q)) (X.far (j + q')))
    (w : V) : ∀ i ∈ X.block C w, ∀ i' ∈ X.block C w,
      origWord g i = origWord g i' ↔ targetWord g j k i = targetWord g j k i' := by
  intro i hi i' hi'
  by_cases hii : i = i'
  · subst hii
    exact iff_of_true rfl rfl
  have hconn : X.FreeConn C (X.far i) (X.far i') := X.freeConn_of_mem_block C hi hi'
  constructor
  · intro h
    exfalso
    rcases equal_pair_of_hexWord_eq g.r i i' h hii with ⟨rfl, hp⟩ | ⟨rfl, hp⟩
    · exact hpairs i hp hconn
    · exact hpairs i' hp (X.freeConn_symm C hconn)
  · intro h
    exfalso
    have h' : tabW k (i - j) = tabW k (i' - j) := pc_injective g j h
    have hne : i - j ≠ i' - j := fun h ↦ hii (sub_left_injective h)
    have := hinj _ _ hne h'
    rw [add_sub_cancel, add_sub_cancel] at this
    exact this hconn

theorem recolourFull_spoke
    (hpairs : ∀ i, g.PairAt i → ¬ X.FreeConn C (X.far i) (X.far (i + 1)))
    (hinj : ∀ q q', q ≠ q' → tabW k q = tabW k q' →
      ¬ X.FreeConn C (X.far (j + q)) (X.far (j + q')))
    (i : Fin 6) (hfree : X.IsFree C (X.far i)) :
    recolourFull C g j k (X.spoke i) = g.c (targetWord g j k i) := by
  rw [recolourFull_of_not_h C g j k (fun i' ↦ X.spoke_ne_h i i'), g.spoke_color, g.idx_c,
    edgePerm_eq_vertexPerm C g j k hfree (kk := Fin.rev (X.side i)) rfl]
  unfold vertexPerm
  exact congrArg g.c
    (blockPerm_spec g j k _ (block_condition C g j k hpairs hinj _) i (X.mem_block_far C i))

omit [DecidableEq V] [DecidableEq E] in
/-- Distinctness of the three colours at a hexagon vertex. -/
theorem table_distinct (i : Fin 6) :
    edgeWord g j k i ≠ targetWord g j k i ∧ edgeWord g j k (i - 1) ≠ targetWord g j k i ∧
      edgeWord g j k (i - 1) ≠ edgeWord g j k i := by
  have hq : i - 1 - j + 1 = i - j := by
    rw [sub_right_comm, sub_add_cancel]
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact (tab_proper k (i - j)).1 (pc_injective g j h)
  · intro h
    have := (tab_proper k (i - 1 - j)).2.1
    rw [hq] at this
    exact this (pc_injective g j h)
  · intro h
    have := (tab_proper k (i - 1 - j)).2.2
    rw [hq] at this
    exact this (pc_injective g j h)

/-- The recoloured graph is properly coloured off the circuit. -/
theorem recolourFull_properOff (hCubic : ∀ v : V, H.degree v = 3)
    (hpairs : ∀ i, g.PairAt i → ¬ X.FreeConn C (X.far i) (X.far (i + 1)))
    (hinj : ∀ q q', q ≠ q' → tabW k q = tabW k q' →
      ¬ X.FreeConn C (X.far (j + q)) (X.far (j + q'))) :
    H.ProperOff (H.edgeSupport C.edges) (recolourFull C g j k) := by
  refine ⟨fun e _ ↦ recolourFull_ne_zero C g j k e, ?_⟩
  intro w hw x y hx hy heq
  by_cases hwv : ∃ i, X.v i = w
  · obtain ⟨i, rfl⟩ := hwv
    have v0 : recolourFull C g j k (X.hex0 i).1.1 = g.c (edgeWord g j k i) :=
      recolourFull_h C g j k i
    have v1 : recolourFull C g j k (X.hex1 i).1.1 = g.c (edgeWord g j k (i - 1)) :=
      recolourFull_h C g j k (i - 1)
    have v2 : ∀ z : H.halfEdgesAt (X.v i), z = X.spokeHalf i →
        (∀ kk, H.endAt z.1.1 kk ∉ H.edgeSupport C.edges) →
        recolourFull C g j k z.1.1 = g.c (targetWord g j k i) := by
      rintro z rfl hz
      exact recolourFull_spoke C g j k hpairs hinj i
        ⟨hz (Fin.rev (X.side i)), fun i' ↦ X.far_ne_v i i'⟩
    obtain ⟨d1, d2, d3⟩ := table_distinct g j k i
    have hcases := X.halfEdge_cases hCubic i
    rcases hcases x with hx' | hx' | hx' <;> rcases hcases y with hy' | hy' | hy'
    · exact hx'.trans hy'.symm
    · rw [hx', hy', v0, v1] at heq
      exact absurd (g.c_injective heq).symm d3
    · rw [hx', v0, v2 y hy' hy] at heq
      exact absurd (g.c_injective heq) d1
    · rw [hx', hy', v1, v0] at heq
      exact absurd (g.c_injective heq) d3
    · exact hx'.trans hy'.symm
    · rw [hx', v1, v2 y hy' hy] at heq
      exact absurd (g.c_injective heq) d2
    · rw [hy', v2 x hx' hx, v0] at heq
      exact absurd (g.c_injective heq).symm d1
    · rw [hy', v2 x hx' hx, v1] at heq
      exact absurd (g.c_injective heq).symm d2
    · exact hx'.trans hy'.symm
  · push Not at hwv
    have hfree : X.IsFree C w := ⟨hw, fun i h ↦ hwv i h.symm⟩
    have hwv' : ∀ i, w ≠ X.v i := fun i h ↦ hwv i h.symm
    have hxh := ExteriorColoring.halfEdge_not_h hwv' x
    have hyh := ExteriorColoring.halfEdge_not_h hwv' y
    rw [recolourFull_of_not_h C g j k hxh, recolourFull_of_not_h C g j k hyh,
      edgePerm_eq_vertexPerm C g j k hfree x.2, edgePerm_eq_vertexPerm C g j k hfree y.2] at heq
    have h1 := (vertexPerm C g j k w).injective (g.c_injective heq)
    have h2 := congrArg g.c h1
    rw [g.c_idx (g.nonzero _ hxh), g.c_idx (g.nonzero _ hyh)] at h2
    exact g.injective_at w x y hxh hyh h2

/-- **Recolouring case.**  When no equal-colour pair is joined off `C ∪ H` and the opposite
pairs are not all joined, the exterior colouring can be permuted on the components so that the
hexagon becomes colourable, and `C` is an entire member of a five-cycle double cover. -/
theorem exists_fiveCycleDoubleCover_of_recolour (hCubic : ∀ v : V, H.degree v = 3)
    (hj : g.PairAt j)
    (hpairs : ∀ i, g.PairAt i → ¬ X.FreeConn C (X.far i) (X.far (i + 1)))
    (hexc : ¬ (X.FreeConn C (X.far j) (X.far (j + 3)) ∧
      X.FreeConn C (X.far (j + 1)) (X.far (j + 4)) ∧
      X.FreeConn C (X.far (j + 2)) (X.far (j + 5)))) :
    ∃ D : H.CycleDoubleCover 5, D.Contains C.edges := by
  obtain ⟨k, hk⟩ := exists_table_word (fun q q' ↦ X.FreeConn C (X.far (j + q)) (X.far (j + q')))
    (fun _ _ h ↦ X.freeConn_symm C h) (fun _ _ _ h₁ h₂ ↦ X.freeConn_trans C h₁ h₂)
    (by
      have := hpairs j hj
      simpa using this)
    (by
      have := hpairs (j + 2) (pairAt_add_two g.r j hj)
      simpa [add_assoc] using this)
    (by
      have := hpairs (j + 4) (pairAt_add_four g.r j hj)
      simpa [add_assoc] using this)
    (by simpa using hexc)
  exact C.toTraversedCircuit.exists_fiveCycleDoubleCover_of_properOff hCubic
    (recolourFull_properOff C g j k hCubic hpairs hk)

end Recolour

section Assembly

variable {X : H.Hexagon}

private theorem fin6_cases_of_offset (i j : Fin 6) :
    i = j ∨ i = j + 1 ∨ i = j + 2 ∨ i = j + 3 ∨ i = j + 4 ∨ i = j + 5 := by
  revert i j
  decide

/-- **A circuit disjoint from the hexagon.**  Either the circuit is an entire member of a
five-cycle double cover, or there are six even layers with the circuit and the hexagon entire
and five even layers with their union entire. -/
theorem exists_cover_of_disjoint (hCubic : ∀ v : V, H.degree v = 3) (g : X.ExteriorColoring)
    (C : H.OrdinaryCircuit) (hC : ∀ i, X.v i ∉ H.edgeSupport C.edges) :
    (∃ D : H.CycleDoubleCover 5, D.Contains C.edges) ∨
      ((∃ D : H.CycleDoubleCover 6, D.Contains C.edges ∧ D.Contains X.edgeSet) ∧
        ∃ D : H.CycleDoubleCover 5, D.Contains (C.edges ∪ X.edgeSet)) := by
  obtain ⟨j, hj⟩ := exists_pairAt g.r
  by_cases hpair : ∃ i, g.PairAt i ∧ X.FreeConn C (X.far i) (X.far (i + 1))
  · obtain ⟨i, hi, hconn⟩ := hpair
    exact Or.inr (exists_sixCover_of_pair_conn g C hCubic hC i hi hconn)
  push Not at hpair
  by_cases hopp : X.FreeConn C (X.far j) (X.far (j + 3)) ∧
      X.FreeConn C (X.far (j + 1)) (X.far (j + 4)) ∧
      X.FreeConn C (X.far (j + 2)) (X.far (j + 5))
  · right
    apply exists_sixCover_of_opposite_conn g C hCubic hC
    intro i
    have e1 : j + 1 + 3 = j + 4 := by rw [add_assoc]; rfl
    have e2 : j + 2 + 3 = j + 5 := by rw [add_assoc]; rfl
    have e3 : j + 3 + 3 = j := by rw [add_assoc]; exact add_zero j
    have e4 : j + 4 + 3 = j + 1 := by rw [add_assoc]; rfl
    have e5 : j + 5 + 3 = j + 2 := by rw [add_assoc]; rfl
    rcases fin6_cases_of_offset i j with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hopp.1
    · rw [e1]
      exact hopp.2.1
    · rw [e2]
      exact hopp.2.2
    · rw [e3]
      exact X.freeConn_symm C hopp.1
    · rw [e4]
      exact X.freeConn_symm C hopp.2.1
    · rw [e5]
      exact X.freeConn_symm C hopp.2.2
  · left
    exact exists_fiveCycleDoubleCover_of_recolour C g j hCubic hj hpair hopp

/-- The intersection pattern of a circuit meeting the hexagon of a cubic graph: at least three
common vertices, or exactly the two ends of a hexagon edge. -/
theorem meet_cases (hCubic : ∀ v : V, H.degree v = 3) (C : H.OrdinaryCircuit)
    (hmeet : ∃ i, X.v i ∈ H.edgeSupport C.edges) :
    3 ≤ (X.onCircuit C).card ∨
      ∃ j, ∀ i, X.v i ∈ H.edgeSupport C.edges ↔ (i = j ∨ i = j + 1) := by
  have hmemT : ∀ i, i ∈ X.onCircuit C ↔ X.v i ∈ H.edgeSupport C.edges := fun i ↦ by
    simp [onCircuit]
  by_cases h3 : 3 ≤ (X.onCircuit C).card
  · exact Or.inl h3
  · right
    push Not at h3
    obtain ⟨i, hi⟩ := hmeet
    have hiT : i ∈ X.onCircuit C := (hmemT i).mpr hi
    obtain ⟨j, hj⟩ : ∃ j : Fin 6, X.onCircuit C = {j, j + 1} := by
      rcases X.neighbor_onCircuit hCubic C hi with hl | hr
      · refine ⟨i - 1, (Finset.eq_of_subset_of_card_le ?_ ?_).symm⟩
        · intro k hk
          simp only [Finset.mem_insert, Finset.mem_singleton] at hk
          rcases hk with rfl | rfl
          · exact (hmemT _).mpr hl
          · rw [sub_add_cancel]
            exact hiT
        · rw [Finset.card_pair (fin6_ne_add_one (i - 1))]
          omega
      · refine ⟨i, (Finset.eq_of_subset_of_card_le ?_ ?_).symm⟩
        · intro k hk
          simp only [Finset.mem_insert, Finset.mem_singleton] at hk
          rcases hk with rfl | rfl
          · exact hiT
          · exact (hmemT _).mpr hr
        · rw [Finset.card_pair (fin6_ne_add_one i)]
          omega
    refine ⟨j, fun k ↦ ?_⟩
    rw [← hmemT k, hj]
    simp

end Assembly

section Intersection
private theorem fin6_add_one_add_one_ne (j : Fin 6) : j + 1 + 1 ≠ j := by
  revert j
  decide

private theorem fin6_sub_one_ne (j : Fin 6) : j - 1 ≠ j := by
  revert j
  decide

variable (X : H.Hexagon) (j : Fin 6) (C : H.OrdinaryCircuit)
variable (hT : ∀ i, X.v i ∈ H.edgeSupport C.edges ↔ (i = j ∨ i = j + 1))
include hT

omit [DecidableEq E] in
theorem h_notin_C_of_ne {i : Fin 6} (hi : i ≠ j) : X.h i ∉ C.edges := by
  intro h
  by_cases hi' : i = j + 1
  · subst hi'
    have hmem : X.v (j + 1 + 1) ∈ H.edgeSupport C.edges :=
      H.mem_edgeSupport_iff.mpr ⟨_, h, 1, X.h_end1 _⟩
    rcases (hT _).mp hmem with h' | h'
    · exact fin6_add_one_add_one_ne j h'
    · exact fin6_ne_add_one j (add_right_cancel h').symm
  · have hmem : X.v i ∈ H.edgeSupport C.edges := H.mem_edgeSupport_iff.mpr ⟨_, h, 0, X.h_end0 i⟩
    rcases (hT i).mp hmem with h' | h'
    · exact hi h'
    · exact hi' h'

/-- The shared hexagon edge lies on the circuit. -/
theorem e_mem_C (hCubic : ∀ v : V, H.degree v = 3) : X.h j ∈ C.edges := by
  by_contra he
  have hu : X.v j ∈ H.edgeSupport C.edges := (hT j).mpr (Or.inl rfl)
  have h2 : H.degreeIn C.edges (X.v j) = 2 := C.twoRegular _ hu
  rw [H.degreeIn_eq_card_halfEdges] at h2
  have hsub : (Finset.univ.filter fun x : H.halfEdgesAt (X.v j) ↦ x.1.1 ∈ C.edges) ⊆
      {X.spokeHalf j} := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rcases X.halfEdge_cases hCubic j x with rfl | rfl | rfl
    · exact absurd hx.2 he
    · exact absurd hx.2 (X.h_notin_C_of_ne j C hT (fin6_sub_one_ne j))
    · exact Finset.mem_singleton_self _
  have := Finset.card_le_card hsub
  rw [Finset.card_singleton] at this
  omega

end Intersection

/-- The hexagon is an even edge set. -/
theorem edgeSet_even (hCubic : ∀ v, H.degree v = 3) : H.IsEvenEdgeSet X.edgeSet := by
  intro w
  change H.boundary X.edgeSet w = 0
  by_cases hw : ∃ i, X.v i = w
  · obtain ⟨i, rfl⟩ := hw
    rw [X.boundary_at_vertex hCubic, if_pos (X.h_mem_edgeSet i), if_pos (X.h_mem_edgeSet (i - 1)),
      if_neg (X.spoke_notin_edgeSet i)]
    decide
  · push Not at hw
    exact X.boundary_eq_zero_of_subset_edgeSet subset_rfl (fun i h ↦ hw i h.symm)

end Hexagon

end LoopMultigraph
end GraphPuzzles
