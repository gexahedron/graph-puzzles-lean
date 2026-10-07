import GraphPuzzles.Core.Color

/-!
# Finite labelled multigraphs on natural-number labels

A `FinGraph` is a finite set of vertex labels, a finite set of edge labels, and an endpoint
function.  An edge with an end outside the vertex set is *dangling*; a graph without dangling
edges is *closed*.  Restricting a closed graph to a vertex set `X` (keeping the boundary edges)
produces a multipole in which the boundary edges are dangling.  All constructions of the
factorisation theory (completions, quotients, dot products) are finite-set operations on labels,
so isomorphisms between the results can be written down explicitly.

This file records the basic counting facts: half-edge degrees, the handshake identity
`∑ deg = 2 |E(X)| + |∂X|`, submodularity of the boundary size, and the forest bound
`|E(X)| < |X|` for vertex sets spanning no even edge set (by an `F₂` rank argument).
-/

namespace GraphPuzzles

/-- A finite labelled multigraph on natural-number labels. -/
structure FinGraph where
  /-- The vertex labels. -/
  Vs : Finset ℕ
  /-- The edge labels. -/
  Es : Finset ℕ
  /-- The two numbered ends of every edge label. -/
  ends : ℕ → Fin 2 → ℕ

namespace FinGraph

open Finset

variable (Γ : FinGraph)

/-- Half-edges: an edge label with one of its two numbered ends. -/
def halfEdges : Finset (ℕ × Fin 2) := Γ.Es ×ˢ Finset.univ

/-- The half-edges of an edge set at a vertex. -/
def halfEdgesIn (F : Finset ℕ) (v : ℕ) : Finset (ℕ × Fin 2) :=
  (F ×ˢ (Finset.univ : Finset (Fin 2))).filter fun h ↦ Γ.ends h.1 h.2 = v

/-- The degree of a vertex inside an edge set (half-edge incidences). -/
def degIn (F : Finset ℕ) (v : ℕ) : ℕ := (Γ.halfEdgesIn F v).card

/-- The degree of a vertex. -/
def deg (v : ℕ) : ℕ := Γ.degIn Γ.Es v

/-- Every vertex label has degree three. -/
def IsCubic : Prop := ∀ v ∈ Γ.Vs, Γ.deg v = 3

/-- No dangling edges: every end of every edge is a vertex label. -/
def IsClosed : Prop := ∀ e ∈ Γ.Es, ∀ i, Γ.ends e i ∈ Γ.Vs

/-- The edges with both ends in `X`. -/
def edgesIn (X : Finset ℕ) : Finset ℕ := Γ.Es.filter fun e ↦ ∀ i, Γ.ends e i ∈ X

/-- The boundary of `X`: edges with exactly one end in `X`. -/
def bd (X : Finset ℕ) : Finset ℕ :=
  Γ.Es.filter fun e ↦ ¬ ((Γ.ends e 0 ∈ X) ↔ (Γ.ends e 1 ∈ X))

/-- An even edge set: every vertex has even degree in it. -/
def IsEven (F : Finset ℕ) : Prop := ∀ v ∈ Γ.Vs, Even (Γ.degIn F v)

/-- `X` spans a nonempty even edge set (equivalently, a cycle). -/
def HasCycle (X : Finset ℕ) : Prop := ∃ F ⊆ Γ.edgesIn X, F.Nonempty ∧ Γ.IsEven F

variable {Γ}

theorem mem_halfEdgesIn {F : Finset ℕ} {v : ℕ} {h : ℕ × Fin 2} :
    h ∈ Γ.halfEdgesIn F v ↔ h.1 ∈ F ∧ Γ.ends h.1 h.2 = v := by
  simp [halfEdgesIn]

theorem mem_edgesIn {X : Finset ℕ} {e : ℕ} : e ∈ Γ.edgesIn X ↔ e ∈ Γ.Es ∧ ∀ i, Γ.ends e i ∈ X := by
  simp [edgesIn]

theorem mem_bd {X : Finset ℕ} {e : ℕ} :
    e ∈ Γ.bd X ↔ e ∈ Γ.Es ∧ ¬ ((Γ.ends e 0 ∈ X) ↔ (Γ.ends e 1 ∈ X)) := by
  simp [bd]

theorem edgesIn_subset (X : Finset ℕ) : Γ.edgesIn X ⊆ Γ.Es := Finset.filter_subset _ _

theorem bd_subset (X : Finset ℕ) : Γ.bd X ⊆ Γ.Es := Finset.filter_subset _ _

theorem edgesIn_mono {X Y : Finset ℕ} (h : X ⊆ Y) : Γ.edgesIn X ⊆ Γ.edgesIn Y := by
  intro e he
  rw [mem_edgesIn] at he ⊢
  exact ⟨he.1, fun i ↦ h (he.2 i)⟩

theorem disjoint_edgesIn_bd (X : Finset ℕ) : Disjoint (Γ.edgesIn X) (Γ.bd X) := by
  rw [Finset.disjoint_left]
  intro e he hb
  rw [mem_edgesIn] at he
  rw [mem_bd] at hb
  exact hb.2 ⟨fun _ ↦ he.2 1, fun _ ↦ he.2 0⟩

theorem HasCycle.mono {X Y : Finset ℕ} (h : X ⊆ Y) (hX : Γ.HasCycle X) : Γ.HasCycle Y := by
  obtain ⟨F, hF, hne, hev⟩ := hX
  exact ⟨F, hF.trans (edgesIn_mono h), hne, hev⟩

/-- The two ends of an edge with exactly one end in `X`, distinguished by side. -/
theorem bd_side {X : Finset ℕ} {e : ℕ} (he : e ∈ Γ.bd X) :
    ∃ i : Fin 2, Γ.ends e i ∈ X ∧ Γ.ends e (Fin.rev i) ∉ X := by
  rw [mem_bd] at he
  by_cases h0 : Γ.ends e 0 ∈ X
  · exact ⟨0, h0, fun h1 ↦ he.2 ⟨fun _ ↦ h1, fun _ ↦ h0⟩⟩
  · refine ⟨1, ?_, h0⟩
    by_contra h1
    exact he.2 ⟨fun h ↦ (h0 h).elim, fun h ↦ (h1 h).elim⟩

/-- For a closed graph the boundary of the complement is the boundary. -/
theorem bd_compl (hc : Γ.IsClosed) (X : Finset ℕ) : Γ.bd (Γ.Vs \ X) = Γ.bd X := by
  ext e
  simp only [mem_bd, Finset.mem_sdiff]
  constructor
  · rintro ⟨he, h⟩
    refine ⟨he, fun h' ↦ h ?_⟩
    have h0 := hc e he 0
    have h1 := hc e he 1
    tauto
  · rintro ⟨he, h⟩
    refine ⟨he, fun h' ↦ h ?_⟩
    have h0 := hc e he 0
    have h1 := hc e he 1
    tauto

section Handshake

/-- The number of ends of an edge lying in `X`. -/
def endsIn (X : Finset ℕ) (e : ℕ) : ℕ :=
  (Finset.univ.filter fun i : Fin 2 ↦ Γ.ends e i ∈ X).card

theorem endsIn_eq (X : Finset ℕ) (e : ℕ) :
    Γ.endsIn X e = (if Γ.ends e 0 ∈ X then 1 else 0) + (if Γ.ends e 1 ∈ X then 1 else 0) := by
  unfold endsIn
  rw [Finset.card_filter, Fin.sum_univ_two]

theorem sum_degIn_eq (F X : Finset ℕ) : ∑ v ∈ X, Γ.degIn F v = ∑ e ∈ F, Γ.endsIn X e := by
  unfold degIn endsIn
  have : ∀ v ∈ X, (Γ.halfEdgesIn F v).card =
      ∑ e ∈ F, (Finset.univ.filter fun i : Fin 2 ↦ Γ.ends e i = v).card := by
    intro v _
    unfold halfEdgesIn
    rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro e _
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_congr rfl this, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.card_filter, Fin.sum_univ_two]
  have h1 : ∀ i : Fin 2, ∑ x ∈ X, (if Γ.ends e i = x then 1 else 0) =
      if Γ.ends e i ∈ X then 1 else 0 := by
    intro i
    rw [Finset.sum_ite_eq]
  have h2 : ∀ x ∈ X, ((Finset.univ.filter fun i : Fin 2 ↦ Γ.ends e i = x).card) =
      (if Γ.ends e 0 = x then 1 else 0) + (if Γ.ends e 1 = x then 1 else 0) := by
    intro x _
    rw [Finset.card_filter, Fin.sum_univ_two]
  rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib, h1, h1]

theorem endsIn_of_mem_edgesIn {X : Finset ℕ} {e : ℕ} (h : e ∈ Γ.edgesIn X) : Γ.endsIn X e = 2 := by
  rw [mem_edgesIn] at h
  rw [endsIn_eq, if_pos (h.2 0), if_pos (h.2 1)]

theorem endsIn_of_mem_bd {X : Finset ℕ} {e : ℕ} (h : e ∈ Γ.bd X) : Γ.endsIn X e = 1 := by
  rw [mem_bd] at h
  rw [endsIn_eq]
  by_cases h0 : Γ.ends e 0 ∈ X
  · have h1 : Γ.ends e 1 ∉ X := fun h1 ↦ h.2 ⟨fun _ ↦ h1, fun _ ↦ h0⟩
    rw [if_pos h0, if_neg h1]
  · have h1 : Γ.ends e 1 ∈ X := by
      by_contra h1
      exact h.2 ⟨fun h ↦ (h0 h).elim, fun h ↦ (h1 h).elim⟩
    rw [if_neg h0, if_pos h1]

theorem endsIn_of_not_mem {X : Finset ℕ} {e : ℕ} (he : e ∈ Γ.Es) (h1 : e ∉ Γ.edgesIn X)
    (h2 : e ∉ Γ.bd X) : Γ.endsIn X e = 0 := by
  rw [mem_edgesIn] at h1
  rw [mem_bd] at h2
  rw [endsIn_eq]
  by_cases h0 : Γ.ends e 0 ∈ X
  · exfalso
    by_cases hh : Γ.ends e 1 ∈ X
    · exact h1 ⟨he, fun i ↦ by fin_cases i <;> assumption⟩
    · exact h2 ⟨he, fun h ↦ hh (h.mp h0)⟩
  · by_cases hh : Γ.ends e 1 ∈ X
    · exact absurd ⟨he, fun h ↦ h0 (h.mpr hh)⟩ h2
    · rw [if_neg h0, if_neg hh]

/-- The handshake identity for a vertex set. -/
theorem sum_deg_eq (X : Finset ℕ) :
    ∑ v ∈ X, Γ.deg v = 2 * (Γ.edgesIn X).card + (Γ.bd X).card := by
  unfold deg
  rw [sum_degIn_eq]
  have hsub : Γ.edgesIn X ∪ Γ.bd X ⊆ Γ.Es := Finset.union_subset (edgesIn_subset X) (bd_subset X)
  have hsplit : Γ.Es = (Γ.edgesIn X ∪ Γ.bd X) ∪ (Γ.Es \ (Γ.edgesIn X ∪ Γ.bd X)) := by
    rw [Finset.union_sdiff_of_subset hsub]
  rw [hsplit, Finset.sum_union Finset.disjoint_sdiff,
    Finset.sum_union (disjoint_edgesIn_bd X)]
  have hA : ∑ e ∈ Γ.edgesIn X, Γ.endsIn X e = 2 * (Γ.edgesIn X).card := by
    rw [Finset.sum_congr rfl (fun e he ↦ endsIn_of_mem_edgesIn he)]
    simp [mul_comm]
  have hB : ∑ e ∈ Γ.bd X, Γ.endsIn X e = (Γ.bd X).card := by
    rw [Finset.sum_congr rfl (fun e he ↦ endsIn_of_mem_bd he)]
    simp
  have hC : ∑ e ∈ Γ.Es \ (Γ.edgesIn X ∪ Γ.bd X), Γ.endsIn X e = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    rw [Finset.mem_sdiff, Finset.mem_union, not_or] at he
    exact endsIn_of_not_mem he.1 he.2.1 he.2.2
  rw [hA, hB, hC, add_zero]

/-- The handshake identity in a cubic graph. -/
theorem three_mul_card_eq (hcub : Γ.IsCubic) {X : Finset ℕ} (hX : X ⊆ Γ.Vs) :
    3 * X.card = 2 * (Γ.edgesIn X).card + (Γ.bd X).card := by
  rw [← sum_deg_eq, Finset.sum_congr rfl (fun v hv ↦ hcub v (hX hv))]
  simp [mul_comm]

end Handshake

section Submodular

/-- The boundary indicator of an edge. -/
def bdInd (X : Finset ℕ) (e : ℕ) : ℕ := if e ∈ Γ.bd X then 1 else 0

theorem card_bd_eq_sum (X : Finset ℕ) : (Γ.bd X).card = ∑ e ∈ Γ.Es, Γ.bdInd X e := by
  unfold bdInd
  rw [← Finset.sum_filter, Finset.card_eq_sum_ones]
  congr 1
  ext e
  simp only [Finset.mem_filter]
  exact ⟨fun h ↦ ⟨bd_subset X h, h⟩, fun h ↦ h.2⟩

private theorem bool_cases (p : Prop) [Decidable p] : (p ∧ (if p then 1 else 0) = 1) ∨
    (¬ p ∧ (if p then 1 else 0) = 0) := by
  by_cases h : p <;> simp [h]

theorem bdInd_submodular (X Y : Finset ℕ) {e : ℕ} (he : e ∈ Γ.Es) :
    Γ.bdInd (X ∩ Y) e + Γ.bdInd (X ∪ Y) e ≤ Γ.bdInd X e + Γ.bdInd Y e := by
  unfold bdInd
  simp only [mem_bd, he, true_and, Finset.mem_inter, Finset.mem_union]
  by_cases a0 : Γ.ends e 0 ∈ X <;> by_cases a1 : Γ.ends e 1 ∈ X <;>
    by_cases b0 : Γ.ends e 0 ∈ Y <;> by_cases b1 : Γ.ends e 1 ∈ Y <;> simp [a0, a1, b0, b1]

/-- Submodularity of the boundary size. -/
theorem card_bd_inter_add_card_bd_union (X Y : Finset ℕ) :
    (Γ.bd (X ∩ Y)).card + (Γ.bd (X ∪ Y)).card ≤ (Γ.bd X).card + (Γ.bd Y).card := by
  rw [card_bd_eq_sum, card_bd_eq_sum, card_bd_eq_sum, card_bd_eq_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun e he ↦ bdInd_submodular X Y he

end Submodular

end FinGraph

end GraphPuzzles
