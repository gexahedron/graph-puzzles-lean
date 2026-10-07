import GraphPuzzles.FinGraph.FinGraphCompletionIso

/-!
# Edges between two vertex sets

For disjoint vertex sets `X`, `Z` the set `between X Z` consists of the edges with one end in
`X` and the other in `Z`.  The boundary of a union is governed by
`|∂(X ∪ Z)| + 2 |between X Z| = |∂X| + |∂Z|`, the boundary of a subset of a closed graph is the
set of edges between it and its complement, and the edges between `X` and a disjoint union add.
These identities turn the cut arithmetic of the atom theorem into linear arithmetic.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

variable {Γ : FinGraph}

/-- The edges with one end in `X` and the other in `Z`. -/
def between (Γ : FinGraph) (X Z : Finset ℕ) : Finset ℕ :=
  Γ.Es.filter fun e ↦ (Γ.ends e 0 ∈ X ∧ Γ.ends e 1 ∈ Z) ∨ (Γ.ends e 0 ∈ Z ∧ Γ.ends e 1 ∈ X)

theorem mem_between {X Z : Finset ℕ} {e : ℕ} : e ∈ Γ.between X Z ↔
    e ∈ Γ.Es ∧ ((Γ.ends e 0 ∈ X ∧ Γ.ends e 1 ∈ Z) ∨ (Γ.ends e 0 ∈ Z ∧ Γ.ends e 1 ∈ X)) := by
  simp [between]

theorem between_comm (X Z : Finset ℕ) : Γ.between X Z = Γ.between Z X := by
  ext e
  rw [mem_between, mem_between]
  tauto

theorem between_subset (X Z : Finset ℕ) : Γ.between X Z ⊆ Γ.Es := Finset.filter_subset _ _

/-- For a closed graph, the boundary of `X` is the set of edges between `X` and its complement. -/
theorem bd_eq_between (hcl : Γ.IsClosed) (X : Finset ℕ) :
    Γ.bd X = Γ.between X (Γ.Vs \ X) := by
  ext e
  rw [mem_bd, mem_between]
  constructor
  · rintro ⟨he, hiff⟩
    refine ⟨he, ?_⟩
    by_cases h0 : Γ.ends e 0 ∈ X
    · have h1 : Γ.ends e 1 ∉ X := fun h1 ↦ hiff ⟨fun _ ↦ h1, fun _ ↦ h0⟩
      exact Or.inl ⟨h0, Finset.mem_sdiff.mpr ⟨hcl e he 1, h1⟩⟩
    · have h1 : Γ.ends e 1 ∈ X := by
        by_contra h1
        exact hiff ⟨fun h ↦ (h0 h).elim, fun h ↦ (h1 h).elim⟩
      exact Or.inr ⟨Finset.mem_sdiff.mpr ⟨hcl e he 0, h0⟩, h1⟩
  · rintro ⟨he, h⟩
    refine ⟨he, ?_⟩
    rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact fun hiff ↦ (Finset.mem_sdiff.mp h1).2 (hiff.mp h0)
    · exact fun hiff ↦ (Finset.mem_sdiff.mp h0).2 (hiff.mpr h1)

theorem between_union_right {X Z Z' : Finset ℕ} (hXZ : Disjoint X Z) (hXZ' : Disjoint X Z')
    (h : Disjoint Z Z') :
    Γ.between X (Z ∪ Z') = Γ.between X Z ∪ Γ.between X Z' ∧
      Disjoint (Γ.between X Z) (Γ.between X Z') := by
  constructor
  · ext e
    simp only [mem_between, Finset.mem_union]
    constructor
    · rintro ⟨he, h'⟩
      rcases h' with ⟨h0, h1 | h1⟩ | ⟨h0 | h0, h1⟩
      · exact Or.inl ⟨he, Or.inl ⟨h0, h1⟩⟩
      · exact Or.inr ⟨he, Or.inl ⟨h0, h1⟩⟩
      · exact Or.inl ⟨he, Or.inr ⟨h0, h1⟩⟩
      · exact Or.inr ⟨he, Or.inr ⟨h0, h1⟩⟩
    · rintro (⟨he, h'⟩ | ⟨he, h'⟩)
      · exact ⟨he, h'.elim (fun h ↦ Or.inl ⟨h.1, Or.inl h.2⟩) (fun h ↦ Or.inr ⟨Or.inl h.1, h.2⟩)⟩
      · exact ⟨he, h'.elim (fun h ↦ Or.inl ⟨h.1, Or.inr h.2⟩) (fun h ↦ Or.inr ⟨Or.inr h.1, h.2⟩)⟩
  · rw [Finset.disjoint_left]
    intro e h1 h2
    rw [mem_between] at h1 h2
    rcases h1.2 with ⟨a0, a1⟩ | ⟨a0, a1⟩ <;> rcases h2.2 with ⟨b0, b1⟩ | ⟨b0, b1⟩
    · exact Finset.disjoint_left.mp h a1 b1
    · exact Finset.disjoint_left.mp hXZ' a0 b0
    · exact Finset.disjoint_left.mp hXZ b0 a0
    · exact Finset.disjoint_left.mp h a0 b0

theorem card_between_union_right {X Z Z' : Finset ℕ} (hXZ : Disjoint X Z) (hXZ' : Disjoint X Z')
    (h : Disjoint Z Z') :
    (Γ.between X (Z ∪ Z')).card = (Γ.between X Z).card + (Γ.between X Z').card := by
  obtain ⟨h1, h2⟩ := between_union_right (Γ := Γ) hXZ hXZ' h
  rw [h1, Finset.card_union_of_disjoint h2]

/-- The boundary indicator of an edge. -/
def betweenInd (X Z : Finset ℕ) (e : ℕ) : ℕ := if e ∈ Γ.between X Z then 1 else 0

theorem card_between_eq_sum (X Z : Finset ℕ) :
    (Γ.between X Z).card = ∑ e ∈ Γ.Es, Γ.betweenInd X Z e := by
  unfold betweenInd
  rw [← Finset.sum_filter, Finset.card_eq_sum_ones]
  congr 1
  ext e
  simp only [Finset.mem_filter]
  exact ⟨fun h ↦ ⟨between_subset X Z h, h⟩, fun h ↦ h.2⟩

theorem bdInd_union {X Z : Finset ℕ} (hXZ : Disjoint X Z) {e : ℕ} (he : e ∈ Γ.Es) :
    Γ.bdInd (X ∪ Z) e + 2 * Γ.betweenInd X Z e = Γ.bdInd X e + Γ.bdInd Z e := by
  unfold bdInd betweenInd
  simp only [mem_bd, mem_between, he, true_and, Finset.mem_union]
  have d0 : Γ.ends e 0 ∈ X → Γ.ends e 0 ∉ Z := fun h ↦ Finset.disjoint_left.mp hXZ h
  have d1 : Γ.ends e 1 ∈ X → Γ.ends e 1 ∉ Z := fun h ↦ Finset.disjoint_left.mp hXZ h
  by_cases a0 : Γ.ends e 0 ∈ X <;> by_cases a1 : Γ.ends e 1 ∈ X <;>
    by_cases b0 : Γ.ends e 0 ∈ Z <;> by_cases b1 : Γ.ends e 1 ∈ Z <;>
    simp [a0, a1, b0, b1] <;> first | exact d0 a0 b0 | exact d1 a1 b1

/-- **Boundary of a disjoint union.** -/
theorem card_bd_union {X Z : Finset ℕ} (hXZ : Disjoint X Z) :
    (Γ.bd (X ∪ Z)).card + 2 * (Γ.between X Z).card = (Γ.bd X).card + (Γ.bd Z).card := by
  rw [card_bd_eq_sum, card_bd_eq_sum, card_bd_eq_sum, card_between_eq_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun e he ↦ bdInd_union hXZ he

theorem crossEdges_eq_between {X Z : Finset ℕ} (hXZ : Disjoint X Z) :
    Γ.crossEdges X Z = Γ.between X Z := by
  ext e
  unfold crossEdges
  rw [Finset.mem_sdiff, Finset.mem_union, mem_edgesIn, mem_edgesIn, mem_edgesIn, mem_between]
  constructor
  · rintro ⟨⟨he, hend⟩, hnot⟩
    refine ⟨he, ?_⟩
    have h0 := Finset.mem_union.mp (hend 0)
    have h1 := Finset.mem_union.mp (hend 1)
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
    · exact absurd (Or.inl ⟨he, fun i ↦ by fin_cases i <;> assumption⟩) hnot
    · exact Or.inl ⟨h0, h1⟩
    · exact Or.inr ⟨h0, h1⟩
    · exact absurd (Or.inr ⟨he, fun i ↦ by fin_cases i <;> assumption⟩) hnot
  · rintro ⟨he, h⟩
    rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · refine ⟨⟨he, fun i ↦ ?_⟩, ?_⟩
      · fin_cases i
        · exact Finset.mem_union_left _ h0
        · exact Finset.mem_union_right _ h1
      · rintro (⟨-, h⟩ | ⟨-, h⟩)
        · exact Finset.disjoint_left.mp hXZ (h 1) h1
        · exact Finset.disjoint_left.mp hXZ h0 (h 0)
    · refine ⟨⟨he, fun i ↦ ?_⟩, ?_⟩
      · fin_cases i
        · exact Finset.mem_union_right _ h0
        · exact Finset.mem_union_left _ h1
      · rintro (⟨-, h⟩ | ⟨-, h⟩)
        · exact Finset.disjoint_left.mp hXZ (h 0) h0
        · exact Finset.disjoint_left.mp hXZ h1 (h 1)

/-- Two acyclic sets whose union has a cycle are joined by at least two edges. -/
theorem two_le_card_between {X Z : Finset ℕ} (hXV : X ⊆ Γ.Vs) (hXZ : Disjoint X Z)
    (hX : ¬ Γ.HasCycle X) (hZ : ¬ Γ.HasCycle Z) (h : Γ.HasCycle (X ∪ Z)) :
    2 ≤ (Γ.between X Z).card := by
  by_contra hlt
  push Not at hlt
  rw [← crossEdges_eq_between hXZ] at hlt
  exact not_hasCycle_union hXV hXZ hX hZ (by omega) h

theorem edgesIn_union {X Z : Finset ℕ} (_hXZ : Disjoint X Z) :
    Γ.edgesIn (X ∪ Z) = (Γ.edgesIn X ∪ Γ.edgesIn Z) ∪ Γ.between X Z := by
  ext e
  rw [Finset.mem_union, Finset.mem_union, mem_edgesIn, mem_edgesIn, mem_edgesIn, mem_between]
  constructor
  · rintro ⟨he, hend⟩
    have h0 := Finset.mem_union.mp (hend 0)
    have h1 := Finset.mem_union.mp (hend 1)
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
    · exact Or.inl (Or.inl ⟨he, fun i ↦ by fin_cases i <;> assumption⟩)
    · exact Or.inr ⟨he, Or.inl ⟨h0, h1⟩⟩
    · exact Or.inr ⟨he, Or.inr ⟨h0, h1⟩⟩
    · exact Or.inl (Or.inr ⟨he, fun i ↦ by fin_cases i <;> assumption⟩)
  · rintro ((⟨he, hend⟩ | ⟨he, hend⟩) | ⟨he, h⟩)
    · exact ⟨he, fun i ↦ Finset.mem_union_left _ (hend i)⟩
    · exact ⟨he, fun i ↦ Finset.mem_union_right _ (hend i)⟩
    · refine ⟨he, fun i ↦ ?_⟩
      rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> fin_cases i
      · exact Finset.mem_union_left _ h0
      · exact Finset.mem_union_right _ h1
      · exact Finset.mem_union_right _ h0
      · exact Finset.mem_union_left _ h1

theorem card_edgesIn_union {X Z : Finset ℕ} (hXZ : Disjoint X Z) :
    (Γ.edgesIn (X ∪ Z)).card = (Γ.edgesIn X).card + (Γ.edgesIn Z).card + (Γ.between X Z).card := by
  rw [edgesIn_union hXZ, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint]
  · rw [Finset.disjoint_left]
    intro e h1 h2
    rw [mem_edgesIn] at h1 h2
    exact Finset.disjoint_left.mp hXZ (h1.2 0) (h2.2 0)
  · rw [← crossEdges_eq_between hXZ]
    unfold crossEdges
    exact Finset.disjoint_sdiff

/-- Girth at least five excludes loops. -/
theorem Girth5.no_loop (hg : Γ.Girth5) {e : ℕ} (he : e ∈ Γ.Es) (_hv : Γ.ends e 0 ∈ Γ.Vs) :
    Γ.ends e 0 ≠ Γ.ends e 1 := by
  intro heq
  have := hg {e} (Finset.singleton_subset_iff.mpr he) (Finset.singleton_nonempty e) ?_
  · simp at this
  · intro v _
    rw [degIn_eq_sum, Finset.sum_singleton, ← heq]
    by_cases h : Γ.ends e 0 = v
    · rw [if_pos h]
      exact ⟨1, rfl⟩
    · rw [if_neg h]
      exact ⟨0, rfl⟩

/-- The internal degree of a vertex added to a set is the number of edges between them. -/
theorem degIn_edgesIn_insert (hg : Γ.Girth5) (hcl : Γ.IsClosed) {Z : Finset ℕ} {q : ℕ}
    (_hq : q ∉ Z) (_hqV : q ∈ Γ.Vs) :
    Γ.degIn (Γ.edgesIn (insert q Z)) q = (Γ.between Z {q}).card := by
  unfold degIn
  have hinj : ∀ h ∈ Γ.halfEdgesIn (Γ.edgesIn (insert q Z)) q,
      ∀ h' ∈ Γ.halfEdgesIn (Γ.edgesIn (insert q Z)) q, h.1 = h'.1 → h = h' := by
    intro h hh h' hh' heq
    rw [mem_halfEdgesIn] at hh hh'
    have he := (mem_edgesIn.mp hh.1).1
    by_cases hij : h.2 = h'.2
    · exact Prod.ext heq hij
    · exfalso
      have hloop := hg.no_loop he (hcl _ he 0)
      have h0 : Γ.ends h.1 h.2 = q := hh.2
      have h1 : Γ.ends h'.1 h'.2 = q := hh'.2
      rw [← heq] at h1
      have h2 : h.2 = 0 ∨ h.2 = 1 := by omega
      have h2' : h'.2 = 0 ∨ h'.2 = 1 := by omega
      rcases h2 with h2 | h2 <;> rcases h2' with h2' | h2' <;> rw [h2] at h0 <;> rw [h2'] at h1
      · exact hij (h2.trans h2'.symm)
      · exact hloop (h0.trans h1.symm)
      · exact hloop (h1.trans h0.symm)
      · exact hij (h2.trans h2'.symm)
  rw [← Finset.card_image_of_injOn (f := Prod.fst) (fun h hh h' hh' heq ↦ hinj h hh h' hh' heq)]
  congr 1
  ext e
  rw [Finset.mem_image, mem_between]
  constructor
  · rintro ⟨h, hh, rfl⟩
    rw [mem_halfEdgesIn, mem_edgesIn] at hh
    have he := hh.1.1
    refine ⟨he, ?_⟩
    have hq0 := hh.1.2 0
    have hq1 := hh.1.2 1
    rw [Finset.mem_insert] at hq0 hq1
    have hloop := hg.no_loop he (hcl _ he 0)
    have h2 : h.2 = 0 ∨ h.2 = 1 := by omega
    rcases h2 with h2 | h2
    · rw [h2] at hh
      have h0 : Γ.ends h.1 0 = q := hh.2
      rcases hq1 with hq1 | hq1
      · exact absurd (h0.trans hq1.symm) hloop
      · exact Or.inr ⟨by rw [h0]; exact Finset.mem_singleton_self _, hq1⟩
    · rw [h2] at hh
      have h1 : Γ.ends h.1 1 = q := hh.2
      rcases hq0 with hq0 | hq0
      · exact absurd (hq0.trans h1.symm) hloop
      · exact Or.inl ⟨hq0, by rw [h1]; exact Finset.mem_singleton_self _⟩
  · rintro ⟨he, h⟩
    rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · rw [Finset.mem_singleton] at h1
      refine ⟨(e, 1), mem_halfEdgesIn.mpr ⟨mem_edgesIn.mpr ⟨he, fun i ↦ ?_⟩, h1⟩, rfl⟩
      fin_cases i
      · exact Finset.mem_insert_of_mem h0
      · rw [Finset.mem_insert]
        exact Or.inl h1
    · rw [Finset.mem_singleton] at h0
      refine ⟨(e, 0), mem_halfEdgesIn.mpr ⟨mem_edgesIn.mpr ⟨he, fun i ↦ ?_⟩, h0⟩, rfl⟩
      fin_cases i
      · rw [Finset.mem_insert]
        exact Or.inl h0
      · exact Finset.mem_insert_of_mem h1

/-- A set with a cycle spans at least five edges when the girth is at least five. -/
theorem five_le_card_edgesIn (hg : Γ.Girth5) {X : Finset ℕ} (h : Γ.HasCycle X) :
    5 ≤ (Γ.edgesIn X).card := by
  obtain ⟨F, hF, hne, hev⟩ := h
  exact (hg F (hF.trans (edgesIn_subset X)) hne hev).trans (Finset.card_le_card hF)

end FinGraph
end GraphPuzzles
