import GraphPuzzles.Graph.LoopMultigraph

/-!
# Binary T-joins

The binary boundary of an edge set records, at every vertex, the parity of its degree.  This file
proves the elementary characterization of boundaries of subsets of a fixed edge set `F`: a vertex
function is such a boundary exactly when it is orthogonal to every vertex function that is
constant along the edges of `F`.  The proof is a direct induction on `F`; it uses neither
connectivity nor linear-algebra machinery.
-/

namespace GraphPuzzles
namespace LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LoopMultigraph V E)

/-- The binary boundary of an edge set: the parity of its degree at each vertex. -/
def boundary (J : Finset E) (v : V) : F₂ := ∑ e ∈ J, G.edgeIncidence v e

omit [DecidableEq E] in
@[simp]
theorem boundary_empty (v : V) : G.boundary ∅ v = 0 := by
  simp [boundary]

theorem boundary_insert {J : Finset E} {e : E} (he : e ∉ J) (v : V) :
    G.boundary (insert e J) v = G.edgeIncidence v e + G.boundary J v := by
  simp [boundary, Finset.sum_insert he]

omit [DecidableEq E] in
theorem isEvenEdgeSet_iff_boundary_eq_zero (J : Finset E) :
    G.IsEvenEdgeSet J ↔ ∀ v, G.boundary J v = 0 := Iff.rfl

omit [DecidableEq E] in
/-- Pairing a vertex function with the incidence vector of an edge evaluates it at both ends. -/
theorem sum_mul_edgeIncidence (c : V → F₂) (e : E) :
    ∑ v, c v * G.edgeIncidence v e = c (G.endAt e 0) + c (G.endAt e 1) := by
  simp [edgeIncidence, mul_add, Finset.sum_add_distrib]

private theorem F₂_add_eq_add_of_ne {a b a' b' : F₂} (h : a ≠ b) (h' : a' ≠ b') :
    a + a' = b + b' := by
  revert a b a' b'
  decide

private theorem F₂_eq_one_of_ne_zero {a : F₂} (h : a ≠ 0) : a = 1 := by
  revert a
  decide

private theorem F₂_add_eq_one_of_ne {a b : F₂} (h : a ≠ b) : a + b = 1 := by
  revert a b
  decide

/-- **Binary T-join lemma.**  A vertex function orthogonal to every function that is constant
along the edges of `F` is the boundary of a subset of `F`. -/
theorem exists_boundary_eq (F : Finset E) (d : V → F₂)
    (hd : ∀ c : V → F₂, (∀ e ∈ F, c (G.endAt e 0) = c (G.endAt e 1)) →
      ∑ v, c v * d v = 0) :
    ∃ J ⊆ F, ∀ v, G.boundary J v = d v := by
  classical
  induction F using Finset.induction_on generalizing d with
  | empty =>
      refine ⟨∅, Finset.Subset.refl _, ?_⟩
      intro v
      rw [boundary_empty]
      have h := hd (Pi.single v 1) (by simp)
      have hsingle : ∑ w, (Pi.single v (1 : F₂) : V → F₂) w * d w = d v := by
        simp [Pi.single_apply]
      rw [hsingle] at h
      exact h.symm
  | insert e F heF ih =>
      by_cases hall : ∀ c : V → F₂,
          (∀ e' ∈ F, c (G.endAt e' 0) = c (G.endAt e' 1)) → ∑ v, c v * d v = 0
      · obtain ⟨J, hJF, hJ⟩ := ih d hall
        exact ⟨J, hJF.trans (Finset.subset_insert e F), hJ⟩
      · push Not at hall
        obtain ⟨c₀, hc₀F, hc₀d⟩ := hall
        have hc₀e : c₀ (G.endAt e 0) ≠ c₀ (G.endAt e 1) := by
          intro h
          apply hc₀d
          apply hd c₀
          intro e' he'
          rcases Finset.mem_insert.mp he' with rfl | he'
          · exact h
          · exact hc₀F e' he'
        have hc₀d' : ∑ v, c₀ v * d v = 1 := F₂_eq_one_of_ne_zero hc₀d
        let d' : V → F₂ := fun v ↦ d v + G.edgeIncidence v e
        have hd' : ∀ c : V → F₂,
            (∀ e' ∈ F, c (G.endAt e' 0) = c (G.endAt e' 1)) → ∑ v, c v * d' v = 0 := by
          intro c hc
          have hsplit : ∑ v, c v * d' v =
              ∑ v, c v * d v + (c (G.endAt e 0) + c (G.endAt e 1)) := by
            simp only [d', mul_add, Finset.sum_add_distrib, G.sum_mul_edgeIncidence]
          rw [hsplit]
          by_cases hce : c (G.endAt e 0) = c (G.endAt e 1)
          · have h0 : ∑ v, c v * d v = 0 := by
              apply hd c
              intro e' he'
              rcases Finset.mem_insert.mp he' with rfl | he'
              · exact hce
              · exact hc e' he'
            rw [h0, hce, F₂_add_self, add_zero]
          · have hsum0 : ∑ v, (c v + c₀ v) * d v = 0 := by
              apply hd (c + c₀)
              intro e' he'
              rcases Finset.mem_insert.mp he' with rfl | he'
              · exact F₂_add_eq_add_of_ne hce hc₀e
              · simp only [Pi.add_apply, hc e' he', hc₀F e' he']
            have hcd : ∑ v, c v * d v = 1 := by
              simp only [add_mul, Finset.sum_add_distrib, hc₀d'] at hsum0
              have h1 := congrArg (· + 1) hsum0
              simpa [add_assoc] using h1
            rw [hcd, F₂_add_eq_one_of_ne hce]
            exact F₂_add_self 1
        obtain ⟨J, hJF, hJ⟩ := ih d' hd'
        refine ⟨insert e J, Finset.insert_subset_insert e hJF, ?_⟩
        intro v
        have heJ : e ∉ J := fun h ↦ heF (hJF h)
        rw [G.boundary_insert heJ, hJ v]
        simp only [d']
        calc
          G.edgeIncidence v e + (d v + G.edgeIncidence v e) =
              d v + (G.edgeIncidence v e + G.edgeIncidence v e) := by abel
          _ = d v := by rw [F₂_add_self, add_zero]

end LoopMultigraph
end GraphPuzzles
