import GraphPuzzles.FinGraph.FinGraphCycles
import GraphPuzzles.FinGraph.FinGraphColouring

/-!
# Short cycles violate girth `5`

Explicit two-, three- and four-cycles (given by their edges and vertices) are nonempty even
edge sets, so a graph of girth at least `5` contains none.
-/

namespace GraphPuzzles
namespace FinGraph

open Finset

variable {Γ : FinGraph}

/-- `e` joins `a` and `b` (in either order). -/
def Joins (Γ : FinGraph) (e a b : ℕ) : Prop :=
  (Γ.ends e 0 = a ∧ Γ.ends e 1 = b) ∨ (Γ.ends e 0 = b ∧ Γ.ends e 1 = a)

theorem Joins.symm {e a b : ℕ} (h : Γ.Joins e a b) : Γ.Joins e b a := Or.symm h

/-- The contribution of an edge joining two distinct vertices to the degree of `v`. -/
theorem endCount_of_joins {e a b : ℕ} (h : Γ.Joins e a b) (hab : a ≠ b) (v : ℕ) :
    ((if Γ.ends e 0 = v then 1 else 0) + (if Γ.ends e 1 = v then 1 else 0)) =
      if v = a ∨ v = b then 1 else 0 := by
  rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rw [h0, h1] <;> split_ifs <;> omega

/-- No two-cycle. -/
theorem Girth5.no_two_cycle (hg : Γ.Girth5) {e e' a b : ℕ} (he : e ∈ Γ.Es) (he' : e' ∈ Γ.Es)
    (hne : e ≠ e') (hab : a ≠ b) (h1 : Γ.Joins e a b) (h2 : Γ.Joins e' a b) : False := by
  have hF : ({e, e'} : Finset ℕ) ⊆ Γ.Es := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hev : Γ.IsEven {e, e'} := by
    intro v _
    rw [degIn_eq_sum, Finset.sum_pair hne, endCount_of_joins h1 hab, endCount_of_joins h2 hab]
    split_ifs <;> decide
  have := hg _ hF ⟨e, Finset.mem_insert_self _ _⟩ hev
  rw [Finset.card_pair hne] at this
  omega

/-- No triangle. -/
theorem Girth5.no_triangle (hg : Γ.Girth5) {e₁ e₂ e₃ a b c : ℕ} (he₁ : e₁ ∈ Γ.Es)
    (he₂ : e₂ ∈ Γ.Es) (he₃ : e₃ ∈ Γ.Es) (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃) (h23 : e₂ ≠ e₃)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (j₁ : Γ.Joins e₁ a b) (j₂ : Γ.Joins e₂ b c) (j₃ : Γ.Joins e₃ c a) : False := by
  have hF : ({e₁, e₂, e₃} : Finset ℕ) ⊆ Γ.Es := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hev : Γ.IsEven {e₁, e₂, e₃} := by
    intro v _
    rw [degIn_eq_sum, Finset.sum_insert (by simp [h12, h13]), Finset.sum_pair h23,
      endCount_of_joins j₁ hab, endCount_of_joins j₂ hbc, endCount_of_joins j₃ hac.symm]
    split_ifs <;> first | decide | omega
  have := hg _ hF ⟨e₁, Finset.mem_insert_self _ _⟩ hev
  rw [Finset.card_insert_of_notMem (by simp [h12, h13]), Finset.card_pair h23] at this
  omega

/-- No quadrilateral. -/
theorem Girth5.no_quad (hg : Γ.Girth5) {e₁ e₂ e₃ e₄ a b c d : ℕ} (he₁ : e₁ ∈ Γ.Es)
    (he₂ : e₂ ∈ Γ.Es) (he₃ : e₃ ∈ Γ.Es) (he₄ : e₄ ∈ Γ.Es)
    (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃) (h14 : e₁ ≠ e₄) (h23 : e₂ ≠ e₃) (h24 : e₂ ≠ e₄) (h34 : e₃ ≠ e₄)
    (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (had : a ≠ d) (hac : a ≠ c) (hbd : b ≠ d)
    (j₁ : Γ.Joins e₁ a b) (j₂ : Γ.Joins e₂ b c) (j₃ : Γ.Joins e₃ c d) (j₄ : Γ.Joins e₄ d a) :
    False := by
  have hF : ({e₁, e₂, e₃, e₄} : Finset ℕ) ⊆ Γ.Es := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hev : Γ.IsEven {e₁, e₂, e₃, e₄} := by
    intro v _
    rw [degIn_eq_sum, Finset.sum_insert (by simp [h12, h13, h14]),
      Finset.sum_insert (by simp [h23, h24]), Finset.sum_pair h34,
      endCount_of_joins j₁ hab, endCount_of_joins j₂ hbc, endCount_of_joins j₃ hcd,
      endCount_of_joins j₄ had.symm]
    split_ifs <;> first | decide | omega
  have := hg _ hF ⟨e₁, Finset.mem_insert_self _ _⟩ hev
  rw [Finset.card_insert_of_notMem (by simp [h12, h13, h14]),
    Finset.card_insert_of_notMem (by simp [h23, h24]), Finset.card_pair h34] at this
  omega

end FinGraph
end GraphPuzzles
