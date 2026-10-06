import Mathlib.Data.Finset.Card

/-! Counting predicates on a three-element finite type. -/

namespace GraphPuzzles
namespace LoopMultigraph

/-- The number of elements of a three-element type satisfying a predicate. -/
theorem card_filter_of_three {α : Type*} [Fintype α] [DecidableEq α] (y₁ y₂ y₃ : α)
    (h12 : y₁ ≠ y₂) (h13 : y₁ ≠ y₃) (h23 : y₂ ≠ y₃) (hcases : ∀ x, x = y₁ ∨ x = y₂ ∨ x = y₃)
    (P : α → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card =
      (if P y₁ then 1 else 0) + ((if P y₂ then 1 else 0) + (if P y₃ then 1 else 0)) := by
  have huniv : (Finset.univ : Finset α) = {y₁, y₂, y₃} := by
    ext x
    simp only [Finset.mem_univ, true_iff]
    rcases hcases x with rfl | rfl | rfl <;> simp
  rw [huniv, Finset.filter_insert, Finset.filter_insert, Finset.filter_singleton]
  by_cases ha : P y₁ <;> by_cases hb : P y₂ <;> by_cases hc : P y₃ <;>
    simp only [ha, hb, hc, if_true, if_false] <;>
    simp [Finset.card_insert_of_notMem, h12, h13, h23]


end LoopMultigraph
end GraphPuzzles
