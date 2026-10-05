import GraphPuzzles.CycleCovers.General.Statement
import Mathlib.Algebra.BigOperators.Group.Finset.Pi

/-! Convert any of the existing bounded even-subgraph covers into ordinary circuits. -/

namespace GraphPuzzles.LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  {H : LoopMultigraph V E}

private theorem filter_flatMap_length {α β : Type*} (L : List α)
    (f : α → List β) (p : β → Bool) :
    ((L.flatMap f).filter p).length = (L.map fun a ↦ ((f a).filter p).length).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.filter_append, ih]

/-- Decompose each even layer using the existing ordinary-circuit decomposition theorem.
The edge multiplicities are preserved, even when layers or resulting circuits repeat. -/
noncomputable def CycleDoubleCover.toOrdinary {k : ℕ} (D : H.CycleDoubleCover k) :
    H.OrdinaryCycleDoubleCover := by
  classical
  choose L hL using fun i ↦ H.decompose_even_edge_set_ordinary
    (D.cycles i).edges (D.cycles i).even
  refine ⟨(List.ofFn (fun i : Fin k ↦ i)).flatMap L, ?_⟩
  intro e
  rw [filter_flatMap_length]
  simp_rw [hL]
  rw [List.map_ofFn, List.sum_ofFn]
  simpa only [Finset.card_filter, Function.comp_apply] using D.coveredTwice e

end GraphPuzzles.LoopMultigraph
