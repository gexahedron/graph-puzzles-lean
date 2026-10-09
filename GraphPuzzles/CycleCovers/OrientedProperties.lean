import GraphPuzzles.CycleCovers.OrientedCover
import GraphPuzzles.CycleCovers.StrongProperties

/-! Existence and direction-forgetting properties of oriented cycle double covers. -/

namespace GraphPuzzles
namespace LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- A bounded oriented cycle double cover exists. -/
def HasOrientedCycleDoubleCover (H : LoopMultigraph V E) (k : ℕ) : Prop :=
  Nonempty (H.OrientedCycleDoubleCover k)

/-- A balanced directed subgraph is even after forgetting its directions. -/
theorem DirectedCycle.even (D : H.DirectedCycle) : H.IsEvenEdgeSet D.edges := by
  rw [H.isEvenEdgeSet_iff_even_degree]
  intro v
  rw [H.degreeIn_eq_card_halfEdges]
  let S := Finset.univ.filter fun h : H.halfEdgesAt v ↦ h.1.1 ∈ D.edges
  have hc := Finset.card_filter_add_card_filter_not (s := S)
    (fun h : H.halfEdgesAt v ↦ h.1.2 = D.tail h.1.1)
  have hb := D.balanced v
  simp only [S, Finset.filter_filter] at hc
  rw [← hb] at hc
  exact ⟨_, hc.symm⟩

/-- Forget the directions of an oriented cover. -/
def OrientedCycleDoubleCover.toCycleDoubleCover {k : ℕ} (D : H.OrientedCycleDoubleCover k) :
    H.CycleDoubleCover k where
  cycles i := ⟨(D.cycles i).edges, (D.cycles i).even⟩
  coveredTwice := D.coveredTwice

@[simp]
theorem OrientedCycleDoubleCover.toCycleDoubleCover_contains_iff {k : ℕ}
    (D : H.OrientedCycleDoubleCover k) (F : Finset E) :
    D.toCycleDoubleCover.Contains F ↔ D.Contains F := Iff.rfl

theorem HasOrientedCycleDoubleCover.forget {k : ℕ} (h : H.HasOrientedCycleDoubleCover k) :
    H.HasCycleDoubleCover k := h.map OrientedCycleDoubleCover.toCycleDoubleCover

end LoopMultigraph
end GraphPuzzles
