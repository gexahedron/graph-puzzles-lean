import GraphPuzzles.Graph.Bridgeless
import GraphPuzzles.CycleCovers.DominatingCircuit

/-!
# The cycle double cover theorem in the book's graph model

The conclusion uses ordinary nonempty connected 2-regular circuits. A list retains
repeated occurrences, including two copies of a singleton loop or a parallel-edge circuit.
There is no connectedness, cubicity, simplicity, or looplessness hypothesis.
-/

namespace GraphPuzzles.LoopMultigraph

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E]

/-- A finite list of ordinary circuits covering every labelled edge exactly twice. -/
structure OrdinaryCycleDoubleCover (H : LoopMultigraph V E) where
  circuits : List H.OrdinaryCircuit
  coveredTwice : ∀ e : E, (circuits.filter fun C ↦ e ∈ C.edges).length = 2

/-- Every finite bridgeless endpoint multigraph has an ordinary circuit double cover. -/
def CycleDoubleCoverTheorem : Prop :=
  ∀ (V : Type u) (E : Type v) [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (H : LoopMultigraph V E),
    H.IsBridgeless → Nonempty H.OrdinaryCycleDoubleCover

end GraphPuzzles.LoopMultigraph
