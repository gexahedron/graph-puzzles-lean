import GraphPuzzles.Claims.CycleDoubleCover

/-! Scope checks for the assembled theorem and its graph predicates. -/

namespace GraphPuzzles.CycleDoubleCoverChecks

open LoopMultigraph

universe u v

example : CycleDoubleCoverTheorem.{u, v} := cycleDoubleCover

example {V : Type u} {E : Type v} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (H : LoopMultigraph V E) (hb : H.IsBridgeless) :
    ∃ L : List H.OrdinaryCircuit, ∀ e : E,
      (L.filter fun C ↦ e ∈ C.edges).length = 2 := Claims.cycle_double_cover hb

def edgeless (n : ℕ) : LoopMultigraph (Fin n) (Fin 0) :=
  ⟨fun e _ ↦ Fin.elim0 e⟩

example (n : ℕ) : Nonempty (edgeless n).OrdinaryCycleDoubleCover :=
  exists_ordinaryCycleDoubleCover (fun e ↦ Fin.elim0 e)

example : Nonempty (edgeless 0).OrdinaryCycleDoubleCover :=
  exists_ordinaryCycleDoubleCover (fun e ↦ Fin.elim0 e)

/-- Multiple loops and any number of isolated vertices are permitted. -/
def loopsWithIsolates (n m : ℕ) : LoopMultigraph (Fin (n + 1)) (Fin m) :=
  ⟨fun _ _ ↦ 0⟩

example (n m : ℕ) : Nonempty (loopsWithIsolates n m).OrdinaryCycleDoubleCover :=
  exists_ordinaryCycleDoubleCover (fun _ _ _ ↦ rfl)

def parallelPair : LoopMultigraph (Fin 2) (Fin 2) := ⟨fun _ i ↦ i⟩

example : Nonempty parallelPair.OrdinaryCycleDoubleCover := by
  apply exists_ordinaryCycleDoubleCover
  intro e c h
  fin_cases e
  · exact h 1 (by decide)
  · exact h 0 (by decide)

/-- Two disconnected parallel-edge components. -/
def twoParallelPairs : LoopMultigraph (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun e i ↦ (e.1, i)⟩

example : Nonempty twoParallelPairs.OrdinaryCycleDoubleCover := by
  apply exists_ordinaryCycleDoubleCover
  rintro ⟨a, b⟩ c h
  fin_cases b
  · exact h (a, 1) (by simp)
  · exact h (a, 0) (by simp)

/-- A single non-loop edge fails the hypothesis: bridgelessness is not vacuous. -/
def singleEdge : LoopMultigraph (Fin 2) (Fin 1) := ⟨fun _ i ↦ i⟩

example : ¬ singleEdge.IsBridgeless := by
  intro hb
  have h := hb 0 (fun i ↦ decide (i = 0)) (fun f hf ↦ by
    fin_cases f
    exact (hf rfl).elim)
  simp [singleEdge] at h

end GraphPuzzles.CycleDoubleCoverChecks
