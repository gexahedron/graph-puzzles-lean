import CDCLean.Expansion
import CDCLean.JaegerKilpatrick
import GraphPuzzles.CycleCovers.General.Statement

/-!
# The checked OpenAI proof input

The pinned `cdc_lean` dependency supplies the eight-flow theorem, the affine-pair
construction and cubic expansion. We compose those proved results at their even-cover
interface, retaining the eight layers for transport to our existing cover type.
-/

namespace GraphPuzzles.CycleDoubleCoverProof

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- The unconditional eight-layer conclusion of the upstream proof, before its own
cycle decomposition. Our ordinary-circuit decomposition will supply the final step. -/
theorem exists_indexed_even_cover (G : CDCLean.FiniteGraph V E) (hb : G.Bridgeless) :
    Nonempty G.IndexedEvenDoubleCover := by
  let R := G.rotationSystemOfBridgeless hb
  let K := G.cubicExpansion R
  have hK : K.toFiniteGraph.Bridgeless := G.cubicExpansion_bridgeless R hb
  obtain ⟨f⟩ := K.toFiniteGraph.jaegerKilpatrickEightFlow hK
  exact ⟨G.projectEvenDoubleCover R
    (CDCLean.cubic_even_double_cover K (K.gammaFlowOfNowhereZero f))⟩

/-- Delete only loops, preserving every non-loop edge label and both numbered ends. -/
def nonLoopGraph (H : LoopMultigraph V E) :
    CDCLean.FiniteGraph V {e : E // H.endAt e 0 ≠ H.endAt e 1} where
  endAt e i := H.endAt e.1 i
  loopless e := e.2

omit [DecidableEq E] in
/-- Loop deletion preserves the no-singleton-cut condition. -/
theorem nonLoopGraph_bridgeless (H : LoopMultigraph V E) (hb : H.IsBridgeless) :
    (nonLoopGraph H).Bridgeless := by
  intro S hS
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp hS
  have hcol := hb e.1 (fun w ↦ decide (w ∈ S)) (fun f hf ↦ by
    rw [decide_eq_decide]
    by_cases hl : H.endAt f 0 = H.endAt f 1
    · rw [hl]
    · have hn : (⟨f, hl⟩ : {e : E // H.endAt e 0 ≠ H.endAt e 1}) ∉
          (nonLoopGraph H).cut S := by
        rw [he, Finset.mem_singleton]
        exact fun h ↦ hf (congrArg Subtype.val h)
      simpa [CDCLean.FiniteGraph.cut, CDCLean.FiniteGraph.Crosses, nonLoopGraph,
        propext_iff] using hn)
  have heS : e ∈ (nonLoopGraph H).cut S := by rw [he]; simp
  have hcross : ¬ (H.endAt e.1 0 ∈ S ↔ H.endAt e.1 1 ∈ S) := by
    simpa [CDCLean.FiniteGraph.cut, CDCLean.FiniteGraph.Crosses, nonLoopGraph,
      propext_iff] using heS
  rw [decide_eq_decide] at hcol
  exact hcross hcol

end GraphPuzzles.CycleDoubleCoverProof
