import GraphPuzzles.Reduction.Parallel.ParallelInduction
import GraphPuzzles.Reduction.Induction.NearBrickCrossingInduction
import GraphPuzzles.Petersen.PetersenCutConclusion

/-! Reduction of the main induction to simple non-Petersen bricks. -/

namespace GraphPuzzles.LoopMultigraph

universe u v

/-- The remaining induction step only needs to handle nontrivial separating
cuts in simple non-Petersen bricks. All other cases are discharged here. -/
theorem nearBrickCutTheorem_of_simple_brick_step
    (step : ∀ {V : Type u} {E : Type v} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (H : LoopMultigraph V E),
      NearBrickCutInductionHypothesis.{u, v} H.inductionSize →
      H.IsSimple → H.IsBrick → ¬ H.IsPetersen → ∀ X,
      H.IsSeparatingCut X → IsNontrivialCut X → H.NearBrickCutConclusion X) :
    NearBrickCutTheorem.{u, v} := by
  have aux (n : ℕ) : ∀ {V : Type u} {E : Type v} [Fintype V] [Fintype E]
      [DecidableEq V] [DecidableEq E] (H : LoopMultigraph V E),
      H.inductionSize = n → H.IsNearBrick → ∀ X,
      H.IsSeparatingCut X → H.NearBrickCutConclusion X := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro V E _ _ _ _ H heq hn X hs
      have hIH : NearBrickCutInductionHypothesis.{u, v} H.inductionSize := by
        intro W F _ _ _ _ K hlt hK Y hY
        exact ih K.inductionSize (heq ▸ hlt) K rfl hK Y hY
      by_cases hX : IsNontrivialCut X
      · by_cases hsimple : H.IsSimple
        · by_cases hb : H.IsBrick
          · by_cases hp : H.IsPetersen
            · exact hp.cutConclusion hs
            · exact step H hIH hsimple hb hp X hs hX
          · exact hn.cutConclusion_of_not_brick hb hIH hs
        · exact hn.cutConclusion_of_not_simple hsimple hIH hs
      · exact Or.inr (Or.inl (cutCharacteristic_eq_top_of_not_nontrivial hX))
  intro V E _ _ _ _ H hn X hs
  exact aux H.inductionSize H rfl hn X hs

end GraphPuzzles.LoopMultigraph
