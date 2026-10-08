import GraphPuzzles.Reduction.Wheels.OddWheel
import GraphPuzzles.Ears.EarHubFactorCritical
import GraphPuzzles.Ears.LongEarSeparation

/-! The complete brick case of the Campos–Lucchesi odd-wheel theorem. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

theorem IsBrick.three_le_degree (hb : H.IsBrick) (w : V) : 3 ≤ H.degree w := by
  have hcut := (hb.isBicritical hb.matchingCovered.loopless).three_le_singleton_cut
    hb.matchingCovered hb.notBipartite w
  have hs := sum_degree_eq_two_mul_add (H := H) {w}
  simp only [Finset.sum_singleton] at hs
  omega

/-- Theorem 5.1 for bricks, including the long-ear alternative. -/
theorem IsBrick.oddWheel_or_not_solid_or_removable (hb : H.IsBrick)
    {v : V} {M : Finset E} (hM : H.IsVertexMatching v M) :
    H.IsOddWheel v ∨ ¬ H.IsSolid ∨
      ∃ f, f ∉ M ∧ (∀ k, H.endAt f k ≠ v) ∧
        (H.IsRemovable f ∨ ∃ g, g ∉ M ∧ (∀ k, H.endAt g k ≠ v) ∧
          H.IsRemovableDoubleton f g) := by
  rcases hb.oddWheel_or_removable_or_longEar hM with hW | hR | ⟨r, q, hq, hmax, L, hi⟩
  · exact Or.inl hW
  · exact Or.inr (Or.inr hR)
  · have hfc := L.factorCritical_hub rfl rfl hmax
      (fun w hw ↦ (hM w (Finset.mem_erase.mp hw).1).le)
      (fun w _ ↦ hb.three_le_degree w) hi
    exact Or.inr (Or.inl (L.not_solid_of_factorCritical_hub hb rfl hq hi hfc))

/-- In a solid brick, only the odd-wheel and avoiding-removable-class
alternatives remain. -/
theorem IsBrick.oddWheel_or_removable_of_solid (hb : H.IsBrick) (hs : H.IsSolid)
    {v : V} {M : Finset E} (hM : H.IsVertexMatching v M) :
    H.IsOddWheel v ∨
      ∃ f, f ∉ M ∧ (∀ k, H.endAt f k ≠ v) ∧
        (H.IsRemovable f ∨ ∃ g, g ∉ M ∧ (∀ k, H.endAt g k ≠ v) ∧
          H.IsRemovableDoubleton f g) := by
  rcases hb.oddWheel_or_not_solid_or_removable hM with hW | hn | hR
  · exact Or.inl hW
  · exact (hn hs).elim
  · exact Or.inr hR

end GraphPuzzles.LoopMultigraph
