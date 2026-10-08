import GraphPuzzles.Matching.Fractional.FractionalPeel
import GraphPuzzles.Matching.Fractional.FractionalTutte
import GraphPuzzles.Matching.Fractional.MatchingCombinationGlue

/-!
# Edmonds' rational perfect matching polytope

Every nonnegative rational edge vector satisfying the degree equations and odd-cut
inequalities is a convex combination of perfect matchings. The proof contracts a
nontrivial tight odd cut, or peels off a matching in the positive support. The
induction decreases the number of vertices, then the number of positive edges.
-/

namespace GraphPuzzles.LoopMultigraph

universe u v

private theorem fractional_decomposition_aux (n : ℕ) :
    ∀ {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (H : LoopMultigraph V E), Fintype.card V = n →
      ∀ (x : E → ℚ), H.IsFractionalPerfectMatching x → Nonempty (H.MatchingCombination x) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V E _ _ _ _ H hn
    have cutCase (x : E → ℚ) (hx : H.IsFractionalPerfectMatching x)
        (X : Finset V) (ho : Odd X.card) (hX : IsNontrivialCut X)
        (ht : H.cutWeight x X = 1) : Nonempty (H.MatchingCombination x) := by
      have hcard := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ X)
      rw [Finset.card_univ, hn] at hcard
      have hL : Fintype.card (Option X) < n := by
        rw [Fintype.card_option, Fintype.card_coe]
        have hh := hX.2
        omega
      have hR : Fintype.card (Option ↥(Finset.univ \ X)) < n := by
        rw [Fintype.card_option, Fintype.card_coe]
        have hh := hX.1
        omega
      obtain ⟨C⟩ := ih _ hL (H.contract X) rfl (fun e ↦ x e.1) (hx.contract X ho ht)
      obtain ⟨D⟩ := ih _ hR (H.contract (Finset.univ \ X)) rfl (fun e ↦ x e.1)
        (hx.contract _ (hx.odd_compl ho) ((cutWeight_compl x X).trans ht))
      exact ⟨C.glue D⟩
    have inner (k : ℕ) : ∀ (x : E → ℚ), (positiveEdges x).card = k →
        H.IsFractionalPerfectMatching x → Nonempty (H.MatchingCombination x) := by
      induction k using Nat.strong_induction_on with
      | h k ik =>
        intro x hk hx
        by_cases ht : ∃ X : Finset V, Odd X.card ∧ IsNontrivialCut X ∧ H.cutWeight x X = 1
        · obtain ⟨X, ho, hX, hc⟩ := ht
          exact cutCase x hx X ho hX hc
        · have hnt (X : Finset V) (ho : Odd X.card) (hX : IsNontrivialCut X) :
              H.cutWeight x X ≠ 1 := fun hc ↦ ht ⟨X, ho, hX, hc⟩
          obtain ⟨M, hM, hpos⟩ := hx.exists_perfectMatching_support
          rcases hx.peel hnt hM hpos with heq | ⟨a, y, ha, ha1, hy, hmix, hstep⟩
          · rw [heq]
            exact ⟨MatchingCombination.single hM⟩
          · have hcy : Nonempty (H.MatchingCombination y) := by
              rcases hstep with hsmall | ⟨X, ho, hX, hc⟩
              · exact ik _ (hsmall.trans_eq hk) y rfl hy
              · exact cutCase y hy X ho hX hc
            obtain ⟨D⟩ := hcy
            have heq : (fun e ↦ a * matchingVector M e + (1 - a) * y e) = x :=
              funext fun e ↦ (hmix e).symm
            exact ⟨heq ▸ (MatchingCombination.single hM).mix D a ha.le ha1.le⟩
    intro x hx
    exact inner _ x rfl hx

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- Edmonds' perfect matching polytope theorem for rational weights. -/
theorem IsFractionalPerfectMatching.exists_matchingCombination {x : E → ℚ}
    (hx : H.IsFractionalPerfectMatching x) : Nonempty (H.MatchingCombination x) :=
  fractional_decomposition_aux _ H rfl x hx

/-- In a bridgeless cubic graph, the uniform edge vector is a distribution of matchings. -/
theorem exists_matchingCombination_third (hc : ∀ v, H.degree v = 3)
    (hb : H.IsBridgeless) : Nonempty (H.MatchingCombination (fun _ ↦ 1 / 3)) :=
  (isFractionalPerfectMatching_third hc hb).exists_matchingCombination

end GraphPuzzles.LoopMultigraph
