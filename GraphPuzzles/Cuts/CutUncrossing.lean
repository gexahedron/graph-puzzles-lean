import GraphPuzzles.Cuts.SeparatingCutTheory

/-! Weighted cut identities and uncrossing of tight odd cuts. -/

namespace GraphPuzzles.LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

/-- Edges between two vertex sets; all applications below use disjoint sets. -/
def edgesBetween (H : LoopMultigraph V E) (X Y : Finset V) : Finset E :=
  Finset.univ.filter fun e ↦
    (H.endAt e 0 ∈ X ∧ H.endAt e 1 ∈ Y) ∨ (H.endAt e 1 ∈ X ∧ H.endAt e 0 ∈ Y)

omit [DecidableEq E] in
/-- The weighted cut submodularity identity, including its exact error term. -/
theorem cutWeight_modular (x : E → ℚ) (X Y : Finset V) :
    H.cutWeight x X + H.cutWeight x Y =
      H.cutWeight x (X ∩ Y) + H.cutWeight x (X ∪ Y) +
        2 * ∑ e ∈ H.edgesBetween (X \ Y) (Y \ X), x e := by
  unfold cutWeight dangling edgesBetween
  simp only [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hX0 : H.endAt e 0 ∈ X <;> by_cases hX1 : H.endAt e 1 ∈ X <;>
    by_cases hY0 : H.endAt e 0 ∈ Y <;> by_cases hY1 : H.endAt e 1 ∈ Y <;>
    simp [hX0, hX1, hY0, hY1] <;> ring

omit [DecidableEq E] in
theorem cutWeight_submodular {x : E → ℚ} (hx : ∀ e, 0 ≤ x e) (X Y : Finset V) :
    H.cutWeight x (X ∩ Y) + H.cutWeight x (X ∪ Y) ≤ H.cutWeight x X + H.cutWeight x Y := by
  have hh := cutWeight_modular (H := H) x X Y
  have hn : (0 : ℚ) ≤ ∑ e ∈ H.edgesBetween (X \ Y) (Y \ X), x e :=
    Finset.sum_nonneg fun e _ ↦ hx e
  linarith

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem odd_union_of_odd_inter {X Y : Finset V} (hX : Odd X.card) (hY : Odd Y.card)
    (hI : Odd (X ∩ Y).card) : Odd (X ∪ Y).card := by
  have hh := Finset.card_union_add_card_inter X Y
  rw [Nat.odd_iff] at hX hY hI ⊢
  omega

omit [DecidableEq E] in
/-- Uncrossing two tight odd-cut inequalities when their intersection is odd. -/
theorem IsFractionalPerfectMatching.uncross {x : E → ℚ}
    (hx : H.IsFractionalPerfectMatching x) {X Y : Finset V}
    (hX : Odd X.card) (hY : Odd Y.card) (hI : Odd (X ∩ Y).card)
    (htX : H.cutWeight x X = 1) (htY : H.cutWeight x Y = 1) :
    H.cutWeight x (X ∩ Y) = 1 ∧ H.cutWeight x (X ∪ Y) = 1 ∧
      (∑ e ∈ H.edgesBetween (X \ Y) (Y \ X), x e) = 0 := by
  have hl := hx.odd_cut (X ∩ Y) hI
  have hr := hx.odd_cut (X ∪ Y) (odd_union_of_odd_inter hX hY hI)
  have hh := cutWeight_modular (H := H) x X Y
  rw [htX, htY] at hh
  have hn : (0 : ℚ) ≤ ∑ e ∈ H.edgesBetween (X \ Y) (Y \ X), x e :=
    Finset.sum_nonneg fun e _ ↦ hx.nonneg e
  exact ⟨by linarith, by linarith, by linarith⟩

theorem IsPerfectMatching.odd_of_crossing_one {M : Finset E} (hM : H.IsPerfectMatching M)
    {X : Finset V} (hX : (M ∩ H.dangling X).card = 1) : Odd X.card := by
  have hh := hM.crossing_mod_two X
  rw [hX] at hh
  exact Nat.odd_iff.mpr hh.symm

theorem IsTightCut.compl {X : Finset V} (ht : H.IsTightCut X) :
    H.IsTightCut (Finset.univ \ X) := by
  intro M hM
  simpa only [dangling_compl] using ht M hM

/-- Uncrossing tight graph cuts preserves tightness on the odd intersection and union. -/
theorem IsTightCut.uncross {X Y : Finset V} (hX : H.IsTightCut X) (hY : H.IsTightCut Y)
    (hI : Odd (X ∩ Y).card) : H.IsTightCut (X ∩ Y) ∧ H.IsTightCut (X ∪ Y) := by
  have key {M : Finset E} (hM : H.IsPerfectMatching M) :
      H.cutWeight (matchingVector M) (X ∩ Y) = 1 ∧
        H.cutWeight (matchingVector M) (X ∪ Y) = 1 := by
    have hx : H.cutWeight (matchingVector M) X = 1 := by rw [cutWeight_matchingVector, hX M hM]; norm_num
    have hy : H.cutWeight (matchingVector M) Y = 1 := by rw [cutWeight_matchingVector, hY M hM]; norm_num
    have hh := hM.isFractional.uncross
      (hM.odd_of_crossing_one (hX M hM)) (hM.odd_of_crossing_one (hY M hM)) hI hx hy
    exact ⟨hh.1, hh.2.1⟩
  constructor
  · intro M hM
    have hh := (key hM).1
    rw [cutWeight_matchingVector] at hh
    exact_mod_cast hh
  · intro M hM
    have hh := (key hM).2
    rw [cutWeight_matchingVector] at hh
    exact_mod_cast hh

/-- The complementary uncrossing: when the difference is odd, both differences are tight. -/
theorem IsTightCut.uncross_diff {X Y : Finset V} (hX : H.IsTightCut X) (hY : H.IsTightCut Y)
    (hD : Odd (X \ Y).card) : H.IsTightCut (X \ Y) ∧ H.IsTightCut (Y \ X) := by
  have hi : X ∩ (Finset.univ \ Y) = X \ Y := by ext v; simp
  have hu : Finset.univ \ (X ∪ (Finset.univ \ Y)) = Y \ X := by ext v; simp; tauto
  have hh := hX.uncross hY.compl (hi.symm ▸ hD)
  refine ⟨hi ▸ hh.1, ?_⟩
  have hc := hh.2.compl
  rwa [hu] at hc

end GraphPuzzles.LoopMultigraph
