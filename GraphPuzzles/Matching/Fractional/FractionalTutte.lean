import GraphPuzzles.Matching.Fractional.FractionalMatching
import GraphPuzzles.Matching.MatchingSubgraph

/-!
# Tutte's theorem for the support of a fractional perfect matching

Each odd component needs cut weight at least one. Its boundary lies in the deleted
vertex set's boundary, and these component boundaries are disjoint. The degree equations
therefore imply Tutte's inequality. Restricting to edges of positive weight gives a
perfect matching contained in the support, as needed in the matching-polytope argument.
-/

namespace GraphPuzzles.LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

namespace ComponentFamily

variable {Z : Finset V} (F : H.ComponentFamily Z)

omit [DecidableEq E] in
theorem dangling_subset {Q : Finset V} (hQ : Q ∈ F.parts) :
    H.dangling Q ⊆ H.dangling Z := by
  intro e he
  obtain ⟨k, hk, _, hkZ⟩ := F.exists_end_of_mem_dangling hQ he
  have hn := F.avoid Q hQ _ hk
  rw [mem_dangling]
  fin_cases k
  · exact fun h ↦ hn (h.mpr hkZ)
  · exact fun h ↦ hn (h.mp hkZ)

omit [DecidableEq E] in
theorem disjoint_dangling {Q Q' : Finset V} (hQ : Q ∈ F.parts) (hQ' : Q' ∈ F.parts)
    (hne : Q ≠ Q') : Disjoint (H.dangling Q) (H.dangling Q') := by
  rw [Finset.disjoint_left]
  intro e he he'
  obtain ⟨k, hk, _, hkZ⟩ := F.exists_end_of_mem_dangling hQ he
  obtain ⟨k', hk', _, _⟩ := F.exists_end_of_mem_dangling hQ' he'
  have hkk : k = k' := by
    by_contra hn
    have hrev : k' = Fin.rev k :=
      (show ∀ a b : Fin 2, a ≠ b → b = Fin.rev a by decide) k k' hn
    have hnot := F.avoid Q' hQ' _ hk'
    rw [hrev] at hnot
    exact hnot hkZ
  subst k'
  exact hne (F.eq_of_mem hQ hQ' hk hk')

/-- The total weight leaving odd components is bounded by the deleted vertex count. -/
theorem sum_odd_cutWeight_le {x : E → ℚ} (hx : H.IsFractionalPerfectMatching x) :
    (∑ Q ∈ F.odd, H.cutWeight x Q) ≤ (Z.card : ℚ) := by
    calc
      _ = ∑ e ∈ F.odd.biUnion H.dangling, x e := by
        rw [Finset.sum_biUnion]
        · rfl
        · intro Q hQ Q' hQ' hne
          exact F.disjoint_dangling (F.mem_odd.mp hQ).1 (F.mem_odd.mp hQ').1 hne
      _ ≤ H.cutWeight x Z := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.biUnion_subset.mpr fun Q hQ ↦ F.dangling_subset (F.mem_odd.mp hQ).1)
        (fun e _ _ ↦ hx.nonneg e)
      _ ≤ ∑ v ∈ Z, H.weightedDegree x v := cutWeight_le_sum_weightedDegree hx.nonneg Z
      _ = _ := by simp [hx.degree]

/-- Weighted Tutte counting for a component family. -/
theorem odd_card_le_of_fractional {x : E → ℚ} (hx : H.IsFractionalPerfectMatching x) :
    F.odd.card ≤ Z.card := by
  have hsum : (F.odd.card : ℚ) ≤ ∑ Q ∈ F.odd, H.cutWeight x Q := by
    calc
      _ = ∑ _Q ∈ F.odd, (1 : ℚ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun Q hQ ↦ hx.odd_cut Q (F.mem_odd.mp hQ).2
  exact_mod_cast hsum.trans (F.sum_odd_cutWeight_le hx)

end ComponentFamily

/-- Feasibility of the odd-cut system implies existence of a perfect matching. -/
theorem IsFractionalPerfectMatching.exists_perfectMatching {x : E → ℚ}
    (hx : H.IsFractionalPerfectMatching x) : ∃ M, H.IsPerfectMatching M :=
  exists_perfectMatching_of_component_bound fun _ F ↦ F.odd_card_le_of_fractional hx

omit [DecidableEq E] in
private theorem sum_restrict (S : Finset E) (f : E → ℚ) (hz : ∀ e, e ∉ S → f e = 0) :
    ∑ e : S, f e.1 = ∑ e, f e := by
  rw [← Finset.sum_subtype S (fun _ ↦ Iff.rfl)]
  exact Finset.sum_subset (Finset.subset_univ _) (fun e _ he ↦ hz e he)

omit [DecidableEq E] in
theorem restrictEdges_weightedDegree (S : Finset E) (x : E → ℚ)
    (hz : ∀ e, e ∉ S → x e = 0) (v : V) :
    (H.restrictEdges S).weightedDegree (fun e ↦ x e.1) v = H.weightedDegree x v := by
  unfold weightedDegree
  apply sum_restrict S (fun e ↦ ∑ k : Fin 2, if H.endAt e k = v then x e else 0)
  intro e he
  simp [hz e he]

omit [DecidableEq E] in
theorem restrictEdges_cutWeight (S : Finset E) (x : E → ℚ)
    (hz : ∀ e, e ∉ S → x e = 0) (X : Finset V) :
    (H.restrictEdges S).cutWeight (fun e ↦ x e.1) X = H.cutWeight x X := by
  unfold cutWeight dangling
  rw [Finset.sum_filter, Finset.sum_filter]
  apply sum_restrict S (fun e ↦ if ¬ (H.endAt e 0 ∈ X ↔ H.endAt e 1 ∈ X) then x e else 0)
  intro e he
  simp [hz e he]

omit [DecidableEq E] in
theorem IsFractionalPerfectMatching.restrictEdges {x : E → ℚ}
    (hx : H.IsFractionalPerfectMatching x) (S : Finset E)
    (hz : ∀ e, e ∉ S → x e = 0) :
    (H.restrictEdges S).IsFractionalPerfectMatching (fun e ↦ x e.1) := by
  refine ⟨fun e ↦ hx.nonneg e.1, ?_, ?_⟩
  · intro v
    rw [restrictEdges_weightedDegree S x hz, hx.degree]
  · intro X hX
    rw [restrictEdges_cutWeight S x hz]
    exact hx.odd_cut X hX

/-- A fractional perfect matching has a perfect matching in its positive support. -/
theorem IsFractionalPerfectMatching.exists_perfectMatching_support {x : E → ℚ}
    (hx : H.IsFractionalPerfectMatching x) :
    ∃ M, H.IsPerfectMatching M ∧ ∀ e ∈ M, 0 < x e := by
  let S := Finset.univ.filter fun e ↦ 0 < x e
  have hz : ∀ e, e ∉ S → x e = 0 := by
    intro e he
    have hn : ¬ 0 < x e := by simpa [S] using he
    exact le_antisymm (le_of_not_gt hn) (hx.nonneg e)
  obtain ⟨M, hM⟩ := (hx.restrictEdges S hz).exists_perfectMatching
  refine ⟨M.image Subtype.val, hM.of_restrictEdges, ?_⟩
  intro e he
  obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp he
  exact (Finset.mem_filter.mp f.2).2

end GraphPuzzles.LoopMultigraph
