import GraphPuzzles.Matching.Fractional.FractionalTutte
import GraphPuzzles.Matching.MatchingContraction

/-! Fractional perfect matchings descend through cuts of weight one. -/

namespace GraphPuzzles.LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

omit [DecidableEq E] in
theorem contract_weightedDegree_some (X : Finset V) (x : E → ℚ) (v : X) :
    (H.contract X).weightedDegree (fun e ↦ x e.1) (some v) = H.weightedDegree x v.1 := by
  unfold weightedDegree
  simp only [contract_endAt_eq_some_iff]
  rw [← Finset.sum_subtype (H.meets X) (fun _ ↦ Iff.rfl)
    (fun e ↦ ∑ k : Fin 2, if H.endAt e k = v.1 then x e else 0)]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro e _ he
  apply Finset.sum_eq_zero
  intro k _
  apply if_neg
  intro hk
  exact he (mem_meets.mpr ⟨k, hk ▸ v.2⟩)

theorem contract_weightedDegree_none (X : Finset V) (x : E → ℚ) :
    (H.contract X).weightedDegree (fun e ↦ x e.1) none = H.cutWeight x X := by
  have key (e : H.meets X) :
      (∑ k : Fin 2, if (H.contract X).endAt e k = none then x e.1 else 0) =
        if e.1 ∈ H.dangling X then x e.1 else 0 := by
    have hc := contract_ends_none X e
    have hc' : (∑ k : Fin 2, if (H.contract X).endAt e k = none then (1 : ℚ) else 0) =
        if e.1 ∈ H.dangling X then 1 else 0 := by exact_mod_cast hc
    calc
      _ = (∑ k : Fin 2, if (H.contract X).endAt e k = none then (1 : ℚ) else 0) * x e.1 := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _
        split_ifs <;> simp
      _ = _ := by rw [hc']; split_ifs <;> simp
  rw [weightedDegree, Finset.sum_congr rfl (fun e _ ↦ key e),
    ← Finset.sum_subtype (H.meets X) (fun _ ↦ Iff.rfl)
      (fun e ↦ if e ∈ H.dangling X then x e else 0), ← Finset.sum_filter]
  unfold cutWeight
  congr 1
  ext e
  simp only [Finset.mem_filter]
  exact ⟨And.right, fun he ↦ ⟨dangling_subset_meets X he, he⟩⟩

/-- The original vertices represented by the `some` vertices of a contraction shore. -/
def sourceShore (X : Finset V) (Y : Finset (Option X)) : Finset V :=
  (Finset.univ.filter fun v : X ↦ some v ∈ Y).image Subtype.val

omit [Fintype V] in
theorem sourceShore_subset (X : Finset V) (Y : Finset (Option X)) : sourceShore X Y ⊆ X := by
  intro v hv
  obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
  exact w.2

omit [Fintype V] in
theorem card_sourceShore (X : Finset V) (Y : Finset (Option X)) (hn : none ∉ Y) :
    (sourceShore X Y).card = Y.card := by
  rw [sourceShore, Finset.card_image_of_injective _ Subtype.val_injective]
  apply Finset.card_bij (fun v _ ↦ some v)
  · intro v hv
    exact (Finset.mem_filter.mp hv).2
  · intro v _ w _ h
    exact Option.some_injective _ h
  · intro w hw
    cases w with
    | none => exact (hn hw).elim
    | some v => exact ⟨v, by simpa using hw, rfl⟩

omit [DecidableEq E] in
theorem contract_mem_sourceShore (X : Finset V) (Y : Finset (Option X)) (hn : none ∉ Y)
    (e : H.meets X) (k : Fin 2) :
    H.endAt e.1 k ∈ sourceShore X Y ↔ (H.contract X).endAt e k ∈ Y := by
  rw [contract_endAt]
  split_ifs with h
  · simp only [sourceShore, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨v, hv, he⟩
      have hh : v = ⟨H.endAt e.1 k, h⟩ := Subtype.ext he
      rwa [hh] at hv
    · intro hv
      exact ⟨⟨_, h⟩, hv, rfl⟩
  · exact iff_of_false (fun hv ↦ h (sourceShore_subset X Y hv)) hn

omit [DecidableEq E] in
theorem contract_cutWeight_sourceShore (X : Finset V) (Y : Finset (Option X))
    (hn : none ∉ Y) (x : E → ℚ) :
    (H.contract X).cutWeight (fun e ↦ x e.1) Y = H.cutWeight x (sourceShore X Y) := by
  unfold cutWeight dangling
  rw [Finset.sum_filter, Finset.sum_filter]
  simp only [← contract_mem_sourceShore X Y hn]
  rw [← Finset.sum_subtype (H.meets X) (fun _ ↦ Iff.rfl)
    (fun e ↦ if ¬ (H.endAt e 0 ∈ sourceShore X Y ↔ H.endAt e 1 ∈ sourceShore X Y)
      then x e else 0)]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro e _ he
  have h0 : H.endAt e 0 ∉ sourceShore X Y := fun h ↦
    he (mem_meets.mpr ⟨0, sourceShore_subset X Y h⟩)
  have h1 : H.endAt e 1 ∉ sourceShore X Y := fun h ↦
    he (mem_meets.mpr ⟨1, sourceShore_subset X Y h⟩)
  simp [h0, h1]

omit [DecidableEq E] in
/-- Restriction through an odd shore preserves odd-cut inequalities, even when
the degree at the contraction vertex is not one. -/
theorem IsFractionalPerfectMatching.contract_odd_cut {x : E → ℚ}
    (hx : H.IsFractionalPerfectMatching x) (X : Finset V) (hX : Odd X.card)
    (Y : Finset (Option X)) (hY : Odd Y.card) :
    1 ≤ (H.contract X).cutWeight (fun e ↦ x e.1) Y := by
  have key (Y : Finset (Option X)) (hY : Odd Y.card) (hn : none ∉ Y) :
        1 ≤ (H.contract X).cutWeight (fun e ↦ x e.1) Y := by
    rw [contract_cutWeight_sourceShore X Y hn]
    exact hx.odd_cut _ ((card_sourceShore X Y hn).symm ▸ hY)
  by_cases hn : none ∈ Y
  · have he : Odd (Finset.univ \ Y).card := by
      have hle := Finset.card_le_univ Y
      rw [Fintype.card_option, Fintype.card_coe] at hle
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
        Fintype.card_option, Fintype.card_coe]
      rw [Nat.odd_iff] at hX hY ⊢
      omega
    have hb := key (Finset.univ \ Y) he (by simp [hn])
    simpa only [cutWeight, dangling_compl] using hb
  · exact key Y hY hn

/-- Contracting an odd shore of weight one preserves the fractional matching constraints. -/
theorem IsFractionalPerfectMatching.contract {x : E → ℚ} (hx : H.IsFractionalPerfectMatching x)
    (X : Finset V) (hX : Odd X.card) (ht : H.cutWeight x X = 1) :
    (H.contract X).IsFractionalPerfectMatching (fun e ↦ x e.1) := by
  refine ⟨fun e ↦ hx.nonneg e.1, ?_, hx.contract_odd_cut X hX⟩
  intro v
  cases v with
  | none => exact (contract_weightedDegree_none X x).trans ht
  | some v => exact (contract_weightedDegree_some X x v).trans (hx.degree v.1)

end GraphPuzzles.LoopMultigraph
