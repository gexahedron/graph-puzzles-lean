import GraphPuzzles.Matching.Fractional.MatchingCombination
import GraphPuzzles.Matching.MatchingContraction
import GraphPuzzles.Matching.Fractional.FiniteCoupling

/-! Gluing matching distributions of the two contractions of a cut. -/

namespace GraphPuzzles.LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

omit [Fintype E] in
theorem mem_image_subtype {S : Finset E} (M : Finset S) (e : S) :
    e.1 ∈ M.image Subtype.val ↔ e ∈ M := by
  constructor
  · rintro h
    obtain ⟨f, hf, he⟩ := Finset.mem_image.mp h
    exact (Subtype.ext he : f = e) ▸ hf
  · exact fun h ↦ Finset.mem_image.mpr ⟨e, h, rfl⟩

theorem IsPoleMatching.mem_glue_left {X : Finset V} {P Q : Finset E}
    (hQ : H.IsPoleMatching (Finset.univ \ X) Q)
    (hag : ∀ e ∈ H.dangling X, e ∈ P ↔ e ∈ Q) {e : E} (he : e ∈ H.meets X) :
    e ∈ P ∪ Q ↔ e ∈ P := by
  constructor
  · intro h
    rcases Finset.mem_union.mp h with h | h
    · exact h
    · obtain ⟨k, hk⟩ := mem_meets.mp he
      have hd : e ∈ H.dangling X := mem_dangling_of_mem_meets
        (X := X) (Y := Finset.univ \ X)
        (fun _ hX hXC ↦ (Finset.mem_sdiff.mp hXC).2 hX) (hQ.1 h) hk
      exact (hag e hd).mpr h
  · exact Finset.mem_union_left _

namespace MatchingCombination

variable {x : E → ℚ} {X : Finset V}

/-- The distribution of the unique matching edge at the contracted vertex. -/
theorem boundary_marginal
    (C : (H.contract X).MatchingCombination (fun e ↦ x e.1)) (e : E) :
    (∑ M : C.support,
      if (C.support_valid M).contractBoundary = e then C.weight M.1 else 0) =
      if e ∈ H.dangling X then x e else 0 := by
  by_cases he : e ∈ H.dangling X
  · rw [if_pos he]
    let e' : H.meets X := ⟨e, dangling_subset_meets X he⟩
    calc
      _ = ∑ M : C.support, C.weight M.1 * matchingVector M.1 e' := by
        apply Finset.sum_congr rfl
        intro M _
        have hm : (C.support_valid M).contractBoundary = e ↔ e' ∈ M.1 := by
          rw [eq_comm, ← (C.support_valid M).contract_boundary_iff he]
          exact mem_image_subtype M.1 e'
        simp only [hm, matchingVector]
        split_ifs <;> simp
      _ = x e := C.support_marginal e'
  · rw [if_neg he]
    apply Finset.sum_eq_zero
    intro M _
    apply if_neg
    intro hm
    exact he (hm ▸ (C.support_valid M).contract_boundary_mem.2)

/-- Couple the two distributions by their chosen boundary edge and glue each matched pair. -/
noncomputable def glue
    (C : (H.contract X).MatchingCombination (fun e ↦ x e.1))
    (D : (H.contract (Finset.univ \ X)).MatchingCombination (fun e ↦ x e.1)) :
    H.MatchingCombination x := by
  classical
  let a : C.support → ℚ := fun M ↦ C.weight M.1
  let b : D.support → ℚ := fun N ↦ D.weight N.1
  let f : C.support → E := fun M ↦ (C.support_valid M).contractBoundary
  let g : D.support → E := fun N ↦ (D.support_valid N).contractBoundary
  let m : E → ℚ := fun e ↦ if e ∈ H.dangling X then x e else 0
  have hfa : ∀ e, (∑ M, if f M = e then a M else 0) = m e := C.boundary_marginal
  have hgb : ∀ e, (∑ N, if g N = e then b N else 0) = m e := by
    intro e
    simpa only [dangling_compl] using D.boundary_marginal e
  let Q := FiniteCoupling.ofCommonMarginal a b f g m C.support_positive D.support_positive hfa hgb
  have same {M : C.support} {N : D.support} (h : Q.mass M N ≠ 0) : f M = g N := by
    by_contra hn
    exact h (FiniteCoupling.ofCommonMarginal_zero_of_ne a b f g m
      C.support_positive D.support_positive hfa hgb hn)
  let P : C.support × D.support → Finset E :=
    fun p ↦ p.1.1.image Subtype.val ∪ p.2.1.image Subtype.val
  apply ofFamily P (fun p ↦ Q.mass p.1 p.2) (fun p ↦ Q.nonneg p.1 p.2)
  · intro p hp
    exact glue_contract_matchings (C.support_valid p.1) (D.support_valid p.2)
      (contract_boundary_agreement (C.support_valid p.1) (D.support_valid p.2) (same hp))
  · rw [Fintype.sum_prod_type]
    simpa only [Q.row] using C.support_total
  · intro e
    by_cases he : e ∈ H.meets X
    · let e' : H.meets X := ⟨e, he⟩
      have key (M : C.support) (N : D.support) :
          Q.mass M N * matchingVector (P (M, N)) e =
            Q.mass M N * matchingVector M.1 e' := by
        by_cases hw : Q.mass M N = 0
        · simp [hw]
        · have hag := contract_boundary_agreement (C.support_valid M) (D.support_valid N) (same hw)
          have hh : e ∈ P (M, N) ↔ e' ∈ M.1 :=
            ((D.support_valid N).contract_to_pole.1.mem_glue_left hag he).trans
              (mem_image_subtype M.1 e')
          simp only [matchingVector, hh]
      rw [Fintype.sum_prod_type]
      calc
        _ = ∑ M : C.support, ∑ N : D.support, Q.mass M N * matchingVector M.1 e' := by
          apply Finset.sum_congr rfl
          intro M _
          exact Finset.sum_congr rfl fun N _ ↦ key M N
        _ = ∑ M : C.support, a M * matchingVector M.1 e' := by
          simp_rw [← Finset.sum_mul, Q.row]
        _ = x e := C.support_marginal e'
    · have he' : e ∈ H.meets (Finset.univ \ X) := by
        apply mem_meets.mpr
        refine ⟨0, ?_⟩
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
        exact fun h ↦ he (mem_meets.mpr ⟨0, h⟩)
      let e' : H.meets (Finset.univ \ X) := ⟨e, he'⟩
      have key (M : C.support) (N : D.support) :
          matchingVector (P (M, N)) e = matchingVector N.1 e' := by
        have hm : e ∉ M.1.image Subtype.val :=
          fun h ↦ he ((C.support_valid M).contract_to_pole.1.1 h)
        have hh : e ∈ P (M, N) ↔ e' ∈ N.1 := by
          change e ∈ M.1.image Subtype.val ∪ N.1.image Subtype.val ↔ _
          rw [Finset.mem_union, or_iff_right hm]
          exact mem_image_subtype N.1 e'
        simp only [matchingVector, hh]
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      calc
        _ = ∑ N : D.support, ∑ M : C.support, Q.mass M N * matchingVector N.1 e' := by
          apply Finset.sum_congr rfl
          intro N _
          apply Finset.sum_congr rfl
          intro M _
          rw [key]
        _ = ∑ N : D.support, b N * matchingVector N.1 e' := by
          simp_rw [← Finset.sum_mul, Q.column]
        _ = x e := D.support_marginal e'

end MatchingCombination
end GraphPuzzles.LoopMultigraph
