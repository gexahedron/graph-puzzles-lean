import GraphPuzzles.Matching.Fractional.FractionalArithmetic

/-!
# Peeling a perfect matching from a fractional matching

If there is no nontrivial tight odd cut, move towards a matching in the positive
support until an edge disappears or an odd-cut inequality becomes an equality.
The step size is the minimum of a finite set of positive rational bounds.
-/

namespace GraphPuzzles.LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

def positiveEdges (x : E → ℚ) : Finset E := Finset.univ.filter fun e ↦ 0 < x e

omit [DecidableEq E] in
@[simp] theorem mem_positiveEdges (x : E → ℚ) (e : E) :
    e ∈ positiveEdges x ↔ 0 < x e := by simp [positiveEdges]

/-- A nonzero feasible peeling step, with an explicit certificate of progress. -/
theorem IsFractionalPerfectMatching.peel {x : E → ℚ}
    (hx : H.IsFractionalPerfectMatching x)
    (hnt : ∀ X : Finset V, Odd X.card → IsNontrivialCut X → H.cutWeight x X ≠ 1)
    {M : Finset E} (hM : H.IsPerfectMatching M) (hpos : ∀ e ∈ M, 0 < x e) :
    x = matchingVector M ∨
      ∃ (a : ℚ) (y : E → ℚ), 0 < a ∧ a < 1 ∧ H.IsFractionalPerfectMatching y ∧
        (∀ e, x e = a * matchingVector M e + (1 - a) * y e) ∧
        ((positiveEdges y).card < (positiveEdges x).card ∨
          ∃ X : Finset V, Odd X.card ∧ IsNontrivialCut X ∧ H.cutWeight y X = 1) := by
  classical
  let T : Finset (Finset V) := Finset.univ.filter fun X ↦
    Odd X.card ∧ 1 < (M ∩ H.dangling X).card
  let r : Finset V → ℚ := fun X ↦
    (H.cutWeight x X - 1) / ((M ∩ H.dangling X).card - 1)
  let S : Finset ℚ := insert 1 (M.image x ∪ T.image r)
  have hs : S.Nonempty := ⟨1, Finset.mem_insert_self ..⟩
  let a := S.min' hs
  have ha_mem : a ∈ S := S.min'_mem hs
  have ha_le (b : ℚ) (hb : b ∈ S) : a ≤ b := S.min'_le b hb
  have hrpos (X : Finset V) (hX : X ∈ T) : 0 < r X := by
    obtain ⟨ho, hk⟩ := (Finset.mem_filter.mp hX).2
    have hne := hnt X ho (hM.nontrivial_of_crossing_gt_one hk)
    have hc : 0 < H.cutWeight x X - 1 :=
      sub_pos.mpr (lt_of_le_of_ne (hx.odd_cut X ho) hne.symm)
    have hd : (0 : ℚ) < (M ∩ H.dangling X).card - 1 := by
      have hk' : (1 : ℚ) < (M ∩ H.dangling X).card := by exact_mod_cast hk
      linarith
    exact div_pos hc hd
  have ha : 0 < a := by
    rcases Finset.mem_insert.mp ha_mem with he | he
    · rw [he]; norm_num
    · rcases Finset.mem_union.mp he with he | he
      · obtain ⟨e, he, hxe⟩ := Finset.mem_image.mp he
        rw [← hxe]
        exact hpos e he
      · obtain ⟨X, hX, hXe⟩ := Finset.mem_image.mp he
        rw [← hXe]
        exact hrpos X hX
  have ha1 : a ≤ 1 := ha_le 1 (Finset.mem_insert_self ..)
  have hae (e : E) (he : e ∈ M) : a ≤ x e :=
    ha_le _ (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, he, rfl⟩)))
  have hax (X : Finset V) (hX : Odd X.card) :
      a * ((M ∩ H.dangling X).card - 1) ≤ H.cutWeight x X - 1 := by
    by_cases hk : 1 < (M ∩ H.dangling X).card
    · have hXT : X ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hX, hk⟩
      have hb : a ≤ r X := ha_le _
        (Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨X, hXT, rfl⟩)))
      have hk' : (1 : ℚ) < (M ∩ H.dangling X).card := by exact_mod_cast hk
      exact (le_div_iff₀ (by linarith : (0 : ℚ) < (M ∩ H.dangling X).card - 1)).mp hb
    · have hl := hM.isFractional.odd_cut X hX
      rw [cutWeight_matchingVector] at hl
      have hl' : 1 ≤ (M ∩ H.dangling X).card := by exact_mod_cast hl
      have he : (M ∩ H.dangling X).card = 1 := by omega
      rw [he]
      simp only [Nat.cast_one, sub_self, mul_zero]
      linarith [hx.odd_cut X hX]
  by_cases haeq : a = 1
  · left
    apply eq_of_le_of_weightedDegree_eq (H := H)
    · intro e
      by_cases he : e ∈ M
      · simpa only [matchingVector, if_pos he, haeq] using hae e he
      · simpa only [matchingVector, if_neg he] using hx.nonneg e
    · intro v
      rw [hx.degree, hM.isFractional.degree]
  · right
    have halt : a < 1 := lt_of_le_of_ne ha1 haeq
    have hd : 0 < 1 - a := sub_pos.mpr halt
    let y : E → ℚ := fun e ↦ (x e - a * matchingVector M e) / (1 - a)
    have hn (e : E) : 0 ≤ x e - a * matchingVector M e := by
      by_cases he : e ∈ M
      · simp only [matchingVector, if_pos he, mul_one]
        exact sub_nonneg.mpr (hae e he)
      · simp only [matchingVector, if_neg he, mul_zero, sub_zero]
        exact hx.nonneg e
    have hy : H.IsFractionalPerfectMatching y := by
      refine ⟨fun e ↦ div_nonneg (hn e) hd.le, ?_, ?_⟩
      · intro v
        change H.weightedDegree (fun e ↦ (x e - a * matchingVector M e) / (1 - a)) v = 1
        rw [weightedDegree_div, weightedDegree_sub, weightedDegree_mul,
          hx.degree, hM.isFractional.degree, mul_one, div_self (ne_of_gt hd)]
      · intro X hX
        change 1 ≤ H.cutWeight (fun e ↦ (x e - a * matchingVector M e) / (1 - a)) X
        rw [cutWeight_div, cutWeight_sub, cutWeight_mul, cutWeight_matchingVector]
        apply (le_div_iff₀ hd).mpr
        linarith [hax X hX]
    have hmix (e : E) : x e = a * matchingVector M e + (1 - a) * y e := by
      dsimp [y]
      field_simp
      ring
    refine ⟨a, y, ha, halt, hy, hmix, ?_⟩
    rcases Finset.mem_insert.mp ha_mem with he | he
    · exact (haeq he).elim
    · rcases Finset.mem_union.mp he with he | he
      · left
        obtain ⟨e, he, hxe⟩ := Finset.mem_image.mp he
        have hey : y e = 0 := by simp [y, matchingVector, he, hxe]
        have hsub : positiveEdges y ⊆ positiveEdges x := by
          intro f hf
          rw [mem_positiveEdges] at hf ⊢
          have hm0 := hM.isFractional.nonneg f
          have hh := hmix f
          nlinarith
        apply Finset.card_lt_card
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨hsub, ?_⟩
        intro heq
        have hmem : e ∈ positiveEdges x := (mem_positiveEdges _ _).mpr (hpos e he)
        rw [← heq, mem_positiveEdges, hey] at hmem
        exact (lt_irrefl 0) hmem
      · right
        obtain ⟨X, hX, hXa⟩ := Finset.mem_image.mp he
        obtain ⟨ho, hk⟩ := (Finset.mem_filter.mp hX).2
        refine ⟨X, ho, hM.nontrivial_of_crossing_gt_one hk, ?_⟩
        have hk' : (1 : ℚ) < (M ∩ H.dangling X).card := by exact_mod_cast hk
        have heq : H.cutWeight x X - 1 = a * ((M ∩ H.dangling X).card - 1) :=
          (div_eq_iff (by linarith : ((M ∩ H.dangling X).card : ℚ) - 1 ≠ 0)).mp hXa
        change H.cutWeight (fun e ↦ (x e - a * matchingVector M e) / (1 - a)) X = 1
        rw [cutWeight_div, cutWeight_sub, cutWeight_mul, cutWeight_matchingVector]
        apply (div_eq_iff (ne_of_gt hd)).mpr
        linarith

end GraphPuzzles.LoopMultigraph
