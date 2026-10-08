import GraphPuzzles.Cuts.SeparatingCutTheory

/-! Equality in Tutte's component bound and the resulting tight cuts. -/

namespace GraphPuzzles.LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

namespace ComponentFamily

variable {Z : Finset V} (F : H.ComponentFamily Z)

/-- A barrier is an equality case of Tutte's inequality. -/
def IsBarrier : Prop := F.odd.card = Z.card

theorem IsBarrier.cutWeight_sum (hb : F.IsBarrier) {x : E → ℚ}
    (hx : H.IsFractionalPerfectMatching x) :
    (∑ Q ∈ F.odd, H.cutWeight x Q) = Z.card := by
  apply le_antisymm (F.sum_odd_cutWeight_le hx)
  calc
    _ = ∑ _Q ∈ F.odd, (1 : ℚ) := by simp [IsBarrier] at hb; simp [hb]
    _ ≤ _ := Finset.sum_le_sum fun Q hQ ↦ hx.odd_cut Q (F.mem_odd.mp hQ).2

/-- Every odd component of a barrier has fractional cut weight one. -/
theorem IsBarrier.cutWeight_one (hb : F.IsBarrier) {x : E → ℚ}
    (hx : H.IsFractionalPerfectMatching x) {Q : Finset V} (hQ : Q ∈ F.odd) :
    H.cutWeight x Q = 1 := by
  have hle := hx.odd_cut Q (F.mem_odd.mp hQ).2
  by_contra hne
  have hlt : 1 < H.cutWeight x Q := lt_of_le_of_ne hle (Ne.symm hne)
  have hs : (∑ _R ∈ F.odd, (1 : ℚ)) < ∑ R ∈ F.odd, H.cutWeight x R :=
    Finset.sum_lt_sum (fun R hR ↦ hx.odd_cut R (F.mem_odd.mp hR).2) ⟨Q, hQ, hlt⟩
  rw [hb.cutWeight_sum F hx] at hs
  have hh : F.odd.card = Z.card := hb
  simp [hh] at hs

/-- The boundary of each odd component of a barrier is tight. -/
theorem IsBarrier.isTightCut (hb : F.IsBarrier) {Q : Finset V} (hQ : Q ∈ F.odd) :
    H.IsTightCut Q := by
  intro M hM
  have hh := hb.cutWeight_one F hM.isFractional hQ
  rw [cutWeight_matchingVector] at hh
  exact_mod_cast hh

/-- In a brick, a barrier with at least two vertices can have only singleton odd components. -/
theorem IsBarrier.odd_card_one (hb : F.IsBarrier) (hg : H.IsBrick) (hZ : 2 ≤ Z.card)
    {Q : Finset V} (hQ : Q ∈ F.odd) : Q.card = 1 := by
  have hn := hg.tight_trivial Q (hb.isTightCut F hQ)
  have hp := Finset.card_pos.mpr (F.nonempty Q (F.mem_odd.mp hQ).1)
  have hs : Z ⊆ Finset.univ \ Q := by
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hq ↦ F.avoid Q (F.mem_odd.mp hQ).1 v hq hv⟩
  have hc := Finset.card_le_card hs
  by_contra hne
  exact hn ⟨by omega, by omega⟩

/-- Every matching edge incident with a barrier goes to an odd component. -/
theorem IsBarrier.endsIn_of_matching (hb : F.IsBarrier) {M : Finset E}
    (hM : H.IsPerfectMatching M) {e : E} (he : e ∈ M) :
    H.endsIn Z e = if e ∈ F.odd.biUnion H.dangling then 1 else 0 := by
  let B := F.odd.biUnion H.dangling
  have hsub : B ⊆ H.dangling Z :=
    Finset.biUnion_subset.mpr fun Q hQ ↦ F.dangling_subset (F.mem_odd.mp hQ).1
  have hnon (f : E) : (0 : ℚ) ≤ (H.endsIn Z f : ℚ) - (if f ∈ B then 1 else 0) := by
    by_cases hf : f ∈ B
    · rw [if_pos hf]
      have hm := endsIn_mod_two (K := H) Z f
      rw [if_pos (hsub hf)] at hm
      have hn : 1 ≤ H.endsIn Z f := by omega
      have hn' : (1 : ℚ) ≤ H.endsIn Z f := by exact_mod_cast hn
      linarith
    · simp only [if_neg hf, sub_zero]
      exact Nat.cast_nonneg _
  have hs : (∑ f, ((H.endsIn Z f : ℚ) - (if f ∈ B then 1 else 0)) * matchingVector M f) = 0 := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [← sum_weightedDegree]
    have hright : (∑ f, (if f ∈ B then (1 : ℚ) else 0) * matchingVector M f) = Z.card := by
      simp only [ite_mul, one_mul, zero_mul, ← Finset.sum_filter,
        Finset.filter_mem_eq_inter, Finset.univ_inter]
      change (∑ f ∈ F.odd.biUnion H.dangling, matchingVector M f) = _
      rw [Finset.sum_biUnion]
      · exact hb.cutWeight_sum F hM.isFractional
      · intro Q hQ R hR hne
        exact F.disjoint_dangling (F.mem_odd.mp hQ).1 (F.mem_odd.mp hR).1 hne
    rw [hright]
    simp [hM.isFractional.degree]
  have heq := (Finset.sum_eq_zero_iff_of_nonneg
    (fun f _ ↦ mul_nonneg (hnon f) (hM.isFractional.nonneg f))).mp hs e (Finset.mem_univ _)
  simp only [matchingVector, if_pos he, mul_one] at heq
  have hh := sub_eq_zero.mp heq
  change H.endsIn Z e = if e ∈ B then 1 else 0
  split_ifs at hh ⊢ <;> exact_mod_cast hh

/-- Barrier equality forces every incidence in the barrier to go to an odd component. -/
theorem IsBarrier.endsIn (hb : F.IsBarrier) (hg : H.IsMatchingCovered) (e : E) :
    H.endsIn Z e = if e ∈ F.odd.biUnion H.dangling then 1 else 0 := by
  obtain ⟨M, hM, he⟩ := hg.2 e
  exact hb.endsIn_of_matching F hM he

/-- A barrier of size at least two contradicts the brick conditions. -/
theorem IsBarrier.not_of_brick (hb : F.IsBarrier) (hg : H.IsBrick)
    (hloop : ∀ e, H.endAt e 0 ≠ H.endAt e 1) (hZ : 2 ≤ Z.card) : False := by
  let U := F.odd.biUnion id
  have hUZ (v : V) (hv : v ∈ U) : v ∉ Z := by
    obtain ⟨Q, hQ, hv⟩ := Finset.mem_biUnion.mp hv
    exact F.avoid Q (F.mem_odd.mp hQ).1 v hv
  have otherZ (e : E) (k : Fin 2) (hk : H.endAt e k ∈ U) : H.endAt e (Fin.rev k) ∈ Z := by
    obtain ⟨Q, hQ, hk⟩ := Finset.mem_biUnion.mp hk
    by_contra hn
    have hh := F.closed Q (F.mem_odd.mp hQ).1 e k hk hn
    have heq := Finset.card_le_one_iff.mp (hb.odd_card_one F hg hZ hQ).le hk hh
    exact endAt_rev_ne e k hloop heq
  have otherU (e : E) (k : Fin 2) (hk : H.endAt e k ∈ Z) : H.endAt e (Fin.rev k) ∈ U := by
    have hp : 0 < H.endsIn Z e := Finset.card_pos.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩
    have hh := hb.endsIn F hg.matchingCovered e
    have hm : e ∈ F.odd.biUnion H.dangling := by
      by_contra hn
      rw [if_neg hn] at hh
      omega
    obtain ⟨Q, hQ, heQ⟩ := Finset.mem_biUnion.mp hm
    obtain ⟨j, hj, _, _⟩ := F.exists_end_of_mem_dangling (F.mem_odd.mp hQ).1 heQ
    have hkj : k ≠ j := by
      intro heq
      exact F.avoid Q (F.mem_odd.mp hQ).1 _ hj (heq ▸ hk)
    have hjk : j = Fin.rev k :=
      (show ∀ a b : Fin 2, a ≠ b → b = Fin.rev a by decide) k j hkj
    apply Finset.mem_biUnion.mpr
    exact ⟨Q, hQ, hjk ▸ hj⟩
  let S := Z ∪ U
  have step (e : E) (k : Fin 2) (hk : H.endAt e k ∈ S) : H.endAt e (Fin.rev k) ∈ S := by
    rcases Finset.mem_union.mp hk with hz | hu
    · exact Finset.mem_union_right _ (otherU e k hz)
    · exact Finset.mem_union_left _ (otherZ e k hu)
  let c : V → Bool := fun v ↦ decide (v ∈ S)
  have hcol (e : E) : c (H.endAt e 0) = c (H.endAt e 1) := by
    by_cases h0 : H.endAt e 0 ∈ S
    · have h1 : H.endAt e 1 ∈ S := step e 0 h0
      simp [c, h0, h1]
    · have h1 : H.endAt e 1 ∉ S := fun hh ↦ h0 (step e 1 hh)
      simp [c, h0, h1]
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega : 0 < Z.card)
  have hzS : z ∈ S := Finset.mem_union_left _ hz
  have hAll (v : V) : v ∈ S := by
    by_contra hn
    have hh := hg.matchingCovered.1 c hcol z v
    simp [c, hzS, hn] at hh
  apply hg.notBipartite
  refine ⟨fun v ↦ decide (v ∈ Z), ?_⟩
  intro e
  rcases Finset.mem_union.mp (hAll (H.endAt e 0)) with hz | hu
  · have hn := hUZ _ (otherU e 0 hz)
    change H.endAt e 1 ∉ Z at hn
    simp [hz, hn]
  · have hz : H.endAt e 1 ∈ Z := otherZ e 0 hu
    simp [hUZ _ hu, hz]

end ComponentFamily

/-- Deleting any two distinct vertices leaves a perfect matching. -/
def IsBicritical (H : LoopMultigraph V E) : Prop :=
  ∀ u v : V, u ≠ v → ∃ P, H.IsPerfectMatchingOn ((Finset.univ.erase u).erase v) P

/-- The bicritical direction of the brick characterization, proved by Tutte barriers. -/
theorem IsBrick.isBicritical (hg : H.IsBrick) (hloop : ∀ e, H.endAt e 0 ≠ H.endAt e 1) :
    H.IsBicritical := by
  classical
  have hE : Nonempty E := by
    by_contra hn
    haveI : IsEmpty E := not_nonempty_iff.mp hn
    exact hg.notBipartite ⟨fun _ ↦ false, fun e ↦ isEmptyElim e⟩
  obtain ⟨M, hM, _⟩ := hg.matchingCovered.2 (Classical.choice hE)
  intro u v huv
  by_contra hno
  obtain ⟨Z₀, hu, hv, F, hge⟩ := exists_componentFamily_of_no_matching hloop
    hM.isFractional.card_even huv hno
  have hZ : (Z₀ ∪ {u, v}).card = Z₀.card + 2 := by
    rw [Finset.card_union_of_disjoint, Finset.card_pair huv]
    rw [Finset.disjoint_insert_right, Finset.disjoint_singleton_right]
    exact ⟨hu, hv⟩
  have hle := F.odd_card_le_of_fractional hM.isFractional
  have hbar : F.IsBarrier := by
    change F.odd.card = (Z₀ ∪ {u, v}).card
    omega
  exact hbar.not_of_brick F hg hloop (by omega)

end GraphPuzzles.LoopMultigraph
