import GraphPuzzles.Matching.MatchingOn

/-! Counting a local matching against a larger selected shore. -/

namespace GraphPuzzles.LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E} {X Y Z : Finset V} {M : Finset E}

/-- When every exterior vertex is accounted for by a boundary matching
edge, no selected edge can join two exterior vertices. -/
theorem IsPerfectMatchingOn.no_internal_of_saturated_boundary
    (hM : H.IsPerfectMatchingOn (Y ∪ Z) M) (hd : Disjoint Y Z)
    (hc : (M ∩ H.dangling Y).card = Z.card) :
    ∀ e ∈ M, ¬ (H.endAt e 0 ∈ Z ∧ H.endAt e 1 ∈ Z) := by
  have hle (e : E) (he : e ∈ M) :
      (if e ∈ H.dangling Y then (1 : ℕ) else 0) ≤ H.endsIn Z e := by
    by_cases heY : e ∈ H.dangling Y
    · rw [if_pos heY]
      apply Finset.card_pos.mpr
      have hh := mem_dangling.mp heY
      by_cases h0 : H.endAt e 0 ∈ Y
      · have h1 : H.endAt e 1 ∉ Y := fun h ↦ hh ⟨fun _ ↦ h, fun _ ↦ h0⟩
        exact ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Finset.mem_union.mp (hM.1 e he 1)).resolve_left h1⟩⟩
      · exact ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Finset.mem_union.mp (hM.1 e he 0)).resolve_left h0⟩⟩
    · simp only [if_neg heY, Nat.zero_le]
  have hsum : (∑ e ∈ M, H.endsIn Z e) = Z.card := by
    rw [← sum_degreeIn_eq]
    rw [Finset.sum_congr rfl (fun v hv ↦ hM.2 v (Finset.mem_union_right _ hv))]
    simp
  have hsum' : (∑ e ∈ M, if e ∈ H.dangling Y then (1 : ℕ) else 0) = Z.card := by
    simpa only [Finset.sum_boole, Finset.filter_mem_eq_inter, Nat.cast_id] using hc
  have heq (e : E) (he : e ∈ M) :
      (if e ∈ H.dangling Y then (1 : ℕ) else 0) = H.endsIn Z e := by
    apply Nat.le_antisymm (hle e he)
    by_contra hn
    have hh := Finset.sum_lt_sum hle ⟨e, he, Nat.lt_of_not_ge hn⟩
    rw [hsum, hsum'] at hh
    exact (Nat.lt_irrefl _ hh)
  intro e he hZ
  have h0 : H.endAt e 0 ∉ Y := Finset.disjoint_right.mp hd hZ.1
  have h1 : H.endAt e 1 ∉ Y := Finset.disjoint_right.mp hd hZ.2
  have hcut : e ∉ H.dangling Y := by simp [mem_dangling, h0, h1]
  have hend : H.endsIn Z e = 2 := by
    unfold endsIn
    rw [Finset.card_filter, Fin.sum_univ_two]
    simp [hZ.1, hZ.2]
  have hh := heq e he
  rw [if_neg hcut, hend] at hh
  omega

/-- A local matching whose exterior vertices all match into `Y` crosses
any larger shore once for each exterior vertex outside that shore. -/
theorem IsPerfectMatchingOn.crossing_of_saturated_boundary
    (hM : H.IsPerfectMatchingOn (Y ∪ Z) M) (hd : Disjoint Y Z)
    (hc : (M ∩ H.dangling Y).card = Z.card) (hYX : Y ⊆ X) :
    (M ∩ H.dangling X).card = (Z \ X).card := by
  have hno := hM.no_internal_of_saturated_boundary hd hc
  have hout {e : E} (he : e ∈ M) (k : Fin 2) :
      H.endAt e k ∈ Z \ X ↔ H.endAt e k ∉ X := by
    constructor
    · exact fun h ↦ (Finset.mem_sdiff.mp h).2
    · intro h
      refine Finset.mem_sdiff.mpr ⟨?_, h⟩
      exact (Finset.mem_union.mp (hM.1 e he k)).resolve_left (fun hh ↦ h (hYX hh))
  have hedge (e : E) (he : e ∈ M) : H.endsIn (Z \ X) e =
      if e ∈ H.dangling X then (1 : ℕ) else 0 := by
    unfold endsIn
    rw [Finset.card_filter, Fin.sum_univ_two]
    simp only [hout he, mem_dangling]
    by_cases h0 : H.endAt e 0 ∈ X <;> by_cases h1 : H.endAt e 1 ∈ X
    · simp [h0, h1]
    · simp [h0, h1]
    · simp [h0, h1]
    · exact (hno e he ⟨(Finset.mem_sdiff.mp ((hout he 0).mpr h0)).1,
        (Finset.mem_sdiff.mp ((hout he 1).mpr h1)).1⟩).elim
  have hsum : (∑ v ∈ Z \ X, H.degreeIn M v) = (Z \ X).card := by
    rw [Finset.sum_congr rfl (fun v hv ↦ hM.2 v
      (Finset.mem_union_right _ (Finset.mem_sdiff.mp hv).1))]
    simp
  rw [sum_degreeIn_eq, Finset.sum_congr rfl hedge, Finset.sum_boole,
    Finset.filter_mem_eq_inter] at hsum
  exact hsum

end GraphPuzzles.LoopMultigraph
