import GraphPuzzles.Matching.Barriers.BarrierObstruction

/-! Bicriticality is equivalent to the absence of barriers containing two vertices. -/

namespace GraphPuzzles.LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

namespace ComponentFamily

variable {B : Finset V} (F : H.ComponentFamily B)

/-- Component-boundary counting with arbitrary nonnegative weights. -/
theorem sum_odd_cutWeight_le_sum_weightedDegree {x : E → ℚ} (hx : ∀ e, 0 ≤ x e) :
    (∑ Q ∈ F.odd, H.cutWeight x Q) ≤ ∑ v ∈ B, H.weightedDegree x v := by
  calc
    _ = ∑ e ∈ F.odd.biUnion H.dangling, x e := by
      rw [Finset.sum_biUnion]
      · rfl
      · intro Q hQ R hR hne
        exact F.disjoint_dangling (F.mem_odd.mp hQ).1 (F.mem_odd.mp hR).1 hne
    _ ≤ H.cutWeight x B := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.biUnion_subset.mpr fun Q hQ ↦ F.dangling_subset (F.mem_odd.mp hQ).1)
      (fun e _ _ ↦ hx e)
    _ ≤ _ := cutWeight_le_sum_weightedDegree hx B

/-- Covering the vertices of every odd part requires at least that many
matching incidences in the separator. -/
theorem odd_card_le_sum_degreeIn {P : Finset E}
    (hP : ∀ Q ∈ F.odd, ∀ v ∈ Q, H.degreeIn P v = 1) :
    F.odd.card ≤ ∑ v ∈ B, H.degreeIn P v := by
  have hcut (Q : Finset V) (hQ : Q ∈ F.odd) :
      (1 : ℚ) ≤ H.cutWeight (matchingVector P) Q := by
    have hp := card_mod_two_of_degreeIn_one (hP Q hQ)
    have ho := (F.mem_odd.mp hQ).2
    rw [Nat.odd_iff] at ho
    have hh : 1 ≤ (P ∩ H.dangling Q).card := by omega
    rw [cutWeight_matchingVector]
    exact_mod_cast hh
  have hsum : (F.odd.card : ℚ) ≤ ∑ v ∈ B, (H.degreeIn P v : ℚ) := by
    calc
      _ = ∑ _Q ∈ F.odd, (1 : ℚ) := by simp
      _ ≤ ∑ Q ∈ F.odd, H.cutWeight (matchingVector P) Q :=
        Finset.sum_le_sum hcut
      _ ≤ ∑ v ∈ B, H.weightedDegree (matchingVector P) v :=
        F.sum_odd_cutWeight_le_sum_weightedDegree
          (fun e ↦ by unfold matchingVector; split_ifs <;> norm_num)
      _ = _ := Finset.sum_congr rfl fun v _ ↦ weightedDegree_matchingVector P v
  exact_mod_cast hsum

/-- No matching can cover all vertices except two distinct vertices of a barrier. -/
theorem IsBarrier.not_pairMatching (hb : F.IsBarrier) {u v : V}
    (hu : u ∈ B) (hv : v ∈ B) (huv : u ≠ v) {P : Finset E}
    (hP : H.IsPerfectMatchingOn ((Finset.univ.erase u).erase v) P) : False := by
  have hbound := F.odd_card_le_sum_degreeIn (P := P) (by
    intro Q hQ w hw
    have hwB := F.avoid Q (F.mem_odd.mp hQ).1 w hw
    exact hP.2 w (by
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact ⟨fun h ↦ hwB (h ▸ hv), fun h ↦ hwB (h ▸ hu)⟩))
  let D := (B.erase u).erase v
  have hDB : D ⊆ B := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
  have hsum : (∑ w ∈ B, H.degreeIn P w) = D.card := by
    calc
      _ = ∑ w ∈ D, H.degreeIn P w := by
        symm
        apply Finset.sum_subset hDB
        intro w hwB hwD
        apply hP.degree_zero
        intro hw
        exact hwD (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hw).1,
          Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp (Finset.mem_erase.mp hw).2).1, hwB⟩⟩)
      _ = ∑ _w ∈ D, 1 := Finset.sum_congr rfl (by
        intro w hw
        exact hP.2 w (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hw).1,
          Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp (Finset.mem_erase.mp hw).2).1,
            Finset.mem_univ _⟩⟩))
      _ = _ := by simp
  have hvD : v ∈ B.erase u := Finset.mem_erase.mpr ⟨Ne.symm huv, hv⟩
  have hcard : D.card = B.card - 1 - 1 := by
    change ((B.erase u).erase v).card = _
    rw [Finset.card_erase_of_mem hvD, Finset.card_erase_of_mem hu]
  have hp : 0 < B.card := Finset.card_pos.mpr ⟨u, hu⟩
  change F.odd.card = B.card at hb
  rw [hb, hsum, hcard] at hbound
  omega

end ComponentFamily

/-- A bicritical graph has no barrier with two distinct vertices. -/
theorem IsBicritical.barrier_card_le_one (hc : H.IsBicritical) {B : Finset V}
    (F : H.ComponentFamily B) (hb : F.IsBarrier) : B.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro u hu v hv
  by_contra huv
  obtain ⟨P, hP⟩ := hc u v huv
  exact hb.not_pairMatching F hu hv huv hP

/-- The barrier characterization of bicriticality, for a graph with a perfect matching. -/
theorem isBicritical_iff_barrier_card_le_one {M : Finset E} (hM : H.IsPerfectMatching M) :
    H.IsBicritical ↔ ∀ B, ∀ F : H.ComponentFamily B, F.IsBarrier → B.card ≤ 1 := by
  constructor
  · exact fun hc _ F hb ↦ hc.barrier_card_le_one F hb
  · intro hb u v huv
    by_contra hn
    obtain ⟨B, hu, hv, F, hF⟩ := hM.exists_barrier_of_no_pair_matching huv hn
    exact huv (Finset.card_le_one.mp (hb B F hF) u hu v hv)

end GraphPuzzles.LoopMultigraph
