import GraphPuzzles.Matching.VertexMatching
import GraphPuzzles.Matching.Barriers.BarrierInternalEdge

/-! Barrier obstructions for matchings with a distinguished hub. -/

namespace GraphPuzzles.LoopMultigraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

namespace ComponentFamily

variable {B : Finset V} (F : H.ComponentFamily B)

/-- An internal barrier edge cannot belong to a vertex matching whose hub
lies outside the barrier. Odd component boundaries consume all barrier
incidences, leaving no room for the two incidences of an internal edge. -/
theorem IsBarrier.vertexMatching_not_mem (hb : F.IsBarrier) {v : V} {M : Finset E}
    (hv : v ∉ B) (hM : H.IsVertexMatching v M) (heven : Even (Fintype.card V))
    {e : E} (h0 : H.endAt e 0 ∈ B) (h1 : H.endAt e 1 ∈ B) : e ∉ M := by
  intro he
  have hs := F.sum_odd_cutWeight_add_internal_le
    (x := matchingVector M) (fun f ↦ by unfold matchingVector; split_ifs <;> norm_num) h0 h1
  have hd : (∑ w ∈ B, H.weightedDegree (matchingVector M) w) = (B.card : ℚ) := by
    calc
      _ = ∑ _w ∈ B, (1 : ℚ) := Finset.sum_congr rfl fun w hw ↦ by
        rw [weightedDegree_matchingVector, hM w (fun hh ↦ hv (hh ▸ hw))]
        norm_num
      _ = _ := by simp
  have hl : (F.odd.card : ℚ) ≤ ∑ Q ∈ F.odd, H.cutWeight (matchingVector M) Q := by
    calc
      _ = ∑ _Q ∈ F.odd, (1 : ℚ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun Q hQ ↦ by
        have ho := hM.odd_crossing heven (F.mem_odd.mp hQ).2
        rw [Nat.odd_iff] at ho
        have hp : 1 ≤ (M ∩ H.dangling Q).card := by omega
        rw [cutWeight_matchingVector]
        exact_mod_cast hp
  rw [hd, show matchingVector M e = 1 from if_pos he] at hs
  rw [show F.odd.card = B.card from hb] at hl
  linarith

/-- If deleting the hub leaves a factor-critical graph, a barrier containing
both ends of a non-loop edge must avoid the hub. -/
theorem IsBarrier.hub_not_mem_of_factorCritical (hb : F.IsBarrier) {v : V}
    (hfc : H.IsFactorCritical (Finset.univ.erase v))
    {e : E} (hne : H.endAt e 0 ≠ H.endAt e 1)
    (h0 : H.endAt e 0 ∈ B) (h1 : H.endAt e 1 ∈ B) : v ∉ B := by
  intro hv
  have hw : ∃ w ∈ B, w ≠ v := by
    by_cases h : H.endAt e 0 = v
    · exact ⟨H.endAt e 1, h1, fun hh ↦ hne (h.trans hh.symm)⟩
    · exact ⟨H.endAt e 0, h0, h⟩
  obtain ⟨w, hwB, hwv⟩ := hw
  obtain ⟨P, hP⟩ := hfc w (by simp [hwv])
  exact hb.not_pairMatching F hv hwB hwv.symm hP

end ComponentFamily

/-- A vertex matching on an even graph supplies an edge at the hub. If the
hub-deleted graph is factor-critical, that edge extends to a perfect matching. -/
theorem IsVertexMatching.exists_perfectMatching_of_factorCritical {v : V} {M : Finset E}
    (hM : H.IsVertexMatching v M) (heven : Even (Fintype.card V))
    (hloop : ∀ e, H.endAt e 0 ≠ H.endAt e 1)
    (hfc : H.IsFactorCritical (Finset.univ.erase v)) : ∃ P, H.IsPerfectMatching P := by
  have ho := hM.odd_hub_degree heven
  rw [Nat.odd_iff] at ho
  have hp : 0 < H.degreeIn M v := by omega
  obtain ⟨⟨e, k⟩, he⟩ := Finset.card_pos.mp hp
  have hk : H.endAt e k = v := (Finset.mem_filter.mp he).2
  have hw : H.endAt e (Fin.rev k) ≠ v := fun hh ↦
    endAt_rev_ne e k hloop (hk.trans hh.symm)
  obtain ⟨P, hP⟩ := hfc (H.endAt e (Fin.rev k)) (by simp [hw])
  refine ⟨insert e P, hP.insert_perfect ?_ hw.symm⟩
  fin_cases k
  · exact Or.inl ⟨hk, rfl⟩
  · exact Or.inr ⟨rfl, hk⟩

end GraphPuzzles.LoopMultigraph
