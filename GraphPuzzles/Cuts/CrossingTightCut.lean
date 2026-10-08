import GraphPuzzles.Cuts.Shores.UniqueShoreNeighbors
import GraphPuzzles.Cuts.TrivialCutCharacteristic
import GraphPuzzles.Cuts.CohesiveCrossingTransport

/-! The new noncrossing tight cut in Section 6, Case 2. -/

namespace GraphPuzzles.LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {H : LoopMultigraph V E}

theorem IsTightCut.of_modular_shores {X Y : Finset V}
    (htX : H.IsTightCut X) (htI : H.IsTightCut (X ∩ Y))
    (htU : H.IsTightCut (X ∪ Y)) (hz : H.edgesBetween (X \ Y) (Y \ X) = ∅) :
    H.IsTightCut Y := by
  intro M hM
  have hh := cutWeight_modular (H := H) (matchingVector M) X Y
  simp only [hz, Finset.sum_empty, mul_zero, add_zero, cutWeight_matchingVector,
    htX M hM, htI M hM, htU M hM] at hh
  norm_cast at hh
  omega

omit [DecidableEq E] in
/-- If the contraction pole has only one neighbor in the selected shore,
all original edges from that shore to the discarded side have one common end. -/
theorem HasUniqueCrossNeighbor.exists_attachment {X Y : Finset V}
    (h : (H.contract Y).HasUniqueCrossNeighbor (contractShore Y X))
    (hne : (X ∩ Y).Nonempty) :
    ∃ i ∈ X ∩ Y, ∀ a ∈ X ∩ Y, ∀ w, w ∉ Y → ∀ e, H.Joins e w a → a = i := by
  classical
  by_cases hex : ∃ i ∈ X ∩ Y, ∃ w, w ∉ Y ∧ ∃ e, H.Joins e w i
  · obtain ⟨i, hi, w, hw, e, he⟩ := hex
    refine ⟨i, hi, ?_⟩
    intro a ha z hz f hf
    have hei : e ∈ H.meets Y := by
      obtain ⟨k, hk⟩ := (H.joins_comm.mp he).exists_end
      exact mem_meets.mpr ⟨k, hk.symm ▸ (Finset.mem_inter.mp hi).2⟩
    have hfi : f ∈ H.meets Y := by
      obtain ⟨k, hk⟩ := (H.joins_comm.mp hf).exists_end
      exact mem_meets.mpr ⟨k, hk.symm ▸ (Finset.mem_inter.mp ha).2⟩
    have hhe := he.contract hei
    have hhf := hf.contract hfi
    have hiY := (Finset.mem_inter.mp hi).2
    have haY := (Finset.mem_inter.mp ha).2
    simp only [contractVertex, dif_neg hw, dif_pos hiY] at hhe
    simp only [contractVertex, dif_neg hz, dif_pos haY] at hhf
    have hh := h none (none_not_mem_contractShore Y X)
      (some ⟨a, haY⟩) ((some_mem_contractShore Y X _).mpr (Finset.mem_inter.mp ha).1)
      (some ⟨i, hiY⟩) ((some_mem_contractShore Y X _).mpr (Finset.mem_inter.mp hi).1)
      ⟨f, hfi⟩ ⟨e, hei⟩ hhf hhe
    simpa only [Option.some.injEq, Subtype.mk.injEq] using hh
  · obtain ⟨i, hi⟩ := hne
    exact ⟨i, hi, fun a ha w hw e he ↦ (hex ⟨a, ha, w, hw, e, he⟩).elim⟩

/-- A large surviving intersection with a unique attachment supplies a
nontrivial tight cut nested in the original selected shore. -/
theorem IsCohesiveCuts.exists_noncrossing_tight_of_unique_attachment {X Y : Finset V}
    (hc : H.IsCohesiveCuts {X, Y}) (ho : Odd (X ∩ Y).card)
    (hcross : CutsCross X Y) (htY : H.IsTightCut Y) (htU : H.IsTightCut (X ∪ Y))
    (hcard : 3 ≤ (X ∩ Y).card)
    (hN : (H.contract Y).HasUniqueCrossNeighbor (contractShore Y X)) :
    ∃ D, H.IsTightCut D ∧ IsNontrivialCut D ∧ ¬ CutsCross X D := by
  classical
  obtain ⟨i, hi, hatt⟩ := hN.exists_attachment hcross.1
  have hiX := (Finset.mem_inter.mp hi).1
  have hiY := (Finset.mem_inter.mp hi).2
  let D := insert i (X \ Y)
  have hDX : D ⊆ X := Finset.insert_subset hiX Finset.sdiff_subset
  have hI : Y ∩ D = {i} := by
    ext v
    simp only [D, Finset.mem_inter, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · rintro ⟨hy, h | ⟨_, hn⟩⟩
      · exact h
      · exact (hn hy).elim
    · rintro rfl
      exact ⟨hiY, Or.inl rfl⟩
  have hU : Y ∪ D = X ∪ Y := by
    ext v
    simp only [D, Finset.mem_union, Finset.mem_insert, Finset.mem_sdiff]
    constructor
    · rintro (hy | rfl | ⟨hx, _⟩)
      · exact Or.inr hy
      · exact Or.inl hiX
      · exact Or.inl hx
    · rintro (hx | hy)
      · by_cases hy : v ∈ Y
        · exact Or.inl hy
        · exact Or.inr (Or.inr ⟨hx, hy⟩)
      · exact Or.inl hy
  have hzBC := hc.edgesBetween_eq_empty (by simp : X ∈ ({X, Y} : Finset (Finset V)))
    (by simp : Y ∈ ({X, Y} : Finset (Finset V))) ho
  have impossible (e : E) (a b : V) (he : H.Joins e a b)
      (ha : a ∈ Y \ D) (hb : b ∈ D \ Y) : False := by
    have haY := (Finset.mem_sdiff.mp ha).1
    have haD := (Finset.mem_sdiff.mp ha).2
    have hbY := (Finset.mem_sdiff.mp hb).2
    have hbX : b ∈ X := hDX (Finset.mem_sdiff.mp hb).1
    by_cases haX : a ∈ X
    · have heq := hatt a (Finset.mem_inter.mpr ⟨haX, haY⟩) b hbY e (H.joins_comm.mp he)
      exact haD (heq.symm ▸ Finset.mem_insert_self i (X \ Y))
    · have hem : e ∈ H.edgesBetween (X \ Y) (Y \ X) := by
        rcases he with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;>
          simp [edgesBetween, h0, h1, haY, haX, hbY, hbX]
      exact Finset.notMem_empty e (hzBC ▸ hem)
  have hz : H.edgesBetween (Y \ D) (D \ Y) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    rcases (Finset.mem_filter.mp he).2 with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact impossible e _ _ (Or.inl ⟨rfl, rfl⟩) ha hb
    · exact impossible e _ _ (Or.inr ⟨rfl, rfl⟩) ha hb
  have htD : H.IsTightCut D := htY.of_modular_shores
    (hI.symm ▸ isTightCut_singleton H i) (hU.symm ▸ htU) hz
  have hiB : i ∉ X \ Y := fun hh ↦ (Finset.mem_sdiff.mp hh).2 hiY
  have hcardD : 2 ≤ D.card := by
    have hb := Finset.card_pos.mpr hcross.2.1
    simp only [D, Finset.card_insert_of_notMem hiB]
    omega
  have herase : (X ∩ Y).erase i ⊆ Finset.univ \ D := by
    intro v hv
    obtain ⟨hne, hvI⟩ := Finset.mem_erase.mp hv
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    rintro h
    rcases Finset.mem_insert.mp h with h | h
    · exact hne h
    · exact (Finset.mem_sdiff.mp h).2 (Finset.mem_inter.mp hvI).2
  have hcomp : 2 ≤ (Finset.univ \ D).card := by
    have hh := Finset.card_le_card herase
    rw [Finset.card_erase_of_mem hi] at hh
    omega
  refine ⟨D, htD, ⟨hcardD, hcomp⟩, (not_cutsCross_iff X D).mpr
    (Or.inr (Or.inr (Or.inr ?_)))⟩
  intro v hv
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hd ↦ (Finset.mem_sdiff.mp hv).2 (hDX hd)⟩

end GraphPuzzles.LoopMultigraph
